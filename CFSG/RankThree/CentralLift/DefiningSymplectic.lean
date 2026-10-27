module

public import CFSG.RankThree.CentralLift.DefiningTools
public import CFSG.RankThree.Classical.SiegelRadical
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect

public section

namespace CFSG.RankThree.CentralLift

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Classical (siegelRadicalSp mem_siegelRadicalSp siegel_radical_sp
  siegel_radical_sp_preimage_comm)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (leviSp coe_leviSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent mem_unipotent
  exists_sylow_unipotent blockMat blockMat_eq_mul IsUnitriangular isUnitriangular_one)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular mem_unitriangular)

variable {F : Type} [Field F] {r : ℕ}

@[expose] noncomputable def leviSL : SpecialLinearGroup (Fin r) F →* StatedSp r F :=
  leviSp.comp SpecialLinearGroup.toGL

theorem coe_leviSL (A : SpecialLinearGroup (Fin r) F) :
    (((leviSL A : StatedSp r F) : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
      fromBlocks (A : Matrix (Fin r) (Fin r) F) 0 0
        ((A⁻¹ : SpecialLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F)ᵀ := by
  rw [leviSL, MonoidHom.comp_apply, coe_leviSp, ← map_inv]
  rfl

theorem leviSL_injective : Function.Injective (leviSL (F := F) (r := r)) := by
  intro A B h
  have h1 := congrArg (fun g : StatedSp r F => (((g : GL (Fin r ⊕ Fin r) F) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)).toBlocks₁₁) h
  simp only [coe_leviSL, toBlocks_fromBlocks₁₁] at h1
  exact Subtype.ext h1

theorem coe_leviSp_conj (A : GL (Fin r) F) {x : StatedSp r F} {B : Matrix (Fin r) (Fin r) F}
    (hx : ((x : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
      fromBlocks 1 B 0 1) :
    ((leviSp A * x * (leviSp A)⁻¹ : StatedSp r F) : GL (Fin r ⊕ Fin r) F) =
      (fromBlocks 1 ((A : Matrix (Fin r) (Fin r) F) * B * (A : Matrix (Fin r) (Fin r) F)ᵀ) 0 1 :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) := by
  have h1 : (A : Matrix (Fin r) (Fin r) F) * ((A⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((A⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)ᵀ *
      (A : Matrix (Fin r) (Fin r) F)ᵀ = 1 := by
    rw [← transpose_mul, h1, transpose_one]
  rw [← map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_leviSp,
    coe_leviSp, hx, inv_inv, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, h1, h2]

theorem leviSp_conj_mem_siegelRadicalSp (A : GL (Fin r) F) {x : StatedSp r F}
    (hx : x ∈ siegelRadicalSp r F) : leviSp A * x * (leviSp A)⁻¹ ∈ siegelRadicalSp r F := by
  obtain ⟨B, hB, hxB⟩ := mem_siegelRadicalSp.1 hx
  refine mem_siegelRadicalSp.2 ⟨_, ?_, coe_leviSp_conj A hxB⟩
  rw [transpose_mul, transpose_mul, transpose_transpose, hB, Matrix.mul_assoc]

@[expose] noncomputable def leviUnipotent (r : ℕ) (F : Type) [Field F] : Subgroup (StatedSp r F) :=
  (unitriangular r F).map leviSL

theorem siegelRadicalSp_inf_leviUnipotent : siegelRadicalSp r F ⊓ leviUnipotent r F = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hR, A, -, rfl⟩
  obtain ⟨B, -, hB⟩ := mem_siegelRadicalSp.1 hR
  rw [coe_leviSL] at hB
  have h1 := congrArg toBlocks₁₁ hB
  simp only [toBlocks_fromBlocks₁₁] at h1
  have hA : A = 1 := Subtype.ext h1
  rw [hA, map_one]
  exact one_mem _

theorem leviUnipotent_le_normalizer [Finite F] :
    leviUnipotent r F ≤ Subgroup.normalizer (siegelRadicalSp r F : Set (StatedSp r F)) := by
  rintro _ ⟨A, -, rfl⟩
  exact mem_normalizer_of_conj_mem fun x hx => leviSp_conj_mem_siegelRadicalSp _ hx

theorem unipotent_eq_sup : unipotent r F = siegelRadicalSp r F ⊔ leviUnipotent r F := by
  apply le_antisymm
  · rintro g ⟨A, C, hA, hC, hg⟩
    let A' : SpecialLinearGroup (Fin r) F := ⟨A, hA.det_eq_one⟩
    have hA' : A' ∈ unitriangular r F := mem_unitriangular.2 ⟨fun i j hij => hA.1 hij, hA.2⟩
    have hR : (⟨CFSG.RankThree.Classical.siegelGL C,
        CFSG.RankThree.Classical.siegelGL_mem_statedSp hC⟩ : StatedSp r F) ∈
        siegelRadicalSp r F := mem_siegelRadicalSp.2 ⟨C, hC, rfl⟩
    have hg' : g = leviSL A' * ⟨CFSG.RankThree.Classical.siegelGL C,
        CFSG.RankThree.Classical.siegelGL_mem_statedSp hC⟩ := by
      refine Subtype.ext (Units.ext ?_)
      rw [hg, Subgroup.coe_mul, Units.val_mul, coe_leviSL, blockMat_eq_mul]
      congr 2
      change A⁻¹ᵀ = (adjugate A)ᵀ
      rw [inv_def, hA.det_eq_one, Ring.inverse_one, one_smul]
    rw [hg']
    exact mul_mem (Subgroup.mem_sup_right ⟨A', hA', rfl⟩) (Subgroup.mem_sup_left hR)
  · refine sup_le (fun x hx => ?_) ?_
    · obtain ⟨B, hB, hxB⟩ := mem_siegelRadicalSp.1 hx
      refine mem_unipotent.2 ⟨1, B, isUnitriangular_one, hB, ?_⟩
      rw [hxB, blockMat]
      simp
    · rintro _ ⟨A, hA, rfl⟩
      obtain ⟨hA1, hA2⟩ := mem_unitriangular.1 hA
      refine mem_unipotent.2 ⟨A, 0, ⟨fun i j hij => hA1 i j hij, hA2⟩, transpose_zero, ?_⟩
      rw [coe_leviSL, blockMat, Matrix.mul_zero]
      congr 2
      rw [Matrix.SpecialLinearGroup.coe_inv, inv_def, A.2, Ring.inverse_one, one_smul]

theorem subsingleton_specialLinearGroup (hr : r ≤ 1) :
    Subsingleton (SpecialLinearGroup (Fin r) F) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hr with rfl | rfl
  · exact ⟨fun A B => Subtype.ext (Subsingleton.elim _ _)⟩
  · refine ⟨fun A B => Subtype.ext ?_⟩
    ext i j
    fin_cases i
    fin_cases j
    have hA := A.2
    have hB := B.2
    rw [det_fin_one] at hA hB
    exact hA.trans hB.symm

theorem siegelMat_pow (B : Matrix (Fin r) (Fin r) F) (n : ℕ) :
    CFSG.RankThree.Classical.siegelMat B ^ n = CFSG.RankThree.Classical.siegelMat (n • B) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, CFSG.RankThree.Classical.siegelMat_zero]
  | succ n ih => rw [pow_succ, ih, CFSG.RankThree.Classical.siegelMat_mul, succ_nsmul]

theorem coprime_orderOf_leviSp_scalar {p f : ℕ} (hp : p.Prime) [Finite F]
    (hF : Nat.card F = p ^ f) (hf : 1 ≤ f) (τ : Fˣ) :
    Nat.Coprime (orderOf (leviSp (Matrix.GeneralLinearGroup.scalar (Fin r) τ) :
      StatedSp r F)) p := by
  have h1 : orderOf (leviSp (Matrix.GeneralLinearGroup.scalar (Fin r) τ) : StatedSp r F) ∣
      orderOf τ := (orderOf_map_dvd _ _).trans (orderOf_map_dvd _ τ)
  have h2 : orderOf τ ∣ p ^ f - 1 := by
    have := orderOf_dvd_natCard τ
    rwa [Nat.card_units, hF] at this
  refine Nat.Coprime.coprime_dvd_left (h1.trans h2) ?_
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have h1p : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hpq : p ∣ p ^ f := dvd_pow_self p (by omega)
  have h3 : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub hpq hdvd
  rw [show p ^ f - (p ^ f - 1) = 1 by omega] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.1 h3)

theorem leviSp_scalar_conj {τ : Fˣ} {n : ℕ} (hn : (τ : F) ^ 2 = (n : F)) {x : StatedSp r F}
    (hx : x ∈ siegelRadicalSp r F) :
    leviSp (Matrix.GeneralLinearGroup.scalar (Fin r) τ) * x *
      (leviSp (Matrix.GeneralLinearGroup.scalar (Fin r) τ))⁻¹ = x ^ n := by
  obtain ⟨B, hB, hxB⟩ := mem_siegelRadicalSp.1 hx
  refine Subtype.ext (Units.ext ?_)
  rw [coe_leviSp_conj _ hxB, Subgroup.coe_pow, Units.val_pow_eq_pow_val, hxB]
  change _ = CFSG.RankThree.Classical.siegelMat B ^ n
  rw [siegelMat_pow, CFSG.RankThree.Classical.siegelMat, Matrix.GeneralLinearGroup.coe_scalar]
  congr 1
  rw [scalar_apply, diagonal_transpose, ← smul_one_eq_diagonal, Matrix.smul_mul,
    Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, ← pow_two, hn,
    Nat.cast_smul_eq_nsmul]

theorem leviSp_scalar_commute (τ : Fˣ) (A : SpecialLinearGroup (Fin r) F) :
    leviSp (Matrix.GeneralLinearGroup.scalar (Fin r) τ) * leviSL A =
      leviSL A * leviSp (Matrix.GeneralLinearGroup.scalar (Fin r) τ) := by
  have hc : Matrix.GeneralLinearGroup.scalar (Fin r) τ * SpecialLinearGroup.toGL A =
      SpecialLinearGroup.toGL A * Matrix.GeneralLinearGroup.scalar (Fin r) τ := by
    have hz : Matrix.GeneralLinearGroup.scalar (Fin r) τ ∈ Subgroup.center (GL (Fin r) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨τ, rfl⟩
    exact (Subgroup.mem_center_iff.1 hz _).symm
  rw [leviSL, MonoidHom.comp_apply, ← map_mul, hc, map_mul]

theorem symplectic_perfect_ker_eq_bot {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p) [Finite F]
    (hF : Nat.card F = p ^ f) (hf : 1 ≤ f) {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* StatedSp r F) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hCp : IsPGroup p π.ker) : π.ker = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  have hp2 : p ≠ 2 := by omega
  have hp4 : p ≠ 4 := fun h => by
    rw [h] at hp
    exact absurd hp (by decide)
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq F p]; exact hp2)
  obtain ⟨hRel, -⟩ := siegel_radical_sp hp hF r
  have hlift : ∃! β : SpecialLinearGroup (Fin r) F →* E, π.comp β = leviSL := by
    rcases Nat.lt_or_ge r 2 with hr | hr
    · have := subsingleton_specialLinearGroup (F := F) (r := r) (by omega)
      refine ⟨1, MonoidHom.ext fun A => ?_, fun β _ => MonoidHom.ext fun A => ?_⟩
      · rw [Subsingleton.elim A 1, map_one, map_one]
      · rw [Subsingleton.elim A 1, map_one, map_one]
    · exact existsUnique_lift_specialLinear hp hp3 hp (hp.odd_of_ne_two hp2) hf hF hr π hπ hC
        hCp leviSL
  obtain ⟨lh, hlh, hlhu⟩ := hlift
  have hlhA : ∀ A, π (lh A) = leviSL A := fun A => DFunLike.congr_fun hlh A
  have hVhmap : ((unitriangular r F).map lh).map π = leviUnipotent r F := by
    rw [Subgroup.map_map, hlh]
    rfl
  have hVhinj : π.ker ⊓ (unitriangular r F).map lh = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨h1, A, -, rfl⟩
    have hA : A = 1 := leviSL_injective (by rw [← hlhA, MonoidHom.mem_ker.1 h1, map_one])
    rw [hA, map_one]
    exact one_mem _
  obtain ⟨a, ha, hacop⟩ := exists_coprime_lift hp π hπ
    (coprime_orderOf_leviSp_scalar (r := r) hp hF hf (Units.mk0 (2 : F) h2))
  have haV : a ∈ Subgroup.centralizer (((unitriangular r F).map lh : Subgroup E) : Set E) := by
    have hβ : π.comp ((MulAut.conj a).toMonoidHom.comp lh) = leviSL := by
      refine MonoidHom.ext fun A => ?_
      change π (a * lh A * a⁻¹) = leviSL A
      rw [map_mul, map_mul, map_inv, ha, hlhA, leviSp_scalar_commute, mul_inv_cancel_right]
    have hβ' := hlhu _ hβ
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨A, -, rfl⟩
    have h1 : a * lh A * a⁻¹ = lh A := DFunLike.congr_fun hβ' A
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  have h4 : (4 : ZMod p) ≠ 0 := by
    intro h
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) by norm_num, ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have h41 : Units.mk0 (4 : ZMod p) h4 ≠ 1 := by
    intro h
    have h' : ((3 : ℕ) : ZMod p) = 0 := by
      have := congrArg Units.val h
      simp only [Units.val_mk0, Units.val_one] at this
      have h3 : ((3 : ℕ) : ZMod p) = (4 : ZMod p) - 1 := by norm_num
      rw [h3, this, sub_self]
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hval : ((Units.mk0 (4 : ZMod p) h4 : (ZMod p)ˣ) : ZMod p).val = 4 := by
    rw [Units.val_mk0, show (4 : ZMod p) = ((4 : ℕ) : ZMod p) by norm_num, ZMod.val_natCast,
      Nat.mod_eq_of_lt (by omega)]
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := F) p r
  refine ker_eq_bot_of_radical_dilation π hπ hC hCp (siegelRadicalSp r F) (leviUnipotent r F)
    (fun x hx y hy => congrArg Subtype.val (hRel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    hRel.2 (siegel_radical_sp_preimage_comm hp hp3 hF r π hπ hC)
    siegelRadicalSp_inf_leviUnipotent leviUnipotent_le_normalizer
    ⟨P, hP.trans unipotent_eq_sup⟩ _ hVhmap hVhinj a hacop haV (Units.mk0 (4 : ZMod p) h4) h41
    fun x hx => ?_
  rw [ha, hval]
  exact leviSp_scalar_conj (by simp only [Units.val_mk0]; norm_num) hx

theorem ker_comp_subtype_le_center {E S : Type*} [Group E] [Group S] (π : E →* S)
    (hC : π.ker ≤ Subgroup.center E) (D : Subgroup E) :
    (π.comp D.subtype).ker ≤ Subgroup.center D := fun _ hx =>
  Subgroup.mem_center_iff.2 fun y => Subtype.ext (Subgroup.mem_center_iff.1 (hC hx) (y : E))

theorem isPGroup_ker_comp_subtype {E S : Type*} [Group E] [Group S] (π : E →* S) {p : ℕ}
    (hCp : IsPGroup p π.ker) (D : Subgroup E) : IsPGroup p (π.comp D.subtype).ker := by
  refine hCp.of_injective ((D.subtype.comp (π.comp D.subtype).ker.subtype).codRestrict π.ker
    fun y => MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 y.2)) fun x y hxy => ?_
  have h := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext h)

theorem symplectic_defining_splitting {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f)
    [Finite F] (hF : Nat.card F = p ^ f) {E : Type*} [Group E] [Finite E]
    (π : E →* StatedSp r F) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hCp : IsPGroup p π.ker) :
    (∃! s : StatedSp r F →* E, π.comp s = MonoidHom.id _) ∧
      ∀ s : StatedSp r F →* E, π.comp s = MonoidHom.id _ →
        ∃ e : π.ker × s.range ≃* E, ∀ c g, e (c, g) = (c : E) * g := by
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 ≤ p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have : Group.IsPerfect (StatedSp r F) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp r F
      (Or.inl (CFSG.LinearGroups.exists_finset_card_eq_four h4))
  refine splitting_of_perfect_case π hπ hC fun D hD hDs => ?_
  have : Group.IsPerfect D := hD
  exact symplectic_perfect_ker_eq_bot hp hp3 hF hf (π.comp D.subtype) hDs
    (ker_comp_subtype_le_center π hC D) (isPGroup_ker_comp_subtype π hCp D)

end CFSG.RankThree.CentralLift
