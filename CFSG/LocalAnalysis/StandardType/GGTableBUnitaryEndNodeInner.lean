module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeElt
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagUnitary
public import CFSG.LocalAnalysis.StandardType.GGStdSubExistDefs
import CFSG.RankThree.PartOne.S15K.CentralCover

public section

namespace CFSG.StandardType

namespace TableBUE

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.RankThree.Classical2

section General

theorem center_eq_bot_of_simple {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center Q := by rw [h]; exact Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab

theorem ggEndNode_of_pow_eq_one {p r : ℕ} {R : Type} [Group R] {I I' : Set (MulAut R)}
    (h : GGEndNode p r R I') (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ I') : GGEndNode p r R I := by
  intro L' _ _ ψ hψ hker hL A hA hAI hr h3
  refine h L' ψ hψ hker hL A hA (fun a ha => ?_) hr h3
  obtain ⟨φ, hφ, hφa⟩ := hAI a ha
  refine ⟨φ, hI φ hφ ?_, hφa⟩
  have hk : ∀ k : ℕ, ∀ l : L', (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
    intro k
    induction k with
    | zero => intro l; rfl
    | succ k ih =>
      intro l
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφa, ih]
  ext x
  obtain ⟨l, rfl⟩ := hψ x
  rw [hk p l, hA.2 a ha, MulAut.one_apply, MulAut.one_apply]

end General

section Unitary

variable {K : Type} [Field K] [Finite K] {n d p : ℕ} (h : UnitaryFieldData 2 n K)

omit [Finite K] in
include h in
theorem gu_subset_normalizer :
    LargeEvenGUSet (Fin d) K (2 ^ n) ⊆
      Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K)) := by
  have : CharP K 2 := h.charP
  set σ := iterateFrobenius K 2 n with hσdef
  have hσ : ∀ x, σ x = x ^ 2 ^ n := iterateFrobenius_def 2 n
  have hm : ∀ M : Matrix (Fin d) (Fin d) K, M.map (· ^ 2 ^ n) = M.map σ := fun M => by
    ext i j
    simp [hσ]
  have hSU : LargeEvenSUGroup (Fin d) K (2 ^ n) = Subgroup.closure (TableB.suGens σ) := by
    unfold LargeEvenSUGroup TableB.suGens
    simp only [hm]
  intro A hA
  obtain ⟨μ, hμ0, -, hA⟩ := hA
  rw [hSU]
  exact TableB.mem_normalizer_closure_suGens ⟨μ, hμ0, by rw [← hm]; exact hA⟩

omit [Finite K] in
include h in
theorem diagHom_mem_unitarySU {t : Fin d → Kˣ} (ht : ∀ k, t k ^ (2 ^ n + 1) = 1)
    (hprod : ∏ k, t k = 1) : diagHom d t ∈ unitarySU 2 n K d := by
  rw [mem_unitarySU_iff h, det_diagHom, coe_diagHom]
  refine ⟨by rw [← Units.coe_prod, hprod, Units.val_one], ?_⟩
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext k
  rw [UnitaryFieldData.bar_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, ht k, Units.val_one]

omit [Finite K] in
include h in
theorem mem_scalars_of_commute (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) {N : GL (Fin d) K}
    (hN : ∀ g ∈ unitarySU 2 n K d, N * g = g * N) : N ∈ LargeEvenScalars (Fin d) K := by
  classical
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one h.one_le hpq
  obtain ⟨ζ, hζo, hζq⟩ := exists_orderOf_eq_norm_one h hp hpq
  have hζ2 : ζ ≠ ζ⁻¹ := by
    intro he
    have h1 : ζ ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [he]; exact mul_inv_cancel ζ
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hζo] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hdiag : (N : Matrix (Fin d) (Fin d) K).IsDiag := by
    intro i j hij
    set t : Fin d → Kˣ := Pi.mulSingle i ζ * Pi.mulSingle j ζ⁻¹ with ht
    have hti : t i = ζ := by simp [ht, hij]
    have htj : t j = ζ⁻¹ := by simp [ht, Ne.symm hij]
    have htmem : diagHom d t ∈ unitarySU 2 n K d := by
      refine diagHom_mem_unitarySU h (fun k => ?_) ?_
      · simp only [ht, Pi.mul_apply, Pi.mulSingle_apply]
        split_ifs <;> simp [hζq, inv_pow]
      · simp only [ht, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
        exact mul_inv_cancel ζ
    refine entry_eq_zero_of_commute (hN _ htmem) ?_
    rw [hti, htj]
    exact hζ2
  obtain ⟨β, hβ⟩ := exists_diagHom_of_isDiag hdiag
  have hconst : ∀ i j, β i = β j := by
    intro i j
    have hw := hN _ (permGL_swap_mem h i j)
    rw [hβ] at hw
    have h1 := permGL_mul_diagHom_mul_inv (K := K) (Equiv.swap i j) β
    rw [← hw, mul_inv_cancel_right] at h1
    have h2 := congrFun (diagHom_injective d h1) j
    rw [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_right] at h2
    exact h2.symm
  rcases isEmpty_or_nonempty (Fin d) with hd | ⟨⟨i₀⟩⟩
  · refine ⟨1, Units.ext ?_⟩
    ext i
    exact isEmptyElim i
  · refine ⟨β i₀, ?_⟩
    rw [hβ]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, coe_diagHom, Matrix.scalar_apply]
    congr 1
    funext k
    rw [hconst k i₀]

include h in
theorem mem_range_conj_of_pow_eq_one (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d)
    {φ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenGUSet (Fin d) K (2 ^ n)))
    (hφp : φ ^ p = 1) :
    φ ∈ Set.range (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) →*
      MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := LargeEvenSUGroup (Fin d) K (2 ^ n) with hH
  have hHu : H = unitarySU 2 n K d := rfl
  have hN := gu_subset_normalizer (d := d) h
  obtain ⟨A, hA, rfl⟩ := TableB.exists_eq_projConj hN hφ
  set Nn : Subgroup.normalizer (H : Set (GL (Fin d) K)) := ⟨A, hN hA⟩ with hNn
  have hperf : Group.IsPerfect H :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK hd hdq
  have hker : (LargeEvenProjMk H).ker ≤ Subgroup.center H := ker_projMk_le_center
  have hcomm : ∀ g ∈ unitarySU 2 n K d, A ^ p * g = g * A ^ p := by
    intro g hg
    have key := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq (LargeEvenProjMk H) hker hperf
      (H.normalizerMonoidHom (Nn ^ p)).toMonoidHom (MonoidHom.id H) (fun u => by
        have h1 := congrArg (fun ψ : MulAut (LargeEvenProj H) => ψ (LargeEvenProjMk H u))
          (show TableB.projConj H (Nn ^ p) = 1 by rw [map_pow]; exact hφp)
        exact h1) ⟨g, hg⟩
    have h2 := congrArg Subtype.val key
    change (A ^ p : GL (Fin d) K) * g * (A ^ p)⁻¹ = g at h2
    calc A ^ p * g = A ^ p * g * (A ^ p)⁻¹ * A ^ p := by group
      _ = g * A ^ p := by rw [h2]
  obtain ⟨c, hc⟩ := mem_scalars_of_commute h hp hpq hcomm
  obtain ⟨μ, hμ0, hμq, hAμ⟩ := hA
  obtain ⟨l, hl⟩ := TableB.exists_norm_eq (q := 2 ^ n) (by
    have := Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp h.one_le); omega) hK hμ0 hμq
  set B := Matrix.GeneralLinearGroup.scalar (Fin d) l⁻¹ * A with hB
  have hbar : ∀ M : Matrix (Fin d) (Fin d) K, M.map h.bar = M.map (· ^ 2 ^ n) := fun M => by
    ext i j
    rfl
  have hAμ' : ((A : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (A : Matrix (Fin d) (Fin d) K) =
      μ • 1 := by rw [hbar]; exact hAμ
  have hBu : ((B : Matrix (Fin d) (Fin d) K).map h.bar)ᵀ * (B : Matrix (Fin d) (Fin d) K) = 1 := by
    rw [hB, TableB.coe_scalar_mul, TableB.transpose_map_smul, Matrix.smul_mul, Matrix.mul_smul,
      hAμ', smul_smul, smul_smul, UnitaryFieldData.bar_apply, ← hl]
    have hinv : ((l⁻¹ : Kˣ) : K) * (l : K) = 1 := Units.inv_mul l
    have h0 : ((l⁻¹ : Kˣ) : K) ^ 2 ^ n * ((l⁻¹ : Kˣ) : K) * (l : K) ^ (2 ^ n + 1) = 1 := by
      calc ((l⁻¹ : Kˣ) : K) ^ 2 ^ n * ((l⁻¹ : Kˣ) : K) * (l : K) ^ (2 ^ n + 1) =
            (((l⁻¹ : Kˣ) : K) * l) ^ 2 ^ n * (((l⁻¹ : Kˣ) : K) * l) := by ring
        _ = 1 := by rw [hinv, one_pow, one_mul]
    rw [h0, one_smul]
  have hBU : B ∈ UnitaryHigher.primeFormUnitary h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K d) := by
    rw [UnitaryHigher.mem_primeFormUnitary, CFSG.RankThree.PartOne.KCUnitaryModel.idGram,
      Units.val_one, Matrix.mul_one]
    exact hBu
  set c₁ : Kˣ := l⁻¹ ^ p * c with hc₁
  have hBp : B ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) c₁ := by
    have hcomm' : Commute (Matrix.GeneralLinearGroup.scalar (Fin d) l⁻¹) A :=
      (Subgroup.mem_center_iff.mp (TableB.scalar_mem_center (ι := Fin d) l⁻¹) A).symm
    rw [hB, hcomm'.mul_pow, ← map_pow, ← hc, hc₁, map_mul]
  have hd0 : NeZero d := ⟨by omega⟩
  have hc₁q : c₁ ^ (2 ^ n + 1) = 1 := by
    have h1 : B ^ p ∈ UnitaryHigher.primeFormUnitary h
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K d) := Subgroup.pow_mem _ hBU p
    rw [hBp, UnitaryHigher.mem_primeFormUnitary, CFSG.RankThree.PartOne.KCUnitaryModel.idGram,
      Units.val_one, Matrix.mul_one] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_map
      (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, Matrix.one_apply_eq, UnitaryFieldData.bar_apply] at h2
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ]
    exact h2
  set δ : Kˣ := Matrix.GeneralLinearGroup.det B with hδ
  have hδq : δ ^ (2 ^ n + 1) = 1 := by
    apply Units.ext
    have h1 := congrArg Matrix.det hBu
    rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      Matrix.det_one, UnitaryFieldData.bar_apply] at h1
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, hδ,
      Matrix.GeneralLinearGroup.val_det_apply]
    exact h1
  have hδp : δ ^ p = c₁ ^ d := by
    have h1 := congrArg Matrix.GeneralLinearGroup.det hBp
    rw [map_pow] at h1
    rw [hδ, h1]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Units.val_pow_eq_pow_val]
  have hgcd : Nat.gcd d p = 1 := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd)
  set a := Nat.gcdA d p with ha
  set b := Nat.gcdB d p with hb
  have hab : (d : ℤ) * a + (p : ℤ) * b = 1 := by
    have := Nat.gcd_eq_gcd_ab d p
    rw [hgcd] at this
    exact_mod_cast this.symm
  set s : Kˣ := δ ^ a * c₁ ^ b with hs
  have hsd : s ^ d = δ := by
    have h1 : c₁ ^ ((d : ℤ) * b) = δ ^ ((p : ℤ) * b) := by
      rw [_root_.zpow_mul, _root_.zpow_mul, zpow_natCast, zpow_natCast, hδp]
    calc s ^ d = s ^ (d : ℤ) := (zpow_natCast s d).symm
      _ = δ ^ ((d : ℤ) * a) * c₁ ^ ((d : ℤ) * b) := by
        rw [hs, mul_zpow, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm a, mul_comm b]
      _ = δ ^ ((d : ℤ) * a + (p : ℤ) * b) := by rw [h1, _root_.zpow_add]
      _ = δ := by rw [hab, zpow_one]
  have hsq : s ^ (2 ^ n + 1) = 1 := by
    rw [hs, mul_pow, ← zpow_natCast, ← zpow_natCast (c₁ ^ b), ← _root_.zpow_mul, ← _root_.zpow_mul,
      mul_comm a, mul_comm b, _root_.zpow_mul, _root_.zpow_mul, zpow_natCast, zpow_natCast, hδq,
      hc₁q,
      _root_.one_zpow, _root_.one_zpow, mul_one]
  set B' := Matrix.GeneralLinearGroup.scalar (Fin d) s⁻¹ * B with hB'
  have hB'mem : B' ∈ unitarySU 2 n K d := by
    rw [mem_unitarySU_iff h]
    refine ⟨?_, ?_⟩
    · rw [← Matrix.GeneralLinearGroup.val_det_apply, hB', map_mul, ← hδ]
      have h1 : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin d) s⁻¹) =
          (s ^ d)⁻¹ := by
        apply Units.ext
        rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_scalar,
          Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, ← Units.val_pow_eq_pow_val, inv_pow]
      rw [h1, hsd, inv_mul_cancel, Units.val_one]
    · rw [hB', TableB.coe_scalar_mul, TableB.transpose_map_smul, Matrix.smul_mul,
        Matrix.mul_smul, hBu, smul_smul, UnitaryFieldData.bar_apply]
      have h2 : ((s⁻¹ : Kˣ) : K) ^ 2 ^ n * ((s⁻¹ : Kˣ) : K) = 1 := by
        rw [← pow_succ, ← Units.val_pow_eq_pow_val, inv_pow, hsq, inv_one, Units.val_one]
      rw [h2, one_smul]
  have hA_eq : A = Matrix.GeneralLinearGroup.scalar (Fin d) (l * s) * B' := by
    rw [hB', hB, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_assoc l,
      mul_inv_cancel, mul_one, mul_inv_cancel, map_one, one_mul]
  have hsplit : Nn = ⟨Matrix.GeneralLinearGroup.scalar (Fin d) (l * s),
      TableB.scalar_mem_normalizer H ⟨l * s, rfl⟩⟩ * ⟨B', Subgroup.le_normalizer hB'mem⟩ := by
    apply Subtype.ext
    rw [hNn]
    exact hA_eq
  refine ⟨((⟨B', hB'mem⟩ : H) : LargeEvenProj H), ?_⟩
  rw [hsplit, map_mul, TableB.projConj_of_scalar H ⟨l * s, rfl⟩, one_mul,
    TableB.projConj_of_mem H B' hB'mem]

theorem center_proj_eq_bot (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d)
    (hdq : (d, 2 ^ n) ≠ (3, 2)) :
    Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq, hcen⟩ :=
    CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) hK hd hdq
  obtain ⟨-, hsimple, hnab⟩ := hq
  have e₀ := QuotientGroup.quotientMulEquivOfEq hcen
  have e : ↥(CFSG.Assembly.LowTwoRank.StatedSU d (2 ^ n) K) ⧸
      Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSU d (2 ^ n) K) ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)) := e₀
  have hbot := center_eq_bot_of_simple hnab
  rw [eq_bot_iff]
  intro x hx
  have hx' : e.symm x ∈ Subgroup.center (↥(CFSG.Assembly.LowTwoRank.StatedSU d (2 ^ n) K) ⧸
      Subgroup.center ↥(CFSG.Assembly.LowTwoRank.StatedSU d (2 ^ n) K)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.symm.surjective g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx) y]
  rw [hbot, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hx'
  rw [hx']
  exact Subgroup.one_mem _

include h in
theorem ggEndNodeAdm_unitary (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : ¬ p ∣ d) (hq : 2 < 2 ^ n ∨ 6 ≤ d) :
    GGEndNodeAdm p (d - 2) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro he
    have h1 : d = 3 := congrArg Prod.fst he
    have h2 : 2 ^ n = 2 := congrArg Prod.snd he
    omega
  apply ggEndNodeAdm_of_ggEndNode
  refine ggEndNode_of_pow_eq_one (I' := Set.range MulAut.conj) ?_
    fun φ hφ hφp => mem_range_conj_of_pow_eq_one h hK hd hdq hp hpq hpd hφ hφp
  exact ggEndNode_of_elt subset_rfl (center_proj_eq_bot hK hd hdq)
    (ggEndNodeElt_unitary h hK hp hpq hpd hd hq)

end Unitary

end TableBUE

end CFSG.StandardType
