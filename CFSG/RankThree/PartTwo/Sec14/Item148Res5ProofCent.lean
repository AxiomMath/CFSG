module

public import CFSG.GH74.GLS.IVK.L2.Fixed
import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSubfieldCore
import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob
public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofFieldTools
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec14

namespace Item148Res5

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.GH74.GLS.IVK (fixedField)
open Matrix

section Fixed

theorem card_eqLocus_quotient_le {S : Type*} [Group S] [Finite S] {Z : Subgroup S} [Z.Normal]
    (hZ : Z ≤ Subgroup.center S) (φ : S →* S) (ψ : S ⧸ Z →* S ⧸ Z)
    (hψ : ∀ s : S, ψ (s : S ⧸ Z) = ((φ s : S) : S ⧸ Z)) :
    Nat.card (ψ.eqLocus (MonoidHom.id (S ⧸ Z))) ≤ Nat.card (φ.eqLocus (MonoidHom.id S)) := by
  set F := ψ.eqLocus (MonoidHom.id (S ⧸ Z)) with hF
  set T := φ.eqLocus (MonoidHom.id S) with hT
  set St := F.comap (QuotientGroup.mk' Z) with hSt
  have hmem : ∀ s : S, s ∈ St → s⁻¹ * φ s ∈ Z := by
    intro s hs
    have h1 : ψ (s : S ⧸ Z) = (s : S ⧸ Z) := hs
    rw [hψ] at h1
    exact QuotientGroup.eq.mp h1.symm
  have hcomm : ∀ z ∈ Z, ∀ g : S, g * z = z * g := fun z hz g =>
    Subgroup.mem_center_iff.mp (hZ hz) g
  let f : St →* Z :=
    { toFun := fun s => ⟨(s : S)⁻¹ * φ s, hmem s s.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev]
        have h := hcomm _ (hmem a a.2) (b : S)⁻¹
        calc (b : S)⁻¹ * (a : S)⁻¹ * (φ a * φ b) = ((b : S)⁻¹ * ((a : S)⁻¹ * φ a)) * φ b := by
              group
          _ = (((a : S)⁻¹ * φ a) * (b : S)⁻¹) * φ b := by rw [h]
          _ = (a : S)⁻¹ * φ a * ((b : S)⁻¹ * φ b) := by group }
  have h1 : Nat.card St = Nat.card f.range * Nat.card f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have h2 : Nat.card f.range ≤ Nat.card Z := Subgroup.card_le_card_group _
  have h3 : Nat.card f.ker ≤ Nat.card T := by
    refine Nat.card_le_card_of_injective (fun s => ⟨((s : St) : S), ?_⟩) ?_
    · have hs := s.2
      rw [MonoidHom.mem_ker] at hs
      have h0 : ((s : St) : S)⁻¹ * φ s = 1 := congrArg Subtype.val hs
      exact (inv_mul_eq_one.mp h0).symm
    · intro a b hab
      have h := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
  have hidx : St.index = F.index :=
    Subgroup.index_comap_of_surjective F (QuotientGroup.mk'_surjective Z)
  have h4 : Nat.card St * St.index = Nat.card S := Subgroup.card_mul_index St
  have h5 : Nat.card F * F.index = Nat.card (S ⧸ Z) := Subgroup.card_mul_index F
  have h6 : Nat.card S = Nat.card (S ⧸ Z) * Nat.card Z :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  have hpos : 0 < F.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have h7 : Nat.card St = Nat.card F * Nat.card Z := by
    have e : Nat.card St * St.index = Nat.card F * Nat.card Z * St.index := by
      rw [h4, h6, ← h5, hidx]
      ring
    exact Nat.eq_of_mul_eq_mul_right (hidx ▸ hpos) e
  have h8 : Nat.card F * Nat.card Z ≤ Nat.card T * Nat.card Z := by
    rw [← h7, h1, mul_comm (Nat.card T)]
    exact Nat.mul_le_mul h2 h3
  exact Nat.le_of_mul_le_mul_right h8 hZpos

end Fixed

section Field

theorem card_eqLocus_fieldAut_le {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    Nat.card ((fieldAut 3 K σ).toMonoidHom.eqLocus (MonoidHom.id (projectiveSL 3 K))) ≤
      Nat.card (SpecialLinearGroup (Fin 3) (fixedField σ)) := by
  have hc := card_eqLocus_quotient_le (scalars_le_center 3 K)
    (SpecialLinearGroup.map σ.toRingHom) (fieldAut 3 K σ).toMonoidHom
    (fun s => fieldAut_proj σ s)
  refine hc.trans ?_
  have hle : (SpecialLinearGroup.map σ.toRingHom).eqLocus
      (MonoidHom.id (SpecialLinearGroup (Fin 3) K)) ≤
        (SpecialLinearGroup.map (n := Fin 3) (fixedField σ).subtype).range := by
    intro A hA
    obtain ⟨A₀, hA₀⟩ := exists_sl_map_subtype_eq (σ := σ) hA
    exact ⟨A₀, hA₀⟩
  calc _ ≤ Nat.card (SpecialLinearGroup.map (n := Fin 3) (fixedField σ).subtype).range :=
        Subgroup.card_le_of_le hle
    _ = _ := (Nat.card_congr (MonoidHom.ofInjective (sl_map_subtype_injective σ)).toEquiv).symm

theorem card_eqLocus_psuField_le {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {σ : K ≃+* K} {f₀ : ℕ} (hf : f = 3 * f₀) (h₀ : UnitaryFieldData p f₀ (fixedField σ)) :
    Nat.card ((psuField h σ).toMonoidHom.eqLocus (MonoidHom.id (unitaryPSU h 3))) ≤
      Nat.card (unitarySU p f₀ (fixedField σ) 3) := by
  have := h.finite
  have hc := card_eqLocus_quotient_le (unitaryScalars_le_center h 3)
    (suField h σ).toMonoidHom (psuField h σ).toMonoidHom (fun s => psuField_mk σ s)
  refine hc.trans (le_of_eq ?_)
  have hbar := bar_coe_fixedField h hf h₀
  have heq : (suField h σ).toMonoidHom.eqLocus (MonoidHom.id (unitarySU p f K 3)) =
      (suIncl h h₀ hbar).range := by
    ext g
    rw [mem_range_suIncl_iff h h₀ hbar g]
    rfl
  rw [heq]
  exact (Nat.card_congr (MonoidHom.ofInjective (suIncl_injective h h₀ hbar)).toEquiv).symm

end Field

section Unitary

theorem exists_cube_of_pow_three_eq_one_of_nine_dvd {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {m : ℕ} (hm : m ∣ Nat.card G) (h9 : 9 ∣ m) {ε : G} (hε : ε ^ 3 = 1) :
    ∃ ν : G, ν ^ m = 1 ∧ ν ^ 3 = ε := by
  obtain ⟨k, rfl⟩ := h9
  refine Item148Rank.exists_cube_of_pow_div_three148 hm ⟨3 * k, by ring⟩ ?_
  rw [show 9 * k / 3 = 3 * k by omega, pow_mul, hε, one_pow]

theorem isInnerAut_of_psuConj_fix_involution {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (h9 : 9 ∣ 2 ^ f + 1) {A : unitaryIsom3 h}
    (hA3 : psuConj h A ^ 3 = 1) {x : unitaryPSU h 3} (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1)
    (hfix : psuConj h A x = x) : KFacts.IsInnerAut (psuConj h A) := by
  classical
  have := h.finite
  have : CharP K 2 := h.charP
  obtain ⟨-, u, -, hu⟩ := eq_one_of_psuConj_mul_psuField_eq_one (A ^ 3) 1
    (by rw [map_one, mul_one, map_pow, hA3])
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
  rw [psuConj_mk] at hfix
  obtain ⟨c, -, hc3, hc⟩ := QuotientGroup.eq.mp hfix
  have hs2 : (s ^ 2 : unitarySU 2 f K 3) ∈ unitaryScalars h 3 := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hx2
  obtain ⟨d, -, hd3, hd⟩ := hs2
  set S : Matrix (Fin 3) (Fin 3) K := ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hS
  set M : Matrix (Fin 3) (Fin 3) K := ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  set Mi : Matrix (Fin 3) (Fin 3) K := (((A : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) with hMi
  have hMiM : Mi * M = 1 := by rw [hM, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hMMi : M * Mi = 1 := by rw [hM, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hconj : M * S * Mi = scalar (Fin 3) ((c⁻¹ : Kˣ) : K) * S := by
    have hc' : ((((suConj h A s)⁻¹ * s : unitarySU 2 f K 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) (c : K) := by
      rw [hc, GeneralLinearGroup.coe_scalar]
    have hC : (((suConj h A s : unitarySU 2 f K 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = M * S * Mi := by
      rw [coe_suConj]
      rfl
    have hCi : ((((suConj h A s)⁻¹ : unitarySU 2 f K 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * (M * S * Mi) = 1 := by
      rw [← hC, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
        Units.val_one]
    have hsplit : ((((suConj h A s)⁻¹ * s : unitarySU 2 f K 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ((((suConj h A s)⁻¹ : unitarySU 2 f K 3) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) * S := by
      rw [Subgroup.coe_mul, Units.val_mul]
    have hSeq : S = (M * S * Mi) * scalar (Fin 3) (c : K) := by
      rw [← hc', hsplit, ← Matrix.mul_assoc, (mul_eq_one_comm.mp hCi), Matrix.one_mul]
    have hsc1 : scalar (Fin 3) (c : K) * scalar (Fin 3) ((c⁻¹ : Kˣ) : K) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    calc M * S * Mi = (M * S * Mi) * scalar (Fin 3) (c : K) *
          scalar (Fin 3) ((c⁻¹ : Kˣ) : K) := by rw [Matrix.mul_assoc _ (scalar _ _), hsc1,
            Matrix.mul_one]
      _ = S * scalar (Fin 3) ((c⁻¹ : Kˣ) : K) := by rw [← hSeq]
      _ = scalar (Fin 3) ((c⁻¹ : Kˣ) : K) * S :=
        ((scalar_commute _ (fun _ => Commute.all _ _) S).eq).symm
  have hS2 : S * S = scalar (Fin 3) (d : K) := by
    have h1 : (((s ^ 2 : unitarySU 2 f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        S * S := by
      rw [pow_two, Subgroup.coe_mul, Units.val_mul]
    rw [← h1, hd, GeneralLinearGroup.coe_scalar]
  have hc3' : ((c⁻¹ : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, inv_pow, hc3, inv_one, Units.val_one]
  have hd3' : (d : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hd3, Units.val_one]
  set t : Matrix (Fin 3) (Fin 3) K := S * S * S with ht
  have htt : t * t = 1 := by
    have e : t * t = (S * S) * (S * S) * (S * S) := by
      rw [ht]
      noncomm_ring
    rw [e, hS2, ← map_mul, ← map_mul, ← pow_three', hd3', map_one]
  have ht1 : t ≠ 1 := by
    intro h1
    apply hx1
    have hs3 : s ^ 3 = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, pow_three, ← Matrix.mul_assoc]
      exact h1
    have h3 : ((s : unitaryPSU h 3)) ^ 3 = 1 := by rw [← QuotientGroup.mk_pow, hs3]; rfl
    calc (s : unitaryPSU h 3) = (s : unitaryPSU h 3) ^ 3 * ((s : unitaryPSU h 3) ^ 2)⁻¹ := by
          group
      _ = 1 := by rw [h3, hx2, inv_one, one_mul]
  have hMt : M * t = t * M := by
    set B := scalar (Fin 3) ((c⁻¹ : Kˣ) : K) with hB
    have hBS : B * S = S * B := (scalar_commute _ (fun _ => Commute.all _ _) S).eq
    have hBBB : B * B * B = 1 := by
      rw [hB, ← map_mul, ← map_mul, ← pow_three', hc3', map_one]
    have hMS : M * S = B * S * M := by
      rw [← hconj, Matrix.mul_assoc (M * S), hMiM, Matrix.mul_one]
    have hSB : ∀ X : Matrix (Fin 3) (Fin 3) K, S * (B * X) = B * (S * X) := fun X => by
      rw [← Matrix.mul_assoc, ← hBS, Matrix.mul_assoc]
    calc M * t = M * S * S * S := by rw [ht]; simp only [Matrix.mul_assoc]
      _ = B * S * M * S * S := by rw [hMS]
      _ = B * S * (M * S) * S := by simp only [Matrix.mul_assoc]
      _ = B * S * (B * S * M) * S := by rw [hMS]
      _ = B * S * B * S * (M * S) := by simp only [Matrix.mul_assoc]
      _ = B * S * B * S * (B * S * M) := by rw [hMS]
      _ = (B * B * B) * t * M := by
          rw [ht]
          simp only [Matrix.mul_assoc, hSB]
      _ = t * M := by rw [hBBB, Matrix.one_mul]
  have hM3 : M ^ 3 = scalar (Fin 3) (u : K) := by
    have h1 : (((A ^ 3 : unitaryIsom3 h) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = M ^ 3 := by
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    rw [← h1, hu, GeneralLinearGroup.coe_scalar]
  obtain ⟨μ, hμ⟩ := Sec19.Item19Res2Proof.exists_cube_of_commute_involution hM3 htt ht1 hMt
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hμ
    exact u.ne_zero hμ.symm
  set μ' : Kˣ := Units.mk0 μ hμ0 with hμ'
  have hμ'3 : μ' ^ 3 = u := Units.ext (by rw [Units.val_pow_eq_pow_val, hμ', Units.val_mk0, hμ])
  have hK : Sec4.PiField false 2 f K :=
    ⟨Nat.prime_two, h.one_le, by rw [h.card, Sec4.piCard, Bool.cond_false, ← pow_mul,
      mul_comm]⟩
  have hq : Sec4.ModThree false (2 ^ f) := by
    change 2 ^ f % 3 = 2
    omega
  obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
  have hAH : (A : GL (Fin 3) K) ∈ Sec4.glPi false 3 (2 ^ f) K := (Sec4.mem_glPi_false h).mpr A.2
  by_cases hAs : (A : GL (Fin 3) K) ∈ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K
  ·
    obtain ⟨c₀, hc₀⟩ := hAs
    have hA' : A = ⟨GeneralLinearGroup.scalar (Fin 3) c₀, hc₀ ▸ A.2⟩ := Subtype.ext hc₀.symm
    rw [hA', psuConj_scalar]
    exact ⟨1, map_one _⟩
  have hA3' : (A : GL (Fin 3) K) ^ 3 = GeneralLinearGroup.scalar (Fin 3) (μ' ^ 3) := by
    rw [hμ'3, ← hu, Subgroup.coe_pow]
  obtain ⟨y, ⟨z, hz, rfl⟩, g, -, hdiag⟩ :=
    Sec4.exists_diag_normal_form hK hq hτ hτ1 hAH hAs hA3'
  rw [Sec4.zPi_eq (fun _ => h) (fun _ => hq) hτ hτ1] at hz
  obtain ⟨hzH, ζ, rfl⟩ := hz
  have hζ : ζ ^ (2 ^ f + 1) = 1 := by
    have h1 := (Sec4.mem_glPi_false h).mp hzH
    have h2 := congrFun (congrFun h1 0) 0
    rw [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_map (map_zero h.bar),
      diagonal_transpose, diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq,
      UnitaryFieldData.bar_apply] at h2
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ]
    exact h2
  have hdet3 : (GeneralLinearGroup.det ((A : GL (Fin 3) K) *
      GeneralLinearGroup.scalar (Fin 3) ζ)) ^ 3 = 1 := by
    have e1 : ∀ w : GL (Fin 3) K, GeneralLinearGroup.det w =
        GeneralLinearGroup.det (g⁻¹ * w * g) := fun w => by
      rw [map_mul, map_mul, map_inv, mul_comm _ (GeneralLinearGroup.det g), ← mul_assoc,
        mul_inv_cancel, one_mul]
    rw [e1]
    rcases hdiag with hd' | ⟨e, he, hd'⟩
    · rw [hd']
      apply Units.ext
      have hdt : (!![τ, 0, 0; 0, τ ^ 2, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K).det = τ ^ 3 := by
        rw [Matrix.det_fin_three]
        simp
        ring
      rw [Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, Sec4.coe_diagTau, hdt, hτ,
        one_pow, Units.val_one]
    · rw [hd']
      apply Units.ext
      have hde : (diagonal ![(e : K), 1, 1]).det = e := by
        rw [det_diagonal, Fin.prod_univ_three]
        simp
      rw [Units.val_pow_eq_pow_val, GeneralLinearGroup.val_det_apply, Sec4.coe_diagE, hde,
        Units.val_one]
      rcases he with he | he <;> rw [he]
      · exact hτ
      · rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hτ, one_pow]
  set ε := GeneralLinearGroup.det ((A : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) ζ)
    with hε
  have hcardU : 2 ^ f + 1 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card]
    refine ⟨2 ^ f - 1, ?_⟩
    obtain ⟨r, hr⟩ : ∃ r, 2 ^ f = r + 1 :=
      ⟨2 ^ f - 1, by have := Nat.one_le_two_pow (n := f); omega⟩
    rw [pow_mul', hr, Nat.add_sub_cancel]
    have : (r + 1) ^ 2 = (r + 1 + 1) * r + 1 := by ring
    omega
  obtain ⟨ν, hν1, hν3⟩ := exists_cube_of_pow_three_eq_one_of_nine_dvd hcardU h9 hdet3
  have hdetz : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 3) ζ : GL (Fin 3) K) =
      ζ ^ 3 := Item148Rank.det_scalar_three148 ζ
  refine Item148Rank.isInnerAut_psuConj_of_det_eq_cube148 A (u := ν * ζ⁻¹) ?_ ?_
  · rw [mul_pow, hν3, hε, map_mul, hdetz, inv_pow, mul_inv_cancel_right]
  · rw [mul_pow, hν1, inv_pow, hζ, inv_one, one_mul]

end Unitary

section Model

theorem nine_dvd_of_two_pow_three_mul (n : ℕ) :
    (2 ^ (3 * n) % 3 = 1 → 9 ∣ 2 ^ (3 * n) - 1) ∧
      (2 ^ (3 * n) % 3 = 2 → 9 ∣ 2 ^ (3 * n) + 1) := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have h : 2 ^ (3 * (m + m)) = 64 ^ m := by
      rw [show 3 * (m + m) = 6 * m by ring, pow_mul]
      norm_num
    have h9 : 64 ^ m % 9 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have h3 : 64 ^ m % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    rw [h]
    exact ⟨fun _ => Nat.dvd_of_mod_eq_zero (by omega), fun h2 => absurd h2 (by omega)⟩
  · have h : 2 ^ (3 * (2 * m + 1)) = 8 * 64 ^ m := by
      rw [show 3 * (2 * m + 1) = 6 * m + 3 by ring, pow_add, pow_mul]
      norm_num
      ring
    have h9 : 64 ^ m % 9 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    rw [h]
    exact ⟨fun h1 => absurd h1 (by omega), fun _ => Nat.dvd_of_mod_eq_zero (by omega)⟩

theorem two_dvd_card_of_isoLThreePi {Y : Type} [Group Y] {n : ℕ} (hn : 1 ≤ n)
    (hY : Sec4.IsoLThreePi Y 2 n) : 2 ∣ Nat.card Y := by
  have h2 : 2 ∣ (2 ^ n) ^ 3 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
  rcases hY with ⟨-, ⟨eY⟩⟩ | ⟨-, ⟨eY⟩⟩
  · have h1 := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 n)
    rw [GaloisField.card 2 n (by omega)] at h1
    rw [Nat.card_congr eY.toEquiv]
    have hcop : Nat.Coprime 2 (Nat.gcd 3 (2 ^ n - 1)) :=
      Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) (by norm_num)
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [h1]
    exact dvd_mul_of_dvd_left h2 _
  · have h1 := KFacts.KS14.card_projSU_three_mul_gcd 2 n hn
    rw [Nat.card_congr eY.toEquiv]
    have hcop : Nat.Coprime 2 (Nat.gcd 3 (2 ^ n + 1)) :=
      Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _) (by norm_num)
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [h1]
    exact dvd_mul_of_dvd_left h2 _

end Model

end Item148Res5

open Item148Res5

end CFSG.RankThree.PartTwo.Sec14
