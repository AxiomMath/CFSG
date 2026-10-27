module

public import CFSG.RankThree.GF2n.Stroth80.Sec79OmegaFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec78OmegaA2Conj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped Matrix

section UBound

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]
  {Q : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}

theorem polar_eichlerG_ne_zero {u w v : ι → K} (hu : Q u = 0) (hw : polar Q u w = 0)
    (hQw : Q w ≠ 0) (hv : polar Q v u ≠ 0) : polar Q v ((eichlerG Q u w).app v) ≠ 0 := by
  show polar Q v (eichler Q u w v) ≠ 0
  rw [polar_apply_eichler_self hu hw v, CharTwo.two_eq_zero, zero_mul, zero_sub]
  exact neg_ne_zero.mpr (mul_ne_zero hQw (pow_ne_zero 2 hv))

theorem uBound_of_c2 (E : ElemMatrixIso Q X) (hQ : (polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ Fintype.card ι) {R : Type*} [Group R] (φ : R →* GL ι K) (hφ : φ.range = X)
    {Y : Type*} [AddCommGroup Y] [Finite Y] [DistribMulAction R Y] (h2 : ∀ a : Y, a + a = 0)
    (hker : ∀ r ∈ φ.ker, ∀ a : Y, r • a = a) {u u' : ι → K} (hu : Q u = 0) (hu' : Q u' = 0)
    (huu' : polar Q u u' ≠ 0) {L₁ L₂ : Subgroup R} (hL₁ : L₁.map φ = E.LomGL u)
    (hL₂ : L₂.map φ = E.LomGL u')
    (hdec : IsCompl (fixedSub Y (L₁ : Set R)) (fixedSub Y (L₂ : Set R))) {y : R} (hy : y ∈ L₁)
    (hn : ∃ v : ι → K, polar Q v ((φ y : Matrix ι ι K) *ᵥ v) ≠ 0) :
    (comm Y y).range = fixedSub Y (L₁ : Set R) ∧
      Nat.card Y = Nat.card (fixedSub Y (L₁ : Set R)) ^ 2 := by
  have huu'' : polar Q u' u ≠ 0 := by rwa [polar_comm]
  obtain ⟨-, h2', h3'⟩ := stroth_2_1_ii_omega_fixed_of_hom E φ hφ hQ h2 hker hu' hu huu'' hL₂ hL₁
    hdec.symm h4 hy hn
  exact ⟨h2', h3'⟩

theorem card_sup_le_mul {Y : Type*} [AddCommGroup Y] [Finite Y] (A B : AddSubgroup Y) :
    Nat.card ↥(A ⊔ B) ≤ Nat.card ↥A * Nat.card ↥B := by
  have hs : Function.Surjective (fun p : ↥A × ↥B =>
      (⟨(p.1 : Y) + (p.2 : Y), AddSubgroup.mem_sup.mpr ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩ :
        ↥(A ⊔ B))) := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have := Nat.card_le_card_of_surjective _ hs
  rwa [Nat.card_prod] at this

theorem uBound (E : ElemMatrixIso Q X)
    (hQ : (polarBilin Q).Nondegenerate) (h6 : 6 ≤ Fintype.card ι) {R : Type*} [Group R]
    (φ : R →* GL ι K) (hφ : φ.range = X) {Y : Type*} [AddCommGroup Y] [Finite Y]
    [DistribMulAction R Y] (h2 : ∀ a : Y, a + a = 0) (hker : ∀ r ∈ φ.ker, ∀ a : Y, r • a = a)
    {u u' : ι → K} (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0)
    {L₁ L₂ : Subgroup R} (hL₁ : L₁.map φ = E.LomGL u) (hL₂ : L₂.map φ = E.LomGL u')
    (hdec : IsCompl (fixedSub Y (L₁ : Set R)) (fixedSub Y (L₂ : Set R))) {y : R} (hy : y ∈ L₁)
    (hy1 : φ y ≠ 1) : Nat.card Y ≤ Nat.card ↥(comm Y y).range ^ 4 := by
  classical
  have h4 : 4 ≤ Fintype.card ι := by omega
  have huu'' : polar Q u' u ≠ 0 := by rwa [polar_comm]
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact huu' (by simp)
  have hc0 : 0 < Nat.card ↥(comm Y y).range := Nat.card_pos
  set Φ := viaMatrix X E.equiv φ hφ with hΦ
  have hΦapp : ∀ (r : R) (v : ι → K), (Φ r).app v = (φ r : Matrix ι ι K) *ᵥ v :=
    fun r v => viaMatrix_app E φ hφ r v
  have hΦy : Φ y ∈ Lom Q u := by
    have h1 : φ y ∈ E.LomGL u := by
      rw [← hL₁]
      exact Subgroup.mem_map_of_mem φ hy
    obtain ⟨hA, hmem⟩ := mem_matrixOf_iff.1 h1
    exact hmem
  have hΦy1 : Φ y ≠ 1 := by
    intro h
    apply hy1
    have h' : y ∈ (viaMatrix X E.equiv φ hφ).ker := h
    rw [ker_viaMatrix] at h'
    exact h'
  obtain ⟨w, hw, hxw⟩ := mem_rootGroup.mp hΦy
  have hx' : Φ y = eichlerG Q u w := Subtype.ext hxw.symm
  by_cases hQw : Q w = 0
  ·
    have hli : LinearIndependent K ![u, w] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      by_cases ht : t = 0
      · subst ht
        rw [zero_smul, add_zero] at hst
        exact ⟨(smul_eq_zero.mp hst).resolve_right hu0, rfl⟩
      · exfalso
        apply hΦy1
        have hw' : w = (-(s / t)) • u := by
          have h1 : t • w = -(s • u) := eq_neg_of_add_eq_zero_right hst
          have h2 : w = t⁻¹ • (t • w) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          rw [h2, h1, smul_neg, smul_smul, ← neg_smul]
          congr 1
          field_simp
        rw [hx', hw', ← zero_add ((-(s / t)) • u), eichlerG_add_smul_self hu, eichlerG_zero]
    obtain ⟨h, hhu, hQh⟩ := omegaA2Conj_holds K (ι → K) Q hQ (by simpa using h6) u w hu hw hQw hli
    obtain ⟨r', hr'⟩ := viaMatrix_surjective φ hφ h
    have hhw : polar Q u (h.app w) = 0 := by
      have := Gom.polar_app h u w
      rwa [hhu, hw] at this
    set y' : R := r' * y * r'⁻¹ with hy'
    have hΦy' : Φ y' = eichlerG Q u (h.app w) := by
      rw [hy', map_mul, map_mul, map_inv, hr', hx', eichlerG_conj, hhu]
    set yh : R := y * y' with hyh
    have hΦyh : Φ yh = eichlerG Q u (w + h.app w) := by
      rw [hyh, map_mul, hΦy', hx', eichlerG_mul hw hhw]
    have hmem : φ yh ∈ E.LomGL u := by
      rw [ElemMatrixIso.LomGL]
      refine mem_matrixOf_iff.2 ⟨hφ ▸ MonoidHom.mem_range.mpr ⟨yh, rfl⟩, ?_⟩
      have := hΦyh
      rw [viaMatrix_apply] at this
      rw [this]
      exact eichlerG_mem_Lom (by rw [polar_add_right, hw, hhw, add_zero])
    rw [← hL₁] at hmem
    obtain ⟨l, hl, hlyh⟩ := Subgroup.mem_map.mp hmem
    have hlker : l⁻¹ * yh ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hlyh, inv_mul_cancel]
    have hact : ∀ a : Y, yh • a = l • a := by
      intro a
      have := hker _ hlker a
      rw [mul_smul, inv_smul_eq_iff] at this
      exact this
    have hΦl : Φ l = eichlerG Q u (w + h.app w) := by
      rw [← hΦyh]
      have : l⁻¹ * yh ∈ (viaMatrix X E.equiv φ hφ).ker := by
        rw [ker_viaMatrix]
        exact hlker
      rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at this
      exact this
    have hn : ∃ v : ι → K, polar Q v ((φ l : Matrix ι ι K) *ᵥ v) ≠ 0 := by
      refine ⟨u', ?_⟩
      rw [← hΦapp, hΦl]
      exact polar_eichlerG_ne_zero hu (by rw [polar_add_right, hw, hhw, add_zero]) hQh huu''
    obtain ⟨-, hl2⟩ := uBound_of_c2 E hQ h4 φ hφ h2 hker hu hu' huu' hL₁ hL₂ hdec hl hn
    obtain ⟨hl1, -⟩ := uBound_of_c2 E hQ h4 φ hφ h2 hker hu hu' huu' hL₁ hL₂ hdec hl hn
    have hrange : (comm Y l).range ≤ (comm Y y).range ⊔ (comm Y y').range := by
      rintro _ ⟨a, rfl⟩
      rw [comm_apply, ← hact, hyh, mul_smul]
      have e : y • y' • a - a = (y • (y' • a) - y' • a) + (y' • a - a) := by abel
      rw [e]
      exact AddSubgroup.add_mem_sup ⟨y' • a, by rw [comm_apply]⟩ ⟨a, by rw [comm_apply]⟩
    have hrange' : (comm Y y').range ≤
        (comm Y y).range.map (DistribSMul.toAddMonoidHom Y r') := by
      rintro _ ⟨a, rfl⟩
      refine AddSubgroup.mem_map.mpr ⟨comm Y y (r'⁻¹ • a), ⟨_, rfl⟩, ?_⟩
      show r' • (y • r'⁻¹ • a - r'⁻¹ • a) = y' • a - a
      simp only [smul_sub, smul_smul, mul_inv_cancel, one_smul, hy', mul_assoc]
    have hcard' : Nat.card ↥(comm Y y').range ≤ Nat.card ↥(comm Y y).range := by
      refine (AddSubgroup.card_le_of_le hrange').trans ?_
      rw [AddSubgroup.card_map_of_injective (f := DistribSMul.toAddMonoidHom Y r')
        (MulAction.injective r')]
    have hcardsup : Nat.card ↥((comm Y y).range ⊔ (comm Y y').range) ≤
        Nat.card ↥(comm Y y).range ^ 2 :=
      (card_sup_le_mul _ _).trans (by rw [pow_two]; exact Nat.mul_le_mul le_rfl hcard')
    have hC₁ : Nat.card ↥(fixedSub Y (L₁ : Set R)) ≤ Nat.card ↥(comm Y y).range ^ 2 := by
      rw [← hl1]
      exact (AddSubgroup.card_le_of_le hrange).trans hcardsup
    calc Nat.card Y = Nat.card ↥(fixedSub Y (L₁ : Set R)) ^ 2 := hl2
      _ ≤ (Nat.card ↥(comm Y y).range ^ 2) ^ 2 := Nat.pow_le_pow_left hC₁ 2
      _ = Nat.card ↥(comm Y y).range ^ 4 := by ring
  ·
    have hn : ∃ v : ι → K, polar Q v ((φ y : Matrix ι ι K) *ᵥ v) ≠ 0 := by
      refine ⟨u', ?_⟩
      rw [← hΦapp, hx']
      exact polar_eichlerG_ne_zero hu hw hQw huu''
    obtain ⟨h2', h3'⟩ := uBound_of_c2 E hQ h4 φ hφ h2 hker hu hu' huu' hL₁ hL₂ hdec hy hn
    rw [h3', ← h2']
    exact Nat.pow_le_pow_right hc0 (by norm_num)

end UBound

end CFSG.RankThree.GF2n.Stroth80
