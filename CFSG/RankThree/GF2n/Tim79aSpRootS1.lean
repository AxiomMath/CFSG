module

public import CFSG.RankThree.GF2n.Tim79aRootStatements
public import CFSG.Timmesfeld.Transvection.ModelRadical
public import CFSG.Timmesfeld.Transvection.ModelSpGen
public import CFSG.Timmesfeld.Transvection.ModelGeometry

public section

namespace CFSG.RankThree.GF2n.Tim79a

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank

theorem rootS1Model_sp {n : ℕ} {F : Type} [Field F] [CharP F 2] {a : Fin n ⊕ Fin n → F}
    (ha : a ≠ 0) {T : Subgroup (StatedSp n F)} (hT : CFSG.Timmesfeld.ARS.CaseM.IsTransGroup a T) :
    RootS1Model (StatedSp n F) T := by
  intro g hg a' ha' ha'1
  set d := SpExtras.mat n F g *ᵥ a
  have hTg : IsTransGroup d (conjSub T g) := hT.conjSub g
  obtain ⟨c, hc⟩ := (hTg.1 a').1 ha'
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply ha'1
    apply SpExtras.mat_injective
    rw [hc, spTrans_zero, map_one]
  have hβ : spForm a d ≠ 0 := by
    intro h0
    exact hg fun x hx y hy => (hT.commuting hTg h0 x hx y hy).eq
  set β := spForm a d
  set d₁ := β⁻¹ • d with hd₁
  set c₁ := β * β * c with hc₁def
  have hc₁0 : c₁ ≠ 0 := mul_ne_zero (mul_ne_zero hβ hβ) hc0
  have had₁ : spForm a d₁ = 1 := by
    rw [hd₁, spForm_smul_right', inv_mul_cancel₀ hβ]
  have hc₁ : SpExtras.mat n F a' = spTrans d₁ c₁ := by
    rw [hc, hd₁, spTrans_smul, hc₁def]
    congr 1
    field_simp
  set L := spRad a ⊔ Subgroup.zpowers a'
  have hQL : spRad a ≤ L := le_sup_left
  have ha'L : a' ∈ L := Subgroup.mem_sup_right (Subgroup.mem_zpowers a')
  have hTL : T ≤ L := (le_spRad_of_isTransGroup hT).trans hQL
  have h1 : ∀ v, spForm a v = 1 → ∃ t ∈ L, SpExtras.mat n F t = spTrans v c₁ := by
    intro v hv
    obtain ⟨x, hxQ, hxv⟩ := exists_mem_spRad_mulVec_eq had₁ hv
    refine ⟨x * a' * x⁻¹, L.mul_mem (L.mul_mem (hQL hxQ) ha'L) (L.inv_mem (hQL hxQ)), ?_⟩
    rw [mat_conj_of_mat_eq hc₁ x, hxv]
  have h2 : ∀ v, spForm a v = 1 → ∀ X, IsTransGroup v X → X ≤ L := by
    intro v hv X hX
    obtain ⟨t, htL, ht⟩ := h1 v hv
    obtain ⟨s, hs⟩ := hT.2 c₁⁻¹
    have hsL : s ∈ L := hTL ((hT.1 s).2 ⟨c₁⁻¹, hs⟩)
    have hva : spForm v a = -1 := by rw [spForm_comm, hv]
    have hsa : SpExtras.mat n F s *ᵥ a = a := by
      rw [hs, spTrans_mulVec, spForm_self, mul_zero, zero_smul, add_zero]
    have hta : SpExtras.mat n F t *ᵥ a = a - c₁ • v := by
      rw [ht, spTrans_mulVec, hva, mul_neg_one, neg_smul, sub_eq_add_neg]
    have hsv : SpExtras.mat n F s *ᵥ (a - c₁ • v) = (-c₁) • v := by
      rw [hs, spTrans_mulVec, spForm_sub_right, spForm_self, spForm_smul_right', hv, mul_one,
        zero_sub, mul_neg, inv_mul_cancel₀ hc₁0, neg_smul, one_smul, neg_smul]
      abel
    have hW : SpExtras.mat n F (s * t * s) *ᵥ a = (-c₁) • v := by
      rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hsa, hta, hsv]
    have hWX : IsTransGroup v (conjSub T (s * t * s)) := by
      refine IsTransGroup.of_smul (neg_ne_zero.2 hc₁0) ?_
      rw [← hW]
      exact hT.conjSub _
    rw [hX.eq hWX]
    exact conjSub_le hTL (L.mul_mem (L.mul_mem hsL htL) hsL)
  have h3 : ∀ v, spForm a v ≠ 0 → ∀ X, IsTransGroup v X → X ≤ L := by
    intro v hv X hX
    refine h2 ((spForm a v)⁻¹ • v) (by rw [spForm_smul_right', inv_mul_cancel₀ hv]) X ?_
    refine IsTransGroup.of_smul hv ?_
    rwa [smul_smul, mul_inv_cancel₀ hv, one_smul]
  have h4 : ∀ v X, IsTransGroup v X → X ≤ L := by
    intro v X hX
    by_cases hv0 : v = 0
    · intro x hx
      obtain ⟨c', hc'⟩ := (hX.1 x).1 hx
      have hx1 : x = 1 := by
        apply SpExtras.mat_injective
        rw [hc', hv0, map_one, ← smul_zero (0 : F), spTrans_smul, zero_mul, zero_mul,
          spTrans_zero]
      rw [hx1]
      exact L.one_mem
    by_cases hav : spForm a v = 0
    · obtain ⟨y, hay, hvy⟩ := exists_spForm_ne_zero_both ha hv0
      obtain ⟨Y, hY⟩ := ModelRank.exists_isTransGroup y
      obtain ⟨k, hk⟩ := hY.2 1
      have hkL : k ∈ L := h3 y hay Y hY ((hY.1 k).2 ⟨1, hk⟩)
      have hav' : spForm a (SpExtras.mat n F k *ᵥ v) ≠ 0 := by
        rw [hk, spTrans_mulVec, spForm_add_right, hav, zero_add, spForm_smul_right', one_mul]
        refine mul_ne_zero ?_ hay
        rw [spForm_comm]
        exact neg_ne_zero.2 hvy
      have hle := h3 _ hav' _ (hX.conjSub k)
      have hX' : X = conjSub (conjSub X k) k⁻¹ := by
        rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
      rw [hX']
      exact conjSub_le hle (L.inv_mem hkL)
    · exact h3 v hav X hX
  have hLtop : L = ⊤ := eq_top_of_forall_isTransGroup_le h4
  rw [eq_top_iff, ← hLtop]
  exact sup_le_sup_right (spRad_le_pCoreOf ha hT) _

end CFSG.RankThree.GF2n.Tim79a
