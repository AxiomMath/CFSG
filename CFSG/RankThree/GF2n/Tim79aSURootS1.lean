module

public import CFSG.Timmesfeld.Transvection.ModelSUTransitive
public import CFSG.Timmesfeld.Transvection.ModelRankSU

public section

namespace CFSG.RankThree.GF2n.Tim79a

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed
  CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank

theorem uRad_sup_zpowers_eq_top_of_involutive {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}
    (hσ : ∀ c, σ (σ c) = c) {m : ℕ}
    (hG : ∀ L : Subgroup (SU σ m), (∀ (v : Fin m → F) (X : Subgroup (SU σ m)),
      uForm σ v v = 0 → IsUTransGroup σ v X → X ≤ L) → L = ⊤)
    (hB : SUBothStmt σ m) {a : Fin m → F} (ha : a ≠ 0) (haa : uForm σ a a = 0)
    {T : Subgroup (SU σ m)} (hT : IsUTransGroup σ a T) {g : SU σ m}
    (hg : ¬ Commuting T (conjSub T g)) {x : SU σ m} (hx : x ∈ conjSub T g) (hx1 : x ≠ 1) :
    uRad σ a ⊔ Subgroup.zpowers x = ⊤ := by
  have h1tr : (1 : F) + σ 1 = 0 := by rw [map_one, CharTwo.add_self_eq_zero]
  set d := suMat σ m g *ᵥ a
  have hTg : IsUTransGroup σ d (conjSub T g) := hT.conjSub g
  have hdd : uForm σ d d = 0 := (uForm_mulVec σ g a a).trans haa
  obtain ⟨c, hc, hxc⟩ := (hTg.1 x).1 hx
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hx1
    apply suMat_injective σ
    rw [hxc, uTrans_zero, map_one]
  have hβ : uForm σ a d ≠ 0 := fun h0 => hg (hT.commuting hσ hTg h0)
  set β := uForm σ a d
  set d₁ := β⁻¹ • d with hd₁
  set c₁ := β * σ β * c with hc₁def
  have hc₁ : c₁ + σ c₁ = 0 := traceZero_mul_norm hσ β hc
  have hc₁0 : c₁ ≠ 0 := mul_ne_zero (mul_ne_zero hβ ((map_ne_zero σ).2 hβ)) hc0
  have hc₁inv : c₁⁻¹ + σ c₁⁻¹ = 0 := by
    have hneg : σ c₁ = -c₁ := by linear_combination hc₁
    rw [map_inv₀, hneg, inv_neg, add_neg_cancel]
  have had₁ : uForm σ a d₁ = 1 := by rw [hd₁, uForm_smul_right, inv_mul_cancel₀ hβ]
  have hd₁d₁ : uForm σ d₁ d₁ = 0 := by
    rw [hd₁, uForm_smul_left, uForm_smul_right, hdd, mul_zero, mul_zero]
  have hxc₁ : suMat σ m x = uTrans σ d₁ c₁ := by
    rw [hxc, hd₁, hc₁def, ← uTrans_smul, smul_smul, mul_inv_cancel₀ hβ, one_smul]
  set L := uRad σ a ⊔ Subgroup.zpowers x
  have hQL : uRad σ a ≤ L := le_sup_left
  have hxL : x ∈ L := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hTL : T ≤ L := (le_uRad_of_isUTransGroup haa hT).trans hQL
  have h1 : ∀ v, uForm σ v v = 0 → uForm σ a v = 1 →
      ∃ t ∈ L, suMat σ m t = uTrans σ v c₁ := by
    intro v hvv hv
    obtain ⟨y, hyQ, hyv⟩ := exists_mem_uRad_mulVec_eq hσ haa hd₁d₁ hvv had₁ hv
    refine ⟨y * x * y⁻¹, L.mul_mem (L.mul_mem (hQL hyQ) hxL) (L.inv_mem (hQL hyQ)), ?_⟩
    rw [suMat_conj_of_eq σ hxc₁ y, hyv]
  have h2 : ∀ v, uForm σ v v = 0 → uForm σ a v = 1 → ∀ X, IsUTransGroup σ v X → X ≤ L := by
    intro v hvv hv X hX
    obtain ⟨t, htL, ht⟩ := h1 v hvv hv
    obtain ⟨s, hs⟩ := hT.2 c₁⁻¹ hc₁inv
    have hsL : s ∈ L := hTL ((hT.1 s).2 ⟨c₁⁻¹, hc₁inv, hs⟩)
    have hva : uForm σ v a = 1 := by rw [← uForm_conj σ hσ, hv, map_one]
    have hsa : suMat σ m s *ᵥ a = a := by
      rw [hs, uTrans_mulVec, haa, mul_zero, zero_smul, add_zero]
    have hta : suMat σ m t *ᵥ a = a + c₁ • v := by
      rw [ht, uTrans_mulVec, hva, mul_one]
    have hsv : suMat σ m s *ᵥ (a + c₁ • v) = c₁ • v := by
      rw [hs, uTrans_mulVec, uForm_add_right, haa, uForm_smul_right, hv, zero_add, mul_one,
        inv_mul_cancel₀ hc₁0, one_smul]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination a i * (CharTwo.two_eq_zero : (2 : F) = 0)
    have hW : suMat σ m (s * t * s) *ᵥ a = c₁ • v := by
      rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hsa, hta, hsv]
    have hWX : IsUTransGroup σ v (conjSub T (s * t * s)) := by
      refine IsUTransGroup.of_smul hσ hc₁0 ?_
      rw [← hW]
      exact hT.conjSub _
    rw [hX.eq hWX]
    exact conjSub_le hTL (L.mul_mem (L.mul_mem hsL htL) hsL)
  have h3 : ∀ v, uForm σ v v = 0 → uForm σ a v ≠ 0 → ∀ X, IsUTransGroup σ v X → X ≤ L := by
    intro v hvv hv X hX
    refine h2 ((uForm σ a v)⁻¹ • v) ?_ (by rw [uForm_smul_right, inv_mul_cancel₀ hv]) X ?_
    · rw [uForm_smul_left, uForm_smul_right, hvv, mul_zero, mul_zero]
    · refine IsUTransGroup.of_smul hσ hv ?_
      rwa [smul_smul, mul_inv_cancel₀ hv, one_smul]
  refine hG L fun v X hvv hX => ?_
  by_cases hv0 : v = 0
  · intro y hy
    obtain ⟨c', -, hc'⟩ := (hX.1 y).1 hy
    have hy1 : y = 1 := by
      apply suMat_injective σ
      rw [hc', hv0, map_one, uTrans, uNil, zero_vecMulVec, smul_zero, add_zero]
    rw [hy1]
    exact L.one_mem
  by_cases hav : uForm σ a v = 0
  · obtain ⟨y, hyy, hay, hvy⟩ := hB ha hv0 haa hvv
    obtain ⟨Y, hY⟩ := exists_isUTransGroup hσ hyy
    obtain ⟨k, hk⟩ := hY.2 1 h1tr
    have hkL : k ∈ L := h3 y hyy hay Y hY ((hY.1 k).2 ⟨1, h1tr, hk⟩)
    have hkv : uForm σ (suMat σ m k *ᵥ v) (suMat σ m k *ᵥ v) = 0 :=
      (uForm_mulVec σ k v v).trans hvv
    have hav' : uForm σ a (suMat σ m k *ᵥ v) ≠ 0 := by
      rw [hk, uTrans_mulVec, uForm_add_right, hav, zero_add, uForm_smul_right, one_mul]
      refine mul_ne_zero ?_ hay
      rw [← uForm_conj σ hσ v y]
      exact (map_ne_zero σ).2 hvy
    have hle := h3 _ hkv hav' _ (hX.conjSub k)
    have hX' : X = conjSub (conjSub X k) k⁻¹ := by
      rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
    rw [hX']
    exact conjSub_le hle (L.inv_mem hkL)
  · exact h3 v hvv hav X hX

theorem uRad_sup_zpowers_eq_top {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {m : ℕ} (hG : SUGenStmt F f m)
    (hP : SUPartnerStmt (unitaryInvolution F 2 f) m)
    (hB : SUBothStmt (unitaryInvolution F 2 f) m)
    {a : Fin m → F} (ha : a ≠ 0) (haa : uForm (unitaryInvolution F 2 f) a a = 0)
    {T : Subgroup (SU (unitaryInvolution F 2 f) m)}
    (hT : IsUTransGroup (unitaryInvolution F 2 f) a T)
    {g : SU (unitaryInvolution F 2 f) m} (hg : ¬ Commuting T (conjSub T g))
    {x : SU (unitaryInvolution F 2 f) m} (hx : x ∈ conjSub T g) (hx1 : x ≠ 1) :
    uRad (unitaryInvolution F 2 f) a ⊔ Subgroup.zpowers x = ⊤ :=
  uRad_sup_zpowers_eq_top_of_involutive (unitaryInvolution_involutive hF) (fun _ hL => hG hL) hB
    ha haa hT hg hx hx1

end CFSG.RankThree.GF2n.Tim79a
