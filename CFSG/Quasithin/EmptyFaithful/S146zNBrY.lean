module

public import CFSG.Quasithin.EmptyFaithful.S146zNAmtDef
public import CFSG.Quasithin.Background.F9Tilde

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace CFSG.Quasithin

section Bridge

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
private theorem a6br_conjAct_eq_one_iff {V : Subgroup Y} (g : Subgroup.normalizer (V : Set Y)) :
    conjAct V g = 1 ↔ (g : Y) ∈ Subgroup.centralizer (V : Set Y) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff g

omit [Finite Y] in
private theorem a6br_zpowers_conjAct {V : Subgroup Y} (g : Subgroup.normalizer (V : Set Y)) :
    Subgroup.zpowers (conjAct V g) = autOn (Subgroup.zpowers (g : Y)) V := by
  ext a
  rw [Subgroup.mem_zpowers_iff, mem_autOn_iff]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨g ^ n, ⟨n, by simp⟩, by simp⟩
  · rintro ⟨h, ⟨n, hn⟩, rfl⟩
    refine ⟨n, ?_⟩
    have : h = g ^ n := Subtype.ext (by simpa using hn.symm)
    rw [this, map_zpow]

omit [Finite Y] in
private theorem a6br_rk_autOn {V X : Subgroup Y} (hXn : X ≤ Subgroup.normalizer (V : Set Y)) :
    rk (autOn X V) = mIdx X (X ⊓ Subgroup.centralizer (V : Set Y)) := by
  unfold rk mIdx
  rw [card_autOn_eq_relIndex hXn]

private theorem a6br_rkIdx_fixV_autOn {V X : Subgroup Y} (hV : IsElemAbelian 2 V)
    (hXn : X ≤ Subgroup.normalizer (V : Set Y)) :
    rkIdx (@fixV V (commGroupOfElemAbelian hV) (autOn X V)) =
      mIdx V (V ⊓ Subgroup.centralizer (X : Set Y)) := by
  have hc := card_fixV_autOn_eq hV hXn
  have h1 := Subgroup.index_mul_card (@fixV V (commGroupOfElemAbelian hV) (autOn X V))
  have h2 := Subgroup.relIndex_mul_card (V ⊓ Subgroup.centralizer (X : Set Y)) V
  rw [inf_eq_left.mpr inf_le_left] at h2
  rw [hc] at h1
  have h3 : (@fixV V (commGroupOfElemAbelian hV) (autOn X V)).index =
      (V ⊓ Subgroup.centralizer (X : Set Y)).relIndex V :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)
  unfold rkIdx mIdx
  rw [h3]

theorem a6amt_bridge (hA6 : A6Amt) {V₀ H K X W₁ W₂ : Subgroup Y} {s : Y}
    (hV : IsElemAbelian 2 V₀) (hHV : H ≤ Subgroup.normalizer (V₀ : Set Y))
    (hKH : K ≤ H) (hXH : X ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set Y)) (hsH : s ∈ H)
    (hW₁ : W₁ ≤ V₀) (hW₂ : W₂ ≤ V₀) (hsup : W₁ ⊔ W₂ = V₀)
    (hKW₁ : K ≤ Subgroup.normalizer (W₁ : Set Y)) (hKW₂ : K ≤ Subgroup.normalizer (W₂ : Set Y))
    (hW₂s : W₂ = conjSub s W₁) (hcard : Nat.card W₁ = 16)
    (hirr : ∀ W : Subgroup Y, W ≤ W₁ → K ≤ Subgroup.normalizer (W : Set Y) → W = ⊥ ∨ W = W₁)
    (hL : Nonempty (↥(autOn K V₀) ≃* ↥(alternatingGroup (Fin 6))))
    (hfuse : ∃ x ∈ K, x ^ 3 ∈ Subgroup.centralizer (V₀ : Set Y) ∧
      x ∉ Subgroup.centralizer (V₀ : Set Y) ∧
      ∀ k ∈ K, (k * x * k⁻¹)⁻¹ * (s * x * s⁻¹) ∉ Subgroup.centralizer (V₀ : Set Y))
    (hX : IsElemAbelian 2 X) (hXnt : ¬ X ≤ Subgroup.centralizer (V₀ : Set Y))
    (hquad : ∀ b₁ ∈ X, ∀ b₂ ∈ X, ∀ e ∈ V₀,
      b₂ * (b₁ * e * b₁⁻¹ * e⁻¹) * b₂⁻¹ * (b₁ * e * b₁⁻¹ * e⁻¹)⁻¹ = 1)
    (hr : mIdx V₀ (V₀ ⊓ Subgroup.centralizer (X : Set Y)) ≤
      2 * mIdx X (X ⊓ Subgroup.centralizer (V₀ : Set Y))) :
    mIdx V₀ (V₀ ⊓ Subgroup.centralizer (X : Set Y)) =
        2 * mIdx X (X ⊓ Subgroup.centralizer (V₀ : Set Y)) ∧
      ∃ x ∈ X, mIdx X (X ⊓ Subgroup.centralizer (V₀ : Set Y)) + 2 ≤
        mIdx V₀ (V₀ ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup Y) : Set Y)) := by
  let _ : CommGroup ↥V₀ := commGroupOfElemAbelian hV
  have hXn : X ≤ Subgroup.normalizer (V₀ : Set Y) := hXH.trans hHV
  have hsn : s ∈ Subgroup.normalizer (V₀ : Set Y) := hHV hsH
  have hsq : ∀ v : ↥V₀, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV.2 v v.2)
  have hnormL : ∀ γ ∈ autOn H V₀, ∀ l ∈ autOn K V₀, γ * l * γ⁻¹ ∈ autOn K V₀ := by
    intro γ hγ l hl
    obtain ⟨g, hgH, rfl⟩ := mem_autOn_iff.mp hγ
    obtain ⟨k, hkK, rfl⟩ := mem_autOn_iff.mp hl
    refine mem_autOn_iff.mpr ⟨g * k * g⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hk' : (g : Y) * (k : Y) * (g : Y)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hHK hgH) k).mp hkK
    simpa using hk'
  have hsup' : W₁.subgroupOf V₀ ⊔ W₂.subgroupOf V₀ = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hW₁ hW₂, hsup, Subgroup.subgroupOf_self]
  have hLW₁ : ∀ l ∈ autOn K V₀, ∀ w ∈ W₁.subgroupOf V₀, l w ∈ W₁.subgroupOf V₀ := by
    intro l hl w hw
    obtain ⟨k, hkK, rfl⟩ := mem_autOn_iff.mp hl
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    rw [conjAct_apply_coe']
    exact (Subgroup.mem_normalizer_iff.mp (hKW₁ hkK) w).mp hw
  have hLW₂ : ∀ l ∈ autOn K V₀, ∀ w ∈ W₂.subgroupOf V₀, l w ∈ W₂.subgroupOf V₀ := by
    intro l hl w hw
    obtain ⟨k, hkK, rfl⟩ := mem_autOn_iff.mp hl
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    rw [conjAct_apply_coe']
    exact (Subgroup.mem_normalizer_iff.mp (hKW₂ hkK) w).mp hw
  have hsW : ∀ w : ↥V₀, w ∈ W₂.subgroupOf V₀ ↔
      (conjAct V₀ ⟨s, hsn⟩)⁻¹ w ∈ W₁.subgroupOf V₀ := by
    intro w
    rw [← map_inv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, conjAct_apply_coe', hW₂s,
      mem_conjSub]
    simp
  have hrk : rk (W₁.subgroupOf V₀) = 4 := by
    have hc : Nat.card (W₁.subgroupOf V₀) = 16 := by
      rw [← hcard]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW₁).toEquiv
    unfold rk
    rw [hc, show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat.prime_pow]
  have hirr' : ∀ S : Subgroup ↥V₀, S ≤ W₁.subgroupOf V₀ →
      (∀ l ∈ autOn K V₀, ∀ w ∈ S, l w ∈ S) → S = ⊥ ∨ S = W₁.subgroupOf V₀ := by
    intro S hSW hSinv
    have hSle : S.map V₀.subtype ≤ W₁ := by
      rintro _ ⟨v, hv, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hSW hv)
    have hSn : K ≤ Subgroup.normalizer ((S.map V₀.subtype : Subgroup Y) : Set Y) := by
      intro k hk
      have hkN : k ∈ Subgroup.normalizer (V₀ : Set Y) := hHV (hKH hk)
      have hkN' : k⁻¹ ∈ Subgroup.normalizer (V₀ : Set Y) := inv_mem hkN
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨conjAct V₀ ⟨k, hkN⟩ v,
          hSinv _ (mem_autOn_iff.mpr ⟨⟨k, hkN⟩, hk, rfl⟩) v hv, ?_⟩
        simp [conjAct_apply_coe']
      · rintro ⟨v, hv, hvy⟩
        have hvy' : (v : Y) = k * y * k⁻¹ := hvy
        refine ⟨conjAct V₀ ⟨k⁻¹, hkN'⟩ v,
          hSinv _ (mem_autOn_iff.mpr ⟨⟨k⁻¹, hkN'⟩, inv_mem hk, rfl⟩) v hv, ?_⟩
        simp only [Subgroup.subtype_apply, conjAct_apply_coe', inv_inv]
        rw [hvy']
        group
    rcases hirr _ hSle hSn with h | h
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective S V₀.subtype_injective).mp h)
    · refine Or.inr ?_
      have := congrArg (Subgroup.comap V₀.subtype) h
      rwa [Subgroup.comap_map_eq_self_of_injective V₀.subtype_injective] at this
  have hfuse' : ∃ x ∈ autOn K V₀, x ^ 3 = 1 ∧ x ≠ 1 ∧ ∀ l ∈ autOn K V₀,
      l * x * l⁻¹ ≠ conjAct V₀ ⟨s, hsn⟩ * x * (conjAct V₀ ⟨s, hsn⟩)⁻¹ := by
    obtain ⟨x, hxK, hx3, hx1, hxk⟩ := hfuse
    have hxn : x ∈ Subgroup.normalizer (V₀ : Set Y) := hHV (hKH hxK)
    refine ⟨conjAct V₀ ⟨x, hxn⟩, mem_autOn_iff.mpr ⟨⟨x, hxn⟩, hxK, rfl⟩, ?_, ?_, ?_⟩
    · rw [← map_pow, a6br_conjAct_eq_one_iff]
      simpa using hx3
    · rw [Ne, a6br_conjAct_eq_one_iff]
      exact hx1
    · intro l hl heq
      obtain ⟨k, hkK, rfl⟩ := mem_autOn_iff.mp hl
      refine hxk (k : Y) hkK ?_
      have h1 := (a6br_conjAct_eq_one_iff
        ((k * ⟨x, hxn⟩ * k⁻¹)⁻¹ * (⟨s, hsn⟩ * ⟨x, hxn⟩ * ⟨s, hsn⟩⁻¹))).mp (by
          simp only [map_mul, map_inv]
          rw [heq, inv_mul_cancel])
      simpa using h1
  have hA2 : IsA2 (autOn H V₀) (autOn X V₀) :=
    ⟨autOn_le_autOn V₀ hXH, autOn_ne_bot_of_not_le_centralizer hXn hXnt,
      isElemAbelian2_autOn hV hX hXn⟩
  have hcs : commSeries (autOn X V₀) 2 = ⊥ :=
    (isQuadratic_iff_commSeries_two _).mp (isQuadratic_autOn_of_forall hV hquad)
  have hr' : rkIdx (fixV (autOn X V₀)) ≤ 2 * rk (autOn X V₀) := by
    rw [a6br_rkIdx_fixV_autOn hV hXn, a6br_rk_autOn hXn]
    exact hr
  obtain ⟨hA1, a, haA, ha⟩ := hA6 ↥V₀ hsq (autOn H V₀) (autOn K V₀) (W₁.subgroupOf V₀)
    (W₂.subgroupOf V₀) (conjAct V₀ ⟨s, hsn⟩) (autOn_le_autOn V₀ hKH) hnormL
    (mem_autOn_iff.mpr ⟨⟨s, hsn⟩, hsH, rfl⟩) hsup' hLW₁ hLW₂ hsW hrk hirr' hL hfuse'
    (autOn X V₀) hA2 hcs hr'
  rw [a6br_rkIdx_fixV_autOn hV hXn, a6br_rk_autOn hXn] at hA1
  refine ⟨hA1, ?_⟩
  obtain ⟨g, hgX, rfl⟩ := mem_autOn_iff.mp haA
  refine ⟨(g : Y), hgX, ?_⟩
  rw [a6br_rk_autOn hXn] at ha
  unfold A6Rank at ha
  rw [a6br_zpowers_conjAct, a6br_rkIdx_fixV_autOn hV (Subgroup.zpowers_le.mpr g.2)] at ha
  exact ha

end Bridge

end CFSG.Quasithin
