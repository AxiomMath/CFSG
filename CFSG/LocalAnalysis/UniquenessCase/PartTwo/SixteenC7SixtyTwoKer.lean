module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoSyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section SylowBar

theorem s16c7_isSylowOf_barSub {p : ℕ} [Fact p.Prime] (V₀ V : Subgroup G)
    (hV : IsElemAbelian 2 V) {P K : Subgroup G} (h : CFSG.ABGLocalTools.IsSylowOf p P K)
    (hK : K ≤ stabTil V₀ V) :
    CFSG.ABGLocalTools.IsSylowOf p (barSub V₀ V hV P) (barSub V₀ V hV K) := by
  have hP : P ≤ stabTil V₀ V := h.le.trans hK
  have h1 : CFSG.ABGLocalTools.IsSylowOf p (P.subgroupOf (stabTil V₀ V))
      (K.subgroupOf (stabTil V₀ V)) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (stabTil V₀ V),
      Subgroup.map_subgroupOf_eq_of_le hP, Subgroup.map_subgroupOf_eq_of_le hK]
    exact h
  exact s16c7_isSylowOf_map h1 (actTil V₀ V hV)

theorem s16c7_eq_map_conj {A B : Subgroup G} {a : G} (h : ∀ x : G, x ∈ B ↔ a⁻¹ * x * a ∈ A) :
    B = A.map (MulAut.conj a).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨a⁻¹ * x * a, (h x).1 hx, ?_⟩
    show a * (a⁻¹ * x * a) * a⁻¹ = x
    group
  · rintro ⟨y, hy, rfl⟩
    rw [h]
    have : a⁻¹ * (MulAut.conj a).toMonoidHom y * a = y := by
      show a⁻¹ * (a * y * a⁻¹) * a = y
      group
    rw [this]
    exact hy

theorem s16c7_exists_lift_sylow {p : ℕ} [Fact p.Prime] (V₀ V : Subgroup G)
    (hV : IsElemAbelian 2 V) {K : Subgroup G} (hK : K ≤ stabTil V₀ V)
    {Xb : Subgroup (MulAut (Vtil V₀ V hV))}
    (hXb : CFSG.ABGLocalTools.IsSylowOf p Xb (barSub V₀ V hV K)) :
    ∃ X : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p X K ∧ barSub V₀ V hV X = Xb := by
  obtain ⟨X₁, hX₁⟩ := CFSG.ABGLocalTools.exists_isSylowOf p K
  have h1 := s16c7_isSylowOf_barSub V₀ V hV hX₁ hK
  obtain ⟨a, ha, hconj⟩ := h1.exists_mem_conj hXb
  obtain ⟨l, hlK, rfl⟩ := (mem_barSub V₀ V hV K a).1 ha
  refine ⟨X₁.map (MulAut.conj (l : G)).toMonoidHom, s16c7_isSylowOf_conj hX₁ hlK, ?_⟩
  rw [s16c7_barSub_map_conj V₀ V hV l.2 X₁]
  exact (s16c7_eq_map_conj hconj).symm

end SylowBar

section Kernel

theorem s16c7_card_eq_inf_centralizer_mul (V : Subgroup G) (hV : IsElemAbelian 2 V)
    {E : Subgroup G} (hE : E ≤ stabTil ⊥ V) :
    Nat.card E = Nat.card ↥(E ⊓ centralizer (V : Set G)) * Nat.card (barSub ⊥ V hV E) := by
  have h := s16c7_card_mul_card_preBarSub (V₀ := ⊥) (V := V) (E := E) hV hE
    (Q := ⊥) bot_le
  have hpre : preBarSub E ⊥ V hV ⊥ = E ⊓ centralizer (V : Set G) := by
    ext g
    rw [mem_preBarSub, Subgroup.mem_inf]
    constructor
    · rintro ⟨hgE, hgs, h1⟩
      exact ⟨hgE,
        (s16c7_actTil_eq_one_iff_mem_centralizer V hV ⟨g, hgs⟩).1 (Subgroup.mem_bot.1 h1)⟩
    · rintro ⟨hgE, hgc⟩
      have hgs : g ∈ stabTil ⊥ V := hE hgE
      exact ⟨hgE, hgs, Subgroup.mem_bot.2
        ((s16c7_actTil_eq_one_iff_mem_centralizer V hV ⟨g, hgs⟩).2 hgc)⟩
  rw [hpre, Subgroup.card_bot, mul_one] at h
  exact h

theorem s16c7_isPGroup_two_inf_centralizer (V : Subgroup G) (hV : IsElemAbelian 2 V)
    {K₁ K₂ : Subgroup G} (h₁₂ : K₁ ≤ normalizer (K₂ : Set G)) (hs : K₁ ⊔ K₂ ≤ stabTil ⊥ V)
    (hA : Nat.card (barSub ⊥ V hV (K₁ ⊔ K₂)) = 168 * 168) {a b : ℕ}
    (h₁ : Nat.card K₁ = 2 ^ a * 168) (h₂ : Nat.card K₂ = 2 ^ b * 168) :
    IsPGroup 2 ↥((K₁ ⊔ K₂) ⊓ centralizer (V : Set G)) := by
  have e1 := s16c7_card_eq_inf_centralizer_mul V hV hs
  have e2 := s16c7_card_sup_mul_card_inf h₁₂
  rw [hA] at e1
  rw [h₁, h₂] at e2
  have h3 : Nat.card ↥((K₁ ⊔ K₂) ⊓ centralizer (V : Set G)) * Nat.card ↥(K₁ ⊓ K₂) =
      2 ^ (a + b) := by
    have h4 : (Nat.card ↥((K₁ ⊔ K₂) ⊓ centralizer (V : Set G)) * Nat.card ↥(K₁ ⊓ K₂)) *
        (168 * 168) = 2 ^ (a + b) * (168 * 168) := by
      calc (Nat.card ↥((K₁ ⊔ K₂) ⊓ centralizer (V : Set G)) * Nat.card ↥(K₁ ⊓ K₂)) *
            (168 * 168)
          = (Nat.card ↥((K₁ ⊔ K₂) ⊓ centralizer (V : Set G)) * (168 * 168)) *
              Nat.card ↥(K₁ ⊓ K₂) := by ring
        _ = Nat.card ↥(K₁ ⊔ K₂) * Nat.card ↥(K₁ ⊓ K₂) := by rw [← e1]
        _ = 2 ^ a * 168 * (2 ^ b * 168) := e2
        _ = 2 ^ (a + b) * (168 * 168) := by ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h4
  have h5 : Nat.card ↥((K₁ ⊔ K₂) ⊓ centralizer (V : Set G)) ∣ 2 ^ (a + b) := Dvd.intro _ h3
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h5
  exact IsPGroup.of_card hk

theorem s16c7_inf_centralizer_le {V L M T : Subgroup G} (hLM : L ≤ M)
    (hML : M ≤ normalizer (L : Set G)) (hMV : M ≤ normalizer (V : Set G))
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hp : IsPGroup 2 ↥(L ⊓ centralizer (V : Set G))) : L ⊓ centralizer (V : Set G) ≤ T := by
  refine le_trans (s16c7_le_pCoreOf (inf_le_left.trans hLM) ?_ hp)
    (s16c7_pCoreOf_le_of_isSylowOf hT)
  intro m hm x hx
  obtain ⟨hxL, hxc⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.1 (hML hm) x).1 hxL
  · rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : m⁻¹ * v * m ∈ V := by
      have := (Subgroup.mem_normalizer_iff.1 ((normalizer (V : Set G)).inv_mem (hMV hm)) v).1 hv
      simpa using this
    have h1 : (m⁻¹ * v * m) * x = x * (m⁻¹ * v * m) := (Subgroup.mem_centralizer_iff.1 hxc) _ hv'
    calc v * (m * x * m⁻¹) = m * ((m⁻¹ * v * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * v * m)) * m⁻¹ := by rw [h1]
      _ = m * x * m⁻¹ * v := by group

end Kernel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
