module

public import CFSG.Quasithin.EmptyFaithful.LRed10Pair
public import CFSG.Quasithin.EmptyFaithful.Insp9QS
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace Insp9

section B56QS

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem commV_bot' : commV (⊥ : Subgroup (MulAut W)) = ⊥ :=
  CFSG.Quasithin.LRed10.commV_bot

omit [Finite W] in
theorem sub_central_or_eq {G A : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥G) (hAG : A ≤ G)
    (hn : G ≤ Subgroup.normalizer (A : Set (MulAut W))) :
    (∀ a ∈ A, ∀ g ∈ G, a * g = g * a) ∨ A = G := by
  have hN : (A.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAG).mpr hn
  rcases qs_normal_le_center_or_top hq (A.subgroupOf G) with h | h
  · left
    intro a ha g hg
    have := Subgroup.mem_center_iff.mp (h (show (⟨a, hAG ha⟩ : ↥G) ∈ A.subgroupOf G from ha))
      ⟨g, hg⟩
    have h2 := congrArg Subtype.val this
    simpa using h2.symm
  · right
    exact le_antisymm hAG (Subgroup.subgroupOf_eq_top.mp h)

omit [Finite W] in
theorem not_both_central {G A B : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥G)
    (hAB : A ⊔ B = G) (hA : ∀ a ∈ A, ∀ g ∈ G, a * g = g * a)
    (hB : ∀ b ∈ B, ∀ g ∈ G, b * g = g * b) : False := by
  have hle : A ⊔ B ≤ Subgroup.centralizer (G : Set (MulAut W)) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun g hg => (hA a ha g hg).symm
    · exact Subgroup.mem_centralizer_iff.mpr fun g hg => (hB b hb g hg).symm
  rw [hAB] at hle
  apply qs_not_commutative hq
  intro x y
  have := hle x.2 y.1 y.2
  exact Subtype.ext (by simpa using this.symm)

theorem b56QL_of_factorList {X : Type} [Group X] (hq : CFSG.IsQuasisimple X)
    (h : B56FactorList X) : B56QuasisimpleList X := by
  rcases h with ⟨n, K, _, _, -, hK, he⟩ | he | ⟨m, K, _, _, -, -, hK, he⟩
  · exact Or.inl ⟨n, K, inferInstance, inferInstance, hK, he⟩
  · obtain ⟨e⟩ := he
    exact absurd hq (not_qs_of_equiv_perm (by norm_num) e)
  · exact Or.inr (Or.inl ⟨m, K, inferInstance, inferInstance, hK, he⟩)

omit [Finite W] in
theorem le_normalizer_of_commute {G A B : Subgroup (MulAut W)} (hAB : A ⊔ B = G)
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    G ≤ Subgroup.normalizer (A : Set (MulAut W)) := by
  rw [← hAB]
  refine sup_le Subgroup.le_normalizer fun b hb => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h2 : b * x * b⁻¹ = x := by rw [mul_inv_eq_iff_eq_mul]; exact (hc x hx b hb).symm
    rw [h2]; exact hx
  · intro hy
    have hyb := hc _ hy b hb
    have : x = b * x * b⁻¹ := by
      calc x = b⁻¹ * (b * x * b⁻¹) * b := by group
        _ = b⁻¹ * ((b * x * b⁻¹) * b) := by rw [mul_assoc]
        _ = b⁻¹ * (b * (b * x * b⁻¹)) := by rw [hyb]
        _ = b * x * b⁻¹ := by group
    rw [this]; exact hy

omit [Finite W] in
theorem card_ne_one_of_equiv_statedSL3 {G₁ : Subgroup (MulAut W)} 
    (hc : Nat.card ↥(commV G₁) = 2 ^ 3) : G₁ ≠ ⊥ := by
  intro h
  rw [h, commV_bot'] at hc
  simp at hc

theorem b56_qs {G : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥G)
    (h : B56Case1 G ∨ B56Case2 G ∨ B56Case3 G ∨ B56Case4 G ∨ B56Case5 G) :
    B56QuasisimpleList ↥G := by
  rcases h with h1 | h2 | h3 | h4 | h5
  · obtain ⟨hLq, -, hlist⟩ := h1
    have hL : quasithinGenFitting G = G := by
      rcases sub_central_or_eq hq (quasithinGenFitting_le G) (le_normalizer_quasithinGenFitting G)
        with hc | he
      · exfalso
        apply qs_not_commutative hLq
        intro x y
        have := hc x.1 x.2 y.1 (quasithinGenFitting_le G y.2)
        exact Subtype.ext this
      · exact he
    rw [hL] at hlist
    exact hlist
  · obtain ⟨e⟩ := h2.1
    exact absurd hq (not_qs_of_equiv_perm (by norm_num) e)
  · obtain ⟨G₁, G₂, hsup, hinf, hcomm, hF₁, hF₂, -⟩ := h3
    have hle₁ : G₁ ≤ G := hsup ▸ le_sup_left
    have hle₂ : G₂ ≤ G := hsup ▸ le_sup_right
    have hn₁ := le_normalizer_of_commute hsup hcomm
    have hn₂ := le_normalizer_of_commute (sup_comm G₁ G₂ ▸ hsup)
      (fun a ha b hb => (hcomm b hb a ha).symm)
    rcases sub_central_or_eq hq hle₁ hn₁ with hc₁ | he₁
    · rcases sub_central_or_eq hq hle₂ hn₂ with hc₂ | he₂
      · exact (not_both_central hq hsup hc₁ hc₂).elim
      · subst he₂
        exact b56QL_of_factorList hq hF₂
    · subst he₁
      exact b56QL_of_factorList hq hF₁
  · obtain ⟨G₁, G₂, t, hG, hinf, hcomm, -, hcard₂, -, -, -, -, -, ht₁, ht₂, hout₁, -⟩ := h4
    exfalso
    have hle₁ : G₁ ≤ G := hG ▸ le_sup_left.trans le_sup_left
    have hle₂ : G₂ ≤ G := hG ▸ le_sup_right.trans le_sup_left
    have htG : t ∈ G := hG ▸ (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
    have hn₁ : G ≤ Subgroup.normalizer (G₁ : Set (MulAut W)) := by
      rw [hG]
      refine sup_le (sup_le Subgroup.le_normalizer fun b hb => ?_) ?_
      · rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          have h2 : b * x * b⁻¹ = x := by rw [mul_inv_eq_iff_eq_mul]; exact (hcomm x hx b hb).symm
          rw [h2]; exact hx
        · intro hy
          have hyb := hcomm _ hy b hb
          have : x = b * x * b⁻¹ := by
            calc x = b⁻¹ * (b * x * b⁻¹) * b := by group
              _ = b⁻¹ * ((b * x * b⁻¹) * b) := by rw [mul_assoc]
              _ = b⁻¹ * (b * (b * x * b⁻¹)) := by rw [hyb]
              _ = b * x * b⁻¹ := by group
          rw [this]; exact hy
      · exact Subgroup.zpowers_le.mpr ht₁
    rcases sub_central_or_eq hq hle₁ hn₁ with hc₁ | he₁
    · apply hout₁
      refine ⟨1, G₁.one_mem, fun x hx => ?_⟩
      have := hc₁ x hx t htG
      rw [one_mul, inv_one, mul_one, mul_inv_eq_iff_eq_mul]
      exact this.symm
    · have : G₂ ≤ G₁ := he₁ ▸ hle₂
      have hbot : G₂ = ⊥ := by
        rw [eq_bot_iff, ← hinf]
        exact le_inf this le_rfl
      rw [hbot] at hcard₂
      simp at hcard₂
  · obtain ⟨G₁, G₂, hsup, hinf, hcomm, -, ⟨e⟩, hcard, -, -⟩ := h5
    have hle₁ : G₁ ≤ G := hsup ▸ le_sup_left
    have hle₂ : G₂ ≤ G := hsup ▸ le_sup_right
    have hn₁ := le_normalizer_of_commute hsup hcomm
    have hn₂ := le_normalizer_of_commute (sup_comm G₁ G₂ ▸ hsup)
      (fun a ha b hb => (hcomm b hb a ha).symm)
    have hne : G₁ ≠ ⊥ := card_ne_one_of_equiv_statedSL3 hcard
    rcases sub_central_or_eq hq hle₁ hn₁ with hc₁ | he₁
    · rcases sub_central_or_eq hq hle₂ hn₂ with hc₂ | he₂
      · exact (not_both_central hq hsup hc₁ hc₂).elim
      · exfalso
        apply hne
        rw [eq_bot_iff, ← hinf]
        exact le_inf le_rfl (he₂ ▸ hle₁)
    · subst he₁
      exact Or.inr (Or.inl ⟨1, ZMod 2, inferInstance, inferInstance, by simp, ⟨e.symm.symm⟩⟩)

end B56QS

end Insp9

end CFSG.Quasithin
