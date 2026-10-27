module

public import CFSG.Quasithin.H13.Sp62D3
public import CFSG.Quasithin.H13.Sp62Transport
public import CFSG.Quasithin.H13.Sp62DSystem

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv

structure ModelData (K : Type*) [Group K] : Prop where
  exists_data : ∃ P₀ X₁ X₂ : Subgroup K, IsPGroup 2 P₀ ∧ ¬ 2 ∣ P₀.index ∧
    (∀ Y : Subgroup K, P₀ ≤ Y → Y = P₀ ∨ Y = X₁ ∨ Y = X₂ ∨ Y = ⊤) ∧
    P₀ ≤ X₁ ∧ P₀ ≤ X₂ ∧ ¬ X₁ ≤ X₂ ∧ ¬ X₂ ≤ X₁

theorem modelData_SL3 : ModelData SL3.S :=
  ⟨⟨SL3.P0, SL3.X1, SL3.X2, SL3.P0_sylow.1, SL3.P0_sylow.2, SL3.overgroups_SL3,
    inf_le_left, inf_le_right, SL3.X_incomparable.1, SL3.X_incomparable.2⟩⟩

theorem modelData_SL22 : ModelData SL22.K :=
  ⟨⟨SL22.P0, SL22.X1, SL22.X2, SL22.P0_sylow.1, SL22.P0_sylow.2, SL22.overgroups_SL22,
    fun _ hx => SL22.mem_X1.2 (Subgroup.mem_prod.1 hx).2,
    fun _ hx => SL22.mem_X2.2 (Subgroup.mem_prod.1 hx).1,
    SL22.X_incomparable.1, SL22.X_incomparable.2⟩⟩

theorem modelData_S6 : ModelData (Perm (Fin 6)) := by
  refine ⟨⟨D6sub, P1sub, P2sub, D6syl.isPGroup', ?_, overgroups_D6,
    fun σ hσ => (D6sub_le hσ).1, fun σ hσ => (D6sub_le hσ).2, P1_not_le_P2.1, P1_not_le_P2.2⟩⟩
  have := D6syl.not_dvd_index
  exact this

theorem d3max_of_modelData {G : Type} [Group G] [Finite G] {K : Type*} [Group K] [Finite K]
    (hK : ModelData K) {X T E₁ E₂ : Subgroup G} (hiso : quasithinO2QuotientIso X K)
    (hT : IsSylowTwoOf T X) (hE₁ : T ≤ E₁) (hE₁X : E₁ ≤ X) (hE₁T : E₁ ≠ T) (hE₁X' : E₁ ≠ X)
    (hE₂ : T ≤ E₂) (hE₂X : E₂ ≤ X) (hE₂T : E₂ ≠ T) (hE₂X' : E₂ ≠ X) (hE : E₁ ≠ E₂) :
    ∀ Y : Subgroup G, (T ≤ Y ∧ IsMaxSubgroupIn Y X) ↔ (Y = E₁ ∨ Y = E₂) := by
  obtain ⟨P₀, X₁, X₂, hP, hP', hcls, h₁, h₂, h₁₂, h₂₁⟩ := hK.exists_data
  obtain ⟨A₁, A₂, hT₁, hT₂, h₁X, h₂X, hA₁₂, hA₂₁, hA₁, hA₂, hclsX⟩ :=
    overgroups_transport hiso hT hP hP' hcls h₁ h₂ h₁₂ h₂₁
  exact maxOvergroups_eq hclsX hT₁ hT₂ h₁X h₂X hA₁₂ hA₂₁ hA₁ hA₂ hE₁ hE₁X hE₁T hE₁X' hE₂ hE₂X
    hE₂T hE₂X' hE

theorem modelData_A6 : ModelData ↥(alternatingGroup (Fin 6)) := by
  set A := alternatingGroup (Fin 6) with hA
  have hQA : QA6sub ≤ A := inf_le_right
  have hcardA : Nat.card ↥A = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hcardP : Nat.card ↥(QA6sub.subgroupOf A) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQA).toEquiv, card_QA6sub]
  have hmap : ∀ Y : Subgroup ↥A, (Y.map A.subtype).subgroupOf A = Y := fun Y =>
    Subgroup.comap_map_eq_self_of_injective A.subtype_injective Y
  refine ⟨⟨QA6sub.subgroupOf A, P1sub.subgroupOf A, P2sub.subgroupOf A,
    IsPGroup.of_card (n := 3) (by rw [hcardP]; norm_num), ?_, fun Y hY => ?_,
    Subgroup.subgroupOf_mono _ (fun σ hσ => (D6sub_le hσ.1).1),
    Subgroup.subgroupOf_mono _ (fun σ hσ => (D6sub_le hσ.1).2), ?_, ?_⟩⟩
  · have := Subgroup.card_mul_index (QA6sub.subgroupOf A)
    rw [hcardP, hcardA] at this
    have h45 : (QA6sub.subgroupOf A).index = 45 := by omega
    rw [h45]
    norm_num
  · have hQY : QA6sub ≤ Y.map A.subtype := by
      intro σ hσ
      exact ⟨⟨σ, hQA hσ⟩, hY hσ, rfl⟩
    have hYA : Y.map A.subtype ≤ A := Subgroup.map_subtype_le Y
    rcases overgroups_QA6 _ hQY hYA with h | h | h | h
    · left
      rw [← hmap Y, h]
    · right; left
      rw [← hmap Y, h, Subgroup.inf_subgroupOf_right]
    · right; right; left
      rw [← hmap Y, h, Subgroup.inf_subgroupOf_right]
    · right; right; right
      rw [← hmap Y, h, Subgroup.subgroupOf_self]
  · intro h
    have hm : (⟨swap 0 2 * swap 4 5, by
        rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ : ↥A) ∈ P1sub.subgroupOf A :=
      show InP1 (swap 0 2 * swap 4 5) by decide
    exact absurd (h hm) (show ¬ InP2 (swap 0 2 * swap 4 5) by decide)
  · intro h
    have hm : (⟨swap 0 4 * swap 1 5, by
        rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ : ↥A) ∈ P2sub.subgroupOf A :=
      show InP2 (swap 0 4 * swap 1 5) by decide +kernel
    exact absurd (h hm) (show ¬ InP1 (swap 0 4 * swap 1 5) by decide)

theorem inf3_le {G : Type} [Group G] (Es : Fin 3 → Subgroup G) (i : Fin 3) :
    Es 0 ⊓ Es 1 ⊓ Es 2 ≤ Es i := by
  fin_cases i
  · exact inf_le_left.trans inf_le_left
  · exact inf_le_left.trans inf_le_right
  · exact inf_le_right

theorem isDSystemIn_C3_of {G : Type} [Group G] [Finite G] (Es : Fin 3 → Subgroup G)
    (hD1 : quasithinO2QuotientIso (Es 0) ↥(alternatingGroup (Fin 6)) ∨
      quasithinO2QuotientIso (Es 0) (Perm (Fin 6)))
    (hD2a : quasithinO2QuotientIso (Es 1)
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)))
    (hD2b : quasithinO2QuotientIso (Es 2) (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hsyl : ∀ i : Fin 3, IsSylowTwoOf (Es 0 ⊓ Es 1 ⊓ Es 2) (Es i))
    (hT : ∀ i j : Fin 3, i ≠ j → Es i ⊓ Es j ≠ Es 0 ⊓ Es 1 ⊓ Es 2)
    (hX : ∀ i j : Fin 3, i ≠ j → Es i ⊓ Es j ≠ Es i)
    (hdist : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → Es i ⊓ Es j ≠ Es i ⊓ Es k)
    (hD4 : ∀ N : Subgroup G, N ≤ Es 0 ⊓ Es 1 ⊓ Es 2 →
      Es 0 ⊔ Es 1 ⊔ Es 2 ≤ Subgroup.normalizer (N : Set G) → N = ⊥)
    (hD5 : Subgroup.center ↥(Es 0) ≠ ⊥ ∨ 2 ^ 5 < Nat.card ↥(pCoreOf 2 (Es 0))) :
    IsDSystemIn .C3 Es := by
  refine ⟨fun h => absurd h (by decide), fun _ => hD1, hD2a, hD2b, hsyl, ?_, hD4, fun _ => hD5⟩
  intro i j k hij hik hjk
  refine ⟨hdist i j k hij hik hjk, ?_⟩
  have hTij : Es 0 ⊓ Es 1 ⊓ Es 2 ≤ Es i ⊓ Es j := le_inf (inf3_le Es i) (inf3_le Es j)
  have hTik : Es 0 ⊓ Es 1 ⊓ Es 2 ≤ Es i ⊓ Es k := le_inf (inf3_le Es i) (inf3_le Es k)
  have key : ∀ {K : Type} [Group K] [Finite K], ModelData K →
      quasithinO2QuotientIso (Es i) K →
      ∀ Y : Subgroup G, (Es 0 ⊓ Es 1 ⊓ Es 2 ≤ Y ∧ IsMaxSubgroupIn Y (Es i)) ↔
        (Y = Es i ⊓ Es j ∨ Y = Es i ⊓ Es k) := fun hK hiso =>
    d3max_of_modelData hK hiso (hsyl i) hTij inf_le_left (hT i j hij) (hX i j hij) hTik
      inf_le_left (hT i k hik) (hX i k hik) (hdist i j k hij hik hjk)
  fin_cases i
  · rcases hD1 with h | h
    · exact key modelData_A6 h
    · exact key modelData_S6 h
  · exact key modelData_SL22 hD2a
  · exact key modelData_SL3 hD2b

end CFSG.Quasithin.H13.A6
