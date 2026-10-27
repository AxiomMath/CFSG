module

public import CFSG.Quasithin.Vol2.Ch1Sec3Basic
public import CFSG.Quasithin.Background.RonanD33
public import CFSG.Quasithin.Background.C1PackS15212A

public section

namespace CFSG.Quasithin.H13.L827X

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

theorem exists_mem_comm_not_le_pCoreOf [Finite G] {T X H' V : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hX : IsXi T X) (hTH' : IsSylowTwoOf T H')
    (hH'X : H' ≤ X ⊔ T) (hVT : V ≤ T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hVH' : ¬ V ≤ pCoreOf 2 H') :
    ∃ v ∈ V, ¬ ⁅oTwoUpper H' ⊔ pCoreOf 2 X, Subgroup.zpowers v⁆ ≤ pCoreOf 2 X := by
  classical
  by_contra hcon
  push_neg at hcon
  set O : Subgroup G := pCoreOf 2 X with hOdef
  set X₁ : Subgroup G := oTwoUpper H' ⊔ O with hX₁def
  have hOT : O ≤ T := pCoreOf_le_of_quasithinIsSylowTwo hT hX.2.1
  have hO2 : IsPGroup 2 ↥O := pCoreOf_isPGroup 2 X
  have hTO : T ≤ Subgroup.normalizer (O : Set G) :=
    hX.2.1.trans (normalizer_le_normalizer_pCoreOf 2 X)
  have hXTO : X ⊔ T ≤ Subgroup.normalizer (O : Set G) :=
    sup_le (le_normalizer_pCoreOf 2 X) hTO
  have hH'O : H' ≤ Subgroup.normalizer (O : Set G) := hH'X.trans hXTO
  have hO2H' : oTwoUpper H' ≤ H' := oTwoUpper_le H'
  have hTH'le : T ≤ H' := hTH'.1
  have hdecomp : H' = oTwoUpper H' ⊔ T := (C1Pack12.oTwoUpper_sup_eq_of_sylow hTH').symm
  have hX₁X : X₁ ≤ X ⊔ T := sup_le ((oTwoUpper_le H').trans hH'X) (hOT.trans le_sup_right)
  have hX₁N : X₁ ≤ Subgroup.normalizer (O : Set G) := hX₁X.trans hXTO
  set N : Subgroup G := V ⊔ O with hNdef
  have hNT : N ≤ T := sup_le hVT hOT
  have hN2 : IsPGroup 2 ↥N := hT.1.to_le hNT
  have hVN : V ≤ N := le_sup_left
  have hON : O ≤ N := le_sup_right
  have hTN : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N := by
    intro t ht n hn
    have hmem : n ∈ V ⊔ O := hn
    obtain ⟨v, hv, o, ho, rfl⟩ :=
      (Ch1Sec3.mem_sup_iff_of_le_normalizer (Q := V) (P := O) (by
        intro x hx
        exact hTV (hOT hx))).1 hmem
    have hv' : t * v * t⁻¹ ∈ V := by
      have := hTV ht
      exact (Subgroup.mem_normalizer_iff.mp this v).mp hv
    have ho' : t * o * t⁻¹ ∈ O := by
      have := hTO ht
      exact (Subgroup.mem_normalizer_iff.mp this o).mp ho
    have : t * (v * o) * t⁻¹ = (t * v * t⁻¹) * (t * o * t⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ (hVN hv') (hON ho')
  have hX₁N' : ∀ x ∈ X₁, ∀ v ∈ V, x * v * x⁻¹ ∈ N := by
    intro x hx v hv
    have hc : ⁅x, v⁆ ∈ O := by
      have hmem : ⁅x, v⁆ ∈ ⁅X₁, Subgroup.zpowers v⁆ :=
        Subgroup.commutator_mem_commutator hx (Subgroup.mem_zpowers v)
      exact hcon v hv hmem
    have hid : x * v * x⁻¹ = ⁅x, v⁆ * v := by
      simp only [commutatorElement_def]
      group
    rw [hid]
    exact Subgroup.mul_mem _ (hON hc) (hVN hv)
  have hX₁N'' : ∀ x ∈ X₁, ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
    intro x hx n hn
    obtain ⟨v, hv, o, ho, rfl⟩ :=
      (Ch1Sec3.mem_sup_iff_of_le_normalizer (Q := V) (P := O) (by
        intro y hy
        exact hTV (hOT hy))).1 hn
    have hxo : x * o * x⁻¹ ∈ O := by
      have := hX₁N hx
      exact (Subgroup.mem_normalizer_iff.mp this o).mp ho
    have : x * (v * o) * x⁻¹ = (x * v * x⁻¹) * (x * o * x⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ (hX₁N' x hx v hv) (hON hxo)
  have hTH'N : ∀ h ∈ H', ∀ n ∈ N, h * n * h⁻¹ ∈ N := by
    intro h hh n hn
    have hOT2 : T ≤ Subgroup.normalizer (oTwoUpper H' : Set G) :=
      hTH'le.trans (le_normalizer_oTwoUpper H')
    obtain ⟨q, hq, t, ht, rfl⟩ :=
      (Ch1Sec3.mem_sup_iff_of_le_normalizer (Q := oTwoUpper H') (P := T) hOT2).1
        (by rw [← hdecomp]; exact hh)
    have hqX₁ : q ∈ X₁ := le_sup_left (a := oTwoUpper H') (b := O) |> fun h' => h' hq
    have htn : t * n * t⁻¹ ∈ N := hTN t ht n hn
    have : q * t * n * (q * t)⁻¹ = q * (t * n * t⁻¹) * q⁻¹ := by group
    rw [this]
    exact hX₁N'' q hqX₁ _ htn
  have hH'N : H' ≤ Subgroup.normalizer (N : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hTH'N h hh n hn
    · intro hn
      have := hTH'N h⁻¹ (H'.inv_mem hh) _ hn
      simpa [mul_assoc] using this
  have hNH' : N ≤ H' := sup_le (hVT.trans hTH'le) (hOT.trans hTH'le)
  have hNpc : N ≤ pCoreOf 2 H' :=
    CFSG.Quasithin.RonanD33.le_pCoreOf_of_le_normalizer hNH' hH'N hN2
  exact hVH' (hVN.trans hNpc)

end CFSG.Quasithin.H13.L827X
