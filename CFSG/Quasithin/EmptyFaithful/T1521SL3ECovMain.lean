module

public import CFSG.Quasithin.EmptyFaithful.T1521SL3ECov
public import CFSG.Quasithin.EmptyFaithful.T1521SL3EMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.L31521E

@[expose] def E1L3Cover : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), Std1521 X S L →
    IsComponentOf L X → IsPGroup 2 ↥(Subgroup.center ↥L) →
    (∃ n : ℕ, 1 < n ∧ IsPSL 3 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) →
    (∀ z ∈ Subgroup.center ↥L, z ^ 2 = 1) → thompsonJ S ≤ innerPart1521 S L

theorem isElemAbelian_center_of_sq_eq_one {G : Type} [Group G] {L : Subgroup G}
    (h : ∀ z ∈ Subgroup.center ↥L, z ^ 2 = 1) :
    IsElemAbelian 2 (L ⊓ Subgroup.centralizer (L : Set G)) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp b.2.2 a a.2.1
  · have hz : (⟨x, hx.1⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 y y.2)
    have := h _ hz
    exact congrArg Subtype.val this

theorem e1L3Cover_of (h37 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A37Statement Y)
    (h38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y) : E1L3Cover := by
  intro G _ _ X S L hStd hco _ ⟨n, hn, hL⟩ hEA
  obtain ⟨-, hcase⟩ := a3Orbits_of_a37_a38 h37 h38 X S L hStd.sqtk hStd.sylow hStd.comp
  obtain ⟨V, V', hB⟩ := rankBound1521_l3_cover (by omega) hL
    (isQuasisimple_of_open1521 hco.2.2) (isElemAbelian_center_of_sq_eq_one hEA) hStd.sylowL
  rcases hcase with hnorm | ⟨t, htS, htn, hset, -, -, -⟩
  · exact thompsonJ_le_innerPart_of_bound hB fun t ht => hnorm t ht
  · exact thompsonJ_le_innerPart_of_bound_wreath hB hset
      (commutator_conjByElt_eq_bot1521 hco (hStd.sylow.1 htS) htn)

end CFSG.Quasithin
