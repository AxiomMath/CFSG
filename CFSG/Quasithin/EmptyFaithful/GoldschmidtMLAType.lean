module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLAInv
public import CFSG.Quasithin.EmptyFaithful.S151XF
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma33

public section

namespace CFSG.Quasithin.GoldMLA

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

theorem pCore_two_eq_bot_of_simple {X : Type} [Group X] [Finite X] (hperf : commutator X = ⊤)
    (hs : IsSimpleGroup X) : CFSG.pCore 2 X = ⊥ := by
  have : Nontrivial X := hs.toNontrivial
  rcases hs.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 X) with h | h
  · exact h
  · exfalso
    have hnil : Group.IsNilpotent ↥(CFSG.pCore 2 X) := CFSG.pCore_isNilpotent
    rw [h] at hnil
    have hX : Group.IsNilpotent X := Group.nilpotent_of_mulEquiv (Subgroup.topEquiv (G := X))
    have hsolv : Group.IsSolvable X := inferInstance
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial X
    rw [hperf] at hlt
    exact lt_irrefl _ hlt

theorem fib_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : fusionIsBenderGroup X) : fusionIsBenderGroup Y := by
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ | ⟨a, ha, ⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.symm.trans e'⟩⟩)

theorem fusionIsBenderGroup_of_isPSU3 {f : ℕ} (hf : 2 ≤ f) {X : Type} [Group X]
    (h : IsPSU 3 2 f X) : fusionIsBenderGroup X := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hcard : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  let e' : X ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ f)) := e
  exact Or.inr (Or.inl ⟨f, hf, ⟨e'.trans
    (CFSG.ShultStronglyClosedTI.glaSU3EquivNative f hf hcard)⟩⟩)

theorem fusionIsBenderGroup_quot {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hperf : commutator ↥L = ⊤) (hA : CompTypeA15120 L) :
    fusionIsBenderGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
  rcases hA with hL | hSz
  · have hb : fusionIsBenderGroup ↥L := by
      rcases hL with ⟨n, hn, h⟩ | ⟨e, h⟩ | ⟨n, hn, h⟩
      · exact A5.C25.fusionIsBenderGroup_of_isPSL h
      · exact A5.C25.fusionIsBenderGroup_of_isSz h
      · exact fusionIsBenderGroup_of_isPSU3 hn h
    have hs := RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hb
    have h0 := pCore_two_eq_bot_of_simple hperf hs
    exact fib_of_mulEquiv ((QuotientGroup.quotientBot (G := ↥L)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq h0.symm)) hb
  · exact A5.C25.fusionIsBenderGroup_of_isSz hSz

theorem commute_conj_of_component {G : Type} [Group G] [Finite G] {X L : Subgroup G}
    (hL : CFSG.Open.IsComponentOf L X) {t : G} (ht : t ∈ X)
    (hne : t ∉ Subgroup.normalizer (L : Set G)) :
    ∀ a ∈ L, ∀ b ∈ conjByElt t L, a * b = b * a := by
  have hc1 : IsComponentIn L X := DoubleA3.isComponentIn_iff_open.mpr hL
  let φ : ↥X ≃* ↥X := MulAut.conj (⟨t, ht⟩ : ↥X)
  have hc2 := CFSG.LocalCores.isComponent_map_mulEquiv φ hc1.2
  have hLX : conjByElt t L ≤ X := fun x hx => by
    have h1 : t⁻¹ * x * t ∈ X := hc1.1 ((mem_conjByElt).mp hx)
    have := X.mul_mem (X.mul_mem ht h1) (X.inv_mem ht)
    simpa [mul_assoc] using this
  have hmap : (L.subgroupOf X).map φ.toMonoidHom = (conjByElt t L).subgroupOf X := by
    ext ⟨x, hx⟩
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, mem_conjByElt]
    show (φ.symm ⟨x, hx⟩ : G) ∈ L ↔ t⁻¹ * x * t ∈ L
    rw [show (φ.symm ⟨x, hx⟩ : G) = t⁻¹ * x * t from by
      simp [φ, MulAut.conj_symm_apply]]
  rw [hmap] at hc2
  rcases CFSG.LocalCores.distinct_components_commute hc1.2 hc2 with h | h
  · exfalso
    apply hne
    have h1 := Subgroup.subgroupOf_inj.mp h
    rw [inf_of_le_left hc1.1, inf_of_le_left hLX] at h1
    exact mem_normalizer_of_conjByElt_eq h1.symm
  · intro a ha b hb
    have h1 : ⁅(⟨a, hc1.1 ha⟩ : ↥X), (⟨b, hLX hb⟩ : ↥X)⁆ ∈
        ⁅L.subgroupOf X, (conjByElt t L).subgroupOf X⁆ :=
      Subgroup.commutator_mem_commutator ha hb
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact congrArg Subtype.val h1

theorem exists_conj_eq_of_orbits {G : Type} [Group G] {X S L : Subgroup G}
    (horb : conjSubgroupsBy X L = conjSubgroupsBy S L) {m : G} (hm : m ∈ X) :
    ∃ s ∈ S, conjByElt m L = conjByElt s L := by
  have h : conjByElt m L ∈ conjSubgroupsBy X L := ⟨m, hm, rfl⟩
  rw [horb] at h
  obtain ⟨s, hs, hseq⟩ := h
  exact ⟨s, hs, hseq⟩

end CFSG.Quasithin.GoldMLA
