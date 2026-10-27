module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223A57Core
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223A57E5
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223BlkAlt
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223BlkOrb
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Swap

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC CFSG.LieType.BorelTits

namespace S15223

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_three_of_isElemAbelian {E : Subgroup G} (hE : IsElemAbelian 3 E) : IsPGroup 3 E :=
  CFSG.Open.IsElemAbelian.isPGroup hE

namespace Core57

variable {I S K H Mc : Subgroup G} (c : Core57 I S K H Mc)
include c

theorem le_normalizer_of_alt5 {X : Subgroup G} (hX : IsBlock2 I X) (h5 : IsAltType X 5)
    (h3 : 3 ∣ Nat.card X) (hUQ : blockU X ≤ pCoreOf 2 (K ⊔ S)) {A : Subgroup G}
    (hA : IsMaxElemAbelian (pCoreOf 2 (K ⊔ S)) A) : A ≤ Subgroup.normalizer (X : Set G) := by
  have hAI : A ≤ I := hA.1.trans ((pCoreOf_sup_le c.sylow c.K_le).trans c.sylow.1)
  have hidx := index_normalizer_le_two distinctBlocksCommuteStatement c.charTwo c.rank hX h3
  set N' : Subgroup ↥I := (Subgroup.normalizer (X : Set G) ⊓ I).subgroupOf I with hN'
  have hmemN : ∀ g : ↥I, g ∈ N' ↔ (g : G) ∈ Subgroup.normalizer (X : Set G) := fun g => by
    rw [hN', Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, g.2⟩⟩
  refine le_normalizer_of_isMaxElemAbelian_alt5 hX.1 h5 ?_ ?_ hA hUQ
  · intro g hg hgn
    have hgI : g ∈ I := hAI hg
    have hX' : IsBlock2 I (conjByElt g X) := IsBlock2.conjByElt_of_mem hX hgI
    have hne : X ≠ conjByElt g X := fun h =>
      hgn (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
    exact distinctBlocksCommuteStatement I X (conjByElt g X) c.charTwo hX hX' hne
  · intro a ha b hb han hbn
    have haI : a ∈ I := hAI ha
    have hbI : b ∈ I := hAI hb
    rcases mem_of_index_le_two hidx 1 ⟨a, haI⟩ ⟨b, hbI⟩ with h | h | h
    · exact absurd ((hmemN _).mp h |> fun h' => by simpa using h') han
    · exact absurd ((hmemN _).mp h |> fun h' => by simpa using h') hbn
    · exact (hmemN _).mp h

theorem false_of_alt5 {X : Subgroup G} (hX : IsBlock2 I X) (h5 : IsAltType X 5) : False := by
  obtain ⟨-, hgen, hns, hV2, h3⟩ := alt_block_facts hX.1 (Or.inl rfl) h5
  have hXMc : ¬ X ≤ Mc :=
    not_le_of_block distinctBlocksCommuteStatement c.charTwo c.rank c.sylow hX h3 c.S_Mc c.P1
      c.K_solv hgen hns hV2
  have cfg := c.blkCfg hX h3
  set S₁ : Subgroup G := S ⊓ Subgroup.normalizer (X : Set G) with hS₁
  set Q₁ : Subgroup G := pCoreOf 2 (K ⊔ S₁) with hQ₁
  have hUO : blockU X ≤ pCoreOf 2 X := fun u hu => (hX.1.2.2.1.1 hu).1
  have hUQ₁ : blockU X ≤ Q₁ := hUO.trans cfg.pCoreOf_le_pCoreOf_sup_inf
  have hUQ : blockU X ≤ pCoreOf 2 (K ⊔ S) := hUQ₁.trans cfg.pCoreOf_sup_inf_le
  obtain ⟨A, hAmax, hAc⟩ := c.exists_isMaxElemAbelian hX h3 hXMc
    (fun A hA => c.le_normalizer_of_alt5 hX h5 h3 hUQ hA)
  have hQ₁N : Q₁ ≤ Subgroup.normalizer (X : Set G) := cfg.pCoreOf_sup_le_S₁.trans inf_le_right
  obtain ⟨α, hα, hαk, -⟩ := id h5
  obtain ⟨P5, -⟩ := exists_a5pi hX.1 h5 α hα hαk
  obtain ⟨j, hjA, hjodd⟩ := exists_sign_neg_of_alt5 P5 (isElemAbelian_blockU hX.1) hUQ₁ hQ₁N hAmax
    hAc
  obtain ⟨P, hPK, hP3, hP9⟩ := c.three
  have hPN : P ≤ Subgroup.normalizer (X : Set G) := hPK.trans cfg.K_normX
  have hPQ₁ : P ≤ Subgroup.normalizer (Q₁ : Set G) :=
    hPK.trans (le_sup_left.trans (le_normalizer_pCoreOf 2 _))
  have hS₁Q₁ : S₁ ≤ Subgroup.normalizer (Q₁ : Set G) :=
    le_sup_right.trans (le_normalizer_pCoreOf 2 _)
  have hS₁2 : IsPGroup 2 S₁ := c.sylow.2.1.to_le inf_le_left
  have hcomm := commutator_eq_bot_of_alt5_odd hX.1 P5 hS₁2 cfg.sylowX₁ cfg.pCoreOf_sup_le_S₁
    hS₁Q₁ hPQ₁ hPN (isPGroup_three_of_isElemAbelian hP3) ⟨j, hAmax.1 hjA, hjodd⟩
  refine false_of_centralizes_block c.rank hX.2.1 (hPK.trans c.K_le) hP3 hP9 hX.1 h3 ?_
  intro p hp
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (Subgroup.mem_centralizer_iff.1 (hcomm hx) p hp).symm

end Core57

end S15223

end CFSG.Quasithin
