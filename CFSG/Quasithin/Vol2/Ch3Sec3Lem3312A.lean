module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem335
public import CFSG.Quasithin.Vol2.Ch1Eight

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped Pointwise

namespace L3312

variable {G : Type} [Group G] [Finite G]

structure Hyp3312 (G : Type) [Group G] [Finite G] (T M L D Y : Subgroup G) : Prop
    extends Hyp331 G T M L D where
  mem : Y ∈ lFamilyOf L T
  pCore_ne : pCoreOf 2 (Y ⊔ T ⊔ D) ≠ ⊥

omit [Finite G] in
theorem ncard_conjSubgroupsBy_eq_index (H K : Subgroup G) :
    (conjSubgroupsBy H K).ncard = ((Subgroup.normalizer (K : Set G)).subgroupOf H).index := by
  let φ : ↥H →* MulAut G := MulAut.conj.comp H.subtype
  let _ : MulAction ↥H (Subgroup G) := MulAction.compHom (Subgroup G) φ
  have hsmul : ∀ (h : ↥H) (X : Subgroup G), h • X = X.map (MulAut.conj (h : G)).toMonoidHom :=
    fun h X => rfl
  have hstab : MulAction.stabilizer ↥H K = (Subgroup.normalizer (K : Set G)).subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hsmul,
      Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Iff.rfl
  have horb : MulAction.orbit ↥H K = conjSubgroupsBy H K := by
    ext X
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, h.2, hsmul h K⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, hsmul ⟨t, ht⟩ K⟩
  rw [← hstab, MulAction.index_stabilizer, horb]

namespace Hyp3312

variable {T M L D Y : Subgroup G} (H : Hyp3312 G T M L D Y)

include H

theorem le_L : Y ≤ L := H.mem.1

theorem isLocal : quasithinIsLocal T Y := H.mem.2

theorem le_normalizer_L (h14 : Stmt3_3_14) : T ≤ Subgroup.normalizer (L : Set G) :=
  H.TM.trans (h14 G T M L D H.toHyp331).2

theorem ne_L
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : Y ≠ L := by
  intro hYL
  apply H.pCore_ne
  rw [hYL]
  exact H.toHyp331.pCoreOf_sup_eq_bot h38 h39

theorem le_normalizer_Y (h14 : Stmt3_3_14) (h37 : A37ForSQTK) (h128 : Lemma128One) :
    T ≤ Subgroup.normalizer (Y : Set G) := by
  have heq := lemma_1_2_8_one H.qtke H.simple H.nonabelian h37 h128 H.isLocal H.Lmax.1 H.le_L
  intro t ht
  have h1 : t ∈ T ⊓ Subgroup.normalizer (L : Set G) := ⟨ht, H.le_normalizer_L h14 ht⟩
  rw [← heq] at h1
  exact h1.2

theorem isSylowTwoOf_H : IsSylowTwoOf T (Y ⊔ T ⊔ D) :=
  isSylowTwoOf_of_quasithinIsSylowTwo H.sylow (le_sup_right.trans le_sup_left)

theorem exists_cComp (h37 : A37ForSQTK) (h39 : A39ForSQTK) :
    ∃ K ∈ cComp (Y ⊔ T ⊔ D), Y ≤ K :=
  lemma_1_2_4_exists H.qtke H.simple H.nonabelian h37 h39 H.pCore_ne H.isSylowTwoOf_H
    (le_sup_left.trans le_sup_left) (mem_lFamily_of_isLocal H.isLocal)

theorem le_normalizer_K (h14 : Stmt3_3_14) (h37 : A37ForSQTK) (h128 : Lemma128One)
    {K : Subgroup G} (hK : K ∈ cComp (Y ⊔ T ⊔ D)) (hYK : Y ≤ K) :
    T ≤ Subgroup.normalizer (K : Set G) := by
  intro t ht
  have hQ' := sqtkHyp_quotient_of_pCoreOf_ne_bot H.qtke H.simple H.nonabelian H.pCore_ne
  have htH : t ∈ Y ⊔ T ⊔ D := (le_sup_right.trans le_sup_left : T ≤ Y ⊔ T ⊔ D) ht
  have hKt : K.map (MulAut.conj t).toMonoidHom ∈ cComp (Y ⊔ T ⊔ D) := map_conj_mem_cComp hK htH
  have hYt : Y.map (MulAut.conj t).toMonoidHom = Y :=
    A38.map_conj_eq_iff.mpr (H.le_normalizer_Y h14 h37 h128 ht)
  have hYKt : Y ≤ K.map (MulAut.conj t).toMonoidHom :=
    calc Y = Y.map (MulAut.conj t).toMonoidHom := hYt.symm
      _ ≤ K.map (MulAut.conj t).toMonoidHom := Subgroup.map_mono hYK
  have heq := lemma_1_2_4_unique (h37 _ hQ') (mem_lFamily_of_isLocal H.isLocal) hK hKt hYK hYKt
  exact A38.map_conj_eq_iff.mp heq.symm

theorem sup_le_normalizer_K (h14 : Stmt3_3_14) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h128 : Lemma128One) {K : Subgroup G} (hK : K ∈ cComp (Y ⊔ T ⊔ D)) (hYK : Y ≤ K) :
    Y ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G) := by
  have hTK := H.le_normalizer_K h14 h37 h128 hK hYK
  rcases lemma_1_2_1_three H.qtke H.simple H.nonabelian h37 h38 H.pCore_ne hK with hn | ⟨h2, -⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hK)).mp hn
  · exfalso
    rw [ncard_conjSubgroupsBy_eq_index] at h2
    have hS := H.isSylowTwoOf_H
    have hTN : T ≤ Subgroup.normalizer (K : Set G) ⊓ (Y ⊔ T ⊔ D) := le_inf hTK hS.1
    apply hS.2.2
    have h3 := Subgroup.relIndex_mul_relIndex T (Subgroup.normalizer (K : Set G) ⊓ (Y ⊔ T ⊔ D))
      (Y ⊔ T ⊔ D) hTN inf_le_right
    have h4 : (Subgroup.normalizer (K : Set G) ⊓ (Y ⊔ T ⊔ D)).relIndex (Y ⊔ T ⊔ D) = 2 := by
      rw [← h2, Subgroup.relIndex, Subgroup.inf_subgroupOf_right]
    show 2 ∣ T.relIndex (Y ⊔ T ⊔ D)
    rw [← h3, h4]
    exact Dvd.intro_left _ rfl

end Hyp3312

end L3312

end CFSG.Quasithin.H13
