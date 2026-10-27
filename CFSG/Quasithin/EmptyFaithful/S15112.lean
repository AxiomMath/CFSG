module

public import CFSG.Quasithin.EmptyFaithful.S151Dual

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem concl319_of_hyp5 {T M V H : Subgroup G} {P : Prop} (c : Concl319 T M V H P) (hP : P) :
    Concl319 T M V H True :=
  { c with shape := fun _ => c.shape hP }

theorem lemma_15_1_12_concl319 (h319 : Lemma319Statement) {T Mc M : Subgroup G}
    (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) (h158 : Lemma1518Concl T Mc M)
    (h159 : Lemma1519Concl T Mc M)
    (h16 : oTwoUpper (M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ≤
      Subgroup.centralizer (V154 T Mc M : Set G))
    (hdual : ¬ IsDualFFOn (M ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)) (V154 T Mc M))
    {H : Subgroup G} (hH : IsHStar T M H) (hVH : V154 T Mc M ≤ pCoreOf 2 H) :
    Concl319 T M (V154 T Mc M) H True := by
  obtain ⟨hbase, hII⟩ := h159.six_hyp H hH
  have hV' := hbase.reduced.2.2.1
  have hq2 : qOn M (V154 T Mc M) = 2 := by
    rcases h158 with h' | h'
    · exact h'.2
    · exact h'.2.2
  have hq : qInt (M ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)) (V154 T Mc M)
      hV' = 2 := by
    rw [qInt_congr hV' h159.six_autOn, ← qOn_eq hV']
    exact hq2
  exact concl319_of_hyp5
    (h319 G T h.simple h.nonabelian h.qtke h.sylow M _ H _ hM.1.1 hbase hII hq h159.five hVH hdual)
    h16

theorem stageLemma15112_of (h319 : Lemma319Statement) (h1416 : StageLemma1416)
    (h1515 : StageLemma1515) (h158 : StageLemma1518) (h159 : StageLemma1519)
    (h16 : StageLemma1516) (h1511 : StageLemma15111) (h4 : StageLemma15112Four) :
    StageLemma15112 := by
  intro G _ _ T Mc M h hM hCE H hH
  exact ⟨lemma_15_1_12_concl319 h319 h hM (h158 G T Mc M h hM hCE) (h159 G T Mc M h hM hCE)
    (h16 G T Mc M h hM) (notDualFF1512_of h1416 h1515 h158 h159 G T Mc M h hM hCE) hH
    (h1511 G T Mc M h hM hCE H hH).1, h4 G T Mc M h hM hCE H hH⟩

end CFSG.Quasithin
