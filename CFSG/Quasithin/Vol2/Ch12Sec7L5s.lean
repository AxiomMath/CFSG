module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModL
public import CFSG.Quasithin.Vol2.Ch12Sec7ModO
public import CFSG.Quasithin.Background.C58Blocks
public import CFSG.Quasithin.Background.C1PackS15212A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S127
open scoped IsMulCommutative

namespace S127.L713

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem V_le_T (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) : V ≤ T := by
  have hy := h.hyp
  obtain ⟨-, -, hall⟩ := ((h1222 G T hy.simple hy.nonabelian hy.qtke hy.sylow).resolve_left
    hy.notAlt) L hy.maximal hy.faithful hy.quasisimple
  exact (hall V hy.irrPlus).1.1

theorem eq_oTwoUpper (h : Hyp1271 G T L V) : L = oTwoUpper L :=
  (h.hyp.faithful.2.1 _ (oTwoUpper_le L)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le L)).mpr
      (le_normalizer_oTwoUpper L))
    fun _ hx => exists_pow_mem_oTwoUpper L hx).symm

omit [Finite G] in
theorem isSylowTwoOf_of_le {H : Subgroup G} (hT : quasithinIsSylowTwo T) (hTH : T ≤ H) :
    QuasithinUnique.IsSylowTwoOf T H :=
  ⟨hTH, hT.1, fun h => hT.2 (h.trans (by
    simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le hTH))⟩

theorem P1_le (h : Hyp1271 G T L V) (hTV1 : T ≤ Subgroup.normalizer (V1 T L V : Set G)) :
    P1 T L V ≤ lOne L (V1 T L V) ⊔ T := by
  set H' : Subgroup G := (L ⊔ T) ⊓ Subgroup.normalizer (V1 T L V : Set G) with hH'
  have hTH' : T ≤ H' := le_inf le_sup_right hTV1
  have hsyl : QuasithinUnique.IsSylowTwoOf T H' := isSylowTwoOf_of_le h.hyp.sylow hTH'
  have hO : oTwoUpper H' ≤ lOne L (V1 T L V) := by
    have h1 : oTwoUpper H' ≤ L :=
      C58.oTwoUpper_le_of_le_sup inf_le_left h.hyp.sylow.1 h.hyp.normalizes
    have h2 : oTwoUpper H' ≤ L ⊓ Subgroup.normalizer (V1 T L V : Set G) :=
      le_inf h1 ((oTwoUpper_le _).trans inf_le_right)
    calc oTwoUpper H' = oTwoUpper (oTwoUpper H') := (S127.Mod.oTwoUpper_idem _).symm
      _ ≤ oTwoUpper (L ⊓ Subgroup.normalizer (V1 T L V : Set G)) := S127.Mod.oTwoUpper_mono h2
  have hP : P1 T L V ≤ H' :=
    le_inf (inf_le_left.trans (sup_le le_sup_left (CFSG.LieType.BorelTits.pCoreOf_le 2 _)))
      inf_le_right
  calc P1 T L V ≤ H' := hP
    _ = oTwoUpper H' ⊔ T := (C1Pack12.oTwoUpper_sup_eq_of_sylow hsyl).symm
    _ ≤ lOne L (V1 T L V) ⊔ T := sup_le_sup_right hO T

end S127.L713

open S127.L713 in
theorem lemma12_7_13_of
    (h1222 : Stmt12_2_2) :
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t : G), Setting1273 G T L V t →
      (∀ H : Subgroup G, InH (P1 T L V ⊔ T) H → H ≤ Subgroup.normalizer (V1 T L V : Set G) →
        AlmostSpecialHyp V (V1 T L V) L T H) ∧
      V ≤ pCoreOf 2 (Subgroup.normalizer (V1 T L V : Set G)) := by
  intro G _ _ T L V t hS
  have h := hS.hyp
  obtain ⟨hcomm, -, hTV⟩ := S127.card_eq_of_1222 h1222 h
  have := hcomm
  have hVab : IsElemAbelian 2 V := ⟨hcomm, fun x hx => S127.sq_eq_one_of_mem h.hyp hx⟩
  obtain ⟨hpt, hLT1, -⟩ := S127.Mod.lemma12_7_2_two h1222 h
  obtain ⟨hirr, -⟩ := S127.Mod.lemma12_7_2_three h1222 h
  have hTV1 := S127.Mod.T_le_normalizer_V1 h1222 h
  have hV1ne : V1 T L V ≠ ⊥ := by
    intro hb
    have h4 := hpt.2
    rw [hb, Subgroup.card_bot] at h4
    norm_num at h4
  have hsylLT : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_le h.hyp.sylow le_sup_right
  have hlL : lOne L (V1 T L V) ≤ L ⊓ Subgroup.normalizer (V1 T L V : Set G) := oTwoUpper_le _
  have hirr' : IsIrredOnSection (lOne L (V1 T L V) ⊔ T) V (V1 T L V) := by
    obtain ⟨hlt, -, -, hW⟩ := hirr
    refine ⟨hlt, sup_le (hlL.trans (inf_le_left.trans (S127.Mod.L_le_normalizer h))) hTV,
      sup_le (hlL.trans inf_le_right) hTV1, fun W h1 h2 h3 => hW W h1 h2 ?_⟩
    exact (P1_le h hTV1).trans h3
  have hyp : ∀ H : Subgroup G, InH (P1 T L V ⊔ T) H →
      H ≤ Subgroup.normalizer (V1 T L V : Set G) → AlmostSpecialHyp V (V1 T L V) L T H := by
    intro H hH hHN
    have hTH : T ≤ H := le_sup_right.trans hH.1
    have hlH : lOne L (V1 T L V) ≤ H :=
      (hlL.trans (inf_le_inf_right _ le_sup_left)).trans (hLT1.le.trans hH.1)
    exact
      { elemAbelian := hVab
        ne_bot := hV1ne
        le_V := inf_le_left
        oTwo_eq := eq_oTwoUpper h
        V_le_T := V_le_T h1222 h
        T_le_normV₁ := hTV1
        T_le_normV := hTV
        T_le_normL := h.hyp.normalizes
        sylow_LT := hsylLT
        H_le := hHN
        lOne_sup_le := sup_le hlH hTH
        sylow_H := isSylowTwoOf_of_le h.hyp.sylow hTH
        charTwo := charTwo_of_inH h.hyp.qtke.2.1 (h.hyp.sylow.1.toSylow h.hyp.sylow.2)
          ⟨hTH, hH.2⟩
        irred := hirr' }
  refine ⟨hyp, ?_⟩
  have hP1N : P1 T L V ⊔ T ≤ Subgroup.normalizer (V1 T L V : Set G) := sup_le inf_le_right hTV1
  have hO2 : pCoreOf 2 (Subgroup.normalizer (V1 T L V : Set G)) ≠ ⊥ := by
    have hle : V1 T L V ≤ pCoreOf 2 (Subgroup.normalizer (V1 T L V : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
        (IsPGroup.to_le (hS.hyp.hyp.sylow.1) (inf_le_left.trans (V_le_T h1222 h)))
    intro hb
    rw [hb, le_bot_iff] at hle
    exact hV1ne hle
  have hA := hyp _ ⟨hP1N, hO2⟩ le_rfl
  intro v hv
  have h1 : tmk (V1 T L V) ⟨v, hA.V_le_N hv⟩ ∈ tildeOf (V1 T L V) V := secMk_mem_secImg hv
  have h2 := omegaOneCenterOf_le _ (hA.G22_one.2 (hA.G22_one.1 h1))
  exact (secMk_mem_secImg_iff hA.V₁_le_pCoreOf).1 h2

end CFSG.Quasithin.H13
