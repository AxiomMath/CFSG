module

public import CFSG.Quasithin.Vol2.Ch10SecKRSh
public import CFSG.Quasithin.Background.B5NonB
public import CFSG.Quasithin.EmptyFaithful.T1515dA
public import CFSG.Quasithin.Vol2.Ch10SecKIK4b
public import CFSG.Quasithin.Vol2.Ch10SecKIK4c

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.exists_altL5 (c : Conf T L I t w J)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h1026 : Stmt10_2_6)
    (h1011 : Stmt10_1_1) (h1012 : Stmt10_1_2) (h1027 : Stmt10_2_7) (h322 : TmpL6_3_2_2_two)
    (hK8a : FactK8a) (hK8b : FactK8b) (h51 : AsB51)
    (hch : CharTwo (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))))
    (hVe : IsElemAbelian 2 (VI T L I J w)) (hq : CFSG.Open.IsQuasisimple ↥(autI hVe J))
    (e5 : ↥(autI hVe J) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (hCJ : J ⊓ Subgroup.centralizer (VI T L I J w : Set G) = pCoreOf 2 J)
    (hcv : fsuCVM T L I = ⊥) :
    ∃ _ : IsMulCommutative ↥(VI T L I J w),
      AltL5 (autOn J (VI T L I J w)) (commV (autOn J (VI T L I J w))) := by
  have hyp := c.hyp
  set Tw := T ⊓ Subgroup.centralizer ({w} : Set G) with hTw
  set W := VI T L I J w with hW
  have : IsMulCommutative ↥W := hVe.1
  refine ⟨this, ?_⟩
  have hJN : J ≤ Subgroup.normalizer (W : Set G) :=
    le_sup_left.trans (le_normalizer_VI T L I J w)
  obtain ⟨eJ⟩ := nonempty_quotient_equiv hVe hJN hCJ e5
  have hTw2 : IsPGroup 2 Tw := hyp.fsu.sylow.1.to_inf_left
  have hTwJ : Tw ≤ Subgroup.normalizer (J : Set G) := c.Tw_le_normalizer
  have hYL : J ⊔ Tw ≤ Subgroup.normalizer (J : Set G) := sup_le (Subgroup.le_normalizer) hTwJ
  have h2 := InternalSec.two_of_sup hTw2 hTwJ
  have hred := (VI_props hyp c.w_mem_V c.isSylowTwoOf_sup hch).2.2
  have hsl5 : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Bridge.isSimple_sl_zmod2 5 (by norm_num)
  have hsimple : IsSimpleGroup (↥J ⧸ CFSG.pCore 2 ↥J) := eJ.isSimpleGroup
  have hqSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e5 (C10P4F.isQuasisimple_of_open' hq)
  have hqJ : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ.symm hqSL
  have := hyp.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hSQ : SQTKGroup ↥J := B5.sqtk_of_le
    (InternalSec.sqtkGroup_of_localSQTK hK (pCoreOf_centralizer_ne_bot c.w_ne_one c.w_sq)) c.J_le
  have hZ : Subgroup.center ↥(autI hVe J) = ⊥ := by
    have h1 : Nat.card (Subgroup.center ↥(autI hVe J)) = 1 := by
      rw [Nat.card_congr (Subgroup.centerCongr e5).toEquiv,
        C10KH.center_SL_eq_bot (by norm_num) (Nat.card_zmod 2), Subgroup.card_bot]
    exact Subgroup.card_eq_one.1 h1
  have hO : pCoreOf 2 J ≤ Subgroup.centralizer (W : Set G) := hCJ ▸ inf_le_right
  have hJperf : ⁅J, J⁆ = J := perfect_of_mem_cComp c.mem
  have hcV1 : cV1 T L I = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxV : (x : G) ∈ fsuCVM T L I :=
      ⟨SecA.fsuUL_le_fsuVM T L I x.2, Subgroup.mem_subgroupOf.mp hx⟩
    rw [hcv, Subgroup.mem_bot] at hxV
    exact Subgroup.mem_bot.mpr (Subtype.ext hxV)
  have hV1W : fsuUL T L I ≤ W :=
    c.fsuUL_le_VI h37 h38 h1011 h1012 h1027 h322 hK8a hK8b (Or.inr hcV1)
  have hC := centralizer_le_of_fsuUL_le hyp h1026 hV1W
  have hLU : ¬ J ≤ Subgroup.centralizer (W : Set G) := fun h =>
    c.L_not_le_centralizer hC (c.le.trans h)
  have hJT : thompsonJ T ≤ Tw := le_inf (B6.thompsonJ_le T) c.claim.2.2.2.2.1
  have hJRV : ¬ thompsonJ Tw ≤ Subgroup.centralizer (W : Set G) := by
    have heq : thompsonJ Tw = thompsonJ T := B6.thompsonJ_eq_of_le hJT inf_le_left
    rw [heq]
    exact c.not_thompsonJ_le_centralizer h37 h38 h1026 hC
  have hJ := C10KH.commutator_thompsonJ_eq hVe hred le_sup_right hYL h2 hZ hO hJperf hsimple hJRV
  have hB := b51Hyp_1527d c.isSylowTwoOf_sup le_sup_left hYL h2 hVe hred hqJ hsimple hSQ hLU hJ
  have e5' : ↥(autOn J W) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) := e5
  have hN : Nat.card ↥(autOn J W) = 9999360 :=
    (Nat.card_congr e5'.toEquiv).trans (SecA.card_SL_five_of_two (Nat.card_zmod 2))
  have hV2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hVe.2 v v.2)
  exact alt_L5_of_b51 h51 hV2 hB hN

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
