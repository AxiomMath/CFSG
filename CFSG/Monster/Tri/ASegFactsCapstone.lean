module

public import CFSG.Monster.Tri.ASegFactsA12
public import CFSG.Monster.Tri.ASegThreeC
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3024
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Certificate10069
public import Certificates.Certificate10070
public import Certificates.Certificate10071
public import Certificates.Certificate10072
public import Certificates.Certificate10073
public import Certificates.Certificate10074
public import Certificates.Certificate10075
public import Certificates.Certificate10076
public import Certificates.Certificate8955

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic CFSG.Monster.B.Recog

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

@[expose] def EdgeNbrInQ (a z₀ : G) : Prop :=
  ∀ z : G, IsConj z₀ z → ∀ u v : ConjVert a, z * u = u * z → z * v = v * z →
    (u : G) ∉ leechQ z → (v : G) ∉ leechQ z → (twoAGraph a).Adj u v →
      ∃ w : ConjVert a, (w : G) ∈ leechQ z ∧ (twoAGraph a).Adj w u ∧ (twoAGraph a).Adj w v

theorem twoAGraph_triangulable_of_gms
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (F : ASegFacts a z₀) (hL : LeechGraphFacts a z₀) (h3A : ThreeACommonNbrs a z₀)
    (hGen : ThreeCGenerated a z₀) (h89 : EdgeNbrInQ a z₀) : Triangulable (twoAGraph a) := by
  have ha : orderOf a = 2 := hG.1.1
  have hμ : MuConnected a := aseg_hmu_of I hG F hL h3A
  refine twoAGraph_triangulable_of a (mul_self_eq_one_of_orderOf ha) (ne_one_of_orderOf ha)
    {w : G | IsConj z₀ w} (fun z => (leechQ z : Set G)) (aseg_hinv_of I hG) (aseg_h88_of hμ)
    (aseg_h85_of I hG F)
    (fun z _ _ hz x y hx hy => hL.diam z hz x y hx hy)
    (fun z hzz hz1 hz => aseg_h87_3_of hG z hzz hz1 hz)
    (fun z _ _ hz u v hu hv hQu hQv huv => h89 z hz u v hu hv hQu hQv huv)
    (aseg_h810_of I hG F) (aseg_h83_2_of hG F)
    (fun z hzz hz1 hz => aseg_h813_1_of I hG F z hzz hz1 hz) (aseg_h814_of I hG)
    (fun hnull => aseg_h3C_of I hG F h3A hGen hμ hnull) (aseg_hS4_of I hG F h3A)

end CFSG.Monster.Tri
