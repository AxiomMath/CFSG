module

public import CFSG.Quasithin.Vol2.Ch11SecBL2OQ
public import CFSG.Quasithin.Vol2.Ch11SecSZK

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique

theorem l2Overgroup_of
    (hF : A312Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK)
    (h39 : A39ForSQTK) (h128 : Lemma128One) (hFSU : Ch10.StmtFSUChoice) : L2Overgroup := by
  intro G _ _ T L I n H K k hS hKf hbad
  have hs := hS.hyp.fsu.simple
  have hnab := hS.hyp.fsu.nonabelian
  have hQ := hS.hyp.fsu.qtke
  have hT := hS.hyp.fsu.sylow
  obtain ⟨Kp, hKKp, hmax, hfKp⟩ := SecS.exists_maximalFaithful_ge hQ hs hnab h37 h128 hT hKf
  have hKH : K ≤ H := by rw [hS.gen]; exact le_sup_left
  set X := H ⊓ Subgroup.normalizer (L : Set G) with hX
  set ψ : ↥K →* ↥(E2.star X H K) :=
    ((QuotientGroup.mk' ((kerIn X H).subgroupOf H)).subgroupMap (K.subgroupOf H)).comp
      (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom with hψ
  have hψs : Function.Surjective ψ :=
    (MonoidHom.subgroupMap_surjective _ _).comp (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective
  have hG' := sqtkHyp_quotient_of_pCoreOf_ne_bot hQ hs hnab hfKp.1.2.2.2
  have h312 := a312_refined hF hG' (h36 _ hG') (h37 _ hG') (h39 _ hG')
  have hq := isQuasisimple_overgroup hS.two_le hbad hKf.1 hfKp.1 hKKp hS.quasisimple ψ hψs h312
  obtain ⟨Ip, hIp⟩ := hFSU G T Kp hs hnab hQ hT hmax hfKp hq
  exact ⟨Kp, Ip, hKKp, hIp⟩

end CFSG.Quasithin.Vol2.Ch11.SecB
