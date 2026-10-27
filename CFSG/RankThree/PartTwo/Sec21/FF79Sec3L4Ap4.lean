module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Ap2


public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (KProper InCatalog)

variable {G : Type} [Group G] [Finite G]
variable {b : G} {J B A P D : Subgroup G} {a : G}

theorem sec34_ap_no27 (hs : FF79Sec3 b J) (h : FF79Sec34In b J B A P D)
    (hU : FF79Sec34UFacts b a J A) :
    ∀ T : Subgroup (CQ (U34 b a J A)), (∀ t ∈ T, cqβ (U34 b a J A) b hU.b_nor t = t) →
      ¬ IsElemAb 3 3 T := by
  intro T hT hE
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb3 : orderOf b = 3 := h.hyp.ord
  have hb3' : b ^ 3 = 1 := by rw [← hb3]; exact pow_orderOf_eq_one b
  have hT3 : IsPGroup 3 T := haveI := hE.1; IsElementaryAbelian.isPGroup 3 T
  have hz : IsPGroup 3 (Subgroup.zpowers (1 : ↥(CenS (U34 b a J A)))) :=
    IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers]; simp)
  obtain ⟨T', hT'le, -, hT'3, hcard, hmap⟩ := cq_lift_pgroup hU.b_nor hb3' T hT hT3 1
    (by simp) hz (show (1 : CQ (U34 b a J A)) ∈ T from T.one_mem)
  have hel : IsElementaryAbelian 3 T' :=
    elemAb_of_cqImg hT'3 (fun x hx => (hT'le hx).2) (by rw [hmap]; exact hE.1)
  exact sec34_no27 hs h hU T' hT'le ⟨hel, by rw [hcard]; exact hE.2⟩

theorem sec34_ap_catalog (hG : IsSimpleGroup G) (hna : ∃ x y : G, x * y ≠ y * x)
    (hKp : KProper InCatalog G) (hs : FF79Sec3 b J) (h : FF79Sec34In b J B A P D)
    (hU : FF79Sec34UFacts b a J A) :
    ∀ L : Subgroup (CQ (U34 b a J A)), IsComponent L → IsSimpleGroup ↥L → InCatalog ↥L := by
  intro L hL hLs
  have hnonab : ∃ x y : ↥L, x * y ≠ y * x := by
    obtain ⟨_, _, a', b', hab⟩ := hL.1
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a'
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b'
    exact ⟨x, y, fun hxy => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy])⟩
  have hC : CenS (U34 b a J A) ≠ ⊤ := by
    intro h'
    apply sec34S_b_not_mem hU
    rw [h']
    exact Subgroup.mem_top b
  let f : ↥(CenS (U34 b a J A)) →* CQ (U34 b a J A) :=
    QuotientGroup.mk' (pPrimeCore 3 ↥(CenS (U34 b a J A)))
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  let L₁ : Subgroup ↥(CenS (U34 b a J A)) := L.comap f
  let K : Subgroup G := L₁.map (CenS (U34 b a J A)).subtype
  have hK : K ≠ ⊤ := KCore.map_subtype_ne_top hC L₁
  let e : ↥L₁ ≃* ↥K := L₁.equivMapOfInjective _ (CenS (U34 b a J A)).subtype_injective
  exact KCore.KProperNonab.catalogue_of_surjective Assembly.inCatalog_isoInvariant hKp K hK
    hnonab ((f.subgroupComap L).comp e.symm.toMonoidHom)
    ((f.subgroupComap_surjective L hf).comp e.symm.surjective)

end CFSG.RankThree.PartTwo.Sec21.FF79
