module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenAbstract
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326CompDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

namespace SL3G

section Transport

variable {H : Type} [Group H]

private theorem fixSub_conjNormal {L : Subgroup H} [L.Normal] {a : H} :
    fixSub (MulAut.conjNormal (H := L) a) =
      (Subgroup.centralizer ({a} : Set H)).subgroupOf L := by
  ext x
  rw [mem_fixSub, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have h := congrArg Subtype.val hx
    rw [MulAut.conjNormal_apply] at h
    calc (x : H) * a = (a * x * a⁻¹) * a := by rw [h]
      _ = a * x := by group
  · intro hx
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, ← hx, mul_inv_cancel_right]

private theorem conjNormal_moves {L T : Subgroup H} [L.Normal] {a : H} (hTL : T ≤ L)
    (hnc : ∃ t ∈ T, ⁅t, a⁆ ∉ zOf L) :
    ∃ t ∈ T.subgroupOf L,
      t * ((MulAut.conjNormal (H := L) a) t)⁻¹ ∉ Subgroup.center ↥L := by
  obtain ⟨t, ht, hnot⟩ := hnc
  refine ⟨⟨t, hTL ht⟩, ht, fun hc => hnot ?_⟩
  refine ⟨_, hc, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply,
    commutatorElement_def]
  group

private theorem conjNormal_abelian {L T : Subgroup H} [L.Normal] {a : H} (hTL : T ≤ L)
    (hab : IsMulCommutative ↥(T ⊓ Subgroup.centralizer ({a} : Set H))) :
    IsMulCommutative ↥(T.subgroupOf L ⊓ fixSub (MulAut.conjNormal (H := L) a)) := by
  rw [fixSub_conjNormal]
  haveI : IsMulCommutative ↥(T ⊓ Subgroup.centralizer ({a} : Set H)) := hab
  have hcomm : IsMulCommutative
      ↥((T ⊓ Subgroup.centralizer ({a} : Set H)).comap L.subtype) :=
    Subgroup.comap_injective_isMulCommutative (T ⊓ Subgroup.centralizer ({a} : Set H))
      L.subtype_injective
  have e : T.subgroupOf L ⊓ (Subgroup.centralizer ({a} : Set H)).subgroupOf L =
      (T ⊓ Subgroup.centralizer ({a} : Set H)).comap L.subtype :=
    (Subgroup.comap_inf _ _ _).symm
  rw [e]
  exact hcomm

theorem modelHyp_conjNormal [Finite H] {L T : Subgroup H} [L.Normal] {a : H}
    (hT : IsSylowOf 3 T L) (ha : a ∈ Subgroup.normalizer (T : Set H))
    (ha3 : a ^ 3 ∈ Subgroup.centralizer (L : Set H)) (hnc : ∃ t ∈ T, ⁅t, a⁆ ∉ zOf L)
    (hidx : (Subgroup.centralizer ({a} : Set H)).relIndex T = 3)
    (hab : IsMulCommutative ↥(T ⊓ Subgroup.centralizer ({a} : Set H)))
    (hTnc : ¬ IsMulCommutative ↥T) :
    ModelHyp (MulAut.conjNormal (H := L) a) (T.subgroupOf L) := by
  have hTL : T ≤ L := hT.le
  obtain ⟨Q, hQ⟩ := hT.exists_sylow_eq_subgroupOf
  refine
    { cube := ?_
      pgroup := ?_
      maximal := ?_
      stable := ?_
      nonabelian := ?_
      moves := ?_
      index := ?_
      abelian := ?_ }
  · rw [← map_pow]
    ext x
    rw [MulAut.conjNormal_apply]
    have hc := Subgroup.mem_centralizer_iff.mp ha3 (x : H) x.2
    show a ^ 3 * (x : H) * (a ^ 3)⁻¹ = x
    rw [← hc, mul_inv_cancel_right]
  · rw [← hQ]
    exact Q.isPGroup'
  · intro S hS hTS
    rw [← hQ] at hTS ⊢
    exact Q.is_maximal' hS hTS
  · intro t ht
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    rw [MulAut.conjNormal_apply]
    exact (Subgroup.mem_normalizer_iff.mp ha _).mp ht
  · intro hc
    apply hTnc
    refine ⟨⟨fun x y => ?_⟩⟩
    have h := hc.is_comm.comm (⟨⟨x, hTL x.2⟩, x.2⟩ : ↥(T.subgroupOf L)) ⟨⟨y, hTL y.2⟩, y.2⟩
    exact Subtype.ext (congrArg (fun z : ↥(T.subgroupOf L) => ((z : ↥L) : H)) h)
  · exact conjNormal_moves hTL hnc
  · rw [fixSub_conjNormal, Subgroup.relIndex_subgroupOf hTL]
    exact hidx
  · exact conjNormal_abelian hTL hab

private theorem sup_of_conjNormal {L T : Subgroup H} [L.Normal] {a : H} (hTL : T ≤ L)
    (h : T.subgroupOf L ⊔ fixSub (MulAut.conjNormal (H := L) a) = ⊤) :
    T ⊔ (L ⊓ Subgroup.centralizer ({a} : Set H)) = L := by
  have h1 := congrArg (Subgroup.map L.subtype) h
  rw [Subgroup.map_sup, fixSub_conjNormal, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTL, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h1
  rw [inf_comm]
  exact h1

theorem model_transport {G₀ : Type} [Group G₀] (hG : ModelGen G₀) [Finite H] {L T : Subgroup H}
    (hLn : L.Normal) {a : H} (ψ : G₀ ≃* ↥L) (hT : IsSylowOf 3 T L)
    (ha : a ∈ Subgroup.normalizer (T : Set H))
    (ha3 : a ^ 3 ∈ Subgroup.centralizer (L : Set H)) (hnc : ∃ t ∈ T, ⁅t, a⁆ ∉ zOf L)
    (hidx : (Subgroup.centralizer ({a} : Set H)).relIndex T = 3)
    (hab : IsMulCommutative ↥(T ⊓ Subgroup.centralizer ({a} : Set H)))
    (hTnc : ¬ IsMulCommutative ↥T) :
    T ⊔ (L ⊓ Subgroup.centralizer ({a} : Set H)) = L := by
  haveI := hLn
  have h1 := modelHyp_conjNormal hT ha ha3 hnc hidx hab hTnc
  have h2 := ModelGen.congr ψ hG (MulAut.conjNormal (H := L) a) (T.subgroupOf L) h1
  exact sup_of_conjNormal hT.le h2

end Transport

end SL3G

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
