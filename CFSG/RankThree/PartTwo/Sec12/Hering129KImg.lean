module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KSub
public import CFSG.RankThree.PartTwo.Sec12.Hering129HKFK

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Hering129KSub

theorem isSubnormal_subgroupOf_of_map {G : Type} [Group G] {Y : Subgroup G} {P M₀ : Subgroup ↥Y}
    (h : ((P.map Y.subtype).subgroupOf (M₀.map Y.subtype)).IsSubnormal) :
    (P.subgroupOf M₀).IsSubnormal := by
  let e := Subgroup.equivMapOfInjective M₀ Y.subtype Y.subtype_injective
  have heq : (P.subgroupOf M₀).map e.toMonoidHom =
      (P.map Y.subtype).subgroupOf (M₀.map Y.subtype) := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.1, hy, rfl⟩
    · intro hw
      obtain ⟨u, hu, huw⟩ := hw
      obtain ⟨m, hm, hmw⟩ := w.2
      have hum : u = m := Subtype.ext (huw.trans hmw.symm)
      exact ⟨⟨u, hum ▸ hm⟩, hu, Subtype.ext huw⟩
  rw [← heq] at h
  have h2 := h.comap e.toMonoidHom
  rwa [Subgroup.comap_map_eq_self_of_injective e.injective] at h2

end Hering129KSub

theorem image_subnormal_in_resCent {Y : Type} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {t : Y} (ht : t ^ 3 = 1) {X : Subgroup Y}
    (hXR : X ≤ inSubgroup perfectResidual (Subgroup.centralizer ({t} : Set Y)))
    (hXsub : (X.subgroupOf (Subgroup.centralizer ({t} : Set Y))).IsSubnormal) :
    X.map (QuotientGroup.mk' N) ≤ resCent (⊤ : Subgroup (Y ⧸ N)) (QuotientGroup.mk' N t) ∧
      ((X.map (QuotientGroup.mk' N)).subgroupOf
        (resCent (⊤ : Subgroup (Y ⧸ N)) (QuotientGroup.mk' N t))).IsSubnormal := by
  set π := QuotientGroup.mk' N with hπ
  have hRmap := map_resCent_quot N hN ht
  have h1 : X.map π ≤ resCent (⊤ : Subgroup (Y ⧸ N)) (π t) := hRmap ▸ Subgroup.map_mono hXR
  refine ⟨h1, ?_⟩
  set C := Subgroup.centralizer ({t} : Set Y) with hC
  set CQ := Subgroup.centralizer ({π t} : Set (Y ⧸ N)) with hCQ
  have hCCQ : ∀ y ∈ C, π y ∈ CQ := fun y hy => by
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [← map_mul, ← map_mul, hy]
  let ψ : ↥C →* ↥CQ := (π.comp C.subtype).codRestrict CQ (fun y => hCCQ y.1 y.2)
  have hCQmap : C.map π = CQ := Hering129HLift.map_centralizer_eq N hN ht
  have hψ : Function.Surjective ψ := by
    rintro ⟨w, hw⟩
    rw [← hCQmap] at hw
    obtain ⟨y, hy, rfl⟩ := hw
    exact ⟨⟨y, hy⟩, rfl⟩
  have h2 : ((X.subgroupOf C).map ψ).IsSubnormal := hXsub.map hψ
  have heq : (X.subgroupOf C).map ψ = (X.map π).subgroupOf CQ := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.1, hy, rfl⟩
    · intro hw
      obtain ⟨x, hx, hxw⟩ := hw
      have hxC : x ∈ C := (Subgroup.map_subtype_le _ : inSubgroup perfectResidual C ≤ C) (hXR hx)
      exact ⟨⟨x, hxC⟩, hx, Subtype.ext hxw⟩
  rw [heq] at h2
  have hle : resCent (⊤ : Subgroup (Y ⧸ N)) (π t) ≤ CQ :=
    (resCent_le (⊤ : Subgroup (Y ⧸ N)) (π t)).trans inf_le_right
  exact Hering129KSub.isSubnormal_subgroupOf_of_le h2 hle

end CFSG.RankThree.PartTwo.Sec12
