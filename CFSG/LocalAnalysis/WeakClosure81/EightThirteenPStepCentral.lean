module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup

variable {Q : Type} [Group Q] [Finite Q]

private theorem wc813pscen_commute_of_sq_one {G : Type*} [Group G] {u v : G}
    (hu : u * u = 1) (hv : v * v = 1) (huv : (u * v) * (u * v) = 1) : u * v = v * u := by
  calc u * v = (u * v)⁻¹ := eq_inv_of_mul_eq_one_right huv
    _ = v⁻¹ * u⁻¹ := mul_inv_rev u v
    _ = v * u := by rw [inv_eq_of_mul_eq_one_right hv, inv_eq_of_mul_eq_one_right hu]

private theorem wc813pscen_pairwise_commute {G : Type*} [Group G] {u : G}
    (h : ∀ w : G, Commute u (w * u * w⁻¹)) :
    (Group.conjugatesOfSet ({u} : Set G)).Pairwise Commute := by
  intro x hx y hy _
  obtain ⟨x', hx', hcx⟩ := (Group.mem_conjugatesOfSet_iff).1 hx
  rw [Set.mem_singleton_iff] at hx'
  subst x'
  obtain ⟨a, ha⟩ := isConj_iff.1 hcx
  obtain ⟨y', hy', hcy⟩ := (Group.mem_conjugatesOfSet_iff).1 hy
  rw [Set.mem_singleton_iff] at hy'
  subst y'
  obtain ⟨b, hb⟩ := isConj_iff.1 hcy
  rw [← ha, ← hb]
  have h0 : Commute (a * u * a⁻¹) (a * ((a⁻¹ * b) * u * (a⁻¹ * b)⁻¹) * a⁻¹) :=
    (h (a⁻¹ * b)).conj a
  convert h0 using 1 <;> group

theorem central_of_commuting_conjugates {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) {s : Q} (hsJ : s ∈ J) (hs : s * s = 1)
    (h : ∀ w ∈ J, ∀ l ∈ J, ((s * (w * s * w⁻¹)) * (s * (w * s * w⁻¹))) * l =
      l * ((s * (w * s * w⁻¹)) * (s * (w * s * w⁻¹)))) :
    ∀ l ∈ J, s * l = l * s := by
  classical
  let π : ↥J →* (↥J ⧸ Subgroup.center ↥J) := QuotientGroup.mk' (Subgroup.center ↥J)
  let u : ↥J ⧸ Subgroup.center ↥J := π ⟨s, hsJ⟩
  have hsG : (⟨s, hsJ⟩ : ↥J) * ⟨s, hsJ⟩ = 1 := by
    apply Subtype.ext
    simpa using hs
  have hu2 : u * u = 1 := by
    change π ⟨s, hsJ⟩ * π ⟨s, hsJ⟩ = 1
    rw [← map_mul, hsG, map_one]
  have hkey : ∀ w : ↥J, Commute u (π w * u * (π w)⁻¹) := by
    intro w
    let e : ↥J := ⟨s, hsJ⟩ * (w * ⟨s, hsJ⟩ * w⁻¹)
    have hec : e * e ∈ Subgroup.center ↥J := by
      change (⟨s, hsJ⟩ * (w * ⟨s, hsJ⟩ * w⁻¹)) *
          (⟨s, hsJ⟩ * (w * ⟨s, hsJ⟩ * w⁻¹)) ∈ Subgroup.center ↥J
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      simpa [e, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using
        (h (w : Q) w.2 (l : Q) l.2).symm
    have hπ : π (e * e) = 1 :=
      (QuotientGroup.eq_one_iff (N := Subgroup.center ↥J) (e * e)).mpr hec
    have hπe : π e = u * (π w * u * (π w)⁻¹) := by
      simp only [e, map_mul, map_inv, u]
    have hsq : (u * (π w * u * (π w)⁻¹)) * (u * (π w * u * (π w)⁻¹)) = 1 := by
      rw [← hπe, ← map_mul]
      exact hπ
    have hv2 : (π w * u * (π w)⁻¹) * (π w * u * (π w)⁻¹) = 1 := by
      have hconj := congrArg (fun t => π w * t * (π w)⁻¹) hu2
      simpa [mul_assoc] using hconj
    exact wc813pscen_commute_of_sq_one hu2 hv2 hsq
  have hkey' : ∀ c : ↥J ⧸ Subgroup.center ↥J, Commute u (c * u * c⁻¹) := by
    intro c
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J) c
    exact hkey w
  have hcomm : IsMulCommutative ↥(Subgroup.normalClosure
      ({u} : Set (↥J ⧸ Subgroup.center ↥J))) := by
    change IsMulCommutative ↥(closure (Group.conjugatesOfSet
      ({u} : Set (↥J ⧸ Subgroup.center ↥J))))
    exact Subgroup.isMulCommutative_closure (wc813pscen_pairwise_commute hkey')
  haveI : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
  haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2
  haveI : Group.IsPerfect (↥J ⧸ Subgroup.center ↥J) := inferInstance
  have hMnontop : Subgroup.normalClosure ({u} : Set (↥J ⧸ Subgroup.center ↥J)) ≠ ⊤ := by
    intro htop
    have hcommTop : IsMulCommutative ↥(⊤ : Subgroup (↥J ⧸ Subgroup.center ↥J)) :=
      htop ▸ hcomm
    have hcommJb : IsMulCommutative (↥J ⧸ Subgroup.center ↥J) :=
      (Subgroup.topEquiv (G := ↥J ⧸ Subgroup.center ↥J)).surjective.isMulCommutative hcommTop
    exact Group.IsPerfect.not_isMulCommutative (↥J ⧸ Subgroup.center ↥J) hcommJb
  have hMbot : Subgroup.normalClosure ({u} : Set (↥J ⧸ Subgroup.center ↥J)) = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure ({u} : Set (↥J ⧸ Subgroup.center ↥J)))).resolve_right hMnontop
  have hu_mem : u ∈ Subgroup.normalClosure ({u} : Set (↥J ⧸ Subgroup.center ↥J)) :=
    Subgroup.subset_normalClosure (Set.mem_singleton u)
  have hu1 : u = 1 := by
    rw [hMbot] at hu_mem
    exact Subgroup.mem_bot.mp hu_mem
  have hs_center : (⟨s, hsJ⟩ : ↥J) ∈ Subgroup.center ↥J := by
    have h1 : ((⟨s, hsJ⟩ : ↥J) : ↥J ⧸ Subgroup.center ↥J) = 1 := hu1
    exact (QuotientGroup.eq_one_iff (⟨s, hsJ⟩ : ↥J)).mp h1
  intro l hl
  have hcl := (Subgroup.mem_center_iff.mp hs_center) ⟨l, hl⟩
  have hcoe := congrArg (Subtype.val) hcl
  simpa [Subgroup.coe_mul] using hcoe.symm

end CFSG.LocalAnalysis.WeakClosure81

end
