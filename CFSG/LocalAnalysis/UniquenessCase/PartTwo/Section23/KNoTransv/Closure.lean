module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_mem_inf {H : Subgroup G} {s : G} (hs : s ∈ normalizer (H : Set G)) {h : G}
    (hh : h ∈ H) : h * s * h⁻¹ * s⁻¹ ∈ H ⊓ conjClosure H s := by
  have hsH : s * h⁻¹ * s⁻¹ ∈ H :=
    ((Subgroup.mem_normalizer_iff.mp hs) h⁻¹).mp (H.inv_mem hh)
  have hmemH : h * s * h⁻¹ * s⁻¹ ∈ H := by
    simpa [mul_assoc] using H.mul_mem hh hsH
  have hconj : h * s * h⁻¹ ∈ conjClosure H s := by
    refine Subgroup.subset_closure ⟨h⁻¹, H.inv_mem hh, ?_⟩
    simp
  have hs' : s ∈ conjClosure H s :=
    Subgroup.subset_closure ⟨1, H.one_mem, by simp⟩
  have hmemC : h * s * h⁻¹ * s⁻¹ ∈ conjClosure H s := by
    simpa [mul_assoc] using (conjClosure H s).mul_mem hconj ((conjClosure H s).inv_mem hs')
  exact Subgroup.mem_inf.mpr ⟨hmemH, hmemC⟩

theorem conj_mem_inf {H : Subgroup G} {s : G} {h n : G} (hh : h ∈ H)
    (hn : n ∈ H ⊓ conjClosure H s) : h * n * h⁻¹ ∈ H ⊓ conjClosure H s := by
  have hmemH : h * n * h⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem hh hn.1) (H.inv_mem hh)
  have hmap : (conjClosure H s).map (MulAut.conj h : G →* G) ≤ conjClosure H s := by
    rw [conjClosure, MonoidHom.map_closure]
    refine (Subgroup.closure_le (conjClosure H s)).mpr ?_
    rintro x ⟨y, ⟨g, hg, rfl⟩, rfl⟩
    refine Subgroup.subset_closure ⟨g * h⁻¹, H.mul_mem hg (H.inv_mem hh), ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hmemC : h * n * h⁻¹ ∈ conjClosure H s := by
    have hmn : (MulAut.conj h : G →* G) n ∈
        (conjClosure H s).map (MulAut.conj h : G →* G) :=
      Subgroup.mem_map.mpr ⟨n, hn.2, rfl⟩
    simpa [MulAut.conj_apply] using hmap hmn
  exact Subgroup.mem_inf.mpr ⟨hmemH, hmemC⟩

theorem conj_eq_of_commutator_mem_centralizer {H : Subgroup G} (hH : ⁅H, H⁆ = H) {s : G}
    (hs : s ∈ normalizer (H : Set G))
    (hc : ∀ h ∈ H, h * s * h⁻¹ * s⁻¹ ∈ centralizer (H : Set G)) {h : G} (hh : h ∈ H) :
    s * h * s⁻¹ = h := by
  let cFun : ↥H → ↥H := fun x =>
    ⟨(x : G) * s * (x : G)⁻¹ * s⁻¹, by
      have hxH : s * (x : G)⁻¹ * s⁻¹ ∈ H :=
        ((Subgroup.mem_normalizer_iff.mp hs) (x : G)⁻¹).mp (H.inv_mem x.2)
      simpa [mul_assoc] using H.mul_mem x.2 hxH⟩
  have hcFun_center : ∀ x : ↥H, cFun x ∈ center ↥H := by
    intro x
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hc (x : G) x.2) (g : G) g.2
  have hcFun_mul : ∀ x y : ↥H, cFun (x * y) = cFun x * cFun y := by
    intro x y
    apply Subtype.ext
    have hxcy : (x : G) * ((y : G) * s * (y : G)⁻¹ * s⁻¹) =
        ((y : G) * s * (y : G)⁻¹ * s⁻¹) * (x : G) := by
      simpa [cFun] using
        congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcFun_center y) x)
    have hcxy : ((x : G) * s * (x : G)⁻¹ * s⁻¹) *
        ((y : G) * s * (y : G)⁻¹ * s⁻¹) =
        ((y : G) * s * (y : G)⁻¹ * s⁻¹) *
          ((x : G) * s * (x : G)⁻¹ * s⁻¹) := by
      simpa [cFun] using
        (congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcFun_center x) (cFun y))).symm
    change (x : G) * (y : G) * s * ((x : G) * (y : G))⁻¹ * s⁻¹ =
      ((x : G) * s * (x : G)⁻¹ * s⁻¹) * ((y : G) * s * (y : G)⁻¹ * s⁻¹)
    rw [mul_inv_rev]
    calc (x : G) * (y : G) * s * ((y : G)⁻¹ * (x : G)⁻¹) * s⁻¹
        = (x : G) * ((y : G) * s * (y : G)⁻¹ * s⁻¹) * s * (x : G)⁻¹ * s⁻¹ := by
          group
      _ = ((y : G) * s * (y : G)⁻¹ * s⁻¹) * (x : G) * s * (x : G)⁻¹ * s⁻¹ := by
          rw [hxcy]
      _ = ((y : G) * s * (y : G)⁻¹ * s⁻¹) *
            ((x : G) * s * (x : G)⁻¹ * s⁻¹) := by
          group
      _ = ((x : G) * s * (x : G)⁻¹ * s⁻¹) *
            ((y : G) * s * (y : G)⁻¹ * s⁻¹) := hcxy.symm
  have hcFun_one : cFun 1 = 1 := by
    apply Subtype.ext
    change (1 : G) * s * (1 : G)⁻¹ * s⁻¹ = 1
    simp
  let c : ↥H →* ↥H := { toFun := cFun, map_one' := hcFun_one, map_mul' := hcFun_mul }
  have hcomm_le : ⁅H, H⁆ ≤ (c.ker).map H.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    let x' : ↥H := ⟨x, hx⟩
    let y' : ↥H := ⟨y, hy⟩
    have hcx : c x' ∈ center ↥H := hcFun_center x'
    have hcomm1 : c ⁅x', y'⁆ = 1 := by
      rw [map_commutatorElement]
      exact Commute.commutator_eq (Subgroup.mem_center_iff.mp hcx (c y')).symm
    have hker : ⁅x', y'⁆ ∈ c.ker := MonoidHom.mem_ker.mpr hcomm1
    refine Subgroup.mem_map.mpr ⟨⁅x', y'⁆, hker, ?_⟩
    simpa [x', y'] using map_commutatorElement H.subtype x' y'
  have hH_le : H ≤ (c.ker).map H.subtype := by
    simpa [hH] using hcomm_le
  have hc1 : h * s * h⁻¹ * s⁻¹ = 1 := by
    have hmem : (⟨h, hh⟩ : ↥H) ∈ c.ker := by
      rcases Subgroup.mem_map.mp (hH_le hh) with ⟨z, hz, hzval⟩
      have hzeq : z = ⟨h, hh⟩ := Subtype.ext hzval
      simpa [hzeq] using hz
    have hval := congrArg Subtype.val (MonoidHom.mem_ker.mp hmem)
    change (cFun ⟨h, hh⟩ : G) = 1 at hval
    simpa [cFun] using hval
  have h1 : h * s * h⁻¹ = s := by
    calc h * s * h⁻¹ = (h * s * h⁻¹) * s⁻¹ * s := by group
      _ = 1 * s := by rw [hc1]
      _ = s := one_mul s
  have h2 : h * s = s * h := by
    calc h * s = h * s * h⁻¹ * h := by group
      _ = s * h := by rw [h1]
  calc s * h * s⁻¹ = h * s * s⁻¹ := by rw [← h2]
    _ = h := by group

theorem le_conjClosure_of_map_eq_top {H : Subgroup G} (hH : ⁅H, H⁆ = H) {s : G} {S : Type*}
    [Group S] (f : ↥H →* S) (hker : f.ker ≤ center ↥H)
    (htop : ((H ⊓ conjClosure H s).subgroupOf H).map f = ⊤) : H ≤ conjClosure H s := by
  let N : Subgroup ↥H := (H ⊓ conjClosure H s).subgroupOf H
  have htopN : N.map f = ⊤ := htop
  have hdec : ∀ x : ↥H, ∃ n ∈ N, ∃ z ∈ center ↥H, x = n * z := by
    intro x
    have hfx : f x ∈ N.map f := by
      rw [htopN]
      exact Subgroup.mem_top (f x)
    rcases Subgroup.mem_map.mp hfx with ⟨n, hnN, hfn⟩
    refine ⟨n, hnN, n⁻¹ * x, ?_, ?_⟩
    · apply hker
      rw [MonoidHom.mem_ker]
      simp [hfn]
    · group
  have hcomm_le : ⁅H, H⁆ ≤ conjClosure H s := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    let x' : ↥H := ⟨x, hx⟩
    let y' : ↥H := ⟨y, hy⟩
    obtain ⟨n, hnN, z, hz, hxz⟩ := hdec x'
    obtain ⟨m, hmN, w, hw, hyw⟩ := hdec y'
    have hcomm_eq : ⁅x', y'⁆ = ⁅n, m⁆ := by
      rw [hxz, hyw, commutatorElement_def, commutatorElement_def]
      have hz1 : Commute z (m * w) := (Subgroup.mem_center_iff.mp hz (m * w)).symm
      have hw1 : Commute w n := (Subgroup.mem_center_iff.mp hw n).symm
      calc (n * z) * (m * w) * (n * z)⁻¹ * (m * w)⁻¹
          = n * (z * (m * w) * z⁻¹) * n⁻¹ * (m * w)⁻¹ := by group
        _ = n * (m * w) * n⁻¹ * (m * w)⁻¹ := by
            rw [hz1.eq, mul_inv_cancel_right]
        _ = n * m * (w * n⁻¹ * w⁻¹) * m⁻¹ := by group
        _ = n * m * n⁻¹ * m⁻¹ := by
            rw [hw1.inv_right.eq, mul_inv_cancel_right]
    have hnmN : ⁅n, m⁆ ∈ N :=
      (Subgroup.commutator_le_self N) (Subgroup.commutator_mem_commutator hnN hmN)
    have hnm_inf : ((⁅n, m⁆ : ↥H) : G) ∈ H ⊓ conjClosure H s :=
      Subgroup.mem_subgroupOf.mp hnmN
    have hval : ((⁅n, m⁆ : ↥H) : G) = ⁅x, y⁆ := by
      rw [← hcomm_eq]
      exact map_commutatorElement H.subtype x' y'
    rw [hval] at hnm_inf
    exact hnm_inf.2
  simpa [hH] using hcomm_le

theorem le_conjClosure_of_simple {H : Subgroup G} (hH : ⁅H, H⁆ = H) {s : G}
    (hs : s ∈ normalizer (H : Set G)) {S : Type*} [Group S] [IsSimpleGroup S] (f : ↥H →* S)
    (hf : Function.Surjective f) (hker : f.ker ≤ center ↥H) (hsH : ∃ h ∈ H, s * h * s⁻¹ ≠ h) :
    H ≤ conjClosure H s := by
  let N : Subgroup G := H ⊓ conjClosure H s
  have hNleH : N ≤ H := inf_le_left
  have hNnormal : (N.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNleH]
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact conj_mem_inf hh hn
    · intro hn
      simpa [N, mul_assoc] using conj_mem_inf (H.inv_mem hh) hn
  haveI : ((N.subgroupOf H).map f).Normal := hNnormal.map f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf H).map f) with hbot | htop
  · have hNker : N.subgroupOf H ≤ f.ker := by
      intro x hx
      have hfx : f x ∈ (N.subgroupOf H).map f := Subgroup.mem_map_of_mem f hx
      rw [hbot] at hfx
      simpa [MonoidHom.mem_ker] using hfx
    have hcs : ∀ h ∈ H, h * s * h⁻¹ * s⁻¹ ∈ centralizer (H : Set G) := by
      intro h hh
      have hmemN : h * s * h⁻¹ * s⁻¹ ∈ N := by
        simpa [N] using commutator_mem_inf hs hh
      let x : ↥H := ⟨h * s * h⁻¹ * s⁻¹, (commutator_mem_inf hs hh).1⟩
      have hxN : x ∈ N.subgroupOf H := by
        rw [Subgroup.mem_subgroupOf]
        exact hmemN
      have hxcenter : x ∈ center ↥H := hker (hNker hxN)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxcenter ⟨y, hy⟩)
    obtain ⟨k, hk, hne⟩ := hsH
    exact (hne (conj_eq_of_commutator_mem_centralizer hH hs hcs hk)).elim
  · exact le_conjClosure_of_map_eq_top hH f hker (by simpa [N] using htop)

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
