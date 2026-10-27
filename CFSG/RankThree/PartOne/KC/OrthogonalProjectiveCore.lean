module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open CFSG CFSG.RankThree.LocalRank

section Abstract

theorem commute_of_central_p_element {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {R N : Subgroup G} [R.Normal] [N.Normal] (hR : ¬ p ∣ Nat.card R) {z : G} (hzN : z ∈ N)
    (hzc : ∀ n ∈ N, z * n = n * z) (hz : z ^ p = 1) {r : G} (hr : r ∈ R) : r * z = z * r := by
  set w : G := r * z * r⁻¹ with hw
  have hwN : w ∈ N := Subgroup.Normal.conj_mem inferInstance z hzN r
  have hzw : Commute z⁻¹ w := (Commute.inv_left ((hzc w hwN))).symm.symm
  have hu : r * z * r⁻¹ * z⁻¹ ∈ R := by
    have h1 : z * r⁻¹ * z⁻¹ ∈ R := Subgroup.Normal.conj_mem inferInstance r⁻¹ (inv_mem hr) z
    have := mul_mem hr h1
    simpa [mul_assoc] using this
  have hup : (r * z * r⁻¹ * z⁻¹) ^ p = 1 := by
    have h1 : w ^ p = 1 := by
      rw [hw, conj_pow, hz, mul_one, mul_inv_cancel]
    have h2 : (z⁻¹) ^ p = 1 := by rw [inv_pow, hz, inv_one]
    show (w * z⁻¹) ^ p = 1
    rw [(hzw.symm).mul_pow, h1, h2, one_mul]
  have hord1 : orderOf (⟨_, hu⟩ : R) ∣ p := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext hup
  have hord2 : orderOf (⟨_, hu⟩ : R) ∣ Nat.card R := orderOf_dvd_natCard _
  rcases (Nat.dvd_prime hp).mp hord1 with h1 | h1
  · have : (⟨_, hu⟩ : R) = 1 := orderOf_eq_one_iff.mp h1
    have h3 : r * z * r⁻¹ * z⁻¹ = 1 := congrArg Subtype.val this
    calc r * z = (r * z * r⁻¹ * z⁻¹) * z * r⁻¹⁻¹ * 1 := by group
      _ = z * r := by rw [h3]; group
  · exact absurd (h1 ▸ hord2) hR

end Abstract

section Projective

variable {T : Type*} [Group T]

theorem conj_injective_of_center_eq_bot (h : Subgroup.center T = ⊥) :
    Function.Injective (MulAut.conj : T →* MulAut T) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro t
    have h1 := DFunLike.congr_fun hg t
    rw [MulAut.conj_apply] at h1
    have h2 : g * t * g⁻¹ = t := h1
    calc t * g = (g * t * g⁻¹) * g := by rw [h2]
      _ = g * t := by group
  rw [h] at hmem
  exact hmem

variable {B : Subgroup (MulAut T)}

theorem conj_mem_inf_centralizer (hB : (MulAut.conj : T →* MulAut T).range ≤ B) {a n : T}
    (hn : n ∈ Subgroup.centralizer ({a} : Set T)) :
    MulAut.conj n ∈ B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut T)) := by
  refine ⟨hB ⟨n, rfl⟩, ?_⟩
  show MulAut.conj n ∈ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut T))
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
    Subgroup.mem_centralizer_singleton_iff.mp hn]

@[expose] def conjToCentralizer (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (a : T) :
    ↥(Subgroup.centralizer ({a} : Set T)) →*
      ↥(B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut T))) :=
  ((MulAut.conj : T →* MulAut T).comp (Subgroup.centralizer ({a} : Set T)).subtype).codRestrict _
    (fun n => conj_mem_inf_centralizer hB n.2)

theorem coe_conjToCentralizer (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (a : T)
    (n : ↥(Subgroup.centralizer ({a} : Set T))) :
    ((conjToCentralizer hB a n :
      ↥(B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut T)))) : MulAut T) =
        MulAut.conj (n : T) := rfl

theorem conjToCentralizer_injective (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (a : T)
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) :
    Function.Injective (conjToCentralizer hB a) := fun _ _ h =>
  Subtype.ext (hinj (congrArg Subtype.val h))

theorem range_conjToCentralizer_normal (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (a : T)
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) :
    (conjToCentralizer hB a).range.Normal := by
  refine ⟨fun y hy c => ?_⟩
  obtain ⟨n, rfl⟩ := hy
  have hca : (c : MulAut T) a = a := by
    have h1 : (c : MulAut T) * MulAut.conj a = MulAut.conj a * (c : MulAut T) :=
      Subgroup.mem_centralizer_singleton_iff.mp c.2.2
    apply hinj
    have h2 : MulAut.conj ((c : MulAut T) a) =
        (c : MulAut T) * MulAut.conj a * (c : MulAut T)⁻¹ := by
      ext t
      simp [MulAut.conj_apply]
    rw [h2, h1, mul_inv_cancel_right]
  have hcn : (c : MulAut T) n ∈ Subgroup.centralizer ({a} : Set T) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp n.2
    have h3 := congrArg (fun t => (c : MulAut T) t) this
    simp only [map_mul, hca] at h3
    exact h3
  refine ⟨⟨(c : MulAut T) n, hcn⟩, Subtype.ext ?_⟩
  show MulAut.conj ((c : MulAut T) n) = (c : MulAut T) * MulAut.conj (n : T) * (c : MulAut T)⁻¹
  ext t
  simp [MulAut.conj_apply]

theorem isSubnormal_map_of_normal {N' G : Type*} [Group N'] [Group G] (γ : N' →* G)
    (hnorm : γ.range.Normal) {J : Subgroup N'} (hJ : J.Normal) : (J.map γ).IsSubnormal := by
  have hle : J.map γ ≤ γ.range := Subgroup.map_le_range γ J
  refine Subgroup.IsSubnormal.trans hle ?_ hnorm.isSubnormal
  refine Subgroup.Normal.isSubnormal ((Subgroup.normal_subgroupOf_iff hle).mpr ?_)
  intro h k hh hk
  obtain ⟨j, hj, rfl⟩ := hh
  obtain ⟨n, rfl⟩ := hk
  exact ⟨n * j * n⁻¹, hJ.conj_mem j hj n, by simp⟩

theorem isComponent_map_conjToCentralizer (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (a : T)
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T))
    {J : Subgroup ↥(Subgroup.centralizer ({a} : Set T))} (hJ : J.Normal)
    (hq : IsQuasisimple ↥J) : IsComponent (J.map (conjToCentralizer hB a)) :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (J.equivMapOfInjective _ (conjToCentralizer_injective hB a hinj)) hq,
    isSubnormal_map_of_normal _ (range_conjToCentralizer_normal hB a hinj) hJ⟩

theorem map_conjToCentralizer_eq (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (a : T)
    {J : Subgroup T} (hJ : J ≤ Subgroup.centralizer ({a} : Set T)) :
    (J.subgroupOf (Subgroup.centralizer ({a} : Set T))).map (conjToCentralizer hB a) =
      (J.map (MulAut.conj : T →* MulAut T)).subgroupOf
        (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut T))) := by
  ext ⟨c, hc⟩
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, congrArg Subtype.val h⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hJ hj⟩, hj, Subtype.ext rfl⟩

theorem isComponent_conj_subgroupOf (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (a : T)
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) {J : Subgroup T}
    (hJ : J ≤ Subgroup.centralizer ({a} : Set T))
    (hJN : (J.subgroupOf (Subgroup.centralizer ({a} : Set T))).Normal) (hq : IsQuasisimple ↥J) :
    IsComponent ((J.map (MulAut.conj : T →* MulAut T)).subgroupOf
      (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut T)))) := by
  rw [← map_conjToCentralizer_eq hB a hJ]
  exact isComponent_map_conjToCentralizer hB a hinj hJN
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ).symm hq)

section Core

variable [Finite T]

theorem commutator_core_map_conj_eq_bot {p : ℕ} (hp : p.Prime)
    (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (a : T)
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) {J : Subgroup T}
    (hJ : J ≤ Subgroup.centralizer ({a} : Set T))
    (hJN : (J.subgroupOf (Subgroup.centralizer ({a} : Set T))).Normal)
    (hq : IsQuasisimple ↥J) :
    ⁅inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut T))),
      J.map (MulAut.conj : T →* MulAut T)⁆ = ⊥ := by
  set C := B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut T)) with hC
  have hq' : IsQuasisimple ↥(J.subgroupOf (Subgroup.centralizer ({a} : Set T))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ).symm hq
  have hcomp := isComponent_map_conjToCentralizer hB a hinj hJN hq'
  have hsolv := (solvable_prime_complement_core_characterization (H := ↥C) hp).1
  have hsub : (aschbacherSolvableCore p ↥C).IsSubnormal :=
    (inferInstance : (aschbacherSolvableCore p ↥C).Normal).isSubnormal
  have h := (CFSG.LocalCores.component_solvable_centralizer (G := ↥C) hsolv hsub).1 _ hcomp
  have hmap := congrArg (Subgroup.map C.subtype) h
  have e : ((J.subgroupOf (Subgroup.centralizer ({a} : Set T))).map (conjToCentralizer hB a)).map
      C.subtype = J.map (MulAut.conj : T →* MulAut T) := by
    rw [Subgroup.map_map]
    have h1 : C.subtype.comp (conjToCentralizer hB a) =
        (MulAut.conj : T →* MulAut T).comp (Subgroup.centralizer ({a} : Set T)).subtype :=
      MonoidHom.ext fun n => rfl
    rw [h1, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hJ]
  rw [Subgroup.map_commutator, Subgroup.map_bot, e] at hmap
  rw [Subgroup.commutator_comm]
  exact hmap

theorem commute_core_conj_of_central {p : ℕ} (hp : p.Prime)
    (hB : (MulAut.conj : T →* MulAut T).range ≤ B) (a : T)
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T)) {z : T}
    (hzN : z ∈ Subgroup.centralizer ({a} : Set T))
    (hzc : ∀ n ∈ Subgroup.centralizer ({a} : Set T), z * n = n * z) (hz : z ^ p = 1) :
    ∀ s ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut T))),
      s * MulAut.conj z = MulAut.conj z * s := by
  set C := B ⊓ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut T)) with hC
  have hchar := (solvable_prime_complement_core_characterization (H := ↥C) hp).2.1
  have hRn : (aschbacherSolvableCore p ↥C).Normal := by
    have := hchar
    infer_instance
  have hRp := (solvable_prime_complement_core_characterization (H := ↥C) hp).2.2.1
  intro s hs
  obtain ⟨r, hr, rfl⟩ := hs
  have hnorm := range_conjToCentralizer_normal hB a hinj
  have hmem : conjToCentralizer hB a ⟨z, hzN⟩ ∈ (conjToCentralizer hB a).range := ⟨_, rfl⟩
  have hcomm := commute_of_central_p_element (G := ↥C) hp (R := aschbacherSolvableCore p ↥C)
    (N := (conjToCentralizer hB a).range) hRp hmem (z := conjToCentralizer hB a ⟨z, hzN⟩)
    (fun ν hν => by
      obtain ⟨n, rfl⟩ := hν
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (hzc n n.2)))
    (by rw [← map_pow]; exact (by
      have : (⟨z, hzN⟩ : ↥(Subgroup.centralizer ({a} : Set T))) ^ p = 1 :=
        Subtype.ext hz
      rw [this, map_one])) hr
  exact congrArg Subtype.val hcomm

end Core

end Projective

end CFSG.RankThree.PartOne.KCOrthogonal
