module

public import CFSG.RankThree.PartTwo.Sec10.HWNormalizes

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}

theorem Sec13Data.isElemAbelian (h : Sec13Data G A c L) : CFSG.Assembly.IsElemAbelian 3 A :=
  h.mem_partTwoF.1

theorem Sec13Data.card_eq (h : Sec13Data G A c L) : Nat.card A = 27 :=
  h.mem_partTwoE.2.1

theorem Sec13Data.eq_of_le (h : Sec13Data G A c L) {B : Subgroup G}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hAB : A ≤ B) : B = A :=
  h.mem_partTwoF.2.1 B hB hAB

theorem Sec13Data.mem_A (h : Sec13Data G A c L) : c ∈ A :=
  h.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)

theorem Sec13Data.card_zpowers (h : Sec13Data G A c L) : Nat.card (Subgroup.zpowers c) = 3 :=
  h.zpowers_mem_omegaA.2.1

theorem Sec13Data.orderOf_eq (h : Sec13Data G A c L) : orderOf c = 3 := by
  rw [← Nat.card_zpowers]
  exact h.card_zpowers

theorem Sec13Data.ne_one (h : Sec13Data G A c L) : c ≠ 1 := by
  intro h1
  have := h.orderOf_eq
  rw [h1, orderOf_one] at this
  omega

theorem Sec13Data.mem_thetaComponentsAt (h : Sec13Data G A c L) : L ∈ thetaComponentsAt 3 c :=
  h.mem_lA.1

theorem Sec13Data.le_centralizer (h : Sec13Data G A c L) :
    L ≤ Subgroup.centralizer ({c} : Set G) :=
  Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt

theorem Sec13Data.le_normalizer (h : Sec13Data G A c L) :
    A ≤ Subgroup.normalizer (L : Set G) :=
  h.mem_lA.2.1

theorem Sec13Data.sectionCentralizer_eq (h : Sec13Data G A c L) :
    Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G) :=
  h.mem_lA.2.2.1

theorem Sec13Data.commute (h : Sec13Data G A c L) {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    x * y = y * x :=
  congrArg Subtype.val (h.isElemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem Sec13Data.A_le_centralizer (h : Sec13Data G A c L) :
    A ≤ Subgroup.centralizer ({c} : Set G) := fun _ hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr (h.commute hx h.mem_A)

end Data

section Normalizes

variable {G : Type} [Group G] [Finite G]

theorem normalizer_inf_le_of_mem {A : Subgroup G} {c : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hsc : Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G)) {d : G}
    (hdA : d ∈ A) (hdL : d ∈ L) (hdc : d ∉ Subgroup.zpowers c) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  rintro g ⟨hgH, hgW⟩
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  by_contra hne
  set L' := L.map (MulAut.conj g).toMonoidHom with hL'
  have hne' : L' ≠ L := hne
  have hzc : Subgroup.zpowers ((MulAut.conj g) c) = Subgroup.zpowers c := by
    have h1 : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers c :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgH
    rw [MonoidHom.map_zpowers] at h1
    exact h1
  have hL'c : L' ∈ thetaComponentsAt 3 c := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj g) hL
    rw [thetaComponentsAt_eq_thetaComponentsIn,
      Sec10.centralizer_singleton_eq_of_zpowers_eq hzc] at h1
    exact h1
  set d' := g * d * g⁻¹ with hd'
  have hd'A : d' ∈ A := (Subgroup.mem_normalizer_iff.mp hgW d).mp hdA
  have hd'L' : d' ∈ L' := ⟨d, hdL, rfl⟩
  have hd'sc : d' ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
    refine ⟨hd'A, fun x hx => ?_⟩
    have h1 := Sec10.commutator_mem_theta_of_ne hL'c hL hne' hd'L' hx
    have h2 : d' * x * d'⁻¹ * x⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAN hd'A) x).mp hx) (L.inv_mem hx)
    have h3 : d' * x * d'⁻¹ * x⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
      rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hL]
      exact ⟨h2, h1⟩
    exact h3
  rw [hsc] at hd'sc
  apply hdc
  have h1 : g⁻¹ * d' * g⁻¹⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgH) d').mp hd'sc
  have e : g⁻¹ * d' * g⁻¹⁻¹ = d := by
    rw [hd']
    group
  rwa [e] at h1

end Normalizes

end CFSG.RankThree.PartTwo.Sec13
