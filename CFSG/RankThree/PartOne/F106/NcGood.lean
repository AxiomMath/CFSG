module

public import CFSG.RankThree.PartOne.F106.NcTheta
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.GroupTheory.ThetaComponents

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank
open scoped Pointwise

theorem perfectResidual_sup_core_decomposition {G : Type} [Group G] [Finite G] {p : ℕ}
    {C H : Subgroup G} (hCH : C ≤ H) :
    ∀ u ∈ inSubgroup perfectResidual (C ⊔ inSubgroup (aschbacherSolvableCore p) H),
      ∃ a ∈ inSubgroup perfectResidual C, ∃ t ∈ inSubgroup (aschbacherSolvableCore p) H,
        u = a * t := by
  set N := inSubgroup (aschbacherSolvableCore p) H with hN
  set P := inSubgroup perfectResidual C with hP
  set X := C ⊔ N with hX
  set Y := P ⊔ N with hY
  have hNH : N ≤ H := Subgroup.map_subtype_le _
  have hPC : P ≤ C := Subgroup.map_subtype_le _
  have hNn : (N.subgroupOf H).Normal := by
    have h : N.subgroupOf H = aschbacherSolvableCore p H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [h]
    infer_instance
  have hHN : H ≤ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hNn
  have hCN : C ≤ Subgroup.normalizer (N : Set G) := hCH.trans hHN
  have hPn : C ≤ Subgroup.normalizer (P : Set G) := by
    have hn : (P.subgroupOf C).Normal := by
      have h : P.subgroupOf C = perfectResidual ↥C :=
        Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
      rw [h]
      infer_instance
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hPC).mp hn
  have hXset : (X : Set G) = (C : Set G) * (N : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right C N hCN
  have hYset : (Y : Set G) = (P : Set G) * (N : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right P N (hPC.trans hCN)
  have hYX : Y ≤ X := sup_le_sup hPC le_rfl
  have hCX : C ≤ X := le_sup_left
  have hXnorm : X ≤ Subgroup.normalizer (Y : Set G) := by
    refine sup_le ?_ (le_sup_right.trans Subgroup.le_normalizer)
    exact (le_inf hPn hCN).trans (Subgroup.inf_normalizer_le_normalizer_sup P N)
  have hYn : (Y.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hXnorm
  let f : ↥C →* ↥X ⧸ Y.subgroupOf X :=
    (QuotientGroup.mk' (Y.subgroupOf X)).comp (Subgroup.inclusion hCX)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    have hm : (m : G) ∈ (X : Set G) := m.2
    rw [hXset] at hm
    obtain ⟨c, hc, t, ht, hct⟩ := hm
    refine ⟨⟨c, hc⟩, ?_⟩
    show QuotientGroup.mk' (Y.subgroupOf X) (Subgroup.inclusion hCX ⟨c, hc⟩) = (m : _)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h : ((Subgroup.inclusion hCX ⟨c, hc⟩)⁻¹ * m : ↥X) = (t : G) := by
      change c⁻¹ * (m : G) = t
      rw [← hct]
      group
    rw [h]
    exact (le_sup_right : N ≤ Y) ht
  have hker : perfectResidual ↥C ≤ f.ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' (Y.subgroupOf X) (Subgroup.inclusion hCX y) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact (le_sup_left : P ≤ Y) (show (y : G) ∈ P from ⟨y, hy, rfl⟩)
  have hsolvC : Group.IsSolvable (↥C ⧸ f.ker) :=
    ((perfect_residual_characterization (G := ↥C)).2.2.2.2.1 f.ker).mpr hker
  have hsolv : Group.IsSolvable (↥X ⧸ Y.subgroupOf X) :=
    Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientKerEquivOfSurjective f hf).toMonoidHom)
      (QuotientGroup.quotientKerEquivOfSurjective f hf).surjective
  have hres : perfectResidual ↥X ≤ Y.subgroupOf X :=
    ((perfect_residual_characterization (G := ↥X)).2.2.2.2.1 (Y.subgroupOf X)).mp hsolv
  intro u hu
  obtain ⟨w, hw, rfl⟩ := hu
  have hwY : (w : G) ∈ Y := hres hw
  have hwY' : (w : G) ∈ (Y : Set G) := hwY
  rw [hYset] at hwY'
  obtain ⟨a, ha, t, ht, hat⟩ := hwY'
  exact ⟨a, ha, t, ht, hat.symm⟩

theorem core_le_of_decomposition {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {x : G}
    {P U : Subgroup G} (hU : U ∈ thetaComponentsAt p x) (hPU : P ≤ U)
    (hdec : ∀ u ∈ U, ∃ a ∈ P,
      ∃ t ∈ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({x} : Set G)), u = a * t) :
    inSubgroup (aschbacherSolvableCore p) P ≤
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({x} : Set G)) := by
  set θH := inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({x} : Set G)) with hθH
  have hθU : inSubgroup (aschbacherSolvableCore p) U = U ⊓ θH :=
    theta_eq_inf_of_mem_thetaComponentsAt hp hU
  set SG := inSubgroup (aschbacherSolvableCore p) P with hSG
  have hSP : SG ≤ P := Subgroup.map_subtype_le _
  have hSU : SG ≤ U := hSP.trans hPU
  have hmemθ : ∀ t : ↥U, t ∈ aschbacherSolvableCore p ↥U ↔ (t : G) ∈ θH := fun t => by
    have h : ((t : ↥U) : G) ∈ inSubgroup (aschbacherSolvableCore p) U ↔
        t ∈ aschbacherSolvableCore p ↥U := Subgroup.mem_map_iff_mem U.subtype_injective
    rw [← h, hθU]
    exact ⟨fun h => h.2, fun h => ⟨t.2, h⟩⟩
  obtain ⟨hθPsol, -, hθPp, -⟩ := solvable_prime_complement_core_characterization (H := ↥P) hp
  have hSGsol : Group.IsSolvable SG :=
    Group.isSolvable_of_surjective
      (f := ((aschbacherSolvableCore p ↥P).equivMapOfInjective P.subtype
        P.subtype_injective).toMonoidHom)
      ((aschbacherSolvableCore p ↥P).equivMapOfInjective P.subtype P.subtype_injective).surjective
  set S : Subgroup ↥U := SG.subgroupOf U with hS
  have hSsol : Group.IsSolvable S :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hSU).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hSU).injective
  have hSp : ¬ p ∣ Nat.card S := by
    have hc : Nat.card SG = Nat.card (aschbacherSolvableCore p ↥P) :=
      Subgroup.card_map_of_injective P.subtype_injective
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSU).toEquiv, hc]
    exact hθPp
  have hNorm : (S.map (QuotientGroup.mk' (aschbacherSolvableCore p ↥U))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨s, hs, rfl⟩ := hn
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨a, ha, t, ht, hat⟩ := hdec u u.2
    have haU : a ∈ U := hPU ha
    have htU : t ∈ U := by
      have h : t = a⁻¹ * (u : G) := by rw [hat]; group
      rw [h]
      exact U.mul_mem (U.inv_mem haU) u.2
    have htθ : (⟨t, htU⟩ : ↥U) ∈ aschbacherSolvableCore p ↥U := (hmemθ ⟨t, htU⟩).mpr ht
    have hu : u = ⟨a, haU⟩ * ⟨t, htU⟩ := Subtype.ext hat
    have hπt : QuotientGroup.mk' (aschbacherSolvableCore p ↥U) ⟨t, htU⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr htθ
    refine ⟨⟨a, haU⟩ * s * ⟨a, haU⟩⁻¹, ?_, ?_⟩
    ·
      have hsG : (s : G) ∈ SG := hs
      obtain ⟨s₀, hs₀, hs₀e⟩ := hsG
      have hconj := (inferInstance : (aschbacherSolvableCore p ↥P).Normal).conj_mem s₀ hs₀
        (⟨a, ha⟩ : ↥P)
      show (⟨a, haU⟩ * s * ⟨a, haU⟩⁻¹ : ↥U) ∈ SG.subgroupOf U
      rw [Subgroup.mem_subgroupOf]
      refine ⟨(⟨a, ha⟩ : ↥P) * s₀ * (⟨a, ha⟩ : ↥P)⁻¹, hconj, ?_⟩
      have hs₀e' : (s₀ : G) = (s : G) := hs₀e
      change (a * (s₀ : G) * a⁻¹ : G) = a * (s : G) * a⁻¹
      rw [hs₀e']
    · have hq : QuotientGroup.mk' (aschbacherSolvableCore p ↥U) u =
          QuotientGroup.mk' (aschbacherSolvableCore p ↥U) ⟨a, haU⟩ := by
        rw [hu, map_mul, hπt, mul_one]
      show QuotientGroup.mk' (aschbacherSolvableCore p ↥U) (⟨a, haU⟩ * s * ⟨a, haU⟩⁻¹) =
        QuotientGroup.mk' (aschbacherSolvableCore p ↥U) u *
          QuotientGroup.mk' (aschbacherSolvableCore p ↥U) s *
          (QuotientGroup.mk' (aschbacherSolvableCore p ↥U) u)⁻¹
      rw [hq, map_mul, map_mul, map_inv]
  have hle := le_aschbacherSolvableCore_of_map_normal hp S hSsol hSp hNorm
  intro s hs
  have h1 : (⟨s, hSU hs⟩ : ↥U) ∈ S := (Subgroup.mem_subgroupOf).mpr hs
  exact (hmemθ ⟨s, hSU hs⟩).mp (hle h1)

end CFSG.RankThree.PartOne.F106
