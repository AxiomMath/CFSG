module

public import CFSG.RankThree.GroupTheory.SteinbergCEThetaQuotientAction
import CFSG.GroupTheory.SolvableHallNodes
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.LocalRank.ThetaCoreQuotients
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.GroupTheory

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank

theorem conj_mem_inSubgroup_perfectResidual {H : Type*} [Group H] {X : Subgroup H} {g x : H}
    (hg : g ∈ X) (hx : x ∈ inSubgroup perfectResidual X) :
    g * x * g⁻¹ ∈ inSubgroup perfectResidual X := by
  obtain ⟨y, hy, rfl⟩ := hx
  have : (perfectResidual X).Normal := inferInstance
  exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, this.conj_mem y hy _, rfl⟩

theorem theta_component_trivial_quotient_action_fixed_residual {L D : Type*} [Group L]
    [Finite L] [Group D] [Finite D] [MulDistribMulAction D L] {p : ℕ} (hp : p.Prime)
    (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore p L))
    (hD : IsPGroup p D)
    (htriv : ∀ (d : D) (l : L),
      ((d • l : L) : L ⧸ aschbacherSolvableCore p L) = (l : L ⧸ aschbacherSolvableCore p L)) :
    aschbacherSolvableCore p L ⊔ inSubgroup perfectResidual (fixedPointSubgroup D L) = ⊤ ∧
      perfectResidual (fixedPointSubgroup D L) ∈ thetaComponents p (fixedPointSubgroup D L) := by
  have : Fact p.Prime := ⟨hp⟩
  set N := aschbacherSolvableCore p L
  set C := fixedPointSubgroup D L
  set π := QuotientGroup.mk' N
  obtain ⟨hNsol, hNchar, hNp, -⟩ := solvable_prime_complement_core_characterization (H := L) hp
  have hNinv : IsInvariant D L N := by
    refine ⟨fun d g => ?_⟩
    have h := Subgroup.characteristic_iff_comap_eq.mp hNchar (MulDistribMulAction.toMulAut D L d)
    constructor
    · intro hg
      have hg' : g ∈ (aschbacherSolvableCore p L).comap
          (MulDistribMulAction.toMulAut D L d).toMonoidHom := by
        rw [h]
        exact hg
      exact hg'
    · intro hg
      have hg' : g ∈ N.comap (MulDistribMulAction.toMulAut D L d).toMonoidHom := hg
      rwa [h] at hg'
  have hcop : Nat.Coprime (Nat.card D) (Nat.card N) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hD
    rw [hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hNp)
  have hlift := CFSG.SolvableHall.coprime_solvable_kernel_fixed_point_lifting N hNinv hNsol hcop
  have hCtop : C.map π = ⊤ := by
    let : MulDistribMulAction D (L ⧸ N) :=
      CFSG.quotientMulDistribMulAction (A := D) (G := L) N hNinv
    let : MulAction.QuotientAction D N := CFSG.quotientAction_of_isInvariant (A := D) N hNinv
    rw [← hlift, eq_top_iff]
    intro q _
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    intro d
    rw [MulAction.Quotient.smul_coe (H := N) d l]
    exact htriv d l
  set g : C →* L ⧸ N := π.comp C.subtype
  have hg : Function.Surjective g := by
    intro q
    obtain ⟨c, hc, hcq⟩ := (Subgroup.mem_map.mp (hCtop ▸ Subgroup.mem_top q :
      q ∈ C.map π))
    exact ⟨⟨c, hc⟩, hcq⟩
  have hgker : ∀ c : C, g c = 1 ↔ (c : L) ∈ N := fun c => by
    change π c = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hQcore : aschbacherSolvableCore p (L ⧸ N) = ⊥ :=
    (solvable_prime_complement_core_quotient_centralizers (G := L) hp N hNsol hNp).2.2.1
  have hθC : aschbacherSolvableCore p C = N.subgroupOf C := by
    apply le_antisymm
    · obtain ⟨hCsol, -, hCp, -⟩ := solvable_prime_complement_core_characterization (H := C) hp
      have himgN : ((aschbacherSolvableCore p C).map g).Normal :=
        Subgroup.Normal.map inferInstance g hg
      have himgS : Group.IsSolvable ((aschbacherSolvableCore p C).map g) :=
        Group.isSolvable_of_surjective (g.subgroupMap_surjective _)
      have himgP : ¬ p ∣ Nat.card ((aschbacherSolvableCore p C).map g) :=
        fun h => hCp (h.trans (Subgroup.card_map_dvd _ g))
      have hle := (solvable_prime_complement_core_characterization (H := L ⧸ N) hp).2.2.2.1 _
        himgN himgS himgP
      rw [hQcore] at hle
      intro c hc
      have h1 : g c = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_map_of_mem g hc))
      exact Subgroup.mem_subgroupOf.mpr ((hgker c).mp h1)
    · let f : N.subgroupOf C →* N :=
        MonoidHom.codRestrict (C.subtype.comp (N.subgroupOf C).subtype) N fun x => x.2
      have hf : Function.Injective f := by
        intro x y hxy
        have h : ((x : C) : L) = ((y : C) : L) := congrArg (fun z : N => (z : L)) hxy
        exact Subtype.ext (Subtype.ext h)
      apply (solvable_prime_complement_core_characterization (H := C) hp).2.2.2.1
      · exact Subgroup.normal_subgroupOf
      · exact Group.isSolvable_of_isSolvable_injective hf
      · exact fun h => hNp (h.trans (Subgroup.card_dvd_of_injective f hf))
  set P := perfectResidual C
  have hPg : P.map g = ⊤ := by
    have hrange : g.range = ⊤ := MonoidHom.range_eq_top.mpr hg
    have hperf : Group.IsPerfect g.range := by
      rw [hrange]
      exact Group.IsPerfect.top_iff.mpr hLq.1
    rw [(perfect_residual_transport g).1, ← inSubgroup,
      inSubgroup_perfectResidual_of_isPerfect hperf, hrange]
  have hsup : N ⊔ inSubgroup perfectResidual C = ⊤ := by
    have hmap : (inSubgroup perfectResidual C).map π = ⊤ := by
      rw [inSubgroup, Subgroup.map_map]
      exact hPg
    have h := Subgroup.comap_map_eq π (inSubgroup perfectResidual C)
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    rw [sup_comm]
    exact h.symm
  obtain ⟨-, -, hPperf, -⟩ := perfect_residual_characterization (G := C)
  have hPsn : P.IsSubnormal := Subgroup.Normal.isSubnormal inferInstance
  have hθP : aschbacherSolvableCore p P = (N.subgroupOf C).subgroupOf P := by
    rw [aschbacherSolvableCore_eq_subgroupOf hp hPsn, hθC]
  obtain ⟨η, -⟩ := exists_quotient_mulEquiv_map g P (aschbacherSolvableCore p P) fun l => by
    rw [hθP, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hgker]
  refine ⟨hsup, hPperf, hPsn, ?_⟩
  exact LocalCores.isQuasisimple_of_mulEquiv
    (η.trans ((MulEquiv.subgroupCongr hPg).trans Subgroup.topEquiv)).symm hLq

theorem theta_component_trivial_quotient_action_fixed_residual_subnormal {H : Type*} [Group H]
    [Finite H] {p : ℕ} (hp : p.Prime) {L D : Subgroup H} (hLsn : L.IsSubnormal)
    (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore p L))
    (hD : IsPGroup p D) (hDL : D ≤ Subgroup.normalizer (L : Set H))
    (htriv : thetaQuotientAction p hDL = 1) :
    inSubgroup (aschbacherSolvableCore p) L ⊔
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (D : Set H)) = L ∧
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (D : Set H)) ≤
        Subgroup.centralizer (D : Set H) ∧
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer (D : Set H))).subgroupOf
          (Subgroup.centralizer (D : Set H)) ∈
        thetaComponents p (Subgroup.centralizer (D : Set H)) := by
  set CD := Subgroup.centralizer (D : Set H)
  set X := L ⊓ CD
  set P := inSubgroup perfectResidual X
  let : MulDistribMulAction D L :=
    MulDistribMulAction.compHom L (L.normalizerMonoidHom.comp (Subgroup.inclusion hDL))
  have hsmul : ∀ (d : D) (l : L), ((d • l : L) : H) = d * l * (d : H)⁻¹ := fun _ _ => rfl
  have htriv' : ∀ (d : D) (l : L), ((d • l : L) : L ⧸ aschbacherSolvableCore p L) =
      (l : L ⧸ aschbacherSolvableCore p L) := fun d l =>
    congrArg (fun φ : MulAut (L ⧸ aschbacherSolvableCore p L) =>
      φ (l : L ⧸ aschbacherSolvableCore p L)) (DFunLike.congr_fun htriv d)
  obtain ⟨hsup, hmem⟩ :=
    theta_component_trivial_quotient_action_fixed_residual hp hLq hD htriv'
  set Cfix := fixedPointSubgroup D L
  have hCfix : Cfix.map L.subtype = X := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨l.2, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
      have h := congrArg Subtype.val (hl ⟨d, hd⟩)
      rw [hsmul] at h
      calc d * (l : H) = d * l * d⁻¹ * d := by group
        _ = l * d := by rw [h]
    · rintro ⟨hxL, hxC⟩
      refine ⟨⟨x, hxL⟩, fun d => Subtype.ext ?_, rfl⟩
      rw [hsmul]
      have h := Subgroup.mem_centralizer_iff.mp hxC d d.2
      calc (d : H) * x * (d : H)⁻¹ = x * d * (d : H)⁻¹ := by rw [h]
        _ = x := by group
  set e : Cfix ≃* X :=
    (Cfix.equivMapOfInjective L.subtype L.subtype_injective).trans (MulEquiv.subgroupCongr hCfix)
  have hcomp : X.subtype.comp e.toMonoidHom = L.subtype.comp Cfix.subtype :=
    MonoidHom.ext fun _ => rfl
  have hPeq : P = ((perfectResidual Cfix).map Cfix.subtype).map L.subtype := by
    have h1 : (perfectResidual Cfix).map e.toMonoidHom = perfectResidual X :=
      RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq e.toMonoidHom e.surjective
    change (perfectResidual X).map X.subtype = _
    rw [← h1, Subgroup.map_map, Subgroup.map_map, hcomp]
  have hPX : P ≤ X := Subgroup.map_subtype_le _
  have hPCD : P ≤ CD := hPX.trans inf_le_right
  have hsupH : inSubgroup (aschbacherSolvableCore p) L ⊔ P = L := by
    have h := congrArg (Subgroup.map L.subtype) hsup
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    rw [hPeq]
    exact h
  have hXsn : (X.subgroupOf CD).IsSubnormal := by
    have heq : X.subgroupOf CD = L.subgroupOf CD := by
      ext x
      simp only [X, Subgroup.mem_subgroupOf, Subgroup.mem_inf, and_iff_left x.2]
    rw [heq]
    exact hLsn.subgroupOf
  have hPsn : (P.subgroupOf CD).IsSubnormal := by
    refine Subgroup.IsSubnormal.step _ (X.subgroupOf CD) (fun x hx => hPX hx) hXsn ?_
    rw [Subgroup.normal_subgroupOf_iff
      (show P.subgroupOf CD ≤ X.subgroupOf CD from fun x hx => hPX hx)]
    intro h k hh hk
    exact conj_mem_inSubgroup_perfectResidual hk hh
  set ψ : perfectResidual Cfix ≃* P.subgroupOf CD :=
    ((perfectResidual Cfix).equivMapOfInjective Cfix.subtype Cfix.subtype_injective).trans
      ((((perfectResidual Cfix).map Cfix.subtype).equivMapOfInjective L.subtype
        L.subtype_injective).trans
        ((MulEquiv.subgroupCongr hPeq.symm).trans (Subgroup.subgroupOfEquivOfLe hPCD).symm))
  have hperf : Group.IsPerfect (P.subgroupOf CD) := by
    have := hmem.1
    exact Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
  have hquot : IsQuasisimple ((P.subgroupOf CD) ⧸ aschbacherSolvableCore p (P.subgroupOf CD)) :=
    LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ ψ (aschbacherSolvableCore_map_mulEquiv hp ψ)) hmem.2.2
  exact ⟨hsupH, hPCD, hperf, hPsn, hquot⟩

end CFSG.RankThree.GroupTheory
