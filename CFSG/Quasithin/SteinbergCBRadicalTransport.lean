module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderSolvable
public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.Quasithin.SteinbergCB

open Subgroup CFSG.SectionRank.Ccomm

variable {H : Type*} [Group H]

theorem nq_characteristic_solvable_quotient_radical_transport [Finite H] (N : Subgroup H)
    [N.Characteristic] (hN : Group.IsSolvable N) :
    N ≤ solvableRadical H ∧
    solvableRadical (H ⧸ N) = (solvableRadical H).map (QuotientGroup.mk' N) ∧
    ∃ e : H ⧸ solvableRadical H ≃* (H ⧸ N) ⧸ solvableRadical (H ⧸ N),
      (∀ h : H, e h = ((h : H ⧸ N) : (H ⧸ N) ⧸ solvableRadical (H ⧸ N))) ∧
      (∀ (α : MulAut H) (x : H ⧸ solvableRadical H),
        e (autQuotient (solvableRadical H) α x) =
          autQuotient (solvableRadical (H ⧸ N)) (autQuotient N α) (e x)) ∧
      ∀ A : Subgroup (MulAut H),
        Nonempty (A.map (autQuotient (solvableRadical H)) ≃*
          (A.map (autQuotient N)).map (autQuotient (solvableRadical (H ⧸ N)))) ∧
        Nat.card (A.map (autQuotient (solvableRadical H))) =
          Nat.card ((A.map (autQuotient N)).map (autQuotient (solvableRadical (H ⧸ N)))) ∧
        (CFSG.IsElementaryAbelian 2 A → CFSG.IsElementaryAbelian 2 (A.map (autQuotient N))) := by
  classical
  obtain ⟨-, hRs, hmax, -⟩ := CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization H
  obtain ⟨-, hRs', hmax', -⟩ :=
    CFSG.QuasithinUnique.Setup.Offender.solvableRadical_characterization (H ⧸ N)
  set R := solvableRadical H with hR
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hNR : N ≤ R := hmax N (normal_of_characteristic N) hN
  have hrad : solvableRadical (H ⧸ N) = R.map π := by
    apply le_antisymm
    · have hcs : Group.IsSolvable ((solvableRadical (H ⧸ N)).comap π) :=
        CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_comap_mk'
      have hle : (solvableRadical (H ⧸ N)).comap π ≤ R :=
        hmax _ ((inferInstance : (solvableRadical (H ⧸ N)).Normal).comap π) hcs
      calc solvableRadical (H ⧸ N) = ((solvableRadical (H ⧸ N)).comap π).map π :=
            (map_comap_eq_self_of_surjective hπs _).symm
        _ ≤ R.map π := map_mono hle
    · refine hmax' _ ((inferInstance : R.Normal).map π hπs) ?_
      exact Group.isSolvable_of_surjective (π.subgroupMap_surjective R)
  set f : H →* (H ⧸ N) ⧸ solvableRadical (H ⧸ N) :=
    (QuotientGroup.mk' (solvableRadical (H ⧸ N))).comp π with hf
  have hfs : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp hπs
  have hker : R = f.ker := by
    rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', hrad, comap_map_eq, QuotientGroup.ker_mk',
      sup_eq_left.2 hNR]
  set e : H ⧸ R ≃* (H ⧸ N) ⧸ solvableRadical (H ⧸ N) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfs) with he
  have he_mk : ∀ h : H, e h = ((h : H ⧸ N) : (H ⧸ N) ⧸ solvableRadical (H ⧸ N)) := fun h => rfl
  have hequiv : ∀ (α : MulAut H) (x : H ⧸ R), e (autQuotient R α x) =
      autQuotient (solvableRadical (H ⧸ N)) (autQuotient N α) (e x) := by
    intro α x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    rw [autQuotient_mk, he_mk, he_mk, autQuotient_mk, autQuotient_mk]
  refine ⟨hNR, hrad, e, he_mk, hequiv, fun A => ?_⟩
  set c := MulAut.congr e with hc
  have hcomp : (c : MulAut (H ⧸ R) →* MulAut ((H ⧸ N) ⧸ solvableRadical (H ⧸ N))).comp
      (autQuotient R) = (autQuotient (solvableRadical (H ⧸ N))).comp (autQuotient N) := by
    refine MonoidHom.ext fun α => MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    change e ((autQuotient R α) (e.symm (e x))) = _
    rw [MulEquiv.symm_apply_apply, hequiv]
    rfl
  have himage : (A.map (autQuotient R)).map (c : MulAut (H ⧸ R) →* _) =
      (A.map (autQuotient N)).map (autQuotient (solvableRadical (H ⧸ N))) := by
    rw [map_map, map_map, hcomp]
  have hiso : A.map (autQuotient R) ≃*
      (A.map (autQuotient N)).map (autQuotient (solvableRadical (H ⧸ N))) :=
    ((A.map (autQuotient R)).equivMapOfInjective _ c.injective).trans
      (MulEquiv.subgroupCongr himage)
  refine ⟨⟨hiso⟩, Nat.card_congr hiso.toEquiv, fun hA => ?_⟩
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => by
    have h := (hA.toIsMulCommutative).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val h
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (@CFSG.IsElementaryAbelian.exponent_dvd_p 2 A _ hA) ⟨a, ha⟩
    simpa using congrArg Subtype.val h
  exact
    { is_comm := ⟨fun a b => by
        obtain ⟨a', ha', ha⟩ := a.2
        obtain ⟨b', hb', hb⟩ := b.2
        apply Subtype.ext
        change (a : MulAut (H ⧸ N)) * b = b * a
        rw [← ha, ← hb, ← map_mul, ← map_mul, hAcomm a' ha' b' hb']⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
        obtain ⟨a', ha', ha⟩ := a.2
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← ha, ← map_pow, hA2 a' ha', map_one]
        rfl }

end CFSG.Quasithin.SteinbergCB
