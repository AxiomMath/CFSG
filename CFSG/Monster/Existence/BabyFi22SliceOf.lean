module

public import CFSG.Monster.Existence.BabyOrbitSphere
public import CFSG.Monster.Existence.BabyThreeSwap
public import CFSG.Monster.B.TwoA.Amalgam.FischerNodesFi22
public import CFSG.Sporadic.Fi22.Classes

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.GMS CFSG.Blueprint

theorem exists_star_equiv {B' G J : Type*} [Group B'] [Group G] [Group J] (ρ : B' ≃* G)
    (N : Subgroup G) (S : Set G) (hSN : S ⊆ N) (φ : N ≃* J) (D : Set J) (star : Set B')
    (hstar : ∀ t, t ∈ star ↔ ρ t ∈ S) (hD : ∀ x : N, φ x ∈ D ↔ (x : G) ∈ S) :
    ∃ χ : star ≃ D,
      (∀ t u : star, (t : B') * u = u * t ↔ ((χ t : J) * χ u = χ u * χ t)) ∧
      ∀ (t u : star) (h : (t : B') * u * t ∈ star),
        ((χ ⟨_, h⟩ : D) : J) = (χ t : J) * χ u * χ t := by
  have hmem : ∀ t : star, ρ t ∈ N := fun t => hSN ((hstar t).1 t.2)
  have hfD : ∀ t : star, φ ⟨ρ t, hmem t⟩ ∈ D := fun t => (hD _).2 ((hstar t).1 t.2)
  have hinj : Function.Injective fun t : star => (⟨φ ⟨ρ t, hmem t⟩, hfD t⟩ : D) := by
    intro t u h
    have h1 : φ ⟨ρ t, hmem t⟩ = φ ⟨ρ u, hmem u⟩ := congrArg Subtype.val h
    have h2 : ρ t = ρ u := congrArg Subtype.val (φ.injective h1)
    exact Subtype.ext (ρ.injective h2)
  have hsurj : Function.Surjective fun t : star => (⟨φ ⟨ρ t, hmem t⟩, hfD t⟩ : D) := by
    rintro ⟨d, hd⟩
    have hx : ((φ.symm d : N) : G) ∈ S := (hD _).1 (by rwa [MulEquiv.apply_symm_apply])
    have hxρ : ρ (ρ.symm ((φ.symm d : N) : G)) ∈ S := by rwa [MulEquiv.apply_symm_apply]
    refine ⟨⟨ρ.symm ((φ.symm d : N) : G), (hstar _).2 hxρ⟩, Subtype.ext ?_⟩
    have e : (⟨ρ (ρ.symm ((φ.symm d : N) : G)), hmem ⟨_, (hstar _).2 hxρ⟩⟩ : N) = φ.symm d :=
      Subtype.ext (MulEquiv.apply_symm_apply ρ _)
    show φ ⟨ρ (ρ.symm ((φ.symm d : N) : G)), _⟩ = d
    rw [e, MulEquiv.apply_symm_apply]
  obtain ⟨χ, hχ⟩ : ∃ χ : star ≃ D, ∀ t, ((χ t : D) : J) = φ ⟨ρ t, hmem t⟩ :=
    ⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩, fun t => rfl⟩
  refine ⟨χ, fun t u => ?_, fun t u h => ?_⟩
  · rw [hχ, hχ, ← map_mul, ← map_mul, φ.injective.eq_iff]
    constructor
    · intro e
      refine Subtype.ext ?_
      show ρ t * ρ u = ρ u * ρ t
      rw [← map_mul, ← map_mul, e]
    · intro e
      apply ρ.injective
      rw [map_mul, map_mul]
      exact congrArg Subtype.val e
  · rw [hχ, hχ, hχ, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    show ρ ((t : B') * u * t) = ρ t * ρ u * ρ t
    rw [map_mul, map_mul]

theorem exists_mulEquiv_J_of_mem_sphereThree
    {v w : CVert} (hw : w ∈ sphereThree v) :
    ∃ φ : cnGroup v w ≃* CFSG.Sporadic.Fi22.J,
      ∀ x : cnGroup v w, φ x ∈ CFSG.Sporadic.Fi22.D ↔ (x : Shat) ∈ cnLabels v w := by
  obtain ⟨e⟩ := native_three_transposition_group_nonempty_mulEquiv_Fi22 hw
  have hP := pair_cnClass (fun x => (nonempty_localHom x).some) hw
  have hpair : CFSG.Blueprint.Fischer.Pair NativeSporadic.Fi22 (e '' cnClass v w) := by
    with_reducible_and_instances exact CFSG.Fischer.pair_map hP e
  have h := CFSG.Sporadic.Fi22.pair_eq_D_native _ hpair
  refine ⟨e.trans CFSG.Sporadic.Fi22.fi22EquivJ, fun x => ?_⟩
  constructor
  · intro hx
    have h1 : CFSG.Sporadic.Fi22.fi22EquivJ.symm (CFSG.Sporadic.Fi22.fi22EquivJ (e x)) ∈
        CFSG.Sporadic.Fi22.fi22EquivJ.symm '' CFSG.Sporadic.Fi22.D := ⟨_, hx, rfl⟩
    rw [MulEquiv.symm_apply_apply, ← h] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    rwa [← e.injective hyx]
  · intro hx
    have h1 : e x ∈ CFSG.Sporadic.Fi22.fi22EquivJ.symm '' CFSG.Sporadic.Fi22.D := by
      rw [← h]
      exact ⟨x, hx, rfl⟩
    obtain ⟨d, hd, hdx⟩ := h1
    show CFSG.Sporadic.Fi22.fi22EquivJ (e x) ∈ CFSG.Sporadic.Fi22.D
    rwa [← hdx, MulEquiv.apply_symm_apply]

theorem babyFi22Slice_of_ne_rep_three
    (h3 : Nat.card ↥(Subgroup.centralizer ({babyRep 3} : Set NativeSporadic.B)) ≠ babyCentOrder 0) :
    BabyFi22Slice := by
  intro r s hr hs hrs
  have hcls : ∀ t : NativeSporadic.B, BabyInv 0 t → IsConj t (babyRep 1) := fun t ht =>
    isConj_babyRep_one_of_babyInv_zero h3 ht
  obtain ⟨v, hv⟩ := (babyInv_zero_iff_clabelS hcls r).1 hr
  obtain ⟨w, hw⟩ := (babyInv_zero_iff_clabelS hcls s).1 hs
  have hvw : w ∈ sphereThree v := mem_sphereThree_of_orderOf_eq_three hr.1 hv hw hrs
  have himg := image_babyStar_eq hcls hr hs hv hw
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_J_of_mem_sphereThree hvw
  have hstar : ∀ t, t ∈ babyStar r s ↔ babyToShat t ∈ cnLabels v w := fun t => by
    rw [← babyToShat.injective.mem_set_image, himg]
    exact Iff.rfl
  have hSN : cnLabels v w ⊆ (cnGroup v w : Set Shat) := Subgroup.subset_closure
  refine ⟨?_, fun g hg hgt => ?_⟩
  · with_reducible_and_instances
      exact exists_star_equiv babyToShat (cnGroup v w) (cnLabels v w) hSN φ
        CFSG.Sporadic.Fi22.D (babyStar r s) hstar hφ
  · have hg1 := (mem_centralizer_iff_mem_vStab hv g).1 (Subgroup.mem_inf.1 hg).1
    have hg2 := (mem_centralizer_iff_mem_vStab hw g).1 (Subgroup.mem_inf.1 hg).2
    apply babyToShat.injective
    rw [map_one]
    refine eq_one_of_centralizes (fun x => (nonempty_localHom x).some) hvw
      (Subgroup.mem_inf.2 ⟨hg1, hg2⟩) fun u hu => ?_
    obtain ⟨t, ht⟩ : ∃ t, clabelS u = babyToShat t := ⟨babyToShat.symm (clabelS u), by simp⟩
    have ht0 : BabyInv 0 t := (babyInv_zero_iff_clabelS hcls t).2 ⟨u, ht⟩
    have htstar : t ∈ babyStar r s := (mem_babyStar_iff hr hs ht0 hv hw ht).2 hu
    rw [ht, ← map_mul, ← map_mul, hgt t htstar]

theorem babyFi22Slice_of
    (hT3 : BabyTableIII) : BabyFi22Slice :=
  babyFi22Slice_of_ne_rep_three (natCard_centralizer_rep_three_ne_of_babyTableIII hT3)

end CFSG.Monster.Existence
