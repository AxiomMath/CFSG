module

public import CFSG.Sporadic.HN.Local.TypeFacts
public import CFSG.Sporadic.HN.Local.ClassCount
public import CFSG.Sporadic.HN.Local.Involutions

public section

namespace CFSG.Sporadic.HN.Local

open CFSG.Sporadic.F5 CFSG.Sporadic.HN.LocalK

theorem isConj_coe {G : Type*} [Group G] (K : Subgroup G) {a b : K} (h : IsConj a b) :
    IsConj (a : G) (b : G) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine isConj_iff.2 ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  simpa using this

theorem isConj_S_of_type
    {a b : stabHN} (ha2 : (thetaS a).1 ^ 2 = 1) (hane : (thetaS a).1 ≠ 1)
    (hc : (thetaS a).1.cycleType = (thetaS b).1.cycleType) : IsConj (a : J dHN) (b : J dHN) := by
  obtain ⟨c, hcA, hconj⟩ := exists_conj_alt ha2 hane hc
  refine isConj_coe stabHN (isConj_iff.2 ⟨thetaS.symm ⟨c, hcA⟩, ?_⟩)
  apply thetaS.injective
  apply Subtype.ext
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hconj

theorem thetaS_sq
    {h : stabHN} (hsq : (h : J dHN) ^ 2 = 1) : (thetaS h).1 ^ 2 = 1 := by
  have : h ^ 2 = 1 := Subtype.ext hsq
  have h2 : thetaS h ^ 2 = 1 := by rw [← map_pow, this, map_one]
  exact congrArg Subtype.val h2

theorem thetaS_ne_one
    {h : stabHN} (hne : (h : J dHN) ≠ 1) : (thetaS h).1 ≠ 1 := by
  intro e
  apply hne
  have : thetaS h = 1 := Subtype.ext e
  have := thetaS.injective (this.trans (map_one thetaS).symm)
  rw [this]; rfl

theorem sig2_ne : sig2 ≠ 1 := by
  intro h; have := congrArg (fun f : Equiv.Perm (Fin 12) => f 0) h; revert this; decide

theorem sig4_ne : sig4 ≠ 1 := by
  intro h; have := congrArg (fun f : Equiv.Perm (Fin 12) => f 0) h; revert this; decide

theorem pOne_ne : pOne ≠ 1 := by
  intro h; have := congrArg (fun f : Equiv.Perm (Fin 12) => f 0) h; revert this; decide

theorem conj_t2_iff
    (h : stabHN) :
    IsConj (wG 12) (h : J dHN) ↔ ((thetaS h).1.cycleType = Multiset.replicate 2 2 ∨
      (thetaS h).1.cycleType = Multiset.replicate 6 2) := by
  constructor
  · intro hc
    obtain ⟨c, hcc⟩ := isConj_iff.1 hc
    have hsq : (h : J dHN) ^ 2 = 1 := by rw [← hcc, conj_pow, t2_sq, mul_one, mul_inv_cancel]
    have hne : (h : J dHN) ≠ 1 := fun e => t2_ne_one (by rw [e] at hcc; exact conj_eq_one_iff.1 hcc)
    rcases involution_alt_type (thetaS_sq hsq) (thetaS_ne_one hne) (thetaS h).2 with h2 | h4 | h6
    · exact Or.inl h2
    · exfalso
      have h13 := isConj_S_of_type (a := ⟨wG 13, t4_mem_stabHN⟩) (b := h)
        (by rw [thetaS_t4]; exact sig4_sq) (by rw [thetaS_t4]; exact sig4_ne)
        (by rw [theta_t4_type, h4])
      exact not_isConj_t2_t4 (hc.trans h13.symm)
    · exact Or.inr h6
  · rintro (h2 | h6)
    · exact isConj_S_of_type (a := ⟨wG 12, t2_mem_stabHN⟩) (b := h)
        (by rw [thetaS_t2]; exact sig2_sq) (by rw [thetaS_t2]; exact sig2_ne)
        (by rw [theta_t2_type, h2])
    · exact isConj_t2_x2.trans (isConj_S_of_type (a := ⟨wG 2, x2_mem_stabHN⟩) (b := h)
        (by rw [thetaS_x2]; exact pOne_sq) (by rw [thetaS_x2]; exact pOne_ne)
        (by rw [theta_x2_type, h6]))

theorem conj_t4_iff
    (h : stabHN) :
    IsConj (wG 13) (h : J dHN) ↔ (thetaS h).1.cycleType = Multiset.replicate 4 2 := by
  constructor
  · intro hc
    obtain ⟨c, hcc⟩ := isConj_iff.1 hc
    have hsq : (h : J dHN) ^ 2 = 1 := by rw [← hcc, conj_pow, t4_sq, mul_one, mul_inv_cancel]
    have hne : (h : J dHN) ≠ 1 := fun e => t4_ne_one (by rw [e] at hcc; exact conj_eq_one_iff.1 hcc)
    rcases involution_alt_type (thetaS_sq hsq) (thetaS_ne_one hne) (thetaS h).2 with h2 | h4 | h6
    · exact absurd (((conj_t2_iff h).2 (Or.inl h2)).trans hc.symm) not_isConj_t2_t4
    · exact h4
    · exact absurd (((conj_t2_iff h).2 (Or.inr h6)).trans hc.symm) not_isConj_t2_t4
  · intro h4
    exact isConj_S_of_type (a := ⟨wG 13, t4_mem_stabHN⟩) (b := h)
      (by rw [thetaS_t4]; exact sig4_sq) (by rw [thetaS_t4]; exact sig4_ne)
      (by rw [theta_t4_type, h4])

theorem card_alt_filter (Q : Equiv.Perm (Fin 12) → Prop) [DecidablePred Q]
    (hQ : ∀ σ, Q σ → σ ∈ alternatingGroup (Fin 12)) :
    Nat.card {σ : alternatingGroup (Fin 12) // Q σ.1} = (Finset.univ.filter Q).card := by
  classical
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr
    { toFun := fun σ => ⟨σ.1.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, σ.2⟩⟩
      invFun := fun g => ⟨⟨g.1, hQ g.1 (Finset.mem_filter.1 g.2).2⟩, (Finset.mem_filter.1 g.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_T_of_iff
    {t : J dHN} {Q : Equiv.Perm (Fin 12) → Prop}
    (h : ∀ h : stabHN, IsConj t (h : J dHN) ↔ Q (thetaS h).1) :
    Nat.card {x : J dHN // x ∈ stabHN ∧ IsConj t x} =
      Nat.card {σ : alternatingGroup (Fin 12) // Q σ.1} := by
  refine Nat.card_congr ?_
  refine Equiv.trans ?_ (Equiv.subtypeEquiv thetaS.toEquiv (p := fun x : stabHN => IsConj t x.1)
    (q := fun σ : alternatingGroup (Fin 12) => Q σ.1) h)
  exact { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
          invFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }

theorem card_T_t2 :
    Nat.card {x : J dHN // x ∈ stabHN ∧ IsConj (wG 12) x} = 11880 := by
  classical
  have e := card_alt_filter (fun σ : Equiv.Perm (Fin 12) => σ.cycleType = Multiset.replicate 2 2 ∨
      σ.cycleType = Multiset.replicate 6 2) (fun σ hσ => by
      rcases hσ with h | h
      · exact mem_alt_of_cycleType_replicate (by decide) h
      · exact mem_alt_of_cycleType_replicate (by decide) h)
  rw [card_T_of_iff (Q := fun σ => σ.cycleType = Multiset.replicate 2 2 ∨
      σ.cycleType = Multiset.replicate 6 2) conj_t2_iff, e,
    Finset.filter_or, Finset.card_union_of_disjoint, card_type_two, card_type_six]
  exact Finset.disjoint_filter.2 fun σ _ h2 h6 => by
    rw [h2] at h6; exact absurd h6 (by decide)

theorem card_T_t4 :
    Nat.card {x : J dHN // x ∈ stabHN ∧ IsConj (wG 13) x} = 51975 := by
  classical
  have e := card_alt_filter (fun σ : Equiv.Perm (Fin 12) => σ.cycleType = Multiset.replicate 4 2)
    (fun σ hσ => mem_alt_of_cycleType_replicate (by decide) hσ)
  rw [card_T_of_iff (Q := fun σ => σ.cycleType = Multiset.replicate 4 2) conj_t4_iff, e,
    card_type_four]

noncomputable abbrev rootOrbit : Type := MulAction.orbit (J dHN) rootV

noncomputable abbrev rootPt : rootOrbit := ⟨rootV, MulAction.mem_orbit_self rootV⟩

theorem stabilizer_rootPt : MulAction.stabilizer (J dHN) rootPt = stabHN := by
  ext g
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  exact Subtype.ext_iff

noncomputable def Xc : Fin 1140000 → Vec dHN :=
  type_certificate.2.2.2.2.2.choose

theorem Xc_spec :
    Function.Injective Xc ∧ (∀ k, Xc k ∈ MulAction.orbit (J dHN) rootV) ∧
      Nat.card {k // wG 12 • Xc k = Xc k} = 8800 ∧ Nat.card {k // wG 13 • Xc k = Xc k} = 800 :=
  type_certificate.2.2.2.2.2.choose_spec

theorem Xc_bijective :
    Function.Bijective (fun k => (⟨Xc k, Xc_spec.2.1 k⟩ : rootOrbit)) := by
  have hinj : Function.Injective (fun k => (⟨Xc k, Xc_spec.2.1 k⟩ : rootOrbit)) :=
    fun i j e => Xc_spec.1 (congrArg Subtype.val e)
  refine (Function.Injective.bijective_of_nat_card_le hinj ?_)
  rw [Nat.card_eq_fintype_card (α := Fin 1140000), Fintype.card_fin, card_orbit_root]

theorem card_fixed_orbit
    (t : J dHN) :
    Nat.card {y : rootOrbit // t • y = y} = Nat.card {k // t • Xc k = Xc k} := by
  refine (Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective _ Xc_bijective) fun k => ?_)).symm
  rw [Equiv.ofBijective_apply, Subtype.ext_iff, MulAction.orbit.coe_smul]

theorem card_centralizer_t2 :
    Nat.card (Subgroup.centralizer {wG 12}) = 177408000 := by
  have h := card_centralizer_mul_card_inter (G := J dHN) (X := rootOrbit) rootPt (wG 12)
  rw [stabilizer_rootPt, card_T_t2, card_fixed_orbit, Xc_spec.2.2.1, card_stabHN] at h
  generalize Nat.card (Subgroup.centralizer {wG 12}) = c at h ⊢
  omega

theorem card_centralizer_t4 :
    Nat.card (Subgroup.centralizer {wG 13}) = 3686400 := by
  have h := card_centralizer_mul_card_inter (G := J dHN) (X := rootOrbit) rootPt (wG 13)
  rw [stabilizer_rootPt, card_T_t4, card_fixed_orbit, Xc_spec.2.2.2, card_stabHN] at h
  generalize Nat.card (Subgroup.centralizer {wG 13}) = c at h ⊢
  omega

end CFSG.Sporadic.HN.Local
