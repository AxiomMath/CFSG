module

public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.GroupTheory.WeirSylow QuadraticMap

section Generic

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem finrank_le_of_polar_inj (A A' : Submodule K V)
    (h : ∀ v ∈ A, (∀ w ∈ A', polar Q v w = 0) → v = 0) : finrank K A ≤ finrank K A' := by
  let Φ : A →ₗ[K] Module.Dual K A' := (polarBilin Q).compl₁₂ A.subtype A'.subtype
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    refine Subtype.ext (h v v.2 fun w hw => ?_)
    have := congrArg (fun f : Module.Dual K A' => f ⟨w, hw⟩) hv
    simpa [Φ] using this
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Subspace.dual_finrank_eq] at this

omit [FiniteDimensional K V] in
theorem polar_eq_zero_of_iSup {ι ι' : Type*} (A : ι → Submodule K V) (A' : ι' → Submodule K V)
    (h : ∀ i j, ∀ v ∈ A i, ∀ w ∈ A' j, polar Q v w = 0) :
    ∀ v ∈ ⨆ i, A i, ∀ w ∈ ⨆ j, A' j, polar Q v w = 0 := by
  intro v hv
  refine Submodule.iSup_induction A (motive := fun v => ∀ w ∈ ⨆ j, A' j, polar Q v w = 0) hv
    ?_ ?_ ?_
  · intro i v hvi w hw
    refine Submodule.iSup_induction A' (motive := fun w => polar Q v w = 0) hw ?_ ?_ ?_
    · intro j w hwj
      exact h i j v hvi w hwj
    · exact polar_zero_right _ _
    · intro w₁ w₂ h₁ h₂
      rw [polar_add_right, h₁, h₂, add_zero]
  · intro w _
    exact polar_zero_left _ _
  · intro v₁ v₂ h₁ h₂ w hw
    rw [polar_add_left, h₁ w hw, h₂ w hw, add_zero]

omit [FiniteDimensional K V] in
theorem map_eq_zero_of_iSup {ι : Type*} (A : ι → Submodule K V)
    (hB : ∀ i j, ∀ v ∈ A i, ∀ w ∈ A j, polar Q v w = 0) (hQ : ∀ i, ∀ v ∈ A i, Q v = 0) :
    ∀ v ∈ ⨆ i, A i, Q v = 0 := by
  have hBB := polar_eq_zero_of_iSup (Q := Q) A A hB
  intro v hv
  refine Submodule.iSup_induction' A (motive := fun v _ => Q v = 0) ?_ ?_ ?_ hv
  · intro i v hv
    exact hQ i v hv
  · exact QuadraticMap.map_zero Q
  · intro v₁ v₂ hv₁ hv₂ h₁ h₂
    rw [QuadraticMap.map_add (⇑Q) v₁ v₂, h₁, h₂, hBB v₁ hv₁ v₂ hv₂, add_zero, add_zero]

end Generic


section Main

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem map_eq_zero_of_paired (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (h1 : h ≠ X - 1) (h2 : h ≠ reciprocalPolynomial h) :
    ∀ v ∈ primaryComponent x.toLinearMap h, Q v = 0 := by
  set xe : Module.End K V := x.toLinearMap with hxe
  have hcop : IsCoprime h (X - 1 : K[X]) :=
    isCoprime_of_irreducible_monic_ne (irreducible_of_mem_primaryFactors hh) irreducible_X_sub_one
      (monic_of_mem_primaryFactors hh) monic_X_sub_one h1
  obtain ⟨a, b, hab⟩ := hcop
  intro w hw
  have hw0 : aeval xe h w = 0 := mem_primaryComponent.mp hw
  have hA : aeval xe a * aeval xe h + aeval xe b * (xe - 1) = 1 := by
    have := congrArg (aeval xe) hab
    simpa [map_add, map_mul, aeval_X] using this
  have hcomm : Commute (xe - 1) xe := (Commute.refl xe).sub_left (Commute.one_left xe)
  have key : aeval xe b * (xe - 1) = (xe - 1) * aeval xe b := (commute_aeval hcomm b).eq.symm
  set u : V := aeval xe b w with hu
  have huh : u ∈ primaryComponent xe h := by
    rw [mem_primaryComponent]
    calc aeval xe h u = (aeval xe h * aeval xe b) w := rfl
      _ = (aeval xe b * aeval xe h) w := by rw [← map_mul, ← map_mul, mul_comm]
      _ = 0 := by rw [Module.End.mul_apply, hw0, map_zero]
  have hwu : w = x u - u := by
    calc w = (1 : Module.End K V) w := rfl
      _ = (aeval xe a * aeval xe h + aeval xe b * (xe - 1)) w := by rw [hA]
      _ = aeval xe a (aeval xe h w) + (aeval xe b * (xe - 1)) w := by
        rw [LinearMap.add_apply, Module.End.mul_apply]
      _ = ((xe - 1) * aeval xe b) w := by rw [hw0, map_zero, zero_add, key]
      _ = x u - u := by rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]; rfl
  have hxu : x u ∈ primaryComponent xe h :=
    apply_mem_primaryComponent (Commute.refl xe) huh
  have hpol : polar Q (x u) u = 0 := hx.polar_primaryComponent_eq_zero hh hh h2 hxu huh
  have hQxu : Q (x u) = Q u := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem u
  rw [hwu, sub_eq_add_neg, QuadraticMap.map_add (⇑Q) (x u) (-u), QuadraticMap.map_neg, hQxu,
    polar_neg_right, hpol, neg_zero, add_zero]
  exact CharTwo.add_self_eq_zero (Q u)

theorem exists_halfSpace (hx : OddOrderIsometry Q p x)
    (hno : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 → h ≠ reciprocalPolynomial h)
    {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives x Rep) :
    ∃ T : Submodule K V, (∀ r ∈ Rep, r ≠ X - 1 → primaryComponent x.toLinearMap r ≤ T) ∧
      (∀ t ∈ T, Q t = 0) ∧ (∀ w ∈ fixedSpace x, ∀ t ∈ T, polar Q w t = 0) ∧
      Disjoint (fixedSpace x) T ∧ finrank K (fixedSpace x) + 2 * finrank K T = finrank K V := by
  classical
  set xe : Module.End K V := x.toLinearMap with hxe
  obtain ⟨hcompl, hperp⟩ := hx.fixed_others
  set R : Submodule K V := othersSpace xe (X - 1) with hR
  set Rep' : Finset K[X] := Rep.erase (X - 1) with hRep'
  have hpf : ∀ r ∈ Rep', r ∈ primaryFactors xe := fun r hr =>
    hRep.1 (Finset.mem_of_mem_erase hr)
  have hne1 : ∀ r ∈ Rep', r ≠ X - 1 := fun r hr => Finset.ne_of_mem_erase hr
  have hpair : ∀ r ∈ Rep', r ≠ reciprocalPolynomial r := fun r hr => hno r (hpf r hr) (hne1 r hr)
  have hrpf : ∀ r ∈ Rep', reciprocalPolynomial r ∈ primaryFactors xe := fun r hr =>
    hx.reciprocalPolynomial_mem (hpf r hr)
  have hrne1 : ∀ r ∈ Rep', reciprocalPolynomial r ≠ X - 1 := by
    intro r hr h
    apply hne1 r hr
    have := hx.reciprocal_reciprocal_eq (hpf r hr)
    rw [h, reciprocalPolynomial_X_sub_one] at this
    exact this.symm
  have hrpair : ∀ r ∈ Rep', reciprocalPolynomial r ≠ reciprocalPolynomial (reciprocalPolynomial r) := by
    intro r hr
    rw [hx.reciprocal_reciprocal_eq (hpf r hr)]
    exact (hpair r hr).symm
  let T : Submodule K V := ⨆ r : Rep', primaryComponent xe (r : K[X])
  let T' : Submodule K V := ⨆ r : Rep', primaryComponent xe (reciprocalPolynomial (r : K[X]))
  have hRT : R = T ⊔ T' := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · refine iSup₂_le fun k hk => ?_
      obtain ⟨hkpf, hk1, -⟩ := hk
      obtain ⟨r, ⟨hrRep, hkr⟩, -⟩ := hRep.2 k hkpf
      have hr1 : r ≠ X - 1 := by
        rintro rfl
        rcases hkr with h | h
        · exact hk1 h
        · exact hk1 (h.trans reciprocalPolynomial_X_sub_one)
      have hr' : r ∈ Rep' := Finset.mem_erase.mpr ⟨hr1, hrRep⟩
      rcases hkr with rfl | rfl
      · exact le_sup_of_le_left (le_iSup (fun r : Rep' => primaryComponent xe (r : K[X])) ⟨k, hr'⟩)
      · exact le_sup_of_le_right
          (le_iSup (fun r : Rep' => primaryComponent xe (reciprocalPolynomial (r : K[X]))) ⟨r, hr'⟩)
    · refine iSup_le fun r => ?_
      exact le_iSup₂_of_le (r : K[X]) ⟨hpf r r.2, hne1 r r.2, by
        rw [reciprocalPolynomial_X_sub_one]; exact hne1 r r.2⟩ le_rfl
    · refine iSup_le fun r => ?_
      exact le_iSup₂_of_le (reciprocalPolynomial (r : K[X])) ⟨hrpf r r.2, hrne1 r r.2, by
        rw [reciprocalPolynomial_X_sub_one]; exact hrne1 r r.2⟩ le_rfl
  have hBT : ∀ r s : Rep', ∀ v ∈ primaryComponent xe (r : K[X]), ∀ w ∈ primaryComponent xe (s : K[X]),
      polar Q v w = 0 := by
    intro r s v hv w hw
    refine hx.polar_primaryComponent_eq_zero (hpf r r.2) (hpf s s.2) ?_ hv hw
    by_cases hrs : (r : K[X]) = s
    · rw [hrs]
      exact hpair s s.2
    · exact hRep.ne_reciprocal (Finset.mem_of_mem_erase r.2) (Finset.mem_of_mem_erase s.2) hrs
  have hBT' : ∀ r s : Rep', ∀ v ∈ primaryComponent xe (reciprocalPolynomial (r : K[X])),
      ∀ w ∈ primaryComponent xe (reciprocalPolynomial (s : K[X])), polar Q v w = 0 := by
    intro r s v hv w hw
    refine hx.polar_primaryComponent_eq_zero (hrpf r r.2) (hrpf s s.2) ?_ hv hw
    rw [hx.reciprocal_reciprocal_eq (hpf r r.2)]
    by_cases hrs : (r : K[X]) = s
    · rw [hrs]
      exact hpair s s.2 |>.symm
    · exact (hRep.ne_reciprocal (Finset.mem_of_mem_erase s.2) (Finset.mem_of_mem_erase r.2)
        (fun h => hrs h.symm)).symm
  have hTT : ∀ v ∈ T, ∀ w ∈ T, polar Q v w = 0 :=
    polar_eq_zero_of_iSup _ _ hBT
  have hT'T' : ∀ v ∈ T', ∀ w ∈ T', polar Q v w = 0 :=
    polar_eq_zero_of_iSup _ _ hBT'
  have hQT : ∀ t ∈ T, Q t = 0 :=
    map_eq_zero_of_iSup _ hBT fun r v hv => map_eq_zero_of_paired hx (hpf r r.2) (hne1 r r.2)
      (hpair r r.2) v hv
  have hQT' : ∀ t ∈ T', Q t = 0 :=
    map_eq_zero_of_iSup _ hBT' fun r v hv => map_eq_zero_of_paired hx (hrpf r r.2) (hrne1 r r.2)
      (hrpair r r.2) v hv
  have hTR : T ≤ R := hRT ▸ le_sup_left
  have hT'R : T' ≤ R := hRT ▸ le_sup_right
  have hWT : ∀ w ∈ fixedSpace x, ∀ t ∈ T, polar Q w t = 0 := fun w hw t ht =>
    hperp w hw t (hTR ht)
  have hWT' : ∀ w ∈ fixedSpace x, ∀ t ∈ T', polar Q w t = 0 := fun w hw t ht =>
    hperp w hw t (hT'R ht)
  have hdecomp : ∀ v : V, ∃ w ∈ fixedSpace x, ∃ t ∈ T, ∃ t' ∈ T', v = w + t + t' := by
    intro v
    have hv : v ∈ fixedSpace x ⊔ R := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨w, hw, r, hr, rfl⟩ := Submodule.mem_sup.mp hv
    rw [hRT] at hr
    obtain ⟨t, ht, t', ht', rfl⟩ := Submodule.mem_sup.mp hr
    exact ⟨w, hw, t, ht, t', ht', by abel⟩
  have hinj : ∀ v ∈ T, (∀ w ∈ T', polar Q v w = 0) → v = 0 := by
    intro v hv hvT'
    refine hx.regular v fun y => ?_
    obtain ⟨w, hw, t, ht, t', ht', rfl⟩ := hdecomp y
    rw [polar_add_right, polar_add_right, polar_comm (⇑Q) v w, hWT w hw v hv, hTT v hv t ht,
      hvT' t' ht', add_zero, add_zero]
  have hinj' : ∀ v ∈ T', (∀ w ∈ T, polar Q v w = 0) → v = 0 := by
    intro v hv hvT
    refine hx.regular v fun y => ?_
    obtain ⟨w, hw, t, ht, t', ht', rfl⟩ := hdecomp y
    rw [polar_add_right, polar_add_right, polar_comm (⇑Q) v w, hWT' w hw v hv, hvT t ht,
      hT'T' v hv t' ht', add_zero, zero_add]
  have hle1 : finrank K T ≤ finrank K T' := finrank_le_of_polar_inj T T' hinj
  have hle2 : finrank K T' ≤ finrank K T := finrank_le_of_polar_inj T' T hinj'
  have hdisj : Disjoint T T' := by
    rw [Submodule.disjoint_def]
    intro v hvT hvT'
    exact hinj v hvT fun w hw => by
      rw [polar_comm (⇑Q) v w]
      exact hT'T' w hw v hvT'
  have hdimR : finrank K R = 2 * finrank K T := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq T T'
    rw [disjoint_iff.mp hdisj, finrank_bot, add_zero, ← hRT] at h1
    omega
  have hdimV : finrank K (fixedSpace x) + finrank K R = finrank K V :=
    Submodule.finrank_add_eq_of_isCompl hcompl
  refine ⟨T, fun r hr hr1 => ?_, hQT, hWT, ?_, by omega⟩
  · exact le_iSup (fun r : Rep' => primaryComponent xe (r : K[X]))
      ⟨r, Finset.mem_erase.mpr ⟨hr1, hr⟩⟩
  · exact hcompl.disjoint.mono_right hTR

theorem not_isPlusType_fixedSpace (hx : OddOrderIsometry Q p x)
    (hno : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 → h ≠ reciprocalPolynomial h)
    (hV : ¬ IsPlusType Q) : ¬ IsPlusType (Q.comp (fixedSpace x).subtype) := by
  rintro ⟨S, hS, hSs⟩
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  obtain ⟨T, -, hQT, hWT, hdisj, hdim⟩ := exists_halfSpace hx hno hRep
  apply hV
  let S' : Submodule K V := S.map (fixedSpace x).subtype
  have hS'W : S' ≤ fixedSpace x := fun v ⟨s, _, hsv⟩ => hsv ▸ s.2
  have hfS' : finrank K S' = finrank K S := Submodule.finrank_map_subtype_eq _ _
  refine ⟨S' ⊔ T, ?_, ?_⟩
  · have hd : Disjoint S' T := hdisj.mono_left hS'W
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq S' T
    rw [disjoint_iff.mp hd, finrank_bot, add_zero] at h1
    omega
  · intro v hv
    obtain ⟨s', hs', t, ht, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨s, hs, rfl⟩ := hs'
    have hsQ : Q ((fixedSpace x).subtype s) = 0 := hSs s hs
    have hp : polar Q ((fixedSpace x).subtype s) t = 0 := hWT _ s.2 t ht
    rw [QuadraticMap.map_add (⇑Q) _ t, hsQ, hQT t ht, hp, add_zero, add_zero]

end Main

end CFSG.RankThree.PartOne.S15K
