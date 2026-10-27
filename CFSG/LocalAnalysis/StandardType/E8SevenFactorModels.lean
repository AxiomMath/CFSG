module

public import CFSG.RankThree.PartOne.KE6.E6LStdIso
public import CFSG.RankThree.PartOne.KE6.E6LLayer
public import CFSG.RankThree.PartOne.KE6.E8T3Torus
public import CFSG.LocalAnalysis.StandardType.E8SevenLayerOrderCenter
public import CFSG.RankThree.PartOne.KD4L.TrialityEquiv
public import CFSG.LieType.Steinberg.CentralExt.TwistedE6Center
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LieType.CurtisTits.Minuscule
public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LocalAnalysis.StandardType.GGE6TwoSevenLabelTriD4
public import CFSG.RankThree.PartOne.KE6.E8T3A2
public import CFSG.RankThree.PartOne.KE6.E8T3Act
public import CFSG.RankThree.PartOne.KE6.E8T3Conj
public import CFSG.RankThree.PartOne.KE6.E8T3Supports
public import CFSG.RankThree.PartOne.KE6.E8T3Trans

public noncomputable section

namespace CFSG.StandardType.E8SevenModels

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.CentralExt
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

section D4Equiv
variable {τ : Tag} [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L]
  {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {n₁ : ModGL τ L}
  {π : Equiv.Perm (Fin τ.rank)} {e : ℕ}

theorem thetaFixed_equiv_of_standard (hstd : StdTwist n₁ π e) {h n : ModGL τ L}
    (hh : h ∈ subsystemGroup τ L (d4Set τ))
    (hlang : ∀ g : ModGL τ L,
      n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g * n⁻¹ = g ↔
        n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (h * g * h⁻¹) * n₁⁻¹ =
          h * g * h⁻¹)
    {P : Subgroup (ModGL τ L)}
    (hP : P = subsystemGroup τ L (d4Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    Nonempty (P ≃* d4ThetaFixed L (iterateFrobenius L ℓ f) e) := by
  have hmem : ∀ g : ModGL τ L, g ∈ P ↔ h * g * h⁻¹ ∈ stdLayer ℓ f n₁ := fun g => by
    rw [hP, Subgroup.mem_inf, CFSG.RankThree.PartOne.KD4L.mem_stdLayer, mem_twistedFixedPoints, hlang g]
    refine and_congr_left fun _ => ⟨fun hg => mul_mem (mul_mem hh hg) (inv_mem hh), fun hg => ?_⟩
    have := mul_mem (mul_mem (inv_mem hh) hg) hh
    simpa [mul_assoc] using this
  let eP : P ≃* stdLayer ℓ f n₁ :=
    { toFun := fun g => ⟨h * g * h⁻¹, (hmem g).1 g.2⟩
      invFun := fun u => ⟨h⁻¹ * u * h, (hmem _).2 (by simp [mul_assoc])⟩
      left_inv := fun g => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  exact ⟨eP.trans hstd.layerEquiv⟩

theorem thetaFixed_equiv_of_action (hf : 1 ≤ f) (π : Equiv.Perm (Fin τ.rank)) (e : ℕ)
    (he : e = 1 ∨ e = 2) (hπe : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (rhoE e k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    {P : Subgroup (ModGL τ L)}
    (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    Nonempty (P ≃* d4ThetaFixed L (iterateFrobenius L ℓ f) e) := by
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have h := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at h
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdTwist n₁ π e := ⟨he, hπe, hπ, hπ', hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  exact thetaFixed_equiv_of_standard hstd hh hlang hP


end D4Equiv


variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem card_center_stdLayer_of_rho {n₁ : ModGL .E8 L} {π : Equiv.Perm (Fin Tag.E8.rank)}
    (h : StdTwist6 n₁ π) (hπ : π = rhoτ .E8) :
    Nat.card (Subgroup.center (stdLayer .E8 2 1 n₁)) = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (K2 L 2 1) := finite_frobeniusFixedField (by norm_num : 1 ≤ 2 * 1)
  have hK : Nat.card (K2 L 2 1) = 2 ^ 2 := by simpa using (card_K2 (L := L) (ℓ := 2) (f := 1) le_rfl)
  have hθ : ∀ c : K2 L 2 1, theta2 L 2 1 c = c ^ 2 := by
    intro c
    rw [theta2, iterateFrobenius_def, pow_one]
  have hcard := (TwistedE6Closed.card_center_fixedGroup (k := K2 L 2 1)
    (θ := theta2 L 2 1) (q := 2) hK hθ).1
  have hψ : Function.Injective (psi2 .E8 L 2 1) := by
    intro x y hxy
    apply Subtype.ext
    have h1 := baseChangeGL_injective _ hxy
    exact (m27Equiv .E8 (K2 L 2 1)).symm.injective (Subtype.ext h1)
  let eP : stdLayer .E8 2 1 n₁ ≃* fixedGroup (K2 L 2 1) (theta2 L 2 1) :=
    (MulEquiv.subgroupCongr (h.stdLayer_eq_range_of_rho hπ)).trans
      (MonoidHom.ofInjective hψ).symm
  have hc : Nat.card (Subgroup.center (stdLayer .E8 2 1 n₁)) =
      Nat.card (Subgroup.center (fixedGroup (K2 L 2 1) (theta2 L 2 1))) := by
    rw [← Subgroup.map_center_eq eP, Subgroup.card_map_of_injective eP.injective]
  rw [hc, hcard]
  norm_num

theorem ggHasLabel_minGroup_e6_two {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) :
    GGHasLabel ⟨.E6, 0, 1⟩ (e6Data_valid.minGroup F ⧸ Subgroup.center (e6Data_valid.minGroup F)) := by
  have hker : (e6Isogeny F).ker = Subgroup.center (e6Data_valid.minGroup F) :=
    le_antisymm
      (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
        (CFSG.LieType.CurtisTits.isQuasisimple_e6 F) (e6Isogeny_ne_one F))
      (MinusculeClosed.center_le_ker_of_surjective (e6Isogeny_surjective F)
        center_adjointGroup_eq_bot)
  let eQ : (e6Data_valid.minGroup F ⧸ Subgroup.center (e6Data_valid.minGroup F)) ≃*
      TableBExc.RecipeGroup .E6 F :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivOfSurjective (e6Isogeny F) (e6Isogeny_surjective F)).trans
        (TableBExc.recipeEquiv .E6 F).symm)
  refine ⟨F, inferInstance, inferInstance, ?_, ⟨eQ⟩⟩
  simpa using hF

theorem ggHasLabel_stdLayer_of_one {n₁ : ModGL .E8 L} {π : Equiv.Perm (Fin Tag.E8.rank)}
    (h : StdTwist6 n₁ π) (hπ : π = 1) :
    GGHasLabel ⟨.E6, 0, 1⟩ ((stdLayer .E8 2 1 n₁) ⧸ Subgroup.center (stdLayer .E8 2 1 n₁)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := frobeniusFixedField L 2 1
  have : Finite F := finite_frobeniusFixedField le_rfl
  have hF : Nat.card F = 2 := by simpa [F] using (card_frobeniusFixedField_pow (L := L) (ℓ := 2) (m := 1) le_rfl)
  let eP : stdLayer .E8 2 1 n₁ ≃* subsystemGroup .E8 F (e6Set .E8) :=
    (MulEquiv.subgroupCongr (h.stdLayer_eq_map_of_one hπ)).trans
      (Subgroup.equivMapOfInjective (subsystemGroup .E8 F (e6Set .E8))
        (baseChangeGL F.subtype) (baseChangeGL_injective F.subtype)).symm
  let eM := eP.trans (m27Equiv .E8 F)
  let eC : (stdLayer .E8 2 1 n₁ ⧸ Subgroup.center (stdLayer .E8 2 1 n₁)) ≃*
      (e6Data_valid.minGroup F ⧸ Subgroup.center (e6Data_valid.minGroup F)) :=
    QuotientGroup.congr _ _ eM (Subgroup.map_center_eq eM)
  obtain ⟨k, hkField, hkFinite, hk, ⟨eR⟩⟩ := ggHasLabel_minGroup_e6_two hF
  let _ := hkField
  let _ := hkFinite
  exact ⟨k, inferInstance, inferInstance, hk, ⟨eC.trans eR⟩⟩

theorem ggHasLabel_stdLayer_of_center_three_free {n₁ : ModGL .E8 L}
    {π : Equiv.Perm (Fin Tag.E8.rank)} (h : StdTwist6 n₁ π)
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center (stdLayer .E8 2 1 n₁))) :
    GGHasLabel ⟨.E6, 0, 1⟩ ((stdLayer .E8 2 1 n₁) ⧸ Subgroup.center (stdLayer .E8 2 1 n₁)) := by
  rcases h.hπ with hπ | hπ
  · exact ggHasLabel_stdLayer_of_one h hπ
  · exact False.elim (h3 (by rw [card_center_stdLayer_of_rho h hπ]))

theorem ggHasLabel_e6_layer_of_center_three_free (n : ModGL .E8 L)
    (hn : n ∈ monomialSubgroup .E8 L)
    (hmaps : ∀ β ∈ parabolicRoots .E8 (e6Nodes .E8),
      weylQuotientHom .E8 L ⟨n, hn⟩ • β ∈ parabolicRoots .E8 (e6Nodes .E8))
    {P : Subgroup (ModGL .E8 L)}
    (hP : P = rootSpan .E8 L (parabolicRoots .E8 (e6Nodes .E8)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L 2 1))))
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center P)) :
    GGHasLabel ⟨.E6, 0, 1⟩ (P ⧸ Subgroup.center P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hw : MapsJ .E8 (e6Set .E8) (weylQuotientHom .E8 L ⟨n, hn⟩) := by
    intro α hα
    have h := hmaps α (by rwa [e6Nodes_eq_e6Set])
    rwa [e6Nodes_eq_e6Set] at h
  obtain ⟨u, hu, π, hπ, hact⟩ := exists_action hw
  have hπJ : ∀ i ∈ e6Set .E8, π i ∈ e6Set .E8 := by
    rcases hπ with rfl | rfl
    · exact fun i hi => hi
    · exact fun i hi => rhoτ_mem hi
  have hπJ' : ∀ i ∈ e6Set .E8, π.symm i ∈ e6Set .E8 := by
    rcases hπ with rfl | rfl
    · exact fun i hi => hi
    · exact fun i hi => rhoτ_symm_mem hi
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ :=
    exists_conj_twistedFixed le_rfl hn hπJ hπJ' hu hact
  have hstd : StdTwist6 n₁ π := ⟨hπ, hgen⟩
  have hP' : P = subsystemGroup .E8 L (e6Set .E8) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L 2 1))) := by
    rw [hP, subsystemGroup_eq_rootSpan, e6Nodes_eq_e6Set]
  have hmem : ∀ g : ModGL .E8 L, g ∈ P ↔ h * g * h⁻¹ ∈ stdLayer .E8 2 1 n₁ := fun g => by
    rw [hP', Subgroup.mem_inf, CFSG.RankThree.PartOne.KE6.mem_stdLayer, mem_twistedFixedPoints, hlang g]
    refine and_congr_left fun _ => ⟨fun hg => mul_mem (mul_mem hh hg) (inv_mem hh), fun hg => ?_⟩
    have hq := mul_mem (mul_mem (inv_mem hh) hg) hh
    simpa [mul_assoc] using hq
  let eP : P ≃* stdLayer .E8 2 1 n₁ :=
    { toFun := fun g => ⟨h * g * h⁻¹, (hmem g).1 g.2⟩
      invFun := fun z => ⟨h⁻¹ * z * h, (hmem _).2 (by simp [mul_assoc])⟩
      left_inv := fun g => Subtype.ext (by simp [mul_assoc])
      right_inv := fun z => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have h3std : ¬ 3 ∣ Nat.card (Subgroup.center (stdLayer .E8 2 1 n₁)) := by
    rw [← Subgroup.map_center_eq eP, Subgroup.card_map_of_injective eP.injective]
    exact h3
  let eC : (P ⧸ Subgroup.center P) ≃*
      (stdLayer .E8 2 1 n₁ ⧸ Subgroup.center (stdLayer .E8 2 1 n₁)) :=
    QuotientGroup.congr _ _ eP (Subgroup.map_center_eq eP)
  obtain ⟨k, hkField, hkFinite, hk, ⟨eR⟩⟩ := ggHasLabel_stdLayer_of_center_three_free hstd h3std
  let _ := hkField
  let _ := hkFinite
  exact ⟨k, inferInstance, inferInstance, hk, ⟨eC.trans eR⟩⟩

theorem not_three_dvd_center_sigma_singleton (n : ModGL .E8 L)
    (hn : n ∈ monomialSubgroup .E8 L)
    (hπ : weylQuotientHom .E8 L ⟨n, hn⟩ = e8T3We 1)
    {S : Set (Fin Tag.E8.rank → ℤ)} (P : Unit → Subgroup (ModGL .E8 L))
    (hfam : IsSigmaFamily n (iterateFrobenius L 2 1) S P) :
    ¬ 3 ∣ Nat.card (Subgroup.center (P ())) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Φ : ModGL .E8 L →* ModGL .E8 L := Units.map (entrywiseHom (iterateFrobenius L 2 1))
  let T : Subgroup (ModGL .E8 L) := twistedTorusOf n Φ
  have hTcard : Nat.card T = 7 ^ 4 := by
    have hc := natCard_e8T3Torus (Or.inl rfl) n hn hπ
      (Fr := iterateFrobenius L 2 1) (q := 2)
      (fun x => by rw [iterateFrobenius_def, pow_one]) dvd_rfl
    have h7 : e8T3D 1 2 = 7 := by decide
    simpa only [h7, T, Φ] using hc
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hTcard]; norm_num)
  obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := hfam
  have hZ : ∀ z : Subgroup.center (P ()), ((z : P ()) : ModGL .E8 L) ∈ T := by
    intro z
    have hzP : ((z : P ()) : ModGL .E8 L) ∈ P () := (z : P ()).2
    have hc := hPcent ((z : P ()) : ModGL .E8 L)
      (Subgroup.mem_sup_right (hPQ () hzP)) (hPR () hzP) (fun i w hw => ?_)
    · exact hc.1
    · cases i
      have hzw := (Subgroup.mem_center_iff.mp z.2 (⟨w, hw⟩ : P ())).symm
      exact congrArg (fun x : P () => (x : ModGL .E8 L)) hzw
  let f : Subgroup.center (P ()) →* T :=
    { toFun := fun z => ⟨((z : P ()) : ModGL .E8 L), hZ z⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : T => (x : ModGL .E8 L)) hab
  have hr : Nat.card f.range = Nat.card (Subgroup.center (P ())) :=
    Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm
  have hdiv := Subgroup.card_subgroup_dvd_card f.range
  rw [hr, hTcard] at hdiv
  intro h3
  exact (by decide +kernel : ¬ 3 ∣ 7 ^ 4) (h3.trans hdiv)


theorem ggHasLabel_d4_layer_two {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {k : Type} [Field k] [Finite k] [Algebra k Ω] [IsAlgClosure k Ω] (hk : Nat.card k = 2)
    (a b c : Fin Tag.E8.rank) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ha : a.val ∈ ({1, 2, 4} : Set ℕ)) (hb : b.val ∈ ({1, 2, 4} : Set ℕ))
    (hc : c.val ∈ ({1, 2, 4} : Set ℕ))
    (n : ModGL .E8 Ω) (hn : n ∈ monomialSubgroup .E8 Ω)
    (hact : ∃ u ∈ parabolicWeylGroup .E8 (d4Nodes .E8),
      ∀ α ∈ parabolicRoots .E8 (d4Nodes .E8),
        weylQuotientHom .E8 Ω ⟨n, hn⟩ • α = u • permLattice (List.formPerm [a, b, c]) α)
    {P : Subgroup (ModGL .E8 Ω)}
    (hP : P = rootSpan .E8 Ω (parabolicRoots .E8 (d4Nodes .E8)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius Ω 2 1)))) :
    GGHasLabel ⟨.triD4, 0, 1⟩ (P ⧸ Subgroup.center P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha' : a.val = 1 ∨ a.val = 2 ∨ a.val = 4 := by simpa using ha
  have hb' : b.val = 1 ∨ b.val = 2 ∨ b.val = 4 := by simpa using hb
  have hc' : c.val = 1 ∨ c.val = 2 ∨ c.val = 4 := by simpa using hc
  obtain ⟨hcycle, hπ, hπ'⟩ := leafCycle_E8 a b c ha' hb' hc' hab hbc hac
  rcases hcycle with h1 | h2
  · obtain ⟨eP⟩ := thetaFixed_equiv_of_action (ℓ := 2) (f := 1) le_rfl
      (List.formPerm [a, b, c]) 1 (Or.inl rfl) h1
      (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn hact hP
    exact E6TwoSeven.ggHasLabel_triD4_of_mulEquiv_d4ThetaFixed hk (Or.inl rfl) eP
  · obtain ⟨eP⟩ := thetaFixed_equiv_of_action (ℓ := 2) (f := 1) le_rfl
      (List.formPerm [a, b, c]) 2 (Or.inr rfl) h2
      (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn hact hP
    exact E6TwoSeven.ggHasLabel_triD4_of_mulEquiv_d4ThetaFixed hk (Or.inr rfl) eP


theorem ggHasLabel_transported_e6_layer (v : WeylGroup .E8) (n : ModGL .E8 L)
    (hn : n ∈ monomialSubgroup .E8 L)
    (hmaps : ∀ β ∈ parabolicRoots .E8 (e6Nodes .E8),
      (v⁻¹ * weylQuotientHom .E8 L ⟨n, hn⟩ * v) • β ∈ parabolicRoots .E8 (e6Nodes .E8))
    {P : Subgroup (ModGL .E8 L)}
    (hP : P = rootSpan .E8 L ((fun γ => v • γ) '' parabolicRoots .E8 (e6Nodes .E8)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L 2 1))))
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center P)) :
    GGHasLabel ⟨.E6, 0, 1⟩ (P ⧸ Subgroup.center P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Fr := iterateFrobenius L 2 1
  have hFrbij : Function.Bijective Fr := bijective_iterateFrobenius L 2 1
  let V := canonicalRep (coxeterSystem .E8) L v
  have hVm : V ∈ monomialSubgroup .E8 L := canonicalRep_mem_monomialSubgroup L v
  let n' := V⁻¹ * n * V
  have hn' : n' ∈ monomialSubgroup .E8 L := mul_mem (mul_mem (inv_mem hVm) hn) hVm
  have hπV : weylQuotientHom .E8 L ⟨V, hVm⟩ = v := weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom .E8 L ⟨n', hn'⟩ = v⁻¹ * weylQuotientHom .E8 L ⟨n, hn⟩ * v := by
    have heq : (⟨n', hn'⟩ : monomialSubgroup .E8 L) = ⟨V, hVm⟩⁻¹ * ⟨n, hn⟩ * ⟨V, hVm⟩ := Subtype.ext rfl
    rw [heq, map_mul, map_mul, map_inv, hπV]
  let P₀ := rootSpan .E8 L (parabolicRoots .E8 (e6Nodes .E8)) ⊓
    twistedFixedPoints n' (Units.map (entrywiseHom Fr))
  have hmap : P₀.map (MulAut.conj V).toMonoidHom = P := by
    rw [hP]
    exact map_conj_rootSpan_inf_twistedFixedPoints Fr hFrbij v n (fun _ h => h.1)
  let eP : P₀ ≃* P := (Subgroup.equivMapOfInjective P₀ (MulAut.conj V).toMonoidHom
    (MulAut.conj V).injective).trans (MulEquiv.subgroupCongr hmap)
  have h3₀ : ¬ 3 ∣ Nat.card (Subgroup.center P₀) := by
    intro h
    apply h3
    rw [← Subgroup.map_center_eq eP, Subgroup.card_map_of_injective eP.injective]
    exact h
  have hlabel := ggHasLabel_e6_layer_of_center_three_free n' hn'
    (fun β hβ => by rw [hπn']; exact hmaps β hβ) (P := P₀) rfl h3₀
  let eQ := QuotientGroup.congr _ _ eP (Subgroup.map_center_eq eP)
  exact largeEvenRawDatum_mono (fun _ _ _ _ ⟨f⟩ => ⟨eQ.symm.trans f⟩) hlabel

theorem ggHasLabel_transported_d4_layer_two {k : Type} [Field k] [Finite k]
    [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = 2)
    (v : WeylGroup .E8) (a b c : Fin Tag.E8.rank)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (ha : a.val ∈ ({1, 2, 4} : Set ℕ)) (hb : b.val ∈ ({1, 2, 4} : Set ℕ))
    (hc : c.val ∈ ({1, 2, 4} : Set ℕ))
    (n : ModGL .E8 L) (hn : n ∈ monomialSubgroup .E8 L)
    (hact : ∃ u ∈ parabolicWeylGroup .E8 (d4Nodes .E8),
      ∀ α ∈ parabolicRoots .E8 (d4Nodes .E8),
        (v⁻¹ * weylQuotientHom .E8 L ⟨n, hn⟩ * v) • α =
          u • permLattice (List.formPerm [a, b, c]) α)
    {P : Subgroup (ModGL .E8 L)}
    (hP : P = rootSpan .E8 L ((fun γ => v • γ) '' parabolicRoots .E8 (d4Nodes .E8)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L 2 1)))) :
    GGHasLabel ⟨.triD4, 0, 1⟩ (P ⧸ Subgroup.center P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Fr := iterateFrobenius L 2 1
  have hFrbij : Function.Bijective Fr := bijective_iterateFrobenius L 2 1
  let V := canonicalRep (coxeterSystem .E8) L v
  have hVm : V ∈ monomialSubgroup .E8 L := canonicalRep_mem_monomialSubgroup L v
  let n' := V⁻¹ * n * V
  have hn' : n' ∈ monomialSubgroup .E8 L := mul_mem (mul_mem (inv_mem hVm) hn) hVm
  have hπV : weylQuotientHom .E8 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom .E8 L ⟨n', hn'⟩ =
      v⁻¹ * weylQuotientHom .E8 L ⟨n, hn⟩ * v := by
    have heq : (⟨n', hn'⟩ : monomialSubgroup .E8 L) =
        ⟨V, hVm⟩⁻¹ * ⟨n, hn⟩ * ⟨V, hVm⟩ := Subtype.ext rfl
    rw [heq, map_mul, map_mul, map_inv, hπV]
  let P₀ := rootSpan .E8 L (parabolicRoots .E8 (d4Nodes .E8)) ⊓
    twistedFixedPoints n' (Units.map (entrywiseHom Fr))
  have hmap : P₀.map (MulAut.conj V).toMonoidHom = P := by
    rw [hP]
    exact map_conj_rootSpan_inf_twistedFixedPoints Fr hFrbij v n (fun _ h => h.1)
  let eP : P₀ ≃* P :=
    (Subgroup.equivMapOfInjective P₀ (MulAut.conj V).toMonoidHom
      (MulAut.conj V).injective).trans (MulEquiv.subgroupCongr hmap)
  obtain ⟨u, hu, huact⟩ := hact
  have hact' : ∃ u ∈ parabolicWeylGroup .E8 (d4Nodes .E8),
      ∀ α ∈ parabolicRoots .E8 (d4Nodes .E8),
        weylQuotientHom .E8 L ⟨n', hn'⟩ • α =
          u • permLattice (List.formPerm [a, b, c]) α :=
    ⟨u, hu, fun α hα => by rw [hπn']; exact huact α hα⟩
  have hlabel := ggHasLabel_d4_layer_two (k := k) hk a b c hab hbc hac ha hb hc
    n' hn' hact' (P := P₀) rfl
  let eQ := QuotientGroup.congr _ _ eP (Subgroup.map_center_eq eP)
  exact largeEvenRawDatum_mono (fun _ _ _ _ ⟨f⟩ => ⟨eQ.symm.trans f⟩) hlabel

end CFSG.StandardType.E8SevenModels
