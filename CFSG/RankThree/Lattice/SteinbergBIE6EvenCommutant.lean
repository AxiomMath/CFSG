module

public import CFSG.RankThree.Chevalley.SteinbergBIE6Commutant
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBridge

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley
open scoped Pointwise

section Pair

variable {Ω : Type} [Field Ω] {M : Type*} [Ring M] [Algebra Ω M]

theorem pair_expand (A₁ B₁ A₂ B₂ : M) (a b : Ω) :
    (1 + a • A₁ + a ^ 2 • B₁) * (1 + b • A₂ + b ^ 2 • B₂) =
      ∑ t : Fin 3 × Fin 3, (a ^ (t.1 : ℕ) * b ^ (t.2 : ℕ)) •
        (quadCoeff A₁ B₁ t.1 * quadCoeff A₂ B₂ t.2) := by
  simp_rw [one_add_eq_sum, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm,
    Fintype.sum_prod_type]

theorem commute_sum_smul_iff {ι : Type*} [Fintype ι] {X : M} (c : ι → Ω) (C : ι → M) :
    Commute X (∑ i, c i • C i) ↔ ∑ i, c i • (X * C i - C i * X) = 0 := by
  rw [Commute, SemiconjBy, ← sub_eq_zero, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [mul_smul_comm, smul_mul_assoc, smul_sub]

theorem commute_of_pair_card {X A₁ B₁ A₂ B₂ : M} {q : ℕ} (hq : 3 ≤ q) {F : Finset Ω}
    (hF : F.card = q ^ 2)
    (h : ∀ a ∈ F, Commute X ((1 + a • A₁ + a ^ 2 • B₁) * (1 + a ^ q • A₂ + (a ^ q) ^ 2 • B₂))) :
    Commute X A₁ ∧ Commute X B₁ ∧ Commute X A₂ ∧ Commute X B₂ := by
  set n : Fin 3 × Fin 3 → ℕ := fun t => (t.1 : ℕ) + q * (t.2 : ℕ) with hn
  have hinj : Function.Injective n := by
    rintro ⟨s, t⟩ ⟨s', t'⟩ e
    simp only [hn] at e
    have hs := s.2
    have hs' := s'.2
    have ht := t.2
    have ht' := t'.2
    have h1 : (s : ℕ) = s' := by
      have := congrArg (· % q) e
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : (s : ℕ) < q),
        Nat.mod_eq_of_lt (by omega : (s' : ℕ) < q)] at this
      exact this
    have h2 : (t : ℕ) = t' := by
      rw [h1] at e
      have := Nat.add_left_cancel e
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  have hlt : ∀ t, n t < F.card := by
    rintro ⟨s, t⟩
    rw [hF]
    have hs := s.2
    have ht := t.2
    simp only [hn]
    have h3 : 3 * q ≤ q * q := Nat.mul_le_mul_right q hq
    nlinarith
  have key := eq_zero_of_forall_sum_pow_smul hinj hlt
    (c := fun t => X * (quadCoeff A₁ B₁ t.1 * quadCoeff A₂ B₂ t.2) -
      (quadCoeff A₁ B₁ t.1 * quadCoeff A₂ B₂ t.2) * X) fun a ha => by
    have h1 := (commute_sum_smul_iff (M := M) (X := X)
      (fun t : Fin 3 × Fin 3 => a ^ (t.1 : ℕ) * (a ^ q) ^ (t.2 : ℕ))
      (fun t => quadCoeff A₁ B₁ t.1 * quadCoeff A₂ B₂ t.2)).1 (by rw [← pair_expand]; exact h a ha)
    rw [← h1]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hn, pow_add, pow_mul]
  have e : ∀ s t, X * (quadCoeff A₁ B₁ s * quadCoeff A₂ B₂ t) =
      (quadCoeff A₁ B₁ s * quadCoeff A₂ B₂ t) * X := fun s t => sub_eq_zero.1 (key (s, t))
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (by simpa [quadCoeff] using e 1 0 : X * A₁ = A₁ * X)
  · exact (by simpa [quadCoeff] using e 2 0 : X * B₁ = B₁ * X)
  · exact (by simpa [quadCoeff] using e 0 1 : X * A₂ = A₂ * X)
  · exact (by simpa [quadCoeff] using e 0 2 : X * B₂ = B₂ * X)

end Pair

section Toral

variable {τ : Tag} {K : Type} [Field K]

theorem mem_torusGroup_of_commute_subsystemGroup {S : Set (Fin τ.rank)} {h z : ModGL τ K}
    (hh : h ∈ torusGroup τ K) (hz : z ∈ subsystemGroup τ K S)
    (hc : ∀ x ∈ subsystemGroup τ K S, h * z * x = x * (h * z)) : h * z ∈ torusGroup τ K := by
  obtain ⟨v, hv, hzv⟩ := mem_subsystemCells.1 (subsystemGroup_subset_subsystemCells hz)
  rw [subsystemCell_eq_mul hv] at hzv
  obtain ⟨_, ⟨b, hb, _, rfl, rfl⟩, u, hu, hbu⟩ := hzv
  beta_reduce at hbu
  have hv1 : v = 1 := by
    by_contra hne
    obtain ⟨i, hi⟩ := (weyl_exchange_condition τ).2.2.2 v hne
    have hiS : i ∈ S := by
      by_contra hiS
      have h1 := (IsRoot.height_neg_iff hi.1).1 hi.2 i
      rw [smul_apply_of_mem_parabolicWeylGroup hv _ hiS, Pi.single_eq_same] at h1
      omega
    have hI : (Pi.single i 1 : Fin τ.rank → ℤ) ∈ inversionSet v :=
      ⟨isRoot_single τ i, by rw [height_single]; exact one_pos, hi⟩
    have hx : xUnit τ K i 1 ∈ rootSpan τ K (inversionSet v) := by
      rw [← pinnedX_single]
      exact pinnedX_mem_rootSpan hI 1
    have hconj := conj_pinnedX_of_mem_torusGroup (inv_mem hh) (isRoot_single τ i) 1
    rw [inv_inv, pinnedX_single, pinnedX_single] at hconj
    set x' := xUnit τ K i (torusRootChar h⁻¹ (Pi.single i 1) * 1) with hx'def
    have hcz := hc _ (xUnit_mem_subsystemGroup hiS 1)
    have hzx : z * xUnit τ K i 1 = x' * z := by
      rw [← hconj]
      calc z * xUnit τ K i 1 = h⁻¹ * (h * z * xUnit τ K i 1) := by group
        _ = h⁻¹ * (xUnit τ K i 1 * (h * z)) := by rw [hcz]
        _ = h⁻¹ * xUnit τ K i 1 * h * z := by group
    rw [← hbu] at hzx
    have h1 := (bijOn_subsystemCell (K := K) hv).injOn (x₁ := (x' * b, u))
      (x₂ := (b, u * xUnit τ K i 1)) ⟨mul_mem (xUnit_mem_subsystemBorel hiS _) hb, hu⟩
      ⟨hb, mul_mem hu hx⟩ (by
        simp only [mul_assoc] at hzx ⊢
        exact hzx.symm)
    have h2 : xUnit τ K i 1 = 1 := by
      have h3 := (Prod.ext_iff.1 h1).2
      simpa using h3
    have h4 : pinnedX τ K (Pi.single i 1) 1 = pinnedX τ K (Pi.single i 1) 0 := by
      rw [pinnedX_single, pinnedX_zero, h2]
    exact one_ne_zero (pinnedX_injective τ K _ h4)
  subst hv1
  have hu1 : u = 1 := by
    rw [inversionSet_one] at hu
    simpa [rootSpan] using hu
  have hzB : z ∈ subsystemBorel τ K S := by
    rw [← hbu, hu1, canonicalRep_one, mul_one, mul_one]
    exact hb
  rw [← SetLike.mem_coe, coe_subsystemBorel] at hzB
  obtain ⟨t, ht, w', hw', htw⟩ := hzB
  obtain ⟨wS, ⟨hwS, hwSΦ⟩, -⟩ := (parabolic_Weyl_coordinate_stabilizer τ S).2.2.2
  set n := canonicalRep (coxeterSystem τ) K wS
  have hht : h * t ∈ torusGroup τ K := mul_mem hh (subsystemTorus_le_torusGroup ht)
  have hconj : n * (h * z) * n⁻¹ = h * z := by
    rw [← hc n (canonicalRep_mem_subsystemGroup hwS), mul_inv_cancel_right]
  have hnt : n * (h * t) * n⁻¹ ∈ torusGroup τ K := by
    have hN := mem_normalizer_torusGroup_of_mem_monomialSubgroup
      (canonicalRep_mem_monomialSubgroup K wS)
    exact (Subgroup.mem_normalizer_iff.1 hN _).1 hht
  have hnw : n * w' * n⁻¹ ∈ negUnipotent τ K := by
    have h1 := canonicalRep_conj_mem_rootSpan (w := wS) (S := parabolicPosRoots τ S)
      (fun α hα => hα.2.1) hw'
    rw [hwSΦ] at h1
    refine rootSpan_le_negUnipotent ?_ h1
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨IsRoot.neg hα.2.1, by rw [height_neg]; linarith [hα.2.2]⟩
  have hhz : h * z = h * t * w' := by rw [← htw, mul_assoc]
  have hmem : (n * (h * t) * n⁻¹)⁻¹ * (h * z) ∈ borelGroup τ K ⊓ negUnipotent τ K := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (torusGroup_le_borelGroup (inv_mem hnt)) ?_, ?_⟩
    · rw [hhz]
      exact mul_mem (torusGroup_le_borelGroup hht)
        (Subgroup.mem_sup_right (parabolicLeviUnipotent_le_posUnipotent S hw'))
    · have e : n * (h * z) * n⁻¹ = n * (h * t) * n⁻¹ * (n * w' * n⁻¹) := by
        rw [hhz]
        group
      rw [← hconj, e, inv_mul_cancel_left]
      exact hnw
  rw [borelGroup_inf_negUnipotent, Subgroup.mem_bot] at hmem
  rw [← inv_mul_eq_one.1 hmem]
  exact hnt

theorem rootSpan_le_centralizer {S : Set (Fin τ.rank → ℤ)} {g : ModGL τ K}
    (h : ∀ α ∈ S, ∀ c : K, pinnedX τ K α c * g = g * pinnedX τ K α c) :
    rootSpan τ K S ≤ Subgroup.centralizer {g} := by
  refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  exact h α hα c

end Toral

theorem GenFixedRootDatum.exists_finset_orbitField {τ : Tag} {p₀ : ℕ}
    [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k] {M : Type} [CommGroup M]
    (D : GenFixedRootDatum τ p₀ k M) {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    ∃ F : Finset k, F.card = D.q ^ GenFixedRootDatum.orbitCard O ∧
      ∀ a, a ∈ F ↔ a ∈ D.orbitField O := by
  have h := D.card_orbitField hO
  have hpos : 0 < D.q ^ GenFixedRootDatum.orbitCard O :=
    pow_pos (pow_pos (Fact.out : p₀.Prime).pos _) _
  have hfin : ((D.orbitField O : Subfield k) : Set k).Finite := by
    have : Finite (D.orbitField O) := Nat.finite_of_card_ne_zero (by rw [h]; exact hpos.ne')
    exact Set.toFinite _
  refine ⟨hfin.toFinset, ?_, fun a => hfin.mem_toFinset⟩
  rw [← Nat.card_eq_card_finite_toFinset hfin]
  exact h

namespace E6EvenFixedRootDatum

variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsAlgClosed Ω] (D : E6EvenFixedRootDatum Ω)

theorem rootGroup_eq_subsystemGroup : D.rootGroup = subsystemGroup Tag.E6 Ω D.support := by
  rw [rootGroup, D.Ξ_eq_parabolicRoots, subsystemGroup_eq_rootSpan]

theorem map_uSL_frobenius (O : Set (Fin Tag.E6.rank → ℤ)) (k : ℕ) (a : D.orbitField O) :
    Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 (D.f * k))
        (Matrix.SpecialLinearGroup.map (D.orbitField O).subtype (uSL a)) =
      uSL ((a : Ω) ^ D.q ^ k) := by
  rw [map_uSL, map_uSL, iterateFrobenius_def, pow_mul]
  rfl

theorem map_vSL_frobenius (O : Set (Fin Tag.E6.rank → ℤ)) (k : ℕ) (a : D.orbitField O) :
    Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 (D.f * k))
        (Matrix.SpecialLinearGroup.map (D.orbitField O).subtype (vSL a)) =
      vSL ((a : Ω) ^ D.q ^ k) := by
  rw [map_vSL, map_vSL, iterateFrobenius_def, pow_mul]
  rfl

theorem orbitX_eq_prod {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits) (a : D.orbitField O) :
    D.orbitX O a = ((List.range (orbitCard O)).map fun k =>
      pinnedX Tag.E6 Ω (D.δ^[k] (orbitRoot O)) ((a : Ω) ^ D.q ^ k)).prod := by
  rw [orbitX, orbitMap]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  have hr : IsRoot Tag.E6 (D.δ^[k] (orbitRoot O)) := by
    rcases D.iterate_δ k (orbitRoot O) with e | e <;> rw [e]
    · exact D.isRoot_of_mem_Ξ (D.mem_Ξ_of_mem_orbits hO (D.orbitRoot_mem hO))
    · exact D.isRoot_δ (D.isRoot_of_mem_Ξ (D.mem_Ξ_of_mem_orbits hO (D.orbitRoot_mem hO)))
  rw [D.map_uSL_frobenius, CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo hr]

theorem orbitY_eq_prod {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits) (a : D.orbitField O) :
    D.orbitY O a = ((List.range (orbitCard O)).map fun k =>
      pinnedX Tag.E6 Ω (-D.δ^[k] (orbitRoot O)) ((a : Ω) ^ D.q ^ k)).prod := by
  rw [orbitY, orbitMap]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  have hr : IsRoot Tag.E6 (D.δ^[k] (orbitRoot O)) := by
    rcases D.iterate_δ k (orbitRoot O) with e | e <;> rw [e]
    · exact D.isRoot_of_mem_Ξ (D.mem_Ξ_of_mem_orbits hO (D.orbitRoot_mem hO))
    · exact D.isRoot_δ (D.isRoot_of_mem_Ξ (D.mem_Ξ_of_mem_orbits hO (D.orbitRoot_mem hO)))
  rw [D.map_vSL_frobenius, CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo hr]

theorem exists_finset_orbitField {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits) :
    ∃ F : Finset Ω, F.card = D.q ^ orbitCard O ∧ ∀ a, a ∈ F ↔ a ∈ D.orbitField O :=
  D.gen.exists_finset_orbitField (D.mem_gen_orbits.2 hO)

theorem four_le_q : 4 ≤ D.q :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ D.f := Nat.pow_le_pow_right (by norm_num) D.two_le_f

theorem commute_xOp_yOp_of_mem_e6Commutant {X : Module.End Ω (RootModule Tag.E6 Ω)}
    (hX : X ∈ e6Commutant (D.orbitGroup : Set (ModGL Tag.E6 Ω))) {j : Fin Tag.E6.rank}
    (hj : j ∈ D.support) (c : Ω) :
    Commute X (xOp Tag.E6 Ω j c) ∧ Commute X (yOp Tag.E6 Ω j c) := by
  set O := D.simpleOrbit j with hOdef
  have hO : O ∈ D.orbits := ⟨j, hj, rfl⟩
  have hα₀ := D.orbitRoot_mem hO
  have hOα := D.eq_pair_of_mem_orbits hO hα₀
  set α₀ := orbitRoot O with hα₀def
  have hjO : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ O := ⟨0, rfl⟩
  set i := orbitIndex O with hidef
  have hα₀i : α₀ = Pi.single i 1 := rfl
  have hiS : i ∈ D.support := by
    rw [mem_support_iff, ← hα₀i]
    exact D.mem_Ξ_of_mem_orbits hO hα₀
  have hδα₀ : D.δ α₀ = Pi.single (e6QpPerm D.qpIndex i) 1 := by rw [hα₀i, D.δ_single hiS]
  have hX' : ∀ a : D.orbitField O, Commute X (D.orbitX O a : Module.End Ω (RootModule Tag.E6 Ω)) ∧
      Commute X (D.orbitY O a : Module.End Ω (RootModule Tag.E6 Ω)) := fun a =>
    ⟨hX _ (D.orbitX_mem_orbitGroup hO a), hX _ (D.orbitY_mem_orbitGroup hO a)⟩
  obtain ⟨F, hFcard, hF⟩ := D.exists_finset_orbitField hO
  have hq := D.four_le_q
  by_cases hfix : D.δ α₀ = α₀
  ·
    have h1 : orbitCard O = 1 := by
      rw [orbitCard, hOα, hfix, Set.pair_eq_singleton, Set.ncard_singleton]
    have hji : j = i := by
      rw [hOα, hfix, Set.pair_eq_singleton, Set.mem_singleton_iff, hα₀i] at hjO
      exact single_one_inj hjO
    have hXO : ∀ a : D.orbitField O, D.orbitX O a = xUnit Tag.E6 Ω i a := fun a => by
      rw [D.orbitX_eq_prod hO, h1, List.range_one, List.map_singleton, List.prod_singleton,
        Function.iterate_zero, id, pow_zero, pow_one, ← hα₀def, hα₀i, pinnedX_single]
    have hYO : ∀ a : D.orbitField O, D.orbitY O a = yUnit Tag.E6 Ω i a := fun a => by
      rw [D.orbitY_eq_prod hO, h1, List.range_one, List.map_singleton, List.prod_singleton,
        Function.iterate_zero, id, pow_zero, pow_one, ← hα₀def, hα₀i, pinnedX_neg_single]
    have hF3 : 3 ≤ F.card := by rw [hFcard, h1, pow_one]; omega
    rw [hji]
    refine ⟨commute_xOp_of_three_le_card hF3 (fun a ha => ?_) c,
      commute_yOp_of_three_le_card hF3 (fun a ha => ?_) c⟩
    · have := (hX' ⟨a, (hF a).1 ha⟩).1
      rwa [hXO, coe_xUnit] at this
    · have := (hX' ⟨a, (hF a).1 ha⟩).2
      rwa [hYO, coe_yUnit] at this
  ·
    have hne : α₀ ≠ D.δ α₀ := fun e => hfix e.symm
    have h2 : orbitCard O = 2 := by
      rw [orbitCard, hOα]
      exact Set.ncard_pair hne
    set i' := e6QpPerm D.qpIndex i
    have hXO : ∀ a : D.orbitField O, (D.orbitX O a : Module.End Ω (RootModule Tag.E6 Ω)) =
        xOp Tag.E6 Ω i a * xOp Tag.E6 Ω i' ((a : Ω) ^ D.q) := fun a => by
      rw [D.orbitX_eq_prod hO, h2, show List.range 2 = [0, 1] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        Function.iterate_zero, id, Function.iterate_one, pow_zero, pow_one]
      rw [← hα₀def, hδα₀, hα₀i, pinnedX_single, pinnedX_single, Units.val_mul, coe_xUnit,
        coe_xUnit]
    have hYO : ∀ a : D.orbitField O, (D.orbitY O a : Module.End Ω (RootModule Tag.E6 Ω)) =
        yOp Tag.E6 Ω i a * yOp Tag.E6 Ω i' ((a : Ω) ^ D.q) := fun a => by
      rw [D.orbitY_eq_prod hO, h2, show List.range 2 = [0, 1] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        Function.iterate_zero, id, Function.iterate_one, pow_zero, pow_one]
      rw [← hα₀def, hδα₀, hα₀i, pinnedX_neg_single, pinnedX_neg_single, Units.val_mul,
        coe_yUnit, coe_yUnit]
    have hFc : F.card = D.q ^ 2 := by rw [hFcard, h2]
    obtain ⟨hA₁, hB₁, hA₂, hB₂⟩ := commute_of_pair_card (by omega) hFc (X := X)
      (A₁ := xCoeff Tag.E6 Ω i 1) (B₁ := xCoeff Tag.E6 Ω i 2)
      (A₂ := xCoeff Tag.E6 Ω i' 1) (B₂ := xCoeff Tag.E6 Ω i' 2) fun a ha => by
        have := (hX' ⟨a, (hF a).1 ha⟩).1
        rwa [hXO, xOp_E6_eq, xOp_E6_eq] at this
    obtain ⟨hC₁, hD₁, hC₂, hD₂⟩ := commute_of_pair_card (by omega) hFc (X := X)
      (A₁ := yCoeff Tag.E6 Ω i 1) (B₁ := yCoeff Tag.E6 Ω i 2)
      (A₂ := yCoeff Tag.E6 Ω i' 1) (B₂ := yCoeff Tag.E6 Ω i' 2) fun a ha => by
        have := (hX' ⟨a, (hF a).1 ha⟩).2
        rwa [hYO, yOp_E6_eq, yOp_E6_eq] at this
    have hji : j = i ∨ j = i' := by
      rw [hOα, hδα₀, hα₀i] at hjO
      rcases hjO with e | e
      · exact Or.inl (single_one_inj e)
      · exact Or.inr (single_one_inj e)
    rcases hji with e | e <;> rw [e]
    · rw [xOp_E6_eq, yOp_E6_eq]
      exact ⟨commute_one_add_of_commute hA₁ hB₁ c, commute_one_add_of_commute hC₁ hD₁ c⟩
    · rw [xOp_E6_eq, yOp_E6_eq]
      exact ⟨commute_one_add_of_commute hA₂ hB₂ c, commute_one_add_of_commute hC₂ hD₂ c⟩

theorem e6Commutant_orbitGroup :
    e6Commutant (D.orbitGroup : Set (ModGL Tag.E6 Ω)) =
      e6Commutant (D.rootGroup : Set (ModGL Tag.E6 Ω)) := by
  refine Set.Subset.antisymm (fun X hX => ?_) (e6Commutant_anti D.orbitGroup_le_rootGroup)
  rw [D.rootGroup_eq_subsystemGroup]
  exact mem_e6Commutant_subsystemGroup
    (fun j hj c => (D.commute_xOp_yOp_of_mem_e6Commutant hX hj c).1)
    (fun j hj c => (D.commute_xOp_yOp_of_mem_e6Commutant hX hj c).2)

end E6EvenFixedRootDatum

end CFSG.RankThree.Lattice
