module

public import CFSG.RankThree.PartOne.KD4L.TauFixed
public import CFSG.Monster.B.Classical.E6AdjointDefs

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4L

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.Lattice CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.Monster.B.Classical.E6Adjoint
open scoped Pointwise

section Pair

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
  (hf : 1 ≤ f)

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem toLex_single_four_lt_two :
    toLex (Pi.single 4 1 : Fin Tag.E6.rank → ℤ) < toLex (Pi.single 2 1) := by
  have key : ∀ j : Fin 6, (j : ℕ) < 2 →
      (Pi.single (4 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) j = (Pi.single (2 : Fin 6) (1 : ℤ) : Fin 6 → ℤ) j := by
    decide
  refine ⟨2, fun j hj => key j hj, ?_⟩
  decide

omit [IsAlgClosed L] [Fact ℓ.Prime] [CharP L ℓ] in
theorem orbitRoot_pair :
    GenFixedRootDatum.orbitRoot ({Pi.single 2 1, Pi.single 4 1} : Set (Fin Tag.E6.rank → ℤ)) =
      Pi.single 4 1 := by
  have hmem := (tauDatum (AlgebraicClosure (ZMod 2)) 2 1 le_rfl).orbitRoot_mem
    (orbit24_mem (L := AlgebraicClosure (ZMod 2)) (ℓ := 2) (f := 1) le_rfl)
  rcases hmem with h | h
  · exfalso
    have hle := lexLeast_le (Set.toFinite ({Pi.single 2 1, Pi.single 4 1} :
      Set (Fin Tag.E6.rank → ℤ))) (Set.insert_nonempty _ _) (β := Pi.single 4 1)
      (Set.mem_insert_of_mem _ rfl)
    have h2 : lexLeast ({Pi.single 2 1, Pi.single 4 1} : Set (Fin Tag.E6.rank → ℤ)) =
        Pi.single 2 1 := h
    rw [h2] at hle
    exact absurd toLex_single_four_lt_two (not_lt.2 hle)
  · exact Set.mem_singleton_iff.1 h

theorem orbitVec_pair :
    (tauDatum L ℓ f hf).orbitVec ({Pi.single 2 1, Pi.single 4 1} :
        Set (Fin Tag.E6.rank → ℤ)) 0 = Pi.single 4 1 ∧
      (tauDatum L ℓ f hf).orbitVec ({Pi.single 2 1, Pi.single 4 1} :
        Set (Fin Tag.E6.rank → ℤ)) 1 = Pi.single 2 1 := by
  obtain ⟨-, hcase⟩ := pair_data hf rfl (orbit24_mem (L := L) (ℓ := ℓ) (f := f) hf)
  have h0 : (tauDatum L ℓ f hf).orbitVec ({Pi.single 2 1, Pi.single 4 1} :
        Set (Fin Tag.E6.rank → ℤ)) 0 = Pi.single 4 1 := by
    rw [(tauDatum L ℓ f hf).orbitVec_zero]
    exact orbitRoot_pair
  rcases hcase with ⟨hi, hi'⟩ | ⟨hi, hi'⟩
  · exact absurd (hi.symm.trans h0) (single_ne_single (by decide))
  · exact ⟨hi, hi'⟩

theorem orbitX_pair (a : (tauDatum L ℓ f hf).orbitField ({Pi.single 2 1, Pi.single 4 1} :
    Set (Fin Tag.E6.rank → ℤ))) :
    (tauDatum L ℓ f hf).orbitX ({Pi.single 2 1, Pi.single 4 1} :
        Set (Fin Tag.E6.rank → ℤ)) a =
      xUnit Tag.E6 L 4 (a : L) * xUnit Tag.E6 L 2 ((a : L) ^ ℓ ^ f) := by
  obtain ⟨hc, -⟩ := pair_data hf rfl (orbit24_mem (L := L) (ℓ := ℓ) (f := f) hf)
  obtain ⟨hv0, hv1⟩ := orbitVec_pair (L := L) (ℓ := ℓ) hf
  rw [GenFixedRootDatum.orbitX, GenFixedRootDatum.orbitMap_eq_prod, hc,
    show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_cons, List.prod_nil, mul_one,
    (tauDatum L ℓ f hf).orbitFactor_uSL, (tauDatum L ℓ f hf).orbitFactor_uSL, hv0, hv1,
    rootSL2_single', rootSL2_single', simpleRootSL2_uSL, simpleRootSL2_uSL, pow_zero, pow_one,
    pow_one]
  rfl

theorem orbitY_pair (a : (tauDatum L ℓ f hf).orbitField ({Pi.single 2 1, Pi.single 4 1} :
    Set (Fin Tag.E6.rank → ℤ))) :
    (tauDatum L ℓ f hf).orbitY ({Pi.single 2 1, Pi.single 4 1} :
        Set (Fin Tag.E6.rank → ℤ)) a =
      yUnit Tag.E6 L 4 (a : L) * yUnit Tag.E6 L 2 ((a : L) ^ ℓ ^ f) := by
  obtain ⟨hc, -⟩ := pair_data hf rfl (orbit24_mem (L := L) (ℓ := ℓ) (f := f) hf)
  obtain ⟨hv0, hv1⟩ := orbitVec_pair (L := L) (ℓ := ℓ) hf
  rw [GenFixedRootDatum.orbitY, GenFixedRootDatum.orbitMap_eq_prod, hc,
    show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_cons, List.prod_nil, mul_one,
    (tauDatum L ℓ f hf).orbitFactor_vSL, (tauDatum L ℓ f hf).orbitFactor_vSL, hv0, hv1,
    rootSL2_single', rootSL2_single', simpleRootSL2_vSL, simpleRootSL2_vSL, pow_zero, pow_one,
    pow_one]
  rfl

end Pair

section Comm

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
  (hf : 1 ≤ f)

theorem exists_finset_orbitField {O : Set (Fin Tag.E6.rank → ℤ)}
    (hO : O ∈ (tauDatum L ℓ f hf).orbits) :
    ∃ F : Finset L, F.card = (ℓ ^ f) ^ GenFixedRootDatum.orbitCard O ∧
      ∀ a, a ∈ F ↔ a ∈ (tauDatum L ℓ f hf).orbitField O :=
  (tauDatum L ℓ f hf).exists_finset_orbitField hO

theorem commute_of_three_le (hq : 3 ≤ ℓ ^ f) {X : Module.End L (RootModule Tag.E6 L)}
    (hX : X ∈ e6Commutant ((tauDatum L ℓ f hf).orbitGroup : Set (ModGL Tag.E6 L)))
    {j : Fin Tag.E6.rank} (hj : j ∈ d4Support) (c : L) :
    Commute X (xOp Tag.E6 L j c) ∧ Commute X (yOp Tag.E6 L j c) := by
  set D := tauDatum L ℓ f hf with hD
  have hXm : ∀ {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits) (a : D.orbitField O),
      Commute X ((D.orbitX O a : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L)) ∧
        Commute X ((D.orbitY O a : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L)) :=
    fun hO a => ⟨hX _ (orbitX_mem_orbitGroup D hO a), hX _ (orbitY_mem_orbitGroup D hO a)⟩
  have hsingle : ∀ {i : Fin Tag.E6.rank},
      ({Pi.single i 1} : Set (Fin Tag.E6.rank → ℤ)) ∈ D.orbits →
      Commute X (xOp Tag.E6 L i c) ∧ Commute X (yOp Tag.E6 L i c) := by
    intro i hO
    obtain ⟨F, hFc, hF⟩ := exists_finset_orbitField hf hO
    have h1 : GenFixedRootDatum.orbitCard ({Pi.single i 1} : Set (Fin Tag.E6.rank → ℤ)) = 1 :=
      Set.ncard_singleton _
    have hF3 : 3 ≤ F.card := by rw [hFc, h1, pow_one]; exact hq
    have hr := orbitRoot_single hf hO rfl
    refine ⟨commute_xOp_of_three_le_card hF3 (fun a ha => ?_) c,
      commute_yOp_of_three_le_card hF3 (fun a ha => ?_) c⟩
    · have := (hXm hO ⟨a, (hF a).1 ha⟩).1
      rwa [orbitX_eq_xUnit D h1 hr, coe_xUnit] at this
    · have := (hXm hO ⟨a, (hF a).1 ha⟩).2
      rwa [orbitY_eq_yUnit D h1 hr, coe_yUnit] at this
  have hpair : (Commute X (xOp Tag.E6 L 4 c) ∧ Commute X (yOp Tag.E6 L 4 c)) ∧
      (Commute X (xOp Tag.E6 L 2 c) ∧ Commute X (yOp Tag.E6 L 2 c)) := by
    have hO := orbit24_mem (L := L) (ℓ := ℓ) (f := f) hf
    obtain ⟨F, hFc, hF⟩ := exists_finset_orbitField hf hO
    obtain ⟨hc, -⟩ := pair_data hf rfl hO
    have hFc2 : F.card = (ℓ ^ f) ^ 2 := by rw [hFc, hc]
    obtain ⟨hA₁, hB₁, hA₂, hB₂⟩ := commute_of_pair_card hq hFc2 (X := X)
      (A₁ := xCoeff Tag.E6 L 4 1) (B₁ := xCoeff Tag.E6 L 4 2) (A₂ := xCoeff Tag.E6 L 2 1)
      (B₂ := xCoeff Tag.E6 L 2 2) fun a ha => by
        have := (hXm hO ⟨a, (hF a).1 ha⟩).1
        rwa [orbitX_pair (L := L) (ℓ := ℓ) hf, Units.val_mul, coe_xUnit, coe_xUnit, xOp_E6_eq, xOp_E6_eq] at this
    obtain ⟨hC₁, hD₁, hC₂, hD₂⟩ := commute_of_pair_card hq hFc2 (X := X)
      (A₁ := yCoeff Tag.E6 L 4 1) (B₁ := yCoeff Tag.E6 L 4 2) (A₂ := yCoeff Tag.E6 L 2 1)
      (B₂ := yCoeff Tag.E6 L 2 2) fun a ha => by
        have := (hXm hO ⟨a, (hF a).1 ha⟩).2
        rwa [orbitY_pair (L := L) (ℓ := ℓ) hf, Units.val_mul, coe_yUnit, coe_yUnit, yOp_E6_eq, yOp_E6_eq] at this
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [xOp_E6_eq]; exact commute_one_add_of_commute hA₁ hB₁ c
    · rw [yOp_E6_eq]; exact commute_one_add_of_commute hC₁ hD₁ c
    · rw [xOp_E6_eq]; exact commute_one_add_of_commute hA₂ hB₂ c
    · rw [yOp_E6_eq]; exact commute_one_add_of_commute hC₂ hD₂ c
  rcases d4Support_cases hj with rfl | rfl | rfl | rfl
  · exact hsingle (orbit1_mem hf)
  · exact hpair.2
  · exact hsingle (orbit3_mem hf)
  · exact hpair.1

end Comm

end CFSG.RankThree.PartOne.KD4L
