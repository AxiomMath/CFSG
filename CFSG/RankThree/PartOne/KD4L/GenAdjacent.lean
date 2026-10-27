module

public import CFSG.RankThree.Lattice.SteinbergBIGenOrbitMaps

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4L

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Adjacent

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀]
  [IsAlgClosed k] {M : Type} [CommGroup M] (D : GenFixedRootDatum τ p₀ k M)

omit [IsAlgClosed k] in
theorem rootSL2_single' (j : Fin τ.rank) (A : SL2 k) :
    rootSL2 τ k (Pi.single j 1) A = simpleRootSL2 τ k j A := by
  rw [rootSL2_apply, pinnedData_single]
  simp [pinnedWeyl, pinnedData_single]

theorem orbitX_eq_xUnit {O : Set (Fin τ.rank → ℤ)} (h1 : GenFixedRootDatum.orbitCard O = 1)
    {i : Fin τ.rank} (hi : GenFixedRootDatum.orbitRoot O = Pi.single i 1) (c : D.orbitField O) :
    D.orbitX O c = xUnit τ k i (c : k) := by
  rw [GenFixedRootDatum.orbitX, GenFixedRootDatum.orbitMap_eq_prod, h1,
    show List.range 1 = [0] from rfl, List.map_singleton, List.prod_singleton, D.orbitFactor_uSL,
    pow_zero, pow_one, D.orbitVec_zero, hi, rootSL2_single', simpleRootSL2_uSL]

theorem orbitY_eq_yUnit {O : Set (Fin τ.rank → ℤ)} (h1 : GenFixedRootDatum.orbitCard O = 1)
    {i : Fin τ.rank} (hi : GenFixedRootDatum.orbitRoot O = Pi.single i 1) (c : D.orbitField O) :
    D.orbitY O c = yUnit τ k i (c : k) := by
  rw [GenFixedRootDatum.orbitY, GenFixedRootDatum.orbitMap_eq_prod, h1,
    show List.range 1 = [0] from rfl, List.map_singleton, List.prod_singleton, D.orbitFactor_vSL,
    pow_zero, pow_one, D.orbitVec_zero, hi, rootSL2_single', simpleRootSL2_vSL]

theorem orbitX_mem_orbitGroup {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (c : D.orbitField O) :
    D.orbitX O c ∈ D.orbitGroup :=
  Subgroup.subset_closure ⟨O, hO, c, Or.inl rfl⟩

theorem orbitY_mem_orbitGroup {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (c : D.orbitField O) :
    D.orbitY O c ∈ D.orbitGroup :=
  Subgroup.subset_closure ⟨O, hO, c, Or.inr rfl⟩

theorem eq_commutatorElement_conj {G : Type*} [Group G] {a x y n : G}
    (h : ⁅a, x⁆ = n * y * n⁻¹) : y = ⁅n⁻¹ * a * n, n⁻¹ * x * n⁆ := by
  have h' : y = n⁻¹ * ⁅a, x⁆ * n := by rw [h]; group
  calc y = n⁻¹ * ⁅a, x⁆ * n := h'
    _ = ⁅n⁻¹ * a * n, n⁻¹ * x * n⁆ := by simp only [commutatorElement_def]; group

theorem orbitXY_mem_commutator_of_adjacent {O P : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (hP : P ∈ D.orbits) (h1O : GenFixedRootDatum.orbitCard O = 1)
    (h1P : GenFixedRootDatum.orbitCard P = 1) {i j : Fin τ.rank}
    (hOi : GenFixedRootDatum.orbitRoot O = Pi.single i 1)
    (hPj : GenFixedRootDatum.orbitRoot P = Pi.single j 1)
    (hij : τ.cartan i j = -1) (hji : τ.cartan j i = -1) (a : D.orbitField P) :
    D.orbitX P a ∈ ⁅D.orbitGroup, D.orbitGroup⁆ ∧ D.orbitY P a ∈ ⁅D.orbitGroup, D.orbitGroup⁆ := by
  have hn : (weylElt τ k i 1 : ModGL τ k) ∈ D.orbitGroup := by
    have e : (weylElt τ k i 1 : ModGL τ k) = D.orbitX O 1 * D.orbitY O (-1) * D.orbitX O 1 := by
      rw [weylElt_eq_xUnit_mul, orbitX_eq_xUnit D h1O hOi, orbitY_eq_yUnit D h1O hOi]
      simp
    rw [e]
    exact mul_mem (mul_mem (orbitX_mem_orbitGroup D hO _) (orbitY_mem_orbitGroup D hO _))
      (orbitX_mem_orbitGroup D hO _)
  have hxi : (xUnit τ k i 1 : ModGL τ k) ∈ D.orbitGroup := by
    have := orbitX_mem_orbitGroup D hO 1
    rwa [orbitX_eq_xUnit D h1O hOi] at this
  have hyi : (yUnit τ k i 1 : ModGL τ k) ∈ D.orbitGroup := by
    have := orbitY_mem_orbitGroup D hO 1
    rwa [orbitY_eq_yUnit D h1O hOi] at this
  have hxa : (xUnit τ k j (a : k) : ModGL τ k) ∈ D.orbitGroup := by
    have := orbitX_mem_orbitGroup D hP a
    rwa [orbitX_eq_xUnit D h1P hPj] at this
  have hya : (yUnit τ k j (-(a : k)) : ModGL τ k) ∈ D.orbitGroup := by
    have := orbitY_mem_orbitGroup D hP (-a)
    rwa [orbitY_eq_yUnit D h1P hPj, Subfield.coe_neg] at this
  have hn' : (weylElt τ k i 1 : ModGL τ k)⁻¹ ∈ D.orbitGroup := inv_mem hn
  obtain ⟨hcx, -⟩ := a2_simple_root_commutatorElement k hij hji (1 : k) (a : k)
  obtain ⟨-, hcy'⟩ := a2_simple_root_commutatorElement k hij hji (1 : k) (-(a : k))
  rw [one_mul] at hcx
  rw [one_mul, neg_neg] at hcy'
  constructor
  · rw [orbitX_eq_xUnit D h1P hPj]
    rw [eq_commutatorElement_conj hcx]
    exact Subgroup.commutator_mem_commutator (mul_mem (mul_mem hn' hxi) hn)
      (mul_mem (mul_mem hn' hxa) hn)
  · rw [orbitY_eq_yUnit D h1P hPj]
    rw [eq_commutatorElement_conj hcy']
    exact Subgroup.commutator_mem_commutator (mul_mem (mul_mem hn' hyi) hn)
      (mul_mem (mul_mem hn' hya) hn)

theorem torusElt_mem_orbitGroup_of_single {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (h1 : GenFixedRootDatum.orbitCard O = 1) {i : Fin τ.rank}
    (hi : GenFixedRootDatum.orbitRoot O = Pi.single i 1) (s : kˣ) (hs : (s : k) ^ D.q = s) :
    torusElt τ k i s ∈ D.orbitGroup := by
  have hmem : (s : k) ∈ D.orbitField O := D.mem_orbitField.2 (by rw [h1, pow_one]; exact hs)
  have hne : (⟨(s : k), hmem⟩ : D.orbitField O) ≠ 0 := fun h => s.ne_zero (congrArg Subtype.val h)
  let u : (D.orbitField O)ˣ := Units.mk0 ⟨(s : k), hmem⟩ hne
  have hu : D.orbitMap O (HSL u) = torusElt τ k i s := by
    rw [GenFixedRootDatum.orbitMap_eq_prod, h1, show List.range 1 = [0] from rfl,
      List.map_singleton, List.prod_singleton, GenFixedRootDatum.orbitFactor_apply,
      D.orbitVec_zero, hi, rootSL2_single', map_HSL, map_HSL, simpleRootSL2_HSL]
    congr 1
    refine Units.ext ?_
    simp [u]
  rw [← hu]
  exact D.orbitMap_mem_orbitGroup hO _

theorem torusElt_pair_mem_orbitGroup {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (h2 : GenFixedRootDatum.orbitCard O = 2) {i i' : Fin τ.rank}
    (hi : D.orbitVec O 0 = Pi.single i 1) (hi' : D.orbitVec O 1 = Pi.single i' 1) (s : kˣ)
    (hs : (s : k) ^ D.q ^ 2 = s) :
    torusElt τ k i s * torusElt τ k i' (s ^ D.q) ∈ D.orbitGroup := by
  have hmem : (s : k) ∈ D.orbitField O := D.mem_orbitField.2 (by rw [h2]; exact hs)
  have hne : (⟨(s : k), hmem⟩ : D.orbitField O) ≠ 0 := fun h => s.ne_zero (congrArg Subtype.val h)
  let u : (D.orbitField O)ˣ := Units.mk0 ⟨(s : k), hmem⟩ hne
  have hu : D.orbitMap O (HSL u) = torusElt τ k i s * torusElt τ k i' (s ^ D.q) := by
    rw [GenFixedRootDatum.orbitMap_eq_prod, h2, show List.range 2 = [0, 1] from rfl,
      List.map_cons, List.map_cons, List.map_nil, List.prod_cons, List.prod_cons, List.prod_nil,
      mul_one, GenFixedRootDatum.orbitFactor_apply, GenFixedRootDatum.orbitFactor_apply, hi, hi',
      rootSL2_single', rootSL2_single']
    simp only [map_HSL, simpleRootSL2_HSL]
    congr 2
    · refine Units.ext ?_
      simp [u]
    · refine Units.ext ?_
      simp [u, GenFixedRootDatum.q]
  rw [← hu]
  exact D.orbitMap_mem_orbitGroup hO _

end Adjacent

end CFSG.RankThree.PartOne.KD4L
