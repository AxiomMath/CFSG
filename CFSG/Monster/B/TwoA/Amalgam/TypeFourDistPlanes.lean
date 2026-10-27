module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Monster.B.TwoA.Amalgam.Flag1Action
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Planes

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Fischer CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Unitary

theorem ncard_mul_eq_ncard_mul_of_rel {α β : Type*} [Finite α] [Finite β] (r : α → β → Prop)
    {S : Set α} {T : Set β} {m n : ℕ}
    (hm : ∀ a ∈ S, {b | b ∈ T ∧ r a b}.ncard = m)
    (hn : ∀ b ∈ T, {a | a ∈ S ∧ r a b}.ncard = n) :
    S.ncard * m = T.ncard * n := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  rw [Set.ncard_eq_toFinset_card' S, Set.ncard_eq_toFinset_card' T]
  refine Finset.card_mul_eq_card_mul r (fun a ha => ?_) (fun b hb => ?_)
  · rw [← hm a (Set.mem_toFinset.1 ha), Set.ncard_eq_toFinset_card']
    congr 1
    ext b
    simp only [Finset.mem_bipartiteAbove, Set.mem_toFinset, Set.mem_ofPred_eq]
  · rw [← hn b (Set.mem_toFinset.1 hb), Set.ncard_eq_toFinset_card']
    congr 1
    ext a
    simp only [Finset.mem_bipartiteBelow, Set.mem_toFinset, Set.mem_ofPred_eq]

theorem sigmaAct_injective (x : SigmaU6) :
    Function.Injective fun S : Submodule F4 V6 => sigmaAct S x := fun S S' h => by
  have h' := congrArg (fun P => sigmaAct P x⁻¹) h
  simp only [sigmaAct_sigmaAct_inv] at h'
  exact h'

theorem sigmaAct_mem_orbitA
    {P : Submodule F4 V6} {a : Usig} (ha : a ∈ Atau) :
    sigmaAct P (phiU a) ∈ orbitA P :=
  ⟨a, ha, rfl⟩

theorem finite_submodule : Finite (Submodule F4 V6) :=
  Finite.of_injective (fun S : Submodule F4 V6 => (S : Set V6)) SetLike.coe_injective

theorem ncard_planes_through_le
    {R R' : Submodule F4 V6} (hR : R ∈ ptOrbit 1)
    (hR' : R' ∈ ptOrbit 1) :
    {T | T ∈ plOrbit 0 ∧ R ≤ T}.ncard ≤ {T | T ∈ plOrbit 0 ∧ R' ≤ T}.ncard := by
  have := finite_submodule
  obtain ⟨-, -, hpt, -, -, -, -, hpl, -⟩ := native_unitary_1408_stabilizer_point_plane_orbits
  have hR'' : R' ∈ orbitA R := by
    rw [hpt 1 (by norm_num) R hR]
    exact hR'
  obtain ⟨a, ha, rfl⟩ := hR''
  refine Set.ncard_le_ncard_of_injOn (fun T => sigmaAct T (phiU a)) ?_
    ((sigmaAct_injective (phiU a)).injOn) (Set.toFinite _)
  rintro T ⟨hT, hRT⟩
  refine ⟨?_, sigmaAct_mono hRT _⟩
  have h := sigmaAct_mem_orbitA (P := T) ha
  rwa [hpl 0 (by norm_num) T hT] at h

theorem ncard_planes_through_eq
    {R R' : Submodule F4 V6} (hR : R ∈ ptOrbit 1)
    (hR' : R' ∈ ptOrbit 1) :
    {T | T ∈ plOrbit 0 ∧ R ≤ T}.ncard = {T | T ∈ plOrbit 0 ∧ R' ≤ T}.ncard :=
  le_antisymm (ncard_planes_through_le hR hR') (ncard_planes_through_le hR' hR)

theorem ncard_planes_through
    {R : Submodule F4 V6} (hR : R ∈ ptOrbit 1) :
    {T | T ∈ plOrbit 0 ∧ R ≤ T}.ncard = 12 := by
  have := finite_submodule
  obtain ⟨-, -, -, -, -, -, hpt1, -, -, -, hpl0, -, hinc, -⟩ :=
    native_unitary_1408_stabilizer_point_plane_orbits
  have h := ncard_mul_eq_ncard_mul_of_rel (fun (R' : Submodule F4 V6) T => R' ≤ T)
    (S := ptOrbit 1) (T := plOrbit 0) (m := {T | T ∈ plOrbit 0 ∧ R ≤ T}.ncard) (n := 21)
    (fun R' hR' => ncard_planes_through_eq hR' hR) (fun T hT => (hinc T hT).2)
  rw [hpt1, hpl0] at h
  omega

theorem not_le_of_mem_ptOrbit_zero
    {T R : Submodule F4 V6} (hT : T ∈ plOrbit 0)
    (hR : R ∈ ptOrbit 0) : ¬ R ≤ T := by
  have := finite_submodule
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hinc, -⟩ :=
    native_unitary_1408_stabilizer_point_plane_orbits
  intro hRT
  have h := (hinc T hT).1
  rw [Set.ncard_eq_zero (Set.toFinite _)] at h
  have hmem : R ∈ {Q | Q ∈ ptOrbit 0 ∧ Q ≤ T} := ⟨hR, hRT⟩
  rw [h] at hmem
  exact hmem

end CFSG.Monster.B.TwoA.Amalgam
