module

public import CFSG.RankThree.PartOne.KD4L.Layer
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4L

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

section Leaves

theorem leafCycle_E8 : ∀ a b c : Fin Tag.E8.rank, a.val = 1 ∨ a.val = 2 ∨ a.val = 4 →
    b.val = 1 ∨ b.val = 2 ∨ b.val = 4 → c.val = 1 ∨ c.val = 2 ∨ c.val = 4 →
    a ≠ b → b ≠ c → a ≠ c →
    ((∀ k : Fin Tag.D4.rank, List.formPerm [a, b, c] (d4Id k) = d4Id (rhoE 1 k)) ∨
      (∀ k : Fin Tag.D4.rank, List.formPerm [a, b, c] (d4Id k) = d4Id (rhoE 2 k))) ∧
    (∀ i : Fin Tag.E8.rank, (1 ≤ i.val ∧ i.val ≤ 4) →
      (1 ≤ (List.formPerm [a, b, c] i).val ∧ (List.formPerm [a, b, c] i).val ≤ 4)) ∧
    (∀ i : Fin Tag.E8.rank, (1 ≤ i.val ∧ i.val ≤ 4) →
      (1 ≤ ((List.formPerm [a, b, c]).symm i).val ∧ ((List.formPerm [a, b, c]).symm i).val ≤ 4)) := by
  decide +kernel

theorem leafCycle_E7 : ∀ a b c : Fin Tag.E7.rank, a.val = 1 ∨ a.val = 2 ∨ a.val = 4 →
    b.val = 1 ∨ b.val = 2 ∨ b.val = 4 → c.val = 1 ∨ c.val = 2 ∨ c.val = 4 →
    a ≠ b → b ≠ c → a ≠ c →
    ((∀ k : Fin Tag.D4.rank, List.formPerm [a, b, c] (d4Id k) = d4Id (rhoE 1 k)) ∨
      (∀ k : Fin Tag.D4.rank, List.formPerm [a, b, c] (d4Id k) = d4Id (rhoE 2 k))) ∧
    (∀ i : Fin Tag.E7.rank, (1 ≤ i.val ∧ i.val ≤ 4) →
      (1 ≤ (List.formPerm [a, b, c] i).val ∧ (List.formPerm [a, b, c] i).val ≤ 4)) ∧
    (∀ i : Fin Tag.E7.rank, (1 ≤ i.val ∧ i.val ≤ 4) →
      (1 ≤ ((List.formPerm [a, b, c]).symm i).val ∧ ((List.formPerm [a, b, c]).symm i).val ≤ 4)) := by
  decide +kernel

end Leaves


section Generic

variable {τ : Tag} [hτ : E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem triality_layer_generic (hf : 1 ≤ f) (π : Equiv.Perm (Fin τ.rank)) (e : ℕ)
    (he : e = 1 ∨ e = 2) (hπe : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (rhoE e k))
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice π α)
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (d4Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    Finite P ∧ CFSG.IsQuasisimple P ∧
      (∀ y ∈ torusGroup τ L ⊔ rootSpan τ L (parabolicRoots τ (d4Nodes τ)),
        (∀ u ∈ P, y * u = u * y) →
        y ∈ torusGroup τ L ∧
          y ∈ Subgroup.centralizer (rootSpan τ L (parabolicRoots τ (d4Nodes τ)) : Set (ModGL τ L))) ∧
      ∀ (m : Fin τ.rank), m.val = 3 → ∀ (k : Type) [Field k] [Algebra k L] [IsAlgClosure k L],
        Nat.card k = ℓ ^ f → ∃ h₀ : ModGL τ L, ∀ Y : SL(2, k),
          h₀ * simpleRootSL2 τ L m (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P := by
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdTwist n₁ π e := ⟨he, hπe, hπ, hπ', hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  have hd4 : d4Nodes τ = d4Set τ := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  obtain ⟨h1, h2, h3, h4⟩ := layer_of_standard hf hstd hh hlang hP
  exact ⟨h1, h2, h3, fun m hm k _ _ _ hk => h4 m hm k hk⟩

end Generic

section OfLeafCycle

variable {τ : Tag} [E6Sub τ]

theorem d4TrialityLayer_of_leafCycle
    (hleaf : ∀ a b c : Fin τ.rank, a.val = 1 ∨ a.val = 2 ∨ a.val = 4 →
      b.val = 1 ∨ b.val = 2 ∨ b.val = 4 → c.val = 1 ∨ c.val = 2 ∨ c.val = 4 →
      a ≠ b → b ≠ c → a ≠ c →
      ((∀ k : Fin Tag.D4.rank, List.formPerm [a, b, c] (d4Id k) = d4Id (rhoE 1 k)) ∨
        (∀ k : Fin Tag.D4.rank, List.formPerm [a, b, c] (d4Id k) = d4Id (rhoE 2 k))) ∧
      (∀ i : Fin τ.rank, (1 ≤ i.val ∧ i.val ≤ 4) →
        (1 ≤ (List.formPerm [a, b, c] i).val ∧ (List.formPerm [a, b, c] i).val ≤ 4)) ∧
      (∀ i : Fin τ.rank, (1 ≤ i.val ∧ i.val ≤ 4) →
        (1 ≤ ((List.formPerm [a, b, c]).symm i).val ∧
          ((List.formPerm [a, b, c]).symm i).val ≤ 4))) :
    D4TrialityLayer τ := by
  intro L _ _ ℓ f _ _ hf a b c hab hbc hac ha hb hc n hn _ hact P hP
  have ha' : a.val = 1 ∨ a.val = 2 ∨ a.val = 4 := by simpa using ha
  have hb' : b.val = 1 ∨ b.val = 2 ∨ b.val = 4 := by simpa using hb
  have hc' : c.val = 1 ∨ c.val = 2 ∨ c.val = 4 := by simpa using hc
  obtain ⟨hcyc, hπ, hπ'⟩ := hleaf a b c ha' hb' hc' hab hbc hac
  rcases hcyc with h1 | h2
  · exact triality_layer_generic hf (List.formPerm [a, b, c]) 1 (Or.inl rfl) h1
      (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn hact P hP
  · exact triality_layer_generic hf (List.formPerm [a, b, c]) 2 (Or.inr rfl) h2
      (fun i hi => hπ i hi) (fun i hi => hπ' i hi) n hn hact P hP

end OfLeafCycle

section Final

theorem d4TrialityLayer_E8 : D4TrialityLayer .E8 := by
  exact d4TrialityLayer_of_leafCycle leafCycle_E8

theorem d4TrialityLayer_E7 : D4TrialityLayer .E7 := by
  exact d4TrialityLayer_of_leafCycle leafCycle_E7

end Final

end CFSG.RankThree.PartOne.KD4L
