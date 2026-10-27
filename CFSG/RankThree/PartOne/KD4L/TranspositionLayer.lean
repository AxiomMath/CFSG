module

public import CFSG.RankThree.PartOne.KD4L.TauStd
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4L

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KE CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups

section Leaves

theorem leafSwap_E8 : ∀ i j : Fin Tag.E8.rank, (i.val = 1 ∨ i.val = 2 ∨ i.val = 4) →
    (j.val = 1 ∨ j.val = 2 ∨ j.val = 4) → i ≠ j →
    ((∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 1 3 k)) ∨
      (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 3 k)) ∨
      (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 1 k))) ∧
    (∀ x : Fin Tag.E8.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
      (1 ≤ (Equiv.swap i j x).val ∧ (Equiv.swap i j x).val ≤ 4)) ∧
    (∀ x : Fin Tag.E8.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
      (1 ≤ ((Equiv.swap i j).symm x).val ∧ ((Equiv.swap i j).symm x).val ≤ 4)) := by
  decide +kernel

theorem leafSwap_E7 : ∀ i j : Fin Tag.E7.rank, (i.val = 1 ∨ i.val = 2 ∨ i.val = 4) →
    (j.val = 1 ∨ j.val = 2 ∨ j.val = 4) → i ≠ j →
    ((∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 1 3 k)) ∨
      (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 3 k)) ∨
      (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 1 k))) ∧
    (∀ x : Fin Tag.E7.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
      (1 ≤ (Equiv.swap i j x).val ∧ (Equiv.swap i j x).val ≤ 4)) ∧
    (∀ x : Fin Tag.E7.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
      (1 ≤ ((Equiv.swap i j).symm x).val ∧ ((Equiv.swap i j).symm x).val ≤ 4)) := by
  decide +kernel

theorem rho_conj_swap : rhoPerm * Equiv.swap 1 3 * rhoPerm⁻¹ = Equiv.swap 0 3 := by
  ext k
  revert k
  decide

theorem rho_sq_conj_swap :
    rhoPerm * rhoPerm * Equiv.swap 1 3 * (rhoPerm * rhoPerm)⁻¹ = Equiv.swap 0 1 := by
  ext k
  revert k
  decide

end Leaves

section E6Cases

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}

omit [IsAlgClosed L] in
theorem frob_d4TrialityRep :
    Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (d4TrialityRep L) = d4TrialityRep L := by
  rw [← baseChangeGL_eq_entrywise]
  exact baseChangeGL_wordRep (iterateFrobenius L ℓ f) d4TrialityWord

omit [IsAlgClosed L] in
theorem map_conj_mul {R S : ModGL Tag.E6 L}
    (hR : (subsystemGroup Tag.E6 L d4Support).map (MulAut.conj R).toMonoidHom =
      subsystemGroup Tag.E6 L d4Support)
    (hS : (subsystemGroup Tag.E6 L d4Support).map (MulAut.conj S).toMonoidHom =
      subsystemGroup Tag.E6 L d4Support) :
    (subsystemGroup Tag.E6 L d4Support).map (MulAut.conj (R * S)).toMonoidHom =
      subsystemGroup Tag.E6 L d4Support := by
  have h : (MulAut.conj (R * S)).toMonoidHom =
      (MulAut.conj R).toMonoidHom.comp (MulAut.conj S).toMonoidHom := by
    ext g
    simp [MulAut.conj_apply, mul_assoc]
  rw [h, ← Subgroup.map_map, hS, hR]

variable (hf : 1 ≤ f)

include hf in
theorem exists_fix_swap13 : ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 1 3) ∧
    E6Fix (ℓ := ℓ) f n₂ :=
  ⟨dN L, acts_dN, E6Fix_dN hf⟩

include hf in
theorem exists_fix_swap03 : ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 3) ∧
    E6Fix (ℓ := ℓ) f n₂ := by
  refine ⟨d4TrialityRep L * dN L * (d4TrialityRep L)⁻¹, ?_, ?_⟩
  · have h := Acts.conj (acts_d4TrialityRep (L := L)) (acts_dN (L := L))
    rwa [rho_conj_swap] at h
  · exact E6Fix.conj map_conj_d4TrialityRep frob_d4TrialityRep (E6Fix_dN hf)

include hf in
theorem exists_fix_swap01 : ∃ n₂ : ModGL Tag.E6 L, Acts n₂ (Equiv.swap 0 1) ∧
    E6Fix (ℓ := ℓ) f n₂ := by
  refine ⟨(d4TrialityRep L * d4TrialityRep L) * dN L *
    (d4TrialityRep L * d4TrialityRep L)⁻¹, ?_, ?_⟩
  · have h := Acts.conj ((acts_d4TrialityRep (L := L)).mul (acts_d4TrialityRep (L := L)))
      (acts_dN (L := L))
    rwa [rho_sq_conj_swap] at h
  · refine E6Fix.conj (map_conj_mul map_conj_d4TrialityRep map_conj_d4TrialityRep) ?_
      (E6Fix_dN hf)
    rw [map_mul, frob_d4TrialityRep]

end E6Cases

section Generic

variable {τ : Tag} [hτ : E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem transposition_layer_generic (hf : 1 ≤ f) (σ : Equiv.Perm (Fin Tag.D4.rank))
    (hσ2 : σ 2 = 2) (hE : ∃ n₂ : ModGL Tag.E6 L, Acts n₂ σ ∧ E6Fix (ℓ := ℓ) f n₂)
    (π : Equiv.Perm (Fin τ.rank)) (hπσ : ∀ k : Fin Tag.D4.rank, π (d4Id k) = d4Id (σ k))
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
  obtain ⟨n₂, h₂, hfix⟩ := hE
  obtain ⟨u, hu, hu'⟩ := hact
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := fun j hj => by
    have := hu' _ (single_mem_parabolicRoots hj)
    rwa [permLattice_single] at this
  obtain ⟨n₁, h, hn₁, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn hπ hπ' hu hact'
  have hstd : StdSwap n₁ π σ := ⟨hπ, hπ', hπσ, hgen⟩
  rw [← subsystemGroup_eq_rootSpan] at hP
  have hd4 : d4Nodes τ = d4Set τ := rfl
  rw [hd4, ← subsystemGroup_eq_rootSpan]
  obtain ⟨h1, h2, h3, h4⟩ := layer_of_swap hstd h₂ hσ2 hfix hh hlang hP
  exact ⟨h1, h2, h3, fun m hm k _ _ _ hk => h4 m hm k hk⟩

theorem transposition_layer_of_leafSwap
    (hleaf : ∀ i j : Fin τ.rank, (i.val = 1 ∨ i.val = 2 ∨ i.val = 4) →
      (j.val = 1 ∨ j.val = 2 ∨ j.val = 4) → i ≠ j →
      ((∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 1 3 k)) ∨
        (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 3 k)) ∨
        (∀ k : Fin Tag.D4.rank, Equiv.swap i j (d4Id k) = d4Id (Equiv.swap 0 1 k))) ∧
      (∀ x : Fin τ.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
        (1 ≤ (Equiv.swap i j x).val ∧ (Equiv.swap i j x).val ≤ 4)) ∧
      (∀ x : Fin τ.rank, (1 ≤ x.val ∧ x.val ≤ 4) →
        (1 ≤ ((Equiv.swap i j).symm x).val ∧ ((Equiv.swap i j).symm x).val ≤ 4)))
    (hf : 1 ≤ f) {i j : Fin τ.rank} (hij : i ≠ j) (hi : i.val ∈ ({1, 2, 4} : Set ℕ))
    (hj : j.val ∈ ({1, 2, 4} : Set ℕ)) (n : ModGL τ L) (hn : n ∈ monomialSubgroup τ L)
    (hact : ∃ u ∈ parabolicWeylGroup τ (d4Nodes τ), ∀ α ∈ parabolicRoots τ (d4Nodes τ),
      weylQuotientHom τ L ⟨n, hn⟩ • α = u • permLattice (Equiv.swap i j) α)
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
  have hi' : i.val = 1 ∨ i.val = 2 ∨ i.val = 4 := by simpa using hi
  have hj' : j.val = 1 ∨ j.val = 2 ∨ j.val = 4 := by simpa using hj
  obtain ⟨hcases, hπ, hπ'⟩ := hleaf i j hi' hj' hij
  rcases hcases with h1 | h2 | h3
  · exact transposition_layer_generic hf (Equiv.swap 1 3) (by decide)
      (exists_fix_swap13 (L := L) (ℓ := ℓ) hf) (Equiv.swap i j) h1 (fun x hx => hπ x hx)
      (fun x hx => hπ' x hx) n hn hact P hP
  · exact transposition_layer_generic hf (Equiv.swap 0 3) (by decide)
      (exists_fix_swap03 (L := L) (ℓ := ℓ) hf) (Equiv.swap i j) h2 (fun x hx => hπ x hx)
      (fun x hx => hπ' x hx) n hn hact P hP
  · exact transposition_layer_generic hf (Equiv.swap 0 1) (by decide)
      (exists_fix_swap01 (L := L) (ℓ := ℓ) hf) (Equiv.swap i j) h3 (fun x hx => hπ x hx)
      (fun x hx => hπ' x hx) n hn hact P hP

end Generic

section Final

theorem d4TranspositionLayer_E8 : D4TranspositionLayer .E8 := by
  intro L _ _ ℓ f _ _ hf _ i j hij hi hj n hn _ hact P hP
  exact transposition_layer_of_leafSwap leafSwap_E8 hf hij hi hj n hn hact P hP

theorem d4TranspositionLayer_E7 : D4TranspositionLayer .E7 := by
  intro L _ _ ℓ f _ _ hf _ i j hij hi hj n hn _ hact P hP
  exact transposition_layer_of_leafSwap leafSwap_E7 hf hij hi hj n hn hact P hP

end Final

end CFSG.RankThree.PartOne.KD4L
