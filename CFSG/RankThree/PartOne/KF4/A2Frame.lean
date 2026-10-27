module

public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.ConjRootSpan

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

variable {τ : Tag} {L : Type} [Field L]

structure IsA2Frame (ρ : SL(3, L) →* ModGL τ L) (σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ) : Prop where
  injective : Function.Injective ρ
  isRoot : ∀ i j, i ≠ j → IsRoot τ (σ i j)
  neg : ∀ i j, σ j i = -σ i j
  add : ∀ i j k, σ i j + σ j k = σ i k
  transv : ∀ (i j : Fin 3) (hij : i ≠ j), ∃ ε : Lˣ, ∀ t : L,
    ρ (Matrix.SpecialLinearGroup.transvection hij t) = pinnedX τ L (σ i j) ((ε : L) * t)
  range : ρ.range = rootSpan τ L {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j}
  diag : ∀ A : SL(3, L), (∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) →
    ρ A ∈ torusGroup τ L


section Transport

variable
  {τ : Tag} {L : Type} [Field L]

namespace IsA2Frame

variable {ρ : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}

theorem eq_sub (h : IsA2Frame ρ σ) (i j : Fin 3) : σ i j = σ i 0 - σ j 0 := by
  have h1 := h.add i 0 j
  rw [h.neg j 0] at h1
  rw [← h1]
  abel

theorem torus (h : IsA2Frame ρ σ) (b : Fin τ.rank → Lˣ) (A : SL(3, L)) :
    rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ =
      ρ (conjDiag3 (fun i => rootChar b (σ i 0)) A) := by
  set d : Fin 3 → Lˣ := fun i => rootChar b (σ i 0) with hd
  have hh : (MulAut.conj (rootDiagUnit τ b)).toMonoidHom.comp ρ =
      ρ.comp (conjDiag3Hom d) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := L)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    obtain ⟨ε, hε⟩ := h.transv i j hij
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      conjDiag3Hom_apply]
    rw [hε, conjDiag3_transvection (L := L), hε,
      rootDiagUnit_conj_pinnedX b (h.isRoot i j hij)]
    congr 1
    rw [h.eq_sub i j, rootChar_sub]
    simp only [hd, Units.val_mul, Units.val_inv_eq_inv_val]
    ring
  exact DFunLike.congr_fun hh A

theorem transport (h : IsA2Frame ρ σ) (v : WeylGroup τ) :
    IsA2Frame ((MulAut.conj (canonicalRep (coxeterSystem τ) L v)).toMonoidHom.comp ρ)
      (fun i j => v • σ i j) where
  injective := (MulAut.conj (canonicalRep (coxeterSystem τ) L v)).injective.comp h.injective
  isRoot i j hij := IsRoot.smul (h.isRoot i j hij) v
  neg i j := by rw [h.neg i j, smul_neg]
  add i j k := by rw [← smul_add, h.add]
  transv i j hij := by
    obtain ⟨ε₀, h₀⟩ := h.transv i j hij
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX (canonicalRep_mem_monomialSubgroup L v)
      (h.isRoot i j hij)
    have hπ : weylQuotientHom τ L ⟨canonicalRep (coxeterSystem τ) L v,
        canonicalRep_mem_monomialSubgroup L v⟩ = v :=
      weylQuotientHom_eq (mapsRootLines_canonicalRep v)
    refine ⟨μ * ε₀, fun t => ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [h₀, hμ, hπ, Units.val_mul, mul_assoc]
  range := by
    rw [MonoidHom.range_comp, h.range, map_conj_rootSpan v (by
      rintro γ ⟨i, j, hij, rfl⟩
      exact h.isRoot i j hij)]
    congr 1
    ext r
    constructor
    · rintro ⟨γ, ⟨i, j, hij, rfl⟩, rfl⟩
      exact ⟨i, j, hij, rfl⟩
    · rintro ⟨i, j, hij, rfl⟩
      exact ⟨σ i j, ⟨i, j, hij, rfl⟩, rfl⟩
  diag A hA := by
    have hH := h.diag A hA
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer v) _).1 hH

theorem family_split [IsAlgClosed L] (h : IsA2Frame ρ σ) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (n : ModGL τ L)
    (hnm : n ∈ monomialSubgroup τ L) (π : Equiv.Perm (Fin 3))
    (hπ : ∀ i j : Fin 3, i ≠ j → weylQuotientHom τ L ⟨n, hnm⟩ • σ i j = σ (π i) (π j)) :
    ∃ P : Unit → Subgroup (ModGL τ L),
      IsSigmaFamily n Fr {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j} P := by
  classical
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from
      pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  choose! ε hε using fun (i j : Fin 3) (hij : i ≠ j) => h.transv i j hij
  have hconj : ∀ i j : Fin 3, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      n * pinnedX τ L (σ i j) c * n⁻¹ = pinnedX τ L (σ (π i) (π j)) ((b : L) * c) := by
    intro i j hij
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm (h.isRoot i j hij)
    exact ⟨μ, fun c => by rw [hμ c, hπ i j hij]⟩
  have htne : ∀ i j : Fin 3, i ≠ j →
      ((fun i j => (π i, π j) : Fin 3 → Fin 3 → Fin 3 × Fin 3) i j).1 ≠
        ((fun i j => (π i, π j) : Fin 3 → Fin 3 → Fin 3 × Fin 3) i j).2 :=
    fun i j hij => π.injective.ne hij
  have htsurj : ∀ i j : Fin 3, i ≠ j → ∃ i' j' : Fin 3, i' ≠ j' ∧
      (fun i j => (π i, π j) : Fin 3 → Fin 3 → Fin 3 × Fin 3) i' j' = (i, j) :=
    fun i j hij => ⟨π.symm i, π.symm j, π.symm.injective.ne hij, by simp⟩
  obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData ρ h.injective σ ε hε Fr hFrbij n
    (fun i j => (π i, π j)) htne htsurj hconj
  have hS3 : ∀ r ∈ {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j}, IsRoot τ r :=
    fun r ⟨i, j, hij, hr⟩ => hr ▸ h.isRoot i j hij
  exact a2_family_split hℓ hf hk hS3 ρ h.injective
    h.range (fun b => ⟨fun i => rootChar b (σ i 0), fun A => h.torus b A⟩) h.diag Fr n Φ' hΦ' π b
    (fun i j hij t => by rw [hshape i j hij t, hFr])

theorem family_unitary [IsAlgClosed L] (h : IsA2Frame ρ σ) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f)
    (hq2 : 2 < ℓ ^ f) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (n : ModGL τ L)
    (hnm : n ∈ monomialSubgroup τ L) (π : Equiv.Perm (Fin 3))
    (hπ : ∀ i j : Fin 3, i ≠ j → weylQuotientHom τ L ⟨n, hnm⟩ • σ i j = σ (π j) (π i)) :
    ∃ P : Unit → Subgroup (ModGL τ L),
      IsSigmaFamily n Fr {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j} P := by
  classical
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from
      pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  choose! ε hε using fun (i j : Fin 3) (hij : i ≠ j) => h.transv i j hij
  have hconj : ∀ i j : Fin 3, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      n * pinnedX τ L (σ i j) c * n⁻¹ = pinnedX τ L (σ (π j) (π i)) ((b : L) * c) := by
    intro i j hij
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm (h.isRoot i j hij)
    exact ⟨μ, fun c => by rw [hμ c, hπ i j hij]⟩
  have htne : ∀ i j : Fin 3, i ≠ j →
      ((fun i j => (π j, π i) : Fin 3 → Fin 3 → Fin 3 × Fin 3) i j).1 ≠
        ((fun i j => (π j, π i) : Fin 3 → Fin 3 → Fin 3 × Fin 3) i j).2 :=
    fun i j hij => (π.injective.ne hij).symm
  have htsurj : ∀ i j : Fin 3, i ≠ j → ∃ i' j' : Fin 3, i' ≠ j' ∧
      (fun i j => (π j, π i) : Fin 3 → Fin 3 → Fin 3 × Fin 3) i' j' = (i, j) :=
    fun i j hij => ⟨π.symm j, π.symm i, (π.symm.injective.ne hij).symm, by simp⟩
  obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData ρ h.injective σ ε hε Fr hFrbij n
    (fun i j => (π j, π i)) htne htsurj hconj
  have hS3 : ∀ r ∈ {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j}, IsRoot τ r :=
    fun r ⟨i, j, hij, hr⟩ => hr ▸ h.isRoot i j hij
  exact a2_family_unitary hℓ hf hk hq2 hS3 ρ h.injective h.range
    (fun b => ⟨fun i => rootChar b (σ i 0), fun A => h.torus b A⟩) h.diag Fr n Φ' hΦ' π b
    (fun i j hij t => by rw [hshape i j hij t, hFr])

end IsA2Frame

end Transport

end CFSG.RankThree.PartOne.KF4
