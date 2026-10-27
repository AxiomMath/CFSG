module

public import CFSG.RankThree.PartOne.KF4.F4BlockSL
public import CFSG.RankThree.PartOne.KF4.Lattice3
public import CFSG.RankThree.PartOne.KE.SLnFamily
public import CFSG.RankThree.PartOne.KE.SLnDescended

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (chainRoot weylMatrix weylMatrix_mulVec)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (blockSL)
open CFSG.RankThree.PartOne.KE
open scoped Matrix MatrixGroups


namespace IsA2Frame

variable {τ : Tag} {L : Type} [Field L] {ρ : SL(3, L) →* ModGL τ L}
  {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}

theorem family_split_ex [IsAlgClosed L] (h : IsA2Frame ρ σ) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (n : ModGL τ L)
    (hnm : n ∈ monomialSubgroup τ L) (π : Equiv.Perm (Fin 3))
    (hπ : ∀ i j : Fin 3, i ≠ j → weylQuotientHom τ L ⟨n, hnm⟩ • σ i j = σ (π i) (π j)) :
    ∃ P : Unit → Subgroup (ModGL τ L),
      IsSigmaFamily n Fr {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j} P ∧
      P () = rootSpan τ L {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j} ⊓
        twistedFixedPoints n (Units.map (entrywiseHom Fr)) ∧
      ∃ J : SL(3, L), ∀ Y : SL(2, k),
        ρ (J * blockSL L 2 1 (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * J⁻¹) ∈ P () := by
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
  have hshape' : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, L)) :
        Matrix (Fin 3) (Fin 3) L) = 1 + single (π i) (π j) ((b i j : L) * t ^ ℓ ^ f) :=
    fun i j hij t => by rw [hshape i j hij t, hFr]
  obtain ⟨P, hP, hP1, hP2⟩ := an_family_split hℓ hf hk (le_refl 3) hS3 ρ h.injective h.range
    (fun b => ⟨fun i => rootChar b (σ i 0), fun A => h.torus b A⟩) h.diag Fr n Φ' hΦ' π b hshape'
  obtain ⟨J, hJ⟩ := sln_fixed_contains_block_split hℓ hf hk (m := 1) le_rfl π Φ' b hshape'
  refine ⟨P, hP, by rw [hP1, h.range], J, fun Y => ?_⟩
  rw [hP2]
  exact ⟨_, hJ Y, rfl⟩

theorem family_unitary_ex [IsAlgClosed L] (h : IsA2Frame ρ σ) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) (hq2 : 2 < ℓ ^ f) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (n : ModGL τ L) (hnm : n ∈ monomialSubgroup τ L)
    (π : Equiv.Perm (Fin 3))
    (hπ : ∀ i j : Fin 3, i ≠ j → weylQuotientHom τ L ⟨n, hnm⟩ • σ i j = σ (π j) (π i)) :
    ∃ P : Unit → Subgroup (ModGL τ L),
      IsSigmaFamily n Fr {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j} P ∧
      P () = rootSpan τ L {r | ∃ i j : Fin 3, i ≠ j ∧ r = σ i j} ⊓
        twistedFixedPoints n (Units.map (entrywiseHom Fr)) ∧
      ∃ J : SL(3, L), ∀ Y : SL(2, k),
        ρ (J * blockSL L 2 1 (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * J⁻¹) ∈ P () := by
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
  have hshape' : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, L)) :
        Matrix (Fin 3) (Fin 3) L) = 1 + single (π j) (π i) ((b i j : L) * t ^ ℓ ^ f) :=
    fun i j hij t => by rw [hshape i j hij t, hFr]
  obtain ⟨P, hP, hP1, hP2⟩ := an_family_unitary hℓ hf hk (Or.inr hq2) (le_refl 3) hS3 ρ
    h.injective h.range (fun b => ⟨fun i => rootChar b (σ i 0), fun A => h.torus b A⟩) h.diag Fr n
    Φ' hΦ' π b hshape'
  obtain ⟨J, hJ⟩ := sln_fixed_contains_block_unitary hℓ hf hk (m := 1) le_rfl π Φ' b hshape'
  refine ⟨P, hP, by rw [hP1, h.range], J, fun Y => ?_⟩
  rw [hP2]
  exact ⟨_, hJ Y, rfl⟩

end IsA2Frame

section Families

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} {k : Type} [Field k] [Algebra k L]
  [IsAlgClosure k L]

omit
  [IsAlgClosed L] in
theorem conj_blockSL_aux (c r h : ModGL Tag.F4 L) (Ψ : ModGL Tag.F4 L) :
    (c * r * (h * Ψ * h⁻¹) * (c * r)⁻¹) = c * (r * (h * Ψ * h⁻¹) * r⁻¹) * c⁻¹ := by
  group

omit [IsAlgClosed L] in
theorem f4rhoLong_mem_adjointGroup (X : SL(3, L)) : f4rhoLong L X ∈ adjointGroup Tag.F4 L := by
  have h := f4rhoLong_mem X
  rw [subsystemGroup_eq_rootSpan] at h
  exact rootSpan_le_adjointGroup L _ h

omit [IsAlgClosed L] in
theorem f4rhoShort_mem_adjointGroup (X : SL(3, L)) : f4rhoShort L X ∈ adjointGroup Tag.F4 L := by
  have h := f4rhoShort_mem X
  rw [subsystemGroup_eq_rootSpan] at h
  exact rootSpan_le_adjointGroup L _ h

theorem f4Three_family_long (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f)
    (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) (hq : δ = -1 → 2 < ℓ ^ f) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (n : ModGL Tag.F4 L) (hnm : n ∈ monomialSubgroup Tag.F4 L)
    (hnW : ∀ u, weylQuotientHom Tag.F4 L ⟨n, hnm⟩ • u = (δ • weylMatrix f4W3) *ᵥ u)
    (v : WeylGroup Tag.F4)
    (hπ : ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
      f4W3 • (v • chainRoot f4chainLong i j) = v • chainRoot f4chainLong (π i) (π j)) :
    ∃ P : Unit → Subgroup (ModGL Tag.F4 L),
      IsSigmaFamily n Fr {r | ∃ i j : Fin 3, i ≠ j ∧ r = v • chainRoot f4chainLong i j} P ∧
      P () = rootSpan Tag.F4 L {r | ∃ i j : Fin 3, i ≠ j ∧ r = v • chainRoot f4chainLong i j} ⊓
        twistedFixedPoints n (Units.map (entrywiseHom Fr)) ∧
      ∃ h₀ : ModGL Tag.F4 L, h₀ ∈ adjointGroup Tag.F4 L ∧ ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.F4 L (f4Index 0)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P () := by
  obtain ⟨π, hπ⟩ := hπ
  have hfr := (f4Long_frame (L := L)).transport v
  have hex : ∀ P : Unit → Subgroup (ModGL Tag.F4 L), (∃ J : SL(3, L), ∀ Y : SL(2, k),
      ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) L v)).toMonoidHom.comp (f4rhoLong L))
        (J * blockSL L 2 1 (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * J⁻¹) ∈ P ()) →
      ∃ h₀ : ModGL Tag.F4 L, h₀ ∈ adjointGroup Tag.F4 L ∧ ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.F4 L (f4Index 0)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P () := by
    rintro P ⟨J, hJ⟩
    refine ⟨canonicalRep (coxeterSystem Tag.F4) L v * f4rhoLong L J,
      mul_mem (canonicalRep_mem_adjointGroup _ L v) (f4rhoLong_mem_adjointGroup J), fun Y => ?_⟩
    have h := hJ Y
    have e : ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) L v)).toMonoidHom.comp
        (f4rhoLong L)) (J * blockSL L 2 1 (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) *
          J⁻¹) =
        (canonicalRep (coxeterSystem Tag.F4) L v * f4rhoLong L J) *
          simpleRootSL2 Tag.F4 L (f4Index 0) (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) *
          (canonicalRep (coxeterSystem Tag.F4) L v * f4rhoLong L J)⁻¹ := by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [map_mul, map_mul, map_inv, f4rhoLong_blockSL]
      group
    rw [e] at h
    exact h
  rcases hδ with rfl | rfl
  · have hπ' : ∀ i j : Fin 3, i ≠ j → weylQuotientHom Tag.F4 L ⟨n, hnm⟩ •
        (v • chainRoot f4chainLong i j) = v • chainRoot f4chainLong (π i) (π j) :=
      fun i j _ => by rw [hnW, one_smul, weylMatrix_mulVec]; exact hπ i j
    obtain ⟨P, hP, hP1, hJ⟩ := hfr.family_split_ex hℓ hf hk Fr hFr n hnm π hπ'
    exact ⟨P, hP, hP1, hex P hJ⟩
  · have hπ' : ∀ i j : Fin 3, i ≠ j → weylQuotientHom Tag.F4 L ⟨n, hnm⟩ •
        (v • chainRoot f4chainLong i j) = v • chainRoot f4chainLong (π j) (π i) :=
      fun i j _ => by
        rw [hnW, neg_one_smul, Matrix.neg_mulVec, weylMatrix_mulVec, hπ i j,
          f4chainLong_neg (π i) (π j), smul_neg]
    obtain ⟨P, hP, hP1, hJ⟩ := hfr.family_unitary_ex hℓ hf hk (hq rfl) Fr hFr n hnm π hπ'
    exact ⟨P, hP, hP1, hex P hJ⟩

theorem f4Three_family_short (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f)
    (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) (hq : δ = -1 → 2 < ℓ ^ f) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (n : ModGL Tag.F4 L) (hnm : n ∈ monomialSubgroup Tag.F4 L)
    (hnW : ∀ u, weylQuotientHom Tag.F4 L ⟨n, hnm⟩ • u = (δ • weylMatrix f4W3) *ᵥ u)
    (v : WeylGroup Tag.F4)
    (hπ : ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
      f4W3 • (v • f4ShortSigma i j) = v • f4ShortSigma (π i) (π j)) :
    ∃ P : Unit → Subgroup (ModGL Tag.F4 L),
      IsSigmaFamily n Fr {r | ∃ i j : Fin 3, i ≠ j ∧ r = v • f4ShortSigma i j} P ∧
      P () = rootSpan Tag.F4 L {r | ∃ i j : Fin 3, i ≠ j ∧ r = v • f4ShortSigma i j} ⊓
        twistedFixedPoints n (Units.map (entrywiseHom Fr)) ∧
      ∃ h₀ : ModGL Tag.F4 L, h₀ ∈ adjointGroup Tag.F4 L ∧ ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.F4 L (f4Index 2)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P () := by
  obtain ⟨π, hπ⟩ := hπ
  have hfr := (f4Short_frame (L := L)).transport v
  have hex : ∀ P : Unit → Subgroup (ModGL Tag.F4 L), (∃ J : SL(3, L), ∀ Y : SL(2, k),
      ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) L v)).toMonoidHom.comp (f4rhoShort L))
        (J * blockSL L 2 1 (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * J⁻¹) ∈ P ()) →
      ∃ h₀ : ModGL Tag.F4 L, h₀ ∈ adjointGroup Tag.F4 L ∧ ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.F4 L (f4Index 2)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P () := by
    rintro P ⟨J, hJ⟩
    refine ⟨canonicalRep (coxeterSystem Tag.F4) L v * f4rhoShort L J *
      simpleRootSL2 Tag.F4 L (f4Index 2) WSL,
      mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ L v) (f4rhoShort_mem_adjointGroup J))
        (simpleRootSL2_mem_adjointGroup _ _), fun Y => ?_⟩
    have h := hJ Y
    have e : ((MulAut.conj (canonicalRep (coxeterSystem Tag.F4) L v)).toMonoidHom.comp
        (f4rhoShort L)) (J * blockSL L 2 1 (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) *
          J⁻¹) =
        (canonicalRep (coxeterSystem Tag.F4) L v * f4rhoShort L J *
          simpleRootSL2 Tag.F4 L (f4Index 2) WSL) *
          simpleRootSL2 Tag.F4 L (f4Index 2) (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) *
          (canonicalRep (coxeterSystem Tag.F4) L v * f4rhoShort L J *
            simpleRootSL2 Tag.F4 L (f4Index 2) WSL)⁻¹ := by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [map_mul, map_mul, map_inv, f4rhoShort_blockSL]
      group
    rw [e] at h
    exact h
  rcases hδ with rfl | rfl
  · have hπ' : ∀ i j : Fin 3, i ≠ j → weylQuotientHom Tag.F4 L ⟨n, hnm⟩ •
        (v • f4ShortSigma i j) = v • f4ShortSigma (π i) (π j) :=
      fun i j _ => by rw [hnW, one_smul, weylMatrix_mulVec]; exact hπ i j
    obtain ⟨P, hP, hP1, hJ⟩ := hfr.family_split_ex hℓ hf hk Fr hFr n hnm π hπ'
    exact ⟨P, hP, hP1, hex P hJ⟩
  · have hπ' : ∀ i j : Fin 3, i ≠ j → weylQuotientHom Tag.F4 L ⟨n, hnm⟩ •
        (v • f4ShortSigma i j) = v • f4ShortSigma (π j) (π i) :=
      fun i j _ => by
        rw [hnW, neg_one_smul, Matrix.neg_mulVec, weylMatrix_mulVec, hπ i j,
          f4ShortSigma_neg (π i) (π j), smul_neg]
    obtain ⟨P, hP, hP1, hJ⟩ := hfr.family_unitary_ex hℓ hf hk (hq rfl) Fr hFr n hnm π hπ'
    exact ⟨P, hP, hP1, hex P hJ⟩

end Families

end CFSG.RankThree.PartOne.KF4
