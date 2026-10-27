module

public import CFSG.RankThree.PartOne.KE.E6FourGraph
public import CFSG.RankThree.PartOne.KE.E6FourSigned

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (chainRoot weylMatrix e6Index e6Rho permLattice_e6Rho_e6Rho)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (blockSL)
open CFSG.RankThree.Classical2 (sln_root_permuting_frobenius_fixed_split)
open scoped Matrix MatrixGroups

abbrev twistE6 {L : Type} [Field L] (Fr : L →+* L) : ModGL Tag.E6 L →* ModGL Tag.E6 L :=
  twistHom TwistTag.E6 L Fr

theorem twistE6_apply {L : Type} [Field L] (Fr : L →+* L) (g : ModGL Tag.E6 L) :
    twistE6 Fr g = diagE6 L * Units.map (entrywiseHom Fr) g * (diagE6 L)⁻¹ :=
  rfl

theorem twistedFixedPoints_twist {L : Type} [Field L] (n : ModGL Tag.E6 L) (Fr : L →+* L) :
    twistedFixedPoints n (twistE6 Fr) =
      twistedFixedPoints (n * diagE6 L) (Units.map (entrywiseHom Fr)) := by
  ext y
  rw [mem_twistedFixedPoints, mem_twistedFixedPoints, twistE6_apply]
  have : (n * diagE6 L) * Units.map (entrywiseHom Fr) y * (n * diagE6 L)⁻¹ =
      n * (diagE6 L * Units.map (entrywiseHom Fr) y * (diagE6 L)⁻¹) * n⁻¹ := by group
  rw [this]

theorem twistedTorusOf_twist {L : Type} [Field L] (n : ModGL Tag.E6 L) (Fr : L →+* L) :
    twistedTorusOf n (twistE6 Fr) =
      twistedTorusOf (n * diagE6 L) (Units.map (entrywiseHom Fr)) := by
  ext y
  rw [mem_twistedTorusOf, mem_twistedTorusOf, twistE6_apply]
  have : (n * diagE6 L) * Units.map (entrywiseHom Fr) y * (n * diagE6 L)⁻¹ =
      n * (diagE6 L * Units.map (entrywiseHom Fr) y * (diagE6 L)⁻¹) * n⁻¹ := by group
  rw [this]

theorem subtorusSigma_twist {L : Type} [Field L] (n : ModGL Tag.E6 L) (Fr : L →+* L)
    (S : Set (Fin Tag.E6.rank → ℤ)) :
    subtorusSigma n (twistE6 Fr) S =
      subtorusSigma (n * diagE6 L) (Units.map (entrywiseHom Fr)) S := by
  unfold subtorusSigma
  rw [twistedTorusOf_twist]

@[expose] def IsSigmaFamilyΦ {τ : Tag} {L : Type} [Field L] {ι' : Type} (n : ModGL τ L)
    (Φ : ModGL τ L →* ModGL τ L) (S : Set (Fin τ.rank → ℤ)) (P : ι' → Subgroup (ModGL τ L)) :
    Prop :=
  (∀ i, Finite (P i)) ∧ (∀ i, CFSG.IsQuasisimple (P i)) ∧ (∀ i, P i ≤ rootSpan τ L S) ∧
    (∀ i, P i ≤ twistedFixedPoints n Φ) ∧ (∀ i, P i ≤ adjointGroup τ L) ∧
    (∀ i, ∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, y ∈ twistedFixedPoints n Φ →
      ∀ u ∈ P i, y * u * y⁻¹ ∈ P i) ∧
    (∀ y ∈ torusGroup τ L ⊔ rootSpan τ L S, y ∈ twistedFixedPoints n Φ →
      (∀ i, ∀ u ∈ P i, y * u = u * y) → y ∈ subtorusSigma n Φ S)

theorem isSigmaFamilyΦ_twist {L : Type} [Field L] {ι' : Type} (n : ModGL Tag.E6 L)
    (Fr : L →+* L) (S : Set (Fin Tag.E6.rank → ℤ)) (P : ι' → Subgroup (ModGL Tag.E6 L))
    (h : IsSigmaFamily (n * diagE6 L) Fr S P) : IsSigmaFamilyΦ n (twistE6 Fr) S P := by
  unfold IsSigmaFamilyΦ
  simp only [twistedFixedPoints_twist, subtorusSigma_twist]
  exact h

theorem e6_tw_four_family_aux {L : Type} [Field L] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    [IsAlgClosed L] {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (n : ModGL Tag.E6 L) (hnm : n ∈ monomialSubgroup Tag.E6 L)
    (hnW : ∀ x, weylQuotientHom Tag.E6 L ⟨n, hnm⟩ • x =
      (e6SM (-1)) *ᵥ permLattice e6Rho x)
    (v : WeylGroup Tag.E6)
    (hperm : ∃ π : Equiv.Perm (Fin 4), ∀ i j : Fin 4, i ≠ j →
      e6SM (-1) *ᵥ sigmaRootE6A3 v i j = sigmaRootE6A3 v (π i) (π j)) :
    ∃ P : Unit → Subgroup (ModGL Tag.E6 L),
      IsSigmaFamily (n * diagE6 L) Fr (sigmaSetE6A3 v) P ∧
      P () = rootSpan Tag.E6 L (sigmaSetE6A3 v) ⊓
        twistedFixedPoints (n * diagE6 L) (Units.map (entrywiseHom Fr)) ∧
      (∃ h₀ : ModGL Tag.E6 L, ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.E6 L (e6Index 0)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P ()) ∧
      ∃ H : SL(4, L), ∀ Y : SL(4, k),
        rhoSigmaE6A3 L v (H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹) ∈ P () := by
  classical
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  choose! ε hε using fun (i j : Fin 4) (hij : i ≠ j) =>
    rhoSigmaE6A3_transvection (L := L) v i j hij
  have htor : ∀ b : Fin Tag.E6.rank → Lˣ, ∃ d : Fin 4 → Lˣ, ∀ A : SL(4, L),
      rootDiagUnit Tag.E6 b * rhoSigmaE6A3 L v A * (rootDiagUnit Tag.E6 b)⁻¹ =
        rhoSigmaE6A3 L v (conjDiagn d A) := fun b =>
    ⟨fun i => rootChar b (wbE6A3 v i), fun A => rhoSigmaE6A3_torus v b A⟩
  have hdiag : ∀ A : SL(4, L), (∀ i j, i ≠ j → (A : Matrix (Fin 4) (Fin 4) L) i j = 0) →
      rhoSigmaE6A3 L v A ∈ torusGroup Tag.E6 L := fun A hA => rhoSigmaE6A3_diagonal v A hA
  have hrange := rhoSigmaE6A3_range (L := L) v
  have hh₀ : ∀ (J : SL(4, L)) (Y : SL(2, k)),
      rhoSigmaE6A3 L v (J * blockSL L 2 2 (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) *
          J⁻¹) =
        (canonicalRep (coxeterSystem Tag.E6) L v * e6rhoJ3 L J) *
          simpleRootSL2 Tag.E6 L (e6Index 0)
            (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) *
          (canonicalRep (coxeterSystem Tag.E6) L v * e6rhoJ3 L J)⁻¹ := by
    intro J Y
    have h1 : e6rhoJ3 L (J * blockSL L 2 2 (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) *
        J⁻¹) = e6rhoJ3 L J * simpleRootSL2 Tag.E6 L (e6Index 0)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * (e6rhoJ3 L J)⁻¹ := by
      rw [map_mul, map_mul, map_inv, e6rhoJ3_blockSL]
    change (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) L v))
      (e6rhoJ3 L (J * blockSL L 2 2 (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) *
        J⁻¹)) = _
    rw [h1, MulAut.conj_apply]
    group
  obtain ⟨π, hπ⟩ := hperm
  set Q : ModGL Tag.E6 L := diagE6 L with hQ
  have hconj : ∀ i j : Fin 4, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      (n * Q) * pinnedX Tag.E6 L (sigmaRootE6A3 v i j) c * (n * Q)⁻¹ =
        pinnedX Tag.E6 L (sigmaRootE6A3 v (π i) (π j)) ((b : L) * c) := fun i j hij => by
    have hα : IsRoot Tag.E6 (sigmaRootE6A3 v i j) := isRoot_sigmaRootE6A3 v hij
    obtain ⟨e, hee, he⟩ := diagramMap_conj_pinnedX (K := L) TwistTag.E6 hα
    have he' : ∀ c : L, Q * pinnedX Tag.E6 L (sigmaRootE6A3 v i j) c * Q⁻¹ =
        pinnedX Tag.E6 L (permLattice e6Rho (sigmaRootE6A3 v i j)) (e * c) := he
    have hρα : IsRoot Tag.E6 (permLattice e6Rho (sigmaRootE6A3 v i j)) :=
      hα.permLattice TwistTag.E6.cartan_perm
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm hρα
    have hW : weylQuotientHom Tag.E6 L ⟨n, hnm⟩ • permLattice e6Rho (sigmaRootE6A3 v i j) =
        sigmaRootE6A3 v (π i) (π j) := by
      rw [hnW, permLattice_e6Rho_e6Rho, hπ i j hij]
    refine ⟨μ * ⟨e, e, hee, hee⟩, fun c => ?_⟩
    have e1 : (n * Q) * pinnedX Tag.E6 L (sigmaRootE6A3 v i j) c * (n * Q)⁻¹ =
        n * (Q * pinnedX Tag.E6 L (sigmaRootE6A3 v i j) c * Q⁻¹) * n⁻¹ := by group
    rw [e1, he' c, hμ (e * c), hW]
    congr 1
    simp only [Units.val_mul]
    ring
  obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData_n (τ := Tag.E6) (ν := 4)
    (rhoSigmaE6A3 L v) (rhoSigmaE6A3_injective v) (sigmaRootE6A3 v) ε hε Fr hFrbij (n * Q)
    (fun i j => (π i, π j)) (fun i j hij => π.injective.ne hij)
    (fun i j hij => ⟨π.symm i, π.symm j, π.symm.injective.ne hij, by simp⟩) hconj
  have hshape' : ∀ (i j : Fin 4) (hij : i ≠ j) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(4, L)) :
        Matrix (Fin 4) (Fin 4) L) = 1 + single (π i) (π j) ((b i j : L) * t ^ ℓ ^ f) :=
    fun i j hij t => by rw [hshape i j hij t, hFr]
  obtain ⟨P, hP, hP1, hP2⟩ := an_family_split hℓ hf hk (by norm_num)
    (sigmaSetE6A3_isRoot v) (rhoSigmaE6A3 L v) (rhoSigmaE6A3_injective v)
    hrange htor hdiag Fr (n * Q) Φ' hΦ' π b hshape'
  obtain ⟨J, hJ⟩ := sln_fixed_contains_block_split hℓ hf hk (m := 2) (by norm_num) π Φ' b
    hshape'
  obtain ⟨-, ⟨H, hH⟩, -, -, -, -⟩ := sln_root_permuting_frobenius_fixed_split hℓ hf hk
    (by norm_num) π Φ' b hshape'
  refine ⟨P, hP, by rw [hP1, hrange], ⟨canonicalRep (coxeterSystem Tag.E6) L v * e6rhoJ3 L J,
    fun Y => ?_⟩, ⟨H, fun Y => ?_⟩⟩
  · rw [hP2, ← hh₀ J Y]
    exact ⟨_, hJ Y, rfl⟩
  · rw [hP2]
    exact ⟨_, (hH _).2 ⟨Y, rfl⟩, rfl⟩

theorem e6_tw_four_family {L : Type} [Field L] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    [IsAlgClosed L] {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (n : ModGL Tag.E6 L) (hnm : n ∈ monomialSubgroup Tag.E6 L)
    (hnW : ∀ x, weylQuotientHom Tag.E6 L ⟨n, hnm⟩ • x =
      (e6SM (-1)) *ᵥ permLattice e6Rho x)
    (v : WeylGroup Tag.E6)
    (hperm : ∃ π : Equiv.Perm (Fin 4), ∀ i j : Fin 4, i ≠ j →
      e6SM (-1) *ᵥ sigmaRootE6A3 v i j = sigmaRootE6A3 v (π i) (π j)) :
    ∃ P : Unit → Subgroup (ModGL Tag.E6 L),
      IsSigmaFamilyΦ n (twistE6 Fr) (sigmaSetE6A3 v) P ∧
      P () = rootSpan Tag.E6 L (sigmaSetE6A3 v) ⊓ twistedFixedPoints n (twistE6 Fr) ∧
      (∃ h₀ : ModGL Tag.E6 L, ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.E6 L (e6Index 0)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P ()) ∧
      ∃ H : SL(4, L), ∀ Y : SL(4, k),
        rhoSigmaE6A3 L v (H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹) ∈ P () := by
  obtain ⟨P, hP, hP1, h₀, H⟩ := e6_tw_four_family_aux hℓ hf hk Fr hFr n hnm hnW v hperm
  refine ⟨P, isSigmaFamilyΦ_twist n Fr _ P hP, ?_, h₀, H⟩
  rw [hP1, twistedFixedPoints_twist]

end CFSG.RankThree.PartOne.KE
