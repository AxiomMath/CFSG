module

public import CFSG.RankThree.PartOne.KE.E6A3Sigma
public import CFSG.RankThree.PartOne.KE.SLnDescended
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderFour
public import CFSG.RankThree.PartOne.KE.SLnShape

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice
open CFSG.RankThree.E6 (chainRoot weylMatrix e6Index)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (blockSL)
open CFSG.RankThree.Classical2 (unitarySet sln_root_permuting_frobenius_fixed_unitary)
open scoped Matrix MatrixGroups

theorem mem_sigmaSetE6A3_iff {v : WeylGroup Tag.E6} {r : Fin Tag.E6.rank → ℤ} :
    r ∈ sigmaSetE6A3 v ↔ ∃ i j : Fin 4, i ≠ j ∧ r = sigmaRootE6A3 v i j := by
  rw [sigmaSetE6A3_eq]
  rfl

theorem sigmaSetE6A3_isRoot (v : WeylGroup Tag.E6) : ∀ r ∈ sigmaSetE6A3 v, IsRoot Tag.E6 r :=
  fun r hr => by
    obtain ⟨i, j, hij, rfl⟩ := mem_sigmaSetE6A3_iff.1 hr
    exact isRoot_sigmaRootE6A3 v hij

theorem sigmaSetE6A3_neg (v : WeylGroup Tag.E6) : ∀ r ∈ sigmaSetE6A3 v, -r ∈ sigmaSetE6A3 v :=
  fun r hr => by
    obtain ⟨i, j, hij, rfl⟩ := mem_sigmaSetE6A3_iff.1 hr
    rw [sigmaRootE6A3_neg]
    exact mem_sigmaSetE6A3_iff.2 ⟨j, i, hij.symm, rfl⟩

theorem e6_four_family {L : Type} [Field L] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    [IsAlgClosed L] {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (n : ModGL Tag.E6 L) (hnm : n ∈ monomialSubgroup Tag.E6 L)
    (hnW : ∀ u, weylQuotientHom Tag.E6 L ⟨n, hnm⟩ • u = (weylMatrix e6F4U) *ᵥ u)
    (v : WeylGroup Tag.E6)
    (hunit : ∃ π : Equiv.Perm (Fin 4), ∀ i j : Fin 4, i ≠ j →
      weylMatrix e6F4U *ᵥ sigmaRootE6A3 v i j = sigmaRootE6A3 v (π j) (π i)) :
    ∃ P : Unit → Subgroup (ModGL Tag.E6 L), IsSigmaFamily n Fr (sigmaSetE6A3 v) P ∧
      P () = rootSpan Tag.E6 L (sigmaSetE6A3 v) ⊓
        twistedFixedPoints n (Units.map (entrywiseHom Fr)) ∧
      (∃ h₀ : ModGL Tag.E6 L, ∀ Y : SL(2, k),
        h₀ * simpleRootSL2 Tag.E6 L (e6Index 0)
          (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) * h₀⁻¹ ∈ P ()) ∧
      ∃ H : SL(4, L), ∀ Z : SL(4, L), (∃ Y ∈ unitarySet (Ω := L) (Nat.card k) 4,
        Matrix.SpecialLinearGroup.toGL Z =
          Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) →
        rhoSigmaE6A3 L v Z ∈ P () := by
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
  obtain ⟨π, hπ⟩ := hunit
  have hconj : ∀ i j : Fin 4, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      n * pinnedX Tag.E6 L (sigmaRootE6A3 v i j) c * n⁻¹ =
        pinnedX Tag.E6 L (sigmaRootE6A3 v (π j) (π i)) ((b : L) * c) := fun i j hij => by
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm (isRoot_sigmaRootE6A3 v hij)
    refine ⟨μ, fun c => ?_⟩
    rw [hμ c, hnW, hπ i j hij]
  obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData_n (τ := Tag.E6) (ν := 4)
    (rhoSigmaE6A3 L v) (rhoSigmaE6A3_injective v) (sigmaRootE6A3 v) ε hε Fr hFrbij n
    (fun i j => (π j, π i)) (fun i j hij => π.injective.ne hij.symm)
    (fun i j hij => ⟨π.symm j, π.symm i, π.symm.injective.ne hij.symm, by simp⟩) hconj
  have hshape' : ∀ (i j : Fin 4) (hij : i ≠ j) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(4, L)) :
        Matrix (Fin 4) (Fin 4) L) = 1 + single (π j) (π i) ((b i j : L) * t ^ ℓ ^ f) :=
    fun i j hij t => by rw [hshape i j hij t, hFr]
  obtain ⟨P, hP, hP1, hP2⟩ := an_family_unitary hℓ hf hk (Or.inl (by norm_num))
    (by norm_num) (sigmaSetE6A3_isRoot v) (rhoSigmaE6A3 L v) (rhoSigmaE6A3_injective v)
    hrange htor hdiag Fr n Φ' hΦ' π b hshape'
  obtain ⟨J, hJ⟩ := sln_fixed_contains_block_unitary hℓ hf hk (m := 2) (by norm_num) π Φ' b
    hshape'
  obtain ⟨-, ⟨H, hH⟩, -, -, -⟩ := sln_root_permuting_frobenius_fixed_unitary hℓ hf hk
    (by norm_num) π Φ' b hshape'
  refine ⟨P, hP, by rw [hP1, hrange], ⟨canonicalRep (coxeterSystem Tag.E6) L v * e6rhoJ3 L J,
    fun Y => ?_⟩, ⟨H, fun Z hZ => ?_⟩⟩
  · rw [hP2, ← hh₀ J Y]
    exact ⟨_, hJ Y, rfl⟩
  · rw [hP2]
    exact ⟨Z, (hH Z).2 (by rwa [hk] at hZ), rfl⟩

end CFSG.RankThree.PartOne.KE
