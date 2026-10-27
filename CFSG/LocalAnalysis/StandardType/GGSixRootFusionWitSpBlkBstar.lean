module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpBlkNorm
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrame

public section

open Polynomial Module Matrix

namespace CFSG.StandardType

namespace WitSpBlk

open SpNS

section Group

open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {n p : ℕ}

theorem exists_frame_of_block_norm {D : Type} [AddCommGroup D] [Module F D] [FiniteDimensional F D]
    [Nontrivial D] {c : D →ₗ[F] D} (hp : p.Prime) (hK : ¬ p ∣ Nat.card F - 1)
    (hD : SpBlockExists F p D c) {e : ℕ} (β : Basis (Fin e) F D) (hcℓ : c ^ p = 1)
    (hcfix : ∀ d, c d = d → d = 0) (hcN : BlockNormal F D c) (ψ : StatedSp n F →* G)
    (hψ : Function.Injective ψ)
    {B Bs : Subgroup G} (hBs : GGBstar p B Bs) (hmem : ∀ b ∈ Bs, b ∈ ψ.range) :
    ∃ (s r : ℕ) (C : Matrix (Fin e) (Fin e) F) (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r)
      (A₀ : GL (Fin n ⊕ Fin n) F),
      C ^ p = 1 ∧ (∀ j : ℕ, ¬ p ∣ j → ∀ c₀ : F, IsUnit (C ^ j - c₀ • 1)) ∧
        (∀ k : Fin s → ℕ, ∃ b ∈ Bs, NoOffPSLRest.SpFrameRep ψ A₀ ε C b k) ∧
          (∀ b ∈ Bs, ∃ k : Fin s → ℕ, NoOffPSLRest.SpFrameRep ψ A₀ ε C b k) ∧
            BlockNormalMat F C := by
  classical
  set S : Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
    {M | ∃ X : StatedSp n F, ψ X ∈ Bs ∧
      M = ((X : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)} with hS
  have hSc : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    rintro _ ⟨X, hX, rfl⟩ _ ⟨Y, hY, rfl⟩
    have h1 : X * Y = Y * X := hψ (by
      rw [map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hBs.2.1 hX hY)
    have h2 := congrArg (fun Z : StatedSp n F =>
      ((Z : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) h1
    simp only [Subgroup.coe_mul, Units.val_mul] at h2
    exact h2
  have hSp : ∀ x ∈ S, x ^ p = 1 := by
    rintro _ ⟨X, hX, rfl⟩
    have h1 : X ^ p = 1 := hψ (by rw [map_pow, map_one]; exact hBs.2.1.2 _ hX)
    have h2 := congrArg (fun Z : StatedSp n F =>
      ((Z : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) h1
    simpa using h2
  have hSJ : ∀ x ∈ S, xᵀ * jMat n F * x = jMat n F := by
    rintro _ ⟨X, -, rfl⟩
    exact CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp X.2
  obtain ⟨s, r, ε, A₀, hframe, hJ⟩ := exists_spFrame_matrix hD hp.one_lt.le β S hSc hSp hSJ
  set C := LinearMap.toMatrix β β c with hC
  have hCp : C ^ p = 1 := by rw [hC, LinearMap.toMatrix_pow, hcℓ, LinearMap.toMatrix_one]
  have hrep : ∀ b ∈ Bs, ∃ k : Fin s → ℕ, NoOffPSLRest.SpFrameRep ψ A₀ ε C b k := by
    intro b hb
    obtain ⟨X, rfl⟩ := hmem b hb
    obtain ⟨k, hk⟩ := hframe _ ⟨X, hb, rfl⟩
    exact ⟨k, X, rfl, hk⟩
  refine ⟨s, r, C, ε, A₀, hCp, isUnit_toMatrix_pow_sub hp hK β hcℓ hcfix, fun k => ?_, hrep,
    blockNormalMat_toMatrix β hcN⟩
  set M := (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * (SLNS.nsCore C k).submatrix ε ε *
    ((A₀⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) with hM
  have hMJ : Mᵀ * jMat n F * M = jMat n F := hJ k
  have hNM : (-(jMat n F) * Mᵀ * jMat n F) * M = 1 := by
    calc (-(jMat n F) * Mᵀ * jMat n F) * M = -(jMat n F) * (Mᵀ * jMat n F * M) := by
          simp only [Matrix.mul_assoc]
      _ = -(jMat n F) * jMat n F := by rw [hMJ]
      _ = 1 := by rw [Matrix.neg_mul, ← Matrix.mul_neg, jMat_mul_neg]
  set X : GL (Fin n ⊕ Fin n) F :=
    ⟨M, -(jMat n F) * Mᵀ * jMat n F, mul_eq_one_comm.mpr hNM, hNM⟩ with hX
  have hXSp : X ∈ StatedSp n F :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mpr hMJ
  have hY : NoOffPSLRest.SpFrameRep ψ A₀ ε C (ψ ⟨X, hXSp⟩) k := ⟨⟨X, hXSp⟩, rfl, rfl⟩
  refine ⟨ψ ⟨X, hXSp⟩, hBs.2.2.2 _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)
    (spFrameRep_pow_eq_one hCp hY), hY⟩
  obtain ⟨k', hk'⟩ := hrep b hb
  have h1 := hk'.mul hY
  have h2 := hY.mul hk'
  rw [add_comm] at h2
  exact h1.eq h2

end Group

end WitSpBlk

section Family

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic WitSpBlk

theorem spNonsplitFrame_norm {G : Type} [Group G] {n f p : ℕ} (hf : 1 ≤ f) (hrk : 2 ≤ n)
    (ψ : StatedSp n (GaloisField 2 f) →* G)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 2 f)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) (hpp : p.Prime) (hp2 : p ≠ 2)
    {B Bs : Subgroup G} (hBs : GGBstar p B Bs)
    (hdiag : ∀ b ∈ Bs, GGPsiInnerDiag (Symplectic.rootDatum n (GaloisField 2 f)) ψ b)
    (hns : ¬ p ∣ 2 ^ f - 1) :
    ∃ (e s r : ℕ) (C : Matrix (Fin e) (Fin e) (GaloisField 2 f))
      (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r) (A₀ : GL (Fin n ⊕ Fin n) (GaloisField 2 f)),
      C ^ p = 1 ∧ (∀ j : ℕ, ¬ p ∣ j → ∀ c : GaloisField 2 f, IsUnit (C ^ j - c • 1)) ∧
        (∀ k : Fin s → ℕ, ∃ b ∈ Bs, NoOffPSLRest.SpFrameRep ψ A₀ ε C b k) ∧
          (∀ b ∈ Bs, ∃ k : Fin s → ℕ, NoOffPSLRest.SpFrameRep ψ A₀ ε C b k) ∧
            BlockNormalMat (GaloisField 2 f) C := by
  classical
  have hmem : ∀ b ∈ Bs, b ∈ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hcg⟩ := PsiDiag.Symp.exists_mem_centralizer (F := GaloisField 2 f) hrk ψ hker
      (hdiag b hb)
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz := hker ha
    rw [Symplectic.center_eq,
      CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by omega)] at hz
    exact Subgroup.mem_bot.mp hz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hK : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by rwa [hcardF]
  have hpK : (p : GaloisField 2 f) ≠ 0 := TableBSymp.natCast_ne_zero_of_charTwo hpp hp2
  have : Fact p.Prime := ⟨hpp⟩
  have hne : ¬ IsUnit (cyclotomic p (GaloisField 2 f)) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero p _),
      natDegree_cyclotomic, Nat.totient_prime hpp]
    have := hpp.two_le
    norm_cast
    omega
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero p _)
  have : Fact (Irreducible g) := ⟨hg⟩
  have hζ := NSFrame.root_isPrimitiveRoot (g := g) hpp hpK hgd
  have : Module.Finite (GaloisField 2 f) (AdjoinRoot g) := (CoordSL.rootPB g).finite
  have hζ1 : AdjoinRoot.root g ≠ 1 := hζ.ne_one hpp.one_lt
  have hζ1' : AdjoinRoot.root g ^ (p - 1) ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt (by have := hpp.two_le; omega) (by have := hpp.pos; omega)
  have hfix : ∀ μ : AdjoinRoot g, μ ≠ 1 → ∀ d : AdjoinRoot g, μ * d = d → d = 0 :=
    fun μ hμ d hd => by
      have h0 : (μ - 1) * d = 0 := by rw [sub_mul, hd, one_mul, sub_self]
      exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hμ)
  have hpowp : ∀ μ : AdjoinRoot g, μ ^ p = 1 → LinearMap.mulLeft (GaloisField 2 f) μ ^ p = 1 :=
    fun μ hμ => LinearMap.ext fun d => by
      rw [LinearMap.pow_mulLeft, LinearMap.mulLeft_apply, hμ, one_mul, Module.End.one_apply]
  have hζp' : (AdjoinRoot.root g ^ (p - 1)) ^ p = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  by_cases hσ : aeval (AdjoinRoot.root g ^ (p - 1)) g = 0
  · obtain ⟨s, r, C, ε, A₀, h₁, h₂, h₃, h₄, h₅⟩ := exists_frame_of_block_norm hpp hK
      (SpNS.spBlockExists_selfDual hpp hp2 hpK hgd hσ) (CoordSL.rootPB g).basis
      (hpowp _ hζ.pow_eq_one) (fun d hd => hfix _ hζ1 d hd)
      (blockNormal_selfDual hpp hp2 hpK hgd hσ) ψ hinj hBs hmem
    exact ⟨_, s, r, C, ε, A₀, h₁, h₂, h₃, h₄, h₅⟩
  · obtain ⟨s, r, C, ε, A₀, h₁, h₂, h₃, h₄, h₅⟩ := exists_frame_of_block_norm hpp hK
      (SpNS.spBlockExists_paired hpp hpK hgd hσ)
      (((CoordSL.rootPB g).basis.prod (CoordSL.rootPB g).basis).reindex finSumFinEquiv)
      (by rw [OrdPNS.prodMap_pow, hpowp _ hζ.pow_eq_one, hpowp _ hζp', LinearMap.prodMap_one])
      (fun d hd => by
        obtain ⟨μ, ν⟩ := d
        rw [LinearMap.prodMap_apply, Prod.mk.injEq] at hd
        exact Prod.ext (hfix _ hζ1 μ hd.1) (hfix _ hζ1' ν hd.2))
      (blockNormal_paired hpp hpK hgd hσ) ψ hinj hBs hmem
    exact ⟨_, s, r, C, ε, A₀, h₁, h₂, h₃, h₄, h₅⟩

end Family

end CFSG.StandardType
