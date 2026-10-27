module

public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameMatrix
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderPSLRestSp
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLFrame
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices

public section

open Polynomial Module Matrix

namespace CFSG.StandardType

namespace SpNS

section Unit

variable {K : Type} [Field K] [Finite K] {ℓ : ℕ} {D : Type} [AddCommGroup D] [Module K D]
  [FiniteDimensional K D] {e : ℕ}

theorem isUnit_toMatrix_pow_sub (hℓ : ℓ.Prime) (hK : ¬ ℓ ∣ Nat.card K - 1)
    (β : Basis (Fin e) K D) {c : D →ₗ[K] D} (hcℓ : c ^ ℓ = 1) (hcfix : ∀ d, c d = d → d = 0)
    (j : ℕ) (hj : ¬ ℓ ∣ j) (c₀ : K) : IsUnit (LinearMap.toMatrix β β c ^ j - c₀ • 1) := by
  have h1 : LinearMap.toMatrix β β c ^ j - c₀ • 1 =
      LinearMap.toMatrix β β (c ^ j - c₀ • (1 : Module.End K D)) := by
    rw [map_sub, map_smul, LinearMap.toMatrix_one, LinearMap.toMatrix_pow]
  rw [h1]
  have hinj : Function.Injective (c ^ j - c₀ • (1 : Module.End K D)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    have h2 : (c ^ j) d = c₀ • d := by
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hd
      exact hd
    have h3 : ∀ m : ℕ, (c ^ (j * m)) d = c₀ ^ m • d := by
      intro m
      induction m with
      | zero => rw [mul_zero, pow_zero, pow_zero, one_smul, Module.End.one_apply]
      | succ m ih => rw [Nat.mul_succ, pow_add, Module.End.mul_apply, h2, map_smul, ih, smul_smul,
          pow_succ, mul_comm]
    by_contra hd0
    have h4 : c₀ ^ ℓ = 1 := by
      have h5 := h3 ℓ
      rw [mul_comm, pow_mul, hcℓ, one_pow, Module.End.one_apply] at h5
      have h6 : (c₀ ^ ℓ - 1) • d = 0 := by rw [sub_smul, ← h5, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h6).resolve_right hd0)
    have hc₀ : c₀ = 1 := OrdPNS.eq_one_of_pow_eq_one hℓ hK h4
    rw [hc₀, one_smul] at h2
    have hcop : Nat.Coprime j ℓ := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hj))
    obtain ⟨j', -, hj'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hℓ.one_lt
    have h7 : (c ^ (j * j')) d = d := by
      rw [h3 j', hc₀, one_pow, one_smul]
    rw [pow_eq_pow_mod _ hcℓ, hj', pow_one] at h7
    exact hd0 (hcfix d h7)
  obtain ⟨u, hu⟩ : IsUnit (c ^ j - c₀ • (1 : Module.End K D)) :=
    (Module.End.isUnit_iff _).mpr ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  rw [← hu]
  exact ⟨⟨LinearMap.toMatrix β β u, LinearMap.toMatrix β β (u⁻¹ : (Module.End K D)ˣ),
    by rw [← LinearMap.toMatrix_mul, Units.mul_inv, LinearMap.toMatrix_one],
    by rw [← LinearMap.toMatrix_mul, Units.inv_mul, LinearMap.toMatrix_one]⟩, rfl⟩

end Unit

section Group

open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {n p : ℕ}

omit [Finite F] in
theorem spFrameRep_pow_eq_one {ψ : StatedSp n F →* G} {A₀ : GL (Fin n ⊕ Fin n) F} {e s r : ℕ}
    {ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r} {C : Matrix (Fin e) (Fin e) F}
    (hCp : C ^ p = 1) {b : G} {k : Fin s → ℕ} (h : NoOffPSLRest.SpFrameRep ψ A₀ ε C b k) :
    b ^ p = 1 := by
  have hpow : ∀ m : ℕ, NoOffPSLRest.SpFrameRep ψ A₀ ε C (b ^ (m + 1)) ((m + 1) • k) := by
    intro m
    induction m with
    | zero => rwa [zero_add, pow_one, one_smul]
    | succ m ih =>
      rw [pow_succ, succ_nsmul]
      exact ih.mul h
  obtain ⟨X, hX, hXm⟩ := hpow p
  have h1 : NoOffPSLRest.SpFrameRep ψ A₀ ε C (b ^ (p + 1)) k := by
    refine ⟨X, hX, ?_⟩
    rw [hXm, NoOffPSLRest.nsCore_congr hCp (k := (p + 1) • k) (k' := k) fun i => ?_]
    rw [Pi.smul_apply, smul_eq_mul, add_mul, one_mul, Nat.mul_add_mod]
  have h2 := h1.eq h
  rw [pow_succ] at h2
  exact mul_eq_right.mp h2

theorem exists_frame_of_block {D : Type} [AddCommGroup D] [Module F D] [FiniteDimensional F D]
    [Nontrivial D] {c : D →ₗ[F] D} (hp : p.Prime) (hK : ¬ p ∣ Nat.card F - 1)
    (hD : SpBlockExists F p D c) {e : ℕ} (β : Basis (Fin e) F D) (hcℓ : c ^ p = 1)
    (hcfix : ∀ d, c d = d → d = 0) (ψ : StatedSp n F →* G) (hψ : Function.Injective ψ)
    {B Bs : Subgroup G} (hBs : GGBstar p B Bs) (hmem : ∀ b ∈ Bs, b ∈ ψ.range) :
    ∃ (s r : ℕ) (C : Matrix (Fin e) (Fin e) F) (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r)
      (A₀ : GL (Fin n ⊕ Fin n) F),
      C ^ p = 1 ∧ (∀ j : ℕ, ¬ p ∣ j → ∀ c₀ : F, IsUnit (C ^ j - c₀ • 1)) ∧
        (∀ k : Fin s → ℕ, ∃ b ∈ Bs, NoOffPSLRest.SpFrameRep ψ A₀ ε C b k) ∧
          ∀ b ∈ Bs, ∃ k : Fin s → ℕ, NoOffPSLRest.SpFrameRep ψ A₀ ε C b k := by
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
  refine ⟨s, r, C, ε, A₀, hCp, isUnit_toMatrix_pow_sub hp hK β hcℓ hcfix, fun k => ?_, hrep⟩
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

end SpNS

section Family

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic

theorem spNonsplitFrame_core {G : Type} [Group G] {n f p : ℕ} (hf : 1 ≤ f) (hrk : 2 ≤ n)
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
          ∀ b ∈ Bs, ∃ k : Fin s → ℕ, NoOffPSLRest.SpFrameRep ψ A₀ ε C b k := by
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
  · obtain ⟨s, r, C, ε, A₀, h₁, h₂, h₃, h₄⟩ := SpNS.exists_frame_of_block hpp hK
      (SpNS.spBlockExists_selfDual hpp hp2 hpK hgd hσ) (CoordSL.rootPB g).basis
      (hpowp _ hζ.pow_eq_one) (fun d hd => hfix _ hζ1 d hd) ψ hinj hBs hmem
    exact ⟨_, s, r, C, ε, A₀, h₁, h₂, h₃, h₄⟩
  · obtain ⟨s, r, C, ε, A₀, h₁, h₂, h₃, h₄⟩ := SpNS.exists_frame_of_block hpp hK
      (SpNS.spBlockExists_paired hpp hpK hgd hσ)
      (((CoordSL.rootPB g).basis.prod (CoordSL.rootPB g).basis).reindex finSumFinEquiv)
      (by rw [OrdPNS.prodMap_pow, hpowp _ hζ.pow_eq_one, hpowp _ hζp', LinearMap.prodMap_one])
      (fun d hd => by
        obtain ⟨μ, ν⟩ := d
        rw [LinearMap.prodMap_apply, Prod.mk.injEq] at hd
        exact Prod.ext (hfix _ hζ1 μ hd.1) (hfix _ hζ1' ν hd.2))
      ψ hinj hBs hmem
    exact ⟨_, s, r, C, ε, A₀, h₁, h₂, h₃, h₄⟩

theorem ggSpNonsplitFrameInput_holds : GGSpNonsplitFrameInput := by
  intro G _ _ p B Bs x L D J n f ψ hctx hC hns
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hctx.range_eq]
    exact hC
  exact spNonsplitFrame_core hctx.2.2.2.1.1.2.1 hctx.2.2.2.1.2 ψ hctx.2.2.2.2.1.2 hCψ hctx.prime
    hctx.ne_two hctx.bstar (fun b hb => hctx.2.2.2.2.2.2.1.2 b hb) hns

theorem ggSixBstarNoOffenderOn_PSpNonsplit : GGSixBstarNoOffenderOn GGPSpNonsplit :=
  ggSixBstarNoOffenderOn_PSpNonsplit_of_frame ggSpNonsplitFrameInput_holds

theorem ggSixBstarNoOffenderAt_PSp_holds : GGSixBstarNoOffenderAt .PSp :=
  ggSixBstarNoOffenderAt_PSp_of_nonsplit ggSixBstarNoOffenderOn_PSpNonsplit

end Family

end CFSG.StandardType
