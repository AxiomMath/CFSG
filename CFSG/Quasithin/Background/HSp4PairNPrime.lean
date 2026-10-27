module

public import CFSG.Quasithin.Background.HSp4M
public import CFSG.Quasithin.Background.HPairNPrime
public import CFSG.Quasithin.Background.HTriSp4
public import CFSG.Quasithin.Background.HSL3PairNPrime
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.Quasithin.Background.HFF
public import CFSG.Quasithin.Background.HSL3Inner

public section

namespace CFSG.Quasithin

namespace H

namespace Sp4

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix PairG CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (sym2 sym2_transpose unitri inv_unitri
  isUnitriangular_unitri eq_unitri_of_isUnitriangular eq_sym2)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (blockMat unipotent mem_unipotent
  exists_mem_unipotent)
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp)
open CFSG.RankThree.SubgroupLists (spForm spE spForm_spE_left spForm_mulVec)
open scoped Matrix Pointwise

local notation "ι₀" => (Sum.inl 0 : Fin 2 ⊕ Fin 2)
local notation "ι₂" => (Sum.inr 0 : Fin 2 ⊕ Fin 2)

section Lin

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

@[expose] def pairMatHom (ι F : Type) [Fintype ι] [DecidableEq ι] [Field F] :
    GL ι F × GL ι F →* MulAut (PairMod ι F) :=
  (pairHom₂ ι F).comp (MonoidHom.prodMap matHom matHom)

theorem pairMatHom_injective : Function.Injective (pairMatHom ι F) := by
  rintro ⟨A, A'⟩ ⟨C, C'⟩ h
  obtain ⟨h1, h2⟩ := pairAut_injective h
  exact Prod.ext (matHom_injective h1) (matHom_injective h2)

abbrev linPairG (ι F : Type) [Fintype ι] [DecidableEq ι] [Field F] :
    Subgroup (MulAut (PairMod ι F)) :=
  (pairMatHom ι F).range

theorem mem_linPairG {x : MulAut (PairMod ι F)} :
    x ∈ linPairG ι F ↔ ∃ A A' : GL ι F, x = pairAut (matAut A) (matAut A') := by
  constructor
  · rintro ⟨⟨A, A'⟩, rfl⟩
    exact ⟨A, A', rfl⟩
  · rintro ⟨A, A', rfl⟩
    exact ⟨(A, A'), rfl⟩

theorem linPairG_le_pairSub : linPairG ι F ≤ pairSub ι F := by
  rintro _ ⟨⟨A, A'⟩, rfl⟩
  exact pairAut_mem_pairSub _ _

theorem pairAut_mem_linPairG {a b : MulAut (StdMod ι F)} (ha : a ∈ linSub) (hb : b ∈ linSub) :
    pairAut a b ∈ linPairG ι F := by
  obtain ⟨A, rfl⟩ := exists_matAut_of_mem_linSub ha
  obtain ⟨A', rfl⟩ := exists_matAut_of_mem_linSub hb
  exact ⟨(A, A'), rfl⟩

@[expose] noncomputable def linFstG (ι F : Type) [Fintype ι] [DecidableEq ι] [Field F] :
    ↥(linPairG ι F) →* GL ι F :=
  (MonoidHom.fst _ _).comp (MonoidHom.ofInjective pairMatHom_injective).symm.toMonoidHom

theorem linFstG_apply {x : ↥(linPairG ι F)} {A A' : GL ι F}
    (h : (x : MulAut (PairMod ι F)) = pairAut (matAut A) (matAut A')) : linFstG ι F x = A := by
  have hx : x = MonoidHom.ofInjective (pairMatHom_injective (ι := ι) (F := F)) (A, A') :=
    Subtype.ext (h.trans rfl)
  change ((MonoidHom.ofInjective (pairMatHom_injective (ι := ι) (F := F))).symm x).1 = A
  rw [hx, MulEquiv.symm_apply_apply]

theorem toAddMap_pow_of_smul {M : GL ι F} {x : MulAut (StdMod ι F)} {μ : F}
    (h : ∀ w, toAddMap x w = μ • ((M : Matrix ι ι F) *ᵥ w)) (k : ℕ) (w : ι → F) :
    toAddMap (x ^ k) w = μ ^ k • (((M ^ k : GL ι F) : Matrix ι ι F) *ᵥ w) := by
  induction k generalizing w with
  | zero =>
    simp only [pow_zero, Units.val_one, one_mulVec, one_smul]
    rfl
  | succ k ih =>
    rw [pow_succ x, toAddMap_mul, h, ih, pow_succ μ, pow_succ M, Units.val_mul, mulVec_smul,
      smul_smul, mulVec_mulVec]

end Lin

variable {K : Type} [Field K]

section Normalizer

variable [CharP K 2]

omit [CharP K 2] in
theorem isSemilinear_of_eq {a : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)} {B : StatedSp 2 K}
    {σ : K ≃+* K} {D : K}
    (ha : ∀ v, toAddMap a v = D • (((B : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ fun i => σ (v i))) :
    IsSemilinear a σ := by
  intro c v
  rw [ha, ha]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show (fun i => σ c * σ (v i)) = σ c • fun i => σ (v i) from rfl, Matrix.mulVec_smul,
    smul_comm]

theorem eq_natAut_of_pow_two_pow {x : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)} {B : StatedSp 2 K}
    {D : K} (hx : ∀ v, toAddMap x v = D • (((B : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v)) {j : ℕ} (hxj : x ^ 2 ^ j = 1) :
    x = natAut (StatedSp 2 K) B := by
  have hpow := toAddMap_pow_of_smul (M := (B : GL (Fin 2 ⊕ Fin 2) K)) hx (2 ^ j)
  have hBj : ((B : GL (Fin 2 ⊕ Fin 2) K) ^ 2 ^ j) ∈ StatedSp 2 K := (StatedSp 2 K).pow_mem B.2 _
  have hform : spForm 2 K spE (Pi.single ι₂ 1) =
      (D ^ 2 ^ j) ^ 2 * spForm 2 K spE (Pi.single ι₂ 1) := by
    have h1 : ∀ v, v = D ^ 2 ^ j • ((((B : GL (Fin 2 ⊕ Fin 2) K) ^ 2 ^ j : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) := fun v => by
      rw [← hpow, hxj, toAddMap_one]
    conv_lhs => rw [h1 spE, h1 (Pi.single ι₂ 1)]
    rw [LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul, spForm_mulVec hBj]
    ring
  rw [spForm_spE_left, Pi.single_eq_same, mul_one] at hform
  have hD : D = 1 := by
    refine SL3Pair.eq_one_of_pow_two_pow (j := j + 1) ?_
    rw [pow_succ, pow_mul]
    exact hform.symm
  exact toAddMap_injective fun v => by rw [hx, hD, one_smul, toAddMap_natAut]

variable [Finite K]

theorem exists_semilinear_of_mem {x : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)}
    (hxN : x ∈ pairNormSp K) (hxS : x ∈ pairSub (Fin 2 ⊕ Fin 2) K) :
    ∃ a b : MulAut (StdMod (Fin 2 ⊕ Fin 2) K), ∃ σ : K ≃+* K,
      x = pairAut a b ∧ IsSemilinear a σ ∧ IsSemilinear b σ := by
  obtain ⟨a, b, rfl⟩ := mem_pairSub_iff.mp hxS
  obtain ⟨B, σ, D₁, D₂, ha, hb⟩ := exists_eq_of_mem_pairNormSp hxN
  exact ⟨a, b, σ, rfl, isSemilinear_of_eq ha, isSemilinear_of_eq hb⟩

theorem mem_linPairG_of {a b : MulAut (StdMod (Fin 2 ⊕ Fin 2) K)} (hx : pairAut a b ∈ pairNormSp K)
    (ha : IsSemilinear a (RingEquiv.refl K)) : pairAut a b ∈ linPairG (Fin 2 ⊕ Fin 2) K := by
  obtain ⟨B, σ, D₁, D₂, ha', hb'⟩ := exists_eq_of_mem_pairNormSp hx
  have hσ : σ = RingEquiv.refl K := (isSemilinear_of_eq ha').unique ha
  have hb : IsSemilinear b (RingEquiv.refl K) := hσ ▸ isSemilinear_of_eq hb'
  exact pairAut_mem_linPairG ha hb

theorem mem_pairSp_of_two_pow {s : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)} (hsN : s ∈ pairNormSp K)
    (hsL : s ∈ linPairG (Fin 2 ⊕ Fin 2) K) {j : ℕ} (hs : s ^ 2 ^ j = 1) : s ∈ pairSp K := by
  obtain ⟨A, A', rfl⟩ := mem_linPairG.mp hsL
  obtain ⟨B, σ, D₁, D₂, ha, hb⟩ := exists_eq_of_mem_pairNormSp hsN
  have hσ : σ = RingEquiv.refl K := (isSemilinear_of_eq ha).unique (isSemilinear_matAut A)
  subst hσ
  rw [pairAut_pow] at hs
  obtain ⟨h1, h2⟩ := pairAut_injective (hs.trans pairAut_one.symm)
  have ha' := eq_natAut_of_pow_two_pow (fun v => ha v) h1
  have hb' := eq_natAut_of_pow_two_pow (fun v => hb v) h2
  rw [ha', hb']
  exact pairHom_mem_pairImg _ _ B

theorem mem_pairSub_of_odd {y : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)} (hyN : y ∈ pairNormSp K)
    {p : ℕ} (hp : Odd p) (hyp : y ^ p = 1) : y ∈ pairSub (Fin 2 ⊕ Fin 2) K :=
  (PairN.mem_pairSub_iff_map isNatIrr_statedSp tauSp_surjective not_isoMod hyN).mpr
    (PairN.map_V₁_of_pow_odd isNatIrr_statedSp tauSp_surjective not_isoMod hyN hp hyp)

theorem permute_linPairG {B S : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))}
    (hBN : B ≤ pairNormSp K) (hSN : S ≤ pairNormSp K) (hBodd : Odd (Nat.card B))
    (hS : IsPGroup 2 S) (hBS : (B : Set (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) * S = S * B) :
    ((B ⊓ linPairG (Fin 2 ⊕ Fin 2) K : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) :
        Set (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) *
        ((S ⊓ pairSp K : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) :
          Set (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) =
      ((S ⊓ pairSp K : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) :
          Set (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) *
        ((B ⊓ linPairG (Fin 2 ⊕ Fin 2) K : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) :
          Set (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) := by
  classical
  apply SL3Pair.mul_comm_of_subset
  rintro _ ⟨u, hu, b, hb, rfl⟩
  have huL : u ∈ linPairG (Fin 2 ⊕ Fin 2) K := by
    obtain ⟨γ, rfl⟩ := hu.2
    exact ⟨((γ : GL (Fin 2 ⊕ Fin 2) K), ((tauSp γ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K)), rfl⟩
  have hub : u * b ∈ (S : Set (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) * B :=
    Set.mul_mem_mul hu.1 hb.1
  rw [← hBS] at hub
  obtain ⟨b', hb', s, hs, hbs⟩ := hub
  have hbs' : b' * s = u * b := hbs
  have hubL : u * b ∈ linPairG (Fin 2 ⊕ Fin 2) K := (linPairG _ K).mul_mem huL hb.2
  have hb'k : b' ^ Nat.card B = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B hb')
  have hb'S := mem_pairSub_of_odd (hBN hb') hBodd hb'k
  obtain ⟨j, hj⟩ := hS ⟨s, hs⟩
  have hsj : s ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hse' : s = b'⁻¹ * (u * b) := by rw [← hbs']; group
  have hsS : s ∈ pairSub (Fin 2 ⊕ Fin 2) K := by
    rw [hse']
    exact (pairSub _ K).mul_mem ((pairSub _ K).inv_mem hb'S) (linPairG_le_pairSub hubL)
  obtain ⟨b₁, b₂, σ, hb'e, hσ₁, -⟩ := exists_semilinear_of_mem (hBN hb') hb'S
  obtain ⟨s₁, s₂, τ, hse, hτ₁, -⟩ := exists_semilinear_of_mem (hSN hs) hsS
  obtain ⟨L₁, L₂, hle⟩ := mem_linPairG.mp hubL
  have h1 : b₁ * s₁ = matAut L₁ := by
    have h' := hbs'
    rw [hb'e, hse, hle, pairAut_mul] at h'
    exact (pairAut_injective h').1
  have hστ : σ * τ = 1 := by
    have h' := hσ₁.mul hτ₁
    rw [h1] at h'
    exact h'.unique (isSemilinear_matAut L₁)
  have hσk : σ ^ Nat.card B = 1 := by
    have h2 := hσ₁.pow (Nat.card B)
    have h3 : b₁ ^ Nat.card B = 1 := by
      rw [hb'e, pairAut_pow] at hb'k
      exact (pairAut_injective (hb'k.trans pairAut_one.symm)).1
    rw [h3] at h2
    exact h2.unique isSemilinear_one
  have hτj : τ ^ 2 ^ j = 1 := by
    have h2 := hτ₁.pow (2 ^ j)
    have h3 : s₁ ^ 2 ^ j = 1 := by
      rw [hse, pairAut_pow] at hsj
      exact (pairAut_injective (hsj.trans pairAut_one.symm)).1
    rw [h3] at h2
    exact h2.unique isSemilinear_one
  have hσ1 : σ = 1 := by
    have hτσ : τ = σ⁻¹ := eq_inv_of_mul_eq_one_right hστ
    have hσj : σ ^ 2 ^ j = 1 := by
      rw [hτσ, inv_pow, inv_eq_one] at hτj
      exact hτj
    have hcop : Nat.Coprime (Nat.card B) (2 ^ j) :=
      Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hBodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one hσk) (orderOf_dvd_of_pow_eq_one hσj))
  rw [hσ1] at hσ₁
  have hb'L : b' ∈ linPairG (Fin 2 ⊕ Fin 2) K := by
    have h' := hBN hb'
    rw [hb'e] at h' ⊢
    exact mem_linPairG_of h' hσ₁
  have hsL : s ∈ linPairG (Fin 2 ⊕ Fin 2) K := by
    rw [hse']
    exact (linPairG _ K).mul_mem ((linPairG _ K).inv_mem hb'L) hubL
  exact ⟨b', ⟨hb', hb'L⟩, s, ⟨hs, mem_pairSp_of_two_pow (hSN hs) hsL hsj⟩, hbs⟩

end Normalizer

@[expose] def e4 : Fin 2 ⊕ Fin 2 ≃ Fin 4 where
  toFun := Sum.elim ![0, 1] ![3, 2]
  invFun := ![Sum.inl 0, Sum.inl 1, Sum.inr 1, Sum.inr 0]
  left_inv := by decide
  right_inv := by decide

@[expose] noncomputable def reGL (K : Type) [Field K] : GL (Fin 2 ⊕ Fin 2) K →* GL (Fin 4) K :=
  Units.map (Matrix.reindexAlgEquiv K K e4).toMonoidHom

theorem coe_reGL (g : GL (Fin 2 ⊕ Fin 2) K) :
    ((reGL K g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.reindex e4 e4 (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := rfl

theorem reGL_injective : Function.Injective (reGL K) := by
  intro g h hgh
  apply Units.ext
  have := congrArg (fun x : GL (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K)) hgh
  simp only [coe_reGL] at this
  exact (Matrix.reindex e4 e4).injective this

theorem reindex_blockMat (a b c d : K) :
    Matrix.reindex e4 e4 (blockMat (unitri a) (sym2 b c d)) = Tri.spMat a b c d := by
  rw [blockMat, inv_unitri]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [e4, Tri.spMat, unitri, sym2]

theorem reGL_mem_uniGL {u : StatedSp 2 K} (hu : u ∈ unipotent 2 K) :
    reGL K u ∈ Tri.uniGL 4 K := by
  obtain ⟨A, C, hA, hC, hu⟩ := mem_unipotent.mp hu
  have hA' := eq_unitri_of_isUnitriangular hA
  have hC' := eq_sym2 hC
  have h : ((reGL K u : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Tri.spMat (A 0 1) (C 0 0) (C 0 1) (C 1 1) := by
    rw [coe_reGL, hu, hA', hC', reindex_blockMat]
    simp [unitri, sym2]
  exact Tri.mem_uniGL_of (fun i j hij => by rw [h]; exact Tri.spMat_lower _ _ _ _ i j hij)
    (fun i => by rw [h]; exact Tri.spMat_diag _ _ _ _ i)

theorem exists_reGL_eq_spN (a b c d : K) :
    ∃ u ∈ unipotent 2 K, reGL K u = Tri.spN a b c d := by
  obtain ⟨g, hg, hgm⟩ := exists_mem_unipotent (isUnitriangular_unitri a) (sym2_transpose b c d)
  refine ⟨g, hg, Units.ext ?_⟩
  rw [coe_reGL, hgm, reindex_blockMat, Tri.coe_spN]

section Bound

variable [CharP K 2]

theorem pairHom_mem_linPairG (γ : StatedSp 2 K) :
    pairHom (StatedSp 2 K) tauSp γ ∈ linPairG (Fin 2 ⊕ Fin 2) K :=
  ⟨((γ : GL (Fin 2 ⊕ Fin 2) K), ((tauSp γ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K)), rfl⟩

theorem pairHom_injective : Function.Injective (pairHom (StatedSp 2 K) tauSp) := by
  intro γ δ h
  rw [pairHom_apply, pairHom_apply] at h
  exact natAut_injective _ (pairAut_injective h).1

theorem linFstG_pairHom {x : ↥(linPairG (Fin 2 ⊕ Fin 2) K)} {γ : StatedSp 2 K}
    (h : (x : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) = pairHom (StatedSp 2 K) tauSp γ) :
    linFstG (Fin 2 ⊕ Fin 2) K x = (γ : GL (Fin 2 ⊕ Fin 2) K) :=
  linFstG_apply (h.trans rfl)

variable [Finite K]

theorem le_of_permutes {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hX1 : pairSp K ≤ X)
    (hX2 : X ≤ pairNormSp K) {Y B S : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} {c : ℕ}
    (hYB : Y ≤ B) (hBX : B ≤ X) (hY : IsCyclic Y) (hYc : Nat.card Y = 2 ^ c - 1)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBodd : Odd (Nat.card B))
    (hS : IsSylowIn 2 S X)
    (hBS : (B : Set (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) * S = S * B) : c ≤ n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) := MulEquiv.finite_left
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hBN : B ≤ pairNormSp K := hBX.trans hX2
  have hSN : S ≤ pairNormSp K := hS.le.trans hX2
  have hperm := permute_linPairG hBN hSN hBodd hS.isPGroup hBS
  set ρ := pairHom (StatedSp 2 K) tauSp with hρ
  have hρrange : ρ.range = pairSp K := rfl
  have hLnX : ((pairSp K).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX1).mpr hX2
  have hU := hS.inf_normal hX1 hLnX
  set U' := (S ⊓ pairSp K).comap ρ with hU'
  have hU'map : U'.map ρ = S ⊓ pairSp K :=
    Subgroup.map_comap_eq_self (by rw [hρrange]; exact inf_le_right)
  have htopmap : (⊤ : Subgroup ↥(StatedSp 2 K)).map ρ = pairSp K := by
    rw [← MonoidHom.range_eq_map, hρrange]
  have hU'syl : IsSylowIn 2 U' ⊤ := by
    rw [← E1.isSylowIn_map_of_injective pairHom_injective, hU'map, htopmap]
    exact hU
  let P' : Sylow 2 ↥(StatedSp 2 K) :=
    hU'syl.isPGroup.toSylow (by
      have := hU'syl.not_dvd_relIndex
      rwa [Subgroup.relIndex_top_right] at this)
  obtain ⟨P₀, hP₀⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(StatedSp 2 K) P' P₀
  have hgU : U'.map (MulAut.conj g).toMonoidHom = unipotent 2 K := by
    rw [← hP₀, ← hg, LinearFlag.coe_sylow_smul]
    rfl
  set c₀ := ρ g with hc₀
  have hU₁ : (S ⊓ pairSp K).map (MulAut.conj c₀).toMonoidHom = (unipotent 2 K).map ρ := by
    rw [← hgU, ← hU'map, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun x => ?_
    change c₀ * ρ x * c₀⁻¹ = ρ (g * x * g⁻¹)
    rw [hc₀, map_mul, map_mul, map_inv]
  set B₁ := (B ⊓ linPairG (Fin 2 ⊕ Fin 2) K).map (MulAut.conj c₀).toMonoidHom with hB₁
  have hc₀L : c₀ ∈ linPairG (Fin 2 ⊕ Fin 2) K := pairHom_mem_linPairG g
  have hc₀N : c₀ ∈ pairNormSp K := pairImg_le_pairNorm _ _ (pairHom_mem_pairImg _ _ g)
  have hB₁L : B₁ ≤ linPairG (Fin 2 ⊕ Fin 2) K := by
    rintro _ ⟨b, hb, rfl⟩
    exact (linPairG _ K).mul_mem ((linPairG _ K).mul_mem hc₀L hb.2) ((linPairG _ K).inv_mem hc₀L)
  have hB₁N : B₁ ≤ pairNormSp K := by
    rintro _ ⟨b, hb, rfl⟩
    exact (pairNormSp K).mul_mem ((pairNormSp K).mul_mem hc₀N (hBN hb.1))
      ((pairNormSp K).inv_mem hc₀N)
  have hB₁ab : ∀ a ∈ B₁, ∀ b ∈ B₁, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hBab a ha.1 b hb.1]
  set U₁ := (unipotent 2 K).map ρ with hU₁def
  have hU₁L : U₁ ≤ linPairG (Fin 2 ⊕ Fin 2) K := by
    rintro _ ⟨u, -, rfl⟩
    exact pairHom_mem_linPairG u
  have hperm₁ : (B₁ : Set (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) *
      (U₁ : Set (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) =
      (U₁ : Set (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))) * B₁ := by
    rw [← hU₁, hB₁, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hperm,
      Set.image_mul]
  set ψ := (reGL K).comp (linFstG (Fin 2 ⊕ Fin 2) K) with hψ
  set B₂ := (B₁.subgroupOf (linPairG (Fin 2 ⊕ Fin 2) K)).map ψ with hB₂
  set U₂ := (U₁.subgroupOf (linPairG (Fin 2 ⊕ Fin 2) K)).map ψ with hU₂
  have hU₂U : U₂ ≤ Tri.uniGL 4 K := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu, hux⟩ := hx
    change reGL K (linFstG _ K x) ∈ _
    rw [linFstG_pairHom hux.symm]
    exact reGL_mem_uniGL hu
  have hU₂N : ∀ a b c d : K, Tri.spN a b c d ∈ U₂ := by
    intro a b c d
    obtain ⟨u, hu, hue⟩ := exists_reGL_eq_spN a b c d
    refine ⟨⟨ρ u, hU₁L ⟨u, hu, rfl⟩⟩, ⟨u, hu, rfl⟩, ?_⟩
    change reGL K (linFstG _ K _) = _
    rw [linFstG_pairHom rfl, ← hue]
  have hB₂ab : ∀ a ∈ B₂, ∀ b ∈ B₂, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hB₁ab _ ha _ hb)
  have hB₂odd : Odd (Nat.card B₂) := by
    have h1 : Nat.card B₂ ∣ Nat.card (B₁.subgroupOf (linPairG (Fin 2 ⊕ Fin 2) K)) :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card (B₁.subgroupOf (linPairG (Fin 2 ⊕ Fin 2) K)) = Nat.card B₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₁L).toEquiv
    have h3 : Nat.card B₁ = Nat.card ↥(B ⊓ linPairG (Fin 2 ⊕ Fin 2) K) :=
      Subgroup.card_map_of_injective (MulAut.conj c₀).injective
    have h4 : Nat.card ↥(B ⊓ linPairG (Fin 2 ⊕ Fin 2) K) ∣ Nat.card B :=
      Subgroup.card_dvd_of_le inf_le_left
    rw [h2, h3] at h1
    exact Odd.of_dvd_nat hBodd (h1.trans h4)
  have hB₂U : (B₂ : Set (GL (Fin 4) K)) * (U₂ : Set (GL (Fin 4) K)) =
      (U₂ : Set (GL (Fin 4) K)) * B₂ := by
    rw [hU₂, hB₂, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, ← Set.image_mul,
      Tri.subgroupOf_mul_comm hB₁L hU₁L hperm₁]
  have htri : B₂ ≤ Tri.borGL 4 K := Tri.triangular_sp4 hK4 hU₂U hU₂N hB₂ab hB₂odd hB₂U
  have hz : ∀ z ∈ B₁, z ^ (Nat.card K - 1) = 1 := by
    intro z hz
    set A := linFstG (Fin 2 ⊕ Fin 2) K ⟨z, hB₁L hz⟩ with hA
    have hAB : reGL K A ∈ B₂ := ⟨⟨z, hB₁L hz⟩, hz, rfl⟩
    have hAodd : Odd (orderOf (reGL K A)) :=
      Odd.of_dvd_nat hB₂odd (Subgroup.orderOf_dvd_natCard B₂ hAB)
    have hA1 : A ^ (Nat.card K - 1) = 1 := by
      have h1 := Tri.pow_card_sub_one_eq_one (htri hAB) hAodd
      rw [← map_pow] at h1
      exact reGL_injective (h1.trans (map_one _).symm)
    obtain ⟨A₁, A₂, hze⟩ := mem_linPairG.mp (hB₁L hz)
    have hAA : A = A₁ := linFstG_apply (x := ⟨z, hB₁L hz⟩) hze
    rw [← hAA] at hze
    have hzN := hB₁N hz
    rw [hze] at hzN
    obtain ⟨Bs, σ, D₁, D₂, ha, hb⟩ := exists_eq_of_mem_pairNormSp hzN
    have hσ : σ = RingEquiv.refl K := (isSemilinear_of_eq ha).unique (isSemilinear_matAut A)
    subst hσ
    have ha' : ∀ v, toAddMap (matAut A) v = D₁ • (((Bs : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) := fun v => ha v
    have hb' : ∀ v, toAddMap (matAut A₂) v = D₂ • ((((tauSp Bs : StatedSp 2 K) :
        GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) := fun v => hb v
    have hD₁ : D₁ ≠ 0 := by
      rintro rfl
      have h1 := ha' (Pi.single ι₀ 1)
      rw [zero_smul, toAddMap_eq_zero_iff] at h1
      have h2 := congrFun h1 ι₀
      simp at h2
    have hD₂ : D₂ ≠ 0 := by
      rintro rfl
      have h1 := hb' (Pi.single ι₀ 1)
      rw [zero_smul, toAddMap_eq_zero_iff] at h1
      have h2 := congrFun h1 ι₀
      simp at h2
    have hq : ∀ μ : K, μ ≠ 0 → μ ^ (Nat.card K - 1) = 1 := fun μ hμ => by
      have : Fintype K := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one μ hμ
    have hBs : Bs ^ (Nat.card K - 1) = 1 := by
      apply natAut_injective (StatedSp 2 K)
      refine toAddMap_injective fun v => ?_
      have h1 := toAddMap_pow_of_smul ha' (Nat.card K - 1) v
      have h2 : matAut A ^ (Nat.card K - 1) = 1 := by
        rw [← matHom_apply, ← map_pow, hA1, map_one]
      rw [h2, toAddMap_one, hq D₁ hD₁, one_smul] at h1
      rw [map_one, toAddMap_one, toAddMap_natAut, Subgroup.coe_pow]
      exact h1.symm
    have hτ : (tauSp Bs) ^ (Nat.card K - 1) = 1 := by rw [← map_pow, hBs, map_one]
    have hx₂ : matAut A₂ ^ (Nat.card K - 1) = 1 := toAddMap_injective fun w => by
      rw [toAddMap_pow_of_smul hb', hq D₂ hD₂, one_smul, ← Subgroup.coe_pow, hτ,
        Subgroup.coe_one, Units.val_one, one_mulVec, toAddMap_one]
    rw [hze, pairAut_pow, hx₂, ← matHom_apply, ← map_pow, hA1, map_one]
    exact pairAut_one
  obtain ⟨y, hy⟩ := hY.exists_generator
  have hyo : orderOf (y : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) = 2 ^ c - 1 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hy, hYc]
  have hyB : (y : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) ∈ B := hYB y.2
  have hyk : (y : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) ^ Nat.card B = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B hyB)
  have hyS := mem_pairSub_of_odd (hBN hyB) hBodd hyk
  obtain ⟨y₁, y₂, σ, hye, hσ₁, -⟩ := exists_semilinear_of_mem (hBN hyB) hyS
  have : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
    (fun _ _ h => RingEquiv.ext (congrFun h))
  set m := orderOf σ with hm
  have hmn : m ∣ n := by
    obtain ⟨-, -, -, -, hcard, -⟩ :=
      finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega) hK
    rw [← hcard]
    exact orderOf_dvd_natCard σ
  have hm0 : 0 < m := orderOf_pos σ
  have hym : (y : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) ^ m ∈ B ⊓ linPairG (Fin 2 ⊕ Fin 2) K := by
    refine ⟨B.pow_mem hyB m, ?_⟩
    have h1 : IsSemilinear (y₁ ^ m) (RingEquiv.refl K) := by
      have h' := hσ₁.pow m
      rw [hm, pow_orderOf_eq_one] at h'
      exact h'
    have h2 : (y : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) ^ m ∈ pairNormSp K :=
      (pairNormSp K).pow_mem (hBN hyB) m
    rw [hye, pairAut_pow] at h2 ⊢
    exact mem_linPairG_of h2 h1
  have hypow : (y : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) ^ (m * (Nat.card K - 1)) = 1 := by
    have h1 := hz _ ⟨_, hym, rfl⟩
    change (c₀ * (y : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) ^ m * c₀⁻¹) ^ (Nat.card K - 1) = 1
      at h1
    rw [conj_pow, conj_eq_one_iff] at h1
    rw [pow_mul]
    exact h1
  have hdvd : 2 ^ c - 1 ∣ m * (2 ^ n - 1) := by
    rw [← hyo, ← hK]
    exact orderOf_dvd_of_pow_eq_one hypow
  exact SL3Pair.le_of_dvd_mul_pow_sub_one (by omega) hm0 (Nat.le_of_dvd (by omega) hmn) hdvd

theorem nPrime_le {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {X : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K))} (hX1 : pairSp K ≤ X)
    (hX2 : X ≤ pairNormSp K) : E3.nPrime X ≤ n := by
  have : Finite (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) := MulEquiv.finite_left
  unfold E3.nPrime
  refine csSup_le ⟨1, ⊥, ⊥, (E1.exists_isSylowIn_two X).choose, bot_le, bot_le, inferInstance,
    by simp, fun a ha b hb => ?_, by simp, (E1.exists_isSylowIn_two X).choose_spec, by simp⟩ ?_
  · rw [Subgroup.mem_bot.1 ha, Subgroup.mem_bot.1 hb]
  · rintro c ⟨Y, B, S, hYB, hBX, hY, hYc, hBab, hBodd, hS, hBS⟩
    exact le_of_permutes hn hK hX1 hX2 hYB hBX hY hYc hBab hBodd hS hBS

end Bound

end Sp4

end H

end CFSG.Quasithin
