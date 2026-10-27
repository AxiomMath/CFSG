module

public import CFSG.RankThree.PartOne.S11d.PSLBlockCoord
public import CFSG.RankThree.PartOne.S11d.PSLSl
public import CFSG.RankThree.PartOne.S11d.PerfectCentral
public import CFSG.RankThree.PartOne.S11d.PSLDescent
public import CFSG.RankThree.PartOne.S11d.LieGoodConclusion
public import CFSG.RankThree.PartOne.S11d.PSLComponent

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG Polynomial Matrix
open CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCPrimary
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.LocalAnalysis.ComponentInitial.LinearCover (projectiveSpecialLinearEquivProjectiveSL)
open CFSG.Assembly.LowTwoRank (projectiveSpecialLinearGroupEquivStatedProj)

variable {n p : ℕ} {K : Type} [Field K]

abbrev slX (A : SpecialLinearGroup (Fin n) K) : Module.End K (Fin n → K) :=
  Matrix.toLin' ((SpecialLinearGroup.toGL A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

structure PSLBlock (p : ℕ) (σ : K ≃+* K) (A : SpecialLinearGroup (Fin n) K) where
  c : Kˣ
  γ : Kˣ
  hap : (SpecialLinearGroup.toGL A) ^ p = GeneralLinearGroup.scalar (Fin n) c
  hγ : γ ^ p = c
  hσγ : σ (γ : K) = γ
  hsq : Squarefree (minpoly K (slX A))
  b₀ : primaryFactors (slX A)
  hb₀ : (b₀ : K[X]) = X - C (γ : K)
  hm2 : 2 ≤ mult (slX A) b₀
  huniq : ∀ b : primaryFactors (slX A), 2 ≤ mult (slX A) b → b = b₀
  two : ∀ g ∈ Subgroup.centralizer ({SpecialLinearGroup.toGL A} : Set (GL (Fin n) K)),
    ∀ k : ℕ, g ^ 2 ^ k = 1 → g ∈ blockImage hsq b₀

theorem exists_pow_scalar {A : SpecialLinearGroup (Fin n) K} (hxp : (proj n K A) ^ p = 1) :
    ∃ c : Kˣ, ((A ^ p : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        scalar (Fin n) (c : K) ∧
      (SpecialLinearGroup.toGL A) ^ p = GeneralLinearGroup.scalar (Fin n) c := by
  have hAp' : A ^ p ∈ scalars n K := proj_eq_one_iff.mp (by rw [map_pow]; exact hxp)
  obtain ⟨c, -, hAc⟩ := mem_scalars.mp hAp'
  refine ⟨c, hAc, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar, ← hAc]
  change ((SpecialLinearGroup.toGL (A ^ p) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = _
  rw [map_pow]
  rfl

theorem psl_block_exists [Finite K] [CharP K 2] [NeZero n] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : ¬ p ∣ Nat.card Kˣ) (hrank : CFSG.pRank p (projectiveSL n K) ≤ 1) (σ : K ≃+* K)
    {A : SpecialLinearGroup (Fin n) K} (hσA : (A : Matrix (Fin n) (Fin n) K).map σ = A)
    {y : projectiveSL n K} (hxp : (proj n K A) ^ p = 1) (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1)
    (hxy : proj n K A * y = y * proj n K A) : Nonempty (PSLBlock p σ A) := by
  obtain ⟨c, hAc, hap⟩ := exists_pow_scalar hxp
  obtain ⟨hsq, γ, b₀, hγ, hb₀, hm2, htwo⟩ := exists_block_data hp hp2 hpK hrank hap hxp hy2 hy1 hxy
  have hσAmap : SpecialLinearGroup.map σ.toRingHom A = A := Subtype.ext hσA
  have hσc : σ (c : K) = c := by
    have h1 : (((A ^ p : SpecialLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K).map σ =
        ((A ^ p : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      have := congrArg (fun g : SpecialLinearGroup (Fin n) K => (g : Matrix (Fin n) (Fin n) K))
        (show SpecialLinearGroup.map σ.toRingHom (A ^ p) = A ^ p by rw [map_pow, hσAmap])
      exact this
    rw [hAc] at h1
    have h2 := congrFun (congrFun h1 (0 : Fin n)) (0 : Fin n)
    simpa [Matrix.scalar_apply, Matrix.diagonal_apply_eq] using h2
  have hσγ : σ (γ : K) = γ := by
    have hu := (exists_unique_pth_root hp hpK c).unique (y₁ := γ) hγ
      (y₂ := Units.map σ.toRingHom.toMonoidHom γ) (by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.coe_map]
        change σ (γ : K) ^ p = (c : K)
        rw [← map_pow, ← Units.val_pow_eq_pow_val, hγ, hσc])
    have := congrArg (fun u : Kˣ => (u : K)) hu
    simpa using this.symm
  have huniq : ∀ b : primaryFactors (slX A), 2 ≤ mult (slX A) b → b = b₀ := fun b hb =>
    Subtype.ext ((eq_X_sub_C_of_mult_ge_two hap hp hp2 hpK hγ hrank b hb).trans hb₀.symm)
  exact ⟨⟨c, γ, hap, hγ, hσγ, hsq, b₀, hb₀, hm2, huniq, htwo⟩⟩


namespace PSLBlock

variable {σ : K ≃+* K} {A : SpecialLinearGroup (Fin n) K} (R : PSLBlock p σ A)

noncomputable abbrev blk : Subgroup (GL (Fin n) K) := blockImage R.hsq R.b₀

noncomputable def B' : Subgroup (SpecialLinearGroup (Fin n) K) :=
  R.blk.comap SpecialLinearGroup.toGL

noncomputable def D : Subgroup (projectiveSL n K) := R.B'.map (proj n K)

theorem blk_le_range [Finite K] (hK4 : 4 ≤ Nat.card K) :
    R.blk ≤ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range :=
  blockImage_le_range_toGL R.hsq hK4 R.b₀ R.hm2

theorem B'_map [Finite K] (hK4 : 4 ≤ Nat.card K) :
    R.B'.map SpecialLinearGroup.toGL = R.blk :=
  Subgroup.map_comap_eq_self (R.blk_le_range hK4)

theorem mem_B' {g : SpecialLinearGroup (Fin n) K} :
    g ∈ R.B' ↔ SpecialLinearGroup.toGL g ∈ R.blk := Iff.rfl

theorem blk_le_centralizer :
    R.blk ≤ Subgroup.centralizer ({SpecialLinearGroup.toGL A} : Set (GL (Fin n) K)) := by
  rw [← range_commutantUnitsToGL_eq_centralizer (x := slX A) (SpecialLinearGroup.toGL A) rfl]
  exact blockImage_le_range R.hsq R.b₀

theorem B'_le_centralizer :
    R.B' ≤ Subgroup.centralizer ({A} : Set (SpecialLinearGroup (Fin n) K)) := by
  intro g hg
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  have h1 := R.blk_le_centralizer hg
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at h1
  exact SpecialLinearGroup.toGL_injective h1

theorem toGL_mem_centralizer {H : SpecialLinearGroup (Fin n) K}
    (hH : H ∈ Subgroup.centralizer ({A} : Set (SpecialLinearGroup (Fin n) K))) :
    SpecialLinearGroup.toGL H ∈
      Subgroup.centralizer ({SpecialLinearGroup.toGL A} : Set (GL (Fin n) K)) := by
  have hH' : H * A = A * H := Subgroup.mem_centralizer_singleton_iff.mp hH
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hH']

theorem B'_norm {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ Subgroup.centralizer ({A} : Set (SpecialLinearGroup (Fin n) K)))
    {f : SpecialLinearGroup (Fin n) K} (hf : f ∈ R.B') : g * f * g⁻¹ ∈ R.B' := by
  have h1 := toGL_mem_centralizer hg
  rw [← range_commutantUnitsToGL_eq_centralizer (x := slX A) (SpecialLinearGroup.toGL A) rfl]
    at h1
  rw [mem_B', map_mul, map_mul, map_inv]
  exact conj_mem_blockImage R.hsq R.b₀ h1 hf

theorem B'_quasisimple [Finite K] (hK4 : 4 ≤ Nat.card K) : CFSG.IsQuasisimple ↥R.B' := by
  have hBq : CFSG.IsQuasisimple ↥R.blk := isQuasisimple_blockImage R.hsq hK4 R.b₀ R.hm2
  have e : ↥R.B' ≃* ↥R.blk :=
    (Subgroup.equivMapOfInjective R.B' SpecialLinearGroup.toGL
      SpecialLinearGroup.toGL_injective).trans (MulEquiv.subgroupCongr (R.B'_map hK4))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hBq

theorem B'_perfect [Finite K] (hK4 : 4 ≤ Nat.card K) : Group.IsPerfect ↥R.B' :=
  (R.B'_quasisimple hK4).1

theorem isComponent [Finite K] (hK4 : 4 ≤ Nat.card K) :
    IsComponentOf (Subgroup.centralizer ({proj n K A} : Set (projectiveSL n K))) R.D :=
  isComponentOf_map_block (proj n K) (proj_surjective n K)
    (by rw [ker_proj]; exact (scalars_eq_center n K).le) A R.B' (R.B'_quasisimple hK4)
    R.B'_le_centralizer fun g hg f hf => R.B'_norm hg hf


theorem exists_lift_centralizer [Finite K] [NeZero n] (hp : p.Prime) (hpK : ¬ p ∣ Nat.card Kˣ)
    {c : Kˣ} (hAp : (SpecialLinearGroup.toGL A) ^ p = GeneralLinearGroup.scalar (Fin n) c)
    {u : projectiveSL n K} (hu : u ∈ Subgroup.centralizer ({proj n K A} : Set (projectiveSL n K))) :
    ∃ G : SpecialLinearGroup (Fin n) K, proj n K G = u ∧ A * G = G * A := by
  obtain ⟨G, rfl⟩ := proj_surjective n K u
  refine ⟨G, rfl, ?_⟩
  have h1 : proj n K G * proj n K A = proj n K A * proj n K G :=
    Subgroup.mem_centralizer_singleton_iff.mp hu
  apply mul_comm_of_commutator_scalar hp hpK hAp
  rw [← proj_eq_one_iff, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr h1.symm

theorem exists_pow_two_pow_eq [CharP K 2] [Finite K] (k : ℕ) (c : Kˣ) :
    ∃ μ : Kˣ, μ ^ 2 ^ k = c := by
  induction k generalizing c with
  | zero => exact ⟨c, by simp⟩
  | succ k ih =>
    obtain ⟨μ', hμ'⟩ := ih c
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (μ' : K)
    have hr0 : r ≠ 0 := fun h => μ'.ne_zero (by rw [hr, h, mul_zero])
    refine ⟨Units.mk0 r hr0, ?_⟩
    have : (Units.mk0 r hr0) ^ 2 = μ' := Units.ext (by simp [hr, sq])
    rw [pow_succ', pow_mul, this, hμ']

theorem two_mem [Finite K] [CharP K 2] [NeZero n] (hp : p.Prime) (hpK : ¬ p ∣ Nat.card Kˣ)
    (hK4 : 4 ≤ Nat.card K) {g : projectiveSL n K}
    (hg : g ∈ Subgroup.centralizer ({proj n K A} : Set (projectiveSL n K)))
    (hk : ∃ k : ℕ, orderOf g = 2 ^ k) : g ∈ R.D := by
  obtain ⟨G, rfl, hAG⟩ := exists_lift_centralizer hp hpK R.hap hg
  obtain ⟨k, hk⟩ := hk
  have hGk : (proj n K G) ^ 2 ^ k = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one _
  have hGs : G ^ 2 ^ k ∈ scalars n K := proj_eq_one_iff.mp (by rw [map_pow]; exact hGk)
  obtain ⟨c₂, -, hc₂⟩ := mem_scalars.mp hGs
  obtain ⟨μ, hμ⟩ := exists_pow_two_pow_eq (K := K) k c₂⁻¹
  set sμ : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) μ with hsμ
  set g' : GL (Fin n) K := sμ * SpecialLinearGroup.toGL G with hg'
  have hGLk : (SpecialLinearGroup.toGL G) ^ 2 ^ k = GeneralLinearGroup.scalar (Fin n) c₂ := by
    refine Units.ext ?_
    rw [GeneralLinearGroup.coe_scalar, ← hc₂]
    change ((SpecialLinearGroup.toGL (G ^ 2 ^ k) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = _
    rw [map_pow]
    rfl
  have hcomm : Commute sμ (SpecialLinearGroup.toGL G) :=
    (GeneralLinearGroup.scalar_commute μ _)
  have hg'pow : g' ^ 2 ^ k = 1 := by
    rw [hg', hcomm.mul_pow, hGLk, hsμ, ← map_pow, hμ, ← map_mul, inv_mul_cancel, map_one]
  have hg'cent : g' ∈ Subgroup.centralizer ({SpecialLinearGroup.toGL A} : Set (GL (Fin n) K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hg']
    have h1 : SpecialLinearGroup.toGL G * SpecialLinearGroup.toGL A =
        SpecialLinearGroup.toGL A * SpecialLinearGroup.toGL G := by
      rw [← map_mul, ← map_mul, hAG.symm]
    calc sμ * SpecialLinearGroup.toGL G * SpecialLinearGroup.toGL A
        = sμ * (SpecialLinearGroup.toGL G * SpecialLinearGroup.toGL A) := by group
      _ = sμ * (SpecialLinearGroup.toGL A * SpecialLinearGroup.toGL G) := by rw [h1]
      _ = SpecialLinearGroup.toGL A * (sμ * SpecialLinearGroup.toGL G) := by
        rw [← mul_assoc, ← mul_assoc, show sμ * SpecialLinearGroup.toGL A =
          SpecialLinearGroup.toGL A * sμ from GeneralLinearGroup.scalar_commute μ _]
  have hmem : g' ∈ R.blk := R.two g' hg'cent k hg'pow
  obtain ⟨H, hHg⟩ := R.blk_le_range hK4 hmem
  have hHB : H ∈ R.B' := by
    rw [mem_B', hHg]
    exact hmem
  have hmat : (H : Matrix (Fin n) (Fin n) K) = (μ : K) • (G : Matrix (Fin n) (Fin n) K) := by
    have h1 := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hHg
    simp only [hg', hsμ, Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
    rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul] at h1
    exact h1
  have hdet : (μ ^ n : Kˣ) = 1 := by
    have h1 := congrArg Matrix.det hmat
    rw [H.2, Matrix.det_smul, G.2, Fintype.card_fin, mul_one] at h1
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h1.symm)
  have hz : (μ⁻¹ : Kˣ) ^ n = 1 := by rw [inv_pow, hdet, inv_one]
  have hGz : G = scalarElement (μ⁻¹ : Kˣ) hz * H := by
    ext i j
    have h1 : ((μ : K)⁻¹ • (H : Matrix (Fin n) (Fin n) K)) i j =
        (G : Matrix (Fin n) (Fin n) K) i j := by
      rw [hmat, smul_smul, inv_mul_cancel₀ μ.ne_zero, one_smul]
    rw [← h1]
    simp [coe_scalarElement, Matrix.scalar_apply, Matrix.diagonal_mul]
  have : proj n K G = proj n K H := by
    rw [hGz, map_mul, (proj_eq_one_iff.mpr (scalarElement_mem_scalars _ hz)), one_mul]
  rw [this]
  exact ⟨H, hHB, rfl⟩


theorem comm_of_centralizer_D [Finite K] [NeZero n] (hp : p.Prime) (hpK : ¬ p ∣ Nat.card Kˣ)
    (hK4 : 4 ≤ Nat.card K) {u v : projectiveSL n K}
    (hu : u ∈ Subgroup.centralizer ({proj n K A} : Set (projectiveSL n K)))
    (huD : u ∈ Subgroup.centralizer (R.D : Set (projectiveSL n K)))
    (hv : v ∈ Subgroup.centralizer ({proj n K A} : Set (projectiveSL n K))) : u * v = v * u := by
  obtain ⟨Gu, rfl, hAu⟩ := exists_lift_centralizer hp hpK R.hap hu
  obtain ⟨Gv, rfl, hAv⟩ := exists_lift_centralizer hp hpK R.hap hv
  have hcomm : ∀ q ∈ R.B', Gu * q = q * Gu := by
    apply commute_of_commutator_central (R.B'_perfect hK4)
    intro q hq
    rw [← scalars_eq_center n K, ← proj_eq_one_iff]
    simp only [map_mul, map_inv]
    have h1 : proj n K q * proj n K Gu = proj n K Gu * proj n K q :=
      Subgroup.mem_centralizer_iff.mp huD (proj n K q) ⟨q, hq, rfl⟩
    rw [← h1]
    group
  have hGuC := toGL_mem_centralizer (Subgroup.mem_centralizer_singleton_iff.mpr hAu.symm)
  have hGvC := toGL_mem_centralizer (Subgroup.mem_centralizer_singleton_iff.mpr hAv.symm)
  rw [← range_commutantUnitsToGL_eq_centralizer (x := slX A) (SpecialLinearGroup.toGL A) rfl]
    at hGuC hGvC
  obtain ⟨u', hu'⟩ := hGuC
  obtain ⟨v', hv'⟩ := hGvC
  have hmem := mem_range_centerUnitsToGL_of_commute R.hsq u' (fun b hb g hg => by
    have hbb : b = R.b₀ := R.huniq b hb
    subst hbb
    obtain ⟨q, hq⟩ := R.blk_le_range hK4 hg
    have hqB : q ∈ R.B' := by
      rw [mem_B', hq]
      exact hg
    rw [hu', ← hq, ← map_mul, ← map_mul, hcomm q hqB])
  rw [hu'] at hmem
  obtain ⟨z, hz⟩ := hmem
  have hcomm2 : SpecialLinearGroup.toGL Gu * SpecialLinearGroup.toGL Gv =
      SpecialLinearGroup.toGL Gv * SpecialLinearGroup.toGL Gu := by
    rw [← hz, ← hv']
    exact centerUnitsToGL_commute (slX A) z v'
  have h3 : Gu * Gv = Gv * Gu :=
    SpecialLinearGroup.toGL_injective (by rw [map_mul, map_mul]; exact hcomm2)
  rw [← map_mul, ← map_mul, h3]


structure BlockCoordData (R : PSLBlock p σ A) (m : ℕ) where
  Φ : ↥R.B' ≃* SpecialLinearGroup (Fin m) K
  hm2 : 2 ≤ m
  stable : ∀ g ∈ R.B', SpecialLinearGroup.map σ.toRingHom g ∈ R.B'
  compat : ∀ g g' : ↥R.B', (g' : SpecialLinearGroup (Fin n) K) =
    SpecialLinearGroup.map σ.toRingHom (g : SpecialLinearGroup (Fin n) K) →
      Φ g' = SpecialLinearGroup.map σ.toRingHom (Φ g)

namespace BlockCoordData

variable {R} {m : ℕ} (c : BlockCoordData R m)

noncomputable def sig (g : ↥R.B') : ↥R.B' :=
  ⟨SpecialLinearGroup.map σ.toRingHom (g : SpecialLinearGroup (Fin n) K), c.stable g g.2⟩

theorem Φ_sig (g : ↥R.B') :
    c.Φ (c.sig g) = SpecialLinearGroup.map σ.toRingHom (c.Φ g) :=
  c.compat g (c.sig g) rfl

theorem false_of_inner (hσ1 : σ ≠ 1) (N : ↥R.B') (h : ∀ g : ↥R.B', c.sig g = N * g * N⁻¹) :
    False := by
  have hm := c.hm2
  refine not_inner_map hσ1 ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff]) (c.Φ N)
    (fun t => ?_)
  obtain ⟨g, rfl⟩ := c.Φ.surjective t
  rw [← c.Φ_sig, h g, map_mul, map_mul, map_inv]

include c in
theorem outer [Finite K] (hK4 : 4 ≤ Nat.card K) (hσ1 : σ ≠ 1) :
    ∀ e ∈ R.D, ¬ ∀ g ∈ R.D, fieldAut n K σ g = e * g * e⁻¹ := by
  intro e he hcon
  obtain ⟨E, hE, rfl⟩ := he
  have h1 := hom_eq_of_div_central (R.B'_perfect hK4)
    ((SpecialLinearGroup.map σ.toRingHom).comp R.B'.subtype)
    ((MulAut.conj E).toMonoidHom.comp R.B'.subtype) (fun q => by
      rw [← scalars_eq_center n K, ← proj_eq_one_iff]
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, map_mul, map_inv]
      rw [← fieldAut_proj, hcon (proj n K q) ⟨q, q.2, rfl⟩]
      group)
  refine c.false_of_inner hσ1 ⟨E, hE⟩ (fun g => ?_)
  apply Subtype.ext
  exact congrArg (fun f : ↥R.B' →* SpecialLinearGroup (Fin n) K => f g) h1

theorem sig_eq_of_fixed {s : SpecialLinearGroup (Fin m) K}
    (hs : SpecialLinearGroup.map σ.toRingHom s = s) :
    SpecialLinearGroup.map σ.toRingHom (c.Φ.symm s : SpecialLinearGroup (Fin n) K) =
      (c.Φ.symm s : SpecialLinearGroup (Fin n) K) := by
  have h : c.Φ (c.sig (c.Φ.symm s)) = c.Φ (c.Φ.symm s) := by
    rw [c.Φ_sig, MulEquiv.apply_symm_apply, hs]
  exact congrArg Subtype.val (c.Φ.injective h)

include c in
theorem pair [CharP K 2] :
    ∃ t₁ ∈ R.D, fieldAut n K σ t₁ = t₁ ∧ ∃ t₂ ∈ R.D, fieldAut n K σ t₂ = t₂ ∧
      (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧ (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁ := by
  have hm := c.hm2
  set i : Fin m := ⟨0, by omega⟩ with hi
  set j : Fin m := ⟨1, by omega⟩ with hj
  have hij : i ≠ j := by simp [hi, hj, Fin.ext_iff]
  set s₁ := tvSL i j hij (1 : K) with hs₁
  set s₂ := tvSL j i hij.symm (1 : K) with hs₂
  have hf₁ : SpecialLinearGroup.map σ.toRingHom s₁ = s₁ := by
    rw [hs₁, map_tvSL, map_one]
  have hf₂ : SpecialLinearGroup.map σ.toRingHom s₂ = s₂ := by
    rw [hs₂, map_tvSL, map_one]
  set g₁ : ↥R.B' := c.Φ.symm s₁ with hg₁
  set g₂ : ↥R.B' := c.Φ.symm s₂ with hg₂
  have hsq : ∀ (t : SpecialLinearGroup (Fin m) K) (g : ↥R.B'), c.Φ g = t → t * t = 1 →
      ∃ k : ℕ, orderOf (proj n K (g : SpecialLinearGroup (Fin n) K)) = 2 ^ k := by
    intro t g hg ht
    have h1 : g * g = 1 := by
      apply c.Φ.injective
      rw [map_mul, hg, ht, map_one]
    have h2 : (proj n K (g : SpecialLinearGroup (Fin n) K)) ^ 2 = 1 := by
      rw [pow_two, ← map_mul]
      have : (g : SpecialLinearGroup (Fin n) K) * g = 1 := congrArg Subtype.val h1
      rw [this, map_one]
    have h3 : orderOf (proj n K (g : SpecialLinearGroup (Fin n) K)) ∣ 2 ^ 1 := by
      simpa using orderOf_dvd_of_pow_eq_one h2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h3
    exact ⟨k, hk⟩
  refine ⟨proj n K (g₁ : SpecialLinearGroup (Fin n) K), ⟨g₁, g₁.2, rfl⟩, ?_,
    proj n K (g₂ : SpecialLinearGroup (Fin n) K), ⟨g₂, g₂.2, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [fieldAut_proj, c.sig_eq_of_fixed hf₁]
  · rw [fieldAut_proj, c.sig_eq_of_fixed hf₂]
  · exact hsq s₁ g₁ (c.Φ.apply_symm_apply s₁) (tvSL_sq i j hij)
  · exact hsq s₂ g₂ (c.Φ.apply_symm_apply s₂) (tvSL_sq j i hij.symm)
  · intro hcomm
    have h1 : proj n K ((g₂ : SpecialLinearGroup (Fin n) K) * g₁) =
        proj n K ((g₁ : SpecialLinearGroup (Fin n) K) * g₂) := by
      rw [map_mul, map_mul]
      exact hcomm.symm
    have h2 := proj_eq_proj_iff.mp h1
    set z : ↥R.B' := (g₂ * g₁)⁻¹ * (g₁ * g₂) with hz
    have hzc : (z : SpecialLinearGroup (Fin n) K) ∈
        Subgroup.center (SpecialLinearGroup (Fin n) K) := by
      rw [← scalars_eq_center]
      exact h2
    have hzφ : c.Φ z ∈ Subgroup.center (SpecialLinearGroup (Fin m) K) := by
      rw [Subgroup.mem_center_iff]
      intro t
      obtain ⟨q, rfl⟩ := c.Φ.surjective t
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp hzc (q : SpecialLinearGroup (Fin n) K))
    have hg12 : g₁ * g₂ = g₂ * g₁ * z := by
      rw [hz]
      group
    have hs12 : s₁ * s₂ = s₂ * s₁ * c.Φ z := by
      have := congrArg c.Φ hg12
      rw [map_mul, map_mul, map_mul, hg₁, hg₂, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply] at this
      exact this
    obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hzφ
    have hmat : ((s₁ * s₂ : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) =
        r • ((s₂ * s₁ : SpecialLinearGroup (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
      rw [hs12, Matrix.SpecialLinearGroup.coe_mul, ← hrz, Matrix.scalar_apply,
        ← Matrix.smul_eq_mul_diagonal]
    have hr0 : r = 0 := tvSL_comm_ne i j hij hmat
    rw [hr0, Fintype.card_fin, zero_pow (by omega)] at hr
    exact zero_ne_one hr

include c in
theorem model [Finite K] [CharP K 2] {f₀ : ℕ} (hK4 : 4 ≤ Nat.card K)
    (hKcard : Nat.card K = 2 ^ (p * f₀)) (hf₀ : 1 ≤ f₀) (hp0 : 1 ≤ p) :
    ∃ (t' : CFSG.Assembly.LowTwoRank.StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
      CFSG.Blueprint.LieModel (↥R.D ⧸ Subgroup.center ↥R.D) t' n' 2 (p * f') := by
  have hm := c.hm2
  have hpf : 1 ≤ p * f₀ := Nat.mul_pos hp0 hf₀
  let f : ↥R.B' →* ↥R.D :=
    ((proj n K).comp R.B'.subtype).codRestrict R.D (fun g => ⟨g, g.2, rfl⟩)
  have hf : Function.Surjective f := by
    rintro ⟨_, g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  have hker : f.ker ≤ Subgroup.center ↥R.B' := by
    intro g hg
    have h1 : proj n K (g : SpecialLinearGroup (Fin n) K) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
    have h2 : (g : SpecialLinearGroup (Fin n) K) ∈
        Subgroup.center (SpecialLinearGroup (Fin n) K) := by
      rw [← scalars_eq_center n K]
      exact proj_eq_one_iff.mp h1
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (Subgroup.mem_center_iff.mp h2 (h : SpecialLinearGroup (Fin n) K))
  obtain ⟨e₂⟩ := nonempty_centerQuotientEquiv_of_surjective (R.B'_perfect hK4) f hf hker
  let e₃ : ↥R.B' ⧸ Subgroup.center ↥R.B' ≃*
      SpecialLinearGroup (Fin m) K ⧸ Subgroup.center (SpecialLinearGroup (Fin m) K) :=
    QuotientGroup.congr _ _ c.Φ (Subgroup.map_center_eq c.Φ)
  let e₄ : SpecialLinearGroup (Fin m) K ⧸ Subgroup.center (SpecialLinearGroup (Fin m) K) ≃*
      projectiveSL m K :=
    QuotientGroup.quotientMulEquivOfEq (scalars_eq_center m K).symm
  let e : ↥R.D ⧸ Subgroup.center ↥R.D ≃* projectiveSL m K := e₂.symm.trans (e₃.trans e₄)
  have hpow : 4 ≤ 2 ^ (p * f₀) := hKcard ▸ hK4
  refine ⟨.PSL, m, f₀, hf₀, ?_⟩
  exact (CFSG.RankThree.PartOne.Sec66T.lieModel_classical_iff (by decide)).mpr
    ⟨⟨Nat.prime_two, hpf, hm, fun hc => by have := (Prod.mk.inj hc).2; omega,
        fun hc => by have := (Prod.mk.inj hc).2; omega⟩,
      K, inferInstance, inferInstance, hKcard,
      ⟨e.trans ((projectiveSpecialLinearEquivProjectiveSL m K).symm.trans
        (projectiveSpecialLinearGroupEquivStatedProj m K))⟩⟩

end BlockCoordData

theorem toGL_map_sl (g : SpecialLinearGroup (Fin n) K) :
    SpecialLinearGroup.toGL (SpecialLinearGroup.map σ.toRingHom g) =
      GeneralLinearGroup.map (n := Fin n) σ.toRingHom (SpecialLinearGroup.toGL g) :=
  Units.ext rfl

@[expose] noncomputable def eqv [Finite K] (hK4 : 4 ≤ Nat.card K) : ↥R.B' ≃* ↥R.blk :=
  (Subgroup.equivMapOfInjective R.B' SpecialLinearGroup.toGL
    SpecialLinearGroup.toGL_injective).trans (MulEquiv.subgroupCongr (R.B'_map hK4))

theorem coe_eqv [Finite K] (hK4 : 4 ≤ Nat.card K) (g : ↥R.B') :
    ((R.eqv hK4 g : ↥R.blk) : GL (Fin n) K) =
      SpecialLinearGroup.toGL (g : SpecialLinearGroup (Fin n) K) := rfl

theorem exists_coordData [Finite K] [CharP K 2] (hp : Odd p) (hK4 : 4 ≤ Nat.card K)
    (hσA : (A : Matrix (Fin n) (Fin n) K).map σ = A) :
    ∃ m : ℕ, Nonempty (BlockCoordData R m) := by
  have hσa : ((SpecialLinearGroup.toGL A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ =
      (SpecialLinearGroup.toGL A : GL (Fin n) K) := hσA
  have hap : (SpecialLinearGroup.toGL A) ^ p =
      GeneralLinearGroup.scalar (Fin n) (R.γ ^ p) := by
    rw [R.hγ]
    exact R.hap
  obtain ⟨m, C, Φ, -, hm2, -, hΦσ⟩ := exists_blockCoord hp σ hap hσa R.hσγ (x := slX A) rfl
    R.hsq hK4 R.b₀ R.hb₀ R.hm2
  refine ⟨m, ⟨⟨(R.eqv hK4).trans Φ, hm2, ?_, ?_⟩⟩⟩
  · intro g hg
    rw [mem_B', toGL_map_sl]
    exact map_mem_blockImage σ hσa R.hsq hK4 R.hm2 R.huniq (R.mem_B'.mp hg)
  · intro g g' hgg
    apply hΦσ
    change ((SpecialLinearGroup.toGL (g' : SpecialLinearGroup (Fin n) K) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = ((SpecialLinearGroup.toGL
        (g : SpecialLinearGroup (Fin n) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ
    rw [hgg]
    rfl

end PSLBlock

theorem psl_good_conclusion {n p f₀ : ℕ} [NeZero n] {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hp5 : 5 ≤ p) (hf₀ : 1 ≤ f₀) (hK : Nat.card K = 2 ^ (p * f₀))
    (hpK : ¬ p ∣ Nat.card Kˣ) (hrank : CFSG.pRank p (projectiveSL n K) ≤ 1) {σ : K ≃+* K}
    (hσ1 : σ ≠ 1) {A : SpecialLinearGroup (Fin n) K}
    (hσA : (A : Matrix (Fin n) (Fin n) K).map σ = A) {y : projectiveSL n K}
    (hxp : (proj n K A) ^ p = 1) (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1)
    (hxy : proj n K A * y = y * proj n K A) :
    GoodConclusion p (projectiveSL n K) (fieldAut n K σ) (proj n K A) := by
  have hp2 : p ≠ 2 := by omega
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (p * f₀) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  obtain ⟨R⟩ := psl_block_exists hp hp2 hpK hrank σ hσA hxp hy2 hy1 hxy
  obtain ⟨m, ⟨c⟩⟩ := R.exists_coordData (hp.odd_of_ne_two hp2) hK4 hσA
  have hQ : ∀ _ : Unit,
      IsComponentOf (Subgroup.centralizer ({proj n K A} : Set (projectiveSL n K))) R.D :=
    fun _ => R.isComponent hK4
  have hsolv : Group.IsSolvable ↥(Subgroup.centralizer ({proj n K A} : Set (projectiveSL n K)) ⊓
      Subgroup.centralizer ((⨆ _ : Unit, R.D : Subgroup (projectiveSL n K)) :
        Set (projectiveSL n K))) := by
    rw [iSup_const]
    refine Group.isSolvable_of_comm fun u v => Subtype.ext ?_
    obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp u.2
    exact R.comm_of_centralizer_D hp hpK hK4 hu1 hu2 (Subgroup.mem_inf.mp v.2).1
  have hlayer := inSubgroup_layer_eq_of_decomposition (fun _ : Unit => R.D) hQ hsolv
  rw [iSup_const] at hlayer
  refine ⟨⟨R.D, R.isComponent hK4⟩, fun E hE _ => ?_, fun g hg _ hg2 => ?_⟩
  · obtain ⟨_, rfl⟩ := isComponentOf_eq_of_decomposition (fun _ : Unit => R.D) hQ hsolv hE
    exact ⟨c.outer hK4 hσ1, c.model hK4 hK hf₀ hp.one_lt.le, c.pair⟩
  · rw [hlayer]
    exact R.two_mem hp hpK hK4 hg hg2

open scoped _root_.Classical in
theorem psl_two_vacuous {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x y : projectiveSL 2 K} (hxp : x ^ p = 1) (hx1 : x ≠ 1) (hy2 : y ^ 2 = 1)
    (hy1 : y ≠ 1) (hxy : x * y = y * x) : False := by
  obtain ⟨A, rfl⟩ := proj_surjective 2 K x
  obtain ⟨b, hb⟩ := exists_mult_two_PSL hp hp2 hxp hy2 hy1 hxy
  obtain ⟨c, -, hap⟩ := exists_pow_scalar hxp
  have hpK' : (p : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm
  have hsq := squarefree_minpoly_toLin'_of_pow_scalar hpK' hap
  have hirr : Irreducible (b : K[X]) := irreducible_of_mem_primaryFactors b.2
  have : Fact (Irreducible (b : K[X])) := ⟨hirr⟩
  have hdeg : 1 ≤ (b : K[X]).natDegree := hirr.natDegree_pos
  have hfin : Module.finrank K (primaryComponent (slX A) (b : K[X])) =
      (b : K[X]).natDegree * mult (slX A) b := finrank_primaryComponent (slX A) (b : K[X])
  have hle : Module.finrank K (primaryComponent (slX A) (b : K[X])) ≤ 2 := by
    simpa using Submodule.finrank_le (primaryComponent (slX A) (b : K[X]))
  have hdeg1 : (b : K[X]).natDegree = 1 := by nlinarith
  have htop : primaryComponent (slX A) (b : K[X]) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa using le_antisymm hle (by nlinarith)
  obtain ⟨μ, hμ⟩ : ∃ μ : K, (b : K[X]) = X - C μ := by
    refine ⟨-(b : K[X]).coeff 0, ?_⟩
    rw [map_neg, sub_neg_eq_add]
    exact (monic_of_mem_primaryFactors b.2).eq_X_add_C hdeg1
  have hall : ∀ v : Fin 2 → K, (A : Matrix (Fin 2) (Fin 2) K).mulVec v = μ • v := by
    intro v
    have hv : v ∈ primaryComponent (slX A) (b : K[X]) := by rw [htop]; trivial
    rw [hμ, mem_primaryComponent] at hv
    have h1 : (Polynomial.aeval (slX A) (X - C μ)) v =
        ((SpecialLinearGroup.toGL A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec v -
          μ • v := by
      simp [slX, Matrix.toLin'_apply', Module.algebraMap_end_apply]
    rw [h1, sub_eq_zero] at hv
    exact hv
  have hAμ : (A : Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) μ := by
    ext i j
    have := congrFun (hall (Pi.single j 1)) i
    simpa [Matrix.scalar_apply, Matrix.diagonal_apply, Pi.single_apply, eq_comm] using this
  have hμ2 : μ ^ Fintype.card (Fin 2) = 1 := by
    have hdet := A.2
    rw [hAμ] at hdet
    simpa [Matrix.scalar_apply, Matrix.det_diagonal] using hdet
  apply hx1
  apply proj_eq_one_iff.mpr
  rw [scalars_eq_center]
  exact Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨μ, hμ2, hAμ.symm⟩

theorem lieGoodComponentFixT_PSL : LieGoodComponentFixT .PSL := by
  intro T _ _ p hp hp5 _ hrank n f₀ hf₀ hM α hαp hαinn _ _ x hxp hx1 hαx y hy2 hy1 hxy
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hn2, K, _, _, _, hK, ⟨e⟩⟩ := exists_equiv_projectiveSL hM
  have : Fact p.Prime := ⟨hp⟩
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · obtain rfl : n = 2 := by omega
    exfalso
    refine psl_two_vacuous hp hp2 (x := e x) (y := e y) ?_ ?_ ?_ ?_ ?_
    · rw [← map_pow, hxp, map_one]
    · exact fun h => hx1 (e.injective (by rw [h, map_one]))
    · rw [← map_pow, hy2, map_one]
    · exact fun h => hy1 (e.injective (by rw [h, map_one]))
    · rw [← map_mul, ← map_mul, hxy]
  · have : NeZero n := ⟨by omega⟩
    have hpq : ¬ p ∣ 2 ^ (p * f₀) - 1 := by
      intro hd
      have h2 := two_le_pRank_projectiveSL (K := K) hn3 hp (by omega)
        (by rw [Nat.card_units, hK]; exact hd)
      have h1 : CFSG.pRank p (projectiveSL n K) = 1 := by
        rw [← hrank]
        exact (pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e).symm
      omega
    obtain ⟨K', _, _, _, hK', φ, σ, hσord, -, hφα⟩ :=
      exists_fieldAut_model_PSL hp hp5 hn3 hM hf₀ hpq α hαp hαinn
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hσord
      exact hp.one_lt.ne hσord
    have hpK' : ¬ p ∣ Nat.card K'ˣ := by
      rw [Nat.card_units, hK']
      exact hpq
    have hrank' : CFSG.pRank p (projectiveSL n K') ≤ 1 := by
      rw [← pRank_eq_of_mulEquiv_of_one_lt hp.one_lt φ]
      exact hrank.le
    have hfix : fieldAut n K' σ (φ x) = φ x := by
      rw [← hφα]
      simp [MulAut.congr_apply, hαx]
    have hmem : φ x ∈ ((linearSubfieldInclusion n (semilinearFixedSubfield σ)).range :
        Set (projectiveSL n K')) := by
      rw [← fixed_eq_range_PSL hp hp5 hn3 hf₀ hK' hpq σ hσord]
      exact hfix
    obtain ⟨A, hA, hAx⟩ := mem_range_linearSubfieldInclusion.mp (SetLike.mem_coe.mp hmem)
    have hσA : (A : Matrix (Fin n) (Fin n) K').map σ = A := by
      ext i j
      exact hA i j
    have hxp' : (proj n K' A) ^ p = 1 := by rw [hAx, ← map_pow, hxp, map_one]
    have hy2' : (φ y) ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
    have hy1' : φ y ≠ 1 := fun h => hy1 (φ.injective (by rw [h, map_one]))
    have hxy' : proj n K' A * φ y = φ y * proj n K' A := by
      rw [hAx, ← map_mul, ← map_mul, hxy]
    have key := psl_good_conclusion hp hp5 hf₀ hK' hpK' hrank' hσ1 hσA hxp' hy2' hy1' hxy'
    rw [hAx, ← hφα] at key
    exact GoodConclusion.of_mulEquiv φ α x key

end CFSG.RankThree.PartOne
