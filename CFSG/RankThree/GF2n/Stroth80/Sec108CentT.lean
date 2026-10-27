module

public import CFSG.RankThree.GF2n.Stroth80.Sec108Cent
public import CFSG.RankThree.GF2n.Stroth80.Sec108Std
public import CFSG.LocalAnalysis.ComponentInitial.ScalarSemilinearNormalizer
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Mod
public import CFSG.Quasithin.Vol2.Ch11SecAKA6

public section

namespace CFSG.RankThree.GF2n.Stroth80.Sec108

open CFSG CFSG.Open Matrix
open scoped commutatorElement

variable {𝓜 : Type} [Group 𝓜] [Finite 𝓜] {K : Type} [Field K] [Finite K] [CharP K 2]
  {L R N Y : Subgroup 𝓜} {ρ : ↥R →* GL (Fin 3) K} {μ : ↥N →* Multiplicative (Fin 3 → K)}
  {T : ↥(NLY L Y) →* AddMonoid.End (Fin 3 → K)}

private noncomputable def Tsigma (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NLY L Y)) : K ≃+* K :=
  Classical.choose (hC.T_semilinear g)

private theorem T_smul (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NLY L Y)) (c : K)
    (v : Fin 3 → K) : T g (c • v) = Tsigma hC g c • T g v :=
  (Classical.choose_spec (hC.T_semilinear g)) c v

private noncomputable def Tmat (T : ↥(NLY L Y) →* AddMonoid.End (Fin 3 → K))
    (g : ↥(NLY L Y)) : Matrix (Fin 3) (Fin 3) K :=
  fun i j => T g (Pi.single j 1) i

private def q3 (w : Fin 2 → K) : Fin 3 → K
  | 0 => 0
  | 1 => w 0
  | 2 => w 1

private def p3 (v : Fin 3 → K) : Fin 2 → K := fun i => v i.succ

private theorem q3_succ (w : Fin 2 → K) (i : Fin 2) : q3 w i.succ = w i := by
  fin_cases i <;> rfl

private theorem q3_zero : q3 (0 : Fin 2 → K) = 0 := by
  funext i
  fin_cases i <;> rfl

private def u3 (a b : K) : Fin 3 → K
  | 0 => 0
  | 1 => a
  | 2 => b

private noncomputable def Tblock (T : ↥(NLY L Y) →* AddMonoid.End (Fin 3 → K))
    (g : ↥(NLY L Y)) : Matrix (Fin 2) (Fin 2) K :=
  fun i j => Tmat T g i.succ j.succ

private theorem split_vec (v : Fin 3 → K) :
    v = v 0 • (Pi.single 0 (1 : K) : Fin 3 → K) + q3 (p3 v) := by
  funext i
  fin_cases i <;> simp [q3, p3]

private theorem T_q3 (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NLY L Y)) (σ : K ≃+* K)
    (hσ : ∀ (c : K) (v : Fin 3 → K), T g (c • v) = σ c • T g v) (w : Fin 2 → K) :
    T g (q3 w) = (∑ j : Fin 2, Tmat T g 0 j.succ * σ (w j)) •
        (Pi.single 0 (1 : K) : Fin 3 → K) +
      q3 (Tblock T g *ᵥ fun j => σ (w j)) := by
  have h : q3 w = ∑ j : Fin 2, w j • (Pi.single j.succ (1 : K) : Fin 3 → K) := by
    funext i
    fin_cases i <;> simp [q3, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h]
  rw [map_sum]
  have h1 : (∑ x, (T g) (w x • (Pi.single x.succ (1 : K) : Fin 3 → K))) =
      ∑ x, σ (w x) • ((T g) (Pi.single x.succ (1 : K) : Fin 3 → K)) :=
    Finset.sum_congr rfl fun x _ => hσ (w x) (Pi.single x.succ (1 : K))
  rw [h1]
  funext i
  fin_cases i <;>
    simp [Tblock, Tmat, q3, Matrix.mulVec, Fin.sum_univ_two, Finset.sum_apply, mul_comm]

private theorem T_mul_inv (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NLY L Y)) :
    T g * T g⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

private theorem T_inv_mul (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NLY L Y)) :
    T g⁻¹ * T g = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

private theorem T_leftInverse (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NLY L Y)) :
    Function.LeftInverse (T g⁻¹) (T g) := by
  intro x
  have h := congrArg (fun f : AddMonoid.End (Fin 3 → K) => (⇑f) x) (T_inv_mul hC g)
  simpa [AddMonoid.End.coe_mul, AddMonoid.End.coe_one] using h

private theorem T_injective (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NLY L Y)) :
    Function.Injective (T g) := by
  intro a b hab
  calc a = T g⁻¹ (T g a) := (T_leftInverse hC g a).symm
    _ = T g⁻¹ (T g b) := by rw [hab]
    _ = b := T_leftInverse hC g b

private theorem T_surjective (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NLY L Y)) :
    Function.Surjective (T g) := by
  intro x
  refine ⟨T g⁻¹ x, ?_⟩
  have h := congrArg (fun f : AddMonoid.End (Fin 3 → K) => (⇑f) x) (T_mul_inv hC g)
  simpa [AddMonoid.End.coe_mul, AddMonoid.End.coe_one] using h

private theorem Tmat_col_zero (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NLY L Y)) :
    Tmat T g 1 0 = 0 ∧ Tmat T g 2 0 = 0 := by
  obtain ⟨c, hc⟩ := hC.T_line g
  constructor
  · simpa [Tmat, e₀, Pi.single_apply] using congrFun hc (1 : Fin 3)
  · simpa [Tmat, e₀, Pi.single_apply] using congrFun hc (2 : Fin 3)

private theorem T_e0 (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NLY L Y)) :
    T g (e₀ K) = Tmat T g 0 0 • e₀ K := by
  obtain ⟨c, hc⟩ := hC.T_line g
  have h0 : Tmat T g 0 0 = c := by simpa [Tmat, e₀] using congrFun hc 0
  rw [hc, h0]

private def mkN (L Y : Subgroup 𝓜) : ↥(NLY L Y) →* GG L :=
  (mkG L).comp (Subgroup.inclusion (inf_le_left : NLY L Y ≤ NL L))

private theorem mkN_apply (L Y : Subgroup 𝓜) (g : ↥(NLY L Y)) :
    mkN L Y g = mkG L ⟨(g : 𝓜), g.2.1⟩ := rfl

private theorem conj_mem_L (hC : Levi108 K L R N Y ρ μ T) {g₀ r : ↥(NL L)}
    (hcomm : mkG L g₀ * mkG L r = mkG L r * mkG L g₀) :
    ((g₀ * r * g₀⁻¹ * r⁻¹ : ↥(NL L)) : 𝓜) ∈ L := by
  have hker : mkG L (g₀ * r * g₀⁻¹ * r⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have hx : (g₀ * r * g₀⁻¹ * r⁻¹ : ↥(NL L)) ∈ (mkG L).ker := MonoidHom.mem_ker.mpr hker
  rwa [QuotientGroup.ker_mk'] at hx

private theorem T_conj_eq (hC : Levi108 K L R N Y ρ μ T) {g r x : ↥(NLY L Y)}
    (h : T (g * r * g⁻¹ * r⁻¹) = T x) : T g * T r = T x * T r * T g := by
  have h1 : T g * T r * T g⁻¹ * T r⁻¹ = T x := by
    rw [← h]
    simp only [map_mul]
  have h2 : T g * T r * T g⁻¹ = T x * T r := by
    have := congrArg (fun y => y * T r) h1
    simpa [mul_assoc, T_inv_mul hC r] using this
  have h3 : T g * T r = T x * T r * T g := by
    have := congrArg (fun y => y * T g) h2
    simpa [mul_assoc, T_inv_mul hC g] using this
  exact h3

private theorem mulVec_q3 (M : Matrix (Fin 3) (Fin 3) K) (A : Matrix (Fin 2) (Fin 2) K)
    (h10 : M 1 0 = 0) (h20 : M 2 0 = 0)
    (hblock : ∀ i j : Fin 2, M i.succ j.succ = A i j) (w : Fin 2 → K) :
    M *ᵥ q3 w = (∑ j : Fin 2, M 0 j.succ * w j) • e₀ K + q3 (A *ᵥ w) := by
  have h11 : M 1 1 = A 0 0 := by simpa using hblock 0 0
  have h12 : M 1 2 = A 0 1 := by simpa using hblock 0 1
  have h21 : M 2 1 = A 1 0 := by simpa using hblock 1 0
  have h22 : M 2 2 = A 1 1 := by simpa using hblock 1 1
  funext i
  fin_cases i <;>
    simp [e₀, q3, Matrix.mulVec, Fin.sum_univ_three, Fin.sum_univ_two, Pi.single_apply,
      h10, h20, h11, h12, h21, h22, Finset.sum_apply, dotProduct]

private theorem mulVec_q3_add (M : Matrix (Fin 3) (Fin 3) K) (A : Matrix (Fin 2) (Fin 2) K)
    (h00 : M 0 0 = 1) (h10 : M 1 0 = 0) (h20 : M 2 0 = 0)
    (hblock : ∀ i j : Fin 2, M i.succ j.succ = A i j) (c : K) (w : Fin 2 → K) :
    M *ᵥ (c • e₀ K + q3 w) =
      (c * M 0 0 + ∑ j : Fin 2, M 0 j.succ * w j) • e₀ K + q3 (A *ᵥ w) := by
  have hcol : M *ᵥ e₀ K = e₀ K := by
    funext i
    fin_cases i <;> simp [e₀, Matrix.mulVec, Fin.sum_univ_three, Pi.single_apply, h00, h10, h20]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hcol, mulVec_q3 M A h10 h20 hblock w, ← add_assoc,
    ← add_smul, h00, mul_one]

private theorem transvection_q3 (u : Fin 3 → K) (hu0 : u 0 = 0) (c : K) (v : Fin 2 → K) :
    (1 + Matrix.vecMulVec (e₀ K) u : Matrix (Fin 3) (Fin 3) K) *ᵥ (c • e₀ K + q3 v) =
      (c + ∑ j : Fin 2, u j.succ * v j) • e₀ K + q3 v := by
  funext i
  fin_cases i <;>
    simp [e₀, q3, Matrix.mulVec, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.one_apply, Matrix.vecMulVec, Pi.single_apply, hu0, dotProduct]
  ring

private theorem p3_T (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NLY L Y))
    (σ : K ≃+* K) (hσ : ∀ (c : K) (v : Fin 3 → K), T g (c • v) = σ c • T g v)
    (c : K) (v : Fin 2 → K) :
    p3 (T g (c • e₀ K + q3 v)) = Tblock T g *ᵥ fun j => σ (v j) := by
  rw [map_add, hσ, T_e0 hC g]
  have hzero : p3 (σ c • (Tmat T g 0 0 • e₀ K) + T g (q3 v)) =
      p3 (T g (q3 v)) := by
    funext i
    simp [p3, e₀, Pi.smul_apply, Pi.add_apply, Pi.single_apply]
  rw [hzero, T_q3 hC g σ hσ v]
  funext i
  simp only [p3, Pi.add_apply, Pi.smul_apply, q3_succ, e₀, Pi.single_apply, Fin.succ_ne_zero,
    if_false, smul_zero, zero_add]

private theorem p3_transvection (hC : Levi108 K L R N Y ρ μ T) {x : ↥(NLY L Y)}
    (hxL : (x : 𝓜) ∈ L) (c : K) (v : Fin 2 → K) :
    p3 (T x (c • e₀ K + q3 v)) = v := by
  obtain ⟨u, hu0, hu⟩ := hC.rho_L (x : 𝓜) hxL
  have hxR : (x : 𝓜) ∈ R := hC.L_le_R hxL
  rw [hC.T_rho x hxR, hu, transvection_q3 u hu0 c v]
  funext i
  simp [p3, q3_succ, e₀, Pi.smul_apply, Pi.add_apply, Pi.single_apply]

private theorem block_vec (hC : Levi108 K L R N Y ρ μ T) {g : ↥(NLY L Y)} {g₀ : ↥(NL L)}
    (hg₀ : (g : 𝓜) = (g₀ : 𝓜))
    (hcent : ∀ x ∈ Xlevi L R, mkG L g₀ * x = x * mkG L g₀)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) (w : Fin 2 → K) :
    Tblock T g *ᵥ (fun j => Tsigma hC g ((A.1 *ᵥ w) j)) =
      A.1 *ᵥ (Tblock T g *ᵥ fun j => Tsigma hC g (w j)) := by
  obtain ⟨r, hrX, hrR, hrblock⟩ := hC.exists_Xlevi_block A
  have hrP0 : mkG L r ∈ P0frak L R := Xlevi_le_P0frak L R hrX
  have h00 : (ρ ⟨(r : 𝓜), hrR⟩ : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 :=
    (hC.mem_P0frak_iff r hrR).mp hrP0
  have h10 : (ρ ⟨(r : 𝓜), hrR⟩ : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 :=
    ((hC.mem_normalizer_iff (r : 𝓜) hrR).mp r.2).1
  have h20 : (ρ ⟨(r : 𝓜), hrR⟩ : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 :=
    ((hC.mem_normalizer_iff (r : 𝓜) hrR).mp r.2).2
  let r' : ↥(NLY L Y) := ⟨(r : 𝓜), ⟨r.2, hC.R_le_normalizer_Y hrR⟩⟩
  let x : ↥(NLY L Y) := g * r' * g⁻¹ * r'⁻¹
  have hxLm : ((g₀ * r * g₀⁻¹ * r⁻¹ : ↥(NL L)) : 𝓜) ∈ L :=
    conj_mem_L hC (hcent (mkG L r) hrX)
  have hx_val : (x : 𝓜) = ((g₀ * r * g₀⁻¹ * r⁻¹ : ↥(NL L)) : 𝓜) := by
    simp only [x, r', Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hg₀]
  have hxL : (x : 𝓜) ∈ L := by rw [hx_val]; exact hxLm
  have hmap : T g * T r' = T x * T r' * T g := by
    refine T_conj_eq hC (x := x) ?_
    rw [show x = g * r' * g⁻¹ * r'⁻¹ from rfl]
  have hvec : T g (T r' (q3 w)) = T x (T r' (T g (q3 w))) := by
    have h := congrArg (fun f : AddMonoid.End (Fin 3 → K) => (⇑f) (q3 w)) hmap
    simpa [AddMonoid.End.coe_mul] using h
  have hLHS : p3 (T g (T r' (q3 w))) =
      Tblock T g *ᵥ (fun j => Tsigma hC g ((A.1 *ᵥ w) j)) := by
    rw [hC.T_rho r' hrR,
      mulVec_q3 (ρ ⟨(r' : 𝓜), hrR⟩ : Matrix (Fin 3) (Fin 3) K) A.1 h10 h20 hrblock w]
    simpa using p3_T hC g (Tsigma hC g) (T_smul hC g)
      (∑ j : Fin 2, (ρ ⟨(r : 𝓜), hrR⟩ : Matrix (Fin 3) (Fin 3) K) 0 j.succ * w j)
      (A.1 *ᵥ w)
  have hRHS : p3 (T x (T r' (T g (q3 w)))) =
      A.1 *ᵥ (Tblock T g *ᵥ fun j => Tsigma hC g (w j)) := by
    rw [hC.T_rho r' hrR, T_q3 hC g (Tsigma hC g) (T_smul hC g) w,
      mulVec_q3_add (ρ ⟨(r' : 𝓜), hrR⟩ : Matrix (Fin 3) (Fin 3) K) A.1 h00 h10 h20 hrblock
        (∑ j : Fin 2, Tmat T g 0 j.succ * Tsigma hC g (w j))
        (fun j => (Tblock T g *ᵥ fun k => Tsigma hC g (w k)) j)]
    exact p3_transvection hC hxL _ _
  have h := congrArg p3 hvec
  rw [hLHS, hRHS] at h
  exact h

private theorem block_vec' (hC : Levi108 K L R N Y ρ μ T) {g : ↥(NLY L Y)} {g₀ : ↥(NL L)}
    (hg₀ : (g : 𝓜) = (g₀ : 𝓜))
    (hcent : ∀ x ∈ Xlevi L R, mkG L g₀ * x = x * mkG L g₀)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K) :
    (Tblock T g * Matrix.of (fun i j => Tsigma hC g (A.1 i j))) *ᵥ v =
      A.1 *ᵥ (Tblock T g *ᵥ v) := by
  have h := block_vec hC hg₀ hcent A (fun k => (Tsigma hC g).symm (v k))
  have h1 : (fun j => Tsigma hC g
        ((A.1 *ᵥ (fun k => (Tsigma hC g).symm (v k))) j)) =
      Matrix.of (fun i j => Tsigma hC g (A.1 i j)) *ᵥ v := by
    funext j
    simp [Matrix.mulVec, Matrix.of_apply, map_sum, map_mul, Finset.sum_apply]
  have h2 : (fun j => Tsigma hC g ((fun k => (Tsigma hC g).symm (v k)) j)) = v := by
    funext j
    exact (Tsigma hC g).apply_symm_apply (v j)
  rw [h1, h2, Matrix.mulVec_mulVec] at h
  exact h

private theorem block_comm (hC : Levi108 K L R N Y ρ μ T) {g : ↥(NLY L Y)} {g₀ : ↥(NL L)}
    (hg₀ : (g : 𝓜) = (g₀ : 𝓜))
    (hcent : ∀ x ∈ Xlevi L R, mkG L g₀ * x = x * mkG L g₀)
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    Tblock T g * Matrix.of (fun i j => Tsigma hC g (A.1 i j)) = A.1 * Tblock T g := by
  ext i j
  have h := block_vec' hC hg₀ hcent A (Pi.single j 1)
  simpa [Matrix.mulVec, Matrix.mul_apply, Matrix.col, Finset.sum_apply] using congrFun h i

private theorem Tsigma_eq_one (hC : Levi108 K L R N Y ρ μ T) {g : ↥(NLY L Y)} {g₀ : ↥(NL L)}
    (hg₀ : (g : 𝓜) = (g₀ : 𝓜))
    (hcent : ∀ x ∈ Xlevi L R, mkG L g₀ * x = x * mkG L g₀) :
    ∀ c, Tsigma hC g c = c := by
  by_contra hne
  have hσ : Tsigma hC g ≠ 1 := fun h1 => hne fun c => by rw [h1]; rfl
  let Φ : (Fin 2 → K) →+ (Fin 2 → K) :=
    { toFun := fun v => Tblock T g *ᵥ fun j => Tsigma hC g (v j)
      map_zero' := by simp [Matrix.mulVec]
      map_add' := fun a b => by rw [← Matrix.mulVec_add]; congr 1; funext j; simp }
  have hΦσ : ∀ (c : K) (v : Fin 2 → K), Φ (c • v) = Tsigma hC g c • Φ v := by
    intro c v
    show Tblock T g *ᵥ (fun j => Tsigma hC g (c * v j)) =
      Tsigma hC g c • (Tblock T g *ᵥ fun j => Tsigma hC g (v j))
    rw [show (fun j => Tsigma hC g (c * v j)) = Tsigma hC g c • (fun j => Tsigma hC g (v j))
      by funext j; simp [map_mul], Matrix.mulVec_smul]
  have hΦSL : ∀ (B : Matrix.SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
      Φ (B.1 *ᵥ v) = B.1 *ᵥ Φ v := fun B v => block_vec hC hg₀ hcent B v
  have hΦ0 : Φ = 0 :=
    CFSG.GH74.GLS.IVK.sl2_semilinear_commutant_zero (Tsigma hC g) hσ Φ hΦσ hΦSL
  have hM0 : Tblock T g = 0 := by
    ext i j
    have hΦe : Φ (Pi.single j (1 : K)) = Tblock T g *ᵥ Pi.single j (1 : K) := by
      show Tblock T g *ᵥ (fun k => Tsigma hC g ((Pi.single j (1 : K) : Fin 2 → K) k)) = _
      congr 1
      funext k
      simp [Pi.single_apply]
    have h := congrFun (congrArg (fun f : (Fin 2 → K) →+ (Fin 2 → K) =>
      f (Pi.single j 1)) hΦ0) i
    rw [hΦe, Matrix.mulVec_single_one, Matrix.col] at h
    exact h
  have hrange : ∀ v : Fin 3 → K, ∃ c : K, T g v = c • e₀ K := by
    intro v
    rw [split_vec v, map_add, T_smul hC g (v 0) (e₀ K), T_e0 hC g,
      T_q3 hC g (Tsigma hC g) (T_smul hC g) (p3 v), hM0]
    refine ⟨Tsigma hC g (v 0) * Tmat T g 0 0 +
      ∑ j : Fin 2, Tmat T g 0 j.succ * Tsigma hC g (p3 v j), ?_⟩
    rw [Matrix.zero_mulVec, q3_zero, add_zero, smul_smul, ← add_smul]
  obtain ⟨v, hv⟩ := T_surjective hC g (Pi.single 1 (1 : K))
  obtain ⟨c, hc⟩ := hrange v
  have h1 : (Pi.single 1 (1 : K) : Fin 3 → K) = c • e₀ K := by rw [← hv, hc]
  have := congrFun h1 (1 : Fin 3)
  simp [e₀, Pi.single_apply] at this

private theorem Tblock_eq_scalar (hC : Levi108 K L R N Y ρ μ T) {g : ↥(NLY L Y)}
    {g₀ : ↥(NL L)} (hg₀ : (g : 𝓜) = (g₀ : 𝓜))
    (hcent : ∀ x ∈ Xlevi L R, mkG L g₀ * x = x * mkG L g₀) :
    ∃ α : K, Tblock T g = Matrix.scalar (Fin 2) α := by
  have hσ1 := Tsigma_eq_one hC hg₀ hcent
  refine CFSG.GH74.GLS.IVK.sl2_commutant_scalar (Tblock T g) fun A => ?_
  have hσA : Matrix.of (fun i j => Tsigma hC g (A.1 i j)) = A.1 := by
    ext i j
    simp [Matrix.of_apply, hσ1]
  have h := block_comm hC hg₀ hcent A
  rwa [hσA] at h

private theorem mkG_eq_one_of_mem {x : ↥(NL L)} (hx : (x : 𝓜) ∈ L) : mkG L x = 1 := by
  have h : x ∈ (mkG L).ker := by
    rwa [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf]
  exact MonoidHom.mem_ker.mp h

private theorem L_le_NLY (hC : Levi108 K L R N Y ρ μ T) : L ≤ NLY L Y := by
  have hLc : L ≤ Subgroup.centralizer (Y : Set 𝓜) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp (hC.Y_le_centralizer hy)) l
      (hC.L_le_R hl)).symm
  exact le_inf Subgroup.le_normalizer (hLc.trans (Subgroup.centralizer_le_normalizer (Y : Set 𝓜)))

private theorem Tmat_mulVec_of_linear (hC : Levi108 K L R N Y ρ μ T) {x : ↥(NLY L Y)}
    (hx : ∀ (c : K) (v : Fin 3 → K), T x (c • v) = c • T x v) (v : Fin 3 → K) :
    T x v = Tmat T x *ᵥ v := by
  have hv : v = ∑ j : Fin 3, v j • (Pi.single j (1 : K) : Fin 3 → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  have h1 : (∑ x_1, (T x) (v x_1 • (Pi.single x_1 (1 : K) : Fin 3 → K))) =
      ∑ x_1, v x_1 • ((T x) (Pi.single x_1 (1 : K) : Fin 3 → K)) :=
    Finset.sum_congr rfl fun j _ => hx (v j) (Pi.single j (1 : K))
  rw [h1]
  ext i
  simp [Tmat, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

private theorem Tmat_mul (hC : Levi108 K L R N Y ρ μ T) {x y : ↥(NLY L Y)}
    (hx : ∀ (c : K) (v : Fin 3 → K), T x (c • v) = c • T x v)
    (hy : ∀ (c : K) (v : Fin 3 → K), T y (c • v) = c • T y v) :
    Tmat T (x * y) = Tmat T x * Tmat T y := by
  ext i j
  calc Tmat T (x * y) i j = T (x * y) (Pi.single j (1 : K)) i := rfl
    _ = (T x * T y) (Pi.single j (1 : K)) i := by rw [map_mul]
    _ = T x (T y (Pi.single j (1 : K))) i := rfl
    _ = T x (Tmat T y *ᵥ Pi.single j (1 : K)) i := by
        rw [Tmat_mulVec_of_linear hC hy]
    _ = (Tmat T x *ᵥ (Tmat T y *ᵥ Pi.single j (1 : K))) i := by
        rw [Tmat_mulVec_of_linear hC hx]
    _ = ((Tmat T x * Tmat T y) *ᵥ Pi.single j (1 : K)) i := by
        rw [Matrix.mulVec_mulVec]
    _ = (Tmat T x * Tmat T y) i j := by
        rw [Matrix.mulVec_single_one]
        rfl

private theorem ker_mkN (L Y : Subgroup 𝓜) :
    (mkN L Y).ker = L.subgroupOf (NLY L Y) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have h' : (Subgroup.inclusion (inf_le_left : NLY L Y ≤ NL L)) x ∈ (mkG L).ker :=
      MonoidHom.mem_ker.mpr h
    rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at h'
    simpa using h'
  · intro h
    rw [show mkN L Y x = mkG L ((Subgroup.inclusion (inf_le_left : NLY L Y ≤ NL L)) x)
      from rfl]
    exact mkG_eq_one_of_mem (by simpa using h)

private theorem Tmat_zero_zero_ne_zero (hC : Levi108 K L R N Y ρ μ T)
    (g : ↥(NLY L Y)) : Tmat T g 0 0 ≠ 0 := by
  intro h0
  have h1 : T g (e₀ K) = T g 0 := by rw [T_e0 hC g, h0, zero_smul, map_zero]
  have h2 : e₀ K = 0 := T_injective hC g h1
  have := congrFun h2 0
  simpa [e₀] using this

private theorem Tmat_mul_transvection_diag (hC : Levi108 K L R N Y ρ μ T)
    {g l' : ↥(NLY L Y)} {α : K}
    (hg_lin : ∀ (c : K) (v : Fin 3 → K), T g (c • v) = c • T g v)
    (hl_lin : ∀ (c : K) (v : Fin 3 → K), T l' (c • v) = c • T l' v)
    (hα : Tblock T g = Matrix.scalar (Fin 2) α)
    (hβ : Tmat T g 0 0 ≠ 0)
    (hlmat : Tmat T l' = 1 + Matrix.vecMulVec (e₀ K)
      (u3 (-(Tmat T g 0 1 * (Tmat T g 0 0)⁻¹)) (-(Tmat T g 0 2 * (Tmat T g 0 0)⁻¹)))) :
    Tmat T (g * l') =
      Matrix.diagonal (fun i : Fin 3 => if i = 0 then Tmat T g 0 0 else α) := by
  have h11 : Tmat T g 1 1 = α := by
    simpa [Tblock, Matrix.scalar_apply] using congrFun (congrFun hα 0) 0
  have h12 : Tmat T g 1 2 = 0 := by
    simpa [Tblock, Matrix.scalar_apply] using congrFun (congrFun hα 0) 1
  have h21 : Tmat T g 2 1 = 0 := by
    simpa [Tblock, Matrix.scalar_apply] using congrFun (congrFun hα 1) 0
  have h22 : Tmat T g 2 2 = α := by
    simpa [Tblock, Matrix.scalar_apply] using congrFun (congrFun hα 1) 1
  have hg0 : Tmat T g 1 0 = 0 := (Tmat_col_zero hC g).1
  have hg2 : Tmat T g 2 0 = 0 := (Tmat_col_zero hC g).2
  rw [Tmat_mul hC hg_lin hl_lin, hlmat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply, Matrix.one_apply,
      Matrix.vecMulVec, Matrix.diagonal_apply, e₀, Pi.single_apply, u3, h11, h12, h21, h22,
      hg0, hg2]
  all_goals try field_simp [hβ]
  all_goals try ring

private theorem exists_diag (hC : Levi108 K L R N Y ρ μ T) {k : GG L} (hk : k ∈ Kfrak L R) :
    ∃ (x : ↥(NLY L Y)) (β α : K), mkN L Y x = k ∧
      Tmat T x = Matrix.diagonal (fun i : Fin 3 => if i = 0 then β else α) ∧
      (∀ (c : K) (v : Fin 3 → K), T x (c • v) = c • T x v) := by
  have hN : k ∈ Nfrak L Y := Levi108.Kfrak_le_Nfrak hC hk
  obtain ⟨g₀, hg₀Y, hg₀k⟩ := Subgroup.mem_map.mp hN
  have hg₀Y' : (g₀ : 𝓜) ∈ Subgroup.normalizer (Y : Set 𝓜) := hg₀Y
  let g : ↥(NLY L Y) := ⟨(g₀ : 𝓜), g₀.2, hg₀Y'⟩
  have hg_val : (g : 𝓜) = (g₀ : 𝓜) := rfl
  have hcent : ∀ y ∈ Xlevi L R, mkG L g₀ * y = y * mkG L g₀ := by
    intro y hy
    have h := (Subgroup.mem_centralizer_iff.mp hk) y hy
    rw [hg₀k]
    exact h.symm
  have hg_lin : ∀ (c : K) (v : Fin 3 → K), T g (c • v) = c • T g v := by
    intro c v
    rw [T_smul hC g c v, Tsigma_eq_one hC hg_val hcent c]
  obtain ⟨α, hα⟩ := Tblock_eq_scalar hC hg_val hcent
  have hβ : Tmat T g 0 0 ≠ 0 := Tmat_zero_zero_ne_zero hC g
  let w : Fin 2 → K := fun j => Tmat T g 0 j.succ
  let u : Fin 3 → K := u3 (-(w 0 * (Tmat T g 0 0)⁻¹)) (-(w 1 * (Tmat T g 0 0)⁻¹))
  have hu0 : u 0 = 0 := rfl
  obtain ⟨l, hlL, hlρ⟩ := hC.exists_L u hu0
  have hlNL : l ∈ NL L := Subgroup.le_normalizer hlL
  have hlNY : l ∈ Subgroup.normalizer (Y : Set 𝓜) := (L_le_NLY hC hlL).2
  let l' : ↥(NLY L Y) := ⟨l, ⟨hlNL, hlNY⟩⟩
  have hl'_val : (l' : 𝓜) = l := rfl
  have hl'R : (l' : 𝓜) ∈ R := hC.L_le_R hlL
  have hl_lin : ∀ (c : K) (v : Fin 3 → K), T l' (c • v) = c • T l' v := by
    intro c v
    rw [hC.T_rho l' hl'R, hC.T_rho l' hl'R, Matrix.mulVec_smul]
  have hlρ' : (ρ ⟨(l' : 𝓜), hl'R⟩ : Matrix (Fin 3) (Fin 3) K) =
      1 + Matrix.vecMulVec (e₀ K) u := hlρ
  have hlmat : Tmat T l' = 1 + Matrix.vecMulVec (e₀ K) u := by
    ext i j
    rw [show Tmat T l' i j = T l' (Pi.single j (1 : K)) i from rfl, hC.T_rho l' hl'R, hlρ',
      Matrix.mulVec_single_one, Matrix.col_apply]
  refine ⟨g * l', Tmat T g 0 0, α, ?_, ?_, ?_⟩
  · rw [map_mul, show mkN L Y g = mkG L g₀ from rfl, show mkN L Y l' = 1 from ?_]
    · rw [mul_one]; exact hg₀k
    · rw [mkN_apply]
      exact mkG_eq_one_of_mem hlL
  · exact Tmat_mul_transvection_diag hC hg_lin hl_lin hα hβ hlmat
  · intro c v
    have h : T (g * l') = T g * T l' := map_mul T g l'
    rw [h]
    show T g (T l' (c • v)) = c • T g (T l' v)
    rw [hl_lin, hg_lin]

private theorem T_apply_inv_apply (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NLY L Y))
    (v : Fin 3 → K) : T g (T g⁻¹ v) = v := by
  have h := congrArg (fun f : (Fin 3 → K) →+ (Fin 3 → K) => f v) (T_mul_inv hC g)
  exact h

private theorem Tsigma_unique (hC : Levi108 K L R N Y ρ μ T) {g : ↥(NLY L Y)}
    {σ : K ≃+* K} (hσ : ∀ (c : K) (v : Fin 3 → K), T g (c • v) = σ c • T g v) :
    σ = Tsigma hC g := by
  have hfix : T g (T g⁻¹ (e₀ K)) = e₀ K := T_apply_inv_apply hC g (e₀ K)
  ext c
  have h1 : T g (c • T g⁻¹ (e₀ K)) = σ c • T g (T g⁻¹ (e₀ K)) := hσ c (T g⁻¹ (e₀ K))
  have h2 : T g (c • T g⁻¹ (e₀ K)) =
      Tsigma hC g c • T g (T g⁻¹ (e₀ K)) := T_smul hC g c (T g⁻¹ (e₀ K))
  rw [hfix] at h1 h2
  have h3 : σ c • e₀ K = Tsigma hC g c • e₀ K := h1.symm.trans h2
  have := congrFun h3 0
  simpa [e₀, Pi.smul_apply] using this

private theorem Tsigma_mul (hC : Levi108 K L R N Y ρ μ T) (a b : ↥(NLY L Y)) :
    Tsigma hC (a * b) = Tsigma hC a * Tsigma hC b := by
  refine (Tsigma_unique hC (g := a * b) (σ := Tsigma hC a * Tsigma hC b) ?_).symm
  intro c v
  rw [map_mul]
  show T a (T b (c • v)) = (Tsigma hC a * Tsigma hC b) c • T a (T b v)
  rw [T_smul hC b c v, T_smul hC a ((Tsigma hC b) c) (T b v)]
  rfl

private theorem Tsigma_one (hC : Levi108 K L R N Y ρ μ T) : Tsigma hC 1 = 1 := by
  refine (Tsigma_unique hC (g := 1) (σ := 1) ?_).symm
  intro c v
  rw [map_one]
  rfl

private noncomputable def Tsig (hC : Levi108 K L R N Y ρ μ T) :
    ↥(NLY L Y) →* RingAut K where
  toFun := Tsigma hC
  map_one' := Tsigma_one hC
  map_mul' := Tsigma_mul hC

private theorem Tsig_apply (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NLY L Y)) :
    Tsig hC g = Tsigma hC g := rfl

private theorem T_linear_of_tsig (hC : Levi108 K L R N Y ρ μ T) {g : ↥(NLY L Y)}
    (hg : Tsig hC g = 1) : ∀ (c : K) (v : Fin 3 → K), T g (c • v) = c • T g v := by
  intro c v
  rw [T_smul hC g c v, show Tsigma hC g = 1 from hg]
  rfl

private theorem Tmat_one (hC : Levi108 K L R N Y ρ μ T) :
    Tmat T (1 : ↥(NLY L Y)) = 1 := by
  ext i j
  show T 1 (Pi.single j (1 : K)) i = (1 : Matrix (Fin 3) (Fin 3) K) i j
  rw [map_one]
  simp [Pi.single_apply, Matrix.one_apply]

private theorem Tmat_det_ne_zero (hC : Levi108 K L R N Y ρ μ T) (g : ↥(NLY L Y))
    (hg : Tsig hC g = 1) : (Tmat T g).det ≠ 0 := by
  have hg' : Tsig hC g⁻¹ = 1 := by rw [map_inv, hg, inv_one]
  have hmul : Tmat T g * Tmat T g⁻¹ = 1 := by
    rw [← Tmat_mul hC (T_linear_of_tsig hC hg) (T_linear_of_tsig hC hg'), mul_inv_cancel,
      Tmat_one hC]
  have hdet : (Tmat T g).det * (Tmat T g⁻¹).det = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  intro h0
  rw [h0, zero_mul] at hdet
  exact zero_ne_one hdet

private theorem beta_mul (hC : Levi108 K L R N Y ρ μ T) {a b : ↥(NLY L Y)}
    (ha : Tsig hC a = 1) (hb : Tsig hC b = 1) :
    Tmat T (a * b) 0 0 = Tmat T a 0 0 * Tmat T b 0 0 := by
  rw [Tmat_mul hC (T_linear_of_tsig hC ha) (T_linear_of_tsig hC hb), Matrix.mul_apply,
    Fin.sum_univ_three, (Tmat_col_zero hC b).1, (Tmat_col_zero hC b).2, mul_zero, mul_zero,
    add_zero, add_zero]

private noncomputable def betaHom (hC : Levi108 K L R N Y ρ μ T) :
    ↥((Tsig hC).ker) →* Kˣ where
  toFun g := Units.mk0 (Tmat T (g : ↥(NLY L Y)) 0 0) (Tmat_zero_zero_ne_zero hC _)
  map_one' := by
    ext
    rw [Units.val_one, Units.val_mk0]
    show Tmat T (1 : ↥(NLY L Y)) 0 0 = 1
    rw [Tmat_one hC]
    rfl
  map_mul' a b := by
    ext
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0]
    exact beta_mul hC a.2 b.2

private noncomputable def detHom (hC : Levi108 K L R N Y ρ μ T) :
    ↥((Tsig hC).ker) →* Kˣ where
  toFun g := Units.mk0 (Tmat T (g : ↥(NLY L Y))).det (Tmat_det_ne_zero hC _ g.2)
  map_one' := by
    ext
    rw [Units.val_one, Units.val_mk0]
    show (Tmat T (1 : ↥(NLY L Y))).det = 1
    rw [Tmat_one hC, Matrix.det_one]
  map_mul' a b := by
    ext
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0]
    show (Tmat T ((a : ↥(NLY L Y)) * (b : ↥(NLY L Y)))).det =
      (Tmat T (a : ↥(NLY L Y))).det * (Tmat T (b : ↥(NLY L Y))).det
    rw [Tmat_mul hC (T_linear_of_tsig hC a.2) (T_linear_of_tsig hC b.2), Matrix.det_mul]

private theorem commutator_sup_sup_le {G : Type} [Group G] {P D : Subgroup G}
    (hD : D ≤ Subgroup.normalizer (P : Set G)) :
    ⁅P ⊔ D, P ⊔ D⁆ ≤ P ⊔ ⁅D, D⁆ := by
  let N : Subgroup G := P ⊔ D
  have hPN : N ≤ Subgroup.normalizer (P : Set G) := sup_le Subgroup.le_normalizer hD
  have hPnorm : (P.subgroupOf N).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPN
  let π : N →* N ⧸ (P.subgroupOf N) := QuotientGroup.mk' (P.subgroupOf N)
  have hπtop : π.range = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  have hsup : P.subgroupOf N ⊔ D.subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hkill : Subgroup.map π (P.subgroupOf N) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    rwa [QuotientGroup.ker_mk']
  have hmapD : Subgroup.map π (D.subgroupOf N) = ⊤ := by
    have htop : Subgroup.map π (P.subgroupOf N ⊔ D.subgroupOf N) = ⊤ := by
      rw [hsup, Subgroup.map_top, hπtop]
    rwa [Subgroup.map_sup, hkill, bot_sup_eq] at htop
  have hmain : Subgroup.map π ⁅P.subgroupOf N ⊔ D.subgroupOf N,
      P.subgroupOf N ⊔ D.subgroupOf N⁆ = Subgroup.map π ⁅D.subgroupOf N, D.subgroupOf N⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hsup, Subgroup.map_top, hπtop, hmapD]
  have hle : ⁅P.subgroupOf N ⊔ D.subgroupOf N, P.subgroupOf N ⊔ D.subgroupOf N⁆ ≤
      P.subgroupOf N ⊔ ⁅D.subgroupOf N, D.subgroupOf N⁆ := by
    calc ⁅P.subgroupOf N ⊔ D.subgroupOf N, P.subgroupOf N ⊔ D.subgroupOf N⁆
        ≤ Subgroup.comap π (Subgroup.map π ⁅P.subgroupOf N ⊔ D.subgroupOf N,
            P.subgroupOf N ⊔ D.subgroupOf N⁆) := Subgroup.le_comap_map π _
      _ = Subgroup.comap π (Subgroup.map π ⁅D.subgroupOf N, D.subgroupOf N⁆) := by rw [hmain]
      _ = ⁅D.subgroupOf N, D.subgroupOf N⁆ ⊔ π.ker := Subgroup.comap_map_eq π _
      _ = ⁅D.subgroupOf N, D.subgroupOf N⁆ ⊔ P.subgroupOf N := by rw [QuotientGroup.ker_mk']
      _ = P.subgroupOf N ⊔ ⁅D.subgroupOf N, D.subgroupOf N⁆ := sup_comm ..
  have e1 : Subgroup.map N.subtype (P.subgroupOf N ⊔ D.subgroupOf N) = P ⊔ D := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (show P ≤ N from le_sup_left),
      Subgroup.map_subgroupOf_eq_of_le (show D ≤ N from le_sup_right)]
  have e2 : Subgroup.map N.subtype (P.subgroupOf N ⊔ ⁅D.subgroupOf N, D.subgroupOf N⁆) =
      P ⊔ ⁅D, D⁆ := by
    rw [Subgroup.map_sup, Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le (show P ≤ N from le_sup_left),
      Subgroup.map_subgroupOf_eq_of_le (show D ≤ N from le_sup_right)]
  have h3 := Subgroup.map_mono (f := N.subtype) hle
  rw [Subgroup.map_commutator, e1, e2] at h3
  exact h3

private theorem Nfrak_le_range (hC : Levi108 K L R N Y ρ μ T) :
    Nfrak L Y ≤ (mkN L Y).range := by
  rintro x ⟨g, hg, rfl⟩
  exact ⟨⟨(g : 𝓜), g.2, Subgroup.mem_subgroupOf.mp hg⟩, rfl⟩

private theorem comap_mkN_le_ker_Tsig (hC : Levi108 K L R N Y ρ μ T)
    {J : Subgroup (GG L)} (hJ : J ≤ Nfrak L Y) (hJp : ⁅J, J⁆ = J) :
    J.comap (mkN L Y) ≤ (Tsig hC).ker := by
  have hmap : Subgroup.map (mkN L Y) (J.comap (mkN L Y)) = J := by
    rw [Subgroup.map_comap_eq, inf_eq_right]
    exact hJ.trans (Nfrak_le_range hC)
  have hJ' : Subgroup.map (mkN L Y) ⁅J.comap (mkN L Y), J.comap (mkN L Y)⁆ = J := by
    rw [Subgroup.map_commutator, hmap, hJp]
  have hcomm : ⁅J.comap (mkN L Y), J.comap (mkN L Y)⁆ ≤ (Tsig hC).ker := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K _ _)
  have hL : L.subgroupOf (NLY L Y) ≤ (Tsig hC).ker := by
    intro l hl
    rw [MonoidHom.mem_ker, Tsig_apply]
    refine (Tsigma_unique hC (g := l) (σ := 1) ?_).symm
    intro c v
    have hlL : (l : 𝓜) ∈ L := Subgroup.mem_subgroupOf.mp hl
    have hlR : (l : 𝓜) ∈ R := hC.L_le_R hlL
    calc T l (c • v) = (ρ ⟨(l : 𝓜), hlR⟩ : Matrix (Fin 3) (Fin 3) K) *ᵥ (c • v) :=
          hC.T_rho l hlR (c • v)
      _ = c • ((ρ ⟨(l : 𝓜), hlR⟩ : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := Matrix.mulVec_smul ..
      _ = c • T l v := by rw [hC.T_rho l hlR]
  intro g hg
  have hmem : mkN L Y g ∈ Subgroup.map (mkN L Y)
      ⁅J.comap (mkN L Y), J.comap (mkN L Y)⁆ := by
    rw [hJ']
    exact hg
  have hgc : g ∈ ⁅J.comap (mkN L Y), J.comap (mkN L Y)⁆ ⊔ (mkN L Y).ker := by
    rw [← Subgroup.comap_map_eq]
    exact Subgroup.mem_comap.mpr hmem
  rw [ker_mkN] at hgc
  exact sup_le hcomm hL hgc

private theorem good_commutator (hC : Levi108 K L R N Y ρ μ T) {J : Subgroup (GG L)}
    (hker : J.comap (mkN L Y) ≤ (Tsig hC).ker) :
    ⁅J.comap (mkN L Y), J.comap (mkN L Y)⁆ ≤
      (Tsig hC).ker ⊓
        (((betaHom hC).ker ⊓ (detHom hC).ker).map ((Tsig hC).ker).subtype) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hkerab : ⁅a, b⁆ ∈ (Tsig hC).ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (CFSG.LocalAnalysis.ComponentInitial.ringAut_mul_comm K _ _)
  refine ⟨hkerab, ?_⟩
  refine Subgroup.mem_map.mpr ⟨⟨⁅a, b⁆, hkerab⟩, ?_, rfl⟩
  refine ⟨?_, ?_⟩
  · change betaHom hC ⟨⁅a, b⁆, hkerab⟩ = 1
    have h1 : (⟨⁅a, b⁆, hkerab⟩ : ↥((Tsig hC).ker)) =
        (⁅(⟨a, hker ha⟩ : ↥((Tsig hC).ker)), (⟨b, hker hb⟩ : ↥((Tsig hC).ker))⁆ :
          ↥((Tsig hC).ker)) := rfl
    rw [h1, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  · change detHom hC ⟨⁅a, b⁆, hkerab⟩ = 1
    have h1 : (⟨⁅a, b⁆, hkerab⟩ : ↥((Tsig hC).ker)) =
        (⁅(⟨a, hker ha⟩ : ↥((Tsig hC).ker)), (⟨b, hker hb⟩ : ↥((Tsig hC).ker))⁆ :
          ↥((Tsig hC).ker)) := rfl
    rw [h1, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

private theorem Tmat_of_mem_L (hC : Levi108 K L R N Y ρ μ T) {l : ↥(NLY L Y)}
    (hl : (l : 𝓜) ∈ L) :
    ∃ u : Fin 3 → K, u 0 = 0 ∧ Tmat T l = 1 + Matrix.vecMulVec (e₀ K) u ∧
      Tmat T l 0 0 = 1 ∧ Tblock T l = 1 := by
  have hlR : (l : 𝓜) ∈ R := hC.L_le_R hl
  obtain ⟨u, hu0, hu⟩ := hC.rho_L (l : 𝓜) hl
  have hmat : Tmat T l = 1 + Matrix.vecMulVec (e₀ K) u := by
    ext i j
    rw [show Tmat T l i j = T l (Pi.single j (1 : K)) i from rfl, hC.T_rho l hlR, hu]
    simp [Matrix.mulVec_single_one, Matrix.col_apply]
  refine ⟨u, hu0, hmat, ?_, ?_⟩
  · rw [hmat]
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec, e₀, Pi.single_apply, hu0]
  · ext i j
    rw [show Tblock T l i j = Tmat T l i.succ j.succ from rfl, hmat]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec, e₀, Pi.single_apply]

private theorem good_L (hC : Levi108 K L R N Y ρ μ T) :
    L.subgroupOf (NLY L Y) ≤
      (Tsig hC).ker ⊓
        (((betaHom hC).ker ⊓ (detHom hC).ker).map ((Tsig hC).ker).subtype) := by
  intro l hl
  have hlL : (l : 𝓜) ∈ L := Subgroup.mem_subgroupOf.mp hl
  have hlR : (l : 𝓜) ∈ R := hC.L_le_R hlL
  obtain ⟨u, hu0, hmat, hl00, hblk⟩ := Tmat_of_mem_L hC hlL
  have hlker : l ∈ (Tsig hC).ker := by
    rw [MonoidHom.mem_ker, Tsig_apply]
    refine (Tsigma_unique hC (g := l) (σ := 1) ?_).symm
    intro c v
    calc T l (c • v) = (ρ ⟨(l : 𝓜), hlR⟩ : Matrix (Fin 3) (Fin 3) K) *ᵥ (c • v) :=
          hC.T_rho l hlR (c • v)
      _ = c • ((ρ ⟨(l : 𝓜), hlR⟩ : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := Matrix.mulVec_smul ..
      _ = c • T l v := by rw [hC.T_rho l hlR]
  have hβ : (⟨l, hlker⟩ : ↥((Tsig hC).ker)) ∈ (betaHom hC).ker := by
    change betaHom hC ⟨l, hlker⟩ = 1
    refine Units.ext ?_
    rw [show (betaHom hC ⟨l, hlker⟩ : Kˣ) =
      Units.mk0 (Tmat T l 0 0) (Tmat_zero_zero_ne_zero hC l) from rfl, Units.val_mk0,
      Units.val_one]
    exact hl00
  have hd : (⟨l, hlker⟩ : ↥((Tsig hC).ker)) ∈ (detHom hC).ker := by
    change detHom hC ⟨l, hlker⟩ = 1
    refine Units.ext ?_
    rw [show (detHom hC ⟨l, hlker⟩ : Kˣ) =
      Units.mk0 (Tmat T l).det (Tmat_det_ne_zero hC l hlker) from rfl, Units.val_mk0,
      Units.val_one]
    show (Tmat T l).det = 1
    have hdet : (Tmat T l).det = Tmat T l 0 0 * (Tblock T l).det := by
      rw [Matrix.det_fin_three]
      simp only [Tblock, Matrix.det_fin_two, (Tmat_col_zero hC l).1,
        (Tmat_col_zero hC l).2, zero_mul, mul_zero, add_zero, sub_zero,
        Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
      ring
    rw [hdet, hl00, hblk, Matrix.det_one, mul_one]
  exact ⟨hlker, Subgroup.mem_map.mpr ⟨⟨l, hlker⟩, ⟨hβ, hd⟩, rfl⟩⟩

private theorem comap_mkN_le_good (hC : Levi108 K L R N Y ρ μ T)
    {J : Subgroup (GG L)} (hJ : J ≤ Nfrak L Y) (hJp : ⁅J, J⁆ = J) :
    J.comap (mkN L Y) ≤
      (Tsig hC).ker ⊓
        (((betaHom hC).ker ⊓ (detHom hC).ker).map ((Tsig hC).ker).subtype) := by
  have hker := comap_mkN_le_ker_Tsig hC hJ hJp
  have hmap : Subgroup.map (mkN L Y) (J.comap (mkN L Y)) = J := by
    rw [Subgroup.map_comap_eq, inf_eq_right]
    exact hJ.trans (Nfrak_le_range hC)
  have hJ' : Subgroup.map (mkN L Y) ⁅J.comap (mkN L Y), J.comap (mkN L Y)⁆ = J := by
    rw [Subgroup.map_commutator, hmap, hJp]
  have hLnorm : (L.subgroupOf (NLY L Y)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (inf_le_left : NLY L Y ≤ NL L)
  intro g hg
  have hgker : g ∈ (Tsig hC).ker := hker hg
  have hmem : mkN L Y g ∈ Subgroup.map (mkN L Y)
      ⁅J.comap (mkN L Y), J.comap (mkN L Y)⁆ := by
    rw [hJ']
    exact hg
  have hgc : g ∈ ⁅J.comap (mkN L Y), J.comap (mkN L Y)⁆ ⊔ (mkN L Y).ker := by
    rw [← Subgroup.comap_map_eq]
    exact Subgroup.mem_comap.mpr hmem
  rw [ker_mkN] at hgc
  exact sup_le (good_commutator hC hker) (good_L hC) hgc

private theorem T_pow_linear (hC : Levi108 K L R N Y ρ μ T) {x : ↥(NLY L Y)}
    (hx_lin : ∀ (c : K) (v : Fin 3 → K), T x (c • v) = c • T x v) :
    ∀ (m : ℕ) (c : K) (v : Fin 3 → K), (T x ^ m) (c • v) = c • (T x ^ m) v := by
  intro m
  induction m with
  | zero => intro c v; simp
  | succ m ih =>
    intro c v
    rw [pow_succ]
    show (T x ^ m) ((T x) (c • v)) = c • (T x ^ m) ((T x) v)
    rw [hx_lin c v, ih c ((T x) v)]

private theorem T_pow_eigen (hC : Levi108 K L R N Y ρ μ T) {x : ↥(NLY L Y)} {β α : K}
    (hx_lin : ∀ (c : K) (v : Fin 3 → K), T x (c • v) = c • T x v)
    (hx_diag : Tmat T x = Matrix.diagonal (fun i : Fin 3 => if i = 0 then β else α)) :
    (∀ m : ℕ, (T x ^ m) (e₀ K) = β ^ m • e₀ K) ∧
      (∀ m : ℕ, (T x ^ m) (Pi.single 1 (1 : K) : Fin 3 → K) =
        α ^ m • (Pi.single 1 (1 : K) : Fin 3 → K)) := by
  have heig0 : T x (e₀ K) = β • e₀ K := by
    rw [Tmat_mulVec_of_linear hC hx_lin, hx_diag]
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, Matrix.diagonal_apply, e₀, Pi.single_apply, Fin.sum_univ_three]
  have heig1 : T x (Pi.single 1 (1 : K) : Fin 3 → K) =
      α • (Pi.single 1 (1 : K) : Fin 3 → K) := by
    rw [Tmat_mulVec_of_linear hC hx_lin, hx_diag]
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, Matrix.diagonal_apply, e₀, Pi.single_apply, Fin.sum_univ_three]
  have hlin := T_pow_linear hC hx_lin
  constructor
  · intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ]
      show (T x ^ m) ((T x) (e₀ K)) = β ^ (m + 1) • e₀ K
      rw [heig0, hlin m β (e₀ K), ih, smul_smul, pow_succ, mul_comm]
  · intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ]
      show (T x ^ m) ((T x) (Pi.single 1 (1 : K))) = α ^ (m + 1) • Pi.single 1 (1 : K)
      rw [heig1, hlin m α (Pi.single 1 (1 : K)), ih, smul_smul, pow_succ, mul_comm]

private theorem T_fixes_of_mem_L (hC : Levi108 K L R N Y ρ μ T) {z : ↥(NLY L Y)}
    (hz : (z : 𝓜) ∈ L) :
    T z (e₀ K) = e₀ K ∧ (T z (Pi.single 1 (1 : K) : Fin 3 → K)) 1 = 1 := by
  obtain ⟨u, hu0, hmat, -, -⟩ := Tmat_of_mem_L hC hz
  have hzR : (z : 𝓜) ∈ R := hC.L_le_R hz
  have hρ : (ρ ⟨(z : 𝓜), hzR⟩ : Matrix (Fin 3) (Fin 3) K) = Tmat T z := by
    ext i j
    rw [show Tmat T z i j = T z (Pi.single j (1 : K)) i from rfl, hC.T_rho z hzR]
    simp [Matrix.mulVec_single_one, Matrix.col_apply]
  constructor
  · rw [hC.T_rho z hzR, hρ, hmat]
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec, e₀,
        Pi.single_apply, Fin.sum_univ_three, hu0]
  · rw [hC.T_rho z hzR, hρ, hmat]
    simp [Matrix.mulVec, Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec, e₀,
      Pi.single_apply, Fin.sum_univ_three]

private theorem T_eq_one_of_diag (hC : Levi108 K L R N Y ρ μ T) {x : ↥(NLY L Y)} {β α : K}
    (hx_lin : ∀ (c : K) (v : Fin 3 → K), T x (c • v) = c • T x v)
    (hx_diag : Tmat T x = Matrix.diagonal (fun i : Fin 3 => if i = 0 then β else α))
    (hβ1 : β = 1) (hα1 : α = 1) : T x = 1 := by
  have hTmat1 : Tmat T x = 1 := by
    rw [hx_diag]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_apply, Matrix.one_apply, hβ1, hα1]
  refine AddMonoidHom.ext fun v => ?_
  change (T x : (Fin 3 → K) →+ (Fin 3 → K)) v = v
  rw [Tmat_mulVec_of_linear hC hx_lin v, hTmat1, Matrix.one_mulVec]

private theorem T_pow_mem_N (hC : Levi108 K L R N Y ρ μ T) {x : ↥(NLY L Y)} (n : ℕ)
    (hxL : ((x ^ 2 ^ n : ↥(NLY L Y)) : 𝓜) ∈ L) (hTx : T x = 1) :
    ((x ^ 2 ^ n : ↥(NLY L Y)) : 𝓜) ∈ N := by
  have hxR : ((x ^ 2 ^ n : ↥(NLY L Y)) : 𝓜) ∈ R := hC.L_le_R hxL
  have hT1 : T (x ^ 2 ^ n) = 1 := by rw [map_pow, hTx, one_pow]
  have hρ1m : ((ρ ⟨((x ^ 2 ^ n : ↥(NLY L Y)) : 𝓜), hxR⟩ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = 1 := by
    ext i j
    have h : ((ρ ⟨((x ^ 2 ^ n : ↥(NLY L Y)) : 𝓜), hxR⟩ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single j (1 : K) : Fin 3 → K) =
        (Pi.single j (1 : K) : Fin 3 → K) := by
      rw [← hC.T_rho (x ^ 2 ^ n) hxR, hT1]
      rfl
    have h' := congrFun h i
    simpa [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.one_apply,
      Pi.single_apply] using h'
  have hρ1 : (ρ ⟨((x ^ 2 ^ n : ↥(NLY L Y)) : 𝓜), hxR⟩ : GL (Fin 3) K) = 1 := Units.ext hρ1m
  have hmem : (⟨((x ^ 2 ^ n : ↥(NLY L Y)) : 𝓜), hxR⟩ : ↥R) ∈ ρ.ker :=
    MonoidHom.mem_ker.mpr hρ1
  rw [hC.ker_rho] at hmem
  exact Subgroup.mem_subgroupOf.mp hmem

private theorem mem_Yhat_of_mem_N (hC : Levi108 K L R N Y ρ μ T) {x : ↥(NLY L Y)} {k : GG L}
    (hx_k : mkN L Y x = k) (hxN : (x : 𝓜) ∈ N) : k ∈ Yhat L N := by
  rw [← hx_k, mkN_apply]
  exact Subgroup.mem_map.mpr ⟨⟨(x : 𝓜), x.2.1⟩, Subgroup.mem_subgroupOf.mpr hxN, rfl⟩

theorem Levi108.mem_Yhat_of_pow (hC : Levi108 K L R N Y ρ μ T) {k : GG L}
    (hk : k ∈ Kfrak L R) {n : ℕ} (hkn : k ^ 2 ^ n = 1) : k ∈ Yhat L N := by
  obtain ⟨x, β, α, hx_k, hx_diag, hx_lin⟩ := exists_diag hC hk
  have hxL : ((x ^ 2 ^ n : ↥(NLY L Y)) : 𝓜) ∈ L := by
    have h : (x ^ 2 ^ n : ↥(NLY L Y)) ∈ (mkN L Y).ker := by
      rw [MonoidHom.mem_ker, map_pow, hx_k, hkn]
    rwa [ker_mkN, Subgroup.mem_subgroupOf] at h
  obtain ⟨hpow0, hpow1⟩ := T_pow_eigen hC hx_lin hx_diag
  obtain ⟨hfix0, hfix1⟩ := T_fixes_of_mem_L hC hxL
  have hpowT0 : (T x ^ 2 ^ n) (e₀ K) = e₀ K := by
    rw [← map_pow]
    exact hfix0
  have hpowT1 : ((T x ^ 2 ^ n) (Pi.single 1 (1 : K) : Fin 3 → K)) 1 = 1 := by
    rw [← map_pow]
    exact hfix1
  have hβpow : β ^ 2 ^ n = 1 := by
    have h := (hpow0 (2 ^ n)).symm.trans hpowT0
    have := congrFun h 0
    simpa [e₀, Pi.smul_apply] using this
  have hαpow : α ^ 2 ^ n = 1 := by
    have h := hpow1 (2 ^ n)
    rw [h] at hpowT1
    simpa [Pi.smul_apply] using hpowT1
  have hβ1 : β = 1 := CFSG.Quasithin.Vol2.KGNat.KA.eq_one_of_pow_two_pow hβpow
  have hα1 : α = 1 := CFSG.Quasithin.Vol2.KGNat.KA.eq_one_of_pow_two_pow hαpow
  have hTx1 : T x = 1 := T_eq_one_of_diag hC hx_lin hx_diag hβ1 hα1
  exact mem_Yhat_of_mem_N hC hx_k (hC.T_ker_two x hTx1 n (T_pow_mem_N hC n hxL hTx1))

private theorem D_normalizer (hC : Levi108 K L R N Y ρ μ T) :
    T.ker.map (mkN L Y) ≤ Subgroup.normalizer (P0frak L R : Set (GG L)) ∧
      ⁅⁅T.ker.map (mkN L Y), T.ker.map (mkN L Y)⁆,
        ⁅T.ker.map (mkN L Y), T.ker.map (mkN L Y)⁆⁆ ≤ P0frak L R := by
  have hD : T.ker.map (mkN L Y) ≤
      Subgroup.normalizer (P0frak L R : Set (GG L)) := by
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap]
    refine hC.Nfrak_le_normalizer_P0frak ?_
    exact Subgroup.mem_map.mpr ⟨⟨(x : 𝓜), x.2.1⟩, Subgroup.mem_subgroupOf.mpr x.2.2, rfl⟩
  refine ⟨hD, ?_⟩
  have h1 : ⁅⁅T.ker.map (mkN L Y), T.ker.map (mkN L Y)⁆,
      ⁅T.ker.map (mkN L Y), T.ker.map (mkN L Y)⁆⁆ =
      (⁅⁅T.ker, T.ker⁆, ⁅T.ker, T.ker⁆⁆ : Subgroup ↥(NLY L Y)).map (mkN L Y) := by
    rw [Subgroup.map_commutator]
    congr 1 <;> rw [Subgroup.map_commutator]
  rw [h1]
  calc (⁅⁅T.ker, T.ker⁆, ⁅T.ker, T.ker⁆⁆ : Subgroup ↥(NLY L Y)).map (mkN L Y)
      ≤ (N.subgroupOf (NLY L Y)).map (mkN L Y) := Subgroup.map_mono hC.T_ker_comm
    _ ≤ Yhat L N := by
        rintro y ⟨x, hx, rfl⟩
        exact Subgroup.mem_map.mpr ⟨⟨(x : 𝓜), x.2.1⟩,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx), rfl⟩
    _ ≤ P0frak L R := by
        rw [← hC.Yhat_sup_Xlevi]
        exact le_sup_left

private theorem exists_P0_preimage (hC : Levi108 K L R N Y ρ μ T) {y : ↥((Tsig hC).ker)}
    (hyβ : Tmat T y.1 0 0 = 1) (hyδ : (Tmat T y.1).det = 1) :
    ∃ r₀ : ↥(NLY L Y), mkN L Y r₀ ∈ P0frak L R ∧ T r₀ = T y.1 := by
  have hgl : ∀ (c : K) (v : Fin 3 → K), T y.1 (c • v) = c • T y.1 v :=
    T_linear_of_tsig hC (MonoidHom.mem_ker.mp y.2)
  have hginv : Tsig hC y.1⁻¹ = 1 := by rw [map_inv, MonoidHom.mem_ker.mp y.2, inv_one]
  have hmul : Tmat T y.1 * Tmat T (y.1⁻¹) = 1 := by
    rw [← Tmat_mul hC hgl (T_linear_of_tsig hC hginv), mul_inv_cancel, Tmat_one hC]
  have hmul' : Tmat T (y.1⁻¹) * Tmat T y.1 = 1 := by
    rw [← Tmat_mul hC (T_linear_of_tsig hC hginv) hgl, inv_mul_cancel, Tmat_one hC]
  let U : GL (Fin 3) K := ⟨Tmat T y.1, Tmat T (y.1⁻¹), hmul, hmul'⟩
  have hU : U ∈ StatedSL 3 K := by
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
    simpa [U] using hyδ
  obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp (by rw [hC.range_rho]; exact hU)
  have hrR : (r : 𝓜) ∈ R := r.2
  have hUmat : (ρ ⟨(r : 𝓜), hrR⟩ : Matrix (Fin 3) (Fin 3) K) =
      (U : Matrix (Fin 3) (Fin 3) K) :=
    congrArg (fun u : GL (Fin 3) K => (u : Matrix (Fin 3) (Fin 3) K)) hr
  have hr00 : (ρ ⟨(r : 𝓜), hrR⟩ : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
    rw [hUmat]; exact hyβ
  have hr10 : (ρ ⟨(r : 𝓜), hrR⟩ : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    rw [hUmat]; exact (Tmat_col_zero hC y.1).1
  have hr20 : (ρ ⟨(r : 𝓜), hrR⟩ : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    rw [hUmat]; exact (Tmat_col_zero hC y.1).2
  have hrNL : (r : 𝓜) ∈ NL L :=
    (hC.mem_normalizer_iff (r : 𝓜) hrR).mpr ⟨hr10, hr20⟩
  have hrP0 : mkG L ⟨(r : 𝓜), hrNL⟩ ∈ P0frak L R :=
    (hC.mem_P0frak_iff ⟨(r : 𝓜), hrNL⟩ hrR).mpr hr00
  have hrP0' : mkN L Y ⟨(r : 𝓜), ⟨hrNL, hC.R_le_normalizer_Y hrR⟩⟩ ∈ P0frak L R := by
    rw [mkN_apply]
    exact hrP0
  let r₀ : ↥(NLY L Y) := ⟨(r : 𝓜), ⟨hrNL, hC.R_le_normalizer_Y hrR⟩⟩
  have hr₀R : (r₀ : 𝓜) ∈ R := hrR
  have hTrm : T r₀ = T y.1 := by
    refine AddMonoidHom.ext fun v => ?_
    show (T r₀ : (Fin 3 → K) →+ (Fin 3 → K)) v =
      (T y.1 : (Fin 3 → K) →+ (Fin 3 → K)) v
    rw [hC.T_rho r₀ hr₀R, Tmat_mulVec_of_linear hC hgl v]
    exact congrArg (fun u : GL (Fin 3) K => (u : Matrix (Fin 3) (Fin 3) K) *ᵥ v) hr
  exact ⟨r₀, hrP0', hTrm⟩

private theorem mkN_mem_sup_of_good (hC : Levi108 K L R N Y ρ μ T) {g : ↥(NLY L Y)}
    (hgker : g ∈ (Tsig hC).ker)
    (hgood : g ∈ (Tsig hC).ker ⊓
      (((betaHom hC).ker ⊓ (detHom hC).ker).map ((Tsig hC).ker).subtype)) :
    mkN L Y g ∈ P0frak L R ⊔ T.ker.map (mkN L Y) := by
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hgood.2
  rw [← hyg]
  clear hgker hgood hyg
  have hyβ : Tmat T y.1 0 0 = 1 := by
    have h : betaHom hC y = 1 := hy.1
    have h' := congrArg (fun u : Kˣ => (u : K)) h
    rw [show (betaHom hC y : Kˣ) = Units.mk0 (Tmat T y.1 0 0)
      (Tmat_zero_zero_ne_zero hC y.1) from rfl, Units.val_mk0, Units.val_one] at h'
    exact h'
  have hyδ : (Tmat T y.1).det = 1 := by
    have h : detHom hC y = 1 := hy.2
    have h' := congrArg (fun u : Kˣ => (u : K)) h
    rw [show (detHom hC y : Kˣ) = Units.mk0 (Tmat T y.1).det
      (Tmat_det_ne_zero hC y.1 y.2) from rfl, Units.val_mk0, Units.val_one] at h'
    exact h'
  obtain ⟨r₀, hrP0', hTrm⟩ := exists_P0_preimage hC hyβ hyδ
  have hkerT : (r₀⁻¹ * y.1) ∈ T.ker := by
    rw [MonoidHom.mem_ker, map_mul]
    have h := T_inv_mul hC r₀
    rw [hTrm] at h
    exact h
  have hDmem : mkN L Y (r₀⁻¹ * y.1) ∈ T.ker.map (mkN L Y) :=
    Subgroup.mem_map.mpr ⟨_, hkerT, rfl⟩
  have hsplit : mkN L Y (y.1 : ↥(NLY L Y)) =
      mkN L Y r₀ * mkN L Y (r₀⁻¹ * y.1) := by
    rw [← map_mul, mul_inv_cancel_left]
  rw [show mkN L Y ((Tsig hC).ker.subtype y) = mkN L Y y.1 from rfl, hsplit]
  exact Subgroup.mul_mem_sup hrP0' hDmem

theorem Levi108.le_Xlevi_of_perfect (hC : Levi108 K L R N Y ρ μ T) {J : Subgroup (GG L)}
    (hJ : J ≤ Nfrak L Y) (hJp : ⁅J, J⁆ = J) : J ≤ Xlevi L R := by
  obtain ⟨hD, hDdouble⟩ := D_normalizer hC
  have hDnorm : ⁅T.ker.map (mkN L Y), T.ker.map (mkN L Y)⁆ ≤
      Subgroup.normalizer (P0frak L R : Set (GG L)) :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le hD hD)
  have hJsup : J ≤ P0frak L R ⊔ T.ker.map (mkN L Y) := by
    intro j hj
    have hj' : j ∈ Nfrak L Y := hJ hj
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (Nfrak_le_range hC hj')
    rw [← hg]
    have hgJ : g ∈ J.comap (mkN L Y) := by
      rw [Subgroup.mem_comap]
      exact hg ▸ hj
    obtain ⟨hgker, hgood⟩ := comap_mkN_le_good hC hJ hJp hgJ
    exact mkN_mem_sup_of_good hC hgker ⟨hgker, hgood⟩
  have hP0 : J ≤ P0frak L R := by
    calc J = ⁅⁅J, J⁆, ⁅J, J⁆⁆ := by rw [hJp, hJp]
      _ ≤ ⁅⁅P0frak L R ⊔ T.ker.map (mkN L Y),
            P0frak L R ⊔ T.ker.map (mkN L Y)⁆,
            ⁅P0frak L R ⊔ T.ker.map (mkN L Y),
            P0frak L R ⊔ T.ker.map (mkN L Y)⁆⁆ :=
          Subgroup.commutator_mono
            (Subgroup.commutator_mono hJsup hJsup) (Subgroup.commutator_mono hJsup hJsup)
      _ ≤ ⁅P0frak L R ⊔ ⁅T.ker.map (mkN L Y), T.ker.map (mkN L Y)⁆,
            P0frak L R ⊔ ⁅T.ker.map (mkN L Y), T.ker.map (mkN L Y)⁆⁆ :=
          Subgroup.commutator_mono (commutator_sup_sup_le hD) (commutator_sup_sup_le hD)
      _ ≤ P0frak L R ⊔ ⁅⁅T.ker.map (mkN L Y), T.ker.map (mkN L Y)⁆,
            ⁅T.ker.map (mkN L Y), T.ker.map (mkN L Y)⁆⁆ :=
          commutator_sup_sup_le hDnorm
      _ ≤ P0frak L R := sup_le le_rfl hDdouble
  calc J = ⁅J, J⁆ := hJp.symm
    _ ≤ ⁅P0frak L R, P0frak L R⁆ := Subgroup.commutator_mono hP0 hP0
    _ = Xlevi L R := rfl

theorem Levi108.leviStd (hC : Levi108 K L R N Y ρ μ T) :
    LeviStd K (Xlevi L R) (Yhat L N) (Nfrak L Y) where
  four_le_card := hC.four_le_card
  mulEquiv := hC.nonempty_mulEquiv_SL2
  elemAb := hC.isElemAbelian_Yhat
  card_Yh := hC.card_Yhat
  Yh_le_centralizer := hC.Yhat_le_Kfrak
  X_le := hC.Xlevi_le_Nfrak
  le_normalizer := hC.Nfrak_le_normalizer_Xlevi
  centralizer_le := fun _ hr hr1 => hC.centralizer_le_Nfrak hr hr1
  normalizer_le := hC.normalizer_Yhat_le_Nfrak
  mem_of_pow := fun _ hk _ hkn => hC.mem_Yhat_of_pow hk hkn
  le_of_perfect := fun _ hJ hJp => hC.le_Xlevi_of_perfect hJ hJp

end CFSG.RankThree.GF2n.Stroth80.Sec108
