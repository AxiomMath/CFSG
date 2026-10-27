module

public import CFSG.Quasithin.Background.RonanH44Sig
public import CFSG.Quasithin.Background.HFL3PRank

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3
  CFSG.Quasithin.SteinbergCB Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] noncomputable def rhoF (hK : Nat.card K = (2 ^ n) ^ 2) :
    SL(3, Fq n K) →* MulAut (HMod n K) :=
  (rho hK).comp (Matrix.SpecialLinearGroup.map (frobFixed (barR n K)).subtype)

private theorem two_pow_mod_three_cases (n : ℕ) :
    (2 ^ n % 3 = 1 ∧ Even n) ∨ (2 ^ n % 3 = 2 ∧ Odd n) := by
  induction n with
  | zero => exact Or.inl ⟨rfl, ⟨0, rfl⟩⟩
  | succ k ih =>
    rcases ih with ⟨h1, he⟩ | ⟨h1, ho⟩
    · exact Or.inr ⟨by rw [pow_succ]; omega, he.add_one⟩
    · exact Or.inl ⟨by rw [pow_succ]; omega, ho.add_one⟩

private theorem pow_eq_pow_mod_three {R : Type*} [Monoid R] {c : R} (h3 : c ^ 3 = 1) (e : ℕ) :
    c ^ e = c ^ (e % 3) := by
  conv_lhs => rw [← Nat.div_add_mod e 3, pow_add, pow_mul, h3, one_pow, one_mul]

private theorem exists_cube_twist {R : Type} [Field R] (n : ℕ) {c : R} (hc : c ^ 3 = 1)
    (hcc : c * c ^ 2 ^ n = 1) :
    ∃ μ : R, μ ^ 3 = 1 ∧ μ ^ 2 ^ n * c = μ ∧ μ * μ ^ 2 ^ n = 1 := by
  rcases two_pow_mod_three_cases n with ⟨h3, -⟩ | ⟨h3, -⟩
  · have hc2 : c ^ 2 ^ n = c := by
      rw [pow_eq_pow_mod_three hc (2 ^ n), h3, pow_one]
    rw [hc2] at hcc
    have hc1 : c = 1 := by
      calc c = c * (c * c) := by rw [hcc, mul_one]
        _ = c ^ 3 := by ring
        _ = 1 := hc
    subst hc1
    exact ⟨1, by simp, by simp, by simp⟩
  · refine ⟨c ^ 2, ?_, ?_, ?_⟩
    · rw [show (c ^ 2) ^ 3 = (c ^ 3) ^ 2 by ring, hc, one_pow]
    · rw [← pow_mul, ← pow_succ, pow_eq_pow_mod_three hc (2 * 2 ^ n + 1),
        show (2 * 2 ^ n + 1) % 3 = 2 by omega]
    · rw [← pow_mul, ← pow_add, pow_eq_pow_mod_three hc (2 + 2 * 2 ^ n),
        show (2 + 2 * 2 ^ n) % 3 = 0 by omega, pow_zero]

private theorem sig_conj_rho (hK : Nat.card K = (2 ^ n) ^ 2) (g : SL(3, K)) :
    sig n K * rho hK g * (sig n K)⁻¹ =
      rho hK (Matrix.SpecialLinearGroup.map (barR n K) g) := by
  change fldAut (bar n) * rhoT hK (SpecialLinearGroup.toGL g) * (fldAut (bar n))⁻¹ =
    rhoT hK (SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (barR n K) g))
  rw [fldAut_conj_rhoT]
  congr 1
  exact Units.ext rfl

private theorem map_barR_map_frob (x : SL(3, Fq n K)) :
    Matrix.SpecialLinearGroup.map (barR n K)
        (Matrix.SpecialLinearGroup.map (frobFixed (barR n K)).subtype x) =
      Matrix.SpecialLinearGroup.map (frobFixed (barR n K)).subtype x := by
  apply Subtype.ext
  exact Matrix.ext fun i j => frobFixed_apply (x i j)

private theorem map_frob_injective (x y : SL(3, Fq n K))
    (hxy : Matrix.SpecialLinearGroup.map (frobFixed (barR n K)).subtype x =
      Matrix.SpecialLinearGroup.map (frobFixed (barR n K)).subtype y) : x = y := by
  apply Subtype.ext
  refine Matrix.ext fun i j => ?_
  refine (frobFixed (barR n K)).subtype.injective ?_
  exact congrArg (fun z : SL(3, K) => (z : Matrix (Fin 3) (Fin 3) K) i j) hxy

private theorem exists_lift (g : SL(3, K))
    (hg : ∀ i j, barR n K ((g : Matrix (Fin 3) (Fin 3) K) i j) = (g : Matrix (Fin 3) (Fin 3) K) i j) :
    ∃ h : SL(3, Fq n K), Matrix.SpecialLinearGroup.map (frobFixed (barR n K)).subtype h = g := by
  let M : Matrix (Fin 3) (Fin 3) (Fq n K) := fun i j =>
    ⟨(g : Matrix (Fin 3) (Fin 3) K) i j, mem_frobFixed.mpr (hg i j)⟩
  have hMι : M.map (frobFixed (barR n K)).subtype = (g : Matrix (Fin 3) (Fin 3) K) :=
    Matrix.ext fun i j => rfl
  have hdet : M.det = 1 := by
    apply (frobFixed (barR n K)).subtype.injective
    rw [map_one, RingHom.map_det, RingHom.mapMatrix_apply, hMι, g.2]
  exact ⟨⟨M, hdet⟩, Subtype.ext hMι⟩

private theorem rho_smul_eq (hK : Nat.card K = (2 ^ n) ^ 2) {μ : K} (hμ0 : μ ≠ 0)
    (hμμ : μ * bar n μ = 1) (g g' : SL(3, K))
    (hg' : (g' : Matrix (Fin 3) (Fin 3) K) = μ • (g : Matrix (Fin 3) (Fin 3) K)) :
    rho hK g' = rho hK g := by
  change rhoT hK (SpecialLinearGroup.toGL g') = rhoT hK (SpecialLinearGroup.toGL g)
  have hgl : SpecialLinearGroup.toGL g' =
      scalGL (Units.mk0 μ hμ0) * SpecialLinearGroup.toGL g := by
    apply Units.ext
    rw [Units.val_mul, coe_scalGL, Units.val_mk0, SpecialLinearGroup.coe_GL_coe_matrix,
      SpecialLinearGroup.coe_GL_coe_matrix, hg', Matrix.smul_mul, Matrix.one_mul]
  rw [hgl, map_mul, rhoT_eq_one_of_smul hK (B := scalGL (Units.mk0 μ hμ0)) (d := μ)
    (coe_scalGL (Units.mk0 μ hμ0)) hμμ, one_mul]

theorem rhoF_injective (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    Function.Injective (rhoF hK) := by
  rw [injective_iff_map_eq_one]
  intro h hh
  have hg : rho hK (Matrix.SpecialLinearGroup.map (frobFixed (barR n K)).subtype h) = 1 := hh
  obtain ⟨d, hd⟩ := scalar_of_rhoT_eq_one hK
    (B := SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (frobFixed (barR n K)).subtype h))
    hg
  have hdd : d * bar n d = 1 := norm_eq_one_of_rhoT_smul hK hd hg
  have h00 : d = ((h : Matrix (Fin 3) (Fin 3) (Fq n K)) 0 0 : K) := by
    have e : ((SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map
        (frobFixed (barR n K)).subtype h) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 =
        ((h : Matrix (Fin 3) (Fin 3) (Fq n K)) 0 0 : K) := rfl
    rw [hd, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e
    exact e
  have hfix : barR n K d = d := by
    rw [h00]
    exact frobFixed_apply _
  have hdd' : d * d = 1 := by
    have e : bar n d = d := hfix
    rwa [e] at hdd
  have hd1 : d = 1 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hsq : (d - 1) * (d - 1) = 0 := by linear_combination hdd' + (1 - d) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp hsq)
  subst hd1
  refine map_frob_injective h 1 ?_
  rw [map_one]
  rw [one_smul] at hd
  exact Subtype.ext (hd.trans Matrix.SpecialLinearGroup.coe_one.symm)

theorem mem_range_rhoF_iff (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (r : MulAut (HMod n K)) :
    r ∈ (rhoF hK).range ↔
      r ∈ img hK ∧ r ∈ Subgroup.centralizer ({sig n K} : Set (MulAut (HMod n K))) := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨MonoidHom.mem_range.mpr
      ⟨Matrix.SpecialLinearGroup.map (frobFixed (barR n K)).subtype h, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    have key := sig_conj_rho hK (Matrix.SpecialLinearGroup.map (frobFixed (barR n K)).subtype h)
    rw [map_barR_map_frob] at key
    exact mul_inv_eq_iff_eq_mul.mp key
  · rintro ⟨hr, hc⟩
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hr
    have hc' : sig n K * rho hK g = rho hK g * sig n K :=
      Subgroup.mem_centralizer_iff.mp hc (sig n K) (Set.mem_singleton _)
    have hfixg : rho hK (Matrix.SpecialLinearGroup.map (barR n K) g) = rho hK g := by
      have h1 : sig n K * rho hK g * (sig n K)⁻¹ = rho hK g := by
        rw [hc', mul_assoc, mul_inv_cancel, mul_one]
      rwa [sig_conj_rho hK g] at h1
    have hk1 : rho hK (Matrix.SpecialLinearGroup.map (barR n K) g * g⁻¹) = 1 := by
      rw [map_mul, map_inv, hfixg, mul_inv_cancel]
    obtain ⟨d, hd⟩ := scalar_of_rhoT_eq_one hK
      (B := SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (barR n K) g * g⁻¹)) hk1
    have hdd : d * bar n d = 1 := norm_eq_one_of_rhoT_smul hK hd hk1
    have hk : ((Matrix.SpecialLinearGroup.map (barR n K) g * g⁻¹ : SL(3, K)) :
        Matrix (Fin 3) (Fin 3) K) = d • 1 := hd
    have hgbar : ((Matrix.SpecialLinearGroup.map (barR n K) g : SL(3, K)) :
        Matrix (Fin 3) (Fin 3) K) = d • (g : Matrix (Fin 3) (Fin 3) K) := by
      have e : Matrix.SpecialLinearGroup.map (barR n K) g =
          Matrix.SpecialLinearGroup.map (barR n K) g * g⁻¹ * g :=
        (inv_mul_cancel_right _ _).symm
      calc ((Matrix.SpecialLinearGroup.map (barR n K) g : SL(3, K)) :
            Matrix (Fin 3) (Fin 3) K)
          = (((Matrix.SpecialLinearGroup.map (barR n K) g * g⁻¹) * g : SL(3, K)) :
              Matrix (Fin 3) (Fin 3) K) :=
            congrArg (fun X : SL(3, K) => (X : Matrix (Fin 3) (Fin 3) K)) e
        _ = ((Matrix.SpecialLinearGroup.map (barR n K) g * g⁻¹ : SL(3, K)) :
              Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) := rfl
        _ = d • (g : Matrix (Fin 3) (Fin 3) K) := by
            rw [hk, Matrix.smul_mul, Matrix.one_mul]
    have hdet : (d • (g : Matrix (Fin 3) (Fin 3) K)).det = 1 := by
      rw [← hgbar]
      exact (Matrix.SpecialLinearGroup.map (barR n K) g).2
    rw [Matrix.det_smul, g.2, mul_one, Fintype.card_fin] at hdet
    have hd3 : d ^ 3 = 1 := hdet
    have hdd' : d * d ^ 2 ^ n = 1 := by
      rw [← bar_apply]
      exact hdd
    obtain ⟨μ, hμ3, hμd, hμμ⟩ := exists_cube_twist n hd3 hdd'
    have hμd' : barR n K μ * d = μ := by
      rw [barR_apply, bar_apply]
      exact hμd
    have hμμ' : μ * bar n μ = 1 := by
      rw [bar_apply]
      exact hμμ
    have hμ0 : μ ≠ 0 := by
      intro h0
      rw [h0] at hμ3
      norm_num at hμ3
    have hentry : ∀ i j, barR n K ((g : Matrix (Fin 3) (Fin 3) K) i j) =
        d * (g : Matrix (Fin 3) (Fin 3) K) i j :=
      fun i j => congrFun (congrFun hgbar i) j
    have hent : ∀ i j, barR n K ((μ • (g : Matrix (Fin 3) (Fin 3) K)) i j) =
        (μ • (g : Matrix (Fin 3) (Fin 3) K)) i j := by
      intro i j
      rw [Matrix.smul_apply, smul_eq_mul, map_mul, hentry i j, ← mul_assoc, hμd']
    have hdet' : (μ • (g : Matrix (Fin 3) (Fin 3) K)).det = 1 := by
      rw [Matrix.det_smul, g.2, mul_one, Fintype.card_fin, hμ3]
    let g' : SL(3, K) := ⟨μ • (g : Matrix (Fin 3) (Fin 3) K), hdet'⟩
    obtain ⟨h0, hh0⟩ := exists_lift g' (fun i j => hent i j)
    refine MonoidHom.mem_range.mpr ⟨h0, ?_⟩
    change rho hK (Matrix.SpecialLinearGroup.map (frobFixed (barR n K)).subtype h0) = rho hK g
    rw [hh0]
    exact rho_smul_eq hK hμ0 hμμ' g g' rfl

end CFSG.Quasithin.RonanH44
