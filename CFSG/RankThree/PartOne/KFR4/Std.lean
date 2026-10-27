module

public import CFSG.RankThree.PartOne.KC.OrthogonalEvenNormPlane
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import CFSG.RankThree.PartOne.KFR4.B3Comb
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartOne.KFR4

open QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal

abbrev Vs (K E : Type) : Type := (Fin 3 → E) × (K × K)

section Form

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]

@[expose] noncomputable def Qs (D : EvenNormPlane K E) : QuadraticForm K (Vs K E) :=
  (QuadraticMap.pi fun _ : Fin 3 => D.N).prod
    (QuadraticMap.linMulLin (LinearMap.fst K K K) (LinearMap.snd K K K))

theorem Qs_apply (D : EvenNormPlane K E) (v : Vs K E) :
    Qs D v = ∑ i, D.N (v.1 i) + v.2.1 * v.2.2 := by
  simp [Qs, QuadraticMap.prod_apply, QuadraticMap.pi_apply, QuadraticMap.linMulLin_apply]

end Form

section Polar

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]
  (D : EvenNormPlane K E)

theorem algebraMap_polar_N (z w : E) :
    algebraMap K E (polar D.N z w) = z * D.σ w + D.σ z * w := by
  simp only [polar, map_sub, D.algebraMap_N, map_add]
  ring

theorem N_mul (z w : E) : D.N (z * w) = D.N z * D.N w := by
  apply (algebraMap K E).injective
  simp only [D.algebraMap_N, map_mul]
  ring

theorem exists_trace_ne_zero : ∃ u : E, u + D.σ u ≠ 0 := by
  by_contra hno
  push Not at hno
  have : CharP E 2 := charP_two_of_algebra (K := K)
  apply D.σ_ne_one
  ext u
  have h : D.σ u = -u := by linear_combination hno u
  rw [h, CharTwo.neg_eq]
  rfl

theorem polar_N_ne_zero {z : E} (hz : z ≠ 0) : ∃ w : E, polar D.N z w ≠ 0 := by
  obtain ⟨u, hu⟩ := exists_trace_ne_zero D
  refine ⟨z * u, fun h => ?_⟩
  have h1 := algebraMap_polar_N D z (z * u)
  rw [h, map_zero] at h1
  simp only [map_mul] at h1
  have hσz : D.σ z ≠ 0 := fun h0 => hz (by simpa using h0)
  have h2 : z * D.σ z * (u + D.σ u) = 0 := by linear_combination (-1 : E) * h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact mul_ne_zero hz hσz h3
  · exact hu h3

end Polar

section QsPolar

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]
  (D : EvenNormPlane K E)

theorem polar_Qs (v w : Vs K E) :
    polar (Qs D) v w = ∑ i, polar D.N (v.1 i) (w.1 i) + (v.2.1 * w.2.2 + w.2.1 * v.2.2) := by
  have hN : ∀ a b : E, D.N (a + b) = D.N a + D.N b + polar D.N a b :=
    fun a b => QuadraticMap.map_add D.N a b
  show Qs D (v + w) - Qs D v - Qs D w = _
  rw [Qs_apply, Qs_apply, Qs_apply]
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, hN, Finset.sum_add_distrib]
  ring

theorem Qs_nondegenerate : (polarBilin (Qs D)).Nondegenerate := by
  classical
  have key : ∀ v : Vs K E, (∀ w, polar (Qs D) v w = 0) → v = 0 := by
    intro v hv
    have h1 : ∀ i, v.1 i = 0 := by
      intro i
      by_contra hi
      obtain ⟨u, hu⟩ := polar_N_ne_zero D hi
      apply hu
      have := hv ((Pi.single i u : Fin 3 → E), (0, 0))
      rw [polar_Qs, Finset.sum_eq_single i (fun j _ hj => by simp [hj])
        (by simp)] at this
      simpa using this
    have h2 := hv (0, (0, 1))
    have h3 := hv (0, (1, 0))
    rw [polar_Qs] at h2 h3
    simp at h2 h3
    exact Prod.ext (funext h1) (Prod.ext h2 h3)
  constructor
  · intro v hv
    exact key v fun w => by simpa [polarBilin_apply_apply] using hv w
  · intro v hv
    refine key v fun w => ?_
    rw [polar_comm]
    simpa [polarBilin_apply_apply] using hv w

end QsPolar

structure StdData (K E : Type) [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]
    (p : ℕ) where
  D : EvenNormPlane K E
  hp : p.Prime
  hp5 : 5 ≤ p
  hpq : p ∣ Nat.card K + 1
  ζ : E
  hζ : IsPrimitiveRoot ζ p

section Rot

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] {p : ℕ}
  (S : StdData K E p)

@[expose] noncomputable def StdData.rot (a : ZMod p) : E := S.ζ ^ a.val

theorem StdData.rot_zero : S.rot 0 = 1 := by simp [StdData.rot]

theorem StdData.rot_add (a b : ZMod p) : S.rot (a + b) = S.rot a * S.rot b := by
  have : NeZero p := ⟨S.hp.ne_zero⟩
  rw [StdData.rot, StdData.rot, StdData.rot, ← pow_add, ZMod.val_add,
    ← pow_eq_pow_mod _ S.hζ.pow_eq_one]

theorem StdData.rot_neg (a : ZMod p) : S.rot (-a) * S.rot a = 1 := by
  rw [← S.rot_add, neg_add_cancel, S.rot_zero]

theorem StdData.rot_injective : Function.Injective S.rot := by
  have : NeZero p := ⟨S.hp.ne_zero⟩
  intro a b hab
  have := S.hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) hab
  exact ZMod.val_injective p this

theorem StdData.rot_mul_neg (a : ZMod p) : S.rot a * S.rot (-a) = 1 := by
  rw [mul_comm]
  exact S.rot_neg a

theorem StdData.sigma_zeta : S.D.σ S.ζ = S.ζ⁻¹ := by
  rw [S.D.sigma_eq_pow]
  obtain ⟨k, hk⟩ := S.hpq
  have h1 : S.ζ ^ (Nat.card K + 1) = 1 := by
    rw [hk, pow_mul, S.hζ.pow_eq_one, one_pow]
  exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h1)

theorem StdData.sigma_rot (a : ZMod p) : S.D.σ (S.rot a) = S.rot (-a) := by
  have h : S.rot (-a) = (S.rot a)⁻¹ := eq_inv_of_mul_eq_one_left (S.rot_neg a)
  rw [h, StdData.rot, map_pow, S.sigma_zeta, inv_pow]

theorem StdData.norm_rot (a : ZMod p) : S.D.N (S.rot a) = 1 := by
  apply (algebraMap K E).injective
  rw [S.D.algebraMap_N, S.sigma_rot, mul_comm, S.rot_neg, map_one]

end Rot

section Torus

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] {p : ℕ}
  (S : StdData K E p)

omit [Finite K] [CharP K 2] in
@[expose] noncomputable def mulCoord (r : Fin 3 → E) : Vs K E →ₗ[K] Vs K E where
  toFun v := (fun i => r i * v.1 i, v.2)
  map_add' v w := by
    refine Prod.ext (funext fun i => ?_) rfl
    simp [mul_add]
  map_smul' c v := by
    refine Prod.ext (funext fun i => ?_) rfl
    simp

omit [Finite K] [CharP K 2] in
theorem mulCoord_apply (r : Fin 3 → E) (v : Vs K E) :
    mulCoord r v = ((fun i => r i * v.1 i), v.2) := rfl

@[expose] noncomputable def tor (a : Fin 3 → ZMod p) : Vs K E ≃ₗ[K] Vs K E :=
  LinearEquiv.ofLinearMap (mulCoord fun i => S.rot (a i)) (mulCoord fun i => S.rot (-a i))
    (LinearMap.ext fun v => Prod.ext (funext fun i => by
      simp [mulCoord_apply, ← mul_assoc, S.rot_mul_neg]) rfl)
    (LinearMap.ext fun v => Prod.ext (funext fun i => by
      simp [mulCoord_apply, ← mul_assoc, S.rot_neg]) rfl)

theorem tor_apply (a : Fin 3 → ZMod p) (v : Vs K E) :
    tor S a v = ((fun i => S.rot (a i) * v.1 i), v.2) := rfl

theorem tor_add (a b : Fin 3 → ZMod p) : tor S (a + b) = tor S a * tor S b :=
  LinearEquiv.ext fun v => Prod.ext (funext fun i => by simp [tor_apply, S.rot_add, mul_assoc]) rfl

theorem tor_zero : tor S (0 : Fin 3 → ZMod p) = 1 :=
  LinearEquiv.ext fun v => Prod.ext (funext fun i => by simp [tor_apply, S.rot_zero]) rfl

@[expose] noncomputable def torHom :
    Multiplicative (Fin 3 → ZMod p) →* (Vs K E ≃ₗ[K] Vs K E) where
  toFun a := tor S (Multiplicative.toAdd a)
  map_one' := tor_zero S
  map_mul' _ _ := tor_add S _ _

theorem torHom_injective : Function.Injective (torHom S) := by
  intro a b hab
  have h : tor S (Multiplicative.toAdd a) = tor S (Multiplicative.toAdd b) := hab
  apply Multiplicative.toAdd.injective
  funext i
  have := congrArg (fun g : Vs K E ≃ₗ[K] Vs K E => (g ((Pi.single i 1 : Fin 3 → E), (0, 0))).1 i) h
  simp [tor_apply] at this
  exact S.rot_injective this

@[expose] noncomputable def Tstd : Subgroup (Vs K E ≃ₗ[K] Vs K E) := (torHom S).range

end Torus

section Orth

open CFSG.RankThree.Classical2
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.PartOne.FieldFix

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] [Module.Finite K E]
  {p : ℕ} (S : StdData K E p)

omit [Module.Finite K E] in
theorem Qs_tor (a : Fin 3 → ZMod p) (v : Vs K E) : Qs S.D (tor S a v) = Qs S.D v := by
  rw [Qs_apply, Qs_apply]
  simp [tor_apply, N_mul, S.norm_rot]

omit [Module.Finite K E] in
theorem tor_mem_orthogonalGroup (a : Fin 3 → ZMod p) :
    tor S a ∈ TauCeti.QuadraticMap.orthogonalGroup (Qs S.D) :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 (Qs_tor S a)

theorem exists_three_totSing_Qs (D : EvenNormPlane K E) :
    ∃ T : Submodule K (Vs K E), Module.finrank K T = 3 ∧ ∀ x ∈ T, Qs D x = 0 := by
  let f : (E × K) →ₗ[K] Vs K E :=
    { toFun := fun u => (![u.1, u.1, 0], (u.2, 0))
      map_add' := fun u w => by
        refine Prod.ext (funext fun i => ?_) (by simp)
        fin_cases i <;> simp
      map_smul' := fun c u => by
        refine Prod.ext (funext fun i => ?_) (by simp)
        fin_cases i <;> simp }
  have hf : Function.Injective f := by
    intro u w h
    have h1 := congrArg (fun v : Vs K E => v.1 0) h
    have h2 := congrArg (fun v : Vs K E => v.2.1) h
    simp [f] at h1 h2
    exact Prod.ext h1 h2
  have : Module.Finite K E := Module.finite_of_finrank_pos (by rw [D.finrank_eq]; omega)
  refine ⟨LinearMap.range f, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hf, Module.finrank_prod, D.finrank_eq]
    simp
  · rintro _ ⟨u, rfl⟩
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    simp [f, Qs_apply, Fin.sum_univ_three]
    exact CharTwo.add_self_eq_zero _

noncomputable abbrev Om (D : EvenNormPlane K E) : Subgroup (Vs K E ≃ₗ[K] Vs K E) :=
  orthDerived (Qs D)

theorem Om_eq_omegaGroup (D : EvenNormPlane K E) : Om D = omegaGroup (Qs D) (Qs_nondegenerate D) :=
  le_antisymm (orthDerived_le_omegaGroup (Qs_nondegenerate D))
    (omegaGroup_le_orthDerived (Qs_nondegenerate D) (exists_three_totSing_Qs D))

theorem mem_Om_of_pow_eq_one {D : EvenNormPlane K E} {g : Vs K E ≃ₗ[K] Vs K E}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qs D)) {n : ℕ} (hn : Odd n) (hgn : g ^ n = 1) :
    g ∈ Om D := by
  rw [Om_eq_omegaGroup]
  have h1 : (⟨g, hg⟩ : TauCeti.QuadraticMap.orthogonalGroup (Qs D)) ∈
      (dicksonHom (Qs D) (Qs_nondegenerate D)).ker := by
    rw [MonoidHom.mem_ker]
    have h2 : (dicksonHom (Qs D) (Qs_nondegenerate D) ⟨g, hg⟩) ^ n = 1 := by
      rw [← map_pow]
      have : (⟨g, hg⟩ : TauCeti.QuadraticMap.orthogonalGroup (Qs D)) ^ n = 1 :=
        Subtype.ext hgn
      rw [this, map_one]
    obtain ⟨k, rfl⟩ := hn
    have hx2 : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
    have h3 : ∀ y : Multiplicative (ZMod 2), y ^ (2 * k + 1) = y := fun y => by
      rw [pow_succ, pow_mul, hx2, one_pow, one_mul]
    rw [← h3 (dicksonHom (Qs D) (Qs_nondegenerate D) ⟨g, hg⟩)]
    exact h2
  rw [dicksonHom_ker, Subgroup.mem_subgroupOf] at h1
  exact h1

omit [Module.Finite K E] in
theorem torHom_pow_eq_one (a : Multiplicative (Fin 3 → ZMod p)) : torHom S a ^ p = 1 := by
  rw [← map_pow]
  have : a ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    simp
  rw [this, map_one]

theorem Tstd_le_Om : Tstd S ≤ Om S.D := by
  rintro _ ⟨a, rfl⟩
  have hp2 : p ≠ 2 := by have := S.hp5; omega
  exact mem_Om_of_pow_eq_one (tor_mem_orthogonalGroup S _) (S.hp.odd_of_ne_two hp2)
    (torHom_pow_eq_one S a)

end Orth

section Support

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] [Module.Finite K E]

@[expose] def Ufix (K E : Type) [Field K] [Field E] [Algebra K E] (F : Finset (Fin 3)) :
    Submodule K (Vs K E) where
  carrier := {v | ∀ j, j ∉ F → v.1 j = 0}
  add_mem' := fun {v w} hv hw j hj => by simp [hv j hj, hw j hj]
  zero_mem' := fun j _ => rfl
  smul_mem' := fun c v hv j hj => by simp [hv j hj]

@[expose] def Supp (D : EvenNormPlane K E) (F : Finset (Fin 3)) :
    Subgroup (Vs K E ≃ₗ[K] Vs K E) where
  carrier := {g | g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qs D) ∧
    (∀ v, v ∈ Ufix K E F ↔ g v ∈ Ufix K E F) ∧
    ∀ v : Vs K E, (∀ j ∈ F, v.1 j = 0) → v.2 = 0 → g v = v}
  mul_mem' := by
    rintro g h ⟨hgO, hg1, hg2⟩ ⟨hhO, hh1, hh2⟩
    refine ⟨mul_mem hgO hhO, fun v => (hh1 v).trans (hg1 (h v)), fun v hv hv2 => ?_⟩
    rw [LinearEquiv.mul_apply, hh2 v hv hv2, hg2 v hv hv2]
  one_mem' := ⟨one_mem _, fun v => Iff.rfl, fun v _ _ => rfl⟩
  inv_mem' := by
    rintro g ⟨hgO, hg1, hg2⟩
    refine ⟨inv_mem hgO, fun v => ?_, fun v hv hv2 => ?_⟩
    · have h : g (g⁻¹ v) = v := by simp
      have := hg1 (g⁻¹ v)
      rw [h] at this
      exact this.symm
    · have h := hg2 v hv hv2
      calc g⁻¹ v = g⁻¹ (g v) := by rw [h]
        _ = v := by simp

end Support

section Maps

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]

@[expose] noncomputable def conjCoordLin (D : EvenNormPlane K E) (k : Fin 3) :
    Vs K E →ₗ[K] Vs K E where
  toFun v := (fun j => if j = k then D.σ (v.1 j) else v.1 j, v.2)
  map_add' v w := by
    refine Prod.ext (funext fun j => ?_) rfl
    by_cases h : j = k <;> simp [h]
  map_smul' c v := by
    refine Prod.ext (funext fun j => ?_) rfl
    by_cases h : j = k <;> simp [h]

@[expose] noncomputable def conjCoord (D : EvenNormPlane K E) (k : Fin 3) :
    Vs K E ≃ₗ[K] Vs K E :=
  LinearEquiv.ofLinearMap (conjCoordLin D k) (conjCoordLin D k)
    (LinearMap.ext fun v => Prod.ext (funext fun j => by
      by_cases h : j = k <;> simp [conjCoordLin, h, D.sigma_sigma]) rfl)
    (LinearMap.ext fun v => Prod.ext (funext fun j => by
      by_cases h : j = k <;> simp [conjCoordLin, h, D.sigma_sigma]) rfl)

@[expose] noncomputable def swapH (K E : Type) [Field K] [Field E] [Algebra K E] :
    Vs K E ≃ₗ[K] Vs K E where
  toFun v := (v.1, (v.2.2, v.2.1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := (v.1, (v.2.2, v.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] noncomputable def swapCoord (K E : Type) [Field K] [Field E] [Algebra K E] (i j : Fin 3) :
    Vs K E ≃ₗ[K] Vs K E where
  toFun v := (fun k => v.1 (Equiv.swap i j k), v.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := (fun k => v.1 (Equiv.swap i j k), v.2)
  left_inv v := by
    refine Prod.ext (funext fun k => ?_) rfl
    simp
  right_inv v := by
    refine Prod.ext (funext fun k => ?_) rfl
    simp

@[expose] noncomputable def matLin (M : Matrix (Fin 3) (Fin 3) E) : Vs K E →ₗ[K] Vs K E where
  toFun v := (M.mulVec v.1, v.2)
  map_add' v w := by
    refine Prod.ext ?_ rfl
    simp [Matrix.mulVec_add]
  map_smul' c v := by
    refine Prod.ext ?_ rfl
    simp [Matrix.mulVec_smul]

@[expose] noncomputable def matToG (K : Type) [Field K] [Algebra K E] :
    GL (Fin 3) E →* (Vs K E ≃ₗ[K] Vs K E) where
  toFun M := LinearEquiv.ofLinearMap (matLin M) (matLin ↑M⁻¹)
    (LinearMap.ext fun v => Prod.ext (by simp [matLin]) rfl)
    (LinearMap.ext fun v => Prod.ext (by simp [matLin]) rfl)
  map_one' := LinearEquiv.ext fun v => Prod.ext (by simp [matLin]) rfl
  map_mul' M N := LinearEquiv.ext fun v => Prod.ext (by simp [matLin]) rfl

end Maps

section Blocks

open CFSG.LieType.Universal.Unitary

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]

@[expose] def suSupp (D : EvenNormPlane K E) (i j : Fin 3) : Subgroup (GL (Fin 3) E) where
  carrier := {M | M ∈ SUid D.σ.toRingEquiv 3 ∧ ∀ k, k ≠ i → k ≠ j →
    (M : Matrix (Fin 3) (Fin 3) E).mulVec (Pi.single k 1) = Pi.single k 1}
  mul_mem' := by
    rintro M N ⟨hM, hM2⟩ ⟨hN, hN2⟩
    refine ⟨mul_mem hM hN, fun k hki hkj => ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hN2 k hki hkj, hM2 k hki hkj]
  one_mem' := ⟨one_mem _, fun k _ _ => by rw [Units.val_one, Matrix.one_mulVec]⟩
  inv_mem' := by
    rintro M ⟨hM, hM2⟩
    refine ⟨inv_mem hM, fun k hki hkj => ?_⟩
    have h := hM2 k hki hkj
    calc ((M⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).mulVec (Pi.single k 1)
        = ((M⁻¹ : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).mulVec
          ((M : Matrix (Fin 3) (Fin 3) E).mulVec (Pi.single k 1)) := by rw [h]
      _ = Pi.single k 1 := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]

@[expose] noncomputable def longBlock (D : EvenNormPlane K E) (i j : Fin 3) :
    Subgroup (Vs K E ≃ₗ[K] Vs K E) :=
  (suSupp D i j).map (matToG K)

@[expose] noncomputable def Block (D : EvenNormPlane K E) :
    Root → Subgroup (Vs K E ≃ₗ[K] Vs K E)
  | .s1 => Supp D {0} ⊓ Om D
  | .s2 => Supp D {1} ⊓ Om D
  | .s3 => Supp D {2} ⊓ Om D
  | .m12 => longBlock D 0 1
  | .m13 => longBlock D 0 2
  | .m23 => longBlock D 1 2
  | .p12 => (longBlock D 0 1).map (MulAut.conj (conjCoord D 1)).toMonoidHom
  | .p13 => (longBlock D 0 2).map (MulAut.conj (conjCoord D 2)).toMonoidHom
  | .p23 => (longBlock D 1 2).map (MulAut.conj (conjCoord D 2)).toMonoidHom

variable {p : ℕ} (S : StdData K E p)

@[expose] def hypA (ρ : Root) : Subgroup (Vs K E ≃ₗ[K] Vs K E) where
  carrier := {g | ∃ a : Fin 3 → ZMod p, ρ.vecp p ⬝ᵥ a = 0 ∧ tor S a = g}
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨a + b, ?_, tor_add S a b⟩
    rw [dotProduct_add, ha, hb, add_zero]
  one_mem' := ⟨0, by simp, tor_zero S⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨-a, by rw [dotProduct_neg, ha, neg_zero], ?_⟩
    rw [eq_inv_iff_mul_eq_one, ← tor_add, neg_add_cancel, tor_zero]

end Blocks
