module

public import CFSG.Open.StatedAPI
import CFSG.RankThree.GF2n.Stroth80.Sec5SLDual
import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.ClassicalGroups.Orthogonal.Models

public section

namespace CFSG.RankThree.GF2n.Stroth80

section NatScalars

open CFSG.Open Matrix

@[expose] def AddCommutantScalar {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (X : Subgroup (GL ι K)) : Prop :=
  ∀ f : (ι → K) →+ (ι → K),
    (∀ A ∈ X, ∀ v, f ((A : Matrix ι ι K) *ᵥ v) = (A : Matrix ι ι K) *ᵥ f v) →
      ∃ c : K, ∀ v, f v = c • v

private theorem statedSL_transvection_act {K : Type} [Field K] {m : ℕ} {i j : Fin m}
    (hij : i ≠ j) (c : K) : ∃ g : GL (Fin m) K, g ∈ StatedSL m K ∧
      ∀ x : Fin m → K,
        (g : Matrix (Fin m) (Fin m) K) *ᵥ x = x + (c * x j) • Pi.single i (1 : K) := by
  obtain ⟨g, hg, hgA⟩ := transvection_mem_statedSL (K := K) hij c
  refine ⟨g, hg, fun x => ?_⟩
  rw [hgA, Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]

theorem addCommutantScalar_statedSL {K : Type} [Field K] {m : ℕ} (hm : 2 ≤ m) :
    AddCommutantScalar (StatedSL m K) := by
  intro f hf
  have key : ∀ (i j : Fin m), i ≠ j → ∀ (c : K) (x : Fin m → K),
      f ((c * x j) • Pi.single i (1 : K)) = (c * f x j) • Pi.single i (1 : K) := by
    intro i j hij c x
    obtain ⟨g, hg, hgx⟩ := statedSL_transvection_act hij c
    have h := hf g hg x
    rw [hgx x, hgx (f x), map_add] at h
    exact add_left_cancel h
  have hbasis : ∀ (i j : Fin m), i ≠ j → ∀ c : K,
      f (c • Pi.single i (1 : K)) = (c * f (Pi.single j (1 : K)) j) • Pi.single i (1 : K) := by
    intro i j hij c
    simpa using key i j hij c (Pi.single j 1)
  have hdiag : ∀ i j : Fin m, f (Pi.single i (1 : K)) i = f (Pi.single j (1 : K)) j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · have h := congrFun (by simpa using hbasis i j hij 1) i
      simpa using h
  have hne : ∀ i : Fin m, ∃ j : Fin m, i ≠ j := fun i => by
    have hm1 : 1 < Fintype.card (Fin m) := by simp; omega
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hm1 i
    exact ⟨j, hj.symm⟩
  obtain ⟨i₀⟩ : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  have hfull : ∀ (i : Fin m) (c : K), f (c • Pi.single i (1 : K)) =
      (c * f (Pi.single i₀ (1 : K)) i₀) • Pi.single i (1 : K) := by
    intro i c
    obtain ⟨j, hij⟩ := hne i
    rw [hbasis i j hij c, hdiag j i₀]
  have hv : ∀ v : Fin m → K, v = ∑ i, v i • Pi.single i (1 : K) := by
    intro v
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  refine ⟨f (Pi.single i₀ (1 : K)) i₀, fun v => ?_⟩
  conv_lhs => rw [hv v]
  conv_rhs => rw [hv v]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hfull i (v i), smul_smul, mul_comm]

section Field

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K K' : Type} [Field K] [Field K']
  {A : Type*} [AddCommGroup A] [Module K A]

theorem exists_ringEquiv_of_scalar_commutant [Nonempty ι] [Finite K] [Finite K']
    (hcard : Nat.card K = Nat.card K') {X : Subgroup (GL ι K')} (hX : AddCommutantScalar X)
    (ψ : A ≃+ (ι → K'))
    (hcomm : ∀ (c : K), ∀ B ∈ X, ∀ v : ι → K',
      ψ (c • ψ.symm ((B : Matrix ι ι K') *ᵥ v)) = (B : Matrix ι ι K') *ᵥ ψ (c • ψ.symm v)) :
    ∃ θ : K ≃+* K', ∀ (c : K) (a : A), ψ (c • a) = θ c • ψ a := by
  have hex : ∀ c : K, ∃ d : K', ∀ v : ι → K', ψ (c • ψ.symm v) = d • v := by
    intro c
    let φ : (ι → K') →+ (ι → K') :=
      { toFun := fun v => ψ (c • ψ.symm v)
        map_zero' := by simp
        map_add' := fun v w => by simp [smul_add] }
    exact hX φ fun B hB v => hcomm c B hB v
  choose θ hθ using hex
  have hθa : ∀ (c : K) (a : A), ψ (c • a) = θ c • ψ a := fun c a => by
    simpa using hθ c (ψ a)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set e : ι → K' := Pi.single i₀ 1 with he
  have hcoord : ∀ d d' : K', d • e = d' • e → d = d' := fun d d' h => by
    simpa [he] using congrFun h i₀
  have h0 : ∀ c : K, ψ (c • ψ.symm e) = θ c • e := fun c => by
    simpa using hθa c (ψ.symm e)
  have hone : θ 1 = 1 := hcoord _ _ (by rw [← h0, one_smul, one_smul]; simp)
  have hzero : θ 0 = 0 := hcoord _ _ (by rw [← h0, zero_smul, zero_smul]; simp)
  have hadd : ∀ c d : K, θ (c + d) = θ c + θ d := fun c d =>
    hcoord _ _ (by rw [← h0, add_smul, map_add, add_smul, h0, h0])
  have hmul : ∀ c d : K, θ (c * d) = θ c * θ d := fun c d =>
    hcoord _ _ (by
      rw [← h0, mul_smul, hθa, mul_smul, h0])
  let θr : K →+* K' :=
    { toFun := θ
      map_one' := hone
      map_mul' := hmul
      map_zero' := hzero
      map_add' := hadd }
  have hinj : Function.Injective θr := θr.injective
  have hbij : Function.Bijective θr :=
    hinj.bijective_of_nat_card_le (le_of_eq hcard.symm)
  exact ⟨RingEquiv.ofBijective θr hbij, fun c a => hθa c a⟩

end Field

end NatScalars

section SpScalars

open CFSG.Open CFSG.Open.StatedAPI
open Matrix

private def spJ (m : ℕ) (K : Type) [Field K] : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
  fromBlocks 0 1 (-1) 0

section Basic

variable {m : ℕ} {K : Type} [Field K]

private lemma spJ_mulVec_inl (v : Fin m ⊕ Fin m → K) (i : Fin m) :
    (spJ m K *ᵥ v) (Sum.inl i) = v (Sum.inr i) := by
  simp [spJ, mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

private lemma spJ_mulVec_inr (v : Fin m ⊕ Fin m → K) (i : Fin m) :
    (spJ m K *ᵥ v) (Sum.inr i) = -v (Sum.inl i) := by
  simp [spJ, mulVec, dotProduct, Fintype.sum_sum_type, Matrix.one_apply]

private lemma spJ_mulVec_spJ_mulVec (v : Fin m ⊕ Fin m → K) :
    spJ m K *ᵥ (spJ m K *ᵥ v) = -v := by
  funext c
  rcases c with i | i
  · rw [spJ_mulVec_inl, spJ_mulVec_inr, Pi.neg_apply]
  · rw [spJ_mulVec_inr, spJ_mulVec_inl, Pi.neg_apply]

private lemma spJ_mulVec_eq_zero {v : Fin m ⊕ Fin m → K} (h : spJ m K *ᵥ v = 0) : v = 0 := by
  have h2 := spJ_mulVec_spJ_mulVec (m := m) (K := K) v
  rw [h, mulVec_zero] at h2
  exact neg_eq_zero.mp h2.symm

private lemma spJ_dot_self (v : Fin m ⊕ Fin m → K) : (spJ m K *ᵥ v) ⬝ᵥ v = 0 := by
  simp only [dotProduct, Fintype.sum_sum_type, spJ_mulVec_inl, spJ_mulVec_inr, neg_mul,
    Finset.sum_neg_distrib]
  rw [add_neg_eq_zero]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private lemma spJ_transpose : (spJ m K)ᵀ = -spJ m K := by
  ext (i | i) (j | j) <;> simp [spJ, Matrix.one_apply, eq_comm]

private lemma vecMul_spJ (v : Fin m ⊕ Fin m → K) : v ᵥ* spJ m K = -(spJ m K *ᵥ v) := by
  have h := vecMul_transpose (spJ m K)ᵀ v
  rwa [transpose_transpose, spJ_transpose, neg_mulVec] at h

private lemma vecMulVec_mulVec' {ι : Type} [Fintype ι] (a b x : ι → K) :
    vecMulVec a b *ᵥ x = (b ⬝ᵥ x) • a := by
  funext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

private lemma vecMulVec_neg_right {ι : Type} (a b : ι → K) :
    vecMulVec a (-b) = -vecMulVec a b := by
  ext i j
  simp [vecMulVec_apply]

private lemma exists_dot_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] {w : ι → K}
    (hw : w ≠ 0) : ∃ x : ι → K, w ⬝ᵥ x = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    exact hw (funext fun i => not_not.mp (not_exists.mp h i))
  exact ⟨Pi.single i (w i)⁻¹, by rw [dotProduct_single, mul_inv_cancel₀ hi]⟩

end Basic

section Transvection

variable {m : ℕ} {K : Type} [Field K]

private def spTr (m : ℕ) (K : Type) [Field K] (c : K) (v : Fin m ⊕ Fin m → K) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
  1 + c • vecMulVec v (spJ m K *ᵥ v)

private lemma spTr_mulVec (c : K) (v x : Fin m ⊕ Fin m → K) :
    spTr m K c v *ᵥ x = x + (c * ((spJ m K *ᵥ v) ⬝ᵥ x)) • v := by
  unfold spTr
  rw [add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec', smul_smul]

private lemma spTr_zero (v : Fin m ⊕ Fin m → K) : spTr m K 0 v = 1 := by
  simp [spTr]

private lemma spTr_mul (c d : K) (v : Fin m ⊕ Fin m → K) :
    spTr m K c v * spTr m K d v = spTr m K (c + d) v := by
  have hNN : vecMulVec v (spJ m K *ᵥ v) * vecMulVec v (spJ m K *ᵥ v) = 0 := by
    rw [vecMulVec_mul_vecMulVec, spJ_dot_self, zero_smul, vecMulVec_zero]
  unfold spTr
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hNN, smul_zero,
    add_zero, add_smul]
  abel

private def spTrUnit (c : K) (v : Fin m ⊕ Fin m → K) : GL (Fin m ⊕ Fin m) K :=
  Units.mk (spTr m K c v) (spTr m K (-c) v)
    (by rw [spTr_mul, add_neg_cancel, spTr_zero]) (by rw [spTr_mul, neg_add_cancel, spTr_zero])

private lemma spTr_symp (c : K) (v : Fin m ⊕ Fin m → K) :
    (spTr m K c v)ᵀ * spJ m K * spTr m K c v = spJ m K := by
  have hw : (spJ m K *ᵥ v) ⬝ᵥ v = 0 := spJ_dot_self v
  have hJN : spJ m K * vecMulVec v (spJ m K *ᵥ v) =
      vecMulVec (spJ m K *ᵥ v) (spJ m K *ᵥ v) := mul_vecMulVec _ _ _
  have hNJ : vecMulVec (spJ m K *ᵥ v) v * spJ m K =
      -vecMulVec (spJ m K *ᵥ v) (spJ m K *ᵥ v) := by
    rw [vecMulVec_mul, vecMul_spJ, vecMulVec_neg_right]
  have hNW : vecMulVec (spJ m K *ᵥ v) v * vecMulVec (spJ m K *ᵥ v) (spJ m K *ᵥ v) = 0 := by
    rw [vecMulVec_mul_vecMulVec, dotProduct_comm, hw, zero_smul, vecMulVec_zero]
  unfold spTr
  rw [transpose_add, transpose_one, transpose_smul, transpose_vecMulVec]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, Matrix.mul_assoc]
  rw [hJN, hNJ, hNW]
  simp only [smul_zero, add_zero, smul_neg]
  abel

private lemma spTrUnit_mem (c : K) (v : Fin m ⊕ Fin m → K) : spTrUnit c v ∈ StatedSp m K := by
  rw [mem_statedSp_iff]
  exact spTr_symp c v

private lemma sp_key (f : (Fin m ⊕ Fin m → K) →+ (Fin m ⊕ Fin m → K))
    (hf : ∀ A ∈ StatedSp m K, ∀ v, f ((A : Matrix _ _ K) *ᵥ v) = (A : Matrix _ _ K) *ᵥ f v)
    (c : K) (v x : Fin m ⊕ Fin m → K) :
    f ((c * ((spJ m K *ᵥ v) ⬝ᵥ x)) • v) = (c * ((spJ m K *ᵥ v) ⬝ᵥ f x)) • v := by
  have h : f (spTr m K c v *ᵥ x) = spTr m K c v *ᵥ f x := hf _ (spTrUnit_mem c v) x
  rw [spTr_mulVec, spTr_mulVec, map_add] at h
  exact add_left_cancel h

end Transvection

theorem addCommutantScalar_statedSp {K : Type} [Field K] {m : ℕ} :
    AddCommutantScalar (StatedSp m K) := by
  intro f hf
  have hev : ∀ v : Fin m ⊕ Fin m → K, ∃ β : K, ∀ c : K, f (c • v) = (c * β) • v := by
    intro v
    by_cases hv : v = 0
    · exact ⟨0, fun c => by simp [hv]⟩
    · have hw : spJ m K *ᵥ v ≠ 0 := fun h => hv (spJ_mulVec_eq_zero h)
      obtain ⟨x, hx⟩ := exists_dot_eq_one hw
      refine ⟨(spJ m K *ᵥ v) ⬝ᵥ f x, fun c => ?_⟩
      have h := sp_key f hf c v x
      rwa [hx, mul_one] at h
  have hfv : ∀ v : Fin m ⊕ Fin m → K, ∃ β : K, f v = β • v := fun v => by
    obtain ⟨β, hβ⟩ := hev v
    exact ⟨β, by simpa using hβ 1⟩
  have hhom : ∀ (c : K) (v : Fin m ⊕ Fin m → K), f (c • v) = c • f v := by
    intro c v
    obtain ⟨β, hβ⟩ := hev v
    have h1 : f v = β • v := by simpa using hβ 1
    rw [hβ c, h1, smul_smul]
  let F : (Fin m ⊕ Fin m → K) →ₗ[K] (Fin m ⊕ Fin m → K) :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c v => hhom c v }
  have hdep : ∀ v : Fin m ⊕ Fin m → K, ¬ LinearIndependent K ![v, F v] := by
    intro v hli
    obtain ⟨β, hβ⟩ := hfv v
    have h := LinearIndependent.pair_iff.mp hli β (-1)
      (by rw [show F v = β • v from hβ, neg_one_smul, add_neg_cancel])
    exact one_ne_zero (neg_eq_zero.mp h.2)
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hdep
  exact ⟨a, fun v => by
    show F v = a • v
    rw [ha]
    simp⟩

end SpScalars

section OmegaScalars

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped Matrix commutatorElement

section Homogeneous

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private def homSubmodule (f : V →+ V) : Submodule K V where
  carrier := {v | ∀ l : K, f (l • v) = l • f v}
  zero_mem' := fun l => by simp
  add_mem' := fun {v w} hv hw l => by
    rw [smul_add, map_add, hv l, hw l, map_add, smul_add]
  smul_mem' := fun c v hv l => by
    rw [smul_smul, hv (l * c), hv c, smul_smul]

private theorem map_mem_homSubmodule {f : V →+ V} {g : V ≃ₗ[K] V}
    (hg : ∀ x, f (g x) = g (f x)) {v : V}
    (hv : v ∈ homSubmodule (K := K) f) : g v ∈ homSubmodule (K := K) f := by
  intro l
  rw [← map_smul g l v, hg, hv l, map_smul, hg]

private theorem eq_smul_of_basis {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → K) →+ (ι → K)) (a : K)
    (hhom : ∀ k : ι, (Pi.single k (1 : K) : ι → K) ∈ homSubmodule (K := K) f)
    (heig : ∀ k : ι, f (Pi.single k (1 : K)) = a • (Pi.single k (1 : K) : ι → K))
    (v : ι → K) : f v = a • v := by
  have hdec : v = ∑ k, v k • (Pi.single k (1 : K) : ι → K) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hdec, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hhom k (v k), heig k, smul_comm]

end Homogeneous

section Eichler

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem eq_smul_of_commute_eichler (f : V →+ V) {u w x : V} (hu : Q u = 0)
    (hw : polar Q u w = 0) (hxu : polar Q x u = 0) (hxw : polar Q x w = 1) (l : K)
    (hE : f (eichler Q u (l • w) x) = eichler Q u (l • w) (f x)) :
    f (l • u) = (-(l * polar Q (f x) u)) • w +
      (l * polar Q (f x) w + l ^ 2 * Q w * polar Q (f x) u) • u := by
  have hl : polar Q u (l • w) = 0 := by rw [polar_smul_right_eq, hw, mul_zero]
  rw [eichler_apply hu hl x, eichler_apply hu hl (f x)] at hE
  simp only [hxu, hxw, polar_smul_right_eq, map_smul_eq_sq, zero_smul, add_zero, mul_zero,
    mul_one, map_sub] at hE
  linear_combination (norm := module) (-1 : K) • hE

private theorem mem_homSubmodule_of_commute_eichler (f : V →+ V) {u w₀ w₁ x₀ x₁ : V} (hu : Q u = 0)
    (hw₀ : polar Q u w₀ = 0) (hw₁ : polar Q u w₁ = 0)
    (hx₀u : polar Q x₀ u = 0) (hx₀ : polar Q x₀ w₀ = 1)
    (hx₁u : polar Q x₁ u = 0) (hx₁ : polar Q x₁ w₁ = 1)
    (hind : ∀ a b c : K, a • u + b • w₀ + c • w₁ = 0 → b = 0 ∧ c = 0)
    (hE₀ : ∀ l : K, f (eichler Q u (l • w₀) x₀) = eichler Q u (l • w₀) (f x₀))
    (hE₁ : ∀ l : K, f (eichler Q u (l • w₁) x₁) = eichler Q u (l • w₁) (f x₁)) :
    u ∈ homSubmodule (K := K) f ∧ ∃ γ : K, f u = γ • u := by
  have h0 := fun l : K => eq_smul_of_commute_eichler f hu hw₀ hx₀u hx₀ l (hE₀ l)
  have h1 := fun l : K => eq_smul_of_commute_eichler f hu hw₁ hx₁u hx₁ l (hE₁ l)
  have h0' := h0 1
  have h1' := h1 1
  simp only [one_smul, one_mul, one_pow] at h0' h1'
  have hβ := hind ((polar Q (f x₀) w₀ + Q w₀ * polar Q (f x₀) u) -
      (polar Q (f x₁) w₁ + Q w₁ * polar Q (f x₁) u)) (-polar Q (f x₀) u) (polar Q (f x₁) u)
    (by linear_combination (norm := module) (-1 : K) • h0' + (1 : K) • h1')
  have hb0 : polar Q (f x₀) u = 0 := neg_eq_zero.mp hβ.1
  refine ⟨fun l => ?_, polar Q (f x₀) w₀, ?_⟩
  · have e1 := h0 l
    rw [hb0] at e1 h0'
    rw [e1, h0']
    module
  · rw [hb0] at h0'
    rw [h0']
    module

private theorem exists_perp_polar_eq_one (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    {x : V} (hx : x ∈ P.perp) (hx0 : x ≠ 0) : ∃ y ∈ P.perp, polar Q x y = 1 := by
  obtain ⟨y₀, hy₀, hne⟩ := (HypPair.polarNondegOn_perp hQ P).exists_polar_ne_zero hx hx0
  exact ⟨(polar Q x y₀)⁻¹ • y₀, P.perp.smul_mem _ hy₀, by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hne]⟩

private theorem eichler_mem_commutator_of_perp (hQ : (polarBilin Q).Nondegenerate)
    (P : HypPair Q) {u x : V} (hpu : ∀ y ∈ P.perp, polar Q u y = 0) (hx : x ∈ P.perp)
    (hQx : Q x ≠ 0) :
    eichler Q u x ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hx0 : x ≠ 0 := fun h => hQx (by rw [h, QuadraticMap.map_zero])
  obtain ⟨y₁, hy₁, hxy₁⟩ := exists_perp_polar_eq_one hQ P hx hx0
  obtain ⟨y, hyP, hxy⟩ : ∃ y ∈ P.perp, polar Q x y = -Q x :=
    ⟨(-Q x) • y₁, P.perp.smul_mem _ hy₁, by rw [polar_smul_right_eq, hxy₁, mul_one]⟩
  have hxu : polar Q x u = 0 := by rw [polar_comm]; exact hpu x hx
  have hgu : reflect Q x u = u := reflect_apply_of_polar_eq_zero hxu
  have hr : reflect Q x y - y = x := by
    rw [reflect_apply hQx, hxy, neg_div, div_self hQx, neg_one_smul]
    abel
  have hc := commutatorElement_eichler (reflect_mem_orthogonalGroup Q x) hgu (hpu y hyP)
  rw [hr] at hc
  rw [← hc]
  exact Subgroup.commutator_mem_commutator (reflect_mem_orthogonalGroup Q x)
    (eichler_mem_orthogonalGroup Q u y)

private theorem eichler_smul_mem_commutator (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    {u w : V} (hpu : ∀ y ∈ P.perp, polar Q u y = 0) (hw : w ∈ P.perp) (hQw : Q w ≠ 0) (l : K) :
    eichler Q u (l • w) ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  by_cases hl : l = 0
  · rw [hl, zero_smul, eichler_zero_right]
    exact Subgroup.one_mem _
  · refine eichler_mem_commutator_of_perp hQ P hpu (P.perp.smul_mem l hw) ?_
    rw [map_smul_eq_sq]
    exact mul_ne_zero (pow_ne_zero 2 hl) hQw

private theorem hyp_mem_homSubmodule (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    (f : V →+ V)
    (hf : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, ∀ v, f (g v) = g (f v))
    {w₀ w₁ : V} (hw₀ : w₀ ∈ P.perp) (hw₁ : w₁ ∈ P.perp) (hQ₀ : Q w₀ ≠ 0) (hQ₁ : Q w₁ ≠ 0)
    (hindE : ∀ a b c : K, a • P.e + b • w₀ + c • w₁ = 0 → b = 0 ∧ c = 0)
    (hindF : ∀ a b c : K, a • P.f + b • w₀ + c • w₁ = 0 → b = 0 ∧ c = 0) :
    (P.e ∈ homSubmodule (K := K) f ∧ ∃ γ : K, f P.e = γ • P.e) ∧
      (P.f ∈ homSubmodule (K := K) f ∧ ∃ γ : K, f P.f = γ • P.f) := by
  have hw₀0 : w₀ ≠ 0 := fun h => hQ₀ (by rw [h, QuadraticMap.map_zero])
  have hw₁0 : w₁ ≠ 0 := fun h => hQ₁ (by rw [h, QuadraticMap.map_zero])
  obtain ⟨x₀, hx₀P, hx₀⟩ := exists_perp_polar_eq_one hQ P hw₀ hw₀0
  obtain ⟨x₁, hx₁P, hx₁⟩ := exists_perp_polar_eq_one hQ P hw₁ hw₁0
  have hpe : ∀ y ∈ P.perp, polar Q P.e y = 0 := fun y hy => (HypPair.mem_perp.mp hy).1
  have hpf : ∀ y ∈ P.perp, polar Q P.f y = 0 := fun y hy => (HypPair.mem_perp.mp hy).2
  have hx₀' : polar Q x₀ w₀ = 1 := by rw [polar_comm]; exact hx₀
  have hx₁' : polar Q x₁ w₁ = 1 := by rw [polar_comm]; exact hx₁
  refine ⟨mem_homSubmodule_of_commute_eichler f P.Q_e (hpe _ hw₀) (hpe _ hw₁)
    (by rw [polar_comm]; exact hpe _ hx₀P) hx₀' (by rw [polar_comm]; exact hpe _ hx₁P) hx₁'
    hindE (fun l => hf _ (eichler_smul_mem_commutator hQ P hpe hw₀ hQ₀ l) x₀)
    (fun l => hf _ (eichler_smul_mem_commutator hQ P hpe hw₁ hQ₁ l) x₁),
    mem_homSubmodule_of_commute_eichler f P.Q_f (hpf _ hw₀) (hpf _ hw₁)
    (by rw [polar_comm]; exact hpf _ hx₀P) hx₀' (by rw [polar_comm]; exact hpf _ hx₁P) hx₁'
    hindF (fun l => hf _ (eichler_smul_mem_commutator hQ P hpf hw₀ hQ₀ l) x₀)
    (fun l => hf _ (eichler_smul_mem_commutator hQ P hpf hw₁ hQ₁ l) x₁)⟩

private theorem mem_homSubmodule_of_perp (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    (f : V →+ V)
    (hf : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, ∀ v, f (g v) = g (f v))
    (he : P.e ∈ homSubmodule (K := K) f) (hfm : P.f ∈ homSubmodule (K := K) f) {x : V}
    (hx : x ∈ P.perp) (hQx : Q x ≠ 0) : x ∈ homSubmodule (K := K) f := by
  have hpe : ∀ y ∈ P.perp, polar Q P.e y = 0 := fun y hy => (HypPair.mem_perp.mp hy).1
  have hE := eichler_mem_commutator_of_perp hQ P hpe hx hQx
  have hEf : eichler Q P.e x P.f = P.f + x - Q x • P.e := by
    rw [eichler_apply P.Q_e (HypPair.mem_perp.mp hx).1 P.f, P.polar_fe,
      (HypPair.mem_perp.mp hx).2]
    module
  have h1 : eichler Q P.e x P.f ∈ homSubmodule (K := K) f :=
    map_mem_homSubmodule (fun v => hf _ hE v) hfm
  have hxe : x = (eichler Q P.e x P.f - P.f) + Q x • P.e := by
    rw [hEf]
    module
  rw [hxe]
  exact Submodule.add_mem _ (Submodule.sub_mem _ h1 hfm) (Submodule.smul_mem _ _ he)

private theorem eq_smul_of_perp (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q) (f : V →+ V)
    (hf : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, ∀ v, f (g v) = g (f v))
    (he : P.e ∈ homSubmodule (K := K) f) (hfm : P.f ∈ homSubmodule (K := K) f) {a b : K}
    (hfe : f P.e = a • P.e) (hff : f P.f = b • P.f) {x : V} (hx : x ∈ P.perp)
    (hQx : Q x ≠ 0) : b = a ∧ f x = a • x := by
  have hxe : polar Q P.e x = 0 := (HypPair.mem_perp.mp hx).1
  have hxf : polar Q P.f x = 0 := (HypPair.mem_perp.mp hx).2
  have hpe : ∀ y ∈ P.perp, polar Q P.e y = 0 := fun y hy => (HypPair.mem_perp.mp hy).1
  have hpf : ∀ y ∈ P.perp, polar Q P.f y = 0 := fun y hy => (HypPair.mem_perp.mp hy).2
  have hEe := eichler_mem_commutator_of_perp hQ P hpe hx hQx
  have hEf := eichler_mem_commutator_of_perp hQ P hpf hx hQx
  have hEef : eichler Q P.e x P.f = P.f + x - Q x • P.e := by
    rw [eichler_apply P.Q_e hxe P.f, P.polar_fe, hxf]
    module
  have hEfe : eichler Q P.f x P.e = P.e + x - Q x • P.f := by
    rw [eichler_apply P.Q_f hxf P.e, P.polar_ef, hxe]
    module
  have h1 : f x = b • x + (Q x * (a - b)) • P.e := by
    have h := hf _ hEe P.f
    rw [hEef, hff, map_smul, hEef, map_sub, map_add, hff, he (Q x), hfe] at h
    linear_combination (norm := module) h
  have h2 : f x = a • x + (Q x * (b - a)) • P.f := by
    have h := hf _ hEf P.e
    rw [hEfe, hfe, map_smul, hEfe, map_sub, map_add, hfe, hfm (Q x), hff] at h
    linear_combination (norm := module) h
  have hba : b = a := by
    have e1 : polar Q P.e (f x) = 0 := by
      rw [h1, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hxe, P.polar_ee]
      ring
    have e2 : polar Q P.e (f x) = Q x * (b - a) := by
      rw [h2, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hxe, P.polar_ef]
      ring
    have e3 : Q x * (b - a) = 0 := by rw [← e2]; exact e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp e3).resolve_left hQx)
  refine ⟨hba, ?_⟩
  rw [h1, hba, sub_self, mul_zero, zero_smul, add_zero]

end Eichler

section Dictionary

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

private theorem commute_of_mem_derivedOrthogonal {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}
    (hQ : ⇑Q = Q₀) (f : (ι → K) →+ (ι → K))
    (hf : ∀ A ∈ StatedOmega Q₀, ∀ v, f ((A : Matrix ι ι K) *ᵥ v) = (A : Matrix ι ι K) *ᵥ f v)
    {g : (ι → K) ≃ₗ[K] (ι → K)}
    (hg : g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆) (v : ι → K) : f (g v) = g (f v) := by
  obtain ⟨A, hAg⟩ : ∃ A : GL ι K, toLinEquiv ι K A = g :=
    ⟨(toLinEquiv ι K).symm g, (toLinEquiv ι K).apply_symm_apply g⟩
  have hA : A ∈ StatedOmega Q₀ := by
    rw [statedOmega_eq_comap hQ, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hAg]
    exact hg
  have hgA : ∀ w, g w = (A : Matrix ι ι K) *ᵥ w := fun w => by rw [← hAg, toLinEquiv_apply]
  rw [hgA v, hf A hA v, hgA (f v)]

end Dictionary

section Plus

variable {K : Type} [Field K] {m : ℕ}

private lemma exists_two_ne (hm : 3 ≤ m) (i : Fin m) :
    ∃ j k : Fin m, j ≠ i ∧ k ≠ i ∧ j ≠ k := by
  have h : 1 < (Finset.univ.erase i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp h
  exact ⟨j, k, (Finset.mem_erase.mp hj).1, (Finset.mem_erase.mp hk).1, hjk⟩

private def plusAniso (K : Type) [Field K] (j : Fin m) : Fin m ⊕ Fin m → K :=
  Pi.single (Sum.inl j) 1 + Pi.single (Sum.inr j) 1

private lemma quadPlus_plusAniso (j : Fin m) : quadPlus m K (plusAniso K j) = 1 := by
  rw [plusAniso, QuadraticMap.map_add (quadPlus m K), quadPlus_single, quadPlus_single,
    polar_single_inl_quadPlus]
  simp

private lemma plusAniso_inl_self (j : Fin m) : plusAniso K j (Sum.inl j) = 1 := by
  simp [plusAniso, Pi.single_apply]

private lemma plusAniso_mem_perp {i j : Fin m} (hij : j ≠ i) :
    plusAniso K j ∈ (plusPair K i).perp := by
  rw [HypPair.mem_perp, plusPair_e, plusPair_f, polar_single_inl_quadPlus,
    polar_single_inr_quadPlus]
  simp [plusAniso, Pi.single_apply, hij, hij.symm]

private lemma plus_hyp_mem_hom (f : (Fin m ⊕ Fin m → K) →+ (Fin m ⊕ Fin m → K))
    (hf : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K)⁆, ∀ v, f (g v) = g (f v))
    {i j k : Fin m} (hji : j ≠ i) (hki : k ≠ i) (hjk : j ≠ k) :
    ((Pi.single (Sum.inl i) 1 : Fin m ⊕ Fin m → K) ∈ homSubmodule (K := K) f ∧
        ∃ γ : K, f (Pi.single (Sum.inl i) 1) =
          γ • (Pi.single (Sum.inl i) 1 : Fin m ⊕ Fin m → K)) ∧
      ((Pi.single (Sum.inr i) 1 : Fin m ⊕ Fin m → K) ∈ homSubmodule (K := K) f ∧
        ∃ γ : K, f (Pi.single (Sum.inr i) 1) =
          γ • (Pi.single (Sum.inr i) 1 : Fin m ⊕ Fin m → K)) := by
  refine hyp_mem_homSubmodule (nondegenerate_polarBilin_quadPlus m K) (plusPair K i) f hf
    (plusAniso_mem_perp hji) (plusAniso_mem_perp hki)
    (by rw [quadPlus_plusAniso]; exact one_ne_zero)
    (by rw [quadPlus_plusAniso]; exact one_ne_zero) ?_ ?_
  · intro a b c h
    have h1 := congrFun h (Sum.inl j)
    have h2 := congrFun h (Sum.inl k)
    simp [plusPair_e, plusAniso, Pi.single_apply, hji, hki, hjk, hjk.symm] at h1 h2
    exact ⟨h1, h2⟩
  · intro a b c h
    have h1 := congrFun h (Sum.inl j)
    have h2 := congrFun h (Sum.inl k)
    simp [plusPair_f, plusAniso, Pi.single_apply, hji, hki, hjk, hjk.symm] at h1 h2
    exact ⟨h1, h2⟩

theorem addCommutantScalar_statedOmegaPlus (hm : 3 ≤ m) :
    AddCommutantScalar (StatedOmega (StatedQuadPlus m K)) := by
  intro f hf
  have hcomm : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K),
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K)⁆, ∀ v, f (g v) = g (f v) :=
    fun g hg v => commute_of_mem_derivedOrthogonal (coe_quadPlus m K) f hf hg v
  have hnd := nondegenerate_polarBilin_quadPlus m K
  have hpair : ∀ i : Fin m, ∃ a b : K,
      ((Pi.single (Sum.inl i) 1 : Fin m ⊕ Fin m → K) ∈ homSubmodule (K := K) f ∧
        f (Pi.single (Sum.inl i) 1) = a • (Pi.single (Sum.inl i) 1 : Fin m ⊕ Fin m → K)) ∧
      ((Pi.single (Sum.inr i) 1 : Fin m ⊕ Fin m → K) ∈ homSubmodule (K := K) f ∧
        f (Pi.single (Sum.inr i) 1) = b • (Pi.single (Sum.inr i) 1 : Fin m ⊕ Fin m → K)) := by
    intro i
    obtain ⟨j, k, hji, hki, hjk⟩ := exists_two_ne hm i
    obtain ⟨⟨he, a, ha⟩, ⟨hfm, b, hb⟩⟩ := plus_hyp_mem_hom f hcomm hji hki hjk
    exact ⟨a, b, ⟨he, ha⟩, ⟨hfm, hb⟩⟩
  choose a b hpe hpf using hpair
  have hK : ∀ i k : Fin m, k ≠ i → b i = a i ∧ f (plusAniso K k) = a i • plusAniso K k :=
    fun i k hki => eq_smul_of_perp hnd (plusPair K i) f hcomm (hpe i).1 (hpf i).1 (hpe i).2
      (hpf i).2 (plusAniso_mem_perp hki) (by rw [quadPlus_plusAniso]; exact one_ne_zero)
  have hab : ∀ i : Fin m, b i = a i := fun i => by
    obtain ⟨j, -, hji, -, -⟩ := exists_two_ne hm i
    exact (hK i j hji).1
  have haeq : ∀ i j : Fin m, a i = a j := by
    intro i j
    obtain ⟨j', k', hj'i, hk'i, hjk'⟩ := exists_two_ne hm i
    obtain ⟨k, hki, hkj⟩ : ∃ k : Fin m, k ≠ i ∧ k ≠ j := by
      by_cases h : j' = j
      · exact ⟨k', hk'i, fun h' => hjk' (h.trans h'.symm)⟩
      · exact ⟨j', hj'i, h⟩
    have h := ((hK i k hki).2.symm).trans (hK j k hkj).2
    have h' := congrFun h (Sum.inl k)
    simpa [plusAniso_inl_self] using h'
  obtain ⟨i₀⟩ : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  refine ⟨a i₀, eq_smul_of_basis f (a i₀) ?_ ?_⟩
  · rintro (i | i)
    · exact (hpe i).1
    · exact (hpf i).1
  · rintro (i | i)
    · rw [(hpe i).2, haeq i i₀]
    · rw [(hpf i).2, hab i, haeq i i₀]

end Plus

section Minus

variable {K : Type} [Field K] {m : ℕ} {b c : K}

private lemma quadMinus_single_inr_inr_zero :
    quadMinus m K b c (Pi.single (Sum.inr (Sum.inr 0)) 1) = 1 := by
  rw [quadMinus_apply]
  simp [Pi.single_apply]

private lemma quadMinus_single_inr_inr_one :
    quadMinus m K b c (Pi.single (Sum.inr (Sum.inr 1)) 1) = c := by
  rw [quadMinus_apply]
  simp [Pi.single_apply]

private lemma single_inr_inr_mem_perp (i : Fin (m - 1)) (j : Fin 2) :
    (Pi.single (Sum.inr (Sum.inr j)) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ∈
      (minusPair K b c i).perp := by
  rw [HypPair.mem_perp, minusPair_e, minusPair_f, polar_single_inl_quadMinus,
    polar_single_inr_quadMinus]
  simp [Pi.single_apply]

private lemma minus_hyp_mem_hom [Finite K] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (f : (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) →+ (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K))
    (hf : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus m K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus m K b c)⁆, ∀ v, f (g v) = g (f v))
    (i : Fin (m - 1)) :
    ((Pi.single (Sum.inl i) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ∈
        homSubmodule (K := K) f ∧
      ∃ γ : K, f (Pi.single (Sum.inl i) 1) =
        γ • (Pi.single (Sum.inl i) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)) ∧
    ((Pi.single (Sum.inr (Sum.inl i)) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ∈
        homSubmodule (K := K) f ∧
      ∃ γ : K, f (Pi.single (Sum.inr (Sum.inl i)) 1) =
        γ • (Pi.single (Sum.inr (Sum.inl i)) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)) := by
  have hc0 : c ≠ 0 := by simpa using hirr 0
  refine hyp_mem_homSubmodule (nondegenerate_polarBilin_quadMinus_of_finite m K hirr)
    (minusPair K b c i) f hf (single_inr_inr_mem_perp i 0) (single_inr_inr_mem_perp i 1)
    (by rw [quadMinus_single_inr_inr_zero]; exact one_ne_zero)
    (by rw [quadMinus_single_inr_inr_one]; exact hc0) ?_ ?_
  · intro a β γ h
    have h1 := congrFun h (Sum.inr (Sum.inr 0))
    have h2 := congrFun h (Sum.inr (Sum.inr 1))
    simp [minusPair_e, Pi.single_apply] at h1 h2
    exact ⟨h1, h2⟩
  · intro a β γ h
    have h1 := congrFun h (Sum.inr (Sum.inr 0))
    have h2 := congrFun h (Sum.inr (Sum.inr 1))
    simp [minusPair_f, Pi.single_apply] at h1 h2
    exact ⟨h1, h2⟩

theorem addCommutantScalar_statedOmegaMinus [Finite K] (hm : 2 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    AddCommutantScalar (StatedOmega (StatedQuadMinus m K b c)) := by
  intro f hf
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite m K hirr
  have hc0 : c ≠ 0 := by simpa using hirr 0
  have hcomm : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus m K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus m K b c)⁆, ∀ v, f (g v) = g (f v) :=
    fun g hg v => commute_of_mem_derivedOrthogonal (coe_quadMinus m K b c) f hf hg v
  obtain ⟨i0⟩ : Nonempty (Fin (m - 1)) := ⟨⟨0, by omega⟩⟩
  have hpair : ∀ i : Fin (m - 1), ∃ a a' : K,
      ((Pi.single (Sum.inl i) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ∈
          homSubmodule (K := K) f ∧
        f (Pi.single (Sum.inl i) 1) =
          a • (Pi.single (Sum.inl i) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)) ∧
      ((Pi.single (Sum.inr (Sum.inl i)) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ∈
          homSubmodule (K := K) f ∧
        f (Pi.single (Sum.inr (Sum.inl i)) 1) =
          a' • (Pi.single (Sum.inr (Sum.inl i)) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)) := by
    intro i
    obtain ⟨⟨he, a, ha⟩, ⟨hfm, a', ha'⟩⟩ := minus_hyp_mem_hom hirr f hcomm i
    exact ⟨a, a', ⟨he, ha⟩, ⟨hfm, ha'⟩⟩
  choose a a' hpe hpf using hpair
  have hx₁ : ∀ i : Fin (m - 1), a' i = a i ∧
      f (Pi.single (Sum.inr (Sum.inr 0)) 1) = a i • (Pi.single (Sum.inr (Sum.inr 0)) 1 :
        Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := fun i =>
    eq_smul_of_perp hQ (minusPair K b c i) f hcomm (hpe i).1 (hpf i).1 (hpe i).2 (hpf i).2
      (single_inr_inr_mem_perp i 0) (by rw [quadMinus_single_inr_inr_zero]; exact one_ne_zero)
  have hx₂ : ∀ i : Fin (m - 1),
      f (Pi.single (Sum.inr (Sum.inr 1)) 1) = a i • (Pi.single (Sum.inr (Sum.inr 1)) 1 :
        Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := fun i =>
    (eq_smul_of_perp hQ (minusPair K b c i) f hcomm (hpe i).1 (hpf i).1 (hpe i).2 (hpf i).2
      (single_inr_inr_mem_perp i 1) (by rw [quadMinus_single_inr_inr_one]; exact hc0)).2
  have haeq : ∀ i : Fin (m - 1), a i = a i0 := by
    intro i
    have h := ((hx₁ i).2.symm).trans (hx₁ i0).2
    have h' := congrFun h (Sum.inr (Sum.inr 0))
    simpa using h'
  have hhomj : ∀ j : Fin 2, (Pi.single (Sum.inr (Sum.inr j)) (1 : K) :
      Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ∈ homSubmodule (K := K) f :=
    Fin.forall_fin_two.mpr
      ⟨mem_homSubmodule_of_perp hQ (minusPair K b c i0) f hcomm (hpe i0).1 (hpf i0).1
        (single_inr_inr_mem_perp i0 0)
        (by rw [quadMinus_single_inr_inr_zero]; exact one_ne_zero),
       mem_homSubmodule_of_perp hQ (minusPair K b c i0) f hcomm (hpe i0).1 (hpf i0).1
        (single_inr_inr_mem_perp i0 1)
        (by rw [quadMinus_single_inr_inr_one]; exact hc0)⟩
  have heigj : ∀ j : Fin 2, f (Pi.single (Sum.inr (Sum.inr j)) 1) =
      a i0 • (Pi.single (Sum.inr (Sum.inr j)) 1 : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) :=
    Fin.forall_fin_two.mpr ⟨(hx₁ i0).2, hx₂ i0⟩
  refine ⟨a i0, eq_smul_of_basis f (a i0) ?_ ?_⟩
  · rintro (i | i | j)
    · exact (hpe i).1
    · exact (hpf i).1
    · exact hhomj j
  · rintro (i | i | j)
    · rw [(hpe i).2, haeq i]
    · rw [(hpf i).2, (hx₁ i).1, haeq i]
    · exact heigj j

end Minus

end OmegaScalars

end CFSG.RankThree.GF2n.Stroth80
