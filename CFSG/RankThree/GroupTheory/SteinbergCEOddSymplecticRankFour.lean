module

public import CFSG.RankThree.CentralCover.SteinbergBNVectorPairing
public import CFSG.RankThree.Classical.SteinbergBJProjectiveSiegelRadical
public import CFSG.RankThree.CentralLift.DefiningSymplectic
import CFSG.RankThree.CentralCover.SteinbergBNCommutingSL2OddField
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import CFSG.Milestones.LC_GL_local_rank_bounds
public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore

public section

universe u

namespace CFSG.RankThree.GroupTheory

open Matrix CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.RankThree.CentralCover
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (leviSp lam coe_lam statedSp_ext
  pairMat pairMat_apply_of_ne pairMat_apply_pair)

section Matrices

variable {k : Type} [Field k] {n : ℕ}

theorem diagonal_mul_single_mul_diagonal (d : Fin n → k) (i j : Fin n) (x : k) :
    diagonal d * single i j x * diagonal d = single i j (d i * x * d j) := by
  ext r s
  rw [mul_diagonal, diagonal_mul, single_apply, single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rfl
  · rw [mul_zero, zero_mul]

theorem permGL_mul_single_mul_transpose (σ : Equiv.Perm (Fin n)) (i : Fin n) (x : k) :
    ((permMatrixHom.toHomUnits σ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * single i i x *
      ((permMatrixHom.toHomUnits σ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)ᵀ =
      single (σ i) (σ i) x := by
  rw [MonoidHom.coe_toHomUnits, permMatrixHom_apply, transpose_permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext r s
  simp only [submatrix_apply, id, single_apply, inv_inv]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1]; simp, by rw [h2]; simp⟩
  · rintro ⟨rfl, rfl⟩
    simp

end Matrices

section Conj

variable {k : Type} [Field k] {n : ℕ}

theorem torus_conj_siegelSpHom (δ : Fin n → kˣ) {B B' : symMatrices n k}
    (h : diagonal (fun i => (δ i : k)) * (B : Matrix (Fin n) (Fin n) k) *
      diagonal (fun i => (δ i : k)) = B') :
    (⟨torusGL δ, torusGL_mem_statedSp δ⟩ : StatedSp n k) * siegelSpHom n k (.ofAdd B) *
        (⟨torusGL δ, torusGL_mem_statedSp δ⟩ : StatedSp n k)⁻¹ =
      siegelSpHom n k (.ofAdd B') := by
  apply Subtype.ext
  change torusGL δ * siegelGL (B : Matrix (Fin n) (Fin n) k) * (torusGL δ)⁻¹ =
    siegelGL (B' : Matrix (Fin n) (Fin n) k)
  rw [torusGL_conj_siegelGL, h]

theorem leviSp_conj_siegelSpHom (A : GL (Fin n) k) {B B' : symMatrices n k}
    (h : (A : Matrix (Fin n) (Fin n) k) * (B : Matrix (Fin n) (Fin n) k) *
      (A : Matrix (Fin n) (Fin n) k)ᵀ = B') :
    leviSp A * siegelSpHom n k (.ofAdd B) * (leviSp A)⁻¹ = siegelSpHom n k (.ofAdd B') := by
  apply statedSp_ext
  rw [CFSG.RankThree.CentralLift.coe_leviSp_conj A (B := (B : Matrix (Fin n) (Fin n) k)) rfl, h]
  rfl

theorem mk_conj_eq {g x y : StatedSp n k} (h : g * x * g⁻¹ = y) :
    (g : StatedProj (StatedSp n k)) * (x : StatedProj (StatedSp n k)) *
      (g : StatedProj (StatedSp n k))⁻¹ = (y : StatedProj (StatedSp n k)) := by
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

end Conj

section Four

variable {k : Type} [Field k] {n : ℕ} (p : ℕ) [CharP k p] (a b c : Fin n)

@[expose] def fourMat (v : Fin 4 → ZMod p) : Matrix (Fin n) (Fin n) k :=
  single a a (ZMod.castHom dvd_rfl k (v 0)) + single a b (ZMod.castHom dvd_rfl k (v 1)) +
    single b a (ZMod.castHom dvd_rfl k (v 1)) + single b b (ZMod.castHom dvd_rfl k (v 2)) +
    single c c (ZMod.castHom dvd_rfl k (v 3))

theorem fourMat_transpose (v : Fin 4 → ZMod p) :
    (fourMat (k := k) p a b c v)ᵀ = fourMat p a b c v := by
  simp only [fourMat, transpose_add, transpose_single]
  abel

theorem fourMat_add (v w : Fin 4 → ZMod p) :
    fourMat (k := k) p a b c (v + w) = fourMat p a b c v + fourMat p a b c w := by
  simp only [fourMat, Pi.add_apply, map_add, single_add]
  abel

theorem fourMat_zero : fourMat (k := k) p a b c 0 = 0 := by
  simp [fourMat]

@[expose] def fourHom : (Fin 4 → ZMod p) →+ symMatrices n k where
  toFun v := ⟨fourMat p a b c v, fourMat_transpose p a b c v⟩
  map_zero' := Subtype.ext (fourMat_zero p a b c)
  map_add' v w := Subtype.ext (fourMat_add p a b c v w)

@[expose] def fourTheta : Multiplicative (Fin 4 → ZMod p) →* StatedProj (StatedSp n k) :=
  (projSiegelHom n k).comp (AddMonoidHom.toMultiplicative (fourHom p a b c))

theorem diagonal_conj_fourMat (d : Fin n → k) (v : Fin 4 → ZMod p) :
    diagonal d * fourMat p a b c v * diagonal d =
      single a a (d a * ZMod.castHom dvd_rfl k (v 0) * d a) +
        single a b (d a * ZMod.castHom dvd_rfl k (v 1) * d b) +
        single b a (d b * ZMod.castHom dvd_rfl k (v 1) * d a) +
        single b b (d b * ZMod.castHom dvd_rfl k (v 2) * d b) +
        single c c (d c * ZMod.castHom dvd_rfl k (v 3) * d c) := by
  simp only [fourMat, Matrix.mul_add, Matrix.add_mul, diagonal_mul_single_mul_diagonal]

variable {p a b c}

theorem fourMat_apply (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (v : Fin 4 → ZMod p) :
    fourMat (k := k) p a b c v a a = ZMod.castHom dvd_rfl k (v 0) ∧
      fourMat (k := k) p a b c v a b = ZMod.castHom dvd_rfl k (v 1) ∧
      fourMat (k := k) p a b c v b b = ZMod.castHom dvd_rfl k (v 2) ∧
      fourMat (k := k) p a b c v c c = ZMod.castHom dvd_rfl k (v 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [fourMat, Matrix.add_apply, hab, hac, hbc, hab.symm, hac.symm, hbc.symm]

theorem fourMat_injective (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (fourMat (k := k) p a b c) := by
  intro v w h
  have hcast := ZMod.castHom_injective (n := p) k
  obtain ⟨hv0, hv1, hv2, hv3⟩ := fourMat_apply (k := k) hab hac hbc v
  obtain ⟨hw0, hw1, hw2, hw3⟩ := fourMat_apply (k := k) hab hac hbc w
  rw [h] at hv0 hv1 hv2 hv3
  funext i
  fin_cases i
  · exact hcast (hv0.symm.trans hw0)
  · exact hcast (hv1.symm.trans hw1)
  · exact hcast (hv2.symm.trans hw2)
  · exact hcast (hv3.symm.trans hw3)

theorem fourHom_injective (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (fourHom (k := k) p a b c) :=
  fun _ _ h => fourMat_injective hab hac hbc (congrArg Subtype.val h)

theorem fourTheta_injective (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (fourTheta (k := k) p a b c) :=
  projSiegelHom_injective.comp (Multiplicative.ofAdd.injective.comp
    ((fourHom_injective hab hac hbc).comp Multiplicative.toAdd.injective))

theorem fourTheta_pow_eq_one (v : Multiplicative (Fin 4 → ZMod p)) :
    fourTheta (k := k) p a b c v ^ p = 1 := by
  rw [← map_pow]
  convert map_one (fourTheta (k := k) p a b c)
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_pow, toAdd_one, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
    Pi.zero_apply]

end Four

section Lift

variable {k : Type} [Field k] {n : ℕ} {p : ℕ} [CharP k p] {a b c : Fin n}

theorem sign_conj_fourMat (hab : a ≠ b) (hbc : b ≠ c) (v : Fin 4 → ZMod p) :
    diagonal (fun i => ((if i = b then -1 else 1 : kˣ) : k)) * fourMat p a b c v *
        diagonal (fun i => ((if i = b then -1 else 1 : kˣ) : k)) =
      fourMat p a b c ![v 0, -v 1, v 2, v 3] := by
  rw [diagonal_conj_fourMat]
  simp [fourMat, hab, hbc.symm, map_neg]

theorem eps_conj_fourMat (hac : a ≠ c) (hbc : b ≠ c) (v : Fin 4 → ZMod p) :
    diagonal (fun i => ((if i = a ∨ i = b then -1 else 1 : kˣ) : k)) * fourMat p a b c v *
        diagonal (fun i => ((if i = a ∨ i = b then -1 else 1 : kˣ) : k)) =
      fourMat p a b c v := by
  rw [diagonal_conj_fourMat]
  simp [fourMat, hac.symm, hbc.symm]

theorem liftComm_fourTheta_eq_one (hp : p.Prime) (hp2 : p ≠ 2) (hab : a ≠ b) (hbc : b ≠ c)
    {Y : Type*} [Group Y] {η : Y →* StatedProj (StatedSp n k)} (hη : Function.Surjective η)
    (hker : η.ker ≤ Subgroup.center Y) (v w : Fin 4 → ZMod p) :
    liftComm η hη (fourTheta p a b c (.ofAdd v)) (fourTheta p a b c (.ofAdd w)) = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  set θ := fourTheta (k := k) p a b c with hθ
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hcomm : ∀ v w, Commute (θ (.ofAdd v)) (θ (.ofAdd w)) := commute_map_ofAdd θ
  have hpow : ∀ v, θ (.ofAdd v) ^ p = 1 := fun v => fourTheta_pow_eq_one _
  set e : Fin 4 → Fin 4 → ZMod p := fun j => Pi.single j 1 with he
  set δ : Fin n → kˣ := fun i => if i = b then -1 else 1 with hδ
  set g : StatedProj (StatedSp n k) :=
    ((⟨torusGL δ, torusGL_mem_statedSp δ⟩ : StatedSp n k) : StatedProj (StatedSp n k))
  have hg : ∀ v, g * θ (.ofAdd v) * g⁻¹ = θ (.ofAdd ![v 0, -v 1, v 2, v 3]) := fun v =>
    mk_conj_eq (torus_conj_siegelSpHom δ (B := fourHom p a b c v)
      (B' := fourHom p a b c ![v 0, -v 1, v 2, v 3]) (sign_conj_fourMat hab hbc v))
  have hginv : g * θ (.ofAdd (e 1)) * g⁻¹ = (θ (.ofAdd (e 1)))⁻¹ := by
    have hv : (![e 1 0, -e 1 1, e 1 2, e 1 3] : Fin 4 → ZMod p) = -e 1 := by
      funext i
      fin_cases i <;> simp [e]
    rw [hg, hv, ofAdd_neg, map_inv]
  have hgfix : ∀ j, j ≠ 1 → g * θ (.ofAdd (e j)) * g⁻¹ = θ (.ofAdd (e j)) := by
    intro j hj
    have hv : (![e j 0, -e j 1, e j 2, e j 3] : Fin 4 → ZMod p) = e j := by
      funext i
      fin_cases j <;> fin_cases i <;> simp [e] at hj ⊢
    rw [hg, hv]
  have hy : ∀ j, j ≠ 1 → liftComm η hη (θ (.ofAdd (e 1))) (θ (.ofAdd (e j))) = 1 :=
    fun j hj => liftComm_eq_one_of_conj_inv hη hker hpodd (hcomm _ _) (hpow _) g hginv
      (hgfix j hj)
  have hsw : ∀ x y : Fin n, ∀ j j' : Fin 4, fourMat (k := k) p a b c (e j) = single x x 1 →
      fourMat (k := k) p a b c (e j') = single y y 1 →
        liftComm η hη (θ (.ofAdd (e j))) (θ (.ofAdd (e j'))) = 1 := by
    intro x y j j' hj hj'
    set A : GL (Fin n) k := permMatrixHom.toHomUnits (Equiv.swap x y)
    set g' : StatedProj (StatedSp n k) := ((leviSp A : StatedSp n k) : StatedProj (StatedSp n k))
    have h1 : g' * θ (.ofAdd (e j)) * g'⁻¹ = θ (.ofAdd (e j')) :=
      mk_conj_eq (leviSp_conj_siegelSpHom A (B := fourHom p a b c (e j))
        (B' := fourHom p a b c (e j')) (by
          change (A : Matrix (Fin n) (Fin n) k) * fourMat p a b c (e j) *
            (A : Matrix (Fin n) (Fin n) k)ᵀ = fourMat p a b c (e j')
          rw [hj, hj', permGL_mul_single_mul_transpose, Equiv.swap_apply_left]))
    have h2 : g' * θ (.ofAdd (e j')) * g'⁻¹ = θ (.ofAdd (e j)) :=
      mk_conj_eq (leviSp_conj_siegelSpHom A (B := fourHom p a b c (e j'))
        (B' := fourHom p a b c (e j)) (by
          change (A : Matrix (Fin n) (Fin n) k) * fourMat p a b c (e j') *
            (A : Matrix (Fin n) (Fin n) k)ᵀ = fourMat p a b c (e j)
          rw [hj, hj', permGL_mul_single_mul_transpose, Equiv.swap_apply_right]))
    exact liftComm_eq_one_of_conj_swap hη hker hpodd (hcomm _ _) (hpow _) g' h1 h2
  have he0 : fourMat (k := k) p a b c (e 0) = single a a 1 := by simp [fourMat, e]
  have he2 : fourMat (k := k) p a b c (e 2) = single b b 1 := by simp [fourMat, e]
  have he3 : fourMat (k := k) p a b c (e 3) = single c c 1 := by simp [fourMat, e]
  have key : ∀ i j : Fin 4, i < j → liftComm η hη (θ (.ofAdd (e i))) (θ (.ofAdd (e j))) = 1 := by
    have h01 : liftComm η hη (θ (.ofAdd (e 0))) (θ (.ofAdd (e 1))) = 1 := by
      rw [liftComm_swap, hy 0 (by decide), inv_one]
    have h02 := hsw a b 0 2 he0 he2
    have h03 := hsw a c 0 3 he0 he3
    have h12 := hy 2 (by decide)
    have h13 := hy 3 (by decide)
    have h23 := hsw b c 2 3 he2 he3
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | assumption
  have hgen : ∀ i j : Fin 4, liftComm η hη (θ (.ofAdd (e i))) (θ (.ofAdd (e j))) = 1 := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · exact key i j h
    · exact liftComm_self hη _
    · rw [liftComm_swap, key j i h, inv_one]
  have hS : Submodule.span (ZMod p) (Set.range (Pi.basisFun (ZMod p) (Fin 4))) = ⊤ :=
    (Pi.basisFun (ZMod p) (Fin 4)).span_eq
  refine liftComm_eq_one_of_mem_span θ hη hker (S := Set.range (Pi.basisFun (ZMod p) (Fin 4)))
    (T := Set.range (Pi.basisFun (ZMod p) (Fin 4))) ?_ (by rw [hS]; trivial) (by rw [hS]; trivial)
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  rw [Pi.basisFun_apply, Pi.basisFun_apply]
  exact hgen i j

theorem odd_symplectic_rank_four_witness {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : Type}
    [Field k] [Finite k] (hk : Nat.card k = p ^ f) {n : ℕ} (hn : 3 ≤ n) {X : Type*} [Group X]
    [Finite X] (Y : Subgroup X) (η : Y →* StatedProj (StatedSp n k))
    (hη : Function.Surjective η) (hker : η.ker ≤ Subgroup.center Y) :
    ∃ u : X, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A₀ : Subgroup X,
      A₀ ≤ Y ⊓ Subgroup.centralizer ({u} : Set X) ∧ IsElemAbelian p A₀ ∧
        Nat.card A₀ = p ^ 4 ∧ 4 ≤ localRank p X := by
  classical
  have := Fintype.ofFinite k
  have : CharP k p := by
    have : Fact p.Prime := ⟨hp⟩
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hk])
  set a : Fin n := ⟨0, by omega⟩
  set b : Fin n := ⟨1, by omega⟩
  set c : Fin n := ⟨2, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  set θ := fourTheta (k := k) p a b c with hθ
  have hθinj : Function.Injective θ := fourTheta_injective hab hac hbc
  set D := θ.range
  have hDcard : Nat.card D = p ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv, Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hDp : ∀ x ∈ D, x ^ p = 1 := by
    rintro _ ⟨v, rfl⟩
    exact fourTheta_pow_eq_one v
  have hF : ∀ x ∈ D.comap η, ∀ y ∈ D.comap η, x * y = y * x := fun x hx y hy =>
    mul_comm_of_liftComm_eq_one hη hker (U := D) (fun s hs t ht => by
      obtain ⟨v, rfl⟩ := hs
      obtain ⟨w, rfl⟩ := ht
      exact liftComm_fourTheta_eq_one hp hp2 hab hbc hη hker (Multiplicative.toAdd v)
        (Multiplicative.toAdd w)) hx hy
  set ε : Fin n → kˣ := fun i => if i = a ∨ i = b then -1 else 1 with hε
  set h : StatedSp n k := ⟨torusGL ε, torusGL_mem_statedSp ε⟩
  set z : StatedProj (StatedSp n k) := QuotientGroup.mk h
  have hneg : (-1 : k) ≠ 1 := by
    intro h1
    have h2 : ((2 : ℕ) : k) = 0 := by
      push_cast
      linear_combination -h1
    rw [CharP.cast_eq_zero_iff k p] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hεa : (ε a : k) = -1 := by simp [ε]
  have hεc : (ε c : k) = 1 := by simp [ε, hac.symm, hbc.symm]
  have hεε : ∀ i, ε i * ε i = 1 := fun i => by
    by_cases hi : i = a ∨ i = b <;> simp [ε, hi]
  have hz1 : z ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars,
      MonoidHom.mem_range] at h1
    obtain ⟨d, hd⟩ := h1
    have hd' := congrArg (fun g : GL (Fin n ⊕ Fin n) k =>
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)) hd
    have h0 := congrFun (congrFun hd' (Sum.inl a)) (Sum.inl a)
    have hl := congrFun (congrFun hd' (Sum.inl c)) (Sum.inl c)
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      at h0 hl
    change (d : k) = (↑(torusGL ε) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) _ _ at h0
    change (d : k) = (↑(torusGL ε) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k) _ _ at hl
    rw [coe_torusGL, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply_eq, hεa] at h0
    rw [coe_torusGL, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply_eq, hεc] at hl
    exact hneg (h0.symm.trans hl)
  have hz2 : z ^ 2 = 1 := by
    rw [pow_two, ← QuotientGroup.mk_mul]
    have : h * h = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Units.val_mul, coe_torusGL, Matrix.fromBlocks_multiply]
      simp only [Matrix.diagonal_mul_diagonal, Matrix.mul_zero, Matrix.zero_mul, add_zero,
        zero_add, OneMemClass.coe_one, Units.val_one]
      rw [← Matrix.fromBlocks_one]
      congr 1 <;> rw [← Matrix.diagonal_one] <;> congr 1 <;> funext i
      · rw [← Units.val_mul, hεε, Units.val_one]
      · rw [← Units.val_mul, ← mul_inv, hεε, inv_one, Units.val_one]
    rw [this, QuotientGroup.mk_one]
  have hz : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hzD : ∀ x ∈ D, Commute z x := by
    rintro _ ⟨v, rfl⟩
    have hconj : z * θ v * z⁻¹ = θ v :=
      mk_conj_eq (torus_conj_siegelSpHom ε (B := fourHom p a b c (Multiplicative.toAdd v))
        (B' := fourHom p a b c (Multiplicative.toAdd v)) (eps_conj_fourMat hac hbc _))
    exact mul_inv_eq_iff_eq_mul.mp hconj
  obtain ⟨u, huY, hu, A, hA, hAel, hAcard, -, -, hrank⟩ :=
    central_cover_involution_witness Y hη hker hp hp2 (D := D) hDp hF (r := 4) hDcard.ge hz hzD
  exact ⟨u, huY, hu, A, hA, hAel, hAcard, hrank⟩

end Lift

theorem mk_lam_injective {K : Type} [Field K] {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective ((QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf
      (StatedSp n K))).comp (lam (k := K) (⟨0, by omega⟩ : Fin n))) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hg
  obtain ⟨d, hd⟩ := hg
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  have hd' : ∀ x y, Matrix.scalar (Fin n ⊕ Fin n) (d : K) x y =
      pairMat (Sum.inl i₀) (Sum.inr i₀) (g : Matrix (Fin 2) (Fin 2) K) x y := fun x y => by
    have := congrFun (congrFun (congrArg (fun g : GL (Fin n ⊕ Fin n) K =>
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hd) x) y
    rw [Matrix.GeneralLinearGroup.coe_scalar] at this
    rw [this]
    rfl
  have hi1 : (Sum.inl i₁ : Fin n ⊕ Fin n) ≠ Sum.inl i₀ := by simp [i₀, i₁, Fin.ext_iff]
  have hd1 : (d : K) = 1 := by
    have := hd' (Sum.inl i₁) (Sum.inl i₁)
    rwa [pairMat_apply_of_ne hi1 Sum.inl_ne_inr, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq] at this
  obtain ⟨h00, h01, h10, h11⟩ := pairMat_apply_pair
    (Sum.inl_ne_inr : (Sum.inl i₀ : Fin n ⊕ Fin n) ≠ Sum.inr i₀) (g : Matrix (Fin 2) (Fin 2) K)
  have e00 := hd' (Sum.inl i₀) (Sum.inl i₀)
  have e01 := hd' (Sum.inl i₀) (Sum.inr i₀)
  have e10 := hd' (Sum.inr i₀) (Sum.inl i₀)
  have e11 := hd' (Sum.inr i₀) (Sum.inr i₀)
  rw [h00, Matrix.scalar_apply, Matrix.diagonal_apply_eq, hd1] at e00
  rw [h01, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ Sum.inl_ne_inr] at e01
  rw [h10, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ Sum.inr_ne_inl] at e10
  rw [h11, Matrix.scalar_apply, Matrix.diagonal_apply_eq, hd1] at e11
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using e00.symm
  · simpa using e01.symm
  · simpa using e10.symm
  · simpa using e11.symm

theorem exists_rank_of_symplectic_model {p f : ℕ} (hp2 : p ≠ 2) {X : Type} [Group X] [Finite X]
    (Y : Subgroup X) {n : ℕ} (hmod : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSp n p f)
    (hnf : ¬(n = 2 ∧ f ≤ 3)) :
    ∃ r : ℕ, 4 ≤ r ∧ r ≤ localRank p X ∧ ∃ V : Subgroup X, Nat.card V = p ^ r := by
  obtain ⟨⟨hp, hf, hn2, -⟩, K, _, _, hK, ⟨e⟩⟩ := hmod
  set φ : Y →* StatedProj (StatedSp n K) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Y))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker ≤ Subgroup.center Y := fun x hx => by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    exact hx
  rcases (show 3 ≤ n ∨ n = 2 by omega) with hn | rfl
  · obtain ⟨-, -, -, A, -, -, hA, hrank⟩ :=
      odd_symplectic_rank_four_witness hp hp2 hK hn Y φ hφ hker
    exact ⟨4, le_rfl, hrank, A, hA⟩
  · have hf4 : 4 ≤ f := by omega
    have := Fintype.ofFinite K
    have hK' : Fintype.card K = p ^ f := by rw [← Nat.card_eq_fintype_card, hK]
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have h81 : 81 ≤ p ^ f := calc
      81 = 3 ^ 4 := by norm_num
      _ ≤ p ^ 4 := Nat.pow_le_pow_left hp3 4
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf4
    obtain ⟨-, -, -, V, -, -, hV, hrank⟩ :=
      CFSG.RankThree.CentralCover.commuting_SL2_odd_field_actual_central_cover_local_rank Y hp
        hp2 hf le_rfl hK' (by omega) (by omega) φ hφ hker
        (fun _ => (QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf
          (StatedSp 2 K))).comp (lam (k := K) (⟨0, by omega⟩ : Fin 2)))
        (fun _ => mk_lam_injective le_rfl) (fun i j hij => absurd (Subsingleton.elim i j) hij)
    rw [one_mul] at hV hrank
    exact ⟨f, hf4, hrank, V, hV⟩

theorem odd_symplectic_actual_cover_rank_four_and_small_parameters {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    (∀ (k : Type) [Field k] [Finite k], Nat.card k = p ^ f → ∀ n : ℕ, 3 ≤ n →
      ∀ (X : Type u) [Group X] [Finite X] (Y : Subgroup X)
        (η : Y →* StatedProj (StatedSp n k)), Function.Surjective η →
          η.ker ≤ Subgroup.center Y →
          ∃ u : X, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A₀ : Subgroup X,
            A₀ ≤ Y ⊓ Subgroup.centralizer ({u} : Set X) ∧ IsElemAbelian p A₀ ∧
              Nat.card A₀ = p ^ 4 ∧ 4 ≤ localRank p X) ∧
    ∀ (X : Type) [Group X] [Finite X] (Y : Subgroup X) (n : ℕ),
      (CFSG.twoLocalOddRank X ≤ 3 ∨ CFSG.Assembly.evenRank X ≤ 3 ∨ localRank p X ≤ 3) →
      StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSp n p f → n = 2 ∧ f ≤ 3 := by
  refine ⟨fun k _ _ hk n hn X _ _ Y η hη hker =>
    odd_symplectic_rank_four_witness hp hp2 hk hn Y η hη hker, fun X _ _ Y n hX hmod => ?_⟩
  by_contra hnf
  obtain ⟨r, hr4, hrank, V, hV⟩ := exists_rank_of_symplectic_model hp2 Y hmod hnf
  have hpX : p ∣ Nat.card X := by
    refine (dvd_pow_self p (by omega : r ≠ 0)).trans ?_
    rw [← hV]
    exact Subgroup.card_subgroup_dvd_card V
  have h1 := hrank.trans (CFSG.RankThree.Theta.localRank_le_twoLocalOddRank hp hp2 hpX)
  have h2 := hrank.trans ((CFSG.Milestones.lc_gl_local_rank_bounds X).1 p hp hp2).2
  omega

end CFSG.RankThree.GroupTheory
