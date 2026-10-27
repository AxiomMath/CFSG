module

public import CFSG.LocalAnalysis.StandardType.TableC.GramBlockRank
public import CFSG.LocalAnalysis.StandardType.TableC.OrthGram
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedPair
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockOmegaDecomp
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedShape

public section

namespace CFSG.StandardType.TableC

open Module QuadraticMap
open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal CFSG.RankThree.Classical2
open CFSG.StandardType.ClassicalPosition
open CFSG.StandardType.ClassicalBlocks

private def j1a_orth {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) : Subgroup (GL ι K) where
  carrier := {A | ∀ v, Φ ((A : Matrix ι ι K).mulVec v) = Φ v}
  mul_mem' {a b} ha hb v := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ha, hb]
  one_mem' v := by
    rw [Units.val_one, Matrix.one_mulVec]
  inv_mem' {a} ha v := by
    have h1 : Φ (((a : GL ι K) : Matrix ι ι K).mulVec
        (((a⁻¹ : GL ι K) : Matrix ι ι K).mulVec v)) = Φ v := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    exact (ha (((a⁻¹ : GL ι K) : Matrix ι ι K).mulVec v)).symm.trans h1

private lemma j1a_statedOmega_eq_commutator {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (Φ : QuadraticForm K (ι → K)) :
    StatedOmega ⇑Φ = ⁅j1a_orth Φ, j1a_orth Φ⁆ := by
  have h : Subgroup.closure {A : GL ι K | ∀ v, Φ ((A : Matrix ι ι K).mulVec v) = Φ v} =
      j1a_orth Φ := Subgroup.closure_eq (j1a_orth Φ)
  unfold StatedOmega
  rw [h]

private lemma j1a_statedOmega_le_orth {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) : StatedOmega ⇑Φ ≤ j1a_orth Φ := by
  rw [j1a_statedOmega_eq_commutator]
  exact Subgroup.commutator_le.mpr (fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact (j1a_orth Φ).mul_mem
      ((j1a_orth Φ).mul_mem ((j1a_orth Φ).mul_mem h₁ h₂)
        ((j1a_orth Φ).inv_mem h₁))
      ((j1a_orth Φ).inv_mem h₂))

private lemma j1a_adjoin_comm {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {S : Set (GL ι K)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ {a b : Matrix ι ι K}, a ∈ Algebra.adjoin K (Units.val '' S) →
      b ∈ Algebra.adjoin K (Units.val '' S) → a * b = b * a := by
  have hcommS : (Units.val '' S : Set (Matrix ι ι K)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    show (s : Matrix ι ι K) * (s' : Matrix ι ι K) =
      (s' : Matrix ι ι K) * (s : Matrix ι ι K)
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val (hS s hs s' hs').eq
  letI : CommSemiring (Algebra.adjoin K (Units.val '' S)) :=
    Algebra.adjoinCommSemiringOfComm K hcommS
  intro a b ha hb
  have h := mul_comm (⟨a, ha⟩ : Algebra.adjoin K (Units.val '' S))
    (⟨b, hb⟩ : Algebra.adjoin K (Units.val '' S))
  simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h

private lemma j1a_inv_comm {R : Type} [Ring R] {x xi e : R} (hx : x * xi = 1)
    (hxi : xi * x = 1) (hc : x * e = e * x) : xi * e = e * xi := by
  calc xi * e = xi * e * (x * xi) := by rw [hx, mul_one]
    _ = xi * (e * x) * xi := by noncomm_ring
    _ = xi * (x * e) * xi := by rw [hc]
    _ = xi * x * e * xi := by noncomm_ring
    _ = e * xi := by rw [hxi]; noncomm_ring

private lemma j1a_blk_val_mul_inv {R : Type} [Ring R] (x xi e : R) (hx : x * xi = 1)
    (hid : e * e = e) (hci : xi * e = e * xi) :
    (x * e + (1 - e)) * (xi * e + (1 - e)) = 1 := by
  have hxe : x * (xi * e) = e := by rw [← mul_assoc, hx, one_mul]
  have hexi : e * (xi * e) = xi * e := by
    calc e * (xi * e) = (e * xi) * e := by rw [mul_assoc]
      _ = (xi * e) * e := by rw [← hci]
      _ = xi * (e * e) := by rw [mul_assoc]
      _ = xi * e := by rw [hid]
  have hxe' : (x * e) * (xi * e) = e := by rw [mul_assoc, hexi, hxe]
  noncomm_ring [hxe', hexi, hid]

private lemma j1a_blk_inv_mul {R : Type} [Ring R] (x xi e : R) (hxi : xi * x = 1)
    (hid : e * e = e) (hc : x * e = e * x) :
    (xi * e + (1 - e)) * (x * e + (1 - e)) = 1 := by
  have hxe : xi * (x * e) = e := by rw [← mul_assoc, hxi, one_mul]
  have hexi : e * (x * e) = x * e := by
    calc e * (x * e) = (e * x) * e := by rw [mul_assoc]
      _ = (x * e) * e := by rw [← hc]
      _ = x * (e * e) := by rw [mul_assoc]
      _ = x * e := by rw [hid]
  have hxe' : (xi * e) * (x * e) = e := by rw [mul_assoc, hexi, hxe]
  noncomm_ring [hxe', hexi, hid]

private noncomputable def j1a_blk {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (s : GL ι K) (ε : Matrix ι ι K) (hid : IsIdempotentElem ε)
    (hcomm : (s : Matrix ι ι K) * ε = ε * (s : Matrix ι ι K)) : GL ι K :=
  Units.mk ((s : Matrix ι ι K) * ε + (1 - ε))
    (((s⁻¹ : GL ι K) : Matrix ι ι K) * ε + (1 - ε))
    (j1a_blk_val_mul_inv (s : Matrix ι ι K) ((s⁻¹ : GL ι K) : Matrix ι ι K) ε
      (Units.mul_inv s) hid.eq
      (j1a_inv_comm (Units.mul_inv s) (Units.inv_mul s) hcomm))
    (j1a_blk_inv_mul (s : Matrix ι ι K) ((s⁻¹ : GL ι K) : Matrix ι ι K) ε
      (Units.inv_mul s) hid.eq hcomm)

private lemma j1a_blk_val {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (s : GL ι K) (ε : Matrix ι ι K) (hid : IsIdempotentElem ε)
    (hcomm : (s : Matrix ι ι K) * ε = ε * (s : Matrix ι ι K)) :
    (j1a_blk s ε hid hcomm : Matrix ι ι K) = (s : Matrix ι ι K) * ε + (1 - ε) := by
  rw [j1a_blk, Units.val_mk]

private lemma j1a_blk_mul_step {R : Type} [Ring R] (x e : R) (he : e * e = e)
    (hc : x * e = e * x) (y : R) :
    (y * e + (1 - e)) * (x * e + (1 - e)) = y * x * e + (1 - e) := by
  have he1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h1e : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h1e1 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have hce : (1 - e) * x = x * (1 - e) := by rw [sub_mul, one_mul, mul_sub, mul_one, hc]
  have hmain : y * e * (x * e) = y * x * e := by
    rw [mul_assoc y e (x * e), ← mul_assoc e x e, ← hc, mul_assoc x e e, he,
      ← mul_assoc y x e]
  have hy1 : y * e * (1 - e) = 0 := by rw [mul_assoc, he1, mul_zero]
  have h1x : (1 - e) * (x * e) = 0 := by
    rw [← mul_assoc, hce, mul_assoc, h1e, mul_zero]
  calc (y * e + (1 - e)) * (x * e + (1 - e))
      = y * e * (x * e) + y * e * (1 - e) + (1 - e) * (x * e) +
          (1 - e) * (1 - e) := by rw [mul_add, add_mul, add_mul]; abel
    _ = y * x * e + (1 - e) := by rw [hmain, hy1, h1x, h1e1]; abel

private lemma j1a_blk_pow {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (s : GL ι K) (ε : Matrix ι ι K) (hid : IsIdempotentElem ε)
    (hcomm : (s : Matrix ι ι K) * ε = ε * (s : Matrix ι ι K)) (n : ℕ) :
    ((j1a_blk s ε hid hcomm : GL ι K) : Matrix ι ι K) ^ n =
      (s : Matrix ι ι K) ^ n * ε + (1 - ε) := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, Matrix.one_mul]
      exact (add_sub_cancel ε 1).symm
  | succ n ih =>
      rw [pow_succ, ih, j1a_blk_val, pow_succ]
      exact j1a_blk_mul_step (s : Matrix ι ι K) ε hid.eq hcomm ((s : Matrix ι ι K) ^ n)

private lemma j1a_orderOf_dvd {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (s : GL ι K) (ε : Matrix ι ι K) (hid : IsIdempotentElem ε)
    (hcomm : (s : Matrix ι ι K) * ε = ε * (s : Matrix ι ι K)) :
    orderOf (j1a_blk s ε hid hcomm) ∣ orderOf s := by
  apply orderOf_dvd_iff_pow_eq_one.mpr
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, j1a_blk_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one,
    Units.val_one, Matrix.one_mul, add_sub_cancel]

private lemma j1a_odd_orderOf_blk {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (s : GL ι K) (ε : Matrix ι ι K) (hid : IsIdempotentElem ε)
    (hcomm : (s : Matrix ι ι K) * ε = ε * (s : Matrix ι ι K))
    (hodd : Odd (orderOf s)) : Odd (orderOf (j1a_blk s ε hid hcomm)) :=
  Odd.of_dvd_nat hodd (j1a_orderOf_dvd s ε hid hcomm)

private lemma j1a_mem_statedOmega_iff_orthDerived {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (Φ : QuadraticForm K (ι → K)) (w : GL ι K) :
    w ∈ StatedOmega ⇑Φ ↔
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K w ∈
        CFSG.RankThree.Classical2.orthDerived Φ := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (Q := Φ) rfl, Subgroup.mem_comap]
  rfl

private lemma j1a_mem_statedOmega_of_isometry {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h6 : 6 ≤ Fintype.card ι) {b : GL ι K}
    (hiso : ∀ v, Φ ((b : Matrix ι ι K).mulVec v) = Φ v) (hodd : Odd (orderOf b)) :
    b ∈ StatedOmega ⇑Φ := by
  rw [j1a_mem_statedOmega_iff_orthDerived Φ b]
  refine CFSG.LocalAnalysis.GLTheoremA.T173M.mem_orthDerived_of_odd_pow_of_six_le
    Φ hΦ ?_ ?_ hodd ?_
  · rw [Module.finrank_fintype_fun_eq_card]
    omega
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
    exact hiso v
  · rw [← map_pow, pow_orderOf_eq_one, map_one]

private lemma j1a_polar_eq_dot {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (x y : ι → K) :
    QuadraticMap.polar Φ x y =
      dotProduct x ((LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).mulVec y) := by
  have h1 : (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Φ) := rfl
  rw [h1]
  rw [← Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Φ)) x y,
    Matrix.toBilin'_toMatrix', QuadraticMap.polarBilin_apply_apply]

private lemma j1a_gram_isometry {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (M : Matrix ι ι K)
    (hM : ∀ x : ι → K, Φ (M.mulVec x) = Φ x) :
    Matrix.transpose M * LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) * M =
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) := by
  have hpol : ∀ x y, QuadraticMap.polar Φ (M.mulVec x) (M.mulVec y) = QuadraticMap.polar Φ x y := by
    intro x y
    rw [QuadraticMap.polar, QuadraticMap.polar, ← Matrix.mulVec_add, hM (x + y), hM x, hM y]
  apply (LinearEquiv.injective Matrix.toBilin')
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply']
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, ← j1a_polar_eq_dot Φ (M.mulVec x) (M.mulVec y),
    ← j1a_polar_eq_dot Φ x y]
  exact hpol x y

private lemma j1a_exists_prim_idem {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    {S : Set (GL ι K)} (hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' S)) ε) :
    ∃ e : Matrix ι ι K,
      IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e ∧ e * ε = e ∧
        (e = ε ∨ (e ≠ ε ∧
          formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e ≠ e ∧
          ε = e + formAdj (RingHom.id K)
            (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e)) := by
  have hG : IsUnit (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).det :=
    polarGram_isUnit_det Φ hΦ
  have hGh : Matrix.transpose
      ((LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).map (RingHom.id K)) =
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) := by
    simpa [Matrix.map_id] using polarGram_transpose Φ
  have hSU : ∀ s ∈ S, Matrix.transpose ((s : Matrix ι ι K).map (RingHom.id K)) *
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) * (s : Matrix ι ι K) =
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) := by
    intro s hs
    have h := j1a_gram_isometry Φ (s : Matrix ι ι K)
      (fun v => j1a_statedOmega_le_orth Φ (hSΩ s hs) v)
    simpa [Matrix.map_id] using h
  exact exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id K) (fun _ => rfl) hG hGh hS hSU hε

private lemma j1a_closureS_commute {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {S : Set (GL ι K)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, Commute a b := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S :=
    (Subgroup.closure_le (Subgroup.centralizer S)).mpr (fun x hx => by
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro y hy
      exact (hS x hx y hy).eq.symm)
  have h2 : Subgroup.closure S ≤
      Subgroup.centralizer (Subgroup.closure S : Set (GL ι K)) :=
    (Subgroup.closure_le
      (Subgroup.centralizer (Subgroup.closure S : Set (GL ι K)))).mpr (fun x hx => by
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro y hy
      exact ((Subgroup.mem_centralizer_iff.mp (h1 hy)) x hx).symm)
  intro a ha b hb
  exact ((Subgroup.mem_centralizer_iff.mp (h2 ha)) b hb).symm

private lemma j1a_orderOf_mul_dvd_of_commute {G : Type} [Group G] {a b : G}
    (h : Commute a b) : orderOf (a * b) ∣ orderOf a * orderOf b := by
  apply orderOf_dvd_iff_pow_eq_one.mpr
  have ha : a ^ (orderOf a * orderOf b) = 1 := by
    rw [pow_mul, pow_orderOf_eq_one, one_pow]
  have hb : b ^ (orderOf a * orderOf b) = 1 := by
    rw [mul_comm (orderOf a) (orderOf b), pow_mul, pow_orderOf_eq_one, one_pow]
  rw [h.mul_pow, ha, hb, mul_one]

private lemma j1a_closureS_odd {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {S : Set (GL ι K)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) :
    ∀ s ∈ Subgroup.closure S, Odd (orderOf s) := by
  intro s hs
  induction hs using Subgroup.closure_induction with
  | mem x hx => exact hodd x hx
  | one => simpa using odd_one
  | mul x y hx hy ihx ihy =>
      exact Odd.of_dvd_nat (ihx.mul ihy)
        (j1a_orderOf_mul_dvd_of_commute (j1a_closureS_commute hS x hx y hy))
  | inv x hx ihx => simpa [orderOf_inv] using ihx

private lemma j1a_closureS_mem_adjoin {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] {S : Set (GL ι K)} :
    ∀ s ∈ Subgroup.closure S,
      (s : Matrix ι ι K) ∈ Algebra.adjoin K (Units.val '' S) := by
  intro s hs
  induction hs using Subgroup.closure_induction with
  | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
  | one => exact Subalgebra.one_mem _
  | mul x y hx hy ihx ihy => exact Subalgebra.mul_mem _ ihx ihy
  | inv x hx ihx =>
      have hpow : x ^ (orderOf x - 1) = x⁻¹ := by
        have h1 : x ^ (orderOf x - 1) * x = 1 := by
          rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
        exact eq_inv_of_mul_eq_one_left h1
      rw [← hpow, Units.val_pow_eq_pow_val]
      exact Subalgebra.pow_mem _ ihx _

private lemma j1a_closureS_mem_statedOmega {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {S : Set (GL ι K)} {Φ : QuadraticForm K (ι → K)}
    (hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ) :
    ∀ s ∈ Subgroup.closure S, s ∈ StatedOmega ⇑Φ :=
  (Subgroup.closure_le (StatedOmega ⇑Φ)).mpr hSΩ

private lemma j1a_formAdj_eq_inv {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) {S : Set (GL ι K)}
    (hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ) {x : GL ι K} (hx : x ∈ Subgroup.closure S) :
    formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (x : Matrix ι ι K) = ((x⁻¹ : GL ι K) : Matrix ι ι K) := by
  have hG : IsUnit (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).det :=
    polarGram_isUnit_det Φ hΦ
  have hiso : Matrix.transpose ((x : Matrix ι ι K).map (RingHom.id K)) *
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) * (x : Matrix ι ι K) =
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) := by
    have h := j1a_gram_isometry Φ (x : Matrix ι ι K)
      (fun v => j1a_statedOmega_le_orth Φ (j1a_closureS_mem_statedOmega hSΩ x hx) v)
    simpa [Matrix.map_id] using h
  exact Geo.formAdj_eq_inv_of_isometry (RingHom.id K) hG x hiso

private lemma j1a_star_symm {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    {S : Set (GL ι K)} (hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {e : Matrix ι ι K}
    (heA : e ∈ Algebra.adjoin K (Units.val '' S))
    {x y : GL ι K} (hx : x ∈ Subgroup.closure S) (hy : y ∈ Subgroup.closure S)
    (h : (x : Matrix ι ι K) * e = (y : Matrix ι ι K) * e) :
    (x : Matrix ι ι K) * formAdj (RingHom.id K)
        (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e =
      (y : Matrix ι ι K) * formAdj (RingHom.id K)
        (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e := by
  have hG : IsUnit (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).det :=
    polarGram_isUnit_det Φ hΦ
  have hxA : (x : Matrix ι ι K) ∈ Algebra.adjoin K (Units.val '' S) :=
    j1a_closureS_mem_adjoin x hx
  have hyA : (y : Matrix ι ι K) ∈ Algebra.adjoin K (Units.val '' S) :=
    j1a_closureS_mem_adjoin y hy
  have hstarA : formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e ∈
      Algebra.adjoin K (Units.val '' S) :=
    Geo.formAdj_mem_adjoin (RingHom.id K) hG (by
      intro s hs
      simpa [Matrix.map_id] using j1a_gram_isometry Φ (s : Matrix ι ι K)
        (fun v => j1a_statedOmega_le_orth Φ (hSΩ s hs) v)) heA
  have hxi : ((x⁻¹ : GL ι K) : Matrix ι ι K) ∈ Algebra.adjoin K (Units.val '' S) := by
    have := j1a_closureS_mem_adjoin (S := S) (x⁻¹) (Subgroup.inv_mem _ hx)
    simpa using this
  have hyi : ((y⁻¹ : GL ι K) : Matrix ι ι K) ∈ Algebra.adjoin K (Units.val '' S) := by
    have := j1a_closureS_mem_adjoin (S := S) (y⁻¹) (Subgroup.inv_mem _ hy)
    simpa using this
  have h1 : formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e *
      ((x⁻¹ : GL ι K) : Matrix ι ι K) =
      formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e *
      ((y⁻¹ : GL ι K) : Matrix ι ι K) := by
    have h2 := congrArg
      (formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))) h
    rwa [Geo.formAdj_mul (RingHom.id K) hG (x : Matrix ι ι K) e,
      Geo.formAdj_mul (RingHom.id K) hG (y : Matrix ι ι K) e,
      j1a_formAdj_eq_inv Φ hΦ hSΩ hx, j1a_formAdj_eq_inv Φ hΦ hSΩ hy] at h2
  have hxxi : (x : Matrix ι ι K) * ((x⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hxix : ((x⁻¹ : GL ι K) : Matrix ι ι K) * (x : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hyyi : (y : Matrix ι ι K) * ((y⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hyiy : ((y⁻¹ : GL ι K) : Matrix ι ι K) * (y : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hxA' : (x : Matrix ι ι K) *
      formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e =
      formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e *
      (x : Matrix ι ι K) := j1a_adjoin_comm hS hxA hstarA
  have hyA' : (y : Matrix ι ι K) *
      formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e =
      formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e *
      (y : Matrix ι ι K) := j1a_adjoin_comm hS hyA hstarA
  have hxiA : ((x⁻¹ : GL ι K) : Matrix ι ι K) *
      formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e =
      formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e *
      ((x⁻¹ : GL ι K) : Matrix ι ι K) := j1a_adjoin_comm hS hxi hstarA
  have hyiA : ((y⁻¹ : GL ι K) : Matrix ι ι K) *
      formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e =
      formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e *
      ((y⁻¹ : GL ι K) : Matrix ι ι K) := j1a_adjoin_comm hS hyi hstarA
  have hxy : (x : Matrix ι ι K) * (y : Matrix ι ι K) =
      (y : Matrix ι ι K) * (x : Matrix ι ι K) := j1a_adjoin_comm hS hxA hyA
  have hxiy : ((x⁻¹ : GL ι K) : Matrix ι ι K) * (y : Matrix ι ι K) =
      (y : Matrix ι ι K) * ((x⁻¹ : GL ι K) : Matrix ι ι K) := j1a_adjoin_comm hS hxi hyA
  rw [hxA', hyA']
  have h3 := congrArg (fun z => z * ((y : Matrix ι ι K) * (x : Matrix ι ι K))) h1
  rw [mul_assoc,
    show ((x⁻¹ : GL ι K) : Matrix ι ι K) *
        ((y : Matrix ι ι K) * (x : Matrix ι ι K)) = (y : Matrix ι ι K) from by
      rw [← mul_assoc, hxiy, mul_assoc, hxix, mul_one],
    mul_assoc,
    show ((y⁻¹ : GL ι K) : Matrix ι ι K) *
        ((y : Matrix ι ι K) * (x : Matrix ι ι K)) = (x : Matrix ι ι K) from by
      rw [← mul_assoc, hyiy, one_mul]] at h3
  exact h3.symm

private noncomputable def j1a_fixIdem {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (p : ℕ) (b : GL ι K) : Matrix ι ι K :=
  (p : K)⁻¹ • ∑ i ∈ Finset.range p, (b : Matrix ι ι K) ^ i

private lemma j1a_fixIdem_mem_adjoin {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (p : ℕ) (b : GL ι K) :
    j1a_fixIdem p b ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))) := by
  unfold j1a_fixIdem
  refine Subalgebra.smul_mem _ ?_ _
  refine Subalgebra.sum_mem _ ?_
  intro i hi
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin
    (show (b : Matrix ι ι K) ∈ Units.val '' ({b} : Set (GL ι K)) from
      ⟨b, Set.mem_singleton b, rfl⟩)) i

private lemma j1a_blk_geom_sum {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (s : GL ι K) (ε : Matrix ι ι K) (hid : IsIdempotentElem ε)
    (hcomm : (s : Matrix ι ι K) * ε = ε * (s : Matrix ι ι K)) :
    ∑ i ∈ Finset.range (orderOf s),
        ((j1a_blk s ε hid hcomm : GL ι K) : Matrix ι ι K) ^ i =
      (∑ i ∈ Finset.range (orderOf s), (s : Matrix ι ι K) ^ i) * ε +
        (orderOf s) • (1 - ε) := by
  rw [Finset.sum_congr rfl (fun i _ => j1a_blk_pow s ε hid hcomm i)]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_mul]
  · rw [Finset.sum_const, Finset.card_range]

private lemma j1a_fixIdem_eq_one_sub {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (s : GL ι K) (ε : Matrix ι ι K) (hid : IsIdempotentElem ε)
    (hcomm : (s : Matrix ι ι K) * ε = ε * (s : Matrix ι ι K)) (hodd : Odd (orderOf s))
    (hsum : (∑ i ∈ Finset.range (orderOf s), (s : Matrix ι ι K) ^ i) * ε = 0) :
    j1a_fixIdem (orderOf s) (j1a_blk s ε hid hcomm) = 1 - ε := by
  have hN : (orderOf s : K) ≠ 0 := fun h0 =>
    hodd.not_two_dvd_nat ((CharP.cast_eq_zero_iff K 2 (orderOf s)).mp h0)
  unfold j1a_fixIdem
  rw [j1a_blk_geom_sum, hsum, zero_add, ← Nat.cast_smul_eq_nsmul K (orderOf s) (1 - ε),
    smul_smul, inv_mul_cancel₀ hN, one_smul]

private lemma j1a_sum_mul_block_zero {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] {S : Set (GL ι K)}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {e : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e)
    {x : GL ι K} (hx : x ∈ Subgroup.closure S)
    (hxe : (x : Matrix ι ι K) * e ≠ e) :
    (∑ i ∈ Finset.range (orderOf x), (x : Matrix ι ι K) ^ i) * e = 0 := by
  classical
  let A : Subalgebra K (Matrix ι ι K) := Algebra.adjoin K (Units.val '' S)
  obtain ⟨E, fieldE, _algE, _finiteE, π, _hπsurj, hπker, _hπdeg⟩ :=
    exists_blockField (F := K) hS hodd he
  letI : Field E := fieldE
  have hxA : (x : Matrix ι ι K) ∈ A := j1a_closureS_mem_adjoin x hx
  have hmem_sum : (∑ i ∈ Finset.range (orderOf x), (x : Matrix ι ι K) ^ i) ∈ A :=
    Subalgebra.sum_mem A (fun i _ => Subalgebra.pow_mem A hxA i)
  have hmem_x1 : ((x : Matrix ι ι K) - 1) ∈ A :=
    Subalgebra.sub_mem A hxA (Subalgebra.one_mem A)
  have hπ_ne : π (⟨(x : Matrix ι ι K) - 1, hmem_x1⟩ : A) ≠ 0 := by
    intro h0
    have hmat : ((x : Matrix ι ι K) - 1) * e = 0 := (hπker _).mp h0
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hmat
    exact hxe hmat
  have hgeom : (∑ i ∈ Finset.range (orderOf x), (x : Matrix ι ι K) ^ i) *
      ((x : Matrix ι ι K) - 1) = 0 := by
    have hxN : (x : Matrix ι ι K) ^ orderOf x = 1 := by
      rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
    have h := geom_sum_mul_neg (x : Matrix ι ι K) (orderOf x)
    rw [hxN, sub_self] at h
    rw [show (x : Matrix ι ι K) - 1 = -((1 : Matrix ι ι K) - (x : Matrix ι ι K)) by abel,
      mul_neg, h, neg_zero]
  have hprod : (⟨∑ i ∈ Finset.range (orderOf x), (x : Matrix ι ι K) ^ i, hmem_sum⟩ : A) *
      ⟨(x : Matrix ι ι K) - 1, hmem_x1⟩ = 0 := by
    apply Subtype.ext
    change (∑ i ∈ Finset.range (orderOf x), (x : Matrix ι ι K) ^ i) *
      ((x : Matrix ι ι K) - 1) = 0
    exact hgeom
  have hπzero : π (⟨∑ i ∈ Finset.range (orderOf x),
      (x : Matrix ι ι K) ^ i, hmem_sum⟩ : A) = 0 := by
    have h := congrArg π hprod
    rw [map_zero, map_mul] at h
    exact (mul_eq_zero.mp h).resolve_right hπ_ne
  exact (hπker _).mp hπzero

private lemma j1a_prim_star {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    {S : Set (GL ι K)} (hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {e : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e) :
    IsPrimIdemIn (Algebra.adjoin K (Units.val '' S))
      (formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e) := by
  have hG : IsUnit (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).det :=
    polarGram_isUnit_det Φ hΦ
  have hSU : ∀ s ∈ S, Matrix.transpose (s : Matrix ι ι K) *
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) * (s : Matrix ι ι K) =
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) := fun s hs =>
    j1a_gram_isometry Φ (s : Matrix ι ι K) (fun v => j1a_statedOmega_le_orth Φ (hSΩ s hs) v)
  exact isPrimIdemIn_formAdj_gram K (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
    (polarGram_transpose Φ) hG hSU hS he

private lemma j1a_star_e_ne {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    {S : Set (GL ι K)} (hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {e : Matrix ι ι K}
    (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e)
    {x : GL ι K} (hx : x ∈ Subgroup.closure S)
    (hxe : (x : Matrix ι ι K) * e ≠ e) :
    (x : Matrix ι ι K) * formAdj (RingHom.id K)
        (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e ≠
      formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e := by
  have hG : IsUnit (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).det :=
    polarGram_isUnit_det Φ hΦ
  have hGh : Matrix.transpose
      ((LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).map (RingHom.id K)) =
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) := by
    simpa [Matrix.map_id] using polarGram_transpose Φ
  have heStar : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S))
      (formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e) :=
    j1a_prim_star Φ hΦ hSΩ hS he
  intro h0
  have h1 : (x : Matrix ι ι K) * formAdj (RingHom.id K)
        (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e =
      ((1 : GL ι K) : Matrix ι ι K) * formAdj (RingHom.id K)
        (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e := by
    rw [Units.val_one, Matrix.one_mul]; exact h0
  have h2 := j1a_star_symm Φ hΦ hSΩ hS heStar.1 hx (Subgroup.one_mem _) h1
  rw [Units.val_one, Matrix.one_mul,
    Geo.formAdj_formAdj (RingHom.id K) (fun _ => rfl) hG hGh e] at h2
  exact hxe h2

private lemma j1a_e_ne_of_eps_ne {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    {S : Set (GL ι K)} (hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {ε e : Matrix ι ι K}
    (heA : e ∈ Algebra.adjoin K (Units.val '' S))
    (hcase : e = ε ∨ (e ≠ ε ∧
      formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e ≠ e ∧
      ε = e + formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e))
    {x : GL ι K} (hx : x ∈ Subgroup.closure S)
    (hxε : (x : Matrix ι ι K) * ε ≠ ε) :
    (x : Matrix ι ι K) * e ≠ e := by
  intro hxe
  apply hxε
  have h1 : (x : Matrix ι ι K) * e = ((1 : GL ι K) : Matrix ι ι K) * e := by
    rw [Units.val_one, Matrix.one_mul]; exact hxe
  have hstar := j1a_star_symm Φ hΦ hSΩ hS heA hx (Subgroup.one_mem _) h1
  rw [Units.val_one, Matrix.one_mul] at hstar
  rcases hcase with hE | hD
  · rw [← hE]; exact hxe
  · obtain ⟨-, -, hεeq⟩ := hD
    rw [hεeq, Matrix.mul_add, hxe, hstar]

private lemma j1a_sum_mul_star_block_zero {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    {S : Set (GL ι K)} (hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix ι ι K} (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e)
    {x : GL ι K} (hx : x ∈ Subgroup.closure S)
    (hxe : (x : Matrix ι ι K) * e ≠ e) :
    (∑ i ∈ Finset.range (orderOf x), (x : Matrix ι ι K) ^ i) *
      formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e = 0 :=
  j1a_sum_mul_block_zero hS hodd (j1a_prim_star Φ hΦ hSΩ hS he) hx
    (j1a_star_e_ne Φ hΦ hSΩ hS he hx hxe)

private lemma j1a_sum_pow_mul_eps_eq_zero {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    {S : Set (GL ι K)} (hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε e : Matrix ι ι K} (he : IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e)
    (hcase : e = ε ∨ (e ≠ ε ∧
      formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e ≠ e ∧
      ε = e + formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e))
    {s : GL ι K} (hs : s ∈ Subgroup.closure S)
    (hse : (s : Matrix ι ι K) * ε ≠ ε) :
    (∑ i ∈ Finset.range (orderOf s), (s : Matrix ι ι K) ^ i) * ε = 0 := by
  have hse_e : (s : Matrix ι ι K) * e ≠ e :=
    j1a_e_ne_of_eps_ne Φ hΦ hSΩ hS he.1 hcase hs hse
  have h0 : (∑ i ∈ Finset.range (orderOf s), (s : Matrix ι ι K) ^ i) * e = 0 :=
    j1a_sum_mul_block_zero hS hodd he hs hse_e
  rcases hcase with hE | hD
  · rw [← hE]; exact h0
  · obtain ⟨-, -, hεeq⟩ := hD
    have h1 : (∑ i ∈ Finset.range (orderOf s), (s : Matrix ι ι K) ^ i) *
        formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e = 0 :=
      j1a_sum_mul_star_block_zero Φ hΦ hSΩ hS hodd he hs hse_e
    rw [hεeq, Matrix.mul_add, h0, h1, add_zero]

private lemma j1a_exists_nat_pow_of_mem_zpowers {G : Type} [Group G] [Finite G]
    {g x : G} (hx : x ∈ Subgroup.zpowers g) : ∃ k : ℕ, x = g ^ k := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hne : (orderOf g : ℤ) ≠ 0 := by
    have h := orderOf_pos g
    omega
  refine ⟨(k % (orderOf g : ℤ)).toNat, ?_⟩
  rw [← hk, zpow_eq_zpow_emod' k (pow_orderOf_eq_one g), ← zpow_natCast,
    Int.toNat_of_nonneg (Int.emod_nonneg k hne)]

private lemma j1a_pow_mul_eq_of_mul_eq {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (s : GL ι K) (ε : Matrix ι ι K) (h : (s : Matrix ι ι K) * ε = ε) (k : ℕ) :
    (((s : GL ι K) ^ k : GL ι K) : Matrix ι ι K) * ε = ε := by
  induction k with
  | zero => rw [pow_zero, Units.val_one, Matrix.one_mul]
  | succ n ih => rw [pow_succ, Units.val_mul, Matrix.mul_assoc, h, ih]

private lemma j1a_choose_generator {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    {S : Set (GL ι K)} (hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' S)) ε)
    (hnt : ∃ s ∈ S, (s : Matrix ι ι K) * ε ≠ ε) :
    ∃ s ∈ Subgroup.closure S, Odd (orderOf s) ∧ (s : Matrix ι ι K) * ε ≠ ε ∧
      (∀ s' ∈ Subgroup.closure S, ∃ k : ℕ,
        (s' : Matrix ι ι K) * ε = (s : Matrix ι ι K) ^ k * ε) := by
  classical
  let A : Subalgebra K (Matrix ι ι K) := Algebra.adjoin K (Units.val '' S)
  let H : Subgroup (GL ι K) := Subgroup.closure S
  obtain ⟨e, he, _hee, hcase⟩ := j1a_exists_prim_idem Φ hΦ hSΩ hS hε
  obtain ⟨E, fieldE, _algE, _finiteE, π, _hπsurj, hπker, _hπdeg⟩ :=
    exists_blockField (F := K) hS hodd he
  letI : Field E := fieldE
  have hmemH : ∀ h : H, ((h : GL ι K) : Matrix ι ι K) ∈ A :=
    fun h => j1a_closureS_mem_adjoin h.1 h.2
  have hne0 : ∀ h : H, π ⟨((h : GL ι K) : Matrix ι ι K), hmemH h⟩ ≠ 0 := by
    intro h h0
    have hmat : ((h : GL ι K) : Matrix ι ι K) * e = 0 := (hπker _).mp h0
    have hunit : (((h⁻¹ : H) : GL ι K) : Matrix ι ι K) *
        ((h : GL ι K) : Matrix ι ι K) = 1 := by
      rw [Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have he0 : e = 0 := by
      calc e = 1 * e := (Matrix.one_mul e).symm
        _ = (((h⁻¹ : H) : GL ι K) : Matrix ι ι K) *
              ((h : GL ι K) : Matrix ι ι K) * e := by rw [hunit]
        _ = (((h⁻¹ : H) : GL ι K) : Matrix ι ι K) *
              (((h : GL ι K) : Matrix ι ι K) * e) := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [hmat, Matrix.mul_zero]
    exact he.2.2.1 he0
  let f : H →* Eˣ :=
    { toFun := fun h => Units.mk0 (π ⟨((h : GL ι K) : Matrix ι ι K), hmemH h⟩) (hne0 h)
      map_one' := by
        apply Units.ext
        change π (⟨(((1 : H) : GL ι K) : Matrix ι ι K), hmemH 1⟩ : A) = 1
        rw [show (⟨(((1 : H) : GL ι K) : Matrix ι ι K), hmemH 1⟩ : A) = 1 from
          Subtype.ext rfl, map_one]
      map_mul' := by
        intro a b
        apply Units.ext
        change π (⟨((((a * b : H) : GL ι K)) : Matrix ι ι K), hmemH (a * b)⟩ : A) =
          π ⟨((a : GL ι K) : Matrix ι ι K), hmemH a⟩ *
            π ⟨((b : GL ι K) : Matrix ι ι K), hmemH b⟩
        rw [show (⟨((((a * b : H) : GL ι K)) : Matrix ι ι K), hmemH (a * b)⟩ : A) =
            ⟨((a : GL ι K) : Matrix ι ι K), hmemH a⟩ *
              ⟨((b : GL ι K) : Matrix ι ι K), hmemH b⟩ from Subtype.ext rfl,
          map_mul] }
  haveI : IsCyclic Eˣ := instIsCyclicUnitsOfFinite
  let He : Subgroup Eˣ := f.range
  haveI : IsCyclic He := Subgroup.isCyclic He
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := He)
  obtain ⟨s, hs⟩ := (MonoidHom.mem_range (f := f)).mp g.2
  have hgen : ∀ h : H, ∃ k : ℕ, f h = (f s) ^ k := by
    intro h
    obtain ⟨k, hk⟩ := j1a_exists_nat_pow_of_mem_zpowers (hg ⟨f h, MonoidHom.mem_range.mpr ⟨h, rfl⟩⟩)
    refine ⟨k, ?_⟩
    have hkval := congrArg Subtype.val hk
    change (f h : Eˣ) = (g : Eˣ) ^ k at hkval
    rw [← hs] at hkval
    exact hkval
  have hkey : ∀ h : H, ∃ k : ℕ, ((h : GL ι K) : Matrix ι ι K) * ε =
      ((s : GL ι K) ^ k) * ε := by
    intro h
    obtain ⟨k, hk⟩ := hgen h
    refine ⟨k, ?_⟩
    have hπ : π ⟨((h : GL ι K) : Matrix ι ι K), hmemH h⟩ =
        π ⟨(((s : GL ι K) ^ k) : Matrix ι ι K), hmemH (s ^ k)⟩ := by
      have h1 : (f h : E) = (f s : E) ^ k := by rw [hk, Units.val_pow_eq_pow_val]
      have h2 : (f s : E) ^ k =
          π ⟨(((s : GL ι K) ^ k) : Matrix ι ι K), hmemH (s ^ k)⟩ := by
        have h3 : (f s : E) = π ⟨((s : GL ι K) : Matrix ι ι K), hmemH s⟩ := rfl
        rw [h3, ← map_pow]
        rfl
      exact h1.trans h2
    have hsub : π ((⟨((h : GL ι K) : Matrix ι ι K), hmemH h⟩ : A) -
        ⟨(((s : GL ι K) ^ k) : Matrix ι ι K), hmemH (s ^ k)⟩) = 0 := by
      rw [map_sub, hπ, sub_self]
    have hmat : (((h : GL ι K) : Matrix ι ι K) -
        (((s : GL ι K) ^ k) : Matrix ι ι K)) * e = 0 := (hπker _).mp hsub
    have heq : ((h : GL ι K) : Matrix ι ι K) * e = ((s : GL ι K) ^ k) * e := by
      rw [Matrix.sub_mul, sub_eq_zero] at hmat
      exact hmat
    have heqStar : ((h : GL ι K) : Matrix ι ι K) *
        formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e =
        ((s : GL ι K) ^ k) * formAdj (RingHom.id K)
          (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e := by
      have h := j1a_star_symm Φ hΦ hSΩ hS he.1 h.2 (Subgroup.pow_mem _ s.2 k) heq
      simpa only [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using h
    rcases hcase with hE | hD
    · rw [← hE]; exact heq
    · obtain ⟨-, -, hεeq⟩ := hD
      calc ((h : GL ι K) : Matrix ι ι K) * ε
          = ((h : GL ι K) : Matrix ι ι K) *
              (e + formAdj (RingHom.id K)
                (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e) := by rw [hεeq]
        _ = ((h : GL ι K) : Matrix ι ι K) * e +
              ((h : GL ι K) : Matrix ι ι K) * formAdj (RingHom.id K)
                (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e := by
              rw [Matrix.mul_add]
        _ = ((s : GL ι K) ^ k) * e + ((s : GL ι K) ^ k) * formAdj (RingHom.id K)
              (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e := by
              rw [heq, heqStar]
        _ = ((s : GL ι K) ^ k) *
              (e + formAdj (RingHom.id K)
                (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) e) := by
              rw [Matrix.mul_add]
        _ = ((s : GL ι K) ^ k) * ε := by rw [hεeq]
  have hsne : (s : GL ι K) * ε ≠ ε := by
    obtain ⟨s₀, hs₀S, hs₀⟩ := hnt
    have hs₀H : s₀ ∈ H := Subgroup.subset_closure hs₀S
    obtain ⟨k, hk⟩ := hkey ⟨s₀, hs₀H⟩
    intro hse
    have hpow : (s : GL ι K) ^ k * ε = ε := j1a_pow_mul_eq_of_mul_eq s ε hse k
    exact hs₀ (hk.trans hpow)
  exact ⟨(s : GL ι K), s.2, j1a_closureS_odd hS hodd s s.2, hsne,
    fun s' hs' => hkey ⟨s', hs'⟩⟩

private lemma j1a_blk_pow_mul_eps {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (s : GL ι K) (ε : Matrix ι ι K) (hid : IsIdempotentElem ε)
    (hcomm : (s : Matrix ι ι K) * ε = ε * (s : Matrix ι ι K)) (k : ℕ) :
    (((j1a_blk s ε hid hcomm : GL ι K) ^ k) : Matrix ι ι K) * ε =
      (((s : GL ι K) ^ k) : Matrix ι ι K) * ε := by
  rw [j1a_blk_pow s ε hid hcomm k]
  simp only [Matrix.add_mul, Matrix.mul_assoc, hid.eq, Matrix.sub_mul, Matrix.one_mul,
    sub_self, add_zero]

private lemma j1a_eps_mem_adjoin {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    {S : Set (GL ι K)} (hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' S)) ε)
    {s : GL ι K} (hs : s ∈ Subgroup.closure S)
    (hcomm : (s : Matrix ι ι K) * ε = ε * (s : Matrix ι ι K))
    (hse : (s : Matrix ι ι K) * ε ≠ ε) :
    ε ∈ Algebra.adjoin K (Units.val ''
      ({j1a_blk s ε hε.2.1 hcomm} : Set (GL ι K))) := by
  obtain ⟨e, he, _hee, hcase⟩ := j1a_exists_prim_idem Φ hΦ hSΩ hS hε
  have hsum : (∑ i ∈ Finset.range (orderOf s), (s : Matrix ι ι K) ^ i) * ε = 0 :=
    j1a_sum_pow_mul_eps_eq_zero Φ hΦ hSΩ hS hodd he hcase hs hse
  have hfix : j1a_fixIdem (orderOf s) (j1a_blk s ε hε.2.1 hcomm) = 1 - ε :=
    j1a_fixIdem_eq_one_sub s ε hε.2.1 hcomm (j1a_closureS_odd hS hodd s hs) hsum
  have hmem : j1a_fixIdem (orderOf s) (j1a_blk s ε hε.2.1 hcomm) ∈
      Algebra.adjoin K (Units.val '' ({j1a_blk s ε hε.2.1 hcomm} : Set (GL ι K))) :=
    j1a_fixIdem_mem_adjoin (orderOf s) (j1a_blk s ε hε.2.1 hcomm)
  have h1e : (1 - ε) ∈ Algebra.adjoin K (Units.val ''
      ({j1a_blk s ε hε.2.1 hcomm} : Set (GL ι K))) := hfix ▸ hmem
  have h := Subalgebra.sub_mem _ (Subalgebra.one_mem _) h1e
  simpa using h

private lemma j1a_field_eq {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) {S : Set (GL ι K)}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {ε : Matrix ι ι K} {b : GL ι K}
    (hbA : (b : Matrix ι ι K) ∈ Algebra.adjoin K (Units.val '' S))
    (hgen : ∀ s' ∈ S, ∃ k : ℕ,
      (s' : Matrix ι ι K) * ε = (((b : GL ι K) ^ k : GL ι K) : Matrix ι ι K) * ε) :
    ∀ a ∈ Algebra.adjoin K (Units.val '' S),
      ∃ c ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))), c * ε = a * ε := by
  let A : Subalgebra K (Matrix ι ι K) := Algebra.adjoin K (Units.val '' S)
  let B : Subalgebra K (Matrix ι ι K) :=
    Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))
  have hbB : (b : Matrix ι ι K) ∈ B :=
    Algebra.subset_adjoin ⟨b, Set.mem_singleton b, rfl⟩
  have hpowB : ∀ k : ℕ, (((b : GL ι K) ^ k : GL ι K) : Matrix ι ι K) ∈ B :=
    fun k => Subalgebra.pow_mem B hbB k
  have hBA : B ≤ A := by
    refine Algebra.adjoin_le ?_
    rintro x ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hbA
  have hcommAB : ∀ {a : Matrix ι ι K}, a ∈ A → ∀ {c : Matrix ι ι K}, c ∈ B → a * c = c * a :=
    fun {a} ha {c} hc => j1a_adjoin_comm hS ha (hBA hc)
  intro a ha
  refine Algebra.adjoin_induction
    (p := fun a _ => ∃ c ∈ B, c * ε = a * ε) ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s', hs', rfl⟩
    obtain ⟨k, hk⟩ := hgen s' hs'
    exact ⟨(((b : GL ι K) ^ k : GL ι K) : Matrix ι ι K), hpowB k, hk.symm⟩
  · intro r
    refine ⟨(algebraMap K B) r, Subalgebra.algebraMap_mem _ r, ?_⟩
    have hB : ((algebraMap K B) r : Matrix ι ι K) = r • (1 : Matrix ι ι K) := by
      rw [Algebra.algebraMap_eq_smul_one]; rfl
    have hA : ((algebraMap K A) r : Matrix ι ι K) = r • (1 : Matrix ι ι K) := by
      rw [Algebra.algebraMap_eq_smul_one]; rfl
    rw [hB, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]
  · intro x y hx hy hpx hpy
    obtain ⟨c, hcB, hc⟩ := hpx
    obtain ⟨c', hc'B, hc'⟩ := hpy
    refine ⟨c + c', Subalgebra.add_mem _ hcB hc'B, ?_⟩
    rw [Matrix.add_mul, hc, hc', Matrix.add_mul]
  · intro x y hx hy hpx hpy
    obtain ⟨c, hcB, hc⟩ := hpx
    obtain ⟨c', hc'B, hc'⟩ := hpy
    refine ⟨c' * c, Subalgebra.mul_mem _ hc'B hcB, ?_⟩
    rw [Matrix.mul_assoc, hc, ← Matrix.mul_assoc,
      ← hcommAB (a := x) hx (c := c') hc'B, Matrix.mul_assoc, hc', ← Matrix.mul_assoc]

private lemma j1a_mem_adjoin_commute {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {S : Set (GL ι K)} {g : GL ι K} (hg : g ∈ Subgroup.centralizer S) :
    ∀ a ∈ Algebra.adjoin K (Units.val '' S),
      (g : Matrix ι ι K) * a = a * (g : Matrix ι ι K) := by
  intro a ha
  refine Algebra.adjoin_induction
    (p := fun a _ => (g : Matrix ι ι K) * a = a * (g : Matrix ι ι K)) ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s, hs, rfl⟩
    have h := (Subgroup.mem_centralizer_iff.mp hg) s hs
    show (g : Matrix ι ι K) * (s : Matrix ι ι K) = (s : Matrix ι ι K) * (g : Matrix ι ι K)
    rw [← Units.val_mul, ← Units.val_mul, h]
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  · intro x y hx hy hx' hy'
    rw [Matrix.mul_add, Matrix.add_mul, hx', hy']
  · intro x y hx hy hx' hy'
    calc (g : Matrix ι ι K) * (x * y) = ((g : Matrix ι ι K) * x) * y := by
          rw [Matrix.mul_assoc]
      _ = (x * (g : Matrix ι ι K)) * y := by rw [hx']
      _ = x * ((g : Matrix ι ι K) * y) := by rw [Matrix.mul_assoc]
      _ = x * (y * (g : Matrix ι ι K)) := by rw [hy']
      _ = (x * y) * (g : Matrix ι ι K) := by rw [← Matrix.mul_assoc]

private lemma j1a_one_sub_commute {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    {S : Set (GL ι K)} (hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ) {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' S)) ε)
    {g : GL ι K} (hgΩ : g ∈ StatedOmega ⇑Φ)
    (hgf : (g : Matrix ι ι K) * (1 - ε) = 1 - ε) :
    (1 - ε) * (g : Matrix ι ι K) = 1 - ε := by
  have hG : IsUnit (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).det :=
    polarGram_isUnit_det Φ hΦ
  have hgstar : formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (g : Matrix ι ι K) = ((g⁻¹ : GL ι K) : Matrix ι ι K) :=
    Geo.formAdj_eq_inv_of_isometry (RingHom.id K) hG g (by
      have h := j1a_gram_isometry Φ (g : Matrix ι ι K)
        (fun v => j1a_statedOmega_le_orth Φ hgΩ v)
      simpa [Matrix.map_id] using h)
  have hadj1e : formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (1 - ε) = 1 - ε := by
    have hneg : formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
        (-ε) = -ε := by
      rw [show (-ε : Matrix ι ι K) = (-1 : K) • ε by rw [neg_one_smul],
        Geo.formAdj_smul, hε.2.2.2.1, show (RingHom.id K) (-1) = -1 from rfl, neg_one_smul]
    rw [show (1 - ε : Matrix ι ι K) = 1 + -ε by abel, Geo.formAdj_add,
      Geo.formAdj_one (RingHom.id K) hG, hneg]
  have h2 : (1 - ε) * ((g⁻¹ : GL ι K) : Matrix ι ι K) = 1 - ε := by
    have h := congrArg (formAdj (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))) hgf
    rwa [Geo.formAdj_mul (RingHom.id K) hG (g : Matrix ι ι K) (1 - ε), hadj1e,
      hgstar] at h
  calc (1 - ε) * (g : Matrix ι ι K)
      = ((1 - ε) * ((g⁻¹ : GL ι K) : Matrix ι ι K)) * (g : Matrix ι ι K) := by rw [h2]
    _ = (1 - ε) * (((g⁻¹ : GL ι K) : Matrix ι ι K) * (g : Matrix ι ι K)) := by
          rw [Matrix.mul_assoc]
    _ = (1 - ε) * 1 := by
          rw [show ((g⁻¹ : GL ι K) : Matrix ι ι K) * (g : Matrix ι ι K) = 1 from by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one]]
    _ = 1 - ε := by rw [Matrix.mul_one]

private lemma j1a_blockgroup_iff {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    {S : Set (GL ι K)} (hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' S)) ε)
    {b : GL ι K} (hbA : (b : Matrix ι ι K) ∈ Algebra.adjoin K (Units.val '' S))
    (hbgen : ∀ s' ∈ S, ∃ k : ℕ,
      (s' : Matrix ι ι K) * ε = (((b : GL ι K) ^ k : GL ι K) : Matrix ι ι K) * ε) :
    ∀ g ∈ StatedOmega ⇑Φ,
      (g ∈ Subgroup.centralizer S ∧ g ∈ glFixing (1 - ε)) ↔
        (g ∈ Subgroup.centralizer {b} ∧ g ∈ glFixing (1 - ε)) := by
  intro g hgΩ
  constructor
  · rintro ⟨hgS, hgf⟩
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr
      (Units.ext (j1a_mem_adjoin_commute hgS b hbA)), hgf⟩
  · rintro ⟨hgb, hgf⟩
    have hgb' : (g : Matrix ι ι K) * (b : Matrix ι ι K) =
        (b : Matrix ι ι K) * (g : Matrix ι ι K) :=
      congrArg Units.val (Subgroup.mem_centralizer_singleton_iff.mp hgb)
    have hgf' : (1 - ε) * (g : Matrix ι ι K) = 1 - ε :=
      j1a_one_sub_commute Φ hΦ hSΩ hε hgΩ hgf
    have hgε : (g : Matrix ι ι K) * ε = ε * (g : Matrix ι ι K) := by
      have h1 : (g : Matrix ι ι K) * ε = (g : Matrix ι ι K) - (1 - ε) := by
        rw [← hgf, Matrix.mul_sub, Matrix.mul_one, sub_sub_cancel]
      have h2 : ε * (g : Matrix ι ι K) = (g : Matrix ι ι K) - (1 - ε) := by
        rw [← hgf', Matrix.sub_mul, Matrix.one_mul, sub_sub_cancel]
      rw [h1, h2]
    refine ⟨?_, hgf⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s' hs'
    obtain ⟨k, hk⟩ := hbgen s' hs'
    have hcommb : Commute (g : Matrix ι ι K) (b : Matrix ι ι K) := hgb'
    have hbk : (g : Matrix ι ι K) * (((b : GL ι K) ^ k : GL ι K) : Matrix ι ι K) =
        (((b : GL ι K) ^ k : GL ι K) : Matrix ι ι K) * (g : Matrix ι ι K) := by
      have h := (hcommb.pow_right k).eq
      simpa only [Units.val_pow_eq_pow_val] using h
    have hsA : (s' : Matrix ι ι K) ∈ Algebra.adjoin K (Units.val '' S) :=
      j1a_closureS_mem_adjoin s' (Subgroup.subset_closure hs')
    have h1eA : (1 - ε) ∈ Algebra.adjoin K (Units.val '' S) :=
      Subalgebra.sub_mem _ (Subalgebra.one_mem _) hε.1
    have hs1 : (s' : Matrix ι ι K) * (1 - ε) = (1 - ε) * (s' : Matrix ι ι K) :=
      j1a_adjoin_comm hS hsA h1eA
    have hsplit : (s' : Matrix ι ι K) =
        (s' : Matrix ι ι K) * ε + (s' : Matrix ι ι K) * (1 - ε) := by
      rw [Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]
    have hleft : (g : Matrix ι ι K) * ((s' : Matrix ι ι K) * ε) =
        ((s' : Matrix ι ι K) * ε) * (g : Matrix ι ι K) := by
      calc (g : Matrix ι ι K) * ((s' : Matrix ι ι K) * ε)
          = (g : Matrix ι ι K) * ((((b : GL ι K) ^ k : GL ι K) : Matrix ι ι K) * ε) := by
              rw [hk]
        _ = ((g : Matrix ι ι K) * (((b : GL ι K) ^ k : GL ι K) : Matrix ι ι K)) * ε := by
              rw [Matrix.mul_assoc]
        _ = ((((b : GL ι K) ^ k : GL ι K) : Matrix ι ι K) * (g : Matrix ι ι K)) * ε := by
              rw [hbk]
        _ = (((b : GL ι K) ^ k : GL ι K) : Matrix ι ι K) * ((g : Matrix ι ι K) * ε) := by
              rw [Matrix.mul_assoc]
        _ = (((b : GL ι K) ^ k : GL ι K) : Matrix ι ι K) * (ε * (g : Matrix ι ι K)) := by
              rw [hgε]
        _ = ((((b : GL ι K) ^ k : GL ι K) : Matrix ι ι K) * ε) * (g : Matrix ι ι K) := by
              rw [Matrix.mul_assoc]
        _ = ((s' : Matrix ι ι K) * ε) * (g : Matrix ι ι K) := by rw [← hk]
    have hright : (g : Matrix ι ι K) * ((s' : Matrix ι ι K) * (1 - ε)) =
        ((s' : Matrix ι ι K) * (1 - ε)) * (g : Matrix ι ι K) := by
      calc (g : Matrix ι ι K) * ((s' : Matrix ι ι K) * (1 - ε))
          = (g : Matrix ι ι K) * ((1 - ε) * (s' : Matrix ι ι K)) := by rw [hs1]
        _ = ((g : Matrix ι ι K) * (1 - ε)) * (s' : Matrix ι ι K) := by rw [Matrix.mul_assoc]
        _ = (1 - ε) * (s' : Matrix ι ι K) := by rw [hgf]
        _ = (s' : Matrix ι ι K) * (1 - ε) := by rw [hs1]
        _ = ((s' : Matrix ι ι K) * (1 - ε)) * (g : Matrix ι ι K) := by
              rw [Matrix.mul_assoc, hgf']
    apply Units.ext
    change (s' : Matrix ι ι K) * (g : Matrix ι ι K) =
      (g : Matrix ι ι K) * (s' : Matrix ι ι K)
    rw [hsplit, Matrix.mul_add, hleft, hright, ← Matrix.add_mul, ← hsplit]

private lemma j1a_idem_transfer {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) {S : Set (GL ι K)}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {ε : Matrix ι ι K} {b : GL ι K}
    (hbA : (b : Matrix ι ι K) ∈ Algebra.adjoin K (Units.val '' S))
    (hεA : ε ∈ Algebra.adjoin K (Units.val '' S))
    (hfield : ∀ a ∈ Algebra.adjoin K (Units.val '' S),
      ∃ c ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))), c * ε = a * ε)
    (hεB : ε ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) :
    ∀ e : Matrix ι ι K, IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e → e * ε = e →
      IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e ∧
        blockDegree (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e =
          blockDegree (Algebra.adjoin K (Units.val '' S)) e := by
  let A : Subalgebra K (Matrix ι ι K) := Algebra.adjoin K (Units.val '' S)
  let B : Subalgebra K (Matrix ι ι K) :=
    Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))
  have hBA : B ≤ A := by
    refine Algebra.adjoin_le ?_
    rintro x ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hbA
  intro e he heε
  have heB : e ∈ B := by
    obtain ⟨c, hcB, hc⟩ := hfield e he.1
    have heq : e = c * ε := (hc.trans heε).symm
    rw [heq]
    exact Subalgebra.mul_mem _ hcB hεB
  have hprim : IsPrimIdemIn B e :=
    ⟨heB, he.2.1, he.2.2.1,
      fun e'' he''B he''id he''e => he.2.2.2 e'' (hBA he''B) he''id he''e⟩
  refine ⟨hprim, ?_⟩
  have hsub : (Subalgebra.toSubmodule B).map (LinearMap.mulRight K e) =
      (Subalgebra.toSubmodule A).map (LinearMap.mulRight K e) := by
    apply le_antisymm
    · intro x hx
      rw [Submodule.mem_map] at hx ⊢
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨a, hBA ha, rfl⟩
    · intro x hx
      rw [Submodule.mem_map] at hx ⊢
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨c, hcB, hc⟩ := hfield a ha
      refine ⟨c, hcB, ?_⟩
      calc c * e = c * (e * ε) := by rw [heε]
        _ = c * (ε * e) := by rw [j1a_adjoin_comm hS he.1 hεA]
        _ = (c * ε) * e := by rw [Matrix.mul_assoc]
        _ = (a * ε) * e := by rw [hc]
        _ = a * (ε * e) := by rw [Matrix.mul_assoc]
        _ = a * (e * ε) := by rw [j1a_adjoin_comm hS he.1 hεA]
        _ = a * e := by rw [heε]
  unfold blockDegree
  rw [hsub]

theorem exists_blockElement_nontrivial {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (S : Set (GL ι K)) (hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' S)) ε)
    (hnt : ∃ s ∈ S, (s : Matrix ι ι K) * ε ≠ ε) :
    ∃ b : GL ι K, b ∈ StatedOmega ⇑Φ ∧ Odd (orderOf b) ∧
      IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
        (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε ∧
      (b : Matrix ι ι K) * ε ≠ ε ∧
      (∀ g ∈ StatedOmega ⇑Φ, (g ∈ Subgroup.centralizer S ∧ g ∈ glFixing (1 - ε)) ↔
        (g ∈ Subgroup.centralizer {b} ∧ g ∈ glFixing (1 - ε))) ∧
      (∀ e : Matrix ι ι K, IsPrimIdemIn (Algebra.adjoin K (Units.val '' S)) e → e * ε = e →
        IsPrimIdemIn (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e ∧
          blockDegree (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) e =
            blockDegree (Algebra.adjoin K (Units.val '' S)) e) := by
  classical
  obtain ⟨s, hs, _hsodd, hsne, hkey⟩ := j1a_choose_generator Φ hΦ hSΩ hS hodd hε hnt
  have hsA : (s : Matrix ι ι K) ∈ Algebra.adjoin K (Units.val '' S) :=
    j1a_closureS_mem_adjoin s hs
  have hcomm : (s : Matrix ι ι K) * ε = ε * (s : Matrix ι ι K) :=
    j1a_adjoin_comm hS hsA hε.1
  let b : GL ι K := j1a_blk s ε hε.2.1 hcomm
  have hbval : (b : Matrix ι ι K) = (s : Matrix ι ι K) * ε + (1 - ε) :=
    j1a_blk_val s ε hε.2.1 hcomm
  have hbA : (b : Matrix ι ι K) ∈ Algebra.adjoin K (Units.val '' S) := by
    rw [hbval]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hsA hε.1)
      (Subalgebra.sub_mem _ (Subalgebra.one_mem _) hε.1)
  have hbodd : Odd (orderOf b) := j1a_odd_orderOf_blk s ε hε.2.1 hcomm
    (j1a_closureS_odd hS hodd s hs)
  have hbiso : ∀ v, Φ ((b : Matrix ι ι K).mulVec v) = Φ v := by
    rw [hbval]
    exact ggOmegaBlk_blk_isometry Φ (polarGram_isUnit_det Φ hΦ) hε.2.1 hε.2.2.2.1 hcomm
      (fun v => j1a_statedOmega_le_orth Φ (j1a_closureS_mem_statedOmega hSΩ s hs) v)
  have hbΩ : b ∈ StatedOmega ⇑Φ :=
    j1a_mem_statedOmega_of_isometry Φ hΦ (by omega) hbiso hbodd
  have hbne : (b : Matrix ι ι K) * ε ≠ ε := by
    rw [hbval, Matrix.add_mul, Matrix.mul_assoc, hε.2.1.eq, Matrix.sub_mul, Matrix.one_mul,
      hε.2.1.eq, sub_self, add_zero]
    exact hsne
  have hεB : ε ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))) :=
    j1a_eps_mem_adjoin Φ hΦ hSΩ hS hodd hε hs hcomm hsne
  have hBA' : Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))) ≤
      Algebra.adjoin K (Units.val '' S) := by
    refine Algebra.adjoin_le ?_
    rintro x ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hbA
  have hprim : IsPrimAdjIdemIn (RingHom.id K)
      (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε :=
    ⟨hεB, hε.2.1, hε.2.2.1, hε.2.2.2.1,
      fun e' he'B he'id he'adj he'e =>
        hε.2.2.2.2 e' (hBA' he'B) he'id he'adj he'e⟩
  have hgen : ∀ s' ∈ S, ∃ k : ℕ,
      (s' : Matrix ι ι K) * ε = (((b : GL ι K) ^ k : GL ι K) : Matrix ι ι K) * ε := by
    intro s' hs'
    obtain ⟨k, hk⟩ := hkey s' (Subgroup.subset_closure hs')
    exact ⟨k, hk.trans (j1a_blk_pow_mul_eps s ε hε.2.1 hcomm k).symm⟩
  have hfield : ∀ a ∈ Algebra.adjoin K (Units.val '' S),
      ∃ c ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K))), c * ε = a * ε :=
    j1a_field_eq Φ hS hbA hgen
  refine ⟨b, hbΩ, hbodd, hprim, hbne, ?_, ?_⟩
  · exact j1a_blockgroup_iff Φ hΦ hSΩ hS hε hbA hgen
  · exact j1a_idem_transfer Φ hS hbA hε.1 hfield hεB

private lemma j1b_adjoin_comm {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {S : Set (GL ι K)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ ⦃a b : Matrix ι ι K⦄, a ∈ Algebra.adjoin K (Units.val '' S) →
      b ∈ Algebra.adjoin K (Units.val '' S) → a * b = b * a := by
  have hcommS : (Units.val '' S : Set (Matrix ι ι K)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    show (s : Matrix ι ι K) * (s' : Matrix ι ι K) =
      (s' : Matrix ι ι K) * (s : Matrix ι ι K)
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val (hS s hs s' hs').eq
  letI : CommSemiring (Algebra.adjoin K (Units.val '' S)) :=
    Algebra.adjoinCommSemiringOfComm K hcommS
  intro a b ha hb
  have h := mul_comm (⟨a, ha⟩ : Algebra.adjoin K (Units.val '' S))
    (⟨b, hb⟩ : Algebra.adjoin K (Units.val '' S))
  simpa only [Subalgebra.coe_mul] using congrArg Subtype.val h

private lemma j1b_mul_eq_smul_of_fixed {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (S : Set (GL ι K)) {f : Matrix ι ι K} (hfid : IsIdempotentElem f)
    (hffix : ∀ s ∈ S, (s : Matrix ι ι K) * f = f) :
    ∀ a ∈ Algebra.adjoin K (Units.val '' S), ∃ c : K, a * f = c • f := by
  intro a ha
  refine Algebra.adjoin_induction (p := fun a _ => ∃ c : K, a * f = c • f) ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s, hs, rfl⟩
    exact ⟨1, by rw [hffix s hs, one_smul]⟩
  · intro r
    exact ⟨r, by rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, Matrix.one_mul]⟩
  · rintro x y _ _ ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by rw [Matrix.add_mul, hc, hd, add_smul]⟩
  · rintro x y _ _ ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨d * c, by rw [Matrix.mul_assoc, hd, Matrix.mul_smul, hc, smul_smul]⟩

private lemma j1b_trivial_unique {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {S : Set (GL ι K)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε q : Matrix ι ι K}
    (hεA : ε ∈ Algebra.adjoin K (Units.val '' S)) (hεid : IsIdempotentElem ε)
    (hεfix : ∀ s ∈ S, (s : Matrix ι ι K) * ε = ε) (hε0 : ε ≠ 0)
    (hqA : q ∈ Algebra.adjoin K (Units.val '' S)) (hqid : IsIdempotentElem q)
    (hqfix : ∀ s ∈ S, (s : Matrix ι ι K) * q = q) (hq0 : q ≠ 0) :
    q = ε := by
  have hcomm : q * ε = ε * q := j1b_adjoin_comm hS hqA hεA
  obtain ⟨c, hc⟩ := j1b_mul_eq_smul_of_fixed S hqid hqfix ε hεA
  obtain ⟨d, hd⟩ := j1b_mul_eq_smul_of_fixed S hεid hεfix q hqA
  have hqεne : q * ε ≠ 0 := by
    intro hqε0
    have hεq0 : ε * q = 0 := by rw [← hcomm, hqε0]
    have hfid : IsIdempotentElem (q + ε) := by
      refine IsIdempotentElem.add hqid hεid ?_
      rw [hqε0, hεq0, add_zero]
    have hffix : ∀ s ∈ S, (s : Matrix ι ι K) * (q + ε) = q + ε := by
      intro s hs
      rw [Matrix.mul_add, hqfix s hs, hεfix s hs]
    obtain ⟨k, hk⟩ := j1b_mul_eq_smul_of_fixed S hfid hffix q hqA
    have hqpe : q * (q + ε) = q := by rw [Matrix.mul_add, hqid.eq, hqε0, add_zero]
    rw [hqpe] at hk
    have hkε : k • ε = 0 := by
      have h : q * ε = k • ε := by
        conv_lhs => rw [hk]
        rw [Matrix.smul_mul, Matrix.add_mul, hqε0, hεid.eq, zero_add]
      rw [← h, hqε0]
    have hk0 : k = 0 := by
      rcases smul_eq_zero.mp hkε with h0 | h0
      · exact h0
      · exact absurd h0 hε0
    rw [hk0, zero_smul] at hk
    exact hq0 hk
  have hcne : c ≠ 0 := by
    intro hc0
    exact hqεne (by rw [hcomm, hc, hc0, zero_smul])
  have hc2 : c * c = c := by
    have h := congrArg (fun x : Matrix ι ι K => ε * x) hc
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, hεid.eq, hc, smul_smul] at h
    have h2 : (c * c - c) • q = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hq0
  have hdne : d ≠ 0 := by
    intro hd0
    exact hqεne (by rw [hd, hd0, zero_smul])
  have hd2 : d * d = d := by
    have h := congrArg (fun x : Matrix ι ι K => q * x) hd
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, hqid.eq, hd, smul_smul] at h
    have h2 : (d * d - d) • ε = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hε0
  have hc1 : c = 1 := by
    have h : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hc2, sub_self]
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 hcne
    · exact sub_eq_zero.mp h0
  have hd1 : d = 1 := by
    have h : d * (d - 1) = 0 := by rw [mul_sub, mul_one, hd2, sub_self]
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 hdne
    · exact sub_eq_zero.mp h0
  have h1 : ε * q = q := by rw [hc, hc1, one_smul]
  have h2 : q * ε = ε := by rw [hd, hd1, one_smul]
  calc q = ε * q := h1.symm
    _ = q * ε := hcomm.symm
    _ = ε := h2

private lemma j1b_pow_comm {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {a b : Matrix ι ι K} (hab : a * b = b * a) (i : ℕ) : a * b ^ i = b ^ i * a := by
  induction i with
  | zero => rw [pow_zero, Matrix.mul_one, Matrix.one_mul]
  | succ i ih => rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, hab,
    ← Matrix.mul_assoc]

private lemma j1b_geom_sum_inv_eq {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (s : GL ι K) {N : ℕ} (hspow : s ^ N = 1) :
    (∑ i ∈ Finset.range N, ((s⁻¹ : GL ι K) : Matrix ι ι K) ^ i) =
      ∑ i ∈ Finset.range N, (s : Matrix ι ι K) ^ i := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hpow' : (s : Matrix ι ι K) ^ N = 1 := by
    rw [← Units.val_pow_eq_pow_val, hspow, Units.val_one]
  have hshift : (∑ j ∈ Finset.range N, (s : Matrix ι ι K) ^ (j + 1)) =
      ∑ j ∈ Finset.range N, (s : Matrix ι ι K) ^ j := by
    have h1 := Finset.sum_range_succ (fun k => (s : Matrix ι ι K) ^ k) N
    have h2 := Finset.sum_range_succ' (fun k => (s : Matrix ι ι K) ^ k) N
    rw [hpow'] at h1
    rw [pow_zero] at h2
    exact (add_right_cancel (h1.symm.trans h2)).symm
  rw [← Finset.sum_range_reflect
    (fun i => ((s⁻¹ : GL ι K) : Matrix ι ι K) ^ i) N]
  rw [← hshift]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [Finset.mem_range] at hj
  have hle : N - 1 - j ≤ N := by omega
  have hk : (s⁻¹ : GL ι K) ^ (N - 1 - j) = s ^ (j + 1) := by
    have hmul : s ^ (N - 1 - j) * s ^ (N - (N - 1 - j)) = 1 := by
      rw [← pow_add, Nat.add_sub_of_le hle, hspow]
    have hsub : N - (N - 1 - j) = j + 1 := by omega
    rw [hsub] at hmul
    exact (eq_inv_of_mul_eq_one_right hmul).symm
  have := congrArg (fun u : GL ι K => (u : Matrix ι ι K)) hk
  simpa [Units.val_pow_eq_pow_val] using this

private lemma j1b_decomp {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (S : Set (GL ι K)) (G : Matrix ι ι K) (hG : IsUnit G.det)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) G (Algebra.adjoin K (Units.val '' S)) ε) :
    ∃ Q : Finset (Matrix ι ι K),
      (∀ p ∈ Q, ClassicalPosition.Block.IsPrimStarIdemIn (formAdj (RingHom.id K) G)
          (Algebra.adjoin K (Units.val '' S)) p ∧ p * (1 - ε) = p) ∧
      (∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → p * q = 0) ∧
      ∑ p ∈ Q, p = 1 - ε := by
  classical
  let A : Subalgebra K (Matrix ι ι K) := Algebra.adjoin K (Units.val '' S)
  have hεid : IsIdempotentElem ε := hε.2.1
  have hεadj : formAdj (RingHom.id K) G ε = ε := hε.2.2.2.1
  have hmem : (1 - ε) ∈ A := Subalgebra.sub_mem A (Subalgebra.one_mem A) hε.1
  have hid : IsIdempotentElem (1 - ε) := by
    show (1 - ε) * (1 - ε) = 1 - ε
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hεid.eq]
    abel
  have hst : formAdj (RingHom.id K) G (1 - ε) = 1 - ε := by
    have h1 : (1 - ε : Matrix ι ι K) = 1 + (-1 : K) • ε := by
      rw [neg_smul, one_smul]
      abel
    rw [h1, Geo.formAdj_add, Geo.formAdj_one (RingHom.id K) hG, Geo.formAdj_smul,
      hεadj]
    rw [show (RingHom.id K) (-1 : K) = -1 from rfl, neg_smul, one_smul]
  obtain ⟨Q, hQ⟩ := ClassicalPosition.Block.exists_finset_isPrimStarIdemIn_sum_eq
    (formAdj (RingHom.id K) G) A (fun a ha b hb => j1b_adjoin_comm hS ha hb)
    (fun a _ b _ => Geo.formAdj_add (RingHom.id K) G a b) hmem hid hst
  exact ⟨Q, hQ.1, hQ.2.1, hQ.2.2⟩

private lemma j1b_exists_moves {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {S : Set (GL ι K)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε q : Matrix ι ι K}
    (hεA : ε ∈ Algebra.adjoin K (Units.val '' S)) (hεid : IsIdempotentElem ε)
    (hεfix : ∀ s ∈ S, (s : Matrix ι ι K) * ε = ε) (hε0 : ε ≠ 0)
    (hqA : q ∈ Algebra.adjoin K (Units.val '' S)) (hqid : IsIdempotentElem q)
    (hq0 : q ≠ 0) (hqε : q * (1 - ε) = q) :
    ∃ s ∈ S, (s : Matrix ι ι K) * q ≠ q := by
  by_contra h
  push Not at h
  have hqeq : q = ε :=
    j1b_trivial_unique hS hεA hεid hεfix hε0 hqA hqid h hq0
  rw [hqeq, Matrix.mul_sub, Matrix.mul_one, hεid.eq, sub_self] at hqε
  exact hε0 hqε.symm

private lemma j1b_geom_kills_of_moved {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {S : Set (GL ι K)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (G : Matrix ι ι K) (hG : IsUnit G.det)
    {s : GL ι K} (hsS : s ∈ S) {N : ℕ} (hN : (N : K) ≠ 0) (hspow : s ^ N = 1)
    (hsG : Matrix.transpose (s : Matrix ι ι K) * G * (s : Matrix ι ι K) = G)
    {p : Matrix ι ι K}
    (hp : ClassicalPosition.Block.IsPrimStarIdemIn (formAdj (RingHom.id K) G)
        (Algebra.adjoin K (Units.val '' S)) p)
    (hmoved : (s : Matrix ι ι K) * p ≠ p) :
    (∑ i ∈ Finset.range N, (s : Matrix ι ι K) ^ i) * p = 0 := by
  classical
  have hsA : (s : Matrix ι ι K) ∈ Algebra.adjoin K (Units.val '' S) :=
    Algebra.subset_adjoin ⟨s, hsS, rfl⟩
  have hpA : p ∈ Algebra.adjoin K (Units.val '' S) := hp.1
  have hpid : IsIdempotentElem p := hp.2.1
  have hpstar : formAdj (RingHom.id K) G p = p := hp.2.2.2.1
  have hsp : (s : Matrix ι ι K) * p = p * (s : Matrix ι ι K) :=
    j1b_adjoin_comm hS hsA hpA
  have hsinv : formAdj (RingHom.id K) G (s : Matrix ι ι K) =
      ((s⁻¹ : GL ι K) : Matrix ι ι K) :=
    Geo.formAdj_eq_inv_of_isometry (RingHom.id K) hG s (by simpa [Matrix.map_id] using hsG)
  set Gs : Matrix ι ι K := ∑ i ∈ Finset.range N, (s : Matrix ι ι K) ^ i with hGs
  have hGs_s : Gs * (s : Matrix ι ι K) = Gs := by
    have h : Gs * ((s : Matrix ι ι K) - 1) = 0 := by
      rw [hGs, geom_sum_mul]
      rw [show (s : Matrix ι ι K) ^ N = 1 from by
        rw [← Units.val_pow_eq_pow_val, hspow, Units.val_one], sub_self]
    rw [Matrix.mul_sub, Matrix.mul_one] at h
    exact sub_eq_zero.mp h
  have hs_Gs : (s : Matrix ι ι K) * Gs = Gs := by
    have hcomm : (s : Matrix ι ι K) * Gs = Gs * (s : Matrix ι ι K) := by
      rw [hGs, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact j1b_pow_comm (a := (s : Matrix ι ι K)) (b := (s : Matrix ι ι K)) rfl i
    rw [hcomm, hGs_s]
  have hGs_pow : ∀ i, Gs * (s : Matrix ι ι K) ^ i = Gs := by
    intro i
    induction i with
    | zero => rw [pow_zero, Matrix.mul_one]
    | succ i ih => rw [pow_succ', ← Matrix.mul_assoc, hGs_s, ih]
  have hGsGs : Gs * Gs = (N : K) • Gs := by
    rw [hGs, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun i _ => hGs_pow i)]
    rw [Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]
  have hp_Gs : p * Gs = Gs * p := by
    rw [hGs, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact j1b_pow_comm (a := p) (b := (s : Matrix ι ι K)) hsp.symm i
  have hfsum : formAdj (RingHom.id K) G Gs =
      ∑ i ∈ Finset.range N, formAdj (RingHom.id K) G ((s : Matrix ι ι K) ^ i) := by
    rw [hGs]
    refine Finset.induction_on (Finset.range N) ?_ ?_
    · simp [formAdj]
    · intro a t hat ih
      rw [Finset.sum_insert hat, Finset.sum_insert hat, Geo.formAdj_add, ih]
  have hpowstar : ∀ i, formAdj (RingHom.id K) G ((s : Matrix ι ι K) ^ i) =
      ((s⁻¹ : GL ι K) : Matrix ι ι K) ^ i := by
    intro i
    induction i with
    | zero => rw [pow_zero, pow_zero, Geo.formAdj_one (RingHom.id K) hG]
    | succ i ih => rw [pow_succ', Geo.formAdj_mul (RingHom.id K) hG, ih, hsinv, pow_succ]
  have hGsstar : formAdj (RingHom.id K) G Gs = Gs := by
    rw [hfsum]
    rw [Finset.sum_congr rfl (fun i _ => hpowstar i)]
    rw [hGs]
    exact j1b_geom_sum_inv_eq s hspow
  have hGsA : Gs ∈ Algebra.adjoin K (Units.val '' S) := by
    rw [hGs]
    exact Subalgebra.sum_mem _ (fun i _ => Subalgebra.pow_mem _ hsA i)
  set P : Matrix ι ι K := (N : K)⁻¹ • (Gs * p) with hP
  have hPA : P ∈ Algebra.adjoin K (Units.val '' S) := by
    rw [hP]
    exact Subalgebra.smul_mem _ (Subalgebra.mul_mem _ hGsA hpA) _
  have hPstar : formAdj (RingHom.id K) G P = P := by
    rw [hP, Geo.formAdj_smul, Geo.formAdj_mul (RingHom.id K) hG, hGsstar, hpstar, hp_Gs]
    rfl
  have hPP : P * P = P := by
    rw [hP, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have h1 : (Gs * p) * (Gs * p) = (N : K) • (Gs * p) := by
      calc (Gs * p) * (Gs * p) = Gs * (p * (Gs * p)) := by rw [Matrix.mul_assoc]
        _ = Gs * ((p * Gs) * p) := by rw [Matrix.mul_assoc]
        _ = Gs * ((Gs * p) * p) := by rw [hp_Gs]
        _ = Gs * (Gs * (p * p)) := by rw [Matrix.mul_assoc]
        _ = (Gs * Gs) * p := by rw [← Matrix.mul_assoc, hpid.eq]
        _ = ((N : K) • Gs) * p := by rw [hGsGs]
        _ = (N : K) • (Gs * p) := by rw [Matrix.smul_mul]
    rw [h1, smul_smul]
    congr 1
    rw [mul_assoc, inv_mul_cancel₀ hN, mul_one]
  have hPp : P * p = P := by
    rw [hP, Matrix.smul_mul, Matrix.mul_assoc, hpid.eq]
  have hsP : (s : Matrix ι ι K) * P = P := by
    rw [hP, Matrix.mul_smul, ← Matrix.mul_assoc, hs_Gs]
  rcases hp.2.2.2.2 P hPA hPP hPstar hPp with hP0 | hPeq
  · have : Gs * p = 0 := by
      rw [hP] at hP0
      have h := congrArg (fun x : Matrix ι ι K => (N : K) • x) hP0
      rwa [smul_zero, smul_smul, mul_inv_cancel₀ hN, one_smul] at h
    simpa [hGs] using this
  · exfalso
    apply hmoved
    calc (s : Matrix ι ι K) * p = (s : Matrix ι ι K) * P := by rw [← hPeq]
      _ = P := hsP
      _ = p := hPeq

private lemma j1b_polar_eq_dot {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Q : QuadraticForm K (ι → K)) (x y : ι → K) :
    QuadraticMap.polar Q x y =
      dotProduct x ((LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Q)).mulVec y) := by
  have h1 : (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Q)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) := rfl
  rw [h1]
  rw [← Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q)) x y,
    Matrix.toBilin'_toMatrix', QuadraticMap.polarBilin_apply_apply]

private lemma j1b_transpose_G_eq {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {G p : Matrix ι ι K} (hG : IsUnit G.det)
    (hadj : formAdj (RingHom.id K) G p = p) :
    Matrix.transpose p * G = G * p := by
  have heid : p.map ⇑(RingHom.id K) = p := by ext i j; rfl
  have h : G * (G⁻¹ * Matrix.transpose p * G) = G * p := by
    have hh := congrArg (fun M => G * M) hadj
    rw [formAdj, heid] at hh
    exact hh
  calc Matrix.transpose p * G
      = (1 : Matrix ι ι K) * (Matrix.transpose p * G) := (Matrix.one_mul _).symm
    _ = (G * G⁻¹) * (Matrix.transpose p * G) := by rw [Matrix.mul_nonsing_inv G hG]
    _ = G * (G⁻¹ * (Matrix.transpose p * G)) := by rw [Matrix.mul_assoc]
    _ = G * (G⁻¹ * Matrix.transpose p * G) := by rw [Matrix.mul_assoc]
    _ = G * p := h

private lemma j1b_polar_orth {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Q : QuadraticForm K (ι → K)) {p : Matrix ι ι K}
    (hG : IsUnit (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Q)).det)
    (hadj : formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Q)) p = p) :
    ∀ x y : ι → K, p.mulVec y = 0 → QuadraticMap.polar Q (p.mulVec x) y = 0 := by
  intro x y hy
  have htrans := j1b_transpose_G_eq hG hadj
  rw [j1b_polar_eq_dot Q (p.mulVec x) y]
  calc (p.mulVec x) ⬝ᵥ ((LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Q)).mulVec y)
      = Matrix.vecMul (p.mulVec x)
          (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Q)) ⬝ᵥ y :=
        Matrix.dotProduct_mulVec _ _ _
    _ = Matrix.vecMul x
          (Matrix.transpose p * LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Q)) ⬝ᵥ y := by
        rw [Matrix.vecMul_mulVec]
    _ = Matrix.vecMul x (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Q) * p) ⬝ᵥ y := by
        rw [htrans]
    _ = x ⬝ᵥ ((LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Q)).mulVec (p.mulVec y)) := by
        rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
    _ = 0 := by rw [hy, Matrix.mulVec_zero]; simp

private lemma j1b_isometry_preserves_G {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Q : QuadraticForm K (ι → K)) (M : Matrix ι ι K)
    (hM : ∀ x : ι → K, Q (M.mulVec x) = Q x) :
    M.transpose * LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Q) * M =
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Q) := by
  have hpol : ∀ x y, QuadraticMap.polar Q (M.mulVec x) (M.mulVec y) = QuadraticMap.polar Q x y := by
    intro x y
    rw [QuadraticMap.polar, QuadraticMap.polar, ← Matrix.mulVec_add, hM (x + y), hM x, hM y]
  apply (LinearEquiv.injective Matrix.toBilin')
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply']
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, ← j1b_polar_eq_dot Q (M.mulVec x) (M.mulVec y),
    ← j1b_polar_eq_dot Q x y]
  exact hpol x y

private lemma j1b_mem_orthogonalGroup_of_mem_statedOmega {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] (Φ : QuadraticForm K (ι → K)) {s : GL ι K}
    (hs : s ∈ StatedOmega ⇑Φ) :
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K s ∈ TauCeti.QuadraticMap.orthogonalGroup Φ := by
  rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (Q := Φ) (Q₀ := ⇑Φ) rfl,
    Subgroup.mem_comap] at hs
  exact CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (Q := Φ) hs

private lemma j1b_quad_isometry_of_mem_statedOmega {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (Φ : QuadraticForm K (ι → K)) {s : GL ι K} (hs : s ∈ StatedOmega ⇑Φ) :
    ∀ v : ι → K, Φ ((s : Matrix ι ι K).mulVec v) = Φ v := by
  have horth := j1b_mem_orthogonalGroup_of_mem_statedOmega Φ hs
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at horth
  intro v
  simpa [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply] using horth v

private lemma j1b_formAdj_eq_inv_of_mem_statedOmega {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (Φ : QuadraticForm K (ι → K))
    (hG : IsUnit (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).det) {s : GL ι K}
    (hs : s ∈ StatedOmega ⇑Φ) :
    formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
        (s : Matrix ι ι K) =
      ((s⁻¹ : GL ι K) : Matrix ι ι K) := by
  have hiso : Matrix.transpose (s : Matrix ι ι K) *
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) * (s : Matrix ι ι K) =
      LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ) :=
    j1b_isometry_preserves_G Φ (s : Matrix ι ι K)
      (j1b_quad_isometry_of_mem_statedOmega Φ hs)
  exact Geo.formAdj_eq_inv_of_isometry (RingHom.id K) hG s
    (by simpa [Matrix.map_id] using hiso)

private lemma j1b_polar_add_left {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (x y z : ι → K) :
    QuadraticMap.polar Φ (x + y) z =
      QuadraticMap.polar Φ x z + QuadraticMap.polar Φ y z := by
  rw [← QuadraticMap.polarBilin_apply_apply Φ (x + y) z, map_add, LinearMap.add_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]

private lemma j1b_polar_add_right {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (x y z : ι → K) :
    QuadraticMap.polar Φ z (x + y) =
      QuadraticMap.polar Φ z x + QuadraticMap.polar Φ z y := by
  rw [QuadraticMap.polar_comm, j1b_polar_add_left, QuadraticMap.polar_comm,
    QuadraticMap.polar_comm Φ y z]

private lemma j1b_polar_sum_right {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (T : Finset (Matrix ι ι K)) (x : Matrix ι ι K → ι → K)
    (z : ι → K) :
    QuadraticMap.polar Φ z (∑ p ∈ T, x p) = ∑ p ∈ T, QuadraticMap.polar Φ z (x p) := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has, j1b_polar_add_right, ih]

private lemma j1b_quad_sum_orthogonal {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (T : Finset (Matrix ι ι K)) (x : Matrix ι ι K → ι → K)
    (hT : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → QuadraticMap.polar Φ (x p) (x q) = 0) :
    Φ (∑ p ∈ T, x p) = ∑ p ∈ T, Φ (x p) := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has,
        QuadraticMap.map_add (⇑Φ) (x a) (∑ p ∈ s, x p)]
      have hs_orth : ∀ p ∈ s, ∀ q ∈ s, p ≠ q →
          QuadraticMap.polar Φ (x p) (x q) = 0 := fun p hp q hq hpq =>
        hT p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq) hpq
      rw [ih hs_orth]
      have hzero : QuadraticMap.polar Φ (x a) (∑ p ∈ s, x p) = 0 := by
        rw [j1b_polar_sum_right]
        refine Finset.sum_eq_zero fun q hq => ?_
        exact hT a (Finset.mem_insert_self a s) q (Finset.mem_insert_of_mem hq)
          (fun h => has (h ▸ hq))
      rw [hzero, add_zero]

private lemma j1b_quad_add_sum_orthogonal {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K)) (x₀ : ι → K) (T : Finset (Matrix ι ι K))
    (x : Matrix ι ι K → ι → K)
    (h0 : ∀ p ∈ T, QuadraticMap.polar Φ x₀ (x p) = 0)
    (hT : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → QuadraticMap.polar Φ (x p) (x q) = 0) :
    Φ (x₀ + ∑ p ∈ T, x p) = Φ x₀ + ∑ p ∈ T, Φ (x p) := by
  rw [QuadraticMap.map_add (⇑Φ) x₀ (∑ p ∈ T, x p),
    j1b_quad_sum_orthogonal Φ T x hT]
  have hzero : QuadraticMap.polar Φ x₀ (∑ p ∈ T, x p) = 0 := by
    rw [j1b_polar_sum_right]
    exact Finset.sum_eq_zero fun p hp => h0 p hp
  rw [hzero, add_zero]

private lemma j1b_block_pow_eq_one {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Q : Finset (Matrix ι ι K)) (sOf : Matrix ι ι K → GL ι K) (ε : Matrix ι ι K) {N : ℕ}
    (hεid : ε * ε = ε)
    (hQid : ∀ p ∈ Q, p * p = p)
    (hQorth : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → p * q = 0)
    (hQsum : ∑ p ∈ Q, p = 1 - ε)
    (hεp : ∀ p ∈ Q, ε * p = 0)
    (hpe : ∀ p ∈ Q, p * ε = 0)
    (hsp : ∀ p ∈ Q, (sOf p : Matrix ι ι K) * p = p * (sOf p : Matrix ι ι K))
    (hspow : ∀ p ∈ Q, (sOf p : GL ι K) ^ N = 1) :
    (ε + ∑ p ∈ Q, (sOf p : Matrix ι ι K) * p) ^ N = 1 := by
  classical
  set b : Matrix ι ι K := ε + ∑ p ∈ Q, (sOf p : Matrix ι ι K) * p with hb
  have hb_eps : b * ε = ε := by
    rw [hb, Matrix.add_mul]
    have hzero : (∑ p ∈ Q, (sOf p : Matrix ι ι K) * p) * ε = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun p hp => by
        rw [Matrix.mul_assoc, hpe p hp, Matrix.mul_zero]
    rw [hεid, hzero, add_zero]
  have hb_p : ∀ p ∈ Q, b * p = (sOf p : Matrix ι ι K) * p := by
    intro p hp
    rw [hb, Matrix.add_mul]
    have hsum : (∑ q ∈ Q, (sOf q : Matrix ι ι K) * q) * p =
        (sOf p : Matrix ι ι K) * p * p := by
      rw [Finset.sum_mul]
      refine Finset.sum_eq_single p ?_ ?_
      · intro q hq hqp
        rw [Matrix.mul_assoc, hQorth q hq p hp hqp, Matrix.mul_zero]
      · intro hpnot; exact absurd hp hpnot
    rw [hεp p hp, zero_add, hsum, Matrix.mul_assoc, hQid p hp]
  have hb_pow_p : ∀ i, ∀ p ∈ Q, b ^ i * p = (sOf p : Matrix ι ι K) ^ i * p := by
    intro i
    induction i with
    | zero => intro p hp; rw [pow_zero, Matrix.one_mul, pow_zero, Matrix.one_mul]
    | succ i ih =>
        intro p hp
        rw [pow_succ, Matrix.mul_assoc, hb_p p hp, hsp p hp, ← Matrix.mul_assoc, ih p hp,
          Matrix.mul_assoc, ← hsp p hp, ← Matrix.mul_assoc, ← pow_succ]
  have hb_pow_eps : ∀ i, b ^ i * ε = ε := by
    intro i
    induction i with
    | zero => rw [pow_zero, Matrix.one_mul]
    | succ i ih => rw [pow_succ, Matrix.mul_assoc, hb_eps, ih]
  have hone : ε + ∑ p ∈ Q, p = 1 := by rw [hQsum]; abel
  calc b ^ N = b ^ N * 1 := (Matrix.mul_one _).symm
    _ = b ^ N * (ε + ∑ p ∈ Q, p) := by rw [hone]
    _ = b ^ N * ε + b ^ N * (∑ p ∈ Q, p) := by rw [Matrix.mul_add]
    _ = ε + ∑ p ∈ Q, b ^ N * p := by rw [hb_pow_eps N, Finset.mul_sum]
    _ = ε + ∑ p ∈ Q, p := by
          congr 1
          refine Finset.sum_congr rfl fun p hp => ?_
          have h1 : (sOf p : Matrix ι ι K) ^ N = 1 := by
            rw [← Units.val_pow_eq_pow_val, hspow p hp, Units.val_one]
          rw [hb_pow_p N p hp, h1, Matrix.one_mul]
    _ = 1 := hone

private lemma j1b_block_isometry {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Φ : QuadraticForm K (ι → K))
    (hG : IsUnit (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)).det)
    (Q : Finset (Matrix ι ι K)) (sOf : Matrix ι ι K → GL ι K) (ε : Matrix ι ι K)
    (hεadj : formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) ε = ε)
    (hQadj : ∀ p ∈ Q,
      formAdj (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)) p = p)
    (hεp : ∀ p ∈ Q, ε * p = 0)
    (hQorth : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → p * q = 0)
    (hQsum : ∑ p ∈ Q, p = 1 - ε)
    (hεs : ∀ p ∈ Q, ε * (sOf p : Matrix ι ι K) = (sOf p : Matrix ι ι K) * ε)
    (hspq : ∀ p ∈ Q, ∀ q ∈ Q, p * (sOf q : Matrix ι ι K) = (sOf q : Matrix ι ι K) * p)
    (hiso : ∀ p ∈ Q, ∀ v : ι → K, Φ ((sOf p : Matrix ι ι K).mulVec v) = Φ v) :
    ∀ v : ι → K,
      Φ (((ε + ∑ p ∈ Q, (sOf p : Matrix ι ι K) * p)).mulVec v) = Φ v := by
  classical
  intro v
  set x₀ : ι → K := ε.mulVec v with hx₀
  set x : Matrix ι ι K → ι → K := fun p => (sOf p : Matrix ι ι K).mulVec (p.mulVec v) with hx
  have hsum_mulVec : (∑ p ∈ Q, (sOf p : Matrix ι ι K) * p).mulVec v = ∑ p ∈ Q, x p := by
    rw [Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [hx]
    rw [Matrix.mulVec_mulVec]
  have hbv : ((ε + ∑ p ∈ Q, (sOf p : Matrix ι ι K) * p)).mulVec v = x₀ + ∑ p ∈ Q, x p := by
    rw [Matrix.add_mulVec, hsum_mulVec]
  have h0 : ∀ p ∈ Q, QuadraticMap.polar Φ x₀ (x p) = 0 := by
    intro p hp
    have hzero : ε.mulVec (x p) = 0 := by
      simp only [hx]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      have h1 : (ε * (sOf p : Matrix ι ι K)) * p = 0 := by
        calc (ε * (sOf p : Matrix ι ι K)) * p
            = ((sOf p : Matrix ι ι K) * ε) * p := by rw [hεs p hp]
          _ = (sOf p : Matrix ι ι K) * (ε * p) := Matrix.mul_assoc _ _ _
          _ = 0 := by rw [hεp p hp, Matrix.mul_zero]
      rw [h1, Matrix.zero_mulVec]
    simpa [hx₀] using j1b_polar_orth Φ hG hεadj v (x p) hzero
  have hT : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → QuadraticMap.polar Φ (x p) (x q) = 0 := by
    intro p hp q hq hpq
    have hzero : p.mulVec (x q) = 0 := by
      simp only [hx]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      have h1 : (p * (sOf q : Matrix ι ι K)) * q = 0 := by
        calc (p * (sOf q : Matrix ι ι K)) * q
            = ((sOf q : Matrix ι ι K) * p) * q := by rw [hspq p hp q hq]
          _ = (sOf q : Matrix ι ι K) * (p * q) := Matrix.mul_assoc _ _ _
          _ = 0 := by rw [hQorth p hp q hq hpq, Matrix.mul_zero]
      rw [h1, Matrix.zero_mulVec]
    have h3 : p.mulVec ((sOf p : Matrix ι ι K).mulVec v) = x p := by
      simp only [hx]
      rw [Matrix.mulVec_mulVec, hspq p hp p hp, Matrix.mulVec_mulVec]
    have h2 := j1b_polar_orth Φ hG (hQadj p hp) ((sOf p : Matrix ι ι K).mulVec v) (x q) hzero
    rw [h3] at h2
    exact h2
  have h0' : ∀ p ∈ Q, QuadraticMap.polar Φ x₀ (p.mulVec v) = 0 := by
    intro p hp
    have hzero : ε.mulVec (p.mulVec v) = 0 := by
      rw [Matrix.mulVec_mulVec, hεp p hp, Matrix.zero_mulVec]
    simpa [hx₀] using j1b_polar_orth Φ hG hεadj v (p.mulVec v) hzero
  have hT' : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q →
      QuadraticMap.polar Φ (p.mulVec v) (q.mulVec v) = 0 := by
    intro p hp q hq hpq
    have hzero : p.mulVec (q.mulVec v) = 0 := by
      rw [Matrix.mulVec_mulVec, hQorth p hp q hq hpq, Matrix.zero_mulVec]
    exact j1b_polar_orth Φ hG (hQadj p hp) v (q.mulVec v) hzero
  have hv : x₀ + ∑ p ∈ Q, p.mulVec v = v := by
    have hone : ε + ∑ p ∈ Q, p = 1 := by rw [hQsum]; abel
    rw [hx₀, ← Matrix.sum_mulVec, ← Matrix.add_mulVec, hone, Matrix.one_mulVec]
  have hterms : (∑ p ∈ Q, Φ (x p)) = ∑ p ∈ Q, Φ (p.mulVec v) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [hx]
    exact hiso p hp (p.mulVec v)
  have hquad2 := (j1b_quad_add_sum_orthogonal Φ x₀ Q (fun p => p.mulVec v) h0' hT').symm
  rw [hv] at hquad2
  rw [hbv, j1b_quad_add_sum_orthogonal Φ x₀ Q x h0 hT, hterms]
  exact hquad2

theorem exists_blockElement_trivial {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    [Fintype K] [CharP K 2] (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h8 : 8 ≤ Fintype.card ι)
    (S : Set (GL ι K)) (hSΩ : ∀ s ∈ S, s ∈ StatedOmega ⇑Φ)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix ι ι K}
    (hε : IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin K (Units.val '' S)) ε)
    (htriv : ∀ s ∈ S, (s : Matrix ι ι K) * ε = ε) :
    ∃ b : GL ι K, b ∈ StatedOmega ⇑Φ ∧ Odd (orderOf b) ∧
      IsPrimAdjIdemIn (RingHom.id K) (LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ))
        (Algebra.adjoin K (Units.val '' ({b} : Set (GL ι K)))) ε ∧
      (b : Matrix ι ι K) * ε = ε ∧
      (∀ g ∈ StatedOmega ⇑Φ, (g ∈ Subgroup.centralizer S ∧ g ∈ glFixing (1 - ε)) ↔
        (g ∈ Subgroup.centralizer {b} ∧ g ∈ glFixing (1 - ε))) := by
  classical
  let G : Matrix ι ι K := LinearMap.toMatrix₂' K (QuadraticMap.polarBilin Φ)
  have hG : IsUnit G.det := polarGram_isUnit_det Φ hΦ
  obtain ⟨Q, hQprim, hQorth, hQsum⟩ := j1b_decomp S G hG hS hε
  let sOf : Matrix ι ι K → GL ι K := fun p =>
    if hp : p ∈ Q then
      Classical.choose (j1b_exists_moves hS hε.1 hε.2.1 htriv hε.2.2.1
        (hQprim p hp).1.1 (hQprim p hp).1.2.1 (hQprim p hp).1.2.2.1 (hQprim p hp).2)
    else 1
  have hsOf_mem : ∀ p ∈ Q, sOf p ∈ S := by
    intro p hp
    have hspec := Classical.choose_spec (j1b_exists_moves hS hε.1 hε.2.1 htriv hε.2.2.1
      (hQprim p hp).1.1 (hQprim p hp).1.2.1 (hQprim p hp).1.2.2.1 (hQprim p hp).2)
    simpa only [sOf, dif_pos hp] using hspec.1
  have hsOf_moved : ∀ p ∈ Q, (sOf p : Matrix ι ι K) * p ≠ p := by
    intro p hp
    have hspec := Classical.choose_spec (j1b_exists_moves hS hε.1 hε.2.1 htriv hε.2.2.1
      (hQprim p hp).1.1 (hQprim p hp).1.2.1 (hQprim p hp).1.2.2.1 (hQprim p hp).2)
    simpa only [sOf, dif_pos hp] using hspec.2
  let N : ℕ := ∏ p ∈ Q, orderOf (sOf p)
  have hdvd : ∀ p ∈ Q, orderOf (sOf p) ∣ N := fun p hp =>
    Finset.dvd_prod_of_mem (fun q => orderOf (sOf q)) hp
  have hspow : ∀ p ∈ Q, (sOf p) ^ N = 1 := fun p hp =>
    orderOf_dvd_iff_pow_eq_one.mp (hdvd p hp)
  have hoddN : Odd N := by
    show Odd (∏ p ∈ Q, orderOf (sOf p))
    refine Finset.prod_induction (fun p => orderOf (sOf p)) Odd
      (fun a b ha hb => ha.mul hb) odd_one fun p hp => hodd (sOf p) (hsOf_mem p hp)
  have hNcast : (N : K) ≠ 0 := by
    intro h0
    have hEven : Even N := by
      obtain ⟨k, hk⟩ := (CharP.cast_eq_zero_iff K 2 N).mp h0
      exact ⟨k, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hoddN) hEven
  let b : Matrix ι ι K := ε + ∑ p ∈ Q, (sOf p : Matrix ι ι K) * p
  have hQid : ∀ p ∈ Q, p * p = p := fun p hp => (hQprim p hp).1.2.1.eq
  have hpe : ∀ p ∈ Q, p * ε = 0 := by
    intro p hp
    have h := (hQprim p hp).2
    rw [Matrix.mul_sub, Matrix.mul_one] at h
    exact sub_eq_self.mp h
  have hεp : ∀ p ∈ Q, ε * p = 0 := by
    intro p hp
    rw [j1b_adjoin_comm hS hε.1 (hQprim p hp).1.1, hpe p hp]
  have hsA_mem : ∀ p ∈ Q, (sOf p : Matrix ι ι K) ∈ Algebra.adjoin K (Units.val '' S) :=
    fun p hp => Algebra.subset_adjoin ⟨sOf p, hsOf_mem p hp, rfl⟩
  have hsp : ∀ p ∈ Q, (sOf p : Matrix ι ι K) * p = p * (sOf p : Matrix ι ι K) :=
    fun p hp => j1b_adjoin_comm hS (hsA_mem p hp) (hQprim p hp).1.1
  have hεs : ∀ p ∈ Q, ε * (sOf p : Matrix ι ι K) = (sOf p : Matrix ι ι K) * ε :=
    fun p hp => j1b_adjoin_comm hS hε.1 (hsA_mem p hp)
  have hspq : ∀ p ∈ Q, ∀ q ∈ Q,
      p * (sOf q : Matrix ι ι K) = (sOf q : Matrix ι ι K) * p :=
    fun p hp q hq => j1b_adjoin_comm hS (hQprim p hp).1.1 (hsA_mem q hq)
  have hbNmat : b ^ N = 1 :=
    j1b_block_pow_eq_one Q sOf ε hε.2.1 hQid hQorth hQsum hεp hpe hsp hspow
  have hNpos : 0 < N := by
    show 0 < ∏ p ∈ Q, orderOf (sOf p)
    refine Finset.prod_pos fun p hp => ?_
    obtain ⟨k, hk⟩ := hodd (sOf p) (hsOf_mem p hp)
    omega
  have hbunit : IsUnit b := by
    refine isUnit_iff_exists.mpr ⟨b ^ (N - 1), ?_, ?_⟩
    · rw [← pow_succ', Nat.sub_add_cancel hNpos, hbNmat]
    · rw [← pow_succ, Nat.sub_add_cancel hNpos, hbNmat]
  let bGL : GL ι K := hbunit.unit
  have hbGL_val : (bGL : Matrix ι ι K) = b := IsUnit.unit_spec hbunit
  have hbGL_pow : bGL ^ N = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hbGL_val, hbNmat, Units.val_one]
  have hb_eps : b * ε = ε := by
    change (ε + ∑ p ∈ Q, (sOf p : Matrix ι ι K) * p) * ε = ε
    rw [Matrix.add_mul]
    have hzero : (∑ p ∈ Q, (sOf p : Matrix ι ι K) * p) * ε = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun p hp => by
        rw [Matrix.mul_assoc, hpe p hp, Matrix.mul_zero]
    rw [hε.2.1.eq, hzero, add_zero]
  have hb_p : ∀ p ∈ Q, b * p = (sOf p : Matrix ι ι K) * p := by
    intro p hp
    change (ε + ∑ q ∈ Q, (sOf q : Matrix ι ι K) * q) * p = (sOf p : Matrix ι ι K) * p
    rw [Matrix.add_mul]
    have hsum : (∑ q ∈ Q, (sOf q : Matrix ι ι K) * q) * p =
        (sOf p : Matrix ι ι K) * p * p := by
      rw [Finset.sum_mul]
      refine Finset.sum_eq_single p ?_ ?_
      · intro q hq hqp
        rw [Matrix.mul_assoc, hQorth q hq p hp hqp, Matrix.mul_zero]
      · intro hpnot; exact absurd hp hpnot
    rw [hεp p hp, zero_add, hsum, Matrix.mul_assoc, hQid p hp]
  have hbA : b ∈ Algebra.adjoin K (Units.val '' S) := by
    change ε + ∑ p ∈ Q, (sOf p : Matrix ι ι K) * p ∈ Algebra.adjoin K (Units.val '' S)
    refine Subalgebra.add_mem _ hε.1 ?_
    refine Subalgebra.sum_mem _ fun p hp =>
      Subalgebra.mul_mem _ (hsA_mem p hp) (hQprim p hp).1.1
  have hiso : ∀ p ∈ Q, ∀ v : ι → K, Φ ((sOf p : Matrix ι ι K).mulVec v) = Φ v :=
    fun p hp => j1b_quad_isometry_of_mem_statedOmega Φ (hSΩ (sOf p) (hsOf_mem p hp))
  have hb_iso : ∀ v : ι → K, Φ (b.mulVec v) = Φ v := by
    have h := j1b_block_isometry Φ hG Q sOf ε hε.2.2.2.1
      (fun p hp => (hQprim p hp).1.2.2.2.1) hεp hQorth hQsum hεs hspq hiso
    simpa only [b] using h
  have hbGL_orth : CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K bGL ∈
      TauCeti.QuadraticMap.orthogonalGroup Φ := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, hbGL_val]
    exact hb_iso v
  have hbGL_omega : bGL ∈ StatedOmega ⇑Φ := by
    rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (Q := Φ) (Q₀ := ⇑Φ) rfl,
      Subgroup.mem_comap]
    have hpowmap : ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K) bGL) ^ N = 1 := by
      rw [← map_pow, hbGL_pow, map_one]
    refine CFSG.LocalAnalysis.GLTheoremA.T173M.mem_orthDerived_of_odd_pow_of_six_le Φ hΦ ?_
      hbGL_orth hoddN hpowmap
    rw [Module.finrank_fintype_fun_eq_card]
    omega
  have hodd_bGL : Odd (orderOf bGL) :=
    Odd.of_dvd_nat hoddN (orderOf_dvd_iff_pow_eq_one.mpr hbGL_pow)
  have hb_pow_eps : ∀ i, b ^ i * ε = ε := by
    intro i
    induction i with
    | zero => rw [pow_zero, Matrix.one_mul]
    | succ i ih => rw [pow_succ, Matrix.mul_assoc, hb_eps, ih]
  have hspG : ∀ p ∈ Q,
      Matrix.transpose (sOf p : Matrix ι ι K) * G * (sOf p : Matrix ι ι K) = G :=
    fun p hp => j1b_isometry_preserves_G Φ (sOf p : Matrix ι ι K) (hiso p hp)
  let P : Matrix ι ι K := (N : K)⁻¹ • ∑ i ∈ Finset.range N, (bGL : Matrix ι ι K) ^ i
  have hP_mem : P ∈ Algebra.adjoin K (Units.val '' ({bGL} : Set (GL ι K))) := by
    refine Subalgebra.smul_mem _ ?_ _
    refine Subalgebra.sum_mem _ fun i _ => Subalgebra.pow_mem _ ?_ i
    exact Algebra.subset_adjoin ⟨bGL, Set.mem_singleton bGL, rfl⟩
  have hP_eps : P * ε = ε := by
    change ((N : K)⁻¹ • ∑ i ∈ Finset.range N, (bGL : Matrix ι ι K) ^ i) * ε = ε
    rw [Matrix.smul_mul, Finset.sum_mul]
    have hsum : (∑ i ∈ Finset.range N, (bGL : Matrix ι ι K) ^ i * ε) = (N : K) • ε := by
      have h1 : (∑ i ∈ Finset.range N, (bGL : Matrix ι ι K) ^ i * ε) =
          ∑ _i ∈ Finset.range N, ε := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hbGL_val, hb_pow_eps i]
      rw [h1, Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]
    rw [hsum, smul_smul, inv_mul_cancel₀ hNcast, one_smul]
  have hP_p : ∀ p ∈ Q, P * p = 0 := by
    intro p hp
    have hb_pow_p : ∀ i, b ^ i * p = (sOf p : Matrix ι ι K) ^ i * p := by
      intro i
      induction i with
      | zero => rw [pow_zero, Matrix.one_mul, pow_zero, Matrix.one_mul]
      | succ i ih =>
          rw [pow_succ, Matrix.mul_assoc, hb_p p hp, hsp p hp, ← Matrix.mul_assoc, ih,
            Matrix.mul_assoc, ← hsp p hp, ← Matrix.mul_assoc, ← pow_succ]
    change ((N : K)⁻¹ • ∑ i ∈ Finset.range N, (bGL : Matrix ι ι K) ^ i) * p = 0
    rw [Matrix.smul_mul, Finset.sum_mul]
    have hsum : (∑ i ∈ Finset.range N, (bGL : Matrix ι ι K) ^ i * p) =
        (∑ i ∈ Finset.range N, (sOf p : Matrix ι ι K) ^ i) * p := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hbGL_val]
      exact hb_pow_p i
    rw [hsum]
    have hkill := j1b_geom_kills_of_moved hS G hG (hsOf_mem p hp) hNcast (hspow p hp)
      (hspG p hp) (hQprim p hp).1 (hsOf_moved p hp)
    rw [hkill, smul_zero]
  have hP_eq : P = ε := by
    have hone : ε + ∑ p ∈ Q, p = 1 := by rw [hQsum]; abel
    calc P = P * 1 := (Matrix.mul_one P).symm
      _ = P * (ε + ∑ p ∈ Q, p) := by rw [hone]
      _ = P * ε + P * (∑ p ∈ Q, p) := by rw [Matrix.mul_add]
      _ = ε + ∑ p ∈ Q, P * p := by rw [hP_eps, Finset.mul_sum]
      _ = ε + ∑ _p ∈ Q, (0 : Matrix ι ι K) := by
            congr 1
            exact Finset.sum_congr rfl fun p hp => hP_p p hp
      _ = ε := by simp
  have hε_mem : ε ∈ Algebra.adjoin K (Units.val '' ({bGL} : Set (GL ι K))) := by
    rw [← hP_eq]
    exact hP_mem
  have hA'le : Algebra.adjoin K (Units.val '' ({bGL} : Set (GL ι K))) ≤
      Algebra.adjoin K (Units.val '' S) := by
    refine Algebra.adjoin_le ?_
    rintro x ⟨g, hg, rfl⟩
    rw [Set.mem_singleton_iff] at hg
    rw [hg, hbGL_val]
    exact hbA
  have hεprim : IsPrimAdjIdemIn (RingHom.id K) G
      (Algebra.adjoin K (Units.val '' ({bGL} : Set (GL ι K)))) ε := by
    refine ⟨hε_mem, hε.2.1, hε.2.2.1, hε.2.2.2.1, ?_⟩
    intro e' he'A he'id he'adj he'e
    exact hε.2.2.2.2 e' (hA'le he'A) he'id he'adj he'e
  have hbGL_eps : (bGL : Matrix ι ι K) * ε = ε := by rw [hbGL_val, hb_eps]
  have hfix_cent : ∀ g ∈ StatedOmega ⇑Φ, g ∈ glFixing (1 - ε) →
      (g ∈ Subgroup.centralizer S ∧ g ∈ Subgroup.centralizer ({bGL} : Set (GL ι K))) := by
    intro g hgΩ hgfix
    have hgadj : formAdj (RingHom.id K) G (g : Matrix ι ι K) =
        ((g⁻¹ : GL ι K) : Matrix ι ι K) :=
      j1b_formAdj_eq_inv_of_mem_statedOmega Φ hG hgΩ
    have h1me : formAdj (RingHom.id K) G (1 - ε) = 1 - ε := by
      have h1 : (1 - ε : Matrix ι ι K) = 1 + (-1 : K) • ε := by
        rw [neg_smul, one_smul]; abel
      rw [h1, Geo.formAdj_add, Geo.formAdj_one (RingHom.id K) hG, Geo.formAdj_smul,
        hε.2.2.2.1]
      rw [show (RingHom.id K) (-1 : K) = -1 from rfl, neg_smul, one_smul]
    have hgf : (g : Matrix ι ι K) * (1 - ε) = 1 - ε := hgfix
    have hfg : (1 - ε) * (g : Matrix ι ι K) = 1 - ε := by
      have h := congrArg (formAdj (RingHom.id K) G) hgf
      rw [Geo.formAdj_mul (RingHom.id K) hG, h1me, hgadj] at h
      have h2 := congrArg (fun M : Matrix ι ι K => M * (g : Matrix ι ι K)) h
      rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one] at h2
      exact h2.symm
    have hge : (g : Matrix ι ι K) * ε = ε * (g : Matrix ι ι K) := by
      have hgdec1 : (g : Matrix ι ι K) = (g : Matrix ι ι K) * ε + (1 - ε) := by
        calc (g : Matrix ι ι K) = (g : Matrix ι ι K) * 1 := (Matrix.mul_one _).symm
          _ = (g : Matrix ι ι K) * (ε + (1 - ε)) := by
                rw [show ε + (1 - ε) = (1 : Matrix ι ι K) by abel]
          _ = (g : Matrix ι ι K) * ε + (g : Matrix ι ι K) * (1 - ε) := by rw [Matrix.mul_add]
          _ = (g : Matrix ι ι K) * ε + (1 - ε) := by rw [hgf]
      have hgdec2 : (g : Matrix ι ι K) = ε * (g : Matrix ι ι K) + (1 - ε) := by
        calc (g : Matrix ι ι K) = 1 * (g : Matrix ι ι K) := (Matrix.one_mul _).symm
          _ = (ε + (1 - ε)) * (g : Matrix ι ι K) := by
                rw [show ε + (1 - ε) = (1 : Matrix ι ι K) by abel]
          _ = ε * (g : Matrix ι ι K) + (1 - ε) * (g : Matrix ι ι K) := by rw [Matrix.add_mul]
          _ = ε * (g : Matrix ι ι K) + (1 - ε) := by rw [hfg]
      exact add_right_cancel (hgdec1.symm.trans hgdec2)
    have hcomm_of : ∀ a : Matrix ι ι K, a * ε = ε → ε * a = ε →
        a * (g : Matrix ι ι K) = (g : Matrix ι ι K) * a := by
      intro a hae hea
      have haf : a * (1 - ε) = (1 - ε) * a := by
        rw [Matrix.mul_sub, Matrix.mul_one, hae, Matrix.sub_mul, Matrix.one_mul, hea]
      have hadec : a = ε + (1 - ε) * a := by
        calc a = a * 1 := (Matrix.mul_one a).symm
          _ = a * (ε + (1 - ε)) := by
                rw [show ε + (1 - ε) = (1 : Matrix ι ι K) by abel]
          _ = a * ε + a * (1 - ε) := by rw [Matrix.mul_add]
          _ = ε + (1 - ε) * a := by rw [hae, haf]
      have hgdec : (g : Matrix ι ι K) = ε * (g : Matrix ι ι K) + (1 - ε) := by
        calc (g : Matrix ι ι K) = 1 * (g : Matrix ι ι K) := (Matrix.one_mul _).symm
          _ = (ε + (1 - ε)) * (g : Matrix ι ι K) := by
                rw [show ε + (1 - ε) = (1 : Matrix ι ι K) by abel]
          _ = ε * (g : Matrix ι ι K) + (1 - ε) * (g : Matrix ι ι K) := by rw [Matrix.add_mul]
          _ = ε * (g : Matrix ι ι K) + (1 - ε) := by rw [hfg]
      calc a * (g : Matrix ι ι K)
          = a * (ε * (g : Matrix ι ι K) + (1 - ε)) := by conv_lhs => rw [hgdec]
        _ = a * (ε * (g : Matrix ι ι K)) + a * (1 - ε) := by rw [Matrix.mul_add]
        _ = (a * ε) * (g : Matrix ι ι K) + a * (1 - ε) := by rw [← Matrix.mul_assoc]
        _ = ε * (g : Matrix ι ι K) + (1 - ε) * a := by rw [hae, haf]
        _ = (g : Matrix ι ι K) * a := by
              conv_rhs => rw [hadec]
              rw [Matrix.mul_add, hge, ← Matrix.mul_assoc, hgf]
    have hcentS : g ∈ Subgroup.centralizer S := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hsA : (s : Matrix ι ι K) ∈ Algebra.adjoin K (Units.val '' S) :=
        Algebra.subset_adjoin ⟨s, hs, rfl⟩
      have hse : (s : Matrix ι ι K) * ε = ε := htriv s hs
      have hes : ε * (s : Matrix ι ι K) = ε := by
        rw [← j1b_adjoin_comm hS hsA hε.1, hse]
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul]
      exact hcomm_of (s : Matrix ι ι K) hse hes
    have hcentb : g ∈ Subgroup.centralizer ({bGL} : Set (GL ι K)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul, hbGL_val]
      exact (hcomm_of b hb_eps (by rw [j1b_adjoin_comm hS hε.1 hbA, hb_eps])).symm
    exact ⟨hcentS, hcentb⟩
  have hcentral : ∀ g ∈ StatedOmega ⇑Φ,
      (g ∈ Subgroup.centralizer S ∧ g ∈ glFixing (1 - ε)) ↔
      (g ∈ Subgroup.centralizer ({bGL} : Set (GL ι K)) ∧ g ∈ glFixing (1 - ε)) := by
    intro g hgΩ
    constructor
    · rintro ⟨_, hfix⟩
      exact ⟨(hfix_cent g hgΩ hfix).2, hfix⟩
    · rintro ⟨_, hfix⟩
      exact ⟨(hfix_cent g hgΩ hfix).1, hfix⟩
  exact ⟨bGL, hbGL_omega, hodd_bGL, hεprim, hbGL_eps, hcentral⟩

end CFSG.StandardType.TableC

end
