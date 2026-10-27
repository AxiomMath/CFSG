module

public import CFSG.RankThree.Native.LyFiveTheory
public import Mathlib.Algebra.Order.Ring.Star

public noncomputable section

namespace CFSG.RankThree.Native

open Subgroup
open scoped commutatorElement Matrix

variable {G : Type*} [Group G]

theorem zmod5_val_one : (1 : ZMod 5).val = 1 := rfl

theorem mem_normalizer_of_conj_le {H : Subgroup G} [Finite H] {g : G}
    (hg : ∀ h ∈ H, g * h * g⁻¹ ∈ H) : g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hg y hy, fun hy => ?_⟩
  let f : H → H := fun h => ⟨g * h * g⁻¹, hg h h.2⟩
  have hf : Function.Injective f := fun h h' e => by
    have := congrArg Subtype.val e
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  obtain ⟨h, hh⟩ := (Finite.injective_iff_surjective.1 hf) ⟨_, hy⟩
  have := congrArg Subtype.val hh
  simp only [f, mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact h.2

structure FiveMRel (x : G) (v : Fin 4 → G) (ω : Fin 4 → Fin 4 → ZMod 5) (a b : G)
    (Ab Bb : Matrix (Fin 4) (Fin 4) (ZMod 5)) (αc βc : Fin 4 → ZMod 5) : Prop where
  q : FiveQRel x v ω
  a25 : a ^ 25 = 1
  ax : a ^ 5 = x
  b8 : b ^ 8 = 1
  b4 : b ^ 4 ≠ 1
  bx : b * x = x ^ 2 * b
  av : ∀ i, a * v i = fiveNF x v (αc i) (fun j => Ab j i) * a
  bv : ∀ i, b * v i = fiveNF x v (βc i) (fun j => Bb j i) * b
  vM : ∀ i, v i ∈ closure ({a, b} : Set G)

structure CosetCert (x : G) (v : Fin 4 → G) (a b : G) (Ab Bb : Matrix (Fin 4) (Fin 4) (ZMod 5))
    (n : ℕ) (par : ℕ → ℕ) (gen : ℕ → Bool) (t : ℕ → G)
    (tb : ℕ → Matrix (Fin 4) (Fin 4) (ZMod 5)) (next : ℕ → Bool → ℕ)
    (qc : ℕ → Bool → ZMod 5 × (Fin 4 → ZMod 5)) : Prop where
  pos : 0 < n
  par_lt : ∀ k, 0 < k → k < n → par k < k
  t_zero : t 0 = 1
  t_succ : ∀ k, 0 < k → k < n → t k = (if gen k then b else a) * t (par k)
  tb_zero : tb 0 = 1
  tb_succ : ∀ k, 0 < k → k < n → tb k = (if gen k then Bb else Ab) * tb (par k)
  tb_inj : ∀ k l, k < n → l < n → tb k = tb l → k = l
  next_lt : ∀ k s, k < n → next k s < n
  rel : ∀ k s, k < n →
    (if s then b else a) * t k = t (next k s) * fiveNF x v (qc k s).1 (qc k s).2

@[expose] def fiveU (a b : G) : Subgroup G :=
  closure {a, b * a * b⁻¹, b ^ 2 * a * (b ^ 2)⁻¹, b ^ 3 * a * (b ^ 3)⁻¹, b ^ 4}

theorem fiveU_a {a b : G} : a ∈ fiveU a b := subset_closure (Set.mem_insert _ _)

theorem fiveU_b1 {a b : G} : b * a * b⁻¹ ∈ fiveU a b :=
  subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem fiveU_b2 {a b : G} : b ^ 2 * a * (b ^ 2)⁻¹ ∈ fiveU a b :=
  subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))

theorem fiveU_b3 {a b : G} : b ^ 3 * a * (b ^ 3)⁻¹ ∈ fiveU a b :=
  subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert _ _))))

theorem fiveU_b4 {a b : G} : b ^ 4 ∈ fiveU a b :=
  subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
    (Set.mem_insert_of_mem _ rfl))))

theorem conj_a_mem_fiveU {a b : G} {i : ℕ} (hi : i < 4) : (b ^ i)⁻¹ * a * b ^ i ∈ fiveU a b := by
  interval_cases i
  · simpa using (fiveU_a : a ∈ fiveU a b)
  · have e : (b ^ 1)⁻¹ * a * b ^ 1 = (b ^ 4)⁻¹ * (b ^ 3 * a * (b ^ 3)⁻¹) * b ^ 4 := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem fiveU_b4) fiveU_b3) fiveU_b4
  · have e : (b ^ 2)⁻¹ * a * b ^ 2 = (b ^ 4)⁻¹ * (b ^ 2 * a * (b ^ 2)⁻¹) * b ^ 4 := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem fiveU_b4) fiveU_b2) fiveU_b4
  · have e : (b ^ 3)⁻¹ * a * b ^ 3 = (b ^ 4)⁻¹ * (b * a * b⁻¹) * b ^ 4 := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem fiveU_b4) fiveU_b1) fiveU_b4

namespace FiveMRel

variable {x : G} {v : Fin 4 → G} {ω : Fin 4 → Fin 4 → ZMod 5} {a b : G}
  {Ab Bb : Matrix (Fin 4) (Fin 4) (ZMod 5)} {αc βc : Fin 4 → ZMod 5}
  (h : FiveMRel x v ω a b Ab Bb αc βc)
include h

theorem ax' : a * x = x * a := by rw [← h.ax]; exact (Commute.self_pow a 5).eq

omit h in
theorem a_mem : a ∈ closure ({a, b} : Set G) := subset_closure (Set.mem_insert _ _)

omit h in
theorem b_mem : b ∈ closure ({a, b} : Set G) := subset_closure (Set.mem_insert_of_mem _ rfl)

theorem x_memM : x ∈ closure ({a, b} : Set G) := by rw [← h.ax]; exact Subgroup.pow_mem _ a_mem 5

theorem fiveQ_le_M : fiveQ x v ≤ closure ({a, b} : Set G) := by
  rw [fiveQ, closure_le]
  rintro _ (rfl | ⟨i, rfl⟩)
  · exact h.x_memM
  · exact h.vM i

theorem finite_fiveQ : Finite (fiveQ x v) := Nat.finite_of_card_ne_zero (by
  rw [h.q.card_fiveQ]; norm_num)

theorem a_conj_mem {g : G} (hg : g ∈ fiveQ x v) : a * g * a⁻¹ ∈ fiveQ x v := by
  have hle : fiveQ x v ≤ (fiveQ x v).comap (MulAut.conj a).toMonoidHom := by
    rw [fiveQ, closure_le]
    intro y hy
    rcases hy with hy | ⟨i, rfl⟩
    · rw [hy]
      change a * x * a⁻¹ ∈ fiveQ x v
      rw [h.ax', mul_inv_cancel_right]
      exact FiveQRel.x_mem
    · change a * v i * a⁻¹ ∈ fiveQ x v
      rw [h.av i, mul_inv_cancel_right]
      exact FiveQRel.nf_mem _ _
  exact hle hg

theorem b_conj_mem {g : G} (hg : g ∈ fiveQ x v) : b * g * b⁻¹ ∈ fiveQ x v := by
  have hle : fiveQ x v ≤ (fiveQ x v).comap (MulAut.conj b).toMonoidHom := by
    rw [fiveQ, closure_le]
    intro y hy
    rcases hy with hy | ⟨i, rfl⟩
    · rw [hy]
      change b * x * b⁻¹ ∈ fiveQ x v
      rw [h.bx, mul_inv_cancel_right]
      exact Subgroup.pow_mem _ FiveQRel.x_mem 2
    · change b * v i * b⁻¹ ∈ fiveQ x v
      rw [h.bv i, mul_inv_cancel_right]
      exact FiveQRel.nf_mem _ _
  exact hle hg

theorem M_le_normalizer : closure ({a, b} : Set G) ≤ normalizer (fiveQ x v : Set G) := by
  have := h.finite_fiveQ
  rw [closure_le]
  rintro _ (rfl | rfl)
  · exact mem_normalizer_of_conj_le fun _ hg => h.a_conj_mem hg
  · exact mem_normalizer_of_conj_le fun _ hg => h.b_conj_mem hg

theorem conj_mem {g : G} (hg : g ∈ closure ({a, b} : Set G)) {q : G} (hq : q ∈ fiveQ x v) :
    g * q * g⁻¹ ∈ fiveQ x v :=
  (mem_normalizer_iff.1 (h.M_le_normalizer hg) q).1 hq

theorem fiveQ_normal : ((fiveQ x v).subgroupOf (closure ({a, b} : Set G))).Normal := by
  constructor
  intro n hn g
  rw [mem_subgroupOf] at hn ⊢
  exact h.conj_mem g.2 hn

@[expose] def conjQ (g : closure ({a, b} : Set G)) (q : fiveQ x v) : fiveQ x v :=
  ⟨g * q * (g : G)⁻¹, h.conj_mem g.2 q.2⟩

theorem conjQ_mul (g : closure ({a, b} : Set G)) (q q' : fiveQ x v) :
    h.conjQ g (q * q') = h.conjQ g q * h.conjQ g q' := by
  apply Subtype.ext
  simp only [conjQ, Subgroup.coe_mul]
  group

theorem coord_conj_x (g : closure ({a, b} : Set G)) :
    h.q.coord (h.conjQ g ⟨x, FiveQRel.x_mem⟩) = 0 := by
  rw [h.q.coord_eq_zero_iff]
  have hc : (⟨x, FiveQRel.x_mem⟩ : fiveQ x v) ∈ center (fiveQ x v) := (h.q.mem_center_iff _).2
    (mem_zpowers x)
  have : h.conjQ g ⟨x, FiveQRel.x_mem⟩ ∈ center (fiveQ x v) := by
    rw [Subgroup.mem_center_iff]
    intro k
    obtain ⟨k', hk'⟩ : ∃ k' : fiveQ x v, h.conjQ g k' = k := by
      refine ⟨⟨(g : G)⁻¹ * k * g, ?_⟩, ?_⟩
      · have := h.conj_mem (inv_mem g.2) k.2
        simpa using this
      · apply Subtype.ext
        simp only [conjQ]
        group
    rw [← hk', ← h.conjQ_mul, ← h.conjQ_mul, (Subgroup.mem_center_iff.1 hc) k']
  exact (h.q.mem_center_iff _).1 this

@[expose] def rhoMat (g : closure ({a, b} : Set G)) : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  Matrix.of fun j i => h.q.coord (h.conjQ g ⟨v i, FiveQRel.v_mem i⟩) j

theorem coord_pow (q : fiveQ x v) (n : ℕ) : h.q.coord (q ^ n) = n • h.q.coord q := by
  induction n with
  | zero =>
    have : (1 : fiveQ x v) = ⟨fiveNF x v 0 0, FiveQRel.nf_mem 0 0⟩ :=
      Subtype.ext FiveQRel.nf_zero.symm
    rw [pow_zero, zero_smul, this, h.q.coord_nf]
  | succ n ih => rw [pow_succ, h.q.coord_mul, ih, succ_nsmul]

theorem conjQ_pow (g : closure ({a, b} : Set G)) (q : fiveQ x v) (n : ℕ) :
    h.conjQ g (q ^ n) = h.conjQ g q ^ n := by
  induction n with
  | zero =>
    apply Subtype.ext
    simp [conjQ]
  | succ n ih => rw [pow_succ, h.conjQ_mul, ih, pow_succ]

theorem coord_conjQ (g : closure ({a, b} : Set G)) (q : fiveQ x v) :
    h.q.coord (h.conjQ g q) = h.rhoMat g *ᵥ h.q.coord q := by
  have hq := h.q.eq_nf q
  set c := (h.q.nfEquiv.symm q).1
  set e := h.q.coord q
  have hqe : q = ⟨v 3, FiveQRel.v_mem 3⟩ ^ (e 3).val * ⟨v 2, FiveQRel.v_mem 2⟩ ^ (e 2).val *
      ⟨v 1, FiveQRel.v_mem 1⟩ ^ (e 1).val * ⟨v 0, FiveQRel.v_mem 0⟩ ^ (e 0).val *
        ⟨x, FiveQRel.x_mem⟩ ^ c.val :=
    Subtype.ext (by rw [hq]; rfl)
  rw [hqe, h.conjQ_mul, h.conjQ_mul, h.conjQ_mul, h.conjQ_mul, h.conjQ_pow, h.conjQ_pow,
    h.conjQ_pow, h.conjQ_pow, h.conjQ_pow, h.q.coord_mul, h.q.coord_mul, h.q.coord_mul,
    h.q.coord_mul, h.coord_pow, h.coord_pow, h.coord_pow, h.coord_pow, h.coord_pow,
    h.coord_conj_x, smul_zero, add_zero]
  funext j
  simp only [Pi.add_apply, Pi.smul_apply]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, rhoMat, Matrix.of_apply, nsmul_eq_mul,
    ZMod.natCast_zmod_val]
  ring

theorem rhoMat_mul (g g' : closure ({a, b} : Set G)) :
    h.rhoMat (g * g') = h.rhoMat g * h.rhoMat g' := by
  ext j i
  have e : h.conjQ (g * g') ⟨v i, FiveQRel.v_mem i⟩ =
      h.conjQ g (h.conjQ g' ⟨v i, FiveQRel.v_mem i⟩) := by
    apply Subtype.ext
    simp only [conjQ, Subgroup.coe_mul]
    group
  simp only [rhoMat, Matrix.of_apply]
  rw [e, h.coord_conjQ]
  simp only [rhoMat, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.of_apply]

theorem rhoMat_one : h.rhoMat 1 = 1 := by
  ext j i
  simp only [rhoMat, Matrix.of_apply]
  have : h.conjQ 1 ⟨v i, FiveQRel.v_mem i⟩ =
      ⟨fiveNF x v 0 (Pi.single i 1), FiveQRel.nf_mem _ _⟩ := by
    apply Subtype.ext
    simp only [conjQ, OneMemClass.coe_one, one_mul, inv_one, mul_one]
    unfold fiveNF
    match i with
    | 0 => simp [zmod5_val_one]
    | 1 => simp [zmod5_val_one]
    | 2 => simp [zmod5_val_one]
    | 3 => simp [zmod5_val_one]
  rw [this, h.q.coord_nf, Matrix.one_apply, Pi.single_apply]

@[expose] def rho : closure ({a, b} : Set G) →* GL (Fin 4) (ZMod 5) :=
  MonoidHom.toHomUnits
    { toFun := h.rhoMat
      map_one' := h.rhoMat_one
      map_mul' := h.rhoMat_mul }

theorem rho_val (g : closure ({a, b} : Set G)) : (h.rho g : Matrix (Fin 4) (Fin 4) (ZMod 5)) =
    h.rhoMat g := rfl

theorem coord_conj_rho (g : closure ({a, b} : Set G)) (q : fiveQ x v) :
    h.q.coord (h.conjQ g q) = (h.rho g : Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ h.q.coord q :=
  h.coord_conjQ g q

theorem rhoMat_a : h.rhoMat ⟨a, a_mem⟩ = Ab := by
  ext j i
  have : h.conjQ ⟨a, a_mem⟩ ⟨v i, FiveQRel.v_mem i⟩ =
      ⟨fiveNF x v (αc i) (fun j => Ab j i), FiveQRel.nf_mem _ _⟩ :=
    Subtype.ext (by simp only [conjQ]; rw [h.av i, mul_inv_cancel_right])
  simp only [rhoMat, Matrix.of_apply, this, h.q.coord_nf]

theorem rhoMat_b : h.rhoMat ⟨b, b_mem⟩ = Bb := by
  ext j i
  have : h.conjQ ⟨b, b_mem⟩ ⟨v i, FiveQRel.v_mem i⟩ =
      ⟨fiveNF x v (βc i) (fun j => Bb j i), FiveQRel.nf_mem _ _⟩ :=
    Subtype.ext (by simp only [conjQ]; rw [h.bv i, mul_inv_cancel_right])
  simp only [rhoMat, Matrix.of_apply, this, h.q.coord_nf]

theorem coord_one : h.q.coord 1 = 0 := by
  have : (1 : fiveQ x v) = ⟨fiveNF x v 0 0, FiveQRel.nf_mem 0 0⟩ :=
    Subtype.ext FiveQRel.nf_zero.symm
  rw [this, h.q.coord_nf]

theorem coord_inv (p : fiveQ x v) : h.q.coord p⁻¹ = -h.q.coord p := by
  have e := h.q.coord_mul p p⁻¹
  rw [mul_inv_cancel, h.coord_one] at e
  exact eq_neg_of_add_eq_zero_right e.symm

theorem coord_v (i : Fin 4) : h.q.coord ⟨v i, FiveQRel.v_mem i⟩ = Pi.single i 1 := by
  have : (⟨v i, FiveQRel.v_mem i⟩ : fiveQ x v) =
      ⟨fiveNF x v 0 (Pi.single i 1), FiveQRel.nf_mem _ _⟩ := by
    apply Subtype.ext
    unfold fiveNF
    match i with
    | 0 => simp [zmod5_val_one]
    | 1 => simp [zmod5_val_one]
    | 2 => simp [zmod5_val_one]
    | 3 => simp [zmod5_val_one]
  rw [this, h.q.coord_nf]

theorem rhoMat_of_mem_Q (g : closure ({a, b} : Set G)) (hg : (g : G) ∈ fiveQ x v) :
    h.rhoMat g = 1 := by
  ext j i
  simp only [rhoMat, Matrix.of_apply]
  have e : h.conjQ g ⟨v i, FiveQRel.v_mem i⟩ = ⟨g, hg⟩ * ⟨v i, FiveQRel.v_mem i⟩ * ⟨g, hg⟩⁻¹ := rfl
  rw [e, h.q.coord_mul, h.q.coord_mul, h.coord_inv, h.coord_v, Matrix.one_apply]
  simp only [Pi.add_apply, Pi.neg_apply, Pi.single_apply]
  ring

theorem rho_of_mem_Q (g : closure ({a, b} : Set G)) (hg : (g : G) ∈ fiveQ x v) :
    h.rho g = 1 := Units.ext (h.rhoMat_of_mem_Q g hg)

variable {n : ℕ} {par : ℕ → ℕ} {gen : ℕ → Bool} {t : ℕ → G}
  {tb : ℕ → Matrix (Fin 4) (Fin 4) (ZMod 5)} {next : ℕ → Bool → ℕ}
  {qc : ℕ → Bool → ZMod 5 × (Fin 4 → ZMod 5)}

omit h in
theorem cert_t_mem (hc : CosetCert x v a b Ab Bb n par gen t tb next qc) :
    ∀ k < n, t k ∈ closure ({a, b} : Set G) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [hc.t_zero]; exact one_mem _
    · rw [hc.t_succ k hpos hk]
      refine mul_mem ?_ (ih _ (hc.par_lt k hpos hk) ((hc.par_lt k hpos hk).trans hk))
      split_ifs
      · exact b_mem
      · exact a_mem

theorem cert_rho_t (hc : CosetCert x v a b Ab Bb n par gen t tb next qc) :
    ∀ k (hk : k < n),
      (h.rho ⟨t k, cert_t_mem hc k hk⟩ : Matrix (Fin 4) (Fin 4) (ZMod 5)) = tb k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · have : (⟨t 0, cert_t_mem hc 0 hk⟩ : closure ({a, b} : Set G)) = 1 :=
        Subtype.ext hc.t_zero
      rw [this, map_one, hc.tb_zero]; rfl
    · have hp := hc.par_lt k hpos hk
      have e : (⟨t k, cert_t_mem hc k hk⟩ : closure ({a, b} : Set G)) =
          (if gen k then ⟨b, b_mem⟩ else ⟨a, a_mem⟩) *
            ⟨t (par k), cert_t_mem hc _ (hp.trans hk)⟩ := by
        apply Subtype.ext
        show t k = _
        rw [hc.t_succ k hpos hk]
        split_ifs <;> rfl
      rw [e, map_mul, Units.val_mul, ih _ hp (hp.trans hk), hc.tb_succ k hpos hk]
      split_ifs
      · rw [rho_val, h.rhoMat_b]
      · rw [rho_val, h.rhoMat_a]

@[expose] def cosetSet (t : ℕ → G) (n : ℕ) : Set G := {g | ∃ k < n, ∃ q ∈ fiveQ x v, g = t k * q}

omit h in
theorem cert_mul_mem_cosetSet (hc : CosetCert x v a b Ab Bb n par gen t tb next qc) (s : Bool)
    {g : G}
    (hg : g ∈ cosetSet (x := x) (v := v) t n) :
    (if s then b else a) * g ∈ cosetSet (x := x) (v := v) t n := by
  obtain ⟨k, hk, q, hq, rfl⟩ := hg
  refine ⟨next k s, hc.next_lt k s hk, fiveNF x v (qc k s).1 (qc k s).2 * q,
    mul_mem (FiveQRel.nf_mem _ _) hq, ?_⟩
  rw [← mul_assoc, hc.rel k s hk, mul_assoc]

omit h in
theorem cert_pow_mul_mem (hc : CosetCert x v a b Ab Bb n par gen t tb next qc) (s : Bool) (m : ℕ)
    {g : G} (hg : g ∈ cosetSet (x := x) (v := v) t n) :
    (if s then b else a) ^ m * g ∈ cosetSet (x := x) (v := v) t n := by
  induction m with
  | zero => rwa [pow_zero, one_mul]
  | succ m ih => rw [pow_succ', mul_assoc]; exact cert_mul_mem_cosetSet hc s ih

theorem cert_M_eq (hc : CosetCert x v a b Ab Bb n par gen t tb next qc) :
    (closure ({a, b} : Set G) : Set G) = cosetSet (x := x) (v := v) t n := by
  apply Set.Subset.antisymm
  · intro g hg
    have h1 : (1 : G) ∈ cosetSet (x := x) (v := v) t n :=
      ⟨0, hc.pos, 1, one_mem _, by rw [hc.t_zero, one_mul]⟩
    induction hg using Subgroup.closure_induction_left with
    | one => exact h1
    | mul_left s hs y _ ih =>
      rcases hs with hs | hs
      · rw [hs]
        simpa using cert_mul_mem_cosetSet hc false ih
      · rw [Set.mem_singleton_iff.1 hs]
        simpa using cert_mul_mem_cosetSet hc true ih
    | inv_mul_cancel s hs y _ ih =>
      rcases hs with hs | hs
      · rw [hs]
        have : a⁻¹ = a ^ 24 := by
          rw [inv_eq_iff_mul_eq_one, ← pow_succ', h.a25]
        rw [this]
        simpa using cert_pow_mul_mem hc false 24 ih
      · rw [Set.mem_singleton_iff.1 hs]
        have : b⁻¹ = b ^ 7 := by
          rw [inv_eq_iff_mul_eq_one, ← pow_succ', h.b8]
        rw [this]
        simpa using cert_pow_mul_mem hc true 7 ih
  · rintro _ ⟨k, hk, q, hq, rfl⟩
    exact mul_mem (cert_t_mem hc k hk) (h.fiveQ_le_M hq)

theorem cert_t_inj (hc : CosetCert x v a b Ab Bb n par gen t tb next qc) {k l : ℕ} (hk : k < n)
    (hl : l < n) {q q' : G} (hq : q ∈ fiveQ x v) (hq' : q' ∈ fiveQ x v)
    (he : t k * q = t l * q') : k = l ∧ q = q' := by
  have hkl : k = l := by
    apply hc.tb_inj k l hk hl
    rw [← h.cert_rho_t hc k hk, ← h.cert_rho_t hc l hl]
    have e : (⟨t k, cert_t_mem hc k hk⟩ : closure ({a, b} : Set G)) * ⟨q, h.fiveQ_le_M hq⟩ =
        ⟨t l, cert_t_mem hc l hl⟩ * ⟨q', h.fiveQ_le_M hq'⟩ := Subtype.ext he
    have := congrArg h.rho e
    rw [map_mul, map_mul, h.rho_of_mem_Q ⟨q, h.fiveQ_le_M hq⟩ hq,
      h.rho_of_mem_Q ⟨q', h.fiveQ_le_M hq'⟩ hq', mul_one, mul_one] at this
    rw [this]
  subst hkl
  exact ⟨rfl, mul_left_cancel he⟩

theorem cert_card_M (hc : CosetCert x v a b Ab Bb n par gen t tb next qc) :
    Nat.card (closure ({a, b} : Set G)) = n * 3125 := by
  let f : Fin n × fiveQ x v → closure ({a, b} : Set G) := fun p =>
    ⟨t p.1 * p.2, mul_mem (cert_t_mem hc p.1 p.1.2) (h.fiveQ_le_M p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨k, q⟩ ⟨l, q'⟩ e
      have := h.cert_t_inj hc k.2 l.2 q.2 q'.2 (congrArg Subtype.val e)
      exact Prod.ext (Fin.ext this.1) (Subtype.ext this.2)
    · rintro ⟨g, hg⟩
      have : g ∈ cosetSet (x := x) (v := v) t n := by rw [← h.cert_M_eq hc]; exact hg
      obtain ⟨k, hk, q, hq, rfl⟩ := this
      exact ⟨(⟨k, hk⟩, ⟨q, hq⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_fin, h.q.card_fiveQ]

theorem cert_rho_ker (hc : CosetCert x v a b Ab Bb n par gen t tb next qc) :
    h.rho.ker = (fiveQ x v).subgroupOf (closure ({a, b} : Set G)) := by
  ext ⟨g, hg⟩
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h1
    have : g ∈ cosetSet (x := x) (v := v) t n := by rw [← h.cert_M_eq hc]; exact hg
    obtain ⟨k, hk, q, hq, rfl⟩ := this
    have e : (⟨t k * q, hg⟩ : closure ({a, b} : Set G)) =
        ⟨t k, cert_t_mem hc k hk⟩ * ⟨q, h.fiveQ_le_M hq⟩ := rfl
    rw [e, map_mul, h.rho_of_mem_Q ⟨q, h.fiveQ_le_M hq⟩ hq, mul_one] at h1
    have h0 := congrArg (fun u : GL (Fin 4) (ZMod 5) => (u : Matrix (Fin 4) (Fin 4) (ZMod 5))) h1
    simp only [Units.val_one] at h0
    rw [h.cert_rho_t hc k hk, ← hc.tb_zero] at h0
    have hk0 := hc.tb_inj k 0 hk hc.pos h0
    subst hk0
    simpa [hc.t_zero] using hq
  · intro hq
    exact h.rho_of_mem_Q _ hq

theorem cert_card_rho_range (hc : CosetCert x v a b Ab Bb n par gen t tb next qc) :
    Nat.card h.rho.range = n := by
  let f : Fin n → h.rho.range := fun k => ⟨h.rho ⟨t k, cert_t_mem hc k k.2⟩, ⟨_, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro k l e
      have := congrArg (fun u : h.rho.range => ((u : GL (Fin 4) (ZMod 5)) :
        Matrix (Fin 4) (Fin 4) (ZMod 5))) e
      simp only [f] at this
      rw [h.cert_rho_t hc k k.2, h.cert_rho_t hc l l.2] at this
      exact Fin.ext (hc.tb_inj k l k.2 l.2 this)
    · rintro ⟨_, ⟨g, rfl⟩⟩
      have : (g : G) ∈ cosetSet (x := x) (v := v) t n := by rw [← h.cert_M_eq hc]; exact g.2
      obtain ⟨k, hk, q, hq, hgq⟩ := this
      refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
      have e : g = ⟨t k, cert_t_mem hc k hk⟩ * ⟨q, h.fiveQ_le_M hq⟩ := Subtype.ext hgq
      simp only [f]
      rw [e, map_mul, h.rho_of_mem_Q ⟨q, h.fiveQ_le_M hq⟩ hq, mul_one]
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_fin]

theorem cert_centralizer_Q (hc : CosetCert x v a b Ab Bb n par gen t tb next qc) :
    centralizer (fiveQ x v : Set G) ⊓ closure ({a, b} : Set G) = zpowers x := by
  apply le_antisymm
  · rintro g ⟨hgc, hgM⟩
    have hρ : h.rho ⟨g, hgM⟩ = 1 := by
      apply Units.ext
      ext j i
      rw [rho_val]
      simp only [rhoMat, Matrix.of_apply, Units.val_one]
      have e : h.conjQ ⟨g, hgM⟩ ⟨v i, FiveQRel.v_mem i⟩ = ⟨v i, FiveQRel.v_mem i⟩ := by
        apply Subtype.ext
        simp only [conjQ]
        rw [(mem_centralizer_iff.1 hgc (v i) (FiveQRel.v_mem i)).symm, mul_inv_cancel_right]
      rw [e, h.coord_v, Matrix.one_apply, Pi.single_apply]
    have hgQ : g ∈ fiveQ x v := by
      have hmem : (⟨g, hgM⟩ : closure ({a, b} : Set G)) ∈ h.rho.ker := hρ
      rw [h.cert_rho_ker hc] at hmem
      exact mem_subgroupOf.1 hmem
    rw [← h.q.center_map]
    refine ⟨⟨g, hgQ⟩, Subgroup.mem_center_iff.2 fun k => Subtype.ext ?_, rfl⟩
    exact (mem_centralizer_iff.1 hgc k k.2)
  · rw [zpowers_le]
    refine ⟨mem_centralizer_iff.2 fun q hq => ?_, h.x_memM⟩
    exact (h.q.x_comm hq).eq.symm

omit h in
theorem b_pow_mem (i : ℕ) : b ^ i ∈ closure ({a, b} : Set G) := Subgroup.pow_mem _ b_mem i

theorem conj_x_mem {g : G} (hg : g ∈ closure ({a, b} : Set G)) : g * x * g⁻¹ ∈ zpowers x := by
  have := h.coord_conj_x ⟨g, hg⟩
  rw [h.q.coord_eq_zero_iff] at this
  exact this

omit h in
theorem comm_zpowers_x {c : G} (hc : c * x = x * c) {z : G} (hz : z ∈ zpowers x) :
    c * z = z * c := by
  obtain ⟨k, rfl⟩ := hz
  exact ((Commute.zpow_right (show Commute c x from hc) k)).eq

theorem bpow_x (m : ℕ) : b ^ m * x = x ^ (2 ^ m) * b ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : SemiconjBy (b ^ m) x (x ^ (2 ^ m)) := ih
    have h3 : SemiconjBy (b ^ m) (x ^ 2) ((x ^ (2 ^ m)) ^ 2) := h1.pow_right 2
    have h4 : SemiconjBy (b ^ m * b) x ((x ^ (2 ^ m)) ^ 2) := h3.mul_left h.bx
    rw [← pow_succ, ← pow_mul, ← pow_succ] at h4
    exact h4

theorem b4_comm : b ^ 4 * x = x * b ^ 4 := by
  rw [h.bpow_x 4]
  congr 1
  rw [show (2 : ℕ) ^ 4 = 5 * 3 + 1 by norm_num, pow_succ, pow_mul, h.q.x5, one_pow, one_mul]

theorem bpow_comm_x {d : ℕ} (hd : d < 4) (hc : b ^ d * x = x * b ^ d) : d = 0 := by
  rw [h.bpow_x d] at hc
  have hx : x ^ (2 ^ d) = x := mul_right_cancel hc
  have h1 : x ^ (2 ^ d - 1) = 1 := by
    have : x ^ (2 ^ d - 1) * x = 1 * x := by
      rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, hx, one_mul]
    exact mul_right_cancel this
  have h5 := orderOf_dvd_of_pow_eq_one h1
  rw [h.q.orderOf_x] at h5
  interval_cases d
  · rfl
  all_goals norm_num at h5

theorem fiveU_le_centralizer : fiveU a b ≤ centralizer {x} ⊓ closure ({a, b} : Set G) := by
  rw [fiveU, closure_le]
  have hconj : ∀ i : ℕ, b ^ i * a * (b ^ i)⁻¹ ∈ centralizer {x} ⊓ closure ({a, b} : Set G) := by
    intro i
    refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, mul_mem (mul_mem (b_pow_mem i) a_mem)
      (inv_mem (b_pow_mem i))⟩
    have hz : (b ^ i)⁻¹ * x * ((b ^ i)⁻¹)⁻¹ ∈ zpowers x := h.conj_x_mem (inv_mem (b_pow_mem i))
    rw [inv_inv] at hz
    have hc := comm_zpowers_x h.ax' hz
    calc b ^ i * a * (b ^ i)⁻¹ * x = b ^ i * (a * ((b ^ i)⁻¹ * x * b ^ i)) * (b ^ i)⁻¹ := by
          group
      _ = b ^ i * (((b ^ i)⁻¹ * x * b ^ i) * a) * (b ^ i)⁻¹ := by rw [hc]
      _ = x * (b ^ i * a * (b ^ i)⁻¹) := by group
  rintro _ (rfl | rfl | rfl | rfl | rfl)
  · simpa using hconj 0
  · simpa using hconj 1
  · exact hconj 2
  · exact hconj 3
  · exact mem_inf.2 ⟨mem_centralizer_singleton_iff.2 h.b4_comm, b_pow_mem 4⟩

theorem fiveU_le_M : fiveU a b ≤ closure ({a, b} : Set G) :=
  h.fiveU_le_centralizer.trans inf_le_right

theorem mem_fiveU_cosets {g : G} (hg : g ∈ closure ({a, b} : Set G)) :
    ∃ i < 4, (b ^ i)⁻¹ * g ∈ fiveU a b := by
  have hA : ∀ y : G, (∃ i < 4, (b ^ i)⁻¹ * y ∈ fiveU a b) →
      ∃ i < 4, (b ^ i)⁻¹ * (a * y) ∈ fiveU a b := by
    rintro y ⟨i, hi, hy⟩
    refine ⟨i, hi, ?_⟩
    have e : (b ^ i)⁻¹ * (a * y) = ((b ^ i)⁻¹ * a * b ^ i) * ((b ^ i)⁻¹ * y) := by group
    rw [e]
    exact mul_mem (conj_a_mem_fiveU hi) hy
  have hB : ∀ y : G, (∃ i < 4, (b ^ i)⁻¹ * y ∈ fiveU a b) →
      ∃ i < 4, (b ^ i)⁻¹ * (b * y) ∈ fiveU a b := by
    rintro y ⟨i, hi, hy⟩
    by_cases h3 : i = 3
    · rw [h3] at hy
      refine ⟨0, by norm_num, ?_⟩
      have e : (b ^ 0)⁻¹ * (b * y) = b ^ 4 * ((b ^ 3)⁻¹ * y) := by group
      rw [e]
      exact mul_mem fiveU_b4 hy
    · refine ⟨i + 1, by omega, ?_⟩
      have e : (b ^ (i + 1))⁻¹ * (b * y) = (b ^ i)⁻¹ * y := by group
      rw [e]
      exact hy
  have hpow : ∀ s : G, (∀ y : G, (∃ i < 4, (b ^ i)⁻¹ * y ∈ fiveU a b) →
      ∃ i < 4, (b ^ i)⁻¹ * (s * y) ∈ fiveU a b) → ∀ m : ℕ, ∀ y : G,
      (∃ i < 4, (b ^ i)⁻¹ * y ∈ fiveU a b) → ∃ i < 4, (b ^ i)⁻¹ * (s ^ m * y) ∈ fiveU a b := by
    intro s hs m
    induction m with
    | zero => intro y hy; simpa using hy
    | succ m ih => intro y hy; rw [pow_succ', mul_assoc]; exact hs _ (ih y hy)
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨0, by norm_num, by rw [pow_zero, inv_one, one_mul]; exact one_mem _⟩
  | mul_left s hs y _ ih =>
    rcases hs with hs | hs
    · rw [hs]; exact hA _ ih
    · rw [Set.mem_singleton_iff.1 hs]; exact hB _ ih
  | inv_mul_cancel s hs y _ ih =>
    rcases hs with hs | hs
    · rw [hs, show a⁻¹ = a ^ 24 by rw [inv_eq_iff_mul_eq_one, ← pow_succ', h.a25]]
      exact hpow a hA 24 _ ih
    · rw [Set.mem_singleton_iff.1 hs, show b⁻¹ = b ^ 7 by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ', h.b8]]
      exact hpow b hB 7 _ ih

theorem card_M_le_fiveU [Finite (closure ({a, b} : Set G))] :
    Nat.card (closure ({a, b} : Set G)) ≤ 4 * Nat.card (fiveU a b) := by
  have : Finite (fiveU a b) := Finite.of_injective _ (inclusion_injective h.fiveU_le_M)
  let f : Fin 4 × fiveU a b → closure ({a, b} : Set G) := fun p =>
    ⟨b ^ (p.1 : ℕ) * p.2, mul_mem (b_pow_mem _) (h.fiveU_le_M p.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨i, hi, hu⟩ := h.mem_fiveU_cosets hg
    refine ⟨(⟨i, hi⟩, ⟨_, hu⟩), Subtype.ext ?_⟩
    show b ^ i * ((b ^ i)⁻¹ * g) = g
    rw [mul_inv_cancel_left]
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at this

theorem four_mul_card_C_le [Finite (closure ({a, b} : Set G))] :
    4 * Nat.card (centralizer {x} ⊓ closure ({a, b} : Set G) : Subgroup G) ≤
      Nat.card (closure ({a, b} : Set G)) := by
  let f : Fin 4 × (centralizer {x} ⊓ closure ({a, b} : Set G) : Subgroup G) →
      closure ({a, b} : Set G) := fun p =>
    ⟨b ^ (p.1 : ℕ) * p.2, mul_mem (b_pow_mem _) (mem_inf.1 p.2.2).2⟩
  have key : ∀ (i j : ℕ) (c c' : G), j ≤ i → i < 4 →
      c ∈ (centralizer {x} ⊓ closure ({a, b} : Set G) : Subgroup G) →
      c' ∈ (centralizer {x} ⊓ closure ({a, b} : Set G) : Subgroup G) →
      b ^ i * c = b ^ j * c' → i = j := by
    intro i j c c' hji hi hc hc' e
    have e2 : b ^ (i - j) = c' * c⁻¹ := by
      have hb : b ^ i = b ^ j * b ^ (i - j) := by rw [← pow_add, Nat.add_sub_cancel' hji]
      rw [hb, mul_assoc] at e
      rw [← mul_left_cancel e, mul_inv_cancel_right]
    have hmem : b ^ (i - j) ∈ centralizer {x} := by
      rw [e2]
      exact mul_mem (mem_inf.1 hc').1 (inv_mem (mem_inf.1 hc).1)
    have := h.bpow_comm_x (d := i - j) (by omega) (mem_centralizer_singleton_iff.1 hmem)
    omega
  have hf : Function.Injective f := by
    rintro ⟨i, c⟩ ⟨j, c'⟩ e
    have e' : b ^ (i : ℕ) * c = b ^ (j : ℕ) * c' := congrArg Subtype.val e
    have hij : (i : ℕ) = j := by
      rcases le_total (j : ℕ) i with hji | hij
      · exact key i j c c' hji i.2 c.2 c'.2 e'
      · exact (key j i c' c hij j.2 c'.2 c.2 e'.symm).symm
    have hi : i = j := Fin.ext hij
    subst hi
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel e'))
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at this

theorem centralizer_x_normal :
    ((centralizer {x} ⊓ closure ({a, b} : Set G) : Subgroup G).subgroupOf
      (closure ({a, b} : Set G))).Normal := by
  constructor
  intro c hc g
  rw [mem_subgroupOf] at hc ⊢
  obtain ⟨hcx, hcM⟩ := mem_inf.1 hc
  show (g : G) * c * (g : G)⁻¹ ∈ _
  refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, mul_mem (mul_mem g.2 hcM) (inv_mem g.2)⟩
  have hz : (g : G)⁻¹ * x * ((g : G)⁻¹)⁻¹ ∈ zpowers x := h.conj_x_mem (inv_mem g.2)
  rw [inv_inv] at hz
  have hcz := comm_zpowers_x (mem_centralizer_singleton_iff.1 hcx) hz
  calc (g : G) * c * (g : G)⁻¹ * x = g * (c * ((g : G)⁻¹ * x * g)) * (g : G)⁻¹ := by group
    _ = g * (((g : G)⁻¹ * x * g) * c) * (g : G)⁻¹ := by rw [hcz]
    _ = x * (g * c * (g : G)⁻¹) := by group

theorem fiveQ_le_centralizer_x : fiveQ x v ≤ centralizer {x} ⊓ closure ({a, b} : Set G) :=
  le_inf (fun _ hq => mem_centralizer_singleton_iff.2 (h.q.x_comm hq).eq.symm) h.fiveQ_le_M

theorem fiveQ_normal_of_le {K : Subgroup G} (hK : K ≤ closure ({a, b} : Set G)) :
    ((fiveQ x v).subgroupOf K).Normal := by
  constructor
  intro m hm g
  rw [mem_subgroupOf] at hm ⊢
  exact h.conj_mem (hK g.2) hm

theorem cert_finite_M (hc : CosetCert x v a b Ab Bb n par gen t tb next qc) :
    Finite (closure ({a, b} : Set G)) :=
  Nat.finite_of_card_ne_zero (by
    rw [h.cert_card_M hc]
    exact Nat.mul_ne_zero hc.pos.ne' (by norm_num))

theorem cert_fiveU (hc : CosetCert x v a b Ab Bb n par gen t tb next qc) :
    fiveU a b = centralizer {x} ⊓ closure ({a, b} : Set G) ∧
      Nat.card (closure ({a, b} : Set G)) = 4 * Nat.card (fiveU a b) := by
  have := h.cert_finite_M hc
  have : Finite (centralizer {x} ⊓ closure ({a, b} : Set G) : Subgroup G) :=
    Finite.of_injective _ (inclusion_injective (inf_le_right :
      centralizer {x} ⊓ closure ({a, b} : Set G) ≤ closure ({a, b} : Set G)))
  have h1 := h.card_M_le_fiveU
  have h2 := h.four_mul_card_C_le
  have h3 := Subgroup.card_le_of_le h.fiveU_le_centralizer
  have hUC : fiveU a b = centralizer {x} ⊓ closure ({a, b} : Set G) :=
    Subgroup.eq_of_le_of_card_ge h.fiveU_le_centralizer (by omega)
  exact ⟨hUC, by omega⟩

theorem cert_centralizer_Q_fiveU (hc : CosetCert x v a b Ab Bb n par gen t tb next qc) :
    centralizer (fiveQ x v : Set G) ⊓ fiveU a b = zpowers x := by
  apply le_antisymm
  · rw [← h.cert_centralizer_Q hc]
    exact inf_le_inf_left _ h.fiveU_le_M
  · refine le_inf ?_ ?_
    · rw [← h.cert_centralizer_Q hc]
      exact inf_le_left
    · rw [zpowers_le, (h.cert_fiveU hc).1]
      exact h.fiveQ_le_centralizer_x FiveQRel.x_mem

theorem conj_scalar {g : closure ({a, b} : Set G)} {r : ZMod 5}
    (hg : h.rhoMat g = r • (1 : Matrix (Fin 4) (Fin 4) (ZMod 5))) {q : G} (hq : q ∈ fiveQ x v) :
    ((g : G) * q * (g : G)⁻¹)⁻¹ * q ^ r.val ∈ zpowers x := by
  have hm : ((g : G) * q * (g : G)⁻¹)⁻¹ * q ^ r.val ∈ fiveQ x v :=
    mul_mem (inv_mem (h.conj_mem g.2 hq)) (Subgroup.pow_mem _ hq _)
  have e : (⟨_, hm⟩ : fiveQ x v) = (h.conjQ g ⟨q, hq⟩)⁻¹ * ⟨q, hq⟩ ^ r.val := rfl
  have h0 := (h.q.coord_eq_zero_iff ⟨_, hm⟩).1
  apply h0
  rw [e, h.q.coord_mul, h.coord_inv, h.coord_conjQ, h.coord_pow, hg]
  funext j
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, Pi.zero_apply, Matrix.smul_mulVec,
    Matrix.one_mulVec, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, ZMod.natCast_zmod_val,
    smul_eq_mul]
  ring

theorem cert_comm_mem_of_scalar (hc : CosetCert x v a b Ab Bb n par gen t tb next qc)
    {g : closure ({a, b} : Set G)} {r : ZMod 5}
    (hg : h.rhoMat g = r • (1 : Matrix (Fin 4) (Fin 4) (ZMod 5))) (k : closure ({a, b} : Set G)) :
    k⁻¹ * g⁻¹ * k * g ∈ (fiveQ x v).subgroupOf (closure ({a, b} : Set G)) := by
  rw [← h.cert_rho_ker hc, MonoidHom.mem_ker]
  have hcomm : h.rho g * h.rho k = h.rho k * h.rho g := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, rho_val, rho_val, hg, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc, mul_assoc, ← hcomm,
    inv_mul_cancel_left, inv_mul_cancel]

end FiveMRel

section Map

variable {H : Type*} [Group H] (f : G →* H)

theorem fiveNF_map (x : G) (v : Fin 4 → G) (c : ZMod 5) (e : Fin 4 → ZMod 5) :
    f (fiveNF x v c e) = fiveNF (f x) (f ∘ v) c e := by
  simp only [fiveNF, map_mul, map_pow, Function.comp_apply]

theorem map_closure_pair (a b : G) : (closure ({a, b} : Set G)).map f = closure {f a, f b} := by
  rw [MonoidHom.map_closure, Set.image_pair]

variable {f}

theorem FiveQRel.map (hf : Function.Injective f) {x : G} {v : Fin 4 → G}
    {ω : Fin 4 → Fin 4 → ZMod 5} (h : FiveQRel x v ω) : FiveQRel (f x) (f ∘ v) ω where
  x5 := by rw [← map_pow, h.x5, map_one]
  x1 := fun e => h.x1 (hf (by rw [e, map_one]))
  v5 := fun i => by rw [Function.comp_apply, ← map_pow, h.v5, map_one]
  xv := fun i => by rw [Function.comp_apply, ← map_mul, h.xv, map_mul]
  comm := fun i j => by
    rw [Function.comp_apply, Function.comp_apply, ← map_commutatorElement, h.comm, map_pow]
  nondeg := h.nondeg

theorem FiveMRel.map (hf : Function.Injective f) {x : G} {v : Fin 4 → G}
    {ω : Fin 4 → Fin 4 → ZMod 5} {a b : G} {Ab Bb : Matrix (Fin 4) (Fin 4) (ZMod 5)}
    {αc βc : Fin 4 → ZMod 5} (h : FiveMRel x v ω a b Ab Bb αc βc) :
    FiveMRel (f x) (f ∘ v) ω (f a) (f b) Ab Bb αc βc where
  q := h.q.map hf
  a25 := by rw [← map_pow, h.a25, map_one]
  ax := by rw [← map_pow, h.ax]
  b8 := by rw [← map_pow, h.b8, map_one]
  b4 := fun e => h.b4 (hf (by rw [map_pow, e, map_one]))
  bx := by rw [← map_mul, h.bx, map_mul, map_pow]
  av := fun i => by rw [Function.comp_apply, ← map_mul, h.av, map_mul, fiveNF_map]
  bv := fun i => by rw [Function.comp_apply, ← map_mul, h.bv, map_mul, fiveNF_map]
  vM := fun i => by
    rw [Function.comp_apply, ← map_closure_pair]
    exact mem_map_of_mem f (h.vM i)

theorem CosetCert.map {x : G} {v : Fin 4 → G} {a b : G} {Ab Bb : Matrix (Fin 4) (Fin 4) (ZMod 5)}
    {n : ℕ} {par : ℕ → ℕ} {gen : ℕ → Bool} {t : ℕ → G}
    {tb : ℕ → Matrix (Fin 4) (Fin 4) (ZMod 5)} {next : ℕ → Bool → ℕ}
    {qc : ℕ → Bool → ZMod 5 × (Fin 4 → ZMod 5)}
    (hc : CosetCert x v a b Ab Bb n par gen t tb next qc) :
    CosetCert (f x) (f ∘ v) (f a) (f b) Ab Bb n par gen (f ∘ t) tb next qc where
  pos := hc.pos
  par_lt := hc.par_lt
  t_zero := by rw [Function.comp_apply, hc.t_zero, map_one]
  t_succ := fun k hk hkn => by
    rw [Function.comp_apply, Function.comp_apply, hc.t_succ k hk hkn, map_mul, apply_ite f]
  tb_zero := hc.tb_zero
  tb_succ := hc.tb_succ
  tb_inj := hc.tb_inj
  next_lt := hc.next_lt
  rel := fun k s hk => by
    rw [Function.comp_apply, Function.comp_apply, ← apply_ite f, ← map_mul, hc.rel k s hk, map_mul,
      fiveNF_map]

end Map

end CFSG.RankThree.Native
