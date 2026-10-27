module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix

namespace NoTvAut

section Form

variable {p : ℕ} [Fact p.Prime] {n : Type*} [Fintype n] [DecidableEq n]

theorem eq_zero_of_forall_dotProduct_mulVec {S : Matrix n n (ZMod p)} (hdet : S.det ≠ 0)
    {x : n → ZMod p} (h : ∀ y, y ⬝ᵥ (S *ᵥ x) = 0) : x = 0 := by
  refine eq_zero_of_mulVec_eq_zero hdet (funext fun i => ?_)
  have h1 := h (Pi.single i 1)
  rwa [single_dotProduct, one_mul] at h1

omit [DecidableEq n] in
theorem dotProduct_mulVec_comm {S : Matrix n n (ZMod p)} (hS : Sᵀ = S) (x y : n → ZMod p) :
    x ⬝ᵥ (S *ᵥ y) = y ⬝ᵥ (S *ᵥ x) := by
  calc x ⬝ᵥ (S *ᵥ y) = (x ᵥ* S) ⬝ᵥ y := dotProduct_mulVec x S y
    _ = (Sᵀ *ᵥ x) ⬝ᵥ y := by rw [← vecMul_transpose, transpose_transpose]
    _ = y ⬝ᵥ (S *ᵥ x) := by rw [hS, dotProduct_comm]

omit [Fintype n] [DecidableEq n] in
theorem nsmul_prime_eq_zero (v : n → ZMod p) : p • v = 0 := by
  funext i
  simp [nsmul_eq_mul]

theorem false_of_isTransvection_similitude_nd (hp2 : p ≠ 2) {S : Matrix n n (ZMod p)}
    (hS : Sᵀ = S) (hnd : ∀ x : n → ZMod p, (∀ y, y ⬝ᵥ (S *ᵥ x) = 0) → x = 0)
    (t : (n → ZMod p) →+ (n → ZMod p)) (μ : ZMod p)
    (hB : ∀ x y, t x ⬝ᵥ (S *ᵥ t y) = μ * (x ⬝ᵥ (S *ᵥ y)))
    (hfix : Nat.card {x // t x = x} * p = Nat.card (n → ZMod p))
    (hN : ∀ x, t (t x - x) = t x - x) : False := by
  have hp : p.Prime := Fact.out
  set N : (n → ZMod p) →+ (n → ZMod p) :=
    AddMonoidHom.mk' (fun x => t x - x) (fun x y => by rw [map_add]; abel) with hNdef
  have hNx : ∀ x, N x = t x - x := fun x => rfl
  have htN : ∀ x, t (N x) = N x := fun x => hN x
  have hNN : ∀ x, N (N x) = 0 := fun x => by rw [hNx (N x), htN, sub_self]
  have ht : ∀ x, t x = x + N x := fun x => by rw [hNx]; abel
  have hit : ∀ k : ℕ, ∀ x, t^[k] x = x + k • N x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, map_add, map_nsmul, htN, ht x, succ_nsmul]
      abel
  have hitB : ∀ k : ℕ, ∀ x y, t^[k] x ⬝ᵥ (S *ᵥ t^[k] y) = μ ^ k * (x ⬝ᵥ (S *ᵥ y)) := by
    intro k
    induction k with
    | zero => intro x y; simp
    | succ k ih =>
      intro x y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hB, ih, pow_succ]
      ring
  obtain ⟨u, hu⟩ : ∃ u, N u ≠ 0 := by
    by_contra h
    push Not at h
    have h1 : Nat.card {x // t x = x} = Nat.card (n → ZMod p) :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun x => by rw [ht, h, add_zero])
    rw [h1] at hfix
    have h2 : 0 < Nat.card (n → ZMod p) := Nat.card_pos
    have h3 : Nat.card (n → ZMod p) * p = Nat.card (n → ZMod p) * 1 := by rw [hfix, mul_one]
    exact hp.one_lt.ne' (Nat.eq_of_mul_eq_mul_left h2 h3)
  set v := N u with hv
  have hμ : μ = 1 := by
    obtain ⟨y, hy⟩ : ∃ y, y ⬝ᵥ (S *ᵥ v) ≠ 0 := by
      by_contra h
      push Not at h
      exact hu (hnd v h)
    have h1 := hitB p y v
    rw [hit p y, hit p v, nsmul_prime_eq_zero, nsmul_prime_eq_zero, add_zero, add_zero,
      ZMod.pow_card] at h1
    have h2 : (1 - μ) * (y ⬝ᵥ (S *ᵥ v)) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact (sub_eq_zero.mp h3).symm
    · exact absurd h3 hy
  have hrange : ∀ y, ∃ c : ZMod p, N y = c • v := by
    have : Nonempty {x // t x = x} := ⟨⟨0, map_zero t⟩⟩
    have hker : Nat.card N.ker = Nat.card {x // t x = x} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => by
        rw [AddMonoidHom.mem_ker, hNx, sub_eq_zero])
    have hcard := AddSubgroup.card_ker_mul_card_range N
    rw [hker, ← hfix] at hcard
    have hpos : 0 < Nat.card {x // t x = x} := Nat.card_pos
    have hR : Nat.card N.range = p := Nat.eq_of_mul_eq_mul_left hpos hcard
    have hvR : AddSubgroup.zmultiples v ≤ N.range := by
      rw [AddSubgroup.zmultiples_le]
      exact ⟨u, rfl⟩
    have hZ : Nat.card (AddSubgroup.zmultiples v) = p := by
      rw [Nat.card_zmultiples]
      exact addOrderOf_eq_prime (nsmul_prime_eq_zero v) hu
    have heq : AddSubgroup.zmultiples v = N.range :=
      AddSubgroup.eq_of_le_of_card_ge hvR (by rw [hR, hZ])
    intro y
    have hy : N y ∈ AddSubgroup.zmultiples v := heq ▸ ⟨y, rfl⟩
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    exact ⟨(k : ZMod p), by rw [← hk]; funext i; simp [zsmul_eq_mul]⟩
  have hiso : ∀ x y, t x ⬝ᵥ (S *ᵥ t y) = x ⬝ᵥ (S *ᵥ y) := fun x y => by rw [hB, hμ, one_mul]
  have h0 : ∀ x y, x ⬝ᵥ (S *ᵥ N y) + N x ⬝ᵥ (S *ᵥ y) + N x ⬝ᵥ (S *ᵥ N y) = 0 := by
    intro x y
    have h1 := hiso x y
    rw [ht x, ht y, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct] at h1
    linear_combination h1
  have hNv : N v = 0 := hNN u
  have hvv : v ⬝ᵥ (S *ᵥ v) = 0 := by
    have h1 := h0 u v
    rw [hNv, mulVec_zero, dotProduct_zero, dotProduct_zero] at h1
    simpa using h1
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  have huv : u ⬝ᵥ (S *ᵥ v) = 0 := by
    have h1 := h0 u u
    rw [dotProduct_mulVec_comm hS v u, hvv] at h1
    have h3 : 2 * (u ⬝ᵥ (S *ᵥ v)) = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h3).resolve_left h2
  have hvy : ∀ y, v ⬝ᵥ (S *ᵥ y) = 0 := by
    intro y
    obtain ⟨c, hc⟩ := hrange y
    have h1 := h0 u y
    rw [hc, mulVec_smul, dotProduct_smul, dotProduct_smul, huv, hvv, smul_zero, ← hv] at h1
    simpa using h1
  exact hu (hnd v fun y => by rw [dotProduct_mulVec_comm hS y v]; exact hvy y)

theorem false_of_isTransvection_similitude (hp2 : p ≠ 2) {S : Matrix n n (ZMod p)}
    (hS : Sᵀ = S) (hdet : S.det ≠ 0) (t : (n → ZMod p) →+ (n → ZMod p)) (μ : ZMod p)
    (hB : ∀ x y, t x ⬝ᵥ (S *ᵥ t y) = μ * (x ⬝ᵥ (S *ᵥ y)))
    (hfix : Nat.card {x // t x = x} * p = Nat.card (n → ZMod p))
    (hN : ∀ x, t (t x - x) = t x - x) : False :=
  false_of_isTransvection_similitude_nd hp2 hS
    (fun _ h => eq_zero_of_forall_dotProduct_mulVec hdet h) t μ hB hfix hN

end Form

section Transv

variable {G : Type} [Group G] {p : ℕ}

theorem ggIsTransvection_pow_two (hp : p.Prime) (hp2 : p ≠ 2) {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) {φ : MulAut ↥Bs} (h : GGIsTransvection p φ) :
    GGIsTransvection p (φ ^ 2) := by
  obtain ⟨hcard, hfix⟩ := h
  have hpow : ∀ b : ↥Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hsq : ∀ b : ↥Bs, (φ ^ 2) b = b * (b⁻¹ * φ b) ^ 2 := by
    intro b
    have e1 : φ b = b * (b⁻¹ * φ b) := by rw [mul_inv_cancel_left]
    have e2 : (φ ^ 2) b = φ (φ b) := by rw [pow_two]; rfl
    rw [e2]
    conv_lhs => rw [e1]
    rw [map_mul, hfix b, pow_two]
    group
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
  have hone : ∀ c : ↥Bs, c ^ 2 = 1 → c = 1 := by
    intro c hc
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hc)
      (orderOf_dvd_of_pow_eq_one (hpow c))
  have hiff : ∀ b : ↥Bs, (φ ^ 2) b = b ↔ φ b = b := by
    intro b
    rw [hsq]
    constructor
    · intro h1
      have h2 : (b⁻¹ * φ b) ^ 2 = 1 := mul_eq_left.mp h1
      have h3 := hone _ h2
      rw [inv_mul_eq_one] at h3
      exact h3.symm
    · intro h1
      rw [h1, inv_mul_cancel, one_pow, mul_one]
  refine ⟨?_, fun b => ?_⟩
  · rw [← hcard]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight hiff)
  · have e1 : b⁻¹ * (φ ^ 2) b = (b⁻¹ * φ b) ^ 2 := by rw [hsq, inv_mul_cancel_left]
    rw [e1, map_pow]
    have e2 : (φ ^ 2) (b⁻¹ * φ b) = φ (φ (b⁻¹ * φ b)) := by rw [pow_two]; rfl
    rw [e2, hfix, hfix]

theorem transvection_coords {r : ℕ} {Bs : Subgroup G} {ι : Multiplicative (Fin r → ZMod p) →* G}
    (hι : Function.Injective ι) (hιB : ι.range = Bs) {φ : MulAut ↥Bs}
    {t : (Fin r → ZMod p) → (Fin r → ZMod p)}
    (ht : ∀ (b : ↥Bs) (s : Fin r → ZMod p), (b : G) = ι (Multiplicative.ofAdd s) →
      ((φ b : ↥Bs) : G) = ι (Multiplicative.ofAdd (t s)))
    (h : GGIsTransvection p φ) :
    Nat.card {s // t s = s} * p = Nat.card (Fin r → ZMod p) ∧ ∀ s, t (t s - s) = t s - s := by
  have hmem : ∀ s : Fin r → ZMod p, ι (Multiplicative.ofAdd s) ∈ Bs := fun s => hιB ▸ ⟨_, rfl⟩
  set θ : (Fin r → ZMod p) → ↥Bs := fun s => ⟨ι (Multiplicative.ofAdd s), hmem s⟩ with hθ
  have hθinj : Function.Injective θ := fun s s' h' =>
    Multiplicative.ofAdd.injective (hι (congrArg Subtype.val h'))
  have hθsurj : Function.Surjective θ := by
    rintro ⟨b, hb⟩
    rw [← hιB] at hb
    obtain ⟨x, rfl⟩ := hb
    exact ⟨Multiplicative.toAdd x, rfl⟩
  have hφθ : ∀ s, φ (θ s) = θ (t s) := fun s => Subtype.ext (ht (θ s) s rfl)
  have hθsub : ∀ s s', θ (s' - s) = (θ s)⁻¹ * θ s' := fun s s' => by
    refine Subtype.ext ?_
    simp only [hθ, Subgroup.coe_mul, Subgroup.coe_inv, sub_eq_neg_add, ofAdd_add, ofAdd_neg,
      map_mul, map_inv]
  set e := Equiv.ofBijective θ ⟨hθinj, hθsurj⟩ with he
  refine ⟨?_, fun s => ?_⟩
  · have h1 : Nat.card {s // t s = s} = Nat.card {b : ↥Bs // φ b = b} :=
      Nat.card_congr (e.subtypeEquiv fun s => by
        show t s = s ↔ φ (θ s) = θ s
        rw [hφθ, hθinj.eq_iff])
    have h2 : Nat.card (Fin r → ZMod p) = Nat.card ↥Bs := Nat.card_congr e
    rw [h1, h2]
    exact h.1
  · have h1 := h.2 (θ s)
    rw [hφθ, ← hθsub, hφθ] at h1
    exact hθinj h1

end Transv

section Weyl

variable {τ : Tag} {p : ℕ}

theorem redMod_add (v v' : Fin τ.rank → ℤ) :
    TableBExc.redMod τ p (v + v') = TableBExc.redMod τ p v + TableBExc.redMod τ p v' := by
  funext i
  simp [TableBExc.redMod]

variable [NeZero p]

theorem torusAct_add (w : WeylGroup τ) (s s' : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p w (s + s') =
      TableBExc.torusAct τ p w s + TableBExc.torusAct τ p w s' := by
  rw [TableBExc.torusAct, TableBExc.torusAct, TableBExc.torusAct, ← redMod_add, ← smul_add]
  exact TableBExc.redMod_smul_eq w (by
    rw [redMod_add, TableBExc.redMod_liftMod, TableBExc.redMod_liftMod, TableBExc.redMod_liftMod])

variable (τ p) in
@[expose] noncomputable def torusActHom (w : WeylGroup τ) :
    (Fin τ.rank → ZMod p) →+ (Fin τ.rank → ZMod p) :=
  AddMonoidHom.mk' (TableBExc.torusAct τ p w) (torusAct_add w)

theorem torusActHom_apply (w : WeylGroup τ) (s : Fin τ.rank → ZMod p) :
    torusActHom τ p w s = TableBExc.torusAct τ p w s :=
  rfl

variable (τ p) in
@[expose] def cartanMod : Matrix (Fin τ.rank) (Fin τ.rank) (ZMod p) :=
  τ.symmetrizedCartan.map (Int.castRingHom (ZMod p))

omit [NeZero p] in
theorem det_cartanMod : (cartanMod τ p).det = ((τ.symmetrizedCartan.det : ℤ) : ZMod p) := by
  rw [cartanMod, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

omit [NeZero p] in
theorem redMod_form (u u' : Fin τ.rank → ℤ) :
    TableBExc.redMod τ p u ⬝ᵥ (cartanMod τ p *ᵥ TableBExc.redMod τ p u') =
      ((u ⬝ᵥ (τ.symmetrizedCartan *ᵥ u') : ℤ) : ZMod p) := by
  simp only [dotProduct, mulVec, cartanMod, TableBExc.redMod, Matrix.map_apply,
    Int.coe_castRingHom]
  push_cast
  rfl


omit [NeZero p] in
theorem cartanMod_transpose : (cartanMod τ p)ᵀ = cartanMod τ p := by
  ext i j
  simp [cartanMod, CFSG.LieType.Steinberg.Adjoint.symmetrizedCartan_symm τ j i]

theorem torusAct_form (w : WeylGroup τ) (s s' : Fin τ.rank → ZMod p) :
    TableBExc.torusAct τ p w s ⬝ᵥ (cartanMod τ p *ᵥ TableBExc.torusAct τ p w s') =
      s ⬝ᵥ (cartanMod τ p *ᵥ s') := by
  rw [TableBExc.torusAct, TableBExc.torusAct, redMod_form, dotProduct_mulVec_eq_iform,
    iform_smul, ← dotProduct_mulVec_eq_iform, ← redMod_form, TableBExc.redMod_liftMod,
    TableBExc.redMod_liftMod]

end Weyl

end NoTvAut

end CFSG.StandardType

end
