module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

namespace CFSG.RankThree.PartOne.KCMatrixAlgebra

theorem modEq_one_of_pow_modEq_one_of_odd {j N t : ℕ} (hN : Odd N)
    (h : j ^ N ≡ 1 [MOD 2 ^ t]) : j ≡ 1 [MOD 2 ^ t] := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [Nat.modEq_one]
  have hcop : Nat.Coprime (j ^ N) (2 ^ t) := by
    have := h.gcd_eq
    simpa [Nat.Coprime] using this
  have hcopj : Nat.Coprime j (2 ^ t) := (Nat.coprime_pow_left_iff hN.pos j _).1 hcop
  have h2 : j ^ Nat.totient (2 ^ t) ≡ 1 [MOD 2 ^ t] := Nat.ModEq.pow_totient hcopj
  rw [Nat.totient_prime_pow Nat.prime_two ht] at h2
  simp only [Nat.add_one_sub_one, mul_one] at h2
  have hx1 : (j : ZMod (2 ^ t)) ^ N = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h
    simpa using this
  have hx2 : (j : ZMod (2 ^ t)) ^ (2 ^ (t - 1)) = 1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 h2
    simpa using this
  have hg : Nat.gcd N (2 ^ (t - 1)) = 1 :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hN)
  have := pow_gcd_eq_one.2 ⟨hx1, hx2⟩
  rw [hg, pow_one] at this
  exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (by simpa using this)

theorem monoidHom_apply_eq_of_pow_two_pow_eq_one {F : Type*} [Field F] (τ : F →* F) {N : ℕ}
    (hN : Odd N) (hτ : ∀ y, τ^[N] y = y) {c : F} {s : ℕ} (hc : c ^ 2 ^ s = 1) : τ c = c := by
  have hd : orderOf c ∣ 2 ^ s := orderOf_dvd_of_pow_eq_one hc
  have hd0 : 0 < orderOf c := Nat.pos_of_dvd_of_pos hd (by positivity)
  have hfin : IsOfFinOrder c := isOfFinOrder_iff_pow_eq_one.2 ⟨2 ^ s, by positivity, hc⟩
  obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
  have : NeZero (orderOf c) := ⟨hd0.ne'⟩
  have hτc : τ c ^ orderOf c = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  obtain ⟨j, -, hj⟩ := (IsPrimitiveRoot.orderOf c).eq_pow_of_pow_eq_one hτc
  have hiter : ∀ n : ℕ, τ^[n] c = c ^ j ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, map_pow, ← hj, ← pow_mul, pow_succ']
  have hN1 : c ^ j ^ N = c ^ 1 := by rw [← hiter, hτ, pow_one]
  have hmod : j ^ N ≡ 1 [MOD 2 ^ t] := by
    have := hfin.pow_inj_mod.1 hN1
    rwa [ht] at this
  have hj1 : j ≡ 1 [MOD orderOf c] := by
    rw [ht]; exact modEq_one_of_pow_modEq_one_of_odd hN hmod
  have := hfin.pow_inj_mod.2 hj1
  rw [← hj, this, pow_one]

section Idempotents

variable {ι : Type*} [DecidableEq ι] {K : ι → Type*} [∀ i, Field (K i)]

theorem single_one_ne_zero (i : ι) : (Pi.single i 1 : ∀ i, K i) ≠ 0 := by
  intro h
  have := congrFun h i
  simp at this

theorem apply_ne_zero_of_mul_single_one_eq {g : ∀ i, K i} {i : ι}
    (hg : g * Pi.single i 1 = g) (hg0 : g ≠ 0) : g i ≠ 0 := by
  intro hi
  apply hg0
  funext l
  by_cases hl : l = i
  · subst hl; exact hi
  · have := congrFun hg l
    simpa [Pi.single_eq_of_ne hl] using this.symm

theorem single_one_mul_single_one_of_ne {i j : ι} (hij : i ≠ j) :
    (Pi.single i 1 : ∀ i, K i) * Pi.single j 1 = 0 := by
  funext l
  by_cases hl : l = i
  · subst hl; simp [Pi.single_eq_of_ne hij]
  · simp [Pi.single_eq_of_ne hl]

theorem single_one_mul_eq_single_one {f : ∀ i, K i} {j : ι} (hj : f j = 1) :
    (Pi.single j 1 : ∀ i, K i) * f = Pi.single j 1 := by
  funext l
  by_cases hl : l = j
  · subst hl; simp [hj]
  · simp [Pi.single_eq_of_ne hl]

theorem ringAut_single_one (σ : RingAut (∀ i, K i)) (i : ι) :
    ∃ j, σ (Pi.single i 1) = Pi.single j 1 := by
  set f : ∀ i, K i := σ (Pi.single i 1) with hf
  have hidem : f * f = f := by
    rw [hf, ← map_mul, ← Pi.single_mul]; simp
  have hf0 : f ≠ 0 := fun h => single_one_ne_zero i (σ.injective (by rw [map_zero]; exact h))
  obtain ⟨j, hj⟩ : ∃ j, f j ≠ 0 := by
    by_contra hcon
    exact hf0 (funext fun l => by_contra fun hl => hcon ⟨l, hl⟩)
  have hj1 : f j = 1 :=
    (IsIdempotentElem.iff_eq_zero_or_one.1 (congrFun hidem j)).resolve_left hj
  refine ⟨j, ?_⟩
  funext k
  by_cases hkj : k = j
  · subst hkj; simp [hj1]
  · rw [Pi.single_eq_of_ne hkj]
    by_contra hk
    have hk1 : f k = 1 :=
      (IsIdempotentElem.iff_eq_zero_or_one.1 (congrFun hidem k)).resolve_left hk
    have key : ∀ l, f l = 1 →
        σ.symm (Pi.single l 1) * Pi.single i 1 = σ.symm (Pi.single l 1) := by
      intro l hl
      apply σ.injective
      rw [map_mul, σ.apply_symm_apply, single_one_mul_eq_single_one hl]
    have hg0 : ∀ l, σ.symm (Pi.single l 1) ≠ 0 := fun l h => by
      apply single_one_ne_zero (K := K) l
      have := congrArg σ h
      simp at this
    have h1 := apply_ne_zero_of_mul_single_one_eq (key j hj1) (hg0 j)
    have h2 := apply_ne_zero_of_mul_single_one_eq (key k hk1) (hg0 k)
    have h3 : σ.symm (Pi.single j 1) * σ.symm (Pi.single k 1) = 0 := by
      rw [← map_mul, single_one_mul_single_one_of_ne (Ne.symm hkj), map_zero]
    exact mul_ne_zero h1 h2 (congrFun h3 i)

theorem ringAut_apply_single_one_of_isPGroup {p : ℕ} (hp : p.Prime) [Finite ι]
    (hι : Nat.card ι < p) {A : Type*} [Group A] (hA : IsPGroup p A)
    (ψ : A →* RingAut (∀ i, K i)) (a : A) (i : ι) :
    ψ a (Pi.single i 1) = Pi.single i 1 := by
  have := Fact.mk hp
  let _ : MulAction A (∀ i, K i) := MulAction.compHom _ ψ
  have hsub : MulAction.orbit A (Pi.single i 1 : ∀ i, K i) ⊆
      Set.range (fun j : ι => (Pi.single j 1 : ∀ i, K i)) := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨j, hj⟩ := ringAut_single_one (ψ b) i
    exact ⟨j, hj.symm⟩
  have hfin : (MulAction.orbit A (Pi.single i 1 : ∀ i, K i)).Finite :=
    (Set.finite_range _).subset hsub
  have := hfin.to_subtype
  obtain ⟨n, hn⟩ := hA.card_orbit (Pi.single i 1 : ∀ i, K i)
  have hle : Nat.card (MulAction.orbit A (Pi.single i 1 : ∀ i, K i)) ≤ Nat.card ι :=
    (Nat.card_mono (Set.finite_range _) hsub).trans (Finite.card_range_le _)
  have hn0 : n = 0 := by
    by_contra hn0
    have : p ≤ p ^ n := Nat.le_self_pow hn0 p
    omega
  rw [hn0, pow_zero, Nat.card_eq_one_iff_unique] at hn
  obtain ⟨hsing, -⟩ := hn
  exact congrArg Subtype.val (hsing.elim ⟨ψ a • _, ⟨a, rfl⟩⟩ ⟨_, MulAction.mem_orbit_self _⟩)

theorem ringAut_apply_coord_of_fix (σ : RingAut (∀ i, K i)) (i : ι)
    (hfix : σ (Pi.single i 1) = Pi.single i 1) (y : ∀ i, K i) :
    σ y i = (σ (Pi.mulSingle i (y i))) i := by
  have h1 : y * Pi.single i 1 = Pi.mulSingle i (y i) * Pi.single i 1 := by
    funext l
    by_cases hl : l = i
    · subst hl; simp
    · simp [Pi.single_eq_of_ne hl]
  have h2 := congrArg (fun z => σ z i) h1
  simpa [map_mul, hfix] using h2

theorem ringAut_apply_eq_of_pow_two_pow_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    [Finite ι] (hι : Nat.card ι < p) {A : Type*} [Group A] (hA : IsPGroup p A)
    (ψ : A →* RingAut (∀ i, K i)) (a : A) {x : ∀ i, K i} {s : ℕ} (hx : x ^ 2 ^ s = 1) :
    ψ a x = x := by
  obtain ⟨k, hk⟩ := hA a
  have hfix : ∀ i, ψ a (Pi.single i 1) = Pi.single i 1 := fun i =>
    ringAut_apply_single_one_of_isPGroup hp hι hA ψ a i
  funext i
  let τ : K i →* K i := (Pi.evalMonoidHom K i).comp
    ((ψ a).toRingHom.toMonoidHom.comp (MonoidHom.mulSingle K i))
  have hτ : ∀ y : ∀ i, K i, ψ a y i = τ (y i) := fun y =>
    ringAut_apply_coord_of_fix (ψ a) i (hfix i) y
  have hiter : ∀ (n : ℕ) (y : ∀ i, K i), ((ψ a ^ n) y) i = τ^[n] (y i) := by
    intro n y
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', RingAut.mul_apply, hτ, ih, Function.iterate_succ_apply']
  have hpow : ψ a ^ p ^ k = 1 := by rw [← map_pow, hk, map_one]
  have hτN : ∀ c : K i, τ^[p ^ k] c = c := by
    intro c
    have := hiter (p ^ k) (Pi.mulSingle i c)
    rw [hpow] at this
    simpa using this.symm
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  have hxi : x i ^ 2 ^ s = 1 := by simpa using congrFun hx i
  rw [hτ, monoidHom_apply_eq_of_pow_two_pow_eq_one τ hodd hτN hxi]

end Idempotents

end CFSG.RankThree.PartOne.KCMatrixAlgebra
