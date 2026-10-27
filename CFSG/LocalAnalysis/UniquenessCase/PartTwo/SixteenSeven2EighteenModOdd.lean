module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenLin
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

section Group

variable {A : Type*} [Group A]

theorem s16c167_conj_eq_or_inv {a t : A} {p : ℕ} (hp : p.Prime) (ha : orderOf a = p)
    (ht : t * t = 1) (hn : t * a * t ∈ Subgroup.zpowers a) :
    t * a * t = a ∨ t * a * t = a⁻¹ := by
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hn
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one]; exact ht
  have hconj : ∀ i : ℤ, t * a ^ i * t = (t * a * t) ^ i := by
    intro i
    have h := conj_zpow (a := t) (b := a) (i := i)
    rw [htinv] at h
    exact h.symm
  have hsquare : a = a ^ (j * j) := by
    calc a = t * (t * a * t) * t := by
          rw [show t * (t * a * t) * t = (t * t) * a * (t * t) from by group, ht,
            one_mul, mul_one]
      _ = t * a ^ j * t := by rw [hj]
      _ = (t * a * t) ^ j := hconj j
      _ = (a ^ j) ^ j := by rw [hj]
      _ = a ^ (j * j) := (zpow_mul a j j).symm
  have hpow : a ^ (j * j - 1) = 1 := by
    have h5 : a ^ (j * j) * a⁻¹ = 1 := by
      rw [← hsquare, mul_inv_cancel]
    rwa [← zpow_sub_one] at h5
  have hdvd : (p : ℤ) ∣ j * j - 1 := by
    have h := (orderOf_dvd_iff_zpow_eq_one (x := a) (i := j * j - 1)).mpr hpow
    rwa [ha] at h
  have hfac : j * j - 1 = (j - 1) * (j + 1) := by ring
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpz.dvd_or_dvd (hfac ▸ hdvd) with h | h
  · left
    have hh : a ^ (j - 1) = 1 := by
      rw [← ha] at h
      exact (orderOf_dvd_iff_zpow_eq_one (x := a) (i := j - 1)).mp h
    have hja : a ^ j = a := by
      rw [show j = (j - 1) + 1 by ring, zpow_add, hh, one_mul, zpow_one]
    exact hj ▸ hja
  · right
    have hh : a ^ (j + 1) = 1 := by
      rw [← ha] at h
      exact (orderOf_dvd_iff_zpow_eq_one (x := a) (i := j + 1)).mp h
    have hja : a ^ j = a⁻¹ := by
      have h1 : a ^ j * a = 1 := by
        have h2 := hh
        rw [zpow_add, zpow_one] at h2
        exact h2
      exact (mul_eq_one_iff_eq_inv).mp h1
    exact hj ▸ hja

end Group

variable {W : Type} [CommGroup W] [Finite W]

private lemma s16c167_mem_zpowers_of_map_eq {a : MulAut W} {U : Subgroup W}
    (hU : U.map a.toMonoidHom = U) :
    ∀ g ∈ Subgroup.zpowers a, ∀ w ∈ U, g w ∈ U := by
  have haU : ∀ w ∈ U, a w ∈ U := fun w hw => by
    rw [← hU]; exact Subgroup.mem_map_of_mem a.toMonoidHom hw
  intro g hg w hw
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff g a).mp
    ((mem_powers_iff_mem_zpowers (x := a) (y := g)).mpr hg)
  have key : ∀ n : ℕ, ∀ w ∈ U, (a ^ n) w ∈ U := by
    intro n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih => intro w hw; rw [pow_succ]; exact ih (a w) (haU w hw)
  rw [← hn]
  exact key n w hw

theorem s16c167_prime_dvd_pow_rk (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    {a : MulAut W} (ha : orderOf a = p) {U : Subgroup W} (hU : U.map a.toMonoidHom = U)
    (hfix : U ⊓ fixV (Subgroup.zpowers a) = ⊥) : p ∣ 2 ^ rk ↥U - 1 := by
  let Ω : Set W := (U : Set W) \ {1}
  have hΩ : ∀ g ∈ Subgroup.zpowers a, ∀ v ∈ Ω, g v ∈ Ω := by
    rintro g hg v hv
    rw [Set.mem_sdiff, Set.mem_singleton_iff] at hv ⊢
    obtain ⟨hvU, hv1⟩ := hv
    exact ⟨s16c167_mem_zpowers_of_map_eq hU g hg v hvU,
      fun h => hv1 (g.injective (by rw [h, map_one]))⟩
  have hfree : ∀ g ∈ Subgroup.zpowers a, ∀ v ∈ Ω, g v = v → g = 1 := by
    rintro g hg v hv hgv
    rw [Set.mem_sdiff, Set.mem_singleton_iff] at hv
    obtain ⟨hvU, hv1⟩ := hv
    by_contra hg1
    have hgdvd : orderOf g ∣ p := by
      have hle : Subgroup.zpowers g ≤ Subgroup.zpowers a := Subgroup.zpowers_le.mpr hg
      have := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, Nat.card_zpowers, ha] at this
    have hgord : orderOf g = p := by
      rcases hp.eq_one_or_self_of_dvd (orderOf g) hgdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hg1
      · exact h
    have hcard : Nat.card (Subgroup.zpowers a) ≤ Nat.card (Subgroup.zpowers g) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hgord, ha]
    have heq : Subgroup.zpowers g = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg) hcard
    have hfixv : v ∈ fixV (Subgroup.zpowers a) := by
      have hgv' : v ∈ fixV (Subgroup.zpowers g) := (mem_fixV_zpowers g v).mpr hgv
      rwa [heq] at hgv'
    have hmem : v ∈ U ⊓ fixV (Subgroup.zpowers a) := ⟨hvU, hfixv⟩
    rw [hfix, Subgroup.mem_bot] at hmem
    exact hv1 hmem
  have hdvd := card_dvd_card_of_free hΩ hfree
  have hG : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers]; exact ha
  rw [hG] at hdvd
  have hΩcard : Nat.card Ω = Nat.card U - 1 := by
    change Ω.ncard = (U : Set W).ncard - 1
    rw [show Ω = (U : Set W) \ {1} from rfl, Set.ncard_sdiff_singleton_of_mem U.one_mem]
  rwa [hΩcard, card_eq_two_pow hW U] at hdvd

theorem s16c167_two_le_rk_of_order_three (hW : ∀ w : W, w ^ 2 = 1) {a : MulAut W}
    (ha : orderOf a = 3) {U : Subgroup W} (hU : U.map a.toMonoidHom = U)
    (hfix : U ⊓ fixV (Subgroup.zpowers a) = ⊥) (hne : U ≠ ⊥) : 2 ≤ rk ↥U := by
  have hdvd : 3 ∣ 2 ^ rk ↥U - 1 := s16c167_prime_dvd_pow_rk hW Nat.prime_three ha hU hfix
  have h0 : rk ↥U ≠ 0 := fun h => hne ((rk_eq_zero_iff hW).mp h)
  by_contra hlt
  have hm : rk ↥U = 0 ∨ rk ↥U = 1 := by omega
  rcases hm with h | h
  · exact h0 h
  · rw [h] at hdvd; norm_num at hdvd

theorem s16c167_three_le_rk_of_order_seven (hW : ∀ w : W, w ^ 2 = 1) {a : MulAut W}
    (ha : orderOf a = 7) {U : Subgroup W} (hU : U.map a.toMonoidHom = U)
    (hfix : U ⊓ fixV (Subgroup.zpowers a) = ⊥) (hne : U ≠ ⊥) : 3 ≤ rk ↥U := by
  have hdvd : 7 ∣ 2 ^ rk ↥U - 1 := s16c167_prime_dvd_pow_rk hW Nat.prime_seven ha hU hfix
  have h0 : rk ↥U ≠ 0 := fun h => hne ((rk_eq_zero_iff hW).mp h)
  by_contra hlt
  have hm : rk ↥U = 0 ∨ rk ↥U = 1 ∨ rk ↥U = 2 := by omega
  rcases hm with h | h | h
  · exact h0 h
  · rw [h] at hdvd; norm_num at hdvd
  · rw [h] at hdvd; norm_num at hdvd

private lemma s16c167_map_pow_eq_of_map_eq {τ : MulAut W} {K : Subgroup W}
    (h : K.map τ.toMonoidHom = K) (j : ℕ) : K.map (τ ^ j).toMonoidHom = K := by
  induction j with
  | zero =>
    have h1 : (τ ^ 0).toMonoidHom = MonoidHom.id W := MonoidHom.ext fun _ => rfl
    rw [h1, Subgroup.map_id]
  | succ j ih =>
    have h1 : (τ ^ (j + 1)).toMonoidHom = (τ ^ j).toMonoidHom.comp τ.toMonoidHom := by
      rw [pow_succ]
      exact MonoidHom.ext fun _ => rfl
    rw [h1, ← Subgroup.map_map, h, ih]

theorem s16c167_two_rk_le_mQuot_of_inverts (hW : ∀ w : W, w ^ 2 = 1) {a t : MulAut W}
    {I : Subgroup W} (hodd : Odd (orderOf a)) (ht : t * t = 1) (hta : t * a * t = a⁻¹)
    (hIa : I.map a.toMonoidHom = I) (hIt : I.map t.toMonoidHom = I)
    (hfix : I ⊓ fixV (Subgroup.zpowers a) = ⊥) :
    rk ↥I ≤ 2 * E3.mQuot I (I ⊓ fixV (Subgroup.zpowers t)) := by
  obtain ⟨k, hk⟩ := hodd
  let b : MulAut W := a ^ (k + 1)
  have hb2 : b * b = a := by
    have h1 : b * b = a ^ ((k + 1) * 2) := by
      change a ^ (k + 1) * a ^ (k + 1) = a ^ ((k + 1) * 2)
      rw [pow_mul, pow_two]
    rw [h1]
    have h2 : (k + 1) * 2 = orderOf a + 1 := by omega
    rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one]; exact ht
  have hb_inv : t * b * t = b⁻¹ := by
    have h1 : t * b * t = (t * a * t) ^ (k + 1) := by
      have h := conj_pow (a := t) (b := a) (i := k + 1)
      rw [htinv] at h
      change t * a ^ (k + 1) * t = (t * a * t) ^ (k + 1)
      exact h.symm
    rw [h1, hta, inv_pow]
  have hbt1 : b * t = t * b⁻¹ := by
    have h := hb_inv
    have h2 : t * (t * b * t) = t * b⁻¹ := by rw [h]
    have h3 : t * (t * b * t) = (t * t) * b * t := by group
    rw [h3, ht, one_mul] at h2
    exact h2
  have hbt : a * t = b * t * b⁻¹ := by
    calc a * t = (b * b) * t := by rw [hb2]
      _ = b * (b * t) := by group
      _ = b * (t * b⁻¹) := by rw [hbt1]
      _ = b * t * b⁻¹ := by group
  have hkey : ∀ x : W, (a * t) x = x ↔ t (b.symm x) = b.symm x := by
    intro x
    have h1 : (a * t) x = b (t (b.symm x)) := by rw [hbt]; rfl
    rw [h1]
    constructor
    · intro h
      apply b.injective
      rw [h, b.apply_symm_apply]
    · intro h
      rw [h, b.apply_symm_apply]
  have hIb : I.map b.toMonoidHom = I := by
    have := s16c167_map_pow_eq_of_map_eq (τ := a) hIa (k + 1)
    simpa [b] using this
  have hCs : I ⊓ fixV (Subgroup.zpowers (a * t)) =
      (I ⊓ fixV (Subgroup.zpowers t)).map b.toMonoidHom := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_map_equiv, Subgroup.mem_inf, mem_fixV_zpowers,
      mem_fixV_zpowers]
    constructor
    · rintro ⟨hxI, hxfix⟩
      have hbxI : b.symm x ∈ I := by
        rw [← Subgroup.mem_map_equiv]
        rwa [hIb]
      exact ⟨hbxI, (hkey x).mp hxfix⟩
    · rintro ⟨hbxI, hbxfix⟩
      have hxI : x ∈ I := by
        have h1 : x ∈ I.map b.toMonoidHom := by
          rw [← b.apply_symm_apply x]
          exact Subgroup.mem_map_of_mem b.toMonoidHom hbxI
        rwa [hIb] at h1
      exact ⟨hxI, (hkey x).mpr hbxfix⟩
  let A : Subgroup W := I ⊓ fixV (Subgroup.zpowers t)
  let B : Subgroup W := I ⊓ fixV (Subgroup.zpowers (a * t))
  have hBA : B = A.map b.toMonoidHom := hCs
  have hrkB : rk B = rk A := by rw [hBA, s15_Lin_rk_map]
  have hAB : A ⊓ B = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨⟨hxI, hxt⟩, -, hxat⟩
    have hxt' : t x = x := (mem_fixV_zpowers t x).mp hxt
    have hxat' : (a * t) x = x := (mem_fixV_zpowers (a * t) x).mp hxat
    have hax : a x = x := by
      have h1 : (a * t) x = a (t x) := rfl
      rw [h1, hxt'] at hxat'
      exact hxat'
    have hmem : x ∈ I ⊓ fixV (Subgroup.zpowers a) :=
      ⟨hxI, (mem_fixV_zpowers a x).mpr hax⟩
    rw [hfix, Subgroup.mem_bot] at hmem
    exact hmem
  have hsum : rk ↥(A ⊔ B) = rk A + rk B := by
    have := rk_sup_add_rk_inf A B
    rw [hAB, rk_bot, add_zero] at this
    exact this
  have hle : rk ↥(A ⊔ B) ≤ rk I := rk_mono (sup_le inf_le_left inf_le_left)
  have hrkI : rk I = E3.mQuot I A + rk A := by
    have hcard : Nat.card I = 2 ^ E3.mQuot I A * Nat.card A :=
      E3.card_eq_two_pow_mul ((isPGroup_two_of_sq_eq_one hW).to_subgroup I) inf_le_left
    have h := congrArg (padicValNat 2) hcard
    rw [padicValNat.mul (pow_ne_zero _ (by norm_num)) (Nat.card_pos (α := A)).ne'] at h
    rw [padicValNat.prime_pow] at h
    simpa only [rk] using h
  change rk ↥I ≤ 2 * E3.mQuot I A
  omega

theorem s16c167_oe (hW : ∀ w : W, w ^ 2 = 1) {a t : MulAut W} {I : Subgroup W} {n : ℕ}
    (hodd : Odd (orderOf a)) (ht : t * t = 1) (hta : t * a * t = a⁻¹ ∨ t * a = a * t)
    (hIa : I.map a.toMonoidHom = I) (hIt : I.map t.toMonoidHom = I)
    (hfix : I ⊓ fixV (Subgroup.zpowers a) = ⊥)
    (hn : ∀ U : Subgroup W, U.map a.toMonoidHom = U → U ≠ ⊥ →
      U ⊓ fixV (Subgroup.zpowers a) = ⊥ → n ≤ rk ↥U)
    (hrk : 2 * n ≤ rk ↥I) :
    I ≤ fixV (Subgroup.zpowers t) ∨ n ≤ E3.mQuot I (I ⊓ fixV (Subgroup.zpowers t)) := by
  rcases hta with hta | hcomm
  · right
    have h := s16c167_two_rk_le_mQuot_of_inverts hW hodd ht hta hIa hIt hfix
    omega
  · by_cases hUbot : commSub I (Subgroup.zpowers t) = ⊥
    · left
      rwa [commSub_eq_bot_iff] at hUbot
    · right
      let U : Subgroup W := commSub I (Subgroup.zpowers t)
      have hI : ∀ x ∈ Subgroup.zpowers t, ∀ w ∈ I, x w ∈ I :=
        s16c167_mem_zpowers_of_map_eq hIt
      have hcomp : a.toMonoidHom.comp (commHom t) = (commHom t).comp a.toMonoidHom := by
        ext w
        simp only [MonoidHom.comp_apply, commHom_apply, map_mul, map_inv]
        have h1 : (MulEquiv.toMonoidHom a) (t w) = t ((MulEquiv.toMonoidHom a) w) := by
          have := congrArg (fun z : MulAut W => z w) hcomm.symm
          simpa [MulAut.mul_apply] using this
        rw [h1]
      have hUa : U.map a.toMonoidHom = U := by
        rw [show U = I.map (commHom t) from commSub_zpowers_eq_map hI, Subgroup.map_map,
          hcomp, ← Subgroup.map_map, hIa]
      have hUle : U ≤ I := commSub_le_of_invariant hI
      have hUfix : U ⊓ fixV (Subgroup.zpowers a) = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        rintro x ⟨hxU, hxa⟩
        have hmem : x ∈ I ⊓ fixV (Subgroup.zpowers a) := ⟨hUle hxU, hxa⟩
        rw [hfix, Subgroup.mem_bot] at hmem
        exact hmem
      have hnU : n ≤ rk ↥U := hn U hUa hUbot hUfix
      have hC : rk ↥(I ⊓ fixV (Subgroup.zpowers t)) ≤ rk ↥I := rk_mono inf_le_left
      have hsum : rk ↥U + rk ↥(I ⊓ fixV (Subgroup.zpowers t)) = rk ↥I :=
        rk_commSub_add_rk_inf_fixV (g := t) (W := I) hI
      have hcard : Nat.card I = 2 ^ E3.mQuot I (I ⊓ fixV (Subgroup.zpowers t)) *
          Nat.card (I ⊓ fixV (Subgroup.zpowers t) : Subgroup W) :=
        E3.card_eq_two_pow_mul ((isPGroup_two_of_sq_eq_one hW).to_subgroup I) inf_le_left
      have hmq : rk ↥I = E3.mQuot I (I ⊓ fixV (Subgroup.zpowers t)) +
          rk ↥(I ⊓ fixV (Subgroup.zpowers t)) := by
        have h := congrArg (padicValNat 2) hcard
        rw [padicValNat.mul (pow_ne_zero _ (by norm_num))
          (Nat.card_pos (α := (I ⊓ fixV (Subgroup.zpowers t) : Subgroup W))).ne'] at h
        rw [padicValNat.prime_pow] at h
        simpa only [rk] using h
      omega

theorem s16c167_oe3 (hW : ∀ w : W, w ^ 2 = 1) {a t : MulAut W} {I : Subgroup W}
    (ha : orderOf a = 3) (ht : t * t = 1) (hta : t * a * t = a⁻¹ ∨ t * a = a * t)
    (hIa : I.map a.toMonoidHom = I) (hIt : I.map t.toMonoidHom = I)
    (hfix : I ⊓ fixV (Subgroup.zpowers a) = ⊥) (hrk : 4 ≤ rk ↥I) :
    I ≤ fixV (Subgroup.zpowers t) ∨ 2 ≤ E3.mQuot I (I ⊓ fixV (Subgroup.zpowers t)) := by
  refine s16c167_oe (n := 2) hW ?_ ht hta hIa hIt hfix ?_ ?_
  · rw [ha]; exact ⟨1, by norm_num⟩
  · intro U hU hUne hUfix
    exact s16c167_two_le_rk_of_order_three hW ha hU hUfix hUne
  · omega

theorem s16c167_oe7 (hW : ∀ w : W, w ^ 2 = 1) {a t : MulAut W} {I : Subgroup W}
    (ha : orderOf a = 7) (ht : t * t = 1) (hta : t * a * t = a⁻¹ ∨ t * a = a * t)
    (hIa : I.map a.toMonoidHom = I) (hIt : I.map t.toMonoidHom = I)
    (hfix : I ⊓ fixV (Subgroup.zpowers a) = ⊥) (hrk : 6 ≤ rk ↥I) :
    I ≤ fixV (Subgroup.zpowers t) ∨ 3 ≤ E3.mQuot I (I ⊓ fixV (Subgroup.zpowers t)) := by
  refine s16c167_oe (n := 3) hW ?_ ht hta hIa hIt hfix ?_ ?_
  · rw [ha]; exact ⟨3, by norm_num⟩
  · intro U hU hUne hUfix
    exact s16c167_three_le_rk_of_order_seven hW ha hU hUfix hUne
  · omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
