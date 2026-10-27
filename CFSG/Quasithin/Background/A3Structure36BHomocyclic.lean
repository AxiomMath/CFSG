module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical

public section

universe u

namespace CFSG.Quasithin.A36B

theorem card_le_pow_of_exponent {q : ℕ} :
    ∀ (e : ℕ) (A : Type u) [CommGroup A] [Finite A], (∀ a : A, a ^ q ^ e = 1) →
      Nat.card (powMonoidHom q : A →* A).ker ≤ q ^ 2 → Nat.card A ≤ q ^ (2 * e) := by
  intro e
  induction e with
  | zero =>
    intro A _ _ hexp _
    have hsub : Subsingleton A := ⟨fun a b => by
      have h1 := hexp a
      have h2 := hexp b
      simp only [pow_zero, pow_one] at h1 h2
      rw [h1, h2]⟩
    simp [Nat.card_unique]
  | succ e ih =>
    intro A _ _ hexp hΩ
    have hcard : Nat.card A =
        Nat.card (powMonoidHom q : A →* A).range * Nat.card (powMonoidHom q : A →* A).ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (powMonoidHom q : A →* A).ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange (powMonoidHom q : A →* A)).toEquiv]
    have hexpB : ∀ b : (powMonoidHom q : A →* A).range, b ^ q ^ e = 1 := by
      rintro ⟨_, a, rfl⟩
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one, powMonoidHom_apply]
      rw [← pow_mul, ← pow_succ']
      exact hexp a
    have hΩB : Nat.card (powMonoidHom q : (powMonoidHom q : A →* A).range →*
        (powMonoidHom q : A →* A).range).ker ≤ q ^ 2 := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun b => (⟨(b.1.1 : A), by simpa using congrArg Subtype.val b.2⟩ :
          (powMonoidHom q : A →* A).ker)) ?_) hΩ
      intro b b' hbb'
      have h := congrArg (fun z : (powMonoidHom q : A →* A).ker => (z : A)) hbb'
      apply Subtype.ext
      apply Subtype.ext
      exact h
    have h1 := ih _ hexpB hΩB
    rw [hcard]
    calc Nat.card (powMonoidHom q : A →* A).range * Nat.card (powMonoidHom q : A →* A).ker
        ≤ q ^ (2 * e) * q ^ 2 := Nat.mul_le_mul h1 hΩ
      _ = q ^ (2 * (e + 1)) := by rw [← pow_add]; congr 1

variable {R : Type u} [CommGroup R]

@[expose] def zmodPowHom (a : R) (n : ℕ) [NeZero n] (ha : orderOf a = n) :
    Multiplicative (ZMod n) →* R where
  toFun x := a ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    have h := pow_mod_orderOf a ((Multiplicative.toAdd x).val + (Multiplicative.toAdd y).val)
    rw [ha] at h
    simp only [toAdd_mul, ZMod.val_add]
    rw [h, pow_add]

theorem zmodPowHom_apply (a : R) (n : ℕ) [NeZero n] (ha : orderOf a = n)
    (x : Multiplicative (ZMod n)) : zmodPowHom a n ha x = a ^ (Multiplicative.toAdd x).val :=
  rfl

theorem mulEquiv_zmod_prod {q e : ℕ} (hq : q.Prime) [Finite R]
    (hexp : ∀ x : R, x ^ q ^ e = 1) (hΩ : Nat.card (powMonoidHom q : R →* R).ker ≤ q ^ 2)
    {a b : R} (ha : orderOf a = q ^ e) (hb : orderOf b = q ^ e)
    (hab : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥) :
    Nonempty (R ≃* (Multiplicative (ZMod (q ^ e)) × Multiplicative (ZMod (q ^ e)))) := by
  have hne : NeZero (q ^ e) := ⟨pow_ne_zero e hq.ne_zero⟩
  let Φ : Multiplicative (ZMod (q ^ e)) × Multiplicative (ZMod (q ^ e)) →* R :=
    (zmodPowHom a (q ^ e) ha).comp (MonoidHom.fst _ _) *
      (zmodPowHom b (q ^ e) hb).comp (MonoidHom.snd _ _)
  have hΦ : ∀ x y, Φ (x, y) = a ^ (Multiplicative.toAdd x).val * b ^ (Multiplicative.toAdd y).val :=
    fun x y => rfl
  have hinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have hxy' : a ^ (Multiplicative.toAdd x).val * b ^ (Multiplicative.toAdd y).val = 1 := by
      rw [← hΦ]
      exact hxy
    have h1 : a ^ (Multiplicative.toAdd x).val = (b ^ (Multiplicative.toAdd y).val)⁻¹ :=
      eq_inv_of_mul_eq_one_left hxy'
    have h2 : a ^ (Multiplicative.toAdd x).val ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b := by
      refine ⟨Subgroup.pow_mem _ (Subgroup.mem_zpowers a) _, ?_⟩
      rw [h1]
      exact (Subgroup.zpowers b).inv_mem (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) _)
    rw [hab, Subgroup.mem_bot] at h2
    have hx0 : (Multiplicative.toAdd x).val = 0 := by
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [ha] at h3
      exact Nat.eq_zero_of_dvd_of_lt h3 (ZMod.val_lt _)
    have hy0 : (Multiplicative.toAdd y).val = 0 := by
      have h4 : b ^ (Multiplicative.toAdd y).val = 1 := inv_eq_one.1 (by rw [← h1, h2])
      have h3 := orderOf_dvd_of_pow_eq_one h4
      rw [hb] at h3
      exact Nat.eq_zero_of_dvd_of_lt h3 (ZMod.val_lt _)
    rw [Subgroup.mem_bot]
    refine Prod.ext ?_ ?_
    · exact (ZMod.val_eq_zero _).1 hx0
    · exact (ZMod.val_eq_zero _).1 hy0
  have hcard : Nat.card R ≤
      Nat.card (Multiplicative (ZMod (q ^ e)) × Multiplicative (ZMod (q ^ e))) := by
    have h1 := card_le_pow_of_exponent e R hexp hΩ
    rw [Nat.card_prod]
    have h2 : Nat.card (Multiplicative (ZMod (q ^ e))) = q ^ e := Nat.card_zmod (q ^ e)
    rw [h2, ← pow_add]
    calc Nat.card R ≤ q ^ (2 * e) := h1
      _ = q ^ (e + e) := by rw [two_mul]
  exact ⟨(MulEquiv.ofBijective Φ (Function.Injective.bijective_of_nat_card_le hinj hcard)).symm⟩

theorem mem_zpowers_pow_of_pow_eq_one {q e : ℕ} (hq : q.Prime) (he : 1 ≤ e) {a w : R}
    (ha : orderOf a = q ^ e) (hw : w ∈ Subgroup.zpowers a) (hwq : w ^ q = 1) :
    w ∈ Subgroup.zpowers (a ^ q ^ (e - 1)) := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have h1 : a ^ (m * (q : ℤ)) = 1 := by
    rw [zpow_mul, zpow_natCast]
    exact hwq
  have h2 : ((orderOf a : ℕ) : ℤ) ∣ m * (q : ℤ) := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [ha] at h2
  have h3 : ((q ^ (e - 1) : ℕ) : ℤ) * (q : ℤ) ∣ m * (q : ℤ) := by
    have : q ^ e = q ^ (e - 1) * q := by
      rw [← pow_succ, Nat.sub_add_cancel he]
    rw [this] at h2
    exact_mod_cast h2
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  obtain ⟨m', hm'⟩ := (mul_dvd_mul_iff_right hq0).1 h3
  refine Subgroup.mem_zpowers_iff.2 ⟨m', ?_⟩
  rw [hm', zpow_mul, zpow_natCast]

theorem exists_independent_generators {q : ℕ} (hq : q.Prime) [Finite R]
    (hR : IsPGroup q R) (hΩ : Nat.card (powMonoidHom q : R →* R).ker = q ^ 2)
    (hirr : ∀ S : Subgroup R, S.Characteristic → S ≤ (powMonoidHom q : R →* R).ker →
      S = ⊥ ∨ S = (powMonoidHom q : R →* R).ker) :
    ∃ e : ℕ, 1 ≤ e ∧ (∀ x : R, x ^ q ^ e = 1) ∧ ∃ a b : R, orderOf a = q ^ e ∧
      orderOf b = q ^ e ∧ Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
  classical
  have hfq : Fact q.Prime := ⟨hq⟩
  have hex : ∃ n : ℕ, ∀ x : R, x ^ q ^ n = 1 := by
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    exact ⟨n, fun x => by rw [← hn]; exact pow_card_eq_one'⟩
  obtain ⟨e, he, hmin⟩ : ∃ e : ℕ, (∀ x : R, x ^ q ^ e = 1) ∧
      ∀ e' < e, ¬ ∀ x : R, x ^ q ^ e' = 1 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun e' h => Nat.find_min hex h⟩
  have hq2 : 2 ≤ q := hq.two_le
  have he1 : 1 ≤ e := by
    by_contra h0
    have h0' : e = 0 := by omega
    subst h0'
    have hall : ∀ x : R, x = 1 := fun x => by simpa using he x
    have h1 : Nat.card (powMonoidHom q : R →* R).ker ≤ 1 := by
      have : Subsingleton (powMonoidHom q : R →* R).ker :=
        ⟨fun a b => Subtype.ext ((hall a).trans (hall b).symm)⟩
      exact Finite.card_le_one_iff_subsingleton.2 this
    rw [hΩ] at h1
    nlinarith
  obtain ⟨Ω, hΩdef⟩ : ∃ Ω : Subgroup R, Ω = (powMonoidHom q : R →* R).ker := ⟨_, rfl⟩
  rw [← hΩdef] at hΩ hirr
  obtain ⟨S, hSdef⟩ : ∃ S : Subgroup R, S = (powMonoidHom (q ^ (e - 1)) : R →* R).range :=
    ⟨_, rfl⟩
  have hmemΩ : ∀ x : R, x ∈ Ω ↔ x ^ q = 1 := by
    intro x
    rw [hΩdef, MonoidHom.mem_ker, powMonoidHom_apply]
  have hSchar : S.Characteristic := by
    refine CFSG.SectionRank.Ccomm.characteristic_of_forall_mem fun φ x hx => ?_
    rw [hSdef] at hx ⊢
    obtain ⟨y, rfl⟩ := hx
    exact ⟨φ y, by simp [powMonoidHom_apply, map_pow]⟩
  have hSle : S ≤ Ω := by
    rw [hSdef]
    rintro _ ⟨y, rfl⟩
    rw [hmemΩ, powMonoidHom_apply, ← pow_mul, ← pow_succ, Nat.sub_add_cancel he1]
    exact he y
  have hSne : S ≠ ⊥ := by
    intro hS
    apply hmin (e - 1) (by omega)
    intro x
    have hx : x ^ q ^ (e - 1) ∈ S := by
      rw [hSdef]
      exact ⟨x, rfl⟩
    rw [hS, Subgroup.mem_bot] at hx
    exact hx
  have hSΩ : S = Ω := (hirr S hSchar hSle).resolve_left hSne
  have hΩ_gt : 1 < Nat.card Ω := by
    rw [hΩ]
    nlinarith
  obtain ⟨u, hu1⟩ : ∃ u : Ω, u ≠ 1 := by
    have := Finite.one_lt_card_iff_nontrivial.1 hΩ_gt
    exact exists_ne 1
  have hu : (u : R) ^ q = 1 := (hmemΩ _).1 u.2
  have hu1' : (u : R) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huord : orderOf (u : R) = q := orderOf_eq_prime hu hu1'
  have hzu : Nat.card (Subgroup.zpowers (u : R)) = q := by rw [Nat.card_zpowers, huord]
  obtain ⟨v, hvΩ, hvu⟩ : ∃ v ∈ Ω, v ∉ Subgroup.zpowers (u : R) := by
    by_contra hcon
    push Not at hcon
    have hle : Ω ≤ Subgroup.zpowers (u : R) := fun v hv => hcon v hv
    have h1 := Subgroup.card_le_of_le hle
    rw [hΩ, hzu] at h1
    have h2 : q < q ^ 2 := by nlinarith
    omega
  have hv : v ^ q = 1 := (hmemΩ _).1 hvΩ
  have hv1' : v ≠ 1 := fun h => hvu (h ▸ (Subgroup.zpowers (u : R)).one_mem)
  have hvord : orderOf v = q := orderOf_eq_prime hv hv1'
  have huS : (u : R) ∈ S := hSΩ ▸ u.2
  have hvS : v ∈ S := hSΩ ▸ hvΩ
  rw [hSdef] at huS hvS
  obtain ⟨a, ha⟩ := huS
  obtain ⟨b, hb⟩ := hvS
  have ha' : a ^ q ^ (e - 1) = (u : R) := ha
  have hb' : b ^ q ^ (e - 1) = v := hb
  have hord : ∀ c : R, ¬ c ^ q ^ (e - 1) = 1 → orderOf c = q ^ e := by
    intro c hc
    have := orderOf_eq_prime_pow (p := q) hc (by rw [Nat.sub_add_cancel he1]; exact he c)
    rwa [Nat.sub_add_cancel he1] at this
  have haord : orderOf a = q ^ e := hord a (by rw [ha']; exact hu1')
  have hbord : orderOf b = q ^ e := hord b (by rw [hb']; exact hv1')
  refine ⟨e, he1, he, a, b, haord, hbord, ?_⟩
  by_contra hW
  have hWp : IsPGroup q ↥(Subgroup.zpowers a ⊓ Subgroup.zpowers b) := hR.to_subgroup _
  obtain ⟨k, hk⟩ := hWp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hW
    exact Subgroup.eq_bot_of_card_eq _ (by simpa using hk)
  have hqdvd : q ∣ Nat.card ↥(Subgroup.zpowers a ⊓ Subgroup.zpowers b) := by
    rw [hk]
    exact dvd_pow_self q hk0
  obtain ⟨w, hwo⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.zpowers a ⊓ Subgroup.zpowers b)) q hqdvd
  have hwa : (w : R) ∈ Subgroup.zpowers a := w.2.1
  have hwb : (w : R) ∈ Subgroup.zpowers b := w.2.2
  have hwo' : orderOf (w : R) = q := by rw [Subgroup.orderOf_coe]; exact hwo
  have hwq : (w : R) ^ q = 1 := by rw [← hwo']; exact pow_orderOf_eq_one _
  have hwu : (w : R) ∈ Subgroup.zpowers (u : R) := by
    rw [← ha']
    exact mem_zpowers_pow_of_pow_eq_one hq he1 haord hwa hwq
  have hwv : (w : R) ∈ Subgroup.zpowers v := by
    rw [← hb']
    exact mem_zpowers_pow_of_pow_eq_one hq he1 hbord hwb hwq
  have hcw : Nat.card (Subgroup.zpowers (w : R)) = q := by rw [Nat.card_zpowers, hwo']
  have h1 : Subgroup.zpowers (w : R) = Subgroup.zpowers (u : R) :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hwu) (by rw [hzu, hcw])
  have hzv : Nat.card (Subgroup.zpowers v) = q := by rw [Nat.card_zpowers, hvord]
  have h2 : Subgroup.zpowers (w : R) = Subgroup.zpowers v :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hwv) (by rw [hzv, hcw])
  apply hvu
  rw [← h1, h2]
  exact Subgroup.mem_zpowers v

theorem omegaTwo_equiv {q e : ℕ} (hq : q.Prime) (he : 2 ≤ e) [Finite R]
    (hΩ : Nat.card (powMonoidHom q : R →* R).ker ≤ q ^ 2)
    {a b : R} (ha : orderOf a = q ^ e) (hb : orderOf b = q ^ e)
    (hab : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥) :
    Nonempty (↥(powMonoidHom (q ^ 2) : R →* R).ker ≃*
      (Multiplicative (ZMod (q ^ 2)) × Multiplicative (ZMod (q ^ 2)))) := by
  have hmem : ∀ x : R, x ∈ (powMonoidHom (q ^ 2) : R →* R).ker ↔ x ^ q ^ 2 = 1 := by
    intro x
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
  have hpow : ∀ c : R, orderOf c = q ^ e → c ^ q ^ (e - 2) ∈ (powMonoidHom (q ^ 2) : R →* R).ker ∧
      orderOf (c ^ q ^ (e - 2)) = q ^ 2 := by
    intro c hc
    refine ⟨(hmem _).2 ?_, ?_⟩
    · rw [← pow_mul, ← pow_add, Nat.sub_add_cancel he]
      rw [← hc]
      exact pow_orderOf_eq_one c
    · rw [orderOf_pow_of_dvd (pow_ne_zero _ hq.ne_zero), hc]
      · rw [Nat.pow_div (by omega) hq.pos]
        congr 1
        omega
      · rw [hc]
        exact Nat.pow_dvd_pow q (by omega)
  obtain ⟨ha1, ha2⟩ := hpow a ha
  obtain ⟨hb1, hb2⟩ := hpow b hb
  have hle : ∀ c : R, c ^ q ^ (e - 2) ∈ Subgroup.zpowers c := fun c =>
    Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _
  refine mulEquiv_zmod_prod (R := ↥(powMonoidHom (q ^ 2) : R →* R).ker) (e := 2) hq ?_ ?_
    (a := ⟨a ^ q ^ (e - 2), ha1⟩) (b := ⟨b ^ q ^ (e - 2), hb1⟩) ?_ ?_ ?_
  · intro x
    exact Subtype.ext ((hmem x).1 x.2)
  · refine le_trans (Nat.card_le_card_of_injective
      (fun y => (⟨(y.1.1 : R), by simpa using congrArg Subtype.val y.2⟩ :
        (powMonoidHom q : R →* R).ker)) ?_) hΩ
    intro y y' hyy'
    have h := congrArg (fun z : (powMonoidHom q : R →* R).ker => (z : R)) hyy'
    apply Subtype.ext
    apply Subtype.ext
    exact h
  · rw [Subgroup.orderOf_mk]
    exact ha2
  · rw [Subgroup.orderOf_mk]
    exact hb2
  · rw [eq_bot_iff]
    intro z hz
    have hz1 : (z : R) ∈ Subgroup.zpowers a := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz.1
      have : (z : R) = (a ^ q ^ (e - 2)) ^ k := by
        rw [← hk]
        rfl
      rw [this]
      exact Subgroup.zpow_mem _ (hle a) _
    have hz2 : (z : R) ∈ Subgroup.zpowers b := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz.2
      have : (z : R) = (b ^ q ^ (e - 2)) ^ k := by
        rw [← hk]
        rfl
      rw [this]
      exact Subgroup.zpow_mem _ (hle b) _
    have : (z : R) ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b := ⟨hz1, hz2⟩
    rw [hab, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)

end CFSG.Quasithin.A36B
