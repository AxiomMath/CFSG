module

public import CFSG.Quasithin.Vol2.GoldschmidtF431L3Local

public section

namespace CFSG.Quasithin.H13.F431.L3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G]

namespace L3Datum

section Weyl

variable [Finite G] {M₁ M₂ : Subgroup G} {D : L3Datum M₁ M₂}

abbrev Wn (D : L3Datum M₁ M₂) : Subgroup G := Subgroup.normalizer (D.B : Set G)

omit [Finite G] in
theorem normedBy_conj {K : Subgroup G} (hK : NormedBy D.B K) {g : G} (hg : g ∈ D.Wn) :
    NormedBy D.B (conjSub g K) := by
  intro b hb x hx
  rw [mem_conjSub] at hx ⊢
  have hg' : g⁻¹ ∈ D.Wn := D.Wn.inv_mem hg
  have hb' : g⁻¹ * b * g ∈ D.B := by
    have := (Subgroup.mem_normalizer_iff.mp hg' b).mp hb
    simpa using this
  have := hK _ hb' _ hx
  rwa [show g⁻¹ * (b * x * b⁻¹) * g = (g⁻¹ * b * g) * (g⁻¹ * x * g) * (g⁻¹ * b * g)⁻¹ by group]

theorem normedBy_S : NormedBy D.B D.S := fun b hb _ hx => D.S_norm b (D.B_le hb) _ hx

theorem normedBy_Z : NormedBy D.B D.Z := fun _ hb _ hx => D.Z_norm (D.B_le hb) hx

theorem mem_B_of_mem_H_Wn {h : G} (hh : h ∈ M₁ ⊓ M₂) (hW : h ∈ D.Wn) :
    h ∈ D.B := by
  obtain ⟨s, hs, b, hb, rfl⟩ := D.mul_SB h hh
  have hbW : b ∈ D.Wn := Subgroup.le_normalizer hb
  have hsW : s ∈ D.Wn := by
    have := D.Wn.mul_mem hW (D.Wn.inv_mem hbW)
    simpa using this
  have hcomm : ∀ x ∈ D.B, s * x = x * s := by
    intro x hx
    have h1 : s * x * s⁻¹ ∈ D.B := by
      have := (Subgroup.mem_normalizer_iff.mp hsW x).mp hx
      exact this
    have h2 : x * s⁻¹ * x⁻¹ ∈ D.S := D.S_norm x (D.B_le hx) s⁻¹ (D.S.inv_mem hs)
    have h3 : s * x * s⁻¹ * x⁻¹ ∈ D.S := by
      have := D.S.mul_mem hs h2
      simpa [mul_assoc] using this
    have h4 : s * x * s⁻¹ * x⁻¹ ∈ D.B := D.B.mul_mem h1 (D.B.inv_mem hx)
    have h5 := D.B_inf_S h3 h4
    calc s * x = (s * x * s⁻¹ * x⁻¹) * (x * s) := by group
      _ = x * s := by rw [h5, one_mul]
  have hs1 : s = 1 := D.centS s hs hcomm
  rw [hs1, one_mul]; exact hb

theorem normalizer_S_eq (hG : D.Good) :
    Subgroup.normalizer (D.S : Set G) = M₁ ⊓ M₂ := by
  refine le_antisymm (fun n hn => hG.mem_H_of_normalizer_S hn) (fun h hh => ?_)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨D.S_norm h hh x, fun hx => by
    have := D.S_norm h⁻¹ ((M₁ ⊓ M₂).inv_mem hh) _ hx
    simpa [mul_assoc] using this⟩

end Weyl

end L3Datum

namespace L3Datum

section Weyl2

variable [Finite G] {M₁ M₂ : Subgroup G} {D : L3Datum M₁ M₂}

theorem card_H : Nat.card ↥(M₁ ⊓ M₂) = Nat.card D.S * Nat.card D.B := by
  let f : D.S × D.B → ↥(M₁ ⊓ M₂) := fun p =>
    ⟨p.1 * p.2, (M₁ ⊓ M₂).mul_mem (D.S_le_H p.1.2) (D.B_le p.2.2)⟩
  have hinj : Function.Injective f := by
    rintro ⟨⟨n, hn⟩, ⟨b, hb⟩⟩ ⟨⟨n', hn'⟩, ⟨b', hb'⟩⟩ h
    have h1 : n * b = n' * b' := congrArg Subtype.val h
    have h2 : n'⁻¹ * n = b' * b⁻¹ := by
      calc n'⁻¹ * n = n'⁻¹ * (n * b) * b⁻¹ := by group
        _ = n'⁻¹ * (n' * b') * b⁻¹ := by rw [h1]
        _ = b' * b⁻¹ := by group
    have h3 : n'⁻¹ * n = 1 := D.B_inf_S (D.S.mul_mem (D.S.inv_mem hn') hn)
      (by rw [h2]; exact D.B.mul_mem hb' (D.B.inv_mem hb))
    have h4 : n = n' := by
      have : n = n' * (n'⁻¹ * n) := by group
      rw [this, h3, mul_one]
    subst h4
    have h5 : b = b' := by
      have : n⁻¹ * (n * b) = n⁻¹ * (n * b') := by rw [h1]
      simpa using this
    subst h5
    rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨h, hh⟩
    obtain ⟨s, hs, b, hb, rfl⟩ := D.mul_SB h hh
    exact ⟨(⟨s, hs⟩, ⟨b, hb⟩), rfl⟩
  have := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [Nat.card_prod] at this
  exact this.symm

theorem Good.no_inv_cent_B (hG : D.Good) {y : G} (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1)
    (hc : ∀ b ∈ D.B, y * b = b * y) : False := by
  obtain ⟨a, ha⟩ := hG.inv_conj_Z hy2 hy1
  have hyZa : y ∈ conjSub a D.Z := mem_conjSub.mpr ha
  have hBH : D.B ≤ conjSub a (M₁ ⊓ M₂) := fun b hb =>
    hG.cent_conj_le hyZa hy1 (hc b hb).symm
  have hNH : conjSub a D.S ≤ conjSub a (M₁ ⊓ M₂) := conjSub_mono a D.S_le_H
  have hdisj : ∀ x ∈ conjSub a D.S, x ∈ D.B → x = 1 := fun x hx hxB =>
    eq_one_of_pgroup_of_odd (F7.isPGroup_conjSub D.S_pgroup) D.B_odd hx hxB
  have hcard : Nat.card (conjSub a (M₁ ⊓ M₂)) = Nat.card (conjSub a D.S) * Nat.card D.B := by
    rw [card_conjSub, card_conjSub]; exact card_H
  have hdec := exists_mul_eq_of_card hNH hBH hdisj hcard
  have hconjB : ∀ b' ∈ conjSub a D.B, b' * y = y * b' := by
    intro b' hb'
    have hb'H : b' ∈ conjSub a (M₁ ⊓ M₂) := conjSub_mono a D.B_le hb'
    obtain ⟨n, hn, b, hb, rfl⟩ := hdec b' hb'H
    have h1 : n * y = y * n := commute_of_mem_conj hyZa hn
    have h2 : b * y = y * b := (hc b hb).symm
    calc n * b * y = n * (b * y) := by rw [mul_assoc]
      _ = n * (y * b) := by rw [h2]
      _ = (n * y) * b := by rw [mul_assoc]
      _ = (y * n) * b := by rw [h1]
      _ = y * (n * b) := by rw [mul_assoc]
  have hy'1 : a⁻¹ * y * a ≠ 1 := conj_ne_one' hy1
  have hBy' : ∀ b ∈ D.B, b * (a⁻¹ * y * a) = (a⁻¹ * y * a) * b := by
    intro b hb
    have := hconjB (a * b * a⁻¹) (mul_mem_conjSub hb)
    calc b * (a⁻¹ * y * a) = a⁻¹ * ((a * b * a⁻¹) * y) * a := by group
      _ = a⁻¹ * (y * (a * b * a⁻¹)) * a := by rw [this]
      _ = (a⁻¹ * y * a) * b := by group
  obtain ⟨x₁, hx₁, x₂, hx₂, hx₁1, hx₂1, hne⟩ := D.Z_big
  obtain ⟨b₁, hb₁, e₁⟩ := D.trans _ ha hy'1 x₁ hx₁ hx₁1
  obtain ⟨b₂, hb₂, e₂⟩ := D.trans _ ha hy'1 x₂ hx₂ hx₂1
  have e₁' : x₁ = a⁻¹ * y * a := by
    rw [← e₁, hBy' b₁ hb₁]; group
  have e₂' : x₂ = a⁻¹ * y * a := by
    rw [← e₂, hBy' b₂ hb₂]; group
  exact hne (e₁'.trans e₂'.symm)

end Weyl2

end L3Datum

namespace L3Datum

section CaseT

variable [Finite G] {M₁ M₂ : Subgroup G} {D : L3Datum M₁ M₂}

theorem Good.two_elt_conj_H (_hG : D.Good) {g y : G} (hy : y ∈ conjSub g (M₁ ⊓ M₂)) {k : ℕ}
    (hk : y ^ (2 ^ k) = 1) : y ∈ conjSub g D.S := by
  rw [mem_conjSub] at hy ⊢
  refine two_elt_mem_S hy (k := k) ?_
  have e := conj_pow (a := g⁻¹) (b := y) (i := 2 ^ k)
  have e' : (g⁻¹ * y * g) ^ (2 ^ k) = g⁻¹ * y ^ (2 ^ k) * g := by simpa using e
  rw [e', hk]; group

theorem Good.H_inf_Hg (hG : D.Good) {g : G} (hgW : g ∈ D.Wn)
    (hbot : D.S ⊓ conjSub g D.S = ⊥) : ∀ x ∈ (M₁ ⊓ M₂) ⊓ conjSub g (M₁ ⊓ M₂), x ∈ D.B := by
  intro x hx
  obtain ⟨hxH, hxg⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨s, hs, b, hb, rfl⟩ := D.mul_SB x hxH
  have hBg : D.B ≤ conjSub g (M₁ ⊓ M₂) := by
    have : conjSub g D.B = D.B := conjSub_eq_of_mem_normalizer hgW
    rw [← this]; exact conjSub_mono g D.B_le
  have hsg : s ∈ conjSub g (M₁ ⊓ M₂) := by
    have := (conjSub g (M₁ ⊓ M₂)).mul_mem hxg ((conjSub g (M₁ ⊓ M₂)).inv_mem (hBg hb))
    simpa [mul_assoc] using this
  obtain ⟨k, hk⟩ := exists_pow_two_eq_one D.S_pgroup hs
  have hsS : s ∈ conjSub g D.S := hG.two_elt_conj_H hsg hk
  have : s ∈ D.S ⊓ conjSub g D.S := Subgroup.mem_inf.mpr ⟨hs, hsS⟩
  rw [hbot, Subgroup.mem_bot] at this
  rw [this, one_mul]; exact hb

theorem Good.caseT1 (hG : D.Good) {g : G} (hgW : g ∈ D.Wn) (hbot : D.S ⊓ conjSub g D.S = ⊥) :
    ∃ w : G, w * w = 1 ∧ w * g⁻¹ ∈ D.B := by
  obtain ⟨z, hz, hz1⟩ := hG.ex
  obtain ⟨z', hz'⟩ : ∃ z', z' = g * z * g⁻¹ := ⟨_, rfl⟩
  have hz'Z : z' ∈ conjSub g D.Z := by rw [hz']; exact mul_mem_conjSub hz
  have hz'1 : z' ≠ 1 := by
    intro h; apply hz1
    have := congrArg (fun y => g⁻¹ * y * g) h
    simpa [hz', mul_assoc] using this
  have hzz : z * z = 1 := by rw [← pow_two]; exact D.Z_sq hz
  have hz'z' : z' * z' = 1 := by
    have : z' * z' = g * (z * z) * g⁻¹ := by rw [hz']; group
    rw [this, hzz]; group
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hz'i : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'z'
  obtain ⟨t, ht⟩ : ∃ t, t = z * z' := ⟨_, rfl⟩
  have ht_inv : t⁻¹ = z' * z := by rw [ht, mul_inv_rev, hz'i, hzi]
  have hzt : z * t * z = t⁻¹ := by
    rw [ht_inv, ht]
    calc z * (z * z') * z = (z * z) * z' * z := by group
      _ = z' * z := by rw [hzz, one_mul]
  have hz't : z' * t * z' = t⁻¹ := by
    rw [ht_inv, ht]
    calc z' * (z * z') * z' = z' * z * (z' * z') := by group
      _ = z' * z := by rw [hz'z', mul_one]
  have hztk : ∀ k : ℕ, z * t ^ k * z = (t ^ k)⁻¹ := by
    intro k
    have := conj_pow (a := z) (b := t) (i := k)
    rw [hzi] at this
    rw [← this, hzt, inv_pow]
  have hz'tk : ∀ k : ℕ, z' * t ^ k * z' = (t ^ k)⁻¹ := by
    intro k
    have := conj_pow (a := z') (b := t) (i := k)
    rw [hz'i] at this
    rw [← this, hz't, inv_pow]
  have hodd : Odd (orderOf t) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨N', hN'⟩ := hev
    have hN'pos : 0 < N' := by have := orderOf_pos t; omega
    obtain ⟨u, hu⟩ : ∃ u, u = t ^ N' := ⟨_, rfl⟩
    have hu2 : u * u = 1 := by
      rw [hu, ← pow_add]
      have := pow_orderOf_eq_one t
      rwa [hN'] at this
    have hu1 : u ≠ 1 := by
      rw [hu]; exact pow_ne_one_of_lt_orderOf (by omega) (by omega)
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    have hcz : u * z = z * u := by
      have := hztk N'
      rw [← hu, huinv] at this
      calc u * z = (z * u * z) * z := by rw [this]
        _ = z * u := by rw [mul_assoc, mul_assoc, hzz, mul_one]
    have hcz' : u * z' = z' * u := by
      have := hz'tk N'
      rw [← hu, huinv] at this
      calc u * z' = (z' * u * z') * z' := by rw [this]
        _ = z' * u := by rw [mul_assoc, mul_assoc, hz'z', mul_one]
    have huH : u ∈ M₁ ⊓ M₂ := hG.cent z hz hz1 u hcz
    have huS : u ∈ D.S := two_elt_mem_S huH (k := 1) (by simpa [pow_two] using hu2)
    have huH' : u ∈ conjSub g (M₁ ⊓ M₂) := hG.cent_conj_le hz'Z hz'1 hcz'
    have huS' : u ∈ conjSub g D.S :=
      hG.two_elt_conj_H huH' (k := 1) (by simpa [pow_two] using hu2)
    have : u ∈ D.S ⊓ conjSub g D.S := Subgroup.mem_inf.mpr ⟨huS, huS'⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hu1 this
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨w, hw⟩ : ∃ w, w = t ^ k * z := ⟨_, rfl⟩
  have hww : w * w = 1 := by
    rw [hw]
    calc t ^ k * z * (t ^ k * z) = t ^ k * (z * t ^ k * z) := by group
      _ = 1 := by rw [hztk k]; simp
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have h2k : t ^ (2 * k) = t⁻¹ := by
    have := pow_orderOf_eq_one t
    rw [hk, pow_succ] at this
    exact eq_inv_of_mul_eq_one_left this
  have hwzw : w * z * w = z' := by
    rw [hw]
    calc t ^ k * z * z * (t ^ k * z) = t ^ k * (z * z) * t ^ k * z := by group
      _ = t ^ k * t ^ k * z := by rw [hzz, mul_one]
      _ = t ^ (2 * k) * z := by rw [← pow_add]; ring_nf
      _ = z' := by rw [h2k, ht_inv, mul_assoc, hzz, mul_one]
  have hz'eq : z' = w * z * w⁻¹ := by rw [hwi]; exact hwzw.symm
  have hwS : conjSub w D.S = conjSub g D.S := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      rw [mem_conjSub] at hy
      have hxz : (w⁻¹ * y * w) * z = z * (w⁻¹ * y * w) := (D.mem_Z.mp hz).2 _ hy
      have hycomm : y * z' = z' * y := by
        calc y * z' = w * ((w⁻¹ * y * w) * z) * w⁻¹ := by rw [hz'eq]; group
          _ = w * (z * (w⁻¹ * y * w)) * w⁻¹ := by rw [hxz]
          _ = z' * y := by rw [hz'eq]; group
      obtain ⟨k₀, hk₀⟩ := exists_pow_two_eq_one D.S_pgroup hy
      have hyk : y ^ (2 ^ k₀) = 1 := by
        have e := conj_pow (a := w) (b := w⁻¹ * y * w) (i := 2 ^ k₀)
        rw [hk₀, show w * (w⁻¹ * y * w) * w⁻¹ = y by group] at e
        rw [e]; group
      exact hG.two_elt_conj hz'Z hz'1 hycomm hyk
    · rw [card_conjSub, card_conjSub]
  have hH : conjSub w (M₁ ⊓ M₂) = conjSub g (M₁ ⊓ M₂) := by
    rw [← normalizer_S_eq hG, ← conjSub_normalizer, ← conjSub_normalizer, hwS]
  have hH2 : conjSub w (conjSub g (M₁ ⊓ M₂)) = M₁ ⊓ M₂ := by
    rw [← hH, ← conjSub_mul, hww, conjSub_one]
  have hBg : D.B ≤ conjSub g (M₁ ⊓ M₂) := by
    have : conjSub g D.B = D.B := conjSub_eq_of_mem_normalizer hgW
    rw [← this]; exact conjSub_mono g D.B_le
  have hHg_B : (M₁ ⊓ M₂) ⊓ conjSub g (M₁ ⊓ M₂) = D.B := by
    apply le_antisymm
    · intro x hx; exact hG.H_inf_Hg hgW hbot x hx
    · intro x hx; exact Subgroup.mem_inf.mpr ⟨D.B_le hx, hBg hx⟩
  have hwB : conjSub w D.B = D.B := by
    rw [← hHg_B, conjSub_inf, hH, hH2, inf_comm]
  have hwW : w ∈ D.Wn := mem_normalizer_of_conjSub_eq hwB
  have hgw : g⁻¹ * w ∈ M₁ ⊓ M₂ := by
    rw [← normalizer_S_eq hG]
    apply mem_normalizer_of_conjSub_eq
    rw [conjSub_mul, hwS, conjSub_conjSub_inv]
  have hgwW : g⁻¹ * w ∈ D.Wn := D.Wn.mul_mem (D.Wn.inv_mem hgW) hwW
  have hgwB : g⁻¹ * w ∈ D.B := mem_B_of_mem_H_Wn hgw hgwW
  refine ⟨w, hww, ?_⟩
  have := (Subgroup.mem_normalizer_iff.mp hgW _).mp hgwB
  rwa [show g * (g⁻¹ * w) * g⁻¹ = w * g⁻¹ by group] at this

omit [Finite G] in
theorem s₁_W : D.s₁ ∈ D.Wn := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => D.s₁_norm x hx, fun hx => ?_⟩
  have := D.s₁_norm _ hx
  rwa [show D.s₁ * (D.s₁ * x * D.s₁⁻¹) * D.s₁⁻¹ = (D.s₁ * D.s₁) * x * (D.s₁ * D.s₁)⁻¹ by group,
    D.s₁_sq, inv_one, one_mul, mul_one] at this

omit [Finite G] in
theorem s₂_W : D.s₂ ∈ D.Wn := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => D.s₂_norm x hx, fun hx => ?_⟩
  have := D.s₂_norm _ hx
  rwa [show D.s₂ * (D.s₂ * x * D.s₂⁻¹) * D.s₂⁻¹ = (D.s₂ * D.s₂) * x * (D.s₂ * D.s₂)⁻¹ by group,
    D.s₂_sq, inv_one, one_mul, mul_one] at this

omit [Finite G] in
theorem comm_conj_Z {a x y : G} (hx : x ∈ conjSub a D.Z) (hy : y ∈ conjSub a D.Z) :
    x * y = y * x := by
  rw [mem_conjSub] at hx hy
  have := D.Z_comm hx hy
  have e1 : x * y = a * ((a⁻¹ * x * a) * (a⁻¹ * y * a)) * a⁻¹ := by group
  have e2 : y * x = a * ((a⁻¹ * y * a) * (a⁻¹ * x * a)) * a⁻¹ := by group
  rw [e1, e2, this]

theorem Good.fixedZ_of_le_Q (hG : D.Good) {Q M : Subgroup G} {s : G}
    (hcov : ∀ x ∈ Q, x ≠ 1 → ∃ m ∈ M, m * x * m⁻¹ ∈ D.Z)
    (hfix : ∀ m ∈ M, NormedBy D.B (conjSub m D.Z) →
      conjSub m D.Z = D.Z ∨ conjSub m D.Z = conjSub s D.Z)
    {a : G} (hYQ : conjSub a D.Z ≤ Q) (hYB : NormedBy D.B (conjSub a D.Z)) :
    conjSub a D.Z = D.Z ∨ conjSub a D.Z = conjSub s D.Z := by
  obtain ⟨m, hm, hmeq⟩ := hG.members_in_Q hcov hYQ
  rw [← hmeq] at hYB ⊢
  exact hfix m hm hYB

omit [Finite G] in
theorem Good.conj_Z_eq_Z (hG : D.Good) {g : G} (h : conjSub g D.Z = D.Z) : g ∈ M₁ ⊓ M₂ := by
  apply hG.normalizer_Z
  intro x hx
  have : g * x * g⁻¹ ∈ conjSub g D.Z := mul_mem_conjSub hx
  rwa [h] at this

theorem Good.inv_coset (hG : D.Good) {g s : G} (hg : g ∈ D.Wn) (hs : s ∈ D.Wn)
    (h : conjSub g D.Z = conjSub s D.Z) : s * g⁻¹ ∈ D.B := by
  have h1 : conjSub (s⁻¹ * g) D.Z = D.Z := by
    rw [conjSub_mul, h, conjSub_conjSub_inv]
  have h2 : s⁻¹ * g ∈ M₁ ⊓ M₂ := hG.conj_Z_eq_Z h1
  have h3 : s⁻¹ * g ∈ D.Wn := D.Wn.mul_mem (D.Wn.inv_mem hs) hg
  have h4 : s⁻¹ * g ∈ D.B := mem_B_of_mem_H_Wn h2 h3
  have h5 := (Subgroup.mem_normalizer_iff.mp hs _).mp (D.B.inv_mem h4)
  rwa [show s * (s⁻¹ * g)⁻¹ * s⁻¹ = s * g⁻¹ by group] at h5

theorem Good.caseT2 (hG : D.Good) {g : G} (hgW : g ∈ D.Wn) (hg : g ∉ M₁ ⊓ M₂) {Q : Subgroup G}
    (hQ : Q = D.Q₁ ∨ Q = D.Q₂) (hSP : D.S ⊓ conjSub g D.S = Q)
    (hQc : Q = conjSub g D.Q₁ ∨ Q = conjSub g D.Q₂) : ∃ w : G, w * w = 1 ∧ w * g⁻¹ ∈ D.B := by
  have hZgQ : conjSub g D.Z ≤ Q := by
    rcases hQc with h | h
    · rw [h]; exact conjSub_mono g D.Z_le_Q₁
    · rw [h]; exact conjSub_mono g D.Z_le_Q₂
  have hgB : NormedBy D.B (conjSub g D.Z) := normedBy_conj normedBy_Z hgW
  have hne : conjSub g D.Z ≠ D.Z := fun h => hg (hG.conj_Z_eq_Z h)
  rcases hQ with rfl | rfl
  · rcases hG.fixedZ_of_le_Q D.cov₁ D.fix₁ hZgQ hgB with h | h
    · exact absurd h hne
    · exact ⟨D.s₁, D.s₁_sq, hG.inv_coset hgW s₁_W h⟩
  · rcases hG.fixedZ_of_le_Q D.cov₂ D.fix₂ hZgQ hgB with h | h
    · exact absurd h hne
    · exact ⟨D.s₂, D.s₂_sq, hG.inv_coset hgW s₂_W h⟩

theorem Good.Y_le_Q (hG : D.Good) {a : G} (hY : conjSub a D.Z ≤ D.S) (hne : conjSub a D.Z ≠ D.Z) :
    conjSub a D.Z ≤ D.Q₁ ∨ conjSub a D.Z ≤ D.Q₂ := by
  obtain ⟨y, hy, hy1⟩ := Z_ne_one_mem hG a
  have hyS : y ∈ D.S := hY hy
  have hy2 : y ^ 2 = 1 := sq_of_conj_sq (D.Z_sq (mem_conjSub.mp hy))
  have hyZ : y ∉ D.Z := by
    intro hyZ
    apply hne
    have := hG.TI (a := a) (b := 1) (x := y) hy (by rw [conjSub_one]; exact hyZ) hy1
    rwa [conjSub_one] at this
  rcases D.frame.inv y hyS hy2 hy1 with h | h
  · left
    intro u hu
    exact D.frame.cent₁ y h hyZ u (hY hu) (comm_conj_Z hu hy)
  · right
    intro u hu
    exact D.frame.cent₂ y h hyZ u (hY hu) (comm_conj_Z hu hy)

theorem Good.caseT3 (hG : D.Good) {g a : G} (hgW : g ∈ D.Wn)
    (hSP : D.S ⊓ conjSub g D.S = conjSub a D.Z) (hne : conjSub a D.Z ≠ D.Z) :
    D.S ⊓ conjSub g D.S = conjSub D.s₁ D.Z ∨ D.S ⊓ conjSub g D.S = conjSub D.s₂ D.Z := by
  have hYS : conjSub a D.Z ≤ D.S := hSP ▸ inf_le_left
  have hYB : NormedBy D.B (conjSub a D.Z) := by
    rw [← hSP]
    intro b hb x hx
    obtain ⟨hxS, hxP⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨normedBy_S b hb x hxS, normedBy_conj normedBy_S hgW b hb x hxP⟩
  rw [hSP]
  rcases hG.Y_le_Q hYS hne with h | h
  · rcases hG.fixedZ_of_le_Q D.cov₁ D.fix₁ h hYB with h' | h'
    · exact absurd h' hne
    · exact Or.inl h'
  · rcases hG.fixedZ_of_le_Q D.cov₂ D.fix₂ h hYB with h' | h'
    · exact absurd h' hne
    · exact Or.inr h'

theorem Good.inj_aux (hG : D.Good) {Qa Qb Mb : Subgroup G} {sa sb : G}
    (hF : Frame D.S Qa Qb) (hnc : ∀ x : G, conjSub x Qa ≠ Qb)
    (hnc' : ∀ x : G, conjSub x Qb ≠ Qa) (hZa : D.Z ≤ Qa) (hZb : D.Z ≤ Qb)
    (hsa : conjSub sa Qa = Qa) (hsaW : sa ∈ D.Wn)
    (hcovb : ∀ x ∈ Qb, x ≠ 1 → ∃ m ∈ Mb, m * x * m⁻¹ ∈ D.Z)
    (hfixb : ∀ m ∈ Mb, NormedBy D.B (conjSub m D.Z) →
      conjSub m D.Z = D.Z ∨ conjSub m D.Z = conjSub sb D.Z)
    {g : G} (hgW : g ∈ D.Wn) (hSP : D.S ⊓ conjSub g D.S = conjSub sa D.Z)
    (hne : conjSub sa D.Z ≠ conjSub g D.Z) :
    conjSub g D.Z = conjSub (sa * sb) D.Z := by
  have hY_le_P : conjSub sa D.Z ≤ conjSub g D.S := hSP ▸ inf_le_right
  obtain ⟨y, hy, hy1⟩ := Z_ne_one_mem hG sa
  have hyP : y ∈ conjSub g D.S := hY_le_P hy
  have hy2 : y ^ 2 = 1 := sq_of_conj_sq (D.Z_sq (mem_conjSub.mp hy))
  have hFg := hF.conj g
  have hyZg : y ∉ conjSub g D.Z := fun hyZg => hne (hG.TI hy hyZg hy1)
  have hyZg' : y ∉ centerOf (conjSub g D.S) := by rw [centerOf_conjSub]; exact hyZg
  have hZg_le_S_imp : conjSub g D.Z ≤ D.S → False := by
    intro hle
    apply hne
    have hle' : conjSub g D.Z ≤ conjSub sa D.Z := by
      rw [← hSP]; exact le_inf hle (conjSub_mono g D.Z_le_S)
    exact (Subgroup.eq_of_le_of_card_ge hle' (by rw [card_conjSub, card_conjSub])).symm
  have hYcomm : ∀ u ∈ conjSub sa D.Z, u * y = y * u := fun u hu => comm_conj_Z hu hy
  have hZgb : conjSub g D.Z ≤ conjSub g Qb := conjSub_mono g hZb
  have hZga : conjSub g D.Z ≤ conjSub g Qa := conjSub_mono g hZa
  have hYQb : conjSub sa D.Z ≤ conjSub g Qb := by
    rcases hFg.inv y hyP hy2 hy1 with h | h
    · exfalso
      have hYle : conjSub sa D.Z ≤ conjSub g Qa := fun u hu =>
        hFg.cent₁ y h hyZg' u (hY_le_P hu) (hYcomm u hu)
      have hYQa : conjSub sa D.Z ≤ conjSub 1 Qa := by
        rw [conjSub_one, ← hsa]; exact conjSub_mono sa hZa
      have := hG.Q_unique hF hnc (c := sa) (a := g) (b := 1) hYle hYQa
      rw [conjSub_one] at this
      apply hZg_le_S_imp
      calc conjSub g D.Z ≤ conjSub g Qa := hZga
        _ = Qa := this
        _ ≤ D.S := hF.Q₁_le
    · exact fun u hu => hFg.cent₂ y h hyZg' u (hY_le_P hu) (hYcomm u hu)
  have hYQb' : conjSub sa D.Z ≤ conjSub sa Qb := conjSub_mono sa hZb
  have hQeq : conjSub g Qb = conjSub sa Qb :=
    hG.Q_unique hF.symm hnc' (c := sa) hYQb hYQb'
  have hZ'le : conjSub (sa⁻¹ * g) D.Z ≤ Qb := by
    rw [conjSub_mul]
    have : conjSub g D.Z ≤ conjSub sa Qb := hQeq ▸ hZgb
    exact (le_conjSub_iff sa).mp this
  have hsg : sa⁻¹ * g ∈ D.Wn := D.Wn.mul_mem (D.Wn.inv_mem hsaW) hgW
  have hZ'B : NormedBy D.B (conjSub (sa⁻¹ * g) D.Z) := normedBy_conj normedBy_Z hsg
  rcases hG.fixedZ_of_le_Q hcovb hfixb hZ'le hZ'B with h | h
  · exfalso
    rw [conjSub_mul] at h
    have := congrArg (conjSub sa) h
    rw [conjSub_inv_conjSub] at this
    exact hne this.symm
  · rw [conjSub_mul] at h
    have := congrArg (conjSub sa) h
    rw [conjSub_inv_conjSub] at this
    rw [this, ← conjSub_mul]

theorem Good.inj₁ (hG : D.Good) {g : G} (hgW : g ∈ D.Wn)
    (hSP : D.S ⊓ conjSub g D.S = conjSub D.s₁ D.Z) (hne : conjSub D.s₁ D.Z ≠ conjSub g D.Z) :
    conjSub g D.Z = conjSub (D.s₁ * D.s₂) D.Z :=
  hG.inj_aux D.frame hG.Q_not_conj hG.Q_not_conj' D.Z_le_Q₁ D.Z_le_Q₂
    (conjSub_Q₁_eq D.s₁_mem) s₁_W D.cov₂ D.fix₂ hgW hSP hne

theorem Good.inj₂ (hG : D.Good) {g : G} (hgW : g ∈ D.Wn)
    (hSP : D.S ⊓ conjSub g D.S = conjSub D.s₂ D.Z) (hne : conjSub D.s₂ D.Z ≠ conjSub g D.Z) :
    conjSub g D.Z = conjSub (D.s₂ * D.s₁) D.Z :=
  hG.inj_aux D.frame.symm hG.Q_not_conj' hG.Q_not_conj D.Z_le_Q₂ D.Z_le_Q₁
    (conjSub_Q₂_eq D.s₂_mem) s₂_W D.cov₁ D.fix₁ hgW hSP hne

end CaseT

end L3Datum

namespace L3Datum

section Count

variable [Finite G] {M₁ M₂ : Subgroup G} {D : L3Datum M₁ M₂}

omit [Finite G] in
theorem r_W : D.s₁ * D.s₂ ∈ D.Wn := D.Wn.mul_mem s₁_W s₂_W

omit [Finite G] in
theorem rpow_W (j : ℕ) : (D.s₁ * D.s₂) ^ j ∈ D.Wn := D.Wn.pow_mem r_W j

omit [Finite G] in
theorem B_le_Wn : D.B ≤ D.Wn := Subgroup.le_normalizer

omit [Finite G] in
theorem sq_mem_B {g w : G} (hgW : g ∈ D.Wn) (hww : w * w = 1) (hwb : w * g⁻¹ ∈ D.B) :
    g * g ∈ D.B := by
  have hwW : w ∈ D.Wn := by
    have : w = (w * g⁻¹) * g := by group
    rw [this]; exact D.Wn.mul_mem (B_le_Wn hwb) hgW
  have hw' : w * (w * g⁻¹)⁻¹ * w⁻¹ ∈ D.B :=
    (Subgroup.mem_normalizer_iff.mp hwW _).mp (D.B.inv_mem hwb)
  have : g * g = (w * g⁻¹)⁻¹ * (w * (w * g⁻¹)⁻¹ * w⁻¹) := by
    have e : (w * g⁻¹)⁻¹ * (w * (w * g⁻¹)⁻¹ * w⁻¹) = g * g * (w * w)⁻¹ := by group
    rw [e, hww, inv_one, mul_one]
  rw [this]
  exact D.B.mul_mem (D.B.inv_mem hwb) hw'

theorem Good.type_of_good (hG : D.Good) {n : ℕ} (hn : 0 < n)
    (hnB : (D.s₁ * D.s₂) ^ n ∈ D.B) (hmin : ∀ k, 0 < k → k < n → (D.s₁ * D.s₂) ^ k ∉ D.B)
    {j : ℕ} (hj : 0 < j) (hjn : j < n) (hgood : ¬ n ∣ 2 * j) :
    conjSub ((D.s₁ * D.s₂) ^ j) D.Z = conjSub (D.s₁ * D.s₂) D.Z ∨
    conjSub ((D.s₁ * D.s₂) ^ j) D.Z = conjSub (D.s₂ * D.s₁) D.Z := by
  have hiff := pow_mem_iff_dvd hn hnB hmin
  have hgW : (D.s₁ * D.s₂) ^ j ∈ D.Wn := rpow_W j
  have hgB : (D.s₁ * D.s₂) ^ j ∉ D.B := fun h => by
    have := (hiff j).mp h
    exact absurd (Nat.le_of_dvd hj this) (by omega)
  have hgH : (D.s₁ * D.s₂) ^ j ∉ M₁ ⊓ M₂ := fun h => hgB (mem_B_of_mem_H_Wn h hgW)
  have hg2 : (D.s₁ * D.s₂) ^ j * (D.s₁ * D.s₂) ^ j ∉ D.B := by
    intro h
    apply hgood
    have : (D.s₁ * D.s₂) ^ (2 * j) ∈ D.B := by rw [two_mul, pow_add]; exact h
    exact (hiff (2 * j)).mp this
  rcases hG.trichotomy hgH with hbot | ⟨Q, hQ, hSP, hQc⟩ | ⟨a, hSP, hne1, hne2⟩
  · exfalso
    obtain ⟨w, hww, hwb⟩ := hG.caseT1 hgW hbot
    exact hg2 (sq_mem_B hgW hww hwb)
  · exfalso
    obtain ⟨w, hww, hwb⟩ := hG.caseT2 hgW hgH hQ hSP hQc
    exact hg2 (sq_mem_B hgW hww hwb)
  · rcases hG.caseT3 hgW hSP hne1 with h | h
    · left
      exact hG.inj₁ hgW h (by rw [← h, hSP]; exact hne2)
    · right
      exact hG.inj₂ hgW h (by rw [← h, hSP]; exact hne2)

theorem Good.inj_type (hG : D.Good) {n : ℕ} (_hn : 0 < n)
    (hmin : ∀ k, 0 < k → k < n → (D.s₁ * D.s₂) ^ k ∉ D.B) {j j' : ℕ} (hj : 0 < j) (hjj' : j < j')
    (hj'n : j' < n) :
    conjSub ((D.s₁ * D.s₂) ^ j) D.Z ≠ conjSub ((D.s₁ * D.s₂) ^ j') D.Z := by
  intro h
  have h1 : conjSub (((D.s₁ * D.s₂) ^ j')⁻¹ * (D.s₁ * D.s₂) ^ j) D.Z = D.Z := by
    rw [conjSub_mul, h, conjSub_conjSub_inv]
  have h2 : ((D.s₁ * D.s₂) ^ j')⁻¹ * (D.s₁ * D.s₂) ^ j ∈ M₁ ⊓ M₂ := hG.conj_Z_eq_Z h1
  have h3 : ((D.s₁ * D.s₂) ^ j')⁻¹ * (D.s₁ * D.s₂) ^ j ∈ D.Wn :=
    D.Wn.mul_mem (D.Wn.inv_mem (rpow_W j')) (rpow_W j)
  have h4 := mem_B_of_mem_H_Wn h2 h3
  have h5 : ((D.s₁ * D.s₂) ^ j')⁻¹ * (D.s₁ * D.s₂) ^ j = ((D.s₁ * D.s₂) ^ (j' - j))⁻¹ := by
    have : (D.s₁ * D.s₂) ^ j' = (D.s₁ * D.s₂) ^ j * (D.s₁ * D.s₂) ^ (j' - j) := by
      rw [← pow_add]; congr 1; omega
    rw [this]; group
  rw [h5] at h4
  exact hmin (j' - j) (by omega) (by omega) (by have := D.B.inv_mem h4; simpa using this)

theorem Good.n_le_four (hG : D.Good) {n : ℕ} (hn : 0 < n) (hnB : (D.s₁ * D.s₂) ^ n ∈ D.B)
    (hmin : ∀ k, 0 < k → k < n → (D.s₁ * D.s₂) ^ k ∉ D.B) : n ≤ 4 := by
  by_contra h5
  have h5' : 5 ≤ n := by omega
  have no3 : ∀ j₁ j₂ j₃ : ℕ, 0 < j₁ → j₁ < j₂ → j₂ < j₃ → j₃ < n → ¬ n ∣ 2 * j₁ → ¬ n ∣ 2 * j₂ →
      ¬ n ∣ 2 * j₃ → False := by
    intro j₁ j₂ j₃ h1 h12 h23 h3n g1 g2 g3
    have t1 := hG.type_of_good hn hnB hmin h1 (by omega) g1
    have t2 := hG.type_of_good hn hnB hmin (by omega : 0 < j₂) (by omega) g2
    have t3 := hG.type_of_good hn hnB hmin (by omega : 0 < j₃) h3n g3
    have i12 := hG.inj_type hn hmin h1 h12 (by omega)
    have i13 := hG.inj_type hn hmin h1 (by omega : j₁ < j₃) h3n
    have i23 := hG.inj_type hn hmin (by omega : 0 < j₂) h23 h3n
    rcases t1 with a | a <;> rcases t2 with b | b <;> rcases t3 with c | c
    · exact i12 (a.trans b.symm)
    · exact i12 (a.trans b.symm)
    · exact i13 (a.trans c.symm)
    · exact i23 (b.trans c.symm)
    · exact i23 (b.trans c.symm)
    · exact i13 (a.trans c.symm)
    · exact i12 (a.trans b.symm)
    · exact i12 (a.trans b.symm)
  by_cases h6 : n = 6
  · subst h6
    exact no3 1 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
      (by decide) (by decide)
  · refine no3 1 2 3 (by norm_num) (by norm_num) (by norm_num) (by omega) ?_ ?_ ?_
    · intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    · intro h; have := Nat.le_of_dvd (by norm_num) h; omega
    · intro h
      have := Nat.le_of_dvd (by norm_num) h
      have h56 : n = 5 := by omega
      subst h56
      omega

theorem Good.r_cube_mem_B (hG : D.Good) : (D.s₁ * D.s₂) ^ 3 ∈ D.B := by
  obtain ⟨n, hn, hnB, hmin⟩ := exists_min_pow (D.s₁ * D.s₂) D.B
  have h4 := hG.n_le_four hn hnB hmin
  have hn1 : n ≠ 1 := by
    intro h
    subst h
    rw [pow_one] at hnB
    apply D.s₁_not
    have : D.s₁ = (D.s₁ * D.s₂) * D.s₂⁻¹ := by group
    rw [this]
    exact M₂.mul_mem (D.B_le hnB).2 (M₂.inv_mem D.s₂_mem)
  have hodd : ¬ Even n := fun hev =>
    no_even_of_rot r_W D.rot hn hnB hmin h4 hev (fun y hy hy1 hc =>
      hG.no_inv_cent_B (by rw [pow_two]; exact hy) hy1 hc)
  have hn3 : n = 3 := by
    rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega
  rw [hn3] at hnB
  exact hnB

end Count

end L3Datum

end CFSG.Quasithin.H13.F431.L3
