module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S29

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

structure ScalarTriple (r : ℕ) (A W N Z P : Subgroup G) (y : G) (s : ℕ) : Prop where
  prime : r.Prime
  elem : IsElemAbelian r A
  card_A : Nat.card A = r ^ 3
  inf_eq_bot : Z ⊓ P = ⊥
  Z_le : Z ≤ A
  P_le : P ≤ A
  card_Z : Nat.card Z = r
  card_P : Nat.card P = r ^ 2
  W_le : W ≤ normalizer (A : Set G)
  N_le : N ≤ W
  N_P : N ≤ normalizer (P : Set G)
  N_Z : ∀ n ∈ N, ∀ z ∈ Z, n * z = z * n
  irr : ∀ B : Subgroup G, B ≤ P → N ≤ normalizer (B : Set G) → B = ⊥ ∨ B = P
  y_mem : y ∈ N
  y_P : ∀ p ∈ P, y * p * y⁻¹ = p ^ s
  s_ne : s % r ≠ 1

namespace ScalarTriple

variable {r s : ℕ} {A W N Z P : Subgroup G} {y : G} (h : ScalarTriple r A W N Z P y s)

include h

theorem comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (h.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem pow_eq_one : ∀ a ∈ A, a ^ r = 1 := h.elem.2

theorem conj_mem {w : G} (hw : w ∈ W) {a : G} (ha : a ∈ A) : w * a * w⁻¹ ∈ A :=
  (mem_normalizer_iff.1 (h.W_le hw) a).1 ha

theorem conj_inv_mem {w : G} (hw : w ∈ W) {a : G} (ha : a ∈ A) : w⁻¹ * a * w ∈ A := by
  have := h.conj_mem (W.inv_mem hw) ha
  simpa using this

theorem one_lt : 1 < r := h.prime.one_lt

theorem exists_mul [Finite G] : ∀ a ∈ A, ∃ z ∈ Z, ∃ p ∈ P, a = z * p := by
  have hc : ∀ x ∈ Z, ∀ k ∈ P, x * k = k * x := fun x hx k hk => h.comm x (h.Z_le hx) k (h.P_le hk)
  have hsup : Z ⊔ P = A := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le h.Z_le h.P_le) ?_
    rw [card_sup_of_commute_of_disjoint hc h.inf_eq_bot, h.card_Z, h.card_P, h.card_A]
    ring_nf
    exact le_rfl
  intro a ha
  rw [← hsup] at ha
  obtain ⟨z, hz, p, hp, e⟩ := exists_mul_of_mem_sup_of_commute hc ha
  exact ⟨z, hz, p, hp, e⟩

theorem eq_Z_of_le [Finite G] {B : Subgroup G} (hBZ : B ≤ Z) (hB : B ≠ ⊥) : B = Z := by
  have hdvd : Nat.card B ∣ Nat.card Z := Subgroup.card_dvd_of_le hBZ
  rw [h.card_Z] at hdvd
  have h1 : Nat.card B ≠ 1 := fun e => hB (Subgroup.eq_bot_of_card_eq B e)
  have h3 : Nat.card B = r := ((Nat.dvd_prime h.prime).1 hdvd).resolve_left h1
  exact Subgroup.eq_of_le_of_card_ge hBZ (by rw [h.card_Z, h3])

theorem eq_one_of_pow_s_eq {p : G} (hp : p ∈ P) (hps : p ^ s = p) : p = 1 := by
  by_contra hp1
  have hpr : p ^ r = 1 := h.pow_eq_one p (h.P_le hp)
  have hord : orderOf p = r := by
    rcases (Nat.dvd_prime h.prime).1 (orderOf_dvd_of_pow_eq_one hpr) with h0 | h0
    · exact absurd (orderOf_eq_one_iff.1 h0) hp1
    · exact h0
  have h1 : p ^ (s % r) = p ^ 1 := by
    rw [← hord, pow_mod_orderOf, hps, pow_one]
  have h2 := pow_injOn_Iio_orderOf (x := p) (by rw [hord]; exact Nat.mod_lt _ h.prime.pos)
    (by rw [hord]; exact h.one_lt) h1
  exact h.s_ne h2

theorem le_Z_of_inf_eq_bot [Finite G] {B : Subgroup G} (hBA : B ≤ A)
    (hNB : N ≤ normalizer (B : Set G)) (hB : B ⊓ P = ⊥) : B ≤ Z := by
  intro b hb
  obtain ⟨z, hz, p, hp, rfl⟩ := h.exists_mul b (hBA hb)
  have hpA : p ∈ A := h.P_le hp
  have hzA : z ∈ A := h.Z_le hz
  have hcomm : ∀ n ∈ N, n * p * n⁻¹ = p := by
    intro n hn
    have h1 : n * (z * p) * n⁻¹ ∈ B := (mem_normalizer_iff.1 (hNB hn) (z * p)).1 hb
    have hnz : n * z * n⁻¹ = z := by rw [h.N_Z n hn z hz]; group
    have hnp : n * p * n⁻¹ ∈ P := (mem_normalizer_iff.1 (h.N_P hn) p).1 hp
    have hnpA : n * p * n⁻¹ ∈ A := h.P_le hnp
    have e1 : n * (z * p) * n⁻¹ = z * (n * p * n⁻¹) :=
      calc n * (z * p) * n⁻¹ = (n * z * n⁻¹) * (n * p * n⁻¹) := by group
        _ = z * (n * p * n⁻¹) := by rw [hnz]
    have hzqp : z * ((n * p * n⁻¹) * p⁻¹) = ((n * p * n⁻¹) * p⁻¹) * z :=
      h.comm z hzA _ (A.mul_mem hnpA (A.inv_mem hpA))
    have e2 : n * (z * p) * n⁻¹ * (z * p)⁻¹ = (n * p * n⁻¹) * p⁻¹ :=
      calc n * (z * p) * n⁻¹ * (z * p)⁻¹ = z * ((n * p * n⁻¹) * p⁻¹) * z⁻¹ := by rw [e1]; group
        _ = (((n * p * n⁻¹) * p⁻¹) * z) * z⁻¹ := by rw [hzqp]
        _ = (n * p * n⁻¹) * p⁻¹ := by group
    have h2 : (n * p * n⁻¹) * p⁻¹ ∈ B := by
      have := B.mul_mem h1 (B.inv_mem hb)
      rwa [e2] at this
    have h3 : (n * p * n⁻¹) * p⁻¹ ∈ B ⊓ P := ⟨h2, P.mul_mem hnp (P.inv_mem hp)⟩
    rw [hB, Subgroup.mem_bot] at h3
    exact mul_inv_eq_one.1 h3
  have hzp : Subgroup.zpowers p ≤ P := Subgroup.zpowers_le.2 hp
  have hN : N ≤ normalizer ((Subgroup.zpowers p : Subgroup G) : Set G) := by
    intro n hn
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    have hpn : p * n = n * p := by
      have := hcomm n hn
      calc p * n = (n * p * n⁻¹) * n := by rw [this]
        _ = n * p := by group
    exact (Commute.zpow_left (show Commute p n from hpn) k).eq
  have hp1 : p = 1 := by
    rcases h.irr _ hzp hN with h0 | h0
    · exact Subgroup.zpowers_eq_bot.1 h0
    · exfalso
      have h9 : Nat.card P ≤ r := by
        rw [← h0, Nat.card_zpowers]
        exact Nat.le_of_dvd h.prime.pos (orderOf_dvd_of_pow_eq_one (h.pow_eq_one p hpA))
      rw [h.card_P] at h9
      have := h.one_lt
      nlinarith
  rw [hp1, mul_one]
  exact hz

theorem y_Z : ∀ z ∈ Z, y * z * y⁻¹ = z := fun z hz => by
  rw [h.N_Z y h.y_mem z hz]; group

theorem fixed_iff [Finite G] {a : G} (ha : a ∈ A) : y * a * y⁻¹ = a ↔ a ∈ Z := by
  constructor
  · intro hfix
    obtain ⟨z, hz, p, hp, rfl⟩ := h.exists_mul a ha
    have e : y * (z * p) * y⁻¹ = z * p ^ s := by
      calc y * (z * p) * y⁻¹ = (y * z * y⁻¹) * (y * p * y⁻¹) := by group
        _ = z * p ^ s := by rw [h.y_Z z hz, h.y_P p hp]
    rw [e] at hfix
    have hps : p ^ s = p := mul_left_cancel hfix
    rw [h.eq_one_of_pow_s_eq hp hps, mul_one]
    exact hz
  · intro haZ
    exact h.y_Z a haZ

theorem y_quot [Finite G] : ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ P := by
  intro a ha
  obtain ⟨z, hz, p, hp, rfl⟩ := h.exists_mul a ha
  have hzA : z ∈ A := h.Z_le hz
  have hpA : p ∈ A := h.P_le hp
  have hpsA : p ^ s ∈ A := A.pow_mem hpA s
  have e1 : y * (z * p) * y⁻¹ = z * p ^ s :=
    calc y * (z * p) * y⁻¹ = (y * z * y⁻¹) * (y * p * y⁻¹) := by group
      _ = z * p ^ s := by rw [h.y_Z z hz, h.y_P p hp]
  have hc := h.comm z hzA (p ^ s * p⁻¹) (A.mul_mem hpsA (A.inv_mem hpA))
  have e2 : y * (z * p) * y⁻¹ * (z * p)⁻¹ = p ^ s * p⁻¹ := by
    rw [e1]
    calc z * p ^ s * (z * p)⁻¹ = (z * (p ^ s * p⁻¹)) * z⁻¹ := by group
      _ = ((p ^ s * p⁻¹) * z) * z⁻¹ := by rw [hc]
      _ = p ^ s * p⁻¹ := by group
  rw [e2]
  exact P.mul_mem (P.pow_mem hp s) (P.inv_mem hp)

theorem normalizes_Z_of_normalizes_P [Finite G] (hWP : W ≤ normalizer (P : Set G))
    (hcop : ∀ g ∈ W, g ^ r ∈ centralizer (A : Set G) → g ∈ centralizer (A : Set G)) :
    W ≤ normalizer (Z : Set G) := by
  have hyW : y ∈ W := h.N_le h.y_mem
  intro w hw
  have hw' : w⁻¹ ∈ W := W.inv_mem hw
  have hPw : ∀ p ∈ P, w * p * w⁻¹ ∈ P := fun p hp => (mem_normalizer_iff.1 (hWP hw) p).1 hp
  have hPw' : ∀ p ∈ P, w⁻¹ * p * w ∈ P := fun p hp => by
    have := (mem_normalizer_iff.1 (hWP hw') p).1 hp
    simpa using this
  obtain ⟨y', hy'⟩ : ∃ y' : G, y' = w * y * w⁻¹ := ⟨_, rfl⟩
  have hy'W : y' ∈ W := hy' ▸ W.mul_mem (W.mul_mem hw hyW) hw'
  have hy'P : ∀ p ∈ P, y' * p * y'⁻¹ ∈ P := fun p hp => (mem_normalizer_iff.1 (hWP hy'W) p).1 hp
  have hy'P' : ∀ p ∈ P, y'⁻¹ * p * y' ∈ P := fun p hp => by
    have := (mem_normalizer_iff.1 (hWP (W.inv_mem hy'W)) p).1 hp
    simpa using this
  have hY1' : ∀ p ∈ P, y' * p * y'⁻¹ = p ^ s := by
    intro p hp
    have h1 := h.y_P _ (hPw' p hp)
    calc y' * p * y'⁻¹ = w * (y * (w⁻¹ * p * w) * y⁻¹) * w⁻¹ := by rw [hy']; group
      _ = w * (w⁻¹ * p * w) ^ s * w⁻¹ := by rw [h1]
      _ = (w * (w⁻¹ * p * w) * w⁻¹) ^ s := (conj_pow (a := w) (b := w⁻¹ * p * w) (i := s)).symm
      _ = p ^ s := by congr 1; group
  have hY3' : ∀ a ∈ A, y' * a * y'⁻¹ * a⁻¹ ∈ P := by
    intro a ha
    have h1 := h.y_quot _ (h.conj_mem hw' ha)
    have e : y' * a * y'⁻¹ * a⁻¹ = w * (y * (w⁻¹ * a * w) * y⁻¹ * (w⁻¹ * a * w)⁻¹) * w⁻¹ := by
      rw [hy']; group
    rw [e]
    simpa using hPw _ h1
  obtain ⟨g, hg⟩ : ∃ g : G, g = y * y'⁻¹ := ⟨_, rfl⟩
  have hgW : g ∈ W := hg ▸ W.mul_mem hyW (W.inv_mem hy'W)
  have hq : ∀ p ∈ P, (y'⁻¹ * p * y') ^ s = p := by
    intro p hp
    have := hY1' _ (hy'P' p hp)
    rw [← this]
    group
  have hgP : ∀ p ∈ P, g * p * g⁻¹ = p := by
    intro p hp
    calc g * p * g⁻¹ = y * (y'⁻¹ * p * y') * y⁻¹ := by rw [hg]; group
      _ = (y'⁻¹ * p * y') ^ s := h.y_P _ (hy'P' p hp)
      _ = p := hq p hp
  have hgA : ∀ a ∈ A, g * a * g⁻¹ * a⁻¹ ∈ P := by
    intro a ha
    have ha' : y'⁻¹ * a * y' ∈ A := by
      have := h.conj_inv_mem hy'W ha
      exact this
    obtain ⟨d, hd⟩ : ∃ d : G, d = (y'⁻¹ * a * y') * a⁻¹ := ⟨_, rfl⟩
    have hdP : d ∈ P := by
      have h1 := hY3' _ ha'
      have e : y' * (y'⁻¹ * a * y') * y'⁻¹ * (y'⁻¹ * a * y')⁻¹ = a * (y'⁻¹ * a * y')⁻¹ := by group
      rw [e] at h1
      have h2 := P.inv_mem h1
      have e2 : (a * (y'⁻¹ * a * y')⁻¹)⁻¹ = (y'⁻¹ * a * y') * a⁻¹ := by group
      rw [e2] at h2
      rw [hd]
      exact h2
    obtain ⟨c, hc⟩ : ∃ c : G, c = y * a * y⁻¹ * a⁻¹ := ⟨_, rfl⟩
    have hcP : c ∈ P := hc ▸ h.y_quot a ha
    have e1 : y'⁻¹ * a * y' = d * a := by rw [hd]; group
    have e2 : y * a * y⁻¹ = c * a := by rw [hc]; group
    have e3 : g * a * g⁻¹ * a⁻¹ = d ^ s * c := by
      calc g * a * g⁻¹ * a⁻¹ = y * (y'⁻¹ * a * y') * y⁻¹ * a⁻¹ := by rw [hg]; group
        _ = y * (d * a) * y⁻¹ * a⁻¹ := by rw [e1]
        _ = (y * d * y⁻¹) * (y * a * y⁻¹) * a⁻¹ := by group
        _ = d ^ s * (c * a) * a⁻¹ := by rw [h.y_P d hdP, e2]
        _ = d ^ s * c := by group
    rw [e3]
    exact P.mul_mem (P.pow_mem hdP s) hcP
  have hgk : ∀ a ∈ A, ∀ k : ℕ, g ^ k * a * (g ^ k)⁻¹ = (g * a * g⁻¹ * a⁻¹) ^ k * a := by
    intro a ha k
    obtain ⟨e, he⟩ : ∃ e : G, e = g * a * g⁻¹ * a⁻¹ := ⟨_, rfl⟩
    rw [← he]
    have heP : e ∈ P := he ▸ hgA a ha
    have hga : g * a * g⁻¹ = e * a := by rw [he]; group
    induction k with
    | zero => simp
    | succ k ih =>
      calc g ^ (k + 1) * a * (g ^ (k + 1))⁻¹ = g * (g ^ k * a * (g ^ k)⁻¹) * g⁻¹ := by
            rw [pow_succ']; group
        _ = g * (e ^ k * a) * g⁻¹ := by rw [ih]
        _ = (g * e * g⁻¹) ^ k * (g * a * g⁻¹) := by rw [conj_pow]; group
        _ = e ^ k * (e * a) := by rw [hgP e heP, hga]
        _ = e ^ (k + 1) * a := by rw [pow_succ]; group
  have hgr : g ^ r ∈ centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 := hgk a ha r
    have h2 : (g * a * g⁻¹ * a⁻¹) ^ r = 1 :=
      h.pow_eq_one _ (h.P_le (hgA a ha))
    rw [h2, one_mul] at h1
    calc a * g ^ r = (g ^ r * a * (g ^ r)⁻¹) * g ^ r := by rw [h1]
      _ = g ^ r * a := by group
  have hgC : g ∈ centralizer (A : Set G) := hcop g hgW hgr
  refine mem_normalizer_of_forward_uc6 fun z hz => ?_
  have haA : w * z * w⁻¹ ∈ A := h.conj_mem hw (h.Z_le hz)
  have hfix' : y' * (w * z * w⁻¹) * y'⁻¹ = w * z * w⁻¹ := by
    calc y' * (w * z * w⁻¹) * y'⁻¹ = w * (y * z * y⁻¹) * w⁻¹ := by rw [hy']; group
      _ = w * z * w⁻¹ := by rw [h.y_Z z hz]
  have hcg := Subgroup.mem_centralizer_iff.1 hgC _ haA
  have hfix : y * (w * z * w⁻¹) * y⁻¹ = w * z * w⁻¹ := by
    have e : y * (y'⁻¹ * (w * z * w⁻¹) * y') * y⁻¹ = g * (w * z * w⁻¹) * g⁻¹ := by
      rw [hg]; group
    have e' : y'⁻¹ * (w * z * w⁻¹) * y' = w * z * w⁻¹ := by
      calc y'⁻¹ * (w * z * w⁻¹) * y' = y'⁻¹ * (y' * (w * z * w⁻¹) * y'⁻¹) * y' := by
            rw [hfix']
        _ = w * z * w⁻¹ := by group
    rw [e'] at e
    rw [e, ← hcg]
    group
  exact (h.fixed_iff haA).1 hfix

theorem irreducible [Finite G] (hmove : ¬ W ≤ normalizer (Z : Set G))
    (hcop : ∀ g ∈ W, g ^ r ∈ centralizer (A : Set G) → g ∈ centralizer (A : Set G))
    {B : Subgroup G} (hBA : B ≤ A) (hWB : W ≤ normalizer (B : Set G)) : B = ⊥ ∨ B = A := by
  have hNB : N ≤ normalizer (B : Set G) := fun n hn => hWB (h.N_le hn)
  have hBP : N ≤ normalizer ((B ⊓ P : Subgroup G) : Set G) := by
    intro n hn
    refine mem_normalizer_of_forward_uc6 fun b hb => ?_
    exact ⟨(mem_normalizer_iff.1 (hNB hn) b).1 hb.1, (mem_normalizer_iff.1 (h.N_P hn) b).1 hb.2⟩
  rcases h.irr (B ⊓ P) inf_le_right hBP with h0 | h0
  ·
    left
    by_contra hB0
    have hBZ : B ≤ Z := h.le_Z_of_inf_eq_bot hBA hNB h0
    have hBeq : B = Z := h.eq_Z_of_le hBZ hB0
    exact hmove (hBeq ▸ hWB)
  ·
    have hPB : P ≤ B := h0 ▸ inf_le_left
    by_cases hBA' : B = A
    · exact Or.inr hBA'
    · exfalso
      have hBP' : B ≤ P := by
        intro b hb
        obtain ⟨z, hz, p, hp, rfl⟩ := h.exists_mul b (hBA hb)
        have hzB : z ∈ B := by
          have := B.mul_mem hb (B.inv_mem (hPB hp))
          simpa using this
        by_cases hz1 : z = 1
        · rw [hz1, one_mul]
          exact hp
        · exfalso
          have hzp : Subgroup.zpowers z ≤ Z := Subgroup.zpowers_le.2 hz
          have hne : Subgroup.zpowers z ≠ ⊥ := fun e => hz1 (Subgroup.zpowers_eq_bot.1 e)
          have hZeq : Subgroup.zpowers z = Z := h.eq_Z_of_le hzp hne
          have hZB : Z ≤ B := hZeq ▸ Subgroup.zpowers_le.2 hzB
          apply hBA'
          refine le_antisymm hBA fun a ha => ?_
          obtain ⟨z', hz', p', hp', rfl⟩ := h.exists_mul a ha
          exact B.mul_mem (hZB hz') (hPB hp')
      have hBeq : B = P := le_antisymm hBP' hPB
      exact hmove (h.normalizes_Z_of_normalizes_P (hBeq ▸ hWB) hcop)

end ScalarTriple

end CFSG.LocalAnalysis.UniquenessCase.UC6
