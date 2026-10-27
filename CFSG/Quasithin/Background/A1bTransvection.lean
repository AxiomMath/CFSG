module

public import CFSG.Quasithin.Background.AutOnBasics
public import CFSG.Quasithin.Background.A1bReduced
public import CFSG.Quasithin.Background.A1cRank
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin.A1b
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def twoCoreCentralizer (v : G) : Subgroup G :=
  pCoreOf 2 (Subgroup.centralizer ({v} : Set G))

structure A114Hyp (V : Subgroup G) (v₁ v₂ : G) : Prop where
  isElemAbelian : IsElemAbelian 2 V
  card_eq : Nat.card V = 4
  mem₁ : v₁ ∈ V
  mem₂ : v₂ ∈ V
  ne_one₁ : v₁ ≠ 1
  ne_one₂ : v₂ ≠ 1
  ne : v₁ ≠ v₂
  comm₁ : ⁅V, twoCoreCentralizer v₁⁆ = Subgroup.zpowers v₁
  comm₂ : ⁅V, twoCoreCentralizer v₂⁆ = Subgroup.zpowers v₂

@[expose] def a114Y (v₁ v₂ : G) : Subgroup G := twoCoreCentralizer v₁ ⊔ twoCoreCentralizer v₂

@[expose] def a114P (V : Subgroup G) (v₁ v₂ : G) : Subgroup G :=
  (twoCoreCentralizer v₁ ⊓ Subgroup.centralizer (V : Set G)) ⊔
    (twoCoreCentralizer v₂ ⊓ Subgroup.centralizer (V : Set G))

namespace A114Hyp

variable {V : Subgroup G} {v₁ v₂ : G}

theorem symm (h : A114Hyp V v₁ v₂) : A114Hyp V v₂ v₁ :=
  { h with
    mem₁ := h.mem₂
    mem₂ := h.mem₁
    ne_one₁ := h.ne_one₂
    ne_one₂ := h.ne_one₁
    ne := h.ne.symm
    comm₁ := h.comm₂
    comm₂ := h.comm₁ }

theorem sq_eq_one (h : A114Hyp V v₁ v₂) {x : G} (hx : x ∈ V) : x ^ 2 = 1 :=
  h.isElemAbelian.2 x hx

theorem comm_eq (h : A114Hyp V v₁ v₂) {x y : G} (hx : x ∈ V) (hy : y ∈ V) : x * y = y * x := by
  have := h.isElemAbelian.1
  have := mul_comm' (⟨x, hx⟩ : V) ⟨y, hy⟩
  simpa using congrArg Subtype.val this

theorem mem_V_cases [Finite G] (h : A114Hyp V v₁ v₂) {x : G} (hx : x ∈ V) :
    x = 1 ∨ x = v₁ ∨ x = v₂ ∨ x = v₁ * v₂ := by
  have hcomm : ∀ a b : V, a * b = b * a := fun a b =>
    Subtype.ext (h.comm_eq a.2 b.2)
  have hpow : ∀ a : V, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using h.sq_eq_one a.2)
  have hcard : Nat.card V = 2 ^ 2 := by rw [h.card_eq]; norm_num
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow hcard
  have key : ∀ a b c : Fin 2 → ZMod 2, a ≠ 0 → b ≠ 0 → a ≠ b →
      c = 0 ∨ c = a ∨ c = b ∨ c = a + b := by
    have key' : ∀ a b : Fin 2 → ZMod 2, a ≠ 0 → b ≠ 0 → a ≠ b →
        ∀ c : Fin 2 → ZMod 2, c = 0 ∨ c = a ∨ c = b ∨ c = a + b := by
      intro a b ha hb hab
      revert a b
      decide
    intro a b c ha hb hab
    exact key' a b ha hb hab c
  let u₁ : V := ⟨v₁, h.mem₁⟩
  let u₂ : V := ⟨v₂, h.mem₂⟩
  let ev : V → (Fin 2 → ZMod 2) := fun w => Multiplicative.toAdd (e w)
  have hev_inj : Function.Injective ev := fun a b hab =>
    e.injective (Multiplicative.toAdd.injective hab)
  have hev_one : ev 1 = 0 := by simp [ev]
  have hev_mul : ∀ a b, ev (a * b) = ev a + ev b := fun a b => by simp [ev]
  have h1 : ev u₁ ≠ 0 := fun hh =>
    h.ne_one₁ (congrArg Subtype.val (hev_inj (hh.trans hev_one.symm)))
  have h2 : ev u₂ ≠ 0 := fun hh =>
    h.ne_one₂ (congrArg Subtype.val (hev_inj (hh.trans hev_one.symm)))
  have h12 : ev u₁ ≠ ev u₂ := fun hh => h.ne (congrArg Subtype.val (hev_inj hh))
  rcases key (ev u₁) (ev u₂) (ev ⟨x, hx⟩) h1 h2 h12 with hc | hc | hc | hc
  · left
    exact congrArg Subtype.val (hev_inj (hc.trans hev_one.symm))
  · right; left
    exact congrArg Subtype.val (hev_inj hc)
  · right; right; left
    exact congrArg Subtype.val (hev_inj hc)
  · right; right; right
    exact congrArg Subtype.val (hev_inj (hc.trans (hev_mul u₁ u₂).symm))

theorem conj_cases (h : A114Hyp V v₁ v₂) {q x : G} (hq : q ∈ twoCoreCentralizer v₁) (hx : x ∈ V) :
    q * x * q⁻¹ = x ∨ q * x * q⁻¹ = x * v₁ := by
  have hmem : ⁅q, x⁆ ∈ ⁅V, twoCoreCentralizer v₁⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hq hx
  rw [h.comm₁] at hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hv2 : v₁ ^ 2 = 1 := h.sq_eq_one h.mem₁
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    have : ⁅q, x⁆ = 1 := by
      rw [← hk, zpow_mul]
      simp [hv2]
    rw [commutatorElement_eq_one_iff_mul_comm] at this
    rw [this]
    group
  · right
    have : ⁅q, x⁆ = v₁ := by
      rw [← hk, zpow_add_one, zpow_mul]
      simp [hv2]
    have h2 : q * x * q⁻¹ = ⁅q, x⁆ * x := by
      rw [commutatorElement_def]
      group
    rw [h2, this]
    exact h.comm_eq h.mem₁ hx

theorem twoCoreCentralizer_le_centralizer (v : G) :
    twoCoreCentralizer v ≤ Subgroup.centralizer ({v} : Set G) := pCoreOf_le 2 _

theorem conj_self (q : G) {v : G} (hq : q ∈ twoCoreCentralizer v) : q * v * q⁻¹ = v := by
  have := Subgroup.mem_centralizer_iff.1 (twoCoreCentralizer_le_centralizer v hq) v rfl
  rw [← this]
  group

end A114Hyp

namespace A1b

theorem mem_normalizer_of_conj_mem [Finite G] {V : Subgroup G} {q : G}
    (hq : ∀ y ∈ V, q * y * q⁻¹ ∈ V) : q ∈ Subgroup.normalizer (V : Set G) := by
  rw [← conjSub_eq_iff_mem_normalizer]
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
  · obtain ⟨y, hy, rfl⟩ := hx
    simpa [MulAut.conj_apply] using hq y hy
  · exact (Subgroup.card_map_of_injective (MulAut.conj q).injective).ge

theorem conjSub_twoCoreCentralizer (g v : G) :
    conjSub g (twoCoreCentralizer v) = twoCoreCentralizer (g * v * g⁻¹) := by
  have hcent : conjSub g (Subgroup.centralizer ({v} : Set G)) =
      Subgroup.centralizer ({g * v * g⁻¹} : Set G) := by
    ext x
    rw [mem_conjSub_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    constructor
    · intro hh
      calc g * v * g⁻¹ * x = g * (v * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * v) * g⁻¹ := by rw [hh]
        _ = x * (g * v * g⁻¹) := by group
    · intro hh
      calc v * (g⁻¹ * x * g) = g⁻¹ * (g * v * g⁻¹ * x) * g := by group
        _ = g⁻¹ * (x * (g * v * g⁻¹)) * g := by rw [hh]
        _ = (g⁻¹ * x * g) * v := by group
  unfold twoCoreCentralizer
  rw [← hcent]
  exact (pCoreOf_map_mulEquiv 2 (MulAut.conj g) _).symm

end A1b

namespace A114Hyp

variable {V : Subgroup G} {v₁ v₂ : G}

theorem twoCoreCentralizer_le_normalizer [Finite G] (h : A114Hyp V v₁ v₂) :
    twoCoreCentralizer v₁ ≤ Subgroup.normalizer (V : Set G) := by
  intro q hq
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  rcases h.conj_cases hq hy with h1 | h1
  · rw [h1]
    exact hy
  · rw [h1]
    exact V.mul_mem hy h.mem₁

theorem mem_centralizer_of_fixes [Finite G] (h : A114Hyp V v₁ v₂) {u : G}
    (h₁ : u * v₁ * u⁻¹ = v₁) (h₂ : u * v₂ * u⁻¹ = v₂) :
    u ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hfix : u * x * u⁻¹ = x := by
    rcases h.mem_V_cases hx with rfl | rfl | rfl | rfl
    · group
    · exact h₁
    · exact h₂
    · calc u * (v₁ * v₂) * u⁻¹ = (u * v₁ * u⁻¹) * (u * v₂ * u⁻¹) := by group
        _ = v₁ * v₂ := by rw [h₁, h₂]
  rw [mul_inv_eq_iff_eq_mul] at hfix
  exact hfix.symm

theorem exists_moving [Finite G] (h : A114Hyp V v₁ v₂) :
    ∃ a ∈ twoCoreCentralizer v₁, a * v₂ * a⁻¹ = v₂ * v₁ := by
  by_contra hno
  push Not at hno
  have hall : ∀ a ∈ twoCoreCentralizer v₁, a ∈ Subgroup.centralizer (V : Set G) := by
    intro a ha
    refine h.mem_centralizer_of_fixes (conj_self a ha) ?_
    rcases h.conj_cases ha h.mem₂ with h1 | h1
    · exact h1
    · exact absurd (by rw [h1, h.comm_eq h.mem₂ h.mem₁]) (hno a ha)
  have hbot : ⁅V, twoCoreCentralizer v₁⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx a ha
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.1 (hall a ha) x hx)
  rw [h.comm₁, Subgroup.zpowers_eq_bot] at hbot
  exact h.ne_one₁ hbot

end A114Hyp


namespace A1b

theorem zpow_eq_one_of_odd {Q : Type*} [Group Q] {r : Q} {k : ℤ} (hodd : r ^ (2 * k + 1) = 1)
    {j : ℤ} {n : ℕ} (h : r ^ (j * 2 ^ n) = 1) : r ^ j = 1 := by
  have hc : IsCoprime (2 * k + 1) ((2 : ℤ) ^ n) := by
    refine IsCoprime.pow_right ?_
    exact ⟨1, -k, by ring⟩
  obtain ⟨u, v, huv⟩ := hc
  calc r ^ j = r ^ (j * (u * (2 * k + 1) + v * 2 ^ n)) := by rw [huv, mul_one]
    _ = (r ^ (2 * k + 1)) ^ (j * u) * (r ^ (j * 2 ^ n)) ^ v := by
        rw [← zpow_mul, ← zpow_mul, ← zpow_add]; congr 1; ring
    _ = 1 := by rw [hodd, h, one_zpow, one_zpow, one_mul]

theorem dihedral_structure {Q : Type*} [Group Q] {a b r : Q} (hr : r = a * b) (ha : a * a = 1)
    (hb : b * b = 1) (hgen : Subgroup.closure ({a, b} : Set Q) = ⊤)
    (hconj : ∃ z : Q, z * a * z⁻¹ = b) :
    ∃ k : ℤ, r ^ (2 * k + 1) = 1 ∧ (∀ j : ℤ, a * r ^ j = r ^ (-j) * a) ∧
      ∀ x : Q, ∃ j : ℤ, x = r ^ j ∨ x = r ^ j * a := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have haa : ∀ x : Q, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have hrinv : r⁻¹ = b * a := by rw [hr, mul_inv_rev, ha', hb']
  have har : a * r * a = r⁻¹ := by
    rw [hrinv, hr]
    calc a * (a * b) * a = (a * a) * b * a := by simp only [mul_assoc]
      _ = b * a := by rw [ha, one_mul]
  have hconj_r : ∀ j : ℤ, a * r ^ j * a = r ^ (-j) := by
    intro j
    have h2 : a * r ^ j * a⁻¹ = (a * r * a⁻¹) ^ j := (conj_zpow).symm
    rw [ha', har, inv_zpow'] at h2
    exact h2
  have hconj_r' : ∀ j : ℤ, a * r ^ j = r ^ (-j) * a := by
    intro j
    rw [← hconj_r j]
    simp only [mul_assoc, ha, mul_one]
  have hb_eq : b = r⁻¹ * a := by
    rw [hrinv, mul_assoc, ha, mul_one]
  have hform : ∀ x : Q, ∃ j : ℤ, x = r ^ j ∨ x = r ^ j * a := by
    intro x
    have hx : x ∈ Subgroup.closure ({a, b} : Set Q) := by rw [hgen]; exact Subgroup.mem_top x
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨0, Or.inr (by rw [hx]; simp)⟩
      · rw [Set.mem_singleton_iff] at hx
        exact ⟨-1, Or.inr (by rw [hx, zpow_neg_one, hb_eq])⟩
    | one => exact ⟨0, Or.inl (by simp)⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨i, hi | hi⟩ := ihx <;> obtain ⟨j, hj | hj⟩ := ihy
      · exact ⟨i + j, Or.inl (by rw [hi, hj, zpow_add])⟩
      · exact ⟨i + j, Or.inr (by rw [hi, hj, zpow_add, mul_assoc])⟩
      · refine ⟨i - j, Or.inr ?_⟩
        rw [hi, hj, mul_assoc, hconj_r' j, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
      · refine ⟨i - j, Or.inl ?_⟩
        rw [hi, hj, mul_assoc, ← mul_assoc a, hconj_r' j, mul_assoc (r ^ (-j)), ha, mul_one,
          ← zpow_add, sub_eq_add_neg]
    | inv x _ ih =>
      obtain ⟨i, hi | hi⟩ := ih
      · exact ⟨-i, Or.inl (by rw [hi, zpow_neg])⟩
      · refine ⟨i, Or.inr ?_⟩
        rw [hi, mul_inv_rev, ha', ← zpow_neg, hconj_r' (-i), neg_neg]
  have hodd : ∃ k : ℤ, r ^ (2 * k + 1) = 1 := by
    obtain ⟨z, hz⟩ := hconj
    have key : ∀ k : ℤ, r ^ k * a * (r ^ k)⁻¹ = b → ∃ k' : ℤ, r ^ (2 * k' + 1) = 1 := by
      intro k hk
      refine ⟨k, ?_⟩
      have h1 : r ^ k * a * (r ^ k)⁻¹ = r ^ (2 * k) * a := by
        rw [← zpow_neg, mul_assoc, hconj_r' (-k), neg_neg, ← mul_assoc, ← zpow_add, two_mul]
      rw [h1, hb_eq] at hk
      have h2 := mul_right_cancel hk
      rw [zpow_add_one, h2, inv_mul_cancel]
    obtain ⟨k, hk | hk⟩ := hform z
    · exact key k (by rw [← hz, hk])
    · refine key k ?_
      rw [← hz, hk, mul_inv_rev, ha']
      simp only [mul_assoc, haa]
  obtain ⟨k, hk⟩ := hodd
  exact ⟨k, hk, hconj_r', hform⟩

theorem dihedral_center_trivial {Q : Type*} [Group Q] {a b : Q} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a ≠ b) (hgen : Subgroup.closure ({a, b} : Set Q) = ⊤)
    (hconj : ∃ z : Q, z * a * z⁻¹ = b) {c : Q} (hca : c * a = a * c) (hcb : c * b = b * c) :
    c = 1 := by
  obtain ⟨r, hr⟩ : ∃ r : Q, r = a * b := ⟨_, rfl⟩
  obtain ⟨k, hodd, hrel, hform⟩ := dihedral_structure hr ha hb hgen hconj
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hrinv : r⁻¹ = b * a := by rw [hr, mul_inv_rev, ha', hb']
  have hhalf : ∀ j : ℤ, r ^ (2 * j) = 1 → r ^ j = 1 := fun j hj =>
    zpow_eq_one_of_odd hodd (j := j) (n := 1) (by rw [pow_one, mul_comm]; exact hj)
  have hsq : ∀ j : ℤ, r ^ j = r ^ (-j) → r ^ j = 1 := by
    intro j hj
    apply hhalf
    rw [two_mul, zpow_add]
    nth_rewrite 1 [hj]
    rw [← zpow_add]
    simp
  obtain ⟨j, hj | hj⟩ := hform c
  · rw [hj] at hca ⊢
    rw [hrel j] at hca
    exact hsq j (mul_right_cancel hca)
  · exfalso
    rw [hj] at hca hcb
    have h1 : r ^ j = r ^ (-j) := by
      have h2 : r ^ j * a * a = a * (r ^ j * a) := hca
      rw [mul_assoc, ha, mul_one, ← mul_assoc, hrel j, mul_assoc, ha, mul_one] at h2
      exact h2
    have h4 := hsq j h1
    rw [h4, one_mul] at hcb
    have h5 : r = r⁻¹ := by rw [hrinv, hr]; exact hcb
    have h6 : r * r = 1 := by
      calc r * r = r⁻¹ * r := by rw [← h5]
        _ = 1 := inv_mul_cancel r
    have h7 : r = 1 := by
      have := hhalf 1 (by rw [mul_one, zpow_two]; exact h6)
      rwa [zpow_one] at this
    rw [h7] at hr
    exact hab ((eq_inv_of_mul_eq_one_left hr.symm).trans hb')

theorem dihedral_normal_two_group {Q : Type*} [Group Q] {a b : Q} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a ≠ b) (hgen : Subgroup.closure ({a, b} : Set Q) = ⊤)
    (hconj : ∃ z : Q, z * a * z⁻¹ = b) {R : Subgroup Q}
    (hRn : ∀ x ∈ R, ∀ g : Q, g * x * g⁻¹ ∈ R) (hR2 : ∀ x ∈ R, ∃ n : ℕ, x ^ 2 ^ n = 1) :
    R = ⊥ := by
  obtain ⟨r, hr⟩ : ∃ r : Q, r = a * b := ⟨_, rfl⟩
  obtain ⟨k, hodd, hrel, hform⟩ := dihedral_structure hr ha hb hgen hconj
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hF1 : ∀ j : ℤ, r ^ j ∈ R → r ^ j = 1 := by
    intro j hj
    obtain ⟨n, hn⟩ := hR2 _ hj
    refine zpow_eq_one_of_odd hodd (n := n) ?_
    rw [← zpow_natCast, ← zpow_mul] at hn
    push_cast at hn
    exact hn
  have har1 : a * r⁻¹ * a = r := by
    have h := hrel (-1)
    rw [neg_neg, zpow_neg_one, zpow_one] at h
    rw [h, mul_assoc, ha, mul_one]
  refine eq_bot_iff.2 fun x hx => ?_
  rw [Subgroup.mem_bot]
  obtain ⟨j, hj | hj⟩ := hform x
  · rw [hj] at hx ⊢
    exact hF1 j hx
  · exfalso
    have h1 : r * x * r⁻¹ * x⁻¹ ∈ R := R.mul_mem (hRn x hx r) (R.inv_mem hx)
    have h2 : r * x * r⁻¹ * x⁻¹ = r ^ (2 : ℤ) := by
      rw [hj]
      calc r * (r ^ j * a) * r⁻¹ * (r ^ j * a)⁻¹
          = r * r ^ j * (a * r⁻¹ * a) * (r ^ j)⁻¹ := by rw [mul_inv_rev, ha']; group
        _ = r * r ^ j * r * (r ^ j)⁻¹ := by rw [har1]
        _ = r ^ (2 : ℤ) := by group
    rw [h2] at h1
    have h3 := hF1 2 h1
    have h7 : r = 1 := by
      have := zpow_eq_one_of_odd hodd (j := 1) (n := 1)
        (by rw [show ((1 : ℤ) * 2 ^ 1) = 2 by norm_num]; exact h3)
      rwa [zpow_one] at this
    rw [h7] at hr
    exact hab ((eq_inv_of_mul_eq_one_left hr.symm).trans hb')

end A1b


namespace A1b

theorem conjugate_mul (g x y : G) : g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by
  group

theorem inv_conjugate_eq {g x y : G} (h : g * x * g⁻¹ = y) : g⁻¹ * y * g = x := by
  rw [← h]; group

theorem conjSub_sup (g : G) (H K : Subgroup G) :
    conjSub g (H ⊔ K) = conjSub g H ⊔ conjSub g K := Subgroup.map_sup _ _ _

theorem mem_normalizer_sup' {g : G} {H K : Subgroup G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [← conjSub_eq_iff_mem_normalizer] at hH hK ⊢
  rw [conjSub_sup, hH, hK]

theorem mem_normalizer_inf' {g : G} {H K : Subgroup G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro x
  simp only [Subgroup.mem_inf]
  exact (hH x).and (hK x)

theorem conjAct_coe (V : Subgroup G) (g : Subgroup.normalizer (V : Set G)) (x : V) :
    ((conjAct V g x : V) : G) = g * x * (g : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply V g x

theorem conjAct_eq_one_iff {V : Subgroup G} {g : Subgroup.normalizer (V : Set G)} :
    conjAct V g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff g

theorem conjAct_mem_autOn {V Y : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (hgY : g ∈ Y) : conjAct V ⟨g, hg⟩ ∈ autOn Y V :=
  Subgroup.mem_map.2 ⟨⟨g, hg⟩, Subgroup.mem_subgroupOf.2 hgY, rfl⟩

end A1b

theorem a114P_le_centralizer (V : Subgroup G) (v₁ v₂ : G) :
    a114P V v₁ v₂ ≤ Subgroup.centralizer (V : Set G) :=
  sup_le inf_le_right inf_le_right

theorem a114P_le_a114Y (V : Subgroup G) (v₁ v₂ : G) : a114P V v₁ v₂ ≤ a114Y v₁ v₂ :=
  sup_le_sup inf_le_left inf_le_left

theorem inf_le_a114P_left (V : Subgroup G) (v₁ v₂ : G) :
    twoCoreCentralizer v₁ ⊓ Subgroup.centralizer (V : Set G) ≤ a114P V v₁ v₂ := le_sup_left

theorem inf_le_a114P_right (V : Subgroup G) (v₁ v₂ : G) :
    twoCoreCentralizer v₂ ⊓ Subgroup.centralizer (V : Set G) ≤ a114P V v₁ v₂ := le_sup_right

theorem a114P_comm (V : Subgroup G) (v₁ v₂ : G) : a114P V v₂ v₁ = a114P V v₁ v₂ := sup_comm _ _

theorem a114Y_comm (v₁ v₂ : G) : a114Y v₂ v₁ = a114Y v₁ v₂ := sup_comm _ _

namespace A114Hyp

variable {V : Subgroup G} {v₁ v₂ : G}

theorem v₁_mul_self (h : A114Hyp V v₁ v₂) : v₁ * v₁ = 1 := by
  simpa [pow_two] using h.sq_eq_one h.mem₁

theorem v₂_mul_self (h : A114Hyp V v₁ v₂) : v₂ * v₂ = 1 := h.symm.v₁_mul_self

theorem v_comm (h : A114Hyp V v₁ v₂) : v₁ * v₂ = v₂ * v₁ := h.comm_eq h.mem₁ h.mem₂

theorem v_alg₁ (h : A114Hyp V v₁ v₂) : v₁ * (v₂ * v₁) = v₂ := by
  rw [← h.v_comm, ← mul_assoc, h.v₁_mul_self, one_mul]

theorem v_alg₂ (h : A114Hyp V v₁ v₂) : v₂ * (v₁ * v₂) = v₁ := h.symm.v_alg₁

theorem v_alg₃ (h : A114Hyp V v₁ v₂) : v₂ * v₁ * v₁ = v₂ := by
  rw [mul_assoc, h.v₁_mul_self, mul_one]

theorem v_alg₄ (h : A114Hyp V v₁ v₂) : v₁ * v₂ * v₂ = v₁ := h.symm.v_alg₃

theorem mem_centralizer_iff_fixes [Finite G] (h : A114Hyp V v₁ v₂) {u : G} :
    u ∈ Subgroup.centralizer (V : Set G) ↔ u * v₁ * u⁻¹ = v₁ ∧ u * v₂ * u⁻¹ = v₂ := by
  refine ⟨fun hu => ?_, fun ⟨h1, h2⟩ => h.mem_centralizer_of_fixes h1 h2⟩
  have key := Subgroup.mem_centralizer_iff.1 hu
  constructor
  · rw [← key v₁ h.mem₁]; group
  · rw [← key v₂ h.mem₂]; group

theorem exists_gens [Finite G] (h : A114Hyp V v₁ v₂) :
    ∃ a₁ a₂ : G, a₁ ∈ twoCoreCentralizer v₁ ∧ a₂ ∈ twoCoreCentralizer v₂ ∧
      a₁ * v₂ * a₁⁻¹ = v₂ * v₁ ∧ a₂ * v₁ * a₂⁻¹ = v₁ * v₂ := by
  obtain ⟨a₁, ha₁, h₁⟩ := h.exists_moving
  obtain ⟨a₂, ha₂, h₂⟩ := h.symm.exists_moving
  exact ⟨a₁, a₂, ha₁, ha₂, h₁, h₂⟩

theorem a114Y_le_normalizer [Finite G] (h : A114Hyp V v₁ v₂) :
    a114Y v₁ v₂ ≤ Subgroup.normalizer (V : Set G) :=
  sup_le h.twoCoreCentralizer_le_normalizer h.symm.twoCoreCentralizer_le_normalizer

theorem centralizer_le_normalizer_core (h : A114Hyp V v₁ v₂) :
    Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (twoCoreCentralizer v₁ : Set G) :=
  (Subgroup.centralizer_le (Set.singleton_subset_iff.2 h.mem₁)).trans (le_normalizer_pCoreOf 2 _)

theorem comm_mem_inf [Finite G] (h : A114Hyp V v₁ v₂) {q c : G} (hq : q ∈ twoCoreCentralizer v₁)
    (hc : c ∈ Subgroup.centralizer (V : Set G)) :
    q * c * q⁻¹ * c⁻¹ ∈ twoCoreCentralizer v₁ ⊓ Subgroup.centralizer (V : Set G) := by
  have hqN : q ∈ Subgroup.normalizer (V : Set G) := h.twoCoreCentralizer_le_normalizer hq
  refine ⟨?_, ?_⟩
  · have h1 : c * q⁻¹ * c⁻¹ ∈ twoCoreCentralizer v₁ :=
      (Subgroup.mem_normalizer_iff.1 (h.centralizer_le_normalizer_core hc) q⁻¹).1
        ((twoCoreCentralizer v₁).inv_mem hq)
    have := (twoCoreCentralizer v₁).mul_mem hq h1
    simpa [mul_assoc] using this
  · exact (Subgroup.centralizer (V : Set G)).mul_mem
      (A1b.conj_mem_centralizer_of_mem_normalizer hqN hc)
      ((Subgroup.centralizer (V : Set G)).inv_mem hc)

theorem inf_le_pCoreOf_centralizer [Finite G] (h : A114Hyp V v₁ v₂) :
    twoCoreCentralizer v₁ ⊓ Subgroup.centralizer (V : Set G) ≤
      pCoreOf 2 (Subgroup.centralizer (V : Set G)) := by
  refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    ((pCoreOf_isPGroup 2 _).to_le inf_le_left)
  intro c hc
  exact A1b.mem_normalizer_inf' (h.centralizer_le_normalizer_core hc) (Subgroup.le_normalizer hc)

theorem a114P_isPGroup [Finite G] (h : A114Hyp V v₁ v₂) : IsPGroup 2 (a114P V v₁ v₂) :=
  (pCoreOf_isPGroup 2 (Subgroup.centralizer (V : Set G))).to_le
    (sup_le h.inf_le_pCoreOf_centralizer h.symm.inf_le_pCoreOf_centralizer)

theorem centralizer_le_normalizer_a114P (h : A114Hyp V v₁ v₂) :
    Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (a114P V v₁ v₂ : Set G) := by
  intro c hc
  exact A1b.mem_normalizer_sup'
    (A1b.mem_normalizer_inf' (h.centralizer_le_normalizer_core hc) (Subgroup.le_normalizer hc))
    (A1b.mem_normalizer_inf' (h.symm.centralizer_le_normalizer_core hc) (Subgroup.le_normalizer hc))

theorem twoCoreCentralizer_le_normalizer_a114P [Finite G] (h : A114Hyp V v₁ v₂) :
    twoCoreCentralizer v₁ ≤ Subgroup.normalizer (a114P V v₁ v₂ : Set G) := by
  intro q hq
  refine A1b.mem_normalizer_of_conj_mem fun x hx => ?_
  have h1 := h.comm_mem_inf hq (a114P_le_centralizer V v₁ v₂ hx)
  have h2 : q * x * q⁻¹ * x⁻¹ ∈ a114P V v₁ v₂ := inf_le_a114P_left V v₁ v₂ h1
  have := (a114P V v₁ v₂).mul_mem h2 hx
  simpa [mul_assoc] using this

theorem a114Y_le_normalizer_a114P [Finite G] (h : A114Hyp V v₁ v₂) :
    a114Y v₁ v₂ ≤ Subgroup.normalizer (a114P V v₁ v₂ : Set G) := by
  refine sup_le h.twoCoreCentralizer_le_normalizer_a114P ?_
  have := h.symm.twoCoreCentralizer_le_normalizer_a114P
  rwa [a114P_comm] at this

theorem not_mem_centralizer_of_moves [Finite G] (h : A114Hyp V v₁ v₂) {a : G}
    (ha : a * v₂ * a⁻¹ = v₂ * v₁) : a ∉ Subgroup.centralizer (V : Set G) := by
  intro hC
  have h2 := (h.mem_centralizer_iff_fixes.1 hC).2
  rw [ha] at h2
  exact h.ne_one₁ (mul_left_cancel (h2.trans (mul_one v₂).symm))

theorem mem_centralizer_or_moves [Finite G] (h : A114Hyp V v₁ v₂) {u : G}
    (hu : u ∈ twoCoreCentralizer v₁) :
    u ∈ Subgroup.centralizer (V : Set G) ∨ u * v₂ * u⁻¹ = v₂ * v₁ := by
  rcases h.conj_cases hu h.mem₂ with h1 | h1
  · exact Or.inl (h.mem_centralizer_of_fixes (conj_self u hu) h1)
  · exact Or.inr h1

theorem mul_inv_mem_inf [Finite G] (h : A114Hyp V v₁ v₂) {u w : G}
    (hu : u ∈ twoCoreCentralizer v₁) (hw : w ∈ twoCoreCentralizer v₁)
    (hu' : u ∉ Subgroup.centralizer (V : Set G)) (hw' : w ∉ Subgroup.centralizer (V : Set G)) :
    u * w⁻¹ ∈ twoCoreCentralizer v₁ ⊓ Subgroup.centralizer (V : Set G) := by
  refine Subgroup.mem_inf.2
    ⟨(twoCoreCentralizer v₁).mul_mem hu ((twoCoreCentralizer v₁).inv_mem hw), ?_⟩
  have hu2 := (h.mem_centralizer_or_moves hu).resolve_left hu'
  have hw2 := (h.mem_centralizer_or_moves hw).resolve_left hw'
  have hu1 := conj_self u hu
  have hw1 := conj_self w hw
  rw [h.mem_centralizer_iff_fixes]
  constructor
  · calc u * w⁻¹ * v₁ * (u * w⁻¹)⁻¹ = u * (w⁻¹ * v₁ * w) * u⁻¹ := by group
      _ = u * v₁ * u⁻¹ := by rw [A1b.inv_conjugate_eq hw1]
      _ = v₁ := hu1
  · have hw3 : w⁻¹ * v₂ * w = v₂ * v₁ := by
      have h3 := A1b.inv_conjugate_eq hw2
      have h4 : w⁻¹ * (v₂ * v₁) * w = (w⁻¹ * v₂ * w) * (w⁻¹ * v₁ * w) := by group
      rw [h4, A1b.inv_conjugate_eq hw1] at h3
      have h5 := eq_mul_inv_of_mul_eq h3
      rw [h5, inv_eq_of_mul_eq_one_right h.v₁_mul_self]
    calc u * w⁻¹ * v₂ * (u * w⁻¹)⁻¹ = u * (w⁻¹ * v₂ * w) * u⁻¹ := by group
      _ = u * (v₂ * v₁) * u⁻¹ := by rw [hw3]
      _ = u * v₂ * u⁻¹ * (u * v₁ * u⁻¹) := A1b.conjugate_mul u v₂ v₁
      _ = v₂ := by rw [hu2, hu1, h.v_alg₃]

theorem mem_inf_or_inv_mul_mem [Finite G] (h : A114Hyp V v₁ v₂) {a x : G}
    (ha : a ∈ twoCoreCentralizer v₁) (ha' : a ∉ Subgroup.centralizer (V : Set G))
    (hx : x ∈ twoCoreCentralizer v₁) :
    x ∈ twoCoreCentralizer v₁ ⊓ Subgroup.centralizer (V : Set G) ∨
      x⁻¹ * a ∈ twoCoreCentralizer v₁ ⊓ Subgroup.centralizer (V : Set G) := by
  by_cases hxC : x ∈ Subgroup.centralizer (V : Set G)
  · exact Or.inl ⟨hx, hxC⟩
  · right
    have key := h.mul_inv_mem_inf ((twoCoreCentralizer v₁).inv_mem hx)
      ((twoCoreCentralizer v₁).inv_mem ha)
      (fun hh => hxC (by simpa using (Subgroup.centralizer (V : Set G)).inv_mem hh))
      (fun hh => ha' (by simpa using (Subgroup.centralizer (V : Set G)).inv_mem hh))
    simpa using key

theorem mem_a114P_or_inv_mul_mem [Finite G] (h : A114Hyp V v₁ v₂) {a x : G}
    (ha : a ∈ twoCoreCentralizer v₁) (h₁ : a * v₂ * a⁻¹ = v₂ * v₁)
    (hx : x ∈ twoCoreCentralizer v₁) :
    x ∈ a114P V v₁ v₂ ∨ x⁻¹ * a ∈ a114P V v₁ v₂ := by
  rcases h.mem_inf_or_inv_mul_mem ha (h.not_mem_centralizer_of_moves h₁) hx with h1 | h1
  · exact Or.inl (inf_le_a114P_left V v₁ v₂ h1)
  · exact Or.inr (inf_le_a114P_left V v₁ v₂ h1)

theorem card_mulAut [Finite G] (h : A114Hyp V v₁ v₂) : Nat.card (MulAut V) = 6 := by
  have hcomm : ∀ a b : V, a * b = b * a := fun a b => Subtype.ext (h.comm_eq a.2 b.2)
  have hpow : ∀ a : V, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using h.sq_eq_one a.2)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow
    (n := 2) (by rw [h.card_eq]; norm_num)
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
  simp [Fin.prod_univ_succ]

theorem a₁_sq_mem_centralizer [Finite G] (h : A114Hyp V v₁ v₂) {a₁ : G}
    (ha₁ : a₁ ∈ twoCoreCentralizer v₁) (h₁ : a₁ * v₂ * a₁⁻¹ = v₂ * v₁) :
    a₁ * a₁ ∈ Subgroup.centralizer (V : Set G) := by
  have hf := conj_self a₁ ha₁
  rw [h.mem_centralizer_iff_fixes]
  constructor
  · calc a₁ * a₁ * v₁ * (a₁ * a₁)⁻¹ = a₁ * (a₁ * v₁ * a₁⁻¹) * a₁⁻¹ := by group
      _ = v₁ := by rw [hf, hf]
  · calc a₁ * a₁ * v₂ * (a₁ * a₁)⁻¹ = a₁ * (a₁ * v₂ * a₁⁻¹) * a₁⁻¹ := by group
      _ = a₁ * (v₂ * v₁) * a₁⁻¹ := by rw [h₁]
      _ = a₁ * v₂ * a₁⁻¹ * (a₁ * v₁ * a₁⁻¹) := A1b.conjugate_mul a₁ v₂ v₁
      _ = v₂ := by rw [h₁, hf, h.v_alg₃]

theorem y_act₁ [Finite G] (h : A114Hyp V v₁ v₂) {a₁ a₂ : G} (ha₁ : a₁ ∈ twoCoreCentralizer v₁)
    (h₁ : a₁ * v₂ * a₁⁻¹ = v₂ * v₁) (h₂ : a₂ * v₁ * a₂⁻¹ = v₁ * v₂) :
    a₁ * a₂ * v₁ * (a₁ * a₂)⁻¹ = v₂ := by
  calc a₁ * a₂ * v₁ * (a₁ * a₂)⁻¹ = a₁ * (a₂ * v₁ * a₂⁻¹) * a₁⁻¹ := by group
    _ = a₁ * (v₁ * v₂) * a₁⁻¹ := by rw [h₂]
    _ = a₁ * v₁ * a₁⁻¹ * (a₁ * v₂ * a₁⁻¹) := A1b.conjugate_mul _ _ _
    _ = v₂ := by rw [conj_self a₁ ha₁, h₁, h.v_alg₁]

theorem y_act₂ [Finite G] (h : A114Hyp V v₁ v₂) {a₁ a₂ : G} (ha₂ : a₂ ∈ twoCoreCentralizer v₂)
    (h₁ : a₁ * v₂ * a₁⁻¹ = v₂ * v₁) :
    a₁ * a₂ * v₂ * (a₁ * a₂)⁻¹ = v₁ * v₂ := by
  calc a₁ * a₂ * v₂ * (a₁ * a₂)⁻¹ = a₁ * (a₂ * v₂ * a₂⁻¹) * a₁⁻¹ := by group
    _ = a₁ * v₂ * a₁⁻¹ := by rw [conj_self a₂ ha₂]
    _ = v₂ * v₁ := h₁
    _ = v₁ * v₂ := h.v_comm.symm

theorem y_cube_mem_centralizer [Finite G] (h : A114Hyp V v₁ v₂) {a₁ a₂ : G}
    (ha₁ : a₁ ∈ twoCoreCentralizer v₁) (ha₂ : a₂ ∈ twoCoreCentralizer v₂)
    (h₁ : a₁ * v₂ * a₁⁻¹ = v₂ * v₁) (h₂ : a₂ * v₁ * a₂⁻¹ = v₁ * v₂) :
    a₁ * a₂ * (a₁ * a₂) * (a₁ * a₂) ∈ Subgroup.centralizer (V : Set G) := by
  have e1 : a₁ * a₂ * v₁ * (a₁ * a₂)⁻¹ = v₂ := h.y_act₁ ha₁ h₁ h₂
  have e2 : a₁ * a₂ * v₂ * (a₁ * a₂)⁻¹ = v₁ * v₂ := h.y_act₂ ha₂ h₁
  have e3 : a₁ * a₂ * (v₁ * v₂) * (a₁ * a₂)⁻¹ = v₁ := by
    rw [A1b.conjugate_mul, e1, e2, h.v_alg₂]
  rw [h.mem_centralizer_iff_fixes]
  constructor
  · calc a₁ * a₂ * (a₁ * a₂) * (a₁ * a₂) * v₁ * (a₁ * a₂ * (a₁ * a₂) * (a₁ * a₂))⁻¹
        = a₁ * a₂ * (a₁ * a₂ * (a₁ * a₂ * v₁ * (a₁ * a₂)⁻¹) * (a₁ * a₂)⁻¹) * (a₁ * a₂)⁻¹ := by
          group
      _ = v₁ := by rw [e1, e2, e3]
  · calc a₁ * a₂ * (a₁ * a₂) * (a₁ * a₂) * v₂ * (a₁ * a₂ * (a₁ * a₂) * (a₁ * a₂))⁻¹
        = a₁ * a₂ * (a₁ * a₂ * (a₁ * a₂ * v₂ * (a₁ * a₂)⁻¹) * (a₁ * a₂)⁻¹) * (a₁ * a₂)⁻¹ := by
          group
      _ = v₂ := by rw [e2, e3, e1]

theorem y_not_mem_centralizer [Finite G] (h : A114Hyp V v₁ v₂) {a₁ a₂ : G}
    (ha₁ : a₁ ∈ twoCoreCentralizer v₁) (h₁ : a₁ * v₂ * a₁⁻¹ = v₂ * v₁)
    (h₂ : a₂ * v₁ * a₂⁻¹ = v₁ * v₂) : a₁ * a₂ ∉ Subgroup.centralizer (V : Set G) := by
  intro hC
  have h3 := (h.mem_centralizer_iff_fixes.1 hC).1
  rw [h.y_act₁ ha₁ h₁ h₂] at h3
  exact h.ne h3.symm

theorem autOn_a114Y [Finite G] (h : A114Hyp V v₁ v₂) : autOn (a114Y v₁ v₂) V = ⊤ := by
  obtain ⟨a₁, a₂, ha₁, ha₂, h₁, h₂⟩ := h.exists_gens
  have hN₁ : a₁ ∈ Subgroup.normalizer (V : Set G) := h.twoCoreCentralizer_le_normalizer ha₁
  have hN₂ : a₂ ∈ Subgroup.normalizer (V : Set G) :=
    h.symm.twoCoreCentralizer_le_normalizer ha₂
  have hY₁ : a₁ ∈ a114Y v₁ v₂ := Subgroup.mem_sup_left ha₁
  have hY₂ : a₂ ∈ a114Y v₁ v₂ := Subgroup.mem_sup_right ha₂
  have hNy : a₁ * a₂ ∈ Subgroup.normalizer (V : Set G) := Subgroup.mul_mem _ hN₁ hN₂
  have hτS : conjAct V ⟨a₁, hN₁⟩ ∈ autOn (a114Y v₁ v₂) V := A1b.conjAct_mem_autOn hN₁ hY₁
  have hρS : conjAct V ⟨a₁ * a₂, hNy⟩ ∈ autOn (a114Y v₁ v₂) V :=
    A1b.conjAct_mem_autOn hNy (Subgroup.mul_mem _ hY₁ hY₂)
  have hτne : conjAct V ⟨a₁, hN₁⟩ ≠ 1 := fun hh =>
    h.not_mem_centralizer_of_moves h₁ (A1b.conjAct_eq_one_iff.1 hh)
  have hτsq : conjAct V ⟨a₁, hN₁⟩ ^ 2 = 1 := by
    rw [pow_two, ← map_mul]
    exact A1b.conjAct_eq_one_iff.2 (h.a₁_sq_mem_centralizer ha₁ h₁)
  have hρne : conjAct V ⟨a₁ * a₂, hNy⟩ ≠ 1 := fun hh =>
    h.y_not_mem_centralizer ha₁ h₁ h₂ (A1b.conjAct_eq_one_iff.1 hh)
  have hρcube : conjAct V ⟨a₁ * a₂, hNy⟩ ^ 3 = 1 := by
    rw [pow_three', ← map_mul, ← map_mul]
    exact A1b.conjAct_eq_one_iff.2 (h.y_cube_mem_centralizer ha₁ ha₂ h₁ h₂)
  have hord₂ : orderOf (conjAct V ⟨a₁, hN₁⟩) = 2 := orderOf_eq_prime hτsq hτne
  have hord₃ : orderOf (conjAct V ⟨a₁ * a₂, hNy⟩) = 3 := orderOf_eq_prime hρcube hρne
  have hd₂ : 2 ∣ Nat.card (autOn (a114Y v₁ v₂) V) := by
    have := orderOf_dvd_natCard (⟨_, hτS⟩ : autOn (a114Y v₁ v₂) V)
    rwa [Subgroup.orderOf_mk, hord₂] at this
  have hd₃ : 3 ∣ Nat.card (autOn (a114Y v₁ v₂) V) := by
    have := orderOf_dvd_natCard (⟨_, hρS⟩ : autOn (a114Y v₁ v₂) V)
    rwa [Subgroup.orderOf_mk, hord₃] at this
  have hd₆ : 6 ∣ Nat.card (autOn (a114Y v₁ v₂) V) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hd₂ hd₃
  have hle : Nat.card (autOn (a114Y v₁ v₂) V) ≤ 6 := by
    rw [← h.card_mulAut]
    exact Subgroup.card_le_card_group _
  have heq : Nat.card (autOn (a114Y v₁ v₂) V) = 6 :=
    le_antisymm hle (Nat.le_of_dvd Nat.card_pos hd₆)
  exact Subgroup.eq_top_of_card_eq _ (heq.trans h.card_mulAut.symm)

theorem sq_mem_a114P [Finite G] (h : A114Hyp V v₁ v₂) {a₁ : G}
    (ha₁ : a₁ ∈ twoCoreCentralizer v₁) (h₁ : a₁ * v₂ * a₁⁻¹ = v₂ * v₁) :
    a₁ * a₁ ∈ a114P V v₁ v₂ :=
  inf_le_a114P_left V v₁ v₂
    ⟨(twoCoreCentralizer v₁).mul_mem ha₁ ha₁, h.a₁_sq_mem_centralizer ha₁ h₁⟩

theorem sq_mem_a114P' [Finite G] (h : A114Hyp V v₁ v₂) {a₂ : G}
    (ha₂ : a₂ ∈ twoCoreCentralizer v₂) (h₂ : a₂ * v₁ * a₂⁻¹ = v₁ * v₂) :
    a₂ * a₂ ∈ a114P V v₁ v₂ := by
  have := h.symm.sq_mem_a114P ha₂ h₂
  rwa [a114P_comm] at this

theorem inv_mul_not_mem_a114P [Finite G] (h : A114Hyp V v₁ v₂) {a₁ a₂ : G}
    (ha₁ : a₁ ∈ twoCoreCentralizer v₁) (h₂ : a₂ * v₁ * a₂⁻¹ = v₁ * v₂) :
    a₁⁻¹ * a₂ ∉ a114P V v₁ v₂ := by
  intro hP
  have hfix := (h.mem_centralizer_iff_fixes.1 (a114P_le_centralizer V v₁ v₂ hP)).1
  have e : a₂ * v₁ * a₂⁻¹ = v₁ := by
    calc a₂ * v₁ * a₂⁻¹ = a₁ * ((a₁⁻¹ * a₂) * v₁ * (a₁⁻¹ * a₂)⁻¹) * a₁⁻¹ := by group
      _ = a₁ * v₁ * a₁⁻¹ := by rw [hfix]
      _ = v₁ := conj_self a₁ ha₁
  rw [h₂] at e
  exact h.ne_one₂ (mul_left_cancel (e.trans (mul_one v₁).symm))

theorem conj_mem_a114P [Finite G] (h : A114Hyp V v₁ v₂) {a₁ a₂ : G}
    (ha₁ : a₁ ∈ twoCoreCentralizer v₁) (ha₂ : a₂ ∈ twoCoreCentralizer v₂)
    (h₁ : a₁ * v₂ * a₁⁻¹ = v₂ * v₁) (h₂ : a₂ * v₁ * a₂⁻¹ = v₁ * v₂) :
    (a₁ * a₂ * a₁ * (a₁ * a₂)⁻¹)⁻¹ * a₂ ∈ a114P V v₁ v₂ := by
  have hN : a₁ * a₂ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (h.twoCoreCentralizer_le_normalizer ha₁)
      (h.symm.twoCoreCentralizer_le_normalizer ha₂)
  have hy1 := h.y_act₁ ha₁ h₁ h₂
  have hmem : a₁ * a₂ * a₁ * (a₁ * a₂)⁻¹ ∈ twoCoreCentralizer v₂ := by
    have := A1b.mem_conjSub_of_mem (g := a₁ * a₂) ha₁
    rwa [A1b.conjSub_twoCoreCentralizer, hy1] at this
  have hnC : a₁ * a₂ * a₁ * (a₁ * a₂)⁻¹ ∉ Subgroup.centralizer (V : Set G) := by
    intro hC
    have hinvN : (a₁ * a₂)⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hN
    have := A1b.conj_mem_centralizer_of_mem_normalizer hinvN hC
    have e : (a₁ * a₂)⁻¹ * (a₁ * a₂ * a₁ * (a₁ * a₂)⁻¹) * (a₁ * a₂)⁻¹⁻¹ = a₁ := by group
    rw [e] at this
    exact h.not_mem_centralizer_of_moves h₁ this
  have key := h.symm.mul_inv_mem_inf (u := (a₁ * a₂ * a₁ * (a₁ * a₂)⁻¹)⁻¹) (w := a₂⁻¹)
    ((twoCoreCentralizer v₂).inv_mem hmem) ((twoCoreCentralizer v₂).inv_mem ha₂)
    (fun hh => hnC (by simpa using (Subgroup.centralizer (V : Set G)).inv_mem hh))
    (fun hh => h.symm.not_mem_centralizer_of_moves h₂
      (by simpa using (Subgroup.centralizer (V : Set G)).inv_mem hh))
  have key' : (a₁ * a₂ * a₁ * (a₁ * a₂)⁻¹)⁻¹ * a₂ ∈
      twoCoreCentralizer v₂ ⊓ Subgroup.centralizer (V : Set G) := by simpa using key
  exact inf_le_a114P_right V v₁ v₂ key'

theorem mem_a114P_or_inv_mul_mem' [Finite G] (h : A114Hyp V v₁ v₂) {a x : G}
    (ha : a ∈ twoCoreCentralizer v₂) (h₂ : a * v₁ * a⁻¹ = v₁ * v₂)
    (hx : x ∈ twoCoreCentralizer v₂) : x ∈ a114P V v₁ v₂ ∨ x⁻¹ * a ∈ a114P V v₁ v₂ := by
  have := h.symm.mem_a114P_or_inv_mul_mem ha h₂ hx
  rwa [a114P_comm] at this

theorem commutes_mod_a114P [Finite G] (h : A114Hyp V v₁ v₂) {a₁ x : G}
    (ha₁ : a₁ ∈ twoCoreCentralizer v₁) (hx : x ∈ Subgroup.centralizer (V : Set G)) :
    (x * a₁)⁻¹ * (a₁ * x) ∈ a114P V v₁ v₂ := by
  have key := h.comm_mem_inf ((twoCoreCentralizer v₁).inv_mem ha₁)
    ((Subgroup.centralizer (V : Set G)).inv_mem hx)
  have e : (x * a₁)⁻¹ * (a₁ * x) = a₁⁻¹ * x⁻¹ * a₁⁻¹⁻¹ * x⁻¹⁻¹ := by group
  rw [e]
  exact inf_le_a114P_left V v₁ v₂ key

theorem commutes_mod_a114P' [Finite G] (h : A114Hyp V v₁ v₂) {a₂ x : G}
    (ha₂ : a₂ ∈ twoCoreCentralizer v₂) (hx : x ∈ Subgroup.centralizer (V : Set G)) :
    (x * a₂)⁻¹ * (a₂ * x) ∈ a114P V v₁ v₂ := by
  have := h.symm.commutes_mod_a114P ha₂ hx
  rwa [a114P_comm] at this

theorem a114_inf_le_and_pCore_le [Finite G] (h : A114Hyp V v₁ v₂) :
    a114Y v₁ v₂ ⊓ Subgroup.centralizer (V : Set G) ≤ a114P V v₁ v₂ ∧
      pCoreOf 2 (a114Y v₁ v₂) ≤ a114P V v₁ v₂ := by
  obtain ⟨a₁, a₂, ha₁, ha₂, h₁, h₂⟩ := h.exists_gens
  have hY₁ : a₁ ∈ a114Y v₁ v₂ := Subgroup.mem_sup_left ha₁
  have hY₂ : a₂ ∈ a114Y v₁ v₂ := Subgroup.mem_sup_right ha₂
  have hyY : a₁ * a₂ ∈ a114Y v₁ v₂ := Subgroup.mul_mem _ hY₁ hY₂
  have hPY : a114P V v₁ v₂ ≤ a114Y v₁ v₂ := a114P_le_a114Y V v₁ v₂
  set Y := a114Y v₁ v₂ with hY
  set P := a114P V v₁ v₂ with hP
  have hnormal : (P.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPY).2 h.a114Y_le_normalizer_a114P
  let π : ↥Y →* ↥Y ⧸ P.subgroupOf Y := QuotientGroup.mk' _
  have hπ_one : ∀ x : ↥Y, π x = 1 ↔ (x : G) ∈ P := fun x =>
    (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf
  have hπ_eq : ∀ x y : ↥Y, π x = π y ↔ (x : G)⁻¹ * y ∈ P := fun x y =>
    QuotientGroup.eq.trans Subgroup.mem_subgroupOf
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  let a : ↥Y := ⟨a₁, hY₁⟩
  let b : ↥Y := ⟨a₂, hY₂⟩
  have hsqa : π a * π a = 1 := by
    rw [← map_mul]
    exact (hπ_one _).2 (h.sq_mem_a114P ha₁ h₁)
  have hsqb : π b * π b = 1 := by
    rw [← map_mul]
    exact (hπ_one _).2 (h.sq_mem_a114P' ha₂ h₂)
  have hab : π a ≠ π b := fun hh => h.inv_mul_not_mem_a114P ha₁ h₂ ((hπ_eq a b).1 hh)
  have hconj : ∃ z : ↥Y ⧸ P.subgroupOf Y, z * π a * z⁻¹ = π b := by
    refine ⟨π ⟨a₁ * a₂, hyY⟩, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact (hπ_eq _ b).2 (h.conj_mem_a114P ha₁ ha₂ h₁ h₂)
  have hgen : Subgroup.closure ({π a, π b} : Set (↥Y ⧸ P.subgroupOf Y)) = ⊤ := by
    set H := Subgroup.closure ({π a, π b} : Set (↥Y ⧸ P.subgroupOf Y)) with hH
    have haH : π a ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
    have hbH : π b ∈ H :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have hQ₁ : (twoCoreCentralizer v₁).subgroupOf Y ≤ H.comap π := by
      intro x hx
      rw [Subgroup.mem_comap]
      have hx' : (x : G) ∈ twoCoreCentralizer v₁ := hx
      rcases h.mem_a114P_or_inv_mul_mem ha₁ h₁ hx' with h1 | h1
      · rw [(hπ_one x).2 h1]
        exact H.one_mem
      · have : π x = π a := (hπ_eq x a).2 h1
        rw [this]
        exact haH
    have hQ₂ : (twoCoreCentralizer v₂).subgroupOf Y ≤ H.comap π := by
      intro x hx
      rw [Subgroup.mem_comap]
      have hx' : (x : G) ∈ twoCoreCentralizer v₂ := hx
      rcases h.mem_a114P_or_inv_mul_mem' ha₂ h₂ hx' with h1 | h1
      · rw [(hπ_one x).2 h1]
        exact H.one_mem
      · have : π x = π b := (hπ_eq x b).2 h1
        rw [this]
        exact hbH
    have hsup : (twoCoreCentralizer v₁).subgroupOf Y ⊔ (twoCoreCentralizer v₂).subgroupOf Y =
        ⊤ := by
      have h1 : twoCoreCentralizer v₁ ≤ Y := le_sup_left
      have h2 : twoCoreCentralizer v₂ ≤ Y := le_sup_right
      rw [← Subgroup.subgroupOf_sup h1 h2]
      have h3 : twoCoreCentralizer v₁ ⊔ twoCoreCentralizer v₂ = Y := rfl
      rw [h3]
      exact Subgroup.subgroupOf_self _
    have hW : H.comap π = ⊤ := by
      rw [eq_top_iff, ← hsup]
      exact sup_le hQ₁ hQ₂
    rw [eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := hπsurj q
    have : x ∈ H.comap π := by rw [hW]; trivial
    exact this
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨hxY, hxC⟩ := hx
    have hcommA : π ⟨x, hxY⟩ * π a = π a * π ⟨x, hxY⟩ := by
      rw [← map_mul, ← map_mul]
      exact (hπ_eq _ _).2 (h.commutes_mod_a114P ha₁ hxC)
    have hcommB : π ⟨x, hxY⟩ * π b = π b * π ⟨x, hxY⟩ := by
      rw [← map_mul, ← map_mul]
      exact (hπ_eq _ _).2 (h.commutes_mod_a114P' ha₂ hxC)
    exact (hπ_one _).1 (A1b.dihedral_center_trivial hsqa hsqb hab hgen hconj hcommA hcommB)
  · have hRY : pCoreOf 2 Y ≤ Y := pCoreOf_le 2 Y
    have hRn : ∀ q ∈ ((pCoreOf 2 Y).subgroupOf Y).map π, ∀ g : ↥Y ⧸ P.subgroupOf Y,
        g * q * g⁻¹ ∈ ((pCoreOf 2 Y).subgroupOf Y).map π := by
      intro q hq g
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hq
      obtain ⟨g', rfl⟩ := hπsurj g
      refine Subgroup.mem_map.2 ⟨g' * r * g'⁻¹, ?_, by simp [map_mul, map_inv]⟩
      rw [Subgroup.mem_subgroupOf] at hr ⊢
      have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 Y g'.2) (r : G)).1 hr
      simpa using this
    have hR2 : ∀ q ∈ ((pCoreOf 2 Y).subgroupOf Y).map π, ∃ n : ℕ, q ^ 2 ^ n = 1 := by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hq
      have hr' : (r : G) ∈ pCoreOf 2 Y := Subgroup.mem_subgroupOf.1 hr
      obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 Y) ⟨(r : G), hr'⟩
      refine ⟨n, ?_⟩
      rw [← map_pow]
      have : r ^ 2 ^ n = 1 := by
        apply Subtype.ext
        have := congrArg Subtype.val hn
        simpa using this
      rw [this, map_one]
    have hbot := A1b.dihedral_normal_two_group hsqa hsqb hab hgen hconj hRn hR2
    have hmem : π ⟨x, hRY hx⟩ ∈ ((pCoreOf 2 Y).subgroupOf Y).map π :=
      Subgroup.mem_map.2 ⟨⟨x, hRY hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (hπ_one _).1 hmem

theorem exists_conj_eq [Finite G] (h : A114Hyp V v₁ v₂) {n : G}
    (hn : n ∈ Subgroup.normalizer (V : Set G)) :
    ∃ y ∈ a114Y v₁ v₂, y * v₁ * y⁻¹ = n * v₁ * n⁻¹ := by
  obtain ⟨a₁, a₂, ha₁, ha₂, h₁, h₂⟩ := h.exists_gens
  have hx : n * v₁ * n⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hn v₁).1 h.mem₁
  rcases h.mem_V_cases hx with h0 | h0 | h0 | h0
  · exfalso
    apply h.ne_one₁
    have h3 := mul_inv_eq_one.1 h0
    exact mul_left_cancel (h3.trans (mul_one n).symm)
  · exact ⟨1, Subgroup.one_mem _, by rw [h0]; simp⟩
  · exact ⟨a₁ * a₂, Subgroup.mul_mem _ (Subgroup.mem_sup_left ha₁) (Subgroup.mem_sup_right ha₂),
      by rw [h0]; exact h.y_act₁ ha₁ h₁ h₂⟩
  · exact ⟨a₂, Subgroup.mem_sup_right ha₂, by rw [h0]; exact h₂⟩

end A114Hyp

theorem a114_one [Finite G] {V : Subgroup G} {v₁ v₂ : G} (h : A114Hyp V v₁ v₂) :
    a114Y v₁ v₂ ≤ Subgroup.normalizer (V : Set G) ∧ autOn (a114Y v₁ v₂) V = ⊤ ∧
      a114Y v₁ v₂ ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (a114Y v₁ v₂) ∧
      pCoreOf 2 (a114Y v₁ v₂) = a114P V v₁ v₂ := by
  have hP2 : pCoreOf 2 (a114Y v₁ v₂) = a114P V v₁ v₂ :=
    le_antisymm h.a114_inf_le_and_pCore_le.2
      (le_pCoreOf_of_le_normalizer 2 (a114P_le_a114Y V v₁ v₂) h.a114Y_le_normalizer_a114P
        h.a114P_isPGroup)
  have hker : a114Y v₁ v₂ ⊓ Subgroup.centralizer (V : Set G) = a114P V v₁ v₂ :=
    le_antisymm h.a114_inf_le_and_pCore_le.1
      (le_inf (a114P_le_a114Y V v₁ v₂) (a114P_le_centralizer V v₁ v₂))
  exact ⟨h.a114Y_le_normalizer, h.autOn_a114Y, hker.trans hP2.symm, hP2⟩

theorem a114_two [Finite G] {V : Subgroup G} {v₁ v₂ : G} (h : A114Hyp V v₁ v₂) :
    a114Y v₁ v₂ = conjClosure (twoCoreCentralizer v₁) (Subgroup.normalizer (V : Set G)) ∧
      a114Y v₁ v₂ ≤ Subgroup.normalizer (V : Set G) ∧
      Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (a114Y v₁ v₂ : Set G) := by
  have hYN := h.a114Y_le_normalizer
  have heq : a114Y v₁ v₂ =
      conjClosure (twoCoreCentralizer v₁) (Subgroup.normalizer (V : Set G)) := by
    refine le_antisymm ?_ ?_
    · refine sup_le (le_conjClosure _ _) ?_
      obtain ⟨a₁, a₂, ha₁, ha₂, h₁, h₂⟩ := h.exists_gens
      have hy := h.y_act₁ ha₁ h₁ h₂
      have hyN : a₁ * a₂ ∈ Subgroup.normalizer (V : Set G) :=
        Subgroup.mul_mem _ (h.twoCoreCentralizer_le_normalizer ha₁)
          (h.symm.twoCoreCentralizer_le_normalizer ha₂)
      intro z hz
      have hQ : A1b.conjSub (a₁ * a₂) (twoCoreCentralizer v₁) = twoCoreCentralizer v₂ := by
        rw [A1b.conjSub_twoCoreCentralizer, hy]
      have hz' : z ∈ A1b.conjSub (a₁ * a₂) (twoCoreCentralizer v₁) := by rw [hQ]; exact hz
      rw [A1b.mem_conjSub_iff] at hz'
      have := mem_conjClosure hyN hz'
      simpa [mul_assoc] using this
    · refine conjClosure_le fun n hn z hz => ?_
      obtain ⟨y, hyY, hy⟩ := h.exists_conj_eq hn
      have h1 : n * z * n⁻¹ ∈ A1b.conjSub n (twoCoreCentralizer v₁) := A1b.mem_conjSub_of_mem hz
      rw [A1b.conjSub_twoCoreCentralizer, ← hy, ← A1b.conjSub_twoCoreCentralizer,
        A1b.mem_conjSub_iff] at h1
      have := (a114Y v₁ v₂).mul_mem ((a114Y v₁ v₂).mul_mem hyY (Subgroup.mem_sup_left h1))
        ((a114Y v₁ v₂).inv_mem hyY)
      simpa [mul_assoc] using this
  refine ⟨heq, hYN, ?_⟩
  rw [heq]
  exact le_normalizer_conjClosure _ _

theorem a114_three [Finite G] {V : Subgroup G} {v₁ v₂ : G} (h : A114Hyp V v₁ v₂) :
    Subgroup.normalizer (V : Set G) = a114Y v₁ v₂ ⊔ Subgroup.centralizer (V : Set G) ∧
      a114Y v₁ v₂ ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (a114Y v₁ v₂) ∧
      ⁅a114Y v₁ v₂, Subgroup.centralizer (V : Set G)⁆ ≤ pCoreOf 2 (a114Y v₁ v₂) ∧
      Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (pCoreOf 2 (a114Y v₁ v₂) : Set G) := by
  obtain ⟨hYN, hautY, hker, -⟩ := a114_one h
  obtain ⟨-, -, hNY⟩ := a114_two h
  have hCN : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.centralizer_le_normalizer _
  refine ⟨?_, hker, ?_, hNY.trans (normalizer_le_normalizer_pCoreOf 2 _)⟩
  · refine le_antisymm ?_ (sup_le hYN hCN)
    intro n hn
    have hρ : conjAct V ⟨n, hn⟩ ∈ autOn (a114Y v₁ v₂) V := by rw [hautY]; trivial
    obtain ⟨y, hy, hyρ⟩ := Subgroup.mem_map.1 hρ
    have hc : (y : G)⁻¹ * n ∈ Subgroup.centralizer (V : Set G) := by
      have h1 : conjAct V (y⁻¹ * ⟨n, hn⟩) = 1 := by
        rw [map_mul, map_inv, hyρ, inv_mul_cancel]
      simpa using A1b.conjAct_eq_one_iff.1 h1
    have hyY : (y : G) ∈ a114Y v₁ v₂ := Subgroup.mem_subgroupOf.1 hy
    have := Subgroup.mul_mem_sup hyY hc
    simpa using this
  · rw [← hker]
    refine Subgroup.commutator_le.2 fun y hy c hc => ?_
    have hcN : c ∈ Subgroup.normalizer (V : Set G) := hCN hc
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h1 : c * y⁻¹ * c⁻¹ ∈ a114Y v₁ v₂ :=
        (Subgroup.mem_normalizer_iff.1 (hNY hcN) y⁻¹).1 ((a114Y v₁ v₂).inv_mem hy)
      have := (a114Y v₁ v₂).mul_mem hy h1
      simpa [commutatorElement_def, mul_assoc] using this
    · have h2 := A1b.conj_mem_centralizer_of_mem_normalizer (hYN hy) hc
      have := (Subgroup.centralizer (V : Set G)).mul_mem h2
        ((Subgroup.centralizer (V : Set G)).inv_mem hc)
      simpa [commutatorElement_def] using this

namespace A1b

theorem eq_one_of_mem_pGroups {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    {A B : Subgroup G} (hA : IsPGroup p A) (hB : IsPGroup q B) {x : G} (hxA : x ∈ A)
    (hxB : x ∈ B) : x = 1 := by
  obtain ⟨k, hk⟩ := hA ⟨x, hxA⟩
  obtain ⟨l, hl⟩ := hB ⟨x, hxB⟩
  have h1 : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : x ^ q ^ l = 1 := by simpa using congrArg Subtype.val hl
  have hc : Nat.Coprime (p ^ k) (q ^ l) :=
    Nat.Coprime.pow k l ((Nat.coprime_primes hp.out hq.out).2 hpq)
  have h3 : orderOf x ∣ 1 := by
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rwa [hc.gcd_eq_one] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem pRank_le_evenRank [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup G}
    (hH : IsTwoLocal H) : pRank p H ≤ evenRank G := by
  refine le_csSup ?_ ⟨p, H, hp, hp2, hH, rfl⟩
  refine ⟨Nat.card G, ?_⟩
  rintro k ⟨q, K, hq, -, -, rfl⟩
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hq.one_lt K
  have h1 : q ^ pRank q K ≤ Nat.card G :=
    hE ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card E)
  exact (Nat.lt_pow_self hq.one_lt).le.trans h1

end A1b

theorem a114_four [Finite G] {V : Subgroup G} {v₁ v₂ : G} (h : A114Hyp V v₁ v₂)
    (hq : evenRank G ≤ 2) : pRank 3 (Subgroup.centralizer (V : Set G)) ≤ 1 := by
  have h3prime : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hYN, hautY, hker, -⟩ := a114_one h
  obtain ⟨-, -, hNY⟩ := a114_two h
  have hCN : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.centralizer_le_normalizer _
  obtain ⟨E, hEC, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (Subgroup.centralizer (V : Set G))
  have hE3 : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨S, hS, hES⟩ := exists_isSylowIn_ge 3 (hEC.trans hCN) hE3
  have hSY : IsSylowIn 3 (S ⊓ a114Y v₁ v₂) (a114Y v₁ v₂) :=
    hS.inf_normal hYN ((Subgroup.normal_subgroupOf_iff_le_normalizer hYN).2 hNY)
  have h3Y : 3 ∣ Nat.card (a114Y v₁ v₂) := by
    have h1 : Nat.card (autOn (a114Y v₁ v₂) V) ∣
        Nat.card ((a114Y v₁ v₂).subgroupOf (Subgroup.normalizer (V : Set G))) :=
      Subgroup.card_map_dvd _ (conjAct V)
    have h2 : Nat.card (autOn (a114Y v₁ v₂) V) = 6 := by
      rw [hautY, Subgroup.card_top, h.card_mulAut]
    have h3 : Nat.card ((a114Y v₁ v₂).subgroupOf (Subgroup.normalizer (V : Set G))) =
        Nat.card (a114Y v₁ v₂) := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv
    rw [h2, h3] at h1
    exact (by norm_num : 3 ∣ 6).trans h1
  have h3SY : 3 ∣ Nat.card (S ⊓ a114Y v₁ v₂ : Subgroup G) := by
    rw [hSY.card_eq]
    have hpos : 0 < (Nat.card (a114Y v₁ v₂)).factorization 3 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' h3Y
    exact dvd_pow_self 3 hpos.ne'
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' 3 h3SY
  have hyS : (y' : G) ∈ S := (inf_le_left : S ⊓ a114Y v₁ v₂ ≤ S) y'.2
  have hyY : (y' : G) ∈ a114Y v₁ v₂ := (inf_le_right : S ⊓ a114Y v₁ v₂ ≤ a114Y v₁ v₂) y'.2
  have hy3 : orderOf (y' : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy'
  have hcomm : ∀ e ∈ E, Commute e (y' : G) := by
    intro e he
    have heC : e ∈ Subgroup.centralizer (V : Set G) := hEC he
    have h1 : (y' : G) * e * (y' : G)⁻¹ * e⁻¹ ∈ pCoreOf 2 (a114Y v₁ v₂) := by
      rw [← hker]
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have h1 : e * (y' : G)⁻¹ * e⁻¹ ∈ a114Y v₁ v₂ :=
          (Subgroup.mem_normalizer_iff.1 (hNY (hCN heC)) _).1 ((a114Y v₁ v₂).inv_mem hyY)
        have := (a114Y v₁ v₂).mul_mem hyY h1
        simpa [mul_assoc] using this
      · exact (Subgroup.centralizer (V : Set G)).mul_mem
          (A1b.conj_mem_centralizer_of_mem_normalizer (hYN hyY) heC)
          ((Subgroup.centralizer (V : Set G)).inv_mem heC)
    have h2 : (y' : G) * e * (y' : G)⁻¹ * e⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem (S.mul_mem hyS (hES he)) (S.inv_mem hyS)) (S.inv_mem (hES he))
    have h3 := A1b.eq_one_of_mem_pGroups (by norm_num : (3 : ℕ) ≠ 2) hS.isPGroup
      (pCoreOf_isPGroup 2 _) h2 h1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h3).symm
  have hyE : (y' : G) ∉ E := by
    intro hyE
    have h1 : (y' : G) ∈ pCoreOf 2 (a114Y v₁ v₂) := by
      rw [← hker]
      exact Subgroup.mem_inf.2 ⟨hyY, hEC hyE⟩
    have h2 := A1b.eq_one_of_mem_pGroups (by norm_num : (3 : ℕ) ≠ 2) hS.isPGroup
      (pCoreOf_isPGroup 2 _) hyS h1
    rw [h2, orderOf_one] at hy3
    omega
  obtain ⟨hA, hAcard⟩ := exists_elemAbelian_sup_zpowers hE hy3 hcomm hyE
  have hAN : E ⊔ Subgroup.zpowers (y' : G) ≤ Subgroup.normalizer (V : Set G) :=
    sup_le (hEC.trans hCN) ((Subgroup.zpowers_le).2 (hYN hyY))
  have hrank : pRank 3 (Subgroup.centralizer (V : Set G)) + 1 ≤
      pRank 3 (Subgroup.normalizer (V : Set G)) :=
    le_pRank Nat.prime_three hAN hA (by rw [hAcard, hEcard, pow_succ])
  have hV2 : IsPGroup 2 V := fun g => ⟨1, Subtype.ext (by simpa using h.isElemAbelian.2 g g.2)⟩
  have hVbot : V ≠ ⊥ := by
    intro hV
    have hmem := h.mem₁
    rw [hV, Subgroup.mem_bot] at hmem
    exact h.ne_one₁ hmem
  have hloc : IsTwoLocal (Subgroup.normalizer (V : Set G)) := ⟨V, hVbot, hV2, rfl⟩
  have hle := A1b.pRank_le_evenRank Nat.prime_three (by norm_num) hloc
  omega

end CFSG.Quasithin
