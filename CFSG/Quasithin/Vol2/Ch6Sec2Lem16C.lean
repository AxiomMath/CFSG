module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Vol2.Ch6S5Parab

public section

namespace CFSG.Quasithin.H13

open scoped commutatorElement

variable {G : Type} [Group G]

theorem comm_mul_right_ch616 {x y y' : G} (h : y * ⁅x, y'⁆ = ⁅x, y'⁆ * y) :
    ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
  simp only [commutatorElement_def] at h ⊢
  calc x * (y * y') * x⁻¹ * (y * y')⁻¹ = x * y * x⁻¹ * y⁻¹ * (y * (x * y' * x⁻¹ * y'⁻¹)) * y⁻¹ := by
        group
    _ = x * y * x⁻¹ * y⁻¹ * ((x * y' * x⁻¹ * y'⁻¹) * y) * y⁻¹ := by rw [h]
    _ = _ := by group

theorem eq_or_eq_of_card_four_ch616 {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q = 4)
    (hQ2 : ∀ q : Q, q * q = 1) {a b : Q} (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) (q : Q) :
    q = 1 ∨ q = a ∨ q = b ∨ q = a * b := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have hab1 : a * b ≠ 1 := fun h => hab (by
    calc a = a * (b * b) := by rw [hQ2, mul_one]
      _ = (a * b) * b := by group
      _ = b := by rw [h, one_mul])
  have haba : a * b ≠ a := fun h => hb (by
    calc b = a⁻¹ * (a * b) := by group
      _ = 1 := by rw [h, inv_mul_cancel])
  have habb : a * b ≠ b := fun h => ha (by
    calc a = (a * b) * b⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel])
  have hcard : ({1, a, b, a * b} : Finset Q).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair habb.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, haba.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ha.symm, hb.symm, hab1.symm⟩
  have huniv : ({1, a, b, a * b} : Finset Q) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcard, ← Nat.card_eq_fintype_card, hQ]
  have hq : q ∈ ({1, a, b, a * b} : Finset Q) := by rw [huniv]; exact Finset.mem_univ q
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hq

variable {U ZU Z : Subgroup G}

theorem comm_comm_mul_ch616 (hZZU : Z ≤ ZU) (hZUU : ZU ≤ U)
    (hZUc : ∀ z ∈ ZU, ∀ x ∈ U, x * z = z * x) (hcomm : ∀ x ∈ U, ∀ y ∈ U, ⁅x, y⁆ ∈ Z) {w : G}
    (hw : ∀ u ∈ U, ⁅w, u⁆ ∈ U) {x t t' : G} (hx : x ∈ U) (ht : t ∈ U) (ht' : t' ∈ U) :
    ⁅x, ⁅w, t * t'⁆⁆ = ⁅x, ⁅w, t⁆⁆ * ⁅x, ⁅w, t'⁆⁆ := by
  have hN := hw t ht
  have hN' := hw t' ht'
  have hcZ : ⁅t, ⁅w, t'⁆⁆ ∈ Z := hcomm t ht _ hN'
  have hcU : ⁅t, ⁅w, t'⁆⁆ ∈ U := hZUU (hZZU hcZ)
  have hcz : ∀ y ∈ U, ∀ y' ∈ U, y * ⁅x, y'⁆ = ⁅x, y'⁆ * y := fun y hy y' hy' =>
    hZUc _ (hZZU (hcomm x hx y' hy')) y hy
  have e : ⁅w, t * t'⁆ = ⁅w, t⁆ * (⁅t, ⁅w, t'⁆⁆ * ⁅w, t'⁆) := by
    simp only [commutatorElement_def]; group
  rw [e, comm_mul_right_ch616 (hcz _ hN _ (U.mul_mem hcU hN')),
    comm_mul_right_ch616 (hcz _ hcU _ hN')]
  have h1 : ⁅x, ⁅t, ⁅w, t'⁆⁆⁆ = 1 := by
    rw [commutatorElement_def, hZUc _ (hZZU hcZ) x hx, mul_inv_cancel_right, mul_inv_cancel]
  rw [h1, one_mul]

theorem comm_comm_symm_ch616 (hZZU : Z ≤ ZU) (hZUc : ∀ z ∈ ZU, ∀ x ∈ U, x * z = z * x)
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, ⁅x, y⁆ ∈ Z) (hZ2 : ∀ z ∈ Z, z * z = 1) {w : G} (hw2 : w * w = 1)
    (hwU : ∀ u ∈ U, w * u * w⁻¹ ∈ U) (hwZ : ∀ z ∈ Z, w * z = z * w) {x y : G} (hx : x ∈ U)
    (hy : y ∈ U) : ⁅x, ⁅w, y⁆⁆ = ⁅y, ⁅w, x⁆⁆ := by
  have hcen : ∀ c ∈ Z, ∀ u ∈ U, u * c = c * u := fun c hc u hu => hZUc c (hZZU hc) u hu
  have hinv2 : ∀ c ∈ Z, c⁻¹ = c := fun c hc => inv_eq_of_mul_eq_one_right (hZ2 c hc)
  have hcinv : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁻¹⁆ = ⁅a, b⁆ := by
    intro a ha b hb
    have := comm_mul_right_ch616 (x := a) (y := b) (y' := b⁻¹)
      (hcen _ (hcomm a ha _ (U.inv_mem hb)) b hb)
    rw [mul_inv_cancel, commutatorElement_one_right] at this
    rw [eq_inv_of_mul_eq_one_right this.symm, hinv2 _ (hcomm a ha b hb)]
  have hswap : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ = ⁅b, a⁆ := by
    intro a ha b hb
    rw [← commutatorElement_inv, hinv2 _ (hcomm b hb a ha)]
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hconj : ∀ a ∈ U, ∀ b ∈ U, ⁅a, w * b * w⁻¹⁆ = ⁅w * a * w⁻¹, b⁆ := by
    intro a ha b hb
    have ha' : w⁻¹ * a * w ∈ U := by
      have := hwU a ha
      rw [hwi] at this ⊢
      exact this
    have e : ⁅a, w * b * w⁻¹⁆ = w * ⁅w⁻¹ * a * w, b⁆ * w⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, hwZ _ (hcomm _ ha' b hb), mul_inv_cancel_right, hwi]
  have e1 : ⁅w, y⁆ = w * y * w⁻¹ * y⁻¹ := commutatorElement_def w y
  have e2 : ⁅w, x⁆ = w * x * w⁻¹ * x⁻¹ := commutatorElement_def w x
  rw [e1, e2, comm_mul_right_ch616 (hcen _ (hcomm x hx _ (U.inv_mem hy)) _ (hwU y hy)),
    comm_mul_right_ch616 (hcen _ (hcomm y hy _ (U.inv_mem hx)) _ (hwU x hx)),
    hcinv x hx y hy, hcinv y hy x hx, hconj x hx y hy, hswap _ (hwU x hx) y hy, hswap x hx y hy]

theorem mul_inv_mem_of_a2_ch616 (hZ2 : Nat.card Z = 2) (hZZU : Z ≤ ZU) (hZUU : ZU ≤ U)
    (hZUc : ∀ z ∈ ZU, ∀ x ∈ U, x * z = z * x)
    (hcen : ∀ x ∈ U, (∀ y ∈ U, y * x = x * y) → x ∈ ZU)
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, ⁅x, y⁆ ∈ Z) {v v' : G}
    (hN : ∀ u ∈ U, ⁅v, u⁆ ∈ U) (hN' : ∀ u ∈ U, ⁅v', u⁆ ∈ U)
    (hsym : ∀ x ∈ U, ∀ y ∈ U, ⁅x, ⁅v, y⁆⁆ = ⁅y, ⁅v, x⁆⁆)
    (hsym' : ∀ x ∈ U, ∀ y ∈ U, ⁅x, ⁅v', y⁆⁆ = ⁅y, ⁅v', x⁆⁆)
    (halt : ∀ x ∈ U, ⁅x, ⁅v, x⁆⁆ = 1) (halt' : ∀ x ∈ U, ⁅x, ⁅v', x⁆⁆ = 1)
    (hker : ∀ x ∈ U, ⁅v, x⁆ ∈ ZU ↔ ⁅v', x⁆ ∈ ZU) {x₀ y₀ : G} (hx₀ : x₀ ∈ U) (hy₀ : y₀ ∈ U)
    (hx₀Z : ⁅v, x₀⁆ ∉ ZU)
    (hdec : ∀ t ∈ U, ⁅v, t⁆ ∈ ZU ∨ ⁅v, x₀⁻¹ * t⁆ ∈ ZU ∨ ⁅v, y₀⁻¹ * t⁆ ∈ ZU ∨
      ⁅v, (x₀ * y₀)⁻¹ * t⁆ ∈ ZU) :
    ∀ t ∈ U, ⁅v', t⁆ * ⁅v, t⁆⁻¹ ∈ ZU := by
  have hone : ∀ x ∈ U, ∀ n ∈ ZU, ⁅x, n⁆ = 1 := fun x hx n hn => by
    rw [commutatorElement_def, hZUc n hn x hx, mul_inv_cancel_right, mul_inv_cancel]
  have bmul := fun {w : G} (hw : ∀ u ∈ U, ⁅w, u⁆ ∈ U) {x t t' : G} (hx : x ∈ U) (ht : t ∈ U)
    (ht' : t' ∈ U) => comm_comm_mul_ch616 hZZU hZUU hZUc hcomm hw hx ht ht'
  have hdec' : ∀ t ∈ U, ∃ k ∈ U, ⁅v, k⁆ ∈ ZU ∧ ⁅v', k⁆ ∈ ZU ∧
      (t = k ∨ t = x₀ * k ∨ t = y₀ * k ∨ t = x₀ * y₀ * k) := by
    intro t ht
    rcases hdec t ht with h0 | h0 | h0 | h0
    · exact ⟨t, ht, h0, (hker t ht).mp h0, Or.inl rfl⟩
    · exact ⟨x₀⁻¹ * t, U.mul_mem (U.inv_mem hx₀) ht, h0,
        (hker _ (U.mul_mem (U.inv_mem hx₀) ht)).mp h0, Or.inr (Or.inl (by group))⟩
    · exact ⟨y₀⁻¹ * t, U.mul_mem (U.inv_mem hy₀) ht, h0,
        (hker _ (U.mul_mem (U.inv_mem hy₀) ht)).mp h0, Or.inr (Or.inr (Or.inl (by group)))⟩
    · exact ⟨(x₀ * y₀)⁻¹ * t, U.mul_mem (U.inv_mem (U.mul_mem hx₀ hy₀)) ht, h0,
        (hker _ (U.mul_mem (U.inv_mem (U.mul_mem hx₀ hy₀)) ht)).mp h0,
        Or.inr (Or.inr (Or.inr (by group)))⟩
  have hval : ∀ {w : G} (hw : ∀ u ∈ U, ⁅w, u⁆ ∈ U), ∀ x ∈ U, ∀ t ∈ U, ∀ k ∈ U, ⁅w, k⁆ ∈ ZU →
      (t = k ∨ t = x₀ * k ∨ t = y₀ * k ∨ t = x₀ * y₀ * k) →
      ⁅x, ⁅w, t⁆⁆ = 1 ∨ ⁅x, ⁅w, t⁆⁆ = ⁅x, ⁅w, x₀⁆⁆ ∨ ⁅x, ⁅w, t⁆⁆ = ⁅x, ⁅w, y₀⁆⁆ ∨
        ⁅x, ⁅w, t⁆⁆ = ⁅x, ⁅w, x₀⁆⁆ * ⁅x, ⁅w, y₀⁆⁆ := by
    intro w hw x hx t ht k hk hkw htk
    rcases htk with rfl | rfl | rfl | rfl
    · exact Or.inl (hone x hx _ hkw)
    · right; left
      rw [bmul hw hx hx₀ hk, hone x hx _ hkw, mul_one]
    · right; right; left
      rw [bmul hw hx hy₀ hk, hone x hx _ hkw, mul_one]
    · right; right; right
      rw [bmul hw hx (U.mul_mem hx₀ hy₀) hk, hone x hx _ hkw, mul_one, bmul hw hx hx₀ hy₀]
  have hne : ∀ {w : G} (hw : ∀ u ∈ U, ⁅w, u⁆ ∈ U)
      (hsymw : ∀ x ∈ U, ∀ y ∈ U, ⁅x, ⁅w, y⁆⁆ = ⁅y, ⁅w, x⁆⁆) (haltw : ∀ x ∈ U, ⁅x, ⁅w, x⁆⁆ = 1)
      (hkerw : ∀ t ∈ U, ⁅v, t⁆ ∈ ZU → ⁅w, t⁆ ∈ ZU) (hx₀w : ⁅w, x₀⁆ ∉ ZU),
      ⁅x₀, ⁅w, y₀⁆⁆ ≠ 1 := by
    intro w hw hsymw haltw hkerw hx₀w h1
    apply hx₀w
    refine hcen _ (hw x₀ hx₀) fun y hy => ?_
    have hy1 : ⁅y, ⁅w, x₀⁆⁆ = 1 := by
      rw [← hsymw x₀ hx₀ y hy]
      obtain ⟨k, hk, hkv, -, htk⟩ := hdec' y hy
      rcases hval hw x₀ hx₀ y hy k hk (hkerw k hk hkv) htk with h | h | h | h
      · exact h
      · rw [h, haltw x₀ hx₀]
      · rw [h, h1]
      · rw [h, haltw x₀ hx₀, h1, one_mul]
    rw [commutatorElement_def] at hy1
    calc y * ⁅w, x₀⁆ = (y * ⁅w, x₀⁆ * y⁻¹ * ⁅w, x₀⁆⁻¹) * (⁅w, x₀⁆ * y) := by group
      _ = ⁅w, x₀⁆ * y := by rw [hy1, one_mul]
  have h1 := hne hN hsym halt (fun _ _ h => h) hx₀Z
  have h1' := hne hN' hsym' halt' (fun t ht h => (hker t ht).mp h)
    (fun h => hx₀Z ((hker x₀ hx₀).mpr h))
  have hZval : ⁅x₀, ⁅v, y₀⁆⁆ = ⁅x₀, ⁅v', y₀⁆⁆ := by
    have hm1 : ⁅x₀, ⁅v, y₀⁆⁆ ∈ Z := hcomm x₀ hx₀ _ (hN y₀ hy₀)
    have hm2 : ⁅x₀, ⁅v', y₀⁆⁆ ∈ Z := hcomm x₀ hx₀ _ (hN' y₀ hy₀)
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥Z)).mp hZ2
    have e1 := hy ⟨_, hm1⟩ (fun h => h1 (congrArg Subtype.val h))
    have e2 := hy ⟨_, hm2⟩ (fun h => h1' (congrArg Subtype.val h))
    exact congrArg Subtype.val (e1.trans e2.symm)
  have hZval' : ⁅y₀, ⁅v, x₀⁆⁆ = ⁅y₀, ⁅v', x₀⁆⁆ := by
    rw [← hsym x₀ hx₀ y₀ hy₀, ← hsym' x₀ hx₀ y₀ hy₀, hZval]
  have hE1 : ∀ x ∈ U, ⁅x₀, ⁅v, x⁆⁆ = ⁅x₀, ⁅v', x⁆⁆ := by
    intro x hx
    obtain ⟨k, hk, hkv, hkv', hxk⟩ := hdec' x hx
    rcases hxk with rfl | rfl | rfl | rfl
    · rw [hone x₀ hx₀ _ hkv, hone x₀ hx₀ _ hkv']
    · rw [bmul hN hx₀ hx₀ hk, bmul hN' hx₀ hx₀ hk, hone x₀ hx₀ _ hkv, hone x₀ hx₀ _ hkv',
        halt x₀ hx₀, halt' x₀ hx₀]
    · rw [bmul hN hx₀ hy₀ hk, bmul hN' hx₀ hy₀ hk, hone x₀ hx₀ _ hkv, hone x₀ hx₀ _ hkv',
        hZval]
    · rw [bmul hN hx₀ (U.mul_mem hx₀ hy₀) hk, bmul hN' hx₀ (U.mul_mem hx₀ hy₀) hk,
        hone x₀ hx₀ _ hkv, hone x₀ hx₀ _ hkv', bmul hN hx₀ hx₀ hy₀, bmul hN' hx₀ hx₀ hy₀,
        halt x₀ hx₀, halt' x₀ hx₀, hZval]
  have hE2 : ∀ x ∈ U, ⁅y₀, ⁅v, x⁆⁆ = ⁅y₀, ⁅v', x⁆⁆ := by
    intro x hx
    obtain ⟨k, hk, hkv, hkv', hxk⟩ := hdec' x hx
    rcases hxk with rfl | rfl | rfl | rfl
    · rw [hone y₀ hy₀ _ hkv, hone y₀ hy₀ _ hkv']
    · rw [bmul hN hy₀ hx₀ hk, bmul hN' hy₀ hx₀ hk, hone y₀ hy₀ _ hkv, hone y₀ hy₀ _ hkv',
        hZval']
    · rw [bmul hN hy₀ hy₀ hk, bmul hN' hy₀ hy₀ hk, hone y₀ hy₀ _ hkv, hone y₀ hy₀ _ hkv',
        halt y₀ hy₀, halt' y₀ hy₀]
    · rw [bmul hN hy₀ (U.mul_mem hx₀ hy₀) hk, bmul hN' hy₀ (U.mul_mem hx₀ hy₀) hk,
        hone y₀ hy₀ _ hkv, hone y₀ hy₀ _ hkv', bmul hN hy₀ hx₀ hy₀, bmul hN' hy₀ hx₀ hy₀,
        halt y₀ hy₀, halt' y₀ hy₀, hZval']
  have hE3 : ∀ x ∈ U, ∀ t ∈ U, ⁅x, ⁅v, t⁆⁆ = ⁅x, ⁅v', t⁆⁆ := by
    intro x hx t ht
    obtain ⟨k, hk, hkv, hkv', htk⟩ := hdec' t ht
    rcases htk with rfl | rfl | rfl | rfl
    · rw [hone x hx _ hkv, hone x hx _ hkv']
    · rw [bmul hN hx hx₀ hk, bmul hN' hx hx₀ hk, hone x hx _ hkv, hone x hx _ hkv',
        hsym x hx x₀ hx₀, hsym' x hx x₀ hx₀, hE1 x hx]
    · rw [bmul hN hx hy₀ hk, bmul hN' hx hy₀ hk, hone x hx _ hkv, hone x hx _ hkv',
        hsym x hx y₀ hy₀, hsym' x hx y₀ hy₀, hE2 x hx]
    · rw [bmul hN hx (U.mul_mem hx₀ hy₀) hk, bmul hN' hx (U.mul_mem hx₀ hy₀) hk,
        hone x hx _ hkv, hone x hx _ hkv', bmul hN hx hx₀ hy₀, bmul hN' hx hx₀ hy₀,
        hsym x hx x₀ hx₀, hsym' x hx x₀ hx₀, hsym x hx y₀ hy₀, hsym' x hx y₀ hy₀, hE1 x hx,
        hE2 x hx]
  intro t ht
  have hNt := hN t ht
  have hNt' := hN' t ht
  refine hcen _ (U.mul_mem hNt' (U.inv_mem hNt)) fun y hy => ?_
  have hinv : ⁅y, ⁅v, t⁆⁻¹⁆ = ⁅y, ⁅v, t⁆⁆⁻¹ := by
    have := comm_mul_right_ch616 (x := y) (y := ⁅v, t⁆) (y' := ⁅v, t⁆⁻¹)
      (hZUc _ (hZZU (hcomm y hy _ (U.inv_mem hNt))) _ hNt)
    rw [mul_inv_cancel, commutatorElement_one_right] at this
    exact eq_inv_of_mul_eq_one_right this.symm
  have hc : ⁅y, ⁅v', t⁆ * ⁅v, t⁆⁻¹⁆ = 1 := by
    rw [comm_mul_right_ch616 (hZUc _ (hZZU (hcomm y hy _ (U.inv_mem hNt))) _ hNt'), hinv,
      hE3 y hy t ht, mul_inv_cancel]
  rw [commutatorElement_def] at hc
  calc y * (⁅v', t⁆ * ⁅v, t⁆⁻¹) = (y * (⁅v', t⁆ * ⁅v, t⁆⁻¹) * y⁻¹ * (⁅v', t⁆ * ⁅v, t⁆⁻¹)⁻¹) *
        ((⁅v', t⁆ * ⁅v, t⁆⁻¹) * y) := by group
    _ = (⁅v', t⁆ * ⁅v, t⁆⁻¹) * y := by rw [hc, one_mul]

end CFSG.Quasithin.H13
