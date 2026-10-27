module

public import CFSG.RankThree.PartTwo.Sec4.Item413CoverProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Res413Cover

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_inf_of_inner {L A : Subgroup G} {c : G}
    (hZ : ∀ z : L, z ∈ Subgroup.center L → z ^ 3 = 1 → z = 1)
    (hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) {a : G} (ha : a ∈ A)
    (hal₀ : ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹) :
    ∃ l ∈ A ⊓ L, a * l⁻¹ ∈ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := hAmax.prop
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set n := Nat.card (Subgroup.center L) with hn
  have hn3 : ¬ 3 ∣ n := by
    intro h3
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center L) 3 h3
    have hz3 : (z : L) ^ 3 = 1 := by
      have := pow_orderOf_eq_one z
      rw [hz] at this
      exact congrArg Subtype.val this
    have h1 := hZ z z.2 hz3
    have : z = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hz
    norm_num at hz
  have hk3 : n ^ 2 % 3 = 1 := by
    have : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.pow_mod, h]
  have huniq : ∀ l₁ ∈ L, ∀ l₂ ∈ L, l₁ ^ 3 = 1 → l₂ ^ 3 = 1 →
      (∀ x ∈ L, l₁ * x * l₁⁻¹ = l₂ * x * l₂⁻¹) → l₁ = l₂ := by
    intro l₁ h₁ l₂ h₂ h13 h23 h
    have hzL : l₂⁻¹ * l₁ ∈ L := L.mul_mem (L.inv_mem h₂) h₁
    have hzc := mem_center_of_conj_eq hzL fun x hx => by
      have := h x hx
      calc l₂⁻¹ * l₁ * x * (l₂⁻¹ * l₁)⁻¹ = l₂⁻¹ * (l₁ * x * l₁⁻¹) * l₂ := by group
        _ = l₂⁻¹ * (l₂ * x * l₂⁻¹) * l₂ := by rw [this]
        _ = x := by group
    have hzl : l₂ * (l₂⁻¹ * l₁) = (l₂⁻¹ * l₁) * l₂ := by
      have := (Subgroup.mem_center_iff.mp hzc) ⟨l₂, h₂⟩
      exact congrArg Subtype.val this
    have hz3 : (⟨l₂⁻¹ * l₁, hzL⟩ : L) ^ 3 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      have hc : Commute l₂⁻¹ l₁ := by
        have : l₂ * (l₂⁻¹ * l₁) * l₂⁻¹ = l₂⁻¹ * l₁ := by rw [hzl]; group
        have h' : l₁ * l₂⁻¹ = l₂⁻¹ * l₁ := by
          calc l₁ * l₂⁻¹ = l₂ * (l₂⁻¹ * l₁) * l₂⁻¹ := by group
            _ = l₂⁻¹ * l₁ := this
        exact h'.symm
      rw [hc.mul_pow, inv_pow, h23, h13, inv_one, one_mul]
    have := hZ _ hzc hz3
    have h1 : l₂⁻¹ * l₁ = 1 := congrArg Subtype.val this
    exact (inv_mul_eq_one.mp h1).symm
  obtain ⟨l₀, hl₀, hal₀⟩ := hal₀
  have ha3 : a ^ 3 = 1 := hA.2 a ha
  have hl₀3L : l₀ ^ 3 ∈ L := L.pow_mem hl₀ 3
  have hl₀3Z : (⟨l₀ ^ 3, hl₀3L⟩ : L) ∈ Subgroup.center L := by
    refine mem_center_of_conj_eq hl₀3L fun x hx => ?_
    rw [← conj_pow_eq hl₀ hal₀ 3 x hx, ha3, one_mul, inv_one, mul_one]
  have hl₀n : (l₀ ^ 3) ^ n = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center L) (x := ⟨_, hl₀3Z⟩)
    exact congrArg Subtype.val (congrArg Subtype.val this)
  set l := l₀ ^ (n ^ 2) with hldef
  have hlL : l ∈ L := L.pow_mem hl₀ _
  have hl3 : l ^ 3 = 1 := by
    rw [hldef, ← pow_mul, show n ^ 2 * 3 = 3 * n * n by ring, pow_mul, pow_mul, hl₀n, one_pow]
  have hapow : a ^ (n ^ 2) = a := by
    rw [← Nat.div_add_mod (n ^ 2) 3, hk3, pow_add, pow_mul, ha3, one_pow, one_mul, pow_one]
  have hal : ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹ := by
    intro x hx
    have := conj_pow_eq hl₀ hal₀ (n ^ 2) x hx
    rw [hapow] at this
    exact this
  have hlA : ∀ b ∈ A, b * l = l * b := by
    intro b hb
    have hbN := hAN hb
    have hbL : ∀ y ∈ L, b * y * b⁻¹ ∈ L := fun y hy =>
      (Subgroup.mem_normalizer_iff.mp hbN y).mp hy
    have hbinvL : ∀ y ∈ L, b⁻¹ * y * b ∈ L := fun y hy => by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbN) y).mp hy
      simpa using this
    have hm1 : b * l * b⁻¹ ∈ L := hbL l hlL
    have heq : b * l * b⁻¹ = l := by
      refine huniq _ hm1 _ hlL (by rw [conj_pow, hl3, mul_one, mul_inv_cancel]) hl3 ?_
      intro x hx
      have hy := hbinvL x hx
      calc b * l * b⁻¹ * x * (b * l * b⁻¹)⁻¹ = b * (l * (b⁻¹ * x * b) * l⁻¹) * b⁻¹ := by group
        _ = b * (a * (b⁻¹ * x * b) * a⁻¹) * b⁻¹ := by rw [hal _ hy]
        _ = (b * a * b⁻¹) * x * (b * a * b⁻¹)⁻¹ := by group
        _ = a * x * a⁻¹ := by
          rw [show b * a * b⁻¹ = a by rw [hcomm b hb a ha]; group]
        _ = l * x * l⁻¹ := hal x hx
    calc b * l = b * l * b⁻¹ * b := by group
      _ = l * b := by rw [heq]
  have hlA' : l ∈ A := mem_of_maximal_of_commute hAmax hl3 hlA
  refine ⟨l, ⟨hlA', hlL⟩, ?_⟩
  rw [← hAc]
  refine ⟨A.mul_mem ha (A.inv_mem hlA'), Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  have hx' : l⁻¹ * x * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hlL) hx) hlL
  have := hal _ hx'
  calc x * (a * l⁻¹) = a * (l⁻¹ * x * l) * a⁻¹ * (a * l⁻¹) := by rw [this]; group
    _ = a * l⁻¹ * x := by group

theorem card_le_three_mul' {L A : Subgroup G} {c : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hcA : c ∈ A) (hc3 : orderOf c = 3) {X : Subgroup G}
    (hXA : X ≤ A) (hdec : ∀ x ∈ X, ∃ l ∈ A ⊓ L, x * l⁻¹ ∈ Subgroup.zpowers c) :
    Nat.card X ≤ 3 * Nat.card (X ⊓ (A ⊓ L) : Subgroup G) := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set B := A ⊓ L with hB
  have hcB : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    hcomm x ((Subgroup.zpowers_le.mpr hcA) hx) y hy.1
  have hXle : X ≤ Subgroup.zpowers c ⊔ B := by
    intro a ha
    obtain ⟨l, hl, hal⟩ := hdec a ha
    have : a = a * l⁻¹ * l := by group
    rw [this]
    exact Subgroup.mul_mem_sup hal hl
  have hXB : ∀ x ∈ X, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    hcomm x (hXA hx) y hy.1
  obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute X B hXB
  obtain ⟨h2, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers c) B hcB
  have hle : Nat.card (X ⊔ B : Subgroup G) ≤ Nat.card (Subgroup.zpowers c ⊔ B : Subgroup G) :=
    Subgroup.card_le_of_le (sup_le hXle le_sup_right)
  have hinf : Nat.card (Subgroup.zpowers c ⊓ B : Subgroup G) ≥ 1 := Nat.card_pos
  rw [Nat.card_zpowers, hc3] at h2
  have hB0 : 0 < Nat.card B := Nat.card_pos
  have h3 : Nat.card (Subgroup.zpowers c ⊔ B : Subgroup G) ≤ 3 * Nat.card B := by
    nlinarith
  have h4 : Nat.card X * Nat.card B ≤ 3 * Nat.card B * Nat.card (X ⊓ B : Subgroup G) := by
    rw [← h1]
    exact Nat.mul_le_mul_right _ (hle.trans h3)
  have h5 : Nat.card X * Nat.card B ≤ 3 * Nat.card (X ⊓ B : Subgroup G) * Nat.card B := by
    linarith [h4, mul_comm (3 * Nat.card B) (Nat.card (X ⊓ B : Subgroup G))]
  exact Nat.le_of_mul_le_mul_right h5 hB0

omit [Finite G] in
theorem mem_of_pow_three_mem_of_pow_two_pow_mem {C : Subgroup G} {y : G} (h3 : y ^ 3 ∈ C)
    {k : ℕ} (h2 : y ^ 2 ^ k ∈ C) : y ∈ C := by
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, (3 : ℤ) * u + 2 ^ k * v = 1 := by
    have := Nat.Coprime.isCoprime hcop
    obtain ⟨u, v, h⟩ := this
    exact ⟨u, v, by push_cast at h; linarith⟩
  have : y = (y ^ 3) ^ u * (y ^ 2 ^ k) ^ v := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    push_cast
    rw [huv, zpow_one]
  rw [this]
  exact C.mul_mem (C.zpow_mem h3 u) (C.zpow_mem h2 v)

theorem false_of_inner_E (hG : SectionFourHyp G) {L A E : Subgroup G} {c : G}
    (hL : IsComponent L) (hT : IsTriple413 L A E c)
    (hdecE : ∀ e ∈ E, ∃ l ∈ A ⊓ L, e * l⁻¹ ∈ Subgroup.zpowers c)
    (hcL : Subgroup.zpowers c ⊓ L = ⊥) (h27 : 27 ≤ Nat.card (A ⊓ L : Subgroup G))
    (hcent : ∀ b ∈ A ⊓ L, b ≠ 1 → ∀ y ∈ L, y * b = b * y →
      y ^ 3 ∈ Subgroup.centralizer (L : Set G)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAmax, hAc, hc3, hE27, hEA, T, hTinv, hTE⟩ := hT
  have hA := hAmax.prop
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨-, hT2, hTN⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hTinv
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
  have hcA : c ∈ A := hcAC.1
  have hcC : c ∈ Subgroup.centralizer (L : Set G) := hcAC.2
  have hzC : Subgroup.zpowers c ≤ Subgroup.centralizer (L : Set G) := Subgroup.zpowers_le.mpr hcC
  set B := A ⊓ L with hBdef
  have hB : CFSG.Assembly.IsElemAbelian 3 B := isElemAbelian_of_le hA inf_le_left
  have hcop : Nat.Coprime 3 (Nat.card T) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT2
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  obtain ⟨F, hFE, hF9, hTF⟩ : ∃ F : Subgroup G, F ≤ E ∧ Nat.card F = 9 ∧
      ¬ T ⊓ Subgroup.centralizer (F : Set G) ≤ Subgroup.centralizer (E : Set G) := by
    by_contra hall
    push Not at hall
    exact hTE (Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three hE27.1
      (by rw [hE27.2]; norm_num) hTN hcop fun H hH h9 => hall H hH (by rw [h9]; norm_num))
  set T₀ := T ⊓ Subgroup.centralizer (F : Set G) with hT₀def
  have hFA : F ≤ A := hFE.trans hEA
  have hECF : E ≤ Subgroup.centralizer (F : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.mpr fun f hf => hcomm f (hFA hf) e (hEA he)
  have hET₀ : E ≤ Subgroup.normalizer (T₀ : Set G) :=
    le_trans (le_inf hTN (hECF.trans Subgroup.le_normalizer))
      Subgroup.inf_normalizer_le_normalizer_inf
  have hT₀2 : IsPGroup 2 T₀ := hT2.to_le inf_le_left
  obtain ⟨b, hbF, hbB, hb1⟩ : ∃ b ∈ F, b ∈ B ∧ b ≠ 1 := by
    by_contra hall
    push Not at hall
    have hinf : F ⊓ B = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxF, hxB⟩
      exact Subgroup.mem_bot.mpr (hall x hxF hxB)
    have := card_le_three_mul' hA hcA hc3 hFA fun x hx => hdecE x (hFE hx)
    rw [hinf, Subgroup.card_bot] at this
    omega
  have hbZ : ∃ x ∈ L, x * b ≠ b * x := by
    by_contra hall
    push Not at hall
    have hbC : b ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun x hx => hall x hx
    have hbc : b ∈ Subgroup.zpowers c := hAc ▸ ⟨hbB.1, hbC⟩
    have : b ∈ Subgroup.zpowers c ⊓ L := ⟨hbc, hbB.2⟩
    rw [hcL, Subgroup.mem_bot] at this
    exact hb1 this
  have hT₀N : T₀ ≤ Subgroup.normalizer (L : Set G) := fun t ht =>
    mem_normalizer_of_commute hL hbB.2 hbZ
      ((Subgroup.mem_centralizer_iff.mp ht.2 b hbF).symm)
  have hcommC : ∀ t ∈ T₀, ∀ e ∈ E, e * t * e⁻¹ * t⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    intro t ht e he
    obtain ⟨l, hl, hel⟩ := hdecE e he
    set z := e * l⁻¹ with hz
    have hzC' : z ∈ Subgroup.centralizer (L : Set G) := hzC hel
    have htN := hT₀N ht
    set w := t * e * t⁻¹ * e⁻¹ with hw
    set x := t * z * t⁻¹ * z⁻¹ with hx
    set y := t * l * t⁻¹ * l⁻¹ with hy
    have htzC : t * z * t⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu' : t⁻¹ * u * t ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN) u).mp hu
        simpa [mul_assoc] using this
      have := Subgroup.mem_centralizer_iff.mp hzC' _ hu'
      calc u * (t * z * t⁻¹) = t * ((t⁻¹ * u * t) * z) * t⁻¹ := by group
        _ = t * (z * (t⁻¹ * u * t)) * t⁻¹ := by rw [this]
        _ = t * z * t⁻¹ * u := by group
    have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.mul_mem _ htzC (Subgroup.inv_mem _ hzC')
    have hyL : y ∈ L := by
      have htl : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htN l).mp hl.2
      exact L.mul_mem htl (L.inv_mem hl.2)
    have hwxy : w = x * y := by
      have hzy : z⁻¹ * y = y * z⁻¹ :=
        (Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hzC') y hyL).symm
      have he' : e = z * l := by rw [hz]; group
      calc w = t * z * t⁻¹ * (t * l * t⁻¹ * l⁻¹) * z⁻¹ := by rw [hw, he']; group
        _ = t * z * t⁻¹ * (y * z⁻¹) := by rw [← hy]; group
        _ = t * z * t⁻¹ * (z⁻¹ * y) := by rw [hzy]
        _ = x * y := by rw [hx]; group
    have hxy : x * y = y * x := (Subgroup.mem_centralizer_iff.mp hxC y hyL).symm
    have htb : t * b = b * t := (Subgroup.mem_centralizer_iff.mp ht.2 b hbF).symm
    have hlb : l * b = b * l := hcomm l hl.1 b hbB.1
    have hyb : y * b = b * y := by
      calc y * b = t * l * t⁻¹ * l⁻¹ * b := rfl
        _ = t * l * t⁻¹ * (l⁻¹ * b) := by group
        _ = t * l * t⁻¹ * (b * l⁻¹) := by
          rw [show l⁻¹ * b = b * l⁻¹ by
            calc l⁻¹ * b = l⁻¹ * (b * l) * l⁻¹ := by group
              _ = l⁻¹ * (l * b) * l⁻¹ := by rw [hlb]
              _ = b * l⁻¹ := by group]
        _ = t * l * (t⁻¹ * b) * l⁻¹ := by group
        _ = t * l * (b * t⁻¹) * l⁻¹ := by
          rw [show t⁻¹ * b = b * t⁻¹ by
            calc t⁻¹ * b = t⁻¹ * (b * t) * t⁻¹ := by group
              _ = t⁻¹ * (t * b) * t⁻¹ := by rw [htb]
              _ = b * t⁻¹ := by group]
        _ = t * (l * b) * t⁻¹ * l⁻¹ := by group
        _ = t * (b * l) * t⁻¹ * l⁻¹ := by rw [hlb]
        _ = (t * b) * l * t⁻¹ * l⁻¹ := by group
        _ = (b * t) * l * t⁻¹ * l⁻¹ := by rw [htb]
        _ = b * y := by rw [hy]; group
    have hwT : w ∈ T₀ := by
      have h1 : e * t * e⁻¹ ∈ T₀ := (Subgroup.mem_normalizer_iff.mp (hET₀ he) t).mp ht
      have h2 : t * e * t⁻¹ * e⁻¹ = (e * t * e⁻¹ * t⁻¹)⁻¹ := by group
      rw [hw, h2]
      exact T₀.inv_mem (T₀.mul_mem h1 (T₀.inv_mem ht))
    obtain ⟨k, hk⟩ := hT₀2 ⟨w, hwT⟩
    have hwk : w ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hyk : y ^ 2 ^ k ∈ Subgroup.centralizer (L : Set G) := by
      have hxy' : Commute x y := hxy
      have h1 : w ^ 2 ^ k = x ^ 2 ^ k * y ^ 2 ^ k := by rw [hwxy, hxy'.mul_pow]
      rw [hwk] at h1
      have h2 : y ^ 2 ^ k = (x ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_right h1.symm
      rw [h2]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hxC _)
    have hy3 := hcent b hbB hb1 y hyL hyb
    have hyC := mem_of_pow_three_mem_of_pow_two_pow_mem hy3 hyk
    have hwC : w ∈ Subgroup.centralizer (L : Set G) := by
      rw [hwxy]; exact Subgroup.mul_mem _ hxC hyC
    have : e * t * e⁻¹ * t⁻¹ = w⁻¹ := by rw [hw]; group
    rw [this]
    exact Subgroup.inv_mem _ hwC
  set R := T₀ ⊓ Subgroup.centralizer (L : Set G) with hRdef
  have hR2 : IsPGroup 2 R := hT₀2.to_le inf_le_left
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := by
    intro a ha
    exact Sec4.Res413Cover.mem_normalizer_of_commute hL hbB.2 hbZ
      (hcomm a ha b hbB.1)
  have hCN : E ≤ Subgroup.normalizer ((Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have heN := hAN (hEA he)
    constructor
    · intro hg
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro u hu
      have hu' : e⁻¹ * u * e ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ heN) u).mp hu
        simpa [mul_assoc] using this
      have := hg _ hu'
      calc u * (e * g * e⁻¹) = e * ((e⁻¹ * u * e) * g) * e⁻¹ := by group
        _ = e * (g * (e⁻¹ * u * e)) * e⁻¹ := by rw [this]
        _ = e * g * e⁻¹ * u := by group
    · intro hg
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro u hu
      have hu' : e * u * e⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp heN u).mp hu
      have := hg _ hu'
      calc u * g = e⁻¹ * ((e * u * e⁻¹) * (e * g * e⁻¹)) * e := by group
        _ = e⁻¹ * ((e * g * e⁻¹) * (e * u * e⁻¹)) * e := by rw [this]
        _ = g * u := by group
  have hER : E ≤ Subgroup.normalizer (R : Set G) :=
    le_trans (le_inf hET₀ hCN) Subgroup.inf_normalizer_le_normalizer_inf
  have hRE : ¬ R ≤ Subgroup.centralizer (E : Set G) := by
    intro hcen
    apply hTF
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    set u := e * t * e⁻¹ * t⁻¹ with hu
    have huR : u ∈ R := by
      refine ⟨?_, hcommC t ht e he⟩
      have h1 : e * t * e⁻¹ ∈ T₀ := (Subgroup.mem_normalizer_iff.mp (hET₀ he) t).mp ht
      exact T₀.mul_mem h1 (T₀.inv_mem ht)
    have hue : e * u * e⁻¹ = u := by
      rw [Subgroup.mem_centralizer_iff.mp (hcen huR) e he, mul_inv_cancel_right]
    have het : e * t * e⁻¹ = u * t := by rw [hu]; group
    have he3 : e ^ 3 = 1 := hA.2 e (hEA he)
    have hpow : ∀ n : ℕ, e ^ n * t * (e ^ n)⁻¹ = u ^ n * t := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hun : e * u ^ n * e⁻¹ = u ^ n := by rw [← conj_pow, hue]
        calc e ^ (n + 1) * t * (e ^ (n + 1))⁻¹ = e * (e ^ n * t * (e ^ n)⁻¹) * e⁻¹ := by
              rw [pow_succ', mul_inv_rev]; group
          _ = e * (u ^ n * t) * e⁻¹ := by rw [ih]
          _ = (e * u ^ n * e⁻¹) * (e * t * e⁻¹) := by group
          _ = u ^ (n + 1) * t := by rw [hun, het, pow_succ]; group
    have h3 := hpow 3
    rw [he3] at h3
    have hu3 : u ^ 3 = 1 := by
      have h4 : t = u ^ 3 * t := by simpa using h3
      have := congrArg (· * t⁻¹) h4
      simpa using this.symm
    have hu1 : u = 1 := eq_one_of_isPGroup_two hR2 huR hu3
    have : e * t * e⁻¹ = t := by rw [het, hu1, one_mul]
    calc e * t = e * t * e⁻¹ * e := by group
      _ = t * e := by rw [this]
  have hRne : R ≠ ⊥ := fun h => hRE (h ▸ bot_le)
  have hcR : c ∈ Subgroup.normalizer (R : Set G) := by
    obtain ⟨r, hrR, hrE⟩ := Set.not_subset.mp hRE
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hrE
    push Not at hrE
    obtain ⟨e, he, her⟩ := hrE
    obtain ⟨l, hl, hel⟩ := hdecE e he
    set z := e * l⁻¹ with hz
    have hlr : l * r = r * l :=
      Subgroup.mem_centralizer_iff.mp hrR.2 l hl.2
    have hz1 : z ≠ 1 := by
      intro h1
      apply her
      have : e = l := by rw [← mul_inv_eq_one]; exact h1
      rw [this, hlr]
    have hzR : z ∈ Subgroup.normalizer (R : Set G) := by
      have hlN : l⁻¹ ∈ Subgroup.normalizer (R : Set G) := by
        refine Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ ?_)
        rw [Subgroup.mem_centralizer_iff]
        intro r' hr'
        exact (Subgroup.mem_centralizer_iff.mp hr'.2 l hl.2).symm
      exact Subgroup.mul_mem _ (hER he) hlN
    have hzz : Subgroup.zpowers z = Subgroup.zpowers c := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hel) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hc3]
      have hz3 : z ^ 3 = 1 := by
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hel
        rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
          (show c ^ 3 = 1 by rw [← hc3]; exact pow_orderOf_eq_one c), one_zpow]
      rw [orderOf_eq_prime hz3 hz1]
    have : c ∈ Subgroup.zpowers z := hzz ▸ Subgroup.mem_zpowers c
    exact (Subgroup.zpowers_le.mpr hzR) this
  have hcB : c ∉ B := fun h => by
    have : c ∈ Subgroup.zpowers c ⊓ L := ⟨Subgroup.mem_zpowers c, h.2⟩
    rw [hcL, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hc3
    norm_num at hc3
  have hDcard : Nat.card (B ⊔ Subgroup.zpowers c : Subgroup G) = 3 * Nat.card B :=
    Res417Five.card_sup_zpowers_eq_three_mul hc3 hcB fun a ha b hb =>
      hcomm a ha.1 b ((Subgroup.zpowers_le.mpr hcA) hb)
  have hDe : CFSG.Assembly.IsElemAbelian 3 (B ⊔ Subgroup.zpowers c) :=
    isElemAbelian_of_le hA (sup_le inf_le_left (Subgroup.zpowers_le.mpr hcA))
  have hBR : B ≤ Subgroup.normalizer (R : Set G) := by
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_centralizer_iff.mp hr.2 x hx.2).symm
  have hDN : B ⊔ Subgroup.zpowers c ≤ Subgroup.normalizer (R : Set G) :=
    sup_le hBR (Subgroup.zpowers_le.mpr hcR)
  have := Res417Five.card_le_27_of_le_normalizer hG hDe hR2 hRne hDN
  omega

end Res413Cover

end CFSG.RankThree.PartTwo.Sec4
