module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofTools
public import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Res413Cover

variable {G : Type} [Group G]

omit [Group G] in
theorem eq_one_of_isPGroup_two {G : Type*} [Group G] {T : Subgroup G} (hT : IsPGroup 2 T)
    {x : G} (hxT : x ∈ T) (hx3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hT ⟨x, hxT⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem conj_pow_eq {L : Subgroup G} {a l : G} (hl : l ∈ L)
    (hal : ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹) :
    ∀ k : ℕ, ∀ x ∈ L, a ^ k * x * (a ^ k)⁻¹ = l ^ k * x * (l ^ k)⁻¹ := by
  intro k
  induction k with
  | zero => intro x _; simp
  | succ k ih =>
    intro x hx
    have hxL : l ^ k * x * (l ^ k)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.pow_mem hl k) hx) (L.inv_mem (L.pow_mem hl k))
    calc a ^ (k + 1) * x * (a ^ (k + 1))⁻¹ = a * (a ^ k * x * (a ^ k)⁻¹) * a⁻¹ := by
          rw [pow_succ', mul_inv_rev]; group
      _ = a * (l ^ k * x * (l ^ k)⁻¹) * a⁻¹ := by rw [ih x hx]
      _ = l * (l ^ k * x * (l ^ k)⁻¹) * l⁻¹ := hal _ hxL
      _ = l ^ (k + 1) * x * (l ^ (k + 1))⁻¹ := by rw [pow_succ', mul_inv_rev]; group

theorem mem_center_of_conj_eq {L : Subgroup G} {z : G} (hz : z ∈ L)
    (h : ∀ x ∈ L, z * x * z⁻¹ = x) : (⟨z, hz⟩ : L) ∈ Subgroup.center L := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  change (y : G) * z = z * y
  have := h y y.2
  calc (y : G) * z = z * y * z⁻¹ * z := by rw [this]
    _ = z * y := by group

theorem zpowers_inf_eq_bot {L : Subgroup G} {c : G}
    (hZ : ∀ z : L, z ∈ Subgroup.center L → z ^ 3 = 1 → z = 1)
    (hcC : c ∈ Subgroup.centralizer (L : Set G)) (hc3 : c ^ 3 = 1) :
    Subgroup.zpowers c ⊓ L = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hyc, hyL⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyc
  have hyC : c ^ k ∈ Subgroup.centralizer (L : Set G) := Subgroup.zpow_mem _ hcC k
  have hmem : (⟨c ^ k, hyL⟩ : L) ∈ Subgroup.center L := by
    refine mem_center_of_conj_eq hyL fun x hx => ?_
    rw [← Subgroup.mem_centralizer_iff.mp hyC x hx, mul_inv_cancel_right]
  have h3 : (⟨c ^ k, hyL⟩ : L) ^ 3 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
  have := hZ _ hmem h3
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)

variable [Finite G]

theorem exists_mem_inf_of_forall_inner {L A : Subgroup G} {c : G}
    (hZ : ∀ z : L, z ∈ Subgroup.center L → z ^ 3 = 1 → z = 1)
    (hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    (hinner : ∀ a ∈ A, ∃ l ∈ L, ∀ x ∈ L, a * x * a⁻¹ = l * x * l⁻¹) :
    ∀ a ∈ A, ∃ l ∈ A ⊓ L, a * l⁻¹ ∈ Subgroup.zpowers c := by
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
  intro a ha
  obtain ⟨l₀, hl₀, hal₀⟩ := hinner a ha
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
    obtain ⟨m, hm, hbm⟩ := hinner b hb
    have hbL : ∀ y ∈ L, b * y * b⁻¹ ∈ L := fun y hy => by
      rw [hbm y hy]; exact L.mul_mem (L.mul_mem hm hy) (L.inv_mem hm)
    have hbinvL : ∀ y ∈ L, b⁻¹ * y * b ∈ L := by
      intro y hy
      have hy' : m⁻¹ * y * m ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hm) hy) hm
      have h1 := hbm _ hy'
      have h2 : b⁻¹ * y * b = m⁻¹ * y * m := by
        have : b * (m⁻¹ * y * m) * b⁻¹ = y := by rw [h1]; group
        calc b⁻¹ * y * b = b⁻¹ * (b * (m⁻¹ * y * m) * b⁻¹) * b := by rw [this]
          _ = m⁻¹ * y * m := by group
      rw [h2]; exact hy'
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

theorem card_le_three_mul {L A : Subgroup G} {c : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hcA : c ∈ A) (hc3 : orderOf c = 3)
    (hdec : ∀ a ∈ A, ∃ l ∈ A ⊓ L, a * l⁻¹ ∈ Subgroup.zpowers c) {X : Subgroup G}
    (hXA : X ≤ A) : Nat.card X ≤ 3 * Nat.card (X ⊓ (A ⊓ L) : Subgroup G) := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set B := A ⊓ L with hB
  have hcB : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    hcomm x ((Subgroup.zpowers_le.mpr hcA) hx) y hy.1
  have hAle : A ≤ Subgroup.zpowers c ⊔ B := by
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
    Subgroup.card_le_of_le (sup_le (hXA.trans hAle) le_sup_right)
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

theorem eq_bot_of_le_centralizer (hG : SectionFourHyp G) {L B S : Subgroup G}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hBL : B ≤ L) (hB81 : 81 ≤ Nat.card B)
    (hS2 : IsPGroup 2 S) (hSC : S ≤ Subgroup.centralizer (L : Set G)) : S = ⊥ := by
  by_contra hS
  have hBN : B ≤ Subgroup.normalizer (S : Set G) :=
    (hBL.trans (Subgroup.le_centralizer_iff.mp hSC)).trans (Subgroup.centralizer_le_normalizer _)
  have := Res417Five.card_le_27_of_le_normalizer hG hB hS2 hS hBN
  omega

theorem mem_of_pow_two_pow_mem {L : Subgroup G}
    (hC : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ Subgroup.centralizer (L : Set G) → S = ⊥)
    {x : G} (hxC : x ∈ Subgroup.centralizer (L : Set G)) {k : ℕ} (hxk : x ^ 2 ^ k ∈ L) :
    x ∈ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.even_or_odd (orderOf x) with hev | hodd
  · exfalso
    have h2 : 2 ∣ orderOf x := even_iff_two_dvd.mp hev
    set y := x ^ (orderOf x / 2) with hy
    have hyo : orderOf y = 2 := orderOf_pow_orderOf_div (orderOf_pos x).ne' h2
    have hS : IsPGroup 2 (Subgroup.zpowers y) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
    have hSC : Subgroup.zpowers y ≤ Subgroup.centralizer (L : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ hxC _)
    have h := hC _ hS hSC
    have hy1 : y = 1 := by
      have : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
      rw [h, Subgroup.mem_bot] at this
      exact this
    rw [hy1, orderOf_one] at hyo
    norm_num at hyo
  · have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact L.pow_mem hxk m

theorem mem_normalizer_of_commute {L : Subgroup G} (hL : IsComponent L) {b g : G} (hbL : b ∈ L)
    (hbZ : ∃ x ∈ L, x * b ≠ b * x) (hgb : g * b = b * g) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  set L' := L.map (MulAut.conj g).toMonoidHom with hL'
  have hL'c : IsComponent L' := CFSG.LocalCores.isComponent_map_mulEquiv _ hL
  have hbL' : b ∈ L' := by
    refine ⟨b, hbL, ?_⟩
    change g * b * g⁻¹ = b
    rw [hgb, mul_inv_cancel_right]
  rcases CFSG.LocalCores.distinct_components_commute hL hL'c with heq | hcomm
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [heq]
      exact ⟨h, hh, rfl⟩
    · intro hh
      rw [heq] at hh
      obtain ⟨h', hh', he⟩ := hh
      change g * h' * g⁻¹ = g * h * g⁻¹ at he
      have : h' = h := by
        have := congrArg (fun y => g⁻¹ * y * g) he
        simpa [mul_assoc] using this
      rw [← this]
      exact hh'
  · exfalso
    obtain ⟨x, hxL, hxb⟩ := hbZ
    apply hxb
    have hcen : L ≤ Subgroup.centralizer (L' : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact (Subgroup.mem_centralizer_iff.mp (hcen hxL) b hbL').symm

theorem exists_two_subgroup_of_isTriple413 (hG : SectionFourHyp G) {L A E : Subgroup G} {c : G}
    (hL : IsComponent L) (hT : IsTriple413 L A E c)
    (hdec : ∀ a ∈ A, ∃ l ∈ A ⊓ L, a * l⁻¹ ∈ Subgroup.zpowers c)
    (hcL : Subgroup.zpowers c ⊓ L = ⊥) (h81 : 81 ≤ Nat.card (A ⊓ L : Subgroup G)) :
    ∃ D T₁ : Subgroup G, D ≤ A ⊓ L ∧ 9 ≤ Nat.card D ∧ T₁ ≤ L ∧ IsPGroup 2 T₁ ∧
      D ≤ Subgroup.normalizer (T₁ : Set G) ∧ ¬ T₁ ≤ Subgroup.centralizer (D : Set G) := by
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
  have hC : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ Subgroup.centralizer (L : Set G) → S = ⊥ :=
    fun S hS hSC => eq_bot_of_le_centralizer hG hB inf_le_right h81 hS hSC
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := by
    intro a ha
    obtain ⟨l, hl, hal⟩ := hdec a ha
    have : a = a * l⁻¹ * l := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer _ (hzC hal))
      (Subgroup.le_normalizer hl.2)
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
    have := card_le_three_mul hA hcA hc3 hdec hFA
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
  have hcommL : ∀ t ∈ T₀, ∀ e ∈ E, e * t * e⁻¹ * t⁻¹ ∈ L := by
    intro t ht e he
    obtain ⟨l, hl, hel⟩ := hdec e (hEA he)
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
    have hwT : w ∈ T₀ := by
      have h1 : e * t * e⁻¹ ∈ T₀ := (Subgroup.mem_normalizer_iff.mp (hET₀ he) t).mp ht
      have h2 : t * e * t⁻¹ * e⁻¹ = (e * t * e⁻¹ * t⁻¹)⁻¹ := by group
      rw [hw, h2]
      exact T₀.inv_mem (T₀.mul_mem h1 (T₀.inv_mem ht))
    obtain ⟨k, hk⟩ := hT₀2 ⟨w, hwT⟩
    have hwk : w ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hxk : x ^ 2 ^ k ∈ L := by
      have hxy' : Commute x y := hxy
      have h1 : w ^ 2 ^ k = x ^ 2 ^ k * y ^ 2 ^ k := by rw [hwxy, hxy'.mul_pow]
      rw [hwk] at h1
      have h2 : x ^ 2 ^ k = (y ^ 2 ^ k)⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
      rw [h2]
      exact L.inv_mem (L.pow_mem hyL _)
    have hxL : x ∈ L := mem_of_pow_two_pow_mem hC hxC hxk
    have hwL : w ∈ L := by rw [hwxy]; exact L.mul_mem hxL hyL
    have : e * t * e⁻¹ * t⁻¹ = w⁻¹ := by rw [hw]; group
    rw [this]
    exact L.inv_mem hwL
  set T₁ := T₀ ⊓ L with hT₁def
  have hT₁2 : IsPGroup 2 T₁ := hT₀2.to_le inf_le_left
  have hET₁ : E ≤ Subgroup.normalizer (T₁ : Set G) :=
    le_trans (le_inf hET₀ (hEA.trans hAN)) Subgroup.inf_normalizer_le_normalizer_inf
  have hT₁E : ¬ T₁ ≤ Subgroup.centralizer (E : Set G) := by
    intro hcen
    apply hTF
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    set u := e * t * e⁻¹ * t⁻¹ with hu
    have huT : u ∈ T₁ := by
      refine ⟨?_, hcommL t ht e he⟩
      have h1 : e * t * e⁻¹ ∈ T₀ := (Subgroup.mem_normalizer_iff.mp (hET₀ he) t).mp ht
      exact T₀.mul_mem h1 (T₀.inv_mem ht)
    have hue : e * u * e⁻¹ = u := by
      rw [Subgroup.mem_centralizer_iff.mp (hcen huT) e he, mul_inv_cancel_right]
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
    have hu1 : u = 1 := eq_one_of_isPGroup_two hT₁2 huT hu3
    have : e * t * e⁻¹ = t := by rw [het, hu1, one_mul]
    calc e * t = e * t * e⁻¹ * e := by group
      _ = t * e := by rw [this]
  set D := (E ⊔ Subgroup.zpowers c) ⊓ B with hDdef
  have hEcA : E ⊔ Subgroup.zpowers c ≤ A := sup_le hEA (Subgroup.zpowers_le.mpr hcA)
  have hD9 : 9 ≤ Nat.card D := by
    have h1 : Nat.card (E ⊔ Subgroup.zpowers c : Subgroup G) ≤ 3 * Nat.card D :=
      card_le_three_mul hA hcA hc3 hdec hEcA
    have h2 : 27 ≤ Nat.card (E ⊔ Subgroup.zpowers c : Subgroup G) := by
      rw [← hE27.2]; exact Subgroup.card_le_of_le le_sup_left
    omega
  have hcT₁ : c ∈ Subgroup.normalizer (T₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (fun x hx => hx.2) hcC)
  have hDN : D ≤ Subgroup.normalizer (T₁ : Set G) :=
    inf_le_left.trans (sup_le hET₁ (Subgroup.zpowers_le.mpr hcT₁))
  refine ⟨D, T₁, inf_le_right, hD9, inf_le_right, hT₁2, hDN, fun hcen => hT₁E ?_⟩
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  obtain ⟨l, hl, hel⟩ := hdec e (hEA he)
  have hlD : l ∈ D := by
    refine ⟨?_, hl⟩
    have : l = (e * l⁻¹)⁻¹ * e := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right hel))
      (Subgroup.mem_sup_left he)
  have h1 : l * t = t * l := Subgroup.mem_centralizer_iff.mp (hcen ht) l hlD
  have h2 : t * (e * l⁻¹) = (e * l⁻¹) * t :=
    Subgroup.mem_centralizer_iff.mp (hzC hel) t ht.2
  calc e * t = (e * l⁻¹) * (l * t) := by group
    _ = (e * l⁻¹) * (t * l) := by rw [h1]
    _ = (t * (e * l⁻¹)) * l := by rw [h2]; group
    _ = t * e := by group

theorem exists_thetaQuot_of_two_subgroup {L D T₁ : Subgroup G} (hL : CFSG.IsQuasisimple L)
    (hZodd : Odd (Nat.card (Subgroup.center L))) (hD : CFSG.Assembly.IsElemAbelian 3 D)
    (hDL : D ≤ L) (hD9 : 9 ≤ Nat.card D) (hT₁L : T₁ ≤ L) (hT₁ : IsPGroup 2 T₁)
    (hDT : D ≤ Subgroup.normalizer (T₁ : Set G))
    (hTD : ¬ T₁ ≤ Subgroup.centralizer (D : Set G)) :
    ∃ D' T' : Subgroup (L ⧸ aschbacherSolvableCore 3 L), CFSG.Assembly.IsElemAbelian 3 D' ∧
      9 ≤ Nat.card D' ∧ IsPGroup 2 T' ∧ D' ≤ Subgroup.normalizer (T' : Set _) ∧
      ¬ T' ≤ Subgroup.centralizer (D' : Set _) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 L with hθ
  set q := QuotientGroup.mk' θ with hq
  have hθZ : θ ≤ Subgroup.center L := aschbacherSolvableCore_le_center hL
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
  set D₀ := D.subgroupOf L with hD₀
  set T₀ := T₁.subgroupOf L with hT₀
  have hD₀e : CFSG.Assembly.IsElemAbelian 3 D₀ := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      have := hD.1.1.comm ⟨((x : L) : G), Subgroup.mem_subgroupOf.mp x.2⟩
        ⟨((y : L) : G), Subgroup.mem_subgroupOf.mp y.2⟩
      have h := congrArg Subtype.val this
      exact h
    · apply Subtype.ext
      simpa using hD.2 _ (Subgroup.mem_subgroupOf.mp hx)
  have hD₀card : Nat.card D₀ = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv
  have hinj : D₀ ⊓ q.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxD, hxq⟩
    rw [hq, QuotientGroup.ker_mk'] at hxq
    have hx3 : x ^ 3 = 1 := Subtype.ext (by simpa using hD.2 _ (Subgroup.mem_subgroupOf.mp hxD))
    have h1 : orderOf (⟨x, hxq⟩ : θ) ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext hx3)
    have h2 : orderOf (⟨x, hxq⟩ : θ) ∣ Nat.card θ := orderOf_dvd_natCard _
    have h3 : orderOf (⟨x, hxq⟩ : θ) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · exact h
      · exact absurd (h ▸ h2) hθ3
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (orderOf_eq_one_iff.mp h3))
  have hcardD' : Nat.card (D₀.map q) = Nat.card D₀ := by
    have hqinj : Function.Injective (q.comp D₀.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have hx' : (x : L) ∈ D₀ ⊓ q.ker := ⟨x.2, by simpa [MonoidHom.mem_ker] using hx⟩
      rw [hinj, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.mpr (Subtype.ext hx')
    have hrange : (q.comp D₀.subtype).range = D₀.map q := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange]
    exact Nat.card_congr (MonoidHom.ofInjective hqinj).toEquiv.symm
  refine ⟨D₀.map q, T₀.map q, isElemAbelian_map q hD₀e, by rw [hcardD', hD₀card]; exact hD9,
    (hT₁.of_equiv (Subgroup.subgroupOfEquivOfLe hT₁L).symm).map q, ?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨d * t * d⁻¹, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hDT (Subgroup.mem_subgroupOf.mp hd)) t).mp
        (Subgroup.mem_subgroupOf.mp ht)
    · rintro ⟨t, ht, hty⟩
      refine ⟨d⁻¹ * t * d, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        have hd' : (d : G)⁻¹ ∈ Subgroup.normalizer (T₁ : Set G) :=
          Subgroup.inv_mem _ (hDT (Subgroup.mem_subgroupOf.mp hd))
        have := (Subgroup.mem_normalizer_iff.mp hd' t).mp (Subgroup.mem_subgroupOf.mp ht)
        simpa using this
      · rw [map_mul, map_mul, map_inv, hty]
        group
  · intro hcen
    apply hTD
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have htL := hT₁L ht
    have hdL := hDL hd
    have h1 : q ⟨t, htL⟩ * q ⟨d, hdL⟩ = q ⟨d, hdL⟩ * q ⟨t, htL⟩ := by
      have := Subgroup.mem_centralizer_iff.mp (hcen ⟨⟨t, htL⟩, ht, rfl⟩) (q ⟨d, hdL⟩)
        ⟨⟨d, hdL⟩, hd, rfl⟩
      exact this.symm
    set w : L := ⟨d, hdL⟩ * ⟨t, htL⟩ * (⟨d, hdL⟩ : L)⁻¹ * (⟨t, htL⟩ : L)⁻¹ with hw
    have hwθ : w ∈ θ := by
      have : q w = 1 := by
        rw [hw, map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
        group
      rwa [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have hwT : (w : G) ∈ T₁ := by
      simp only [hw, Subgroup.coe_mul, Subgroup.coe_inv]
      have h2 : d * t * d⁻¹ ∈ T₁ := (Subgroup.mem_normalizer_iff.mp (hDT hd) t).mp ht
      exact T₁.mul_mem h2 (T₁.inv_mem ht)
    have hwZ : w ∈ Subgroup.center L := hθZ hwθ
    obtain ⟨k, hk⟩ := hT₁ ⟨w, hwT⟩
    have hwk : w ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h3 : orderOf (⟨w, hwZ⟩ : Subgroup.center L) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext hwk)
    have h4 : orderOf (⟨w, hwZ⟩ : Subgroup.center L) ∣ Nat.card (Subgroup.center L) :=
      orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ k) (Nat.card (Subgroup.center L)) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hZodd)
    have h5 := Nat.eq_one_of_dvd_coprimes hcop h3 h4
    have hw1 : w = 1 := congrArg Subtype.val (orderOf_eq_one_iff.mp h5)
    have h6 : (d : G) * t * d⁻¹ * t⁻¹ = 1 := by
      have := congrArg Subtype.val hw1
      simpa [hw] using this
    calc d * t = (d * t * d⁻¹ * t⁻¹) * (t * d) := by group
      _ = t * d := by rw [h6, one_mul]

end Res413Cover

end CFSG.RankThree.PartTwo.Sec4
