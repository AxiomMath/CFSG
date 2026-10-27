module

public import CFSG.RankThree.PGroups.CentralCoprimeKernel
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public noncomputable section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup

theorem eq_one_of_commute_of_pCore_eq_bot {G : Type*} [Group G] [Finite G] {Γ P : Subgroup G}
    (hPΓ : P ≤ Γ) (hPn : (P.subgroupOf Γ).Normal) (hΓP : IsPGroup 2 (Γ ⧸ P.subgroupOf Γ))
    (hO2 : CFSG.pCore 2 Γ = ⊥) {a : G} (haΓ : a ∈ Γ) (haP : ∀ x ∈ P, a * x = x * a)
    (ha2 : ∃ k : ℕ, a ^ 2 ^ k = 1) : a = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup Γ := (centralizer (P : Set G)).subgroupOf Γ with hC
  have hmemC : ∀ c : Γ, c ∈ C ↔ ∀ x ∈ P, (c : G) * x = x * c := fun c => by
    rw [hC, mem_subgroupOf, mem_centralizer_iff]
    exact ⟨fun h x hx => (h x hx).symm, fun h x hx => (h x hx).symm⟩
  have hCn : C.Normal := ⟨fun c hc g => by
    rw [hmemC] at hc ⊢
    intro x hx
    have hx' : (g : G)⁻¹ * x * g ∈ P := by
      have h := hPn.conj_mem ⟨x, hPΓ hx⟩ hx g⁻¹
      rw [mem_subgroupOf] at h
      simpa using h
    have h1 := hc _ hx'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (g : G) * c * (g : G)⁻¹ * x = g * (c * ((g : G)⁻¹ * x * g)) * (g : G)⁻¹ := by group
      _ = g * (((g : G)⁻¹ * x * g) * c) * (g : G)⁻¹ := by rw [h1]
      _ = x * ((g : G) * c * (g : G)⁻¹) := by group⟩
  set N : Subgroup C := (P.subgroupOf Γ).subgroupOf C with hN
  have hNmem : ∀ n : C, n ∈ N ↔ ((n : Γ) : G) ∈ P := fun n => by
    rw [hN, mem_subgroupOf, mem_subgroupOf]
  have hNZ : N ≤ center C := fun n hn => by
    rw [mem_center_iff]
    intro c
    apply Subtype.ext
    apply Subtype.ext
    exact ((hmemC c).1 c.2 _ ((hNmem n).1 hn))
  have : N.Normal := ⟨fun n hn g => by
    have h := mem_center_iff.1 (hNZ hn) g
    rw [h, mul_inv_cancel_right]
    exact hn⟩
  have hCN : IsPGroup 2 (C ⧸ N) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hΓP (c : Γ)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hNmem]
    have h := (QuotientGroup.eq_one_iff (N := P.subgroupOf Γ) ((c : Γ) ^ 2 ^ k)).1
      (by rw [QuotientGroup.mk_pow]; exact hk)
    rw [mem_subgroupOf] at h
    simpa using h
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 C))
  obtain ⟨hQn, -, hQ2⟩ :=
    CFSG.RankThree.PGroups.sylow_normal_of_le_center_of_isPGroup_quotient Nat.prime_two hNZ hCN Q
  have : (Q : Subgroup C).Characteristic := Sylow.characteristic_of_normal Q hQn
  have hQΓ : ((Q : Subgroup C).map C.subtype).Normal := inferInstance
  have hle : (Q : Subgroup C).map C.subtype ≤ CFSG.pCore 2 Γ :=
    le_sSup ⟨hQΓ, Q.isPGroup'.map C.subtype⟩
  rw [hO2, le_bot_iff] at hle
  set c : C := ⟨⟨a, haΓ⟩, (hmemC _).2 haP⟩
  obtain ⟨k, hk⟩ := ha2
  have hc2 : ∃ k : ℕ, orderOf c = 2 ^ k := by
    have h : c ^ 2 ^ k = 1 := Subtype.ext (Subtype.ext hk)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h)
    exact ⟨m, hm⟩
  have hcQ := hQ2 c hc2
  have : (c : Γ) ∈ (Q : Subgroup C).map C.subtype := ⟨c, hcQ, rfl⟩
  rw [hle, mem_bot] at this
  exact congrArg Subtype.val this

section Involution

variable {W : Type*} [CommGroup W] {p : ℕ}

@[expose] def fixSub (α : MulAut W) : Subgroup W where
  carrier := {w | α w = w}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_mul] at hx hy ⊢
    rw [hx, hy]
  one_mem' := map_one α
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq, map_inv] at hx ⊢
    rw [hx]

@[expose] def invSub (α : MulAut W) : Subgroup W where
  carrier := {w | α w = w⁻¹}
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq, map_mul] at hx hy ⊢
    rw [hx, hy, mul_inv]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, map_one, inv_one]
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq, map_inv] at hx ⊢
    rw [hx]

theorem mem_fixSub {α : MulAut W} {w : W} : w ∈ fixSub α ↔ α w = w := Iff.rfl

theorem mem_invSub {α : MulAut W} {w : W} : w ∈ invSub α ↔ α w = w⁻¹ := Iff.rfl

theorem eq_one_of_sq_eq_one_of_pow_eq_one (hp : Odd p) {w : W} (h2 : w ^ 2 = 1)
    (hwp : w ^ p = 1) : w = 1 := by
  obtain ⟨k, hk⟩ := hp
  rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul] at hwp
  exact hwp

theorem exists_fix_mul_inv (hp : Odd p) (hWp : ∀ x : W, x ^ p = 1) {α : MulAut W}
    (hα : ∀ w, α (α w) = w) (w : W) :
    ∃ f ∈ fixSub α, ∃ i ∈ invSub α, f * i = w := by
  obtain ⟨k, hk⟩ := hp
  refine ⟨(w * α w) ^ (k + 1), ?_, (w * (α w)⁻¹) ^ (k + 1), ?_, ?_⟩
  · rw [mem_fixSub, map_pow, map_mul, hα, mul_comm]
  · rw [mem_invSub, map_pow, map_mul, map_inv, hα, ← inv_pow, mul_inv, inv_inv, mul_comm]
  · rw [← mul_pow, show w * α w * (w * (α w)⁻¹) = w ^ 2 by
      rw [mul_mul_mul_comm, mul_inv_cancel, mul_one, pow_two], ← pow_mul,
      show 2 * (k + 1) = p + 1 by omega, pow_succ, hWp, one_mul]

theorem fixSub_inf_invSub (hp : Odd p) (hWp : ∀ x : W, x ^ p = 1) (α : MulAut W) :
    fixSub α ⊓ invSub α = ⊥ := by
  refine eq_bot_iff.2 fun w hw => ?_
  obtain ⟨hf, hi⟩ := mem_inf.1 hw
  rw [mem_fixSub] at hf
  rw [mem_invSub, hf] at hi
  refine (mem_bot).2 (eq_one_of_sq_eq_one_of_pow_eq_one hp ?_ (hWp w))
  rw [pow_two]
  nth_rewrite 1 [hi]
  exact inv_mul_cancel w

theorem card_inf_fixSub_mul_card_inf_invSub [Finite W] (hp : Odd p) (hWp : ∀ x : W, x ^ p = 1)
    {α : MulAut W} (hα : ∀ w, α (α w) = w) {Q : Subgroup W} (hQ : ∀ w ∈ Q, α w ∈ Q) :
    Nat.card (Q ⊓ fixSub α : Subgroup W) * Nat.card (Q ⊓ invSub α : Subgroup W) = Nat.card Q := by
  rw [← Nat.card_prod]
  refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨(x.1 : W) * x.2,
    mul_mem (mem_inf.1 x.1.2).1 (mem_inf.1 x.2.2).1⟩) ⟨?_, ?_⟩)
  · rintro ⟨⟨f, hf⟩, ⟨i, hi⟩⟩ ⟨⟨f', hf'⟩, ⟨i', hi'⟩⟩ h
    have h' : f * i = f' * i' := congrArg Subtype.val h
    have hm : f'⁻¹ * f ∈ fixSub α ⊓ invSub α := by
      refine mem_inf.2 ⟨mul_mem (inv_mem (mem_inf.1 hf').2) (mem_inf.1 hf).2, ?_⟩
      have e : f'⁻¹ * f = i' * i⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h', mul_inv_cancel_right]
      rw [e]
      exact mul_mem (mem_inf.1 hi').2 (inv_mem (mem_inf.1 hi).2)
    rw [fixSub_inf_invSub hp hWp, mem_bot, inv_mul_eq_one] at hm
    subst hm
    have hii : i = i' := mul_left_cancel h'
    subst hii
    rfl
  · rintro ⟨w, hw⟩
    obtain ⟨k, hk⟩ := hp
    refine ⟨⟨⟨(w * α w) ^ (k + 1), mem_inf.2 ⟨pow_mem (mul_mem hw (hQ w hw)) _, ?_⟩⟩,
      ⟨(w * (α w)⁻¹) ^ (k + 1), mem_inf.2 ⟨pow_mem (mul_mem hw (inv_mem (hQ w hw))) _, ?_⟩⟩⟩,
      Subtype.ext ?_⟩
    · rw [mem_fixSub, map_pow, map_mul, hα, mul_comm]
    · rw [mem_invSub, map_pow, map_mul, map_inv, hα, ← inv_pow, mul_inv, inv_inv, mul_comm]
    · change (w * α w) ^ (k + 1) * (w * (α w)⁻¹) ^ (k + 1) = w
      rw [← mul_pow, show w * α w * (w * (α w)⁻¹) = w ^ 2 by
        rw [mul_mul_mul_comm, mul_inv_cancel, mul_one, pow_two], ← pow_mul,
        show 2 * (k + 1) = p + 1 by omega, pow_succ, hWp, one_mul]

theorem fix_or_inv_of_card_prime [Finite W] (hp : p.Prime) (hp2 : p ≠ 2)
    (hWp : ∀ x : W, x ^ p = 1) {α : MulAut W} (hα : ∀ w, α (α w) = w) {Q : Subgroup W}
    (hQ : ∀ w ∈ Q, α w ∈ Q) (hQp : Nat.card Q = p) :
    (∀ w ∈ Q, α w = w) ∨ ∀ w ∈ Q, α w = w⁻¹ := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have h := card_inf_fixSub_mul_card_inf_invSub hodd hWp hα hQ
  rw [hQp] at h
  rcases Nat.prime_mul_iff.1 (h ▸ hp) with ⟨-, h1⟩ | ⟨-, h1⟩
  · left
    rw [h1, mul_one] at h
    have heq : Q ⊓ fixSub α = Q := eq_of_le_of_card_ge inf_le_left (by rw [h, hQp])
    have hle : Q ≤ fixSub α := heq ▸ inf_le_right
    exact fun w hw => hle hw
  · right
    rw [h1, one_mul] at h
    have heq : Q ⊓ invSub α = Q := eq_of_le_of_card_ge inf_le_left (by rw [h, hQp])
    have hle : Q ≤ invSub α := heq ▸ inf_le_right
    exact fun w hw => hle hw

end Involution

section Rank

variable {W : Type*} [CommGroup W] [Finite W] {p : ℕ}

theorem mul_comm_of_sq_eq_one {A : Type*} [Group A] (hA : ∀ a : A, a ^ 2 = 1) (a b : A) :
    a * b = b * a := by
  have h : ∀ x : A, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_left (by rw [← pow_two, hA])
  rw [← h (a * b), mul_inv_rev, h a, h b]

theorem card_le_four_of_injective (hp : p.Prime) (hp2 : p ≠ 2) (hWp : ∀ x : W, x ^ p = 1)
    (hW : Nat.card W ∣ p ^ 2) {A : Type*} [Group A] [Finite A] (hA : ∀ a : A, a ^ 2 = 1)
    (φ : A →* MulAut W) (hφ : Function.Injective φ) :
    Nat.card A ≤ 4 ∧ (Nat.card A = 4 → ∃ t₁ t₂ : A, ∃ Q₁ Q₂ : Subgroup W,
      Nat.card Q₁ = p ∧ Nat.card Q₂ = p ∧ Q₁ ⊔ Q₂ = ⊤ ∧
      (∀ x ∈ Q₁, φ t₁ x = x⁻¹) ∧ (∀ x ∈ Q₂, φ t₁ x = x) ∧
      (∀ x ∈ Q₁, φ t₂ x = x) ∧ (∀ x ∈ Q₂, φ t₂ x = x⁻¹)) := by
  classical
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hinvol : ∀ a : A, ∀ w, φ a (φ a w) = w := fun a w => by
    rw [← MulAut.mul_apply, ← map_mul, ← pow_two, hA, map_one, MulAut.one_apply]
  have htop : ∀ a : A, fixSub (φ a) ⊔ invSub (φ a) = ⊤ := fun a => by
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨f, hf, i, hi, rfl⟩ := exists_fix_mul_inv hodd hWp (hinvol a) w
    exact mul_mem_sup hf hi
  have hext : ∀ t : A, ∀ α β : MulAut W, (∀ w ∈ fixSub (φ t), α w = β w) →
      (∀ w ∈ invSub (φ t), α w = β w) → α = β := fun t α β h1 h2 => by
    ext w
    obtain ⟨f, hf, i, hi, rfl⟩ := exists_fix_mul_inv hodd hWp (hinvol t) w
    rw [map_mul, map_mul, h1 f hf, h2 i hi]
  by_cases hcase : ∃ t : A, fixSub (φ t) ≠ ⊥ ∧ invSub (φ t) ≠ ⊥
  · obtain ⟨t, hfix, hinv⟩ := hcase
    have hcard := card_inf_fixSub_mul_card_inf_invSub hodd hWp (hinvol t) (Q := ⊤)
      fun w _ => mem_top _
    rw [top_inf_eq, top_inf_eq, card_top] at hcard
    have hdvd₂ : Nat.card (fixSub (φ t)) ∣ p ^ 2 := (Dvd.intro _ hcard).trans hW
    have hdvd₁ : Nat.card (invSub (φ t)) ∣ p ^ 2 := (Dvd.intro_left _ hcard).trans hW
    obtain ⟨a, ha, hfa⟩ := (Nat.dvd_prime_pow hp).1 hdvd₂
    obtain ⟨b, hb, hib⟩ := (Nat.dvd_prime_pow hp).1 hdvd₁
    have ha0 : a ≠ 0 := fun h => hfix (card_eq_one.1 (by rw [hfa, h, pow_zero]))
    have hb0 : b ≠ 0 := fun h => hinv (card_eq_one.1 (by rw [hib, h, pow_zero]))
    have hab : a + b ≤ 2 := by
      have h := hcard ▸ hW
      rw [hfa, hib, ← pow_add] at h
      exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h
    have hQ₂ : Nat.card (fixSub (φ t)) = p := by
      rw [hfa, show a = 1 by omega, pow_one]
    have hQ₁ : Nat.card (invSub (φ t)) = p := by
      rw [hib, show b = 1 by omega, pow_one]
    have hcomm := mul_comm_of_sq_eq_one hA
    have hpres₁ : ∀ s : A, ∀ w ∈ invSub (φ t), φ s w ∈ invSub (φ t) := fun s w hw => by
      rw [mem_invSub] at hw ⊢
      rw [← MulAut.mul_apply, ← map_mul, hcomm t s, map_mul, MulAut.mul_apply, hw, map_inv]
    have hpres₂ : ∀ s : A, ∀ w ∈ fixSub (φ t), φ s w ∈ fixSub (φ t) := fun s w hw => by
      rw [mem_fixSub] at hw ⊢
      rw [← MulAut.mul_apply, ← map_mul, hcomm t s, map_mul, MulAut.mul_apply, hw]
    have hd₁ := fun s => fix_or_inv_of_card_prime hp hp2 hWp (hinvol s) (hpres₁ s) hQ₁
    have hd₂ := fun s => fix_or_inv_of_card_prime hp hp2 hWp (hinvol s) (hpres₂ s) hQ₂
    set σ : A → Bool × Bool := fun s =>
      (decide (∀ w ∈ invSub (φ t), φ s w = w⁻¹), decide (∀ w ∈ fixSub (φ t), φ s w = w⁻¹))
      with hσdef
    have hagree : ∀ (Q : Subgroup W) (s s' : A),
        ((∀ w ∈ Q, φ s w = w) ∨ ∀ w ∈ Q, φ s w = w⁻¹) →
        ((∀ w ∈ Q, φ s' w = w) ∨ ∀ w ∈ Q, φ s' w = w⁻¹) →
        decide (∀ w ∈ Q, φ s w = w⁻¹) = decide (∀ w ∈ Q, φ s' w = w⁻¹) →
        ∀ w ∈ Q, φ s w = φ s' w := by
      intro Q s s' hs hs' h w hw
      by_cases h1 : ∀ w ∈ Q, φ s w = w⁻¹
      · have h1' : ∀ w ∈ Q, φ s' w = w⁻¹ := by
          have := h ▸ (decide_eq_true h1)
          exact of_decide_eq_true this
        rw [h1 w hw, h1' w hw]
      · have h1' : ¬ ∀ w ∈ Q, φ s' w = w⁻¹ := by
          have := h ▸ (decide_eq_false h1)
          exact of_decide_eq_false this
        rw [hs.resolve_right h1 w hw, hs'.resolve_right h1' w hw]
    have hσ : Function.Injective σ := by
      intro s s' h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      exact hφ (hext t _ _ (hagree _ s s' (hd₂ s) (hd₂ s') h2)
        (hagree _ s s' (hd₁ s) (hd₁ s') h1))
    have hB4 : Nat.card (Bool × Bool) = 4 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool]
    have hle : Nat.card A ≤ 4 := hB4 ▸ Nat.card_le_card_of_injective σ hσ
    refine ⟨hle, fun h4 => ?_⟩
    have hbij : Function.Bijective σ := hσ.bijective_of_nat_card_le (by rw [h4, hB4])
    obtain ⟨t₁, ht₁⟩ := hbij.2 (true, false)
    obtain ⟨t₂, ht₂⟩ := hbij.2 (false, true)
    have e₁ := congrArg Prod.fst ht₁
    have e₂ := congrArg Prod.snd ht₁
    have e₃ := congrArg Prod.fst ht₂
    have e₄ := congrArg Prod.snd ht₂
    simp only [hσdef, decide_eq_true_eq, decide_eq_false_iff_not] at e₁ e₂ e₃ e₄
    refine ⟨t₁, t₂, invSub (φ t), fixSub (φ t), hQ₁, hQ₂, by rw [sup_comm]; exact htop t,
      e₁, (hd₂ t₁).resolve_right e₂, (hd₁ t₂).resolve_right e₃, e₄⟩
  ·
    push Not at hcase
    have hinvW : ∀ a : A, a ≠ 1 → ∀ w, φ a w = w⁻¹ := by
      intro a ha w
      by_cases hf : fixSub (φ a) = ⊥
      · have hi : invSub (φ a) = ⊤ := by rw [← htop a, hf, bot_sup_eq]
        have hw : w ∈ invSub (φ a) := by rw [hi]; exact mem_top w
        exact hw
      · exfalso
        have hi := hcase a hf
        have hf' : fixSub (φ a) = ⊤ := by rw [← htop a, hi, sup_bot_eq]
        apply ha
        apply hφ
        ext w
        have hw : w ∈ fixSub (φ a) := by rw [hf']; exact mem_top w
        rw [map_one, MulAut.one_apply]
        exact hw
    have hinj : Function.Injective fun a : A => decide (a = 1) := by
      intro a b h
      simp only at h
      by_cases ha : a = 1
      · have hb : b = 1 := by
          have := h ▸ (decide_eq_true ha)
          exact of_decide_eq_true this
        rw [ha, hb]
      · have hb : b ≠ 1 := by
          have := h ▸ (decide_eq_false ha)
          exact of_decide_eq_false this
        have hab : φ (a * b) = 1 := by
          ext w
          rw [map_mul, MulAut.mul_apply, hinvW b hb, hinvW a ha, inv_inv, MulAut.one_apply]
        have h1 : a * b = 1 := hφ (by rw [hab, map_one])
        have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by rw [← pow_two, hA])
        rw [mul_eq_one_iff_eq_inv, hbinv] at h1
        exact h1
    have hB2 : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
    have h2 : Nat.card A ≤ 2 := hB2 ▸ Nat.card_le_card_of_injective _ hinj
    exact ⟨by omega, fun h4 => by omega⟩

end Rank

end CFSG.Quasithin.SteinbergCD
