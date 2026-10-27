module

public import CFSG.Quasithin.H13.U3S1347W

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open

theorem card_mulAut_eq_card_GL {W : Type*} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) :
    letI : Module (ZMod 2) (Additive W) :=
      AddCommGroup.zmodModule (n := 2) fun x => by
        show Additive.ofMul ((Additive.toMul x) ^ 2) = 0
        rw [hW2]; rfl
    Nat.card (MulAut W) = Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) (Additive W)) := by
  let _ : Module (ZMod 2) (Additive W) :=
    AddCommGroup.zmodModule (n := 2) fun x => by
      show Additive.ofMul ((Additive.toMul x) ^ 2) = 0
      rw [hW2]; rfl
  refine Nat.card_congr ((MulEquiv.toAdditive (G := W) (H := W)).trans ?_)
  refine Equiv.trans ?_ (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
    (Additive W)).toEquiv.symm
  exact
    { toFun := fun e => LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap 2) e.bijective
      invFun := fun l => l.toAddEquiv
      left_inv := fun e => by ext; rfl
      right_inv := fun l => by ext; rfl }

theorem card_mulAut_dvd {W : Type*} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    (hW : Nat.card W ≤ 16) : Nat.card (MulAut W) ∣ 20160 := by
  let _ : Module (ZMod 2) (Additive W) :=
    AddCommGroup.zmodModule (n := 2) fun x => by
      show Additive.ofMul ((Additive.toMul x) ^ 2) = 0
      rw [hW2]; rfl
  rw [card_mulAut_eq_card_GL hW2]
  have : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
  set n := Module.finrank (ZMod 2) (Additive W) with hn
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive W) hn.symm
  rw [← Nat.card_congr (Matrix.GeneralLinearGroup.toLin' b).toEquiv, Matrix.card_GL_field,
    ZMod.card]
  have hcard : Nat.card (Additive W) = 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h16 : 2 ^ n ≤ 2 ^ 4 := by
    have : Nat.card (Additive W) = Nat.card W := rfl
    rw [← hcard, this]
    exact hW
  have hn4 : n ≤ 4 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h16
  interval_cases n <;> decide

@[expose] def fixAutU3 {W : Type*} [Group W] (α : MulAut W) : Subgroup W where
  carrier := {w | α w = w}
  mul_mem' := fun {a b} ha hb => by
    show α (a * b) = a * b
    rw [map_mul, show α a = a from ha, show α b = b from hb]
  one_mem' := map_one α
  inv_mem' := fun {a} ha => by
    show α a⁻¹ = a⁻¹
    rw [map_inv, show α a = a from ha]

theorem card_modEq_fixAutU3 {W : Type*} [Group W] [Finite W] {q : ℕ} [hq : Fact q.Prime]
    {α β : MulAut W} (hα : α ^ q = 1) (hαβ : α * β = β * α) :
    Nat.card (fixAutU3 β) ≡ Nat.card ↥(fixAutU3 β ⊓ fixAutU3 α) [MOD q] := by
  set A := zpowers α with hA
  have hAq : IsPGroup q ↥A := by
    rintro ⟨a, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα, one_zpow]
  have hcomm : ∀ a ∈ A, a * β = β * a := by
    rintro _ ⟨n, rfl⟩
    exact ((Commute.zpow_left hαβ n)).eq
  let act : MulAction ↥A ↥(fixAutU3 β) :=
    { smul := fun a w => ⟨(a : MulAut W) w, by
        show β ((a : MulAut W) w) = (a : MulAut W) w
        rw [← MulAut.mul_apply, ← hcomm a a.2, MulAut.mul_apply, w.2]⟩
      one_smul := fun w => rfl
      mul_smul := fun a b w => rfl }
  have h1 := hAq.card_modEq_card_fixedPoints ↥(fixAutU3 β)
  suffices e : MulAction.fixedPoints ↥A ↥(fixAutU3 β) ≃ ↥(fixAutU3 β ⊓ fixAutU3 α) by
    rwa [Nat.card_congr e] at h1
  exact
    { toFun := fun x => ⟨x.1, mem_inf.2 ⟨x.1.2, by
        have := x.2 ⟨α, mem_zpowers α⟩
        exact congrArg Subtype.val this⟩⟩
      invFun := fun w => ⟨⟨w, (mem_inf.1 w.2).1⟩, fun a => by
        have hst : α ∈ MulAction.stabilizer (MulAut W) (w : W) := (mem_inf.1 w.2).2
        have ha : (a : MulAut W) ∈ MulAction.stabilizer (MulAut W) (w : W) :=
          (zpowers_le.2 hst) a.2
        exact Subtype.ext ha⟩
      left_inv := fun x => rfl
      right_inv := fun w => rfl }

theorem fixAutU3_one {W : Type*} [Group W] : fixAutU3 (1 : MulAut W) = ⊤ :=
  eq_top_iff.2 fun _ _ => rfl

theorem eq_one_of_fixAutU3_eq_top {W : Type*} [Group W] {α : MulAut W} (h : fixAutU3 α = ⊤) :
    α = 1 :=
  MulEquiv.ext fun w => by
    have : w ∈ fixAutU3 α := h ▸ mem_top w
    exact this

theorem exists_card_lt_of_ne_top {W : Type*} [Group W] [Finite W] (hW2 : IsPGroup 2 W) {n : ℕ}
    (hn : Nat.card W = 2 ^ n) {U : Subgroup W} (hU : U ≠ ⊤) : ∃ m, Nat.card U = 2 ^ m ∧ m < n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (hW2.to_subgroup U).exists_card_eq
  refine ⟨m, hm, ?_⟩
  have hlt : Nat.card U < Nat.card W := by
    refine lt_of_le_of_ne (card_le_card_group U) fun h => hU (eq_top_of_card_eq U h)
  rw [hm, hn] at hlt
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt

theorem comm_of_card_dvd_sq {E : Type*} [Group E] [Finite E] {p : ℕ} [hp : Fact p.Prime]
    (h : Nat.card E ∣ p ^ 2) (a b : E) : a * b = b * a := by
  obtain ⟨e, he, hce⟩ := (Nat.dvd_prime_pow hp.out).1 h
  interval_cases e
  · rw [pow_zero] at hce
    have : Subsingleton E := (Nat.card_eq_one_iff_unique.1 hce).1
    exact Subsingleton.elim _ _
  · rw [pow_one] at hce
    have : IsCyclic E := isCyclic_of_prime_card hce
    exact IsCyclic.isMulCommutative.is_comm.comm a b
  · exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq hce).is_comm.comm a b

theorem exists_abelian_of_small {W : Type*} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    (hW : Nat.card W ≤ 16) {X : Subgroup (MulAut W)} (hXs : Group.IsSolvable ↥X)
    (hX2 : ∀ P : Subgroup ↥X, IsPGroup 2 ↥P → Nat.card ↥P ≤ 2) {t k : MulAut W} (ht : t ∈ X)
    (hk : k ∈ X) (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1) (htk : t * k * t⁻¹ = k⁻¹) {u : W} (hu : u ≠ 1)
    (hku : k u = u) :
    ∃ M : Subgroup (MulAut W), M ≤ X ∧ (∀ a ∈ M, ∀ b ∈ M, a * b = b * a) ∧
      ∀ g ∈ X, Odd (orderOf g) → g ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX20160 : Nat.card ↥X ∣ 20160 :=
    (card_subgroup_dvd_card X).trans (card_mulAut_dvd hW2 hW)
  have hW2g : IsPGroup 2 W := fun w => ⟨1, by rw [pow_one, hW2]⟩
  obtain ⟨n, hn⟩ := hW2g.exists_card_eq
  have hn4 : n ≤ 4 := by
    have : 2 ^ n ≤ 2 ^ 4 := by rw [← hn]; exact hW
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  have hk3' := card_modEq_fixAutU3 (q := 3) (α := k) (β := 1) hk3 (by rw [mul_one, one_mul])
  rw [fixAutU3_one, top_inf_eq, card_top, hn] at hk3'
  have hkne : fixAutU3 k ≠ ⊤ := fun h => hk1 (eq_one_of_fixAutU3_eq_top h)
  obtain ⟨m, hm, hmn⟩ := exists_card_lt_of_ne_top hW2g hn hkne
  have hm1 : 1 ≤ m := by
    by_contra h0
    have h0' : m = 0 := by omega
    rw [h0', pow_zero] at hm
    have : u ∈ fixAutU3 k := hku
    exact hu ((card_eq_one.1 hm) ▸ this : u ∈ (⊥ : Subgroup W))
  rw [hm] at hk3'
  have hnm : (n = 3 ∧ m = 1) ∨ (n = 4 ∧ m = 2) := by
    interval_cases n <;> interval_cases m <;> simp_all [Nat.ModEq]
  obtain ⟨M₀, hM₀n, hM₀c, a, hM₀i⟩ : ∃ M₀ : Subgroup ↥X,
      CFSG.GroupTheory.IsNormalPComplement 2 M₀ := by
    refine (CFSG.GroupTheory.frobenius_normal_p_complement (G := ↥X) 2).1.2 fun Q hQ => ?_
    rintro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨0, ?_⟩
    rw [pow_zero, pow_one, QuotientGroup.eq_one_iff, mem_subgroupOf, mem_centralizer_iff]
    intro x hx
    have hgx : (g : ↥X) * x * (g : ↥X)⁻¹ ∈ Q := (mem_normalizer_iff.1 g.2 x).1 hx
    exact (comm_of_card_le_two (hX2 Q hQ) hx hgx).symm
  set M := M₀.map X.subtype
  have hodd : ∀ g ∈ X, Odd (orderOf g) → g ∈ M := by
    intro g hg ho
    have h1 : orderOf (QuotientGroup.mk (⟨g, hg⟩ : ↥X) : ↥X ⧸ M₀) ∣ 2 ^ a := by
      rw [← hM₀i]
      exact orderOf_dvd_natCard _
    have h2 : orderOf (QuotientGroup.mk (⟨g, hg⟩ : ↥X) : ↥X ⧸ M₀) ∣ orderOf g := by
      have := orderOf_map_dvd (QuotientGroup.mk' M₀) ⟨g, hg⟩
      rwa [QuotientGroup.mk'_apply, Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (orderOf g) (2 ^ a) :=
      Nat.Coprime.pow_right a (Nat.coprime_two_right.2 ho)
    have h3 := Nat.eq_one_of_dvd_coprimes hcop h2 h1
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
    exact ⟨_, h3, rfl⟩
  have hYdvd : Nat.card ↥M₀ ∣ 315 := by
    have h1 : Nat.card ↥M₀ ∣ 64 * 315 := (card_subgroup_dvd_card M₀).trans hX20160
    exact (Nat.Coprime.pow_right 6 hM₀c).dvd_of_dvd_mul_left h1
  have hYs : Group.IsSolvable ↥M₀ := inferInstance
  have hkM : (⟨k, hk⟩ : ↥X) ∈ M₀ := by
    have hko : orderOf k = 3 := orderOf_eq_prime hk3 hk1
    obtain ⟨y, hy, hye⟩ := hodd k hk (by rw [hko]; decide)
    have : y = ⟨k, hk⟩ := Subtype.ext hye
    rw [← this]
    exact hy
  have h357 : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥M₀ → q = 3 ∨ q = 5 ∨ q = 7 := by
    intro q hq hqd
    have h1 : q ∣ 3 ^ 2 * (5 * 7) := hqd.trans (by norm_num at hYdvd ⊢; exact hYdvd)
    rcases (Nat.Prime.dvd_mul hq).1 h1 with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h))
    · rcases (Nat.Prime.dvd_mul hq).1 h with h' | h'
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h'))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h'))
  have hOq : ∀ q : ℕ, q.Prime → (q = 5 ∨ q = 7) → CFSG.pCore q ↥M₀ = ⊥ := by
    intro q hq hq57
    have : Fact q.Prime := ⟨hq⟩
    by_contra hne
    set P := CFSG.pCore q ↥M₀ with hPdef
    have hPp : IsPGroup q ↥P := CFSG.pCore_isPGroup
    obtain ⟨e, he⟩ := hPp.exists_card_eq
    have hPdvd : Nat.card ↥P ∣ 315 := (card_subgroup_dvd_card P).trans hYdvd
    have he1 : e = 1 := by
      have hpos : e ≠ 0 := by
        rintro rfl
        rw [pow_zero] at he
        exact hne (card_eq_one.1 he)
      rw [he] at hPdvd
      have h2 : ¬ q ^ 2 ∣ 315 := by rcases hq57 with rfl | rfl <;> decide
      by_contra hne1
      exact h2 ((pow_dvd_pow q (by omega : 2 ≤ e)).trans hPdvd)
    rw [he1, pow_one] at he
    have : Nontrivial ↥P := (nontrivial_iff_ne_bot P).2 hne
    obtain ⟨⟨f, hfP⟩, hf1⟩ := exists_ne (1 : ↥P)
    have hf1' : f ≠ 1 := fun h => hf1 (Subtype.ext h)
    have hfq : f ^ q = 1 := by
      have := pow_card_eq_one' (G := ↥P) (x := ⟨f, hfP⟩)
      rw [he] at this
      simpa using congrArg Subtype.val this
    set P' := P.map M₀.subtype
    have hP'n : P'.Normal := by
      refine ⟨fun x hx g => ?_⟩
      obtain ⟨y, hy, rfl⟩ := hx
      have hch := (characteristic_iff_map_eq.1 (CFSG.pCore_characteristic (p := q) (G := ↥M₀)))
        (MulAut.conjNormal (H := M₀) g)
      have hmem : MulAut.conjNormal (H := M₀) g y ∈ P := by
        rw [hPdef, ← hch]
        exact ⟨y, hy, rfl⟩
      exact ⟨_, hmem, by simp [MulAut.conjNormal_apply]⟩
    have hP'card : Nat.card ↥P' = q := by
      rw [card_map_of_injective M₀.subtype_injective, he]
    have hP'c : IsCyclic ↥P' := isCyclic_of_prime_card hP'card
    set ρ := MulAut.conjNormal (H := P') with hρ
    have hρk : ρ ⟨k, hk⟩ = 1 := by
      have hcom := F6.mulAut_comm_of_isCyclic (ρ ⟨t, ht⟩) (ρ ⟨k, hk⟩)
      have h1 : ρ ⟨t, ht⟩ * ρ ⟨k, hk⟩ * (ρ ⟨t, ht⟩)⁻¹ = (ρ ⟨k, hk⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
        congr 1
        exact Subtype.ext htk
      rw [hcom, mul_inv_cancel_right] at h1
      have h3 : ρ ⟨k, hk⟩ ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨k, hk⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hk3)
        rw [this, map_one]
      have h2 : ρ ⟨k, hk⟩ * ρ ⟨k, hk⟩ = 1 := by
        nth_rw 2 [h1]
        exact mul_inv_cancel _
      calc ρ ⟨k, hk⟩ = ρ ⟨k, hk⟩ ^ 3 * (ρ ⟨k, hk⟩ * ρ ⟨k, hk⟩)⁻¹ := by group
        _ = 1 := by rw [h3, h2, one_mul, inv_one]
    obtain ⟨fX, hfX⟩ : ∃ fX : ↥X, fX = (f : ↥X) := ⟨_, rfl⟩
    have hfP' : fX ∈ P' := by
      rw [hfX]
      exact ⟨f, hfP, rfl⟩
    have hkfX : fX * ⟨k, hk⟩ = ⟨k, hk⟩ * fX := by
      have h1 := congrArg Subtype.val (DFunLike.congr_fun hρk ⟨fX, hfP'⟩)
      rw [hρ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      dsimp only at h1
      calc fX * ⟨k, hk⟩ = (⟨k, hk⟩ * fX * (⟨k, hk⟩ : ↥X)⁻¹) * ⟨k, hk⟩ := by rw [h1]
        _ = ⟨k, hk⟩ * fX := by group
    have hfWq : (fX : MulAut W) ^ q = 1 := by
      rw [hfX]
      have := congrArg (fun z : ↥M₀ => ((z : ↥X) : MulAut W)) hfq
      simpa using this
    have hfW1 : (fX : MulAut W) ≠ 1 := by
      rw [hfX]
      exact fun h => hf1' (Subtype.ext (Subtype.ext h))
    have hkf : (fX : MulAut W) * k = k * (fX : MulAut W) := congrArg Subtype.val hkfX
    have hc1 := card_modEq_fixAutU3 (q := q) (α := (fX : MulAut W)) (β := 1) hfWq
      (by rw [mul_one, one_mul])
    rw [fixAutU3_one, top_inf_eq, card_top, hn] at hc1
    obtain ⟨j, hj, hjn⟩ := exists_card_lt_of_ne_top hW2g hn
      (fun h => hfW1 (eq_one_of_fixAutU3_eq_top h))
    rw [hj] at hc1
    have hc2 := card_modEq_fixAutU3 (q := q) (α := (fX : MulAut W)) (β := k) hfWq hkf
    rw [hm] at hc2
    obtain ⟨i, hi⟩ := (hW2g.to_subgroup (fixAutU3 k ⊓ fixAutU3 (fX : MulAut W))).exists_card_eq
    have hij : i ≤ j := by
      have : 2 ^ i ∣ 2 ^ j := by
        rw [← hi, ← hj]
        exact card_dvd_of_le inf_le_right
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
    rw [hi] at hc2
    rcases hnm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hq57 with rfl | rfl <;>
      interval_cases j <;> interval_cases i <;> revert hc1 hc2 <;> decide
  have hP₃p : IsPGroup 3 ↥(CFSG.pCore 3 ↥M₀) := CFSG.pCore_isPGroup
  have hF3 : CFSG.fittingSubgroup ↥M₀ ≤ CFSG.pCore 3 ↥M₀ := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.1 p.1.2
    rcases h357 _ hpp hpd with h | h | h
    · exact le_of_eq (by rw [h])
    · rw [h, hOq 5 (by norm_num) (Or.inl rfl)]
      exact bot_le
    · rw [h, hOq 7 (by norm_num) (Or.inr rfl)]
      exact bot_le
  have hCP₃ : centralizer (CFSG.pCore 3 ↥M₀ : Set ↥M₀) ≤ CFSG.pCore 3 ↥M₀ :=
    (centralizer_le hF3).trans
      ((CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hYs).trans hF3)
  obtain ⟨e, he⟩ := hP₃p.exists_card_eq
  have he2 : e ≤ 2 := by
    have h1 : 3 ^ e ∣ 315 := by
      rw [← he]
      exact (card_subgroup_dvd_card _).trans hYdvd
    by_contra h
    exact absurd ((pow_dvd_pow 3 (by omega : 3 ≤ e)).trans h1) (by decide)
  have h3only : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥M₀ → q = 3 := by
    intro q hq hqd
    have : Fact q.Prime := ⟨hq⟩
    rcases h357 q hq hqd with h | hq57
    · exact h
    exfalso
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥M₀) q hqd
    set α := MulAut.conjNormal (H := CFSG.pCore 3 ↥M₀) y with hα
    have hαq : α ^ q = 1 := by
      rw [hα, ← map_pow, ← hy, pow_orderOf_eq_one, map_one]
    have hc := card_modEq_fixAutU3 (q := q) (α := α) (β := 1) hαq (by rw [mul_one, one_mul])
    rw [fixAutU3_one, top_inf_eq, card_top, he] at hc
    obtain ⟨i, hi⟩ := (hP₃p.to_subgroup (fixAutU3 α)).exists_card_eq
    have hie : i ≤ e := by
      have : 3 ^ i ∣ 3 ^ e := by
        rw [← hi, ← he]
        exact card_subgroup_dvd_card _
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
    rw [hi] at hc
    have hie' : i = e := by
      rcases hq57 with rfl | rfl <;> interval_cases e <;> interval_cases i <;>
        first | rfl | (exfalso; revert hc; decide)
    have htop : fixAutU3 α = ⊤ := eq_top_of_card_eq _ (by rw [hi, hie', he])
    have hα1 : α = 1 := eq_one_of_fixAutU3_eq_top htop
    have hyC : y ∈ centralizer (CFSG.pCore 3 ↥M₀ : Set ↥M₀) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h1 := congrArg Subtype.val (DFunLike.congr_fun hα1 ⟨x, hx⟩)
      rw [hα, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      dsimp only at h1
      calc x * y = (y * x * y⁻¹) * y := by rw [h1]
        _ = y * x := by group
    obtain ⟨r, hr⟩ := hP₃p ⟨y, hCP₃ hyC⟩
    have hr' : y ^ 3 ^ r = 1 := by simpa using congrArg Subtype.val hr
    have hqd3 : q ∣ 3 ^ r := by
      rw [← hy]
      exact orderOf_dvd_of_pow_eq_one hr'
    have hq3 : q = 3 :=
      (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow hqd3)
    omega
  have h9 : Nat.card ↥M₀ ∣ 3 ^ 2 := by
    obtain ⟨e', he'⟩ : ∃ e', Nat.card ↥M₀ = 3 ^ e' :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := ↥M₀)).ne'
        (fun {d} hd hdd => h3only d hd hdd)⟩
    rw [he'] at hYdvd ⊢
    have : e' ≤ 2 := by
      by_contra h
      exact absurd ((pow_dvd_pow 3 (by omega : 3 ≤ e')).trans hYdvd) (by decide)
    exact pow_dvd_pow 3 this
  refine ⟨M, map_subtype_le M₀, ?_, hodd⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have hab := comm_of_card_dvd_sq (p := 3) h9 ⟨a, ha⟩ ⟨b, hb⟩
  have := congrArg (fun z : ↥M₀ => ((z : ↥X) : MulAut W)) hab
  simpa using this

end CFSG.Quasithin.H13.U3
