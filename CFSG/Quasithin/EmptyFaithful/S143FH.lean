module

public import CFSG.Quasithin.EmptyFaithful.S153OfourFacts
public import CFSG.Quasithin.EmptyFaithful.S1417NaturalMore

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section SwapModel

variable {W : Type*} [CommGroup W] {X L₁ L₂ : Subgroup (MulAut W)} {t₀ : MulAut W}

theorem conj_mem_of_conjAut {L L' : Subgroup (MulAut W)} {α : MulAut W} (hα : B1.conjAut α L = L')
    {l : MulAut W} (hl : l ∈ L) : α * l * α⁻¹ ∈ L' := by
  rw [← hα, B1.mem_conjAut]
  simpa [mul_assoc] using hl

theorem conjAut_swap_of_not_mem_sup (h : OfourStruct X L₁ L₂ t₀) {α : MulAut W} (hαX : α ∈ X)
    (hαN : α ∉ L₁ ⊔ L₂) : B1.conjAut α L₁ = L₂ ∧ B1.conjAut α L₂ = L₁ := by
  rcases h.perm α hαX with ⟨h1, -⟩ | h12
  · exfalso
    apply hαN
    refine (h.mem_sup_iff hαX).mpr fun u hu => ?_
    exact OfourStruct.commV_apply_mem α L₁ L₁ h1 hu
  · exact h12

@[expose] noncomputable def deltaHom {α : MulAut W} (hconj : B1.conjAut α L₁ = L₂)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) : ↥L₁ →* MulAut W where
  toFun l := (l : MulAut W) * (α * (l : MulAut W) * α⁻¹)
  map_one' := by simp
  map_mul' a b := by
    have h1 : α * (a : MulAut W) * α⁻¹ ∈ L₂ := conj_mem_of_conjAut hconj a.2
    have h2 : (b : MulAut W) * (α * (a : MulAut W) * α⁻¹) =
        (α * (a : MulAut W) * α⁻¹) * (b : MulAut W) := hcomm b b.2 _ h1
    calc ((a * b : ↥L₁) : MulAut W) * (α * ((a * b : ↥L₁) : MulAut W) * α⁻¹)
        = (a : MulAut W) * ((b : MulAut W) * (α * (a : MulAut W) * α⁻¹)) *
            (α * (b : MulAut W) * α⁻¹) := by
          simp only [Subgroup.coe_mul]; group
      _ = (a : MulAut W) * ((α * (a : MulAut W) * α⁻¹) * (b : MulAut W)) *
            (α * (b : MulAut W) * α⁻¹) := by rw [h2]
      _ = (a : MulAut W) * (α * (a : MulAut W) * α⁻¹) *
            ((b : MulAut W) * (α * (b : MulAut W) * α⁻¹)) := by group

theorem deltaHom_apply {α : MulAut W} (hconj : B1.conjAut α L₁ = L₂)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (l : ↥L₁) :
    deltaHom hconj hcomm l = (l : MulAut W) * (α * (l : MulAut W) * α⁻¹) := rfl

theorem exists_eq_delta (h : OfourStruct X L₁ L₂ t₀) {α : MulAut W}
    (hconj : B1.conjAut α L₁ = L₂ ∧ B1.conjAut α L₂ = L₁) {y : MulAut W} (hy : y ∈ L₁ ⊔ L₂)
    (hyα : α * y = y * α) : ∃ l ∈ L₁, y = l * (α * l * α⁻¹) := by
  obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := S1417.exists_mul_of_mem_sup_of_commute h.comm hy
  have h1 : α * l₁ * α⁻¹ ∈ L₂ := conj_mem_of_conjAut hconj.1 hl₁
  have h2 : α * l₂ * α⁻¹ ∈ L₁ := conj_mem_of_conjAut hconj.2 hl₂
  have e : α * (l₁ * l₂) * α⁻¹ = l₁ * l₂ := by
    calc α * (l₁ * l₂) * α⁻¹ = (α * (l₁ * l₂)) * α⁻¹ := rfl
      _ = ((l₁ * l₂) * α) * α⁻¹ := by rw [hyα]
      _ = l₁ * l₂ := by group
  have hc := h.comm (α * l₂ * α⁻¹) h2 (α * l₁ * α⁻¹) h1
  have e' : (α * l₂ * α⁻¹) * (α * l₁ * α⁻¹) = l₁ * l₂ := by
    rw [← e]
    calc (α * l₂ * α⁻¹) * (α * l₁ * α⁻¹) = (α * l₁ * α⁻¹) * (α * l₂ * α⁻¹) := hc
      _ = α * (l₁ * l₂) * α⁻¹ := by group
  obtain ⟨-, hb⟩ := S1417.eq_of_mul_eq_of_inf_eq_bot h.Linf h2 hl₁ h1 hl₂ e'
  exact ⟨l₁, hl₁, by rw [hb]⟩


theorem mem_zpowers_invol {α : MulAut W} (hα2 : α * α = 1) {z : MulAut W}
    (hz : z ∈ Subgroup.zpowers α) : z = 1 ∨ z = α := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have ht2 : α ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hα2
  rw [zpow_eq_zpow_emod k ht2]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left; rw [hk, zpow_zero]
  · right; rw [hk, zpow_one]

theorem centralizer_equiv (h : OfourStruct X L₁ L₂ t₀) {α : MulAut W} (hαX : α ∈ X)
    (hαN : α ∉ L₁ ⊔ L₂) (hα2 : α * α = 1) :
    Nonempty (↥(Subgroup.centralizer ({α} : Set (MulAut W)) ⊓ X) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 3)) := by
  have hconj := conjAut_swap_of_not_mem_sup h hαX hαN
  have hα1 : α ≠ 1 := fun he => hαN (he ▸ (L₁ ⊔ L₂).one_mem)
  have hαinv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα2
  have hcomm := h.comm
  have hδapp := deltaHom_apply (α := α) hconj.1 hcomm
  set δ := deltaHom (α := α) hconj.1 hcomm with hδ
  set C := Subgroup.centralizer ({α} : Set (MulAut W)) ⊓ X with hC
  have hδL : ∀ l : ↥L₁, α * (l : MulAut W) * α⁻¹ ∈ L₂ := fun l => conj_mem_of_conjAut hconj.1 l.2
  have hδsup : ∀ l : ↥L₁, δ l ∈ L₁ ⊔ L₂ := fun l => by
    rw [hδapp]
    exact (L₁ ⊔ L₂).mul_mem (Subgroup.mem_sup_left l.2) (Subgroup.mem_sup_right (hδL l))
  have hδX : ∀ l : ↥L₁, δ l ∈ X := fun l => h.le_X_sup (hδsup l)
  have hδα : ∀ l : ↥L₁, δ l * α = α * δ l := by
    intro l
    rw [hδapp]
    have hc := hcomm (l : MulAut W) l.2 _ (hδL l)
    have e1 : (l : MulAut W) * (α * (l : MulAut W) * α⁻¹) * α = (l : MulAut W) * α * (l : MulAut W) := by
      group
    have e2 : α * ((l : MulAut W) * (α * (l : MulAut W) * α⁻¹)) =
        (l : MulAut W) * α * (l : MulAut W) := by
      calc α * ((l : MulAut W) * (α * (l : MulAut W) * α⁻¹))
          = α * ((α * (l : MulAut W) * α⁻¹) * (l : MulAut W)) := by rw [hc]
        _ = (α * α) * (l : MulAut W) * α⁻¹ * (l : MulAut W) := by group
        _ = (l : MulAut W) * α⁻¹ * (l : MulAut W) := by rw [hα2, one_mul]
        _ = (l : MulAut W) * α * (l : MulAut W) := by rw [hαinv]
    rw [e1, e2]
  have hαC : α ∈ C := ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, hαX⟩
  have hδC : ∀ l : ↥L₁, δ l ∈ C := fun l =>
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hδα l), hδX l⟩
  have hzC : Subgroup.zpowers α ≤ C := (Subgroup.zpowers_le).2 hαC
  let f₁ : ↥L₁ →* ↥C := δ.codRestrict C hδC
  let f₂ : ↥(Subgroup.zpowers α) →* ↥C := Subgroup.inclusion hzC
  have hfc : ∀ (l : ↥L₁) (z : ↥(Subgroup.zpowers α)), Commute (f₁ l) (f₂ z) := by
    intro l z
    apply Subtype.ext
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp z.2
    have hcom : Commute (δ l) α := hδα l
    have := (Commute.zpow_right hcom k).eq
    rw [hk] at this
    exact this
  let Θ : ↥L₁ × ↥(Subgroup.zpowers α) →* ↥C := f₁.noncommCoprod f₂ hfc
  have hΘapp : ∀ (a : ↥L₁) (b : ↥(Subgroup.zpowers α)),
      ((Θ (a, b) : ↥C) : MulAut W) = δ a * (b : MulAut W) := fun a b => rfl
  have hinj : Function.Injective Θ := by
    refine (injective_iff_map_eq_one Θ).mpr ?_
    rintro ⟨l, z⟩ hΘ
    have hΘ' : δ l * (z : MulAut W) = 1 := by
      have := congrArg Subtype.val hΘ
      rw [hΘapp] at this
      exact this
    rcases mem_zpowers_invol hα2 z.2 with hz | hz
    · rw [hz, mul_one, hδapp] at hΘ'
      have hlL₂ : (l : MulAut W) ∈ L₂ := by
        have h1 : (l : MulAut W) = (α * (l : MulAut W) * α⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hΘ'
        rw [h1]
        exact L₂.inv_mem (hδL l)
      have hl1 : (l : MulAut W) ∈ L₁ ⊓ L₂ := ⟨l.2, hlL₂⟩
      rw [h.Linf, Subgroup.mem_bot] at hl1
      have hlone : l = 1 := Subtype.ext hl1
      have hz1 : z = 1 := Subtype.ext hz
      rw [hlone, hz1]
      rfl
    · exfalso
      rw [hz] at hΘ'
      have h1 : α = (δ l)⁻¹ := eq_inv_of_mul_eq_one_right hΘ'
      exact hαN (by rw [h1]; exact (L₁ ⊔ L₂).inv_mem (hδsup l))
  have hsurj : Function.Surjective Θ := by
    rintro ⟨y, hyC⟩
    have hyα : α * y = y * α := (Subgroup.mem_centralizer_singleton_iff.mp hyC.1).symm
    have hyX : y ∈ X := hyC.2
    rcases coset_of_relIndex_two h.relIndex_sup hyX hαX hαN with hy | hy
    · obtain ⟨l, hl, hyl⟩ := exists_eq_delta h hconj hy hyα
      refine ⟨(⟨l, hl⟩, 1), ?_⟩
      apply Subtype.ext
      rw [hΘapp, hδapp]
      simp [hyl]
    · have hyα' : α * (y * α⁻¹) = (y * α⁻¹) * α := by
        calc α * (y * α⁻¹) = (α * y) * α⁻¹ := by group
          _ = (y * α) * α⁻¹ := by rw [hyα]
          _ = (y * α⁻¹) * α := by group
      obtain ⟨l, hl, hyl⟩ := exists_eq_delta h hconj hy hyα'
      refine ⟨(⟨l, hl⟩, ⟨α, Subgroup.mem_zpowers α⟩), ?_⟩
      apply Subtype.ext
      rw [hΘapp, hδapp]
      show l * (α * l * α⁻¹) * α = y
      rw [← hyl]
      group
  obtain ⟨e₁⟩ := S1417.nonempty_equiv_perm h.nat₁
  have hcard2 : Nat.card ↥(Subgroup.zpowers α) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hα2) hα1
  let e₂ : ↥(Subgroup.zpowers α) ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq (p := 2) hcard2 (by rw [Nat.card_eq_fintype_card]; rfl)
  exact ⟨(MulEquiv.ofBijective Θ ⟨hinj, hsurj⟩).symm.trans
    ((e₁.prodCongr e₂).trans MulEquiv.prodComm)⟩

end SwapModel

section Abstract

theorem exists_odd_mul_of_card_four {Γ : Type*} [Group Γ]
    (e : Γ ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 3)) (R : Subgroup Γ)
    (hR : Nat.card R = 4) (y : Γ) : ∃ o s : Γ, Odd (orderOf o) ∧ s ∈ R ∧ y = o * s := by
  have hfin : Finite Γ := Finite.of_equiv _ e.symm.toEquiv
  have hcard : Nat.card Γ = 12 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    have h1 : Nat.card (Multiplicative (ZMod 2)) = 2 := by rw [Nat.card_eq_fintype_card]; rfl
    have h2 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; decide
    rw [h1, h2]
  have hrot : orderOf (finRotate 3) = 3 :=
    orderOf_eq_prime (by decide) (by decide)
  set ω : Γ := e.symm (1, finRotate 3) with hωdef
  have hω : orderOf ω = 3 := by
    rw [hωdef, MulEquiv.orderOf_eq, Prod.orderOf, orderOf_one, hrot]
    rfl
  have hOcard : Nat.card (Subgroup.zpowers ω) = 3 := by rw [Nat.card_zpowers, hω]
  have hbot : Subgroup.zpowers ω ⊓ R = ⊥ := by
    have h1 : Nat.card ↥(Subgroup.zpowers ω ⊓ R) ∣ 3 :=
      hOcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(Subgroup.zpowers ω ⊓ R) ∣ 4 :=
      hR ▸ Subgroup.card_dvd_of_le inf_le_right
    have h3 : Nat.card ↥(Subgroup.zpowers ω ⊓ R) = 1 := by
      have := Nat.dvd_gcd h1 h2
      exact Nat.dvd_one.mp (by simpa using this)
    exact Subgroup.eq_bot_of_card_eq _ h3
  let f : ↥(Subgroup.zpowers ω) × ↥R → Γ := fun p => (p.1 : Γ) * (p.2 : Γ)
  have hf : Function.Injective f := by
    rintro ⟨⟨o, ho⟩, ⟨s, hs⟩⟩ ⟨⟨o', ho'⟩, ⟨s', hs'⟩⟩ hEq
    have hEq' : o * s = o' * s' := hEq
    have h1 : o'⁻¹ * o = s' * s⁻¹ := by
      calc o'⁻¹ * o = o'⁻¹ * (o * s) * s⁻¹ := by group
        _ = o'⁻¹ * (o' * s') * s⁻¹ := by rw [hEq']
        _ = s' * s⁻¹ := by group
    have hmem : o'⁻¹ * o ∈ Subgroup.zpowers ω ⊓ R :=
      ⟨(Subgroup.zpowers ω).mul_mem ((Subgroup.zpowers ω).inv_mem ho') ho, by
        rw [h1]; exact R.mul_mem hs' (R.inv_mem hs)⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hoo : o = o' := by
      calc o = o' * (o'⁻¹ * o) := by group
        _ = o' := by rw [hmem, mul_one]
    subst hoo
    have hss : s = s' := mul_left_cancel hEq'
    subst hss
    rfl
  have hbij : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by rw [Nat.card_prod, hOcard, hR, hcard])
  obtain ⟨⟨⟨o, ho⟩, ⟨s, hs⟩⟩, hy⟩ := hbij.2 y
  refine ⟨o, s, ?_, hs, hy.symm⟩
  have hdvd : orderOf o ∣ 3 := by rw [← hω]; exact orderOf_dvd_of_mem_zpowers ho
  exact Odd.of_dvd_nat (by decide : Odd 3) hdvd

end Abstract

section Fix

variable {W : Type*} [CommGroup W] [Finite W] {X L₁ L₂ : Subgroup (MulAut W)} {t₀ : MulAut W}

theorem eq_one_of_mem_S_of_fix (h : OfourStruct X L₁ L₂ t₀) {q : W → ZMod 2}
    (hq : ∀ w, q w = 1 ↔ (w ∈ commV L₁ ∨ w ∈ commV L₂) ∧ w ≠ 1)
    (hexp : ∀ w : W, w * w = 1) {T' : Subgroup (MulAut W)} (hT : IsSylowTwoOf T' X) {v x : W}
    (hv1 : v ≠ 1) (hvfix : ∀ y ∈ T', y v = v) (hx1 : x ≠ 1) (hxv : x ≠ v) (hxq : q x = 0)
    (hvxq : q (v * x) = 0) {y : MulAut W} (hyS : y ∈ T' ⊓ (L₁ ⊔ L₂)) (hyx : y x = x) :
    y = 1 := by
  obtain ⟨s₁, s₂, τ, a₁, a₂, hF⟩ := h.exists_sylowFacts hT
  have hs₁L : s₁ ∈ L₁ := hF.sylow.s₁_mem_L
  have hs₂L : s₂ ∈ L₂ := hF.sylow.s₂_mem_L
  have hva : v = a₁ * a₂ := by
    rcases hF.fix v hvfix with he | he
    · exact absurd he hv1
    · exact he
  have ha₁ := hF.sylow.a₁_mem
  have ha₂ := hF.sylow.a₂_mem
  have hinv : ∀ w : W, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (hexp w)
  obtain ⟨x₁, hx₁, x₂, hx₂, hxe⟩ := h.exists_decomp_W x
  have hx₁1 : x₁ ≠ 1 := by
    intro he
    rw [he, one_mul] at hxe
    have : q x = 1 := (hq x).mpr ⟨Or.inr (hxe ▸ hx₂), hx1⟩
    rw [hxq] at this
    exact zero_ne_one this
  have hx₂1 : x₂ ≠ 1 := by
    intro he
    rw [he, mul_one] at hxe
    have : q x = 1 := (hq x).mpr ⟨Or.inl (hxe ▸ hx₁), hx1⟩
    rw [hxq] at this
    exact zero_ne_one this
  have hx₁a : x₁ ≠ a₁ := by
    intro he
    have hvx : v * x = a₂ * x₂ := by
      rw [hva, hxe, he]
      calc a₁ * a₂ * (a₁ * x₂) = (a₁ * a₁) * (a₂ * x₂) := by
            calc a₁ * a₂ * (a₁ * x₂) = a₁ * (a₂ * a₁) * x₂ := by group
              _ = a₁ * (a₁ * a₂) * x₂ := by rw [mul_comm a₂ a₁]
              _ = (a₁ * a₁) * (a₂ * x₂) := by group
        _ = a₂ * x₂ := by rw [hexp a₁, one_mul]
    by_cases hx₂a : a₂ * x₂ = 1
    · apply hxv
      have : x₂ = a₂ := by
        have := mul_eq_one_iff_eq_inv.mp hx₂a
        rw [hinv] at this
        exact this.symm
      rw [hxe, he, this, hva]
    · have : q (v * x) = 1 := (hq _).mpr ⟨Or.inr (by rw [hvx]; exact (commV L₂).mul_mem ha₂ hx₂), by
        rw [hvx]; exact hx₂a⟩
      rw [hvxq] at this
      exact zero_ne_one this
  have hx₂a : x₂ ≠ a₂ := by
    intro he
    have hvx : v * x = a₁ * x₁ := by
      rw [hva, hxe, he]
      calc a₁ * a₂ * (x₁ * a₂) = a₁ * x₁ * (a₂ * a₂) := by
            calc a₁ * a₂ * (x₁ * a₂) = a₁ * (a₂ * x₁) * a₂ := by group
              _ = a₁ * (x₁ * a₂) * a₂ := by rw [mul_comm a₂ x₁]
              _ = a₁ * x₁ * (a₂ * a₂) := by group
        _ = a₁ * x₁ := by rw [hexp a₂, mul_one]
    by_cases hx₁a' : a₁ * x₁ = 1
    · apply hxv
      have : x₁ = a₁ := by
        have := mul_eq_one_iff_eq_inv.mp hx₁a'
        rw [hinv] at this
        exact this.symm
      rw [hxe, he, this, hva]
    · have : q (v * x) = 1 := (hq _).mpr ⟨Or.inl (by rw [hvx]; exact (commV L₁).mul_mem ha₁ hx₁), by
        rw [hvx]; exact hx₁a'⟩
      rw [hvxq] at this
      exact zero_ne_one this
  have hs₁x₂ : s₁ x₂ = x₂ := h.L₁_fix₂ hs₁L hx₂
  have hs₁x : s₁ x = s₁ x₁ * x₂ := by rw [hxe, map_mul, hs₁x₂]
  have hs₁x₁ : s₁ x₁ ∈ commV L₁ := commV_stable L₁ hs₁L hx₁
  have hmove₁ : s₁ x ≠ x := by
    intro he
    rw [hs₁x, hxe] at he
    have := S1417.eq_of_mul_eq_of_inf_eq_bot h.inf hs₁x₁ hx₁ hx₂ hx₂ he
    rcases (hF.sylow.fix₁ x₁ hx₁).mp this.1 with h1 | h1
    · exact hx₁1 h1
    · exact hx₁a h1
  have hs₂x₁ : s₂ x₁ = x₁ := h.L₂_fix₁ hs₂L hx₁
  have hs₂x : s₂ x = x₁ * s₂ x₂ := by rw [hxe, map_mul, hs₂x₁]
  have hs₂x₂ : s₂ x₂ ∈ commV L₂ := commV_stable L₂ hs₂L hx₂
  have hmove₂ : s₂ x ≠ x := by
    intro he
    rw [hs₂x, hxe] at he
    have := mul_left_cancel he
    rcases (hF.sylow.fix₂ x₂ hx₂).mp this with h1 | h1
    · exact hx₂1 h1
    · exact hx₂a h1
  rcases (hF.S_eq y).mp hyS with h1 | h1 | h1 | h1
  · exact h1
  · rw [h1] at hyx; exact absurd hyx hmove₁
  · rw [h1] at hyx; exact absurd hyx hmove₂
  · rw [h1] at hyx
    exact absurd (h.fix_of_fix_mul hs₁L hs₂L hyx).1 hmove₁

end Fix

end S143

end CFSG.Quasithin
