module

public import CFSG.RankThree.PartOne.S9.Planes.AlphaPlanes
public import CFSG.RankThree.GroupTheory.SteinbergBMMovingPlaneTwoSubgroupObstruction
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartOne.S11c.Sec66TDefs

public section

namespace CFSG.RankThree.PartOne.Sec66T

open Subgroup CFSG CFSG.RankThree.GroupTheory

theorem mulAut_mul_conj_mul_inv' {G : Type*} [Group G] (α : MulAut G) (g : G) :
    α * MulAut.conj g * α⁻¹ = MulAut.conj (α g) := by
  refine MulEquiv.ext fun y => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem exists_fixed_line_of_K1 {T : Type} [Group T] [Finite T] (hcenter : Subgroup.center T = ⊥)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {α : MulAut T} {q : T} {U : Subgroup T}
    (hord : orderOf α = p) (hαinn : α ∉ innerAut T) (hq1 : q ≠ 1) (hqp : q ^ p = 1)
    (hαq : α q = q) (hU2 : IsPGroup 2 ↥U) (hαU : ∀ u ∈ U, α u ∈ U)
    (hqU : ∀ u ∈ U, q * u * q⁻¹ ∈ U) (hmv : ∃ u ∈ U, α u ≠ u ∨ q * u * q⁻¹ ≠ u) :
    ∃ (R : Subgroup T) (β : MulAut T), R ≠ ⊥ ∧ IsPGroup 2 ↥R ∧
      (p = 5 → 16 ≤ Nat.card R) ∧ (p = 7 → 8 ≤ Nat.card R) ∧ (p = 11 → 1024 ≤ Nat.card R) ∧
      (p = 5 → Nat.card R = 16 → IsElementaryAbelian 2 ↥R) ∧
      β ≠ 1 ∧ β ^ p = 1 ∧ (∀ r ∈ R, β r = r) ∧
      ((∃ b : T, MulAut.conj b = β ∧ orderOf b = p) ∨ (β ∉ innerAut T ∧ orderOf β = p)) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hαp : α ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one α
  have hconj_inj : Function.Injective (MulAut.conj : T →* MulAut T) := by
    intro a c hac
    have hz : c⁻¹ * a ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h : a * x * a⁻¹ = c * x * c⁻¹ := by
        simpa only [MulAut.conj_apply] using congrArg (fun φ : MulAut T => φ x) hac
      calc x * (c⁻¹ * a) = c⁻¹ * (c * x * c⁻¹) * a := by group
        _ = c⁻¹ * (a * x * a⁻¹) * a := by rw [h]
        _ = c⁻¹ * a * x := by group
    rw [hcenter, Subgroup.mem_bot, inv_mul_eq_one] at hz
    exact hz.symm
  set β₀ : MulAut T := MulAut.conj q with hβ₀
  have hqord : orderOf q = p := orderOf_eq_prime hqp hq1
  have hβ₀ord : orderOf β₀ = p := by
    rw [hβ₀, orderOf_injective _ hconj_inj q, hqord]
  have hβ₀p : β₀ ^ p = 1 := by rw [← hβ₀ord]; exact pow_orderOf_eq_one β₀
  have hβ₀1 : β₀ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hβ₀ord
    exact hp.one_lt.ne hβ₀ord
  have hcomm : β₀ * α = α * β₀ := by
    have h := mulAut_mul_conj_mul_inv' α q
    rw [hαq] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hαnot : α ∉ zpowers β₀ := by
    rintro ⟨i, hi⟩
    apply hαinn
    rw [← hi]
    exact (innerAut T).zpow_mem ⟨q, rfl⟩ i
  obtain ⟨hEel, hEcard⟩ := Planes.zpowers_sup_plane hp hβ₀p hβ₀1 hαp hαnot hcomm
  set E : Subgroup (MulAut T) := zpowers β₀ ⊔ zpowers α with hE
  have hEgen : E = Subgroup.closure ({β₀, α} : Set (MulAut T)) := by
    rw [hE, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
      Set.singleton_union]
  have hpowU : ∀ (g : MulAut T), (∀ u ∈ U, g u ∈ U) → ∀ n : ℕ, ∀ u ∈ U, (g ^ n) u ∈ U := by
    intro g hg n
    induction n with
    | zero => intro u hu; simpa using hu
    | succ n ih =>
      intro u hu
      rw [pow_succ]
      exact ih _ (hg u hu)
  have hβ₀U : ∀ u ∈ U, β₀ u ∈ U := by
    intro u hu
    rw [hβ₀, MulAut.conj_apply]
    exact hqU u hu
  have hEU : ∀ e ∈ E, ∀ u ∈ U, e u ∈ U := by
    intro e he
    rw [hEgen] at he
    induction he using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with h | h
      · subst h
        exact hβ₀U
      · have h' : x = α := h
        subst h'
        exact hαU
    | one => intro u hu; simpa using hu
    | mul x y hx hy ihx ihy =>
      intro u hu
      exact ihx _ (ihy u hu)
    | inv x hx ihx =>
      have hxE : x ∈ E := by rw [hEgen]; exact hx
      have hxp : x ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian x hxE
      have hxinv : x⁻¹ = x ^ (p - 1) := by
        have : x ^ (p - 1) * x = 1 := by
          rw [← pow_succ, Nat.sub_add_cancel hp.one_le, hxp]
        exact (eq_inv_of_mul_eq_one_left this).symm
      rw [hxinv]
      exact hpowU x ihx (p - 1)
  have hinv : CFSG.IsInvariant E T U :=
    ⟨fun a g => ⟨fun hg => hEU a a.2 g hg, fun hg => by
      have h1 := hEU (a⁻¹ : E) (a⁻¹).2 ((a : MulAut T) g) hg
      have h2 : ((a⁻¹ : E) : MulAut T) ((a : MulAut T) g) = g := by
        change ((a : MulAut T)⁻¹ * (a : MulAut T)) g = g
        rw [inv_mul_cancel]
        rfl
      rwa [h2] at h1⟩⟩
  have hβ₀E : β₀ ∈ E := mem_sup_left (mem_zpowers β₀)
  have hαE : α ∈ E := mem_sup_right (mem_zpowers α)
  have hcommA : commutatorAction ↥E ↥U ≠ ⊥ := by
    intro h0
    obtain ⟨u0, hu0, hmv0⟩ := hmv
    have hne : ∃ e0 ∈ E, e0 u0 ≠ u0 := by
      rcases hmv0 with h | h
      · exact ⟨α, hαE, h⟩
      · refine ⟨β₀, hβ₀E, ?_⟩
        rw [hβ₀, MulAut.conj_apply]
        exact h
    obtain ⟨e0, he0, hne0⟩ := hne
    have hmem : (⟨u0, hu0⟩ : U)⁻¹ * ((⟨e0, he0⟩ : E) • (⟨u0, hu0⟩ : U)) ∈
        commutatorAction ↥E ↥U :=
      Subgroup.subset_closure ⟨⟨e0, he0⟩, ⟨u0, hu0⟩, Subgroup.mem_top _, rfl⟩
    rw [h0, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hne0 (congrArg Subtype.val hmem.symm)
  obtain ⟨R, hR, D, hDcard, -, hRne, -, -, -, -, h5, h7, h11, h16, hβfix, -⟩ :=
    SteinbergBM.moving_large_prime_plane_two_subgroup_fixed_line_and_small_order_obstruction hp hp2
      hEcard hU2 hcommA
  obtain ⟨β, hβD, hβ1⟩ : ∃ b ∈ D, b ≠ 1 := by
    by_contra h
    push Not at h
    have hD : D = ⊥ := (Subgroup.eq_bot_iff_forall D).mpr h
    rw [hD, Subgroup.card_bot] at hDcard
    exact hp.one_lt.ne hDcard
  have hβp : (β : MulAut T) ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian _ β.2
  have hβ1' : (β : MulAut T) ≠ 1 := fun h => hβ1 (Subtype.ext h)
  set R' : Subgroup T := R.map U.subtype with hR'
  have hR'2 : IsPGroup 2 R' := hU2.to_le (Subgroup.map_subtype_le R)
  have hcardR' : Nat.card R' = Nat.card R := Subgroup.card_map_of_injective U.subtype_injective
  have hR'ne : R' ≠ ⊥ := by
    intro h
    apply hRne
    have : Nat.card R' = 1 := by rw [h]; exact Subgroup.card_bot
    have h1 : Nat.card R = 1 := by rw [← hcardR']; exact this
    exact Subgroup.eq_bot_of_card_eq R h1
  refine ⟨R', β, hR'ne, hR'2, ?_, ?_, ?_, ?_, hβ1', hβp, ?_, ?_⟩
  · intro h; rw [hcardR']; exact h5 h
  · intro h; rw [hcardR']; exact h7 h
  · intro h; rw [hcardR']; exact h11 h
  · intro h5' h16'
    have hel : IsElementaryAbelian 2 ↥R := h16 h5' (by rw [← hcardR']; exact h16')
    exact IsElementaryAbelian.map_subtype (H := R) (K := U)
  · intro r hr
    obtain ⟨r0, hr0, rfl⟩ := hr
    exact congrArg Subtype.val (hβfix β hβD hβ1 r0 hr0)
  · by_cases hinn : (β : MulAut T) ∈ innerAut T
    · left
      obtain ⟨b, hb⟩ := hinn
      refine ⟨b, hb, ?_⟩
      have hbp : b ^ p = 1 := by
        apply hconj_inj
        rw [map_pow, hb, map_one]
        exact hβp
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hbp) with h | h
      · exfalso
        apply hβ1'
        rw [← hb, orderOf_eq_one_iff.mp h, map_one]
      · exact h
    · right
      refine ⟨hinn, ?_⟩
      exact orderOf_eq_prime hβp hβ1'

end CFSG.RankThree.PartOne.Sec66T
