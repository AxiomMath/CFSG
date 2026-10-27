module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.CX_tau_invariant_subgroups
    {B B₁ : Subgroup G} {b b₁ b₂ b₃ : G}
    (hB : B = Subgroup.zpowers b ⊔ B₁) (hB₁ : B₁ = Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hE4 : IsElemAb 3 4 B) (hbB : b ∈ B) (hb₁B : b₁ ∈ B) (hb₂B : b₂ ∈ B) (hb₃B : b₃ ∈ B)
    {X : Subgroup (MulAut ↥B)} {τX : MulAut ↥B} (hτXmem : τX ∈ X)
    (hτX2 : τX * τX = 1)
    (hτXb : τX ⟨b, hbB⟩ = ⟨b, hbB⟩)
    (hτX₁ : τX ⟨b₁, hb₁B⟩ = (⟨b₁, hb₁B⟩)⁻¹)
    (hτX₂ : τX ⟨b₂, hb₂B⟩ = (⟨b₂, hb₂B⟩)⁻¹)
    (hτX₃ : τX ⟨b₃, hb₃B⟩ = (⟨b₃, hb₃B⟩)⁻¹)
    (hB1irr : ∀ U₁ : Subgroup ↥B, U₁ ≤ B₁.subgroupOf B →
      (∀ σ : MulAut ↥B, σ ∈ X → σ * τX = τX * σ → Subgroup.map σ U₁ = U₁) →
      U₁ = ⊥ ∨ U₁ = B₁.subgroupOf B)
    {U : Subgroup ↥B} (hUB : U ≤ ⊤)
    (hU : ∀ σ : MulAut ↥B, σ ∈ X → σ * τX = τX * σ → Subgroup.map σ U = U) :
    U = ⊥ ∨ U = Subgroup.zpowers (⟨b, hbB⟩ : ↥B) ∨ U = B₁.subgroupOf B ∨ U = ⊤ := by
  let bB : ↥B := ⟨b, hbB⟩
  haveI : IsElementaryAbelian 3 ↥B := hE4.1
  have hpow3 : ∀ x : ↥B, x ^ 3 = 1 := fun x =>
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 ↥B)) x
  have hτXinv : τX⁻¹ = τX := inv_eq_of_mul_eq_one_right hτX2
  have hτXb' : τX bB = bB := hτXb
  have hle1 : Subgroup.zpowers b ≤ B := by rw [hB]; exact le_sup_left
  have hle2 : B₁ ≤ B := by rw [hB]; exact le_sup_right
  have hzp : (Subgroup.zpowers b).subgroupOf B = Subgroup.zpowers bB := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      simpa [bB] using hk
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have h := congrArg (fun y : ↥B => (y : G)) hk
      simpa [bB, Subgroup.coe_zpow] using h
  have htop : (⊤ : Subgroup ↥B) = Subgroup.zpowers bB ⊔ B₁.subgroupOf B := by
    calc (⊤ : Subgroup ↥B) = B.subgroupOf B := (Subgroup.subgroupOf_self (H := B)).symm
      _ = (Subgroup.zpowers b ⊔ B₁).subgroupOf B := by rw [hB]
      _ = (Subgroup.zpowers b).subgroupOf B ⊔ B₁.subgroupOf B :=
            Subgroup.subgroupOf_sup hle1 hle2
      _ = Subgroup.zpowers bB ⊔ B₁.subgroupOf B := by rw [hzp]
  have hx_decomp : ∀ x : ↥B, ∃ a ∈ Subgroup.zpowers bB, ∃ c ∈ B₁.subgroupOf B, a * c = x := by
    intro x
    have hx : x ∈ (Subgroup.zpowers bB ⊔ B₁.subgroupOf B : Subgroup ↥B) := by
      rw [← htop]
      exact Subgroup.mem_top x
    exact Subgroup.mem_sup.mp hx
  have hzp_fix : ∀ a : ↥B, a ∈ Subgroup.zpowers bB → τX a = a := by
    intro a ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← hk, map_zpow, hτXb']
  have hB1sub : B₁.subgroupOf B =
      Subgroup.closure ({(⟨b₁, hb₁B⟩ : ↥B), ⟨b₂, hb₂B⟩, ⟨b₃, hb₃B⟩} : Set ↥B) := by
    apply (Subgroup.map_subtype_inj (H := B)).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hle2, MonoidHom.map_closure, hB₁]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h | h)
      · rw [h]
        exact ⟨⟨b₁, hb₁B⟩, Or.inl rfl, rfl⟩
      · rw [h]
        exact ⟨⟨b₂, hb₂B⟩, Or.inr (Or.inl rfl), rfl⟩
      · rw [h]
        exact ⟨⟨b₃, hb₃B⟩, Or.inr (Or.inr rfl), rfl⟩
    · rintro ⟨x, hx, hxy⟩
      rw [← hxy]
      rcases hx with h | h | h <;> simp [h]
  have hgen_inv : ∀ y ∈ ({(⟨b₁, hb₁B⟩ : ↥B), ⟨b₂, hb₂B⟩, ⟨b₃, hb₃B⟩} : Set ↥B),
      τX y = y⁻¹ := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h | h
    · rw [h]; exact hτX₁
    · rw [h]; exact hτX₂
    · rw [h]; exact hτX₃
  have hinv : ∀ c : ↥B, c ∈ B₁.subgroupOf B → τX c = c⁻¹ := by
    intro c hc
    rw [hB1sub] at hc
    induction hc using Subgroup.closure_induction with
    | mem x hx => exact hgen_inv x hx
    | one => simp
    | mul x y _ _ ihx ihy =>
        rw [map_mul, ihx, ihy, mul_inv_rev]
        exact mul_comm' _ _
    | inv x _ ih => rw [map_inv, ih]
  have hB1_of_inv : ∀ y : ↥B, τX y = y⁻¹ → y ∈ B₁.subgroupOf B := by
    intro y hy
    obtain ⟨a, ha, c, hc, hac⟩ := hx_decomp y
    have hτa : τX a = a := hzp_fix a ha
    have hτc : τX c = c⁻¹ := hinv c hc
    have hτy : τX y = a * c⁻¹ := by rw [← hac, map_mul, hτa, hτc]
    have hkey : a * c⁻¹ = a⁻¹ * c⁻¹ := by
      calc a * c⁻¹ = τX y := hτy.symm
        _ = y⁻¹ := hy
        _ = (a * c)⁻¹ := by rw [hac]
        _ = c⁻¹ * a⁻¹ := mul_inv_rev a c
        _ = a⁻¹ * c⁻¹ := mul_comm' c⁻¹ a⁻¹
    have haa : a = a⁻¹ := mul_right_cancel hkey
    have hsq : a * a = a * a⁻¹ := congrArg (fun t => a * t) haa
    have ha2 : a ^ 2 = 1 := by rw [pow_two, hsq, mul_inv_cancel]
    have ha3 : a ^ 3 = 1 := hpow3 a
    have ha1 : a = 1 := by
      calc a = a * a ^ 2 := by rw [ha2, mul_one]
        _ = a ^ 3 := (pow_succ' a 2).symm
        _ = 1 := ha3
    have hyc : y = c := by rw [← hac, ha1, one_mul]
    rw [hyc]
    exact hc
  have hτU : ∀ x ∈ U, τX x ∈ U := by
    intro x hx
    have hmap : Subgroup.map τX U = U := hU τX hτXmem rfl
    rw [← hmap]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hmul_mem : ∀ x ∈ U, (x * τX x) ^ 2 ∈ U := by
    intro x hx
    exact U.pow_mem (U.mul_mem hx (hτU x hx)) 2
  have hinv_mem : ∀ x ∈ U, (x * (τX x)⁻¹) ^ 2 ∈ U := by
    intro x hx
    exact U.pow_mem (U.mul_mem hx (U.inv_mem (hτU x hx))) 2
  have ha_eq : ∀ (x a c : ↥B), a ∈ Subgroup.zpowers bB → c ∈ B₁.subgroupOf B →
      a * c = x → a = (x * τX x) ^ 2 := by
    intro x a c ha hc hac
    have hτa : τX a = a := hzp_fix a ha
    have hτc : τX c = c⁻¹ := hinv c hc
    have hτx : τX x = a * c⁻¹ := by rw [← hac, map_mul, hτa, hτc]
    have hxa : x * τX x = a * a := by
      calc x * τX x = (a * c) * (a * c⁻¹) := by rw [hτx, ← hac]
        _ = a * (c * a) * c⁻¹ := by simp only [mul_assoc]
        _ = a * (a * c) * c⁻¹ := by rw [mul_comm' c a]
        _ = a * a * (c * c⁻¹) := by simp only [mul_assoc]
        _ = a * a := by rw [mul_inv_cancel, mul_one]
    have ha4 : a ^ 4 = a := by
      calc a ^ 4 = a ^ 3 * a := by rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ]
        _ = a := by rw [hpow3 a, one_mul]
    have hsq : (a * a) ^ 2 = a ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      simp only [pow_two]
    rw [hxa, hsq]
    exact ha4.symm
  have hc_eq : ∀ (x a c : ↥B), a ∈ Subgroup.zpowers bB → c ∈ B₁.subgroupOf B →
      a * c = x → c = (x * (τX x)⁻¹) ^ 2 := by
    intro x a c ha hc hac
    have hτa : τX a = a := hzp_fix a ha
    have hτc : τX c = c⁻¹ := hinv c hc
    have hτx : τX x = a * c⁻¹ := by rw [← hac, map_mul, hτa, hτc]
    have hτxinv : (τX x)⁻¹ = c * a⁻¹ := by rw [hτx, mul_inv_rev, inv_inv]
    have hxc : x * (τX x)⁻¹ = c * c := by
      calc x * (τX x)⁻¹ = (a * c) * (c * a⁻¹) := by rw [hτxinv, ← hac]
        _ = a * (c * c) * a⁻¹ := by simp only [mul_assoc]
        _ = (c * c) * (a * a⁻¹) := by rw [mul_comm' a (c * c), mul_assoc]
        _ = c * c := by rw [mul_inv_cancel, mul_one]
    have hc4 : c ^ 4 = c := by
      calc c ^ 4 = c ^ 3 * c := by rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ]
        _ = c := by rw [hpow3 c, one_mul]
    have hsq : (c * c) ^ 2 = c ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      simp only [pow_two]
    rw [hxc, hsq]
    exact hc4.symm
  have hUdecomp : U = U ⊓ Subgroup.zpowers bB ⊔ U ⊓ B₁.subgroupOf B := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, c, hc, hac⟩ := hx_decomp x
      have haU : a ∈ U := by
        rw [ha_eq x a c ha hc hac]
        exact hmul_mem x hx
      have hcU : c ∈ U := by
        rw [hc_eq x a c ha hc hac]
        exact hinv_mem x hx
      rw [← hac]
      exact Subgroup.mul_mem_sup ⟨haU, ha⟩ ⟨hcU, hc⟩
    · exact sup_le inf_le_left inf_le_left
  have hcard_zp : Nat.card (Subgroup.zpowers bB) ∣ 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_iff_pow_eq_one.mpr (hpow3 bB)
  have hA : U ⊓ Subgroup.zpowers bB = ⊥ ∨ U ⊓ Subgroup.zpowers bB = Subgroup.zpowers bB := by
    have hle : U ⊓ Subgroup.zpowers bB ≤ Subgroup.zpowers bB := inf_le_right
    have hdvd : Nat.card (U ⊓ Subgroup.zpowers bB : Subgroup ↥B) ∣ 3 :=
      (Subgroup.card_dvd_of_le hle).trans hcard_zp
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · left
      exact Subgroup.eq_bot_of_card_eq _ h1
    · right
      have hzp_pos : 0 < Nat.card (Subgroup.zpowers bB) :=
        Nat.pos_of_dvd_of_pos hcard_zp (by norm_num)
      have hzp_le : Nat.card (Subgroup.zpowers bB) ≤ 3 :=
        Nat.le_of_dvd (by norm_num) hcard_zp
      have h3le : 3 ≤ Nat.card (Subgroup.zpowers bB) := by
        rw [← h3]
        exact Nat.le_of_dvd hzp_pos (Subgroup.card_dvd_of_le hle)
      have hcard_eq : Nat.card (Subgroup.zpowers bB) = 3 := le_antisymm hzp_le h3le
      exact Subgroup.eq_of_le_of_card_ge hle (by omega)
  have hσ_mem_B1 : ∀ (σ : MulAut ↥B), σ * τX = τX * σ →
      ∀ c ∈ B₁.subgroupOf B, σ c ∈ B₁.subgroupOf B := by
    intro σ hσ c hc
    refine hB1_of_inv (σ c) ?_
    calc τX (σ c) = (τX * σ) c := rfl
      _ = (σ * τX) c := by rw [← hσ]
      _ = σ (τX c) := rfl
      _ = σ c⁻¹ := by rw [hinv c hc]
      _ = (σ c)⁻¹ := map_inv σ c
  have hC_inv : ∀ σ : MulAut ↥B, σ ∈ X → σ * τX = τX * σ →
      Subgroup.map σ (U ⊓ B₁.subgroupOf B) = U ⊓ B₁.subgroupOf B := by
    intro σ hσX hσ
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨?_, hσ_mem_B1 σ hσ x hx.2⟩
      have hmap : Subgroup.map σ U = U := hU σ hσX hσ
      rw [← hmap]
      exact Subgroup.mem_map.mpr ⟨x, hx.1, rfl⟩
    · intro y hy
      have hσinv : σ⁻¹ * τX = τX * σ⁻¹ := by
        have h := congrArg Inv.inv hσ
        rw [mul_inv_rev, mul_inv_rev, hτXinv] at h
        exact h.symm
      refine Subgroup.mem_map.mpr ⟨σ⁻¹ y, ⟨?_, hσ_mem_B1 σ⁻¹ hσinv y hy.2⟩, ?_⟩
      · have hmap := hU σ⁻¹ (X.inv_mem hσX) hσinv
        rw [← hmap]
        exact Subgroup.mem_map_of_mem ((σ⁻¹ : MulAut ↥B) : ↥B →* ↥B) hy.1
      · exact MulAut.apply_inv_self (M := ↥B) σ y
  have hC := hB1irr (U ⊓ B₁.subgroupOf B) inf_le_right hC_inv
  rcases hA with hA | hA <;> rcases hC with hC | hC
  · left
    rw [hUdecomp, hA, hC, bot_sup_eq]
  · right; right; left
    rw [hUdecomp, hA, hC, bot_sup_eq]
  · right; left
    rw [hUdecomp, hA, hC, sup_bot_eq]
  · right; right; right
    rw [hUdecomp, hA, hC]
    exact htop.symm

end CFSG.RankThree.PartTwo.Sec21.FF81
