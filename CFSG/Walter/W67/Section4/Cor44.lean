module

public import CFSG.Walter.W67.Statements
public import CFSG.Walter.W67.Section4.Cor44A
import CFSG.Walter.W67.Section4.Lemma42
import CFSG.Walter.W67.Section4.Prop43cA
import CFSG.Walter.W67.Section4.Prop43ab
import CFSG.Walter.W67.Section4.Basic
import CFSG.Walter.W67.W2Cor32A

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_commutator' [Finite G] {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  have hmap : ∀ X : Subgroup G, g ∈ Subgroup.normalizer (X : Set G) →
      X.map (MulAut.conj g).toMonoidHom = X := by
    intro X hX
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
    · obtain ⟨y, hy, rfl⟩ := hx
      exact (Subgroup.mem_normalizer_iff.mp hX y).mp hy
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have h1 : ⁅H, K⁆.map (MulAut.conj g).toMonoidHom = ⁅H, K⁆ := by
    rw [Subgroup.map_commutator, hmap H hH, hmap K hK]
  refine JT.mem_normalizer_of_conj_mem fun x hx => ?_
  rw [← h1]
  exact ⟨x, hx, rfl⟩

theorem eq_of_card_eq_of_le_cyclic {A B C : Subgroup G} (hA : IsCyclic A) (hBA : B ≤ A)
    (hCA : C ≤ A) (hcard : Nat.card B = Nat.card C) : B = C := by
  have hc : Nat.card (B.subgroupOf A) = Nat.card (C.subgroupOf A) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv, hcard]
  have heq : B.subgroupOf A = C.subgroupOf A := (IsCyclic.subgroup_eq_iff_card_eq).mpr hc
  have h1 := congrArg (Subgroup.map A.subtype) heq
  rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hBA, inf_eq_left.mpr hCA] at h1

namespace Std

variable (s : Std G) {T₂ : G}

theorem A_comm
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2) :
    ∀ x ∈ s.fr.A T₂, ∀ y ∈ s.fr.A T₂, x * y = y * x := by
  have hcycA := s.isCyclic_A hp hT₂ h2
  intro x hx y hy
  exact congrArg Subtype.val
    ((IsCyclic.isMulCommutative (α := s.fr.A T₂)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem E_le_normalizer_A (hT₂ : T₂ ∈ s.fr.T) :
    s.fr.E ≤ Subgroup.normalizer (s.fr.A T₂ : Set G) := fun _ he =>
  JT.mem_normalizer_of_conj_mem fun _ hx => s.fr.E_conj_mem_A he hx hT₂

theorem A_decomp
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2)
    (hcop : Nat.Coprime (Nat.card (s.fr.A T₂)) (Nat.card s.fr.E)) :
    s.fr.A₀ T₂ ⊔ s.fr.A₁ T₂ = s.fr.A T₂ ∧ s.fr.A₀ T₂ ⊓ s.fr.A₁ T₂ = ⊥ ∧
      Nat.Coprime (Nat.card (s.fr.A₀ T₂)) (Nat.card (s.fr.A₁ T₂)) ∧
      s.fr.A₁ T₂ ≤ s.fr.A T₂ ∧ s.fr.E ≤ Subgroup.normalizer (s.fr.A₁ T₂ : Set G) := by
  have hcycA := s.isCyclic_A hp hT₂ h2
  have hab := s.A_comm hp hT₂ h2
  obtain ⟨g₀, hg₀⟩ := s.exists_E_eq_zpowers
  have hg₀E : g₀ ∈ s.fr.E := hg₀ ▸ Subgroup.mem_zpowers g₀
  obtain ⟨hdisj, hcard, hA₁A, hEA₁⟩ :=
    coprime_decomp hab hg₀ (s.E_le_normalizer_A hT₂ hg₀E) hcop
  change s.fr.A₀ T₂ ⊓ s.fr.A₁ T₂ = ⊥ at hdisj
  change Nat.card (s.fr.A₀ T₂) * Nat.card (s.fr.A₁ T₂) = Nat.card (s.fr.A T₂) at hcard
  change s.fr.A₁ T₂ ≤ s.fr.A T₂ at hA₁A
  change ∀ b ∈ s.fr.A₁ T₂, g₀ * b * g₀⁻¹ ∈ s.fr.A₁ T₂ at hEA₁
  have hA₀A : s.fr.A₀ T₂ ≤ s.fr.A T₂ := inf_le_left
  have hEN₁ : s.fr.E ≤ Subgroup.normalizer (s.fr.A₁ T₂ : Set G) := by
    rw [hg₀, Subgroup.zpowers_le]
    exact JT.mem_normalizer_of_conj_mem hEA₁
  obtain ⟨hcA, -⟩ := card_sup_mul_card_inf_of_commute (s.fr.A₀ T₂) (s.fr.A₁ T₂)
    (fun x hx y hy => hab x (hA₀A hx) y (hA₁A hy))
  rw [hdisj, Subgroup.card_bot, mul_one, hcard] at hcA
  have hA01 : s.fr.A₀ T₂ ⊔ s.fr.A₁ T₂ = s.fr.A T₂ :=
    Subgroup.eq_of_le_of_card_ge (sup_le hA₀A hA₁A) (by rw [hcA])
  refine ⟨hA01, hdisj, ?_, hA₁A, hEN₁⟩
  apply Nat.coprime_of_dvd
  intro r hr h0 h1
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := s.fr.A₀ T₂) r h0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := s.fr.A₁ T₂) r h1
  have hzx : Nat.card (Subgroup.zpowers (x : G)) = r := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hzy : Nat.card (Subgroup.zpowers (y : G)) = r := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hy]
  have heq := eq_of_card_eq_of_le_cyclic hcycA (Subgroup.zpowers_le.mpr (hA₀A x.2))
    (Subgroup.zpowers_le.mpr (hA₁A y.2)) (by rw [hzx, hzy])
  have hxA₁ : (x : G) ∈ s.fr.A₁ T₂ := by
    have : (x : G) ∈ Subgroup.zpowers (y : G) := heq ▸ Subgroup.mem_zpowers _
    exact (Subgroup.zpowers_le.mpr y.2) this
  have h1' : (x : G) ∈ s.fr.A₀ T₂ ⊓ s.fr.A₁ T₂ := ⟨x.2, hxA₁⟩
  rw [hdisj, Subgroup.mem_bot] at h1'
  have : x = 1 := Subtype.ext h1'
  rw [this, orderOf_one] at hx
  exact hr.one_lt.ne' hx.symm

theorem E_le_normalizer_V (hT₂ : T₂ ∈ s.fr.T) :
    s.fr.E ≤ Subgroup.normalizer (s.fr.V T₂ : Set G) := fun e he =>
  JT.mem_normalizer_of_conj_mem fun v hv => by
    rw [(Subgroup.mem_centralizer_iff.mp (s.fr.E_le_CS he) v (s.fr.V_le_S hT₂ hv)).symm,
      mul_inv_cancel_right]
    exact hv

theorem coprime_card_A₀_Y
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2)
    (hcop : Nat.Coprime (Nat.card (s.fr.A T₂)) (Nat.card s.fr.E)) :
    Nat.Coprime (Nat.card (s.fr.A₀ T₂))
      (Nat.card (s.fr.V T₂ ⊔ s.fr.A₁ T₂ ⊔ s.fr.E : Subgroup G)) := by
  obtain ⟨-, -, hcop01, hA₁A, hEN₁⟩ := s.A_decomp hp hT₂ h2 hcop
  have hA₀A : s.fr.A₀ T₂ ≤ s.fr.A T₂ := inf_le_left
  have hVA := s.A_le_centralizer_V T₂
  have hA₁V : s.fr.A₁ T₂ ≤ Subgroup.normalizer (s.fr.V T₂ : Set G) :=
    (hA₁A.trans hVA).trans (Subgroup.centralizer_le_normalizer _)
  have hY1 : Nat.card (s.fr.V T₂ ⊔ s.fr.A₁ T₂ : Subgroup G) ∣
      Nat.card (s.fr.V T₂) * Nat.card (s.fr.A₁ T₂) :=
    Dvd.intro _ (card_sup_mul_card_inf_of_le_normalizer hA₁V)
  have hEVA₁ : s.fr.E ≤ Subgroup.normalizer ((s.fr.V T₂ ⊔ s.fr.A₁ T₂ : Subgroup G) : Set G) :=
    fun e he => mem_normalizer_sup (s.E_le_normalizer_V hT₂ he) (hEN₁ he)
  have hY2 : Nat.card (s.fr.V T₂ ⊔ s.fr.A₁ T₂ ⊔ s.fr.E : Subgroup G) ∣
      Nat.card (s.fr.V T₂ ⊔ s.fr.A₁ T₂ : Subgroup G) * Nat.card s.fr.E :=
    Dvd.intro _ (card_sup_mul_card_inf_of_le_normalizer hEVA₁)
  refine Nat.Coprime.coprime_dvd_right (hY2.trans (Nat.mul_dvd_mul_right hY1 _)) ?_
  rw [s.fr.card_V hT₂ h2]
  refine Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ hcop01) ?_
  · have hodd : Odd (Nat.card (s.fr.A₀ T₂)) := Odd.of_dvd_nat (s.fr.odd_card_A T₂)
      (Subgroup.card_dvd_of_le hA₀A)
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hodd)
  · exact Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hA₀A) hcop

theorem A₀_comm
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2) {a x : G}
    (ha : a ∈ s.fr.A₀ T₂) (hx : x ∈ s.fr.V T₂ ⊔ s.fr.A T₂ ⊔ s.fr.E) : a * x = x * a := by
  have hab := s.A_comm hp hT₂ h2
  have hA₀A : s.fr.A₀ T₂ ≤ s.fr.A T₂ := inf_le_left
  have hC : s.fr.V T₂ ⊔ s.fr.A T₂ ⊔ s.fr.E ≤ Subgroup.centralizer (s.fr.A₀ T₂ : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact Subgroup.le_centralizer_iff.mpr (hA₀A.trans (s.A_le_centralizer_V T₂))
    · exact fun y hy => Subgroup.mem_centralizer_iff.mpr fun z hz => hab z (hA₀A hz) y hy
    · exact Subgroup.le_centralizer_iff.mpr inf_le_right
  exact Subgroup.mem_centralizer_iff.mp (hC hx) a ha

theorem exists_decomp_X
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2)
    (hcop : Nat.Coprime (Nat.card (s.fr.A T₂)) (Nat.card s.fr.E)) {x : G}
    (hx : x ∈ s.fr.V T₂ ⊔ s.fr.A T₂ ⊔ s.fr.E) :
    ∃ a ∈ s.fr.A₀ T₂, ∃ y ∈ s.fr.V T₂ ⊔ s.fr.A₁ T₂ ⊔ s.fr.E, x = a * y := by
  obtain ⟨hA01, -, -, hA₁A, -⟩ := s.A_decomp hp hT₂ h2 hcop
  have hab := s.A_comm hp hT₂ h2
  have hA₀A : s.fr.A₀ T₂ ≤ s.fr.A T₂ := inf_le_left
  have hAV : s.fr.A T₂ ≤ Subgroup.normalizer (s.fr.V T₂ : Set G) :=
    (s.A_le_centralizer_V T₂).trans (Subgroup.centralizer_le_normalizer _)
  have hEVA : s.fr.E ≤ Subgroup.normalizer ((s.fr.V T₂ ⊔ s.fr.A T₂ : Subgroup G) : Set G) :=
    fun e he => mem_normalizer_sup (s.E_le_normalizer_V hT₂ he) (s.E_le_normalizer_A hT₂ he)
  obtain ⟨w, hw, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hEVA).mp hx
  obtain ⟨v, hv, a, ha, rfl⟩ := (mem_sup_iff_of_le_normalizer hAV).mp hw
  have hA₁A₀ : s.fr.A₁ T₂ ≤ Subgroup.normalizer (s.fr.A₀ T₂ : Set G) := fun y hy =>
    JT.mem_normalizer_of_conj_mem fun z hz => by
      rw [hab y (hA₁A hy) z (hA₀A hz), mul_inv_cancel_right]
      exact hz
  have haA : a ∈ s.fr.A₀ T₂ ⊔ s.fr.A₁ T₂ := hA01 ▸ ha
  obtain ⟨a₀, ha₀, a₁, ha₁, rfl⟩ := (mem_sup_iff_of_le_normalizer hA₁A₀).mp haA
  refine ⟨a₀, ha₀, v * a₁ * e, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left
      (Subgroup.mem_sup_left hv)) (Subgroup.mem_sup_left (Subgroup.mem_sup_right ha₁)))
      (Subgroup.mem_sup_right he)
  · have hva : v * a₀ = a₀ * v := (s.A₀_comm hp hT₂ h2 ha₀
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hv))).symm
    calc v * (a₀ * a₁) * e = (v * a₀) * a₁ * e := by group
      _ = (a₀ * v) * a₁ * e := by rw [hva]
      _ = a₀ * (v * a₁ * e) := by group


theorem pow_mem_A₀
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2)
    (hcop : Nat.Coprime (Nat.card (s.fr.A T₂)) (Nat.card s.fr.E)) {x : G}
    (hx : x ∈ s.fr.D₂ T₂) :
    x ^ Nat.card (s.fr.V T₂ ⊔ s.fr.A₁ T₂ ⊔ s.fr.E : Subgroup G) ∈ s.fr.A₀ T₂ ∧
      x ^ Nat.card (s.fr.V T₂ ⊔ s.fr.A₁ T₂ ⊔ s.fr.E : Subgroup G) ≠ 1 := by
  obtain ⟨-, -, -, hA₁A, -⟩ := s.A_decomp hp hT₂ h2 hcop
  have hcopY := s.coprime_card_A₀_Y hp hT₂ h2 hcop
  obtain ⟨hxX, hxY⟩ := hx
  obtain ⟨a, ha, y, hy, rfl⟩ := s.exists_decomp_X hp hT₂ h2 hcop hxX
  have hYX : s.fr.V T₂ ⊔ s.fr.A₁ T₂ ⊔ s.fr.E ≤ s.fr.V T₂ ⊔ s.fr.A T₂ ⊔ s.fr.E :=
    sup_le_sup_right (sup_le_sup_left hA₁A _) _
  have hay : Commute a y := s.A₀_comm hp hT₂ h2 ha (hYX hy)
  have hy1 : y ^ Nat.card (s.fr.V T₂ ⊔ s.fr.A₁ T₂ ⊔ s.fr.E : Subgroup G) = 1 :=
    (orderOf_dvd_iff_pow_eq_one).mp (Subgroup.orderOf_dvd_natCard _ hy)
  rw [hay.mul_pow, hy1, mul_one]
  refine ⟨Subgroup.pow_mem _ ha _, fun h1 => hxY ?_⟩
  have hdvd : orderOf a ∣ Nat.card (s.fr.V T₂ ⊔ s.fr.A₁ T₂ ⊔ s.fr.E : Subgroup G) :=
    orderOf_dvd_of_pow_eq_one h1
  have hdvd' : orderOf a ∣ Nat.card (s.fr.A₀ T₂) := Subgroup.orderOf_dvd_natCard _ ha
  have ha1 : a = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcopY hdvd' hdvd)
  rw [ha1, one_mul]
  exact hy

theorem mem_normalizer_V_of_D₂
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2)
    (hcop : Nat.Coprime (Nat.card (s.fr.A T₂)) (Nat.card s.fr.E)) {g x : G}
    (hx : x ∈ s.fr.D₂ T₂) (hgx : g * x * g⁻¹ ∈ s.fr.D₂ T₂) :
    g ∈ Subgroup.normalizer (s.fr.V T₂ : Set G) := by
  have hcycA := s.isCyclic_A hp hT₂ h2
  have hA₀A : s.fr.A₀ T₂ ≤ s.fr.A T₂ := inf_le_left
  obtain ⟨hy0, hy1⟩ := s.pow_mem_A₀ hp hT₂ h2 hcop hx
  obtain ⟨hy0', -⟩ := s.pow_mem_A₀ hp hT₂ h2 hcop hgx
  rw [conj_pow] at hy0'
  generalize x ^ Nat.card (s.fr.V T₂ ⊔ s.fr.A₁ T₂ ⊔ s.fr.E : Subgroup G) = y at hy0 hy1 hy0'
  have hZne : Subgroup.zpowers y ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hy1
  have hZA : Subgroup.zpowers y ≤ s.fr.A T₂ := Subgroup.zpowers_le.mpr (hA₀A hy0)
  have hZA' : Subgroup.zpowers (g * y * g⁻¹) ≤ s.fr.A T₂ :=
    Subgroup.zpowers_le.mpr (hA₀A hy0')
  have heq : Subgroup.zpowers (g * y * g⁻¹) = Subgroup.zpowers y :=
    eq_of_card_eq_of_le_cyclic hcycA hZA' hZA (by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_conj_mul])
  have hgN : g ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
    refine JT.mem_normalizer_of_conj_mem fun z hz => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← heq, ← conj_zpow]
    exact Subgroup.zpow_mem_zpowers _ k
  rw [← s.normalizer_eq_of lemma_4_2 hp hT₂ h2 hZA hZne]
  exact hgN

theorem normalizer_V_le_XY
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2)
    (hcop : Nat.Coprime (Nat.card (s.fr.A T₂)) (Nat.card s.fr.E)) {g : G}
    (hg : g ∈ Subgroup.normalizer (s.fr.V T₂ : Set G)) :
    g ∈ Subgroup.normalizer ((s.fr.V T₂ ⊔ s.fr.A T₂ ⊔ s.fr.E : Subgroup G) : Set G) ∧
      g ∈ Subgroup.normalizer ((s.fr.V T₂ ⊔ s.fr.A₁ T₂ ⊔ s.fr.E : Subgroup G) : Set G) := by
  obtain ⟨hA01, -, -, hA₁A, hEN₁⟩ := s.A_decomp hp hT₂ h2 hcop
  have hab := s.A_comm hp hT₂ h2
  have hVS := s.fr.V_le_S hT₂
  obtain ⟨U, -, hNV, hUE, -, -, hC, -, -⟩ := prop_4_3_ab G s.toHyp s.fr hp s.hidx hT₂ h2
  generalize hT₁ : (s.fr.S : Subgroup G) ⊓ Subgroup.centralizer (U : Set G) = T₁ at hC
  have hT₁S : T₁ ≤ (s.fr.S : Subgroup G) := hT₁ ▸ inf_le_left
  have hNVA : Subgroup.normalizer (s.fr.V T₂ : Set G) ≤
      Subgroup.normalizer (s.fr.A T₂ : Set G) := s.normalizer_V_le hp hT₂ h2 le_rfl
  have hgood : ∀ g, g ∈ Subgroup.normalizer (s.fr.V T₂ : Set G) →
      g ∈ Subgroup.normalizer (s.fr.A T₂ : Set G) → g ∈ Subgroup.normalizer (s.fr.E : Set G) →
      g ∈ Subgroup.normalizer ((s.fr.V T₂ ⊔ s.fr.A T₂ ⊔ s.fr.E : Subgroup G) : Set G) ∧
        g ∈ Subgroup.normalizer ((s.fr.V T₂ ⊔ s.fr.A₁ T₂ ⊔ s.fr.E : Subgroup G) : Set G) :=
    fun g hgV hgA hgE =>
      ⟨mem_normalizer_sup (mem_normalizer_sup hgV hgA) hgE,
        mem_normalizer_sup (mem_normalizer_sup hgV (mem_normalizer_commutator' hgE hgA)) hgE⟩
  have hSE : (s.fr.S : Subgroup G) ≤ Subgroup.normalizer (s.fr.E : Set G) := fun t ht =>
    JT.mem_normalizer_of_conj_mem fun e he => by
      rw [Subgroup.mem_centralizer_iff.mp (s.fr.E_le_CS he) t ht, mul_inv_cancel_right]
      exact he
  have hSV : (s.fr.S : Subgroup G) ≤ Subgroup.normalizer (s.fr.V T₂ : Set G) := fun t ht =>
    JT.mem_normalizer_of_conj_mem fun v hv => by
      rw [s.fr.comm_of_mem_S ht (hVS hv), mul_inv_cancel_right]
      exact hv
  have hSA : (s.fr.S : Subgroup G) ≤ Subgroup.normalizer (s.fr.A T₂ : Set G) := fun t ht =>
    JT.mem_normalizer_of_conj_mem fun x hx => s.fr.S_conj_mem_A ht hx hT₂
  have hAV : s.fr.A T₂ ≤ Subgroup.normalizer (s.fr.V T₂ : Set G) :=
    (s.A_le_centralizer_V T₂).trans (Subgroup.centralizer_le_normalizer _)
  have hAY : s.fr.A T₂ ≤
      Subgroup.normalizer ((s.fr.V T₂ ⊔ s.fr.A₁ T₂ ⊔ s.fr.E : Subgroup G) : Set G) := by
    intro a ha
    refine JT.mem_normalizer_of_conj_mem fun y hy => ?_
    have hEVA₁ : s.fr.E ≤
        Subgroup.normalizer ((s.fr.V T₂ ⊔ s.fr.A₁ T₂ : Subgroup G) : Set G) :=
      fun e he => mem_normalizer_sup (s.E_le_normalizer_V hT₂ he) (hEN₁ he)
    have hVA₁N : s.fr.A T₂ ≤
        Subgroup.normalizer ((s.fr.V T₂ ⊔ s.fr.A₁ T₂ : Subgroup G) : Set G) := fun a' ha' =>
      mem_normalizer_sup (hAV ha') (JT.mem_normalizer_of_conj_mem fun z hz => by
        rw [hab a' ha' z (hA₁A hz), mul_inv_cancel_right]
        exact hz)
    obtain ⟨w, hw, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hEVA₁).mp hy
    have h1 : a * (w * e) * a⁻¹ = (a * w * a⁻¹) * ⁅a, e⁆ * e := by
      rw [commutatorElement_def]; group
    rw [h1]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left
      ((Subgroup.mem_normalizer_iff.mp (hVA₁N ha) w).mp hw)) ?_) (Subgroup.mem_sup_right he)
    refine Subgroup.mem_sup_left (Subgroup.mem_sup_right ?_)
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator he ha)
  have hle : Subgroup.normalizer (s.fr.V T₂ : Set G) ≤
      Subgroup.normalizer ((s.fr.V T₂ ⊔ s.fr.A T₂ ⊔ s.fr.E : Subgroup G) : Set G) ⊓
        Subgroup.normalizer ((s.fr.V T₂ ⊔ s.fr.A₁ T₂ ⊔ s.fr.E : Subgroup G) : Set G) := by
    rw [hNV, ← hC.1]
    refine sup_le (fun u hu => ?_) (sup_le (fun v hv => ?_) (sup_le (sup_le
      (fun t ht => ?_) (fun a ha => ?_)) (fun e he => ?_)))
    · have huV : u ∈ Subgroup.normalizer (s.fr.V T₂ : Set G) := by
        rw [hNV]; exact Subgroup.mem_sup_left hu
      exact hgood u huV (hNVA huV) (Subgroup.centralizer_le_normalizer _ (hUE hu))
    · exact hgood v (hSV (hVS hv)) (hSA (hVS hv)) (hSE (hVS hv))
    · exact hgood t (hSV (hT₁S ht)) (hSA (hT₁S ht)) (hSE (hT₁S ht))
    · exact ⟨Subgroup.le_normalizer (Subgroup.mem_sup_left (Subgroup.mem_sup_right ha)),
        hAY ha⟩
    · exact ⟨Subgroup.le_normalizer (Subgroup.mem_sup_right he),
        Subgroup.le_normalizer (Subgroup.mem_sup_right he)⟩
  exact hle hg

theorem isTISubset_D₂
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2)
    (hcop : Nat.Coprime (Nat.card (s.fr.A T₂)) (Nat.card s.fr.E)) (hA₀ : s.fr.A₀ T₂ ≠ ⊥) :
    CFSG.IsTISubset (s.fr.D₂ T₂) (Subgroup.normalizer (s.fr.V T₂ : Set G)) := by
  have hcopY := s.coprime_card_A₀_Y hp hT₂ h2 hcop
  have hA₀A : s.fr.A₀ T₂ ≤ s.fr.A T₂ := inf_le_left
  have hne : (s.fr.D₂ T₂).Nonempty := by
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA₀
    refine ⟨a, Subgroup.mem_sup_left (Subgroup.mem_sup_right (hA₀A ha)), fun haY => ?_⟩
    have h1 : orderOf a ∣ Nat.card (s.fr.A₀ T₂) := Subgroup.orderOf_dvd_natCard _ ha
    have h2' : orderOf a ∣ Nat.card (s.fr.V T₂ ⊔ s.fr.A₁ T₂ ⊔ s.fr.E : Subgroup G) :=
      Subgroup.orderOf_dvd_natCard _ haY
    exact ha1 (Subtype.ext (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcopY h1 h2')))
  refine ⟨hne, fun h => h.2 (Subgroup.one_mem _), ?_, ?_⟩
  · apply le_antisymm
    · intro g hg
      by_contra hgV
      obtain ⟨x, hx⟩ := hne
      have hgx : g * x * g⁻¹ ∈ s.fr.D₂ T₂ := (Subgroup.mem_set_normalizer_iff.mp hg x).mp hx
      exact hgV (s.mem_normalizer_V_of_D₂ hp hT₂ h2 hcop hx hgx)
    · intro g hg
      obtain ⟨hgX, hgY⟩ := s.normalizer_V_le_XY hp hT₂ h2 hcop hg
      rw [Subgroup.mem_set_normalizer_iff]
      intro n
      constructor
      · rintro ⟨hnX, hnY⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hgX n).mp hnX,
          fun h => hnY ((Subgroup.mem_normalizer_iff.mp hgY n).mpr h)⟩
      · rintro ⟨hnX, hnY⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hgX n).mpr hnX,
          fun h => hnY ((Subgroup.mem_normalizer_iff.mp hgY n).mp h)⟩
  · intro g hg
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro x ⟨hx, ⟨y, hy, rfl⟩⟩
    apply hg
    have hgy : g * (g⁻¹ * y * g) * g⁻¹ ∈ s.fr.D₂ T₂ := by
      rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
      exact hy
    exact s.mem_normalizer_V_of_D₂ hp hT₂ h2 hcop hx hgy

end Std

theorem cor_4_4_of
    (h41 : S_prop_4_1_three) : S_cor_4_4 := by
  intro G _ _ s hp T₂ hT₂ h2 hR
  have hcop := s.coprime_card_A_E h41 hR hp hT₂ h2
  exact ⟨s.coprime_card_A_index hp hT₂ h2 hcop, fun hA₀ => s.isTISubset_D₂ hp hT₂ h2 hcop hA₀⟩

end CFSG.Walter.W67
