module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem9

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

namespace Sec1219Geom

variable {G : Type} [Group G] [Finite G]

theorem le_commutator_sup_centralizer {P X : Subgroup G}
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hsolv : Group.IsSolvable ↥P)
    (hcop : Nat.Coprime (Nat.card X) (Nat.card P)) :
    P ≤ ⁅P, X⁆ ⊔ (P ⊓ Subgroup.centralizer (X : Set G)) := by
  have : Subgroup.Normalizes X P := ⟨hXP⟩
  have hsup := CFSG.fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (A := ↥X) (G := ↥P) hsolv hcop
  have hcommMap : (CFSG.commutatorAction (A := ↥X) (G := ↥P)).map P.subtype = ⁅P, X⁆ :=
    CFSG.commutatorAction_subgroup_conj_map_eq_commutator P X hXP
  have hfixEq : CFSG.fixedPointSubgroup ↥X ↥P =
      (P ⊓ Subgroup.centralizer (X : Set G)).subgroupOf P := by
    simpa [CFSG.subgroupCentralizerIn] using
      CFSG.fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn P X hXP
  intro x hx
  have htop : (⟨x, hx⟩ : ↥P) ∈ CFSG.fixedPointSubgroup ↥X ↥P ⊔
      CFSG.commutatorAction (A := ↥X) (G := ↥P) := by
    rw [hsup]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem P.subtype htop
  rw [Subgroup.map_sup, hcommMap, hfixEq, Subgroup.map_subgroupOf_eq_of_le inf_le_left] at hmap
  rw [sup_comm]
  exact hmap

theorem four_le_index {W X : Subgroup G} (hW2 : ∀ w ∈ W, w ^ 2 = 1)
    (hXW : ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ ∈ W)
    (hXo : Odd (Nat.card X)) (hne : ¬ W ≤ Subgroup.centralizer (X : Set G)) :
    4 ≤ ((W ⊓ Subgroup.centralizer (X : Set G)).subgroupOf W).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := (W ⊓ Subgroup.centralizer (X : Set G)).subgroupOf W with hD
  have hWp : IsPGroup 2 ↥W := fun w => ⟨1, Subtype.ext (by simpa using hW2 w w.2)⟩
  obtain ⟨k, hk⟩ := hWp.exists_card_eq
  have hidx : D.index ∣ 2 ^ k := hk ▸ Subgroup.index_dvd_card D
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hidx
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.index_eq_one] at hj
    apply hne
    intro w hw
    have : (⟨w, hw⟩ : ↥W) ∈ D := by rw [hj]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).2
  have hj1 : j ≠ 1 := by
    rintro rfl
    rw [pow_one] at hj
    obtain ⟨w, hw, hwC⟩ := IsConcreteLE.not_le_iff_exists.mp hne
    rw [Subgroup.mem_centralizer_iff] at hwC
    push Not at hwC
    obtain ⟨x, hx, hxw⟩ := hwC
    have hxo : Odd (orderOf x) := Odd.of_dvd_nat hXo (Subgroup.orderOf_dvd_natCard X hx)
    have hw'W : x * w * x⁻¹ ∈ W := hXW x hx w hw
    have hmemD : ∀ y (hy : y ∈ W),
        (⟨y, hy⟩ : ↥W) ∈ D ↔ y ∈ Subgroup.centralizer (X : Set G) := fun y hy => by
      rw [hD, Subgroup.mem_subgroupOf]
      exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
    have hwD : (⟨w, hw⟩ : ↥W) ∉ D := by
      rw [hmemD]
      exact fun h => hxw ((Subgroup.mem_centralizer_iff.mp h) x hx)
    have hw'D : (⟨x * w * x⁻¹, hw'W⟩ : ↥W) ∉ D := by
      rw [hmemD]
      intro h
      apply hwD
      rw [hmemD]
      have h2 : x⁻¹ * (x * w * x⁻¹) = (x * w * x⁻¹) * x⁻¹ :=
        (Subgroup.mem_centralizer_iff.mp h) x⁻¹ (X.inv_mem hx)
      have e : w = x * w * x⁻¹ := by
        calc w = x⁻¹ * (x * w * x⁻¹) * x := by group
          _ = (x * w * x⁻¹) * x⁻¹ * x := by rw [h2]
          _ = x * w * x⁻¹ := by group
      rw [e]
      exact h
    have hcD : (⟨x * w * x⁻¹, hw'W⟩ : ↥W) * ⟨w, hw⟩ ∈ D :=
      (Subgroup.mul_mem_iff_of_index_two hj).mpr (iff_of_false hw'D hwD)
    set c := x * w * x⁻¹ * w with hc
    clear_value c
    have hcW : c ∈ W := hc ▸ W.mul_mem hw'W hw
    have hcC : c ∈ Subgroup.centralizer (X : Set G) := (hmemD c hcW).mp (by subst hc; exact hcD)
    have hxc : x * c * x⁻¹ = c := by
      rw [(Subgroup.mem_centralizer_iff.mp hcC) x hx, mul_inv_cancel_right]
    have hxw' : x * w * x⁻¹ = c * w := by
      calc x * w * x⁻¹ = x * w * x⁻¹ * (w * w) := by rw [← pow_two, hW2 w hw, mul_one]
        _ = c * w := by rw [hc]; group
    have hpow : ∀ m : ℕ, x ^ m * w * (x ^ m)⁻¹ = c ^ m * w := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        calc x ^ (m + 1) * w * (x ^ (m + 1))⁻¹ = x * (x ^ m * w * (x ^ m)⁻¹) * x⁻¹ := by group
          _ = x * (c ^ m * w) * x⁻¹ := by rw [ih]
          _ = (x * c ^ m * x⁻¹) * (x * w * x⁻¹) := by group
          _ = c ^ m * (c * w) := by rw [← conj_pow, hxc, hxw']
          _ = c ^ (m + 1) * w := by rw [pow_succ, mul_assoc]
    have h1 := hpow (orderOf x)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
    obtain ⟨r, hr⟩ := hxo
    have hcr : c ^ orderOf x = c := by
      rw [hr, pow_succ, pow_mul, hW2 c hcW, one_pow, one_mul]
    rw [hcr] at h1
    have hc1 : c = 1 := by
      have h3 : c * w = 1 * w := by rw [one_mul]; exact h1.symm
      exact mul_right_cancel h3
    apply hxw
    have h4 : x * w * x⁻¹ = w := by rw [hxw', hc1, one_mul]
    calc x * w = (x * w * x⁻¹) * x := by group
      _ = w * x := by rw [h4]
  have h2 : 2 ≤ j := by omega
  rw [hj]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) h2

variable {T L V V₁ V₂ : Subgroup G} {n : ℕ}

theorem conj_mem_of_odd (hyp : Hyp121 G T L V V₁ V₂ n) [IsMulCommutative ↥V] {x : G}
    (hxM : x ∈ Subgroup.normalizer (L : Set G)) (hodd : Odd (orderOf x)) :
    (∀ a ∈ V₁, x * a * x⁻¹ ∈ V₁) ∧ ∀ c ∈ V₂, x * c * x⁻¹ ∈ V₂ := by
  rcases Sec1212.conj_mem_of_hyp121 hyp hxM with h | h
  · exact h
  · exfalso
    obtain ⟨hc₁, hnat₁⟩ := hyp.nat₁
    have hV₁0 : V₁ ≠ ⊥ :=
      Sec121Q.ne_bot_of_natural (by rcases hyp.rank with h | h <;> omega) hnat₁
    have hx1 : x ∉ Subgroup.normalizer (V₁ : Set G) := by
      intro hN
      apply hV₁0
      rw [eq_bot_iff]
      intro a ha
      have h1 : x * a * x⁻¹ ∈ V₁ ⊓ V₂ := ⟨(Subgroup.mem_normalizer_iff.mp hN a).mp ha, h a ha⟩
      rw [hyp.inf, Subgroup.mem_bot] at h1
      rw [Subgroup.mem_bot]
      calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨h1, h2⟩ := Sec121Swap.swap_of_hyp121 hyp hxM hx1
    have hx2 : x ^ 2 ∈ Subgroup.normalizer (V₁ : Set G) :=
      Sec121Swap.mem_normalizer_of_conj_mem fun a ha => by
        have h3 := h2 _ (h1 a ha)
        have e : x ^ 2 * a * (x ^ 2)⁻¹ = x * (x * a * x⁻¹) * x⁻¹ := by rw [pow_two]; group
        rw [e]
        exact h3
    apply hx1
    obtain ⟨k, hk⟩ := hodd
    have e : x = (x ^ 2) ^ (k + 1) := by
      rw [← pow_mul]
      calc x = x ^ (orderOf x + 1) := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
        _ = x ^ (2 * (k + 1)) := by rw [hk]; ring_nf
    rw [e]
    exact Subgroup.pow_mem _ hx2 _

theorem exists_mem_of_conj_mem (hyp : Hyp121 G T L V V₁ V₂ n) [IsMulCommutative ↥V] {x : G}
    (hxM : x ∈ Subgroup.normalizer (L : Set G)) (hx₁ : ∀ a ∈ V₁, x * a * x⁻¹ ∈ V₁) :
    ∃ l ∈ L, l⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨hc₁, hnat₁⟩ := hyp.nat₁
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hxN : x ∈ Subgroup.normalizer (V₁ : Set G) := Sec121Swap.mem_normalizer_of_conj_mem hx₁
  have hτ : conjAct V₁ ⟨x, hxN⟩ ∈ autOn L V₁ := by
    rw [G64.BinaryNaturalSL.eq_top hnat₁]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hl⟩, hlτ⟩ := (A4.mem_autOn_iff hyp.norm₁).mp hτ
  refine ⟨l, hl, Sec1212.mem_centralizer_of_hyp121 hyp hV₁V hyp.norm₁ hnat₁
    ((Subgroup.normalizer (L : Set G)).mul_mem
      (Subgroup.inv_mem _ (Subgroup.le_normalizer hl)) hxM) ?_⟩
  refine Sec1212.mem_centralizer_iff_conj.mpr fun a ha => ?_
  have h1 := congrArg (fun φ : MulAut ↥V₁ => ((φ ⟨a, ha⟩ : ↥V₁) : G)) hlτ
  simp only [A4.actionOn_apply_coe, InternalSec.coe_conjAct_apply] at h1
  calc l⁻¹ * x * a * (l⁻¹ * x)⁻¹ = l⁻¹ * (x * a * x⁻¹) * l := by group
    _ = l⁻¹ * (l * a * l⁻¹) * l := by rw [h1]
    _ = a := by group

end Sec1219Geom

open Sec1219Geom in
theorem lem1219Geom_holds : Lem1219Geom := by
  intro G _ _ T L V V₁ V₂ n β hyp hβ X hXM hXo hXV U hUV hXU hsing
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVe := Sec121Thm.isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have hcV : IsMulCommutative ↥V := hVe.1
  obtain ⟨hcard₁, hcard₂, hcardV⟩ := Sec1212.card_eq_of_hyp121 hyp
  have hV₁V : V₁ ≤ V := hyp.sup ▸ le_sup_left
  have hV₂V : V₂ ≤ V := hyp.sup ▸ le_sup_right
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥V) ⟨b, hb⟩)
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := hVe.2
  have hinv2 : ∀ v ∈ V, v⁻¹ = v := fun v hv =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two, hV2 v hv])
  obtain ⟨hβ₁, hβ₂, hnd₁, hnd₂, hβL⟩ := hβ
  have h2self : ∀ y : ZMod 2, y + y = 0 := fun y => CharTwo.add_self_eq_zero y
  have hβ1 : ∀ a ∈ V₁, β a 1 = 0 := fun a ha => by
    have h := hβ₂ a ha 1 V₂.one_mem 1 V₂.one_mem
    rw [mul_one] at h
    have h3 := h2self (β a 1)
    rwa [← h] at h3
  have hβ1' : ∀ c ∈ V₂, β 1 c = 0 := fun c hc => by
    have h := hβ₁ 1 V₁.one_mem 1 V₁.one_mem c hc
    rw [mul_one] at h
    have h3 := h2self (β 1 c)
    rwa [← h] at h3
  have hxodd : ∀ x ∈ X, Odd (orderOf x) := fun x hx =>
    Odd.of_dvd_nat hXo (Subgroup.orderOf_dvd_natCard X hx)
  have hXV₁ : ∀ x ∈ X, ∀ a ∈ V₁, x * a * x⁻¹ ∈ V₁ := fun x hx =>
    (conj_mem_of_odd hyp (hXM hx) (hxodd x hx)).1
  have hXV₂ : ∀ x ∈ X, ∀ c ∈ V₂, x * c * x⁻¹ ∈ V₂ := fun x hx =>
    (conj_mem_of_odd hyp (hXM hx) (hxodd x hx)).2
  have hinv : ∀ x ∈ X, ∀ a ∈ V₁, ∀ c ∈ V₂, β (x * a * x⁻¹) (x * c * x⁻¹) = β a c := by
    intro x hx a ha c hc
    obtain ⟨l, hl, hlx⟩ := exists_mem_of_conj_mem hyp (hXM hx) (hXV₁ x hx)
    have e : ∀ v ∈ V, x * v * x⁻¹ = l * v * l⁻¹ := fun v hv => by
      have h1 := Sec1212.mem_centralizer_iff_conj.mp hlx v hv
      calc x * v * x⁻¹ = l * (l⁻¹ * x * v * (l⁻¹ * x)⁻¹) * l⁻¹ := by group
        _ = l * v * l⁻¹ := by rw [h1]
    rw [e a (hV₁V ha), e c (hV₂V hc)]
    exact hβL l hl a ha c hc
  have hfix : ∀ y ∈ Subgroup.centralizer (X : Set G), ∀ x ∈ X, x * y * x⁻¹ = y :=
    fun y hy x hx => by rw [(Subgroup.mem_centralizer_iff.mp hy) x hx, mul_inv_cancel_right]
  obtain ⟨hc₁, hnat₁⟩ := hyp.nat₁
  obtain ⟨hc₂, hnat₂⟩ := hyp.nat₂
  have hne₁ : ¬ V₁ ≤ Subgroup.centralizer (X : Set G) := fun h => hXV fun x hx =>
    Sec1212.mem_centralizer_of_hyp121 hyp hV₁V hyp.norm₁ hnat₁ (hXM hx)
      (Subgroup.le_centralizer_iff.mp h hx)
  have hne₂ : ¬ V₂ ≤ Subgroup.centralizer (X : Set G) := fun h => hXV fun x hx =>
    Sec1212.mem_centralizer_of_hyp121 hyp hV₂V hyp.norm₂ hnat₂ (hXM hx)
      (Subgroup.le_centralizer_iff.mp h hx)
  set C₁ := V₁ ⊓ Subgroup.centralizer (X : Set G) with hC₁
  set C₂ := V₂ ⊓ Subgroup.centralizer (X : Set G) with hC₂
  have hker₂ : ∀ a ∈ C₁, ∀ w ∈ ⁅V₂, X⁆, β a w = 0 := by
    intro a ha w hw
    let K : Subgroup G :=
      { carrier := {w | w ∈ V₂ ∧ β a w = 0}
        mul_mem' := fun {u w} hu hw => ⟨V₂.mul_mem hu.1 hw.1, by
          rw [hβ₂ a ha.1 u hu.1 w hw.1, hu.2, hw.2, add_zero]⟩
        one_mem' := ⟨V₂.one_mem, hβ1 a ha.1⟩
        inv_mem' := fun {w} hw => by
          show w⁻¹ ∈ V₂ ∧ β a w⁻¹ = 0
          rw [hinv2 w (hV₂V hw.1)]
          exact hw }
    have hle : ⁅V₂, X⁆ ≤ K := by
      rw [Subgroup.commutator_le]
      intro c hc x hx
      have hxc : x * c⁻¹ * x⁻¹ ∈ V₂ := hXV₂ x hx _ (V₂.inv_mem hc)
      have e : ⁅c, x⁆ = c * (x * c⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
      refine ⟨by rw [e]; exact V₂.mul_mem hc hxc, ?_⟩
      show β a ⁅c, x⁆ = 0
      rw [e, hβ₂ a ha.1 c hc _ hxc]
      have h1 := hinv x hx a ha.1 c⁻¹ (V₂.inv_mem hc)
      rw [hfix a ha.2 x hx, hinv2 c (hV₂V hc)] at h1
      rw [hinv2 c (hV₂V hc), h1]
      exact h2self _
    exact (hle hw).2
  have hker₁ : ∀ c ∈ C₂, ∀ w ∈ ⁅V₁, X⁆, β w c = 0 := by
    intro c hc w hw
    let K : Subgroup G :=
      { carrier := {w | w ∈ V₁ ∧ β w c = 0}
        mul_mem' := fun {u w} hu hw => ⟨V₁.mul_mem hu.1 hw.1, by
          rw [hβ₁ u hu.1 w hw.1 c hc.1, hu.2, hw.2, add_zero]⟩
        one_mem' := ⟨V₁.one_mem, hβ1' c hc.1⟩
        inv_mem' := fun {w} hw => by
          show w⁻¹ ∈ V₁ ∧ β w⁻¹ c = 0
          rw [hinv2 w (hV₁V hw.1)]
          exact hw }
    have hle : ⁅V₁, X⁆ ≤ K := by
      rw [Subgroup.commutator_le]
      intro a ha x hx
      have hxa : x * a⁻¹ * x⁻¹ ∈ V₁ := hXV₁ x hx _ (V₁.inv_mem ha)
      have e : ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
      refine ⟨by rw [e]; exact V₁.mul_mem ha hxa, ?_⟩
      show β ⁅a, x⁆ c = 0
      rw [e, hβ₁ a ha _ hxa c hc.1]
      have h1 := hinv x hx a⁻¹ (V₁.inv_mem ha) c hc.1
      rw [hfix c hc.2 x hx, hinv2 a (hV₁V ha)] at h1
      rw [hinv2 a (hV₁V ha), h1]
      exact h2self _
    exact (hle hw).2
  have hcop : ∀ {W : Subgroup G}, W ≤ V → Nat.card W = 2 ^ n →
      Nat.Coprime (Nat.card X) (Nat.card W) :=
    fun _ hW => by
      rw [hW]
      exact Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hXo)
  have hsolv : ∀ {W : Subgroup G}, W ≤ V → Group.IsSolvable ↥W := fun hWV =>
    Group.isSolvable_of_comm fun a b => Subtype.ext (hVc a (hWV a.2) b (hWV b.2))
  have hdec₂ := le_commutator_sup_centralizer
    (fun x hx => Sec121Swap.mem_normalizer_of_conj_mem (hXV₂ x hx)) (hsolv hV₂V) (hcop hV₂V hcard₂)
  have hdec₁ := le_commutator_sup_centralizer
    (fun x hx => Sec121Swap.mem_normalizer_of_conj_mem (hXV₁ x hx)) (hsolv hV₁V) (hcop hV₁V hcard₁)
  have hcommV₂ : ∀ a ∈ ⁅V₂, X⁆, ∀ b ∈ C₂, a * b = b * a := fun a ha b hb =>
    hVc a (hV₂V (Subgroup.le_normalizer_iff_commutator_le_left.1
      (fun x hx => Sec121Swap.mem_normalizer_of_conj_mem (hXV₂ x hx)) ha)) b (hV₂V hb.1)
  have hcommV₁ : ∀ a ∈ ⁅V₁, X⁆, ∀ b ∈ C₁, a * b = b * a := fun a ha b hb =>
    hVc a (hV₁V (Subgroup.le_normalizer_iff_commutator_le_left.1
      (fun x hx => Sec121Swap.mem_normalizer_of_conj_mem (hXV₁ x hx)) ha)) b (hV₁V hb.1)
  have hnd₁' : ∀ a ∈ C₁, a ≠ 1 → ∃ c ∈ C₂, β a c = 1 := by
    intro a ha ha1
    by_contra hcon
    push Not at hcon
    obtain ⟨c, hc, hac⟩ := hnd₁ a ha.1 ha1
    obtain ⟨w, hw, c₂, hc₂, rfl⟩ := Sec121Thm.exists_mul_of_mem_sup hcommV₂ (hdec₂ hc)
    have hwV : w ∈ V₂ := Subgroup.le_normalizer_iff_commutator_le_left.1
      (fun x hx => Sec121Swap.mem_normalizer_of_conj_mem (hXV₂ x hx)) hw
    rw [hβ₂ a ha.1 w hwV c₂ hc₂.1, hker₂ a ha w hw, zero_add] at hac
    exact hcon c₂ hc₂ hac
  have hnd₂' : ∀ c ∈ C₂, c ≠ 1 → ∃ a ∈ C₁, β a c = 1 := by
    intro c hc hc1
    by_contra hcon
    push Not at hcon
    obtain ⟨a, ha, hac⟩ := hnd₂ c hc.1 hc1
    obtain ⟨w, hw, a₁, ha₁, rfl⟩ := Sec121Thm.exists_mul_of_mem_sup hcommV₁ (hdec₁ ha)
    have hwV : w ∈ V₁ := Subgroup.le_normalizer_iff_commutator_le_left.1
      (fun x hx => Sec121Swap.mem_normalizer_of_conj_mem (hXV₁ x hx)) hw
    rw [hβ₁ w hwV a₁ ha₁.1 c hc.1, hker₁ c hc w hw, zero_add] at hac
    exact hcon a₁ ha₁ hac
  have hUdec : ∀ u ∈ U, ∃ a ∈ C₁, ∃ c ∈ C₂, u = a * c ∧ β a c = 0 := by
    intro u hu
    obtain ⟨a, ha, c, hc, rfl, hac⟩ := hsing u hu
    have huC : a * c ∈ Subgroup.centralizer (X : Set G) := Subgroup.le_centralizer_iff.mp hXU hu
    have key : ∀ x ∈ X, x * a * x⁻¹ = a ∧ x * c * x⁻¹ = c := fun x hx =>
      Sec1212.decomp_unique hyp.inf (hXV₁ x hx a ha) (hXV₂ x hx c hc) ha hc
        (by rw [← hfix _ huC x hx]; group)
    have hcen : ∀ {y : G}, (∀ x ∈ X, x * y * x⁻¹ = y) → y ∈ Subgroup.centralizer (X : Set G) :=
      fun {y} h => Subgroup.mem_centralizer_iff.mpr fun x hx => by
        calc x * y = (x * y * x⁻¹) * x := by group
          _ = y * x := by rw [h x hx]
    exact ⟨a, ⟨ha, hcen fun x hx => (key x hx).1⟩, c, ⟨hc, hcen fun x hx => (key x hx).2⟩,
      rfl, hac⟩
  have hinfC : C₁ ⊓ C₂ = ⊥ := by
    rw [eq_bot_iff, ← hyp.inf]
    exact inf_le_inf inf_le_left inf_le_left
  have hcC : IsMulCommutative ↥(C₁ ⊔ C₂) :=
    ⟨⟨fun a b => Subtype.ext (hVc a ((sup_le (inf_le_left.trans hV₁V)
      (inf_le_left.trans hV₂V)) a.2) b ((sup_le (inf_le_left.trans hV₁V)
      (inf_le_left.trans hV₂V)) b.2))⟩⟩
  have hβC : IsDualPairing121 (⊥ : Subgroup G) C₁ C₂ β :=
    ⟨fun a ha b hb c hc => hβ₁ a ha.1 b hb.1 c hc.1, fun a ha c hc d hd => hβ₂ a ha.1 c hc.1 d hd.1,
      hnd₁', hnd₂', fun l hl a _ c _ => by
        rw [Subgroup.mem_bot] at hl
        subst hl
        simp⟩
  have hUC : U ≤ C₁ ⊔ C₂ := fun u hu => by
    obtain ⟨a, ha, c, hc, rfl, -⟩ := hUdec u hu
    exact (C₁ ⊔ C₂).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hc)
  have hcardU : Nat.card U ≤ Nat.card C₂ :=
    Sec1212.card_le_of_forall_singular (L := ⊥) le_sup_left le_sup_right rfl hinfC hβC hUC
      fun u hu => hUdec u hu
  have hidx := four_le_index (fun w hw => hV2 w (hV₂V hw)) hXV₂ hXo hne₂
  have hC₂card : 4 * Nat.card C₂ ≤ 2 ^ n := by
    have h1 := Subgroup.card_mul_index (C₂.subgroupOf V₂)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hcard₂] at h1
    calc 4 * Nat.card C₂ ≤ (C₂.subgroupOf V₂).index * Nat.card C₂ := Nat.mul_le_mul_right _ hidx
      _ = 2 ^ n := by rw [mul_comm]; exact h1
  have hU2 : IsPGroup 2 ↥U := fun u => ⟨1, Subtype.ext (by simpa using hV2 u (hUV u.2))⟩
  obtain ⟨j, hj⟩ := hU2.exists_card_eq
  have hjn : j + 2 ≤ n := by
    have h1 : 2 ^ (j + 2) ≤ 2 ^ n := by
      rw [pow_add, ← hj, mul_comm]
      exact (Nat.mul_le_mul_left 4 hcardU).trans hC₂card
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hrel : U.relIndex V * 2 ^ j = 2 ^ n * 2 ^ n := by
    have h1 := Subgroup.card_mul_index (U.subgroupOf V)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv, hj, hcardV] at h1
    rw [mul_comm]
    exact h1
  have hrel' : U.relIndex V = 2 ^ (2 * n - j) := by
    have h2 : 2 ^ n * 2 ^ n = 2 ^ (2 * n - j) * 2 ^ j := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    rw [h2] at hrel
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hrel
  rw [mQuot, hrel', padicValNat.prime_pow]
  omega

end CFSG.Quasithin.H13
