module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OuterRSplit
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.SupCommute
public import CFSG.Quasithin.Background.A1cRank
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qz
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1BlockPushUp
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompR

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.ComponentClassification

variable {G : Type} [Group G]

theorem exists_orderOf_normalizerMonoidHom {X : Subgroup G} {r : ℕ} (hr : r.Prime) {y : G}
    (hyN : y ∈ Subgroup.normalizer (X : Set G)) (hyo : ∃ k : ℕ, orderOf y = r ^ k) :
    ∃ i : ℕ, orderOf (X.normalizerMonoidHom ⟨y, hyN⟩) = r ^ i := by
  obtain ⟨k, hk⟩ := hyo
  have h1 : orderOf (⟨y, hyN⟩ : Subgroup.normalizer (X : Set G)) = orderOf y :=
    (Subgroup.orderOf_coe (⟨y, hyN⟩ : Subgroup.normalizer (X : Set G))).symm
  have h2 : orderOf (X.normalizerMonoidHom ⟨y, hyN⟩) ∣ r ^ k := by
    rw [← hk, ← h1]
    exact orderOf_map_dvd _ _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hr).1 h2
  exact ⟨i, hi⟩

theorem exists_elemAbelian_cube_of_normalizer [Finite G] {r : ℕ} (hr : r.Prime)
    {X : Subgroup G} (hZ : Subgroup.center X = ⊥) (hX : OuterRSplit X r 2)
    {y : G} (hyN : y ∈ Subgroup.normalizer (X : Set G)) (hyo : ∃ k : ℕ, orderOf y = r ^ k)
    (hyX : y ∉ X) (hyr : y ^ r ∈ X) :
    ∃ E : Subgroup G, IsElemAbelian r E ∧ Nat.card E = r ^ 3 := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  set α : MulAut X := X.normalizerMonoidHom ⟨y, hyN⟩ with hαdef
  have hα : ∀ a : X, ((α a : X) : G) = y * a * y⁻¹ := fun a =>
    Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨y, hyN⟩ a
  have hαr : α ^ r = MulAut.conj (⟨y ^ r, hyr⟩ : X) := by
    refine MulEquiv.ext fun a => Subtype.ext ?_
    rw [UC22.uc22p22qz_pow_apply hα r a]
    simp [MulAut.conj_apply]
  obtain ⟨β, hβα, hβr, E₀, hE₀, hE₀card, hE₀fix⟩ :=
    hX α (exists_orderOf_normalizerMonoidHom hr hyN hyo) (hαr ▸ ⟨_, rfl⟩)
  obtain ⟨g, hg⟩ := hβα
  have hβ : β = MulAut.conj g * α := by
    rw [hg, mul_assoc, inv_mul_cancel, mul_one]
  set z : G := (g : G) * y with hzdef
  have hz : ∀ a : X, ((β a : X) : G) = z * a * z⁻¹ := by
    intro a
    rw [hβ, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hα, hzdef]
    group
  have hzr : z ^ r ∈ X := by
    have h1 := CFSG.LocalAnalysis.RankThreeTheoremC.mul_pow_mul_inv_pow_mem g.2 hyN r
    have h2 : z ^ r = ((g * y) ^ r * (y ^ r)⁻¹) * y ^ r := by rw [inv_mul_cancel_right, hzdef]
    rw [h2]
    exact X.mul_mem h1 hyr
  have hzr1 : z ^ r = 1 := by
    have hcent : (⟨z ^ r, hzr⟩ : X) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro b
      apply Subtype.ext
      have h1 := UC22.uc22p22qz_pow_apply hz r b
      rw [hβr, MulAut.one_apply] at h1
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      calc (b : G) * z ^ r = z ^ r * b * (z ^ r)⁻¹ * z ^ r := by rw [← h1]
        _ = z ^ r * b := by group
    rw [hZ, Subgroup.mem_bot] at hcent
    exact congrArg Subtype.val hcent
  have hzX : z ∉ X := by
    intro hz'
    apply hyX
    have : y = (g : G)⁻¹ * z := by rw [hzdef]; group
    rw [this]
    exact X.mul_mem (X.inv_mem g.2) hz'
  have hzord : orderOf z = r := by
    refine orderOf_eq_prime hzr1 ?_
    intro h1
    exact hzX (h1 ▸ X.one_mem)
  set E₁ : Subgroup G := E₀.map X.subtype with hE₁
  have hE₁ab : IsElemAbelian r E₁ := hE₀.map X.subtype
  have hE₁card : Nat.card E₁ = r ^ 2 := by
    rw [hE₁, Subgroup.card_map_of_injective X.subtype_injective, hE₀card]
  have hcomm : ∀ e ∈ E₁, Commute e z := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 := hz a
    rw [hE₀fix a ha] at h1
    change (a : G) * z = z * a
    calc (a : G) * z = z * a * z⁻¹ * z := by rw [← h1]
      _ = z * a := by group
  have hzE₁ : z ∉ E₁ := by
    rintro ⟨a, -, ha⟩
    exact hzX (ha ▸ a.2)
  obtain ⟨hEab, hEcard⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hE₁ab hzord hcomm hzE₁
  refine ⟨E₁ ⊔ Subgroup.zpowers z, hEab, ?_⟩
  rw [hEcard, hE₁card]
  ring

theorem exists_elemAbelian_cube_of_pair [Finite G] {r : ℕ} (hr : r.Prime)
    {X₁ X₂ : Subgroup G} (hc : ∀ a ∈ X₁, ∀ b ∈ X₂, a * b = b * a)
    (hZ₁ : Subgroup.center X₁ = ⊥) (hZ₂ : Subgroup.center X₂ = ⊥)
    (h₁ : OuterRSplit X₁ r 1) (h₂ : OuterRSplit X₂ r 1) {y : G}
    (hy₁ : y ∈ Subgroup.normalizer (X₁ : Set G)) (hy₂ : y ∈ Subgroup.normalizer (X₂ : Set G))
    (hyo : ∃ k : ℕ, orderOf y = r ^ k) (hyX : y ∉ X₁ ⊔ X₂) (hyr : y ^ r ∈ X₁ ⊔ X₂) :
    ∃ E : Subgroup G, IsElemAbelian r E ∧ Nat.card E = r ^ 3 := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hc' : ∀ a ∈ X₁, ∀ b ∈ X₂, Commute a b := fun a ha b hb => hc a ha b hb
  have hinf : X₁ ⊓ X₂ = ⊥ := CFSG.Quasithin.S143.InspW2.inf_eq_bot_of_commute hZ₁ hc
  have hyS : y ∈ Subgroup.normalizer ((X₁ ⊔ X₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hy₁ hy₂ ⊢
    rw [Subgroup.map_sup, hy₁, hy₂]
  obtain ⟨a₁, ha₁, a₂, ha₂, hyra⟩ := (CFSG.mem_sup_of_commute hc').1 hyr
  set α₁ : MulAut X₁ := X₁.normalizerMonoidHom ⟨y, hy₁⟩ with hα₁def
  set α₂ : MulAut X₂ := X₂.normalizerMonoidHom ⟨y, hy₂⟩ with hα₂def
  have hα₁ : ∀ a : X₁, ((α₁ a : X₁) : G) = y * a * y⁻¹ := fun a =>
    Subgroup.normalizerMonoidHom_apply_apply_coe X₁ ⟨y, hy₁⟩ a
  have hα₂ : ∀ a : X₂, ((α₂ a : X₂) : G) = y * a * y⁻¹ := fun a =>
    Subgroup.normalizerMonoidHom_apply_apply_coe X₂ ⟨y, hy₂⟩ a
  have hα₁r : α₁ ^ r = MulAut.conj (⟨a₁, ha₁⟩ : X₁) := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [UC22.uc22p22qz_pow_apply hα₁ r b, ← hyra]
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    have hb : (b : G) * a₂ = a₂ * b := hc b b.2 a₂ ha₂
    calc a₁ * a₂ * (b : G) * (a₁ * a₂)⁻¹ = a₁ * (a₂ * b) * a₂⁻¹ * a₁⁻¹ := by group
      _ = a₁ * b * a₁⁻¹ := by rw [← hb]; group
  have hα₂r : α₂ ^ r = MulAut.conj (⟨a₂, ha₂⟩ : X₂) := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [UC22.uc22p22qz_pow_apply hα₂ r b, ← hyra]
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    have hmem : a₂ * (b : G) * a₂⁻¹ ∈ X₂ := X₂.mul_mem (X₂.mul_mem ha₂ b.2) (X₂.inv_mem ha₂)
    have hb : a₁ * (a₂ * (b : G) * a₂⁻¹) = (a₂ * (b : G) * a₂⁻¹) * a₁ := hc a₁ ha₁ _ hmem
    calc a₁ * a₂ * (b : G) * (a₁ * a₂)⁻¹ = (a₁ * (a₂ * (b : G) * a₂⁻¹)) * a₁⁻¹ := by group
      _ = a₂ * b * a₂⁻¹ := by rw [hb]; group
  obtain ⟨β₁, hβα₁, hβ₁r, E₁, hE₁, hE₁card, hE₁fix⟩ :=
    h₁ α₁ (exists_orderOf_normalizerMonoidHom hr hy₁ hyo) (hα₁r ▸ ⟨_, rfl⟩)
  obtain ⟨β₂, hβα₂, hβ₂r, E₂, hE₂, hE₂card, hE₂fix⟩ :=
    h₂ α₂ (exists_orderOf_normalizerMonoidHom hr hy₂ hyo) (hα₂r ▸ ⟨_, rfl⟩)
  obtain ⟨g₁, hg₁⟩ := hβα₁
  obtain ⟨g₂, hg₂⟩ := hβα₂
  have hβ₁ : β₁ = MulAut.conj g₁ * α₁ := by rw [hg₁, mul_assoc, inv_mul_cancel, mul_one]
  have hβ₂ : β₂ = MulAut.conj g₂ * α₂ := by rw [hg₂, mul_assoc, inv_mul_cancel, mul_one]
  set z : G := (g₁ : G) * g₂ * y with hzdef
  have hz₁ : ∀ a : X₁, ((β₁ a : X₁) : G) = z * a * z⁻¹ := by
    intro a
    rw [hβ₁, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hα₁, hzdef]
    have hmem : y * (a : G) * y⁻¹ ∈ X₁ := (Subgroup.mem_normalizer_iff.1 hy₁ a).1 a.2
    have hb : y * (a : G) * y⁻¹ * g₂ = g₂ * (y * a * y⁻¹) := hc _ hmem g₂ g₂.2
    calc (g₁ : G) * (y * a * y⁻¹) * (g₁ : G)⁻¹
        = g₁ * (y * a * y⁻¹ * g₂) * (g₂ : G)⁻¹ * (g₁ : G)⁻¹ := by group
      _ = (g₁ : G) * g₂ * y * a * ((g₁ : G) * g₂ * y)⁻¹ := by rw [hb]; group
  have hz₂ : ∀ a : X₂, ((β₂ a : X₂) : G) = z * a * z⁻¹ := by
    intro a
    rw [hβ₂, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hα₂, hzdef]
    have hmem : (g₂ : G) * (y * a * y⁻¹) * (g₂ : G)⁻¹ ∈ X₂ := by
      have h0 : y * (a : G) * y⁻¹ ∈ X₂ := (Subgroup.mem_normalizer_iff.1 hy₂ a).1 a.2
      exact X₂.mul_mem (X₂.mul_mem g₂.2 h0) (X₂.inv_mem g₂.2)
    have hb : (g₁ : G) * ((g₂ : G) * (y * a * y⁻¹) * (g₂ : G)⁻¹) =
        ((g₂ : G) * (y * a * y⁻¹) * (g₂ : G)⁻¹) * g₁ := hc g₁ g₁.2 _ hmem
    calc (g₂ : G) * (y * a * y⁻¹) * (g₂ : G)⁻¹
        = ((g₁ : G) * ((g₂ : G) * (y * a * y⁻¹) * (g₂ : G)⁻¹)) * (g₁ : G)⁻¹ := by
          rw [hb]; group
      _ = (g₁ : G) * g₂ * y * a * ((g₁ : G) * g₂ * y)⁻¹ := by group
  have hg : (g₁ : G) * g₂ ∈ X₁ ⊔ X₂ := Subgroup.mul_mem_sup g₁.2 g₂.2
  have hzr : z ^ r ∈ X₁ ⊔ X₂ := by
    have h1 := CFSG.LocalAnalysis.RankThreeTheoremC.mul_pow_mul_inv_pow_mem hg hyS r
    have h2 : z ^ r = (((g₁ : G) * g₂ * y) ^ r * (y ^ r)⁻¹) * y ^ r := by
      rw [inv_mul_cancel_right, hzdef]
    rw [h2]
    exact (X₁ ⊔ X₂).mul_mem h1 hyr
  have hzr1 : z ^ r = 1 := by
    obtain ⟨m₁, hm₁, m₂, hm₂, hm⟩ := (CFSG.mem_sup_of_commute hc').1 hzr
    have hm₁1 : m₁ = 1 := by
      have hcent : (⟨m₁, hm₁⟩ : X₁) ∈ Subgroup.center X₁ := by
        rw [Subgroup.mem_center_iff]
        intro b
        apply Subtype.ext
        have h1 := UC22.uc22p22qz_pow_apply hz₁ r b
        rw [hβ₁r, MulAut.one_apply, ← hm] at h1
        have hb : (b : G) * m₂ = m₂ * b := hc b b.2 m₂ hm₂
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        calc (b : G) * m₁ = m₁ * m₂ * b * (m₁ * m₂)⁻¹ * m₁ := by rw [← h1]
          _ = m₁ * (m₂ * b) * m₂⁻¹ := by group
          _ = m₁ * b := by rw [← hb]; group
      rw [hZ₁, Subgroup.mem_bot] at hcent
      exact congrArg Subtype.val hcent
    have hm₂1 : m₂ = 1 := by
      have hcent : (⟨m₂, hm₂⟩ : X₂) ∈ Subgroup.center X₂ := by
        rw [Subgroup.mem_center_iff]
        intro b
        apply Subtype.ext
        have h1 := UC22.uc22p22qz_pow_apply hz₂ r b
        rw [hβ₂r, MulAut.one_apply, ← hm, hm₁1, one_mul] at h1
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        calc (b : G) * m₂ = m₂ * b * m₂⁻¹ * m₂ := by rw [← h1]
          _ = m₂ * b := by group
      rw [hZ₂, Subgroup.mem_bot] at hcent
      exact congrArg Subtype.val hcent
    rw [← hm, hm₁1, hm₂1, one_mul]
  have hzS : z ∉ X₁ ⊔ X₂ := by
    intro hz'
    apply hyX
    have : y = ((g₁ : G) * g₂)⁻¹ * z := by rw [hzdef]; group
    rw [this]
    exact (X₁ ⊔ X₂).mul_mem ((X₁ ⊔ X₂).inv_mem hg) hz'
  have hzord : orderOf z = r := by
    refine orderOf_eq_prime hzr1 ?_
    intro h1
    exact hzS (h1 ▸ (X₁ ⊔ X₂).one_mem)
  set F₁ : Subgroup G := E₁.map X₁.subtype with hF₁
  set F₂ : Subgroup G := E₂.map X₂.subtype with hF₂
  have hF₁X : F₁ ≤ X₁ := by rintro _ ⟨a, -, rfl⟩; exact a.2
  have hF₂X : F₂ ≤ X₂ := by rintro _ ⟨a, -, rfl⟩; exact a.2
  have hFc : ∀ a ∈ F₁, ∀ b ∈ F₂, a * b = b * a := fun a ha b hb => hc a (hF₁X ha) b (hF₂X hb)
  have hF : IsElemAbelian r (F₁ ⊔ F₂) :=
    (hE₁.map X₁.subtype).sup_of_commute (hE₂.map X₂.subtype) hFc
  have hFinf : F₁ ⊓ F₂ = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf hF₁X hF₂X
  have hFcard : Nat.card (F₁ ⊔ F₂ : Subgroup G) = r ^ 2 := by
    rw [CFSG.card_sup_eq_mul_of_commute F₁ F₂ (fun a ha b hb => hFc a ha b hb) hFinf,
      hF₁, hF₂, Subgroup.card_map_of_injective X₁.subtype_injective,
      Subgroup.card_map_of_injective X₂.subtype_injective, hE₁card, hE₂card]
    ring
  have hcomm : ∀ e ∈ F₁ ⊔ F₂, Commute e z := by
    have hle : F₁ ⊔ F₂ ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := hz₁ a
        rw [hE₁fix a ha] at h1
        change (a : G) * z = z * a
        calc (a : G) * z = z * a * z⁻¹ * z := by rw [← h1]
          _ = z * a := by group
      · rintro _ ⟨a, ha, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := hz₂ a
        rw [hE₂fix a ha] at h1
        change (a : G) * z = z * a
        calc (a : G) * z = z * a * z⁻¹ * z := by rw [← h1]
          _ = z * a := by group
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle he)
  have hzF : z ∉ F₁ ⊔ F₂ := fun h => hzS (sup_le_sup hF₁X hF₂X h)
  obtain ⟨hEab, hEcard⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hF hzord hcomm hzF
  refine ⟨F₁ ⊔ F₂ ⊔ Subgroup.zpowers z, hEab, ?_⟩
  rw [hEcard, hFcard]
  ring

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
