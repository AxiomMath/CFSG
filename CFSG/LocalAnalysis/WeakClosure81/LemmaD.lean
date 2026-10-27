module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.Hyperplane

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.Coprime CFSG.SignalizerFunctorTheorem.Glauberman.Steps678
open scoped commutatorElement

namespace CFSG.LocalAnalysis.WeakClosure81

variable {E : Type*} [Group E]

theorem conj_eq_inv_of_mem_zpowers' {t w : E} (h : t * w * t⁻¹ = w⁻¹) {y : E}
    (hy : y ∈ Subgroup.zpowers w) : t * y * t⁻¹ = y⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h, inv_zpow']
  rw [zpow_neg]

theorem exists_prime_order_of_conj_eq_inv [Finite E] {a : E} {Y : Subgroup E}
    (ha : a * a = 1) (hN : a ∈ Subgroup.normalizer (Y : Set E))
    (hnot : a ∉ Subgroup.centralizer (Y : Set E)) :
    ∃ p, p.Prime ∧ ∃ y ∈ Y, orderOf y = p ∧ a * y * a⁻¹ = y⁻¹ := by
  rw [Subgroup.mem_centralizer_iff] at hnot
  push Not at hnot
  obtain ⟨y, hyY, hya⟩ := hnot
  have haY : a * y * a⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hN y).mp hyY
  have hyi : y⁻¹ ∈ Y := Y.inv_mem hyY
  have hya' : a * y * a⁻¹ ≠ y := by
    intro h
    apply hya
    have := congrArg (· * a) h
    simpa [mul_assoc] using this.symm
  set w : E := y⁻¹ * (a * y * a⁻¹) with hwdef
  have hwY : w ∈ Y := Y.mul_mem hyi haY
  have hw1 : w ≠ 1 := by
    intro hw
    apply hya'
    have h1 : y * w = a * y * a⁻¹ := by
      rw [hwdef, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [hw, mul_one] at h1
    exact h1.symm
  have hwinv : a * w * a⁻¹ = w⁻¹ := by
    rw [hwdef]
    change MulAut.conj a (y⁻¹ * MulAut.conj a y) = (y⁻¹ * MulAut.conj a y)⁻¹
    rw [map_mul, map_inv]
    have h2 : MulAut.conj a (MulAut.conj a y) = y := by
      have hmul : MulAut.conj a * MulAut.conj a = 1 := by
        rw [← map_mul, ha, map_one]
      have := congrArg (fun f : MulAut E => f y) hmul
      simpa using this
    rw [h2]
    group
  have hw_ord : orderOf w ≠ 1 := fun h => hw1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hw_ord
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : p ∣ Nat.card (Subgroup.zpowers w) := by
    rwa [Nat.card_zpowers]
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers w) p hcard
  refine ⟨p, hp, (z : E), (Subgroup.zpowers_le.mpr hwY) z.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]; exact hz
  · exact conj_eq_inv_of_mem_zpowers' hwinv z.2

theorem index_le_two_of_lt_four {A H : Subgroup E} [Finite E] (hA : IsElemAbelian 2 A)
    (h : (H.subgroupOf A).index < 4) : (H.subgroupOf A).index ≤ 2 := by
  have hA2 : IsPGroup 2 ↥A :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 A hA
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hA2.index (H.subgroupOf A)
  rw [hn] at h ⊢
  have hn1 : n ≤ 1 := by
    by_contra hcon
    have h2 : 2 ≤ n := by omega
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
    omega
  interval_cases n <;> norm_num

theorem index_inf_eq_four_of_index_two {A H K : Subgroup E} [Finite E]
    (hHA : H ≤ A) (hKA : K ≤ A)
    (hHi : (H.subgroupOf A).index = 2) (hKi : (K.subgroupOf A).index = 2) (hne : H ≠ K) :
    ((H ⊓ K).subgroupOf A).index = 4 := by
  have hsub : (H ⊓ K).subgroupOf A = H.subgroupOf A ⊓ K.subgroupOf A :=
    Subgroup.comap_inf H K A.subtype
  rw [hsub]
  set hH : Subgroup A := H.subgroupOf A with hhH
  set hK : Subgroup A := K.subgroupOf A with hhK
  have hidx : (hH ⊓ hK).index = hH.relIndex hK * hK.index := Subgroup.index_inf
  rw [hKi] at hidx
  have hle4 : (hH ⊓ hK).index ≤ 4 := by
    calc (hH ⊓ hK).index ≤ hH.index * hK.index := Subgroup.index_inf_le
      _ = 4 := by rw [hHi, hKi]
  have hrel2 : 2 ≤ hH.relIndex hK := by
    have hne0 : hH.relIndex hK ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hidx
      exact (Subgroup.index_ne_zero_of_finite (H := hH ⊓ hK)) hidx
    have hne1 : hH.relIndex hK ≠ 1 := by
      intro h1
      have hle : hK ≤ hH := Subgroup.relIndex_eq_one.mp h1
      have hcH : Nat.card hH * 2 = Nat.card A := by
        rw [← hHi, Subgroup.card_mul_index]
      have hcK : Nat.card hK * 2 = Nat.card A := by
        rw [← hKi, Subgroup.card_mul_index]
      have hcard : Nat.card hH = Nat.card hK := by omega
      have heq : hH = hK := (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm
      exact hne (by
        have := Subgroup.subgroupOf_inj.mp heq
        rwa [inf_eq_left.mpr hHA, inf_eq_left.mpr hKA] at this)
    omega
  have hrel_eq : hH.relIndex hK = 2 := by
    rw [hidx] at hle4
    omega
  calc (hH ⊓ hK).index = hH.relIndex hK * 2 := hidx
    _ = 4 := by rw [hrel_eq]

theorem conj_mem_centralizer_of_comm {A B : Subgroup E}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {a x : E} (ha : a ∈ A) (hx : x ∈ Subgroup.centralizer (B : Set E)) :
    a * x * a⁻¹ ∈ Subgroup.centralizer (B : Set E) := by
  have ha' : a⁻¹ ∈ A := A.inv_mem ha
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro b hb
  have h1 : b * (a * x * a⁻¹) = (b * a) * x * a⁻¹ := by group
  have h2 : (b * a) * x * a⁻¹ = (a * b) * x * a⁻¹ := by rw [← hcomm a ha b hb]
  have h3 : (a * b) * x * a⁻¹ = a * (b * x) * a⁻¹ := by group
  have h4 : a * (b * x) * a⁻¹ = a * (x * b) * a⁻¹ := by rw [hx b hb]
  have h5 : a * (x * b) * a⁻¹ = a * x * (b * a⁻¹) := by group
  have h6 : a * x * (b * a⁻¹) = a * x * (a⁻¹ * b) := by rw [← hcomm a⁻¹ ha' b hb]
  have h7 : a * x * (a⁻¹ * b) = (a * x * a⁻¹) * b := by group
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))

theorem le_normalizer_centralizer_of_comm {A B : Subgroup E}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ≤ Subgroup.normalizer (Subgroup.centralizer (B : Set E) : Set E) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => conj_mem_centralizer_of_comm hcomm ha hx,
    fun hx => by
      have h := conj_mem_centralizer_of_comm hcomm (A.inv_mem ha) hx
      rwa [show a⁻¹ * (a * x * a⁻¹) * (a⁻¹)⁻¹ = x by group] at h⟩

theorem centralizer_zpowers_sup (y₁ y₂ : E) :
    Subgroup.centralizer ((Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ : Subgroup E) : Set E) =
      Subgroup.centralizer ({y₁} : Set E) ⊓ Subgroup.centralizer ({y₂} : Set E) := by
  apply le_antisymm
  · refine le_inf (Subgroup.centralizer_le ?_) (Subgroup.centralizer_le ?_)
    · rintro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y₁)
    · rintro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y₂)
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro z hz
    have hy1 : y₁ ∈ Subgroup.centralizer ({x} : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hx.1 y₁ rfl).symm
    have hy2 : y₂ ∈ Subgroup.centralizer ({x} : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hx.2 y₂ rfl).symm
    have hle : Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ ≤
        Subgroup.centralizer ({x} : Set E) :=
      sup_le (Subgroup.zpowers_le.mpr hy1) (Subgroup.zpowers_le.mpr hy2)
    exact ((Subgroup.mem_centralizer_iff.mp (hle hz)) x rfl).symm

theorem eq_or_eq_of_le_of_index_two {A H K : Subgroup E} [Finite E]
    (hHA : H ≤ A) (hHK : H ≤ K) (hKA : K ≤ A)
    (hHi : (H.subgroupOf A).index = 2) : K = H ∨ K = A := by
  have hle : H.subgroupOf A ≤ K.subgroupOf A := Subgroup.comap_mono hHK
  have hdvd : (K.subgroupOf A).index ∣ (H.subgroupOf A).index := Subgroup.index_dvd_of_le hle
  rw [hHi] at hdvd
  have hpos : 0 < (K.subgroupOf A).index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hle2 : (K.subgroupOf A).index ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hr : (K.subgroupOf A).index = 1 ∨ (K.subgroupOf A).index = 2 := by omega
  rcases hr with h1 | h2
  · right
    have htop : K.subgroupOf A = ⊤ := Subgroup.index_eq_one.mp h1
    exact le_antisymm hKA (Subgroup.subgroupOf_eq_top.mp htop)
  · left
    have hcard : Nat.card (K.subgroupOf A) = Nat.card (H.subgroupOf A) := by
      have hc1 := (K.subgroupOf A).card_mul_index
      have hc2 := (H.subgroupOf A).card_mul_index
      rw [h2] at hc1
      rw [hHi] at hc2
      omega
    have heq : K.subgroupOf A = H.subgroupOf A :=
      (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm
    have := Subgroup.subgroupOf_inj.mp heq
    rwa [inf_eq_left.mpr hKA, inf_eq_left.mpr hHA] at this

theorem le_centralizer_iSup {A : Subgroup E} {ι : Type*} {f : ι → Subgroup E}
    (h : ∀ i, A ≤ Subgroup.centralizer (f i : Set E)) :
    A ≤ Subgroup.centralizer ((⨆ i, f i : Subgroup E) : Set E) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : x ∈ Subgroup.centralizer ({a} : Set E) := by
    have hle : (⨆ i, f i) ≤ Subgroup.centralizer ({a} : Set E) := by
      refine iSup_le fun i => ?_
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact ((Subgroup.mem_centralizer_iff.mp (h i ha)) y hy).symm
    exact hle hx
  rw [Subgroup.mem_centralizer_iff] at hx'
  exact (hx' a rfl).symm

theorem mul_inv_mem_of_not_mem_of_index_two {A B : Subgroup E} [Finite E]
    (hBi : (B.subgroupOf A).index = 2) {a c : E}
    (ha : a ∈ A) (hc : c ∈ A) (han : a ∉ B) (hcn : c ∉ B) : c * a⁻¹ ∈ B := by
  have hrel : B.relIndex A = 2 := hBi
  obtain ⟨r, -, hr⟩ := Subgroup.relIndex_eq_two_iff.mp hrel
  have har : a * r ∈ B := by
    have h : (a * r ∈ B) ↔ ¬ (a ∈ B) := by
      have := hr a ha
      rwa [xor_iff_iff_not] at this
    exact h.mpr han
  have hcr : c * r ∈ B := by
    have h : (c * r ∈ B) ↔ ¬ (c ∈ B) := by
      have := hr c hc
      rwa [xor_iff_iff_not] at this
    exact h.mpr hcn
  have hce : c * a⁻¹ = (c * r) * (a * r)⁻¹ := by group
  rw [hce]
  exact B.mul_mem hcr (B.inv_mem har)

theorem odd_dvd_two {n : ℕ} (hodd : Odd n) (h : n ∣ 2) : n = 1 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
  · exact h1
  · rw [h2] at hodd; obtain ⟨k, hk⟩ := hodd; omega

theorem not_mem_centralizer_singleton_of_conj_eq_inv {g y : E}
    (hinv : g * y * g⁻¹ = y⁻¹) (hodd : Odd (orderOf y)) (hyne : y ≠ 1) :
    g ∉ Subgroup.centralizer ({y} : Set E) := by
  intro hc
  have hcomm : y * g = g * y := (Subgroup.mem_centralizer_iff.mp hc) y rfl
  have hfix : g * y * g⁻¹ = y := by rw [← hcomm]; group
  rw [hinv] at hfix
  have hy_eq : y = y⁻¹ := hfix.symm
  have h2 : y ^ 2 = 1 := by
    rw [pow_two]; nth_rewrite 2 [hy_eq]; rw [mul_inv_cancel]
  exact hyne (orderOf_eq_one_iff.mp (odd_dvd_two hodd (orderOf_dvd_of_pow_eq_one h2)))

theorem zpow_mem_of_two_mul_mem {K : Subgroup E} {y : E} {m : ℤ}
    (hodd : Odd (orderOf y)) (h : y ^ (2 * m) ∈ K) : y ^ m ∈ K := by
  obtain ⟨k, hk⟩ := hodd
  have hj : ((orderOf y + 1) / 2 : ℕ) = k + 1 := by omega
  have heq : y ^ m = (y ^ (2 * m)) ^ ((k + 1 : ℕ) : ℤ) := by
    rw [← zpow_mul]
    have hz : (2 * m) * ((k + 1 : ℕ) : ℤ) = m * (orderOf y : ℤ) + m := by
      rw [hk]; push_cast; ring
    have hz2 : y ^ (m * (orderOf y : ℤ)) = 1 := by
      rw [show m * (orderOf y : ℤ) = ((orderOf y : ℕ) : ℤ) * m by ring, zpow_mul,
        show y ^ ((orderOf y : ℕ) : ℤ) = 1 by rw [zpow_natCast, pow_orderOf_eq_one], one_zpow]
    rw [hz, zpow_add, hz2, one_mul]
  rw [heq]
  exact K.zpow_mem h ((k + 1 : ℕ) : ℤ)

theorem mul_mem_of_not_mem_of_index_two {A H : Subgroup E} [Finite E]
    (hHi : (H.subgroupOf A).index = 2) {a c : E} (hc2 : c * c = 1)
    (ha : a ∈ A) (hc : c ∈ A) (han : a ∉ H) (hcn : c ∉ H) : a * c ∈ H := by
  have h := mul_inv_mem_of_not_mem_of_index_two hHi hc ha hcn han
  rwa [inv_eq_of_mul_eq_one_right hc2] at h

theorem commute_of_minimal_invariant {A X₀ : Subgroup E} [Finite E] (hA : IsElemAbelian 2 A)
    (hAX₀ : A ≤ Subgroup.normalizer (X₀ : Set E)) (hodd : Odd (Nat.card X₀)) (hne : X₀ ≠ ⊥)
    {y₁ y₂ a₁ a₂ : E} (hX₀ : X₀ = Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂)
    (hnorm₁ : A ≤ Subgroup.normalizer (Subgroup.zpowers y₁ : Set E))
    (hnorm₂ : A ≤ Subgroup.normalizer (Subgroup.zpowers y₂ : Set E))
    (hy₁ : (orderOf y₁).Prime) (hy₂ : (orderOf y₂).Prime)
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (h11 : a₁ * y₁ * a₁⁻¹ = y₁⁻¹) (h12 : a₁ * y₂ * a₁⁻¹ = y₂)
    (h21 : a₂ * y₁ * a₂⁻¹ = y₁) (h22 : a₂ * y₂ * a₂⁻¹ = y₂⁻¹)
    (hmin : ∀ W : Subgroup E, W < X₀ → A ≤ Subgroup.normalizer (W : Set E) →
      ((A ⊓ Subgroup.centralizer (W : Set E)).subgroupOf A).index ≤ 2) :
    y₁ * y₂ = y₂ * y₁ := by
  classical
  haveI hAcomm : IsMulCommutative ↥A := hA.1
  have hcommA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) (⟨b, hb⟩ : A))
  have hy₁X₀ : y₁ ∈ X₀ := by rw [hX₀]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y₁)
  have hy₂X₀ : y₂ ∈ X₀ := by rw [hX₀]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y₂)
  have hy₁odd : Odd (orderOf y₁) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hy₁X₀)
  have hy₂odd : Odd (orderOf y₂) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hy₂X₀)
  have hy₁ne : y₁ ≠ 1 := fun h => hy₁.ne_one (h ▸ orderOf_one)
  have hy₂ne : y₂ ≠ 1 := fun h => hy₂.ne_one (h ▸ orderOf_one)
  have ha₁sq : a₁ * a₁ = 1 := by rw [← pow_two]; exact hA.2 a₁ ha₁
  have ha₂sq : a₂ * a₂ = 1 := by rw [← pow_two]; exact hA.2 a₂ ha₂
  by_contra hnecomm
  set K : Subgroup E := ⁅X₀, X₀⁆ with hKdef
  have hKle : K ≤ X₀ := by
    rw [hKdef]
    refine Subgroup.commutator_le.mpr ?_
    intro g₁ hg₁ g₂ hg₂
    rw [commutatorElement_def]
    exact X₀.mul_mem (X₀.mul_mem (X₀.mul_mem hg₁ hg₂) (X₀.inv_mem hg₁)) (X₀.inv_mem hg₂)
  have hKlt : K < X₀ := by
    haveI : Group.IsSolvable ↥X₀ := CFSG.FeitThompson.isSolvable_of_odd_natCard (G := ↥X₀) hodd
    have hnt : Nontrivial ↥X₀ :=
      Finite.one_lt_card_iff_nontrivial.mp ((Subgroup.one_lt_card_iff_ne_bot X₀).mpr hne)
    have hne_top : (⊤ : Subgroup ↥X₀) ≠ ⊥ := top_ne_bot
    have h := Group.IsSolvable.commutator_lt_of_ne_bot (G := ↥X₀) (H := ⊤) hne_top
    have hmap : (⁅(⊤ : Subgroup ↥X₀), (⊤ : Subgroup ↥X₀)⁆ : Subgroup ↥X₀).map X₀.subtype <
        (⊤ : Subgroup ↥X₀).map X₀.subtype :=
      (Subgroup.map_subtype_lt_map_subtype).mpr h
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    rw [hKdef]; exact hmap
  have hKinv : A ≤ Subgroup.normalizer (K : Set E) := by
    intro a ha
    have hnorm : X₀.map (MulAut.conj a).toMonoidHom = X₀ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAX₀ ha)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change K.map (MulAut.conj a).toMonoidHom = K
    rw [hKdef, Subgroup.map_commutator, hnorm]
  have hKX : X₀ ≤ Subgroup.normalizer (K : Set E) := by
    intro x hx
    have hnorm : X₀.map (MulAut.conj x).toMonoidHom = X₀ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hx)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change K.map (MulAut.conj x).toMonoidHom = K
    rw [hKdef, Subgroup.map_commutator, hnorm]
  have hKidx : ((A ⊓ Subgroup.centralizer (K : Set E)).subgroupOf A).index ≤ 2 :=
    hmin K hKlt hKinv
  set c : E := ⁅y₁, y₂⁆ with hcdef
  have hcK : c ∈ K := by
    rw [hKdef, hcdef]
    exact Subgroup.commutator_mem_commutator hy₁X₀ hy₂X₀
  have hcne1 : c ≠ 1 := by
    rw [hcdef, Ne, commutatorElement_eq_one_iff_mul_comm]; exact hnecomm
  have hid₁ : a₁ * c * a₁⁻¹ = y₁⁻¹ * c⁻¹ * y₁ := by
    have h1 : a₁ * c * a₁⁻¹ = ⁅a₁ * y₁ * a₁⁻¹, a₁ * y₂ * a₁⁻¹⁆ := by
      rw [hcdef, ← MulAut.conj_apply, map_commutatorElement]; rfl
    rw [h1, h11, h12, commutatorElement_inv_left, ← commutatorElement_inv, hcdef]
  have hid₂ : a₂ * c * a₂⁻¹ = y₂⁻¹ * c⁻¹ * y₂ := by
    have h1 : a₂ * c * a₂⁻¹ = ⁅a₂ * y₁ * a₂⁻¹, a₂ * y₂ * a₂⁻¹⁆ := by
      rw [hcdef, ← MulAut.conj_apply, map_commutatorElement]; rfl
    rw [h1, h21, h22, commutatorElement_inv_right, ← commutatorElement_inv, hcdef]
  have h_inv_eq_one : ∀ g : E, g * c * g⁻¹ = c⁻¹ → Odd (orderOf g) → c = 1 := by
    intro g hg hoddg
    have hg2 : g * g * c * (g * g)⁻¹ = c := by
      calc g * g * c * (g * g)⁻¹ = g * (g * c * g⁻¹) * g⁻¹ := by group
        _ = g * c⁻¹ * g⁻¹ := by rw [hg]
        _ = (g * c * g⁻¹)⁻¹ := by group
        _ = (c⁻¹)⁻¹ := by rw [hg]
        _ = c := by group
    have hfix2 : (MulAut.conj g * MulAut.conj g) c = c := by
      rw [← map_mul, MulAut.conj_apply]; exact hg2
    have hfix2' : ((MulAut.conj g) ^ 2) c = c := by rw [sq]; exact hfix2
    have hφ : (MulAut.conj g) ^ (orderOf g) = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    obtain ⟨k, hk⟩ := hoddg
    have hfixk : ∀ j : ℕ, (((MulAut.conj g) ^ 2) ^ j) c = c := by
      intro j; induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, MulAut.mul_apply, hfix2', ih]
    have hgc : MulAut.conj g c = c := by
      have heq : MulAut.conj g = ((MulAut.conj g) ^ 2) ^ (k + 1) := by
        rw [← pow_mul]
        rw [show 2 * (k + 1) = orderOf g + 1 by rw [hk]; ring, pow_succ, hφ, one_mul]
      rw [heq]; exact hfixk (k + 1)
    rw [MulAut.conj_apply] at hgc
    rw [hgc] at hg
    have hcc : c = c⁻¹ := hg
    have h2 : c ^ 2 = 1 := by
      rw [pow_two]; nth_rewrite 2 [hcc]; rw [mul_inv_cancel]
    have hcX₀ : c ∈ X₀ := hKle hcK
    have hcodd : Odd (orderOf c) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hcX₀)
    exact orderOf_eq_one_iff.mp (odd_dvd_two hcodd (orderOf_dvd_of_pow_eq_one h2))
  have hprod : ∀ W : Subgroup E, K ≤ W → W ≤ X₀ → A ≤ Subgroup.normalizer (W : Set E) →
      a₁ ∉ Subgroup.centralizer (W : Set E) → a₂ ∉ Subgroup.centralizer (W : Set E) →
      a₁ * a₂ ∉ Subgroup.centralizer (W : Set E) →
      ¬ ((A ⊓ Subgroup.centralizer (W : Set E)).subgroupOf A).index ≤ 2 := by
    intro W hKW hWX hWinv ha₁n ha₂n ha₁a₂n hidx
    have hne1 : ((A ⊓ Subgroup.centralizer (W : Set E)).subgroupOf A).index ≠ 1 := by
      intro h1
      have htop : (A ⊓ Subgroup.centralizer (W : Set E)).subgroupOf A = ⊤ :=
        Subgroup.index_eq_one.mp h1
      have hAle : A ≤ A ⊓ Subgroup.centralizer (W : Set E) := Subgroup.subgroupOf_eq_top.mp htop
      exact ha₁n (hAle ha₁).2
    have hidx2 : ((A ⊓ Subgroup.centralizer (W : Set E)).subgroupOf A).index = 2 := by
      have hpos : 0 < ((A ⊓ Subgroup.centralizer (W : Set E)).subgroupOf A).index :=
        Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
      omega
    have ha₁H : a₁ ∉ A ⊓ Subgroup.centralizer (W : Set E) := fun h => ha₁n h.2
    have ha₂H : a₂ ∉ A ⊓ Subgroup.centralizer (W : Set E) := fun h => ha₂n h.2
    exact ha₁a₂n (mul_mem_of_not_mem_of_index_two hidx2 ha₂sq ha₁ ha₂ ha₁H ha₂H).2
  by_cases ha₁C : a₁ ∈ Subgroup.centralizer (K : Set E)
  · have hc_fix : a₁ * c * a₁⁻¹ = c := by
      have h := (Subgroup.mem_centralizer_iff.mp ha₁C) c hcK
      rw [← h]; group
    rw [hc_fix] at hid₁
    have hy₁inv : y₁ * c * y₁⁻¹ = c⁻¹ := by nth_rewrite 1 [hid₁]; group
    exact hcne1 (h_inv_eq_one y₁ hy₁inv hy₁odd)
  · by_cases ha₂C : a₂ ∈ Subgroup.centralizer (K : Set E)
    · have hc_fix : a₂ * c * a₂⁻¹ = c := by
        have h := (Subgroup.mem_centralizer_iff.mp ha₂C) c hcK
        rw [← h]; group
      rw [hc_fix] at hid₂
      have hy₂inv : y₂ * c * y₂⁻¹ = c⁻¹ := by nth_rewrite 1 [hid₂]; group
      exact hcne1 (h_inv_eq_one y₂ hy₂inv hy₂odd)
    · have ha₁a₂_inv₁ : (a₁ * a₂) * y₁ * (a₁ * a₂)⁻¹ = y₁⁻¹ := by
        have h1 : (a₁ * a₂) * y₁ * (a₁ * a₂)⁻¹ = a₁ * (a₂ * y₁ * a₂⁻¹) * a₁⁻¹ := by group
        rw [h1, h21, h11]
      have ha₁a₂_inv₂ : (a₁ * a₂) * y₂ * (a₁ * a₂)⁻¹ = y₂⁻¹ := by
        have h1 : (a₁ * a₂) * y₂ * (a₁ * a₂)⁻¹ = a₁ * (a₂ * y₂ * a₂⁻¹) * a₁⁻¹ := by group
        rw [h1, h22]
        rw [show a₁ * y₂⁻¹ * a₁⁻¹ = (a₁ * y₂ * a₁⁻¹)⁻¹ by group, h12]
      have hW₁eq : K ⊔ Subgroup.zpowers y₁ = X₀ := by
        have hle : K ⊔ Subgroup.zpowers y₁ ≤ X₀ := sup_le hKle (Subgroup.zpowers_le.mpr hy₁X₀)
        have hinv : A ≤ Subgroup.normalizer ((K ⊔ Subgroup.zpowers y₁ : Subgroup E) : Set E) :=
          (le_inf hKinv hnorm₁).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
        have hy₁W : y₁ ∈ (K ⊔ Subgroup.zpowers y₁ : Subgroup E) :=
          Subgroup.mem_sup_right (Subgroup.mem_zpowers y₁)
        have hsub : ({y₁} : Set E) ⊆ (K ⊔ Subgroup.zpowers y₁ : Subgroup E) := by
          intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hy₁W
        have ha₁n : a₁ ∉ Subgroup.centralizer ((K ⊔ Subgroup.zpowers y₁ : Subgroup E) : Set E) :=
          fun hc => not_mem_centralizer_singleton_of_conj_eq_inv h11 hy₁odd hy₁ne
            (Subgroup.centralizer_le hsub hc)
        have ha₂n : a₂ ∉ Subgroup.centralizer ((K ⊔ Subgroup.zpowers y₁ : Subgroup E) : Set E) :=
          fun hc => ha₂C (Subgroup.centralizer_le
            (by intro z hz; exact Subgroup.mem_sup_left hz) hc)
        have ha₁a₂n : a₁ * a₂ ∉
            Subgroup.centralizer ((K ⊔ Subgroup.zpowers y₁ : Subgroup E) : Set E) :=
          fun hc => not_mem_centralizer_singleton_of_conj_eq_inv ha₁a₂_inv₁ hy₁odd hy₁ne
            (Subgroup.centralizer_le hsub hc)
        by_contra hne'
        exact hprod _ le_sup_left hle hinv ha₁n ha₂n ha₁a₂n
          (hmin _ (lt_of_le_of_ne hle hne') hinv)
      have hW₂eq : K ⊔ Subgroup.zpowers y₂ = X₀ := by
        have hle : K ⊔ Subgroup.zpowers y₂ ≤ X₀ := sup_le hKle (Subgroup.zpowers_le.mpr hy₂X₀)
        have hinv : A ≤ Subgroup.normalizer ((K ⊔ Subgroup.zpowers y₂ : Subgroup E) : Set E) :=
          (le_inf hKinv hnorm₂).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
        have hy₂W : y₂ ∈ (K ⊔ Subgroup.zpowers y₂ : Subgroup E) :=
          Subgroup.mem_sup_right (Subgroup.mem_zpowers y₂)
        have hsub : ({y₂} : Set E) ⊆ (K ⊔ Subgroup.zpowers y₂ : Subgroup E) := by
          intro z hz; rw [Set.mem_singleton_iff] at hz; rw [hz]; exact hy₂W
        have ha₂n : a₂ ∉ Subgroup.centralizer ((K ⊔ Subgroup.zpowers y₂ : Subgroup E) : Set E) :=
          fun hc => not_mem_centralizer_singleton_of_conj_eq_inv h22 hy₂odd hy₂ne
            (Subgroup.centralizer_le hsub hc)
        have ha₁n : a₁ ∉ Subgroup.centralizer ((K ⊔ Subgroup.zpowers y₂ : Subgroup E) : Set E) :=
          fun hc => ha₁C (Subgroup.centralizer_le
            (by intro z hz; exact Subgroup.mem_sup_left hz) hc)
        have ha₁a₂n : a₁ * a₂ ∉
            Subgroup.centralizer ((K ⊔ Subgroup.zpowers y₂ : Subgroup E) : Set E) :=
          fun hc => not_mem_centralizer_singleton_of_conj_eq_inv ha₁a₂_inv₂ hy₂odd hy₂ne
            (Subgroup.centralizer_le hsub hc)
        by_contra hne'
        exact hprod _ le_sup_left hle hinv ha₁n ha₂n ha₁a₂n
          (hmin _ (lt_of_le_of_ne hle hne') hinv)
      have hy₂mem : y₂ ∈ (K ⊔ Subgroup.zpowers y₁ : Subgroup E) := by rw [hW₁eq]; exact hy₂X₀
      have hy₂mem' : y₂ ∈ ((K ⊔ Subgroup.zpowers y₁ : Subgroup E) : Set E) := hy₂mem
      rw [Subgroup.coe_mul_of_right_le_normalizer_left K (Subgroup.zpowers y₁)
        (Subgroup.zpowers_le.mpr (hKX hy₁X₀))] at hy₂mem'
      rw [Set.mem_mul] at hy₂mem'
      obtain ⟨k, hkK, z, hz, hkz⟩ := hy₂mem'
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hy₂eq : y₂ = k * y₁ ^ m := by rw [← hkz, hm]
      have hconj : y₂ = (a₁ * k * a₁⁻¹) * y₁ ^ (-m) := by
        have h1 : a₁ * y₂ * a₁⁻¹ = (a₁ * k * a₁⁻¹) * (y₁⁻¹) ^ m := by
          rw [hy₂eq]
          calc a₁ * (k * y₁ ^ m) * a₁⁻¹
              = (a₁ * k * a₁⁻¹) * ((MulAut.conj a₁) (y₁ ^ m)) := by
                simp only [MulAut.conj_apply]; group
            _ = (a₁ * k * a₁⁻¹) * (a₁ * y₁ * a₁⁻¹) ^ m := by
                rw [map_zpow, MulAut.conj_apply]
            _ = (a₁ * k * a₁⁻¹) * (y₁⁻¹) ^ m := by rw [h11]
        rw [h12] at h1
        rw [h1, inv_zpow, ← zpow_neg]
      have hkey : y₁ ^ (2 * m) ∈ K := by
        have h2 : k * y₁ ^ m = (a₁ * k * a₁⁻¹) * y₁ ^ (-m) := by rw [← hy₂eq, hconj]
        have h3 : y₁ ^ (2 * m) = k⁻¹ * (a₁ * k * a₁⁻¹) := by
          have h4 : y₁ ^ m * y₁ ^ m = k⁻¹ * (a₁ * k * a₁⁻¹) := by
            calc y₁ ^ m * y₁ ^ m = (k⁻¹ * (k * y₁ ^ m)) * y₁ ^ m := by group
              _ = (k⁻¹ * ((a₁ * k * a₁⁻¹) * y₁ ^ (-m))) * y₁ ^ m := by rw [h2]
              _ = k⁻¹ * (a₁ * k * a₁⁻¹) := by group
          rwa [← zpow_add, ← two_mul] at h4
        rw [h3]
        exact K.mul_mem (K.inv_mem hkK)
          ((Subgroup.mem_normalizer_iff.mp (hKinv ha₁) k).mp hkK)
      have hy₁mK : y₁ ^ m ∈ K := zpow_mem_of_two_mul_mem hy₁odd hkey
      have hy₂K : y₂ ∈ K := by rw [hy₂eq]; exact K.mul_mem hkK hy₁mK
      have hKeq : (K ⊔ Subgroup.zpowers y₂ : Subgroup E) = K :=
        le_antisymm (sup_le le_rfl (Subgroup.zpowers_le.mpr hy₂K)) le_sup_left
      exact hKlt.ne (by rw [← hW₂eq, hKeq])

structure LemmaDData (A X : Subgroup E) where
  X₀ : Subgroup E
  X₀_le : X₀ ≤ X
  X₀_invariant : A ≤ Subgroup.normalizer (X₀ : Set E)
  D : Subgroup E
  D_eq : D = A ⊓ Subgroup.centralizer (X₀ : Set E)
  D_index : (D.subgroupOf A).index = 4
  a₁ : E
  a₂ : E
  a₁_mem : a₁ ∈ A
  a₂_mem : a₂ ∈ A
  p₁ : ℕ
  p₂ : ℕ
  p₁_prime : p₁.Prime
  p₂_prime : p₂.Prime
  x₁ : E
  x₂ : E
  x₁_mem : x₁ ∈ X₀
  x₂_mem : x₂ ∈ X₀
  x₁_order : orderOf x₁ = p₁
  x₂_order : orderOf x₂ = p₂
  X₀_eq : X₀ = Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂
  x_comm : x₁ * x₂ = x₂ * x₁
  A_eq : A = D ⊔ Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂
  a₁_inverts : a₁ * x₁ * a₁⁻¹ = x₁⁻¹
  a₂_inverts : a₂ * x₂ * a₂⁻¹ = x₂⁻¹
  a₁_centralizes : a₁ * x₂ * a₁⁻¹ = x₂
  a₂_centralizes : a₂ * x₁ * a₂⁻¹ = x₁
  hyperplane : ((D ⊔ Subgroup.zpowers a₂).subgroupOf A).index = 2

theorem lemmaD {A X : Subgroup E} [Finite E] (hA : IsElemAbelian 2 A)
    (hAX : A ≤ Subgroup.normalizer (X : Set E)) (hodd : Odd (Nat.card X))
    (hindex : 4 ≤ ((A ⊓ Subgroup.centralizer (X : Set E)).subgroupOf A).index) :
    Nonempty (LemmaDData A X) := by
  classical
  haveI hAcomm : IsMulCommutative ↥A := hA.1
  have hcommA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) (⟨b, hb⟩ : A))
  have hcardA : 4 ≤ Nat.card A := by
    calc 4 ≤ ((A ⊓ Subgroup.centralizer (X : Set E)).subgroupOf A).index := hindex
      _ ≤ ((A ⊓ Subgroup.centralizer (X : Set E)).subgroupOf A).index *
            Nat.card ((A ⊓ Subgroup.centralizer (X : Set E)).subgroupOf A) :=
            Nat.le_mul_of_pos_right _ Nat.card_pos
      _ = Nat.card A := Subgroup.index_mul_card _
  have hA2le : 2 ^ 2 ≤ Nat.card A := by simpa using hcardA
  let P : ℕ → Prop := fun k => ∃ W : Subgroup E,
    W ≤ X ∧ A ≤ Subgroup.normalizer (W : Set E) ∧
    4 ≤ ((A ⊓ Subgroup.centralizer (W : Set E)).subgroupOf A).index ∧ Nat.card W = k
  have hP : ∃ k, P k := ⟨Nat.card X, X, le_rfl, hAX, hindex, rfl⟩
  obtain ⟨X₀, hX₀X, hX₀inv, hX₀idx, hX₀card⟩ := Nat.find_spec hP
  have hmin : ∀ W : Subgroup E, W ≤ X → A ≤ Subgroup.normalizer (W : Set E) →
      Nat.card W < Nat.card X₀ →
      ¬ 4 ≤ ((A ⊓ Subgroup.centralizer (W : Set E)).subgroupOf A).index := by
    intro W hWX hWi hWc hidx
    have hPm : P (Nat.card W) := ⟨W, hWX, hWi, hidx, rfl⟩
    have hlt : Nat.card W < Nat.find hP := by rwa [← hX₀card]
    exact (Nat.find_min hP hlt) hPm
  have hX₀odd : Odd (Nat.card X₀) := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hX₀X)
  have hX₀ne : X₀ ≠ ⊥ := by
    intro hbot
    have hidx1 : ((A ⊓ Subgroup.centralizer (X₀ : Set E)).subgroupOf A).index = 1 := by
      have h1 : A ⊓ Subgroup.centralizer (X₀ : Set E) = A := by
        rw [hbot]
        refine inf_eq_left.mpr ?_
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy1 : y = 1 := by simpa using hy
        rw [hy1, mul_one, one_mul]
      rw [h1, Subgroup.subgroupOf_eq_top.mpr le_rfl, Subgroup.index_top]
    omega
  have hgen := CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.generation_hyperplanes
    (p := 2) Nat.prime_two hA hA2le hX₀inv (Nat.coprime_two_left.mpr hX₀odd)
  let YB : Subgroup E → Subgroup E := fun B => X₀ ⊓ Subgroup.centralizer (B : Set E)
  let KB : Subgroup E → Subgroup E := fun B => A ⊓ Subgroup.centralizer (YB B : Set E)
  have hhyperIdx : ∀ B (hB : B ∈ hyperplanes 2 A), (B.subgroupOf A).index = 2 :=
    fun B hB => (mem_hyperplanes_iff_index hB.1).mp hB
  have hYB_inv : ∀ B, B ≤ A → A ≤ Subgroup.normalizer (YB B : Set E) := by
    intro B hBA
    have hCB : A ≤ Subgroup.normalizer (Subgroup.centralizer (B : Set E) : Set E) :=
      le_normalizer_centralizer_of_comm (fun a ha b hb => hcommA a ha b (hBA hb))
    exact (le_inf hX₀inv hCB).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hYB_ne : ∀ B (hB : B ∈ hyperplanes 2 A), YB B ≠ X₀ := by
    intro B hB heq
    have hBX : B ≤ Subgroup.centralizer (X₀ : Set E) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyB : y ∈ YB B := by rw [heq]; exact hy
      exact ((Subgroup.mem_centralizer_iff.mp hyB.2) b hb).symm
    have hle : B ≤ A ⊓ Subgroup.centralizer (X₀ : Set E) := le_inf hB.1 hBX
    have hle' : B.subgroupOf A ≤ (A ⊓ Subgroup.centralizer (X₀ : Set E)).subgroupOf A :=
      Subgroup.comap_mono hle
    have hdvd : ((A ⊓ Subgroup.centralizer (X₀ : Set E)).subgroupOf A).index ∣
        (B.subgroupOf A).index := Subgroup.index_dvd_of_le hle'
    rw [hhyperIdx B hB] at hdvd
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd
    omega
  have hK_eq : ∀ B (hB : B ∈ hyperplanes 2 A), KB B = B ∨ KB B = A := by
    intro B hB
    have hBleK : B ≤ KB B := by
      refine le_inf hB.1 ?_
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact ((Subgroup.mem_centralizer_iff.mp hy.2) b hb).symm
    exact eq_or_eq_of_le_of_index_two hB.1 hBleK inf_le_left (hhyperIdx B hB)
  have htwo : ∃ B₁ ∈ hyperplanes 2 A, ∃ B₂ ∈ hyperplanes 2 A,
      B₁ ≠ B₂ ∧ KB B₁ = B₁ ∧ KB B₂ = B₂ := by
    by_contra hcon
    have huniq : ∀ B₁ ∈ hyperplanes 2 A, KB B₁ = B₁ →
        ∀ B₂ ∈ hyperplanes 2 A, KB B₂ = B₂ → B₁ = B₂ := by
      intro B₁ hB₁ h₁ B₂ hB₂ h₂
      by_contra hne
      exact hcon ⟨B₁, hB₁, B₂, hB₂, hne, h₁, h₂⟩
    by_cases hgood : ∃ B ∈ hyperplanes 2 A, KB B = B
    · obtain ⟨B₀, hB₀H, hB₀⟩ := hgood
      have hle : X₀ ≤ YB B₀ := by
        rw [← hgen]
        refine iSup_le fun B => iSup_le fun hBH => ?_
        rcases hK_eq B hBH with hKB | hKA
        · have hBeq : B = B₀ := huniq B hBH hKB B₀ hB₀H hB₀
          rw [hBeq]
        · have hKA' : A ≤ Subgroup.centralizer (YB B : Set E) := by
            rw [← hKA]; exact inf_le_right
          refine le_inf inf_le_left ?_
          intro y hy
          rw [Subgroup.mem_centralizer_iff]
          intro b hb
          exact ((Subgroup.mem_centralizer_iff.mp (hKA' (hB₀H.1 hb))) y hy).symm
      exact hYB_ne B₀ hB₀H (le_antisymm inf_le_left hle)
    · push Not at hgood
      have hKA_all : ∀ B ∈ hyperplanes 2 A, KB B = A := by
        intro B hB
        rcases hK_eq B hB with h | h
        · exact absurd h (hgood B hB)
        · exact h
      have hAcent : A ≤ Subgroup.centralizer (X₀ : Set E) := by
        rw [← hgen]
        refine le_centralizer_iSup ?_
        intro B
        by_cases hB : B ∈ hyperplanes 2 A
        · have h := hKA_all B hB
          have h' : A ≤ Subgroup.centralizer (YB B : Set E) := by
            rw [← h]; exact inf_le_right
          rwa [iSup_pos hB]
        · rw [iSup_neg hB]
          intro a ha
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hy1 : y = 1 := by simpa using hy
          rw [hy1, mul_one, one_mul]
      have h1 : A ⊓ Subgroup.centralizer (X₀ : Set E) = A := inf_eq_left.mpr hAcent
      have hidx1 : ((A ⊓ Subgroup.centralizer (X₀ : Set E)).subgroupOf A).index = 1 := by
        rw [h1, Subgroup.subgroupOf_eq_top.mpr le_rfl, Subgroup.index_top]
      omega
  obtain ⟨B₁, hB₁H, B₂, hB₂H, hB₁B₂, hK₁, hK₂⟩ := htwo
  have hcard12 : Nat.card B₁ = Nat.card B₂ := by
    have hc1 := (B₁.subgroupOf A).card_mul_index
    have hc2 := (B₂.subgroupOf A).card_mul_index
    rw [hhyperIdx B₁ hB₁H] at hc1
    rw [hhyperIdx B₂ hB₂H] at hc2
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₁H.1).toEquiv] at hc1
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₂H.1).toEquiv] at hc2
    omega
  have hB₂notle : ¬ B₂ ≤ B₁ := by
    intro hle
    exact hB₁B₂ (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard12)).symm
  have hB₁notle : ¬ B₁ ≤ B₂ := by
    intro hle
    exact hB₁B₂ (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard12.symm))
  obtain ⟨a₁, ha₁B₂, ha₁nB₁⟩ := Set.not_subset.mp hB₂notle
  obtain ⟨a₂, ha₂B₁, ha₂nB₂⟩ := Set.not_subset.mp hB₁notle
  have ha₁A : a₁ ∈ A := hB₂H.1 ha₁B₂
  have ha₂A : a₂ ∈ A := hB₁H.1 ha₂B₁
  have ha₁sq : a₁ * a₁ = 1 := by rw [← pow_two]; exact hA.2 a₁ ha₁A
  have ha₂sq : a₂ * a₂ = 1 := by rw [← pow_two]; exact hA.2 a₂ ha₂A
  have ha₁notcent : a₁ ∉ Subgroup.centralizer (YB B₁ : Set E) := by
    intro hc
    have : a₁ ∈ KB B₁ := ⟨ha₁A, hc⟩
    rw [hK₁] at this
    exact ha₁nB₁ this
  have ha₂notcent : a₂ ∉ Subgroup.centralizer (YB B₂ : Set E) := by
    intro hc
    have : a₂ ∈ KB B₂ := ⟨ha₂A, hc⟩
    rw [hK₂] at this
    exact ha₂nB₂ this
  obtain ⟨p₁, hp₁, y₁, hy₁YB, hy₁ord, ha₁inv⟩ :=
    exists_prime_order_of_conj_eq_inv (a := a₁) (Y := YB B₁) ha₁sq
      (hYB_inv B₁ hB₁H.1 ha₁A) ha₁notcent
  obtain ⟨p₂, hp₂, y₂, hy₂YB, hy₂ord, ha₂inv⟩ :=
    exists_prime_order_of_conj_eq_inv (a := a₂) (Y := YB B₂) ha₂sq
      (hYB_inv B₂ hB₂H.1 ha₂A) ha₂notcent
  have hy₁X₀ : y₁ ∈ X₀ := hy₁YB.1
  have hy₂X₀ : y₂ ∈ X₀ := hy₂YB.1
  have hnorm_general : ∀ (B : Subgroup E) (hB : B ∈ hyperplanes 2 A) (a : E) (ha : a ∈ A)
      (han : a ∉ B) (y : E) (hy : y ∈ YB B) (hinv : a * y * a⁻¹ = y⁻¹),
      A ≤ Subgroup.normalizer (Subgroup.zpowers y : Set E) := by
    intro B hB a ha han y hy hinv
    rw [Subgroup.le_normalizer_iff]
    intro c hc z hz
    rw [Subgroup.mem_zpowers_iff] at hz ⊢
    obtain ⟨k, rfl⟩ := hz
    by_cases hcB : c ∈ B
    · have hcy : c * y * c⁻¹ = y := by
        rw [(Subgroup.mem_centralizer_iff.mp hy.2) c hcB, mul_assoc, mul_inv_cancel, mul_one]
      refine ⟨k, ?_⟩
      rw [show c * y ^ k * c⁻¹ = (c * y * c⁻¹) ^ k by
            rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply], hcy]
    · have hd : c * a⁻¹ ∈ B :=
        mul_inv_mem_of_not_mem_of_index_two (hhyperIdx B hB) ha hc han hcB
      have hdy : (c * a⁻¹) * y * (c * a⁻¹)⁻¹ = y := by
        rw [(Subgroup.mem_centralizer_iff.mp hy.2) (c * a⁻¹) hd, mul_assoc, mul_inv_cancel,
          mul_one]
      have hc_eq : c = (c * a⁻¹) * a := by group
      have hcy : c * y * c⁻¹ = y⁻¹ := by
        rw [hc_eq]
        calc (c * a⁻¹) * a * y * ((c * a⁻¹) * a)⁻¹
            = (c * a⁻¹) * (a * y * a⁻¹) * (c * a⁻¹)⁻¹ := by group
          _ = (c * a⁻¹) * y⁻¹ * (c * a⁻¹)⁻¹ := by rw [hinv]
          _ = ((c * a⁻¹) * y * (c * a⁻¹)⁻¹)⁻¹ := by group
          _ = y⁻¹ := by rw [hdy]
      refine ⟨-k, ?_⟩
      rw [show c * y ^ k * c⁻¹ = (c * y * c⁻¹) ^ k by
            rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply],
          hcy, inv_zpow, zpow_neg]
  have hnorm₁ : A ≤ Subgroup.normalizer (Subgroup.zpowers y₁ : Set E) :=
    hnorm_general B₁ hB₁H a₁ ha₁A ha₁nB₁ y₁ hy₁YB ha₁inv
  have hnorm₂ : A ≤ Subgroup.normalizer (Subgroup.zpowers y₂ : Set E) :=
    hnorm_general B₂ hB₂H a₂ ha₂A ha₂nB₂ y₂ hy₂YB ha₂inv
  let Z : Subgroup E := Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂
  have hZX : Z ≤ X₀ := sup_le (Subgroup.zpowers_le.mpr hy₁X₀) (Subgroup.zpowers_le.mpr hy₂X₀)
  have hZinv : A ≤ Subgroup.normalizer (Z : Set E) :=
    (le_inf hnorm₁ hnorm₂).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hcy₁ : A ⊓ Subgroup.centralizer ({y₁} : Set E) = B₁ := by
    have hle : B₁ ≤ A ⊓ Subgroup.centralizer ({y₁} : Set E) := by
      refine le_inf hB₁H.1 ?_
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact ((Subgroup.mem_centralizer_iff.mp hy₁YB.2) b hb).symm
    rcases eq_or_eq_of_le_of_index_two hB₁H.1 hle inf_le_left (hhyperIdx B₁ hB₁H) with h | h
    · exact h
    · exfalso
      have ha₁y : a₁ ∉ Subgroup.centralizer ({y₁} : Set E) := by
        intro hc
        have hcent : a₁ * y₁ * a₁⁻¹ = y₁ := by
          have hcomm : y₁ * a₁ = a₁ * y₁ := (Subgroup.mem_centralizer_iff.mp hc) y₁ rfl
          rw [← hcomm]
          group
        rw [ha₁inv] at hcent
        have hy_eq : y₁ = y₁⁻¹ := hcent.symm
        have h2 : y₁ ^ 2 = 1 := by
          rw [pow_two]
          nth_rewrite 2 [hy_eq]
          rw [mul_inv_cancel]
        have hdvdp : p₁ ∣ Nat.card X₀ := by
          rw [← hy₁ord]
          exact Subgroup.orderOf_dvd_natCard _ hy₁X₀
        have hodd1 : Odd p₁ := Odd.of_dvd_nat hX₀odd hdvdp
        have hdvd2 : p₁ ∣ 2 := hy₁ord ▸ orderOf_dvd_of_pow_eq_one h2
        have hp2 : p₁ = 2 := (Nat.prime_dvd_prime_iff_eq hp₁ Nat.prime_two).mp hdvd2
        rw [hp2] at hodd1
        obtain ⟨m, hm⟩ := hodd1
        omega
      have hAleqC : A ≤ Subgroup.centralizer ({y₁} : Set E) := by
        rw [← h]; exact inf_le_right
      exact ha₁y (hAleqC ha₁A)
  have hcy₂ : A ⊓ Subgroup.centralizer ({y₂} : Set E) = B₂ := by
    have hle : B₂ ≤ A ⊓ Subgroup.centralizer ({y₂} : Set E) := by
      refine le_inf hB₂H.1 ?_
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact ((Subgroup.mem_centralizer_iff.mp hy₂YB.2) b hb).symm
    rcases eq_or_eq_of_le_of_index_two hB₂H.1 hle inf_le_left (hhyperIdx B₂ hB₂H) with h | h
    · exact h
    · exfalso
      have ha₂y : a₂ ∉ Subgroup.centralizer ({y₂} : Set E) := by
        intro hc
        have hcent : a₂ * y₂ * a₂⁻¹ = y₂ := by
          have hcomm : y₂ * a₂ = a₂ * y₂ := (Subgroup.mem_centralizer_iff.mp hc) y₂ rfl
          rw [← hcomm]
          group
        rw [ha₂inv] at hcent
        have hy_eq : y₂ = y₂⁻¹ := hcent.symm
        have h2 : y₂ ^ 2 = 1 := by
          rw [pow_two]
          nth_rewrite 2 [hy_eq]
          rw [mul_inv_cancel]
        have hdvdp : p₂ ∣ Nat.card X₀ := by
          rw [← hy₂ord]
          exact Subgroup.orderOf_dvd_natCard _ hy₂X₀
        have hodd2 : Odd p₂ := Odd.of_dvd_nat hX₀odd hdvdp
        have hdvd2 : p₂ ∣ 2 := hy₂ord ▸ orderOf_dvd_of_pow_eq_one h2
        have hp2 : p₂ = 2 := (Nat.prime_dvd_prime_iff_eq hp₂ Nat.prime_two).mp hdvd2
        rw [hp2] at hodd2
        obtain ⟨m, hm⟩ := hodd2
        omega
      have hAleqC : A ≤ Subgroup.centralizer ({y₂} : Set E) := by
        rw [← h]; exact inf_le_right
      exact ha₂y (hAleqC ha₂A)
  have hZCA : A ⊓ Subgroup.centralizer (Z : Set E) = B₁ ⊓ B₂ := by
    change A ⊓ Subgroup.centralizer
      ((Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ : Subgroup E) : Set E) = B₁ ⊓ B₂
    rw [centralizer_zpowers_sup]
    rw [show A ⊓ (Subgroup.centralizer ({y₁} : Set E) ⊓ Subgroup.centralizer ({y₂} : Set E)) =
        (A ⊓ Subgroup.centralizer ({y₁} : Set E)) ⊓ (A ⊓ Subgroup.centralizer ({y₂} : Set E))
        from by ext x; simp only [Subgroup.mem_inf]; tauto]
    rw [hcy₁, hcy₂]
  have hZidx : ((A ⊓ Subgroup.centralizer (Z : Set E)).subgroupOf A).index = 4 := by
    rw [hZCA]
    exact index_inf_eq_four_of_index_two hB₁H.1 hB₂H.1 (hhyperIdx B₁ hB₁H) (hhyperIdx B₂ hB₂H) hB₁B₂
  have hZeqX : Z = X₀ := by
    have hPm : P (Nat.card Z) := ⟨Z, hZX.trans hX₀X, hZinv, by rw [hZidx], rfl⟩
    have hle : Nat.card X₀ ≤ Nat.card Z := by
      have := Nat.find_min' hP hPm
      rwa [← hX₀card] at this
    exact Subgroup.eq_of_le_of_card_ge hZX hle
  have hmin' : ∀ W : Subgroup E, W < X₀ → A ≤ Subgroup.normalizer (W : Set E) →
      ((A ⊓ Subgroup.centralizer (W : Set E)).subgroupOf A).index ≤ 2 := by
    intro W hW hWinv
    exact index_le_two_of_lt_four hA
      (not_le.mp (hmin W (hW.le.trans hX₀X) hWinv (Subgroup.card_lt_of_lt hW)))
  have ha₁cent₂ : a₁ * y₂ * a₁⁻¹ = y₂ := by
    rw [(Subgroup.mem_centralizer_iff.mp hy₂YB.2) a₁ ha₁B₂, mul_assoc, mul_inv_cancel, mul_one]
  have ha₂cent₁ : a₂ * y₁ * a₂⁻¹ = y₁ := by
    rw [(Subgroup.mem_centralizer_iff.mp hy₁YB.2) a₂ ha₂B₁, mul_assoc, mul_inv_cancel, mul_one]
  have hcomm12 : y₁ * y₂ = y₂ * y₁ :=
    commute_of_minimal_invariant hA hX₀inv hX₀odd hX₀ne hZeqX.symm hnorm₁ hnorm₂
      (hy₁ord ▸ hp₁) (hy₂ord ▸ hp₂) ha₁A ha₂A ha₁inv ha₁cent₂ ha₂cent₁ ha₂inv hmin'
  have hD_eq : B₁ ⊓ B₂ = A ⊓ Subgroup.centralizer (X₀ : Set E) := by
    rw [← hZeqX]; exact hZCA.symm
  have hD_idx : ((B₁ ⊓ B₂).subgroupOf A).index = 4 := by rw [← hZCA]; exact hZidx
  have hDBidx : ∀ (C : Subgroup E) (hCB : B₁ ⊓ B₂ ≤ C) (hCA : C ≤ A)
      (hCi : (C.subgroupOf A).index = 2), ((B₁ ⊓ B₂).subgroupOf C).index = 2 := by
    intro C hCB hCA hCi
    have hDcardA : Nat.card (B₁ ⊓ B₂ : Subgroup E) * 4 = Nat.card A := by
      have h := ((B₁ ⊓ B₂).subgroupOf A).card_mul_index
      rw [hD_idx] at h
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left.trans hB₁H.1)).toEquiv] at h
    have hCcardA : Nat.card C * 2 = Nat.card A := by
      have h := (C.subgroupOf A).card_mul_index
      rw [hCi] at h
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCA).toEquiv] at h
    have h1 := ((B₁ ⊓ B₂).subgroupOf C).card_mul_index
    have h2 : Nat.card ((B₁ ⊓ B₂).subgroupOf C : Subgroup C) = Nat.card (B₁ ⊓ B₂ : Subgroup E) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCB).toEquiv
    rw [h2] at h1
    have hCcard : Nat.card C = Nat.card (B₁ ⊓ B₂ : Subgroup E) * 2 := by omega
    rw [hCcard] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hB₂eq : B₂ = (B₁ ⊓ B₂) ⊔ Subgroup.zpowers a₁ := by
    have hsup_le : (B₁ ⊓ B₂) ⊔ Subgroup.zpowers a₁ ≤ B₂ :=
      sup_le inf_le_right (Subgroup.zpowers_le.mpr ha₁B₂)
    have hne : (B₁ ⊓ B₂) ⊔ Subgroup.zpowers a₁ ≠ B₁ ⊓ B₂ := by
      intro h
      have : a₁ ∈ B₁ ⊓ B₂ := by
        rw [← h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a₁)
      exact ha₁nB₁ this.1
    rcases eq_or_eq_of_le_of_index_two inf_le_right le_sup_left hsup_le
      (hDBidx B₂ inf_le_right hB₂H.1 (hhyperIdx B₂ hB₂H)) with h | h
    · exact absurd h hne
    · exact h.symm
  have hB₁eq : B₁ = (B₁ ⊓ B₂) ⊔ Subgroup.zpowers a₂ := by
    have hsup_le : (B₁ ⊓ B₂) ⊔ Subgroup.zpowers a₂ ≤ B₁ :=
      sup_le inf_le_left (Subgroup.zpowers_le.mpr ha₂B₁)
    have hne : (B₁ ⊓ B₂) ⊔ Subgroup.zpowers a₂ ≠ B₁ ⊓ B₂ := by
      intro h
      have : a₂ ∈ B₁ ⊓ B₂ := by
        rw [← h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a₂)
      exact ha₂nB₂ this.2
    rcases eq_or_eq_of_le_of_index_two inf_le_left le_sup_left hsup_le
      (hDBidx B₁ inf_le_left hB₁H.1 (hhyperIdx B₁ hB₁H)) with h | h
    · exact absurd h hne
    · exact h.symm
  have hBsup : B₁ ⊔ B₂ = A := by
    have hsup_le : B₁ ⊔ B₂ ≤ A := sup_le hB₁H.1 hB₂H.1
    have hne : B₁ ⊔ B₂ ≠ B₁ := by
      intro h
      have : B₂ ≤ B₁ := by rw [← h]; exact le_sup_right
      exact hB₁B₂ (Subgroup.eq_of_le_of_card_ge this (le_of_eq hcard12)).symm
    rcases eq_or_eq_of_le_of_index_two hB₁H.1 le_sup_left hsup_le (hhyperIdx B₁ hB₁H) with h | h
    · exact absurd h hne
    · exact h
  have hAeq : A = (B₁ ⊓ B₂) ⊔ Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂ := by
    rw [← hBsup]
    nth_rewrite 1 [hB₂eq]
    nth_rewrite 1 [hB₁eq]
    ac_rfl
  refine ⟨{
    X₀ := X₀
    X₀_le := hX₀X
    X₀_invariant := hX₀inv
    D := B₁ ⊓ B₂
    D_eq := hD_eq
    D_index := hD_idx
    a₁ := a₁
    a₂ := a₂
    a₁_mem := ha₁A
    a₂_mem := ha₂A
    p₁ := p₁
    p₂ := p₂
    p₁_prime := hp₁
    p₂_prime := hp₂
    x₁ := y₁
    x₂ := y₂
    x₁_mem := hy₁X₀
    x₂_mem := hy₂X₀
    x₁_order := hy₁ord
    x₂_order := hy₂ord
    X₀_eq := hZeqX.symm
    x_comm := hcomm12
    A_eq := hAeq
    a₁_inverts := ha₁inv
    a₂_inverts := ha₂inv
    a₁_centralizes := ha₁cent₂
    a₂_centralizes := ha₂cent₁
    hyperplane := by rw [← hB₁eq, hhyperIdx B₁ hB₁H] }⟩

end CFSG.LocalAnalysis.WeakClosure81
