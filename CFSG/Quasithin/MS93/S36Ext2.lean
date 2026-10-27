module

public import CFSG.Quasithin.MS93.S36Two

public section

namespace CFSG.Quasithin.MS93.S36

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G]

section General

@[expose] def subgroupOfMulClosed [Finite G] (S : Set G) (h1 : (1 : G) ∈ S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) : Subgroup G where
  carrier := S
  one_mem' := h1
  mul_mem' := fun {a b} ha hb => hmul a ha b hb
  inv_mem' := fun {a} ha => by
    have hpow : ∀ n : ℕ, a ^ n ∈ S := by
      intro n
      induction n with
      | zero => simpa using h1
      | succ n ih => rw [pow_succ]; exact hmul _ ih _ ha
    have hn : 0 < orderOf a := orderOf_pos a
    have : a⁻¹ = a ^ (orderOf a - 1) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_succ, Nat.sub_add_cancel hn, pow_orderOf_eq_one]
    rw [this]
    exact hpow _

theorem elem_of_closure {S : Set G} (hc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (h2 : ∀ x ∈ S, x ^ 2 = 1) :
    (∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x) ∧
      ∀ x ∈ Subgroup.closure S, x ^ 2 = 1 := by
  have hcomm : IsMulCommutative ↥(Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hc x hx y hy
  have hc' : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
    intro x hx y hy
    have := hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  refine ⟨hc', fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h2 x hx
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    rw [sq, show x * y * (x * y) = x * x * (y * y) by
      rw [mul_assoc, ← mul_assoc y x y, ← hc' x hx y hy]; group, ← sq, ← sq, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem card_le_of_le_sup [Finite G] {V U E₀ E₁ E₂ : Subgroup G}
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hUV : U ≤ V) (hE₀ : E₀ ≤ V) (hE₁ : E₁ ≤ V)
    (hE₂ : E₂ ≤ V) (hV : V ≤ U ⊔ E₀ ⊔ E₁ ⊔ E₂) {q : ℕ}
    (h₀ : Nat.card ↥E₀ ≤ q * Nat.card ↥(E₀ ⊓ U)) (h₁ : Nat.card ↥E₁ ≤ q * Nat.card ↥(E₁ ⊓ U))
    (h₂ : Nat.card ↥E₂ ≤ q * Nat.card ↥(E₂ ⊓ U)) : Nat.card ↥V ≤ q ^ 3 * Nat.card ↥U := by
  let _ : CommGroup ↥V :=
    { (inferInstance : Group ↥V) with mul_comm := fun x y => Subtype.ext (hVc x x.2 y y.2) }
  set U' := U.subgroupOf V with hU'
  let π : ↥V →* ↥V ⧸ U' := QuotientGroup.mk' U'
  have hcardV := Subgroup.card_eq_card_quotient_mul_card_subgroup U'
  have hcU' : Nat.card ↥U' = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv
  have himg : ∀ {E : Subgroup G}, E ≤ V → Nat.card ↥E ≤ q * Nat.card ↥(E ⊓ U) →
      Nat.card ↥((E.subgroupOf V).map π) ≤ q := by
    intro E hEV hEq
    have h1 := card_eq_card_inf_ker_mul_card_map π (E.subgroupOf V)
    rw [QuotientGroup.ker_mk'] at h1
    have h2 : E.subgroupOf V ⊓ U' = (E ⊓ U).subgroupOf V := by
      ext x
      simp [hU', Subgroup.mem_subgroupOf]
    rw [h2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hEV)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEV).toEquiv] at h1
    have hpos : 0 < Nat.card ↥(E ⊓ U) := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : Nat.card ↥(E ⊓ U) * (q + 1) ≤ Nat.card ↥(E ⊓ U) *
        Nat.card ↥((E.subgroupOf V).map π) := Nat.mul_le_mul_left _ hlt
    nlinarith
  have hsub : (U ⊔ E₀ ⊔ E₁ ⊔ E₂).subgroupOf V =
      U' ⊔ E₀.subgroupOf V ⊔ E₁.subgroupOf V ⊔ E₂.subgroupOf V := by
    rw [Subgroup.subgroupOf_sup (sup_le (sup_le hUV hE₀) hE₁) hE₂,
      Subgroup.subgroupOf_sup (sup_le hUV hE₀) hE₁, Subgroup.subgroupOf_sup hUV hE₀]
  have htop : (⊤ : Subgroup (↥V ⧸ U')) ≤
      (E₀.subgroupOf V).map π ⊔ (E₁.subgroupOf V).map π ⊔ (E₂.subgroupOf V).map π := by
    intro x _
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective U' x
    have hv : v ∈ (U ⊔ E₀ ⊔ E₁ ⊔ E₂).subgroupOf V := hV v.2
    rw [hsub] at hv
    have := Subgroup.mem_map_of_mem π hv
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']), bot_sup_eq] at this
    exact this
  have hc := (Subgroup.card_le_of_le htop).trans ((card_sup_le_mul _ _).trans
    (Nat.mul_le_mul_right _ (card_sup_le_mul _ _)))
  rw [Subgroup.card_top] at hc
  have hb₀ := himg hE₀ h₀
  have hb₁ := himg hE₁ h₁
  have hb₂ := himg hE₂ h₂
  rw [hcardV, hcU']
  calc Nat.card (↥V ⧸ U') * Nat.card ↥U ≤ (q * q * q) * Nat.card ↥U := by
        refine Nat.mul_le_mul_right _ (hc.trans ?_)
        exact Nat.mul_le_mul (Nat.mul_le_mul hb₀ hb₁) hb₂
    _ = q ^ 3 * Nat.card ↥U := by ring

end General

section Centralizing

variable [Finite G] {M T L : Subgroup G}

theorem exists_mul_inv_mem_L (h : PUHyp M T L) {c : G} (hcM : c ∈ M)
    (hcU : ∀ u ∈ Uq M T L, c * u = u * c) : ∃ x ∈ pCoreOf 2 M, c * x⁻¹ ∈ L := by
  obtain ⟨f, m, hm, hcm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hcop : Nat.Coprime (2 ^ f) m := Nat.Coprime.pow_left f (Nat.coprime_two_left.mpr hm)
  have hbez : ((2 ^ f : ℕ) : ℤ) * Nat.gcdA (2 ^ f) m + (m : ℤ) * Nat.gcdB (2 ^ f) m = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one, Nat.cast_one]
  set c₂ := c ^ ((m : ℤ) * Nat.gcdB (2 ^ f) m) with hc₂
  set c₀ := c ^ (((2 ^ f : ℕ) : ℤ) * Nat.gcdA (2 ^ f) m) with hc₀
  have hcdec : c = c₀ * c₂ := by
    rw [hc₀, hc₂, ← zpow_add, hbez, zpow_one]
  have hord : c ^ (2 ^ f * m) = 1 := by rw [← hcm, pow_orderOf_eq_one]
  have hc₂2 : c₂ ^ 2 ^ f = 1 := by
    rw [hc₂, ← zpow_natCast, ← zpow_mul, show (m : ℤ) * Nat.gcdB (2 ^ f) m * ((2 ^ f : ℕ) : ℤ) =
      ((2 ^ f * m : ℕ) : ℤ) * Nat.gcdB (2 ^ f) m by push_cast; ring, zpow_mul, zpow_natCast, hord,
      one_zpow]
  have hc₀m : c₀ ^ m = 1 := by
    rw [hc₀, ← zpow_natCast, ← zpow_mul, show ((2 ^ f : ℕ) : ℤ) * Nat.gcdA (2 ^ f) m * (m : ℤ) =
      ((2 ^ f * m : ℕ) : ℤ) * Nat.gcdA (2 ^ f) m by push_cast; ring, zpow_mul, zpow_natCast, hord,
      one_zpow]
  have hzM : ∀ k : ℤ, c ^ k ∈ M := fun k => M.zpow_mem hcM k
  have hzU : ∀ k : ℤ, ∀ u ∈ Uq M T L, c ^ k * u = u * c ^ k := by
    intro k u hu
    have hcomm : Commute c u := hcU u hu
    exact (hcomm.zpow_left k).eq
  have hUn := le_normalizer_Uq h.le_normalizer (T := T) (M := M) (L := L)
  have hDn : M ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (Uq M T L : Set G) :
      Subgroup G) : Set G) :=
    le_normalizer_inf h.le_normalizer (le_normalizer_centralizer hUn)
  have hLD : ¬ L ≤ L ⊓ Subgroup.centralizer (Uq M T L : Set G) := fun hle =>
    h.not_le_centralizer_of_Uq_le le_rfl (hle.trans inf_le_right)
  have hc₂Q : c₂ ∈ pCoreOf 2 M := by
    refine h.mem_pCoreOf_of_rel hDn hLD (hzM _) ⟨f, hc₂2⟩ fun l hl => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hl' : c₂ * l * c₂⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (h.le_normalizer (hzM _)) l).mp hl
      rw [commutatorElement_def]
      exact L.mul_mem hl' (L.inv_mem hl)
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hlu : l⁻¹ * u * l⁻¹⁻¹ ∈ Uq M T L :=
        (Subgroup.mem_normalizer_iff.mp (hUn (h.L_le (L.inv_mem hl))) u).mp hu
      have h1 := hzU ((m : ℤ) * Nat.gcdB (2 ^ f) m) _ hlu
      have h2 := hzU ((m : ℤ) * Nat.gcdB (2 ^ f) m) u hu
      rw [← hc₂] at h1 h2
      rw [inv_inv] at h1
      rw [commutatorElement_def]
      calc u * (c₂ * l * c₂⁻¹ * l⁻¹) = c₂ * u * l * c₂⁻¹ * l⁻¹ := by rw [h2]; group
        _ = c₂ * l * (l⁻¹ * u * l) * c₂⁻¹ * l⁻¹ := by group
        _ = c₂ * l * c₂⁻¹ * (c₂ * (l⁻¹ * u * l)) * c₂⁻¹ * l⁻¹ := by group
        _ = c₂ * l * c₂⁻¹ * ((l⁻¹ * u * l) * c₂) * c₂⁻¹ * l⁻¹ := by rw [h1]
        _ = c₂ * l * c₂⁻¹ * l⁻¹ * u := by group
  have hc₀L : c₀ ∈ L := by
    obtain ⟨e, he⟩ := h.exists_pow_mem_L (hzM (((2 ^ f : ℕ) : ℤ) * Nat.gcdA (2 ^ f) m))
    rw [← hc₀] at he
    have hcop' : (2 ^ e).gcd (orderOf c₀) = 1 := by
      have h1 : orderOf c₀ ∣ m := orderOf_dvd_of_pow_eq_one hc₀m
      exact Nat.Coprime.coprime_dvd_right h1
        (Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hm))
    exact (Subgroup.zpowers_le.mpr he) (mem_zpowers_pow_iff.mpr hcop')
  refine ⟨c₂, hc₂Q, ?_⟩
  rw [hcdec, mul_inv_cancel_right]
  exact hc₀L

theorem closure_sup_pCore_eq_top (h : PUHyp M T L) {F : Type} [Field F]
    {a : ↥L →* ↥(StatedSL 3 F)} (hU : IsSumOfNaturalModulesVia L (Uq M T L) ⊥ a false 1)
    (ha : Function.Surjective a) {S : Set ↥L}
    (hS : Subgroup.closure S ⊔ (toSL3 a).ker = ⊤) :
    Subgroup.closure S ⊔ CFSG.pCore 2 ↥L = ⊤ := by
  set P := CFSG.pCore 2 ↥L with hP
  have hPker : P ≤ (toSL3 a).ker := by
    intro o ho
    have hoQ : (o : G) ∈ pCoreOf 2 M := pCoreOf_le_pCoreOf_of_le_normalizer h.L_le
      h.le_normalizer (mem_pCoreOf_of_mem_pCore_two ho)
    have hao : a o = 1 := eq_one_of_isSumOfNaturalModulesVia hU fun v hv => by
      rw [commute_of_mem_pCoreOf_Xq hoQ (h.Uq_le_Xq hv), mul_inv_cancel_right]
    rw [MonoidHom.mem_ker]
    simp [toSL3, hao]
  let φ : ↥L ⧸ P →* SL3 F := QuotientGroup.lift P (toSL3 a) hPker
  have hφ : ∃ k, φ k ≠ 1 := by
    obtain ⟨l, hl⟩ := toSL3_surjective ha (rootElt 0 1 (1 : F))
    refine ⟨QuotientGroup.mk' P l, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk, hl, Ne,
      rootElt_eq_one_iff (by decide)]
    exact one_ne_zero
  have hcen := CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple h.quasisimple hφ
  have hkerP : ∀ k ∈ (toSL3 a).ker, ∀ l : ↥L, ⁅k, l⁆ ∈ P := by
    intro k hk l
    have hk' : QuotientGroup.mk' P k ∈ φ.ker := by
      rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
      exact hk
    have hc := Subgroup.mem_center_iff.mp (hcen hk') (QuotientGroup.mk' P l)
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hc.symm
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr h.perfect
  rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := ↥L), commutator_def,
    Subgroup.commutator_le]
  intro x _ y _
  have hx : x ∈ Subgroup.closure S ⊔ (toSL3 a).ker := by rw [hS]; exact Subgroup.mem_top x
  have hy : y ∈ Subgroup.closure S ⊔ (toSL3 a).ker := by rw [hS]; exact Subgroup.mem_top y
  obtain ⟨c, hc, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨c', hc', k', hk', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  rw [show ⁅c * k, c' * k'⁆ = (c * ⁅k, c' * k'⁆ * c⁻¹) * (⁅c, c'⁆ * (c' * ⁅c, k'⁆ * c'⁻¹)) by
    simp only [commutatorElement_def]; group]
  have hP1 : c * ⁅k, c' * k'⁆ * c⁻¹ ∈ P := (inferInstance : P.Normal).conj_mem _ (hkerP k hk _) c
  have hP2 : c' * ⁅c, k'⁆ * c'⁻¹ ∈ P := by
    refine (inferInstance : P.Normal).conj_mem _ ?_ c'
    rw [← commutatorElement_inv]
    exact P.inv_mem (hkerP k' hk' c)
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_right hP1) (Subgroup.mul_mem _ ?_
    (Subgroup.mem_sup_right hP2))
  refine Subgroup.mem_sup_left ?_
  rw [commutatorElement_def]
  exact (Subgroup.closure S).mul_mem ((Subgroup.closure S).mul_mem ((Subgroup.closure S).mul_mem
    hc hc') ((Subgroup.closure S).inv_mem hc)) ((Subgroup.closure S).inv_mem hc')

end Centralizing

end CFSG.Quasithin.MS93.S36
