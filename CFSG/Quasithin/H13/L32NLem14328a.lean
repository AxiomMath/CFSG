module

public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoBase
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.H13.L32NSet14
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L32NSet14

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] [IsMulCommutative ↥V] in
theorem pow_mul_inv_mem {X : Subgroup G} {y q : G} (hy : y ∈ X)
    (hq : q ∈ Subgroup.normalizer (X : Set G)) (n : ℕ) : (y * q) ^ n * (q ^ n)⁻¹ ∈ X := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hqn : q ^ n ∈ Subgroup.normalizer (X : Set G) := (Subgroup.normalizer _).pow_mem hq n
    have h1 : q ^ n * y * (q ^ n)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hqn y).mp hy
    have e : (y * q) ^ (n + 1) * (q ^ (n + 1))⁻¹ =
        ((y * q) ^ n * (q ^ n)⁻¹) * (q ^ n * y * (q ^ n)⁻¹) := by
      rw [pow_succ, pow_succ']
      group
    rw [e]
    exact X.mul_mem ih h1

namespace Setting

variable (S : Setting G T L V V₂)
include S

theorem fix_V {z a b c : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (ha : a ∈ V₂)
    (ha1 : a ∉ fsuV1 T V) (hb : b ∈ V) (hbV : b ∉ V₂) (hcz : c * z * c⁻¹ = z)
    (hca : c * a * c⁻¹ = a) (hcb : c * b * c⁻¹ = b) {v : G} (hv : v ∈ V) : c * v * c⁻¹ = v := by
  have h1 : ∀ w ∈ fsuV1 T V, c * w * c⁻¹ = w := by
    intro w hw
    rcases S.eq_of_mem_V1 hz hz1 hw with rfl | rfl
    · group
    · exact hcz
  have h2 : ∀ w ∈ V₂, c * w * c⁻¹ = w := by
    intro w hw
    rcases S.mem_V2 ha ha1 hw with h | h
    · exact h1 w h
    · rw [show w = a⁻¹ * (a * w) by group,
        show c * (a⁻¹ * (a * w)) * c⁻¹ = (c * a * c⁻¹)⁻¹ * (c * (a * w) * c⁻¹) by group, hca,
        h1 _ h]
  rcases S.mem_V hb hbV hv with h | h
  · exact h2 v h
  · rw [show v = b⁻¹ * (b * v) by group,
      show c * (b⁻¹ * (b * v)) * c⁻¹ = (c * b * c⁻¹)⁻¹ * (c * (b * v) * c⁻¹) by group, hcb,
      h2 _ h]

theorem isSimple_autOn : IsSimpleGroup ↥(autOn L V) := by
  have hLV := S.LV
  have hsurj := InternalSec.autOnHom_surjective hLV
  have hker : (InternalSec.autOnHom hLV).ker = CFSG.pCore 2 ↥L := by
    ext l
    rw [InternalSec.mem_ker_autOnHom]
    constructor
    · intro hl
      have h1 : (l : G) ∈ pCoreOf 2 L := by
        rw [← S.cent_eq]
        exact ⟨l.2, hl⟩
      obtain ⟨q, hq, hql⟩ := h1
      have : q = l := Subtype.ext hql
      rw [← this]
      exact hq
    · intro hl
      have h1 : (l : G) ∈ pCoreOf 2 L := ⟨l, hl, rfl⟩
      rw [← S.cent_eq] at h1
      exact h1.2
  obtain ⟨e⟩ := S.h1281.quot
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Vol2Native.A312L.Seven.slThree_isSimple
  exact ((QuotientGroup.quotientKerEquivOfSurjective _ hsurj).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans e)).isSimpleGroup

theorem eq_of_autOn_eq {X : Subgroup G} (hXL : X ≤ L)
    (hXn : pCoreOf 2 L ≤ Subgroup.normalizer (X : Set G)) (hA : autOn X V = autOn L V) :
    X = L := by
  have hLV := S.LV
  have hdec : ∀ l ∈ L, ∃ x ∈ X, x⁻¹ * l ∈ pCoreOf 2 L := by
    intro l hl
    have hmem : conjAct V ⟨l, hLV hl⟩ ∈ autOn X V := by
      rw [hA]
      exact ⟨⟨l, hLV hl⟩, hl, rfl⟩
    obtain ⟨⟨x, hxN⟩, hxX, hx⟩ := hmem
    refine ⟨x, hxX, ?_⟩
    rw [← S.cent_eq]
    refine ⟨L.mul_mem (L.inv_mem (hXL hxX)) hl, ?_⟩
    have h1 : conjAct V ((⟨x, hxN⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ * ⟨l, hLV hl⟩) = 1 := by
      rw [map_mul, map_inv, hx, inv_mul_cancel]
    exact A4.conjAct_eq_one_iff.mp h1
  refine S.hH.faithful.2.1 X hXL ⟨fun x hx l => ?_⟩ fun l hl => ?_
  · obtain ⟨y, hyX, hyq⟩ := hdec l l.2
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hq := hXn hyq
    have e : ((l * x * l⁻¹ : ↥L) : G) =
        y * ((y⁻¹ * l) * x * (y⁻¹ * l)⁻¹) * y⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact X.mul_mem (X.mul_mem hyX ((Subgroup.mem_normalizer_iff.mp hq _).mp hx)) (X.inv_mem hyX)
  · obtain ⟨y, hyX, hyq⟩ := hdec l hl
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨_, hyq⟩
    have hk' : (y⁻¹ * l) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    have := pow_mul_inv_mem hyX (hXn hyq) (2 ^ k)
    rwa [hk', inv_one, mul_one, mul_inv_cancel_left] at this

theorem autOn_eq_of_normal {X : Subgroup G} (hXL : X ≤ L)
    (hXn : L ≤ Subgroup.normalizer (X : Set G)) (hX1 : ¬ X ≤ Subgroup.centralizer (V : Set G)) :
    autOn X V = autOn L V := by
  have := S.isSimple_autOn
  have hLV := S.LV
  have hAB : autOn X V ≤ autOn L V := by
    rintro φ ⟨⟨x, hxN⟩, hxX, rfl⟩
    exact ⟨⟨x, hxN⟩, hXL hxX, rfl⟩
  set A' := (autOn X V).subgroupOf (autOn L V) with hA'
  have hn : A'.Normal := by
    refine ⟨fun φ hφ ψ => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hφ ⊢
    obtain ⟨⟨x, hxN⟩, hxX, hx⟩ := hφ
    obtain ⟨⟨l, hlN⟩, hlL, hl⟩ := ψ.2
    refine ⟨⟨l, hlN⟩ * ⟨x, hxN⟩ * (⟨l, hlN⟩)⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hXn hlL) x).mp hxX
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rw [hx, hl]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A' with hb | ht
  · exfalso
    apply hX1
    intro x hxX
    have hmem : (⟨conjAct V ⟨x, hLV (hXL hxX)⟩, ⟨_, hXL hxX, rfl⟩⟩ : ↥(autOn L V)) ∈ A' :=
      Subgroup.mem_subgroupOf.mpr ⟨_, hxX, rfl⟩
    rw [hb, Subgroup.mem_bot] at hmem
    exact A4.conjAct_eq_one_iff.mp (congrArg Subtype.val hmem)
  · refine le_antisymm hAB fun φ hφ => ?_
    have : (⟨φ, hφ⟩ : ↥(autOn L V)) ∈ A' := by rw [ht]; trivial
    exact Subgroup.mem_subgroupOf.mp this

theorem autOn_eq_of_dvd {X : Subgroup G} (hXL : X ≤ L) (h84 : 84 ∣ Nat.card ↥(autOn X V)) :
    autOn X V = autOn L V := by
  have := S.isSimple_autOn
  have hAB : autOn X V ≤ autOn L V := by
    rintro φ ⟨⟨x, hxN⟩, hxX, rfl⟩
    exact ⟨⟨x, hxN⟩, hXL hxX, rfl⟩
  set A' := (autOn X V).subgroupOf (autOn L V) with hA'
  have hcardA' : Nat.card A' = Nat.card ↥(autOn X V) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  have hmul := A'.index_mul_card
  rw [hcardA', S.card_autOn] at hmul
  have hidx : A'.index = 1 := by
    obtain ⟨k, hk⟩ := h84
    rw [hk] at hmul
    have h2 : A'.index * k = 2 :=
      Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 84) (by linarith)
    rcases (Nat.dvd_prime Nat.prime_two).mp ⟨k, h2.symm⟩ with h | h
    · exact h
    · exfalso
      have hn : A'.Normal := Subgroup.normal_of_index_eq_two h
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A' with hb | ht
      · have h1 : Nat.card A' = 1 := by rw [hb, Subgroup.card_bot]
        rw [hcardA', hk] at h1
        omega
      · rw [ht, Subgroup.index_top] at h
        omega
  refine le_antisymm hAB fun φ hφ => ?_
  have : (⟨φ, hφ⟩ : ↥(autOn L V)) ∈ A' := by
    rw [Subgroup.index_eq_one.mp hidx]
    trivial
  exact Subgroup.mem_subgroupOf.mp this

theorem conjClosure_eq {X : Subgroup G} (hXL : X ≤ L)
    (hX1 : ¬ X ≤ Subgroup.centralizer (V : Set G)) : conjClosure X L = L := by
  have hNL : conjClosure X L ≤ L := conjClosure_le fun h hh x hx =>
    L.mul_mem (L.mul_mem hh (hXL hx)) (L.inv_mem hh)
  refine S.eq_of_autOn_eq hNL ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans
    (le_normalizer_conjClosure _ _)) (S.autOn_eq_of_normal hNL (le_normalizer_conjClosure _ _)
      fun h => hX1 ((le_conjClosure X L).trans h))

omit [IsMulCommutative ↥V] S in
theorem dvd_84 {X : Subgroup G} {α ι₁ ι₂ ω : MulAut ↥V} (hα : α ∈ autOn X V)
    (hι₁ : ι₁ ∈ autOn X V) (hι₂ : ι₂ ∈ autOn X V) (hω : ω ∈ autOn X V) (hα3 : α ^ 3 = 1)
    (hα1 : α ≠ 1) (hι₁2 : ι₁ ^ 2 = 1) (hι₁1 : ι₁ ≠ 1) (hι₂2 : ι₂ ^ 2 = 1) (hι₂1 : ι₂ ≠ 1)
    (hι : ι₁ ≠ ι₂) (hιc : ι₁ * ι₂ = ι₂ * ι₁) (hω7 : ω ^ 7 = 1) (hω1 : ω ≠ 1) :
    84 ∣ Nat.card ↥(autOn X V) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : 3 ∣ Nat.card ↥(autOn X V) := by
    rw [← orderOf_eq_prime hα3 hα1]
    exact Subgroup.orderOf_dvd_natCard _ hα
  have h7 : 7 ∣ Nat.card ↥(autOn X V) := by
    rw [← orderOf_eq_prime hω7 hω1]
    exact Subgroup.orderOf_dvd_natCard _ hω
  have ho₁ : orderOf ι₁ = 2 := orderOf_eq_prime hι₁2 hι₁1
  have ho₂ : orderOf ι₂ = 2 := orderOf_eq_prime hι₂2 hι₂1
  have hnorm : Subgroup.zpowers ι₁ ≤
      Subgroup.normalizer (Subgroup.zpowers ι₂ : Set (MulAut ↥V)) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((Commute.zpow_left (show Commute ι₂ ι₁ from hιc.symm) k).eq)
  have hinf : Subgroup.zpowers ι₁ ⊓ Subgroup.zpowers ι₂ = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers ι₁ ⊓ Subgroup.zpowers ι₂) ∣ 2 := by
      rw [← ho₂, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers ι₁ ⊓ Subgroup.zpowers ι₂ = Subgroup.zpowers ι₂ :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h2, Nat.card_zpowers, ho₂])
      have h21 : ι₂ ∈ Subgroup.zpowers ι₁ :=
        (heq ▸ inf_le_left : Subgroup.zpowers ι₂ ≤ _) (Subgroup.mem_zpowers ι₂)
      classical
      rw [mem_zpowers_iff_mem_range_orderOf, ho₁] at h21
      simp only [Finset.mem_image, Finset.mem_range] at h21
      obtain ⟨k, hk, hkι⟩ := h21
      interval_cases k
      · exact hι₂1 (by rw [← hkι, pow_zero])
      · exact hι (by rw [← hkι, pow_one])
  have hcard4 := L32NSet14.card_sup_mul_card_inf hnorm
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, ho₁, ho₂] at hcard4
  have h4 : 4 ∣ Nat.card ↥(autOn X V) := by
    have := Subgroup.card_dvd_of_le (sup_le ((Subgroup.zpowers_le).mpr hι₁)
      ((Subgroup.zpowers_le).mpr hι₂))
    rwa [hcard4] at this
  have h12 : 12 ∣ Nat.card ↥(autOn X V) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h3
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h12 h7

end Setting

end L32NSet14

end CFSG.Quasithin.H13
