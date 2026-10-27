module

public import CFSG.Quasithin.Vol2.Ch10Reselect.RElem
public import CFSG.Quasithin.Vol2.Ch10Reselect.L0Facts
public import CFSG.Quasithin.Vol2.Ch10Reselect.Rank
public import CFSG.Quasithin.Vol2.Ch10Reselect.ActML2

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10 CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {K : Type} [Field K]

theorem conj_mem_centralizer_fsuVM {n c : G} (hn : n ∈ fsuM T L)
    (hc : c ∈ Subgroup.centralizer (fsuVM T L I : Set G)) :
    n * c * n⁻¹ ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
  have hNA : fsuM T L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    SecA.fsuM_le_normalizer_fsuVM T L I
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have ha' : n⁻¹ * a * n ∈ fsuVM T L I := by
    have := (Subgroup.mem_normalizer_iff.mp (hNA ((fsuM T L).inv_mem hn)) a).mp ha
    simpa using this
  have h := Subgroup.mem_centralizer_iff.mp hc _ ha'
  calc a * (n * c * n⁻¹) = n * ((n⁻¹ * a * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * a * n)) * n⁻¹ := by rw [h]
    _ = n * c * n⁻¹ * a := by group

theorem false_of_rElement (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hfsu : FSU G T L I) (hlt : L < fsuL0 T L)
    [IsMulCommutative ↥(fsuVM T L I)] (hA : Concl326A T L I) [Finite K] (M : RModel T L I K)
    {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) {k : G} (hk : k ∈ fsuM T L)
    (hk0 : ∀ l ∈ fsuL0 T L, ⁅k, l⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G)) {j : ℕ}
    (hkord : orderOf k = r ^ j) (hknot : k ∉ Subgroup.centralizer (fsuVM T L I : Set G))
    (hkr : k ^ r ∈ Subgroup.centralizer (fsuVM T L I : Set G)) : False := by
  classical
  obtain ⟨t, ht, htn⟩ := Set.not_subset.mp (not_le_normalizer_of_lt hlt)
  by_cases hrSL : r ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K)
  ·
    have hrL : r ∣ Nat.card L := hrSL.trans (card_SL_dvd_card_L M)
    rcases Nat.lt_or_ge j 2 with hj | hj
    · interval_cases j
      ·
        have hk1 : k = 1 := orderOf_eq_one_iff.mp (by simpa using hkord)
        exact hknot (hk1 ▸ Subgroup.one_mem _)
      ·
        have hkord' : orderOf k = r := by simpa using hkord
        have hkL0 := mem_fsuL0_of_orderOf_eq h37 h38 hfsu hlt hA hr2 hrL hk hkord'
        have hkO := mem_pCoreOf_of_commutators_mem h37 h38 hfsu hlt hkL0 hk0
        have hkr1 : k ^ r = 1 := by rw [← hkord']; exact pow_orderOf_eq_one k
        have hk1 := eq_one_of_mem_isPGroup_two (X := pCoreOf 2 (fsuL0 T L))
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hkO hr.out hr2 hkr1
        exact hknot (hk1 ▸ Subgroup.one_mem _)
    ·
      have hk1ord : orderOf (k ^ (r ^ (j - 1))) = r :=
        orderOf_pow_prime_pow_pred (by omega) hkord
      have hk1M : k ^ (r ^ (j - 1)) ∈ fsuM T L := Subgroup.pow_mem _ hk _
      have hk1A : k ^ (r ^ (j - 1)) ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
        have e : r ^ (j - 1) = r * r ^ (j - 2) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [e, pow_mul]
        exact Subgroup.pow_mem _ hkr _
      exact false_of_mem_centralizer_of_orderOf_eq h37 h38 hfsu hlt hA hr2 hrL hk1M hk1A hk1ord
  ·
    have hkodd : Odd (orderOf k) := by
      rw [hkord]
      exact Odd.pow (hr.out.odd_of_ne_two hr2)
    have hkL : k ∈ fsuML T L :=
      Subgroup.mem_inf.mpr ⟨hk, mem_normalizer_of_odd_orderOf h37 h38 hfsu hlt hk hkodd⟩
    have hk0L : ∀ l ∈ L, ⁅k, l⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G) :=
      fun l hl => hk0 l (le_fsuL0 T L hl)
    have hkpow : k ^ (r ^ j) = 1 := by rw [← hkord]; exact pow_orderOf_eq_one k
    have hU := commutator_mem_Z_of_rElement M hrSL hkL hk0L hkpow
    have hk'L : t * k * t⁻¹ ∈ fsuML T L :=
      conj_mem_fsuML h37 h38 hfsu hlt (le_fsuM T L ht) hkL
    have hk'0L : ∀ l ∈ L, ⁅t * k * t⁻¹, l⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
      intro l hl
      have hl' : t⁻¹ * l * t ∈ fsuL0 T L := by
        have h1 : t⁻¹ ∈ fsuM T L := (fsuM T L).inv_mem (le_fsuM T L ht)
        have h2 := (Subgroup.mem_normalizer_iff.mp h1 l).mp (le_fsuL0 T L hl)
        simpa using h2
      have h3 := conj_mem_centralizer_fsuVM (T := T) (L := L) (I := I) (le_fsuM T L ht)
        (hk0 _ hl')
      have e : t * ⁅k, t⁻¹ * l * t⁆ * t⁻¹ = ⁅t * k * t⁻¹, l⁆ := by
        simp only [commutatorElement_def]
        group
      rwa [e] at h3
    have hkpow' : (t * k * t⁻¹) ^ (r ^ j) = 1 := by
      rw [conj_pow, hkpow]
      group
    have hUt := commutator_mem_Z_of_rElement M hrSL hk'L hk'0L hkpow'
    exact hknot (mem_centralizer_of_trivial_on_U h37 h38 hfsu hlt hA ht htn hk hk0 hU hUt)

theorem lemma3 (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : Ch10.TmpL6_3_2_2_two) (hfsu : FSU G T L I)
    (hlt : L < fsuL0 T L) [IsMulCommutative ↥(fsuVM T L I)] (hA : Concl326A T L I) [Finite K]
    (M : RModel T L I K) {k : G} (hk : k ∈ fsuM T L)
    (hk0 : ∀ l ∈ fsuL0 T L, ⁅k, l⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G)) :
    k ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
  classical
  have hAM : fsuVM T L I ≤ fsuM T L := (h322 G T L I hfsu).1
  have hRed := (h322 G T L I hfsu).2
  let C0 : Subgroup G :=
    { carrier := {x | x ∈ fsuM T L ∧ ∀ l ∈ fsuL0 T L,
        ⁅x, l⁆ ∈ Subgroup.centralizer (fsuVM T L I : Set G)}
      mul_mem' := by
        rintro x y ⟨hx, hx0⟩ ⟨hy, hy0⟩
        refine ⟨(fsuM T L).mul_mem hx hy, fun l hl => ?_⟩
        have e : ⁅x * y, l⁆ = x * ⁅y, l⁆ * x⁻¹ * ⁅x, l⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.mul_mem _ (conj_mem_centralizer_fsuVM hx (hy0 l hl)) (hx0 l hl)
      one_mem' := by
        refine ⟨(fsuM T L).one_mem, fun l hl => ?_⟩
        simp only [commutatorElement_def]
        simpa using Subgroup.one_mem _
      inv_mem' := by
        rintro x ⟨hx, hx0⟩
        refine ⟨(fsuM T L).inv_mem hx, fun l hl => ?_⟩
        have e : ⁅x⁻¹, l⁆ = x⁻¹ * (⁅x, l⁆)⁻¹ * x⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact conj_mem_centralizer_fsuVM ((fsuM T L).inv_mem hx)
          (Subgroup.inv_mem _ (hx0 l hl)) }
  have hC0M : C0 ≤ fsuM T L := fun x hx => hx.1
  have hC0norm : ∀ m ∈ fsuM T L, ∀ x ∈ C0, m * x * m⁻¹ ∈ C0 := by
    rintro m hm x ⟨hx, hx0⟩
    refine ⟨(fsuM T L).mul_mem ((fsuM T L).mul_mem hm hx) ((fsuM T L).inv_mem hm), fun l hl => ?_⟩
    have hl' : m⁻¹ * l * m ∈ fsuL0 T L := by
      have h1 : m⁻¹ ∈ fsuM T L := (fsuM T L).inv_mem hm
      have h2 := (Subgroup.mem_normalizer_iff.mp h1 l).mp hl
      simpa using h2
    have h3 := conj_mem_centralizer_fsuVM (T := T) (L := L) (I := I) hm (hx0 _ hl')
    have e : m * ⁅x, m⁻¹ * l * m⁆ * m⁻¹ = ⁅m * x * m⁻¹, l⁆ := by
      simp only [commutatorElement_def]
      group
    rwa [e] at h3
  have hN : (C0.subgroupOf (fsuM T L)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hC0M]
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hC0norm m hm x hx
    · intro hx
      have := hC0norm m⁻¹ ((fsuM T L).inv_mem hm) _ hx
      simpa [mul_assoc] using this
  have hmain : C0 ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
    refine le_centralizer_of_normal_of_two_power hAM hRed hC0M hN ?_
    intro x hx
    obtain ⟨hVnorm, -, -⟩ := hRed
    set Cx : Subgroup ↥(fsuM T L) :=
      Subgroup.centralizer (((fsuVM T L I).subgroupOf (fsuM T L) : Subgroup ↥(fsuM T L)) :
        Set ↥(fsuM T L)) with hCx
    have hCxmem : ∀ y : ↥(fsuM T L),
        y ∈ Cx ↔ (y : G) ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
      intro y
      rw [hCx, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
      constructor
      · intro h a ha
        have := h ⟨a, hAM ha⟩ (SetLike.mem_coe.mpr (Subgroup.mem_subgroupOf.mpr ha))
        simpa using congrArg Subtype.val this
      · intro h a ha
        have haA : (a : G) ∈ fsuVM T L I := Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp ha)
        exact Subtype.ext (h _ haA)
    let q := QuotientGroup.mk' Cx
    let x' : ↥(fsuM T L) := ⟨x, hC0M hx⟩
    by_cases hpow : ∃ j : ℕ, orderOf (q x') = 2 ^ j
    · obtain ⟨j, hj⟩ := hpow
      refine ⟨j, ?_⟩
      have h1 : (q x') ^ (2 ^ j) = 1 := by rw [← hj]; exact pow_orderOf_eq_one _
      have h2 : x' ^ (2 ^ j) ∈ Cx := by
        have : q (x' ^ (2 ^ j)) = 1 := by rw [map_pow]; exact h1
        exact (QuotientGroup.eq_one_iff _).mp this
      have h3 := (hCxmem _).mp h2
      simpa using h3
    · push Not at hpow
      exfalso
      obtain ⟨r, hrp, hr2, hrd⟩ := exists_odd_prime_dvd_of_ne_two_pow (orderOf_pos (q x')) hpow
      haveI : Fact r.Prime := ⟨hrp⟩
      obtain ⟨k', hk'mem, ⟨j, hj⟩, hk'ord⟩ := exists_pPower_lift q hrd
      have hk'C0 : (k' : G) ∈ C0 := by
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hk'mem
        rw [← hn]
        have : ((x' ^ n : ↥(fsuM T L)) : G) = x ^ n := by simp [x']
        rw [this]
        exact Subgroup.zpow_mem _ hx n
      have hk'ordG : orderOf (k' : G) = r ^ j := by
        rw [Subgroup.orderOf_coe]; exact hj
      have hk'not : (k' : G) ∉ Subgroup.centralizer (fsuVM T L I : Set G) := by
        intro h
        have h1 : k' ∈ Cx := (hCxmem k').mpr h
        have h2 : q k' = 1 := (QuotientGroup.eq_one_iff _).mpr h1
        rw [h2, orderOf_one] at hk'ord
        exact hrp.one_lt.ne hk'ord
      have hk'r : (k' : G) ^ r ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
        have h1 : (q k') ^ r = 1 := by rw [← hk'ord]; exact pow_orderOf_eq_one _
        have h2 : k' ^ r ∈ Cx := by
          have : q (k' ^ r) = 1 := by rw [map_pow]; exact h1
          exact (QuotientGroup.eq_one_iff _).mp this
        have h3 := (hCxmem _).mp h2
        simpa using h3
      exact false_of_rElement h37 h38 hfsu hlt hA M hr2 k'.2 hk'C0.2 hk'ordG hk'not hk'r
  exact hmain ⟨hk, hk0⟩

end CFSG.Quasithin.Vol2.Ch10Reselect
