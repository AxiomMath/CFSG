module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5AbsFixA
import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

namespace CFSG.Quasithin.Stroth.G5

open Subgroup CFSG.Quasithin.OperatorJH

open scoped commutatorElement

variable {G : Type} [Group G] {n : ℕ}

namespace Conf

variable [Finite G] (c : Conf G n)

private theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨2 ^ m - 1, ?_⟩
  have h : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  omega

private theorem odd_card_of_le_H {R : Subgroup G} (hR : R ≤ c.H) : Odd (Nat.card R) := by
  have hn : 1 ≤ n := by have := c.three_le; omega
  have hoddN : Odd (2 ^ n - 1) := odd_two_pow_sub_one hn
  have hcent : zpowers c.d₁ ≤ Subgroup.centralizer (zpowers c.d₂ : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← hk]
    exact (c.commute.zpow_right k).eq.symm
  have hAB : zpowers c.d₁ ≤ Subgroup.normalizer (zpowers c.d₂ : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hcardB : Nat.card (zpowers c.d₂) = 2 ^ n - 1 := by
    rw [Nat.card_zpowers, c.orderOf₂]
  have hcardA : Nat.card (zpowers c.d₁) = 2 ^ n - 1 := by
    rw [Nat.card_zpowers, c.orderOf₁]
  have hrel : (zpowers c.d₁).relIndex (zpowers c.d₁ ⊔ zpowers c.d₂) =
      (zpowers c.d₁ ⊓ zpowers c.d₂).relIndex (zpowers c.d₂) :=
    (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hAB).1
  have hdiv : (zpowers c.d₁ ⊓ zpowers c.d₂).relIndex (zpowers c.d₂) ∣ 2 ^ n - 1 := by
    have h := Subgroup.relIndex_dvd_card (H := zpowers c.d₁ ⊓ zpowers c.d₂) (K := zpowers c.d₂)
    rwa [hcardB] at h
  have hoddrel : Odd ((zpowers c.d₁).relIndex (zpowers c.d₁ ⊔ zpowers c.d₂)) := by
    rw [hrel]
    exact hoddN.of_dvd_nat hdiv
  have hmain : Nat.card (zpowers c.d₁ ⊔ zpowers c.d₂ : Subgroup G) =
      (zpowers c.d₁).relIndex (zpowers c.d₁ ⊔ zpowers c.d₂) * Nat.card (zpowers c.d₁) := by
    have h := Subgroup.relIndex_mul_card (H := zpowers c.d₁)
      (K := zpowers c.d₁ ⊔ zpowers c.d₂)
    rw [inf_eq_left.mpr le_sup_left] at h
    exact h.symm
  have hAodd : Odd (Nat.card (zpowers c.d₁)) := by
    rw [hcardA]
    exact hoddN
  have hoddH : Odd (Nat.card c.H) := by
    rw [c.H_eq, hmain]
    exact hoddrel.mul hAodd
  exact hoddH.of_dvd_nat (Subgroup.card_dvd_of_le hR)

private def trivAct (C S : Subgroup G) : Subgroup G where
  carrier := {r | r ∈ Subgroup.normalizer (S : Set G) ∧ r ∈ Subgroup.normalizer (C : Set G) ∧
    ∀ s ∈ S, r * s * r⁻¹ * s⁻¹ ∈ C}
  one_mem' := by
    refine ⟨Subgroup.one_mem _, Subgroup.one_mem _, ?_⟩
    intro s _
    simpa using C.one_mem
  mul_mem' := by
    intro a b ha hb
    obtain ⟨haS, haC, ha⟩ := ha
    obtain ⟨hbS, hbC, hb⟩ := hb
    refine ⟨Subgroup.mul_mem _ haS hbS, Subgroup.mul_mem _ haC hbC, fun s hs => ?_⟩
    have hbs : b * s * b⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hbS s).mp hs
    have h1 : a * (b * s * b⁻¹) * a⁻¹ * (b * s * b⁻¹)⁻¹ ∈ C := ha _ hbs
    have h2 : b * s * b⁻¹ * s⁻¹ ∈ C := hb s hs
    have e : (a * b) * s * (a * b)⁻¹ * s⁻¹ =
        a * (b * s * b⁻¹) * a⁻¹ * (b * s * b⁻¹)⁻¹ * (b * s * b⁻¹ * s⁻¹) := by
      group
    rw [e]
    exact C.mul_mem h1 h2
  inv_mem' := by
    intro a ha
    obtain ⟨haS, haC, ha⟩ := ha
    refine ⟨Subgroup.inv_mem _ haS, Subgroup.inv_mem _ haC, fun s hs => ?_⟩
    have has : a⁻¹ * s * a ∈ S := by
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haS) s).mp hs
      simpa using h
    have h1 : s * a⁻¹ * s⁻¹ * a ∈ C := by
      have h := ha _ has
      rwa [show a * (a⁻¹ * s * a) * a⁻¹ * (a⁻¹ * s * a)⁻¹ = s * a⁻¹ * s⁻¹ * a by group] at h
    have h2 : a⁻¹ * s * a * s⁻¹ ∈ C := by
      have h3 := C.inv_mem h1
      rwa [show (s * a⁻¹ * s⁻¹ * a)⁻¹ = a⁻¹ * s * a * s⁻¹ by group] at h3
    simpa using h2

private theorem mem_trivAct_of_act {C S : Subgroup G} {φ : Coord n}
    {β : G → GaloisField 2 n} {r : G} (h : IsChiEmb c.ζ c.d₁ c.d₂ C S φ β)
    (hrS : r ∈ Subgroup.normalizer (S : Set G)) (hrC : r ∈ Subgroup.normalizer (C : Set G))
    {k : ℕ} (hsc : ∀ s ∈ S, β (r * s * r⁻¹) = c.ζ ^ k * β s) (hk : c.ζ ^ k = 1) :
    r ∈ trivAct C S := by
  refine ⟨hrS, hrC, fun s hs => ?_⟩
  have hmul := h.map_mul (r * s * r⁻¹) ((Subgroup.mem_normalizer_iff.mp hrS s).mp hs) s⁻¹
    (S.inv_mem hs)
  have hone := h.map_mul s hs s⁻¹ (S.inv_mem hs)
  have hbeta1 : β 1 = 0 := by
    have h1 := h.map_mul 1 S.one_mem 1 S.one_mem
    rw [mul_one] at h1
    exact left_eq_add.mp h1
  have hzero : β ((r * s * r⁻¹) * s⁻¹) = 0 := by
    rw [hmul, hsc s hs, hk, one_mul, ← hone, mul_inv_cancel, hbeta1]
  exact (h.eq_zero_iff _ (S.mul_mem ((Subgroup.mem_normalizer_iff.mp hrS s).mp hs)
    (S.inv_mem hs))).mp hzero

private theorem trivAct_apply {C S : Subgroup G} {r : G} (h : r ∈ trivAct C S) :
    ∀ s ∈ S, r * s * r⁻¹ * s⁻¹ ∈ C := fun s hs => h.2.2 s hs

private theorem zeta_pow_val_eq_one_iff (hn : n ≠ 0) {x : ZMod (2 ^ n - 1)} :
    c.ζ ^ x.val = 1 ↔ x = 0 := by
  have hN : 2 ^ n - 1 ≠ 0 := by
    have := Nat.one_lt_two_pow hn
    omega
  constructor
  · intro hx
    have hdvd : 2 ^ n - 1 ∣ x.val := by
      have h := orderOf_dvd_iff_pow_eq_one.mpr hx
      rwa [c.orderOf_ζ] at h
    haveI : NeZero (2 ^ n - 1) := ⟨hN⟩
    have hlt : x.val < 2 ^ n - 1 := ZMod.val_lt x
    exact ZMod.val_eq_zero x |>.mp (Nat.eq_zero_of_dvd_of_lt hdvd hlt)
  · rintro rfl
    simp

private theorem factor_dichotomy {R C S : Subgroup G} {φ : Coord n}
    {β : G → GaloisField 2 n} (hY : IsYSimple c.H C S) (h2C : IsPGroup 2 C) (hR : R ≤ c.H)
    (hRodd : Odd (Nat.card R)) (h : IsChiEmb c.ζ c.d₁ c.d₂ C S φ β) :
    (R ≤ trivAct C S → (C ⊓ Subgroup.centralizer (R : Set G)).relIndex
        (S ⊓ Subgroup.centralizer (R : Set G)) = 2 ^ (cls φ).card) ∧
      (∀ (r : G), r ∈ R → ∀ k : ℕ, (∀ s ∈ S, β (r * s * r⁻¹) = c.ζ ^ k * β s) →
        c.ζ ^ k ≠ 1 → (C ⊓ Subgroup.centralizer (R : Set G)).relIndex
          (S ⊓ Subgroup.centralizer (R : Set G)) = 1) := by
  have hn : n ≠ 0 := by have := c.three_le; omega
  have hCS : C ≤ S := hY.1.le
  have hSC : S ≤ Subgroup.normalizer (C : Set G) := hY.2.1
  have hRC : R ≤ Subgroup.normalizer (C : Set G) := hR.trans hY.2.2.1
  constructor
  · intro htriv
    have htriv' : ∀ r ∈ R, ∀ s ∈ S, r * s * r⁻¹ * s⁻¹ ∈ C :=
      fun r hr => trivAct_apply (htriv hr)
    have hN : (C.subgroupOf S).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hCS).mpr hSC
    have hsolv : Group.IsSolvable ↥C := @IsNilpotent.to_isSolvable ↥C _ h2C.isNilpotent
    obtain ⟨m, hm⟩ := h2C.exists_card_eq
    have hcop : Nat.Coprime (Nat.card C) (Nat.card R) := by
      rw [hm]
      exact (Nat.coprime_two_left.mpr hRodd).pow_left m
    have hcover : ∀ x ∈ S, ∃ y ∈ S ⊓ Subgroup.centralizer (R : Set G), x⁻¹ * y ∈ C := by
      intro x hx
      have hcomm : ∀ r ∈ R, ⁅x, r⁆ ∈ C := by
        intro r hr
        have hc : r * x⁻¹ * r⁻¹ * x ∈ C := by
          simpa using htriv' r hr x⁻¹ (S.inv_mem hx)
        have e : ⁅x, r⁆ = x * (r * x⁻¹ * r⁻¹ * x) * x⁻¹ := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hSC hx) (r * x⁻¹ * r⁻¹ * x)).mp hc
      obtain ⟨y, hyS, hycom, hxy⟩ :=
        CFSG.GroupTheory.exists_mem_centralizer_of_commutator_mem hCS hN hRC hsolv hcop hx hcomm
      exact ⟨y, ⟨hyS, Subgroup.mem_centralizer_iff.mpr fun r hr => (hycom r hr).symm⟩, hxy⟩
    have hsup : (S ⊓ Subgroup.centralizer (R : Set G)) ⊔ C = S := by
      refine le_antisymm (sup_le inf_le_left hCS) fun x hx => ?_
      obtain ⟨y, hy, hxy⟩ := hcover x hx
      obtain ⟨c, hc, hxc⟩ : ∃ c ∈ C, x = y * c :=
        ⟨(x⁻¹ * y)⁻¹, C.inv_mem hxy, by group⟩
      rw [hxc]
      exact Subgroup.mul_mem_sup hy hc
    have hinf : (S ⊓ Subgroup.centralizer (R : Set G)) ⊓ C =
        C ⊓ Subgroup.centralizer (R : Set G) := by
      rw [inf_comm, ← inf_assoc, inf_eq_left.mpr hCS]
    have hT : (S ⊓ Subgroup.centralizer (R : Set G)) ≤ Subgroup.normalizer (C : Set G) :=
      inf_le_left.trans hSC
    have hkey := (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hT).2
    rw [hsup, hinf] at hkey
    rw [← hkey]
    exact IsChiEmb.relIndex_eq h hn c.orderOf_ζ (by rwa [← c.H_eq])
  · rintro r hr k hsc hne
    have hle : S ⊓ Subgroup.centralizer (R : Set G) ≤ C ⊓ Subgroup.centralizer (R : Set G) := by
      intro y hy
      obtain ⟨hyS, hyc⟩ := hy
      have hyr : r * y = y * r := (Subgroup.mem_centralizer_iff.mp hyc) r hr
      have hry : r * y * r⁻¹ = y := by rw [hyr, mul_assoc, mul_inv_cancel, mul_one]
      have hby : β y = 0 := by
        have h1 : c.ζ ^ k * β y = β y := by rw [← hsc y hyS, hry]
        have h2 : (c.ζ ^ k - 1) * β y = 0 := by rw [sub_mul, one_mul, h1, sub_self]
        rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd (sub_eq_zero.mp h3) hne
        · exact h3
      exact ⟨(h.eq_zero_iff y hyS).mp hby, hyc⟩
    have heq : S ⊓ Subgroup.centralizer (R : Set G) = C ⊓ Subgroup.centralizer (R : Set G) :=
      le_antisymm hle (inf_le_inf_right _ hCS)
    rw [heq, Subgroup.relIndex_self]

private theorem relIndex_eq_two_pow_sum {R : Subgroup G} {P : Coord n → Prop} [DecidablePred P]
    {C D : Subgroup G} {l : List (Subgroup G)} {μ : Multiset (Coord n)}
    (hD : D ≤ c.Q₁) (hl : IsYSeries c.H C l D)
    (hμ : facMultiset (chiLab c.ζ c.d₁ c.d₂) l D = clsSets μ)
    (hfac : ∀ (C' S : Subgroup G) (φ : Coord n), IsYSimple c.H C' S → C' ≤ c.Q₁ →
      φ ∈ chiLab c.ζ c.d₁ c.d₂ C' S →
      (C' ⊓ centralizer (R : Set G)).relIndex (S ⊓ centralizer (R : Set G)) =
        if P φ then 2 ^ (cls φ).card else 1) :
    (C ⊓ centralizer (R : Set G)).relIndex (D ⊓ centralizer (R : Set G)) =
      2 ^ ((μ.filter P).map (fun φ => (cls φ).card)).sum := by
  have hn : n ≠ 0 := by have := c.three_le; omega
  induction l generalizing C D μ with
  | nil =>
    have hCD : C = D := hl
    have hμ0 : μ = 0 := by
      have h : μ.map (fun φ => (cls φ : Set (Coord n))) = 0 := hμ.symm
      exact Multiset.map_eq_zero.mp h
    subst hCD
    subst hμ0
    rw [Subgroup.relIndex_self]
    simp
  | cons S l ih =>
    obtain ⟨hS, hl'⟩ := hl
    have hmem : chiLab c.ζ c.d₁ c.d₂ S D ∈ clsSets μ := by
      rw [← hμ]
      exact Multiset.mem_cons_self _ _
    obtain ⟨φ, hφμ, hφcls⟩ := Multiset.mem_map.mp hmem
    obtain ⟨μ₁, hμ₁⟩ := Multiset.exists_cons_of_mem hφμ
    have hμ' : facMultiset (chiLab c.ζ c.d₁ c.d₂) l S = clsSets μ₁ := by
      have h := hμ
      rw [hμ₁] at h
      simp only [clsSets, Multiset.map_cons, facMultiset] at h
      rw [← hφcls] at h
      exact (Multiset.cons_inj_right _).mp h
    have hφlab : φ ∈ chiLab c.ζ c.d₁ c.d₂ S D := by
      rw [← hφcls]
      exact mem_cls_self hn φ
    have hle1 : C ⊓ centralizer (R : Set G) ≤ S ⊓ centralizer (R : Set G) :=
      inf_le_inf_right _ hl'.le
    have hle2 : S ⊓ centralizer (R : Set G) ≤ D ⊓ centralizer (R : Set G) :=
      inf_le_inf_right _ hS.1.le
    have hIH := ih (C := C) (D := S) (μ := μ₁) (hS.1.le.trans hD) hl' hμ'
    have hstep := hfac S D φ hS (hS.1.le.trans hD) hφlab
    calc (C ⊓ centralizer (R : Set G)).relIndex (D ⊓ centralizer (R : Set G))
        = (C ⊓ centralizer (R : Set G)).relIndex (S ⊓ centralizer (R : Set G)) *
            (S ⊓ centralizer (R : Set G)).relIndex (D ⊓ centralizer (R : Set G)) :=
          (Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2).symm
      _ = 2 ^ ((μ₁.filter P).map (fun φ => (cls φ).card)).sum *
            (if P φ then 2 ^ (cls φ).card else 1) := by rw [hIH, hstep]
      _ = 2 ^ (((μ₁.filter P).map (fun φ => (cls φ).card)).sum +
            (if P φ then (cls φ).card else 0)) := by
          by_cases hP : P φ
          · rw [if_pos hP, if_pos hP, pow_add]
          · rw [if_neg hP, if_neg hP, mul_one, add_zero]
      _ = 2 ^ ((μ.filter P).map (fun φ => (cls φ).card)).sum := by
          rw [hμ₁]
          have e : ((φ ::ₘ μ₁).filter P).map (fun φ => (cls φ).card) =
              (if P φ then {(cls φ).card} else 0) +
                (μ₁.filter P).map (fun φ => (cls φ).card) := by
            by_cases hP : P φ
            · rw [Multiset.filter_cons_of_pos _ hP, if_pos hP, Multiset.map_cons,
                Multiset.singleton_add]
            · rw [Multiset.filter_cons_of_neg _ hP, if_neg hP, Multiset.zero_add]
          rw [e, Multiset.sum_add]
          by_cases hP : P φ
          · rw [if_pos hP, if_pos hP, Multiset.sum_singleton]
            congr 1
            exact Nat.add_comm _ _
          · rw [if_neg hP, if_neg hP, Multiset.sum_zero, Nat.zero_add, Nat.add_zero]

private theorem eq_two_pow_of_mul {X S T U : ℕ} (h1 : X * 2 ^ T = 2 ^ S) (h2 : S = T + U) :
    X = 2 ^ U := by
  rw [h2, pow_add] at h1
  rw [mul_comm X] at h1
  exact mul_left_cancel₀ (pow_ne_zero T two_ne_zero) h1

private theorem card_Q₁_eq_two_pow_sum {l : List (Subgroup G)} {μ : Multiset (Coord n)}
    (hl : IsYSeries c.H ⊥ l c.Q₁)
    (hμ : facMultiset (chiLab c.ζ c.d₁ c.d₂) l c.Q₁ = clsSets μ) :
    Nat.card c.Q₁ = 2 ^ ((μ.map (fun φ => (cls φ).card)).sum) := by
  have hn : n ≠ 0 := by have := c.three_le; omega
  have htop : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
    ext x
    exact ⟨fun _ => Subgroup.mem_top x, fun _ => (Subgroup.mem_centralizer_iff).mpr fun h hh => by
      rw [Subgroup.mem_bot.mp hh, mul_one, one_mul]⟩
  have hfacBot : ∀ (C' S : Subgroup G) (φ : Coord n), IsYSimple c.H C' S → C' ≤ c.Q₁ →
      φ ∈ chiLab c.ζ c.d₁ c.d₂ C' S →
      (C' ⊓ centralizer ((⊥ : Subgroup G) : Set G)).relIndex
          (S ⊓ centralizer ((⊥ : Subgroup G) : Set G)) =
        if (fun _ : Coord n => True) φ then 2 ^ (cls φ).card else 1 := by
    rintro C' S φ hY hC' ⟨β, hβ⟩
    rw [if_pos trivial, htop, inf_top_eq, inf_top_eq]
    exact IsChiEmb.relIndex_eq hβ hn c.orderOf_ζ (by rwa [← c.H_eq])
  have h := relIndex_eq_two_pow_sum (c := c) (R := ⊥) (P := fun _ : Coord n => True)
    (C := ⊥) (D := c.Q₁) (l := l) (μ := μ) (le_refl _) hl hμ hfacBot
  rw [bot_inf_eq, htop, inf_top_eq, Subgroup.relIndex_bot_left, Multiset.filter_true] at h
  exact h

private theorem sum_filter_add_not (f : Coord n → ℕ) (P : Coord n → Prop) [DecidablePred P]
    (μ : Multiset (Coord n)) :
    ((μ.map f).sum) = ((μ.filter P).map f).sum + ((μ.filter fun φ => ¬ P φ).map f).sum := by
  have h := Multiset.filter_add_not (p := P) μ
  have h2 := congrArg (fun s : Multiset (Coord n) => ((s.map f).sum)) h
  rw [Multiset.map_add, Multiset.sum_add] at h2
  exact h2.symm

theorem four_dvd_card_filter_ne_zero {l : List (Subgroup G)} {μ : Multiset (Coord n)}
    (hl : IsYSeries c.H ⊥ l c.Q₁) (hμ : facMultiset (chiLab c.ζ c.d₁ c.d₂) l c.Q₁ = clsSets μ) :
    4 ∣ (μ.filter fun φ => φ.1 ≠ 0).card := by
  have hn : n ≠ 0 := by have := c.three_le; omega
  have hfacTriv : ∀ (C' S : Subgroup G) (φ : Coord n), IsYSimple c.H C' S → C' ≤ c.Q₁ →
      φ ∈ chiLab c.ζ c.d₁ c.d₂ C' S →
      (C' ⊓ centralizer (zpowers c.d₁ : Set G)).relIndex
          (S ⊓ centralizer (zpowers c.d₁ : Set G)) =
        if (fun φ : Coord n => φ.1 = 0) φ then 2 ^ (cls φ).card else 1 := by
    rintro C' S φ hY hC' ⟨β, hβ⟩
    have h2C : IsPGroup 2 C' := c.isPGroup₁.to_le hC'
    have hR : zpowers c.d₁ ≤ c.H := by rw [c.H_eq]; exact le_sup_left
    have hRodd : Odd (Nat.card (zpowers c.d₁)) := odd_card_of_le_H c hR
    have hdich := factor_dichotomy (c := c) (R := zpowers c.d₁) hY h2C hR hRodd hβ
    have hd1H : c.d₁ ∈ c.H := c.d₁_mem_H
    by_cases h1 : φ.1 = 0
    · rw [if_pos h1]
      refine hdich.1 (Subgroup.zpowers_le.mpr ?_)
      exact mem_trivAct_of_act c hβ (hY.2.2.2.1 hd1H) (hY.2.2.1 hd1H) hβ.conj₁ (by simp [h1])
    · rw [if_neg h1]
      exact hdich.2 c.d₁ (Subgroup.mem_zpowers _) φ.1.val hβ.conj₁
        fun hc => h1 ((zeta_pow_val_eq_one_iff c hn).mp hc)
  have hAll := card_Q₁_eq_two_pow_sum c hl hμ
  have hTriv := relIndex_eq_two_pow_sum (c := c) (R := zpowers c.d₁)
    (P := fun φ : Coord n => φ.1 = 0) (C := ⊥) (D := c.Q₁) (l := l) (μ := μ)
    (le_refl _) hl hμ hfacTriv
  rw [bot_inf_eq, Subgroup.relIndex_bot_left] at hTriv
  have hsplit := sum_filter_add_not (fun φ : Coord n => (cls φ).card)
    (fun φ : Coord n => φ.1 = 0) μ
  have hcard := Subgroup.relIndex_mul_card
    (H := c.Q₁ ⊓ centralizer (zpowers c.d₁ : Set G)) (K := c.Q₁)
  rw [inf_eq_left.mpr inf_le_left] at hcard
  have hX : (c.Q₁ ⊓ centralizer (zpowers c.d₁ : Set G)).relIndex c.Q₁ =
      2 ^ ((μ.filter fun φ : Coord n => φ.1 ≠ 0).map (fun φ => (cls φ).card)).sum := by
    refine eq_two_pow_of_mul ?_ hsplit
    rw [hAll, hTriv] at hcard
    exact hcard
  have hE : ((μ.filter fun φ : Coord n => φ.1 ≠ 0).map (fun φ => (cls φ).card)).sum =
      (μ.filter fun φ : Coord n => φ.1 ≠ 0).card * n := by
    have hconst : ∀ b ∈ (μ.filter fun φ : Coord n => φ.1 ≠ 0).map (fun φ => (cls φ).card),
        b = n := by
      intro b hb
      obtain ⟨φ, hφ, rfl⟩ := Multiset.mem_map.mp hb
      have hφμ : φ ∈ μ := Multiset.mem_of_mem_filter hφ
      have hφ1 : φ.1 ≠ 0 := (Multiset.mem_filter.mp hφ).2
      rcases Conf.fst_eq_zero_or_isUnit c hl hμ φ hφμ with h | h
      · exact absurd h hφ1
      · exact card_cls_of_isUnit hn h
    have hrep := Multiset.eq_replicate_of_mem (a := n) hconst
    rw [Multiset.card_map] at hrep
    rw [hrep, Multiset.sum_replicate]
    simp
  obtain ⟨k₀, hk₀⟩ := c.fixB
  have hpow : (μ.filter fun φ : Coord n => φ.1 ≠ 0).card * n = n * (4 * k₀) := by
    have h : 2 ^ ((μ.filter fun φ : Coord n => φ.1 ≠ 0).card * n) = 2 ^ (n * (4 * k₀)) := by
      rw [← hE, ← hX, hk₀, ← pow_mul]
    exact Nat.pow_right_injective (a := 2) (by norm_num) h
  have hnpos : 0 < n := by have := c.three_le; omega
  refine ⟨k₀, mul_right_cancel₀ hnpos.ne' ?_⟩
  rw [hpow, mul_comm n (4 * k₀)]

private theorem filter_ne_zero_psi (m₀ : ZMod (2 ^ n - 1)) (μ : Multiset (Coord n)) :
    μ.filter (fun φ => φ ≠ 0) =
      μ.filter (fun φ => φ.2 ≠ m₀ * φ.1) + μ.filter (fun φ => φ.1 ≠ 0 ∧ φ.2 = m₀ * φ.1) := by
  induction μ using Multiset.induction_on with
  | empty => simp
  | cons a μ ih =>
    by_cases ha : a = 0
    · subst ha
      have h1 : ¬ ((0 : Coord n) ≠ 0) := by simp
      have h2 : ¬ ((0 : Coord n).2 ≠ m₀ * (0 : Coord n).1) := by simp
      have h3 : ¬ ((0 : Coord n).1 ≠ 0 ∧ (0 : Coord n).2 = m₀ * (0 : Coord n).1) := by simp
      rw [Multiset.filter_cons_of_neg (p := fun φ : Coord n => φ ≠ 0) μ h1,
        Multiset.filter_cons_of_neg (p := fun φ : Coord n => φ.2 ≠ m₀ * φ.1) μ h2,
        Multiset.filter_cons_of_neg (p := fun φ : Coord n => φ.1 ≠ 0 ∧ φ.2 = m₀ * φ.1) μ h3]
      exact ih
    · have ha' : (fun φ : Coord n => φ ≠ 0) a := ha
      by_cases hb : a.2 ≠ m₀ * a.1
      · have h3 : ¬ (a.1 ≠ 0 ∧ a.2 = m₀ * a.1) := fun h => hb h.2
        rw [Multiset.filter_cons_of_pos (p := fun φ : Coord n => φ ≠ 0) μ ha',
          Multiset.filter_cons_of_pos (p := fun φ : Coord n => φ.2 ≠ m₀ * φ.1) μ hb,
          Multiset.filter_cons_of_neg (p := fun φ : Coord n => φ.1 ≠ 0 ∧ φ.2 = m₀ * φ.1) μ h3,
          Multiset.cons_add]
        exact congrArg (a ::ₘ ·) ih
      · have hb' : a.2 = m₀ * a.1 := not_not.mp hb
        have ha1 : a.1 ≠ 0 := by
          intro h
          exact ha (Prod.ext h (by rw [h] at hb'; simpa using hb'))
        rw [Multiset.filter_cons_of_pos (p := fun φ : Coord n => φ ≠ 0) μ ha',
          Multiset.filter_cons_of_neg (p := fun φ : Coord n => φ.2 ≠ m₀ * φ.1) μ hb,
          Multiset.filter_cons_of_pos (p := fun φ : Coord n => φ.1 ≠ 0 ∧ φ.2 = m₀ * φ.1) μ
            ⟨ha1, hb'⟩, Multiset.add_cons]
        exact congrArg (a ::ₘ ·) ih

private theorem sum_filter_psi (m₀ : ZMod (2 ^ n - 1)) (f : Coord n → ℕ)
    (μ : Multiset (Coord n)) :
    ((μ.filter fun φ => φ ≠ 0).map f).sum =
      ((μ.filter fun φ => φ.2 ≠ m₀ * φ.1).map f).sum +
        ((μ.filter fun φ => φ.1 ≠ 0 ∧ φ.2 = m₀ * φ.1).map f).sum := by
  rw [filter_ne_zero_psi, Multiset.map_add, Multiset.sum_add]

theorem four_dvd_card_filter_psi {l : List (Subgroup G)} {μ : Multiset (Coord n)}
    (hl : IsYSeries c.H ⊥ l c.Q₁) (hμ : facMultiset (chiLab c.ζ c.d₁ c.d₂) l c.Q₁ = clsSets μ) :
    4 ∣ (μ.filter fun φ => φ.1 ≠ 0 ∧ φ.2 = c.m₀ * φ.1).card := by
  have hn : n ≠ 0 := by have := c.three_le; omega
  have hN : 2 ^ n - 1 ≠ 0 := by
    have := Nat.one_lt_two_pow hn
    omega
  haveI : Fact (1 < 2 ^ n - 1) := ⟨by
    have h : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by have := c.three_le; omega)
    omega⟩
  haveI : NeZero (2 ^ n - 1) := ⟨hN⟩
  have hgH : c.d₁ ^ (-c.m₀).val * c.d₂ ∈ c.H := by
    rw [c.H_eq]
    exact Subgroup.mul_mem_sup
      ((Subgroup.zpowers c.d₁).pow_mem (Subgroup.mem_zpowers _) _) (Subgroup.mem_zpowers _)
  have hval : ((1 : ZMod (2 ^ n - 1))).val = 1 := ZMod.val_one (2 ^ n - 1)
  have hCHN : centralizer (c.H : Set G) ≤
      centralizer (Subgroup.zpowers (c.d₁ ^ (-c.m₀).val * c.d₂) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    exact hx y (Subgroup.zpowers_le.mpr hgH hy)
  have hfacH : ∀ (C' S : Subgroup G) (φ : Coord n), IsYSimple c.H C' S → C' ≤ c.Q₁ →
      φ ∈ chiLab c.ζ c.d₁ c.d₂ C' S →
      (C' ⊓ centralizer (c.H : Set G)).relIndex (S ⊓ centralizer (c.H : Set G)) =
        if (fun φ : Coord n => φ = 0) φ then 2 ^ (cls φ).card else 1 := by
    rintro C' S φ hY hC' ⟨β, hβ⟩
    have h2C : IsPGroup 2 C' := c.isPGroup₁.to_le hC'
    have hRodd : Odd (Nat.card (c.H : Subgroup G)) := odd_card_of_le_H c le_rfl
    have hdich := factor_dichotomy (c := c) (R := c.H) hY h2C le_rfl hRodd hβ
    have hS1 : c.d₁ ∈ Subgroup.normalizer (S : Set G) := hY.2.2.2.1 c.d₁_mem_H
    have hS2 : c.d₂ ∈ Subgroup.normalizer (S : Set G) := hY.2.2.2.1 c.d₂_mem_H
    have hC1 : c.d₁ ∈ Subgroup.normalizer (C' : Set G) := hY.2.2.1 c.d₁_mem_H
    have hC2 : c.d₂ ∈ Subgroup.normalizer (C' : Set G) := hY.2.2.1 c.d₂_mem_H
    by_cases h0 : φ = 0
    · rw [if_pos h0]
      refine hdich.1 ?_
      rw [c.H_eq]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact mem_trivAct_of_act c hβ hS1 hC1 hβ.conj₁ (by rw [h0]; simp)
      · exact mem_trivAct_of_act c hβ hS2 hC2 hβ.conj₂ (by rw [h0]; simp)
    · rw [if_neg h0]
      by_cases h1 : φ.1 = 0
      · have h2 : φ.2 ≠ 0 := by
          intro h
          exact h0 (Prod.ext h1 h)
        exact hdich.2 c.d₂ c.d₂_mem_H φ.2.val hβ.conj₂
          fun hc => h2 ((zeta_pow_val_eq_one_iff c hn).mp hc)
      · exact hdich.2 c.d₁ c.d₁_mem_H φ.1.val hβ.conj₁
          fun hc => h1 ((zeta_pow_val_eq_one_iff c hn).mp hc)
  have hfacN : ∀ (C' S : Subgroup G) (φ : Coord n), IsYSimple c.H C' S → C' ≤ c.Q₁ →
      φ ∈ chiLab c.ζ c.d₁ c.d₂ C' S →
      (C' ⊓ centralizer (Subgroup.zpowers (c.d₁ ^ (-c.m₀).val * c.d₂) : Set G)).relIndex
          (S ⊓ centralizer (Subgroup.zpowers (c.d₁ ^ (-c.m₀).val * c.d₂) : Set G)) =
        if (fun φ : Coord n => φ.2 = c.m₀ * φ.1) φ then 2 ^ (cls φ).card else 1 := by
    rintro C' S φ hY hC' ⟨β, hβ⟩
    have h2C : IsPGroup 2 C' := c.isPGroup₁.to_le hC'
    have hR : Subgroup.zpowers (c.d₁ ^ (-c.m₀).val * c.d₂) ≤ c.H :=
      Subgroup.zpowers_le.mpr hgH
    have hRodd : Odd (Nat.card (Subgroup.zpowers (c.d₁ ^ (-c.m₀).val * c.d₂))) :=
      odd_card_of_le_H c hR
    have hdich := factor_dichotomy (c := c)
      (R := Subgroup.zpowers (c.d₁ ^ (-c.m₀).val * c.d₂)) hY h2C hR hRodd hβ
    have hS1 : c.d₁ ∈ Subgroup.normalizer (S : Set G) := hY.2.2.2.1 c.d₁_mem_H
    have hS2 : c.d₂ ∈ Subgroup.normalizer (S : Set G) := hY.2.2.2.1 c.d₂_mem_H
    have hC1 : c.d₁ ∈ Subgroup.normalizer (C' : Set G) := hY.2.2.1 c.d₁_mem_H
    have hC2 : c.d₂ ∈ Subgroup.normalizer (C' : Set G) := hY.2.2.1 c.d₂_mem_H
    have hsc := hβ.conj_mul_pow hn c.orderOf_ζ hS1 hS2 (-c.m₀) 1
    have hg : c.d₁ ^ (-c.m₀).val * c.d₂ ^ (1 : ZMod (2 ^ n - 1)).val =
        c.d₁ ^ (-c.m₀).val * c.d₂ := by rw [hval, pow_one]
    have hNS : c.d₁ ^ (-c.m₀).val * c.d₂ ^ (1 : ZMod (2 ^ n - 1)).val ∈
        Subgroup.normalizer (S : Set G) := by
      rw [hval, pow_one]
      exact Subgroup.mul_mem _ ((Subgroup.normalizer (S : Set G)).pow_mem hS1 _) hS2
    have hNC : c.d₁ ^ (-c.m₀).val * c.d₂ ^ (1 : ZMod (2 ^ n - 1)).val ∈
        Subgroup.normalizer (C' : Set G) := by
      rw [hval, pow_one]
      exact Subgroup.mul_mem _ ((Subgroup.normalizer (C' : Set G)).pow_mem hC1 _) hC2
    by_cases hp : φ.2 = c.m₀ * φ.1
    · rw [if_pos hp]
      refine hdich.1 (Subgroup.zpowers_le.mpr ?_)
      rw [← hg]
      refine mem_trivAct_of_act c hβ hNS hNC (fun s hs => (hsc s hs).2) ?_
      have hzero : -c.m₀ * φ.1 + 1 * φ.2 = 0 := by rw [hp]; ring
      rw [hzero, ZMod.val_zero, pow_zero]
    · rw [if_neg hp]
      have hne : -c.m₀ * φ.1 + 1 * φ.2 ≠ 0 := by
        intro h
        apply hp
        linear_combination h
      have hmem : c.d₁ ^ (-c.m₀).val * c.d₂ ^ (1 : ZMod (2 ^ n - 1)).val ∈
          Subgroup.zpowers (c.d₁ ^ (-c.m₀).val * c.d₂) := by
        rw [hg]
        exact Subgroup.mem_zpowers _
      refine hdich.2 _ hmem (-c.m₀ * φ.1 + 1 * φ.2).val (fun s hs => (hsc s hs).2) ?_
      intro hc
      exact hne ((zeta_pow_val_eq_one_iff c hn).mp hc)
  have hcardH := relIndex_eq_two_pow_sum (c := c) (R := c.H) (P := fun φ : Coord n => φ = 0)
    (C := ⊥) (D := c.Q₁) (l := l) (μ := μ) (le_refl _) hl hμ hfacH
  rw [bot_inf_eq, Subgroup.relIndex_bot_left] at hcardH
  have hcardN := relIndex_eq_two_pow_sum (c := c)
    (R := Subgroup.zpowers (c.d₁ ^ (-c.m₀).val * c.d₂))
    (P := fun φ : Coord n => φ.2 = c.m₀ * φ.1) (C := ⊥) (D := c.Q₁) (l := l) (μ := μ)
    (le_refl _) hl hμ hfacN
  rw [bot_inf_eq, Subgroup.relIndex_bot_left] at hcardN
  have hAll := card_Q₁_eq_two_pow_sum c hl hμ
  have hsplitH := sum_filter_add_not (fun φ : Coord n => (cls φ).card) (fun φ : Coord n => φ = 0) μ
  have hsplitN := sum_filter_add_not (fun φ : Coord n => (cls φ).card)
    (fun φ : Coord n => φ.2 = c.m₀ * φ.1) μ
  have hpsi := sum_filter_psi c.m₀ (fun φ : Coord n => (cls φ).card) μ
  have hconst : ∀ b ∈ (μ.filter fun φ : Coord n =>
      φ.1 ≠ 0 ∧ φ.2 = c.m₀ * φ.1).map (fun φ => (cls φ).card), b = n := by
    intro b hb
    obtain ⟨φ, hφ, rfl⟩ := Multiset.mem_map.mp hb
    have hφμ : φ ∈ μ := Multiset.mem_of_mem_filter hφ
    have hφ1 : φ.1 ≠ 0 := (Multiset.mem_filter.mp hφ).2.1
    rcases Conf.fst_eq_zero_or_isUnit c hl hμ φ hφμ with h | h
    · exact absurd h hφ1
    · exact card_cls_of_isUnit hn h
  have hrep := Multiset.eq_replicate_of_mem (a := n) hconst
  rw [Multiset.card_map] at hrep
  have hpsiN : ((μ.filter fun φ : Coord n => φ ≠ 0).map (fun φ => (cls φ).card)).sum =
      ((μ.filter fun φ : Coord n => φ.2 ≠ c.m₀ * φ.1).map (fun φ => (cls φ).card)).sum +
        (μ.filter fun φ : Coord n => φ.1 ≠ 0 ∧ φ.2 = c.m₀ * φ.1).card * n := by
    rw [hpsi, hrep, Multiset.sum_replicate]
    simp
  obtain ⟨k₀, hk₀⟩ := c.fixC
  have hZ : (c.Q₁ ⊓ centralizer (c.H : Set G)).relIndex
      (c.Q₁ ⊓ centralizer (Subgroup.zpowers (c.d₁ ^ (-c.m₀).val * c.d₂) : Set G)) =
      2 ^ (n * (4 * k₀)) := by
    rw [hk₀, ← pow_mul]
  have hZY := Subgroup.relIndex_mul_card
    (H := c.Q₁ ⊓ centralizer (c.H : Set G))
    (K := c.Q₁ ⊓ centralizer (Subgroup.zpowers (c.d₁ ^ (-c.m₀).val * c.d₂) : Set G))
  have hinf : (c.Q₁ ⊓ centralizer (c.H : Set G)) ⊓
      (c.Q₁ ⊓ centralizer (Subgroup.zpowers (c.d₁ ^ (-c.m₀).val * c.d₂) : Set G)) =
      c.Q₁ ⊓ centralizer (c.H : Set G) :=
    inf_eq_left.mpr (inf_le_inf_left _ hCHN)
  rw [hinf] at hZY
  have hStriv : ((μ.filter fun φ : Coord n => φ.2 = c.m₀ * φ.1).map
        (fun φ => (cls φ).card)).sum =
      n * (4 * k₀) + ((μ.filter fun φ : Coord n => φ = 0).map (fun φ => (cls φ).card)).sum := by
    have h : 2 ^ ((μ.filter fun φ : Coord n => φ.2 = c.m₀ * φ.1).map
          (fun φ => (cls φ).card)).sum =
        2 ^ (n * (4 * k₀) + ((μ.filter fun φ : Coord n => φ = 0).map
          (fun φ => (cls φ).card)).sum) := by
      rw [← hcardN, ← hZY, hZ, hcardH, pow_add]
    exact Nat.pow_right_injective (a := 2) (by norm_num) h
  have hSnon : ((μ.filter fun φ : Coord n => φ ≠ 0).map (fun φ => (cls φ).card)).sum =
      n * (4 * k₀) + ((μ.filter fun φ : Coord n => φ.2 ≠ c.m₀ * φ.1).map
        (fun φ => (cls φ).card)).sum := by
    have h1 : ((μ.filter fun φ : Coord n => φ = 0).map (fun φ => (cls φ).card)).sum +
          ((μ.filter fun φ : Coord n => φ ≠ 0).map (fun φ => (cls φ).card)).sum =
        ((μ.filter fun φ : Coord n => φ = 0).map (fun φ => (cls φ).card)).sum +
          (n * (4 * k₀) + ((μ.filter fun φ : Coord n => φ.2 ≠ c.m₀ * φ.1).map
            (fun φ => (cls φ).card)).sum) := by
      calc ((μ.filter fun φ : Coord n => φ = 0).map (fun φ => (cls φ).card)).sum +
            ((μ.filter fun φ : Coord n => φ ≠ 0).map (fun φ => (cls φ).card)).sum
          = (μ.map (fun φ => (cls φ).card)).sum := hsplitH.symm
        _ = ((μ.filter fun φ : Coord n => φ.2 = c.m₀ * φ.1).map
              (fun φ => (cls φ).card)).sum +
            ((μ.filter fun φ : Coord n => φ.2 ≠ c.m₀ * φ.1).map (fun φ => (cls φ).card)).sum :=
              hsplitN
        _ = (n * (4 * k₀) + ((μ.filter fun φ : Coord n => φ = 0).map
              (fun φ => (cls φ).card)).sum) +
            ((μ.filter fun φ : Coord n => φ.2 ≠ c.m₀ * φ.1).map (fun φ => (cls φ).card)).sum := by
              rw [hStriv]
        _ = ((μ.filter fun φ : Coord n => φ = 0).map (fun φ => (cls φ).card)).sum +
            (n * (4 * k₀) + ((μ.filter fun φ : Coord n => φ.2 ≠ c.m₀ * φ.1).map
              (fun φ => (cls φ).card)).sum) := by omega
    exact Nat.add_left_cancel h1
  have hk : (μ.filter fun φ : Coord n => φ.1 ≠ 0 ∧ φ.2 = c.m₀ * φ.1).card * n =
      (4 * k₀) * n := by
    have h2 : ((μ.filter fun φ : Coord n => φ.2 ≠ c.m₀ * φ.1).map
          (fun φ => (cls φ).card)).sum +
          (μ.filter fun φ : Coord n => φ.1 ≠ 0 ∧ φ.2 = c.m₀ * φ.1).card * n =
        ((μ.filter fun φ : Coord n => φ.2 ≠ c.m₀ * φ.1).map (fun φ => (cls φ).card)).sum +
          (4 * k₀) * n := by
      rw [← hpsiN, hSnon, Nat.add_comm (n * (4 * k₀)), Nat.mul_comm (4 * k₀) n]
    exact Nat.add_left_cancel h2
  have hnpos : 0 < n := by have := c.three_le; omega
  exact ⟨k₀, mul_right_cancel₀ hnpos.ne' hk⟩

end Conf

end CFSG.Quasithin.Stroth.G5

end
