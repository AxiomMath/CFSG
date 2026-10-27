module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148CRowTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowAlt
public import CFSG.Quasithin.Background.ONanE68M22
public import CFSG.GH74.GLS.Balance.SolvAPIDefs
public import CFSG.Mathlib.LinearAlgebra.BilinForm.Determinant
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofSteps
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof
public import CFSG.RankThree.PartTwo.Sec11.Item119K
public import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
public import CFSG.Walter.J1Props
public import Certificates.Certificate8166

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.GH74.GLS (pPrimeCoreOf)
open Equiv Equiv.Perm

section Perm

variable {α : Type} [Fintype α] [DecidableEq α]

theorem eq_one_of_card_support_le_three {σ : Perm α} (hs : Perm.sign σ = 1)
    (h3 : ¬ 3 ∣ orderOf σ) (hc : σ.support.card ≤ 3) : σ = 1 := by
  have h1 := card_support_ne_one σ
  rcases (show σ.support.card = 0 ∨ σ.support.card = 2 ∨ σ.support.card = 3 by omega) with
    h | h | h
  · exact support_eq_empty_iff.mp (Finset.card_eq_zero.mp h)
  · exfalso
    rw [(card_support_eq_two.mp h).sign_eq] at hs
    exact absurd hs (by decide)
  · exfalso
    exact h3 (by rw [(card_support_eq_three_iff.mp h).orderOf])

theorem mul_cycleOf_mul_inv {e x : Perm α} (hxe : x * e = e * x) (a : α) :
    x * e.cycleOf a * x⁻¹ = e.cycleOf (x a) := by
  have hsame : ∀ y, e.SameCycle a (x⁻¹ y) ↔ e.SameCycle (x a) y := by
    have hpow : ∀ i : ℤ, x * e ^ i = e ^ i * x := fun i =>
      (Commute.zpow_right (show Commute x e from hxe) i).eq
    intro y
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have := congrArg x hi
      rw [show x (x⁻¹ y) = y from Equiv.apply_symm_apply x y] at this
      rw [← this]
      change (e ^ i * x) a = (x * e ^ i) a
      rw [hpow]
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      rw [← hi]
      change (e ^ i) a = (x⁻¹ * (e ^ i * x)) a
      rw [← hpow, ← mul_assoc, inv_mul_cancel, one_mul]
  ext y
  simp only [Perm.mul_apply]
  rw [cycleOf_apply, cycleOf_apply]
  split_ifs with h1 h2 h2
  · change x (e (x⁻¹ y)) = e y
    have : x (e (x⁻¹ y)) = (x * e) (x⁻¹ y) := rfl
    rw [this, hxe, Perm.mul_apply, show x (x⁻¹ y) = y from Equiv.apply_symm_apply x y]
  · exact absurd ((hsame y).mp h1) h2
  · exact absurd ((hsame y).mpr h2) h1
  · exact Equiv.apply_symm_apply x y

theorem cycleOf_mul_comm (e : Perm α) (a : α) : e.cycleOf a * e = e * e.cycleOf a := by
  ext y
  simp only [Perm.mul_apply]
  rw [cycleOf_apply, cycleOf_apply]
  by_cases h : e.SameCycle a y
  · have h' : e.SameCycle a (e y) := sameCycle_apply_right.mpr h
    rw [if_pos h', if_pos h]
  · have h' : ¬ e.SameCycle a (e y) := fun h'' => h (sameCycle_apply_right.mp h'')
    rw [if_neg h', if_neg h]

theorem isThreeCycle_cycleOf {e : Perm α} (he : e ^ 3 = 1) {a : α} (ha : e a ≠ a) :
    (e.cycleOf a).IsThreeCycle := by
  have hc := isCycle_cycleOf e ha
  have hdvd : orderOf (e.cycleOf a) ∣ 3 :=
    (orderOf_cycleOf_dvd_orderOf e a).trans (orderOf_dvd_of_pow_eq_one he)
  have hne : e.cycleOf a ≠ 1 := fun h => ha (by rw [← cycleOf_apply_self, h, Perm.one_apply])
  rw [← card_support_eq_three_iff, ← hc.orderOf]
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

theorem apply_eq_of_mem_pPrimeCoreOf {e x : Perm α} (he : e ^ 3 = 1)
    (hx : x ∈ pPrimeCoreOf 3 (alternatingGroup α ⊓ Subgroup.centralizer ({e} : Set (Perm α))))
    {a : α} (ha : e a ≠ a) : x a = a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := alternatingGroup α ⊓ Subgroup.centralizer ({e} : Set (Perm α)) with hK
  set N := pPrimeCoreOf 3 K with hN
  have hxK : x ∈ K := Sec14.pPrimeCoreOf_le 3 K hx
  have hxe : x * e = e * x := Subgroup.mem_centralizer_singleton_iff.mp hxK.2
  have hNcop : Nat.Coprime 3 (Nat.card N) := Sec14.coprime_card_pPrimeCoreOf 3 K
  have hord : ∀ y ∈ N, ¬ 3 ∣ orderOf y := fun y hy h3 =>
    absurd (Nat.Coprime.eq_one_of_dvd hNcop (h3.trans (Subgroup.orderOf_dvd_natCard N hy)))
      (by norm_num)
  set c := e.cycleOf a with hc
  have hc3 : c.IsThreeCycle := isThreeCycle_cycleOf he ha
  have hcK : c ∈ K := ⟨hc3.sign, Subgroup.mem_centralizer_singleton_iff.mpr (cycleOf_mul_comm e a)⟩
  have hy : x * c * x⁻¹ * c⁻¹ ∈ N := by
    have : x * c * x⁻¹ * c⁻¹ = x * (c * x⁻¹ * c⁻¹) := by group
    rw [this]
    exact N.mul_mem hx ((Subgroup.mem_normalizer_iff.mp
      (Sec14.le_normalizer_pPrimeCoreOf 3 K hcK) _).mp (N.inv_mem hx))
  rw [mul_cycleOf_mul_inv hxe a] at hy
  have hsame : e.SameCycle a (x a) := by
    by_contra hns
    set c' := e.cycleOf (x a) with hc'
    have hc'3 : c'.IsThreeCycle := by
      refine isThreeCycle_cycleOf he fun h => ?_
      apply ha
      have h1 : x (e a) = x a := by
        rw [show x (e a) = (x * e) a from rfl, hxe, Perm.mul_apply, h]
      exact x.injective h1
    have hdisj : c'.Disjoint c⁻¹ := by
      intro y
      by_contra h
      push Not at h
      have h1 : e.SameCycle (x a) y := by
        by_contra h1
        exact h.1 (by rw [hc', cycleOf_apply, if_neg h1])
      have h2 : e.SameCycle a y := by
        by_contra h2
        apply h.2
        rw [hc, cycleOf_inv, cycleOf_apply, if_neg (fun h3 => h2 (sameCycle_inv.mp h3))]
      exact hns (h2.trans h1.symm)
    have hord3 : orderOf (c' * c⁻¹) = 3 := by
      rw [hdisj.orderOf, hc'3.orderOf, orderOf_inv, hc3.orderOf]
      rfl
    exact hord _ hy (by rw [hord3])
  obtain ⟨i, hi, hia⟩ := hsame.exists_pow_eq'
  have he3 : orderOf e = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one he) with h | h
    · exact absurd (by rw [orderOf_eq_one_iff.mp h, Perm.one_apply]) ha
    · exact h
  have hpow : ∀ m : ℕ, (x ^ m) a = (e ^ (i * m)) a := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hcomm : x * e ^ (i * m) = e ^ (i * m) * x :=
        (Commute.pow_right (show Commute x e from hxe) _).eq
      rw [pow_succ', Perm.mul_apply, ih, show x ((e ^ (i * m)) a) = (x * e ^ (i * m)) a from rfl,
        hcomm, Perm.mul_apply, ← hia, ← Perm.mul_apply, ← pow_add]
      congr 2
  have hxr := hpow (orderOf x)
  rw [pow_orderOf_eq_one, Perm.one_apply] at hxr
  have hx3 : ¬ 3 ∣ orderOf x := hord x hx
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with h0 | h1 | h2
  · rw [h0, pow_zero, Perm.one_apply] at hia
    exact hia.symm
  · exfalso
    subst h1
    have hmod : (1 * orderOf x) % 3 = 1 ∨ (1 * orderOf x) % 3 = 2 := by omega
    have : (e ^ (1 * orderOf x)) a = (e ^ ((1 * orderOf x) % 3)) a := by
      rw [← pow_mod_orderOf, he3]
    rw [this] at hxr
    rcases hmod with h | h
    · rw [h, pow_one] at hxr
      exact ha hxr.symm
    · rw [h] at hxr
      apply ha
      have : (e ^ 3) a = e a := by rw [pow_succ', Perm.mul_apply, ← hxr]
      rw [he, Perm.one_apply] at this
      exact this.symm
  · exfalso
    subst h2
    have hmod : (2 * orderOf x) % 3 = 1 ∨ (2 * orderOf x) % 3 = 2 := by omega
    have : (e ^ (2 * orderOf x)) a = (e ^ ((2 * orderOf x) % 3)) a := by
      rw [← pow_mod_orderOf, he3]
    rw [this] at hxr
    rcases hmod with h | h
    · rw [h, pow_one] at hxr
      exact ha hxr.symm
    · rw [h] at hxr
      apply ha
      have : (e ^ 3) a = e a := by rw [pow_succ', Perm.mul_apply, ← hxr]
      rw [he, Perm.one_apply] at this
      exact this.symm

theorem pPrimeCoreOf_eq_bot_of_card_fix {e : Perm α} (he : e ^ 3 = 1)
    (hf : 5 ≤ (Finset.univ.filter (fun y => e y = y)).card) :
    pPrimeCoreOf 3 (alternatingGroup α ⊓ Subgroup.centralizer ({e} : Set (Perm α))) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T := Finset.univ.filter (fun y => e y = y) with hT
  set K := alternatingGroup α ⊓ Subgroup.centralizer ({e} : Set (Perm α)) with hK
  set N := pPrimeCoreOf 3 K with hN
  set ι : Perm {y // y ∈ T} →* Perm α := ofSubtype with hι
  set KT := (alternatingGroup {y // y ∈ T}).map ι with hKT
  have hmemT : ∀ y, y ∈ T ↔ e y = y := fun y => by simp [hT]
  have hKTK : KT ≤ K := by
    rintro _ ⟨σ, hσ, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · change Perm.sign (ofSubtype σ) = 1
      rw [sign_ofSubtype]
      exact hσ
    · rw [Subgroup.mem_centralizer_singleton_iff]
      ext y
      simp only [Perm.mul_apply]
      by_cases hy : y ∈ T
      · have hey : e y = y := (hmemT y).mp hy
        rw [hey, ofSubtype_apply_of_mem σ hy]
        exact ((hmemT _).mp (σ ⟨y, hy⟩).2).symm
      · have hey : e y ∉ T := by
          intro h
          apply hy
          rw [hmemT] at h ⊢
          exact e.injective h
        change ofSubtype σ (e y) = e (ofSubtype σ y)
        rw [ofSubtype_apply_of_not_mem σ hey, ofSubtype_apply_of_not_mem σ hy]
  have hNKT : N ≤ KT := by
    intro x hx
    have hfix : ∀ y, x y ≠ y → y ∈ T := fun y hy => by
      by_contra h
      exact hy (apply_eq_of_mem_pPrimeCoreOf he hx fun h' => h ((hmemT y).mpr h'))
    have hxK : x ∈ K := Sec14.pPrimeCoreOf_le 3 K hx
    have hxe : x * e = e * x := Subgroup.mem_centralizer_singleton_iff.mp hxK.2
    have h₁ : ∀ y, x y ∈ T ↔ y ∈ T := by
      intro y
      rw [hmemT, hmemT]
      constructor
      · intro h
        apply x.injective
        rw [show x (e y) = (x * e) y from rfl, hxe, Perm.mul_apply, h]
      · intro h
        rw [show e (x y) = (e * x) y from rfl, ← hxe, Perm.mul_apply, h]
    refine ⟨x.subtypePerm h₁, ?_, ofSubtype_subtypePerm h₁ hfix⟩
    change Perm.sign (x.subtypePerm h₁) = 1
    rw [← sign_ofSubtype, ofSubtype_subtypePerm h₁ hfix]
    exact hxK.1
  have hTcard : Nat.card {y // y ∈ T} = T.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  haveI : IsSimpleGroup (alternatingGroup {y // y ∈ T}) :=
    alternatingGroup.isSimpleGroup (by rw [hTcard]; exact hf)
  have hιinj : Function.Injective ι := ofSubtype_injective
  have eKT : KT ≃* alternatingGroup {y // y ∈ T} :=
    ((alternatingGroup {y // y ∈ T}).equivMapOfInjective ι hιinj).symm
  haveI : IsSimpleGroup KT := eKT.isSimpleGroup
  have h3KT : 3 ∣ Nat.card KT := by
    rw [Nat.card_congr eKT.toEquiv, Nat.card_eq_fintype_card]
    haveI : Nontrivial {y // y ∈ T} := by
      rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_coe]
      omega
    rw [card_alternatingGroup, Fintype.card_coe]
    have h6 : 6 ∣ T.card.factorial :=
      (Nat.factorial_dvd_factorial (show 3 ≤ T.card by omega))
    obtain ⟨k, hk⟩ := h6
    rw [hk, show 6 * k = 2 * (3 * k) by ring, Nat.mul_div_cancel_left _ (by norm_num)]
    exact dvd_mul_right 3 k
  have hnormal : (N.subgroupOf KT).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp
      (Sec14.le_normalizer_pPrimeCoreOf 3 K (hKTK g.2)) _).mp hx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf KT) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hNKT hx⟩ : KT) ∈ N.subgroupOf KT := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  · exfalso
    have hKTN : KT ≤ N := fun y hy => by
      have : (⟨y, hy⟩ : KT) ∈ N.subgroupOf KT := by rw [h]; trivial
      exact Subgroup.mem_subgroupOf.mp this
    have hcop := Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hKTN)
      (Sec14.coprime_card_pPrimeCoreOf 3 K)
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3KT) (by norm_num)

theorem eq_one_of_forall_mem_pPrimeCoreOf (hα : Fintype.card α ≤ 12) {E : Subgroup (Perm α)}
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hE9 : Nat.card E = 9) {x : Perm α}
    (hx : ∀ e ∈ E, e ≠ 1 →
      x ∈ pPrimeCoreOf 3 (alternatingGroup α ⊓ Subgroup.centralizer ({e} : Set (Perm α)))) :
    x = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hx1
  obtain ⟨e₀, he₀E, he₀1⟩ : ∃ e ∈ E, e ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hE1 : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
    rw [hE1, Subgroup.card_bot] at hE9
    omega
  have hx₀ := hx e₀ he₀E he₀1
  have hxA : Perm.sign x = 1 := (Subgroup.mem_inf.mp (Sec14.pPrimeCoreOf_le 3 _ hx₀)).1
  have hx3 : ¬ 3 ∣ orderOf x := fun h3 =>
    absurd (Nat.Coprime.eq_one_of_dvd (Sec14.coprime_card_pPrimeCoreOf 3 _)
      (h3.trans (Subgroup.orderOf_dvd_natCard _ hx₀))) (by norm_num)
  have hsupp : 4 ≤ x.support.card := by
    by_contra h
    exact hx1 (eq_one_of_card_support_le_three hxA hx3 (by omega))
  have hfix : ∀ e ∈ E, e ≠ 1 → ∀ y, e y = y ↔ y ∈ x.support := by
    intro e he he1
    set T := Finset.univ.filter (fun y => e y = y) with hT
    have hsub : x.support ⊆ T := by
      intro y hy
      rw [Perm.mem_support] at hy
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra h
      exact hy (apply_eq_of_mem_pPrimeCoreOf (hE3 e he) (hx e he he1) h)
    have hT4 : T.card ≤ 4 := by
      by_contra h
      have hbot := pPrimeCoreOf_eq_bot_of_card_fix (hE3 e he) (by omega : 5 ≤ T.card)
      have := hx e he he1
      rw [hbot, Subgroup.mem_bot] at this
      exact hx1 this
    have heq : x.support = T := Finset.eq_of_subset_of_card_le hsub (by omega)
    intro y
    rw [heq]
    simp [hT]
  obtain ⟨ω, hω⟩ : ∃ ω, e₀ ω ≠ ω := by
    by_contra h
    push Not at h
    exact he₀1 (Equiv.ext h)
  have hωT : ω ∉ x.support := fun h => hω ((hfix e₀ he₀E he₀1 ω).mpr h)
  haveI : Fintype E := Fintype.ofFinite E
  have hmaps : ∀ g ∈ (Finset.univ : Finset E), (g : Perm α) ω ∈ x.supportᶜ := by
    intro g _
    rw [Finset.mem_compl]
    intro hg
    by_cases hg1 : (g : Perm α) = 1
    · rw [hg1, Perm.one_apply] at hg
      exact hωT hg
    · have h1 : (g : Perm α) ((g : Perm α) ω) = (g : Perm α) ω := (hfix g g.2 hg1 _).mpr hg
      have h2 : (g : Perm α) ω = ω := (g : Perm α).injective h1
      exact hωT ((hfix g g.2 hg1 ω).mp h2)
  have hinj : Set.InjOn (fun g : E => (g : Perm α) ω) (Finset.univ : Finset E) := by
    intro g _ h _ hgh
    simp only at hgh
    by_contra hne
    have hne' : (h : Perm α)⁻¹ * g ≠ 1 := by
      intro h1
      apply hne
      apply Subtype.ext
      exact (inv_mul_eq_one.mp h1).symm
    have hmem : (h : Perm α)⁻¹ * g ∈ E := E.mul_mem (E.inv_mem h.2) g.2
    have hfx : ((h : Perm α)⁻¹ * g) ω = ω := by
      rw [Perm.mul_apply, hgh]
      exact Equiv.symm_apply_apply _ ω
    exact hωT ((hfix _ hmem hne' ω).mp hfx)
  have hle := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hE9, Finset.card_compl] at hle
  omega

end Perm

theorem rowS148_alternatingGroup {n : ℕ} (hn5 : 5 ≤ n) (hn : n ≤ 12) :
    RowS148 (alternatingGroup (Fin n)) := by
  have hcardn : Nat.card (Fin n) = n := Nat.card_eq_fintype_card.trans (Fintype.card_fin n)
  refine rowS148_of_inner (alternatingGroup.center_eq_bot (by omega))
    (RonanK429.not_three_dvd_outer_alternatingGroup hn5) fun E hE hE9 R hR => ?_
  set ι := (alternatingGroup (Fin n)).subtype with hι
  have hιinj : Function.Injective ι := Subtype.val_injective
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  apply hιinj
  rw [map_one]
  refine eq_one_of_forall_mem_pPrimeCoreOf (by rw [Fintype.card_fin]; exact hn) (E := E.map ι)
    ?_ (by rw [Subgroup.card_map_of_injective hιinj, hE9]) ?_
  · rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, hE.2 e he, map_one]
  · rintro _ ⟨e, he, rfl⟩ he1
    have he1' : e ≠ 1 := fun h => he1 (by rw [h, map_one])
    have h1 : ι r ∈ (pPrimeCoreOf 3 (Subgroup.centralizer ({e} : Set (alternatingGroup (Fin n))))).map
        ι := ⟨r, hR e he he1' hr, rfl⟩
    rw [map_pPrimeCoreOf_of_injective ι hιinj, RonanK429H.map_centralizer_singleton ι hιinj e,
      Subgroup.range_subtype, inf_comm] at h1
    exact h1

theorem rowSOf148_alternating {n : ℕ} (hn5 : 5 ≤ n) (hn : n ≤ 12) :
    RowSOf148 (alternatingGroup (Fin n)) :=
  rowSOf148_of_rowS148 (rowS148_alternatingGroup hn5 hn)

end CFSG.RankThree.PartTwo.Sec4.Ronan148C
