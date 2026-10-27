module

public import CFSG.RankThree.GF2n.Parrott.A1Section2Lemma11SecondHalf
import all CFSG.RankThree.GF2n.Parrott.A1Section2Lemma11FirstHalf
import all CFSG.RankThree.GF2n.Parrott.A1LocalData
import CFSG.Monster.Existence.StdOdd.Coprime
import TauCeti.Algebra.Group.Subgroup.ZPowers

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

namespace CaseIData

variable {σ : G} {J₀ J₁ : Subgroup G}

private theorem card_sq_eq_one_le (d : CaseIData z σ J₀ J₁) :
    Nat.card {x : ↥J₁ // (x : G) * x = 1} ≤ 72 := by
  classical
  have hz2 := d.orderOf_z
  have hzz : z * z = 1 := by
    rw [← pow_two, ← hz2]
    exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz2
    norm_num at hz2
  have : Fintype ↥J₁ := Fintype.ofFinite _
  have hzc : ∀ x : ↥J₁, z * (x : G) = (x : G) * z := fun x =>
    (Subgroup.mem_centralizer_singleton_iff.mp (J_le_H (d.J₁_le x.2))).symm
  have hsq : ∀ x : ↥J₁, (x : G) * x = 1 ∨ (x : G) * x = z := by
    intro x
    have hc := (CFSG.IsExtraspecial2.pow_two_mem_center d.hyp.extraspecial
      ⟨(x : G), d.J₁_le x.2⟩)
    have hmem : (x : G) * x ∈ Subgroup.zpowers z := by
      rw [← centerIn_J_eq_zpowers_A1 d.hyp, centerIn_eq_map_center]
      exact Subgroup.mem_map.mpr ⟨_, hc, by simp [pow_two]⟩
    exact (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp hmem
  have hcm : ∀ x w : ↥J₁, ⁅(w : G), (x : G)⁆ = 1 ∨ ⁅(w : G), (x : G)⁆ = z := fun x w =>
    (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp
      (d.comm_mem_zpowers (d.J₁_le w.2) (d.J₁_le x.2))
  let ν : G → ℤ := fun y => if y = 1 then 1 else -1
  have hν1 : ν 1 = 1 := by simp [ν]
  have hνz : ν z = -1 := by simp [ν, hz1]
  have hν : ∀ a b : G, (a = 1 ∨ a = z) → (b = 1 ∨ b = z) → ν (a * b) = ν a * ν b := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · simp [ν]
    · simp [ν, hz1]
    · simp [ν, hz1]
    · rw [hzz, hν1, hνz]
      norm_num
  let χ : ↥J₁ → ℤ := fun x => ν ((x : G) * x)
  let ε : ↥J₁ → ↥J₁ → ℤ := fun x w => ν ⁅(w : G), (x : G)⁆
  have hχsq : ∀ x : ↥J₁, χ x * χ x = 1 := by
    intro x
    rcases hsq x with h1 | h1 <;> simp [χ, h1, hν1, hνz]
  have hχmul : ∀ x w : ↥J₁, χ (x * w) = χ x * χ w * ε x w := by
    intro x w
    set c : G := ⁅(w : G), (x : G)⁆ with hcdef
    have hcx : c * x = x * c := by
      rcases hcm x w with h1 | h1
      · rw [← hcdef] at h1
        rw [h1, one_mul, mul_one]
      · rw [← hcdef] at h1
        rw [h1]
        exact hzc x
    have hwx : (w : G) * x = c * x * w := by
      rw [hcdef, commutatorElement_def]
      group
    have e : ((x * w : ↥J₁) : G) * ((x * w : ↥J₁) : G) = c * ((x : G) * x) * ((w : G) * w) := by
      simp only [Subgroup.coe_mul]
      calc (x : G) * w * (x * w) = x * ((w : G) * x) * w := by group
        _ = x * (c * x * w) * w := by rw [hwx]
        _ = (x * c) * x * ((w : G) * w) := by group
        _ = (c * x) * x * ((w : G) * w) := by rw [hcx]
        _ = c * ((x : G) * x) * ((w : G) * w) := by group
    have hc' : c * ((x : G) * x) = 1 ∨ c * ((x : G) * x) = z := by
      rcases hcm x w with h1 | h1 <;> rcases hsq x with h2 | h2 <;>
        simp only [← hcdef] at h1 <;> simp [h1, h2, hzz]
    show ν (((x * w : ↥J₁) : G) * ((x * w : ↥J₁) : G)) =
      ν ((x : G) * x) * ν ((w : G) * w) * ν c
    rw [e, hν _ _ hc' (hsq w), hν _ _ (hcm x w) (hsq x)]
    ring
  have hεmul : ∀ x y w : ↥J₁, ε (x * y) w = ε x w * ε y w := by
    intro x y w
    have hcy : (x : G) * ⁅(w : G), (y : G)⁆ * (x : G)⁻¹ = ⁅(w : G), (y : G)⁆ := by
      rcases hcm y w with h1 | h1
      · rw [h1, mul_one, mul_inv_cancel]
      · rw [h1, ← hzc x, mul_inv_cancel_right]
    show ν ⁅(w : G), ((x * y : ↥J₁) : G)⁆ = ν ⁅(w : G), (x : G)⁆ * ν ⁅(w : G), (y : G)⁆
    rw [Subgroup.coe_mul, commutatorElement_mul_right', hcy, hν _ _ (hcm x w) (hcm y w)]
  have hinner : ∀ w : ↥J₁, (∑ x : ↥J₁, ε x w) =
      if (w : G) ∈ Subgroup.zpowers z then 128 else 0 := by
    intro w
    split_ifs with hw
    · have h1 : ∀ x : ↥J₁, ε x w = 1 := by
        intro x
        have hc : ⁅(w : G), (x : G)⁆ = 1 := by
          rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp hw with h1 | h1
          · rw [h1, commutatorElement_one_left]
          · rw [h1, commutatorElement_eq_one_iff_mul_comm]
            exact hzc x
        simp [ε, hc, hν1]
      rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_const, Finset.card_univ,
        ← Nat.card_eq_fintype_card, d.card₁]
      norm_num
    · have hnc : ¬ ∀ y : ↥J₁, ⁅(w : G), (y : G)⁆ = 1 := by
        intro hall
        apply hw
        refine d.mem_zpowers_of_commute₀₁ (d.J₁_le w.2) (fun a ha => (d.comm a ha _ w.2))
          (fun b hb => ?_)
        exact (commutatorElement_eq_one_iff_mul_comm.mp (hall ⟨b, hb⟩)).symm
      push Not at hnc
      obtain ⟨y₀, hy₀⟩ := hnc
      have hεy₀ : ε y₀ w = -1 := by
        have h1 : ⁅(w : G), (y₀ : G)⁆ = z := (hcm y₀ w).resolve_left hy₀
        simp [ε, h1, hνz]
      have hsum : (∑ x : ↥J₁, ε x w) = ∑ x : ↥J₁, ε (x * y₀) w :=
        (Fintype.sum_equiv (Equiv.mulRight y₀) _ _ (fun x => rfl)).symm
      simp only [hεmul, hεy₀, mul_neg, mul_one, Finset.sum_neg_distrib] at hsum
      linarith
  have hS : (∑ x : ↥J₁, χ x) * (∑ x : ↥J₁, χ x) = 256 := by
    rw [Finset.sum_mul_sum]
    have h1 : ∀ x : ↥J₁, (∑ y : ↥J₁, χ x * χ y) = ∑ w : ↥J₁, χ w * ε x w := by
      intro x
      rw [← Fintype.sum_equiv (Equiv.mulLeft x) (fun w => χ x * χ (x * w)) _ (fun w => rfl)]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hχmul]
      calc χ x * (χ x * χ w * ε x w) = (χ x * χ x) * (χ w * ε x w) := by ring
        _ = χ w * ε x w := by rw [hχsq, one_mul]
    rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_comm]
    have h2 : ∀ w : ↥J₁, (∑ x : ↥J₁, χ w * ε x w) =
        if (w : G) ∈ Subgroup.zpowers z then 128 else 0 := by
      intro w
      rw [← Finset.mul_sum, hinner w]
      split_ifs with hw
      · rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp hw with h1 | h1 <;>
          simp [χ, h1, hzz, hν1]
      · simp
    rw [Finset.sum_congr rfl fun w _ => h2 w, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter fun w : ↥J₁ => (w : G) ∈ Subgroup.zpowers z).card = 2 := by
      rw [← Fintype.card_subtype]
      have e : {w : ↥J₁ // (w : G) ∈ Subgroup.zpowers z} ≃ ↥(Subgroup.zpowers z) :=
        { toFun := fun w => ⟨w.1, w.2⟩
          invFun := fun w => ⟨⟨w.1, d.zpowers_le₁ w.2⟩, w.2⟩
          left_inv := fun w => rfl
          right_inv := fun w => rfl }
      rw [← Nat.card_eq_fintype_card, Nat.card_congr e, Nat.card_zpowers, hz2]
    rw [hcard]
    norm_num
  have hSval : (∑ x : ↥J₁, χ x) =
      2 * ((Finset.univ.filter fun x : ↥J₁ => (x : G) * x = 1).card : ℤ) - 128 := by
    have hχ : ∀ x : ↥J₁, χ x = if (x : G) * x = 1 then 1 else -1 := fun x => rfl
    rw [Finset.sum_congr rfl fun x _ => hχ x, Finset.sum_ite, Finset.sum_const,
      Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ↥J₁))
      (p := fun x : ↥J₁ => (x : G) * x = 1)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, d.card₁] at hc
    omega
  rw [hSval] at hS
  set N : ℤ := ((Finset.univ.filter fun x : ↥J₁ => (x : G) * x = 1).card : ℤ) with hN
  have hN72 : N ≤ 72 := by nlinarith
  have hcardN : Nat.card {x : ↥J₁ // (x : G) * x = 1} =
      (Finset.univ.filter fun x : ↥J₁ => (x : G) * x = 1).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcardN]
  omega

private theorem relIndex_le_seventy (d : CaseIData z σ J₀ J₁) {j : G} (hj1 : j ∈ J₁)
    (hjj : j * j = 1) (hjz : j ∉ Subgroup.zpowers z) :
    (H z ⊓ Subgroup.centralizer ({j} : Set G)).relIndex (H z) ≤ 70 := by
  classical
  have hz2 := d.orderOf_z
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz2
    norm_num at hz2
  have hzz : z * z = 1 := by
    rw [← pow_two, ← hz2]
    exact pow_orderOf_eq_one z
  set A : Set ↥J₁ := {x | (x : G) * x = 1 ∧ (x : G) ∉ Subgroup.zpowers z} with hA
  set B : Set ↥J₁ := {x | (x : G) * x = 1} with hB
  set T : Set G := Subtype.val '' A with hT
  have hmem : ∀ k ∈ H z, k * j * k⁻¹ ∈ T := by
    intro k hk
    refine ⟨⟨k * j * k⁻¹, d.conj_mem₁ hk hj1⟩, ⟨?_, ?_⟩, rfl⟩
    · show k * j * k⁻¹ * (k * j * k⁻¹) = 1
      calc k * j * k⁻¹ * (k * j * k⁻¹) = k * (j * j) * k⁻¹ := by group
        _ = 1 := by rw [hjj]; group
    · intro hkz
      apply hjz
      have h2 := conj_eq_of_mem_zpowers_z ((H z).inv_mem hk) hkz
      rw [show k⁻¹ * (k * j * k⁻¹) * k⁻¹⁻¹ = j by group] at h2
      rw [h2]
      exact hkz
  have hTA : T.ncard = A.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  have hAB : A.ncard + 2 ≤ B.ncard := by
    set one₁ : ↥J₁ := 1
    set z₁ : ↥J₁ := ⟨z, d.z_mem₁⟩
    have hne : one₁ ≠ z₁ := fun h => hz1 (congrArg Subtype.val h).symm
    have hsub : A ∪ {one₁, z₁} ⊆ B := by
      rintro x (hx | hx | hx)
      · exact hx.1
      · rw [hx]
        show (1 : G) * 1 = 1
        rw [one_mul]
      · rw [hx]
        exact hzz
    have hdisj : Disjoint A {one₁, z₁} := by
      rw [Set.disjoint_left]
      rintro x hx (hx1 | hx1)
      · exact hx.2 (by rw [hx1]; exact Subgroup.one_mem _)
      · exact hx.2 (by rw [hx1]; exact Subgroup.mem_zpowers z)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite B)
    rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.ncard_pair hne] at h1
    exact h1
  have hB72 : B.ncard ≤ 72 := by
    rw [← Nat.card_coe_set_eq]
    exact d.card_sq_eq_one_le
  calc (H z ⊓ Subgroup.centralizer ({j} : Set G)).relIndex (H z) ≤ T.ncard :=
        relIndex_inf_centralizer_le_ncard (Set.toFinite T) hmem
    _ ≤ 70 := by omega

private theorem exists_mul_mod_nine_eq_three {r : ℕ} (hr0 : r % 9 ≠ 0) :
    ∃ e : ℕ, r * e % 9 = 3 := by
  have key : ∀ s : Fin 9, s.val ≠ 0 → ∃ e : Fin 9, s.val * e.val % 9 = 3 := by decide
  obtain ⟨e, he⟩ := key ⟨r % 9, Nat.mod_lt _ (by norm_num)⟩ hr0
  refine ⟨e.val, ?_⟩
  rw [Nat.mul_mod, Nat.mod_eq_of_lt e.isLt]
  exact he

private theorem nine_dvd_relIndex (d : CaseIData z σ J₀ J₁) {ρ : ↥(H z)} (hρ9 : orderOf ρ = 9)
    (hρσ : ((ρ ^ 3 : ↥(H z)) : G) = σ) {j : G} (hj1 : j ∈ J₁)
    (hjz : j ∉ Subgroup.zpowers z) :
    9 ∣ (H z ⊓ Subgroup.centralizer ({j} : Set G)).relIndex (H z) := by
  set C : Subgroup ↥(H z) := (H z ⊓ Subgroup.centralizer ({j} : Set G)).subgroupOf (H z)
    with hC
  have hrel : (H z ⊓ Subgroup.centralizer ({j} : Set G)).relIndex (H z) =
      Nat.card (↥(H z) ⧸ C) := rfl
  have hK9 : Nat.card (Subgroup.zpowers ρ) = 9 := by rw [Nat.card_zpowers, hρ9]
  rw [hrel, ← hK9]
  refine CFSG.Monster.Existence.StdOdd.card_dvd_card_of_free fun q k hk => ?_
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
  rw [Subgroup.smul_def, MulAction.Quotient.smul_mk, QuotientGroup.eq, hC,
    Subgroup.mem_subgroupOf] at hk
  have hmem := (Subgroup.mem_inf.mp hk).2
  rw [Subgroup.mem_centralizer_singleton_iff] at hmem
  simp only [smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv] at hmem
  set κ : G := ((k : ↥(H z)) : G) with hκ
  set γ : G := (c : G) with hγ
  set j' : G := γ * j * γ⁻¹ with hj'
  have hinv : Commute κ⁻¹ j' := by
    have e1 : κ⁻¹ * j' = γ * ((κ * γ)⁻¹ * γ * j) * γ⁻¹ := by rw [hj']; group
    have e2 : j' * κ⁻¹ = γ * (j * ((κ * γ)⁻¹ * γ)) * γ⁻¹ := by rw [hj']; group
    show κ⁻¹ * j' = j' * κ⁻¹
    rw [e1, e2, hmem]
  have hcomm : Commute κ j' := Commute.inv_left_iff.mp hinv
  by_contra hk1
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp k.2
  have hm9 : ¬ (9 : ℤ) ∣ m := by
    intro hdvd
    apply hk1
    have h1 : ρ ^ m = 1 :=
      orderOf_dvd_iff_zpow_eq_one.mp (by rw [hρ9]; exact_mod_cast hdvd)
    exact Subtype.ext (hm.symm.trans h1)
  have hr0 : 0 ≤ m % 9 := Int.emod_nonneg m (by norm_num)
  have hr9 : m % 9 < 9 := Int.emod_lt_of_pos m (by norm_num)
  set r : ℕ := (m % 9).toNat with hr
  have hrz : (r : ℤ) = m % 9 := Int.toNat_of_nonneg hr0
  have hrne : r % 9 ≠ 0 := by
    have hrlt : r < 9 := by omega
    rw [Nat.mod_eq_of_lt hrlt]
    intro hr0'
    apply hm9
    exact Int.dvd_of_emod_eq_zero (by omega)
  obtain ⟨e, he⟩ := exists_mul_mod_nine_eq_three hrne
  have hρm : ρ ^ m = ρ ^ r := by
    rw [← zpow_natCast, hrz, ← zpow_mod_orderOf, hρ9]
    norm_num
  have hpow : ((k : ↥(H z)) ^ e : ↥(H z)) = ρ ^ 3 := by
    rw [← hm, hρm, ← pow_mul, ← pow_mod_orderOf, hρ9, he]
  have hσκ : σ = κ ^ e := by
    rw [← hρσ, ← hpow, hκ, Subgroup.coe_pow]
  have hσj : Commute σ j' := hσκ ▸ hcomm.pow_left e
  have hj'1 : j' ∈ J₁ := d.conj_mem₁ c.2 hj1
  have hj'0 : j' ∈ J₀ := by
    rw [d.J₀_eq]
    exact mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hσj.eq.symm, d.J₁_le hj'1⟩
  have hj'z : j' ∈ Subgroup.zpowers z := d.inf ▸ Subgroup.mem_inf.mpr ⟨hj'0, hj'1⟩
  apply hjz
  have h2 := conj_eq_of_mem_zpowers_z ((H z).inv_mem c.2) hj'z
  rw [show γ⁻¹ * j' * γ⁻¹⁻¹ = j by rw [hj']; group] at h2
  rw [h2]
  exact hj'z

private theorem five_dvd_card_inf_centralizer
    (d : CaseIData z σ J₀ J₁) {ρ : ↥(H z)} (hρ9 : orderOf ρ = 9)
    (hρσ : ((ρ ^ 3 : ↥(H z)) : G) = σ) {j : G} (hj1 : j ∈ J₁) (hj2 : orderOf j = 2)
    (hjz : j ≠ z) : 5 ∣ Nat.card ↥(H z ⊓ Subgroup.centralizer ({j} : Set G)) := by
  have hjzp : j ∉ Subgroup.zpowers z := by
    rw [Subgroup.mem_zpowers_iff_of_orderOf_eq_two d.orderOf_z]
    rintro (h1 | h1)
    · rw [h1, orderOf_one] at hj2
      norm_num at hj2
    · exact hjz h1
  have hjj : j * j = 1 := by
    rw [← pow_two, ← hj2]
    exact pow_orderOf_eq_one j
  have hF2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJp : IsPGroup 2 (J z) := IsPGroup.of_card (n := 9) (card_J_A1 d.hyp)
  have hJy : ¬ J z ≤ Subgroup.centralizer ({j} : Set G) := by
    intro hle
    exact hjzp (d.mem_zpowers_of_commute (d.J₁_le hj1) fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hy))
  have h9 := d.nine_dvd_relIndex hρ9 hρσ hj1 hjzp
  have h2 : 2 ∣ (H z ⊓ Subgroup.centralizer ({j} : Set G)).relIndex (H z) :=
    CFSG.GroupTheory.dvd_relIndex_inf_centralizer_of_normal_pGroup (p := 2) (H := H z)
      (J := J z) (y := j) J_le_H J_le_normalizer_A hJp hJy
  have h70 := d.relIndex_le_seventy hj1 hjj hjzp
  have hmul := Subgroup.relIndex_mul_card (H z ⊓ Subgroup.centralizer ({j} : Set G)) (H z)
  rw [inf_eq_left.mpr (inf_le_left : H z ⊓ Subgroup.centralizer ({j} : Set G) ≤ H z),
    card_H_A1 d.hyp] at hmul
  have hpos : 0 < (H z ⊓ Subgroup.centralizer ({j} : Set G)).relIndex (H z) := by
    rcases Nat.eq_zero_or_pos ((H z ⊓ Subgroup.centralizer ({j} : Set G)).relIndex (H z)) with
      h0 | h0
    · rw [h0, zero_mul] at hmul
      norm_num at hmul
    · exact h0
  have h5 : ¬ 5 ∣ (H z ⊓ Subgroup.centralizer ({j} : Set G)).relIndex (H z) := by
    intro h5
    omega
  have h5H : 5 ∣ (H z ⊓ Subgroup.centralizer ({j} : Set G)).relIndex (H z) *
      Nat.card ↥(H z ⊓ Subgroup.centralizer ({j} : Set G)) := by
    rw [hmul]
    norm_num
  exact ((Nat.Prime.dvd_mul (by norm_num)).mp h5H).resolve_left h5

end CaseIData

theorem lemma11_A1
    (h : Tim79a.ParrottHypA1 z)
    (heq : CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) =
      CJ z ((s2HP (quotientDataA1 h) : ↥(H z)) : G)) :
    ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j := by
  intro j hjJ hj2 hjz
  by_cases hj1 : j ∈ J z ⊓ Subgroup.centralizer
      (CJ z ((s1HP (quotientDataA1 h) : ↥(H z)) : G) : Set G)
  · refine no_conj_z_eq_of_mem_J1_A1 h heq ?_ hj1 hj2 hjz
    intro i hi hi2 hiz
    have d := caseIData_s1HP h heq
    have hi' : i ∈ ⁅Subgroup.zpowers ((s1HP (quotientDataA1 h) : ↥(H z)) : G), J z⁆ := by
      rw [d.eq_inf_centralizer]
      exact hi
    exact d.five_dvd_card_inf_centralizer (ρ := nineRootHP (quotientDataA1 h))
      (orderOf_nineRootHP _) rfl hi' hi2 hiz
  · exact no_conj_z_eq_of_mem_J_not_mem_J1_A1 h heq hjJ hj2 hj1

end CFSG.RankThree.GF2n.Parrott
