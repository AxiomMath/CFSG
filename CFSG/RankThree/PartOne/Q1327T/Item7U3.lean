module

public import CFSG.RankThree.PartOne.Q1327T.Item7U3B
public import CFSG.RankThree.PartOne.Q1327T.Item7UBasic
public import CFSG.RankThree.PartOne.K133.MaxItems
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.Timmesfeld.Orders.Classical
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.RankThree.PartOne.S12.Sec137
public import CFSG.RankThree.PartOne.S12.Sec15FA
public import CFSG.RankThree.PartOne.S12.Sec15Items

public section

namespace CFSG.RankThree.PartOne.Q1327T

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133
  CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryPlane

section Aux

theorem mul_sq_sub_one_lt' {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    a * (a ^ 2 - 1) < b * (b ^ 2 - 1) := by
  have h1 : a ^ 2 < b ^ 2 := Nat.pow_lt_pow_left hab (by norm_num)
  have h2 : a ^ 2 - 1 < b ^ 2 - 1 := by
    have : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
    omega
  calc a * (a ^ 2 - 1) ≤ b * (a ^ 2 - 1) := Nat.mul_le_mul_right _ hab.le
    _ < b * (b ^ 2 - 1) := Nat.mul_lt_mul_of_pos_left h2 (by omega)

theorem eq_of_mul_sq_sub_one_eq' {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : a * (a ^ 2 - 1) = b * (b ^ 2 - 1)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (mul_sq_sub_one_lt' ha hab).ne
  · exact hab
  · exact absurd h.symm (mul_sq_sub_one_lt' hb hab).ne

theorem card_psl2_even {Y : Type} [Group Y] {f : ℕ} (hmod : StatedClassicalModel Y .PSL 2 2 f) :
    Nat.card Y = 2 ^ f * ((2 ^ f) ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hmod

theorem commutator_eq_self_of_perfect {G : Type*} [Group G] {S : Subgroup G}
    (hS : Group.IsPerfect S) : ⁅S, S⁆ = S := by
  have h := congrArg (Subgroup.map S.subtype) (Group.isPerfect_def.1 hS)
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

theorem conj_mem_scalars_iff {K : Type} [Field K] {n : ℕ} (P y : GL (Fin n) K) :
    P * y * P⁻¹ ∈ StatedScalars (Fin n) K ↔ y ∈ StatedScalars (Fin n) K := by
  constructor
  · intro h
    have := (StatedScalars.normal (Fin n) K).conj_mem _ h P⁻¹
    simpa [mul_assoc] using this
  · intro h
    exact (StatedScalars.normal (Fin n) K).conj_mem _ h P

end Aux

section Diag

variable {K : Type} [Field K] {p f n : ℕ}

theorem exists_diag_conj (hU : UnitaryFieldData 2 f K) (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    (E₀ : Subgroup (unitarySU 2 f K n)) (hexp : ∀ x ∈ E₀, x ^ p = 1)
    (hcomm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x) :
    ∃ (P : GL (Fin n) K) (β : unitarySU 2 f K n ≃* unitarySU 2 f K n),
      (∀ x, ((β x : unitarySU 2 f K n) : GL (Fin n) K) = P⁻¹ * x * P) ∧
      ∀ x ∈ E₀, (((β x : unitarySU 2 f K n) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K).IsDiag := by
  classical
  have hle := unitarySU_le_primeFormUnitary (n := n) hU
  set G' : Subgroup (primeFormUnitary hU (idGram K n)) := E₀.map (Subgroup.inclusion hle) with hG'
  have hG'mem : ∀ x ∈ G', ∃ x₀ ∈ E₀, Subgroup.inclusion hle x₀ = x := fun x hx => by
    obtain ⟨x₀, hx₀, hx⟩ := Subgroup.mem_map.mp hx
    exact ⟨x₀, hx₀, hx⟩
  have hGcomm : ∀ x ∈ G', ∀ y ∈ G', x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := hG'mem x hx
    obtain ⟨y₀, hy₀, rfl⟩ := hG'mem y hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact hcomm _ hx₀ _ hy₀
  have hGpow : ∀ x ∈ G', x ^ p = 1 := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hG'mem x hx
    rw [← map_pow, hexp _ hx₀, map_one]
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag hU hp hpq G' hGcomm hGpow
  refine ⟨(P : GL (Fin n) K), (conjSU hU P).symm, fun x => rfl, fun x hx => ?_⟩
  have := hP _ (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  exact this

end Diag

theorem row8U3At_leaf7_two
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    Row8U3At (K133.leaf7 2) := by
  intro Q _ _ p g Ē hX h
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hp5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have hmod : StatedClassicalModel (Q ⧸ Subgroup.center Q) .PSU 3 2 q.exponent := by
    have := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e0
    rw [hq2] at this
    exact this
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := id hmod
  have hf : 1 ≤ q.exponent := q.exponent_pos
  generalize q.exponent = f at hmod hK e hf hadm
  by_cases hpq1 : p ∣ 2 ^ f + 1
  swap
  · exfalso
    have hq1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hpQ : ¬ p ∣ 2 ^ f := fun hd =>
      hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
    have hd2 := two_le_orderOf_neg_of_not_dvd hp hpQ hpq1
    have hrk := pRank_statedProj_statedSU_le_one (n := 3) hp hp2 (by norm_num) hK hpq1
      (Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)))
    have h2 := h.two_le_pRank
    rw [pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e] at h2
    omega
  have hf2 : 2 ≤ f := by
    by_contra hlt
    obtain rfl : f = 1 := by omega
    exact hadm.2.2.2 (by simp)
  have hU : UnitaryFieldData 2 f K := unitaryFieldData_two hK hf
  have hZ : Subgroup.center Q = ⊥ := by
    refine center_eq_bot_of_multiplier hp hGA h.quasisimple h.center_p (t := .PSU) (n := 3)
      (f := f) ⟨hmod.1, Or.inl hmod⟩ fun hdvd => ?_
    rw [card_multiplier_psu_eq (Or.inl ⟨by norm_num, by norm_num⟩)] at hdvd
    have := Nat.le_of_dvd (by norm_num) (hdvd.trans (Nat.gcd_dvd_left 3 _))
    omega
  refine ⟨hZ, fun _ => ?_⟩
  obtain ⟨π, hπ, hπk⟩ := exists_cover_unitary hZ e
  have hscal : ∀ x, π x = 1 ↔ (x : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := fun x => by
    rw [← MonoidHom.mem_ker, hπk, Subgroup.mem_subgroupOf]
  obtain ⟨hker, hpk⟩ := ker_facts hp5 hK π hscal
  obtain ⟨c, hcE, hc1, Kb, x, hKbc, hKbN, hmodKb, hxK, hxo, hgen⟩ := h.conf
  have hKbq := S15K.isQuasisimple_of_model hmodKb
  have hKbp : ⁅Kb, Kb⁆ = Kb := commutator_eq_self_of_perfect hKbq.1
  have hKb1 : Kb ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.mem_bot] at hxK
    rw [hxK, orderOf_one] at hxo
    exact hp.ne_one hxo.symm
  have := h.elem
  obtain ⟨E₀, hE₀, hE₀card, hE₀map⟩ := exists_lift_elementaryAbelian π hp hpk Ē
    (fun y _ => hπ y) h.card
  obtain ⟨ct0, hct0E, hct0⟩ : ∃ ct0 ∈ E₀, π ct0 = c := by
    rw [← hE₀map] at hcE
    obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.1 hcE
    exact ⟨y, hy, hyc⟩
  have hE₀exp : ∀ y ∈ E₀, y ^ p = 1 := fun y hy =>
    elemPow_eq_one_of_isElementaryAbelian (A := E₀) y hy
  have hE₀comm : ∀ y ∈ E₀, ∀ z ∈ E₀, y * z = z * y := fun y hy z hz => by
    have := congrArg Subtype.val ((IsMulCommutative.is_comm (M := E₀)).comm ⟨y, hy⟩ ⟨z, hz⟩)
    simpa using this
  obtain ⟨P, β, hβP, hβ⟩ := exists_diag_conj hU hp hpq1 E₀ hE₀exp hE₀comm
  let π₂ : StatedSU 3 (2 ^ f) K →* Q := π.comp β.symm.toMonoidHom
  have hπ₂ : Function.Surjective π₂ := hπ.comp β.symm.surjective
  have hβsymm : ∀ y : StatedSU 3 (2 ^ f) K, ((β.symm y : StatedSU 3 (2 ^ f) K) : GL (Fin 3) K) =
      P * y * P⁻¹ := by
    intro y
    have h1 := hβP (β.symm y)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [h1]
    group
  have hscal₂ : ∀ y, π₂ y = 1 ↔ (y : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := fun y => by
    change π (β.symm y) = 1 ↔ _
    rw [hscal, hβsymm, conj_mem_scalars_iff]
  have hπ₂β : ∀ y, π₂ (β y) = π y := fun y => by
    change π (β.symm (β y)) = π y
    rw [MulEquiv.symm_apply_apply]
  obtain ⟨d, hd⟩ := exists_diagU_of_isDiag (hβ ct0 hct0E)
  have hct : π₂ (β ct0) = c := by rw [hπ₂β, hct0]
  have hcp : (β ct0) ^ p = 1 := by
    rw [← map_pow, hE₀exp ct0 hct0E, map_one]
  have hcard := u3_card_of_diag hp hp5 hf2 hK π₂ hπ₂ hscal₂ hcp (by rw [hct]; exact hc1)
    (d := d) hd.symm (Kb := Kb) (by rw [hct]; exact hKbc) (by rw [hct]; exact hKbN) hKbp hKb1
  rw [card_psl2_even hmodKb] at hcard
  have hg1 : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  have hf1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h2 : 2 ^ g = 2 ^ f := eq_of_mul_sq_sub_one_eq' hg1 hf1 hcard
  have hfg : f = g := (Nat.pow_right_injective (le_refl 2) h2).symm
  rw [← hfg]
  let ce : Q ≃* (Q ⧸ Subgroup.center Q) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact CFSG.RankThree.PartOne.statedClassicalModel_congr ce hmod

end CFSG.RankThree.PartOne.Q1327T
