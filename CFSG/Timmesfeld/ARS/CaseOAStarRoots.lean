module

public import CFSG.Timmesfeld.ARS.CaseOALevelInv
public import CFSG.Timmesfeld.ARS.CaseOAWeyl
public import CFSG.Timmesfeld.ARS.CaseEStar

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg

namespace CaseOA

section TypeA

variable {m : ℕ}

open CaseE in
theorem starOneAt_A {j : Fin m} (ha : 2 ≤ j.val) (hb : j.val + 3 ≤ m) :
    StarOneAt (CartanMatrix.A m) (SpecialLinear.isFiniteType_A m) j := by
  intro γ hγ hγj
  rw [SpecialLinear.roots_eq] at hγ
  obtain ⟨c, d, -, hγe⟩ := hγ
  obtain ⟨hcj, hdj⟩ := level_of_toStd m hγe hγj
  obtain ⟨a, ha1, ha2⟩ : ∃ a, a < j.val ∧ a ≠ c.val := by
    by_cases hc : c.val = 0
    · exact ⟨1, by omega, by omega⟩
    · exact ⟨0, by omega, fun h => hc h.symm⟩
  obtain ⟨b, hb1, hb2, hb3⟩ : ∃ b, j.val + 2 ≤ b ∧ b ≤ m ∧ b ≠ d.val := by
    by_cases hd : d.val = j.val + 2
    · exact ⟨j.val + 3, by omega, hb, by omega⟩
    · exact ⟨j.val + 2, le_rfl, by omega, fun h => hd h.symm⟩
  obtain ⟨r, l, c', p⟩ := exists_root_A m hγe hcj hdj ha1 hb1 hb2 ha2 hb3
  exact ⟨_, r, l, c', p⟩

theorem eq_of_weylAction_longest_A {w₀ : (coxeterMatrix (SpecialLinear.isFiniteType_A m)).Group}
    (hw₀ : ∀ w, (coxeterMatrix (SpecialLinear.isFiniteType_A m)).toCoxeterSystem.length w ≤
      (coxeterMatrix (SpecialLinear.isFiniteType_A m)).toCoxeterSystem.length w₀)
    {j : Fin m}
    (hjw : weylAction (SpecialLinear.isFiniteType_A m) w₀ (Pi.single j 1) = -Pi.single j 1) :
    m = 2 * j.val + 1 := by
  obtain ⟨π, hπ⟩ := exists_perm_toStd_weylAction w₀
  have hlt : ∀ i (hi : i + 1 ≤ m), (π.symm ⟨i + 1, by omega⟩).val < (π.symm ⟨i, by omega⟩).val :=
    fun i hi => symm_lt_of_longest_A hw₀ hπ ⟨i, by omega⟩
  have hup : ∀ i (hi : i ≤ m), (π.symm ⟨i, by omega⟩).val + i ≤ m := by
    intro i
    induction i with
    | zero => intro _; have := (π.symm 0).isLt; simp only [add_zero]; omega
    | succ i ih =>
      intro hi
      have h1 := hlt i hi
      have h2 := ih (by omega)
      omega
  have hdown : ∀ d (i : ℕ) (hi : i ≤ m), m = i + d → m ≤ (π.symm ⟨i, by omega⟩).val + i := by
    intro d
    induction d with
    | zero => intro i _ hm; omega
    | succ d ih =>
      intro i hi hm
      have h1 := hlt i (by omega)
      have h2 := ih (i + 1) (by omega) (by omega)
      omega
  have hrev : ∀ i (hi : i ≤ m), (π.symm ⟨i, by omega⟩).val + i = m := fun i hi =>
    le_antisymm (hup i hi) (hdown (m - i) i hi (by omega))
  have key := congrArg (SpecialLinear.toStd m) hjw
  rw [hπ, SpecialLinear.toStd_neg] at key
  have e := congrFun key (π.symm j.castSucc)
  simp only [Function.comp_apply, Equiv.apply_symm_apply, Pi.neg_apply,
    SpecialLinear.toStd_single, Pi.sub_apply, Pi.single_eq_same] at e
  have h1 := hrev j.val (by omega)
  have hjc : (j.castSucc : Fin (m + 1)) = ⟨j.val, by omega⟩ := rfl
  rw [hjc] at e
  simp only [Pi.single_apply, Fin.ext_iff, Fin.val_succ] at e
  split_ifs at e <;> omega

end TypeA

section TypeD

variable {n : ℕ}

open CaseE in
theorem starOneAt_D (hn : 6 ≤ n) {j : Fin n} (hj : j.val + 2 = n ∨ j.val + 1 = n) :
    StarOneAt (Spin.cartanD n) (Spin.isFiniteType_cartanD n) j := by
  intro γ hγ hγj
  obtain ⟨c, d, s, t, -, -, -, hγe⟩ :=
    (Set.ext_iff.1 (Spin.rootsD_eq (n := n) (by omega)) γ).1 hγ
  obtain ⟨p, q, hp, hq, hpq, hpc, hpd, hqc, hqd⟩ : ∃ p q : ℕ, p < 4 ∧ q < 4 ∧ p ≠ q ∧
      p ≠ c.val ∧ p ≠ d.val ∧ q ≠ c.val ∧ q ≠ d.val := by
    have hcard : 1 < ((Finset.range 4).filter (fun x => x ≠ c.val ∧ x ≠ d.val)).card := by
      have h1 : (Finset.range 4).filter (fun x => ¬(x ≠ c.val ∧ x ≠ d.val)) ⊆
          {c.val, d.val} := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_range, not_and, not_not] at hx
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases h : x = c.val
        · exact Or.inl h
        · exact Or.inr (hx.2 h)
      have h2 := Finset.card_le_card h1
      have h3 := Finset.card_filter_add_card_filter_not
        (s := Finset.range 4) (fun x => x ≠ c.val ∧ x ≠ d.val)
      have h4 : ({c.val, d.val} : Finset ℕ).card ≤ 2 := Finset.card_le_two
      simp only [Finset.card_range] at h3
      omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 hcard
    simp only [Finset.mem_filter, Finset.mem_range] at hp hq
    exact ⟨p, q, hp.1, hq.1, hpq, hp.2.1, hp.2.2, hq.2.1, hq.2.2⟩
  have hne : (⟨p, by omega⟩ : Fin n) ≠ ⟨q, by omega⟩ := fun e => hpq (congrArg Fin.val e)
  obtain ⟨β, hβ, hβe⟩ := Spin.exists_mem_rootsD_toStdD_eq n hne (Or.inl rfl) (Or.inl rfl)
  refine ⟨β, hβ, ?_, ?_, ?_⟩
  · rcases hj with hj | hj
    · have h1 := sum_sign_toStdD (by omega) β
      rw [hβe, sum_sign_mul_single_add] at h1
      have h2 : j = ⟨n - 2, by omega⟩ := Fin.ext (by simp only; omega)
      rw [h2]
      simp only at h1
      split_ifs at h1 <;> omega
    · have h1 := sum_toStdD (by omega) β
      have h3 : ∑ z : Fin n, Spin.toStdD n β z = 2 := by
        rw [hβe]
        simp [Finset.sum_add_distrib]
      have h2 : j = ⟨n - 1, by omega⟩ := Fin.ext (by simp only; omega)
      rw [h2]
      omega
  · rw [coroot_D_eq_sum (by omega), hβe, sum_single_add_mul]
    rcases hj with hj | hj
    · rw [Spin.toStdD_single_of_lt n (by omega)]
      simp only [Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
    · rw [Spin.toStdD_single_of_not_lt n (by omega) (by omega)]
      simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
      split_ifs <;> omega
  · rw [cartanPair_D (by omega), hβe, hγe, sum_single_add_mul]
    simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega

end TypeD

set_option maxRecDepth 100000 in
theorem starOneAt_E7_cert : ∀ k < Tag.E7.rootCertificate.roots.length,
    Tag.E7.rootCertificate.root k ⟨6, by decide⟩ = 1 →
    ∃ k' < Tag.E7.rootCertificate.roots.length,
      Tag.E7.rootCertificate.root k' ⟨6, by decide⟩ = 1 ∧
      ∑ l, Tag.cartan .E7 ⟨6, by decide⟩ l * Tag.E7.rootCertificate.root k' l = 0 ∧
      ∑ x, Tag.E7.rootCertificate.root k x * ∑ l, Tag.cartan .E7 x l *
        Tag.E7.rootCertificate.root k' l = 0 := by
  decide +kernel

theorem starOneAt_E7 {j : Fin (Tag.rank .E7)} (hj : j.val = 6) :
    StarOneAt (Tag.cartan .E7) Minuscule.isFiniteType_cartan_E7 j := by
  obtain rfl : j = ⟨6, by decide⟩ := Fin.ext hj
  intro γ hγ hγj
  rw [Minuscule.roots_eq, Set.mem_ofPred_eq,
    RootCertificate.isRoot_iff (Tag.rootCertificate_check _)] at hγ
  obtain ⟨k, hk, rfl⟩ := hγ
  obtain ⟨k', hk', h1, h2, h3⟩ := starOneAt_E7_cert k hk hγj
  refine ⟨Tag.E7.rootCertificate.root k', ?_, h1, ?_, ?_⟩
  · rw [Minuscule.roots_eq, Set.mem_ofPred_eq,
      RootCertificate.isRoot_iff (Tag.rootCertificate_check _)]
    exact ⟨k', hk', rfl⟩
  · rw [coroot_apply]
    exact h2
  · simp only [cartanPair, coroot_apply]
    exact h3

@[expose] def rE6 : Fin (Tag.rank .E6) → ℤ := ![1, 0, -1, 0, 1, -1]

theorem dvd_coroot_rE6 : ∀ k : Fin (Tag.rank .E6), (3 : ℤ) ∣ ∑ l, Tag.cartan .E6 k l * rE6 l := by
  decide

theorem dvd_weylAction_sub_E6 (w : (coxeterMatrix Minuscule.isFiniteType_cartan_E6).Group)
    (i : Fin (Tag.rank .E6)) :
    (3 : ℤ) ∣ weylAction Minuscule.isFiniteType_cartan_E6 w rE6 i - rE6 i := by
  obtain ⟨ω, rfl⟩ :=
    (coxeterMatrix Minuscule.isFiniteType_cartan_E6).toCoxeterSystem.wordProd_surjective w
  induction ω generalizing i with
  | nil => simp [CoxeterSystem.wordProd_nil]
  | cons k ω ih =>
    set u := weylAction Minuscule.isFiniteType_cartan_E6
      ((coxeterMatrix Minuscule.isFiniteType_cartan_E6).toCoxeterSystem.wordProd ω) rE6 with hu
    have hc : (3 : ℤ) ∣ coroot (Tag.cartan .E6) k u := by
      have e : coroot (Tag.cartan .E6) k u = ∑ l, Tag.cartan .E6 k l * rE6 l +
          ∑ l, Tag.cartan .E6 k l * (u l - rE6 l) := by
        rw [coroot_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [e]
      exact dvd_add (dvd_coroot_rE6 k) (Finset.dvd_sum fun l _ => dvd_mul_of_dvd_right (ih l) _)
    rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, weylAction_simple,
      reflection_apply_coroot, ← hu]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := ih i
    have e2 : u i - coroot (Tag.cartan .E6) k u * (Pi.single k 1 : Fin (Tag.rank .E6) → ℤ) i -
        rE6 i = (u i - rE6 i) - coroot (Tag.cartan .E6) k u *
          (Pi.single k 1 : Fin (Tag.rank .E6) → ℤ) i := by ring
    rw [e2]
    exact dvd_sub h1 (dvd_mul_of_dvd_left hc _)

theorem weylAction_longest_ne_E6
    (hpd : ((Tag.cartan .E6).map (Int.cast : ℤ → ℚ)).PosDef)
    {w₀ : (coxeterMatrix Minuscule.isFiniteType_cartan_E6).Group}
    (hw₀ : ∀ w, (coxeterMatrix Minuscule.isFiniteType_cartan_E6).toCoxeterSystem.length w ≤
      (coxeterMatrix Minuscule.isFiniteType_cartan_E6).toCoxeterSystem.length w₀)
    {j : Fin (Tag.rank .E6)} (hj : j.val = 0 ∨ j.val = 5) :
    weylAction Minuscule.isFiniteType_cartan_E6 w₀ (Pi.single j 1) ≠ -Pi.single j 1 := by
  intro hjw
  choose σ hσ using exists_weylAction_eq_neg_single Minuscule.isFiniteType_cartan_E6 hpd hw₀
  have hσinj : Function.Injective σ := fun a b e => by
    have h1 : weylAction Minuscule.isFiniteType_cartan_E6 w₀ (Pi.single a 1) =
        weylAction Minuscule.isFiniteType_cartan_E6 w₀ (Pi.single b 1) := by
      rw [hσ a, hσ b, e]
    have h2 := congrFun (weylAction_apply_injective Minuscule.isFiniteType_cartan_E6 w₀ h1) a
    by_contra hab
    simp [Pi.single_eq_of_ne hab] at h2
  have hσj : σ j = j := by
    by_contra hne
    have h1 := congrFun (neg_injective ((hσ j).symm.trans hjw)) j
    rw [Pi.single_eq_of_ne (Ne.symm hne), Pi.single_eq_same] at h1
    exact zero_ne_one h1
  have h1 := dvd_weylAction_sub_E6 w₀⁻¹ j
  rw [weylAction_inv_apply_self_of_neg Minuscule.isFiniteType_cartan_E6 hσ hσinj
    hσj] at h1
  rcases hj with hj | hj
  · obtain rfl : j = ⟨0, by decide⟩ := Fin.ext hj
    revert h1
    decide
  · obtain rfl : j = ⟨5, by decide⟩ := Fin.ext hj
    revert h1
    decide

end CaseOA

end CFSG.Timmesfeld.ARS
