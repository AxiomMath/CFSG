module

public import CFSG.Quasithin.Vol2.KGFact1295Par
public import CFSG.Quasithin.Vol2.KGFact1295Ct
public import CFSG.Quasithin.SteinbergCDBinaryLinearAutIndexThree
public import CFSG.LocalAnalysis.SignalizerFunctor.SubgroupProductIndices
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores

public section

namespace CFSG.Quasithin.H13.KG1295

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Vol2Native.L239.L52 CFSG.Quasithin.H13.KG1297

open scoped Pointwise

local notation "SL₅" => SpecialLinearGroup (Fin 5) (ZMod 2)

theorem card_eq_of_modO2 {M : Type} [Group M] [Finite M] {B : Subgroup M}
    (hB : Nonempty (ModO2 B ≃* SpecialLinearGroup (Fin 3) (ZMod 2))) :
    ∃ r : ℕ, Nat.card B = 168 * 2 ^ r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hB
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥B))
  refine ⟨r, ?_⟩
  have h1 : Nat.card B = Nat.card (ModO2 B) * Nat.card (CFSG.pCore 2 ↥B) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card (ModO2 B) = 168 := by
    rw [Nat.card_congr e.toEquiv, card_SL_eq (by norm_num), Nat.card_zmod]
    decide
  rw [h1, h2, hr]

theorem not_nine_dvd (r : ℕ) : ¬ 9 ∣ 168 * 2 ^ r := by
  intro h
  have hc : Nat.Coprime 9 (2 ^ r) := Nat.Coprime.pow_right r (by norm_num)
  have := hc.dvd_of_dvd_mul_right h
  omega

theorem noE9_of_not_dvd {M : Type*} [Group M] [Finite M] {H : Subgroup M}
    (h : ¬ 9 ∣ Nat.card H) : NoE9 H := by
  intro a ha b hb ha3 hb3 hab ha1
  by_contra hba
  obtain ⟨E, hE, -, -, hE9⟩ := exists_elemAbelian_nine ha3 hb3 hab ha1 hba
  apply h
  rw [← hE9]
  refine Subgroup.card_dvd_of_le (hE.trans ((Subgroup.closure_le H).2 ?_))
  rintro x (rfl | rfl)
  · exact ha
  · exact hb

theorem omg10 : omg (1 : Fin 5) 0 (by decide) ^ 3 = 1 ∧ omg (1 : Fin 5) 0 (by decide) ≠ 1 :=
  ⟨by decide, by decide⟩

theorem omg21 : omg (2 : Fin 5) 1 (by decide) ^ 3 = 1 ∧ omg (2 : Fin 5) 1 (by decide) ≠ 1 :=
  ⟨by decide, by decide⟩

theorem omg32 : omg (3 : Fin 5) 2 (by decide) ^ 3 = 1 ∧ omg (3 : Fin 5) 2 (by decide) ≠ 1 :=
  ⟨by decide, by decide⟩

theorem omg43 : omg (4 : Fin 5) 3 (by decide) ^ 3 = 1 ∧ omg (4 : Fin 5) 3 (by decide) ≠ 1 :=
  ⟨by decide, by decide⟩

theorem not_noE9_10_43 {H : Subgroup SL₅} (ha : omg (1 : Fin 5) 0 (by decide) ∈ H)
    (hb : omg (4 : Fin 5) 3 (by decide) ∈ H) : ¬ NoE9 H :=
  not_noE9 ha hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

theorem not_noE9_10_32 {H : Subgroup SL₅} (ha : omg (1 : Fin 5) 0 (by decide) ∈ H)
    (hb : omg (3 : Fin 5) 2 (by decide) ∈ H) : ¬ NoE9 H :=
  not_noE9 ha hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)

theorem not_noE9_21_43 {H : Subgroup SL₅} (ha : omg (2 : Fin 5) 1 (by decide) ∈ H)
    (hb : omg (4 : Fin 5) 3 (by decide) ∈ H) : ¬ NoE9 H :=
  not_noE9 ha hb (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)


theorem classify {B : Subgroup SL₅}
    (hU : unitriangular 5 (ZMod 2) ≤ Subgroup.normalizer (B : Set SL₅)) (hBO : oTwoUpper B = B)
    (hB : Nonempty (ModO2 B ≃* SpecialLinearGroup (Fin 3) (ZMod 2))) :
    ∃ J : Set ℕ, B ⊔ unitriangular 5 (ZMod 2) = flagStabilizer 5 (ZMod 2) J ∧
      B = oTwoUpper (flagStabilizer 5 (ZMod 2) J) ∧ (J = {3, 4} ∨ J = {1, 2} ∨ J = {1, 4}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨J, hJ, hAJ⟩ := exists_eq_flagStabilizer
    (le_sup_right : unitriangular 5 (ZMod 2) ≤ B ⊔ unitriangular 5 (ZMod 2))
  have hpow : ∀ x ∈ B ⊔ unitriangular 5 (ZMod 2), ∃ k : ℕ, x ^ 2 ^ k ∈ B := by
    intro x hx
    have hx' : x ∈ (B : Set SL₅) * (unitriangular 5 (ZMod 2) : Set SL₅) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left B _ hU]
      exact hx
    obtain ⟨b, hb, u, hu, rfl⟩ := Set.mem_mul.1 hx'
    obtain ⟨k, hk⟩ := isPGroup_unitriangular_charTwo (K := ZMod 2) (n := 5) (by norm_num) ⟨u, hu⟩
    obtain ⟨b', hb', e⟩ := CFSG.Quasithin.A4.exists_pow_mul_eq hb (hU hu) (2 ^ k)
    have hu1 : u ^ 2 ^ k = 1 := congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    rw [e, hu1, mul_one]
    exact hb'
  have hBA : B = oTwoUpper (flagStabilizer 5 (ZMod 2) J) := by
    rw [← hAJ]
    exact eq_oTwoUpper_of_pow_mem le_sup_left hpow hBO.symm
  refine ⟨J, hAJ, hBA, ?_⟩
  obtain ⟨r, hr⟩ := card_eq_of_modO2 hB
  have hnoE9 : NoE9 B := noE9_of_not_dvd (by rw [hr]; exact not_nine_dvd r)
  have hmem : ∀ x ∈ flagStabilizer 5 (ZMod 2) J, x ^ 3 = 1 → x ≠ 1 → x ∈ B :=
    fun x hx h3 h1 => hBA ▸ mem_oTwoUpper_of_pow hx Nat.prime_three (by decide) h3 h1
  have e1 : ¬ (1 ∉ J ∧ 4 ∉ J) := fun ⟨h1, h4⟩ =>
    not_noE9_10_43 (hmem (omg (1 : Fin 5) 0 (by decide)) (omg_mem (by decide) h1) omg10.1 omg10.2)
      (hmem (omg (4 : Fin 5) 3 (by decide)) (omg_mem (by decide) h4) omg43.1 omg43.2) hnoE9
  have e2 : ¬ (1 ∉ J ∧ 3 ∉ J) := fun ⟨h1, h3⟩ =>
    not_noE9_10_32 (hmem (omg (1 : Fin 5) 0 (by decide)) (omg_mem (by decide) h1) omg10.1 omg10.2)
      (hmem (omg (3 : Fin 5) 2 (by decide)) (omg_mem (by decide) h3) omg32.1 omg32.2) hnoE9
  have e3 : ¬ (2 ∉ J ∧ 4 ∉ J) := fun ⟨h2, h4⟩ =>
    not_noE9_21_43 (hmem (omg (2 : Fin 5) 1 (by decide)) (omg_mem (by decide) h2) omg21.1 omg21.2)
      (hmem (omg (4 : Fin 5) 3 (by decide)) (omg_mem (by decide) h4) omg43.1 omg43.2) hnoE9
  have h7 : 7 ∣ Nat.card B := by
    rw [hr]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 7 h7
  have hxJ : (x : SL₅) ∈ flagStabilizer 5 (ZMod 2) J := hAJ ▸ Subgroup.mem_sup_left x.2
  have hx7 : orderOf (x : SL₅) = 7 := by rw [Subgroup.orderOf_coe, hx]
  have hbig : (1 ∈ J ∨ 2 ∈ J) → (2 ∈ J ∨ 3 ∈ J) → (3 ∈ J ∨ 4 ∈ J) → False := by
    intro h12 h23 h34
    refine orderOf_ne_of_small (by norm_num) (by norm_num : Nat.Prime 7) (by decide) (k := 2) ?_
      (fun m hm => card_GL_le_two_not_dvd_seven hm) hxJ hx7
    intro a m h _ _ hno
    by_contra hm
    rcases h12 with c1 | c1 <;> rcases h23 with c2 | c2 <;> rcases h34 with c3 | c3 <;>
      (have d1 := hno _ c1; have d2 := hno _ c2; have d3 := hno _ c3; omega)
  have hJeq : ∀ T : Set ℕ, (∀ i, 1 ≤ i → i < 5 → (i ∈ J ↔ i ∈ T)) →
      (∀ i ∈ T, 1 ≤ i ∧ i < 5) → J = T := by
    intro T hT hT'
    ext i
    constructor
    · intro hi
      obtain ⟨hi1, hi5⟩ := hJ i hi
      exact (hT i hi1 hi5).1 hi
    · intro hi
      obtain ⟨hi1, hi5⟩ := hT' i hi
      exact (hT i hi1 hi5).2 hi
  by_cases h1 : 1 ∈ J
  · by_cases h2 : 2 ∈ J
    · have h3 : 3 ∉ J := fun h3 => hbig (Or.inl h1) (Or.inl h2) (Or.inl h3)
      have h4 : 4 ∉ J := fun h4 => hbig (Or.inl h1) (Or.inl h2) (Or.inr h4)
      refine Or.inr (Or.inl (hJeq _ (fun i hi1 hi5 => ?_) fun i hi => ?_))
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        interval_cases i <;> simp [h1, h2, h3, h4]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
        omega
    · have h4 : 4 ∈ J := by
        by_contra h4
        exact e3 ⟨h2, h4⟩
      have h3 : 3 ∉ J := fun h3 => hbig (Or.inl h1) (Or.inr h3) (Or.inl h3)
      refine Or.inr (Or.inr (hJeq _ (fun i hi1 hi5 => ?_) fun i hi => ?_))
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        interval_cases i <;> simp [h1, h2, h3, h4]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
        omega
  · have h4 : 4 ∈ J := by
      by_contra h4
      exact e1 ⟨h1, h4⟩
    have h3 : 3 ∈ J := by
      by_contra h3
      exact e2 ⟨h1, h3⟩
    have h2 : 2 ∉ J := fun h2 => hbig (Or.inr h2) (Or.inl h2) (Or.inl h3)
    refine Or.inl (hJeq _ (fun i hi1 hi5 => ?_) fun i hi => ?_)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      interval_cases i <;> simp [h1, h2, h3, h4]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      omega

theorem exists_conj_of_normalizes {B : Subgroup SL₅} {J : Set ℕ}
    (hBJ : B ⊔ unitriangular 5 (ZMod 2) = flagStabilizer 5 (ZMod 2) J)
    (hJ : J = {3, 4} ∨ J = {1, 2}) (α : MulAut SL₅)
    (hαU : (unitriangular 5 (ZMod 2)).map α.toMonoidHom = unitriangular 5 (ZMod 2))
    (hαB : B.map α.toMonoidHom = B) : ∃ h : SL₅, α = MulAut.conj h := by
  rcases SteinbergCD.aut_eq_conj_or_conj_mul_graphAut (n := 5) (by norm_num) α with
    ⟨g, hg⟩ | ⟨g, hg⟩
  · exact ⟨g, hg⟩
  · exfalso
    have hmap : ∀ H : Subgroup SL₅, H.map α.toMonoidHom =
        (H.map (BinaryParabolic.graphAut 5).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
      intro H
      rw [hg, Subgroup.map_map]
      rfl
    have hgU : g ∈ unitriangular 5 (ZMod 2) := by
      have h1 := hαU
      rw [hmap, BinaryParabolic.map_graphAut_unitriangular] at h1
      have hg' := CFSG.RankThree.GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq h1
      rwa [normalizer_unitriangular, BinaryParabolic.upperTriangular_eq_unitriangular] at hg'
    have hQ : (flagStabilizer 5 (ZMod 2) J).map α.toMonoidHom = flagStabilizer 5 (ZMod 2) J := by
      rw [← hBJ, Subgroup.map_sup, hαB, hαU]
    have hfix : ∀ I : Set ℕ, (flagStabilizer 5 (ZMod 2) I).map (MulAut.conj g).toMonoidHom =
        flagStabilizer 5 (ZMod 2) I := fun I =>
      CFSG.RankThree.GroupTheory.SteinbergBY.map_conj_eq_of_mem_normalizer
        (Subgroup.le_normalizer (unitriangular_le_flag I hgU))
    rcases hJ with rfl | rfl
    · rw [hmap, map_graphAut_34, hfix] at hQ
      have := subset_of_flagStabilizer_le (I := {3, 4}) (J := {1, 2}) (n := 5) (fun i hi => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi; omega) hQ.le
      have h3 := this (show (3 : ℕ) ∈ ({3, 4} : Set ℕ) by simp)
      simp at h3
    · rw [hmap, map_graphAut_12, hfix] at hQ
      have := subset_of_flagStabilizer_le (I := {1, 2}) (J := {3, 4}) (n := 5) (fun i hi => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi; omega) hQ.le
      have h1 := this (show (1 : ℕ) ∈ ({1, 2} : Set ℕ) by simp)
      simp at h1

end CFSG.Quasithin.H13.KG1295
