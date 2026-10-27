module

public import CFSG.LocalAnalysis.StandardType.GGHalfEndNodes

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

private theorem ggHalfInnerCommA_one_add_one_f2 : (1 : F2) + 1 = 0 := by
  linear_combination gf2_two

private theorem ggHalfInnerCommA_transvection_mul_self {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : F2) *
      SpecialLinearGroup.transvection hij 1 = 1 := by
  rw [← SpecialLinearGroup.transvection_add, ggHalfInnerCommA_one_add_one_f2]
  exact SpecialLinearGroup.transvection_coeff_zero hij

private theorem ggHalfInnerCommA_transvection_irrel {N : ℕ} {i j : Fin N}
    (h h' : i ≠ j) (c : F2) :
    SpecialLinearGroup.transvection h c = SpecialLinearGroup.transvection h' c :=
  Subtype.ext rfl

private theorem ggHalfInnerCommA_f2_eq_zero_or_one (z : F2) : z = 0 ∨ z = 1 := by
  have hcard : Nat.card F2 = 2 := by
    have := GaloisField.card 2 1 (by omega)
    simpa using this
  by_cases hz : z = 0
  · exact Or.inl hz
  · obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
    exact Or.inr ((huniq z hz).trans (huniq 1 one_ne_zero).symm)

private theorem ggHalfInnerCommA_slOn_commute_of_disjoint {N : ℕ} {S T : Set (Fin N)}
    (hST : Disjoint S T) {x y : SpecialLinearGroup (Fin N) F2}
    (hx : x ∈ slOn N S) (hy : y ∈ slOn N T) : x * y = y * x := by
  induction hx using Subgroup.closure_induction with
  | mem s hs =>
      induction hy using Subgroup.closure_induction with
      | mem t ht =>
          rcases hs with ⟨a, b, hab, c, ha, hb, rfl⟩
          rcases ht with ⟨e, f, hef, d, he, hf, rfl⟩
          have hbe : b ≠ e := by
            intro h
            exact (Set.disjoint_left.mp hST hb (h ▸ he))
          have haf : a ≠ f := by
            intro h
            exact (Set.disjoint_left.mp hST ha (h ▸ hf))
          exact (CFSG.StandardType.commute_transvection_of_ne hab hef hbe haf c d).eq
      | one => rw [mul_one, one_mul]
      | mul u v _ _ ihu ihv =>
          calc s * (u * v) = (s * u) * v := by group
            _ = (u * s) * v := by rw [ihu]
            _ = u * (s * v) := by group
            _ = u * (v * s) := by rw [ihv]
            _ = (u * v) * s := by group
      | inv u _ ihu =>
          exact (show Commute s u from ihu).inv_right.eq
  | one => rw [one_mul, mul_one]
  | mul u v _ _ ihu ihv =>
      calc (u * v) * y = u * (v * y) := by group
        _ = u * (y * v) := by rw [ihv]
        _ = (u * y) * v := by group
        _ = (y * u) * v := by rw [ihu]
        _ = y * (u * v) := by group
  | inv u _ ihu =>
      exact (show Commute u y from ihu).inv_left.eq

private theorem ggHalfInnerCommA_slOn_pair_le_closure (n : ℕ) (k : Fin n) :
    slOn (n + 1) {i : Fin (n + 1) | i = k.castSucc ∨ i = k.succ} ≤
      Subgroup.closure ({omegaBlock n k, weylRep n F2 k} :
        Set (SpecialLinearGroup (Fin (n + 1)) F2)) := by
  set H : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2) :=
    Subgroup.closure ({omegaBlock n k, weylRep n F2 k} :
      Set (SpecialLinearGroup (Fin (n + 1)) F2)) with hH
  let x : SpecialLinearGroup (Fin (n + 1)) F2 :=
    SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1
  let y : SpecialLinearGroup (Fin (n + 1)) F2 :=
    SpecialLinearGroup.transvection
      ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1
  have hxx : x * x = 1 := ggHalfInnerCommA_transvection_mul_self _
  have hyy : y * y = 1 := ggHalfInnerCommA_transvection_mul_self _
  have hw : weylRep n F2 k = x * y * x := by
    rw [weylRep_eq_slPerm,
      slPerm_swap_eq_transvections gf2_two (Fin.castSucc_lt_succ).ne]
  have hω : omegaBlock n k = x * y := by
    rw [omegaBlock, hw]
    calc (x * y * x) * x = x * y * (x * x) := by group
      _ = x * y := by rw [hxx, mul_one]
  have hωH : omegaBlock n k ∈ H := Subgroup.subset_closure (by simp)
  have hwH : weylRep n F2 k ∈ H := Subgroup.subset_closure (by simp)
  have hxH : x ∈ H := by
    have hxeq : x = weylRep n F2 k * omegaBlock n k := by
      rw [hw, hω]
      calc x = x * (y * y) := by rw [hyy, mul_one]
        _ = x * y * y := by group
        _ = x * y * (x * x) * y := by rw [hxx, mul_one]
        _ = (x * y * x) * (x * y) := by group
    rw [hxeq]
    exact H.mul_mem hwH hωH
  have hyH : y ∈ H := by
    have hyeq : y = x * omegaBlock n k := by
      rw [hω]
      calc y = (x * x) * y := by rw [hxx, one_mul]
        _ = x * (x * y) := by group
    rw [hyeq]
    exact H.mul_mem hxH hωH
  change slOn (n + 1) {i : Fin (n + 1) | i = k.castSucc ∨ i = k.succ} ≤ H
  rw [slOn, Subgroup.closure_le]
  rintro t ⟨a, b, hab, c, ha, hb, rfl⟩
  have hc : c = 0 ∨ c = 1 := ggHalfInnerCommA_f2_eq_zero_or_one c
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact absurd (ha.trans hb.symm) hab
  · subst a
    subst b
    rcases hc with rfl | rfl
    · rw [SpecialLinearGroup.transvection_coeff_zero]
      exact H.one_mem
    · have htx : SpecialLinearGroup.transvection hab (1 : F2) = x :=
        ggHalfInnerCommA_transvection_irrel (N := n + 1) (i := k.castSucc)
          (j := k.succ) hab (Fin.castSucc_lt_succ).ne 1
      rw [htx]
      exact hxH
  · subst a
    subst b
    rcases hc with rfl | rfl
    · rw [SpecialLinearGroup.transvection_coeff_zero]
      exact H.one_mem
    · have hty : SpecialLinearGroup.transvection hab (1 : F2) = y :=
        ggHalfInnerCommA_transvection_irrel (N := n + 1) (i := k.succ)
          (j := k.castSucc) hab (Fin.castSucc_lt_succ).ne.symm 1
      rw [hty]
      exact hyH
  · exact absurd (ha.trans hb.symm) hab

private theorem ggHalfInnerCommA_lt_pair_image (m : ℕ) :
    ({i : Fin (m + 1 + 1 + 1) | 2 ≤ i.val ∧ i.val < m + 2} :
        Set (Fin (m + 1 + 1 + 1))) =
      (fun j : Fin (m + 1) => j.succ.succ) '' {j : Fin (m + 1) | j.val < m} := by
  ext i
  constructor
  · rintro ⟨h2, hlt⟩
    exact ⟨⟨i.val - 2, by omega⟩, by simp only [Set.mem_setOf_eq]; omega,
      Fin.ext (by simp only [Fin.val_succ, Fin.val_mk]; omega)⟩
  · rintro ⟨j, hj, rfl⟩
    simp only [Set.mem_setOf_eq, Fin.val_succ] at hj ⊢
    omega

private theorem ggHalfInnerCommA_upper_image (m : ℕ) :
    ({i : Fin (m + 1 + 1 + 1) | i.val < m} :
        Set (Fin (m + 1 + 1 + 1))) =
      (fun j : Fin (m + 1) => j.castSucc.castSucc) '' {j : Fin (m + 1) | j.val < m} := by
  ext i
  constructor
  · intro hi
    have hlt : i.val < m + 1 := Nat.lt_succ_of_lt hi
    exact ⟨⟨i.val, hlt⟩, hi, Fin.ext (by simp only [Fin.val_castSucc, Fin.val_mk])⟩
  · rintro ⟨j, hj, rfl⟩
    simpa only [Set.mem_setOf_eq, Fin.val_castSucc] using hj

private theorem ggHalfInnerCommA_zero_m_image (m : ℕ) :
    ({i : Fin (m + 1 + 1 + 1) | i.val = 0 ∨ i.val = m} :
        Set (Fin (m + 1 + 1 + 1))) =
      (fun j : Fin (m + 1) => j.castSucc.castSucc) ''
        {j : Fin (m + 1) | j.val = 0 ∨ j.val = m} := by
  ext i
  constructor
  · rintro (hi | hi)
    · refine ⟨0, Or.inl rfl, ?_⟩
      apply Fin.ext
      simpa only [Fin.val_castSucc, Fin.val_zero] using hi.symm
    · refine ⟨⟨m, by omega⟩, Or.inr rfl, ?_⟩
      apply Fin.ext
      simpa only [Fin.val_castSucc, Fin.val_mk] using hi.symm
  · rintro ⟨j, hj, rfl⟩
    simp only [Set.mem_setOf_eq, Fin.val_castSucc]
    exact hj

private theorem ggHalfInnerCommA_low_image (m : ℕ) :
    ({i : Fin (m + 1 + 1 + 1) | i.val = 2 ∨ i.val = m + 2} :
        Set (Fin (m + 1 + 1 + 1))) =
      (fun j : Fin (m + 1) => j.succ.succ) ''
        {j : Fin (m + 1) | j.val = 0 ∨ j.val = m} := by
  ext i
  constructor
  · rintro (hi | hi)
    · refine ⟨0, Or.inl rfl, ?_⟩
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_zero]
      omega
    · refine ⟨⟨m, by omega⟩, Or.inr rfl, ?_⟩
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_mk]
      omega
  · rintro ⟨j, hj, rfl⟩
    simp only [Set.mem_setOf_eq, Fin.val_succ]
    rcases hj with hj | hj
    · left; omega
    · right; omega

private theorem ggHalfInnerCommA_tau_image (m : ℕ) (hm : 2 ≤ m) :
    tauPerm m '' ({i : Fin (m + 1 + 1 + 1) | i.val = 0 ∨ i.val = m} :
        Set (Fin (m + 1 + 1 + 1))) =
      {i : Fin (m + 1 + 1 + 1) | i.val = m ∨ i.val = m + 1} := by
  have htau0 : tauPerm m (0 : Fin (m + 1 + 1 + 1)) = (Fin.last (m + 1)).castSucc :=
    tauPerm_apply_zero m
  have htaum : tauPerm m (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) = ⟨m, by omega⟩ := by
    refine tauPerm_apply_of_fixed m ?_ ?_ ?_ ?_
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_zero] at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_one] at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_castSucc] at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_last] at hv
      omega
  ext i
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases hj with hj | hj
    · have hj0 : j = 0 := Fin.ext (by simpa using hj)
      rw [hj0, htau0]
      right
      simp only [Fin.val_castSucc, Fin.val_last]
    · have hjm : j = (⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)) := Fin.ext (by simpa using hj)
      rw [hjm, htaum]
      left
      rfl
  · rintro (hi | hi)
    · refine ⟨(⟨m, by omega⟩ : Fin (m + 1 + 1 + 1)), Or.inr rfl, ?_⟩
      rw [htaum]
      exact Fin.ext (by simpa using hi.symm)
    · refine ⟨0, Or.inl rfl, ?_⟩
      rw [htau0]
      exact Fin.ext (by simpa [Fin.val_castSucc, Fin.val_last] using hi.symm)

private theorem ggHalfInnerCommA_mid_eq_conj {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) (hm : 2 ≤ m) :
    (slOn (m + 1 + 1 + 1) {i | i.val = m ∨ i.val = m + 1}).map φ₂ =
      ((slOn (m + 1 + 1 + 1) {i | i.val = 0 ∨ i.val = m}).map φ₂).map
        (MulAut.conj (hElt φ₂)).toMonoidHom := by
  have hτ := ggHalfInnerCommA_tau_image m hm
  have hmap : (slOn (m + 1 + 1 + 1) {i | i.val = 0 ∨ i.val = m}).map
      (MulAut.conj (slPerm gf2_two (tauPerm m))).toMonoidHom =
      slOn (m + 1 + 1 + 1) {i | i.val = m ∨ i.val = m + 1} := by
    rw [slOn_map_conj_slPerm, hτ]
  calc
    (slOn (m + 1 + 1 + 1) {i | i.val = m ∨ i.val = m + 1}).map φ₂
        = ((slOn (m + 1 + 1 + 1) {i | i.val = 0 ∨ i.val = m}).map
            (MulAut.conj (slPerm gf2_two (tauPerm m))).toMonoidHom).map φ₂ := by
          rw [hmap]
    _ = (slOn (m + 1 + 1 + 1) {i | i.val = 0 ∨ i.val = m}).map
          (φ₂.comp (MulAut.conj (slPerm gf2_two (tauPerm m))).toMonoidHom) :=
          Subgroup.map_map (K := slOn (m + 1 + 1 + 1)
            {i | i.val = 0 ∨ i.val = m}) φ₂
            (MulAut.conj (slPerm gf2_two (tauPerm m))).toMonoidHom
    _ = (slOn (m + 1 + 1 + 1) {i | i.val = 0 ∨ i.val = m}).map
          ((MulAut.conj (hElt φ₂)).toMonoidHom.comp φ₂) := by
          congr 1
          ext t
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            hElt, map_mul, map_inv]
    _ = ((slOn (m + 1 + 1 + 1) {i | i.val = 0 ∨ i.val = m}).map φ₂).map
          (MulAut.conj (hElt φ₂)).toMonoidHom :=
          (Subgroup.map_map (K := slOn (m + 1 + 1 + 1)
            {i | i.val = 0 ∨ i.val = m}) (MulAut.conj (hElt φ₂)).toMonoidHom φ₂).symm

private theorem ggHalfInnerCommA_mid_comm_left {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) (a : SpecialLinearGroup
      (Fin (m + 1 + 1 + 1)) F2)
    (ha : a ∈ slOn (m + 1 + 1 + 1) {i | i.val = m ∨ i.val = m + 1})
    (b1 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)
    (hb1 : b1 ∈ slOn (m + 1 + 1 + 1) {i | 2 ≤ i.val ∧ i.val < m + 2}) :
    φ₂ a * φ₁ b1 = φ₁ b1 * φ₂ a := by
  have hb1' := hb1
  rw [ggHalfInnerCommA_lt_pair_image m,
    ← slLower2Hom_map_slOn m (S := {j : Fin (m + 1) | j.val < m})] at hb1'
  obtain ⟨b1', hb1'mem, rfl⟩ := hb1'
  have hagree : φ₁ (slLower2Hom m b1') = φ₂ (slUpper2Hom m b1') := by
    have := DFunLike.congr_fun h.coords.agree b1'
    simpa only [MonoidHom.comp_apply] using this
  rw [hagree]
  have hupper_mem : slUpper2Hom m b1' ∈
      slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | i.val < m} := by
    rw [ggHalfInnerCommA_upper_image m,
      ← slUpper2Hom_map_slOn m (S := {j : Fin (m + 1) | j.val < m})]
    exact ⟨b1', hb1'mem, rfl⟩
  have hdisj : Disjoint ({i : Fin (m + 1 + 1 + 1) | i.val = m ∨ i.val = m + 1} :
      Set (Fin (m + 1 + 1 + 1))) {i : Fin (m + 1 + 1 + 1) | i.val < m} := by
    refine Set.disjoint_left.mpr ?_
    intro i hi hj
    simp only [Set.mem_setOf_eq] at hi hj
    rcases hi with hi | hi <;> omega
  have hcommSL := ggHalfInnerCommA_slOn_commute_of_disjoint hdisj ha hupper_mem
  simpa only [map_mul] using congrArg φ₂ hcommSL

private theorem ggHalfInnerCommA_mid_comm_right {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) (hK1 : GGHalfNormSL014 φ₁ φ₂)
    (hm : 3 ≤ m) (a : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)
    (ha : a ∈ slOn (m + 1 + 1 + 1) {i | i.val = m ∨ i.val = m + 1})
    (b2 : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)
    (hb2 : b2 ∈ slOn (m + 1 + 1 + 1) {0, 1, 4}) :
    φ₂ a * φ₁ b2 = φ₁ b2 * φ₂ a := by
  have hXeq := ggHalfInnerCommA_mid_eq_conj h (by omega : 2 ≤ m)
  have hφa : φ₂ a ∈ ((slOn (m + 1 + 1 + 1) {i | i.val = 0 ∨ i.val = m}).map φ₂).map
      (MulAut.conj (hElt φ₂)).toMonoidHom := by
    rw [← hXeq]
    exact Subgroup.mem_map_of_mem φ₂ ha
  obtain ⟨a0, ha0, ha0eq⟩ := hφa
  obtain ⟨c, hc, hc_eq⟩ := ha0
  have hc' := hc
  rw [ggHalfInnerCommA_zero_m_image m,
    ← slUpper2Hom_map_slOn m (S := {j : Fin (m + 1) | j.val = 0 ∨ j.val = m})] at hc'
  obtain ⟨c', hc'mem, rfl⟩ := hc'
  have hc1mem : slLower2Hom m c' ∈
      slOn (m + 1 + 1 + 1) {i : Fin (m + 1 + 1 + 1) | i.val = 2 ∨ i.val = m + 2} := by
    rw [ggHalfInnerCommA_low_image m,
      ← slLower2Hom_map_slOn m (S := {j : Fin (m + 1) | j.val = 0 ∨ j.val = m})]
    exact ⟨c', hc'mem, rfl⟩
  have hdisj2 : Disjoint ({i : Fin (m + 1 + 1 + 1) | i.val = 2 ∨ i.val = m + 2} :
      Set (Fin (m + 1 + 1 + 1))) ({0, 1, 4} : Set (Fin (m + 1 + 1 + 1))) := by
    refine Set.disjoint_left.mpr ?_
    intro i hi hj
    simp only [Set.mem_setOf_eq] at hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
    have hmod : 4 % (m + 1 + 1 + 1) = 4 :=
      Nat.mod_eq_of_lt (by omega)
    have hj' : i.val = 0 ∨ i.val = 1 ∨ i.val = 4 := by
      rcases hj with hj | hj | hj
      · left; simpa using congrArg Fin.val hj
      · right; left; simpa using congrArg Fin.val hj
      · right; right; simpa [hmod] using congrArg Fin.val hj
    rcases hi with hi | hi <;> rcases hj' with hj | hj | hj <;> omega
  have hcagree : φ₂ (slUpper2Hom m c') = φ₁ (slLower2Hom m c') := by
    have := DFunLike.congr_fun h.coords.agree c'
    simpa only [MonoidHom.comp_apply] using this.symm
  have ha0_eq : a0 = φ₁ (slLower2Hom m c') := by
    rw [← hc_eq, hcagree]
  have ha_eq : hElt φ₂ * a0 * (hElt φ₂)⁻¹ = φ₂ a := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using ha0eq
  have hcommA0 : ∀ z ∈ ((slOn (m + 1 + 1 + 1) {0, 1, 4}).map φ₁), a0 * z = z * a0 := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [ha0_eq]
    have hcommSL := ggHalfInnerCommA_slOn_commute_of_disjoint hdisj2 hc1mem hw
    simpa only [map_mul] using congrArg φ₁ hcommSL
  have hb2H : φ₁ b2 ∈ ((slOn (m + 1 + 1 + 1) {0, 1, 4}).map φ₁) :=
    ⟨b2, hb2, rfl⟩
  have hb2pre : φ₁ b2 ∈ ((slOn (m + 1 + 1 + 1) {0, 1, 4}).map φ₁).map
      (MulAut.conj (hElt φ₂)).toMonoidHom := by
    rw [hK1]
    exact hb2H
  obtain ⟨b2', hb2'H, hb2'eq⟩ := hb2pre
  have hb2'' : hElt φ₂ * b2' * (hElt φ₂)⁻¹ = φ₁ b2 := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hb2'eq
  calc
    φ₂ a * φ₁ b2
        = (hElt φ₂ * a0 * (hElt φ₂)⁻¹) * (hElt φ₂ * b2' * (hElt φ₂)⁻¹) := by
          rw [ha_eq, hb2'']
    _ = hElt φ₂ * (a0 * b2') * (hElt φ₂)⁻¹ := by group
    _ = hElt φ₂ * (b2' * a0) * (hElt φ₂)⁻¹ := by rw [hcommA0 b2' hb2'H]
    _ = (hElt φ₂ * b2' * (hElt φ₂)⁻¹) * (hElt φ₂ * a0 * (hElt φ₂)⁻¹) := by group
    _ = φ₁ b2 * φ₂ a := by rw [hb2'', ha_eq]

theorem slOn_mid_pair_comm {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) (hK1 : GGHalfNormSL014 φ₁ φ₂) :
    ∀ a ∈ slOn (m + 1 + 1 + 1) {i | i.val = m ∨ i.val = m + 1},
      ∀ b ∈ slOn (m + 1 + 1 + 1) {i | i.val < m + 2}, φ₂ a * φ₁ b = φ₁ b * φ₂ a := by
  have hm : 3 ≤ m := by have := h.nbr.2.2.1; omega
  intro a ha b hb
  have h1le : slOn (m + 1 + 1 + 1) {i | 2 ≤ i.val ∧ i.val < m + 2} ≤
      (Subgroup.centralizer ({φ₂ a} : Set G)).comap φ₁ := by
    intro y hy
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact (ggHalfInnerCommA_mid_comm_left h a ha y hy).symm
  have h2le : slOn (m + 1 + 1 + 1) {0, 1, 4} ≤
      (Subgroup.centralizer ({φ₂ a} : Set G)).comap φ₁ := by
    intro y hy
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact (ggHalfInnerCommA_mid_comm_right h hK1 hm a ha y hy).symm
  have hltle : slOn (m + 1 + 1 + 1) {i | i.val < m + 2} ≤
      (Subgroup.centralizer ({φ₂ a} : Set G)).comap φ₁ := by
    rw [slOn_lt_eq_sup m hm]
    exact sup_le h1le h2le
  have hmem := hltle hb
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hmem
  exact hmem.symm

theorem slOn_last_pair_comm {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) :
    ∀ a ∈ slOn (m + 1 + 1 + 1) {i | m + 1 ≤ i.val}, ∀ l ∈ L, φ₂ a * l = l * φ₂ a := by
  have hm : 1 ≤ m := by have := h.nbr.2.2.1; omega
  have hset : ({i : Fin (m + 1 + 1 + 1) | m + 1 ≤ i.val} :
      Set (Fin (m + 1 + 1 + 1))) =
      {i : Fin (m + 1 + 1 + 1) |
        i = (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).castSucc ∨
        i = (⟨m + 1, by omega⟩ : Fin (m + 1 + 1)).succ} := by
    ext i
    constructor
    · intro hi
      have hlt : i.val < m + 1 + 1 + 1 := i.isLt
      have hge : m + 1 ≤ i.val := hi
      have hv : i.val = m + 1 ∨ i.val = m + 2 := by
        by_cases h : i.val = m + 1
        · exact Or.inl h
        · exact Or.inr (by omega)
      rcases hv with hv | hv
      · left
        apply Fin.ext
        simpa only [Fin.val_castSucc, Fin.val_mk] using hv
      · right
        apply Fin.ext
        simpa only [Fin.val_succ, Fin.val_mk] using hv
    · rintro (rfl | rfl)
      · simp only [Set.mem_setOf_eq, Fin.val_castSucc, Fin.val_mk]
        omega
      · simp only [Set.mem_setOf_eq, Fin.val_succ, Fin.val_mk]
        omega
  have hle : slOn (m + 1 + 1 + 1) {i | m + 1 ≤ i.val} ≤
      (Subgroup.centralizer (L : Set G)).comap φ₂ := by
    rw [hset]
    refine (ggHalfInnerCommA_slOn_pair_le_closure (m + 1 + 1) ⟨m + 1, by omega⟩).trans ?_
    rw [Subgroup.closure_le]
    intro g hg
    change φ₂ g ∈ Subgroup.centralizer (L : Set G)
    rw [Subgroup.mem_centralizer_iff]
    rcases hg with hg | hg
    · rw [hg]
      have hwmem : wElt φ₂ ∈ Subgroup.zpowers x := by
        rw [h.zpowers_x]
        exact Subgroup.mem_zpowers _
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwmem
      intro l hl
      rw [show φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩) = wElt φ₂ from rfl, ← hk]
      exact ((Commute.zpow_left (show Commute x l from h.basic.2.2.2.2.2.2.1 l hl) k).eq).symm
    · rw [hg]
      intro l hl
      exact (h.endT₂_central l hl).symm
  intro a ha l hl
  have hmem : φ₂ a ∈ Subgroup.centralizer (L : Set G) := hle ha
  exact (Subgroup.mem_centralizer_iff.mp hmem l hl).symm

end GGHalfCtx

end CFSG.StandardType

end
