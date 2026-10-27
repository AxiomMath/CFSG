module

public import CFSG.Quasithin.EmptyFaithful.SBd8Flag
public import CFSG.Quasithin.EmptyFaithful.SBd8FlagNine
import CFSG.Quasithin.EmptyFaithful.SBc5Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace SBd8

namespace Flag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L

section Full

variable {F : Type} [Field F] {n : ℕ}

theorem reflection_not_mem_upperTriangular {i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    reflection n F i hi hin ∉ upperTriangular n F := by
  intro h
  have hlt : (⟨i - 1, by omega⟩ : Fin n) < ⟨i, hin⟩ := by
    rw [Fin.lt_def]
    simp only
    omega
  have h0 := h ⟨i, hin⟩ ⟨i - 1, by omega⟩ hlt
  rw [coe_reflection] at h0
  simp [reflectionMatrix, Nat.sub_add_cancel hi] at h0

theorem upperTriangular_eq_flagStabilizer_full :
    upperTriangular n F = flagStabilizer n F {i | 1 ≤ i ∧ i < n} := by
  have h := (borel_overgroups (upperTriangular n F) le_rfl).1
  have hc : borelOvergroupCuts (upperTriangular n F) = {i | 1 ≤ i ∧ i < n} := by
    ext i
    constructor
    · rintro ⟨hi, hin, -⟩
      exact ⟨hi, hin⟩
    · rintro ⟨hi, hin⟩
      exact ⟨hi, hin, reflection_not_mem_upperTriangular hi hin⟩
  rwa [hc] at h

end Full

section Four

theorem isCuts_four_cases {I : Set ℕ} (h : IsCuts 4 I) :
    I = ∅ ∨ I = {1} ∨ I = {2} ∨ I = {3} ∨ I = {1, 2} ∨ I = {1, 3} ∨ I = {2, 3} ∨
      I = {1, 2, 3} := by
  have key : ∀ i, i ∈ I ↔ (i = 1 ∧ 1 ∈ I) ∨ (i = 2 ∧ 2 ∈ I) ∨ (i = 3 ∧ 3 ∈ I) := by
    intro i
    constructor
    · intro hi
      have := h i hi
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, hi⟩
      · exact Or.inr (Or.inl ⟨rfl, hi⟩)
      · exact Or.inr (Or.inr ⟨rfl, hi⟩)
    · rintro (⟨rfl, hi⟩ | ⟨rfl, hi⟩ | ⟨rfl, hi⟩) <;> exact hi
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I <;> by_cases h3 : 3 ∈ I <;>
  first
    | (refine Or.inl ?_; ext i; rw [key i]; simp [h1, h2, h3]; done)
    | (refine Or.inr (Or.inl ?_); ext i; rw [key i]; simp [h1, h2, h3]; done)
    | (refine Or.inr (Or.inr (Or.inl ?_)); ext i; rw [key i]; simp [h1, h2, h3]; done)
    | (refine Or.inr (Or.inr (Or.inr (Or.inl ?_))); ext i; rw [key i]; simp [h1, h2, h3]; done)
    | (refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))); ext i; rw [key i]
       simp [h1, h2, h3]; done)
    | (refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))); ext i; rw [key i]
       simp [h1, h2, h3]; done)
    | (refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))); ext i; rw [key i]
       simp [h1, h2, h3]; done)
    | (refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))); ext i; rw [key i]
       simp [h1, h2, h3])

theorem isSolvable_four_two : Group.IsSolvable ↥(flagStabilizer 4 (ZMod 2) {2}) := by
  refine isSolvable_flagStabilizer_of_small (by norm_num) ?_
  intro a m h ha hb hno
  simp only [Set.mem_singleton_iff, forall_eq] at ha hb hno
  omega

theorem not_isSolvable_four_one : ¬ Group.IsSolvable ↥(flagStabilizer 4 (ZMod 2) {1}) :=
  not_isSolvable_flagStabilizer_of_big (a := 1) (m := 3) (by norm_num) le_rfl (by simp) (by simp)
    (by simp)

theorem not_isSolvable_four_three : ¬ Group.IsSolvable ↥(flagStabilizer 4 (ZMod 2) {3}) :=
  not_isSolvable_flagStabilizer_of_big (a := 0) (m := 3) (by norm_num) le_rfl (by simp) (by simp)
    (by simp)

theorem stable_two {A : Subgroup (MulAut (SpecialLinearGroup (Fin 4) (ZMod 2)))}
    (hA : ∀ α ∈ A, (unitriangular 4 (ZMod 2)).map α.toMonoidHom = unitriangular 4 (ZMod 2))
    {α : MulAut (SpecialLinearGroup (Fin 4) (ZMod 2))} (hα : α ∈ A) :
    (flagStabilizer 4 (ZMod 2) {2}).map α.toMonoidHom = flagStabilizer 4 (ZMod 2) {2} := by
  obtain ⟨σ, hσ⟩ := exists_sigma (Nat.card_zmod 2) (hA α hα)
  obtain ⟨h1, h2, h3⟩ := hσ 2 (by norm_num) (by norm_num)
  have hs : Group.IsSolvable ↥(flagStabilizer 4 (ZMod 2) {σ 2}) := by
    rw [← h3]
    exact (isSolvable_map_iff _ α).2 isSolvable_four_two
  have h22 : σ 2 = 2 := by
    rcases (by omega : σ 2 = 1 ∨ σ 2 = 2 ∨ σ 2 = 3) with h | h | h
    · rw [h] at hs
      exact absurd hs not_isSolvable_four_one
    · exact h
    · rw [h] at hs
      exact absurd hs not_isSolvable_four_three
  rw [h3, h22]

section Core

variable {A : Subgroup (MulAut (SpecialLinearGroup (Fin 4) (ZMod 2)))}
  {K : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2))}

theorem eq_pair_of_data
    (d : OvgData (SpecialLinearGroup (Fin 4) (ZMod 2)) A (unitriangular 4 (ZMod 2)) K)
    {I : Set ℕ} (hI : IsCuts 4 I) (hK : K = flagStabilizer 4 (ZMod 2) I) : I = {1, 3} := by
  have hst2 : ∀ α ∈ A, (flagStabilizer 4 (ZMod 2) {2}).map α.toMonoidHom =
      flagStabilizer 4 (ZMod 2) {2} := fun α hα => stable_two d.A_U hα
  have h2 : IsCuts 4 {2} := isCuts_singleton (by norm_num) (by norm_num)
  have hstab : ({2} : Set ℕ) ⊆ I → I = {2} := fun hsub =>
    eq_of_stable d hI h2 hK ⟨2, rfl⟩ hsub hst2
  have key : ∀ {S T : Set ℕ} {x : ℕ}, S = T → x ∈ S → x ∈ T := fun h hx => h ▸ hx
  rcases isCuts_four_cases hI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (d.K_ne (by rw [hK, flagStabilizer_empty])).elim
  · exact (false_of_bigBlock d.Y_solv hK (a := 1) (m := 3) (by norm_num) le_rfl (by simp)
      (by simp) (by simp)).elim
  · refine (d.not_nine ?_).elim
    rw [hK]
    exact nine_dvd_card_flagStabilizer (a := 0) (b := 2) (by norm_num) (by norm_num) (by norm_num)
      (by simp) (by simp)
  · exact (false_of_bigBlock d.Y_solv hK (a := 0) (m := 3) (by norm_num) le_rfl (by simp)
      (by simp) (by simp)).elim
  · have := key (hstab (by simp)) (by simp : (1 : ℕ) ∈ ({1, 2} : Set ℕ))
    simp at this
  · rfl
  · have := key (hstab (by simp)) (by simp : (3 : ℕ) ∈ ({2, 3} : Set ℕ))
    simp at this
  · have := key (hstab (by simp)) (by simp : (1 : ℕ) ∈ ({1, 2, 3} : Set ℕ))
    simp at this

theorem core4
    (d : OvgData (SpecialLinearGroup (Fin 4) (ZMod 2)) A (unitriangular 4 (ZMod 2)) K) :
    IsMinParabolicOf (⊤ : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2))) K ∧
      ∃ α ∈ A, ∀ x : SpecialLinearGroup (Fin 4) (ZMod 2), α ≠ MulAut.conj x := by
  obtain ⟨I, hI, hK⟩ := exists_cuts d
  have hI13 := eq_pair_of_data d hI hK
  subst hI13
  have h1 : IsCuts 4 {1} := isCuts_singleton (by norm_num) (by norm_num)
  have hns1 : ∃ α ∈ A, (flagStabilizer 4 (ZMod 2) {1}).map α.toMonoidHom ≠
      flagStabilizer 4 (ZMod 2) {1} := by
    by_contra hcon
    push Not at hcon
    have := eq_of_stable d hI h1 hK ⟨1, rfl⟩ (by simp) hcon
    have h3 : (3 : ℕ) ∈ ({1, 3} : Set ℕ) := by simp
    rw [this] at h3
    simp at h3
  obtain ⟨α, hαA, hαne⟩ := hns1
  have hU0 : upperTriangular 4 (ZMod 2) = unitriangular 4 (ZMod 2) :=
    upperTriangular_eq_unitriangular (Nat.card_zmod 2)
  have hnorm : Subgroup.normalizer (unitriangular 4 (ZMod 2) :
      Set (SpecialLinearGroup (Fin 4) (ZMod 2))) = unitriangular 4 (ZMod 2) := by
    rw [normalizer_unitriangular, hU0]
  have hout : ∀ x : SpecialLinearGroup (Fin 4) (ZMod 2), α ≠ MulAut.conj x := by
    intro x hx
    subst hx
    have hxN : x ∈ Subgroup.normalizer (unitriangular 4 (ZMod 2) :
        Set (SpecialLinearGroup (Fin 4) (ZMod 2))) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact d.A_U _ hαA
    rw [hnorm, ← hU0] at hxN
    have hxQ : x ∈ flagStabilizer 4 (ZMod 2) {1} := upperTriangular_le_flagStabilizer _ hxN
    exact hαne (Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hxQ))
  refine ⟨?_, α, hαA, hout⟩
  have hne : unitriangular 4 (ZMod 2) ≠ K := by
    intro h
    have h3 := d.three_dvd
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 d.U_syl.2.1
    rw [← h, ha] at h3
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  have hbetween : ∀ N : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2)),
      unitriangular 4 (ZMod 2) ≤ N → N ≤ K → N = unitriangular 4 (ZMod 2) ∨ N = K := by
    intro N hUN hNK
    have hUN' : upperTriangular 4 (ZMod 2) ≤ N := hU0 ▸ hUN
    obtain ⟨hNeq, hNc⟩ := eq_flagStabilizer_borelOvergroupCuts hUN'
    set C := borelOvergroupCuts N with hC
    have hsub : ({1, 3} : Set ℕ) ⊆ C := by
      have hle : flagStabilizer 4 (ZMod 2) C ≤ flagStabilizer 4 (ZMod 2) {1, 3} := by
        rw [← hNeq, ← hK]
        exact hNK
      exact (flagStabilizer_le_iff hNc hI).1 hle
    by_cases h2 : 2 ∈ C
    · left
      have hCfull : C = {i | 1 ≤ i ∧ i < 4} := by
        ext i
        constructor
        · exact fun hi => hNc i hi
        · rintro ⟨hi1, hi2⟩
          rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
          · exact hsub (by simp)
          · exact h2
          · exact hsub (by simp)
      rw [hNeq, hCfull, ← upperTriangular_eq_flagStabilizer_full, hU0]
    · right
      have hC13 : C = {1, 3} := by
        refine Set.Subset.antisymm (fun i hi => ?_) hsub
        have := hNc i hi
        rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
        · simp
        · exact absurd hi h2
        · simp
      rw [hNeq, hC13, ← hK]
  have hlt : unitriangular 4 (ZMod 2) < K := lt_of_le_of_ne d.U_le hne
  have hmax : (maxOver K (unitriangular 4 (ZMod 2))).ncard = 1 := by
    rw [Set.ncard_eq_one]
    refine ⟨unitriangular 4 (ZMod 2), Set.eq_singleton_iff_unique_mem.2
      ⟨⟨⟨hlt, fun H hUH hHK => ?_⟩, le_rfl⟩, ?_⟩⟩
    · rcases hbetween H hUH.le hHK with h | h
      · exact absurd h.symm hUH.ne
      · exact h
    · rintro N ⟨⟨hNK, -⟩, hUN⟩
      rcases hbetween N hUN hNK.le with h | h
      · exact h
      · exact absurd h hNK.ne
  have hnn : ¬ K ≤ Subgroup.normalizer (unitriangular 4 (ZMod 2) :
      Set (SpecialLinearGroup (Fin 4) (ZMod 2))) := by
    intro h
    rw [hnorm] at h
    exact hne (le_antisymm d.U_le h)
  exact ⟨unitriangular 4 (ZMod 2), d.U_syl, ⟨⟨le_top, hlt, hmax⟩, hnn⟩⟩

end Core

end Four

end Flag

section Family

variable {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {U K : Subgroup X}

theorem famL4 (d : OvgData X A U K)
    (e : X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) :
    IsAlt 8 X ∧ IsMinParabolicOf (⊤ : Subgroup X) K ∧ ∃ α ∈ A, ∀ x : X, α ≠ MulAut.conj x := by
  refine ⟨⟨e.trans SBc5.alt8EquivStatedSL.symm⟩, ?_⟩
  obtain ⟨ψ, d'⟩ := Flag.exists_stdData (by norm_num) d
    (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm)
  obtain ⟨hmin, α', hα', hout⟩ := Flag.core4 d'
  refine ⟨?_, ?_⟩
  · have : IsMinParabolicOf ((⊤ : Subgroup X).map ψ.toMonoidHom) (K.map ψ.toMonoidHom) := by
      rw [Subgroup.map_top_of_surjective _ ψ.surjective]
      exact hmin
    exact (isMinParabolicOf_map_equiv_iff ψ).1 this
  · obtain ⟨α, hα, rfl⟩ := hα'
    refine ⟨α, hα, fun x hx => hout (ψ x) ?_⟩
    rw [hx]
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]

end Family


end SBd8

end CFSG.Quasithin
