module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11A11Vec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11A11Uniq
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1Card
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open Equiv
open scoped Pointwise

private lemma s16c11a11_main_altVec_proof_irrel {n : ℕ} (x : Fin n → ZMod 2)
    (h1 h2 : ∑ i, x i = 0) : s16c11AltVec n x h1 = s16c11AltVec n x h2 := by
  unfold s16c11AltVec
  exact congrArg QuotientGroup.mk (Subtype.ext rfl)

theorem s16c11_altEleven_forced :
    S16C11Forced (S16C11AltAct 11) s16c11A11T1 11 (s16c11A11Cls 10) (s16c11A11Cls 8)
      (s16c11A11Cls 9) := by
  refine ⟨s16c11A11Cls_ne_one 10, fun t ht => s16c11A11T1_fix_cls_ten ht,
    s16c11A11_orbit_cls_ncard, ?_, ?_, ?_⟩
  · intro y hy1 hyfix hyorb
    obtain ⟨x, hx, rfl⟩ := s16c11AltVec_surjective 11 y
    obtain ⟨α, β, hxβ⟩ := s16c11A11_fixed_classify hyfix
    subst x
    change s16c11AltVec 11 (s16c11A11Fix α β) hx =
      s16c11AltVec 11 (s16c11A11Co 10) (s16c11A11Co_sum 10)
    refine (s16c11AltVec_eq_iff (n := 11) (by norm_num : ¬ 2 ∣ 11)).2 ?_
    have hα : α = 0 ∨ α = 1 := (by decide : ∀ α : ZMod 2, α = 0 ∨ α = 1) α
    have hβ : β = 0 ∨ β = 1 := (by decide : ∀ β : ZMod 2, β = 0 ∨ β = 1) β
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl
    · exact absurd ((s16c11AltVec_eq_one_iff (n := 11) (by norm_num : ¬ 2 ∣ 11)).2
        (by decide : s16c11A11Fix 0 0 = 0)) hy1
    · exfalso
      have hvec := s16c11a11_main_altVec_proof_irrel (s16c11A11Fix 0 1) hx
        (s16c11A11Fix_sum 0 1)
      rw [hvec] at hyorb
      exact absurd (s16c11A11_orbit_fix_big (Or.inr ⟨rfl, rfl⟩)) (not_lt.2 hyorb)
    · exfalso
      have hvec := s16c11a11_main_altVec_proof_irrel (s16c11A11Fix 1 0) hx
        (s16c11A11Fix_sum 1 0)
      rw [hvec] at hyorb
      exact absurd (s16c11A11_orbit_fix_big (Or.inl ⟨rfl, rfl⟩)) (not_lt.2 hyorb)
    · exact s16c11A11_fix_one_one
  · intro h
    exact absurd (s16c11A11Cls_injective h) (by decide : (8 : Fin 11) ≠ 9)
  · intro z hz hzy hzt
    obtain ⟨g, rfl⟩ := hz
    set j : Fin 11 := ((alternatingGroup (Fin 11)).subtype g) 10 with hj
    have hg10 : j ≠ 10 := by
      intro h
      exact hzy (by
        rw [s16c11A11_act_cls g 10]
        exact congrArg s16c11A11Cls (hj.symm.trans h))
    rw [s16c11A11_act_cls g 10] at hzt ⊢
    change {w | ∃ t ∈ s16c11A11T1,
      S16C11AltAct 11 t (s16c11A11Cls (((alternatingGroup (Fin 11)).subtype g) 10)) = w}.ncard ≤ 2
      at hzt
    change s16c11A11Cls (((alternatingGroup (Fin 11)).subtype g) 10) = s16c11A11Cls 8 ∨
      s16c11A11Cls (((alternatingGroup (Fin 11)).subtype g) 10) = s16c11A11Cls 9
    rw [← hj] at hzt ⊢
    by_cases hlt : (j : ℕ) < 8
    · exfalso
      exact absurd (s16c11A11T1_orbit_ncard_big j hlt) (not_lt.2 hzt)
    · have hge : 8 ≤ (j : ℕ) := not_lt.1 hlt
      have hle : (j : ℕ) ≤ 10 := by have h := j.isLt; omega
      have hne10 : (j : ℕ) ≠ 10 := by
        intro h
        exact hg10 (Fin.ext h)
      have hnat : (j : ℕ) = 8 ∨ (j : ℕ) = 9 := by omega
      rcases hnat with h | h
      · left
        exact congrArg s16c11A11Cls (Fin.ext h)
      · right
        exact congrArg s16c11A11Cls (Fin.ext h)

theorem s16c11_altEleven_forcedPairs :
    (S16C11ForcedPairs (S16C11AltAct 11) s16c11A11T1 (s16c11A11Cls 10) (s16c11A11Cls 8)
      (s16c11A11Cls 9)).ncard = 1 := by
  have hset : S16C11ForcedPairs (S16C11AltAct 11) s16c11A11T1 (s16c11A11Cls 10)
      (s16c11A11Cls 8) (s16c11A11Cls 9) =
      {(s16c11A11Cls 10, s16c11A11Y.subgroupOf (alternatingGroup (Fin 11)))} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
    · refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · exact Subgroup.subgroupOf_mono (alternatingGroup (Fin 11)) s16c11A11_T_le_Y
      · intro g hg
        exact (s16c11A11_setStab_iff g).2
          (s16c11A11_Y_le_pres (Subgroup.mem_subgroupOf.1 hg))
      · show (s16c11A11T.subgroupOf (alternatingGroup (Fin 11))).relIndex
          (s16c11A11Y.subgroupOf (alternatingGroup (Fin 11))) = 3
        rw [Subgroup.relIndex_subgroupOf s16c11A11_Y_le_alt, s16c11_a11_T_relIndex_Y]
      · refine ⟨⟨s16c11A11c, s16c11A11_Y_le_alt s16c11A11_c_mem_Y⟩,
          Subgroup.mem_subgroupOf.2 s16c11A11_c_mem_Y, ?_⟩
        rw [s16c11A11_act_cls ⟨s16c11A11c, s16c11A11_Y_le_alt s16c11A11_c_mem_Y⟩ 10]
        intro hcon
        have hc10 : ((⟨s16c11A11c, s16c11A11_Y_le_alt s16c11A11_c_mem_Y⟩ :
            ↥(alternatingGroup (Fin 11))) : Perm (Fin 11)) 10 = 8 := by
          show s16c11A11c 10 = 8
          decide
        rw [hc10] at hcon
        exact absurd (s16c11A11Cls_injective hcon) (by decide : (8 : Fin 11) ≠ 10)
    · rintro ⟨y, X⟩ hp
      obtain ⟨hy, hT₁X, hXS, h3, hmov⟩ := hp
      refine Prod.ext hy ?_
      have hXA : X.map (alternatingGroup (Fin 11)).subtype ≤ alternatingGroup (Fin 11) :=
        Subgroup.map_subtype_le X
      have hXP : X.map (alternatingGroup (Fin 11)).subtype ≤ s16c11A11Pres := by
        rintro x ⟨x', hx', rfl⟩
        exact (s16c11A11_setStab_iff x').1 (hXS hx')
      have hTX : s16c11A11T ≤ X.map (alternatingGroup (Fin 11)).subtype := by
        intro t ht
        exact Subgroup.mem_map.2
          ⟨⟨t, s16c11A11_T_le_alt ht⟩, hT₁X (Subgroup.mem_subgroupOf.2 ht), rfl⟩
      have hmapT : s16c11A11T1.map (alternatingGroup (Fin 11)).subtype = s16c11A11T :=
        Subgroup.map_subgroupOf_eq_of_le s16c11A11_T_le_alt
      have h3' : s16c11A11T.relIndex (X.map (alternatingGroup (Fin 11)).subtype) = 3 := by
        rw [← hmapT, Subgroup.relIndex_map_map_of_injective s16c11A11T1 X
          (alternatingGroup (Fin 11)).subtype_injective]
        exact h3
      have hmov' : ∃ g ∈ X.map (alternatingGroup (Fin 11)).subtype, g 10 ≠ 10 := by
        obtain ⟨g, hgX, hgy⟩ := hmov
        refine ⟨(alternatingGroup (Fin 11)).subtype g,
          Subgroup.mem_map.2 ⟨g, hgX, rfl⟩, ?_⟩
        intro hg10
        exact hgy (by
          rw [s16c11A11_act_cls g 10]
          exact congrArg s16c11A11Cls hg10)
      have hX₀ : X.map (alternatingGroup (Fin 11)).subtype = s16c11A11Y :=
        s16c11_a11_unique_overgroup hXA hXP hTX h3' hmov'
      rw [← Subgroup.comap_map_eq_self_of_injective
        (alternatingGroup (Fin 11)).subtype_injective X, hX₀]
      rfl
  exact (congrArg Set.ncard hset).trans (Set.ncard_singleton _)

theorem s16c11_altEleven_pairs :
    ∃ (T₁ : Subgroup (FFModel.altDn 11).Gam) (N : ℕ), IsPGroup 2 ↥T₁ ∧ ¬ 2 ∣ T₁.index ∧
      Odd (S16C11ModelPairs (FFModel.altDn_isActionModel 11) T₁ N).ncard := by
  haveI : Finite (FFModel.altDn 11).Gam := inferInstanceAs (Finite ↥(alternatingGroup (Fin 11)))
  refine ⟨s16c11A11T1, 11, s16c11_a11_T_isPGroup, s16c11_a11_T_index_odd, ?_⟩
  have hcard : (S16C11ModelPairs (FFModel.altDn_isActionModel 11) s16c11A11T1 11).ncard = 1 := by
    unfold S16C11ModelPairs
    exact (congrArg Set.ncard (s16c11_actPairs_eq_forcedPairs s16c11_altEleven_forced)).trans
      s16c11_altEleven_forcedPairs
  rw [hcard]
  exact odd_one

theorem s16c11_rf3Odd_of_altEleven {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {J : Subgroup W} (h : AlternatingNatural L J ⊥ 11) : S16C11RF3Odd L J := by
  obtain ⟨T₁, N, hT, hidx, hodd⟩ := s16c11_altEleven_pairs
  exact s16c11_rf3Odd_of_modelPairs (FFC.altDn_faithful (by norm_num))
    (FFModel.altDn_isActionModel 11) h hT hidx hodd

theorem s16c11_rf3_of_altEleven {W : Type} [CommGroup W] [Finite W] {L L₀ : Subgroup (MulAut W)}
    {J : Subgroup W} (hLL₀ : L ≤ L₀) (hS : IsSym ↥L₀ 11) (hA : IsAlt ↥L 11)
    (hJ : ∀ x ∈ L₀, ∀ y ∈ J, x y ∈ J) (h : AlternatingNatural L J ⊥ 11) :
    S16C11RF3 L₀ J :=
  s16c11_rf3_of_rf3Odd hLL₀
    (s16c11_map_conj_eq_of_card_two_mul hLL₀
      (s16e_card_eq_two_mul_of_isSym_isAlt (by omega) hS hA))
    hJ (s16c11_rf3Odd_of_altEleven h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
