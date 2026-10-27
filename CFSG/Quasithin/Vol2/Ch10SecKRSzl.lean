module

public import CFSG.Quasithin.Vol2.Ch10SecKRSzk
public import CFSG.Quasithin.Vol2.Ch10SecKRSs
public import CFSG.Quasithin.Vol2.Ch10SecKRSzi

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C10P4F
open scoped Matrix

variable {G : Type} [Group G]

@[expose] noncomputable def natToMulti {J W : Subgroup G} (C : KGH91.NatCoord J W 5) :
    MultiCoord J W 1 where
  E g _ := C.E g
  ρ := C.ρ
  dual _ := false
  le := C.le
  map_mul a ha b hb := by
    funext i
    rw [C.map_mul a ha b hb]
    rfl
  inj a ha b hb h := C.inj a ha b hb (congrFun h 0)
  surj x := by
    obtain ⟨a, ha, hax⟩ := C.surj (x 0)
    refine ⟨a, ha, funext fun i => ?_⟩
    rw [hax, Subsingleton.elim i 0]
  conj l a ha _ := C.conj l a ha
  ρ_surj := C.ρ_surj

variable [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.false_of_multiCoord (c : Conf T L I t w J)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two)
    (h1011 : Stmt10_1_1) (h318 : A318Facts) (h36' : A36ForSQTK)
    (hE : Ch11.SecA.FactA318ExclTwo) (hK7L5 : FactK7L5)
    (hVe : IsElemAbelian 2 (VI T L I J w)) (hq : CFSG.Open.IsQuasisimple ↥(autI hVe J))
    (e5 : ↥(autI hVe J) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (eJ : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (eL : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hCJ : J ⊓ Subgroup.centralizer (VI T L I J w : Set G) = pCoreOf 2 J)
    (hcv : fsuCVM T L I = ⊥) (hV1W : fsuUL T L I ≤ VI T L I J w)
    (hcase : Case10_1_1Three T L I ∨ Case10_1_1Five T L I) {k : ℕ}
    (C₀ : MultiCoord J (VI T L I J w) k) {i₀ : Fin k} (hi₀ : C₀.dual i₀ = false) : False := by
  obtain ⟨C, hCd, hU⟩ := Conf.exists_multiCoord_normalized c hCJ C₀
  rw [← hCd] at hi₀
  have hker : ∀ j : ↥J, C.ρ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1 := fun j hj => C.ker_two hCJ hj
  obtain ⟨hUN, hperf, hqX⟩ := Conf.lstar_data c h37 h38 C.ρ C.ρ_surj hker hU eL
  rcases invStd_cases hUN hperf hqX with ⟨h3, htriv⟩ | ⟨h2, htriv⟩ | ⟨h1, h4, hfix⟩
  · have hX := eq_X3_of_E3 h3 htriv hqX hUN
    by_cases hd : ∃ i, C.dual i = true
    · obtain ⟨i₁, hi₁⟩ := hd
      exact Conf.false_of_multi_E3_dual c h1011 C hV1W hker h3 htriv hX hi₁
    · have hall : ∀ i, C.dual i = false := fun i => by
        cases h : C.dual i
        · rfl
        · exact absurd ⟨i, h⟩ hd
      rcases hcase with h3c | h5
      · exact Conf.false_of_multi_E3_nat3 c (Conf.Tw_eq_T1_of_case3 c h37 h38 h3c hcv) h37 h38
          h318 h36' hE hK7L5 hVe hq e5 eJ hCJ C hall hU h3 htriv hqX hUN
      · exact Conf.false_of_multi_E3_nat5 c h37 h38 h322 h1011 h5 C hall hV1W hker hU h3 hX
  · exact Conf.false_of_multi_E2 c h1011 C hV1W hker h2 htriv (eq_X2_of_E2 h2 htriv hqX hUN) hi₀
  · obtain ⟨e⟩ := hqX
    exact Conf.false_of_multi_flag c h1011 C hV1W hker h1 h4 hfix
      (eq_X14_of_flag h1 h4 (card_eq_o2G_mul _ e) hUN) i₀

theorem Conf.false_of_altCoord (c : Conf T L I t w J)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1011 : Stmt10_1_1) (h318 : A318Facts) (h36' : A36ForSQTK)
    (hE : Ch11.SecA.FactA318ExclTwo) (hK7L5 : FactK7L5)
    (hVe : IsElemAbelian 2 (VI T L I J w)) (hq : CFSG.Open.IsQuasisimple ↥(autI hVe J))
    (e5 : ↥(autI hVe J) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (eJ : ↥J ⧸ CFSG.pCore 2 ↥J ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (eL : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hCJ : J ⊓ Subgroup.centralizer (VI T L I J w : Set G) = pCoreOf 2 J)
    (hcv : fsuCVM T L I = ⊥) (hV1W : fsuUL T L I ≤ VI T L I J w)
    (hcase : Case10_1_1Three T L I ∨ Case10_1_1Five T L I)
    (C₀ : AltCoord J (VI T L I J w)) : False := by
  obtain ⟨C, hU⟩ := Conf.exists_altCoord_normalized c hCJ C₀
  have hker : ∀ j : ↥J, C.ρ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1 := fun j hj => C.ker_two hCJ hj
  obtain ⟨hUN, hperf, hqX⟩ := Conf.lstar_data c h37 h38 C.ρ C.ρ_surj hker hU eL
  rcases invStd_cases hUN hperf hqX with ⟨h3, htriv⟩ | ⟨h2, htriv⟩ | ⟨h1, h4, hfix⟩
  · rcases hcase with h3c | h5
    · have hTw := Conf.Tw_eq_T1_of_case3 c h37 h38 h3c hcv
      exact Conf.false_of_alt c hTw h37 h38 h318 h36' hE hK7L5 hVe hq e5 eJ hCJ C
        (fun g hg => by
          obtain ⟨j, rfl⟩ := C.ρ_surj g
          exact ⟨j, rfl, (hU j).mp hg⟩)
        (Conf.u_mem_VI c hTw h37 h38) (Conf.u_ne_one c) h3 htriv hqX hUN
    · exact Conf.false_of_alt_E3_five c h1011 h5 C hV1W hker h3 (eq_X3_of_E3 h3 htriv hqX hUN)
  · exact Conf.false_of_alt_E2 c h1011 C hV1W hker h2 htriv (eq_X2_of_E2 h2 htriv hqX hUN)
  · have hX : (piL C.ρ c.le).range = X14 := by
      obtain ⟨e⟩ := hqX
      exact eq_X14_of_flag h1 h4 (card_eq_o2G_mul _ e) hUN
    rcases hcase with h3c | h5
    · obtain ⟨y, hyLt, hy3, hyw⟩ := Conf.exists_y_of_case3 c h37 h38 h1011 h3c
      have hyJ : y ∈ J := Conf.mem_J_of_orderOf_three' c h38 h318 h36' hE eJ
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv e5 (isQuasisimple_of_open' hq))
        (center_SL_eq_bot 5) three_dvd_card_SL5 two_le_pRank_SL5 hK7L5 hyw hy3
      exact Conf.false_of_y_X14 c h37 C.ρ hker hX hqX hyLt hy3 hyJ
    · exact Conf.false_of_alt_flag_five c h1011 h5 C hV1W hker h1 h4 hX

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
