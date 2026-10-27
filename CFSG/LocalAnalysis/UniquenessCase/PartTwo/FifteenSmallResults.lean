module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSmallDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15Small_Six_gamma_eq_three (D : Data G) (hT7 : RT7Small D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hsmall : mSub V₀ ≤ 2) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) {g : G} (hgM : g ∉ D.M) (hg : s15SixAdm D V g)
    (hs : s15 D.M V₀ V hV L = 2)
    (hδ : delta15 D.M V₀ V hV L + 2 ≤ gamma15 D.M V₀ V hV L)
    (hW : ¬ wSub V₀ V hV L ≤ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G)) :
    gamma15 D.M V₀ V hV L = 3 := by
  have h151 := h.hyp151
  have h125 := h151.hyp125
  obtain ⟨hBA, hBM⟩ := s15_Six_conj_wSub_le_M (V₀ := V₀) (L := L) D hV hg
  have hker := s15_Six_two_le_mQuot_ker D h151 hV hL hg hδ hW
  have hBN := s15_Six_le_normalizer_of_ker D h151 hV hg (by omega) hker
  have hK := s15_Six_mQuot_axis_eq_one D h hV hgM hg (by omega) hBN hker
  have hN₁ : ∀ y ∈ D.M, y ∈ normalizer (v1Sub D.M V₀ V hV L : Set G) :=
    fun y hy => s15_Infra_le_normalizer_v1Sub h125 hV hy
  have hKle : (wSub V₀ V hV L ⊓ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G)) ⊔
      v1Sub D.M V₀ V hV L ≤ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L :=
    sup_le (inf_le_left.trans le_sup_left) le_sup_right
  have key := hT7 V₀ V L h hsmall hL 1 (wSub V₀ V hV L) ⟨1, D.M.one_mem, (conjSubgroup_one _).symm⟩
    (conjSubgroup (wSub V₀ V hV L) g)
    (s15SixKer (conjSubgroup (wSub V₀ V hV L) g)
      ((wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) : Set G) (v1Sub D.M V₀ V hV L))
    ((wSub V₀ V hV L ⊓ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G)) ⊔
      v1Sub D.M V₀ V hV L)
    ((E3.isElemAbelian_conjSubgroup hV g).mono hBA)
    (by rw [conjSubgroup_one]; exact hBM) (fun x hx => hx.1)
    (by
      rw [conjSubgroup_one]
      intro x hx
      have hx' : x ∈ D.M ⊓ normalizer (wSub V₀ V hV L : Set G) :=
        Subgroup.mem_inf.2 ⟨hBM hx, hBN hx⟩
      rw [inf_normalizer_wSub_eq_nBar D h151 hV,
        ← inf_normalizer_wSub_sup_v1Sub_eq_nBar D h151 hV] at hx'
      exact (Subgroup.mem_inf.1 hx').2)
    (by
      intro x hx
      rw [conjSubgroup_one, conjSubgroup_one]
      exact ⟨fun hxC d hd => hxC.2.2 d hd, fun hall => ⟨hx, hN₁ _ (hBM hx), hall⟩⟩)
    (by rw [conjSubgroup_one]; exact le_sup_right)
    (by rw [conjSubgroup_one]; exact hKle)
    (by rw [conjSubgroup_one]; exact hK)
    (by
      intro x hx k hk
      rw [conjSubgroup_one]
      exact s15_Six_comm_mem_v1Sub_of_mem_axis D h hV hgM hg hBN hx hk)
    hker
  exact key.1

theorem s15Small_Six_step3 (D : Data G) (h1217 : R1217 D) (hT7 : RT7Small D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hsmall : mSub V₀ ≤ 2) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 2)
    (hStar : ¬ s15SixStar D V₀ V L hV) {g : G} (hgM : g ∉ D.M) (hg : s15SixAdm D V g) :
    ⁅wSub V₀ V hV L, conjSubgroup (wSub V₀ V hV L) g⁆ = ⊥ := by
  by_contra hne
  have hδ := s15_Six_delta_lt_of_not_star D h1217 h hV hL hs hStar
  have hginv : g⁻¹ ∉ D.M := fun hm => hgM (by simpa using D.M.inv_mem hm)
  have hcase : ¬ wSub V₀ V hV L ≤ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G) ∨
      ¬ wSub V₀ V hV L ≤ normalizer (conjSubgroup (wSub V₀ V hV L) g⁻¹ : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hne (s15_Six_commutator_of_normalizes D h hV hgM hcon.1 hcon.2)
  have hγ : gamma15 D.M V₀ V hV L = 3 := by
    rcases hcase with hW | hW
    · exact s15Small_Six_gamma_eq_three D hT7 h hsmall hV hL hgM hg hs (by omega) hW
    · exact s15Small_Six_gamma_eq_three D hT7 h hsmall hV hL hginv (s15_Six_adm_inv hg) hs
        (by omega) hW
  exact hStar (s15_Six_star D h1217 hSg h1219 h hV hL hs hγ hδ)

theorem fifteen_six_small (D : Data G) (h129 : R129_1 D) (h1217 : R1217 D) (hT7 : RT7Small D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) : R15_6Small D := by
  intro V₀ V L h hsmall hL g hVg hAM
  have h151 := h.hyp151
  refine s15_Six_reduce D h1217 h151 h151.isElemAbelian hL (fun g' hg' => ?_) ⟨hVg, hAM⟩
  by_cases hgM : g' ∈ D.M
  · exact s15_Six_commutator_of_mem D h151.hyp125 h151.isElemAbelian hgM
  · have h5 := fifteen_five D h129 h1217 h h151.isElemAbelian hL
    by_cases hs4 : 4 ≤ s15 D.M V₀ V h151.isElemAbelian L
    · exact s15_Six_step1 D h h151.isElemAbelian hs4 hgM hg'
    · by_cases hs2 : s15 D.M V₀ V h151.isElemAbelian L = 2
      · by_cases hStar : s15SixStar D V₀ V L h151.isElemAbelian
        · exact s15_Six_step2 D h h151.isElemAbelian hL (by omega) (Or.inr hStar) hgM hg'
        · exact s15Small_Six_step3 D h1217 hT7 hSg h1219 h hsmall h151.isElemAbelian hL hs2 hStar
            hgM hg'
      · exact s15_Six_step2 D h h151.isElemAbelian hL (by omega) (Or.inl (fun h' => hs2 h'.1))
          hgM hg'

theorem s15Small_Eight_not_le_conj (D : Data G) (h156 : R15_6Small D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hsmall : mSub V₀ ≤ 2) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) {g : G} (hgM : conjSubgroup V g ≤ D.M)
    (hB : ¬ conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g ≤
      normalizer (wSub V₀ V hV L : Set G)) :
    ¬ V ≤ conjSubgroup D.M g := by
  intro hVg
  have hcomm : ⁅V, conjSubgroup V g⁆ = ⊥ := h156 V₀ V L h hsmall hL g hVg hgM
  apply hB
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h.hyp151.hyp125 hV)
  have hBV : conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g ≤ conjSubgroup V g :=
    E3.conjSubgroup_mono_left g hWV
  intro b hb
  have hbC : b ∈ centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : ⁅x, b⁆ ∈ ⁅V, conjSubgroup V g⁆ := Subgroup.commutator_mem_commutator hx (hBV hb)
    rw [hcomm] at h1
    have h2 : x * b * x⁻¹ * b⁻¹ = 1 := by
      have := Subgroup.mem_bot.1 h1
      rwa [commutatorElement_def] at this
    calc x * b = (x * b * x⁻¹ * b⁻¹) * (b * x) := by group
      _ = b * x := by rw [h2, one_mul]
  have hWV' : ((wSub V₀ V hV L : Subgroup G) : Set G) ⊆ (V : Set G) :=
    fun x hx => preTil_le V₀ V hV _ hx
  exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hWV' hbC)

theorem s15Small_Eight_core (D : Data G) (h156 : R15_6Small D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hsmall : mSub V₀ ≤ 2) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) {g : G} (hgM : conjSubgroup V g ≤ D.M) :
    conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g ≤
      normalizer (wSub V₀ V hV L : Set G) := by
  by_contra hB
  have h151 := h.hyp151
  have h125 := h151.hyp125
  have hVg := s15Small_Eight_not_le_conj D h156 h hsmall hV hL hgM hB
  set B := conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g with hBdef
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h125 hV)
  have hBV : B ≤ conjSubgroup V g := E3.conjSubgroup_mono_left g hWV
  have hBM : B ≤ D.M := hBV.trans hgM
  have hB2 : IsPGroup 2 B := (E3.isElemAbelian_conjSubgroup hV g).isPGroup.to_le hBV
  have hlt : B ⊓ normalizer (wSub V₀ V hV L : Set G) < B := by
    refine lt_of_le_of_ne inf_le_left fun heq => hB ?_
    calc B = B ⊓ normalizer (wSub V₀ V hV L : Set G) := heq.symm
      _ ≤ normalizer (wSub V₀ V hV L : Set G) := inf_le_right
  obtain ⟨E, hBE, hEB, hE1⟩ := s15_Glue_exists_hyperplane hB2 hlt
  have hEne : E ≠ B := by
    rintro rfl
    rw [E3.mQuot_self] at hE1
    exact absurd hE1 (by norm_num)
  obtain ⟨v, hvV, hEv, ⟨b, hb, hbv⟩, hvW⟩ :=
    fifteen_seven_G D h151 hV hL hBM hB2 hEB hBE hEne
  by_cases hcase : s15 D.M V₀ V hV L = 2 ∧
      delta15 D.M V₀ V hV L < gamma15 D.M V₀ V hV L - 1
  · have hEN : E ≤ normalizer (wSub V₀ V hV L : Set G) := by
      have hle := s15_Glue_mQuot_inf_normalizer_le_one D h151 hV hBM hB2 hcase.1
      have h1 := E3.mQuot_add (V := B) hBE hEB
      have h2 : E3.mQuot E (B ⊓ normalizer (wSub V₀ V hV L : Set G)) = 0 := by omega
      have h3 := (E3.mQuot_eq_zero_iff (hB2.to_le hEB) hBE).1 h2
      rw [← h3]
      exact inf_le_right
    exact hbv (s15_Eight_fix_of_s_two D h hV hL hBdef hgM hVg hcase (hvW hEN)
      (fun e he => hEv e (hBE he)) b hb)
  · exact hbv (s15_Eight_fix_of_ne D h hV hL hBdef hgM hVg hEB hE1 hcase hvV hEv b hb)

theorem fifteen_eight_small (D : Data G) (h1217 : R1217 D) (h156 : R15_6Small D) :
    R15_8Small D := by
  intro V₀ V L h hsmall hL
  exact s15_Eight_le_of_core D h1217 h h.hyp151.isElemAbelian hL
    (fun g hg => s15Small_Eight_core D h156 h hsmall h.hyp151.isElemAbelian hL hg)

theorem fifteen_nine_small (D : Data G) (h1217 : R1217 D) (h156 : R15_6Small D)
    (h158 : R15_8Small D) : R15_9Small D := by
  intro V₀ V L h hsmall hL
  have hV : IsElemAbelian 2 V := h.hyp151.isElemAbelian
  refine s15_Glue_wClos_zero_le hV (fun g hgM => ?_)
  have hVg := s15_Nine_le_conj D h1217 h hV hL (h158 V₀ V L h hsmall hL) hgM
  have hcomm : ⁅V, conjSubgroup V g⁆ = ⊥ := h156 V₀ V L h hsmall hL g hVg hgM
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : ⁅x, b⁆ ∈ ⁅V, conjSubgroup V g⁆ := Subgroup.commutator_mem_commutator hx hb
  rw [hcomm] at h1
  have h2 : x * b * x⁻¹ * b⁻¹ = 1 := by
    have := Subgroup.mem_bot.1 h1
    rwa [commutatorElement_def] at this
  calc x * b = (x * b * x⁻¹ * b⁻¹) * (b * x) := by group
    _ = b * x := by rw [h2, one_mul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
