module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSixPrime
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSixThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Six_commutator_eq_bot {X Y : Subgroup G}
    (h : ∀ x ∈ X, ∀ y ∈ Y, y * x * y⁻¹ * x⁻¹ = 1) : ⁅X, Y⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.mem_bot, ← commutatorElement_inv]
  have : ⁅y, x⁆ = 1 := h x hx y hy
  rw [this, inv_one]

theorem s15_Six_commutator_of_mem (D : Data G) {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) {g : G} (hg : g ∈ D.M) :
    ⁅wSub V₀ V hV L, conjSubgroup (wSub V₀ V hV L) g⁆ = ⊥ :=
  s15_Six_commutator_eq_bot fun x hx y hy => by
    have hxV : x ∈ V := preTil_le V₀ V hV _ hx
    have hyV : y ∈ V := s15_Tools_conj_wSub_le D h hV hg hy
    have := B2F.isElemAbelian_comm hV hyV hxV
    rw [this]
    group

theorem s15_Six_commutator_of_normalizes (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) {g : G} (hgM : g ∉ D.M)
    (h1 : wSub V₀ V hV L ≤ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G))
    (h2 : wSub V₀ V hV L ≤ normalizer (conjSubgroup (wSub V₀ V hV L) g⁻¹ : Set G)) :
    ⁅wSub V₀ V hV L, conjSubgroup (wSub V₀ V hV L) g⁆ = ⊥ :=
  s15_Six_commutator_eq_bot fun x hx y hy =>
    s15_Six_comm_of_normalizers (s15_Six_inf_conj_wSub_eq_bot D h hV hgM)
      (Subgroup.mem_inf.2 ⟨hy, (s15_Six_conj_le_normalizer_iff _ _ g).2 h2 hy⟩)
      (Subgroup.mem_inf.2 ⟨hx, h1 hx⟩)

theorem s15_Six_step1 (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hs : 4 ≤ s15 D.M V₀ V hV L) {g : G} (hgM : g ∉ D.M)
    (hg : s15SixAdm D V g) :
    ⁅wSub V₀ V hV L, conjSubgroup (wSub V₀ V hV L) g⁆ = ⊥ := by
  have h125 := h.hyp151.hyp125
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  refine s15_Six_commutator_eq_bot fun w hw b hb => ?_
  obtain ⟨-, hBM⟩ := s15_Six_conj_wSub_le_M (V₀ := V₀) (L := L) D hV hg
  have hbM : b ∈ D.M := hBM hb
  have hm : g * w * g⁻¹ ∈ D.M := mem_conjSubgroup_iff.1 (hg.1 (hWV hw))
  have hU₁ : IsPGroup 2 ↥(conjSubgroup (wSub V₀ V hV L) b⁻¹ ⊔ conjSubgroup (wSub V₀ V hV L) 1 :
      Subgroup G) :=
    hV.isPGroup.to_le (sup_le (s15_Tools_conj_wSub_le D h125 hV (D.M.inv_mem hbM))
      (s15_Tools_conj_wSub_le D h125 hV D.M.one_mem))
  have hU₂ : IsPGroup 2 ↥(conjSubgroup (wSub V₀ V hV L) 1 ⊔
      conjSubgroup (wSub V₀ V hV L) (g * w * g⁻¹)⁻¹ : Subgroup G) :=
    hV.isPGroup.to_le (sup_le (s15_Tools_conj_wSub_le D h125 hV D.M.one_mem)
      (s15_Tools_conj_wSub_le D h125 hV (D.M.inv_mem hm)))
  have hbot := inf_conjSubgroup_eq_bot_of_uniqueMax D.maxLocal hU₁ hU₂
    (fun u hu hu1 => s15_Tools_good_of_mem_sup_conj D h hV hs (D.M.inv_mem hbM) D.M.one_mem hu hu1)
    (fun u hu hu1 => s15_Tools_good_of_mem_sup_conj D h hV hs D.M.one_mem (D.M.inv_mem hm) hu hu1)
    hgM
  have hz : b * w * b⁻¹ * w⁻¹ ∈
      (conjSubgroup (wSub V₀ V hV L) b⁻¹ ⊔ conjSubgroup (wSub V₀ V hV L) 1) ⊓
        conjSubgroup (conjSubgroup (wSub V₀ V hV L) 1 ⊔
          conjSubgroup (wSub V₀ V hV L) (g * w * g⁻¹)⁻¹) g := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
      · rw [mem_conjSubgroup_iff]
        have : b⁻¹ * (b * w * b⁻¹) * b⁻¹⁻¹ = w := by group
        rw [this]
        exact hw
      · rw [mem_conjSubgroup_iff]
        simpa using (wSub V₀ V hV L).inv_mem hw
    · rw [mem_conjSubgroup_iff]
      have hb' : g * b * g⁻¹ ∈ wSub V₀ V hV L := mem_conjSubgroup_iff.1 hb
      have e : g * (b * w * b⁻¹ * w⁻¹) * g⁻¹ = (g * b * g⁻¹) *
          ((g * w * g⁻¹) * (g * b * g⁻¹)⁻¹ * (g * w * g⁻¹)⁻¹) := by group
      rw [e]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
      · rw [mem_conjSubgroup_iff]
        simpa using hb'
      · rw [mem_conjSubgroup_iff]
        have : (g * w * g⁻¹)⁻¹ * ((g * w * g⁻¹) * (g * b * g⁻¹)⁻¹ * (g * w * g⁻¹)⁻¹) *
            (g * w * g⁻¹)⁻¹⁻¹ = (g * b * g⁻¹)⁻¹ := by group
        rw [this]
        exact (wSub V₀ V hV L).inv_mem hb'
  rw [hbot] at hz
  exact Subgroup.mem_bot.1 hz

theorem s15_Six_normalizes (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L ≤ 3)
    (hc : ¬ (s15 D.M V₀ V hV L = 2 ∧ delta15 D.M V₀ V hV L < gamma15 D.M V₀ V hV L - 1) ∨
      s15SixStar D V₀ V L hV) {g : G} (hgM : g ∉ D.M) (hg : s15SixAdm D V g) :
    wSub V₀ V hV L ≤ normalizer (conjSubgroup (wSub V₀ V hV L) g : Set G) := by
  have h151 := h.hyp151
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  obtain ⟨hBA, hBM⟩ := s15_Six_conj_wSub_le_M (V₀ := V₀) (L := L) D hV hg
  have hB2 : IsPGroup 2 (conjSubgroup (wSub V₀ V hV L) g) :=
    E3.isPGroup_conjSubgroup (hV.isPGroup.to_le hWV) g
  refine s15_Six_normalizes_of_comm (c := gamma15 D.M V₀ V hV L) ?_
    (s15_Six_mQuot_inf_normalizer_le_one D h151 hV hBM hB2 hs)
    (two_le_gamma15 D h151 hV hL) fun w hw hwn =>
      s15_Six_le_mQuot_conj D h151 hV (hg.1 (hWV hw)) hwn
  intro b hb w hw
  obtain ⟨hbB, hbN⟩ := Subgroup.mem_inf.1 hb
  have hc' : b * w * b⁻¹ * w⁻¹ ∈ wSub V₀ V hV L :=
    (wSub V₀ V hV L).mul_mem ((Subgroup.mem_normalizer_iff.1 hbN w).1 hw)
      ((wSub V₀ V hV L).inv_mem hw)
  have hc'' : b * w * b⁻¹ * w⁻¹ ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L :=
    Subgroup.mem_sup_left hc'
  rcases hc with hc | hStar
  · exact s15_Six_comm_eq_one D h hV rfl hgM hc
      (E3.conjSubgroup_mono_left g le_sup_left hbB) (hg.1 (hWV hw)) hc''
  · have hmem := s15_Six_comm_mem_inf h151.hyp125.pairFacts.le_normalizer hg.1 hg.2 (hWV hw)
      (hBA hbB)
    have h0 := hStar g hgM
    have : b * w * b⁻¹ * w⁻¹ ∈ (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) ⊓ conjSubgroup V g :=
      Subgroup.mem_inf.2 ⟨hc'', (Subgroup.mem_inf.1 hmem).2⟩
    rw [h0] at this
    exact Subgroup.mem_bot.1 this

theorem s15_Six_step2 (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L ≤ 3)
    (hc : ¬ (s15 D.M V₀ V hV L = 2 ∧ delta15 D.M V₀ V hV L < gamma15 D.M V₀ V hV L - 1) ∨
      s15SixStar D V₀ V L hV) {g : G} (hgM : g ∉ D.M) (hg : s15SixAdm D V g) :
    ⁅wSub V₀ V hV L, conjSubgroup (wSub V₀ V hV L) g⁆ = ⊥ :=
  s15_Six_commutator_of_normalizes D h hV hgM (s15_Six_normalizes D h hV hL hs hc hgM hg)
    (s15_Six_normalizes D h hV hL hs hc (fun hm => hgM (by simpa using D.M.inv_mem hm))
      (s15_Six_adm_inv hg))

theorem s15_Six_step3 (D : Data G) (h1217 : R1217 D) (hT7 : RT7 D) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 2)
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
    · exact s15_Six_gamma_eq_three D hT7 h hV hL hgM hg hs (by omega) hW
    · exact s15_Six_gamma_eq_three D hT7 h hV hL hginv (s15_Six_adm_inv hg) hs (by omega) hW
  exact hStar (s15_Six_star D h1217 hSg h1219 h hV hL hs hγ hδ)

theorem fifteen_six (D : Data G) (h129 : R129_1 D) (h1217 : R1217 D) (hT7 : RT7 D)
    (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1) : R15_6 D := by
  intro V₀ V L h hL g hVg hAM
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
        · exact s15_Six_step3 D h1217 hT7 hSg h1219 h h151.isElemAbelian hL hs2 hStar hgM hg'
      · exact s15_Six_step2 D h h151.isElemAbelian hL (by omega) (Or.inl (fun h' => hs2 h'.1))
          hgM hg'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
