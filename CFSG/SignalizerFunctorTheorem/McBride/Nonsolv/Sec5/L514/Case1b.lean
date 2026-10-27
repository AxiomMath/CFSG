module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514.Case1a
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.PermutationAction
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.ThreeSubgroups

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem not_fitting_le_centralizer
    {p : ℕ} {A G J : Subgroup Γ} (h : KSetting p A G)
    (hJ : J ∈ lcalA G A) {J' : Subgroup Γ} (hJ' : J' ∈ conjOrbit A J) :
    ¬ CFSG.inSubgroup CFSG.generalizedFitting (smear J A) ≤
      Subgroup.centralizer (J' : Set Γ) := by
  intro hFc
  have hAG := h.normalizes
  have hL := isDirectProduct_conjOrbit hAG hJ.1
  have hdp := hL.isDirectPair hJ'
  obtain ⟨hFs, hFnc⟩ := smear_fitting_isSimple h hJ
  obtain ⟨hJs, hJnc⟩ := (mem_lcal_iff.mp (conjOrbit_subset_lcal hAG hJ.1 hJ')).2.2
  have hFC : CFSG.inSubgroup CFSG.generalizedFitting (smear J A) ≤ smear J A :=
    Subgroup.map_subtype_le _
  have hFbot : CFSG.inSubgroup CFSG.generalizedFitting (smear J A) = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    have hfC := hFC hf
    have hfL : f ∈ orbitClosure J A := smear_le_orbitClosure J A hfC
    obtain ⟨j, hj, l, hl, hjl⟩ := exists_mul_of_isDirectPair hdp hfL
    have hlc : ∀ y ∈ J', y * l = l * y := fun y hy =>
      (hL.commute_sSup_diff hJ' y hy l hl).eq
    have hfc : ∀ y ∈ J', y * f = f * y := fun y hy =>
      Subgroup.mem_centralizer_iff.mp (hFc hf) y hy
    have hjc : ∀ y ∈ J', y * j = j * y := by
      intro y hy
      have hj' : j = f * l⁻¹ := by rw [← hjl]; group
      rw [hj']
      have hlc' : y * l⁻¹ = l⁻¹ * y := by
        have := hlc y hy
        calc y * l⁻¹ = l⁻¹ * (l * y) * l⁻¹ := by group
          _ = l⁻¹ * (y * l) * l⁻¹ := by rw [this]
          _ = l⁻¹ * y := by group
      calc y * (f * l⁻¹) = (y * f) * l⁻¹ := by group
        _ = (f * y) * l⁻¹ := by rw [hfc y hy]
        _ = f * (y * l⁻¹) := by group
        _ = f * (l⁻¹ * y) := by rw [hlc']
        _ = (f * l⁻¹) * y := by group
    have hj1 : j = 1 := eq_one_of_forall_commute hJnc hj hjc
    have hfl : f ∈ sSup (conjOrbit A J \ {J'}) := by
      rw [hj1, one_mul] at hjl
      exact hjl ▸ hl
    have hper : ∀ a ∈ A, ∀ K ∈ conjOrbit A J, K.map (MulAut.conj a).toMonoidHom ∈ conjOrbit A J :=
      fun a ha K hK => map_conj_mem_conjOrbit hK ha
    have hbot : orbitClosure J A ⊓ Subgroup.centralizer (A : Set Γ) ⊓
        sSup (conjOrbit A J \ {J'}) = ⊥ :=
      inf_centralizer_inf_sSup_eq_bot_of_transitive hL hper hJ'
        (fun K hK => exists_conj_of_mem_conjOrbit hJ' hK)
    have hmem : f ∈ orbitClosure J A ⊓ Subgroup.centralizer (A : Set Γ) ⊓
        sSup (conjOrbit A J \ {J'}) :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hfL, smear_le_centralizer J A hfC⟩, hfl⟩
    rw [hbot] at hmem
    exact hmem
  apply hFnc
  rw [hFbot]
  infer_instance

theorem le_centralizer_fitting
    {p : ℕ} {A G X J : Subgroup Γ} (h : KSetting p A G)
    (hXG : X ≤ G) (hDX : G ⊓ Subgroup.centralizer (A : Set Γ) ≤ Subgroup.normalizer (X : Set Γ))
    (hAX : A ≤ Subgroup.normalizer (X : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcalA G A)
    (hbot : projX G A J X ⊓ smear J A = ⊥) :
    X ≤ Subgroup.centralizer
      ((CFSG.inSubgroup CFSG.generalizedFitting (smear J A) : Subgroup Γ) : Set Γ) := by
  have hAG := h.normalizes
  obtain ⟨hFs, hFnc⟩ := smear_fitting_isSimple h hJ
  have hperf := commutator_self_eq_of_isSimpleGroup hFnc
  have hFC : CFSG.inSubgroup CFSG.generalizedFitting (smear J A) ≤ smear J A :=
    Subgroup.map_subtype_le _
  have hFL := hFC.trans (smear_le_orbitClosure J A)
  have hFXM : ⁅CFSG.inSubgroup CFSG.generalizedFitting (smear J A), X⁆ ≤ outsideOrbit G A J := by
    rw [Subgroup.commutator_le]
    intro f hf x hx
    exact commutator_mem_outsideOrbit h hXG hDX hAX hsol hJ hbot (hFC hf) hx
  have hMF : outsideOrbit G A J ≤
      Subgroup.centralizer ((CFSG.inSubgroup CFSG.generalizedFitting (smear J A) : Subgroup Γ) :
        Set Γ) :=
    (outsideOrbit_le_centralizer hAG hsol hJ.1).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hFL))
  have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hFXM.trans hMF)
  have h2 : ⁅⁅X, CFSG.inSubgroup CFSG.generalizedFitting (smear J A)⁆,
      CFSG.inSubgroup CFSG.generalizedFitting (smear J A)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm X]
    exact h1
  have h3 := three_subgroups_lemma h1 h2
  rw [hperf, Subgroup.commutator_comm] at h3
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3

theorem map_conj_mem_conjOrbit_of_centralizes_fitting
    {p : ℕ} {A G J : Subgroup Γ}
    (h : KSetting p A G) (hsol : sol G = ⊥) (hJ : J ∈ lcalA G A) {g : Γ}
    (hgG : g ∈ Subgroup.normalizer (G : Set Γ))
    (hgF : g ∈ Subgroup.centralizer
      ((CFSG.inSubgroup CFSG.generalizedFitting (smear J A) : Subgroup Γ) : Set Γ))
    {J' : Subgroup Γ} (hJ' : J' ∈ conjOrbit A J) :
    J'.map (MulAut.conj g).toMonoidHom ∈ conjOrbit A J := by
  have hAG := h.normalizes
  by_contra hnot
  have hmem : J'.map (MulAut.conj g).toMonoidHom ∈ lcal G \ conjOrbit A J :=
    ⟨map_conj_mem_lcal (conjOrbit_subset_lcal hAG hJ.1 hJ') hgG, hnot⟩
  have hJM : J'.map (MulAut.conj g).toMonoidHom ≤ outsideOrbit G A J := le_sSup hmem
  have hFC : CFSG.inSubgroup CFSG.generalizedFitting (smear J A) ≤ smear J A :=
    Subgroup.map_subtype_le _
  refine not_fitting_le_centralizer h hJ hJ' fun f hf => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hfL : f ∈ orbitClosure J A := smear_le_orbitClosure J A (hFC hf)
  have hz : g * y * g⁻¹ ∈ outsideOrbit G A J := hJM ⟨y, hy, rfl⟩
  have h1 : f * (g * y * g⁻¹) = (g * y * g⁻¹) * f :=
    (commute_of_mem_orbitClosure hAG hsol hJ.1 hfL hz).eq
  have h2 : f * g = g * f := Subgroup.mem_centralizer_iff.mp hgF f hf
  have h3 : g⁻¹ * f * g = f := by
    calc g⁻¹ * f * g = g⁻¹ * (f * g) := by group
      _ = g⁻¹ * (g * f) := by rw [h2]
      _ = f := by group
  have h4 : g⁻¹ * f * g * y = y * (g⁻¹ * f * g) := by
    calc g⁻¹ * f * g * y = g⁻¹ * (f * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * f) * g := by rw [h1]
      _ = y * (g⁻¹ * f * g) := by group
  rw [h3] at h4
  exact h4.symm

theorem le_centralizer_of_projX_inf_eq_bot
    {p : ℕ} {A G X J : Subgroup Γ} (h : KSetting p A G)
    (hXG : X ≤ G) (hDX : G ⊓ Subgroup.centralizer (A : Set Γ) ≤ Subgroup.normalizer (X : Set Γ))
    (hAX : A ≤ Subgroup.normalizer (X : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcalA G A)
    (hbot : projX G A J X ⊓ smear J A = ⊥) : X ≤ Subgroup.centralizer (J : Set Γ) := by
  have hAG := h.normalizes
  have hL := isDirectProduct_conjOrbit hAG hJ.1
  have hJΩ := self_mem_conjOrbit A J
  have hdp := isDirectPair_orbitClosure_outsideOrbit hAG hsol hJ.1
  have hdpJ := hL.isDirectPair hJΩ
  have hper : ∀ a ∈ A, ∀ K ∈ conjOrbit A J, K.map (MulAut.conj a).toMonoidHom ∈ conjOrbit A J :=
    fun a ha K hK => map_conj_mem_conjOrbit hK ha
  have hFcent := le_centralizer_fitting h hXG hDX hAX hsol hJ hbot
  have hFC : CFSG.inSubgroup CFSG.generalizedFitting (smear J A) ≤ smear J A :=
    Subgroup.map_subtype_le _
  have hAF : A ≤ Subgroup.centralizer
      ((CFSG.inSubgroup CFSG.generalizedFitting (smear J A) : Subgroup Γ) : Set Γ) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (Subgroup.mem_centralizer_iff.mp (smear_le_centralizer J A (hFC hf)) a ha).symm
  have hXcop : Nat.Coprime p (Nat.card X) :=
    h.hypB.2.1.coprime_dvd_right (Subgroup.card_dvd_of_le hXG)
  have hΩ : ∀ g ∈ X ⊔ A, ∀ K ∈ conjOrbit A J,
      K.map (MulAut.conj g).toMonoidHom ∈ conjOrbit A J := by
    intro g hg K hK
    exact map_conj_mem_conjOrbit_of_centralizes_fitting h hsol hJ
      (sup_le (hXG.trans Subgroup.le_normalizer) hAG hg) (sup_le hFcent hAF hg) hK
  have htrans : ∀ K ∈ conjOrbit A J, ∀ K' ∈ conjOrbit A J,
      ∃ a ∈ A, K' = K.map (MulAut.conj a).toMonoidHom :=
    fun K hK K' hK' => exists_conj_of_mem_conjOrbit hK hK'
  have hnorm := normalizes_of_isPGroup_transitive_conj h.prime
    (isPGroup_of_isElemAbelian h.elemAbelian) hXcop hAX hΩ htrans
  intro x hx
  have hxN : ∀ K ∈ conjOrbit A J, x ∈ Subgroup.normalizer (K : Set Γ) :=
    fun K hK => hnorm x hx K hK
  have hxN' : ∀ K ∈ conjOrbit A J, x⁻¹ ∈ Subgroup.normalizer (K : Set Γ) :=
    fun K hK => inv_mem (hxN K hK)
  have hxL : x ∈ Subgroup.normalizer ((orbitClosure J A : Subgroup Γ) : Set Γ) := by
    rw [orbitClosure_eq_sSup]
    exact mem_normalizer_sSup
      (fun K hK => by rw [map_conj_eq_of_mem_normalizer (hxN K hK)]; exact hK)
      (fun K hK => by rw [map_conj_eq_of_mem_normalizer (hxN' K hK)]; exact hK)
  have hcent : ∀ c ∈ smear J A, x * c * x⁻¹ = c := by
    intro c hc
    have hcM := commutator_mem_outsideOrbit h hXG hDX hAX hsol hJ hbot hc hx
    have hcL : c ∈ orbitClosure J A := smear_le_orbitClosure J A hc
    have hcL' : ⁅c, x⁆ ∈ orbitClosure J A := by
      have : ⁅c, x⁆ = c * (x * c⁻¹ * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      exact mul_mem hcL ((Subgroup.mem_normalizer_iff.mp hxL c⁻¹).mp (inv_mem hcL))
    have h1 : ⁅c, x⁆ ∈ orbitClosure J A ⊓ outsideOrbit G A J :=
      Subgroup.mem_inf.mpr ⟨hcL', hcM⟩
    rw [hdp.inf_eq_bot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    calc x * c * x⁻¹ = (c * x) * x⁻¹ := by rw [← h1]
      _ = c := by group
  have hfix : ∀ z ∈ J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ), x * z * x⁻¹ = z := by
    intro z hz
    rw [← projIn_centralizer_eq hL hper hJΩ] at hz
    obtain ⟨hzJ, l, hl, hzl⟩ := (mem_proj_iff hdpJ.commute).mp hz
    have hc := hcent (z * l) hzl
    have hxz : x * z * x⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hxN J hJΩ) z).mp hzJ
    have hxl : x * l * x⁻¹ ∈ sSup (conjOrbit A J \ {J}) := by
      refine conj_mem_sSup (fun K hK => ?_) hl
      rw [map_conj_eq_of_mem_normalizer (hxN K hK.1)]
      exact hK
    have hprod : (x * z * x⁻¹) * (x * l * x⁻¹) = z * l := by rw [← hc]; group
    exact (eq_of_mul_eq_of_isDirectPair hdpJ hxz hzJ hxl hl hprod).1
  have hxp : Nat.Coprime p (orderOf x) :=
    h.hypB.2.1.coprime_dvd_right (Subgroup.orderOf_dvd_natCard G (hXG hx))
  have hxc := centralizes_of_centralizes_fixed h hJ (hxN J hJΩ) hxp hfix
  exact Subgroup.mem_centralizer_iff.mpr fun j hj => (mul_inv_eq_iff_eq_mul.mp (hxc j hj)).symm

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514
