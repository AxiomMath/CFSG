module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma216Aux
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210SetupOrbit

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem IsDirectProduct.conj_eq_coord_conj {S : Set (Subgroup Γ)} {K : Subgroup Γ}
    (hK : IsDirectProduct S K) {J : Subgroup Γ} (hJ : J ∈ S) {y : Γ} (hy : y ∈ K) {x : Γ}
    (hx : x ∈ J) :
    y * x * y⁻¹ = ((hK.coord hJ ⟨y, hy⟩ : J) : Γ) * x * ((hK.coord hJ ⟨y, hy⟩ : J) : Γ)⁻¹ := by
  set c : Γ := ((hK.coord hJ ⟨y, hy⟩ : J) : Γ) with hc
  have hcK : c ∈ K := hK.le hJ (hK.coord hJ ⟨y, hy⟩).2
  have hl : c⁻¹ * y ∈ sSup (S \ {J}) := by
    rw [← hK.coord_eq_one_iff hJ ⟨c⁻¹ * y, mul_mem (inv_mem hcK) hy⟩]
    have e : (⟨c⁻¹ * y, mul_mem (inv_mem hcK) hy⟩ : K) = ⟨c⁻¹, inv_mem hcK⟩ * ⟨y, hy⟩ := rfl
    rw [e, map_mul]
    have h1 : hK.coord hJ ⟨c⁻¹, inv_mem hcK⟩ = (hK.coord hJ ⟨y, hy⟩)⁻¹ :=
      Subtype.ext (hK.coord_of_mem hJ (inv_mem (hK.coord hJ ⟨y, hy⟩).2))
    rw [h1, inv_mul_cancel]
  have hcomm : x * (c⁻¹ * y) = (c⁻¹ * y) * x := (hK.commute_sSup_diff hJ x hx _ hl).eq
  calc y * x * y⁻¹ = c * ((c⁻¹ * y) * x * (c⁻¹ * y)⁻¹) * c⁻¹ := by group
    _ = c * x * c⁻¹ := by rw [← hcomm]; group

theorem IsDirectProduct.commutator_eq_coord {S : Set (Subgroup Γ)} {K : Subgroup Γ}
    (hK : IsDirectProduct S K) {J : Subgroup Γ} (hJ : J ∈ S) {y : Γ} (hy : y ∈ K) {x : Γ}
    (hx : x ∈ J) : ⁅y, x⁆ = ⁅((hK.coord hJ ⟨y, hy⟩ : J) : Γ), x⁆ := by
  have := hK.conj_eq_coord_conj hJ hy hx
  simp only [commutatorElement_def]
  rw [this]

namespace Near

open Thm210

variable {p : ℕ} {A G J : Subgroup Γ}

theorem SemisimpleAction.coord_commutator (h : SemisimpleAction p A G) (hJ : J ∈ lcal G)
    {g : Γ} (hg : g ∈ Subgroup.normalizer (G : Set Γ))
    (hgJ : g ∈ Subgroup.normalizer (J : Set Γ)) {y : Γ} (hy : y ∈ G) :
    ((h.isDirectProduct_lcal.coord hJ
        ⟨⁅g, y⁆, Lemma216.commutator_mem_of_mem_normalizer hg hy⟩ : J) : Γ) =
      ⁅g, ((h.isDirectProduct_lcal.coord hJ ⟨y, hy⟩ : J) : Γ)⁆ := by
  have hP := h.isDirectProduct_lcal
  have ha : ∀ J' ∈ lcal G, J'.map (MulAut.conj g).toMonoidHom ∈ lcal G :=
    fun J' hJ' => map_conj_mem_lcal hJ' hg
  have hgy : g * y * g⁻¹ ∈ G := hP.conj_mem ha hy
  have e1 : (⟨⁅g, y⁆, Lemma216.commutator_mem_of_mem_normalizer hg hy⟩ : ↥G) =
      ⟨g * y * g⁻¹, hgy⟩ * ⟨y, hy⟩⁻¹ := Subtype.ext (by simp [commutatorElement_def])
  rw [e1, map_mul, map_inv, Subgroup.coe_mul, InvMemClass.coe_inv]
  have e2 := hP.coord_conj ha hJ hy
  have e3 := hP.coord_val_congr (ha J hJ) hJ (Subgroup.mem_normalizer_iff_map_conj_eq.mp hgJ)
    ⟨g * y * g⁻¹, hgy⟩
  rw [← e3, e2]
  simp [commutatorElement_def]

theorem SemisimpleAction.exists_mem_kProd_centralizer (h : SemisimpleAction p A G) {g : Γ}
    (hg : ∀ J ∈ lcal G, ∃ m ∈ kJ A J, ∀ x ∈ J, g * x * g⁻¹ = m * x * m⁻¹) :
    ∃ m ∈ kProd A G, m⁻¹ * g ∈ Subgroup.centralizer (G : Set Γ) := by
  have hP := h.isDirectProduct_lcal
  choose! m hm hmx using hg
  let z : (J : lcal G) → ↥(J : Subgroup Γ) := fun J => ⟨m J.1, kJ_le A J.1 (hm J.1 J.2)⟩
  have hz : ∀ J : lcal G, ((z J : ↥(J : Subgroup Γ)) : Γ) ∈ kProd A G := fun J => by
    have hle : kJ A J.1 ≤ kProd A G := le_sSup ⟨J.1, J.2, rfl⟩
    exact hle (hm J.1 J.2)
  refine ⟨((hP.equiv z : ↥G) : Γ), hP.equiv_mem z hz, ?_⟩
  set m0 : Γ := ((hP.equiv z : ↥G) : Γ) with hm0
  have hm0G : m0 ∈ G := (hP.equiv z).2
  have hcent : ∀ J ∈ lcal G, J ≤ Subgroup.centralizer {m0⁻¹ * g} := by
    intro J hJ x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 := hP.conj_eq_coord_conj hJ hm0G hx
    have e2 : ((hP.coord hJ ⟨m0, hm0G⟩ : J) : Γ) = m J :=
      congrArg Subtype.val (hP.coord_equiv hJ z)
    rw [e2, ← hmx J hJ x hx] at e1
    have e3 : g * x = m0 * x * m0⁻¹ * g := by rw [e1]; group
    calc x * (m0⁻¹ * g) = m0⁻¹ * (m0 * x * m0⁻¹ * g) := by group
      _ = m0⁻¹ * (g * x) := by rw [e3]
      _ = m0⁻¹ * g * x := by group
  have hG : G ≤ Subgroup.centralizer {m0⁻¹ * g} := by
    rw [← hP.sSup_eq]
    exact sSup_le fun J hJ => hcent J hJ
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hG hx)

theorem SemisimpleAction.exists_smear_coord (h : SemisimpleAction p A G) (hJ : J ∈ lcal G)
    {v : Γ} (hv : v ∈ cenIn J (norIn A J)) :
    ∃ (d : Γ) (hd : d ∈ G), d ∈ smear J A ∧
      ((h.isDirectProduct_lcal.coord hJ ⟨d, hd⟩ : J) : Γ) = v := by
  rw [← h.projIn_smear hJ] at hv
  obtain ⟨y, hy, rfl⟩ := (h.isDirectProduct_lcal.mem_projIn_iff hJ).mp hv
  exact ⟨y, y.2, hy, rfl⟩

theorem SemisimpleAction.commutator_mem_fitting_of_smear (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) {d : Γ} (hdG : d ∈ G) (hd : d ∈ smear J A)
    (hdc : ∀ c ∈ cenIn J (norIn A J),
      ⁅((h.isDirectProduct_lcal.coord hJ ⟨d, hdG⟩ : J) : Γ), c⁆ ∈
        CFSG.fittingSubgroupOf (cenIn J (norIn A J)))
    {e : Γ} (he : e ∈ cenIn G A) : ⁅d, e⁆ ∈ CFSG.fittingSubgroupOf (cenIn G A) := by
  have hP := h.isDirectProduct_lcal
  have hD := h.isDirectProduct_smear
  have hT : smear J A ∈ {X | ∃ J' ∈ lcal G, X = smear J' A} := ⟨J, hJ, rfl⟩
  have he' : e ∈ smear J A ⊔ sSup ({X | ∃ J' ∈ lcal G, X = smear J' A} \ {smear J A}) := by
    rw [(hD.isDirectPair hT).sup_eq]
    exact he
  obtain ⟨e₁, he₁, e₂, he₂, rfl⟩ := (mem_sup_iff_of_commute (hD.commute_sSup_diff hT)).mp he'
  have hcomm : ⁅d, e₁ * e₂⁆ = ⁅d, e₁⁆ := by
    have h3 : ⁅d, e₂⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (hD.commute_sSup_diff hT d hd e₂ he₂).eq
    have h4 : ⁅d, e₁ * e₂⁆ = ⁅d, e₁⁆ * (e₁ * ⁅d, e₂⁆ * e₁⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h4, h3]
    simp
  rw [hcomm]
  have he₁G : e₁ ∈ G := (mem_cenIn_iff.mp (h.smear_le_cenIn hJ he₁)).1
  have hc₁ : ((hP.coord hJ ⟨e₁, he₁G⟩ : J) : Γ) ∈ cenIn J (norIn A J) := by
    rw [← h.projIn_smear hJ]
    exact (hP.mem_projIn_iff hJ).mpr ⟨⟨e₁, he₁G⟩, he₁, rfl⟩
  have hdJ : d ∈ Subgroup.normalizer (J : Set Γ) := hP.le_normalizer hJ hdG
  have hcomm1 := h.coord_commutator hJ (Subgroup.le_normalizer hdG) hdJ he₁G
  have hcJ : ((hP.coord hJ ⟨e₁, he₁G⟩ : J) : Γ) ∈ J := (hP.coord hJ _).2
  have hFC : ⁅d, ((hP.coord hJ ⟨e₁, he₁G⟩ : J) : Γ)⁆ ∈
      CFSG.fittingSubgroupOf (cenIn J (norIn A J)) := by
    rw [hP.commutator_eq_coord hJ hdG hcJ]
    exact hdc _ hc₁
  rw [← h.projIn_fittingSubgroupOf_smear hJ] at hFC
  obtain ⟨z, hzF, hzc⟩ := (hP.mem_projIn_iff hJ).mp hFC
  have hwT : ⁅d, e₁⁆ ∈ smear J A := by
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hd he₁) (inv_mem hd)) (inv_mem he₁)
  have hwG : ⁅d, e₁⁆ ∈ G := (mem_cenIn_iff.mp (h.smear_le_cenIn hJ hwT)).1
  have hzT : (z : Γ) ∈ smear J A := (Subgroup.map_subtype_le _) hzF
  have hu : (z : Γ)⁻¹ * ⁅d, e₁⁆ ∈ smear J A ⊓ sSup (lcal G \ {J}) := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hzT) hwT, ?_⟩
    have hG' : (z : Γ)⁻¹ * ⁅d, e₁⁆ ∈ G := mul_mem (inv_mem z.2) hwG
    rw [← hP.coord_eq_one_iff hJ ⟨_, hG'⟩]
    have e : (⟨(z : Γ)⁻¹ * ⁅d, e₁⁆, hG'⟩ : ↥G) = z⁻¹ * ⟨⁅d, e₁⁆, hwG⟩ := rfl
    rw [e, map_mul, map_inv]
    have hzw : hP.coord hJ z = hP.coord hJ ⟨⁅d, e₁⁆, hwG⟩ := Subtype.ext (hzc.trans hcomm1.symm)
    rw [hzw, inv_mul_cancel]
  rw [h.smear_inf_sSup hJ, Subgroup.mem_bot, inv_mul_eq_one] at hu
  rw [← hu]
  exact h.fittingSubgroupOf_smear_le hJ hzF

theorem SemisimpleAction.coord_commutator_mem_fitting_kJ
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) {d : Γ} (hdG : d ∈ G)
    (hdc : ∀ e ∈ cenIn G A, ⁅d, e⁆ ∈ CFSG.fittingSubgroupOf (cenIn G A)) :
    ∀ c ∈ cenIn J (norIn A J),
      ⁅((h.isDirectProduct_lcal.coord hJ ⟨d, hdG⟩ : J) : Γ), c⁆ ∈
        CFSG.fittingSubgroupOf (kJ A J) := by
  have hP := h.isDirectProduct_lcal
  intro c hc
  rw [← h.projIn_cenIn hJ] at hc
  obtain ⟨e, he, rfl⟩ := (hP.mem_projIn_iff hJ).mp hc
  have hdN : d ∈ Subgroup.normalizer (G : Set Γ) := Subgroup.le_normalizer hdG
  have hdJ : d ∈ Subgroup.normalizer (J : Set Γ) := hP.le_normalizer hJ hdG
  have hcomm1 := h.coord_commutator hJ hdN hdJ e.2
  have hcJ : ((hP.coord hJ e : J) : Γ) ∈ J := (hP.coord hJ e).2
  have hmem : ⁅d, (e : Γ)⁆ ∈ CFSG.fittingSubgroupOf (cenIn G A) := hdc _ he
  have hproj : ((hP.coord hJ ⟨⁅d, (e : Γ)⁆,
      Lemma216.commutator_mem_of_mem_normalizer hdN e.2⟩ : J) : Γ) ∈
        CFSG.fittingSubgroupOf (cenIn J (norIn A J)) := by
    rw [← h.projIn_fittingSubgroupOf_cenIn hJ]
    exact (hP.mem_projIn_iff hJ).mpr ⟨⟨_, Lemma216.commutator_mem_of_mem_normalizer hdN e.2⟩,
      hmem, rfl⟩
  rw [← hP.commutator_eq_coord hJ hdG hcJ]
  have e1 : ⁅d, ((hP.coord hJ e : J) : Γ)⁆ = ((hP.coord hJ ⟨⁅d, (e : Γ)⁆,
      Lemma216.commutator_mem_of_mem_normalizer hdN e.2⟩ : J) : Γ) := hcomm1.symm
  rw [e1]
  exact h.fittingSubgroupOf_cenIn_le_kJ hJ hproj

end Near

end CFSG.SignalizerFunctorTheorem.McBride
