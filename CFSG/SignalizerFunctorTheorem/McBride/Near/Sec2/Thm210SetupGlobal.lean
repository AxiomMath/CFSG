module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Setup
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210Aux2

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

variable {Γ : Type*} [Group Γ] {p : ℕ} {A G J : Subgroup Γ}

@[expose] def kProd (A G : Subgroup Γ) : Subgroup Γ :=
  sSup {X | ∃ J ∈ lcal G, X = kJ A J}

@[expose] def fProd (A G : Subgroup Γ) : Subgroup Γ :=
  sSup {X | ∃ J ∈ lcal G, X = CFSG.fittingSubgroupOf (kJ A J)}

theorem fittingSubgroupOf_kJ_le (A J : Subgroup Γ) : CFSG.fittingSubgroupOf (kJ A J) ≤ J :=
  (Subgroup.map_subtype_le _).trans (kJ_le A J)

theorem kProd_le (A G : Subgroup Γ) : kProd A G ≤ G := by
  refine sSup_le ?_
  rintro _ ⟨J, hJ, rfl⟩
  exact (kJ_le A J).trans (lcal_le hJ)

theorem fProd_le_kProd (A G : Subgroup Γ) : fProd A G ≤ kProd A G := by
  refine sSup_le ?_
  rintro _ ⟨J, hJ, rfl⟩
  exact (Subgroup.map_subtype_le _).trans (le_sSup ⟨J, hJ, rfl⟩)

theorem fProd_le (A G : Subgroup Γ) : fProd A G ≤ G :=
  (fProd_le_kProd A G).trans (kProd_le A G)

section Finite

variable [Finite Γ]

theorem SemisimpleAction.isDirectProduct_kProd (h : SemisimpleAction p A G) :
    IsDirectProduct {X | ∃ J ∈ lcal G, X = kJ A J} (kProd A G) :=
  isDirectProduct_image h.isDirectProduct_lcal (kJ A) fun J _ => kJ_le A J

theorem SemisimpleAction.isDirectProduct_fProd (h : SemisimpleAction p A G) :
    IsDirectProduct {X | ∃ J ∈ lcal G, X = CFSG.fittingSubgroupOf (kJ A J)} (fProd A G) :=
  isDirectProduct_image h.isDirectProduct_lcal (fun J => CFSG.fittingSubgroupOf (kJ A J))
    fun J _ => fittingSubgroupOf_kJ_le A J

theorem SemisimpleAction.mem_kProd_iff (h : SemisimpleAction p A G) {x : Γ} :
    x ∈ kProd A G ↔ ∃ hx : x ∈ G, ∀ (J : Subgroup Γ) (hJ : J ∈ lcal G),
      ((h.isDirectProduct_lcal.coord hJ ⟨x, hx⟩ : J) : Γ) ∈ kJ A J :=
  mem_sSup_image_iff h.isDirectProduct_lcal (T := kJ A) fun J _ => kJ_le A J

theorem SemisimpleAction.mem_fProd_iff (h : SemisimpleAction p A G) {x : Γ} :
    x ∈ fProd A G ↔ ∃ hx : x ∈ G, ∀ (J : Subgroup Γ) (hJ : J ∈ lcal G),
      ((h.isDirectProduct_lcal.coord hJ ⟨x, hx⟩ : J) : Γ) ∈ CFSG.fittingSubgroupOf (kJ A J) :=
  mem_sSup_image_iff h.isDirectProduct_lcal (T := fun J => CFSG.fittingSubgroupOf (kJ A J))
    fun J _ => fittingSubgroupOf_kJ_le A J

theorem SemisimpleAction.le_kProd_iff (h : SemisimpleAction p A G) {X : Subgroup Γ} :
    X ≤ kProd A G ↔ X ≤ G ∧ ∀ J ∈ lcal G, projIn (lcal G) J X ≤ kJ A J :=
  le_sSup_image_iff h.isDirectProduct_lcal (T := kJ A) fun J _ => kJ_le A J

theorem SemisimpleAction.le_fProd_iff (h : SemisimpleAction p A G) {X : Subgroup Γ} :
    X ≤ fProd A G ↔
      X ≤ G ∧ ∀ J ∈ lcal G, projIn (lcal G) J X ≤ CFSG.fittingSubgroupOf (kJ A J) :=
  le_sSup_image_iff h.isDirectProduct_lcal (T := fun J => CFSG.fittingSubgroupOf (kJ A J))
    fun J _ => fittingSubgroupOf_kJ_le A J

theorem SemisimpleAction.kProd_inf (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    kProd A G ⊓ J = kJ A J := by
  refine le_antisymm (fun x hx => ?_) (le_inf (le_sSup ⟨J, hJ, rfl⟩) (kJ_le A J))
  obtain ⟨hxK, hxJ⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxG, hc⟩ := h.mem_kProd_iff.mp hxK
  have := hc J hJ
  rwa [h.isDirectProduct_lcal.coord_of_mem hJ hxJ] at this

theorem SemisimpleAction.fProd_inf (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    fProd A G ⊓ J = CFSG.fittingSubgroupOf (kJ A J) := by
  refine le_antisymm (fun x hx => ?_) (le_inf (le_sSup ⟨J, hJ, rfl⟩) (fittingSubgroupOf_kJ_le A J))
  obtain ⟨hxK, hxJ⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxG, hc⟩ := h.mem_fProd_iff.mp hxK
  have := hc J hJ
  rwa [h.isDirectProduct_lcal.coord_of_mem hJ hxJ] at this

theorem SemisimpleAction.isSolvable_kProd
    (h : SemisimpleAction p A G) :
    Group.IsSolvable (kProd A G) := by
  refine isSolvable_of_forall_projIn h.isDirectProduct_lcal (kProd_le A G) fun J hJ => ?_
  have hle : projIn (lcal G) J (kProd A G) ≤ kJ A J := (h.le_kProd_iff.mp le_rfl).2 J hJ
  have := h.isSolvable_kJ hJ
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem SemisimpleAction.isMulCommutative_fProd
    (h : SemisimpleAction p A G) :
    IsMulCommutative (fProd A G) := by
  refine isMulCommutative_of_forall_projIn h.isDirectProduct_lcal (fProd_le A G) fun J hJ => ?_
  have hle : projIn (lcal G) J (fProd A G) ≤ CFSG.fittingSubgroupOf (kJ A J) :=
    (h.le_fProd_iff.mp le_rfl).2 J hJ
  have := h.isMulCommutative_fittingSubgroupOf_kJ hJ
  exact isMulCommutative_of_le hle

theorem SemisimpleAction.kProd_le_normalizer (h : SemisimpleAction p A G) :
    kProd A G ≤ Subgroup.normalizer (fProd A G : Set Γ) := by
  refine le_normalizer_of_conj_mem fun g hg x hx => ?_
  obtain ⟨hgG, hgc⟩ := h.mem_kProd_iff.mp hg
  obtain ⟨hxG, hxc⟩ := h.mem_fProd_iff.mp hx
  refine h.mem_fProd_iff.mpr ⟨mul_mem (mul_mem hgG hxG) (inv_mem hgG), fun J hJ => ?_⟩
  have e : (⟨g * x * g⁻¹, mul_mem (mul_mem hgG hxG) (inv_mem hgG)⟩ : ↥G) =
      ⟨g, hgG⟩ * ⟨x, hxG⟩ * ⟨g, hgG⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]
  exact fittingSubgroupOf_conj_mem (hgc J hJ) (hxc J hJ)

theorem SemisimpleAction.norIn_fProd
    (h : SemisimpleAction p A G) :
    norIn G (fProd A G) = kProd A G := by
  refine le_antisymm (fun g hg => ?_) (le_inf (kProd_le A G) h.kProd_le_normalizer)
  obtain ⟨hgG, hgN⟩ := mem_norIn_iff.mp hg
  have hG := h.isDirectProduct_lcal
  refine h.mem_kProd_iff.mpr ⟨hgG, fun J hJ => ?_⟩
  have key : ∀ (g' : Γ) (hg'G : g' ∈ G), g' ∈ Subgroup.normalizer (fProd A G : Set Γ) →
      ∀ y ∈ CFSG.fittingSubgroupOf (kJ A J),
        ((hG.coord hJ ⟨g', hg'G⟩ : J) : Γ) * y * ((hG.coord hJ ⟨g', hg'G⟩ : J) : Γ)⁻¹ ∈
          CFSG.fittingSubgroupOf (kJ A J) := by
    intro g' hg'G hg'N y hy
    have hyJ : y ∈ J := fittingSubgroupOf_kJ_le A J hy
    have hle : CFSG.fittingSubgroupOf (kJ A J) ≤ fProd A G := le_sSup ⟨J, hJ, rfl⟩
    have hyF : y ∈ fProd A G := hle hy
    have hconj : g' * y * g'⁻¹ ∈ fProd A G :=
      (Subgroup.mem_normalizer_iff.mp hg'N y).mp hyF
    obtain ⟨hw, hc⟩ := h.mem_fProd_iff.mp hconj
    have h1 := hc J hJ
    have e : (⟨g' * y * g'⁻¹, hw⟩ : ↥G) = ⟨g', hg'G⟩ * ⟨y, hG.le hJ hyJ⟩ * ⟨g', hg'G⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv] at h1
    have h2 : ((hG.coord hJ ⟨y, hG.le hJ hyJ⟩ : J) : Γ) = y := hG.coord_of_mem hJ hyJ
    change ((hG.coord hJ ⟨g', hg'G⟩ : J) : Γ) * ((hG.coord hJ ⟨y, hG.le hJ hyJ⟩ : J) : Γ) *
      ((hG.coord hJ ⟨g', hg'G⟩ : J) : Γ)⁻¹ ∈ CFSG.fittingSubgroupOf (kJ A J) at h1
    rwa [h2] at h1
  have hcJ : ((hG.coord hJ ⟨g, hgG⟩ : J) : Γ) ∈ J := (hG.coord hJ ⟨g, hgG⟩).2
  have hcN : ((hG.coord hJ ⟨g, hgG⟩ : J) : Γ) ∈
      Subgroup.normalizer (CFSG.fittingSubgroupOf (kJ A J) : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => key g hgG hgN y hy, fun hy => ?_⟩
    have h1 := key g⁻¹ (inv_mem hgG) (inv_mem hgN) _ hy
    have e : hG.coord hJ ⟨g⁻¹, inv_mem hgG⟩ = (hG.coord hJ ⟨g, hgG⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [e] at h1
    simpa [mul_assoc] using h1
  have : ((hG.coord hJ ⟨g, hgG⟩ : J) : Γ) ∈ norIn J (CFSG.fittingSubgroupOf (kJ A J)) :=
    mem_norIn_iff.mpr ⟨hcJ, hcN⟩
  rwa [h.norIn_fittingSubgroupOf_kJ hJ] at this

theorem SemisimpleAction.le_kProd_of_solvable
    (h : SemisimpleAction p A G) {X : Subgroup Γ}
    (hXG : X ≤ G) (hD : cenIn G A ≤ X) (hX : Group.IsSolvable X) : X ≤ kProd A G := by
  have hG := h.isDirectProduct_lcal
  refine h.le_kProd_iff.mpr ⟨hXG, fun J hJ => ?_⟩
  have hsol : Group.IsSolvable (projIn (lcal G) J X) := isSolvable_projIn hG hJ hXG hX
  have hCX : cenIn J (norIn A J) ≤ projIn (lcal G) J X := by
    rw [← h.projIn_cenIn hJ]
    exact projIn_mono J hD
  refine h.le_kJ_of_le_of_ne hJ (projIn_le J X) hCX fun he => ?_
  exact not_isSolvable_of_mem_lcal hJ (he ▸ hsol)

theorem SemisimpleAction.le_fProd_of_nilpotent
    (h : SemisimpleAction p A G) {Y : Subgroup Γ}
    (hYG : Y ≤ G) (hY : Group.IsNilpotent Y)
    (hD : ∀ d ∈ cenIn G A, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y) : Y ≤ fProd A G := by
  have hG := h.isDirectProduct_lcal
  refine h.le_fProd_iff.mpr ⟨hYG, fun J hJ => ?_⟩
  refine h.le_fittingSubgroupOf_kJ_of_nilpotent hJ (projIn_le J Y)
    (isNilpotent_projIn hG hJ hYG hY) ?_
  rw [← h.projIn_cenIn hJ]
  exact le_normalizer_of_conj_mem (projIn_conj_mem hG hJ hD)

theorem SemisimpleAction.fittingSubgroupOf_eq_inf_fProd
    (h : SemisimpleAction p A G)
    {X : Subgroup Γ} (hXG : X ≤ G) (hD : cenIn G A ≤ X) (hX : Group.IsSolvable X) :
    CFSG.fittingSubgroupOf X = X ⊓ fProd A G := by
  have hXK := h.le_kProd_of_solvable hXG hD hX
  refine le_antisymm (le_inf (Subgroup.map_subtype_le _) ?_) ?_
  · refine h.le_fProd_of_nilpotent ((Subgroup.map_subtype_le _).trans hXG)
      (isNilpotent_fittingSubgroupOf X) fun d hd y hy => ?_
    exact fittingSubgroupOf_conj_mem (hD hd) hy
  · have : IsMulCommutative (X ⊓ fProd A G : Subgroup Γ) := by
      have := h.isMulCommutative_fProd
      exact isMulCommutative_of_le inf_le_right
    refine le_fittingSubgroupOf_of_nilpotent inf_le_left ?_ inferInstance
    refine le_normalizer_of_conj_mem fun x hx y hy => ?_
    obtain ⟨hyX, hyF⟩ := Subgroup.mem_inf.mp hy
    exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hx hyX) (inv_mem hx),
      (Subgroup.mem_normalizer_iff.mp (h.kProd_le_normalizer (hXK hx)) y).mp hyF⟩

omit [Finite Γ] in
theorem SemisimpleAction.smear_le_cenIn (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    smear J A ≤ cenIn G A := by
  refine le_inf ((smear_le_orbitClosure J A).trans (orbitClosure_le fun a ha => ?_))
    (smear_le_centralizer J A)
  exact lcal_le (h.permutes_lcal a ha J hJ)

theorem SemisimpleAction.conj_mem_smear (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) {d y : Γ}
    (hd : d ∈ cenIn G A) (hy : y ∈ smear J A) : d * y * d⁻¹ ∈ smear J A := by
  obtain ⟨hdG, hdc⟩ := mem_cenIn_iff.mp hd
  obtain ⟨hyo, hyc⟩ := mem_smear_iff.mp hy
  refine mem_smear_iff.mpr ⟨?_, fun a ha => ?_⟩
  · have hle : orbitClosure J A ≤ (orbitClosure J A).comap (MulAut.conj d).toMonoidHom := by
      refine orbitClosure_le fun a ha x hx => ?_
      have hK : J.map (MulAut.conj a).toMonoidHom ∈ lcal G := h.permutes_lcal a ha J hJ
      have hdK := h.isDirectProduct_lcal.le_normalizer hK hdG
      exact map_conj_le_orbitClosure J ha ((Subgroup.mem_normalizer_iff.mp hdK x).mp hx)
    exact hle hyo
  · have hda : a * d * a⁻¹ = d := by
      rw [Subgroup.mem_centralizer_iff.mp hdc a ha]
      group
    calc a * (d * y * d⁻¹) * a⁻¹ = (a * d * a⁻¹) * (a * y * a⁻¹) * (a * d * a⁻¹)⁻¹ := by group
      _ = d * y * d⁻¹ := by rw [hda, hyc a ha]

private theorem orbit_setup (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    ∃ (S₁ : Set (Subgroup Γ)) (_ : IsDirectProduct S₁ (orbitClosure J A)),
      S₁ ⊆ lcal G ∧ J ∈ S₁ ∧
      projIn S₁ J (smear J A) = cenIn J (norIn A J) ∧ smear J A ⊓ sSup (S₁ \ {J}) = ⊥ := by
  have hG₁ := isDirectProduct_orbit (J := J) h.admits hJ
  have hA₁ : ∀ a ∈ A, ∀ K ∈ {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom},
      K.map (MulAut.conj a).toMonoidHom ∈
        {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom} := by
    rintro a ha _ ⟨b, hb, rfl⟩
    exact ⟨a * b, mul_mem ha hb, map_conj_map_conj J b a⟩
  have hJ₁ : J ∈ {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom} :=
    ⟨1, one_mem A, (map_conj_one J).symm⟩
  refine ⟨_, hG₁, ?_, hJ₁, projIn_centralizer_eq hG₁ hA₁ hJ₁,
    inf_centralizer_inf_sSup_eq_bot_of_transitive hG₁ hA₁ hJ₁ fun K hK => hK⟩
  rintro _ ⟨a, ha, rfl⟩
  exact h.permutes_lcal a ha J hJ

theorem SemisimpleAction.projIn_smear (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    projIn (lcal G) J (smear J A) = cenIn J (norIn A J) := by
  have hG := h.isDirectProduct_lcal
  obtain ⟨S₁, hG₁, hS₁, hJ₁, hproj, -⟩ := orbit_setup h hJ
  refine le_antisymm ?_ fun x hx => ?_
  · rw [← h.projIn_cenIn hJ]
    exact projIn_mono J (h.smear_le_cenIn hJ)
  · rw [← hproj] at hx
    obtain ⟨y, hyD, rfl⟩ := (hG₁.mem_projIn_iff hJ₁).mp hx
    exact (hG.mem_projIn_iff hJ).mpr ⟨⟨y, le_of_subset hG hG₁ hS₁ y.2⟩, hyD,
      (coord_eq_of_subset hG hG₁ hS₁ hJ₁ y.2).symm⟩

theorem SemisimpleAction.smear_inf_sSup (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    smear J A ⊓ sSup (lcal G \ {J}) = ⊥ := by
  have hG := h.isDirectProduct_lcal
  obtain ⟨S₁, hG₁, hS₁, hJ₁, -, hbot⟩ := orbit_setup h hJ
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyD, hyS⟩ := Subgroup.mem_inf.mp hy
  have hyG₁ : y ∈ orbitClosure J A := (Subgroup.mem_inf.mp hyD).1
  have hy1 : hG.coord hJ ⟨y, le_of_subset hG hG₁ hS₁ hyG₁⟩ = 1 :=
    (hG.coord_eq_one_iff hJ _).mpr hyS
  have hy2 : hG₁.coord hJ₁ ⟨y, hyG₁⟩ = 1 := by
    apply Subtype.ext
    rw [coord_eq_of_subset hG hG₁ hS₁ hJ₁ hyG₁, hy1]
  have hy3 : y ∈ sSup (S₁ \ {J}) := (hG₁.coord_eq_one_iff hJ₁ _).mp hy2
  have : y ∈ smear J A ⊓ sSup (S₁ \ {J}) := Subgroup.mem_inf.mpr ⟨hyD, hy3⟩
  rwa [hbot] at this

theorem SemisimpleAction.cenIn_le_normalizer_smear (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    cenIn G A ≤ Subgroup.normalizer (smear J A : Set Γ) :=
  le_normalizer_of_conj_mem fun _ hd _ hy => h.conj_mem_smear hJ hd hy

omit [Finite Γ] in
theorem SemisimpleAction.isSolvable_smear (h : SemisimpleAction p A G) (hJ : J ∈ lcal G) :
    Group.IsSolvable (smear J A) := by
  have := h.solvable_cen
  exact Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (h.smear_le_cenIn hJ))

theorem SemisimpleAction.fittingSubgroupOf_smear_le (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) :
    CFSG.fittingSubgroupOf (smear J A) ≤ CFSG.fittingSubgroupOf (cenIn G A) := by
  refine le_fittingSubgroupOf_of_nilpotent
    ((Subgroup.map_subtype_le _).trans (h.smear_le_cenIn hJ))
    (le_normalizer_of_conj_mem fun d hd y hy => ?_) (isNilpotent_fittingSubgroupOf _)
  exact fittingSubgroupOf_conj_mem_of_mem_normalizer (h.cenIn_le_normalizer_smear hJ hd) hy

theorem SemisimpleAction.fittingSubgroupOf_cenIn_le_projIn_smear (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) :
    CFSG.fittingSubgroupOf (cenIn J (norIn A J)) ≤
      projIn (lcal G) J (CFSG.fittingSubgroupOf (smear J A)) := by
  have hG := h.isDirectProduct_lcal
  set cJ := CFSG.fittingSubgroupOf (cenIn J (norIn A J)) with hcJ
  set N' : Subgroup ↥G := (smear J A).subgroupOf G ⊓ (cJ.subgroupOf J).comap (hG.coord hJ)
    with hN'
  set N : Subgroup Γ := N'.map G.subtype with hN
  have hmemN : ∀ y : Γ, y ∈ N ↔
      ∃ hy : y ∈ G, y ∈ smear J A ∧ ((hG.coord hJ ⟨y, hy⟩ : J) : Γ) ∈ cJ := by
    intro y
    constructor
    · rintro ⟨y', ⟨hy1, hy2⟩, rfl⟩
      exact ⟨y'.2, hy1, hy2⟩
    · rintro ⟨hy, hy1, hy2⟩
      exact ⟨⟨y, hy⟩, ⟨hy1, hy2⟩, rfl⟩
  have hND₁ : N ≤ smear J A := fun y hy => ((hmemN y).mp hy).2.1
  have hNG : N ≤ G := fun y hy => ((hmemN y).mp hy).1
  have hconj : ∀ d ∈ smear J A, ∀ y ∈ N, d * y * d⁻¹ ∈ N := by
    intro d hd y hy
    obtain ⟨hyG, hyD₁, hyc⟩ := (hmemN y).mp hy
    have hdG : d ∈ G := (h.smear_le_cenIn hJ hd).1
    have hdyG : d * y * d⁻¹ ∈ G := mul_mem (mul_mem hdG hyG) (inv_mem hdG)
    refine (hmemN _).mpr ⟨hdyG, mul_mem (mul_mem hd hyD₁) (inv_mem hd), ?_⟩
    have hcd : ((hG.coord hJ ⟨d, hdG⟩ : J) : Γ) ∈ cenIn J (norIn A J) := by
      rw [← h.projIn_smear hJ]
      exact (hG.mem_projIn_iff hJ).mpr ⟨⟨d, hdG⟩, hd, rfl⟩
    have e : (⟨d * y * d⁻¹, hdyG⟩ : ↥G) = ⟨d, hdG⟩ * ⟨y, hyG⟩ * ⟨d, hdG⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact fittingSubgroupOf_conj_mem hcd hyc
  have hNnil : Group.IsNilpotent N := by
    have hle : projIn (lcal G) J N ≤ cJ := by
      intro z hz
      obtain ⟨y, hyN, rfl⟩ := (hG.mem_projIn_iff hJ).mp hz
      exact ((hmemN _).mp hyN).2.2
    have hinj : Function.Injective ((Subgroup.inclusion hle).comp (projInHom hG hJ hNG)) := by
      refine (Subgroup.inclusion_injective hle).comp ?_
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : hG.coord hJ ⟨x, hNG x.2⟩ = 1 := by
        apply Subtype.ext
        have h2 := congrArg Subtype.val hx
        rw [projInHom_apply] at h2
        exact h2
      have h2 : (x : Γ) ∈ sSup (lcal G \ {J}) := (hG.coord_eq_one_iff hJ _).mp h1
      have h3 : (x : Γ) ∈ smear J A ⊓ sSup (lcal G \ {J}) :=
        Subgroup.mem_inf.mpr ⟨hND₁ x.2, h2⟩
      rw [h.smear_inf_sSup hJ] at h3
      exact Subtype.ext (Subgroup.mem_bot.mp h3)
    have : Group.IsNilpotent cJ := isNilpotent_fittingSubgroupOf _
    exact isNilpotent_of_injective _ hinj
  have hNF : N ≤ CFSG.fittingSubgroupOf (smear J A) :=
    le_fittingSubgroupOf_of_nilpotent hND₁ (le_normalizer_of_conj_mem hconj) hNnil
  intro x hx
  have hxC : x ∈ cenIn J (norIn A J) := Subgroup.map_subtype_le _ hx
  rw [← h.projIn_smear hJ] at hxC
  obtain ⟨y, hyD₁, rfl⟩ := (hG.mem_projIn_iff hJ).mp hxC
  have hyN : (y : Γ) ∈ N := (hmemN _).mpr ⟨y.2, hyD₁, hx⟩
  exact (hG.mem_projIn_iff hJ).mpr ⟨y, hNF hyN, rfl⟩

theorem SemisimpleAction.projIn_fittingSubgroupOf_smear_le (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) :
    projIn (lcal G) J (CFSG.fittingSubgroupOf (smear J A)) ≤
      CFSG.fittingSubgroupOf (cenIn J (norIn A J)) := by
  have hG := h.isDirectProduct_lcal
  have hFG : CFSG.fittingSubgroupOf (smear J A) ≤ G :=
    ((Subgroup.map_subtype_le _).trans (h.smear_le_cenIn hJ)).trans inf_le_left
  refine le_fittingSubgroupOf_of_nilpotent ?_ ?_ (isNilpotent_projIn hG hJ hFG
    (isNilpotent_fittingSubgroupOf _))
  · rw [← h.projIn_smear hJ]
    exact projIn_mono J (Subgroup.map_subtype_le _)
  · rw [← h.projIn_smear hJ]
    exact le_normalizer_of_conj_mem (projIn_conj_mem hG hJ fun y hy x hx =>
      fittingSubgroupOf_conj_mem hy hx)

theorem SemisimpleAction.projIn_fittingSubgroupOf_smear (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) :
    projIn (lcal G) J (CFSG.fittingSubgroupOf (smear J A)) =
      CFSG.fittingSubgroupOf (cenIn J (norIn A J)) :=
  le_antisymm (h.projIn_fittingSubgroupOf_smear_le hJ)
    (h.fittingSubgroupOf_cenIn_le_projIn_smear hJ)

theorem SemisimpleAction.fittingSubgroupOf_smear_le_of_normal
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) {N : Subgroup Γ} (hNS : N ≤ smear J A)
    (hN : (N.subgroupOf (smear J A)).Normal) (hN1 : N ≠ ⊥) :
    CFSG.fittingSubgroupOf (smear J A) ≤ N := by
  have hG := h.isDirectProduct_lcal
  have hNG : N ≤ G := hNS.trans ((h.smear_le_cenIn hJ).trans inf_le_left)
  have hQC : projIn (lcal G) J N ≤ cenIn J (norIn A J) := by
    rw [← h.projIn_smear hJ]
    exact projIn_mono J hNS
  have hconj : ∀ y ∈ smear J A, ∀ x ∈ N, y * x * y⁻¹ ∈ N := fun y hy x hx =>
    (Subgroup.normal_subgroupOf_iff hNS).mp hN x y hx hy
  have hQnorm : ((projIn (lcal G) J N).subgroupOf (cenIn J (norIn A J))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQC]
    intro z c hz hc
    rw [← h.projIn_smear hJ] at hc
    exact projIn_conj_mem hG hJ hconj c hc z hz
  have hQ1 : projIn (lcal G) J N ≠ ⊥ := by
    intro hbot
    apply hN1
    rw [eq_bot_iff]
    intro y hy
    have hyG : y ∈ G := hNG hy
    have h1 : ((hG.coord hJ ⟨y, hyG⟩ : J) : Γ) ∈ projIn (lcal G) J N :=
      (hG.mem_projIn_iff hJ).mpr ⟨⟨y, hyG⟩, hy, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : hG.coord hJ ⟨y, hyG⟩ = 1 := Subtype.ext h1
    have h3 : y ∈ smear J A ⊓ sSup (lcal G \ {J}) :=
      Subgroup.mem_inf.mpr ⟨hNS hy, (hG.coord_eq_one_iff hJ _).mp h2⟩
    rw [h.smear_inf_sSup hJ] at h3
    exact h3
  have hFQ : CFSG.fittingSubgroupOf (cenIn J (norIn A J)) ≤ projIn (lcal G) J N :=
    h.fittingSubgroupOf_cenIn_le_of_normal hJ hQC hQnorm hQ1
  intro y hy
  have hyS : y ∈ smear J A := Subgroup.map_subtype_le _ hy
  have hyG : y ∈ G := (h.smear_le_cenIn hJ hyS).1
  have h1 : ((hG.coord hJ ⟨y, hyG⟩ : J) : Γ) ∈ projIn (lcal G) J N := by
    refine hFQ ?_
    rw [← h.projIn_fittingSubgroupOf_smear hJ]
    exact (hG.mem_projIn_iff hJ).mpr ⟨⟨y, hyG⟩, hy, rfl⟩
  obtain ⟨n, hnN, hn⟩ := (hG.mem_projIn_iff hJ).mp h1
  have hnS : (n : Γ) ∈ smear J A := hNS hnN
  have h2 : y * (n : Γ)⁻¹ ∈ smear J A ⊓ sSup (lcal G \ {J}) := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem hyS (inv_mem hnS), ?_⟩
    have hyn : hG.coord hJ (⟨y, hyG⟩ * n⁻¹) = 1 := by
      rw [map_mul, map_inv]
      have : hG.coord hJ n = hG.coord hJ ⟨y, hyG⟩ := (Subtype.ext hn)
      rw [this, mul_inv_cancel]
    exact (hG.coord_eq_one_iff hJ _).mp hyn
  rw [h.smear_inf_sSup hJ, Subgroup.mem_bot, mul_inv_eq_one] at h2
  rw [h2]
  exact hnN

theorem SemisimpleAction.fittingSubgroupOf_smear_ne_bot
    (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) : CFSG.fittingSubgroupOf (smear J A) ≠ ⊥ := by
  intro hbot
  apply h.fittingSubgroupOf_cenIn_ne_bot hJ
  rw [← h.projIn_fittingSubgroupOf_smear hJ, hbot, eq_bot_iff]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (h.isDirectProduct_lcal.mem_projIn_iff hJ).mp hx
  have : (y : Γ) = 1 := Subgroup.mem_bot.mp hy
  have hy1 : y = 1 := Subtype.ext this
  rw [hy1, map_one]
  exact Subgroup.one_mem _

theorem SemisimpleAction.fittingSubgroupOf_cenIn_le_projIn (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) :
    CFSG.fittingSubgroupOf (cenIn J (norIn A J)) ≤
      projIn (lcal G) J (CFSG.fittingSubgroupOf (cenIn G A)) :=
  (h.fittingSubgroupOf_cenIn_le_projIn_smear hJ).trans
    (projIn_mono J (h.fittingSubgroupOf_smear_le hJ))

theorem SemisimpleAction.projIn_fittingSubgroupOf_cenIn (h : SemisimpleAction p A G)
    (hJ : J ∈ lcal G) :
    projIn (lcal G) J (CFSG.fittingSubgroupOf (cenIn G A)) =
      CFSG.fittingSubgroupOf (cenIn J (norIn A J)) := by
  refine le_antisymm ?_ (h.fittingSubgroupOf_cenIn_le_projIn hJ)
  have hG := h.isDirectProduct_lcal
  have hFG : CFSG.fittingSubgroupOf (cenIn G A) ≤ G :=
    (Subgroup.map_subtype_le _).trans inf_le_left
  refine le_fittingSubgroupOf_of_nilpotent ?_ ?_
    (isNilpotent_projIn hG hJ hFG (isNilpotent_fittingSubgroupOf _))
  · rw [← h.projIn_cenIn hJ]
    exact projIn_mono J (Subgroup.map_subtype_le _)
  · rw [← h.projIn_cenIn hJ]
    exact le_normalizer_of_conj_mem (projIn_conj_mem hG hJ fun y hy x hx =>
      fittingSubgroupOf_conj_mem hy hx)

theorem SemisimpleAction.cenIn_fittingSubgroupOf_eq
    (h : SemisimpleAction p A G) {X : Subgroup Γ}
    (hXG : X ≤ G) (hD : cenIn G A ≤ X) (hX : Group.IsSolvable X) :
    cenIn G (CFSG.fittingSubgroupOf X) = fProd A G := by
  have hG := h.isDirectProduct_lcal
  have hFX := h.fittingSubgroupOf_eq_inf_fProd hXG hD hX
  have hFD := h.fittingSubgroupOf_eq_inf_fProd (X := cenIn G A) inf_le_left le_rfl h.solvable_cen
  have hDX : CFSG.fittingSubgroupOf (cenIn G A) ≤ CFSG.fittingSubgroupOf X := by
    rw [hFX, hFD]
    exact inf_le_inf_right _ hD
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨hgG, hgc⟩ := mem_cenIn_iff.mp hg
    refine h.mem_fProd_iff.mpr ⟨hgG, fun J hJ => ?_⟩
    rw [h.fittingSubgroupOf_kJ_eq hJ]
    refine mem_cenIn_iff.mpr ⟨(hG.coord hJ ⟨g, hgG⟩).2,
      Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have hz' : z ∈ projIn (lcal G) J (CFSG.fittingSubgroupOf X) :=
      projIn_mono J hDX (h.fittingSubgroupOf_cenIn_le_projIn hJ hz)
    obtain ⟨y, hyX, rfl⟩ := (hG.mem_projIn_iff hJ).mp hz'
    have e : y * (⟨g, hgG⟩ : ↥G) = ⟨g, hgG⟩ * y :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hgc y hyX)
    have e2 := congrArg (hG.coord hJ) e
    rw [map_mul, map_mul] at e2
    exact congrArg Subtype.val e2
  · refine mem_cenIn_iff.mpr ⟨fProd_le A G hg, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have hzf : z ∈ fProd A G := (Subgroup.mem_inf.mp (hFX ▸ hz)).2
    have := h.isMulCommutative_fProd
    exact congrArg Subtype.val (mul_comm' (⟨z, hzf⟩ : fProd A G) ⟨g, hg⟩)

theorem SemisimpleAction.cenIn_le_kProd
    (h : SemisimpleAction p A G) : cenIn G A ≤ kProd A G :=
  h.le_kProd_of_solvable inf_le_left le_rfl h.solvable_cen

theorem SemisimpleAction.mOf_eq_kProd
    (h : SemisimpleAction p A G) : mOf A G = kProd A G := by
  unfold mOf
  rw [h.cenIn_fittingSubgroupOf_eq (X := cenIn G A) inf_le_left le_rfl h.solvable_cen,
    h.norIn_fProd]

theorem SemisimpleAction.fittingSubgroupOf_kProd
    (h : SemisimpleAction p A G) :
    CFSG.fittingSubgroupOf (kProd A G) = fProd A G := by
  rw [h.fittingSubgroupOf_eq_inf_fProd (kProd_le A G) h.cenIn_le_kProd h.isSolvable_kProd]
  exact inf_eq_right.mpr (fProd_le_kProd A G)

omit [Finite Γ] in
theorem SemisimpleAction.admits_mOf (h : SemisimpleAction p A G) : Admits A (mOf A G) := by
  have hAG : A ≤ Subgroup.normalizer (G : Set Γ) := h.admits
  have hAP : A ≤ Subgroup.normalizer
      (cenIn G (CFSG.fittingSubgroupOf (cenIn G A)) : Set Γ) := by
    refine le_normalizer_of_conj_mem fun a ha x hx => ?_
    obtain ⟨hxG, hxc⟩ := mem_cenIn_iff.mp hx
    refine mem_cenIn_iff.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hAG ha) x).mp hxG,
      Subgroup.mem_centralizer_iff.mpr fun f hf => ?_⟩
    have hfD : f ∈ cenIn G A := Subgroup.map_subtype_le _ hf
    have hfa : a * f = f * a := Subgroup.mem_centralizer_iff.mp (mem_cenIn_iff.mp hfD).2 a ha
    have hfx : f * x = x * f := Subgroup.mem_centralizer_iff.mp hxc f hf
    have hc : Commute a f := hfa
    calc f * (a * x * a⁻¹) = (f * a) * x * a⁻¹ := by group
      _ = (a * f) * x * a⁻¹ := by rw [hfa]
      _ = a * (f * x) * a⁻¹ := by group
      _ = a * (x * f) * a⁻¹ := by rw [hfx]
      _ = a * x * (f * a⁻¹) := by group
      _ = a * x * (a⁻¹ * f) := by rw [← hc.inv_left.eq]
      _ = (a * x * a⁻¹) * f := by group
  refine le_normalizer_of_conj_mem fun a ha x hx => ?_
  obtain ⟨hxG, hxN⟩ := mem_norIn_iff.mp hx
  exact mem_norIn_iff.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hAG ha) x).mp hxG,
    mul_mem (mul_mem (hAP ha) hxN) (inv_mem (hAP ha))⟩

theorem SemisimpleAction.admits_kProd
    (h : SemisimpleAction p A G) : Admits A (kProd A G) := by
  rw [← h.mOf_eq_kProd]
  exact h.admits_mOf

theorem SemisimpleAction.admits_fProd
    (h : SemisimpleAction p A G) : Admits A (fProd A G) := by
  rw [← h.fittingSubgroupOf_kProd]
  exact le_normalizer_of_conj_mem fun a ha x hx =>
    fittingSubgroupOf_conj_mem_of_mem_normalizer (h.admits_kProd ha) hx

end Finite

end CFSG.SignalizerFunctorTheorem.McBride.Near
