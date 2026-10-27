module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515g.Basic

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L68

variable {Γ : Type*} [Group Γ]

theorem map_conj_map_conj_eq {M A : Subgroup Γ} {d a : Γ}
    (hdM : d ∈ Subgroup.normalizer (M : Set Γ)) (ha : a ∈ A)
    (hdA : d ∈ Subgroup.centralizer (A : Set Γ)) :
    (M.map (MulAut.conj a).toMonoidHom).map (MulAut.conj d).toMonoidHom =
      M.map (MulAut.conj a).toMonoidHom := by
  rw [map_conj_map_conj]
  have hda : d * a = a * d := (Subgroup.mem_centralizer_iff.mp hdA a ha).symm
  rw [hda, ← map_conj_map_conj M d a, map_conj_eq_of_mem_normalizer hdM]

theorem mem_normalizer_orbitClosure_of_commute {M A : Subgroup Γ} {d : Γ}
    (hdM : d ∈ Subgroup.normalizer (M : Set Γ)) (hdA : d ∈ Subgroup.centralizer (A : Set Γ)) :
    d ∈ Subgroup.normalizer ((orbitClosure M A : Subgroup Γ) : Set Γ) := by
  rw [orbitClosure_eq_sSup]
  refine mem_normalizer_sSup (fun K hK => ?_) (fun K hK => ?_)
  · obtain ⟨a, ha, rfl⟩ := hK
    rw [map_conj_map_conj_eq hdM ha hdA]
    exact ⟨a, ha, rfl⟩
  · obtain ⟨a, ha, rfl⟩ := hK
    rw [map_conj_map_conj_eq (inv_mem hdM) ha (inv_mem hdA)]
    exact ⟨a, ha, rfl⟩

theorem mem_normalizer_smear {M A : Subgroup Γ} {d : Γ}
    (hdM : d ∈ Subgroup.normalizer (M : Set Γ)) (hdA : d ∈ Subgroup.centralizer (A : Set Γ)) :
    d ∈ Subgroup.normalizer ((smear M A : Subgroup Γ) : Set Γ) :=
  mem_normalizer_inf (mem_normalizer_orbitClosure_of_commute hdM hdA) (Subgroup.le_normalizer hdA)

theorem mem_normalizer_fitting_smear {M A : Subgroup Γ} {d : Γ}
    (hdM : d ∈ Subgroup.normalizer (M : Set Γ)) (hdA : d ∈ Subgroup.centralizer (A : Set Γ)) :
    d ∈ Subgroup.normalizer
      ((CFSG.inSubgroup CFSG.generalizedFitting (smear M A) : Subgroup Γ) : Set Γ) :=
  T515g.mem_normalizer_inSubgroup_generalizedFitting (mem_normalizer_smear hdM hdA)

theorem orbitClosure_mono_right {M A B : Subgroup Γ} (h : B ≤ A) :
    orbitClosure M B ≤ orbitClosure M A :=
  orbitClosure_le fun _ hb => map_conj_le_orbitClosure M (h hb)

theorem fitting_smear_le_orbitClosure {M A B : Subgroup Γ} (h : B ≤ A) :
    CFSG.inSubgroup CFSG.generalizedFitting (smear M B) ≤ orbitClosure M A :=
  ((Subgroup.map_subtype_le _).trans (smear_le_orbitClosure M B)).trans
    (orbitClosure_mono_right h)

theorem fitting_smear_le_smear (M A : Subgroup Γ) :
    CFSG.inSubgroup CFSG.generalizedFitting (smear M A) ≤ smear M A :=
  Subgroup.map_subtype_le _

theorem orbitClosure_le_of_le {L T A : Subgroup Γ} (hLT : L ≤ T)
    (hAT : A ≤ Subgroup.normalizer (T : Set Γ)) : orbitClosure L A ≤ T :=
  orbitClosure_le fun a ha => by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hAT ha) x).mp (hLT hx)

theorem le_centralizer_orbitClosure {X M A : Subgroup Γ}
    (hAX : A ≤ Subgroup.normalizer (X : Set Γ)) (hXM : X ≤ Subgroup.centralizer (M : Set Γ)) :
    X ≤ Subgroup.centralizer (orbitClosure M A : Set Γ) := by
  rw [Subgroup.le_centralizer_iff]
  refine orbitClosure_le fun a ha => ?_
  rintro _ ⟨m, hm, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : a⁻¹ * x * a ∈ X := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hAX (inv_mem ha)) x).mp hx
  have hcomm : m * (a⁻¹ * x * a) = (a⁻¹ * x * a) * m :=
    Subgroup.mem_centralizer_iff.mp (hXM hx') m hm
  have key : x * (a * m * a⁻¹) = a * ((a⁻¹ * x * a) * m) * a⁻¹ := by group
  have key' : (a * m * a⁻¹) * x = a * (m * (a⁻¹ * x * a)) * a⁻¹ := by group
  show x * (a * m * a⁻¹) = (a * m * a⁻¹) * x
  rw [key, key', hcomm]

theorem orbitClosure_le_centralizer {A G M M' : Subgroup Γ} [Finite Γ]
    (hAG : A ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥) (hM : M ∈ lcal G)
    (hM' : M' ∈ lcal G) (h : M' ∉ conjOrbit A M) :
    orbitClosure M' A ≤ Subgroup.centralizer (orbitClosure M A : Set Γ) := by
  refine le_trans ?_ (outsideOrbit_le_centralizer hAG hsol hM)
  rw [orbitClosure_eq_sSup]
  refine sSup_le_sSup fun K hK => ⟨conjOrbit_subset_lcal hAG hM' hK, fun hKM => h ?_⟩
  obtain ⟨b, hb, rfl⟩ := hK
  have := map_conj_mem_conjOrbit hKM (inv_mem hb)
  rwa [map_conj_map_conj_inv] at this

theorem eq_bot_of_le_centralizer {D J : Subgroup Γ} (hJD : J ≤ D)
    (hC : D ⊓ Subgroup.centralizer (J : Set Γ) = ⊥) {K : Subgroup ↥D}
    (hK : K ≤ Subgroup.centralizer ((J.subgroupOf D : Subgroup ↥D) : Set ↥D)) : K = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall K).mpr fun k hk => ?_
  have hk' : (k : Γ) ∈ D ⊓ Subgroup.centralizer (J : Set Γ) := by
    refine ⟨k.2, Subgroup.mem_centralizer_iff.mpr fun j hj => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp (hK hk) ⟨j, hJD hj⟩ hj
    exact congrArg Subtype.val this
  rw [hC, Subgroup.mem_bot] at hk'
  exact Subtype.ext hk'

theorem inSubgroup_generalizedFitting_eq [Finite Γ] {D J : Subgroup Γ} (hJ : J ∈ lcal D)
    (hC : D ⊓ Subgroup.centralizer (J : Set Γ) = ⊥) :
    CFSG.inSubgroup CFSG.generalizedFitting D = J := by
  have hJD : J ≤ D := lcal_le hJ
  have hJ0 : CFSG.IsComponent (J.subgroupOf D) := T515f.isComponent_of_mem_lcal hJ
  have hlayer : CFSG.layer ↥D = J.subgroupOf D := by
    refine le_antisymm (sSup_le fun K hK => ?_) (CFSG.LocalCores.component_le_layer hJ0)
    rcases CFSG.LocalCores.distinct_components_commute hK hJ0 with rfl | hcomm
    · exact le_rfl
    · exfalso
      have hbot := eq_bot_of_le_centralizer hJD hC
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
      have := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
      obtain ⟨y, hyK, hy1⟩ : ∃ y : ↥D, y ∈ K ∧ y ≠ 1 := by
        obtain ⟨x, hx⟩ := exists_ne (1 : ↥K)
        exact ⟨x, x.2, fun h => hx (Subtype.ext h)⟩
      rw [hbot, Subgroup.mem_bot] at hyK
      exact hy1 hyK
  have hfit : CFSG.fittingSubgroup ↥D = ⊥ := by
    refine eq_bot_of_le_centralizer hJD hC ?_
    have := CFSG.LocalCores.fitting_layer_commute (G := ↥D)
    rw [hlayer] at this
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp this
  have hgf : CFSG.generalizedFitting ↥D = J.subgroupOf D := by
    rw [CFSG.generalizedFitting, hfit, hlayer, bot_sup_eq]
  unfold CFSG.inSubgroup
  rw [hgf]
  exact Subgroup.map_subgroupOf_eq_of_le hJD

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L68
