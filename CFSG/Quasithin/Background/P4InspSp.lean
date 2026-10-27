module

public import CFSG.Quasithin.Background.P4InspectStmt
public import CFSG.Quasithin.Background.P4InspSpA6
public import CFSG.Quasithin.Background.P4InspSpRank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

namespace P4InspSp

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

theorem p4inspsp_s5_case [Finite U] (hd : Module.finrank (ZMod 2) U = 4) {M K A : Subgroup (GLV U)}
    (e : ↥M ≃* Equiv.Perm (Fin 5)) (hAM : A ≤ M) (hA : IsL24ModuleFor A) (hKM : K ≤ M)
    (hnorm : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) (hirr : IsIrr K ⊤)
    (hperf : Group.IsPerfect ↥K) : IsSimpleGroup ↥K ∧ IsL24ModuleFor K := by
  have : Finite (GLV U) := p4inspsp_finite_glv
  let ι : Equiv.Perm (Fin 5) →* GLV U := M.subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.symm.injective
  have hMrange : M ≤ ι.range := fun m hm => ⟨e ⟨m, hm⟩, by simp [ι]⟩
  have hPM : Subgroup.map ι (alternatingGroup (Fin 5)) ≤ M := by
    rintro _ ⟨σ, -, rfl⟩
    exact (e.symm σ).2
  have hKP : K ≤ Subgroup.map ι (alternatingGroup (Fin 5)) :=
    p4inspsp_perfect_le_map_alt (by norm_num) ι (hKM.trans hMrange)
      (Subgroup.isPerfect_iff.1 hperf)
  have : IsSimpleGroup ↥(Subgroup.map ι (alternatingGroup (Fin 5))) :=
    p4inspsp_isSimpleGroup_map_alt (by norm_num) ι hι
  have hKeq : K = Subgroup.map ι (alternatingGroup (Fin 5)) :=
    p4inspsp_eq_of_normalized hKP (fun p hp k hk => hnorm p (hPM hp) k hk)
      (p4inspsp_ne_bot hirr (by omega))
  obtain ⟨⟨eA⟩, hω⟩ := hA
  have hA5perf : Group.IsPerfect ↥(alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hAperf : Group.IsPerfect ↥A :=
    Group.IsPerfect.ofSurjective (f := eA.symm.toMonoidHom) eA.symm.surjective
  have hAP : A ≤ Subgroup.map ι (alternatingGroup (Fin 5)) :=
    p4inspsp_perfect_le_map_alt (by norm_num) ι (hAM.trans hMrange)
      (Subgroup.isPerfect_iff.1 hAperf)
  have hcard5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hAeq : A = Subgroup.map ι (alternatingGroup (Fin 5)) := by
    refine Subgroup.eq_of_le_of_card_ge hAP ?_
    rw [Subgroup.card_map_of_injective hι, Nat.card_congr eA.toEquiv, hcard5]
  refine ⟨by rw [hKeq]; exact inferInstance, ?_⟩
  have hKA : K = A := hKeq.trans hAeq.symm
  rw [hKA]
  exact ⟨⟨eA⟩, hω⟩

end P4InspSp

theorem inspectSpCase : InspectSpCase := by
  intro U _ _ _ f M K Q v hdata hM
  subst hM
  have hsymp : IsSymplectic f := hdata.symp
  have hdim : 2 < Module.finrank (ZMod 2) U := hdata.dim
  have : FiniteDimensional (ZMod 2) U := Module.Finite.of_finite
  have heven : Even (Module.finrank (ZMod 2) U) :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.even_finrank f hsymp.1
      (P4InspSp.p4inspsp_nondeg hsymp)
  have hcases : Module.finrank (ZMod 2) U = 4 ∨ 6 ≤ Module.finrank (ZMod 2) U := by
    obtain ⟨k, hk⟩ := heven
    omega
  rcases hcases with h4 | h6
  · obtain ⟨hs, hmod⟩ := P4InspSp.p4inspsp_a6_case hsymp h4 (M := spSub f) (K := K)
      (Subgroup.commutator_le_self _) le_rfl hdata.K_le hdata.K_norm hdata.K_irr
      hdata.K_perf
    exact ⟨hs, fun _ => Or.inr (Or.inr (Or.inl hmod))⟩
  · have : IsSimpleGroup ↥(spSub f) := P4InspSp.p4inspsp_isSimpleGroup_spSub hsymp h6
    have hKeq : K = spSub f := P4InspSp.p4inspsp_eq_of_normalized hdata.K_le hdata.K_norm
      (P4InspSp.p4inspsp_ne_bot hdata.K_irr (by omega))
    subst hKeq
    exact ⟨inferInstance, fun hsqt => absurd hsqt (P4InspSp.p4inspsp_not_sqt_spSub hsymp h6)⟩

theorem inspectD4Case : InspectD4Case := by
  intro U _ _ _ f M K Q v hdata hd4 hM
  rcases hM with hM | ⟨⟨e⟩, A, hAM, hA⟩
  · obtain ⟨hs, hmod⟩ := P4InspSp.p4inspsp_a6_case hdata.symp hd4 (M := M) (K := K)
      (le_of_eq hM.symm) hdata.M_le hdata.K_le hdata.K_norm hdata.K_irr hdata.K_perf
    exact ⟨hs, fun _ => Or.inr (Or.inr (Or.inl hmod))⟩
  · obtain ⟨hs, hL⟩ := P4InspSp.p4inspsp_s5_case hd4 e hAM hA hdata.K_le hdata.K_norm hdata.K_irr
      hdata.K_perf
    exact ⟨hs, fun _ => Or.inr (Or.inl ⟨hd4, ⟨e⟩, hL⟩)⟩

end G11

end CFSG.Quasithin
