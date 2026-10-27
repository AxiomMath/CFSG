module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.C3AlgebraicPart1

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.C3Algebraic
open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal.Symplectic CFSG.Timmesfeld.LieEmbed
  CFSG.SeitzReduction.F4Pilot
  CFSG.StandardType.F4ExplicitPos.BaseChange CFSG.StandardType.F4ExplicitPos.RootBaseChange

section Graph
variable (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

noncomputable def zMap
    (k : Idx) :
    ↥(StatedSp 3 (TauCeti.frobeniusFixedSubfield Ω 2 k.1)) →* ↥(StatedSp 3 Ω) × ↥(adjointGroup .F4
        Ω) :=
  (sMap Ω k).prod ((jMap Ω k).comp (iOf (TauCeti.frobeniusFixedSubfield Ω 2 k.1)))

noncomputable def Gamma :
    Subgroup (↥(StatedSp 3 Ω) × ↥(adjointGroup .F4 Ω)) :=
  ⨆ k, (zMap Ω k).range

theorem zMap_range_le_of_dvd
    {k m : Idx} (h : k.1 ∣ m.1) :
    (zMap Ω k).range ≤ (zMap Ω m).range := by
  intro x hx
  obtain ⟨g, rfl⟩ := hx
  let hle : TauCeti.frobeniusFixedSubfield Ω 2 k.1 ≤ TauCeti.frobeniusFixedSubfield Ω 2 m.1 :=
      TauCeti.frobeniusFixedSubfield_le_of_dvd h
  let f : ↥(TauCeti.frobeniusFixedSubfield Ω 2 k.1) →+* ↥(TauCeti.frobeniusFixedSubfield Ω 2
      m.1) := Subfield.inclusion hle
  refine ⟨statedSpMap f 3 g, ?_⟩
  apply Prod.ext
  · change statedSpMap (incl Ω m) 3 (statedSpMap f 3 g) = statedSpMap (incl Ω k) 3 g
    rw [statedSpMap_comp]
    congr 1
  · have hnat := DFunLike.congr_fun (iOf_natural (f := f)) g
    simp only [MonoidHom.comp_apply] at hnat
    have hj : (jMap Ω m).comp (j (τ := .F4) f) = jMap Ω k := by
      show (j (τ := .F4) (incl Ω m)).comp (j (τ := .F4) f) = j (τ := .F4) (incl Ω k)
      rw [← j_comp]
      congr 1
    change jMap Ω m (iOf (TauCeti.frobeniusFixedSubfield Ω 2 m.1) (statedSpMap f 3 g)) = jMap Ω k
        (iOf (TauCeti.frobeniusFixedSubfield Ω 2 k.1) g)
    calc jMap Ω m (iOf (TauCeti.frobeniusFixedSubfield Ω 2 m.1) (statedSpMap f 3 g))
        = jMap Ω m (j f (iOf (TauCeti.frobeniusFixedSubfield Ω 2 k.1) g)) := by rw [hnat]
      _ = ((jMap Ω m).comp (j (τ := .F4) f)) (iOf (TauCeti.frobeniusFixedSubfield Ω 2 k.1) g) := rfl
      _ = jMap Ω k (iOf (TauCeti.frobeniusFixedSubfield Ω 2 k.1) g) := by rw [hj]

theorem directed_zMap_range :
    Directed (· ≤ ·) (fun k : Idx => (zMap Ω k).range) := by
  intro k m
  refine ⟨⟨k.1 * m.1, mul_ne_zero k.2 m.2⟩, ?_, ?_⟩
  · exact zMap_range_le_of_dvd Ω (dvd_mul_right k.1 m.1)
  · exact zMap_range_le_of_dvd Ω (dvd_mul_left m.1 k.1)

theorem mem_Gamma
    {x} : x ∈ Gamma Ω ↔ ∃ k, x ∈ (zMap Ω k).range :=
  Subgroup.mem_iSup_of_directed (directed_zMap_range Ω)

noncomputable def pi1 :
    Gamma Ω →* ↥(StatedSp 3 Ω) where
  toFun z := ((z : Gamma Ω) : ↥(StatedSp 3 Ω) × ↥(adjointGroup .F4 Ω)).1
  map_one' := rfl
  map_mul' := fun _ _ => rfl

noncomputable def pi2 :
    Gamma Ω →* ↥(adjointGroup .F4 Ω) where
  toFun z := ((z : Gamma Ω) : ↥(StatedSp 3 Ω) × ↥(adjointGroup .F4 Ω)).2
  map_one' := rfl
  map_mul' := fun _ _ => rfl

theorem pi1_injective :
    Function.Injective (pi1 Ω) := by
  intro z1 z2 h
  change (((z1 : Gamma Ω) : ↥(StatedSp 3 Ω) × ↥(adjointGroup .F4 Ω)).1)
      = (((z2 : Gamma Ω) : ↥(StatedSp 3 Ω) × ↥(adjointGroup .F4 Ω)).1) at h
  obtain ⟨k, hk1⟩ := (mem_Gamma Ω).1 z1.2
  obtain ⟨m, hm1⟩ := (mem_Gamma Ω).1 z2.2
  obtain ⟨n, hkn, hmn⟩ := directed_zMap_range Ω k m
  obtain ⟨g1, hg1⟩ := hkn hk1
  obtain ⟨g2, hg2⟩ := hmn hm1
  have h1 : sMap Ω n g1 = sMap Ω n g2 := by
    have hh := h
    rw [show ((z1 : Gamma Ω) : ↥(StatedSp 3 Ω) × ↥(adjointGroup .F4 Ω)) = zMap Ω n g1
          from hg1.symm,
        show ((z2 : Gamma Ω) : ↥(StatedSp 3 Ω) × ↥(adjointGroup .F4 Ω)) = zMap Ω n g2
          from hg2.symm] at hh
    exact hh
  have hg : g1 = g2 := statedSpMap_injective (incl Ω n) 3 h1
  apply Subtype.ext
  rw [show ((z1 : Gamma Ω) : ↥(StatedSp 3 Ω) × ↥(adjointGroup .F4 Ω)) = zMap Ω n g1
        from hg1.symm,
      show ((z2 : Gamma Ω) : ↥(StatedSp 3 Ω) × ↥(adjointGroup .F4 Ω)) = zMap Ω n g2
        from hg2.symm, hg]

theorem pi2_injective :
    Function.Injective (pi2 Ω) := by
  intro z1 z2 h
  change (((z1 : Gamma Ω) : ↥(StatedSp 3 Ω) × ↥(adjointGroup .F4 Ω)).2)
      = (((z2 : Gamma Ω) : ↥(StatedSp 3 Ω) × ↥(adjointGroup .F4 Ω)).2) at h
  obtain ⟨k, hk1⟩ := (mem_Gamma Ω).1 z1.2
  obtain ⟨m, hm1⟩ := (mem_Gamma Ω).1 z2.2
  obtain ⟨n, hkn, hmn⟩ := directed_zMap_range Ω k m
  obtain ⟨g1, hg1⟩ := hkn hk1
  obtain ⟨g2, hg2⟩ := hmn hm1
  have h1 : jMap Ω n (iOf (TauCeti.frobeniusFixedSubfield Ω 2 n.1) g1) = jMap Ω n (iOf
      (TauCeti.frobeniusFixedSubfield Ω 2 n.1) g2) := by
    have hh := h
    rw [show ((z1 : Gamma Ω) : ↥(StatedSp 3 Ω) × ↥(adjointGroup .F4 Ω)) = zMap Ω n g1
          from hg1.symm,
        show ((z2 : Gamma Ω) : ↥(StatedSp 3 Ω) × ↥(adjointGroup .F4 Ω)) = zMap Ω n g2
          from hg2.symm] at hh
    exact hh
  have h2 : iOf (TauCeti.frobeniusFixedSubfield Ω 2 n.1) g1 = iOf (TauCeti.frobeniusFixedSubfield Ω
      2 n.1) g2 :=
    j_injective (incl Ω n) (fun _ _ hh => Subtype.ext hh) h1
  have h3 : g1 = g2 := iOf_injective (TauCeti.frobeniusFixedSubfield Ω 2 n.1) h2
  apply Subtype.ext
  rw [show ((z1 : Gamma Ω) : ↥(StatedSp 3 Ω) × ↥(adjointGroup .F4 Ω)) = zMap Ω n g1
        from hg1.symm,
      show ((z2 : Gamma Ω) : ↥(StatedSp 3 Ω) × ↥(adjointGroup .F4 Ω)) = zMap Ω n g2
        from hg2.symm, h3]

theorem pi1_zMap
    (k : Idx) (g : ↥(StatedSp 3 (TauCeti.frobeniusFixedSubfield Ω 2 k.1)))
    (hz : zMap Ω k g ∈ Gamma Ω) :
    pi1 Ω ⟨zMap Ω k g, hz⟩ = sMap Ω k g := by
  simp only [pi1, zMap, MonoidHom.prod_apply]
  rfl

theorem sMap_mem_range_pi1
    (k : Idx)
    (g : ↥(StatedSp 3 (TauCeti.frobeniusFixedSubfield Ω 2 k.1))) :
    sMap Ω k g ∈ MonoidHom.range (pi1 Ω) := by
  have hz : zMap Ω k g ∈ Gamma Ω :=
    Subgroup.mem_iSup_of_mem k (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
  exact ⟨⟨zMap Ω k g, hz⟩, pi1_zMap Ω k g hz⟩

theorem c3RootSubgroup_le_range_pi1
    {γ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) :
    C3Range.c3RootSubgroup (K := Ω) γ ≤ MonoidHom.range (pi1 Ω) := by
  rw [CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  obtain ⟨k, hk, hc⟩ := TauCeti.exists_mem_frobeniusFixedSubfield Ω 2 c
  have hsk : sMap Ω ⟨k, hk⟩ (Sp.x 3 (TauCeti.frobeniusFixedSubfield Ω 2 k) γ ⟨c, hc⟩)
      = Sp.x 3 Ω γ c := by
    rw [sMap, statedSpMap_x]
    rfl
  rw [← hsk]
  exact sMap_mem_range_pi1 Ω ⟨k, hk⟩
    (Sp.x 3 (TauCeti.frobeniusFixedSubfield Ω 2 k) γ ⟨c, hc⟩)

theorem pi1_surjective :
    Function.Surjective (pi1 Ω) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  rw [← iSup_c3RootSubgroup_eq_top_alg Ω]
  exact iSup₂_le fun γ hγ => c3RootSubgroup_le_range_pi1 Ω hγ

noncomputable def eGamma :
    Gamma Ω ≃* ↥(StatedSp 3 Ω) :=
  MulEquiv.ofBijective (pi1 Ω) ⟨pi1_injective Ω, pi1_surjective Ω⟩

noncomputable def iOmega :
    ↥(StatedSp 3 Ω) →* ↥(adjointGroup .F4 Ω) :=
  (pi2 Ω).comp (eGamma Ω).symm.toMonoidHom

theorem iOmega_injective :
    Function.Injective (iOmega Ω) := by
  change Function.Injective (⇑(pi2 Ω) ∘ ⇑(eGamma Ω).symm)
  exact Function.Injective.comp (pi2_injective Ω) (MulEquiv.injective (eGamma Ω).symm)

theorem iOmega_sMap
    (k : Idx) (g : ↥(StatedSp 3 (TauCeti.frobeniusFixedSubfield Ω 2 k.1))) :
    iOmega Ω (sMap Ω k g) = jMap Ω k (iOf (TauCeti.frobeniusFixedSubfield Ω 2 k.1) g) := by
  have hz : zMap Ω k g ∈ Gamma Ω :=
    Subgroup.mem_iSup_of_mem k (MonoidHom.mem_range.mpr ⟨g, rfl⟩)
  have hpe : (eGamma Ω).symm (sMap Ω k g) = ⟨zMap Ω k g, hz⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  change pi2 Ω ((eGamma Ω).symm (sMap Ω k g)) = jMap Ω k (iOf (TauCeti.frobeniusFixedSubfield Ω 2
      k.1) g)
  rw [hpe]
  rfl

theorem iOmega_x
    (γ : Fin 3 → ℤ) (c : Ω) :
    iOmega Ω (Sp.x 3 Ω γ c) = Adjoint.f4Par Ω (c3ToF4 γ) c := by
  obtain ⟨k, hk, hc⟩ := TauCeti.exists_mem_frobeniusFixedSubfield Ω 2 c
  have : Finite ↥(TauCeti.frobeniusFixedSubfield Ω 2 k) :=
    TauCeti.finite_frobeniusFixedSubfield Ω 2 k hk
  have : CharP ↥(TauCeti.frobeniusFixedSubfield Ω 2 k) 2 :=
    Subfield.charP (TauCeti.frobeniusFixedSubfield Ω 2 k) 2
  have hsk : sMap Ω ⟨k, hk⟩ (Sp.x 3 (TauCeti.frobeniusFixedSubfield Ω 2 k) γ ⟨c,
      hc⟩) = Sp.x 3 Ω γ c := by
    change statedSpMap (incl Ω ⟨k, hk⟩) 3 (Sp.x 3 (TauCeti.frobeniusFixedSubfield Ω 2 k) γ ⟨c,
        hc⟩) = Sp.x 3 Ω γ c
    rw [statedSpMap_x]
    rfl
  calc iOmega Ω (Sp.x 3 Ω γ c)
      = iOmega Ω (sMap Ω ⟨k, hk⟩ (Sp.x 3 (TauCeti.frobeniusFixedSubfield Ω 2 k) γ ⟨c,
          hc⟩)) := by rw [hsk]
    _ = jMap Ω ⟨k, hk⟩ (iOf (TauCeti.frobeniusFixedSubfield Ω 2 k) (Sp.x 3
        (TauCeti.frobeniusFixedSubfield Ω 2 k) γ ⟨c, hc⟩)) :=
          iOmega_sMap Ω ⟨k, hk⟩ _
    _ = jMap Ω ⟨k, hk⟩ (Adjoint.f4Par (TauCeti.frobeniusFixedSubfield Ω 2 k) (c3ToF4 γ) ⟨c,
        hc⟩) := by rw [iOf_x]
    _ = Adjoint.f4Par Ω (c3ToF4 γ) c := by
          change j (τ := .F4) (incl Ω ⟨k, hk⟩)
              (Adjoint.f4Par (TauCeti.frobeniusFixedSubfield Ω 2 k) (c3ToF4 γ) ⟨c, hc⟩)
            = Adjoint.f4Par Ω (c3ToF4 γ) c
          exact map_j_xPar (τ := .F4) (incl Ω ⟨k, hk⟩) (rootOperatorFamily .F4) (c3ToF4 γ) ⟨c, hc⟩

end Graph

end CFSG.StandardType.F4ExplicitPos.C3Algebraic

end

end
