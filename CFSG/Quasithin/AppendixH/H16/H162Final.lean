module

public import CFSG.Quasithin.AppendixH.H16.H162OMod
public import CFSG.Quasithin.AppendixH.H16.H162Std
public import CFSG.Quasithin.AppendixH.H16.OctadCenter

public section

open scoped Pointwise

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc
  CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24 CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Open

theorem h162Z_transport
    {V : Type*} [CommGroup V]
    (ρ : ↥M24g →* MulAut V) (e' : V ≃* W11) (τ : ↥M24g)
    (hcongr : ∀ γ : ↥M24g, congrHom e' (ρ γ) = rhoC11 AutPerm le_rfl (τ⁻¹ * γ * τ))
    {V₅ : Subgroup V} (hV₅ : V₅.map e'.toMonoidHom = octV5)
    {β' : V →* Multiplicative (Fin 6 → ZMod 2)} (hβ : β' = octBeta.comp e'.toMonoidHom)
    {z : S24} (hz : z ∈ octFix ((τ : S24) • octad0)) (hz1 : z ≠ 1) :
    H162Z ρ (fun x => qPlus6 (Multiplicative.toAdd (β' x))) V₅
      (KY M24g ((τ : S24) • octad0)) z := by
  have hKO_std : KY M24g octad0 = fixO := by
    rw [KY, show MY M24g octad0 = octStab octad0 from rfl]
    exact pCoreOf_octStab_octad0
  have hzM : z ∈ M24g := (mem_octStab_iff.mp (octFix_le_octStab _ hz)).1
  have hz' : (τ : S24)⁻¹ * z * (τ : S24) ∈ fixO := by
    have hmem : z ∈ conjSubg (τ : S24) fixO := by
      have h := octFix_smul τ.2 octad0
      rw [octFix_octad0] at h
      rw [h] at hz
      exact hz
    exact (mem_conjSubg_iff (τ : S24) fixO z).mp hmem
  have hz1' : (τ : S24)⁻¹ * z * (τ : S24) ≠ 1 := by
    intro h
    apply hz1
    calc z = (τ : S24) * ((τ : S24)⁻¹ * z * (τ : S24)) * (τ : S24)⁻¹ := by group
      _ = 1 := by rw [h]; group
  refine H162Z_of_twist ρ (rhoC11 AutPerm le_rfl) e' τ hcongr
    (Q := fun x => qPlus6 (Multiplicative.toAdd (β' x))) (Q' := octQ)
    (V₅' := octV5) (KO' := fixO)
    (z' := (τ : S24)⁻¹ * z * (τ : S24)) ?hQ hV₅ ?hKO hzM ?hz ?_
  · intro x
    rw [hβ]
    exact (qPlus6_octBeta (e' x)).symm
  · rw [KY_smul_of_mem τ.2 octad0, hKO_std, conjSubg_inv_conjSubg]
  · rfl
  · exact h162Z_std hz' hz1'

theorem h162_of_coords
    {V : Type*} [CommGroup V]
    (ρ : ↥M24g →* MulAut V) (e : V ≃* W11)
    (he : ∀ (γ : ↥M24g) (v : V), e (ρ γ v) = rhoC11 AutPerm le_rfl γ (e v))
    {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ : Subgroup S24} (hcfg : Cfg14 a b O Tr S B T₀) :

    ∃ V₅ : Subgroup V,
      (IsChiefFactorUnder (actsOnModule (rImg ρ (MY M24g O))) ⊥ (fixV (rImg ρ (KY M24g O))) ∧
        rk ↥(fixV (rImg ρ (KY M24g O))) = 1 ∧
        IsChiefFactorUnder (actsOnModule (rImg ρ (MY M24g O))) (fixV (rImg ρ (KY M24g O))) V₅ ∧
        rk ↥V₅ = 5 ∧ IsChiefFactorUnder (actsOnModule (rImg ρ (MY M24g O))) V₅ ⊤) ∧
      (FullTranspCenter (rImg ρ (MY M24g O)) (rImg ρ (KY M24g O)) V₅ (fixV (rImg ρ (KY M24g O))) ∧
        IsDualOfConj ρ (MY M24g O) V₅ (fixV (rImg ρ (KY M24g O))) (KY M24g O)) ∧
      (∃ β' : V →* Multiplicative (Fin 6 → ZMod 2),
        InducesOnVia (rImg ρ (MY M24g O)) ⊤ V₅ (Multiplicative (Fin 6 → ZMod 2)) (omegaN 6 qPlus6)
          (β'.comp (⊤ : Subgroup V).subtype) ∧
        (∀ g : ↥M24g, (g : S24) ∈ MY M24g O → ((∀ x : V, ρ g x * x⁻¹ ∈ V₅) ↔ (g : S24) ∈ KY M24g O)) ∧
        rk ↥(fixV (rImg ρ (KY M24g S)) ⊔ V₅) = 6 ∧
        (∀ x ∈ fixV (rImg ρ (KY M24g S)) ⊔ V₅, qPlus6 (Multiplicative.toAdd (β' x)) = 0) ∧
        (fixV (rImg ρ (KY M24g S)) = fixV (rImg ρ (KY M24g O ⊓ KY M24g S))) ∧
        ∀ z : S24, (z ∈ T₀ ∧ ∀ t ∈ T₀, (t ∈ Subgroup.zpowers z ↔ ∀ s ∈ T₀, s * t = t * s)) →
          (rk ↥(fixV (rImg ρ (Subgroup.zpowers z)) ⊔ V₅) = 8 ∧
            ∀ x ∈ fixV (rImg ρ (Subgroup.zpowers z)) ⊔ V₅, qPlus6 (Multiplicative.toAdd (β' x)) = 0) ∧
          cenM ρ (fixV (rImg ρ (Subgroup.zpowers z))) = (Subgroup.zpowers z).subgroupOf M24g ∧
          (rk ↥(V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z))) = 4 ∧
            IsE2k 4 ((cenM ρ (V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z)))).map M24g.subtype) ∧
            pCoreOf 2 (M24g ⊓ Subgroup.centralizer ({z} : Set S24)) =
              KY M24g O ⊔ (cenM ρ (V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z)))).map M24g.subtype ∧
            ∀ element ∈ pCoreOf 2 (M24g ⊓ Subgroup.centralizer ({z} : Set S24)),
              ∃ kernelElement ∈ KY M24g O,
                ∃ centralizerElement ∈ (cenM ρ (V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z)))).map M24g.subtype,
                  element = kernelElement * centralizerElement) ∧
          (∀ B : Subgroup S24, z ∈ B → B ≤ (cenM ρ (V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z)))).map M24g.subtype →
            rk ↥(fixV (rImg ρ B)) = 8 - rk ↥B) ∧
          (∀ g ∈ M24g ⊓ Subgroup.centralizer ({z} : Set S24),
            rk ↥(commOn (fixV (rImg ρ (Subgroup.zpowers z))) (rImg ρ (Subgroup.zpowers g))) = 1 →
              g ∈ pCoreOf 2 (M24g ⊓ Subgroup.centralizer ({z} : Set S24))))
  := by
  obtain ⟨τ0, hτ0, hτO, hτS⟩ :=
    exists_flag_conj hcfg.octad hcfg.sextet (hcfg.trio_union O hcfg.O_mem)
  subst hτO
  subst hτS
  let τ : ↥M24g := ⟨τ0, hτ0⟩
  let e' : V ≃* W11 := (ρ τ⁻¹ : MulAut V).trans e
  have hcongr : ∀ γ : ↥M24g, congrHom e' (ρ γ) = rhoC11 AutPerm le_rfl (τ⁻¹ * γ * τ) :=
    congrHom_twist ρ (rhoC11 AutPerm le_rfl) e he τ
  let V₅ : Subgroup V := octV5.map e'.symm.toMonoidHom
  have hV₅ : V₅.map e'.toMonoidHom = octV5 := by
    rw [Subgroup.map_map]
    have : e'.toMonoidHom.comp e'.symm.toMonoidHom = MonoidHom.id W11 := by
      ext w; simp
    rw [this, Subgroup.map_id]
  let β' : V →* Multiplicative (Fin 6 → ZMod 2) := octBeta.comp e'.toMonoidHom
  obtain ⟨c1, c2, c3a, c3b, c3c, c3d, c4⟩ :=
    h162O_transport ρ e' τ hcongr hV₅ rfl
  refine ⟨V₅, c1, c2, β', c3a, c3b, c3c, c3d, c4, ?_⟩
  intro z hz
  obtain ⟨hzO, hz1⟩ := center_gen_mem_octFix hcfg.octad hcfg.sylow hcfg.stab_O hz
  exact h162Z_transport ρ e' τ hcongr hV₅ rfl hzO hz1

end CFSG.ASVolI.H16
