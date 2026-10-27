module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L514.Setup
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Projection

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem nonempty_mulEquiv_smear {A G J : Subgroup Γ} (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    (hJ : J ∈ lcal G) :
    Nonempty (↥(smear J A) ≃* ↥(J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ))) := by
  have hL := isDirectProduct_conjOrbit hAG hJ
  have hJΩ := self_mem_conjOrbit A J
  have hdp := hL.isDirectPair hJΩ
  have hper : ∀ a ∈ A, ∀ K ∈ conjOrbit A J, K.map (MulAut.conj a).toMonoidHom ∈ conjOrbit A J :=
    fun a ha K hK => map_conj_mem_conjOrbit hK ha
  let φ : ↥(smear J A) →* ↥J :=
    (pairProj hdp).comp (Subgroup.inclusion (smear_le_orbitClosure J A))
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    have hφ : pairProj hdp ⟨c, smear_le_orbitClosure J A c.2⟩ = 1 := hc
    obtain ⟨l, hl, hcl⟩ := pairProj_spec hdp ⟨c, smear_le_orbitClosure J A c.2⟩
    rw [hφ] at hcl
    have hlc : (c : Γ) = l := by simpa using hcl.symm
    have hbot : orbitClosure J A ⊓ Subgroup.centralizer (A : Set Γ) ⊓
        sSup (conjOrbit A J \ {J}) = ⊥ :=
      inf_centralizer_inf_sSup_eq_bot_of_transitive hL hper hJΩ
        (fun K hK => exists_conj_of_mem_conjOrbit hJΩ hK)
    have hmem : (c : Γ) ∈ orbitClosure J A ⊓ Subgroup.centralizer (A : Set Γ) ⊓
        sSup (conjOrbit A J \ {J}) := Subgroup.mem_inf.mpr ⟨c.2, hlc ▸ hl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  have hrange : φ.range.map J.subtype = J ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ) := by
    have h1 : φ.range = ((smear J A).subgroupOf (orbitClosure J A)).map (pairProj hdp) := by
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    have h2 := proj_eq_map_pairProj hdp (smear_le_orbitClosure J A)
    rw [h1, ← h2]
    exact projIn_centralizer_eq hL hper hJΩ
  exact ⟨(MonoidHom.ofInjective hinj).trans
    ((Subgroup.equivMapOfInjective _ J.subtype J.subtype_injective).trans
      (MulEquiv.subgroupCongr hrange))⟩

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514
