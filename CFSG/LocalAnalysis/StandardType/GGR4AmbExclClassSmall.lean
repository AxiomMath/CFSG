module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGClassicalEmbed
public import CFSG.LocalAnalysis.StandardType.GGR4ActionHom
public import CFSG.LocalAnalysis.StandardType.GGR4DatumComplement
public import CFSG.LocalAnalysis.StandardType.GGR4PDTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem acs_ggClassDeg_lt_24 {lab : LargeEvenLabel} (hS : GGR4ClassSmall lab) :
    ggClassDeg lab < 24 := by
  obtain ⟨hcl, hbig⟩ := hS
  rcases lab with ⟨t, l, n⟩
  cases t <;>
    simp only [GGR4ClassBig, ggClassDeg, reduceCtorEq, false_and, false_or, or_false, or_true,
      true_and] at hcl hbig ⊢ <;>
    (try split_ifs at hbig ⊢) <;> omega

theorem ggR4AmbExcl_classSmall (hPD : GGProjDegreeF4) : GGR4AmbExcl GGR4ClassSmall := by
  intro G _ _ B Bs x L D J hCfg hInner hCard hFact Γ _ _ C V _ _ ι φ h α hD hF4 hGen hmark
  obtain ⟨hperf, lab, hlab, hraw⟩ := hmark
  have hS : GGR4ClassSmall lab := by
    refine GGDichotomy.rawDatum_elim_const (largeEvenRawDatum_mono (fun R _ I F hq => ?_) hraw)
    obtain ⟨-, -, θ, hθ⟩ := hq
    exact hθ.1
  obtain ⟨R, _, I, F, hq, hemb⟩ :=
    largeEvenRawDatum_exists (ggClassicalProjEmbed_holds lab hlab hS.1 _ hraw)
  obtain ⟨-, -, θ, -, hBsN, hBs3⟩ := hq
  obtain ⟨hinn, K, hField, hAlgClosed, hCharP, ε, hε⟩ := hemb
  letI : Field K := hField
  letI : IsAlgClosed K := hAlgClosed
  letI : CharP K 2 := hCharP
  obtain ⟨ρ, hρI, hρL, hρk⟩ := ggR4_actionHom hCfg hperf θ hBsN hBs3
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  let M₀' : Subgroup ↥N := (Subgroup.closure I).comap ρ
  let M₀ : Subgroup G := M₀'.map N.subtype
  let hmap : Set.MapsTo ρ (M₀' : Set ↥N) (Subgroup.closure I : Set (MulAut R)) :=
    fun x hx => Subgroup.mem_comap.mp hx
  let Φ' : ↥M₀' →* (Matrix.GeneralLinearGroup (Fin (ggClassDeg lab)) K ⧸
      Subgroup.center (Matrix.GeneralLinearGroup (Fin (ggClassDeg lab)) K)) :=
    ε.comp (ρ.restrict hmap)
  let e : ↥M₀' ≃* ↥M₀ := Subgroup.equivMapOfInjective M₀' N.subtype N.subtype_injective
  let Φ : ↥M₀ →* (Matrix.GeneralLinearGroup (Fin (ggClassDeg lab)) K ⧸
      Subgroup.center (Matrix.GeneralLinearGroup (Fin (ggClassDeg lab)) K)) :=
    Φ'.comp (e.symm : ↥M₀ →* ↥M₀')
  obtain ⟨Hb, ι', φ', h', α', hHbBs, hHbx, hHbcard, hHbab, hD', hGen'⟩ :=
    ggR4_datum_complement hCfg hCard hD hF4 hGen
  have hHb : Hb ≤ M₀ := by
    intro b hb
    exact Subgroup.mem_map.mpr ⟨⟨b, hBsN (hHbBs hb)⟩,
      Subgroup.mem_comap.mpr (Subgroup.subset_closure (hρI b (hHbBs hb))), rfl⟩
  have hL : L ≤ M₀ := by
    intro l hl
    refine Subgroup.mem_map.mpr ⟨⟨l, Subgroup.le_normalizer hl⟩, ?_, rfl⟩
    refine Subgroup.mem_comap.mpr ?_
    rw [hρL ⟨l, hl⟩]
    exact Subgroup.subset_closure (hinn _)
  have hinj : ∀ (b : G) (hb : b ∈ Hb), Φ ⟨b, hHb hb⟩ = 1 → b = 1 := by
    intro b hb hΦ
    let hbN : ↥N := ⟨b, hBsN (hHbBs hb)⟩
    have hbM' : hbN ∈ M₀' :=
      Subgroup.mem_comap.mpr (Subgroup.subset_closure (hρI b (hHbBs hb)))
    let hbM : ↥M₀' := ⟨hbN, hbM'⟩
    have he1 : e hbM = ⟨b, hHb hb⟩ := Subtype.ext rfl
    have he : e.symm ⟨b, hHb hb⟩ = hbM := by
      rw [← he1, e.symm_apply_apply]
    have h1 : Φ' (e.symm ⟨b, hHb hb⟩) = 1 := by
      change Φ ⟨b, hHb hb⟩ = 1
      exact hΦ
    have h2 : Φ' hbM = 1 := by
      rw [he] at h1
      exact h1
    have h4 : (ρ.restrict hmap) hbM = 1 := by
      apply hε
      rw [map_one]
      exact h2
    have h3 : ρ hbN = 1 :=
      congrArg (fun z : ↥(Subgroup.closure I) => (z : MulAut R)) h4
    have hbz : b ∈ Subgroup.zpowers x := (hρk b (hHbBs hb)).mp h3
    have hbot : b ∈ (⊥ : Subgroup G) := by
      rw [← hHbx]
      exact ⟨hb, hbz⟩
    simpa using hbot
  have h24 : 24 ≤ ggClassDeg lab :=
    ggR4_pd_transport hPD hHb hL Φ hinj hHbcard hHbab hD' hF4 hGen'
  exact absurd h24 (not_le.mpr (acs_ggClassDeg_lt_24 hS))

end CFSG.StandardType

end
