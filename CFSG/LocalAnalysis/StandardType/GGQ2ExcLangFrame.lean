module

public import CFSG.LocalAnalysis.StandardType.GGQ2ModelFrameMap
public import CFSG.LocalAnalysis.StandardType.GGExcMaxToral
public import CFSG.LocalAnalysis.StandardType.GGQTwoExceptionalComponent

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav
  CFSG.StandardType.ExcMaxToral
open CFSG.Open (IsElemAbelian)

@[expose] def ExcLangModelFrame
    (m : Fin 6) (τ : Tag) : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p), S.D.q = 2 →
    S.IsAlgebraic → (∀ γ, IsRoot τ γ → S.ρ γ = -γ) →
      Nonempty (ModelFrame S.Γ (fullThreeTorus S) (excRaw m))


private theorem rho_eq_neg_of_negative_lang {K : Type} [Field K] {τ : Tag}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {D : LangDatum τ (AlgebraicClosure K)}
    {w : CFSG.LieType.Chevalley.WeylGroup τ} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hDΦ : D.Φ = Units.map (entrywiseHom Fr)) (hDq : D.q = Nat.card K)
    (hDn : D.n = CFSG.LieType.Chevalley.canonicalRep
      (CFSG.LieType.Chevalley.coxeterSystem τ) (AlgebraicClosure K) w)
    (hneg : ∀ u : Fin τ.rank → ℤ, w • u = -u) (hpos : 0 < Nat.card K)
    {S : LangSetup τ (AlgebraicClosure K) 5} (hSD : S.D = D) :
    ∀ γ, IsRoot τ γ → S.ρ γ = -γ := by
  intro γ hγ
  have hfrobD : FrobRootMap D S.ρ := by
    rw [← hSD]
    exact S.frob
  let D' : LangDatum τ (AlgebraicClosure K) :=
    LangDatum.ofFrobenius Fr (Nat.card K) hFr w D.g0_mem
      (by rw [← hDΦ, ← hDn]; exact D.lang)
  have hfrobD' : FrobRootMap D' S.ρ :=
    frobRootMap_congr_fields hDΦ.symm hDq.symm hDn.symm hfrobD
  have h := CFSG.HardMathSupport.Timmesfeld.CrossChar.frobRootMap_ofFrobenius_apply
    (τ := τ) (L := AlgebraicClosure K) (Fr := Fr) (q := Nat.card K) hpos hFr D.g0_mem
    (hg0 := by rw [← hDΦ, ← hDn]; exact D.lang) hfrobD' hγ
  rw [h, hneg γ]

private theorem torus_eq_map_of_torsion_image {K : Type} [Field K] {τ : Tag}
    {E : Subgroup (adjointGroup τ K)} {D : LangDatum τ (AlgebraicClosure K)}
    {S : LangSetup τ (AlgebraicClosure K) 5}
    {ι : adjointGroup τ K →* ModGL τ (AlgebraicClosure K)}
    (hSD : S.D = D) (hqS : S.D.q = 2) (hρS : ∀ γ, IsRoot τ γ → S.ρ γ = -γ)
    (hιval : ∀ c, ι c = D.g0⁻¹ * CFSG.LieType.Chevalley.baseChangeGL
      (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) * D.g0)
    (htor : ∀ y : ModGL τ (AlgebraicClosure K), (y ∈ D.torus ∧ y ^ 3 = 1) ↔
      ∃ x ∈ E, D.g0⁻¹ * CFSG.LieType.Chevalley.baseChangeGL
        (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * D.g0 = y) :
    S.D.torus = E.map ι := by
  rw [hSD]
  ext y
  constructor
  · intro hy
    have hyS : y ∈ S.D.torus := by rwa [hSD]
    have hmemT : y ∈ fullThreeTorus S := by rwa [fullThreeTorus_eq_torus S hqS hρS]
    obtain ⟨x, hx, hxy⟩ := (htor y).1 ⟨hy, ((mem_fullThreeTorus S).1 hmemT).2⟩
    exact ⟨x, hx, (hιval x).trans hxy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ((htor (ι x)).2 ⟨x, hx, (hιval x).symm⟩).1

private theorem langDescent_adjointGroup_exc {K : Type} [Field K] [Finite K] {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (D : LangDatum τ (AlgebraicClosure K))
    (hDΦ : D.Φ = Units.map (entrywiseHom Fr)) :
    LangDescent D 5 ((CFSG.LieType.Chevalley.baseChangeGL
      (algebraMap K (AlgebraicClosure K))).comp (adjointGroup τ K).subtype) := by
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
    rcases hτ with rfl | rfl | rfl
    · exact CFSG.HardMathSupport.Timmesfeld.CrossChar.commutator_adjointGroup_F4_eq_top K
    · exact CFSG.HardMathSupport.Timmesfeld.CrossChar.commutator_adjointGroup_E7_eq_top K
    · exact CFSG.HardMathSupport.Timmesfeld.CrossChar.commutator_adjointGroup_E8_eq_top K
  rcases hτ with rfl | rfl | rfl
  · exact langDescent_exact (Or.inr rfl) hFr D hDΦ hperf
  · exact langDescent_untw 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) hFr D hDΦ
      Nat.prime_five (by norm_num) hperf
  · exact langDescent_untw 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) hFr D hDΦ
      Nat.prime_five (by norm_num) hperf

theorem exists_langSetup_of_excFrame {K : Type} [Field K] [Finite K] {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) (hK : Nat.card K = 2)
    {E : Subgroup (adjointGroup τ K)} (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ excDegCount τ 2 ≤ Nat.card E) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) 5)
      (ι : adjointGroup τ K →* ModGL τ (AlgebraicClosure K)),
      S.D.q = 2 ∧ S.IsAlgebraic ∧ (∀ γ, IsRoot τ γ → S.ρ γ = -γ) ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧ fullThreeTorus S = E.map ι := by
  classical
  let Ω := AlgebraicClosure K
  have hcharK : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK]; norm_num)
  have hcharΩ : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  have hord : orderOf ((Nat.card K : ℕ) : ZMod 3) = 2 := by
    rw [hK]
    exact orderOf_eq_prime (by decide) (by decide)
  have h4 : 4 ≤ excDegCount τ 2 := by
    rcases hτ with rfl | rfl | rfl <;> decide
  have h4' : 4 ≤ excDegCount τ (orderOf (Nat.card K : ZMod 3)) := by
    rw [hord]; exact h4
  have hcard' : 3 ^ excDegCount τ (orderOf (Nat.card K : ZMod 3)) ≤ Nat.card E := by
    rw [hord]; exact hcard
  obtain ⟨Fr, hFr, D, hDΦ, hDq, ⟨w, hDn, hshape⟩, _hmem, htor⟩ :=
    ExcMaxToral.adjointMaxElemToral_of_not_five_four τ K 3 (by norm_num)
      inferInstance inferInstance Nat.prime_three (by norm_num) h4' E hE hcard'
  have hneg : ∀ u : Fin τ.rank → ℤ, w • u = -u := hshape.2.1 hord
  let ι₀ : adjointGroup τ K →* ModGL τ Ω :=
    (CFSG.LieType.Chevalley.baseChangeGL (algebraMap K Ω)).comp (adjointGroup τ K).subtype
  have hι₀ : Function.Injective ι₀ :=
    (CFSG.LieType.Chevalley.baseChangeGL_injective (algebraMap K Ω)).comp
      (Subgroup.subtype_injective _)
  have hd : LangDescent D 5 ι₀ := langDescent_adjointGroup_exc hτ hFr D hDΦ
  have hfin : Finite D.model := hd.finite_model
  have hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := hd.Γ_eq
  obtain ⟨S, ι, hSD, hιval, hιinj, hιrange, _huniform⟩ :=
    LangRat.exists_langSetup_of_toral_datum_uniform (τ := τ) (L := Ω) (ℓ := 2) (f := 1)
      Nat.prime_two le_rfl D (by rw [hDq, hK]; norm_num)
      Nat.prime_five (by norm_num) (Or.inl le_rfl) hfin ι₀ hι₀ hΓ
  have hqS : S.D.q = 2 := by rw [hSD, hDq, hK]
  have hAlg : S.IsAlgebraic :=
    S.isAlgebraic_of_isAlgClosure K 1 (by rw [pow_one, hqS, hK])
  have hρS : ∀ γ, IsRoot τ γ → S.ρ γ = -γ :=
    rho_eq_neg_of_negative_lang hFr hDΦ hDq hDn hneg (by rw [hK]; norm_num) hSD
  have htorEq : S.D.torus = E.map ι :=
    torus_eq_map_of_torsion_image hSD hqS hρS hιval htor
  have hfull : fullThreeTorus S = E.map ι := by
    rw [fullThreeTorus_eq_torus S hqS hρS, htorEq]
  exact ⟨S, ι, hqS, hAlg, hρS, hιinj, hιrange, hfull⟩

theorem excUntwModelFrame_of_lang {m : Fin 6} {τ : Tag}
    (hmτ : (m = 0 ∧ τ = .F4) ∨ (m = 4 ∧ τ = .E7) ∨ (m = 5 ∧ τ = .E8))
    (h : ExcLangModelFrame m τ) : ExcUntwModelFrame m τ := by
  obtain ⟨hτ, hdeg⟩ : (τ = .F4 ∨ τ = .E7 ∨ τ = .E8) ∧ excDegCount τ 2 = ExcRaw.dim m := by
    rcases hmτ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Or.inl rfl, by decide⟩
    · exact ⟨Or.inr (Or.inl rfl), by decide⟩
    · exact ⟨Or.inr (Or.inr rfl), by decide⟩
  intro K _ _ hK E hE hcard _
  obtain ⟨S, ι, hq, hAlg, hρ, hιinj, hιrange, hfull⟩ :=
    exists_langSetup_of_excFrame (K := K) (τ := τ) hτ hK hE (by rw [hdeg]; exact hcard.symm.le)
  obtain ⟨mf⟩ := h S hq hAlg hρ
  have hΓtop : S.Γ = (⊤ : Subgroup (adjointGroup τ K)).map ι := by
    rw [← hιrange, MonoidHom.range_eq_map]
  rw [hΓtop, hfull] at mf
  exact nonempty_modelFrame_of_map hιinj mf

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
