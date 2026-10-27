module

public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLAmbDefs
public import CFSG.LocalAnalysis.StandardType.GGCanonicalToLegacy

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQTwoXInLClTag (t : LargeEvenLieTag) : Prop :=
  t = .A ∨ t = .twA ∨ t = .B ∨ t = .C ∨ t = .D ∨ t = .twD

theorem ggQTwoXInL_rawDatum_extract {lab : LargeEvenLabel} {P : Prop}
    (h : CFSG.Assembly.LargeEvenRawDatum lab (fun _ _ _ _ => P)) : P := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := h; exact hq)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := h; exact hq)

theorem ggQTwoXInL_marking_canonical {G : Type} [Group G] {Bs X : Subgroup G} (h : GGInnerDiagOn Bs X) :
    CFSG.Assembly.LargeEvenMarking X (fun _ _ _ I _ θ => Bs ≤ Subgroup.normalizer (X : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  refine ⟨hX, lab, hlab, largeEvenRawDatum_canonical_of_legacy_mono ?_ hraw⟩
  rintro R _ I I' F hII' ⟨hs, hna, θ, hN, hb⟩
  refine ⟨hs, hna, θ, hN, fun b hbB => ?_⟩
  obtain ⟨φ, hφ, hind⟩ := hb b hbB
  exact ⟨φ, hII' hφ, hind⟩

theorem ggQTwoXInL_ambOn_split (c : LargeEvenLieTag → Prop) {G : Type} [Group G] {Bs X : Subgroup G}
    (h : GGInnerDiagOn Bs X) : GGQTwoXInLAmbOn c Bs X ∨ GGQTwoXInLAmbOn (fun t => ¬ c t) Bs X := by
  obtain ⟨hX, lab, hlab, hraw⟩ := ggQTwoXInL_marking_canonical h
  by_cases hc : c lab.tag
  · left
    refine ⟨hX, lab, hlab, Canonical.largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hθ⟩
    exact ⟨hs, hna, θ, hc, hθ⟩
  · right
    refine ⟨hX, lab, hlab, Canonical.largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hθ⟩
    exact ⟨hs, hna, θ, hc, hθ⟩

theorem ggQTwoXInL_ambOn_cases {c c1 c2 c3 : LargeEvenLieTag → Prop}
    (hc : ∀ t, c t → c1 t ∨ c2 t ∨ c3 t) {G : Type} [Group G] {Bs X : Subgroup G}
    (h : GGQTwoXInLAmbOn c Bs X) :
    GGQTwoXInLAmbOn c1 Bs X ∨ GGQTwoXInLAmbOn c2 Bs X ∨ GGQTwoXInLAmbOn c3 Bs X := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  have hct : c lab.tag := ggQTwoXInL_rawDatum_extract
    (Canonical.largeEvenRawDatum_mono (fun R _ I F ⟨hs, hna, θ, hθ⟩ => hθ.1) hraw)
  rcases hc _ hct with h1 | h2 | h3
  · left
    refine ⟨hX, lab, hlab, Canonical.largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hθ⟩
    exact ⟨hs, hna, θ, h1, hθ.2⟩
  · right; left
    refine ⟨hX, lab, hlab, Canonical.largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hθ⟩
    exact ⟨hs, hna, θ, h2, hθ.2⟩
  · right; right
    refine ⟨hX, lab, hlab, Canonical.largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hθ⟩
    exact ⟨hs, hna, θ, h3, hθ.2⟩

@[expose] def GGQTwoXInLNbrOn (c : LargeEvenLieTag → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGQTwoSetting p B Bs x L D J → GGQTwoI1 Bs D J → x ∈ L →
    GGQTwoXInLAmbOn c Bs (ggG0 p B x L D J) → ∀ [Fact p.Prime],
      ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
        Nonempty (GGQTwoModel p Bs x y D L J K)

@[expose] def GGQTwoXInLNbrClassical : Prop := GGQTwoXInLNbrOn GGQTwoXInLClTag

@[expose] def GGQTwoXInLNbrRest : Prop := GGQTwoXInLNbrOn (fun t => ¬ GGQTwoXInLClTag t)

theorem ggQTwoXInLNbr_of_split (c : LargeEvenLieTag → Prop) (h1 : GGQTwoXInLNbrOn c)
    (h2 : GGQTwoXInLNbrOn (fun t => ¬ c t)) : GGQTwoXInLNbrModelInput := by
  intro G _ _ p B Bs x L D J hS hI hx hp
  rcases ggQTwoXInL_ambOn_split c hS.1.2.2.2.2 with h | h
  · exact h1 G p B Bs x L D J hS hI hx h
  · exact h2 G p B Bs x L D J hS hI hx h

theorem ggQTwoXInLNbr_of_classical_rest (hC : GGQTwoXInLNbrClassical) (hR : GGQTwoXInLNbrRest) :
    GGQTwoXInLNbrModelInput := ggQTwoXInLNbr_of_split GGQTwoXInLClTag hC hR

end CFSG.StandardType

end
