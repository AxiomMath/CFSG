module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGL44iiiTriD4LangInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G),
    GGFieldCaseNoBL5 p B Bs x L D J X → GGTableBModule p Bs x L B₂ → GGL43 Bs x X →
      GGL44i p Bs x X → GGL44ii Bs x X B₂ →
      ∀ d ∈ D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)), d ≠ 1 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        Subgroup.zpowers y = Subgroup.zpowers d →
        ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
          GGMarkingAll (K := ↥K) fun lab _ _ I F θ => lab.tag = .triD4 ∧ p = 3 →
            (∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
              ggLAut K θ ⟨b, hN hb⟩ = u * f) →
            (∀ (b : G) (hb : b ∈ Bs ⊓ Subgroup.centralizer (X : Set G)),
              ggLAut K θ ⟨b, hN hb.1⟩ ∈ I) →
            (∃ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∉ I) →
            ∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧
              LargeEvenInduces θ (fun k k' => (k' : G) = x⁻¹ * k * x) (u * f * u⁻¹)

@[expose] def GGL44iiiTriD4NoneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G),
    GGFieldCaseNoBL5 p B Bs x L D J X → GGTableBModule p Bs x L B₂ → GGL43 Bs x X →
      GGL44i p Bs x X → GGL44ii Bs x X B₂ →
      ∀ d ∈ D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)), d ≠ 1 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        Subgroup.zpowers y = Subgroup.zpowers d →
        ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
          GGMarkingAll (K := ↥K) fun lab _ _ I F θ => lab.tag = .triD4 ∧ p = 3 →
            (∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
              ggLAut K θ ⟨b, hN hb⟩ = u * f) →
            (∀ (b : G) (hb : b ∈ Bs ⊓ Subgroup.centralizer (X : Set G)),
              ggLAut K θ ⟨b, hN hb.1⟩ ∈ I) →
            (∃ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∉ I) → False

theorem ggL44iiiTriD4LangInput_of_none (h : GGL44iiiTriD4NoneInput) : GGL44iiiTriD4LangInput := by
  intro G _ _ p B Bs x L D J X B₂ hFC hM h43 h44 h44ii d hd hd1 y K hnbr hyd hN P hP
  refine largeEvenMarking_mono ?_
    (h G p B Bs x L D J X B₂ hFC hM h43 h44 h44ii d hd hd1 y K hnbr hyd hN P hP)
  rintro lab R _ I F θ ⟨hPθ, hQ⟩
  exact ⟨hPθ, fun hex hgrθ hB₁ hS1θ => (hQ hex hgrθ hB₁ hS1θ).elim⟩

theorem largeEvenMarking_and_labelAll_imp {X : Type*} [Group X] {P : LargeEvenMarkProp X}
    {S : LargeEvenLabel → Prop} {P' : LargeEvenRawCont}
    (hall : ∀ lab, LargeEvenInLambda2 lab → S lab → LargeEvenLabelAll lab P')
    (h : LargeEvenMarking X P) :
    LargeEvenMarking X fun lab R _ I F θ => P lab R I F θ ∧ (S lab → P' R I F) := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  by_cases hS : S lab
  · refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ (hall lab hlab hS _ hraw)⟩
    rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hP'⟩
    exact ⟨hs, hna, θ, hθ, fun _ => hP'⟩
  · refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hθ⟩
    exact ⟨hs, hna, θ, hθ, fun h => absurd h hS⟩

section Core

variable {G : Type} [Group G] [Finite G]

theorem ggL44iiiMarking_core_exc {p : ℕ} {Bs X K : Subgroup G} {x : G} {lab : LargeEvenLabel}
    {R : Type} [Group R] {I F : Set (MulAut R)} (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hxBs : x ∈ Bs) (hxp : x ^ p = 1)
    (hsplit : Bs = (Bs ⊓ Subgroup.centralizer (X : Set G)) ⊔ Subgroup.zpowers x)
    (hxc : ∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G), x * b = b * x)
    (hmul : ∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I) (hinv : ∀ φ ∈ I, φ⁻¹ ∈ I)
    (hone : (1 : MulAut R) ∈ I)
    (hlang : ¬ (lab.tag = .triD4 ∧ p = 3) → ∀ u ∈ I, ∀ f ∈ Subgroup.closure F, u * f ∉ I →
      (u * f) ^ p = 1 → ∃ f' ∈ F, ∃ u' ∈ I, orderOf f' = p ∧ u * f = u' * f' * u'⁻¹)
    (hD4 : lab.tag = .triD4 ∧ p = 3 → ∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧
      LargeEvenInduces θ (fun k k' => (k' : G) = x⁻¹ * k * x) (u * f * u⁻¹))
    (hgr : ∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
      ggLAut K θ ⟨b, hN hb⟩ = u * f)
    (hB₁ : ∀ (b : G) (hb : b ∈ Bs ⊓ Subgroup.centralizer (X : Set G)),
      ggLAut K θ ⟨b, hN hb.1⟩ ∈ I)
    (hS1 : ∃ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∉ I) :
    (∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G), ∃ φ ∈ I,
        LargeEvenInduces θ (fun k k' => (k' : G) = b⁻¹ * k * b) φ) ∧
      ∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧
        LargeEvenInduces θ (fun k k' => (k' : G) = x⁻¹ * k * x) (u * f * u⁻¹) := by
  by_cases hex : lab.tag = .triD4 ∧ p = 3
  · refine ⟨fun b hb => ⟨ggLAut K θ ⟨b⁻¹, hN (Bs.inv_mem hb.1)⟩,
      hB₁ b⁻¹ ((Bs ⊓ Subgroup.centralizer (X : Set G)).inv_mem hb),
      largeEvenInduces_ggLAut_inv K θ (hN (Bs.inv_mem hb.1))⟩, hD4 hex⟩
  · exact ggL44iiiMarking_core θ hN hxBs hxp hsplit hxc hmul hinv hone (hlang hex) hgr hB₁ hS1

end Core

theorem ggL44iiiMarkingInput_of_parts_exc (hBN : GGBstarNbrNormalInput) (hgr : GGNbrGraphInput)
    (hraw : GGRawInnFieldInput) (hcen : GGRawFieldCentralInput)
    (hlang : GGRawFieldConjInputExc) (hL : GGLBalanceInput) (hJp : GGStdSubPrimeInput)
    (hI2 : GGStdSubBstarMeetInput) (hS1 : GGL44iiiNotInnerInput)
    (hS5 : GGL44iiiMcLaughlinInput) (hD4 : GGL44iiiTriD4LangInput) : GGL44iiiMarkingInput := by
  intro G _ _ p B Bs x L D J X B₂ hFC hM h43 h44 h44ii d hd hd1 y K hnbr hyd
  obtain ⟨hI, hBstar, hDJ⟩ := hFC.1
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hI.2.2.2.2.2.1.2.1
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType p B x L := hI.2.2.2.2.2.2.2
  have hBs : IsElemAbelian p Bs := hBstar.2.1
  have hxBs : x ∈ Bs := hBstar.1 hS.2.1
  have hxp : x ^ p = 1 := hBs.2 x hxBs
  have hxc : ∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G), x * b = b * x :=
    fun b hb => mul_comm_of_isElemAbelian hBs hxBs hb.1
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := hBN G p B Bs x L D J hFC.1 y K hnbr
  have hpJ : p ∣ Nat.card J := hJp G p B x L D J hI hDJ
  have hKd : LargeEvenPComponent p (Subgroup.centralizer ({d} : Set G)) K := by
    rw [← centralizer_singleton_eq_of_zpowers_eq hyd]
    exact hnbr.1.2.2.2.2.1
  have hXK : X ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_ggL44i hFC h44 hpJ (hI2 G p B Bs x L D J hFC.1) hd.2.2 hKd
      (le_of_ggNbr hL hI hDJ hpJ hnbr)
  have hK0 : LargeEvenMarking ↥K fun _ _ _ _ _ _ => True :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
      (hst.2.2.1 y K (isNeighborOf_of_ggNbr hDJ hnbr)).2
  have hK1 := hgr G p B Bs x L D J hFC.1 y K hnbr hN _ hK0
  have hK2 := largeEvenMarking_and_labelAll (S := fun _ => True)
    (fun lab hlab _ => hraw p hp hp2 lab hlab) (fun _ _ _ _ _ _ _ => trivial) hK1
  have hK3 := largeEvenMarking_and_labelAll (S := fun _ => True)
    (fun lab hlab _ => hcen lab hlab) (fun _ _ _ _ _ _ _ => trivial) hK2
  have hK4 := largeEvenMarking_and_labelAll_imp (S := fun lab => ¬ (lab.tag = .triD4 ∧ p = 3))
    (fun lab hlab hne => hlang p hp hp2 lab hlab hne) hK3
  have hK5 := hS1 G p B Bs x L D J X B₂ hFC hM h43 h44 h44ii d hd hd1 y K hnbr hyd hN _ hK4
  have hK6 := hD4 G p B Bs x L D J X B₂ hFC hM h43 h44 h44ii d hd hd1 y K hnbr hyd hN _ hK5
  rcases h44ii with h44a | ⟨hlt, h44b⟩
  · refine largeEvenMarking_mono_of_simple ?_ hK6
    rintro lab R _ I F θ hs hna ⟨⟨⟨⟨⟨⟨-, hgrθ⟩, hrawθ⟩, hcenθ⟩, hlangθ⟩, hS1θ⟩, hD4θ⟩
    obtain ⟨hmul, hinv, hinn, -⟩ := hrawθ hs hna
    have hone : (1 : MulAut R) ∈ I := by simpa using hinn 1
    have hB₁ := ggL44iiiInner_of_first θ hN hXK hxBs (hcenθ hs hna) hgrθ inf_le_left
      (fun b hb => (h44a b).1 hb)
    exact ⟨hN, ggL44iiiMarking_core_exc θ hN hxBs hxp h43.2 hxc hmul hinv hone
      (fun hne => hlangθ hne hs hna) (fun hex => hD4θ hex hgrθ hB₁ (hS1θ hgrθ)) hgrθ hB₁
      (hS1θ hgrθ)⟩
  · have hK7 := hS5 G p B Bs x L D J X B₂ hFC hM h43 h44 hlt h44b d hd hd1 y K hnbr hyd hN _ hK6
    refine largeEvenMarking_mono_of_simple ?_ hK7
    rintro lab R _ I F θ hs hna ⟨⟨⟨⟨⟨⟨⟨-, hgrθ⟩, hrawθ⟩, hcenθ⟩, hlangθ⟩, hS1θ⟩, hD4θ⟩, hS5θ⟩
    obtain ⟨hmul, hinv, hinn, -⟩ := hrawθ hs hna
    have hone : (1 : MulAut R) ∈ I := by simpa using hinn 1
    have hB₁₂ := ggL44iiiInner_of_first θ hN hXK hxBs (hcenθ hs hna) hgrθ
      (inf_le_left.trans inf_le_left) (fun b hb => (h44b b).1 hb)
    have hB₁ := hS5θ hgrθ hB₁₂ (hS1θ hgrθ)
    exact ⟨hN, ggL44iiiMarking_core_exc θ hN hxBs hxp h43.2 hxc hmul hinv hone
      (fun hne => hlangθ hne hs hna) (fun hex => hD4θ hex hgrθ hB₁ (hS1θ hgrθ)) hgrθ hB₁
      (hS1θ hgrθ)⟩

theorem ggL44iiiTriD4LangInput_of_conj (hraw : GGRawInnFieldInput)
    (hlang : GGRawFieldConjInput) : GGL44iiiTriD4LangInput := by
  intro G _ _ p B Bs x L D J X B₂ hFC _ h43 _ _ _ _ _ y K _ _ hN P hP
  obtain ⟨hI, hBstar, -⟩ := hFC.1
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hI.2.2.2.2.2.1.2.1
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hBs : IsElemAbelian p Bs := hBstar.2.1
  have hxBs : x ∈ Bs := hBstar.1 hS.2.1
  have hxp : x ^ p = 1 := hBs.2 x hxBs
  have hxc : ∀ b ∈ Bs ⊓ Subgroup.centralizer (X : Set G), x * b = b * x :=
    fun b hb => mul_comm_of_isElemAbelian hBs hxBs hb.1
  have hP2 := largeEvenMarking_and_labelAll (S := fun _ => True)
    (fun lab hlab _ => hraw p hp hp2 lab hlab) (fun _ _ _ _ _ _ _ => trivial) hP
  have hP3 := largeEvenMarking_and_labelAll (S := fun _ => True)
    (fun lab hlab _ => hlang p hp hp2 lab hlab) (fun _ _ _ _ _ _ _ => trivial) hP2
  refine largeEvenMarking_mono_of_simple ?_ hP3
  rintro lab R _ I F θ hs hna ⟨⟨hPθ, hrawθ⟩, hlangθ⟩
  refine ⟨hPθ, fun _ hgrθ hB₁ hS1θ => ?_⟩
  obtain ⟨hmul, hinv, hinn, -⟩ := hrawθ hs hna
  have hone : (1 : MulAut R) ∈ I := by simpa using hinn 1
  exact (ggL44iiiMarking_core θ hN hxBs hxp h43.2 hxc hmul hinv hone (hlangθ hs hna) hgrθ hB₁
    hS1θ).2

end CFSG.StandardType

end
