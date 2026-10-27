module

public import CFSG.RankThree.PartOne.S15K.KtData
public import CFSG.RankThree.PartOne.S15K.CovAtAux
public import CFSG.RankThree.PartOne.S15K.LayerData
public import CFSG.RankThree.PartOne.S12.Sec158

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem autMovedInG_le_zeroLayer (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E) (hEA : E = A) {s : MulAut E}
    (hs : s ∈ reflectionSet p E) (hsp : SplitKt p E s) {b : G} (hb : b ∈ autFixedInG E s)
    (hb1 : b ≠ 1) : autMovedInG E s ≤ zeroLayer p E b := by
  obtain ⟨hKt, hmov, hcard, hθ, hS2⟩ := splitKt_data h15.h12 hEA hs hsp
  obtain ⟨f, hpf, hKFAt⟩ := hsp
  have hcent := hKFAt.2.2.1
  have hbD : b ∈ A ⊓ Subgroup.centralizer (kZero p E s : Set G) := by
    subst hEA
    rw [hcent]
    exact hb
  exact hmov.trans (Sec158.layer_ge_of_KF158A hS h82 h15 hcard hθ hS2 hbD hb1)

omit [Finite G] in
theorem le_of_sup_eq_top {E : Subgroup G} {H₁ H₂ : Subgroup E} {X : Subgroup G}
    (h : H₁ ⊔ H₂ = ⊤) (h1 : H₁.map E.subtype ≤ X) (h2 : H₂.map E.subtype ≤ X) : E ≤ X := by
  intro g hg
  have hmem : g ∈ (H₁ ⊔ H₂).map E.subtype :=
    ⟨⟨g, hg⟩, by rw [h]; trivial, rfl⟩
  rw [Subgroup.map_sup] at hmem
  exact sup_le h1 h2 hmem

omit [Finite G] in
theorem exists_mem_autMoved_of_zpowers {p : ℕ} {E : Subgroup G} {t : MulAut E} (hp : p.Prime)
    (ht : Nat.card (autMoved E t) = p) {a : G} (ha : Subgroup.zpowers a = autMovedInG E t) :
    ∃ ã : E, ã ∈ autMoved E t ∧ (ã : G) = a ∧ ã ≠ 1 := by
  have haM : a ∈ autMovedInG E t := ha ▸ Subgroup.mem_zpowers a
  obtain ⟨ã, hã, hãa⟩ := Subgroup.mem_map.1 haM
  refine ⟨ã, hã, hãa, ?_⟩
  intro h1
  have ha1 : a = 1 := by rw [← hãa, h1]; rfl
  have hcard : Nat.card ↥(autMovedInG E t) = p := by
    unfold autMovedInG
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact ht
  rw [← ha, ha1] at hcard
  simp at hcard
  exact hp.one_lt.ne' hcard.symm

theorem covAt_rowB (hS : SchreierFor InCatalog) (h82 : LocalThetaComponentEmbeddingFrontier) {p : ℕ}
    {A : Subgroup G} {c : G} {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E)
    (hirr : torusIrreducible E) (hEA : E = A) (σ : ↥(reflectionGroup p E) ≃* R2S4)
    (hAll : ∀ s ∈ reflectionSet p E, SplitKt p E s) {t : MulAut E} (ht : t ∈ reflectionSet p E)
    {a : G} (ha : Subgroup.zpowers a = autMovedInG E t) :
    E ≤ zeroLayer p E a ⊔ Subgroup.zpowers a := by
  have h := h15.h12
  have C := reflCtx_of_hyp h
  have hE3 : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  obtain ⟨s₁, hs₁, s₂, hs₂, hne₁, hne₂, hne₁₂, hc₁, hc₂, hc₁₂⟩ := rowB_frame C hirr hE3 σ ht
  obtain ⟨ã, hã, hãa, hã1⟩ := exists_mem_autMoved_of_zpowers C.prime ht.1.2 ha
  have htt := ReflCtx.mul_self_eq_one_of ht.1
  have hss₁ := ReflCtx.mul_self_eq_one_of hs₁.1
  have hss₂ := ReflCtx.mul_self_eq_one_of hs₂.1
  have ha1 : a ≠ 1 := fun h1 => hã1 (Subtype.ext (hãa.trans h1))
  have hfix₁ : a ∈ autFixedInG E s₁ :=
    ⟨ã, C.fixes_moved hss₁ htt hc₁.symm hs₁.1.2 ht.1.2 hne₁ hã, hãa⟩
  have hfix₂ : a ∈ autFixedInG E s₂ :=
    ⟨ã, C.fixes_moved hss₂ htt hc₂.symm hs₂.1.2 ht.1.2 hne₂ hã, hãa⟩
  have hsup := C.eq_sup_of_three ht.1 hs₁.1 hs₂.1 hc₁ hc₂ hc₁₂ hne₁.symm hne₂.symm hne₁₂ hE3
  have h₁ := autMovedInG_le_zeroLayer hS h82 h15 hEA hs₁ (hAll s₁ hs₁) hfix₁ ha1
  have h₂ := autMovedInG_le_zeroLayer hS h82 h15 hEA hs₂ (hAll s₂ hs₂) hfix₂ ha1
  refine le_of_sup_eq_top hsup ?_ ?_
  · show autMovedInG E t ≤ _
    rw [← ha]
    exact le_sup_right
  · rw [Subgroup.map_sup]
    exact le_sup_of_le_left (sup_le h₁ h₂)

theorem covAt_rowOne (hS : SchreierFor InCatalog) (h82 : LocalThetaComponentEmbeddingFrontier)
    {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E)
    (hEA : E = A) (σ : ↥(reflectionGroup p E) ≃* Equiv.Perm (Fin 4))
    (hAll : ∀ s ∈ reflectionSet p E, SplitKt p E s) {t : MulAut E} (ht : t ∈ reflectionSet p E)
    {a : G} (ha : Subgroup.zpowers a = autMovedInG E t) :
    ∃ d ∈ E, d ≠ 1 ∧ d ∈ zeroLayer p E a ⊔ Subgroup.zpowers a ∧
      E ≤ zeroLayer p E d ⊔ Subgroup.zpowers d := by
  have h := h15.h12
  have C := reflCtx_of_hyp h
  have hE3 : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  obtain ⟨s, hs, t', ht', s', hs', hts, htne, ht's', ht'ne, hconj⟩ := rowOne_frame C σ ht
  obtain ⟨ã, hã, hãa, hã1⟩ := exists_mem_autMoved_of_zpowers C.prime ht.1.2 ha
  have htt := ReflCtx.mul_self_eq_one_of ht.1
  have hss := ReflCtx.mul_self_eq_one_of hs.1
  have ha1 : a ≠ 1 := fun h1 => hã1 (Subtype.ext (hãa.trans h1))
  obtain ⟨d, hd1, ⟨b, hb, hdab⟩, hdt', hds', hsup⟩ :=
    C.exists_frame_element ht.1 hs.1 ht'.1 hs'.1 hts htne ht's' ht'ne hconj hE3 hã hã1
  have hfix : a ∈ autFixedInG E s :=
    ⟨ã, C.fixes_moved hss htt hts.symm hs.1.2 ht.1.2 htne.symm hã, hãa⟩
  have hbX : (b : G) ∈ zeroLayer p E a :=
    autMovedInG_le_zeroLayer hS h82 h15 hEA hs (hAll s hs) hfix ha1 ⟨b, hb, rfl⟩
  have hd1' : (d : G) ≠ 1 := fun h1 => hd1 (Subtype.ext h1)
  refine ⟨(d : G), d.2, hd1', ?_, ?_⟩
  · have hda : (d : G) = a * (b : G) := by rw [hdab, ← hãa]; rfl
    rw [hda, sup_comm]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers a) hbX
  · have hfix' : (d : G) ∈ autFixedInG E t' := ⟨d, hdt', rfl⟩
    have hfix'' : (d : G) ∈ autFixedInG E s' := ⟨d, hds', rfl⟩
    have h₁ := autMovedInG_le_zeroLayer hS h82 h15 hEA ht' (hAll t' ht') hfix' hd1'
    have h₂ := autMovedInG_le_zeroLayer hS h82 h15 hEA hs' (hAll s' hs') hfix'' hd1'
    refine le_of_sup_eq_top hsup ?_ ?_
    · have : ((Subgroup.zpowers d).map E.subtype : Subgroup G) = Subgroup.zpowers (d : G) := by
        rw [MonoidHom.map_zpowers]
        rfl
      rw [this]
      exact le_sup_right
    · rw [Subgroup.map_sup]
      exact le_sup_of_le_left (sup_le h₁ h₂)

@[expose] def KF158AllSplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E →
    (Outcome152One p E A (lieGenerated p E) ∨ Outcome152Two p E A (lieGenerated p E) ∨
      Outcome152Three p E A (lieGenerated p E)) →
    ∀ s ∈ reflectionSet p E, SplitKt p E s

@[expose] def KF158CovAtRowFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    Outcome152Four p E A (lieGenerated p E) →
    ∀ t ∈ reflectionSet p E, ∀ K J : Subgroup G, IsKt p E t K → K ≤ J → autMovedInG E t ≤ K →
      p * Nat.card ↥(A ⊓ Subgroup.centralizer (J : Set G)) = Nat.card ↥A →
      J ∈ thetaCompCentralizer p (A ⊓ Subgroup.centralizer (J : Set G)) →
      (∃ S : Subgroup G, S ≤ J ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
        S = ⁅S, A⁆) →
      ∀ a : G, Subgroup.zpowers a = autMovedInG E t →
        (E ≤ zeroLayer p E a ⊔ Subgroup.zpowers a) ∨
        (Outcome152One p E A (lieGenerated p E) ∧ ∃ d ∈ E, d ≠ 1 ∧
          d ∈ zeroLayer p E a ⊔ Subgroup.zpowers a ∧ E ≤ zeroLayer p E d ⊔ Subgroup.zpowers d) ∨
        (Outcome152Five p E A (lieGenerated p E) ∧ ∃ w ∈ torusNormalizer E,
          w * a * w⁻¹ ∈ zeroLayer p E a ∧
          zeroLayer p E a ⊔ conjBy w (zeroLayer p E a) = lieGenerated p E)

@[expose] def KF158CovAtRowFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ t ∈ reflectionSet p E, ∀ K J : Subgroup G, IsKt p E t K → K ≤ J → autMovedInG E t ≤ K →
      p * Nat.card ↥(A ⊓ Subgroup.centralizer (J : Set G)) = Nat.card ↥A →
      J ∈ thetaCompCentralizer p (A ⊓ Subgroup.centralizer (J : Set G)) →
      (∃ S : Subgroup G, S ≤ J ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ A ≤ Subgroup.normalizer (S : Set G) ∧
        S = ⁅S, A⁆) →
      ∀ a : G, Subgroup.zpowers a = autMovedInG E t →
        (E ≤ zeroLayer p E a ⊔ Subgroup.zpowers a) ∨
        (Outcome152One p E A (lieGenerated p E) ∧ ∃ d ∈ E, d ≠ 1 ∧
          d ∈ zeroLayer p E a ⊔ Subgroup.zpowers a ∧ E ≤ zeroLayer p E d ⊔ Subgroup.zpowers d) ∨
        (Outcome152Five p E A (lieGenerated p E) ∧ ∃ w ∈ torusNormalizer E,
          w * a * w⁻¹ ∈ zeroLayer p E a ∧
          zeroLayer p E a ⊔ conjBy w (zeroLayer p E a) = lieGenerated p E)

theorem kf158CovAt_of_rows (hS : SchreierFor InCatalog) (h82 : LocalThetaComponentEmbeddingFrontier)
    (hS13 : Sec13Avail) (hAll : KF158AllSplit) (h4 : KF158CovAtRowFour) (h5 : KF158CovAtRowFive) :
    KF158CovAt := by
  intro G _ _ p A c L E h15 hF hout t ht K J hKt hKJ hmov hcard hJθ hS2 a ha
  have hnot5 : ∀ {A' : Subgroup G}, E = A' → ¬ Outcome152Five p E A' (lieGenerated p E) := by
    rintro A' rfl ⟨-, -, -, -, -, -, hne, -⟩
    exact hne rfl
  rcases hout with h1 | h2 | h3 | h4' | h5'
  · have hall := hAll G p A c L E h15 hF (Or.inl h1)
    have h1' := h1
    obtain ⟨f, -, -, -, ⟨σ⟩, hEA, -⟩ := h1'
    exact Or.inr (Or.inl ⟨h1, covAt_rowOne hS h82 h15 hEA σ hall ht ha⟩)
  · have hall := hAll G p A c L E h15 hF (Or.inr (Or.inl h2))
    have h2' := h2
    obtain ⟨f, -, -, -, ⟨σ⟩, hEA, -⟩ := h2'
    have hirr := (hS13 G p A c L E h15.h12 (hnot5 hEA)).irreducible
    exact Or.inl (covAt_rowB hS h82 h15 hirr hEA σ hall ht ha)
  · have hall := hAll G p A c L E h15 hF (Or.inr (Or.inr h3))
    have h3' := h3
    obtain ⟨f, -, -, -, ⟨σ⟩, hEA, -⟩ := h3'
    have hirr := (hS13 G p A c L E h15.h12 (hnot5 hEA)).irreducible
    exact Or.inl (covAt_rowB hS h82 h15 hirr hEA σ hall ht ha)
  · have h4'' := h4'
    obtain ⟨f, -, -, -, -, hEA, -⟩ := h4''
    exact h4 G p A c L E h15 hF (hS13 G p A c L E h15.h12 (hnot5 hEA)) h4' t ht K J hKt hKJ hmov
      hcard hJθ hS2 a ha
  · exact h5 G p A c L E h15 hF h5' t ht K J hKt hKJ hmov hcard hJθ hS2 a ha

end CFSG.RankThree.PartOne.S15K
