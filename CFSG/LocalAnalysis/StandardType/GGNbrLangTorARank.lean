module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARankKG
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARankBound
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRegKG
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggNbrLangTorACore_of_hyperplane {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {K : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hK : commutator ↥K = ⊤)
    {R : Type} [Group R] {I F : Set (MulAut R)} (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    {lab : LargeEvenLabel} (hinn : ∀ r : R, MulAut.conj r ∈ I)
    (hKG : KGLangAxisTorACont p lab R I F)
    (hall : ∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
      ggLAut K θ ⟨b, hN hb⟩ = u * f)
    (b₀ : G) (hb₀ : b₀ ∈ Bs) (hb₀I : ggLAut K θ ⟨b₀, hN hb₀⟩ ∉ I)
    {B₀ : Subgroup G} (hB₀ : B₀ ≤ Bs)
    (hmem : ∀ (b : G) (hb : b ∈ Bs), b ∈ B₀ ↔ ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hA₀ : p ^ 2 ≤ Nat.card {α : MulAut ↥K // α ∈ (ggBsAut hN).range ∧ kgInducedAut θ α ∈ I})
    (hsplit : GGTypeASplitPrime p lab → p ^ ((lab.rank + 1) / p + 2) ≤
      Nat.card {α : MulAut ↥K // α ∈ (ggBsAut hN).range ∧ kgInducedAut θ α ∈ I}) :
    ∃ k ∈ Subgroup.centralizer (B₀ : Set G), ∃ e ∈ B₀, e ≠ 1 ∧ k * b₀ * k⁻¹ = e * b₀ := by
  obtain ⟨k, e, he1, hep, hefix, hkfix, hke⟩ :=
    hKG ↥K θ hK (ggBsAut hN).range (ggBsAut_range_isElemAbelian hBs hN)
      (by rintro _ ⟨b, rfl⟩; exact hall b b.2) (ggBsAut hN ⟨b₀, hb₀⟩) ⟨_, rfl⟩ hb₀I hA₀ hsplit
  have hBsK : ∀ (b : ↥Bs) (k : ↥K), ggBsAut hN b k = k →
      (b : G) * (k : G) = (k : G) * (b : G) := by
    intro b k h
    have h1 : (b : G) * (k : G) * (b : G)⁻¹ = (k : G) := congrArg Subtype.val h
    calc (b : G) * (k : G) = (b : G) * (k : G) * (b : G)⁻¹ * (b : G) := by group
      _ = (k : G) * (b : G) := by rw [h1]
  have heBs : (e : G) ∈ Bs := by
    refine hSC _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_) (congrArg Subtype.val hep)
    exact hBsK ⟨b, hb⟩ e (hefix (ggBsAut hN ⟨b, hb⟩) ⟨_, rfl⟩)
  have heB₀ : (e : G) ∈ B₀ := by
    refine (hmem _ heBs).2 ?_
    have h1 : ggLAut K θ ⟨(e : G), hN heBs⟩ =
        MulAut.conj (θ ((⟨(e : G), e.2⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K)) :=
      ggLAut_of_mem_outdiag K θ e.2
    rw [h1]
    exact hinn _
  refine ⟨(k : G), ?_, (e : G), heB₀, fun h => he1 (Subtype.ext h), ?_⟩
  ·
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hBsK ⟨b, hB₀ hb⟩ k
      (hkfix (ggBsAut hN ⟨b, hB₀ hb⟩) ⟨_, rfl⟩ ((hmem b (hB₀ hb)).1 hb))
  ·
    have h1 : (k : G) * (b₀ * (k : G) * b₀⁻¹)⁻¹ = (e : G) := congrArg Subtype.val hke
    calc (k : G) * b₀ * (k : G)⁻¹ = ((k : G) * (b₀ * (k : G) * b₀⁻¹)⁻¹) * b₀ := by group
      _ = (e : G) * b₀ := by rw [h1]

theorem ggRawInnFieldOn_typeA : GGRawInnFieldOn fun lab => lab.tag = .A ∨ lab.tag = .twA :=
  (ggRawInnFieldOn_linear.or ggRawInnFieldOn_unitary).mono fun _ h =>
    h.elim (fun h => Or.inl (Or.inl h)) fun h => Or.inr (Or.inl h)

theorem ggRawPCyclicOn_typeA : GGRawPCyclicOn fun _ lab => lab.tag = .A ∨ lab.tag = .twA :=
  (ggRawPCyclicOn_linear.or ggRawPCyclicOn_unitary).mono fun _ _ h =>
    h.elim (fun h => Or.inl (Or.inl h)) fun h => Or.inr (Or.inl h)

theorem ggNbrLangAxisOn_typeARank_of_kg_of_inputs
    (hraw : GGRawInnFieldOn fun lab => lab.tag = .A ∨ lab.tag = .twA)
    (hpc : GGRawPCyclicOn fun _ lab => lab.tag = .A ∨ lab.tag = .twA)
    (hKG : KGLangAxisTorAInput) : GGNbrLangAxisOn GGNbrLangTypeARankLabel := by
  intro G _ _ p B Bs x L D J hcfg y K hK hN
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBstar : GGBstar p B Bs := hcfg.2.1
  refine NbrLangTypeA.ggMarkingAll_mono ?_
    (ggRegKG_markingAll_and (ggRegKG_markingAll_and (ggRegKG_markingAll_and
      (ggRegKG_markingAll_and (ggRegKG_markingAll_perfect_simple ↥K)
        (ggRegKG_markingAll_guard (S := fun _ lab => lab.tag = .A ∨ lab.tag = .twA)
          (P := GGRawInnField p) (p := p) (fun lab hlab hs => hraw p hp hp2 lab hlab hs) ↥K))
      (ggRegKG_markingAll_guard (S := fun _ lab => lab.tag = .A ∨ lab.tag = .twA)
        (P := GGRawPCyclic p) (p := p) (fun lab hlab hs => hpc p hp hp2 lab hlab hs) ↥K))
      (ggMarkingAll_kgLangAxisTorA hKG hp hp2 ↥K))
      (ggMarkingAll_of_labelAll_guard
        (S := fun lab => GGNbrLangTypeARankLabel p lab ∧ GGTypeASplitPrime p lab)
        (P' := fun lab R _ _ _ => ∃ r, (lab.rank + 1) / p + 3 ≤ r ∧ GGTorusLift p r R)
        fun lab hlab hs => largeEvenLabelAll_torusLift_splitTypeARank hp hp2 hlab hs.1 hs.2))
  rintro lab R _ I F θ ⟨⟨⟨⟨⟨hX, hs, hna⟩, hrawθ⟩, hpcθ⟩, hKGθ⟩, hliftθ⟩ hSl hall b₀ hb₀ hb₀I
  obtain ⟨B₀, hB₀, hcard, hb₀', hmem⟩ := exists_index_prime_of_raw_pcyclic hp hBstar.2.1 hs hna
    (hpcθ hSl.1.1) ((ggLAut K θ).comp (Subgroup.inclusion hN)) hb₀ hb₀I
  exact ⟨B₀, hB₀, hcard, hb₀', fun b hb h => (hmem b hb).2 h,
    ggNbrLangTorACore_of_hyperplane hBstar.2.1 hBstar.2.2.2 hN hX θ
      (hrawθ hSl.1.1 hs hna).2.2.1 (hKGθ hSl.1) hall b₀ hb₀ hb₀I hB₀ hmem
      (ggNbr_sq_le_card_A₀ hcfg hK hN θ hB₀ hcard hmem)
      fun hsp => ggNbr_pow_div_le_card_A₀ hcfg hK hX hN θ (hliftθ ⟨hSl, hsp⟩) hB₀ hcard hmem⟩

theorem ggNbrLangAxisOn_typeARank_of_kg
    (hKG : KGLangAxisTorAInput) :
    GGNbrLangAxisOn GGNbrLangTypeARankLabel :=
  ggNbrLangAxisOn_typeARank_of_kg_of_inputs ggRawInnFieldOn_typeA ggRawPCyclicOn_typeA hKG

@[expose] def GGNbrLangRest12NonRegNotRankLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrLangRest12NonRegLabel p lab ∧ ¬ GGNbrLangTypeARankLabel p lab

theorem ggNbrLangAxisOn_rest12NonReg_of_rank (h₁ : GGNbrLangAxisOn GGNbrLangTypeARankLabel)
    (h₂ : GGNbrLangAxisOn GGNbrLangRest12NonRegNotRankLabel) :
    GGNbrLangAxisOn GGNbrLangRest12NonRegLabel := by
  refine (h₁.or h₂).mono ?_
  intro p lab hS
  by_cases h : GGNbrLangTypeARankLabel p lab
  · exact Or.inl h
  · exact Or.inr ⟨hS, h⟩

end CFSG.StandardType
