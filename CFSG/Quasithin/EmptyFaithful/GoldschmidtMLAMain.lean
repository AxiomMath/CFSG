module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLAType
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
public import CFSG.Quasithin.Background.C2A3Orbits
public import CFSG.Quasithin.EmptyFaithful.FLcL45

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.GoldMLA

variable {G : Type} [Group G] [Finite G]

theorem GoldMLA.exists_carrier_conjClosure {X S L P : Subgroup G} (hLX : L ≤ X)
    (hP : IsSylowTwoOf P L) (hPe : P = S ⊓ L) (hB : fusionIsBenderGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hcase : (∀ t ∈ S, t ∈ Subgroup.normalizer (L : Set G)) ∨
      ∃ t ∈ S, t ∉ Subgroup.normalizer (L : Set G) ∧
        conjSubgroupsBy S L = {L, conjByElt t L} ∧
        (L ⊔ pCoreOf 2 X) ⊓ (conjByElt t L ⊔ pCoreOf 2 X) = pCoreOf 2 X ∧
        (∀ a ∈ L, ∀ b ∈ conjByElt t L, a * b = b * a)) :
    ∃ K Q : Subgroup G,
      conjClosure (L ⊓ Subgroup.normalizer (P : Set G)) S = K ∧ IsCarrier K Q := by
  have hBc : IsCarrier (L ⊓ Subgroup.normalizer (P : Set G)) P := isCarrier_borel hP hB
  have hsB : ∀ s ∈ S, s ∈ Subgroup.normalizer (L : Set G) →
      s ∈ Subgroup.normalizer ((L ⊓ Subgroup.normalizer (P : Set G) : Subgroup G) : Set G) := by
    intro s hs hsL
    have hsP : s ∈ Subgroup.normalizer (P : Set G) := by
      rw [hPe]
      exact mem_normalizer_inf (Subgroup.le_normalizer hs) hsL
    exact mem_normalizer_inf hsL (Subgroup.le_normalizer hsP)
  rcases hcase with hSN | ⟨t, htS, htN, hconj, hint0, hcomm⟩
  · refine ⟨_, P, rfl, ?_⟩
    have hKB : conjClosure (L ⊓ Subgroup.normalizer (P : Set G)) S =
        L ⊓ Subgroup.normalizer (P : Set G) := by
      apply le_antisymm
      · refine conjClosure_le fun s hs b hb => ?_
        exact (Subgroup.mem_normalizer_iff.mp (hsB s hs (hSN s hs)) b).mp hb
      · exact le_conjClosure _ _
    rw [hKB]
    exact hBc
  · set B := L ⊓ Subgroup.normalizer (P : Set G) with hBdef
    have hBc' : IsCarrier (conjByElt t B) (conjByElt t P) := hBc.conj t
    have hBcomm : ∀ a ∈ B, ∀ b ∈ conjByElt t B, a * b = b * a := by
      intro a ha b hb
      refine hcomm a ha.1 b ?_
      have : conjByElt t B ≤ conjByElt t L := Subgroup.map_mono inf_le_left
      exact this hb
    have hint : B ⊓ conjByElt t B ≤ P := by
      intro x hx
      have hxL : x ∈ L := hx.1.1
      have hBL : conjByElt t B ≤ conjByElt t L := Subgroup.map_mono inf_le_left
      have hxL' : x ∈ conjByElt t L := hBL hx.2
      have h1 : x ∈ (L ⊔ pCoreOf 2 X) ⊓ (conjByElt t L ⊔ pCoreOf 2 X) :=
        ⟨Subgroup.mem_sup_left hxL, Subgroup.mem_sup_left hxL'⟩
      rw [hint0] at h1
      exact inf_pCoreOf_le hLX hP ⟨h1, hxL⟩
    have hsup := hBc.sup hBc' hBcomm hint
    refine ⟨_, _, ?_, hsup⟩
    show conjClosure B S = B ⊔ conjByElt t B
    apply le_antisymm
    · refine conjClosure_le fun s hs b hb => ?_
      have hmem : conjByElt s L ∈ conjSubgroupsBy S L := ⟨s, hs, rfl⟩
      rw [hconj] at hmem
      rcases hmem with h1 | h1
      · have hsL := mem_normalizer_of_conjByElt_eq h1
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hsB s hs hsL) b).mp hb)
      · have h1 : conjByElt s L = conjByElt t L := h1
        have hnL : t⁻¹ * s ∈ Subgroup.normalizer (L : Set G) := by
          refine mem_normalizer_of_conjByElt_eq ?_
          rw [conjByElt_mul', h1, ← conjByElt_mul', inv_mul_cancel, conjByElt_one']
        have hnS : t⁻¹ * s ∈ S := S.mul_mem (S.inv_mem htS) hs
        have hb' := (Subgroup.mem_normalizer_iff.mp (hsB _ hnS hnL) b).mp hb
        refine Subgroup.mem_sup_right ?_
        rw [mem_conjByElt]
        have e : t⁻¹ * (s * b * s⁻¹) * t = (t⁻¹ * s) * b * (t⁻¹ * s)⁻¹ := by group
        rw [e]
        exact hb'
    · refine sup_le (le_conjClosure _ _) ?_
      intro x hx
      rw [mem_conjByElt] at hx
      have := mem_conjClosure (Z := B) (H := S) htS hx
      simpa [mul_assoc] using this

theorem GoldMLA.borel_of_cComp (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L)
    (hLcomp : L ∈ cComp (g1_1516 Z₁)) (hB : fusionIsBenderGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hcomm : ∀ t ∈ s1516 T Z₁, t ∉ Subgroup.normalizer (L : Set G) →
      ∀ a ∈ L, ∀ b ∈ conjByElt t L, a * b = b * a) :
    IsBorelIn L (mZ1516 Mc Z₁ ⊓ L) := by
  have h18 := hc.h18
  have h19 := hc.h19
  have hS4 : IsSylowTwoOf (s1516 T Z₁) (g1_1516 Z₁) := h18.four
  have hSM : s1516 T Z₁ ≤ mZ1516 Mc Z₁ := s1516_le_mZ1516 h18
  have hLG : L ≤ g1_1516 Z₁ := hc.hL.mem.1
  have hP : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L := lemma_15_1_20_sylow h18.four hc.hL
  have hOG : ∀ H : Subgroup G, s1516 T Z₁ ⊓ L ≤ H → H ≤ L → H ≠ L →
      H ≤ Subgroup.normalizer ((s1516 T Z₁ ⊓ L : Subgroup G) : Set G) :=
    fun H hPH hHL hH => le_normalizer_of_overgroup hP hB hPH hHL hH
  have hN : mZ1516 Mc Z₁ ⊓ L ≤ Subgroup.normalizer ((s1516 T Z₁ ⊓ L : Subgroup G) : Set G) :=
    inf_le_normalizer hSM hP inf_le_left hOG hc.hL.not_le
  have hpc : pCoreOf 2 (mZ1516 Mc Z₁ ⊓ L) = s1516 T Z₁ ⊓ L := pCoreOf_inf_eq hSM hP inf_le_left hN
  have hsqtk : IsSQTKIn (g1_1516 Z₁) := h18.five.2.2.sqtk
  obtain ⟨horb, hcase⟩ :=
    a3Orbits_of_a37_a38 h37 h38 (g1_1516 Z₁) (s1516 T Z₁) L hsqtk hS4 hLcomp
  have hstar : ∀ m ∈ mZ1516 Mc Z₁, ∃ s ∈ s1516 T Z₁, conjByElt m L = conjByElt s L :=
    fun m hm => exists_conj_eq_of_orbits horb (mZ1516_le_g1 Mc Z₁ hm)
  have hK := normalizes_conjClosure hSM hstar
    (fun n hn hnL => (normalizer_stable hpc hn hnL).2)
  have hcase' : (∀ t ∈ s1516 T Z₁, t ∈ Subgroup.normalizer (L : Set G)) ∨
      ∃ t ∈ s1516 T Z₁, t ∉ Subgroup.normalizer (L : Set G) ∧
        conjSubgroupsBy (s1516 T Z₁) L = {L, conjByElt t L} ∧
        (L ⊔ pCoreOf 2 (g1_1516 Z₁)) ⊓ (conjByElt t L ⊔ pCoreOf 2 (g1_1516 Z₁)) =
          pCoreOf 2 (g1_1516 Z₁) ∧
        (∀ a ∈ L, ∀ b ∈ conjByElt t L, a * b = b * a) := by
    rcases hcase with h | ⟨t, ht, htN, hconj, -, hint0, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, htN, hconj, hint0, hcomm t ht htN⟩
  obtain ⟨K, Q, hKe, hKc⟩ := GoldMLA.exists_carrier_conjClosure (X := g1_1516 Z₁) (S := s1516 T Z₁)
    hLG hP rfl hB hcase'
  have hKG : K ≤ g1_1516 Z₁ := by
    rw [← hKe]
    refine conjClosure_le fun s hs b hb => ?_
    have hsG := s1516_le_g1 T Z₁ hs
    exact (g1_1516 Z₁).mul_mem ((g1_1516 Z₁).mul_mem hsG (hLG hb.1)) ((g1_1516 Z₁).inv_mem hsG)
  obtain ⟨hchar, hodd⟩ := hKc.charTwo_odd
  rw [hKe] at hK
  have hKM : K ≤ mZ1516 Mc Z₁ := h19.two K hKG hodd hK hchar
  have hBK : L ⊓ Subgroup.normalizer ((s1516 T Z₁ ⊓ L : Subgroup G) : Set G) ≤ K := by
    rw [← hKe]
    exact le_conjClosure _ _
  exact ⟨s1516 T Z₁ ⊓ L, hP, le_antisymm (fun x hx => ⟨hx.2, hN hx⟩)
    (fun x hx => ⟨hKM (hBK hx), hx.1⟩)⟩

theorem input15120MLA_holds (h37 : A37ForSQTK) (h38 : A38ForSQTK) : Input15120MLA := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hcomp hA
  have hLcomp : L ∈ cComp (g1_1516 Z₁) :=
    Id2519.mem_cComp_of_isComponentIn (DoubleA3.isComponentIn_iff_open.mpr hcomp)
  exact GoldMLA.borel_of_cComp h37 h38 hc hLcomp (fusionIsBenderGroup_quot hcomp.2.2.1 hA)
    fun t ht htN => commute_conj_of_component hcomp (s1516_le_g1 T Z₁ ht) htN

end CFSG.Quasithin
