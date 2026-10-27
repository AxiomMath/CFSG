module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorJInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggNbrLangTriD4Core_of_hyperplane {G : Type} [Group G] [Finite G]
    {Bs : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    {K : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hK : commutator ↥K = ⊤)
    {R : Type} [Group R] {I F : Set (MulAut R)} (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    (hinn : ∀ r : R, MulAut.conj r ∈ I) (hKG : KGLangAxisT3Cont R I F)
    (hall : ∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
      ggLAut K θ ⟨b, hN hb⟩ = u * f)
    (b₀ : G) (hb₀ : b₀ ∈ Bs) (hb₀I : ggLAut K θ ⟨b₀, hN hb₀⟩ ∉ I)
    {B₀ : Subgroup G} (hB₀ : B₀ ≤ Bs)
    (hmem : ∀ (b : G) (hb : b ∈ Bs), b ∈ B₀ ↔ ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    {h : ↥K} (h1 : h ≠ 1) (hhBs : (h : G) ∈ Bs) (hhA : MulAut.conj h ∈ (ggBsAut hN).range)
    {J : Subgroup G} (hJK : J ≤ K)
    (hJc : IsComponentOf (J.subgroupOf K) (Subgroup.centralizer ({h} : Set ↥K)))
    {E : Type} [Field E] [Finite E]
    (θJ : ↥J ⧸ Subgroup.center ↥J ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) E))
    {At : Subgroup (GL (Fin 3) E)} (hAt : IsMulCommutative At)
    (hAtJ : ∀ b ∈ Bs, ∃ g ∈ At, ∀ j : ↥J, ∃ j' : ↥J, (j' : G) = b * (j : G) * b⁻¹ ∧
      θJ (QuotientGroup.mk j') = TableB.linConjAut (Fin 3) E g (θJ (QuotientGroup.mk j))) :
    ∃ k ∈ Subgroup.centralizer (B₀ : Set G), ∃ e ∈ B₀, e ≠ 1 ∧ k * b₀ * k⁻¹ = e * b₀ := by
  have hallA : ∀ α ∈ (ggBsAut hN).range, ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
      kgInducedAut θ α = u * f := by
    rintro _ ⟨b, rfl⟩
    exact hall b.1 b.2
  let eJ : ↥(J.subgroupOf K) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJK
  let θ₀ : ↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K) ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin 3) E) :=
    (QuotientGroup.congr (Subgroup.center ↥(J.subgroupOf K)) (Subgroup.center ↥J) eJ
      (Subgroup.map_center_eq eJ)).trans θJ
  have hAt' : ∃ At' : Subgroup (GL (Fin 3) E), IsMulCommutative At' ∧
      ∀ α ∈ (ggBsAut hN).range, ∃ g ∈ At', ∀ j : ↥(J.subgroupOf K),
        ∃ j' : ↥(J.subgroupOf K), (j' : ↥K) = α j ∧
          θ₀ (QuotientGroup.mk j') =
            TableB.linConjAut (Fin 3) E g (θ₀ (QuotientGroup.mk j)) := by
    refine ⟨At, hAt, ?_⟩
    rintro _ ⟨b, rfl⟩
    obtain ⟨g, hg, hgJ⟩ := hAtJ b.1 b.2
    refine ⟨g, hg, ?_⟩
    intro j
    obtain ⟨j'', hj''1, hj''2⟩ := hgJ (eJ j)
    refine ⟨eJ.symm j'', ?_, ?_⟩
    · apply Subtype.ext
      calc ((eJ.symm j'' : ↥(J.subgroupOf K)) : G) = (j'' : G) := rfl
        _ = b.1 * ((eJ j : ↥J) : G) * b.1⁻¹ := hj''1
        _ = b.1 * (j : G) * b.1⁻¹ := rfl
        _ = ((ggBsAut hN b j : ↥K) : G) := rfl
    · have hθj : θ₀ (QuotientGroup.mk j) = θJ (QuotientGroup.mk (eJ j)) := by
        dsimp only [θ₀]
        rw [MulEquiv.trans_apply, QuotientGroup.congr_mk]
      have hθj' : θ₀ (QuotientGroup.mk (eJ.symm j'')) = θJ (QuotientGroup.mk j'') := by
        dsimp only [θ₀]
        rw [MulEquiv.trans_apply, QuotientGroup.congr_mk]
        simp
      calc θ₀ (QuotientGroup.mk (eJ.symm j'')) = θJ (QuotientGroup.mk j'') := hθj'
        _ = TableB.linConjAut (Fin 3) E g (θJ (QuotientGroup.mk (eJ j))) := hj''2
        _ = TableB.linConjAut (Fin 3) E g (θ₀ (QuotientGroup.mk j)) := by rw [hθj]
  obtain ⟨k, hkfix, hke⟩ :=
    hKG ↥K θ hK (ggBsAut hN).range (ggBsAut_range_isElemAbelian hBs hN)
      hallA (ggBsAut hN ⟨b₀, hb₀⟩) ⟨_, rfl⟩ hb₀I h h1 hhA (J.subgroupOf K) hJc E θ₀ hAt'
  have hBsK : ∀ (b : ↥Bs) (k : ↥K), ggBsAut hN b k = k →
      (b : G) * (k : G) = (k : G) * (b : G) := by
    intro b k h
    have h1 : (b : G) * (k : G) * (b : G)⁻¹ = (k : G) := congrArg Subtype.val h
    calc (b : G) * (k : G) = (b : G) * (k : G) * (b : G)⁻¹ * (b : G) := by group
      _ = (k : G) * (b : G) := by rw [h1]
  have heB₀ : (h : G) ∈ B₀ := by
    refine (hmem _ hhBs).2 ?_
    have hconj : ggLAut K θ ⟨(h : G), hN hhBs⟩ =
        MulAut.conj (θ ((⟨(h : G), h.2⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K)) :=
      ggLAut_of_mem_outdiag K θ h.2
    rw [hconj]
    exact hinn _
  refine ⟨(k : G), ?_, (h : G), heB₀, fun hh => h1 (Subtype.ext hh), ?_⟩
  ·
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hBsK ⟨b, hB₀ hb⟩ k
      (hkfix (ggBsAut hN ⟨b, hB₀ hb⟩) ⟨_, rfl⟩ ((hmem b (hB₀ hb)).1 hb))
  ·
    have h1' : (k : G) * (b₀ * (k : G) * b₀⁻¹)⁻¹ = (h : G) := by
      have hc := congrArg Subtype.val hke
      simpa [ggBsAut, normalizerMonoidHom_coe] using hc
    calc (k : G) * b₀ * (k : G)⁻¹ =
        ((k : G) * (b₀ * (k : G) * b₀⁻¹)⁻¹) * b₀ := by group
      _ = (h : G) * b₀ := by rw [h1']

end CFSG.StandardType
