module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bar13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Layer13
public import CFSG.RankThree.PartTwo.Sec11.Item116R1CensusPure
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.LocalAnalysis.UniquenessCase.UCKPOut
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.RankThree.PartTwo.Sec11.Item116E2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F13

variable {G : Type} [Group G] [Finite G]

theorem s13_le_of_mem_calC {M L : Subgroup G} (hL : L ∈ calC M) : L ≤ M :=
  CFSG.Quasithin.A3.subnormal_le hL.1

theorem s13_barImage_isComponent {M L : Subgroup G} (hL : L ∈ calC M) :
    CFSG.IsComponent (barImage M L) :=
  uc22p22l_barImage_isComponent hL

theorem s13_exists_calC_of_component (M : Subgroup G) {C : Subgroup (Bar2 M)}
    (hC : CFSG.IsComponent C) : ∃ L ∈ calC M, barImage M L = C :=
  uc22p21c_exists_calC_of_component M hC

theorem s13_bar_equiv {M L : Subgroup G} (hL : L ∈ calC M) :
    Nonempty (Bar2 L ≃* ↥(barImage M L)) := by
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL
  exact ⟨e⟩

theorem s13_barImage_normal {M L : Subgroup G} (hL : (L.subgroupOf M).Normal) :
    (barImage M L).Normal :=
  hL.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) (QuotientGroup.mk'_surjective _)

theorem s13_isKGroup_bar (D : Data G) {L : Subgroup G} (hL : L ≤ D.M) :
    CFSG.IsKGroup (Bar2 L) := by
  have hM : CFSG.Open.IsKGroup ↥D.M :=
    D.standing.kProper.isKGroup D.M (uc22br4_M_ne_top D)
  have hLk : CFSG.Open.IsKGroup ↥L := hM.of_le hL
  exact uc22br4_isKGroup_catalog_of_open (hLk.quotient (CFSG.pCore 2 ↥L))

theorem s13_isKGroup_bar_M (D : Data G) : CFSG.IsKGroup (Bar2 D.M) := by
  have hM : CFSG.Open.IsKGroup ↥D.M :=
    D.standing.kProper.isKGroup D.M (uc22br4_M_ne_top D)
  exact uc22br4_isKGroup_catalog_of_open (hM.quotient (CFSG.pCore 2 ↥D.M))

theorem s13_pCore_bar_eq_bot (L : Subgroup G) : CFSG.pCore 2 (Bar2 L) = ⊥ :=
  CFSG.RankThree.PartTwo.Sec11.pCore_quotient_pCore ↥L 2

theorem s13_pRank_bar_le_one {L : Subgroup G} (hL : Thin13 L) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) : CFSG.pRank r (Bar2 L) ≤ 1 := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top r (Bar2 L), s13_pRank_bar_top hr hr2 L]
  exact hL r hr hr2

theorem s13_nonabelian_bar {M L : Subgroup G} (hL : L ∈ calC M) :
    ∃ x y : Bar2 L, x * y ≠ y * x := by
  by_contra h
  push_neg at h
  have htop : Subgroup.center (Bar2 L) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact h y x
  haveI : Subsingleton (Bar2 L ⧸ Subgroup.center (Bar2 L)) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  haveI : Nontrivial (Bar2 L ⧸ Subgroup.center (Bar2 L)) := hL.2.2.2.toNontrivial
  obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial (Bar2 L ⧸ Subgroup.center (Bar2 L)))
  exact hab (Subsingleton.elim a b)

theorem s13_list_bar (hThin : ThinList13) (D : Data G) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hthin : Thin13 L) :
    IsSimpleGroup (Bar2 L) ∧
      ((∃ a : ℕ, IsL2 (Bar2 L) a) ∨ (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsL2Odd (Bar2 L) p) ∨
        (∃ a : ℕ, IsSz (Bar2 L) a) ∨ IsJ1 (Bar2 L)) :=
  hThin (Bar2 L) (s13_isKGroup_bar D (s13_le_of_mem_calC hL)) hL.2.2
    (s13_pCore_bar_eq_bot L) (fun r hr hr2 => s13_pRank_bar_le_one hthin hr hr2)

theorem s13_isSimple_bar (hThin : ThinList13) (D : Data G) (hS : Setting13 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) : IsSimpleGroup (Bar2 L) := by
  rcases hS.hyp131.thinOrU3 L hL with hthin | ⟨n, -, hU⟩
  · exact (s13_list_bar hThin D hL hthin).1
  · exact s13_isSimple_of_isU3 hU

theorem s13_Bridge13_isCyclic_of_pRank_le_one {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hΓ : IsPGroup p Γ) (h : CFSG.pRank p Γ ≤ 1) :
    IsCyclic Γ := by
  by_contra hnc
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have : Fact (IsPGroup p Γ) := ⟨hΓ⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hnc
  have hE : CFSG.Open.IsElemAbelian p S :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p S).mp hSel
  have h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup Γ) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top hE hScard
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top p Γ] at h2
  omega

theorem s13_outAbelian_bar (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (D : Data G)
    (hS : Setting13 D) {L : Subgroup G} (hL : L ∈ calC D.M) :
    ∀ σ τ : MulAut (Bar2 L), ∃ y : Bar2 L, σ * τ * σ⁻¹ * τ⁻¹ = MulAut.conj y := by
  rcases hS.hyp131.thinOrU3 L hL with hthin | ⟨n, ⟨k, hk⟩, hU⟩
  · have hK : CFSG.IsKGroup (Bar2 L) := s13_isKGroup_bar D (s13_le_of_mem_calC hL)
    have hsimple : IsSimpleGroup (Bar2 L) := (s13_list_bar hThin D hL hthin).1
    have hnonab : ∃ x y : Bar2 L, x * y ≠ y * x := s13_nonabelian_bar hL
    have hsyl : ∀ P : Sylow 3 (Bar2 L), IsCyclic ↥(P : Subgroup (Bar2 L)) := by
      intro P
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      refine s13_Bridge13_isCyclic_of_pRank_le_one Nat.prime_three (by norm_num)
        P.isPGroup' ?_
      calc CFSG.pRank 3 ↥(P : Subgroup (Bar2 L))
          = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(P : Subgroup (Bar2 L))) :=
            CFSG.SectionRank.pRank_eq_open_pRank_top 3 _
        _ ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) :=
            CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) (Subgroup.subtype _)
              (Subgroup.subtype_injective _)
        _ = CFSG.pRank 3 (Bar2 L) :=
            (CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Bar2 L)).symm
        _ ≤ 1 := s13_pRank_bar_le_one hthin Nat.prime_three (by norm_num)
    intro σ τ
    obtain ⟨y, hy⟩ := hCyc (Bar2 L) hK hsimple hnonab hsyl σ τ
    exact ⟨y, hy.symm⟩
  · have hSU : IsSU3 (Bar2 L) n := uc22p22d_isSU3_of_isU3 hL.2.2 hU
    obtain ⟨N, hNn, hInn, hcyc, -, hev⟩ := UCK.u3OutShape (Bar2 L) n hSU
    have htwo : 2 ≤ n := s13_two_le_of_isU3 hU
    have hkne : k ≠ 0 := by
      intro hk0
      rw [hk0, pow_zero] at hk
      omega
    have heven : Even n := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkne
      rw [hk, pow_succ, mul_comm]
      exact even_two_mul _
    haveI : N.Normal := hNn
    haveI : IsCyclic (MulAut (Bar2 L) ⧸ N) := hcyc
    have hNle : N ≤ (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range := hev heven
    have hNeq : N = (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).range :=
      le_antisymm hNle hInn
    intro σ τ
    have hmem : σ * τ * σ⁻¹ * τ⁻¹ ∈ N := by
      rw [← QuotientGroup.eq_one_iff (N := N)]
      rw [← QuotientGroup.mk'_apply]
      rw [← commutatorElement_def, map_commutatorElement]
      have hcomm : (QuotientGroup.mk' N) σ * (QuotientGroup.mk' N) τ =
          (QuotientGroup.mk' N) τ * (QuotientGroup.mk' N) σ :=
        isMulCommutative_iff.mp (inferInstance : IsMulCommutative (MulAut (Bar2 L) ⧸ N)) _ _
      exact commutatorElement_eq_one_iff_mul_comm.2 hcomm
    rw [hNeq] at hmem
    obtain ⟨y, hy⟩ := hmem
    exact ⟨y, hy.symm⟩

theorem s13_outAbelian_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : ∀ σ τ : MulAut A, ∃ y : A, σ * τ * σ⁻¹ * τ⁻¹ = MulAut.conj y) :
    ∀ σ τ : MulAut B, ∃ y : B, σ * τ * σ⁻¹ * τ⁻¹ = MulAut.conj y := by
  intro σ τ
  obtain ⟨y, hy⟩ := h ((MulAut.congr e).symm σ) ((MulAut.congr e).symm τ)
  refine ⟨e y, ?_⟩
  have h1 := congrArg (MulAut.congr e) hy
  simp only [map_mul, map_inv] at h1
  rw [CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj] at h1
  simpa only [MulEquiv.apply_symm_apply] using h1

theorem s13_outAbelian_barImage (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) (D : Data G)
    (hS : Setting13 D) {L : Subgroup G} (hL : L ∈ calC D.M) :
    ∀ σ τ : MulAut ↥(barImage D.M L), ∃ y : ↥(barImage D.M L),
      σ * τ * σ⁻¹ * τ⁻¹ = MulAut.conj y := by
  obtain ⟨e⟩ := s13_bar_equiv hL
  exact s13_outAbelian_of_mulEquiv e (s13_outAbelian_bar hThin hCyc D hS hL)

theorem s13_isSimple_barImage (hThin : ThinList13) (D : Data G) (hS : Setting13 D)
    {L : Subgroup G} (hL : L ∈ calC D.M) : IsSimpleGroup ↥(barImage D.M L) := by
  haveI := s13_isSimple_bar hThin D hS hL
  obtain ⟨e⟩ := s13_bar_equiv hL
  exact MulEquiv.isSimpleGroup e.symm

theorem s13_normalSimple (hThin : ThinList13) (D : Data G) (hS : Setting13 D) :
    s13_NormalSimple (Bar2 D.M) := by
  intro J hJ
  obtain ⟨L, hL, hbar⟩ := s13_exists_calC_of_component D.M hJ
  subst hbar
  exact ⟨s13_barImage_normal (hS.hyp131.normal L hL), s13_isSimple_barImage hThin D hS hL⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
