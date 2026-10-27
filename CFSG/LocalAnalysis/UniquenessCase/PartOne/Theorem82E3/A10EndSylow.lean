module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndAction
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
import CFSG.LocalAnalysis.UniquenessCase.UC6A10Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D} (F : A10Frame c)

theorem normalizer_P_le_normalizer_A :
    Subgroup.normalizer (F.P : Set G) ≤ Subgroup.normalizer (F.A : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  have hle : F.A.map (MulAut.conj g).toMonoidHom ≤ F.P := by
    calc F.A.map (MulAut.conj g).toMonoidHom ≤ F.P.map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono F.A_le
      _ = F.P := hg
  exact F.unique _ hle (F.elemAbelian.map _)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, F.card_A])

theorem isSylowOf_top (hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M) :
    CFSG.ABGLocalTools.IsSylowOf 3 F.P ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hT : CFSG.ABGLocalTools.IsSylowOf 3 F.P (D.M ⊓ ⊤) := by simpa using F.sylow
  have hN : Subgroup.normalizer (F.P : Set G) ⊓ ⊤ ≤ D.M :=
    (inf_le_left.trans (normalizer_P_le_normalizer_A F)).trans hNA
  exact CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le hT hN

theorem exists_mem_normalizer_le_map_conj (hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M)
    {Q : Subgroup G} (hQ : IsPGroup 3 Q) (hAQ : F.A ≤ Q) :
    ∃ g ∈ Subgroup.normalizer (F.A : Set G), Q ≤ F.P.map (MulAut.conj g).toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨S, hQS⟩ := hQ.exists_le_sylow
  have hStop : CFSG.ABGLocalTools.IsSylowOf 3 (S : Subgroup G) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, S.isPGroup', by simpa only [Subgroup.relIndex_top_right] using S.not_dvd_index⟩
  obtain ⟨k, -, hk⟩ := (isSylowOf_top F hNA).exists_mem_conj hStop
  have hAle : F.A.map (MulAut.conj k⁻¹).toMonoidHom ≤ F.P := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have haS : a ∈ (S : Subgroup G) := hQS (hAQ ha)
    have hconj : k⁻¹ * a * k ∈ F.P := (hk a).mp haS
    show (MulAut.conj k⁻¹) a ∈ F.P
    rw [MulAut.conj_apply, inv_inv]
    exact hconj
  have hAeq : F.A.map (MulAut.conj k⁻¹).toMonoidHom = F.A :=
    F.unique _ hAle (F.elemAbelian.map _)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, F.card_A])
  have hk' : k⁻¹ ∈ Subgroup.normalizer (F.A : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hAeq
  have hkA : k ∈ Subgroup.normalizer (F.A : Set G) := by
    simpa using (Subgroup.normalizer (F.A : Set G)).inv_mem hk'
  refine ⟨k, hkA, ?_⟩
  intro x hx
  refine Subgroup.mem_map.mpr ⟨k⁻¹ * x * k, (hk x).mp (hQS hx), ?_⟩
  change (MulAut.conj k) (k⁻¹ * x * k) = x
  rw [MulAut.conj_apply]
  group

theorem le_M_of_isPGroup (hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M)
    {Q : Subgroup G} (hQ : IsPGroup 3 Q) (hAQ : F.A ≤ Q) : Q ≤ D.M := by
  obtain ⟨g, hgN, hgQ⟩ := exists_mem_normalizer_le_map_conj F hNA hQ hAQ
  have hgM : g ∈ D.M := hNA hgN
  have hPM : F.P ≤ D.M := F.P_le_L.trans c.hyp81.1
  intro x hx
  obtain ⟨y, hyP, hyx⟩ := Subgroup.mem_map.mp (hgQ hx)
  have hxgy : x = g * y * g⁻¹ := by
    rw [← hyx]
    change (MulAut.conj g) y = g * y * g⁻¹
    rw [MulAut.conj_apply]
  rw [hxgy]
  exact D.M.mul_mem (D.M.mul_mem hgM (hPM hyP)) (D.M.inv_mem hgM)

theorem center_eq_bot (F : A10Frame c) : Subgroup.center c.Lbar = ⊥ :=
  CFSG.LocalAnalysis.UniquenessCase.UCK.kMult_A10 c.Lbar (c.isQuasisimple_lbar F.qs)
    (Subgroup.center c.Lbar) le_rfl ⟨F.iso⟩ (c.odd_card_center_lbar)

theorem a10Hom_eq_one_iff {x : G} (hx : x ∈ c.L) :
    c.a10Hom F.iso ⟨x, c.hyp81.1 hx⟩ = 1 ↔
      x ∈ (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype := by
  classical
  rw [c.a10Hom_apply_of_mem_L F.iso (c.hyp81.1 hx) hx]
  constructor
  · intro h
    have h1 : F.iso (QuotientGroup.mk (QuotientGroup.mk (⟨x, hx⟩ : ↥c.L) : c.Lbar)) = 1 := by
      apply Subtype.ext
      simpa using h
    have h2 : QuotientGroup.mk (QuotientGroup.mk (⟨x, hx⟩ : ↥c.L) : c.Lbar) = 1 :=
      F.iso.injective (by rw [h1, map_one])
    have h3 : (QuotientGroup.mk (⟨x, hx⟩ : ↥c.L) : c.Lbar) ∈ Subgroup.center c.Lbar :=
      (QuotientGroup.eq_one_iff _).mp h2
    rw [center_eq_bot F] at h3
    have h4 : (⟨x, hx⟩ : ↥c.L) ∈ CFSG.Open.pCore 2 ↥c.L :=
      (QuotientGroup.eq_one_iff _).mp (Subgroup.mem_bot.mp h3)
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, h4, rfl⟩
  · intro hxO2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxO2
    have h4 : (⟨x, hx⟩ : ↥c.L) ∈ CFSG.Open.pCore 2 ↥c.L := by
      rw [show (⟨x, hx⟩ : ↥c.L) = y from Subtype.ext hyx.symm]
      exact hy
    have hq : (QuotientGroup.mk (⟨x, hx⟩ : ↥c.L) : c.Lbar) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr h4
    have hq' : (QuotientGroup.mk (QuotientGroup.mk (⟨x, hx⟩ : ↥c.L) : c.Lbar) :
        c.Lbar ⧸ Subgroup.center c.Lbar) = 1 := by
      rw [hq]
      exact QuotientGroup.mk_one _
    rw [hq', map_one]
    rfl

theorem three_le_pRank_five (F : A10Frame c) : 3 ≤ CFSG.Open.pRank 5 D.M :=
  c.three_le 5 (by rw [F.sig]; simp)

theorem normalizer_le_of_isPGroup_five (F : A10Frame c) {R : Subgroup G}
    (hR : IsPGroup 5 R) (hR1 : R ≠ ⊥) (hRM : R ≤ D.M) :
    Subgroup.normalizer (R : Set G) ≤ D.M := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact CFSG.RankThree.PartOne.IsStronglyPEmbedded.normalizer_le
    (c.isStronglyPEmbedded_of_mem_sigma (by rw [F.sig]; simp)) hR1 hR hRM

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
