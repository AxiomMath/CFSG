module

public import CFSG.RankThree.PartTwo.Sec21.FF81Am6LSideRoots
public import CFSG.RankThree.PartTwo.Sec21.FF81Am6Props
public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6Transv
public import CFSG.RankThree.PartTwo.Sec21.FF81Sp6LeviRed
public import CFSG.RankThree.PartTwo.Sec21.HeringFFLKE9
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.EvenBN.Tits.R2.CatalogSp6
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec13.Item135
public import CFSG.RankThree.PartTwo.Sec13.Item135Simple
public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec21.Commute33
public import CFSG.RankThree.PartTwo.Sec21.FF81Sp6LeviNorm
public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofExists
public import CFSG.RankThree.PartTwo.Sec21.Item221Proof228Statements
public import CFSG.RankThree.PartTwo.Sec21.Item221ProofZGen
public import CFSG.RankThree.PartTwo.Sec21.Item223Gaps
public import CFSG.RankThree.PartTwo.Sec21.Item228ResProofOne
public import CFSG.RankThree.PartTwo.Sec21.Item229Diagram
public import CFSG.RankThree.PartTwo.Sec21.Item233
public import CFSG.RankThree.PartTwo.Sec21.Item233OneProof
public import CFSG.RankThree.PartTwo.Sec21.Membership
public import CFSG.RankThree.PartTwo.Sec21.SylowThree
public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
public import CFSG.RankThree.PartTwo.Sec6.Item612

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Am6

open Subgroup CFSG.SeitzReduction.F4Pilot CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.RankThree.PartTwo.Sec21.FF81 (FF81Sec5 β')
open CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSide
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6 mat6_injective)
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Levi (exists_conj_torus)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

local instance am6NeZeroRankLSide : NeZero Tag.F4.rank := ⟨by decide⟩

section Core


theorem lside_core {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G}
    {b₁ b₂ b₃ t₀ s₀ : G} (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) :
    ∃ F : H6 →* G, Function.Injective F ∧ F.range = L ∧ F (zH 2) = b₁ ∧
      F (zH 0 * zH 1 ^ 2) = β' b₂ b₃ ∧ F sigH = s₀ ∧ F (zH 0 * zH 1) = b₂ * b₃ := by
  classical
  have hB := h5.basis
  have hLmodel : StatedClassicalModel L .PSp 3 2 1 := hB.hyp.model
  have hc₂ : Nat.card ↥(L ⊓ Cen b₂) = 2160 :=
    (kf_sp6Transv G L hLmodel b₁ b₂ b₃ hB.hb₁ hB.hb₂ hB.hb₃ hB.elem hB.selfcen
      hB.monoL_stab).1
  have e12 : ({b₂, b₁, b₃} : Set G) = {b₁, b₂, b₃} := Set.insert_comm _ _ _
  have e13 : ({b₁, b₃, b₂} : Set G) = {b₁, b₂, b₃} := by rw [Set.pair_comm]
  have hc₁ : Nat.card ↥(L ⊓ Cen b₁) = 2160 := by
    refine (kf_sp6Transv G L hLmodel b₂ b₁ b₃ hB.hb₂ hB.hb₁ hB.hb₃ (by rw [e12]; exact hB.elem)
      (by rw [e12]; exact hB.selfcen) ?_).1
    intro n hn hnN x hx
    rw [e12] at hnN hx
    have h := hB.monoL_stab n hn hnN x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    tauto
  have hc₃ : Nat.card ↥(L ⊓ Cen b₃) = 2160 := by
    refine (kf_sp6Transv G L hLmodel b₁ b₃ b₂ hB.hb₁ hB.hb₃ hB.hb₂ (by rw [e13]; exact hB.elem)
      (by rw [e13]; exact hB.selfcen) ?_).1
    intro n hn hnN x hx
    rw [e13] at hnN hx
    have h := hB.monoL_stab n hn hnN x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    tauto
  obtain ⟨θ⟩ := nonempty_mulEquiv_H6_of_stated hLmodel
  set f : H6 →* G := L.subtype.comp θ.symm.toMonoidHom with hfdef
  have hf : Function.Injective f := Subtype.val_injective.comp θ.symm.injective
  have hfa : ∀ y : G, ∀ hy : y ∈ L, f (θ ⟨y, hy⟩) = y := fun y hy => by simp [hfdef]
  have hfL : f.range = L := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (θ.symm x).2
    · intro hy
      exact ⟨θ ⟨y, hy⟩, hfa y hy⟩
  set c₁ := θ ⟨b₁, hB.hb₁⟩ with hc₁def
  set c₂ := θ ⟨b₂, hB.hb₂⟩ with hc₂def
  set c₃ := θ ⟨b₃, hB.hb₃⟩ with hc₃def
  have e₁ : f c₁ = b₁ := hfa _ _
  have e₂ : f c₂ = b₂ := hfa _ _
  have e₃ : f c₃ = b₃ := hfa _ _
  have hcl : (Subgroup.closure ({c₁, c₂, c₃} : Set H6)).map f =
      Subgroup.closure ({b₁, b₂, b₃} : Set G) := by
    rw [MonoidHom.map_closure]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton, e₁, e₂, e₃]
  have hBc' : Nat.card (Subgroup.closure ({c₁, c₂, c₃} : Set H6)) = 27 := by
    rw [← Subgroup.card_map_of_injective hf, hcl, hB.elem.2]
    norm_num
  have hBe : CFSG.Assembly.IsElemAbelian 3 (Subgroup.closure ({c₁, c₂, c₃} : Set H6)) := by
    have hB0 : CFSG.Open.IsElemAbelian 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)) :=
      CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hB.elem.1
    obtain ⟨hcomm, hpow⟩ := hB0
    have hmemf : ∀ x ∈ Subgroup.closure ({c₁, c₂, c₃} : Set H6),
        f x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) := fun x hx => by
      rw [← hcl]; exact Subgroup.mem_map_of_mem f hx
    refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
    · have := congrArg Subtype.val (hcomm.is_comm.comm ⟨f a, hmemf a a.2⟩ ⟨f b, hmemf b b.2⟩)
      simpa only [Subgroup.coe_mul, map_mul] using this
    · rw [map_pow, hpow _ (hmemf x hx), map_one]
  have hcen : ∀ (c : H6) (b : G), f c = b → Nat.card ↥(L ⊓ Cen b) = 2160 →
      Nat.card (Subgroup.centralizer {c}) = 2160 := by
    intro c b hcb hb
    have h := CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv.card_map_inf_cen hf (⊤ : Subgroup H6) c
    rw [show (⊤ : Subgroup H6).map f = L by rw [← hfL, MonoidHom.range_eq_map], hcb, hb,
      top_inf_eq] at h
    exact h.symm
  obtain ⟨g, p₁, p₂, p₃, a₁, a₂, a₃, h12, h23, ha₁, ha₂, ha₃, ec₁, ec₂, ec₃⟩ :=
    exists_conj_torus hBe hBc' (hcen c₁ b₁ e₁ hc₁) (hcen c₂ b₂ e₂ hc₂) (hcen c₃ b₃ e₃ hc₃)
  have h13 : p₁ ≠ p₃ := ne_of_card_closure h12 ec₁ ec₂ ec₃ hBc'
  have hs₀sq : s₀ * s₀ = 1 := by
    rw [← pow_two, ← h5.hs₀]
    exact pow_orderOf_eq_one s₀
  have hs₀b₁ : b₁ * s₀ = s₀ * b₁ :=
    Subgroup.mem_centralizer_iff.1 h5.hs₀A b₁ (Subgroup.subset_closure (by simp))
  have hs₀b₂₃ : (b₂ * b₃) * s₀ = s₀ * (b₂ * b₃) :=
    Subgroup.mem_centralizer_iff.1 h5.hs₀A (b₂ * b₃) (Subgroup.subset_closure (by simp))
  set s : H6 := θ ⟨s₀, h5.hs₀L⟩ with hsdef
  have es : f s = s₀ := hfa _ _
  obtain ⟨Φ, hΦ₁, hΦ₂, hΦ₃, hΦ₄⟩ := exists_frame_std h12 h23 h13 ha₁ ha₂ ha₃ ec₁ ec₂ ec₃
    (hf (by rw [map_mul, es, map_one]; exact hs₀sq))
    (hf (by rw [map_mul, map_mul, es, e₁]; exact hs₀b₁.symm))
    (hf (by simp only [map_mul, es, e₂, e₃]; exact hs₀b₂₃.symm))
    (hf (by
      simp only [map_mul, map_pow, map_inv, es, e₂, e₃]
      exact h5.hs₀b))
  set F : H6 →* G := f.comp (MulAut.conj Φ⁻¹).toMonoidHom with hFdef
  have key : ∀ x y : H6, Φ * x * Φ⁻¹ = y → F y = f x := by
    intro x y h
    have hx : Φ⁻¹ * y * Φ = x := by rw [← h]; group
    rw [hFdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hx]
  refine ⟨F, hf.comp (MulAut.conj Φ⁻¹).injective, ?_, (key c₁ _ hΦ₁).trans e₁, ?_,
    (key s _ hΦ₃).trans es, ?_⟩
  · rw [← hfL]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨Φ * x * Φ⁻¹, key x _ rfl⟩
  · rw [key (c₂ * c₃ ^ 2) _ hΦ₂, map_mul, map_pow, e₂, e₃]
  · rw [key (c₂ * c₃) _ hΦ₄, map_mul, e₂, e₃]

end Core

section Main


theorem lside_holds : LSide := by
  intro G _ _ b L B b₁ b₂ b₃ t₀ s₀ h5
  obtain ⟨F, hF, hFrange, hFz2, hFv, hFsig, hFu⟩ := lside_core h5
  have hclos4 : Subgroup.closure ({β' b₂ b₃, s₀} : Set G) = K4s.map F := by
    rw [K4s, MonoidHom.map_closure, Set.image_pair, hFv, hFsig]
  have hpimg0 : pimg (GaloisField 2 1) (F.comp E1.toMonoidHom) (Lv (GaloisField 2 1) {0}) =
      K4s.map F := by
    rw [pimg, ← Subgroup.map_map, map_E1_Lv_zero]
  have hpimg2 : pimg (GaloisField 2 1) (F.comp E1.toMonoidHom) (Lv (GaloisField 2 1) {2}) =
      J2s.map F := by
    rw [pimg, ← Subgroup.map_map, map_E1_Lv_two]
  have hJ2 : J2s.map F = Subgroup.closure ({b₁, F x2pH} : Set G) := by
    rw [J2s, MonoidHom.map_closure, Set.image_pair, hFz2]
  refine ⟨F.comp E1.toMonoidHom, hF.comp E1.injective, ?_, hpimg0.trans hclos4.symm,
    ⟨F x2pH, hpimg2.trans hJ2, ?_, ?_⟩, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ E1.surjective,
      ← MonoidHom.range_eq_map]
    exact hFrange
  · have h : F (x2pH * zH 2 * x2pH⁻¹) = F x2pH * b₁ * (F x2pH)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hFz2]
    rw [← h, x2p_conj_z2, map_inv, hFz2]
  · rw [← hFu, ← map_mul, ← map_mul, x2p_comm_u]
  · rw [hclos4, ← hFrange]
    exact (card_inf_cen_map F hF K4s).trans card_cen_K4s
  · rw [hclos4, hpimg2.trans rfl, ← Subgroup.map_sup, ← hFrange]
    exact (card_inf_cen_map F hF (K4s ⊔ J2s)).trans card_cen_K4s_J2s

end Main

end CFSG.RankThree.PartTwo.Sec21.FF81.Am6
