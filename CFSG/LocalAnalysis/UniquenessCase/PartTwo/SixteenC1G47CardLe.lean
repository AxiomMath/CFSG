module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Ch47Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_G47_card_le_of_V0_le (D : Data G) (hkit : OmegaKit) (h41 : R16_41 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : IntMod V hV}
    (ctx : G47Ctx D V₀ V L hV x) (hU4 : IsU4 (Bar2 L) 1) (h46 : Concl1646 L x.val)
    (hle : V₀ ≤ pCoreOf 2 (centralizer ({x.val} : Set G))) :
    Nat.card ↥V ≤ 2 * Nat.card ↥(uOne V x.val) := by
  have hS := ctx.sect
  have hc := ctx.caseOne
  have hP := hS.setting.hyp151.hyp125.pairFacts
  have hlarge := s16c1_G47_imgTil_large D hkit h41 ctx hU4 h46
  have h1 : Nat.card ↥(imgTil V₀ V hV (uOne V x.val)) * Nat.card ↥(uOne V x.val ⊓ V₀) =
      Nat.card ↥(uOne V x.val) :=
    s16c1_card_imgTil_mul (V₀ := V₀) hV (inf_le_left : uOne V x.val ≤ V)
  have h2 := s16c1_card_imgTil_mul (V₀ := V₀) hV (le_refl V)
  rw [s15_Infra_imgTil_top, Subgroup.card_top, inf_eq_right.2 hP.le] at h2
  have hW64 : Nat.card (Vtil V₀ V hV) = 64 := by
    have h := Sixteen21.card_vTil_of_case1 (V₀ := V₀) hV hc
    simpa using h
  have hUV : uOne V x.val ⊓ V₀ = V₀ := by
    ext y
    simp only [uOne, Subgroup.mem_inf]
    constructor
    · rintro ⟨_, h0⟩
      exact h0
    · intro h0
      exact ⟨⟨hP.le h0, hle h0⟩, h0⟩
  rw [hUV] at h1
  rw [hW64] at h2
  have h3 : 64 * Nat.card ↥V₀ ≤ 2 * Nat.card ↥(imgTil V₀ V hV (uOne V x.val)) * Nat.card ↥V₀ :=
    Nat.mul_le_mul_right _ hlarge
  nlinarith

theorem s16c1_G47_card_le_L3 (D : Data G) (hkit : OmegaKit) (h41 : R16_41 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : IntMod V hV}
    (hsp : IsStronglyPEmbedded 3 D.M) (hL : L ∈ calC D.M) (ctx : G47Ctx D V₀ V L hV x)
    (hU4 : IsU4 (Bar2 L) 1) (h46 : Concl1646 L x.val)
    (hL3 : IsL3Five ↥(starImg (centralizer ({x.val} : Set G)) (yGen L x.val))) :
    Nat.card ↥V ≤ 2 * Nat.card ↥(uOne V x.val) := by
  have hX := h46.2.2.1
  have hSt := G47Star.of_ctx hsp hL ctx hX
  have hVH : V ≤ centralizer ({x.val} : Set G) := s16c1_G47_le_centralizer hV x.val_mem
  have hmul : Nat.card ↥(starImg (centralizer ({x.val} : Set G)) V) *
      Nat.card ↥(uOne V x.val) = Nat.card ↥V := s16c1_G47_card_starImg_mul hVH
  have hpos : 0 < Nat.card ↥(uOne V x.val) := Nat.card_pos
  have h4 := s16c1_G47_card_V_le_four D hkit h41 ctx hU4 h46
  have hVs4 : Nat.card ↥(starImg (centralizer ({x.val} : Set G)) V) ≤ 4 :=
    Nat.le_of_mul_le_mul_right (by rw [hmul]; exact h4) hpos
  have hVX := s16c1_G47_comm_of_card_le_four hX hSt.conj_X hVs4
  have hV2 := s16c1_G47_L3_card_le_abs hSt.pCore_bot hSt.normal_Y hSt.le_XY hX hL3 hSt.split
    hSt.conj_B hSt.pgroup hSt.sq hVX
  rw [← hmul]
  exact Nat.mul_le_mul_right _ hV2

theorem r16_47_card_le_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (hkit : OmegaKit)
    (hkitB : OmegaKitB) (hkitC : OmegaKitC) (h41 : R16_41 D) (h45b : R16_45b D) :
    R16_47_card_le D := by
  intro V₀ V L hV hS hc hL hU4 x hx hch hSyl h46
  have ctx : G47Ctx D V₀ V L hV x := G47Ctx.of_l45b h45b hS hc hx
  have h3σ : 3 ∈ D.sig := by rw [hc.2.2.1]; simp
  have hsp : IsStronglyPEmbedded 3 D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) h3σ
  by_cases hle : V₀ ≤ pCoreOf 2 (centralizer ({x.val} : Set G))
  · exact s16c1_G47_card_le_of_V0_le D hkit h41 ctx hU4 h46 hle
  · rcases h46.2.2.2 with hL3 | hodd
    · exact s16c1_G47_card_le_L3 D hkit h41 hsp hL ctx hU4 h46 hL3
    · exact (s16c1_G47_false_odd D hkit hkitB hkitC h41 hsp hL ctx hU4 h46 hch hle hodd).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
