module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Half
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Trv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_G47_fixed_nontrivial {S V₀ : Subgroup G} (hS : IsPGroup 2 S)
    (hSN : S ≤ normalizer (V₀ : Set G)) (hV₀ : IsPGroup 2 V₀) (hne : V₀ ≠ ⊥) :
    ∃ a ∈ V₀, a ≠ 1 ∧ ∀ s ∈ S, s * a = a * s := by
  haveI : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
  haveI : Subgroup.Normalizes S V₀ := ⟨hSN⟩
  have hsmul : ∀ (s : ↥S) (v : ↥V₀),
      ((s • v : ↥V₀) : G) = (s : G) * (v : G) * (s : G)⁻¹ :=
    fun s v => Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe S V₀ s v
  have h2 : 2 ∣ Nat.card ↥V₀ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hV₀
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.eq_bot_of_card_eq _ (by simpa using hn))
    rw [hn]
    exact dvd_pow_self 2 hn0
  have hfix1 : (1 : ↥V₀) ∈ MulAction.fixedPoints ↥S ↥V₀ := by
    intro s
    apply Subtype.ext
    rw [hsmul]
    simp
  obtain ⟨b, hb, hb1⟩ :=
    hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := ↥V₀) h2 hfix1
  refine ⟨(b : G), b.2, fun h => hb1 (Subtype.ext h.symm), fun s hs => ?_⟩
  have hbs := congrArg Subtype.val (hb ⟨s, hs⟩)
  rw [hsmul] at hbs
  rwa [mul_inv_eq_iff_eq_mul] at hbs

theorem s16c1_G47_card_V0_le (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) {x : IntMod V hV} (hx : Setup1645 D V hV x)
    (hSyl : IsSylowIn 2 (D.T ⊓ centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G))) :
    Nat.card ↥V₀ ≤ 2 * Nat.card ↥(V₀ ⊓ pCoreOf 2 (centralizer ({x.val} : Set G))) := by
  have hP := hS.setting.hyp151.hyp125.pairFacts
  have hSM : D.T ⊓ centralizer ({x.val} : Set G) ≤ D.M := inf_le_left.trans D.sylowM.le
  have h1 := s16c1_G47_two_le_card_fixed (S := D.T ⊓ centralizer ({x.val} : Set G)) (V₀ := V₀)
    hSyl.2.1 (hSM.trans hP.le_normalizer₀) hP.elemAbelian₀.isPGroup
    (Sixteen21.card_le_four_of_hyp16 hS.setting.hyp16)
  have hC := s16c1_cent_V0_le_pCore D hS hx hSyl
  have h2 : Nat.card ↥(V₀ ⊓ centralizer ((D.T ⊓ centralizer ({x.val} : Set G) : Subgroup G) :
      Set G)) ≤ Nat.card ↥(V₀ ⊓ pCoreOf 2 (centralizer ({x.val} : Set G))) :=
    Subgroup.card_le_of_le (le_inf inf_le_left hC)
  omega

theorem s16c1_G47_card_V_le_four (D : Data G) (hkit : OmegaKit) (h41 : R16_41 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : IntMod V hV}
    (ctx : G47Ctx D V₀ V L hV x) (hU4 : IsU4 (Bar2 L) 1) (h46 : Concl1646 L x.val) :
    Nat.card ↥V ≤ 4 * Nat.card ↥(uOne V x.val) := by
  have hS := ctx.sect
  have hc := ctx.caseOne
  have hP := hS.setting.hyp151.hyp125.pairFacts
  have hlarge := s16c1_G47_imgTil_large D hkit h41 ctx hU4 h46
  have hV0 := s16c1_G47_card_V0_le D hS ctx.setup ctx.sylow
  have h1 : Nat.card ↥(imgTil V₀ V hV (uOne V x.val)) * Nat.card ↥(uOne V x.val ⊓ V₀) =
      Nat.card ↥(uOne V x.val) :=
    s16c1_card_imgTil_mul (V₀ := V₀) hV (inf_le_left : uOne V x.val ≤ V)
  have h2 := s16c1_card_imgTil_mul (V₀ := V₀) hV (le_refl V)
  rw [s15_Infra_imgTil_top, Subgroup.card_top, inf_eq_right.2 hP.le] at h2
  have hW64 : Nat.card (Vtil V₀ V hV) = 64 := by
    have h := Sixteen21.card_vTil_of_case1 (V₀ := V₀) hV hc
    simpa using h
  have hUV : uOne V x.val ⊓ V₀ = V₀ ⊓ pCoreOf 2 (centralizer ({x.val} : Set G)) := by
    ext y
    simp only [uOne, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨_, hq⟩, h0⟩
      exact ⟨h0, hq⟩
    · rintro ⟨h0, hq⟩
      exact ⟨⟨hP.le h0, hq⟩, h0⟩
  rw [hUV] at h1
  rw [hW64] at h2
  have h3 : 64 * Nat.card ↥(V₀ ⊓ pCoreOf 2 (centralizer ({x.val} : Set G))) ≤
      2 * Nat.card ↥(imgTil V₀ V hV (uOne V x.val)) *
        Nat.card ↥(V₀ ⊓ pCoreOf 2 (centralizer ({x.val} : Set G))) :=
    Nat.mul_le_mul_right _ hlarge
  nlinarith

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
