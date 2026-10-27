module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeR1532Tens
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeR1532Fix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeR1532StarA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_row153_2 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) (h : Case153_2 D V₀ V hV L) :
    False := by
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  have hwtop : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  obtain ⟨ρ, hρs, hρk, hρe⟩ := s168e3_starnat_exists c hs
  obtain ⟨t, ht, ht2, ht1, htr, hW⟩ := c.conc
  obtain ⟨K₀, p, hKL, hshape, hdir, hsig, hrk, hrs, hrs1⟩ := h
  have hshape' := hshape
  have hr : (conjSet (barSub V₀ V hV K₀)
      (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _))).ncard = 2 := by
    have hr1 := Om8Excl.one_le_ncard_conjSet (barSub V₀ V hV K₀)
      (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _))
    rw [hs, mul_one] at hrs
    have hne : (conjSet (barSub V₀ V hV K₀)
        (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _))).ncard ≠ 1 := by
      intro h1
      have h2 := hrs1 (by rw [h1, hs, mul_one])
      have h3 := c.setting.hyp16.small
      omega
    omega
  have hK : (p = 5 ∧ UC22.IsAlt ↥(barSub V₀ V hV K₀) 5) ∨
      (p = 7 ∧ IsL3 ↥(barSub V₀ V hV K₀) 1) := by
    rcases hshape with ⟨hp, hA, -⟩ | ⟨hp, hL3, -⟩
    · exact Or.inl ⟨hp, hA⟩
    · exact Or.inr ⟨hp, hL3⟩
  have hT := s168e3_153_2_tensor hW hdir hr hK
  have hrk8 : (p = 5 ∧ rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 8) ∨
      (p = 7 ∧ rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 9) := by
    rcases hT with ⟨hp, hT'⟩ | ⟨hp, hT'⟩
    · left
      refine ⟨hp, ?_⟩
      have := s168e3_natTensor_rk hT'
      rw [show commSub ⊤ (lBar V₀ V hV L) = ⊤ from hwtop] at this
      simpa using this
    · right
      refine ⟨hp, ?_⟩
      have := s168e3_natTensor_rk hT'
      rw [show commSub ⊤ (lBar V₀ V hV L) = ⊤ from hwtop] at this
      simpa using this
  obtain ⟨x, hx, hxp⟩ : ∃ x ∈ barSub V₀ V hV K₀, orderOf x = p := by
    rcases hK with ⟨hp, hA⟩ | ⟨hp, hL3⟩
    · subst hp
      haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      have hcard : Nat.card ↥(barSub V₀ V hV K₀) = 60 := Om8Excl.card_isAlt_five hA
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 (G := ↥(barSub V₀ V hV K₀))
        (by rw [hcard]; norm_num)
      exact ⟨y.1, y.2, by rw [Subgroup.orderOf_coe y]; exact hy⟩
    · subst hp
      haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      have hcard : Nat.card ↥(barSub V₀ V hV K₀) = 168 := Om8Excl.card_isL3_one hL3
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 7 (G := ↥(barSub V₀ V hV K₀))
        (by rw [hcard]; norm_num)
      exact ⟨y.1, y.2, by rw [Subgroup.orderOf_coe y]; exact hy⟩
  have hfix := s168e3_153_2_tensor_fix hdir hr hT hK hx hxp
  obtain ⟨x₀, hx₀K, h₀, hx₀⟩ : ∃ x₀ ∈ K₀, ∃ h₀ : x₀ ∈ stabTil V₀ V,
      actTil V₀ V hV ⟨x₀, h₀⟩ = x := by
    obtain ⟨g, hgK, hgx⟩ := (mem_barSub V₀ V hV K₀ x).1 hx
    exact ⟨(g : G), hgK, g.2, hgx⟩
  have h₁ : x₀ ∈ stabTil (v1Sub D.M V₀ V hV L) V := by
    have hM : D.M ≤ normalizer (V : Set G) := c.setting.hyp16.hyp125.pairFacts.le_normalizer
    have hM₁ : D.M ≤ normalizer (v1Sub D.M V₀ V hV L : Set G) :=
      s15_Infra_le_normalizer_v1Sub c.setting.hyp16.hyp125 hV
    exact le_stabTil hM hM₁ (c.setting.hyp151.le (hKL hx₀K))
  have hρi : Function.Injective ρ := by
    rw [injective_iff_map_eq_one ρ]
    intro k hk
    have hkfix : k ∈ fixV (lBar V₀ V hV L) := by
      rw [← hρk]
      exact (MonoidHom.mem_ker).2 hk
    have hxmem : x ∈ lBar V₀ V hV L := barSub_mono V₀ V hV hKL hx
    have hkcomm : k ∈ commSub ⊤ (lBar V₀ V hV L) := by
      rw [show commSub ⊤ (lBar V₀ V hV L) = ⊤ from hwtop]
      exact Subgroup.mem_top k
    exact hfix k hkcomm ((mem_fixV.1 hkfix) x hxmem)
  have hx'K : (actTil (v1Sub D.M V₀ V hV L) V hV ⟨x₀, h₁⟩ :
      MulAut (vStar D.M V₀ V hV L)) ∈ barSub (v1Sub D.M V₀ V hV L) V hV K₀ :=
    actTil_mem_barSub (v1Sub D.M V₀ V hV L) V hV hx₀K h₁
  have hrkcount : rk ↥(commSub ⊤ (barSub (v1Sub D.M V₀ V hV L) V hV K₀)) <
      rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) := by
    rcases hshape' with ⟨hp, -, hnat⟩ | ⟨hp, -, hnat⟩
    · have hrank := s16c1610_rk_alternatingNatural_odd (by decide : Odd 5) hnat
      have htop : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 8 := by
        rcases hrk8 with ⟨-, h⟩ | ⟨hp7, -⟩
        · exact h
        · omega
      omega
    · have hrank := s16c1610_rk_binaryNaturalSL hnat
      have htop : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 9 := by
        rcases hrk8 with ⟨hp5, -⟩ | ⟨-, h⟩
        · omega
        · exact h
      omega
  have hfix' : ∀ w : Vtil V₀ V hV, (actTil V₀ V hV ⟨x₀, h₀⟩ : MulAut (Vtil V₀ V hV)) w = w →
      w = 1 := by
    intro w hw
    refine hfix w ?_ (by rw [← hx₀]; exact hw)
    rw [show commSub ⊤ (lBar V₀ V hV L) = ⊤ from hwtop]
    exact Subgroup.mem_top w
  exact s168e3_153_2_count ⟨hρi, hρs⟩ (hρe x₀ h₀ h₁) hfix' hx'K hrkcount

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
