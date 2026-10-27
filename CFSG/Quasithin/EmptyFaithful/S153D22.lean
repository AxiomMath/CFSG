module

public import CFSG.Quasithin.EmptyFaithful.S153DInputs
public import CFSG.Quasithin.EmptyFaithful.S153D16
public import CFSG.Quasithin.EmptyFaithful.S153DGen4
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary
public import CFSG.Quasithin.Background.B5NonB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.S1417
open scoped commutatorElement

namespace S153D

section Ident

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem nonempty_quot_mulEquiv_of_surjective {L : Subgroup G} {H : Type} [Group H]
    (α : ↥L →* H) (hα : Function.Surjective α) (hk : α.ker = CFSG.pCore 2 ↥L) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* H) := by
  have hN : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα)⟩

theorem nonempty_SL_two_four_equiv_alt_five
    {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* alternatingGroup (Fin 5)) := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
    rw [eq_bot_iff]
    intro A hA
    obtain ⟨r, hr, hAr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
    rw [Subgroup.mem_bot]
    have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have hr1 : r = 1 := by
      have h3 : (r - 1) ^ 2 = 0 := by linear_combination hr2 - (r - 1) * h2
      exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h3)
    rw [hr1, map_one] at hAr
    exact Subtype.ext hAr.symm
  obtain ⟨e⟩ :=
    CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K (Or.inl hK)
  let e1 : Matrix.SpecialLinearGroup (Fin 2) K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
  exact ⟨e1.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).trans e)⟩

omit [Finite G] in
theorem isLin2Quot_of_altBlockTypeWith_five {L : Subgroup G}
    {α : ↥L →* alternatingGroup (Fin 5)} (h : IsAltBlockTypeWith L 5 α) : IsLin2Quot L := by
  obtain ⟨hs, hk, -⟩ := h
  obtain ⟨e⟩ := nonempty_quot_mulEquiv_of_surjective α hs hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hcard : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨e'⟩ := nonempty_SL_two_four_equiv_alt_five (K := GaloisField 2 2) hcard
  refine ⟨2, GaloisField 2 2, inferInstance, inferInstance, by norm_num, ?_, ⟨e.trans e'.symm⟩⟩
  rw [← Nat.card_eq_fintype_card, hcard]
  norm_num

omit [Finite G] in
theorem isLnTwoQuot_four_of_altBlockTypeWith_eight {L : Subgroup G}
    {α : ↥L →* alternatingGroup (Fin 8)} (h : IsAltBlockTypeWith L 8 α) : IsLnTwoQuot L 4 := by
  obtain ⟨hs, hk, -⟩ := h
  obtain ⟨e⟩ := nonempty_quot_mulEquiv_of_surjective α hs hk
  exact ⟨e.trans (CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.trans
    ((CFSG.QuasithinUnique.Setup.Family.slEquivGL 4).symm.trans
      (specialLinearGroupEquivStatedSL 4 (ZMod 2))))⟩

omit [Finite G] in
theorem isSp4Quot_of_isSp4Block {L : Subgroup G} (h : IsSp4Block L) : IsSp4Quot L := by
  obtain ⟨-, F, hF, hFin, hcard, α, hs, hk, -⟩ := h
  obtain ⟨e⟩ := nonempty_quot_mulEquiv_of_surjective α hs hk
  exact ⟨F, hF, hFin, hcard, ⟨e⟩⟩

theorem nonempty_statedSL_equiv_zmod_two {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) (n : ℕ) :
    Nonempty (↥(CFSG.Assembly.LowTwoRank.StatedSL n F) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2))) := by
  have e : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by rw [hF, ZMod.card])
  exact ⟨(specialLinearGroupEquivStatedSL n F).symm.trans
    ((CFSG.ClassicalModels.specialLinearFieldEquiv e (Fin n)).trans
      (specialLinearGroupEquivStatedSL n (ZMod 2)))⟩

end Ident

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem VZ_le_VL153 (h : Hyp15310 G T Mc M V₁ V₂ Yp t) (c : Ctx15313 T Mc M V₁ V₂ Yp I t)
    (hF : Facts15311 T M V₁ Yp I) (hL : L ∈ cComp I)
    (hO : pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ R153 T V₁ Yp) : VZ T M ≤ VL153 T V₁ Yp L :=
  fun v hv => Subgroup.subset_closure ⟨VZ_le_centerOf h c hF hL hO hv, h.hyp.elemAbelian.2 v hv⟩

theorem lemma_15_3_22
    (hcover : AsA36NoOddCover) (c : Ctx15316 T Mc M V₁ V₂ Yp I L t)
    (n18 : ¬ IsLin2Block I L) (n19 : ¬ IsLin2Quot L) (n20 : ¬ IsSL3Quot L ∧ ¬ IsSp4Quot L)
    (n21 : ¬ IsAltBlockType L 6 ∧ ¬ IsG2Block L ∧ ¬ IsHatA6Block L ∧ ¬ IsAltBlockType L 7 ∧
      ¬ IsExcA7Block L) :
    IsLnTwoQuot L 3 ∨ IsLnTwoQuot L 4 ∨ IsLnTwoQuot L 5 := by
  obtain ⟨hLc, hLn, hL3, -, -, hLq⟩ := c.conc
  have hLI : L ∈ cComp I := mem_cComp_of_mem_cComp_thompsonJ hLc
  have hRL := c.c16.R_norm
  have hO := pCoreOf_sup_R153_le c.facts hLI hLq hRL
  obtain ⟨⟨h1a, -, h1c⟩, -, h3⟩ := c.c16.desc
  have hLN : L ≤ Subgroup.normalizer (VL153 T V₁ Yp L : Set G) := le_sup_left.trans h1c.2.1
  have hker : pCoreOf 2 L ≤ Subgroup.centralizer (VL153 T V₁ Yp L : Set G) :=
    (pCoreOf_le_pCoreOf_sup hRL).trans fun x hx => (h1a hx).2
  have hnt : ¬ L ≤ Subgroup.centralizer (VL153 T V₁ Yp L : Set G) := fun hc =>
    not_le_centralizer_VZ c.ctx.hyp (le_of_mem_cComp hLI) hLn
      (hc.trans (Subgroup.centralizer_le (VZ_le_VL153 c.ctx.hyp c.ctx c.facts hLI hO)))
  have hsqI : SQTKGroup ↥I :=
    (lemma_15_3_15_one c.ctx.hyp c.ctx.inH c.facts).sqtk
  have hsq : SQTKGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
    sqtkGroup_quot_pCore (B5.sqtk_of_le hsqI (le_of_mem_cComp hLI))
  have bridge : IsL345Type ↥(autOn L (VL153 T V₁ Yp L)) →
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(autOn L (VL153 T V₁ Yp L))) := fun hH =>
    nonempty_quot_mulEquiv_autOn hcover hLN hLq hsq hker hnt hH
  rcases h3 with ⟨hchi, ⟨hi, -, -⟩ | ⟨hA5, -, -, -⟩ | ⟨hA7, -, -⟩ | ⟨hA7', -, -⟩⟩ |
      ⟨⟨n, α, h5, h8, hshort, hα, -⟩, -⟩ | ⟨hHat, -, -⟩ | ⟨hExc, -⟩ | ⟨hA6 | hSp4, -⟩ |
      ⟨hG2, -, -⟩ | ⟨⟨n, F, hF, hFin, hn1, hcard, ⟨e⟩⟩, -, -⟩ | ⟨hh | hh, -, -⟩
  ·
    obtain ⟨hblock, -⟩ := hchi
    obtain ⟨n, hn1, hnL⟩ := hi
    exact absurd ⟨hblock, n, hn1, hnL⟩ n18
  ·
    obtain ⟨α, hα⟩ := (isAltType_iff_exists_isAltBlockTypeWith (by decide : Odd 5)).mp hA5
    exact absurd (isLin2Quot_of_altBlockTypeWith_five hα) n19
  ·
    obtain ⟨⟨hshort, -, -⟩, -⟩ := hchi
    exact absurd ⟨hshort, (isAltType_iff_exists_isAltBlockTypeWith (by decide : Odd 7)).mp hA7⟩
      n21.2.2.2.1
  ·
    obtain ⟨⟨hshort, -, -⟩, -⟩ := hchi
    exact absurd ⟨hshort, (isAltType_iff_exists_isAltBlockTypeWith (by decide : Odd 7)).mp hA7'⟩
      n21.2.2.2.1
  ·
    interval_cases n
    · exact absurd (isLin2Quot_of_altBlockTypeWith_five hα) n19
    · exact absurd ⟨hshort, α, hα⟩ n21.1
    · exact absurd ⟨hshort, α, hα⟩ n21.2.2.2.1
    · exact Or.inr (Or.inl (isLnTwoQuot_four_of_altBlockTypeWith_eight hα))
  · exact absurd hHat n21.2.2.1
  · exact absurd hExc n21.2.2.2.2
  · exact absurd hA6 n21.1
  · exact absurd (isSp4Quot_of_isSp4Block hSp4) n20.2
  · exact absurd hG2 n21.2.1
  ·
    have hH : IsL345Type ↥(autOn L (VL153 T V₁ Yp L)) :=
      Or.inl ⟨n, F, hF, Finite.of_fintype F, by rw [Nat.card_eq_fintype_card]; exact hcard, ⟨e⟩⟩
    obtain ⟨e'⟩ := bridge hH
    by_cases hn : 1 < n
    · exact absurd ⟨n, F, hF, hFin, hn, hcard, ⟨e'.trans e⟩⟩ n20.1
    · have hn1' : n = 1 := by omega
      subst hn1'
      obtain ⟨e''⟩ := nonempty_statedSL_equiv_zmod_two (F := F) (by simpa using hcard) 3
      exact Or.inl ⟨(e'.trans e).trans e''⟩
  ·
    have hH : IsL345Type ↥(autOn L (VL153 T V₁ Yp L)) :=
      Or.inr (Or.inl ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2, hh⟩)
    obtain ⟨e'⟩ := bridge hH
    obtain ⟨e⟩ := hh
    exact Or.inr (Or.inl ⟨e'.trans e⟩)
  ·
    have hH : IsL345Type ↥(autOn L (VL153 T V₁ Yp L)) :=
      Or.inr (Or.inr ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2, hh⟩)
    obtain ⟨e'⟩ := bridge hH
    obtain ⟨e⟩ := hh
    exact Or.inr (Or.inr ⟨e'.trans e⟩)

end Main

end S153D

end CFSG.Quasithin
