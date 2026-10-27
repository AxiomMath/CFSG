module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenLargeClassicalComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenLargeAlternatingComponent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalTensorAssembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeK168Tensor
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeFStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeSmallSigma
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenL3TensorPointFixer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeKernel
public import CFSG.Quasithin.EmptyFaithful.S153G93DL32

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_irrSet_seven_of_sum_three
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1) :
    Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7 := by
  have hbound : ∃ n : ℕ,
      (IsSLn ↥(lBar V₀ V hV L) n 1 ∧ n < 8) ∨
      (IsSpn ↥(lBar V₀ V hV L) n 1 ∧ n < 8) ∨
      (IsOmegaPlus ↥(lBar V₀ V hV L) n 1 ∧ n < 8) ∨
      (IsOmegaMinus ↥(lBar V₀ V hV L) n 1 ∧ n < 10) ∨
      (UC22.IsAlt ↥(lBar V₀ V hV L) n ∧ n < 12) := by
    obtain ⟨n, hSL | hSp | hOmegaPlus | hOmegaMinus | hAlt⟩ := hsum
    · obtain ⟨hSLn, -⟩ := hSL
      refine ⟨n, Or.inl ⟨hSLn, ?_⟩⟩
      by_contra h
      exact s168e3_false_of_sl_component_ge_eight c hcomp (by omega) hSLn
    · obtain ⟨hSpn, -⟩ := hSp
      refine ⟨n, Or.inr (Or.inl ⟨hSpn, ?_⟩)⟩
      by_contra h
      exact s168e3_false_of_sp_component_ge_eight c hcomp (by omega) hSpn
    · obtain ⟨hOmegaPlusn, -⟩ := hOmegaPlus
      refine ⟨n, Or.inr (Or.inr (Or.inl ⟨hOmegaPlusn, ?_⟩))⟩
      by_contra h
      exact s168e3_false_of_omegaPlus_component_ge_eight c hcomp (by omega) hOmegaPlusn
    · obtain ⟨hOmegaMinusn, -⟩ := hOmegaMinus
      refine ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ⟨hOmegaMinusn, ?_⟩)))⟩
      by_contra h
      exact s168e3_false_of_omegaMinus_component_ge_ten c hcomp (by omega) hOmegaMinusn
    · obtain ⟨hAltn, -⟩ := hAlt
      refine ⟨n, Or.inr (Or.inr (Or.inr (Or.inr ⟨hAltn, ?_⟩)))⟩
      by_contra h
      exact s168e3_false_of_alternating_component_ge_twelve c hcomp (by omega) hAltn
  exact s168e3_irrSet_seven_of_bounded c hcomp hsum htrans hs hbound

theorem s168e3_tensorNatL32_of_sum_three_l3_kBar_168
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1)
    (hL3 : IsL3 ↥(lBar V₀ V hV L) 1)
    (hK168 : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168) :
    TensorNatL32 (Mbar D.M V₀ V hV) := by
  have hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T) :=
    s168e3_threeNat_of_s15_eq_one c hcomp hsum htrans hs
  have h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7 :=
    s168e3_irrSet_seven_of_sum_three c hcomp hsum htrans hs
  have hU : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hZ : wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L) = ⊥ :=
    s168e3_threeNatSeven_l3_fixV_eq_bot c hcomp hsum htrans hs h7 hL3
  have hfix : fixV (lBar V₀ V hV L) = ⊥ := by
    rw [hU, top_inf_eq] at hZ
    exact hZ
  exact s168e3_tensorNatL32_of_threeNat_kBar_168 hT h7 hL3 hfix hK168

theorem s168e3_sig_eq_seven_of_sum_three_l3_kBar_168
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1)
    (hL3 : IsL3 ↥(lBar V₀ V hV L) 1)
    (hK168 : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168) :
    D.sig = {7} := by
  classical
  let A := Mbar D.M V₀ V hV
  let B := lBar V₀ V hV L
  let K := s1t3KBar A B
  have hT : ThreeNat A B (barSub V₀ V hV D.T) :=
    s168e3_threeNat_of_s15_eq_one c hcomp hsum htrans hs
  have h7 : Nat.card ↥(irrSet B) = 7 :=
    s168e3_irrSet_seven_of_sum_three c hcomp hsum htrans hs
  have hT2 : TensorNatL32 A :=
    s168e3_tensorNatL32_of_sum_three_l3_kBar_168 c hcomp hsum htrans hs hL3 hK168
  have hreal : (CFSG.Quasithin.H13.tensorPairModel CFSG.Quasithin.H.L3Wr.SL32
      CFSG.Quasithin.H.L3Wr.SL32).RealizesMod A :=
    CFSG.Quasithin.S153G93D.L32.tensorNatL32_realizesMod hT2
  have hfixA : ∀ x : Vtil V₀ V hV, x ≠ 1 →
      ∃ b ∈ A, orderOf b = 3 ∧ b x = x :=
    tensorPair_exists_order_three_fix hreal
  have hprod : B ⊔ K = A := hT.sup_kBar_eq_of_isL3 h7 hL3
  obtain ⟨N, -, hBN, -, -, hNK, -⟩ := hT.structure_of_seven h7
  have hBK : B ⊓ K = ⊥ := by
    refine le_antisymm ?_ bot_le
    calc
      B ⊓ K ≤ N ⊓ K := inf_le_inf_right K hBN
      _ = ⊥ := hNK
  have hKnorm : K ≤ Subgroup.normalizer (B : Set (MulAut (Vtil V₀ V hV))) := by
    intro k hk
    exact Subgroup.centralizer_le_normalizer (B : Set (MulAut (Vtil V₀ V hV)))
      (Subgroup.mem_inf.mp hk).2
  have hdisj : Disjoint B K := disjoint_iff.2 hBK
  have hcardA : Nat.card ↥A = 168 ^ 2 := by
    rw [← hprod,
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer B K hKnorm hdisj,
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.card_eq_of_isL3 hL3, hK168, pow_two]
  have hcardA' : Nat.card ↥A = 2 ^ 6 * 3 ^ 2 * 7 ^ 2 := by
    rw [hcardA]
    norm_num
  have hcube : ¬ 3 ^ 3 ∣ Nat.card ↥A := by
    rw [hcardA']
    norm_num
  have h3not : 3 ∉ D.sig := by
    intro h3
    exact s168e3_false_of_kernel c Nat.prime_three h3
      (s168e3_kernel_of_cube Nat.prime_three A hcube hfixA)
  have key : ∀ q ∈ D.sig, q = 7 := by
    intro q hq
    obtain ⟨hqp, hq2⟩ := D.sig_prime q hq
    have h2rank : 1 ≤ CFSG.Open.pRank q A :=
      le_trans (by norm_num : 1 ≤ 2) (c.two_le_pRank_mbar hq)
    have hqdvd : q ∣ Nat.card ↥A :=
      CFSG.GroupTheory.dvd_card_of_one_le_pRank hqp h2rank
    rw [hcardA'] at hqdvd
    have hq3 : q ≠ 3 := fun h => h3not (h ▸ hq)
    rcases (Nat.Prime.dvd_mul hqp).1 hqdvd with h5 | h5
    · rcases (Nat.Prime.dvd_mul hqp).1 h5 with h6 | h6
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).1
          (hqp.dvd_of_dvd_pow h6)) hq2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_three).1
          (hqp.dvd_of_dvd_pow h6)) hq3
    · exact (Nat.prime_dvd_prime_iff_eq hqp (by norm_num : Nat.Prime 7)).1
        (hqp.dvd_of_dvd_pow h5)
  obtain ⟨p₀, hp₀⟩ := c.std.hx.sig_nonempty
  ext q
  constructor
  · intro hq
    exact key q hq
  · intro hq
    rw [Set.mem_singleton_iff.1 hq, ← key p₀ hp₀]
    exact hp₀

theorem s168e3_concl163F_of_sum_three_l3_of_s15_eq_one
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1)
    (hL3 : IsL3 ↥(lBar V₀ V hV L) 1) :
    Concl163F D V₀ V hV L := by
  let A := Mbar D.M V₀ V hV
  let B := lBar V₀ V hV L
  let K := s1t3KBar A B
  have hT : ThreeNat A B (barSub V₀ V hV D.T) :=
    s168e3_threeNat_of_s15_eq_one c hcomp hsum htrans hs
  have h7 : Nat.card ↥(irrSet B) = 7 :=
    s168e3_irrSet_seven_of_sum_three c hcomp hsum htrans hs
  have hU : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hZ : wTil V₀ V hV L ⊓ fixV B = ⊥ :=
    s168e3_threeNatSeven_l3_fixV_eq_bot c hcomp hsum htrans hs h7 hL3
  obtain ⟨-, -, -, -, -, -, -, hKcase⟩ := hT.structure_of_seven h7
  have hKcases : (Nat.card ↥K = 7 ∨ Nat.card ↥K = 21) ∨
      (Nat.card ↥K = 168 ∧ IsSimpleGroup ↥K) := by
    rcases hKcase with hK7 | hK21 | hK168
    · exact Or.inl (Or.inl hK7)
    · exact Or.inl (Or.inr hK21)
    · exact Or.inr hK168
  rcases hKcases with hKsmall | ⟨hK168, -⟩
  ·
    have hFstar : Nonempty (↥(fstarBar D.M V₀ V hV) ≃*
        (Multiplicative (ZMod 7) × ↥B)) :=
      s168e3_threeNatSeven_l3_fstarBar_equiv_zmod_seven_prod_lBar_of_small_kBar
        hT h7 hL3 hKsmall
    have hsig : D.sig = {7} :=
      s168e3_threeNatSeven_l3_sig_eq_seven_of_small_kBar c hT h7 hL3 hKsmall
    have hZ' : (⊤ : Subgroup (Vtil V₀ V hV)) ⊓ fixV (lBar V₀ V hV L) = ⊥ := by
      simpa only [hU] using hZ
    have hsum3 : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1) B
        (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ 3 := by
      have h := SumOfNatShape.sl3_of_card_eq_168 hcomp.2.2
        (CFSG.LocalAnalysis.UniquenessCase.PartTwo.card_eq_of_isL3 hL3) hsum
      simpa only [hU, hZ'] using h
    have hcase : Case163_7 D V₀ V hV L := ⟨hFstar, hL3, hsum3, hsig⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcase)))))))
  ·
    have hT2 : TensorNatL32 A :=
      s168e3_tensorNatL32_of_sum_three_l3_kBar_168 c hcomp hsum htrans hs hL3 hK168
    have hsig : D.sig = {7} :=
      s168e3_sig_eq_seven_of_sum_three_l3_kBar_168 c hcomp hsum htrans hs hL3 hK168
    have hF : fstarBar D.M V₀ V hV = A :=
      s168e3_threeNatSeven_l3_fstarBar_eq_mbar_of_kBar_168 hT h7 hL3 hK168
    have hequiv : Nonempty (↥(fstarBar D.M V₀ V hV) ≃* (↥B × ↥B)) :=
      s168e3_threeNatSeven_l3_fstarBar_equiv_lBar_prod_self_of_kBar_168 hT h7 hL3 hK168
    have hnat : NatTensor (fstarBar D.M V₀ V hV) (wTil V₀ V hV L) ⊥ 3 1 := by
      refine ⟨ZMod 2, inferInstance, inferInstance, ?_, ?_⟩
      · rw [Nat.card_zmod]
        norm_num
      · rw [hF, hU]
        exact hT2
    have hcase : Case163_8F D V₀ V hV L :=
      ⟨⟨↥B, inferInstance, hL3, hequiv⟩, hnat, hs, hsig⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl hcase))))))))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
