module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Norm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Four
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677Defs
public import CFSG.RankThree.PartOne.N143.GroupLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16c11_excl_of_r16_4 (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (hR : R16_4 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 2)
    (hγ : 3 < gamma15 D.M V₀ V hV L) : False := by
  obtain ⟨-, h | h | h | h⟩ := hR V₀ V L hV hc.setting hc.conc (by rw [hs]; norm_num)
  · omega
  · have hσ : 3 ∈ D.sig := by
      rw [h.2.1]
      exact Set.mem_singleton 3
    have h1 := hx.four_le h4 3 hσ
    have h3 := h.2.2.1
    omega
  · have hσ : 7 ∈ D.sig := by
      rw [h.2.2.1]
      exact Set.mem_singleton 7
    have h1 := hx.four_le h4 7 hσ
    have h3 := h.2.2.2.1
    omega
  · obtain ⟨p, -, -, -, hsig, hrk, -⟩ := h
    have hσ : p ∈ D.sig := by
      rw [hsig]
      exact Set.mem_singleton p
    have h1 := hx.four_le h4 p hσ
    omega

theorem s16c11_excl_case6 (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (hR : R16_4 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (h6 : Case168_6 D V₀ V hV L) : False := by
  refine s16c11_excl_of_r16_4 D hx h4 hR hc h6.2.2.1 ?_
  rcases h6.2.1 with ⟨-, hsum⟩ | ⟨-, hsum⟩
  · rw [s16e_gamma15_eq_of_inf_fixV D hV
      (s16e_inf_fixV_eq_bot_sumOfNat_alt (by norm_num) (by decide) hsum)]
    have h8 := s16e_rk_sumOfNat_ge (b := 4) (fun I hI => by
      have h := s16c1610_rk_alternatingNatural_odd (by decide : Odd 5) hI
      omega) hsum
    omega
  · rw [s16e_gamma15_eq_of_inf_fixV D hV
      (s16c167_inf_fixV_eq_bot_of_sumOfNat (by norm_num) hsum)]
    have h6' := s16e_rk_sumOfNat_ge (b := 3) (fun I hI => by
      have h := s16c1610_rk_binaryNaturalSL hI
      omega) hsum
    omega

theorem s16c11_excl_case9 (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (hR : R16_4 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (h9 : Case168_9 D V₀ V hV L) : False := by
  refine s16c11_excl_of_r16_4 D hx h4 hR hc h9.2.2.1 ?_
  have hsum := h9.2.2.2.1
  rw [s16e_gamma15_eq_of_inf_fixV D hV
    (s16c167_inf_fixV_eq_bot_of_sumOfNat (by norm_num) hsum)]
  have h9' := s16e_rk_sumOfNat_ge (b := 3) (fun I hI => by
    have h := s16c1610_rk_binaryNaturalSL hI
    omega) hsum
  omega

theorem s16c11_excl_case10 (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (hR : R16_4 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (h10 : Case168_10 D V₀ V hV L) : False := by
  obtain ⟨p, hp, hcyc, hrk, hs, -, -⟩ := h10
  refine s16c11_excl_of_r16_4 D hx h4 hR hc hs ?_
  have hodd : Odd (Nat.card ↥(lBar V₀ V hV L)) := by
    rw [hcyc.2]
    rcases hp with rfl | rfl <;> decide
  rw [s16e_gamma15_eq_of_odd D hV hodd, hrk]
  rcases hp with rfl | rfl
  · rw [s16c1610_dParam_three]
    norm_num
  · rw [s16c1610_dParam_seven]
    norm_num

theorem s16c11_excl_case7 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h4 : 3 < CFSG.Open.evenRank G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (h7 : Case168_7 D V₀ V hV L) : False := by
  have h7σ : 7 ∈ D.sig := by
    rw [h7.2.2.2]
    exact Set.mem_singleton 7
  have h3 := s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 hc.setting.hyp16 hV h4 h7σ
  have h2 := s16n9b_case7_pRank_lt D hV h7
  omega

private theorem s16c11_excl_elemAbelian_card_of_rank {X : Type} [Group X] {E : Subgroup X}
    (hE : IsElemAbelianOfRank 3 2 ↥E) : IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨e⟩ := hE
  refine ⟨⟨IsMulCommutative.of_comm fun a b => ?_, fun a ha => ?_⟩, ?_⟩
  · have h1 : e a * e b = e b * e a := mul_comm _ _
    rw [← map_mul, ← map_mul] at h1
    exact e.injective h1
  · have h1 : e (⟨a, ha⟩ ^ 3) = 1 := by
      rw [map_pow]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      rw [show ((3 : ℕ) : ZMod 3) = 0 from ZMod.natCast_self 3, zero_mul]
    have h2 := e.injective (h1.trans (map_one e).symm)
    simpa using congrArg Subtype.val h2
  · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide

private theorem s16c11_excl_inf_centralizer_fstar_le {Q : Type} [Group Q] [Finite Q]
    (X : Subgroup Q) :
    X ⊓ Subgroup.centralizer (Fstar X : Set Q) ≤ Fstar X := by
  intro x hx
  obtain ⟨hxX, hxc⟩ := hx
  have hc : (⟨x, hxX⟩ : X) ∈
      Subgroup.centralizer (genFittingFStar ↥X : Set ↥X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (y : Q) ∈ Fstar X := ⟨y, hy, rfl⟩
    have h := Subgroup.mem_centralizer_iff.mp hxc (y : Q) hy'
    exact Subtype.ext h
  have hx' : (⟨x, hxX⟩ : X) ∈ genFittingFStar ↥X :=
    CFSG.Adapters.generalized_fitting_self_centralizing ↥X hc
  change x ∈ (genFittingFStar ↥X).map X.subtype
  exact ⟨⟨x, hxX⟩, hx', rfl⟩

private theorem s16c11_excl_false_of_elemAbelian_card_nine {X : Type} [Group X] [Finite X]
    (E : Subgroup X) [E.Normal] [CFSG.IsElementaryAbelian 3 E] (hcard : Nat.card E = 9)
    (hcent : Subgroup.centralizer (E : Set X) ≤ E)
    (h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) : False := by
  obtain ⟨A, -, hAel, hAcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup X)
  haveI : CFSG.IsElementaryAbelian 3 A := hAel.isElementaryAbelian
  have hApg : IsPGroup 3 A := CFSG.IsElementaryAbelian.isPGroup 3 A
  have hAcard27 : 27 ≤ Nat.card A := by
    rw [hAcard]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
          Nat.pow_le_pow_right (by norm_num) h3
  let ρ : A →* MulAut E := (MulAut.conjNormal (H := E)).comp A.subtype
  have hconj : ∀ g : X, MulAut.conjNormal (H := E) g = 1 ↔
      g ∈ Subgroup.centralizer (E : Set X) := by
    intro g
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h e he
      have h1 := congrArg (fun f : MulAut E => f ⟨e, he⟩) h
      simp only [MulAut.one_apply] at h1
      have h2 : g * e * g⁻¹ = e := by
        have h3 := congrArg Subtype.val h1
        rw [MulAut.conjNormal_apply] at h3
        simpa using h3
      calc e * g = (g * e * g⁻¹) * g := by rw [h2]
        _ = g * e := by group
    · intro h
      ext e
      rw [MulAut.conjNormal_apply, MulAut.one_apply]
      rw [← h (e : X) e.2]
      group
  have hker_eq : ρ.ker = (A ⊓ Subgroup.centralizer (E : Set X)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rw [show ρ a = MulAut.conjNormal (H := E) (a : X) from rfl, hconj]
    exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
  have hker_card : Nat.card ρ.ker = Nat.card ↥(A ⊓ Subgroup.centralizer (E : Set X)) := by
    rw [hker_eq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (H := A ⊓ Subgroup.centralizer (E : Set X)) (K := A) inf_le_left).toEquiv
  have hker_le : Nat.card ρ.ker ≤ 9 := by
    rw [hker_card, ← hcard]
    exact Subgroup.card_le_of_le (inf_le_right.trans hcent)
  have hAcard_le : Nat.card A ≤ 27 := by
    have h := CFSG.RankThree.PartOne.N143.card_le_three_mul_ker E hcard hApg ρ
    have h2 : 3 * Nat.card ρ.ker ≤ 3 * 9 := Nat.mul_le_mul_left 3 hker_le
    omega
  have hAcard_eq : Nat.card A = 27 := le_antisymm hAcard_le hAcard27
  have hker_eq9 : Nat.card ρ.ker = 9 := by
    have h := CFSG.RankThree.PartOne.N143.card_le_three_mul_ker E hcard hApg ρ
    omega
  have hinf_eq : A ⊓ Subgroup.centralizer (E : Set X) = E := by
    refine Subgroup.eq_of_le_of_card_ge (inf_le_right.trans hcent) ?_
    rw [← hker_card, hker_eq9]
    exact hcard.le
  have hEA : E ≤ A := by rw [← hinf_eq]; exact inf_le_left
  have hAcent : A ≤ Subgroup.centralizer (E : Set X) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    simpa using congrArg Subtype.val (mul_comm' (⟨e, hEA he⟩ : A) (⟨a, ha⟩ : A))
  have hAE : A ≤ E := hAcent.trans hcent
  have : Nat.card A ≤ Nat.card E := Subgroup.card_le_of_le hAE
  omega

theorem s16c11_excl_case8 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h4 : 3 < CFSG.Open.evenRank G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (h8 : Case168_8 D V₀ V hV) : False := by
  have h3sig : 3 ∈ D.sig := by
    rw [h8.2.2]
    exact Set.mem_singleton 3
  have h3rank : 3 ≤ CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) :=
    s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 hc.setting.hyp16 hV h4 h3sig
  let E : Subgroup ↥(Mbar D.M V₀ V hV) :=
    (fstarBar D.M V₀ V hV).subgroupOf (Mbar D.M V₀ V hV)
  have hcardE : Nat.card E = 9 := by
    change Nat.card ((fstarBar D.M V₀ V hV).subgroupOf (Mbar D.M V₀ V hV)) = 9
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (fstarBar_le_mbar D.M V₀ V hV)).toEquiv]
    exact (s16c11_excl_elemAbelian_card_of_rank h8.1).2
  haveI hEn : E.Normal := by
    change ((fstarBar D.M V₀ V hV).subgroupOf (Mbar D.M V₀ V hV)).Normal
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (fstarBar_le_mbar D.M V₀ V hV)).2 (mbar_le_normalizer_fstarBar D.M V₀ V hV)
  haveI hEl : CFSG.IsElementaryAbelian 3 E := by
    change CFSG.IsElementaryAbelian 3
      ((fstarBar D.M V₀ V hV).subgroupOf (Mbar D.M V₀ V hV))
    exact ((s16c11_excl_elemAbelian_card_of_rank h8.1).1.subgroupOf
      (Mbar D.M V₀ V hV)).isElementaryAbelian
  have hcent : Subgroup.centralizer (E : Set ↥(Mbar D.M V₀ V hV)) ≤ E := by
    intro x hx
    change (x : MulAut (Vtil V₀ V hV)) ∈ fstarBar D.M V₀ V hV
    have hx' : (x : MulAut (Vtil V₀ V hV)) ∈
        Mbar D.M V₀ V hV ⊓
          Subgroup.centralizer (fstarBar D.M V₀ V hV :
            Set (MulAut (Vtil V₀ V hV))) := by
      refine ⟨x.2, ?_⟩
      change (x : MulAut (Vtil V₀ V hV)) ∈
        Subgroup.centralizer (fstarBar D.M V₀ V hV :
          Set (MulAut (Vtil V₀ V hV)))
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have he' : (⟨e, fstarBar_le_mbar D.M V₀ V hV he⟩ :
          ↥(Mbar D.M V₀ V hV)) ∈ E := he
      have h := Subgroup.mem_centralizer_iff.mp hx
        (⟨e, fstarBar_le_mbar D.M V₀ V hV he⟩ : ↥(Mbar D.M V₀ V hV)) he'
      exact congrArg Subtype.val h
    exact s16c11_excl_inf_centralizer_fstar_le (Mbar D.M V₀ V hV) hx'
  have h3' : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(Mbar D.M V₀ V hV)) := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (Mbar D.M V₀ V hV)]
    exact h3rank
  exact s16c11_excl_false_of_elemAbelian_card_nine E hcardE hcent h3'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
