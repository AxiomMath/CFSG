module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenCyclicThreeCoordinates
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSigmaIndexThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSeventeen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0a
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIndexTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LinearAlgebra CFSG.RepresentationTheory
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open scoped Pointwise

theorem mbar_card_ne_six
    {G : Type} [Group G] [Finite G]
    (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    {V₀ V : Subgroup G} (h16 : Hyp16 D V₀ V) (hV : IsElemAbelian 2 V) :
    Nat.card ↥(Mbar D.M V₀ V hV) ≠ 6 := by
  intro h6
  have hcard : Nat.card ↥(Mbar D.M V₀ V hV) = 2 ^ 1 * 3 ^ 1 := by
    rw [h6]
    norm_num
  have hsig : D.sig = {3} :=
    sig_eq_three_of_mbar_card_two_pow_mul_three_pow D hx h61 h127 h16 hV hcard
  have h3 : 3 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 3
  have h2 : 2 ≤ CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) :=
    S17.two_le_pRank_mbar_of_mem_sig h16.hyp125 hx h61 h127
      (c23_card_v0_le_four D h16) h3
  have hnot9 : ¬ 9 ∣ Nat.card ↥(Mbar D.M V₀ V hV) := by
    rw [h6]
    norm_num
  have hle : CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) ≤ 1 :=
    CFSG.LocalAnalysis.RankThreeUC.S15.pRank_le_one_of_not_sq_dvd
      (Y := MulAut (Vtil V₀ V hV)) Nat.prime_three hnot9
  omega

theorem cyclic_three_rank_six_s1_irreducible
    {G : Type} [Group G] [Finite G]
    (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1214 : F12.R1214 D)
    (hS : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    (hm : mBar D.M V₀ V hV = 3)
    (hs : s15 D.M V₀ V hV L = 1)
    (hcyc : IsCyclicOrd ↥(lBar V₀ V hV L) 3)
    (hrk : rk ↥(wTil V₀ V hV L) = 6)
    (z : MulAut (Vtil V₀ V hV)) (hz : orderOf z = 3)
    (hgen : lBar V₀ V hV L = Subgroup.zpowers z)
    (e : Vtil V₀ V hV ≃* Multiplicative (Fin 3 → OmegaField))
    (he : ∀ w : Vtil V₀ V hV,
      Multiplicative.toAdd (e (z w)) = CFSG.LinearAlgebra.omega • Multiplicative.toAdd (e w))
    (ρ : Mbar D.M V₀ V hV →* coordinateSemilinearGroup 3 OmegaField)
    (hρ : ∀ (g : Mbar D.M V₀ V hV) (w : Vtil V₀ V hV),
      Multiplicative.toAdd (e ((g : MulAut (Vtil V₀ V hV)) w)) =
        coordinateSemilinearMap (ρ g) (Multiplicative.toAdd (e w)))
    (hker : (SemidirectProduct.rightHom.comp ρ).ker =
      (Subgroup.centralizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))).subgroupOf
        (Mbar D.M V₀ V hV))
    (τ : (SemidirectProduct.rightHom.comp ρ).ker →*
      Matrix.GeneralLinearGroup (Fin 3) OmegaField)
    (hτ : ∀ c : (SemidirectProduct.rightHom.comp ρ).ker,
      ρ (c : Mbar D.M V₀ V hV) = SemidirectProduct.inl (τ c)) :
    CFSG.RepresentationTheory.IsIrreducibleMatrixRep τ.range.subtype := by
  classical
  let W := Vtil V₀ V hV
  let A : Subgroup (MulAut W) := Mbar D.M V₀ V hV
  let Lb : Subgroup (MulAut W) := lBar V₀ V hV L
  let C : Subgroup A := (Subgroup.centralizer (Lb : Set (MulAut W))).subgroupOf A
  let J : Subgroup (MulAut W) := C.map A.subtype
  have hC : C.Normal ∧ Odd (Nat.card C) ∧ C.index = 2 := by
    simpa [A, C, Lb] using cyclic_three_rank_six_s1_centralizer D hc hm hs hcyc hrk
  have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have htop : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 hc hs
  have hrk' : rk ↥(⊤ : Subgroup (Vtil V₀ V hV)) = 6 := by
    rw [← htop]
    exact hrk
  have hcard : Nat.card (Vtil V₀ V hV) = 2 ^ 6 := by
    rw [s16e_card_eq_two_pow_rk_top hW, hrk']
  have hWL : commSub ⊤ Lb = ⊤ := by
    simpa [Lb, wTil, lBar] using htop
  have hoddz : Odd (orderOf z) := by
    rw [hz]
    norm_num
  have hLbgen : Lb = Subgroup.zpowers z := by
    simpa [Lb] using hgen
  have hfixZ : ∀ w : Vtil V₀ V hV, z w = w → w = 1 :=
    s168e3_cyc_fpf hW hLbgen hoddz hWL
  have hLbA : Lb ≤ A := by
    simpa [Lb, lBar, A] using barSub_mono V₀ V hV hS.hyp151.le
  have hzLb : z ∈ Lb := by
    rw [hLbgen]
    exact Subgroup.mem_zpowers z
  have hzA : z ∈ A := hLbA hzLb
  have hLb_le_centralizer : Lb ≤ Subgroup.centralizer (Lb : Set (MulAut W)) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr
      (@IsCyclic.isMulCommutative ↥Lb _ hcyc.1)
  have hzC : (⟨z, hzA⟩ : A) ∈ C := by
    rw [show C = (Subgroup.centralizer (Lb : Set (MulAut W))).subgroupOf A from rfl]
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_centralizer_iff.mpr fun l hl =>
      ((Subgroup.mem_centralizer_iff.1 (hLb_le_centralizer hl)) z hzLb).symm
  have hzJ : z ∈ J := Subgroup.mem_map.mpr ⟨⟨z, hzA⟩, hzC, rfl⟩
  have hcentJ : ∀ g ∈ J, g * z = z * g := by
    intro g hg
    rcases Subgroup.mem_map.mp hg with ⟨c, hcC, rfl⟩
    exact ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 hcC)) z hzLb).symm
  have hJA : J ≤ A := Subgroup.map_subtype_le C
  have hCeq : J.subgroupOf A = C := by
    change (C.map A.subtype).comap A.subtype = C
    exact Subgroup.comap_map_eq_self_of_injective A.subtype_injective C
  have hJn : (J.subgroupOf A).Normal := by
    rw [hCeq]
    exact hC.1
  have hindex : (J.subgroupOf A).index = 2 := by
    rw [hCeq]
    exact hC.2.2
  have hcardJC : Nat.card J = Nat.card C := by
    rw [show J = C.map A.subtype from rfl]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective C A.subtype A.subtype_injective).toEquiv).symm
  have hJodd : Odd (Nat.card J) := by
    rw [hcardJC]
    exact hC.2.1
  have hJne : J ≠ ⊥ := by
    intro hbot
    have hzbot : z ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← hbot]
      exact hzJ
    rw [Subgroup.mem_bot] at hzbot
    rw [hzbot, orderOf_one] at hz
    omega
  have htrans : IrrSpanTrans A J :=
    twelve_seventeen D hx h61 h127 h1214 hS.hyp16.hyp125 J hJne hJA hJn (Or.inl hJodd)
  have hdich :=
    CFSG.LocalAnalysis.WeakClosure81.irreducible_or_card_three_of_irrSpanTrans_index_two
      (W := W) hW hcard hJA hJn hindex z hzJ hz hfixZ hcentJ htrans
  rcases hdich with hIrr | hJcard
  ·
    intro U hU
    let S : Subgroup W := U.toAddSubgroup.toSubgroup.comap e.toMonoidHom
    have hSmem : ∀ w : W, w ∈ S ↔ Multiplicative.toAdd (e w) ∈ U := by
      intro w
      change e w ∈ U.toAddSubgroup.toSubgroup ↔ Multiplicative.toAdd (e w) ∈ U
      rw [Multiplicative.mem_toSubgroup]
      rfl
    have hSstable : StableUnder J S := by
      intro j hj w hw
      rcases Subgroup.mem_map.mp hj with ⟨c, hcC, rfl⟩
      have hkerC : c ∈ (SemidirectProduct.rightHom.comp ρ).ker := by
        rw [hker]
        exact hcC
      have hρc : ρ c = SemidirectProduct.inl (τ ⟨c, hkerC⟩) := by
        simpa using hτ ⟨c, hkerC⟩
      have hτmem : τ ⟨c, hkerC⟩ ∈ τ.range := MonoidHom.mem_range.mpr ⟨⟨c, hkerC⟩, rfl⟩
      have hwU : Multiplicative.toAdd (e w) ∈ U := (hSmem w).1 hw
      rw [hSmem]
      change Multiplicative.toAdd (e ((c : MulAut W) w)) ∈ U
      have hact := hρ c w
      rw [hρc, coordinateSemilinearMap_inl, matrixLinearEquiv_apply] at hact
      rw [hact]
      simpa using hU ⟨τ ⟨c, hkerC⟩, hτmem⟩ (Multiplicative.toAdd (e w)) hwU
    have hS := hIrr.2.2.2 S hSstable bot_le le_top
    rcases hS with hSbot | hStop
    · left
      rw [Submodule.eq_bot_iff]
      intro u hu
      let w : W := e.symm (Multiplicative.ofAdd u)
      have hwS : w ∈ S := by
        rw [hSmem]
        change Multiplicative.toAdd (e (e.symm (Multiplicative.ofAdd u))) ∈ U
        simpa using hu
      rw [hSbot, Subgroup.mem_bot] at hwS
      have h1 : Multiplicative.ofAdd u = 1 := by
        calc Multiplicative.ofAdd u = e w := (e.apply_symm_apply (Multiplicative.ofAdd u)).symm
          _ = 1 := by rw [hwS, map_one]
      simpa using congrArg Multiplicative.toAdd h1
    · right
      rw [Submodule.eq_top_iff']
      intro u
      let w : W := e.symm (Multiplicative.ofAdd u)
      have hwS : w ∈ S := by
        rw [hStop]
        exact Subgroup.mem_top w
      have hwU : Multiplicative.toAdd (e w) ∈ U := (hSmem w).1 hwS
      have huw : Multiplicative.toAdd (e w) = u := by simp [w]
      rwa [huw] at hwU
  · exfalso
    have hcardC3 : Nat.card C = 3 := by
      rw [← hcardJC]
      exact hJcard
    have hcardA : Nat.card A = Nat.card C * C.index := (Subgroup.card_mul_index C).symm
    have hA6 : Nat.card A = 6 := by
      rw [hcardA, hcardC3, hC.2.2]
    exact (mbar_card_ne_six D hx h61 h127 hS.hyp16 hV) hA6

theorem exists_cyclic_three_rank_six_s1_irreducible
    {G : Type} [Group G] [Finite G]
    (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1214 : F12.R1214 D)
    (hS : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    (hm : mBar D.M V₀ V hV = 3)
    (hs : s15 D.M V₀ V hV L = 1)
    (hcyc : IsCyclicOrd ↥(lBar V₀ V hV L) 3)
    (hrk : rk ↥(wTil V₀ V hV L) = 6) :
    ∃ (z : MulAut (Vtil V₀ V hV))
      (e : Vtil V₀ V hV ≃* Multiplicative (Fin 3 → OmegaField))
      (ρ : Mbar D.M V₀ V hV →* coordinateSemilinearGroup 3 OmegaField)
      (τ : (SemidirectProduct.rightHom.comp ρ).ker →*
        Matrix.GeneralLinearGroup (Fin 3) OmegaField),
      z ∈ lBar V₀ V hV L ∧
      orderOf z = 3 ∧
      lBar V₀ V hV L = Subgroup.zpowers z ∧
      (∀ w : Vtil V₀ V hV,
        Multiplicative.toAdd (e (z w)) = CFSG.LinearAlgebra.omega • Multiplicative.toAdd (e w)) ∧
      Function.Injective ρ ∧
      (∀ (g : Mbar D.M V₀ V hV) (w : Vtil V₀ V hV),
        Multiplicative.toAdd (e ((g : MulAut (Vtil V₀ V hV)) w)) =
          coordinateSemilinearMap (ρ g) (Multiplicative.toAdd (e w))) ∧
      (SemidirectProduct.rightHom.comp ρ).ker =
        (Subgroup.centralizer
          (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))).subgroupOf
            (Mbar D.M V₀ V hV) ∧
      Function.Injective τ ∧
      (∀ c : (SemidirectProduct.rightHom.comp ρ).ker,
        ρ (c : Mbar D.M V₀ V hV) = SemidirectProduct.inl (τ c)) ∧
      (∀ (c : (SemidirectProduct.rightHom.comp ρ).ker) (w : Vtil V₀ V hV),
        Multiplicative.toAdd (e (((c : Mbar D.M V₀ V hV) : MulAut (Vtil V₀ V hV)) w)) =
          (τ c : Matrix (Fin 3) (Fin 3) OmegaField).mulVec
            (Multiplicative.toAdd (e w))) ∧
      CFSG.RepresentationTheory.IsIrreducibleMatrixRep τ.range.subtype := by
  classical
  obtain ⟨z, e, -, hzmem, hzord, hgen, he, -, -, -⟩ :=
    exists_cyclic_three_rank_six_s1_coordinate_action D hc hs hcyc hrk
  have hW : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  have hAN : Mbar D.M V₀ V hV ≤
      Subgroup.normalizer (Subgroup.zpowers z : Set (MulAut (Vtil V₀ V hV))) := by
    intro g hg
    rw [← hgen]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (lBar_conj_eq_of_s15_eq_one hs hg)
  obtain ⟨ρ, τ, hρinj, hact, hker, hτinj, hτ, hτact⟩ :=
    exists_faithful_linear_kernel_action_of_normalizes_three
      hW z hzord e he (Mbar D.M V₀ V hV) hAN
  have hkerL : (Subgroup.centralizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))).subgroupOf
          (Mbar D.M V₀ V hV) =
      (Subgroup.centralizer
        ({z} : Set (MulAut (Vtil V₀ V hV)))).subgroupOf
          (Mbar D.M V₀ V hV) := by
    rw [hgen, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hker' : (SemidirectProduct.rightHom.comp ρ).ker =
      (Subgroup.centralizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))).subgroupOf
          (Mbar D.M V₀ V hV) := by
    rw [hker, hkerL]
  have hirr := cyclic_three_rank_six_s1_irreducible D hx h61 h127 h1214 hS hc hm hs
    hcyc hrk z hzord hgen e he ρ hact hker' τ hτ
  exact ⟨z, e, ρ, τ, hzmem, hzord, hgen, he, hρinj, hact, hker', hτinj, hτ, hτact, hirr⟩


end CFSG.LocalAnalysis.UniquenessCase.PartTwo
