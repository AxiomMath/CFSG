module

public import CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProofAut
public import CFSG.RankThree.PartTwo.Sec4.Item41PRankNarrow41
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
import CFSG.RankThree.PartTwo.KFacts.K71Residual
public import CFSG.RankThree.PartTwo.Sec10.Item1012Res3Proof
public import CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProofChief
public import CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProofCyclic

public section

namespace CFSG.RankThree.PartTwo.Sec10.SuzukiSectionProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof
open Subgroup

section Step

theorem step1012KAutSolv_of_pRankLargePrime (hPR : Sec4.Item4_1PRankLargePrime) :
    Step1012KAutSolv := by
  intro h45 h97 G _ _ A c L a R h d hdL hUθ hUmax S hS hUS hSc hSd hSab w hwA hwS hwa hwd hwc Q
    hQ2 hQA hQS hQB hQθU hQS' hQθ hauto hm3
  classical
  by_cases hS1 : S = ⊥
  ·
    subst hS1
    refine ⟨⊥, bot_le, inferInstance, inf_le_right, fun σ _ => ?_, ?_⟩
    · have : σ = 1 := MulEquiv.ext fun x => Subsingleton.elim _ _
      rw [this]
      exact one_mem _
    · rw [bot_inf_eq]
      infer_instance
  set H := centralizer ((closure {a, d} : Subgroup G) : Set G) with hHdef
  set NS := normalizer (S : Set G) with hNSdef
  set P := inSubgroup perfectResidual (Sec4.autIn H S) with hPdef
  set N := H ⊓ NS with hNdef
  have hT4 := h.toTheoremFourHyp
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.1.2.1
  have haH : ∀ g ∈ H, g * a = a * g := fun g hg =>
    (mem_centralizer_iff.mp hg a (subset_closure (Set.mem_insert a {d}))).symm
  have hNtop : N ≠ ⊤ := by
    intro hN
    apply Sec6.centralizer_ne_top_of_ne_one hT4 h.a_ne_one
    rw [eq_top_iff]
    intro g _
    have hgN : g ∈ N := hN ▸ mem_top g
    exact mem_centralizer_singleton_iff.mpr (haH g hgN.1)
  have hSFH : SectionFourHyp N := hT4.sectionFourHyp hNtop
  have h5N : CFSG.Open.pRank 5 (⊤ : Subgroup N) ≤ 2 := pRank_five_le_two hT4 hS1 hS2 inf_le_right
  have h5 : ∀ (V : Subgroup N) (M : Subgroup V) [M.Normal], CFSG.layer (V ⧸ M) = ⊤ →
      CFSG.Open.pRank 5 (⊤ : Subgroup (V ⧸ M)) ≤ 2 := by
    intro V M _ hlayer
    have h1 := hPR N hSFH V M hlayer 5 (by norm_num) (by norm_num) (h5N.trans (by norm_num))
    exact h1.trans h5N
  set DY : Subgroup N := perfectResidual N with hDY
  have hDYn : DY.Normal := inferInstance
  have hDYp : Group.IsPerfect DY := (CFSG.perfect_residual_characterization (G := N)).2.2.1
  set OY : Subgroup N := closure {x | x ∈ DY ∧ ∃ k : ℕ, x ^ 3 ^ k = 1} with hOY
  have hOYn : OY.Normal := closure_pow_three_normal hDYn
  set O : Subgroup G := OY.map N.subtype with hOdef
  set J : Subgroup G := inSubgroup perfectResidual O with hJdef
  have hON : O ≤ N := map_subtype_le _
  have hJO : J ≤ O := map_subtype_le _
  have hOS : O ≤ NS := hON.trans inf_le_right
  have hNO : N ≤ normalizer (O : Set G) := by
    have h1 := Subgroup.le_normalizer_map (H := OY) N.subtype
    rw [normalizer_eq_top_iff.mpr hOYn, ← MonoidHom.range_eq_map, range_subtype] at h1
    exact h1
  set D : Subgroup G := inSubgroup perfectResidual N with hDdef
  have hDN : D ≤ N := map_subtype_le _
  have hDS : D ≤ NS := hDN.trans inf_le_right
  have hPD : P ≤ Sec4.autIn D S := (Item1012Res3Proof.residual_cover H S).2.2.2
  have hPO : P ≤ Sec4.autIn O S := by
    have h3 : ∀ σ ∈ P, (∃ k : ℕ, σ ^ 3 ^ k = 1) → σ ∈ Sec4.autIn O S := by
      rintro σ hσ ⟨k, hk⟩
      obtain ⟨x, hxD, hxN, ⟨e, he⟩, hx⟩ := exists_pow_three_lift (hPD hσ) hk
      refine Sec4.mem_autIn_iff.mpr ⟨x, hxN, ?_, hx⟩
      obtain ⟨y, hyD, rfl⟩ := hxD
      exact ⟨y, subset_closure ⟨hyD, e, Subtype.ext (by simpa using he)⟩, rfl⟩
    have hPq := (Item1012Res3Proof.isQuasisimple_and_center_of_type
      (Sec6.isPerfect_inSubgroup_perfectResidual _) hauto).1
    obtain ⟨y, hy3, hyc⟩ := exists_pow_three_not_mem_center hauto
    have htop := closure_pow_three_eq_top hPq hy3 hyc
    have hle : (closure {x : P | ∃ k : ℕ, x ^ 3 ^ k = 1}).map P.subtype ≤ Sec4.autIn O S := by
      rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
      exact h3 x x.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
    intro σ hσ
    exact hle ⟨⟨σ, hσ⟩, htop ▸ mem_top _, rfl⟩
  have hPJ : P ≤ Sec4.autIn J S := by
    rw [hJdef, autIn_inSubgroup_perfectResidual hOS]
    exact KFacts.le_inSubgroup_perfectResidual (Sec6.isPerfect_inSubgroup_perfectResidual _) hPO
  set CY : Subgroup N := (centralizer (S : Set G)).subgroupOf N with hCY
  have hCYn : CY.Normal := ⟨fun x hx n => by
    rw [mem_subgroupOf, mem_centralizer_iff] at hx ⊢
    intro s hs
    have hn : ((n : N) : G) ∈ NS := n.2.2
    have h1 : ((n : G))⁻¹ * s * (n : G) ∈ S := by
      have := (mem_normalizer_iff.mp (inv_mem hn) s).mp hs
      simpa using this
    have h2 := hx _ h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc s * ((n : G) * (x : G) * (n : G)⁻¹)
        = (n : G) * (((n : G)⁻¹ * s * (n : G)) * (x : G)) * (n : G)⁻¹ := by group
      _ = (n : G) * ((x : G) * ((n : G)⁻¹ * s * (n : G))) * (n : G)⁻¹ := by rw [h2]
      _ = (n : G) * (x : G) * (n : G)⁻¹ * s := by group⟩
  set XY : Subgroup N := OY ⊓ CY with hXY
  have hXYn : XY.Normal := inferInstance
  have hX3 : ∀ x : XY, x ^ 3 = 1 → ((x : N) : G) ∈ zpowers a := by
    intro x hx
    have hxC : ((x : N) : G) ∈ centralizer (S : Set G) := mem_subgroupOf.mp (mem_inf.mp x.2).2
    have hxH : ((x : N) : G) ∈ H := (x : N).2.1
    refine hm3 _ ⟨hxC, hxH⟩ ?_
    have := congrArg (fun y : XY => ((y : N) : G)) hx
    simpa using this
  have hcent : ∀ x : XY, x ^ 3 = 1 → x ∈ center XY := by
    intro x hx
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hX3 x hx)
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hm]
    exact (Commute.zpow_right (haH _ (g : N).2.1) m).eq
  have hcard3 : Nat.card {x : XY // x ^ 3 = 1} ≤ 3 := by
    have hinj : Function.Injective
        (fun x : {x : XY // x ^ 3 = 1} => (⟨((x.1 : N) : G), hX3 x.1 x.2⟩ : zpowers a)) := by
      intro x y hxy
      have h1 := congrArg Subtype.val hxy
      simp only at h1
      exact Subtype.ext (Subtype.ext (Subtype.ext h1))
    refine (Nat.card_le_card_of_injective _ hinj).trans ?_
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (h.pow_three h.a_mem))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hKn, hK3, hKq⟩ := exists_normal_complement (p := 3) (by norm_num) hcent hcard3
  set UY : Subgroup N := K.map XY.subtype with hUY
  have hUYn : UY.Normal := by
    refine ⟨fun u hu n => ?_⟩
    obtain ⟨k, hk, rfl⟩ := hu
    have hkord : ¬ 3 ∣ orderOf k := (mem_iff_not_dvd_orderOf hK3 hKq k).mp hk
    have hconj : n * (k : N) * n⁻¹ ∈ XY := hXYn.conj_mem _ k.2 n
    refine ⟨⟨n * (k : N) * n⁻¹, hconj⟩, (mem_iff_not_dvd_orderOf hK3 hKq _).mpr ?_, rfl⟩
    rw [Subgroup.orderOf_mk]
    have h1 : orderOf (n * (k : N) * n⁻¹) = orderOf (k : N) := by
      have := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective (k : N)
      simpa using this
    rw [h1, Subgroup.orderOf_coe]
    exact hkord
  have hUY3 : ¬ 3 ∣ Nat.card UY := by
    rw [hUY, Subgroup.card_map_of_injective XY.subtype_injective]
    exact hK3
  have hUYO : UY ≤ OY := (map_subtype_le K).trans inf_le_left
  have hUYs : Group.IsSolvable UY :=
    isSolvable_of_le_closure_pow_three hSFH.kGroup h5 hDYp hUY3 hUYO
  have hKs : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective
      (f := (K.equivMapOfInjective _ XY.subtype_injective).toMonoidHom) (MulEquiv.injective _)
  have hXYs : Group.IsSolvable XY := isSolvable_of_isPGroup_quotient hKq hKs
  refine ⟨J, hJO.trans hON, Sec6.isPerfect_inSubgroup_perfectResidual O, fun n hn =>
    CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual O
      (hNO hn), hPJ, ?_⟩
  have hmemO : ∀ x : G, ∀ hxN : x ∈ N, x ∈ O → (⟨x, hxN⟩ : N) ∈ OY := by
    rintro x hxN ⟨y, hy, rfl⟩
    exact hy
  have hJmem : ∀ x : (J ⊓ centralizer (S : Set G) : Subgroup G), (x : G) ∈ N :=
    fun x => hON (hJO (mem_inf.mp x.2).1)
  let ι : (J ⊓ centralizer (S : Set G) : Subgroup G) →* XY :=
    { toFun := fun x => ⟨⟨x, hJmem x⟩, mem_inf.mpr ⟨hmemO _ _ (hJO (mem_inf.mp x.2).1),
        mem_subgroupOf.mpr (mem_inf.mp x.2).2⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun x y hxy =>
    Subtype.ext (congrArg (fun z : XY => ((z : N) : G)) hxy)
  exact Group.isSolvable_of_isSolvable_injective hι

end Step

section Holds

theorem step1012KAutSolv_holds : Step1012KAutSolv :=
  step1012KAutSolv_of_pRankLargePrime
    (Sec4.Item41Narrow.item4_1PRankLargePrime_of_griess
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)

end Holds

end CFSG.RankThree.PartTwo.Sec10.SuzukiSectionProof
