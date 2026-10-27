module

public import CFSG.RankThree.GF2n.Smith81.InspOrders
public import CFSG.RankThree.GF2n.Smith81.S81BLane
public import CFSG.RankThree.GF2n.Smith81.ERecursion
public import CFSG.RankThree.GF2n.Smith81.S81StrothOracle
public import CFSG.RankThree.GF2n.Smith81.InspLocal
import CFSG.RankThree.GF2n.Smith81.InspE3
import CFSG.RankThree.GF2n.Smith81.TiBridge
import CFSG.GroupTheory.Fitting.SimpleNormal
import CFSG.LieType.Chevalley.OrdinaryExceptionalOuterTwoPart
public import CFSG.RankThree.GF2n.Smith81.Sec2FStar
public import CFSG.RankThree.GF2n.Smith81.TiSylow
import CFSG.RankThree.GF2n.Smith81.InspLinOrder

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 CFSG.Timmesfeld CFSG.Timmesfeld.Orders CFSG.CGT.Timmesfeld75
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Levi

theorem centralizer_fstar_eq_bot {H : Type} [Group H] [Finite H]
    (hS : IsSimpleGroup ↥(generalizedFitting H)) (h4 : 4 ∣ Nat.card ↥(generalizedFitting H)) :
    Subgroup.centralizer (generalizedFitting H : Set H) = ⊥ := by
  haveI : (generalizedFitting H).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := H)).2
  by_contra hne
  have hle := GroupTheory.generalizedFitting_le_of_normal hS
    (Subgroup.normal_centralizer (H := generalizedFitting H)) hne
  haveI : IsMulCommutative ↥(generalizedFitting H) :=
    ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hle a.2)) b b.2).symm⟩⟩
  have hp := (Group.is_simple_iff_prime_card (α := ↥(generalizedFitting H))).mp hS
  have h2 : 2 ∣ Nat.card ↥(generalizedFitting H) := (Nat.dvd_of_pow_dvd (by norm_num :
    1 ≤ 2) (by simpa using h4))
  rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h
  · omega
  · rw [← h] at h4
    omega

theorem card_dvd_of_centralizer_eq_bot {H : Type} [Group H] [Finite H] (N : Subgroup H)
    [N.Normal] (hC : Subgroup.centralizer (N : Set H) = ⊥) :
    Nat.card H ∣ Nat.card (Outer ↥N) * Nat.card ↥N := by
  have hker : (MulAut.conjNormal : H →* MulAut ↥N).ker = ⊥ := by
    rw [← hC]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx n hn
      have := congrArg (fun α : MulAut ↥N => ((α ⟨n, hn⟩ : ↥N) : H)) hx
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc n * x = x * n * x⁻¹ * x := by rw [this]
        _ = x * n := by group
    · intro hx
      refine MulEquiv.ext fun n => Subtype.ext ?_
      simp only [MulAut.conjNormal_apply, MulAut.one_apply]
      rw [← hx n n.2]
      group
  haveI : Finite (MulAut ↥N) :=
    Finite.of_injective (fun α : MulAut ↥N => (α : ↥N → ↥N)) DFunLike.coe_injective
  have hcard := Subgroup.card_ker_mul_card_range (MulAut.conjNormal : H →* MulAut ↥N)
  rw [hker, Subgroup.card_bot, one_mul] at hcard
  rw [← hcard]
  refine (Subgroup.card_subgroup_dvd_card _).trans ?_
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (inner ↥N)]
  exact mul_dvd_mul_left _ (Subgroup.card_range_dvd _)

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem card_H0_dvd_of_fstar (hc : Ctx M Q Z B) [(Q.subgroupOf (H0 M Z)).Normal]
    (hC : Subgroup.centralizer (generalizedFitting (SubCfgGroup M Q Z) :
      Set (SubCfgGroup M Q Z)) = ⊥) :
    Nat.card (H0 M Z) ∣ Nat.card Q * (Nat.card (Outer (FStar (SubCfgGroup M Q Z))) *
      Nat.card (FStar (SubCfgGroup M Q Z))) := by
  haveI : (generalizedFitting (SubCfgGroup M Q Z)).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := SubCfgGroup M Q Z)).2
  have h1 := card_dvd_of_centralizer_eq_bot (generalizedFitting (SubCfgGroup M Q Z)) hC
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf (H0 M Z)),
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Q_le_H0_of_strothHyp hc.hyp)).toEquiv,
    mul_comm]
  exact mul_dvd_mul_left _ h1

theorem card_mul_card_fstar_dvd (hc : Ctx M Q Z B) [(Q.subgroupOf (H0 M Z)).Normal]
    (hS : IsSimpleGroup (FStar (SubCfgGroup M Q Z))) (hLQ : ¬ Lgen M (LB M Q B) ≤ Q) {z : G}
    (hz : z ∈ Z) (hz1 : z ≠ 1) :
    Nat.card Q * Nat.card (FStar (SubCfgGroup M Q Z)) ∣ Nat.card (Subgroup.centralizer
      ({selfIn z} : Set ↥(Subgroup.normalClosure ({z} : Set G)))) := by
  set X := Subgroup.normalClosure ({z} : Set G) with hXdef
  haveI hXn : X.Normal := Subgroup.normalClosure_normal
  set W : Subgroup G := X ⊓ H0 M Z with hWdef
  have hWH : W ≤ H0 M Z := inf_le_right
  have hWX : W ≤ X := inf_le_left
  have hQW : Q ≤ W := le_inf (Q_le_normalClosure hc.hyp hz hz1) (Q_le_H0_of_strothHyp hc.hyp)
  set S : Subgroup ↥(H0 M Z) := W.subgroupOf (H0 M Z) with hSdef
  have hSn : S.Normal := by
    constructor
    intro s hs g
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    refine ⟨hXn.conj_mem _ hs.1 _, ?_⟩
    exact (H0 M Z).mul_mem ((H0 M Z).mul_mem g.2 s.2) ((H0 M Z).inv_mem g.2)
  set K : Subgroup (SubCfgGroup M Q Z) := S.map (QuotientGroup.mk' (Q.subgroupOf (H0 M Z)))
    with hKdef
  have hKn : K.Normal := hSn.map _ (QuotientGroup.mk'_surjective _)
  have hK1 : K ≠ ⊥ := by
    obtain ⟨l, hlL, hlQ⟩ := Set.not_subset.mp hLQ
    have hlH : l ∈ H0 M Z := Lgen_le_H0 hc hlL
    have hlX : l ∈ X := Lgen_le_normalClosure hc hz hz1 hlL
    intro hbot
    have hmem : QuotientGroup.mk' (Q.subgroupOf (H0 M Z)) ⟨l, hlH⟩ ∈ K :=
      ⟨⟨l, hlH⟩, Subgroup.mem_subgroupOf.mpr ⟨hlX, hlH⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hmem
    exact hlQ hmem
  have hFK : generalizedFitting (SubCfgGroup M Q Z) ≤ K :=
    GroupTheory.generalizedFitting_le_of_normal hS hKn hK1
  let φ := (QuotientGroup.mk' (Q.subgroupOf (H0 M Z))).domRestrict S
  have hφr : φ.range = K := MonoidHom.domRestrict_range _ _
  have hφk : φ.ker = (Q.subgroupOf (H0 M Z)).subgroupOf S := by
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
  have hQS : Q.subgroupOf (H0 M Z) ≤ S := fun x hx => Subgroup.mem_subgroupOf.mpr (hQW hx)
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [hφr, hφk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Q_le_H0_of_strothHyp hc.hyp)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWH).toEquiv] at hcard
  have hWC : W.subgroupOf X ≤ Subgroup.centralizer ({selfIn z} : Set ↥X) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hx.2.2 z hz).symm
  have hWcard : Nat.card W = Nat.card (W.subgroupOf X) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWX).toEquiv).symm
  calc Nat.card Q * Nat.card (FStar (SubCfgGroup M Q Z))
      ∣ Nat.card Q * Nat.card K := mul_dvd_mul_left _ (Subgroup.card_dvd_of_le hFK)
    _ = Nat.card W := hcard
    _ = Nat.card (W.subgroupOf X) := hWcard
    _ ∣ _ := Subgroup.card_dvd_of_le hWC

end Levi

theorem rootOutcome_classIn (hK1 : K1NSLStatement) {G : Type} [Group G] [Finite G]
    {M Q Z : Subgroup G} (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (hroot : Timmesfeld.IsRootInvolutionSet {g : G | IsConj z g})
    (hrootZ : rootGroup {g : G | IsConj z g} z = Z) {f : ℕ} (hf : Nat.card Z = 2 ^ f)
    (h6 : 2 ^ 6 ∣ Nat.card Q) :
    2 ≤ f ∧ Hyp ↥(Subgroup.normalClosure ({z} : Set G)) (classIn z) ∧
      ∃ (t : StatedLieTag) (k : ℕ), TimmesfeldTag t k f ∧
        LieModel ↥(Subgroup.normalClosure ({z} : Set G)) t k 2 f ∧
        ∀ d ∈ classIn z, Nat.card (rootGroup (classIn z) d) = 2 ^ f := by
  classical
  obtain ⟨f₀, k₀, -, hcp⟩ := H.cp
  have hf2 : 2 ≤ f := by
    have h4 := H.q4
    rw [hf] at h4
    by_contra hlt
    push Not at hlt
    interval_cases f <;> norm_num at h4
  have hodd : pPrimeCore 2 G = ⊥ := H.toTim81Hyp.pPrimeCore_eq_bot H.q4
  have hnd : ∃ d e : G, IsConj z d ∧ IsConj z e ∧ orderOf (d * e) = 4 := by
    obtain ⟨d, hd, e, he, h4⟩ := exists_orderOf_mul_eq_four H hz hz1
    exact ⟨d, e, hd, he, h4⟩
  have hHyp := hyp_classIn hroot (isConj_normalClosure H hz hz1) hodd H.o2 hnd
  have hcardroot : Nat.card (rootGroup (classIn z) (selfIn z)) = 2 ^ f := by
    rw [card_rootGroup_classIn]
    show Nat.card (rootGroup {g : G | IsConj z g} z) = 2 ^ f
    rw [hrootZ, hf]
  have hl : ∃ d ∈ classIn z, ∃ e ∈ rootSet (classIn z) d, e ≠ d := by
    refine ⟨selfIn z, IsConj.refl z, ?_⟩
    by_contra hcon
    push Not at hcon
    have hle : rootGroup (classIn z) (selfIn z) ≤ Subgroup.zpowers (selfIn z) := by
      rw [rootGroup, Subgroup.closure_le]
      intro e he
      rw [hcon e he]
      exact Subgroup.mem_zpowers _
    have h1 := Subgroup.card_le_of_le hle
    have hz2 : (selfIn z) ^ 2 = 1 := Subtype.ext (by simpa using sq_eq_one_of_cp hcp z hz)
    have h2 := orderOf_le_of_pow_eq_one (by norm_num) hz2
    rw [hcardroot, Nat.card_zpowers] at h1
    have h3 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    omega
  refine ⟨hf2, hHyp, ?_⟩
  rcases rootOutcome_of_K1NSL hK1 hHyp hl with ⟨t, k, f', -, htag, hL, hroot'⟩ | hU
  · have hff : f' = f := by
      have h1 := hroot' (selfIn z) (IsConj.refl z)
      rw [hcardroot] at h1
      exact (Nat.pow_right_injective (le_refl 2) h1).symm
    rw [hff] at htag hL hroot'
    exact ⟨t, k, htag, hL, hroot'⟩
  · exfalso
    have h5 := factorization_psu_three_three hU
    have hX0 : Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) ≠ 0 := Nat.card_pos.ne'
    have hpow : 2 ^ 6 ∣ Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) :=
      h6.trans (Subgroup.card_dvd_of_le (Q_le_normalClosure H hz hz1))
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hX0).mp hpow
    rw [h5] at hle
    omega

theorem laneB_identify (hK1 : K1NSLStatement) (hK2L : K2PSLStatement2) (hK2S : K2PSpStatement2)
    {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G} (H : StrothHyp M Q Z) {z : G}
    (hz : z ∈ Z) (hz1 : z ≠ 1) (hroot : Timmesfeld.IsRootInvolutionSet {g : G | IsConj z g})
    (hrootZ : rootGroup {g : G | IsConj z g} z = Z) {f : ℕ} (hf : Nat.card Z = 2 ^ f)
    {n N₀ a : ℕ} (hn : (n = 10 ∧ N₀ = 36) ∨ (n = 16 ∧ N₀ = 63) ∨ (n = 28 ∧ N₀ = 120))
    (hQ : Nat.card Q = Nat.card Z ^ (2 * n + 1))
    (hlo : f * N₀ ≤ (Nat.card ↥(Subgroup.normalClosure ({z} : Set G))).factorization 2)
    (hup : (Nat.card ↥(Subgroup.normalClosure ({z} : Set G))).factorization 2 ≤ f * N₀ + a)
    (ha : a < 3 * f) :
    ∃ t : StatedLieTag, LieModel ↥(Subgroup.normalClosure ({z} : Set G)) t 0 2 f ∧
      ((n = 10 ∧ (t = .E6 ∨ t = .twistedE6)) ∨ (n = 16 ∧ t = .E7) ∨ (n = 28 ∧ t = .E8)) := by
  have hf2' : 2 ≤ f := by
    have h4 := H.q4
    rw [hf] at h4
    by_contra hlt
    push Not at hlt
    interval_cases f <;> norm_num at h4
  have hn10 : 10 ≤ n := by omega
  have h6 : 2 ^ 6 ∣ Nat.card Q := by
    rw [hQ, hf, ← pow_mul]
    exact pow_dvd_pow 2 (by nlinarith)
  obtain ⟨hf2, hHyp, t, k, htag, hL, hroot'⟩ := rootOutcome_classIn hK1 H hz hz1 hroot hrootZ hf h6
  have hv := factorization_two_card_of_lieModel (by omega) htag hL
  have hlo' : N₀ ≤ Smith219Arith.sylowExp t k := by
    rw [hv] at hlo
    exact Nat.le_of_mul_le_mul_left hlo (by omega)
  have hhi' : Smith219Arith.sylowExp t k ≤ N₀ + 2 := by
    rw [hv] at hup
    exact Smith219Arith.le_add_two_of_mul_le (f := f) hup ha
  have hQ' : (2 ^ f) ^ (2 * n + 1) ≤ Nat.card (pCoreOf 2 (Subgroup.centralizer
      ({selfIn z} : Set ↥(Subgroup.normalClosure ({z} : Set G))))) := by
    have h1 := card_Q_le_pCoreOf H hz hz1
    rwa [hQ, hf] at h1
  have hq1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
  have hPSL : t = .PSL → n + 2 ≤ k := by
    rintro rfl
    have hk : 3 ≤ k := by simpa [TimmesfeldTag] using htag
    have hO := hK2L _ _ k f hHyp hk (by omega) hL hroot' (selfIn z) (IsConj.refl z)
    have hw : 2 * n + 1 ≤ 2 * k - 3 := (Nat.pow_le_pow_iff_right hq1).mp (hQ'.trans hO)
    omega
  have hPSp : t = .PSp → n + 3 ≤ 2 * k := by
    rintro rfl
    have hk : 3 ≤ k := by simpa [TimmesfeldTag] using htag
    rcases hK2S _ _ k f hHyp hk (by omega) hL hroot' (selfIn z) (IsConj.refl z) with hO | ⟨hO, -⟩
    · have hw : 2 * n + 1 ≤ 2 * k - 1 := (Nat.pow_le_pow_iff_right hq1).mp (hQ'.trans hO)
      omega
    · have hw : 2 * n + 1 ≤ 4 * k - 5 := (Nat.pow_le_pow_iff_right hq1).mp (hQ'.trans hO)
      omega
  have hres := Smith219Arith.laneB_window hn hlo' hhi' hPSL hPSp
  have hk0 : k = 0 := by
    rcases hres with ⟨-, rfl | rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
      simpa [TimmesfeldTag] using htag
  subst hk0
  exact ⟨t, hL, hres⟩

theorem smith219EInspectionE4_of (hNf : Smith212ENonfusedStatement) (hSt : Stroth1980Rel)
    (hX4 : SubConfigE4Statement) (hK1 : K1NSLStatement) (hK2L : K2PSLStatement2)
    (hK2S : K2PSpStatement2) : Smith219EInspectionE4Statement := by
  intro G _ _ M Q Z B IH hc hcase hroot _
  obtain ⟨t₀, hD4, h4⟩ := hcase
  have H := hc.ctx.hyp
  obtain ⟨z, hz, hz1, -⟩ := exists_mem_Z_ne H 1
  obtain ⟨hN, f, hf, hLF⟩ := lieModel_of_caseE4_recursion IH (hSt _ IH.1) hX4 hc hD4 h4
  haveI := hN
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := H.q4
      rw [hf] at this
      norm_num at this
    · exact h
  have hFv := factorization_two_card_of_lieModel hf1
    (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, by norm_num⟩)) : TimmesfeldTag .POmegaPlus 6 f) hLF
  have hsyl : Smith219Arith.sylowExp .POmegaPlus 6 = 30 := rfl
  rw [hsyl] at hFv
  have hS := isSimpleGroup_of_lieModel hLF
  have hF0 : Nat.card (FStar (SubCfgGroup M Q Z)) ≠ 0 := Nat.card_pos.ne'
  have h4F : 4 ∣ Nat.card (FStar (SubCfgGroup M Q Z)) := by
    have h := Nat.ordProj_dvd (Nat.card (FStar (SubCfgGroup M Q Z))) 2
    rw [hFv] at h
    exact (pow_dvd_pow 2 (by nlinarith : 2 ≤ f * 30)).trans h
  have hC := centralizer_fstar_eq_bot hS h4F
  have hOut : (Nat.card (Outer (FStar (SubCfgGroup M Q Z)))).factorization 2 ≤
      2 + f.factorization 2 := by
    have h := (LocalAnalysis.ComponentInitial.orthogonal_model_outer_two_part_bound _ .POmegaPlus
      (Or.inr (Or.inl rfl)) 6 2 f (hLF.statedClassicalModel (by decide))).2.2.1 rfl
    have h' : 2 ^ (Nat.card (Outer (FStar (SubCfgGroup M Q Z)))).factorization 2 ≤
        2 ^ (2 + f.factorization 2) := by
      rw [pow_add]
      exact h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h'
  have hO0 : Nat.card (Outer (FStar (SubCfgGroup M Q Z))) ≠ 0 := Nat.card_pos.ne'
  have hQ0 : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hH0 : (Nat.card (H0 M Z)).factorization 2 ≤ f * 33 + (2 + f.factorization 2) + f * 30 := by
    have h := (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
      (mul_ne_zero hQ0 (mul_ne_zero hO0 hF0))).mpr (card_H0_dvd_of_fstar hc.ctx hC) 2
    rw [Nat.factorization_mul hQ0 (mul_ne_zero hO0 hF0), Finsupp.add_apply,
      Nat.factorization_mul hO0 hF0, Finsupp.add_apply, hFv, h4.1, hf, ← pow_mul,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at h
    omega
  have hG : (Nat.card G).factorization 2 ≤ f * 63 + (2 * f.factorization 2 + 2) := by
    have h1 := factorization_relIndex_H0_le H hf
    rw [← factorization_card_M_eq H]
    have hHM : H0 M Z ≤ M := inf_le_left
    have hrel := Subgroup.relIndex_mul_card (H := H0 M Z) (K := M)
    rw [inf_eq_left.mpr hHM] at hrel
    have hr0 : (H0 M Z).relIndex M ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hrel
      exact Nat.card_pos.ne' hrel.symm
    rw [← hrel, Nat.factorization_mul hr0 Nat.card_pos.ne', Finsupp.add_apply]
    omega
  have hLBL : LB M Q B ≤ Lgen M (LB M Q B) := by
    calc LB M Q B = conjSubgroup 1 (LB M Q B) := (conjSubgroup_one _).symm
      _ ≤ Lgen M (LB M Q B) :=
        le_iSup₂ (f := fun m (_ : m ∈ M) => conjSubgroup m (LB M Q B)) 1 M.one_mem
  have hLQ : ¬ Lgen M (LB M Q B) ≤ Q := fun h => hD4.2.2.1 (h (hLBL hD4.2.1))
  have hdvdX := (card_mul_card_fstar_dvd hc.ctx hS hLQ hz hz1).trans
    (Subgroup.card_subgroup_dvd_card _)
  have hX0 : Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) ≠ 0 := Nat.card_pos.ne'
  have hlo : f * 63 ≤ (Nat.card ↥(Subgroup.normalClosure ({z} : Set G))).factorization 2 := by
    have h := (Nat.factorization_le_iff_dvd (mul_ne_zero hQ0 hF0) hX0).mpr hdvdX 2
    rw [Nat.factorization_mul hQ0 hF0, Finsupp.add_apply, hFv, h4.1, hf, ← pow_mul,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at h
    omega
  have hup : (Nat.card ↥(Subgroup.normalClosure ({z} : Set G))).factorization 2 ≤
      f * 63 + (2 * f.factorization 2 + 2) :=
    le_trans ((Nat.factorization_le_iff_dvd hX0 Nat.card_pos.ne').mpr
      (Subgroup.card_subgroup_dvd_card _) 2) hG
  have hv2 := factorization_two_lt f hf1
  obtain ⟨t, hL, hres⟩ := laneB_identify hK1 hK2L hK2S H hz hz1 (hroot z hz hz1)
    (rootGroup_eq_Z_E_of_nonfused hNf IH hc hz hz1) hf (Or.inr (Or.inl ⟨rfl, rfl⟩))
    (by rw [h4.1]) hlo hup (by
      have h3 : 2 ≤ f := by
        have h4' := H.q4
        rw [hf] at h4'
        by_contra hlt
        push Not at hlt
        interval_cases f <;> norm_num at h4'
      omega)
  rcases hres with ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨h, -⟩
  · omega
  · obtain ⟨hF, -⟩ := generalizedFitting_eq_normalClosure H hz hz1
    exact ⟨f, hf, LieModel.of_mulEquiv (MulEquiv.subgroupCongr hF.symm) hL⟩
  · omega

theorem smith219EInspectionE5_of (hNf : Smith212ENonfusedStatement) (hSt : Stroth1980Rel)
    (hX5 : SubConfigE5Statement) (hK1 : K1NSLStatement) (hK2L : K2PSLStatement2)
    (hK2S : K2PSpStatement2) : Smith219EInspectionE5Statement := by
  intro G _ _ M Q Z B IH hc hcase hroot _
  obtain ⟨t₀, hD4, h5⟩ := hcase
  have H := hc.ctx.hyp
  obtain ⟨z, hz, hz1, -⟩ := exists_mem_Z_ne H 1
  obtain ⟨hN, f, hf, hLF⟩ := lieModel_of_caseE5_recursion IH (hSt _ IH.1) hX5 hc hD4 h5
  haveI := hN
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have := H.q4
      rw [hf] at this
      norm_num at this
    · exact h
  have hFv := factorization_two_card_of_lieModel hf1
    (by simp [TimmesfeldTag] : TimmesfeldTag .E7 0 f) hLF
  have hsyl : Smith219Arith.sylowExp .E7 0 = 63 := rfl
  rw [hsyl] at hFv
  have hS := isSimpleGroup_of_lieModel hLF
  have hF0 : Nat.card (FStar (SubCfgGroup M Q Z)) ≠ 0 := Nat.card_pos.ne'
  have h4F : 4 ∣ Nat.card (FStar (SubCfgGroup M Q Z)) := by
    have h := Nat.ordProj_dvd (Nat.card (FStar (SubCfgGroup M Q Z))) 2
    rw [hFv] at h
    exact (pow_dvd_pow 2 (by nlinarith : 2 ≤ f * 63)).trans h
  have hC := centralizer_fstar_eq_bot hS h4F
  have hOut : (Nat.card (Outer (FStar (SubCfgGroup M Q Z)))).factorization 2 ≤
      1 + f.factorization 2 := by
    have h := (LieType.Chevalley.ordinary_exceptional_model_outer_two_part_bound _ .E7 2 f
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (hLF.chevalleyExceptionalModel (by decide))).1
    have h' : 2 ^ (Nat.card (Outer (FStar (SubCfgGroup M Q Z)))).factorization 2 ≤
        2 ^ (1 + f.factorization 2) := by
      rw [pow_add, pow_one]
      exact h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h'
  have hO0 : Nat.card (Outer (FStar (SubCfgGroup M Q Z))) ≠ 0 := Nat.card_pos.ne'
  have hQ0 : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  have hH0 : (Nat.card (H0 M Z)).factorization 2 ≤ f * 57 + (1 + f.factorization 2) + f * 63 := by
    have h := (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
      (mul_ne_zero hQ0 (mul_ne_zero hO0 hF0))).mpr (card_H0_dvd_of_fstar hc.ctx hC) 2
    rw [Nat.factorization_mul hQ0 (mul_ne_zero hO0 hF0), Finsupp.add_apply,
      Nat.factorization_mul hO0 hF0, Finsupp.add_apply, hFv, h5.1, hf, ← pow_mul,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at h
    omega
  have hG : (Nat.card G).factorization 2 ≤ f * 120 + (2 * f.factorization 2 + 1) := by
    have h1 := factorization_relIndex_H0_le H hf
    rw [← factorization_card_M_eq H]
    have hHM : H0 M Z ≤ M := inf_le_left
    have hrel := Subgroup.relIndex_mul_card (H := H0 M Z) (K := M)
    rw [inf_eq_left.mpr hHM] at hrel
    have hr0 : (H0 M Z).relIndex M ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hrel
      exact Nat.card_pos.ne' hrel.symm
    rw [← hrel, Nat.factorization_mul hr0 Nat.card_pos.ne', Finsupp.add_apply]
    omega
  have hLBL : LB M Q B ≤ Lgen M (LB M Q B) := by
    calc LB M Q B = conjSubgroup 1 (LB M Q B) := (conjSubgroup_one _).symm
      _ ≤ Lgen M (LB M Q B) :=
        le_iSup₂ (f := fun m (_ : m ∈ M) => conjSubgroup m (LB M Q B)) 1 M.one_mem
  have hLQ : ¬ Lgen M (LB M Q B) ≤ Q := fun h => hD4.2.2.1 (h (hLBL hD4.2.1))
  have hdvdX := (card_mul_card_fstar_dvd hc.ctx hS hLQ hz hz1).trans
    (Subgroup.card_subgroup_dvd_card _)
  have hX0 : Nat.card ↥(Subgroup.normalClosure ({z} : Set G)) ≠ 0 := Nat.card_pos.ne'
  have hlo : f * 120 ≤ (Nat.card ↥(Subgroup.normalClosure ({z} : Set G))).factorization 2 := by
    have h := (Nat.factorization_le_iff_dvd (mul_ne_zero hQ0 hF0) hX0).mpr hdvdX 2
    rw [Nat.factorization_mul hQ0 hF0, Finsupp.add_apply, hFv, h5.1, hf, ← pow_mul,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at h
    omega
  have hup : (Nat.card ↥(Subgroup.normalClosure ({z} : Set G))).factorization 2 ≤
      f * 120 + (2 * f.factorization 2 + 1) :=
    le_trans ((Nat.factorization_le_iff_dvd hX0 Nat.card_pos.ne').mpr
      (Subgroup.card_subgroup_dvd_card _) 2) hG
  have hv2 := factorization_two_lt f hf1
  obtain ⟨t, hL, hres⟩ := laneB_identify hK1 hK2L hK2S H hz hz1 (hroot z hz hz1)
    (rootGroup_eq_Z_E_of_nonfused hNf IH hc hz hz1) hf (Or.inr (Or.inr ⟨rfl, rfl⟩))
    (by rw [h5.1]) hlo hup (by omega)
  rcases hres with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, rfl⟩
  · omega
  · omega
  · obtain ⟨hF, -⟩ := generalizedFitting_eq_normalClosure H hz hz1
    exact ⟨f, hf, LieModel.of_mulEquiv (MulEquiv.subgroupCongr hF.symm) hL⟩

theorem smith219EInspection_of (hNf : Smith212ENonfusedStatement) (hSt : Stroth1980Rel)
    (hX4 : SubConfigE4Statement) (hX5 : SubConfigE5Statement) (hK1 : K1NSLStatement)
    (hK2L : K2PSLStatement2) (hK2S : K2PSpStatement2) : Smith219EInspectionStatement :=
  smith219EInspection_of_cases (smith219EInspectionE3U_of hNf hK1 hK2L hK2S)
    (smith219EInspectionE3L_of hNf hK1 hK2L hK2S)
    (smith219EInspectionE4_of hNf hSt hX4 hK1 hK2L hK2S)
    (smith219EInspectionE5_of hNf hSt hX5 hK1 hK2L hK2S)

end CFSG.RankThree.GF2n.Smith81.Insp
