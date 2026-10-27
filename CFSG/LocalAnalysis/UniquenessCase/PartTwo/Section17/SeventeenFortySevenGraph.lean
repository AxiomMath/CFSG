module

public import CFSG.GroupTheory.CommutatorCentralizerInNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySevenTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.TenFiveBridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20n
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20u
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SL3TwoAutPowerMap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenElevenStepsA
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214g
public import CFSG.GroupTheory.PerfectCentralSylow
public import CFSG.GroupTheory.OddCentralQuotient
public import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.GroupTheory
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
open CFSG.Quasithin (IsSylowIn)
open CFSG.LargeExtraspecial.S5 (IsSylowTwoIn)
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s17_47_powerMap_of_not_swaps (hK : Inputs1719.K_SL3TwoAutPowerMap) {D : Data G}
    {L : Subgroup G} {n : ℕ} (hL : L ∈ calC D.M) (hTL : D.T ≤ normalizer (L : Set G))
    (hSL : IsSL3 (Bar2 L) n) (hns : ¬ SwapsParabolics D.T L) :
    ∀ t ∈ D.T, ∃ j : ℕ, ∀ b ∈ L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G),
      t * b * t⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ D.T ⊓ L := by
  intro t ht
  have hT2 : IsPGroup 2 D.T := (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM).2.1
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ L) L :=
    isSylowTwoOf_inf_of_mem_calC hL
  have hTU : D.T ≤ normalizer ((D.T ⊓ L : Subgroup G) : Set G) :=
    (le_inf (Subgroup.le_normalizer (H := D.T)) hTL).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  let m : ↥(normalizer (L : Set G)) := ⟨t, hTL ht⟩
  obtain ⟨j, hj⟩ := hK (Bar2 L) n hSL uc22p22l_odd_center_quotient (sylowBar2 L (D.T ⊓ L))
    (isSylowTwoOf_sylowBar2_of hSyl) (UC6S846.rhoL L m)
    (exists_rhoL_pow_two_pow_eq_one hT2 m ht) (rhoL_map_sylowBar2 m (hTU ht))
    (rhoL_map_eq_of_not_swaps hns m ht)
  exact ⟨j, powerMap_lift_of_rhoL hSyl m hj⟩

theorem s17_47_exists_T0_of_powerMap {D : Data G} {L : Subgroup G}
    (hTL : D.T ≤ normalizer (L : Set G))
    (hpow : ∀ t ∈ D.T, ∃ j : ℕ, ∀ b ∈ L ⊓ normalizer ((D.T ⊓ L : Subgroup G) : Set G),
      t * b * t⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ D.T ⊓ L)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {E : Subgroup G} (hEL : E ≤ L)
    (hEN : E ≤ normalizer ((D.T ⊓ L : Subgroup G) : Set G))
    (hEexp : ∀ e ∈ E, e ^ r = 1) (hperm : Permutes E D.T) :
    ∃ T₀ : Subgroup G, T₀ ≤ D.T ∧ D.T ≤ normalizer (T₀ : Set G) ∧
      E ≤ normalizer (T₀ : Set G) ∧
        ∀ v ∈ D.T, ∀ w ∈ D.T, v ^ 2 = 1 → w ^ 2 = 1 → v ∉ T₀ → w ∉ T₀ →
          v * w⁻¹ ∈ T₀ := by
  classical
  have hTS : D.T ≤ normalizer ((D.T ⊓ L : Subgroup G) : Set G) :=
    uc22p20u_T_le_normalizer_inf D hTL
  have hcoe : ((E ⊔ D.T : Subgroup G) : Set G) = (E : Set G) * (D.T : Set G) :=
    uc22p20n_coe_sup_of_perm hperm
  refine ⟨commutatorCentralizerIn D.T (D.T ⊓ L) E hTS, commutatorCentralizerIn_le _ _ _ hTS,
    le_normalizer_commutatorCentralizerIn hTS hEN (le_normalizer_sup_inf_of_permutes hEL hTL hcoe),
    le_normalizer_commutatorCentralizerIn_of_le hTS inf_le_left hEN, ?_⟩
  intro v hv w hw hv2 hw2 hvT₀ hwT₀
  set H : Subgroup G := D.T ⊓ L with hHdef
  have hH2 : IsPGroup 2 ↥H := D.sylowM.isPGroup.to_le inf_le_left
  set N : Subgroup G := E ⊔ D.T with hNdef
  have hHN : H ≤ N := inf_le_left.trans le_sup_right
  have hHnorm : N ≤ Subgroup.normalizer (H : Set G) := sup_le hEN hTS
  have : (H.subgroupOf N).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHnorm
  have hkey : ∀ u ∈ D.T, u ^ 2 = 1 →
      u ∉ commutatorCentralizerIn D.T (D.T ⊓ L) E hTS →
      ∃ j : ℕ, r ∣ 2 ^ j + 1 ∧ ∀ e ∈ E, u * e * u⁻¹ * e ∈ H := by
    intro u hu hu2 huT₀
    obtain ⟨j, hj⟩ := hpow u hu
    have hex : ∃ e ∈ E, ⁅u, e⁆ ∉ H := by
      by_contra hcon
      refine huT₀ ((mem_commutatorCentralizerIn hTS).2 ⟨hu, fun e he => ?_⟩)
      by_contra h'
      exact hcon ⟨e, he, h'⟩
    obtain ⟨e₀, he₀E, he₀c⟩ := hex
    have he₀ne : e₀ ≠ 1 := by
      rintro rfl
      exact he₀c (by simp)
    have huN : u ∈ N := by
      rw [hNdef]
      exact Subgroup.mem_sup_right hu
    have heN : ∀ e ∈ E, e ∈ N := by
      intro e he
      rw [hNdef]
      exact Subgroup.mem_sup_left he
    let Q := ↥N ⧸ (H.subgroupOf N)
    let π : ↥N →* Q := QuotientGroup.mk' (H.subgroupOf N)
    let uN : ↥N := ⟨u, huN⟩
    let e₀N : ↥N := ⟨e₀, heN e₀ he₀E⟩
    have hπH : ∀ (x : G) (hx : x ∈ N), x ∈ H → π ⟨x, hx⟩ = 1 :=
      fun x hx hxH => (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hxH)
    have hπe₀ : π e₀N ≠ 1 := by
      intro h1
      have he₀H : e₀ ∈ H :=
        Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
      exact he₀c (by
        rw [commutatorElement_def]
        exact H.mul_mem ((Subgroup.mem_normalizer_iff.1 (hTS hu) e₀).1 he₀H)
          (H.inv_mem he₀H))
    have : Fact (Nat.Prime r) := ⟨hr⟩
    have hπord : orderOf (π e₀N) = r := by
      have hordN : orderOf e₀N = r := by
        rw [← Subgroup.orderOf_coe e₀N]
        exact orderOf_eq_prime (hEexp e₀ he₀E) he₀ne
      have hdvd : orderOf (π e₀N) ∣ r := by
        have h := orderOf_map_dvd π e₀N
        rwa [hordN] at h
      rcases (Nat.dvd_prime hr).mp hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hπe₀
      · exact h1
    have hrel : ∀ (e : G) (he : e ∈ E),
        π (uN * ⟨e, heN e he⟩ * uN⁻¹) = (π ⟨e, heN e he⟩) ^ 2 ^ j := by
      intro e he
      have hmem : u * e * u⁻¹ * (e ^ 2 ^ j)⁻¹ ∈ H := hj e ⟨hEL he, hEN he⟩
      have h1' : π (uN * ⟨e, heN e he⟩ * uN⁻¹ * (⟨e, heN e he⟩ ^ 2 ^ j)⁻¹) = 1 := by
        have heq : uN * ⟨e, heN e he⟩ * uN⁻¹ * (⟨e, heN e he⟩ ^ 2 ^ j)⁻¹ =
            (⟨u * e * u⁻¹ * (e ^ 2 ^ j)⁻¹, hHN hmem⟩ : ↥N) := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, uN]
        rw [heq]
        exact hπH _ _ hmem
      have h2 : π (uN * ⟨e, heN e he⟩ * uN⁻¹) * ((π ⟨e, heN e he⟩) ^ 2 ^ j)⁻¹ =
          1 := by
        simpa only [map_mul, map_inv, map_pow] using h1'
      exact mul_inv_eq_one.mp h2
    have huN2 : uN * uN = 1 := by
      apply Subtype.ext
      simpa [uN, pow_two] using hu2
    have huNinv : uN⁻¹ = uN := inv_eq_of_mul_eq_one_left huN2
    have h4pow : 4 ^ j = 2 ^ j * 2 ^ j := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, two_mul, ← pow_add]
    have h4j : (π e₀N) ^ (4 ^ j) = π e₀N := by
      have hrel' : π uN * π e₀N * (π uN)⁻¹ = (π e₀N) ^ 2 ^ j := by
        simpa only [map_mul, map_inv] using hrel e₀ he₀E
      have harg : uN * (uN * e₀N * uN⁻¹) * uN⁻¹ = e₀N := by
        rw [huNinv]
        calc uN * (uN * e₀N * uN) * uN = (uN * uN) * e₀N * (uN * uN) := by group
          _ = 1 * e₀N * 1 := by rw [huN2]
          _ = e₀N := by group
      have h1 : π e₀N = π uN * (π e₀N) ^ 2 ^ j * (π uN)⁻¹ := by
        calc π e₀N = π (uN * (uN * e₀N * uN⁻¹) * uN⁻¹) := by rw [harg]
          _ = π uN * π (uN * e₀N * uN⁻¹) * (π uN)⁻¹ := by
              simp only [map_mul, map_inv]
          _ = π uN * (π e₀N) ^ 2 ^ j * (π uN)⁻¹ := by rw [hrel e₀ he₀E]
      calc (π e₀N) ^ (4 ^ j)
          = ((π e₀N) ^ 2 ^ j) ^ 2 ^ j := by rw [h4pow, pow_mul]
        _ = (π uN * π e₀N * (π uN)⁻¹) ^ 2 ^ j := by rw [← hrel']
        _ = π uN * (π e₀N) ^ 2 ^ j * (π uN)⁻¹ := by rw [conj_pow]
        _ = π e₀N := h1.symm
    have hdvd4 : r ∣ 4 ^ j - 1 := by
      have hmod4 : 4 ^ j ≡ 1 [MOD r] := by
        have h := pow_eq_pow_iff_modEq.mp (show (π e₀N) ^ (4 ^ j) = (π e₀N) ^ 1 by
          simpa using h4j)
        rwa [hπord] at h
      have hpos : 1 ≤ 4 ^ j := by
        have h : 0 < 4 ^ j := by positivity
        omega
      exact (Nat.modEq_iff_dvd' hpos).mp hmod4.symm
    have hnotdvd : ¬ r ∣ 2 ^ j - 1 := by
      intro hdvd
      have he₀ord : orderOf e₀ = r := orderOf_eq_prime (hEexp e₀ he₀E) he₀ne
      have hmod : 2 ^ j ≡ 1 [MOD orderOf e₀] := by
        rw [he₀ord]
        have hpos : 1 ≤ 2 ^ j := by
          have h : 0 < 2 ^ j := by positivity
          omega
        exact ((Nat.modEq_iff_dvd' hpos).mpr hdvd).symm
      have heq : e₀ ^ 2 ^ j = e₀ := by
        have h : e₀ ^ 2 ^ j = e₀ ^ 1 := by
          rw [pow_eq_pow_iff_modEq]
          simpa using hmod
        simpa using h
      have h1 : u * e₀ * u⁻¹ * (e₀ ^ 2 ^ j)⁻¹ ∈ H := hj e₀ ⟨hEL he₀E, hEN he₀E⟩
      exact he₀c (by simpa [commutatorElement_def, heq] using h1)
    have hdvdAdd : r ∣ 2 ^ j + 1 := by
      have h4eq : 4 ^ j - 1 = (2 ^ j + 1) * (2 ^ j - 1) := by
        have h4 : (4 : ℕ) ^ j = (2 ^ j) ^ 2 := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, two_mul, pow_add, pow_two]
        rw [h4]
        simpa using Nat.sq_sub_sq (2 ^ j) 1
      rw [h4eq] at hdvd4
      rcases (Nat.Prime.dvd_mul hr).mp hdvd4 with h | h
      · exact h
      · exact absurd h hnotdvd
    refine ⟨j, hdvdAdd, fun e he => ?_⟩
    have hmem1 : u * e * u⁻¹ * (e ^ 2 ^ j)⁻¹ ∈ H := hj e ⟨hEL he, hEN he⟩
    have hepow : e ^ (2 ^ j + 1) = 1 := by
      obtain ⟨k, hk⟩ := hdvdAdd
      rw [hk, pow_mul, hEexp e he, one_pow]
    have hfinal : u * e * u⁻¹ * e = u * e * u⁻¹ * (e ^ 2 ^ j)⁻¹ := by
      have h1 : e ^ 2 ^ j * e = 1 := by rw [← pow_succ]; exact hepow
      have h2 : e ^ 2 ^ j = e⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [h2]
      group
    rw [hfinal]
    exact hmem1
  obtain ⟨jv, -, hvprod⟩ := hkey v hv hv2 hvT₀
  obtain ⟨jw, -, hwprod⟩ := hkey w hw hw2 hwT₀
  refine mul_inv_mem_commutatorCentralizerIn hTS hv hw hv2 hw2 (fun e he => ?_)
  have h1 : v * e * v⁻¹ * e ∈ H := hvprod e he
  have h2 : w * e * w⁻¹ * e ∈ H := hwprod e he
  have e1 : v * e * v⁻¹ = (v * e * v⁻¹ * e) * e⁻¹ := by group
  have e2 : w * e * w⁻¹ = (w * e * w⁻¹ * e) * e⁻¹ := by group
  have e3 : ((v * e * v⁻¹ * e) * e⁻¹) * (((w * e * w⁻¹ * e) * e⁻¹))⁻¹ =
      (v * e * v⁻¹ * e) * (w * e * w⁻¹ * e)⁻¹ := by group
  rw [e1, e2, e3]
  exact H.mul_mem h1 (H.inv_mem h2)

theorem isSL3_barSub_of_isL3_barInf {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥) {n : ℕ}
    (hL3 : IsL3 (BarInf L) n) : IsSL3 ↥(barSub V₀ V h.isElemAbelian L) n := by
  obtain ⟨e⟩ := barSub_centerQuot_equiv_barInf h hL hL1
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  have : Nontrivial ↥(barSub V₀ V h.isElemAbelian L) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hL1
  exact ⟨uc22br4_isQuasisimple_of_surjective hq (barSubBar2HomOfHyp125 h hL)
    (barSubBar2HomOfHyp125_surjective h hL), LieModel.of_mulEquiv e hL3⟩

theorem swapsParabolics_barSub_of_calC {D : Data G} {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hMN : D.M ≤ normalizer (L : Set G))
    (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥) (hswap : SwapsParabolics D.T L) :
    SwapsParabolics (barSub V₀ V h.isElemAbelian D.T) (barSub V₀ V h.isElemAbelian L) := by
  classical
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  obtain ⟨-, -, -, -, hMnorm, hMnorm₀, -⟩ := h.pairFacts
  have hMstab : D.M ≤ stabTil V₀ V := le_stabTil hMnorm hMnorm₀
  have hLstab : L ≤ stabTil V₀ V := hL.1.le.trans hMstab
  have hTstab : D.T ≤ stabTil V₀ V := D.sylowM.le.trans hMstab
  have hTsyl : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM
  have hSsyl : IsSylowIn 2 (D.T ⊓ L) L :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp
      (CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer D.sylowM hL.1.le hMN)
  have hLnorm : (L.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).mpr hMN
  have hConj : conjClosure D.M L = L := uc22p2214_conjClosure_eq_of_normal hL.1.le hLnorm
  have hTnormS : D.T ≤ Subgroup.normalizer ((D.T ⊓ L : Subgroup G) : Set G) :=
    uc22p20u_T_le_normalizer_inf D (D.sylowM.le.trans hMN)
  have hO2le : pCoreOf 2 L ≤ D.T ⊓ L := by
    have hO2normal : ((pCoreOf 2 L).subgroupOf L).Normal := by
      rw [Subgroup.normal_subgroupOf_iff (CFSG.LieType.BorelTits.pCoreOf_le 2 L)]
      intro a b ha hb
      exact CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf hb ha
    exact hSsyl.le_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hO2normal
      (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 L)
  let q : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hO2Lbot : barSub V₀ V hV (pCoreOf 2 L) = ⊥ :=
    TwelveTwentyThree.barSub_pCoreOf_eq_bot_of_isSubnormal hV hL.1
      (barSub_pCoreOf_eq_bot_of_hyp125 h)
  let ψ' : ↥L →* ↥(barSub V₀ V hV L) :=
    ((actTil V₀ V hV).comp (Subgroup.inclusion hLstab)).codRestrict
      (barSub V₀ V hV L) (fun x => actTil_mem_barSub V₀ V hV x.2 (hLstab x.2))
  have hψ'ker : CFSG.pCore 2 ↥L ≤ ψ'.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxP : (x : G) ∈ pCoreOf 2 L := by
      rw [← CFSG.openPCoreOf_subgroupOf 2 L] at hx
      exact Subgroup.mem_subgroupOf.mp hx
    apply Subtype.ext
    have h1 : actTil V₀ V hV ⟨(x : G), hLstab x.2⟩ ∈ barSub V₀ V hV (pCoreOf 2 L) :=
      actTil_mem_barSub V₀ V hV hxP (hLstab x.2)
    rw [hO2Lbot, Subgroup.mem_bot] at h1
    exact h1
  let φ : Bar2 L →* ↥(barSub V₀ V hV L) := QuotientGroup.lift (CFSG.pCore 2 ↥L) ψ' hψ'ker
  have hφmk : ∀ x : ↥L, φ (QuotientGroup.mk x) = ψ' x := fun x =>
    QuotientGroup.lift_mk (CFSG.pCore 2 ↥L) hψ'ker x
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨a, haL, hay⟩ := (mem_barSub V₀ V hV L (y : MulAut (Vtil V₀ V hV))).1 y.2
    refine ⟨QuotientGroup.mk ⟨a, haL⟩, ?_⟩
    apply Subtype.ext
    show actTil V₀ V hV ⟨a, hLstab haL⟩ = (y : MulAut (Vtil V₀ V hV))
    exact hay
  have hφker : φ.ker ≤ Subgroup.center (Bar2 L) := by
    have : Nontrivial ↥(barSub V₀ V hV L) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hL1
    have hne : ∃ k, φ k ≠ 1 := by
      obtain ⟨y, hy⟩ := exists_ne (1 : ↥(barSub V₀ V hV L))
      obtain ⟨k, hk⟩ := hφsurj y
      exact ⟨k, by rw [hk]; exact hy⟩
    exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
      ((CFSG.Foundations.SteinbergCA.quasisimple_iff (Bar2 L)).2.2.1.mpr hL.2.2) hne
  have : φ.ker.Normal := Subgroup.normal_of_le_center hφker
  have hφodd : Odd (Nat.card ↥φ.ker) := by
    have hc : Odd (Nat.card ↥(Subgroup.center (Bar2 L))) := uc22p22l_odd_center_quotient
    have hdvd : Nat.card ↥φ.ker ∣ Nat.card ↥(Subgroup.center (Bar2 L)) := by
      have h1 := Subgroup.card_subgroup_dvd_card (φ.ker.subgroupOf (Subgroup.center (Bar2 L)))
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hφker).toEquiv] at h1
    exact hc.of_dvd_nat hdvd
  have hinf : barSub V₀ V hV D.T ⊓ barSub V₀ V hV L =
      barSub V₀ V hV (D.T ⊓ L) := by
    have h1 := EighteenElevenTransport.barSub_inf_eq (D := D) (V₀ := V₀) (V := V) hV hMstab
      hTsyl (L := L) (hConj.symm ▸ hL.1.le) (hConj.symm ▸ hLnorm)
    rwa [hConj] at h1
  let ψ : ↥L →* MulAut (Vtil V₀ V hV) := (actTil V₀ V hV).comp (Subgroup.inclusion hLstab)
  have hψfac : ∀ x : ↥L, ψ x = (φ (q x) : MulAut (Vtil V₀ V hV)) := by
    intro x
    show actTil V₀ V hV ⟨(x : G), hLstab x.2⟩ = (φ (QuotientGroup.mk x) : MulAut _)
    rw [hφmk x]
    rfl
  have hbase : ∀ H' : Subgroup G, H' ≤ L → (H'.subgroupOf L).map ψ = barSub V₀ V hV H' := by
    intro H' hH'
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact actTil_mem_barSub V₀ V hV hz (hLstab (hH' hz))
    · intro hy
      obtain ⟨a, haH, hay⟩ := (mem_barSub V₀ V hV H' y).1 hy
      exact ⟨⟨a, hH' haH⟩, Subgroup.mem_subgroupOf.mpr haH, hay⟩
  have hqkerZ : (ψ.ker).map q ≤ Subgroup.center (Bar2 L) := by
    rintro y ⟨x, hx, rfl⟩
    have hx1 : ψ x = 1 := MonoidHom.mem_ker.mp hx
    exact hφker (MonoidHom.mem_ker.mpr (Subtype.ext ((hψfac x).symm.trans hx1)))
  have hSylB : sylowBar2 L (D.T ⊓ L) = ((D.T ⊓ L).subgroupOf L).map q := rfl
  have hcomapB : Subgroup.comap q (sylowBar2 L (D.T ⊓ L)) = (D.T ⊓ L).subgroupOf L := by
    rw [hSylB, Subgroup.comap_map_eq_self]
    rw [QuotientGroup.ker_mk', ← CFSG.openPCoreOf_subgroupOf 2 L]
    exact Subgroup.subgroupOf_mono L hO2le
  have hqNiff : ∀ x : ↥L, q x ∈ Subgroup.normalizer ((sylowBar2 L (D.T ⊓ L)) : Set (Bar2 L)) ↔
      (x : G) ∈ Subgroup.normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
    intro x
    constructor
    · intro hx
      have hmap : (D.T ⊓ L).map (MulAut.conj (x : G)).toMonoidHom ≤ D.T ⊓ L := by
        rintro y ⟨u, hu, rfl⟩
        have huS : (u : G) ∈ D.T ⊓ L := hu
        have huL : (u : G) ∈ L := huS.2
        have hmem : q ⟨(x : G) * u * (x : G)⁻¹,
            L.mul_mem (L.mul_mem x.2 huL) (L.inv_mem x.2)⟩ ∈ sylowBar2 L (D.T ⊓ L) := by
          have hqconj : q ⟨(x : G) * u * (x : G)⁻¹,
              L.mul_mem (L.mul_mem x.2 huL) (L.inv_mem x.2)⟩ =
              (MulAut.conj (q x)).toMonoidHom (q ⟨u, huL⟩) := by
            show q ⟨(x : G) * u * (x : G)⁻¹, _⟩ = q x * q ⟨u, huL⟩ * (q x)⁻¹
            rw [← map_mul, ← map_inv, ← map_mul]
            congr 1
          rw [hqconj]
          exact (Subgroup.mem_normalizer_iff.1 hx (q ⟨u, huL⟩)).1
            (Subgroup.mem_map.mpr ⟨⟨u, huL⟩,
              (Subgroup.mem_subgroupOf (H := D.T ⊓ L) (K := L)).mpr huS, rfl⟩)
        have h2 : (⟨(x : G) * u * (x : G)⁻¹,
            L.mul_mem (L.mul_mem x.2 huL) (L.inv_mem x.2)⟩ : ↥L) ∈
            Subgroup.comap q (sylowBar2 L (D.T ⊓ L)) := hmem
        rw [hcomapB] at h2
        exact Subgroup.mem_subgroupOf.mp h2
      have heq : (D.T ⊓ L).map (MulAut.conj (x : G)).toMonoidHom = D.T ⊓ L :=
        Subgroup.eq_of_le_of_card_ge hmap (by
          change Nat.card ↥(D.T ⊓ L) ≤
            Nat.card ↥((D.T ⊓ L).map (MulAut.conj (x : G)).toMonoidHom)
          rw [Subgroup.card_map_of_injective (MulAut.conj (x : G)).injective])
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
    · intro hx
      have hmap : (sylowBar2 L (D.T ⊓ L)).map (MulAut.conj (q x)).toMonoidHom ≤
          sylowBar2 L (D.T ⊓ L) := by
        rintro y ⟨z, hz, rfl⟩
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
        have huS : (u : G) ∈ D.T ⊓ L := hu
        have huL : (u : G) ∈ L := huS.2
        have hmem : (x : G) * (u : G) * (x : G)⁻¹ ∈ D.T ⊓ L :=
          (Subgroup.mem_normalizer_iff.1 hx (u : G)).1 huS
        let w : ↥L := ⟨(x : G) * (u : G) * (x : G)⁻¹,
          L.mul_mem (L.mul_mem x.2 huL) (L.inv_mem x.2)⟩
        have hw : w ∈ (D.T ⊓ L).subgroupOf L :=
          (Subgroup.mem_subgroupOf (H := D.T ⊓ L) (K := L)).mpr hmem
        refine Subgroup.mem_map.mpr ⟨w, hw, ?_⟩
        show (MulAut.conj (q x)).toMonoidHom (q ⟨u, huL⟩) = q w
        show q x * q ⟨u, huL⟩ * (q x)⁻¹ = q w
        rw [← map_mul, ← map_inv, ← map_mul]
        congr 1
      have hcard := Subgroup.card_map_of_injective
        (f := (MulAut.conj (q x)).toMonoidHom) (MulAut.conj (q x)).injective
        (K := sylowBar2 L (D.T ⊓ L))
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (Subgroup.eq_of_le_of_card_ge hmap (le_of_eq hcard.symm))
  have hcenterNB : Subgroup.center (Bar2 L) ≤
      Subgroup.normalizer ((sylowBar2 L (D.T ⊓ L)) : Set (Bar2 L)) :=
    Subgroup.center_le_normalizer _
  have hKleBorel : ψ.ker ≤
      (L ⊓ Subgroup.normalizer ((D.T ⊓ L : Subgroup G) : Set G)).subgroupOf L := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact ⟨x.2, (hqNiff x).mp (hcenterNB (hqkerZ ⟨x, hx, rfl⟩))⟩
  obtain ⟨t, htT, P, hP, hPt⟩ := hswap
  have hTM : t ∈ D.M := D.sylowM.le htT
  have htL : t ∈ Subgroup.normalizer (L : Set G) := hMN hTM
  have hSleP : D.T ⊓ L ≤ P := fun s hs =>
    hP.2.1 (Subgroup.mem_inf.mpr ⟨hs.2, Subgroup.le_normalizer hs⟩)
  have hO2leP : pCoreOf 2 L ≤ P := hO2le.trans hSleP
  have hqkerP : q.ker ≤ P.subgroupOf L := by
    rw [QuotientGroup.ker_mk', ← CFSG.openPCoreOf_subgroupOf 2 L]
    exact Subgroup.subgroupOf_mono L hO2leP
  let Pbar : Subgroup (Bar2 L) := (P.subgroupOf L).map q
  have hPbar_le : Pbar ≤ ⊤ := le_top
  have hPbar_ne : Pbar ≠ ⊤ := by
    intro htop
    have h1 : Subgroup.comap q (Subgroup.map q (P.subgroupOf L)) = P.subgroupOf L :=
      Subgroup.comap_map_eq_self (f := q) hqkerP
    have htop' : Subgroup.map q (P.subgroupOf L) = ⊤ := htop
    rw [htop', Subgroup.comap_top] at h1
    have hmem : ∀ x : ↥L, (x : G) ∈ P := fun x =>
      Subgroup.mem_subgroupOf.mp (h1 ▸ Subgroup.mem_top x)
    exact hP.2.2.1 (le_antisymm hP.1 (fun g hg => hmem ⟨g, hg⟩))
  have hPbar_max : ∀ R : Subgroup (Bar2 L), Pbar ≤ R → R ≤ ⊤ → R = Pbar ∨ R = ⊤ := by
    intro R hPR hR
    have hqrange : q.range = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
    have hRmap : R = (R.comap q).map q :=
      (Subgroup.map_comap_eq_self (by rw [hqrange]; exact le_top)).symm
    set R' : Subgroup ↥L := R.comap q with hR'def
    have hPR' : P.subgroupOf L ≤ R' := fun x hx =>
      hPR (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    have hPRL : P ≤ R'.map L.subtype := by
      rintro p hp
      exact Subgroup.mem_map.mpr ⟨⟨p, hP.1 hp⟩, hPR' (Subgroup.mem_subgroupOf.mpr hp), rfl⟩
    have hR'L : R'.map L.subtype ≤ L := Subgroup.map_subtype_le _
    rcases hP.2.2.2 (R'.map L.subtype) hPRL hR'L with h | h
    · left
      have hR'eq : R' = P.subgroupOf L := by
        calc R' = (R'.map L.subtype).comap L.subtype :=
              (Subgroup.comap_map_eq_self_of_injective L.subtype_injective R').symm
          _ = P.comap L.subtype := by rw [h]
          _ = P.subgroupOf L := rfl
      rw [hRmap, hR'eq]
    · right
      have hR'eq : R' = ⊤ := by
        calc R' = (R'.map L.subtype).comap L.subtype :=
              (Subgroup.comap_map_eq_self_of_injective L.subtype_injective R').symm
          _ = L.comap L.subtype := by rw [h]
          _ = ⊤ := by ext x; simp
      rw [hRmap, hR'eq, Subgroup.map_top, hqrange]
  have hNB : Subgroup.normalizer ((sylowBar2 L (D.T ⊓ L)) : Set (Bar2 L)) ≤ Pbar := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hxN : (x : G) ∈ L ⊓ Subgroup.normalizer ((D.T ⊓ L : Subgroup G) : Set G) :=
      ⟨x.2, (hqNiff x).mp hy⟩
    exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr (hP.2.1 hxN), rfl⟩
  have hPbar : IsMaxParabolicOver (⊤ : Subgroup (Bar2 L)) (sylowBar2 L (D.T ⊓ L)) Pbar :=
    ⟨hPbar_le, by simpa using hNB, hPbar_ne, hPbar_max⟩
  have hkerPbar : φ.ker ≤ Pbar := hφker.trans (hcenterNB.trans hNB)
  let φm : Bar2 L →* MulAut (Vtil V₀ V hV) := (Subgroup.subtype (barSub V₀ V hV L)).comp φ
  have hφmker : φm.ker = φ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro h
      exact Subtype.ext h
    · intro h
      rw [h]
      rfl
  have hφmker_le : φm.ker ≤ Pbar := hφmker ▸ hkerPbar
  have hφmker_c : φm.ker ≤ Subgroup.center (Bar2 L) := hφmker ▸ hφker
  have hφmodd : Odd (Nat.card ↥φm.ker) := hφmker ▸ hφodd
  have hrange : φm.range = barSub V₀ V hV L := by
    rw [show φm = (Subgroup.subtype (barSub V₀ V hV L)).comp φ from rfl,
      MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hφsurj, Subgroup.map_top]
    exact Subgroup.range_subtype (barSub V₀ V hV L)
  set B : Subgroup (Bar2 L) := sylowBar2 L (D.T ⊓ L) with hBdef
  have hφB : Subgroup.map φm B = barSub V₀ V hV (D.T ⊓ L) := by
    rw [hBdef, sylowBar2, show φm = (Subgroup.subtype (barSub V₀ V hV L)).comp φ from rfl,
      Subgroup.map_map]
    have h1 := hbase (D.T ⊓ L) inf_le_right
    rw [← h1]
    congr 1
  have hconj_eq : ∀ y : Bar2 L,
      φm y ∈ Subgroup.normalizer ((Subgroup.map φm B) : Set (MulAut (Vtil V₀ V hV))) →
        B.map (MulAut.conj y).toMonoidHom = B := by
    intro y hy
    set A : Subgroup (Bar2 L) := B.map (MulAut.conj y).toMonoidHom with hAdef
    have hAle : A ≤ B ⊔ φm.ker := by
      rintro a ha
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
      have hφb : φm b ∈ Subgroup.map φm B := Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
      have hφa : φm (y * b * y⁻¹) ∈ Subgroup.map φm B := by
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.1 hy (φm b)).1 hφb
      have h2 : (y * b * y⁻¹) ∈ Subgroup.comap φm (Subgroup.map φm B) := hφa
      rwa [Subgroup.comap_map_eq] at h2
    have hB0 : IsPGroup 2 ↥((D.T ⊓ L).subgroupOf L) :=
      IsPGroup.comap_subtype (p := 2) (H := D.T ⊓ L) (K := L) hSsyl.isPGroup
    have hB2 : IsPGroup 2 ↥B := by
      have := hB0.map q
      simpa only [B, sylowBar2] using this
    have hA2 : IsPGroup 2 ↥A := hB2.map (MulAut.conj y).toMonoidHom
    have hAN : A ⊓ φm.ker = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨n, hn⟩ := hA2.exists_card_eq
      have hzn : z ^ 2 ^ n = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one]
        have h := Subgroup.orderOf_dvd_natCard A hz.1
        rwa [hn] at h
      have hcop : Nat.Coprime (2 ^ n) (Nat.card ↥φm.ker) :=
        Nat.Coprime.pow_left n hφmodd.coprime_two_left
      have hz1 : z = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
        (orderOf_dvd_of_pow_eq_one hzn) (Subgroup.orderOf_dvd_natCard φm.ker hz.2))
      simpa using hz1
    have hBN : B ⊓ φm.ker = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨n, hn⟩ := hB2.exists_card_eq
      have hzn : z ^ 2 ^ n = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one]
        have h := Subgroup.orderOf_dvd_natCard B hz.1
        rwa [hn] at h
      have hcop : Nat.Coprime (2 ^ n) (Nat.card ↥φm.ker) :=
        Nat.Coprime.pow_left n hφmodd.coprime_two_left
      have hz1 : z = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
        (orderOf_dvd_of_pow_eq_one hzn) (Subgroup.orderOf_dvd_natCard φm.ker hz.2))
      simpa using hz1
    have : φm.ker.Normal := Subgroup.normal_of_le_center hφmker_c
    have hcardA : Nat.card ↥(A ⊔ φm.ker) = Nat.card ↥A * Nat.card ↥φm.ker := by
      rw [sup_comm, CFSG.GroupTheory.PerfectCover.card_sup_eq_mul_of_inf_eq_bot (Y := φm.ker) hAN,
        mul_comm]
    have hcardB : Nat.card ↥(B ⊔ φm.ker) = Nat.card ↥B * Nat.card ↥φm.ker := by
      rw [sup_comm, CFSG.GroupTheory.PerfectCover.card_sup_eq_mul_of_inf_eq_bot (Y := φm.ker) hBN,
        mul_comm]
    have hcardAB : Nat.card ↥A = Nat.card ↥B :=
      Subgroup.card_map_of_injective (MulAut.conj y).injective
    have hsup : A ⊔ φm.ker = B ⊔ φm.ker := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le hAle le_sup_right) ?_
      rw [hcardB, hcardA, hcardAB]
    have hAeq : A = B := CFSG.GroupTheory.eq_of_sup_eq_of_le_center hφmker_c hφmodd hA2 hB2 hsup
    exact hAeq
  have hQbar_max : IsMaxParabolicOver (barSub V₀ V hV L)
      (barSub V₀ V hV D.T ⊓ barSub V₀ V hV L) (Subgroup.map φm Pbar) := by
    rw [hinf]
    have hQle : Subgroup.map φm Pbar ≤ barSub V₀ V hV L :=
      hrange ▸ Subgroup.map_le_range φm Pbar
    have hQne : Subgroup.map φm Pbar ≠ barSub V₀ V hV L := by
      intro htop
      have h1 : Subgroup.comap φm (Subgroup.map φm Pbar) = Pbar :=
        Subgroup.comap_map_eq_self (f := φm) hφmker_le
      rw [htop, ← hrange] at h1
      have htop2 : Subgroup.comap φm (φm.range) = ⊤ := by
        rw [← Subgroup.map_top φm]
        exact Subgroup.comap_map_eq_self le_top
      rw [htop2] at h1
      exact hPbar_ne h1.symm
    have hQmax : ∀ Q : Subgroup (MulAut (Vtil V₀ V hV)),
        Subgroup.map φm Pbar ≤ Q → Q ≤ barSub V₀ V hV L →
          Q = Subgroup.map φm Pbar ∨ Q = barSub V₀ V hV L := by
      intro Q hPQ hQ
      have hQmap : Q = Subgroup.map φm (Subgroup.comap φm Q) :=
        (Subgroup.map_comap_eq_self (by rw [hrange]; exact hQ)).symm
      have hkerQ : φm.ker ≤ Subgroup.comap φm Q := fun x hx => by
        rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
        exact Q.one_mem
      set Q' : Subgroup (Bar2 L) := Subgroup.comap φm Q with hQ'def
      have hPbarQ' : Pbar ≤ Q' := fun x hx => hPQ (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      rcases hPbar_max Q' hPbarQ' le_top with h | h
      · left
        rw [hQmap, h]
      · right
        rw [hQmap, h, Subgroup.map_top, hrange]
    refine ⟨hQle, ?_, hQne, hQmax⟩
    rintro c ⟨hcL, hcN⟩
    obtain ⟨y, hyφ⟩ := MonoidHom.mem_range.mp (by rw [hrange]; exact hcL)
    have hyN : y ∈ Subgroup.normalizer ((sylowBar2 L (D.T ⊓ L)) : Set (Bar2 L)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      apply hconj_eq y
      rw [← hφB] at hcN
      exact hyφ ▸ hcN
    exact Subgroup.mem_map.mpr ⟨y, hNB hyN, hyφ⟩
  have hSconj : (D.T ⊓ L).map (MulAut.conj t).toMonoidHom = D.T ⊓ L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTnormS htT)
  have hPt_borel : L ⊓ Subgroup.normalizer ((D.T ⊓ L : Subgroup G) : Set G) ≤
      P.map (MulAut.conj t).toMonoidHom := by
    intro x hx
    have hxconj : t⁻¹ * x * t ∈ L ⊓
        Subgroup.normalizer ((D.T ⊓ L : Subgroup G) : Set G) := by
      refine ⟨?_, ?_⟩
      · have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ htL) x).1 hx.1
        simpa using h1
      · change t⁻¹ * x * t ∈ Subgroup.normalizer ((D.T ⊓ L : Subgroup G) : Set G)
        rw [Subgroup.mem_normalizer_iff]
        intro s
        constructor
        · intro hs
          have hN : t⁻¹ ∈ Subgroup.normalizer ((D.T ⊓ L : Subgroup G) : Set G) :=
            Subgroup.inv_mem _ (hTnormS htT)
          have h1 : t * s * t⁻¹ ∈ D.T ⊓ L :=
            (Subgroup.mem_normalizer_iff.1 (hTnormS htT) s).1 hs
          have h2 : x * (t * s * t⁻¹) * x⁻¹ ∈ D.T ⊓ L :=
            (Subgroup.mem_normalizer_iff.1 hx.2 (t * s * t⁻¹)).1 h1
          have h3 : t⁻¹ * (x * (t * s * t⁻¹) * x⁻¹) * (t⁻¹)⁻¹ ∈ D.T ⊓ L :=
            (Subgroup.mem_normalizer_iff.1 hN (x * (t * s * t⁻¹) * x⁻¹)).1 h2
          simpa [mul_assoc] using h3
        · intro hs
          have hN : t⁻¹ ∈ Subgroup.normalizer ((D.T ⊓ L : Subgroup G) : Set G) :=
            Subgroup.inv_mem _ (hTnormS htT)
          have hs' : t⁻¹ * (x * (t * s * t⁻¹) * x⁻¹) * (t⁻¹)⁻¹ ∈ D.T ⊓ L := by
            convert hs using 1
            group
          have h2 : x * (t * s * t⁻¹) * x⁻¹ ∈ D.T ⊓ L :=
            (Subgroup.mem_normalizer_iff.1 hN (x * (t * s * t⁻¹) * x⁻¹)).2 hs'
          have h1 : t * s * t⁻¹ ∈ D.T ⊓ L :=
            (Subgroup.mem_normalizer_iff.1 hx.2 (t * s * t⁻¹)).2 h2
          exact (Subgroup.mem_normalizer_iff.1 (hTnormS htT) s).2 h1
    have hmem : t⁻¹ * x * t ∈ P := hP.2.1 hxconj
    refine Subgroup.mem_map.mpr ⟨t⁻¹ * x * t, hmem, ?_⟩
    change t * (t⁻¹ * x * t) * t⁻¹ = x
    group
  have hkerPt : ψ.ker ≤ (P.map (MulAut.conj t).toMonoidHom).subgroupOf L :=
    hKleBorel.trans (Subgroup.subgroupOf_mono L hPt_borel)
  refine ⟨actTil V₀ V hV ⟨t, hTstab htT⟩, actTil_mem_barSub V₀ V hV htT (hTstab htT),
    Subgroup.map φm Pbar, hQbar_max, ?_⟩
  intro heq
  have h1 : barSub V₀ V hV (P.map (MulAut.conj t).toMonoidHom) = barSub V₀ V hV P := by
    rw [TwelveTwentyThree.barSub_map_conj hV (hP.1.trans hLstab) (hTstab htT)]
    have hQmapP : Subgroup.map φm Pbar = barSub V₀ V hV P := by
      rw [show φm = (Subgroup.subtype (barSub V₀ V hV L)).comp φ from rfl,
        Subgroup.map_map]
      exact hbase P hP.1
    rw [← hQmapP]
    exact heq
  have hPlePt : P ≤ P.map (MulAut.conj t).toMonoidHom := by
    intro p hp
    have hpL : p ∈ L := hP.1 hp
    have hPtL : P.map (MulAut.conj t).toMonoidHom ≤ L := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact (Subgroup.mem_normalizer_iff.1 htL y).1 (hP.1 hy)
    have hmem : (⟨p, hpL⟩ : ↥L) ∈
        Subgroup.comap ψ (barSub V₀ V hV (P.map (MulAut.conj t).toMonoidHom)) := by
      rw [Subgroup.mem_comap, h1, ← hbase P hP.1]
      exact (Subgroup.mem_map (f := ψ)).mpr
        ⟨⟨p, hpL⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
    have h2 := hmem
    rw [← hbase (P.map (MulAut.conj t).toMonoidHom) hPtL,
      Subgroup.comap_map_eq_self hkerPt] at h2
    exact Subgroup.mem_subgroupOf.mp h2
  have heqP : P.map (MulAut.conj t).toMonoidHom = P := by
    have h := Subgroup.eq_of_le_of_card_ge hPlePt (by
      rw [Subgroup.card_map_of_injective (MulAut.conj t).injective])
    exact h.symm
  exact hPt heqP

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
