module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HYd
public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartTwo.Sec14.Item148HJRes2ProofYd
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_inSubgroup_theta (d : G) :
    Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer
      ((inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({d} : Set G)) :
        Subgroup G) : Set G) := by
  set C := Subgroup.centralizer ({d} : Set G) with hC
  obtain ⟨-, hθc, -, -, -⟩ := solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three
  haveI : (aschbacherSolvableCore 3 ↥C).Normal := by haveI := hθc; infer_instance
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · rintro ⟨t', ht', rfl⟩
    exact ⟨⟨x, hx⟩ * t' * ⟨x, hx⟩⁻¹, (inferInstance : (aschbacherSolvableCore 3 ↥C).Normal).conj_mem
      t' ht' _, rfl⟩
  · rintro ⟨t', ht', ht'e⟩
    refine ⟨⟨x, hx⟩⁻¹ * t' * ⟨x, hx⟩⁻¹⁻¹,
      (inferInstance : (aschbacherSolvableCore 3 ↥C).Normal).conj_mem t' ht' _, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, InvMemClass.coe_inv, inv_inv] at ht'e ⊢
    rw [ht'e]; group

theorem mem_sectionCentralizer_of_le {d b : G} {A Yd LB : Subgroup G} (hbA : b ∈ A)
    (hbd : b ∈ Subgroup.centralizer ({d} : Set G))
    (hYdC : Yd ≤ Subgroup.centralizer ({d} : Set G))
    (hLBC : LB ≤ Subgroup.centralizer ({d} : Set G))
    (hLBb : LB ≤ Subgroup.centralizer ({b} : Set G))
    (hbYd : b ∈ Subgroup.normalizer (Yd : Set G))
    (hYd : Yd ≤ LB ⊔ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({d} : Set G))) :
    b ∈ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd) := by
  set C := Subgroup.centralizer ({d} : Set G) with hC
  set T := inSubgroup (aschbacherSolvableCore 3) C with hT
  obtain ⟨-, hθc, -, -, -⟩ := solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three
  haveI : (aschbacherSolvableCore 3 ↥C).Normal := by haveI := hθc; infer_instance
  have hTC : T ≤ C := Subgroup.map_subtype_le _
  have hCT : C ≤ Subgroup.normalizer (T : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · rintro ⟨t', ht', rfl⟩
      refine ⟨⟨x, hx⟩ * t' * ⟨x, hx⟩⁻¹, (inferInstance : (aschbacherSolvableCore 3 ↥C).Normal).conj_mem
        t' ht' _, rfl⟩
    · rintro ⟨t', ht', ht'e⟩
      refine ⟨⟨x, hx⟩⁻¹ * t' * ⟨x, hx⟩⁻¹⁻¹,
        (inferInstance : (aschbacherSolvableCore 3 ↥C).Normal).conj_mem t' ht' _, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, InvMemClass.coe_inv, inv_inv] at ht'e ⊢
      rw [ht'e]; group
  refine ⟨hbA, fun y hy => ?_⟩
  have hyLT : y ∈ LB ⊔ T := hYd hy
  have hmul : y ∈ ((LB : Set G) * (T : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right LB T (hLBC.trans hCT)]; exact hyLT
  obtain ⟨l, hl, t, ht, rfl⟩ := hmul
  have hbl : b * l = l * b := (Subgroup.mem_centralizer_singleton_iff.mp (hLBb hl)).symm
  have hbt : b * t * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hCT hbd) t).mp ht
  have hcomm : b * (l * t) * b⁻¹ * (l * t)⁻¹ = l * ((b * t * b⁻¹) * t⁻¹) * l⁻¹ := by
    have : b * (l * t) * b⁻¹ = l * (b * t * b⁻¹) := by
      calc b * (l * t) * b⁻¹ = (b * l) * t * b⁻¹ := by group
        _ = (l * b) * t * b⁻¹ := by rw [hbl]
        _ = l * (b * t * b⁻¹) := by group
    rw [this]; group
  have hmemT : b * (l * t) * b⁻¹ * (l * t)⁻¹ ∈ T := by
    rw [hcomm]
    exact (Subgroup.mem_normalizer_iff.mp (hCT (hLBC hl)) _).mp (T.mul_mem hbt (T.inv_mem ht))
  have hmemYd : b * (l * t) * b⁻¹ * (l * t)⁻¹ ∈ Yd :=
    Yd.mul_mem ((Subgroup.mem_normalizer_iff.mp hbYd _).mp hy) (Yd.inv_mem hy)
  have hle := comap_theta_le (Subgroup.inclusion hYdC) (Subgroup.inclusion_injective _)
  obtain ⟨t', ht', ht'e⟩ := hmemT
  have hmem : (⟨_, hmemYd⟩ : Yd) ∈ (aschbacherSolvableCore 3 ↥C).comap (Subgroup.inclusion hYdC) := by
    rw [Subgroup.mem_comap]
    have : Subgroup.inclusion hYdC ⟨_, hmemYd⟩ = t' := Subtype.ext ht'e.symm
    rw [this]; exact ht'
  exact ⟨_, hle hmem, rfl⟩

theorem isList46_of_mem_inf_centralizer (h46 : Sec4.Item4_6) (hG : TheoremFourHyp G)
    {Y Yd : Subgroup G} {d : G} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hdY : d ∈ Subgroup.normalizer (Y : Set G))
    (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G))) :
    Sec4.IsList46 (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) := by
  set C := Subgroup.centralizer ({d} : Set G) with hC
  have hdC : d ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set H := (Y ⊓ C) ⊔ Subgroup.zpowers d with hH
  have hHC : H ≤ C := sup_le inf_le_right (Subgroup.zpowers_le.mpr hdC)
  have hH4 : SectionFourHyp ↥H := hG.sectionFourHyp (fun h => by
    have : (⊤ : Subgroup G) ≤ C := h ▸ hHC
    exact Sec6.centralizer_ne_top_of_ne_one hG hd1 (top_le_iff.mp this))
  set d' : H := ⟨d, Subgroup.mem_sup_right (Subgroup.mem_zpowers d)⟩ with hd'
  have hd'Z : d' ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hHC g.2))
  have hd'o : orderOf d' = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hd3 hd1
  have h3 : 3 ∣ Nat.card (Subgroup.center H) := by
    rw [← hd'o, show orderOf d' = orderOf (⟨d', hd'Z⟩ : Subgroup.center H) from
      (Subgroup.orderOf_mk d' hd'Z).symm]
    exact orderOf_dvd_natCard _
  have hYCn : H ≤ Subgroup.normalizer ((Y ⊓ C : Subgroup G) : Set G) := by
    refine sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).mpr ?_)
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hdY, Subgroup.le_normalizer hdC⟩
  have hYdH : Yd ∈ thetaComponentsIn H :=
    Sec15.Proof1423.mem_thetaComponentsIn_of_isSubnormal hYd le_sup_left
      (Subgroup.Normal.isSubnormal ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        hYCn))
  obtain ⟨Yd', hYd', rfl⟩ := hYdH
  exact Sec21.Item223PrintProof.isList46_of_mulEquiv (Sec13.thetaQuotEquivSub H Yd')
    (h46 H hH4 h3 Yd' hYd')

section Main

set_option linter.unusedSectionVars false

theorem isTripleCover_yd_of_res (Φ : ∀ (T : Type) [Group T], Prop)
    (hΦ : ∀ {T T' : Type} [Group T] [Group T'], (T ≃* T') → Φ T → Φ T')
    (hres : ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
      Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON →
      ∀ P : Subgroup X, Late.IsE27 P → ∀ q ∈ P, q ∉ Subgroup.center X →
      ∀ M F : Subgroup X, P ≤ Subgroup.normalizer (M : Set X) → Group.IsPerfect M →
        IsQuasisimple (M ⧸ aschbacherSolvableCore 3 M) →
        Sec4.IsList46 (M ⧸ aschbacherSolvableCore 3 M) →
        F ≤ M → F ≤ Subgroup.centralizer ({q} : Set X) → Group.IsPerfect F →
        Φ (F ⧸ aschbacherSolvableCore 3 F) →
        q ∉ Late.sectionCentralizer P M (inSubgroup (aschbacherSolvableCore 3) M) → M = ⊤)
    (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8) (h46 : Sec4.Item4_6)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    {B : Subgroup G} (hB : IsHyperplane A B) {YB : Subgroup G}
    (hYB : YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)))
    (hYBΦ : Φ (↥YB ⧸ aschbacherSolvableCore 3 ↥YB))
    (hYB3 : 3 ∣ Nat.card ((↥YB ⧸ aschbacherSolvableCore 3 ↥YB) ⧸
      Subgroup.center (↥YB ⧸ aschbacherSolvableCore 3 ↥YB)))
    {b d : G} {Lb : Subgroup G} (hc : IsLBConfig A B b d Lb)
    (hle : YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B)
    {Yd : Subgroup G} (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)))
    (hYBYd : YB ≤ Yd) (hAYd : A ≤ Subgroup.normalizer (Yd : Set G))
    (hbn : b ∉ Late.sectionCentralizer A Yd (inSubgroup (aschbacherSolvableCore 3) Yd)) :
    d ∈ Yd ∧
      Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) CFSG.Blueprint.NativeSporadic.ON := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA : Late.IsE27 A := h.isE27
  have hJ := Item148HJ.j2_of_isLBConfig hc
  obtain ⟨hb1, hd1⟩ := hc.ne_one hB hA
  have hLBeq := Item148HJ.lB_eq_residual h hB hc
  have hLBCB := Item148HJ.residual_le_centralizer hc
  obtain ⟨hBbd, hbΩ, hLbeq, -, hdL, S, hdS, hSd⟩ := hc
  have hLb : Lb ∈ lA A b := hLbeq ▸ Set.mem_singleton Lb
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΩ).1
  have hbB : b ∈ B := hBbd ▸ Subgroup.subset_closure (Set.mem_insert b {d})
  have hdB : d ∈ B := hBbd ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  have hdA : d ∈ A := hB.1 hdB
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
  have hS := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hdS hSd
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian hd1)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hJ hdL hd1
    ⟨S, hdS, hSd⟩
  obtain ⟨K, hK, hJK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hbA hdA hb1 hLb.1 hJq
  have hdata : Sec13Data G A b Lb :=
    { h.toSec13Data with zpowers_mem_omegaA := hbΩ, mem_lA := hLb }
  set C := Subgroup.centralizer ({d} : Set G) with hC
  set LB := inSubgroup perfectResidual (Lb ⊓ C) with hLBdef
  have hKC : K ≤ C := (mem_thetaComponentsIn_iff.mp ((thetaComponentsAt_eq_thetaComponentsIn d) ▸ hK)).1
  have hYdYC : Yd ≤ Y ⊓ C := le_of_mem_thetaComponentsIn hYd
  have hYdC : Yd ≤ C := hYdYC.trans inf_le_right
  have hYdp : Group.IsPerfect Yd := isPerfect_of_mem_thetaComponentsIn hYd
  have hYdq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hYd
  have hYBp : Group.IsPerfect YB := isPerfect_of_mem_thetaComponentsIn hYB
  have hYBq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hYB
  have hCBd : Subgroup.centralizer (B : Set G) ≤ C :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdB)
  have hCBb : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB)
  set N := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hN
  have hNC : N ≤ C := (pPrimeCoreOf_le 3 _).trans hCBd
  have hN3 : Nat.Coprime 3 (Nat.card N) := coprime_card_pPrimeCoreOf 3 _
  have hLBN : LB ≤ Subgroup.normalizer (N : Set G) :=
    hLBCB.trans (le_normalizer_pPrimeCoreOf 3 _)
  have hYBNL : YB ≤ N ⊔ LB := by rw [← hLBeq]; exact hle
  have hinc : Yd ≤ K ⊔ inSubgroup (aschbacherSolvableCore 3) C :=
    le_sup_theta_centralizer hK hYdC hYdp hYdq hYBp hYBq hYB3 hYBYd hJK hNC hN3 hLBN hYBNL
  have hbd : b ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute hbA hdA)
  have hbYd : b ∈ Subgroup.normalizer (Yd : Set G) := hAYd hbA
  have hLBC : LB ≤ C := (Subgroup.map_subtype_le _).trans inf_le_right
  have hLBb : LB ≤ Subgroup.centralizer ({b} : Set G) :=
    (Subgroup.map_subtype_le _).trans (inf_le_left.trans
      (le_centralizer_of_mem_thetaComponentsAt hLb.1))
  have hKθ : inSubgroup (aschbacherSolvableCore 3) K ≤ inSubgroup (aschbacherSolvableCore 3) C := by
    rw [CFSG.RankThree.PartOne.theta_eq_inf_of_mem_thetaComponentsAt Nat.prime_three hK]
    exact inf_le_right
  have hcase : K = LB ⊔ inSubgroup (aschbacherSolvableCore 3) K → False := by
    intro hKeq
    apply hbn
    have hYdLB : Yd ≤ LB ⊔ inSubgroup (aschbacherSolvableCore 3) C := by
      refine hinc.trans ?_
      rw [hKeq]
      exact sup_le (sup_le le_sup_left (hKθ.trans le_sup_right)) le_sup_right
    exact mem_sectionCentralizer_of_le hbA hbd hYdC hLBC hLBb hbYd hYdLB
  rcases h134 G A b Lb hdata hJ d hdA hd1 ⟨_, hS⟩ K hK hJK with
    ⟨hKeq, -, -⟩ | ⟨hKeq, -⟩ | ⟨hON, -, -⟩
  · exact (hcase hKeq).elim
  · exact (hcase hKeq).elim
  ·
    obtain ⟨-, hdK, -, h9, hALK, hAeq, hbN⟩ := ON134.setup h131 hdata hJ hdA hd1 ⟨_, hS⟩ hK hJK
    have hKq : IsQuasisimple (↥K ⧸ aschbacherSolvableCore 3 ↥K) :=
      CFSG.RankThree.PartOne.isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt Nat.prime_three hK
    have hbK : b ∈ K := ON134.mem_of_maximal hA.1 (fun E hE hAE => h.toSec13Data.eq_of_le hE hAE)
      hbA inf_le_left h9 hALK hAeq hbN (hB.1 hdB |> fun _ => ⟨hdA, hdL⟩)
      hd1 (le_centralizer_of_mem_thetaComponentsAt hK) hKq hON
    have hAK : A ≤ K := by
      rw [hAeq]
      exact sup_le (Subgroup.zpowers_le.mpr hbK) hALK
    have hYdL := isList46_of_mem_inf_centralizer h46 h.toTheoremFourHyp (hA.1.2 d hdA) hd1
      (hY.2 hdA) hYd
    have hYBb : YB ≤ Subgroup.centralizer ({b} : Set G) :=
      (le_of_mem_thetaComponentsIn hYB).trans (inf_le_right.trans hCBb)
    obtain ⟨hTC, hKYd⟩ := isTripleCover_yd_of_core Φ hΦ hres hK hON hA hAK hbA hYdC hYdp hYdq hYdL
      hinc hAYd hYBYd hYBb hYBp hYBΦ hbn
    refine ⟨?_, hTC⟩
    obtain ⟨-, hθCc, hθC3, -, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥C) Nat.prime_three
    have hT3 : Nat.Coprime 3 (Nat.card (inSubgroup (aschbacherSolvableCore 3) C)) := by
      rw [inSubgroup, Subgroup.card_map_of_injective C.subtype_injective]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθC3
    exact mem_of_mem_sup_coprime (hYdC.trans (le_normalizer_inSubgroup_theta d)) hT3
      (hA.1.2 d hdA)
      (fun t ht => Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.map_subtype_le _) ht))
      (hKYd hdK)

theorem card_alternatingGroup_fin_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have h : 2 * Nat.card (alternatingGroup (Fin 5)) = 120 := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]; rfl
  omega

theorem step148HJTypeYdONA5_of_res (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h46 : Sec4.Item4_6) (hres : Item464OneA5K) : Step148HJTypeYdONA5 := by
  intro G _ _ A c L hS Y hY _ _ B hB _ YB hYB _ _ b d Lb hc hle Yd hYd hYBYd hAYd hbn
    _ _ _ _ hA5
  have hYB3 : 3 ∣ Nat.card ((↥YB ⧸ aschbacherSolvableCore 3 ↥YB) ⧸
      Subgroup.center (↥YB ⧸ aschbacherSolvableCore 3 ↥YB)) := by
    obtain ⟨e⟩ := hA5
    have hZ : Subgroup.center (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) = ⊥ := by
      have hc5 : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ := by
        haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
        rcases (inferInstance : (Subgroup.center (alternatingGroup (Fin 5))).Normal).eq_bot_or_eq_top with h | h
        · exact h
        · exfalso
          have hcomm : ∀ a b : alternatingGroup (Fin 5), a * b = b * a := fun a b =>
            (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
          have := (IsSimpleGroup.comm_iff_isSolvable (G := alternatingGroup (Fin 5))).mp hcomm
          exact Equiv.Perm.not_isSolvable_fin_5 (Group.isSolvable_of_ker_le_range
            (alternatingGroup (Fin 5)).subtype (Equiv.Perm.sign) (by
              intro x hx; exact ⟨⟨x, (Equiv.Perm.mem_alternatingGroup).mpr hx⟩, rfl⟩))
      rw [← Subgroup.map_center_eq e.symm, hc5, Subgroup.map_bot]
    rw [hZ, Nat.card_congr (QuotientGroup.quotientBot (G := ↥YB ⧸ aschbacherSolvableCore 3 ↥YB)).toEquiv,
      Nat.card_congr e.toEquiv, card_alternatingGroup_fin_five]
    norm_num
  exact isTripleCover_yd_of_res (fun (T : Type) [Group T] =>
      Nonempty (T ≃* alternatingGroup (Fin 5)))
    (fun e h => h.map e.symm.trans) hres h131 h134 h48 h46 hS hY hB hYB hA5
    hYB3 hc hle hYd hYBYd hAYd hbn

end Main

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
