module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Sylow
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight106Odd
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight106Faithful
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight106Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Fixed
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102AltTen
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.StatedPSLTwo
import CFSG.CGT.PushingUpLit.T2K.SixA
import CFSG.GroupTheory.Fitting.LayerProjection
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.Quasithin.Background.F1Models
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

variable {G : Type} [Group G] [Finite G]

private theorem two_le_n {D : Data G} {L P : Subgroup G} {p n : ℕ}
    (hSg : SigmaStd D) (h8103 : R8103At D L P p n) (hH : F08.Hyp8102 D L P p n) : 2 ≤ n := by
  have hEven : Even n := h8103.1
  have hp : p.Prime := (prime_of_hyp8102 hSg hH).1
  have hp2 : p ≠ 2 := (prime_of_hyp8102 hSg hH).2.1
  by_contra hlt
  have hn0 : n = 0 := by
    rcases hEven with ⟨k, hk⟩
    omega
  have hmod : (2 : ℤ) ^ n ≡ -1 [ZMOD p] := h8103.2.1.1
  rw [hn0, pow_zero] at hmod
  have hdvd : (p : ℤ) ∣ 2 := by
    have h := hmod.dvd
    rw [show (-1 : ℤ) - 1 = -2 by ring] at h
    exact dvd_neg.mp h
  have hdvdNat : p ∣ 2 := by exact_mod_cast hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvdNat)

private theorem K_isPerfect {L B : Subgroup G} : Group.IsPerfect ↥(F08.KOf8103 L B) := by
  unfold F08.KOf8103
  exact isPerfect_derInf8 _

private theorem R_odd {B : Subgroup G} (hX2 : pCoreOf 2 (centralizer (B : Set G)) = ⊥) :
    Odd (Nat.card (CFSG.fittingSubgroupOf (centralizer (B : Set G)))) :=
  odd_card_fittingSubgroupOf hX2

private theorem R_solvable {B : Subgroup G} :
    Group.IsSolvable ↥(CFSG.fittingSubgroupOf (centralizer (B : Set G))) := by
  have hnil : Group.IsNilpotent (CFSG.fittingSubgroupOf (centralizer (B : Set G))) :=
    fittingSubgroupOf_isNilpotent (centralizer (B : Set G))
  haveI : Group.IsNilpotent (CFSG.fittingSubgroupOf (centralizer (B : Set G))) := hnil
  exact IsNilpotent.to_isSolvable

private theorem K_le_centralizer {L B : Subgroup G} :
    F08.KOf8103 L B ≤ centralizer (B : Set G) := by
  unfold F08.KOf8103 F08.DerInf8
  exact (Subgroup.map_subtype_le _).trans inf_le_right

private theorem centralizer_ne_top {B : Subgroup G} (hB1 : B ≠ ⊥)
    (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) :
    centralizer (B : Set G) ≠ ⊤ := by
  intro hX
  have hBZ : B ≤ Subgroup.center G := by
    rw [Subgroup.centralizer_eq_top_iff_subset] at hX
    exact hX
  have hZ : Subgroup.center G = ⊥ := by
    apply TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative
    intro hcomm
    rcases hnab with ⟨a, b, hab⟩
    exact hab (hcomm.is_comm.comm a b)
  rw [hZ] at hBZ
  exact hB1 (le_bot_iff.mp hBZ)

private theorem K_isKGroup {D : Data G} {L B : Subgroup G} (hB1 : B ≠ ⊥) :
    CFSG.Open.IsKGroup ↥(F08.KOf8103 L B) := by
  have hXne : centralizer (B : Set G) ≠ ⊤ :=
    centralizer_ne_top hB1 D.standing.simple D.standing.nonab
  have hKne : F08.KOf8103 L B ≠ ⊤ := by
    intro hKtop
    have hle : (⊤ : Subgroup G) ≤ centralizer (B : Set G) := by
      rw [← hKtop]
      exact K_le_centralizer
    exact hXne (top_le_iff.mp hle)
  exact CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_open_isKGroup
    (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1 D.standing.kProper)
    (F08.KOf8103 L B) hKne

private theorem K_le_normalizer_R {L B : Subgroup G} :
    F08.KOf8103 L B ≤
      normalizer (CFSG.fittingSubgroupOf (centralizer (B : Set G)) : Set G) := by
  let X := centralizer (B : Set G)
  let R := CFSG.fittingSubgroupOf X
  have hKX : F08.KOf8103 L B ≤ X := K_le_centralizer
  have hRX : R ≤ X := Subgroup.map_subtype_le _
  have hRsub : (R.subgroupOf X).Normal := by
    have hR : R.subgroupOf X = fittingSubgroup ↥X := by
      dsimp only [R, X, CFSG.fittingSubgroupOf]
      exact comap_map_eq_self_of_injective X.subtype_injective (fittingSubgroup ↥X)
    rw [hR]
    infer_instance
  exact hKX.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hRX).mp hRsub)

private theorem X_le_normalizer_R {B : Subgroup G} :
    centralizer (B : Set G) ≤
      normalizer (CFSG.fittingSubgroupOf (centralizer (B : Set G)) : Set G) := by
  let X := centralizer (B : Set G)
  let R := CFSG.fittingSubgroupOf X
  have hRX : R ≤ X := Subgroup.map_subtype_le _
  have hRsub : (R.subgroupOf X).Normal := by
    have hR : R.subgroupOf X = fittingSubgroup ↥X := by
      dsimp only [R, X, CFSG.fittingSubgroupOf]
      exact comap_map_eq_self_of_injective X.subtype_injective (fittingSubgroup ↥X)
    rw [hR]
    infer_instance
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hRX).mp hRsub

private theorem normalizer_inf_le_normalizer_K {L B : Subgroup G} :
    normalizer ((L ⊓ centralizer (B : Set G) : Subgroup G) : Set G) ≤
      normalizer (F08.KOf8103 L B : Set G) := by
  have h := CFSG.SignalizerFunctorTheorem.Nonsolvable.normalizer_le_normalizer_perfectResidual_map
    (L ⊓ centralizer (B : Set G))
  simpa only [F08.KOf8103, F08.DerInf8, CFSG.perfectResidual] using h

private theorem eq_bot_of_odd_of_isL2 {K N : Subgroup G} {m : ℕ}
    (hL2 : IsL2 (Bar2 K) m) (hm : 1 ≤ m) (hNK : N ≤ K)
    (hKN : K ≤ normalizer (N : Set G)) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmodel : StatedClassicalModel (Bar2 K) .PSL 2 2 m := hL2.statedClassicalModel (by decide)
  haveI : IsSimpleGroup (Bar2 K) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2
  let π : K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  have hker : π.ker = CFSG.pCore 2 ↥K := QuotientGroup.ker_mk' _
  have hNnormal : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  have hmapnormal : ((N.subgroupOf K).map π).Normal :=
    hNnormal.map π (QuotientGroup.mk'_surjective _)
  haveI := hmapnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf K).map π) with h | h
  · have hle : N.subgroupOf K ≤ CFSG.pCore 2 ↥K := by
      rw [← hker]
      exact (Subgroup.map_eq_bot_iff (H := N.subgroupOf K) (f := π)).mp h
    have h2sub : IsPGroup 2 (N.subgroupOf K) := CFSG.pCore_isPGroup.to_le hle
    have h2 : IsPGroup 2 N := by
      rw [IsPGroup.iff_card] at h2sub ⊢
      obtain ⟨n, hn⟩ := h2sub
      exact ⟨n, by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv] at hn⟩
    exact CFSG.CGT.PushingUpLit.T2K.eq_bot_of_odd_of_isPGroup hodd h2
  · exfalso
    have hcard : Nat.card (Bar2 K) = 2 ^ m * ((2 ^ m) ^ 2 - 1) :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hmodel
    have heven : Even (Nat.card (Bar2 K)) := by
      rw [hcard]
      have h2m : Even (2 ^ m) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      obtain ⟨k, hk⟩ := h2m
      exact ⟨k * ((2 ^ m) ^ 2 - 1), by rw [hk]; ring⟩
    have hdvd : Nat.card ((N.subgroupOf K).map π) ∣ Nat.card N := by
      have h1 : Nat.card ((N.subgroupOf K).map π) ∣ Nat.card (N.subgroupOf K) :=
        Subgroup.card_map_dvd (H := N.subgroupOf K) π
      have h2 : Nat.card (N.subgroupOf K) = Nat.card N :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv
      rwa [h2] at h1
    rw [h, Subgroup.card_top] at hdvd
    obtain ⟨k, hk⟩ := heven
    obtain ⟨d, hd⟩ := hdvd
    have hNeven : Even (Nat.card N) := ⟨k * d, by rw [hd, hk]; ring⟩
    exact (Nat.not_even_iff_odd.mpr hodd) hNeven

private theorem R_inf_K_eq_bot {L B : Subgroup G} {m : ℕ}
    (hL2 : IsL2 (Bar2 (F08.KOf8103 L B)) m) (hm : 1 ≤ m)
    (hRK : F08.KOf8103 L B ≤
      normalizer (CFSG.fittingSubgroupOf (centralizer (B : Set G)) : Set G))
    (hodd : Odd (Nat.card (CFSG.fittingSubgroupOf (centralizer (B : Set G))))) :
    CFSG.fittingSubgroupOf (centralizer (B : Set G)) ⊓ F08.KOf8103 L B = ⊥ := by
  apply eq_bot_of_odd_of_isL2 hL2 hm inf_le_right
  · exact CFSG.Walter.Transitivity.le_normalizer_inf hRK Subgroup.le_normalizer
  · exact Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le inf_le_left)

private theorem B_le_R {B : Subgroup G} (hBcard : Nat.card B = 3) :
    B ≤ CFSG.fittingSubgroupOf (centralizer (B : Set G)) := by
  let X := centralizer (B : Set G)
  have hBX : B ≤ X := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    haveI : IsCyclic B := isCyclic_of_prime_card (p := 3) hBcard
    have hcomm := (isCyclic_of_prime_card (p := 3) hBcard).isMulCommutative.is_comm.comm
      (⟨b, hb⟩ : B) (⟨c, hc⟩ : B)
    exact (congrArg Subtype.val hcomm).symm
  have hBcenter : B.subgroupOf X ≤ Subgroup.center X := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hxB : (x : G) ∈ B := hx
    have hy := Subgroup.mem_centralizer_iff.mp y.2 (x : G) hxB
    exact Subtype.ext hy.symm
  have hmap : (B.subgroupOf X).map X.subtype ≤ (fittingSubgroup X).map X.subtype :=
    Subgroup.map_mono (hBcenter.trans (CFSG.Quasithin.A36A.center_le_fittingSubgroup (X := X)))
  rw [Subgroup.map_subgroupOf_eq_of_le hBX] at hmap
  simpa [CFSG.fittingSubgroupOf] using hmap

private theorem exists_D {hK2 : KU45Syl3} {D : Data G} {L P B : Subgroup G} {p n : ℕ}
    (hH : F08.Hyp8102 D L P p n) (hB : F08.NotationB8103 L P n B)
    (h8103 : R8103At D L P p n) :
    ∃ D : Subgroup G, D ≤ P ⊓ F08.KOf8103 L B ∧ Nat.card D = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K := F08.KOf8103 L B
  have hEven : Even n := h8103.1
  have hX : IsU45 (Bar2 L) n := isU45_of_hyp8102 hH hEven
  have hP : IsSylowOf 3 P L := hH.2.2.2.2
  have hPcent : P ≤ centralizer (B : Set G) := le_centralizer_of_notationB8103 hK2 hX hP hB
  have hPLX : P ≤ L ⊓ centralizer (B : Set G) := le_inf hP.le hPcent
  have hSylow : IsSylowOf 3 P (L ⊓ centralizer (B : Set G)) := hP.of_le hPLX inf_le_left
  have hKLX : K ≤ L ⊓ centralizer (B : Set G) := by
    dsimp only [K, F08.KOf8103, F08.DerInf8]
    exact (Subgroup.map_subtype_le _).trans (le_inf inf_le_left inf_le_right)
  have hNormK : L ⊓ centralizer (B : Set G) ≤ normalizer (K : Set G) := by
    have h := (Subgroup.le_normalizer (H := L ⊓ centralizer (B : Set G))).trans
      (normalizer_inf_le_normalizer_K (L := L) (B := B))
    simpa [K] using h
  have hSylowK : IsSylowOf 3 (P ⊓ K) K :=
    hSylow.inf_of_le_normalizer hKLX hNormK
  have h3dvd : 3 ∣ Nat.card K := by
    have hKcard : 3 ∣ Nat.card (Bar2 K) :=
      CFSG.Open.StatedAPI.three_dvd_card_of_statedClassicalModel_psl_two_two
        (hB.2.2.statedClassicalModel (by decide))
    exact hKcard.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥K))
  have hfact : 0 < (Nat.card K).factorization 3 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_three (Nat.card_pos.ne') h3dvd
  have h3dvd' : 3 ∣ Nat.card ((P ⊓ K : Subgroup G)) := by
    have hcard : Nat.card ((P ⊓ K : Subgroup G)) = 3 ^ (Nat.card K).factorization 3 :=
      IsSylowOf.card_eq (p := 3) hSylowK
    rw [hcard]
    exact pow_dvd_pow 3 (Nat.succ_le_of_lt hfact)
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := (P ⊓ K : Subgroup G)) (p := 3) h3dvd'
  refine ⟨Subgroup.zpowers d, ?_, ?_⟩
  · simpa [K] using Subgroup.zpowers_le.mpr d.2
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe]
    exact hd

private theorem B_sup_D_eq_E {B D E R K : Subgroup G}
    (hBcard : Nat.card B = 3) (hDcard : Nat.card D = 3)
    (hBE : B ≤ E) (hDE : D ≤ E) (hEcard : Nat.card E = 9)
    (hBR : B ≤ R) (hDK : D ≤ K) (hRK : R ⊓ K = ⊥) :
    B ⊔ D = E := by
  let S : Subgroup G := B ⊔ D
  have hDnotB : ¬ D ≤ B := by
    intro hDB
    have hD_bot : D ≤ R ⊓ K := le_inf (hDB.trans hBR) hDK
    rw [hRK] at hD_bot
    have hD_eq_bot : D = ⊥ := le_bot_iff.mp hD_bot
    have hDcard1 : Nat.card D = 1 := by rw [hD_eq_bot, Subgroup.card_bot]
    omega
  have hlt : B < S := by
    refine lt_of_le_of_ne (show B ≤ S from le_sup_left) ?_
    intro h
    apply hDnotB
    have hDle : D ≤ S := le_sup_right
    rw [← h] at hDle
    exact hDle
  have hS_le_E : S ≤ E := sup_le hBE hDE
  have hcard_lt : Nat.card B < Nat.card S := Subgroup.card_lt_of_lt hlt
  have hcard_dvd : Nat.card S ∣ Nat.card E := Subgroup.card_dvd_of_le hS_le_E
  have hcard9 : Nat.card S = 9 := by
    rw [hEcard] at hcard_dvd
    obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow (p := 3) (m := 2) Nat.prime_three).mp hcard_dvd
    have hk2 : k = 2 := by
      by_contra h
      have hk1 : k ≤ 1 := by omega
      have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      rw [hk] at hcard_lt
      omega
    rw [hk, hk2]
    norm_num
  have hSE : S = E := Subgroup.eq_of_le_of_card_ge hS_le_E (by omega)
  exact hSE

private theorem mem_centralizer_A_of_commute_D {D : Data G} {L P B : Subgroup G} {p n : ℕ}
    (hH : F08.Hyp8102 D L P p n) (hB : F08.NotationB8103 L P n B)
    {R E Dsub A : Subgroup G} (hRX : R ≤ centralizer (B : Set G))
    (hEall : ∀ y ∈ P, y ^ 3 = 1 → y ∈ E)
    (hBDE : B ⊔ Dsub = E) (hA : F08.NotationA8103 L P p n A)
    {x : G} (hxR : x ∈ R) (hxD : ∀ d ∈ Dsub, x * d = d * x) :
    x ∈ centralizer (A : Set G) := by
  let X := centralizer (B : Set G)
  have hxX : x ∈ X := hRX hxR
  have hB_le_cent : B ≤ centralizer ({x} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hxX b hb
  have hD_le_cent : Dsub ≤ centralizer ({x} : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hxD d hd).symm
  have hBD_le_cent : B ⊔ Dsub ≤ centralizer ({x} : Set G) := sup_le hB_le_cent hD_le_cent
  have hx_cent_BD : x ∈ centralizer ((B ⊔ Dsub : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y * x = x * y := by
      simpa [Subgroup.mem_centralizer_singleton_iff] using hBD_le_cent hy
    exact hy'
  have hx_cent_E : x ∈ centralizer (E : Set G) := by
    rwa [hBDE] at hx_cent_BD
  have hAE : A ≤ E := by
    intro a ha
    refine hEall a (hA.2.1 ha) ?_
    have h := pow_card_eq_one' (x := (⟨a, ha⟩ : A))
    rw [hA.1] at h
    exact congrArg Subtype.val h
  exact (Subgroup.centralizer_le hAE) hx_cent_E

private theorem mem_normalizer_K_of_centralizes_A {D : Data G} {L P B : Subgroup G} {p n : ℕ}
    (hSg : SigmaStd D) (hK2 : KU45Syl3) (h8103 : R8103At D L P p n)
    (hH : F08.Hyp8102 D L P p n)
    {K R A : Subgroup G} (hKdef : K = F08.KOf8103 L B)
    (hRX : R ≤ centralizer (B : Set G))
    (hA : F08.NotationA8103 L P p n A)
    {x : G} (hxR : x ∈ R) (hx_cent_A : x ∈ centralizer (A : Set G)) :
    x ∈ normalizer (K : Set G) := by
  let X := centralizer (B : Set G)
  have hxX : x ∈ X := hRX hxR
  have hx_NA : x ∈ normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer (A : Set G) hx_cent_A
  have hAU : A ∈ uniqueSet D.M := h8103.2.2.2.2.2.1 A hA
  have hxM : x ∈ D.M :=
    CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hAU hx_NA
  have hEven : Even n := h8103.1
  have hX : IsU45 (Bar2 L) n := isU45_of_hyp8102 hH hEven
  have hNM : D.M ≤ normalizer (L : Set G) := le_normalizer_of_hyp8102 hSg hK2 hH hX
  have hxNL : x ∈ normalizer (L : Set G) := hNM hxM
  have hxNX : x ∈ normalizer (X : Set G) := Subgroup.le_normalizer hxX
  have hxNLX : x ∈ normalizer ((L ⊓ X : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at hxNL hxNX ⊢
    intro y
    exact ⟨fun h => ⟨(hxNL y).1 h.1, (hxNX y).1 h.2⟩,
           fun h => ⟨(hxNL y).2 h.1, (hxNX y).2 h.2⟩⟩
  rw [hKdef]
  exact normalizer_inf_le_normalizer_K (L := L) (B := B) hxNLX

private theorem mem_centralizer_K_of_mem_normalizer_K {K R : Subgroup G}
    (hKleR : K ≤ normalizer (R : Set G)) (hRK : R ⊓ K = ⊥)
    {x : G} (hxR : x ∈ R) (hxNK : x ∈ normalizer (K : Set G)) :
    x ∈ centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hcK : x * k * x⁻¹ * k⁻¹ ∈ K := by
    have h1 : x * k * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hxNK k).mp hk
    exact K.mul_mem h1 (K.inv_mem hk)
  have hcR : x * k * x⁻¹ * k⁻¹ ∈ R := by
    have hkNR : k ∈ normalizer (R : Set G) := hKleR hk
    have h1 : k * x⁻¹ * k⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hkNR x⁻¹).mp (R.inv_mem hxR)
    have h2 : x * (k * x⁻¹ * k⁻¹) ∈ R := R.mul_mem hxR h1
    simpa [mul_assoc] using h2
  have hc_bot : x * k * x⁻¹ * k⁻¹ ∈ R ⊓ K := ⟨hcR, hcK⟩
  rw [hRK] at hc_bot
  have hc_one : x * k * x⁻¹ * k⁻¹ = 1 := Subgroup.mem_bot.mp hc_bot
  have h1 : x * k * x⁻¹ = k := mul_inv_eq_one.mp hc_one
  have hcomm : x * k = k * x := by
    calc x * k = (x * k * x⁻¹) * x := by group
      _ = k * x := by rw [h1]
  exact hcomm.symm

private theorem mem_centralizer_K_of_commute_D {D : Data G} {L P B : Subgroup G} {p n : ℕ}
    (hSg : SigmaStd D) (hK2 : KU45Syl3) (h8103 : R8103At D L P p n)
    (hH : F08.Hyp8102 D L P p n)
    (hB : F08.NotationB8103 L P n B)
    {K R E Dsub A : Subgroup G} (hKdef : K = F08.KOf8103 L B)
    (hRX : R ≤ centralizer (B : Set G)) (hKleR : K ≤ normalizer (R : Set G))
    (hRK : R ⊓ K = ⊥) (hEall : ∀ y ∈ P, y ^ 3 = 1 → y ∈ E)
    (hBDE : B ⊔ Dsub = E) (hA : F08.NotationA8103 L P p n A)
    {x : G} (hxR : x ∈ R) (hxD : ∀ d ∈ Dsub, x * d = d * x) :
    x ∈ centralizer (K : Set G) := by
  have hx_cent_A :=
    mem_centralizer_A_of_commute_D hH hB hRX hEall hBDE hA hxR hxD
  have hxNK :=
    mem_normalizer_K_of_centralizes_A hSg hK2 h8103 hH hKdef hRX hA hxR hx_cent_A
  exact mem_centralizer_K_of_mem_normalizer_K hKleR hRK hxR hxNK

private theorem exists_conj_mem_P_of_pow_three_eq_one {B P : Subgroup G}
    (hPX : IsSylowOf 3 P (centralizer (B : Set G)))
    {x : G} (hxX : x ∈ centralizer (B : Set G)) (hx3 : x ^ 3 = 1) :
    ∃ k ∈ centralizer (B : Set G), k⁻¹ * x * k ∈ P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X := centralizer (B : Set G)
  let x' : X := ⟨x, hxX⟩
  have hx'3 : x' ^ 3 = 1 := by ext; simpa using hx3
  have hzpow3 : IsPGroup 3 (Subgroup.zpowers x') := by
    have hdvd : orderOf x' ∣ 3 := orderOf_dvd_of_pow_eq_one hx'3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3, pow_one])
  obtain ⟨Q, hQ⟩ := hzpow3.exists_le_sylow
  let Q' : Subgroup G := (Q : Subgroup X).map X.subtype
  have hQ'sylow : IsSylowOf 3 Q' X := ⟨Q, rfl⟩
  obtain ⟨k, hkX, hkconj⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hPX hQ'sylow
  refine ⟨k, hkX, ?_⟩
  have hx'Q : x' ∈ (Q : Subgroup X) := hQ (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
  have hxQ' : x ∈ Q' := Subgroup.mem_map.mpr ⟨x', hx'Q, rfl⟩
  exact (hkconj x).mp hxQ'

private theorem R_inf_E_eq_B {B Dsub R E K : Subgroup G}
    (hBcard : Nat.card B = 3) (hDcard : Nat.card Dsub = 3)
    (hBR : B ≤ R) (hDK : Dsub ≤ K)
    (hBDE : B ⊔ Dsub = E) (hEcard : Nat.card E = 9)
    (hRK : R ⊓ K = ⊥) :
    (R ⊓ E : Subgroup G) = B := by
  have hB_le_RE : B ≤ (R ⊓ E : Subgroup G) := le_inf hBR (hBDE ▸ le_sup_left)
  have hRE_le_E : (R ⊓ E : Subgroup G) ≤ E := inf_le_right
  have hcard_dvd : Nat.card ((R ⊓ E : Subgroup G)) ∣ Nat.card E :=
    Subgroup.card_dvd_of_le hRE_le_E
  rw [hEcard] at hcard_dvd
  have hRE_ne_E : (R ⊓ E : Subgroup G) ≠ E := by
    intro h
    have hD_le_R : Dsub ≤ R := by
      have hD_le_E : Dsub ≤ E := hBDE ▸ le_sup_right
      rw [← h] at hD_le_E
      exact hD_le_E.trans inf_le_left
    have hD_le_RK : Dsub ≤ R ⊓ K := le_inf hD_le_R hDK
    rw [hRK] at hD_le_RK
    have hD_bot : Dsub = ⊥ := le_bot_iff.mp hD_le_RK
    have hDcard1 : Nat.card Dsub = 1 := by rw [hD_bot, Subgroup.card_bot]
    omega
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow (p := 3) (m := 2) Nat.prime_three).mp hcard_dvd
  have hk1 : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hcardB : Nat.card B ≤ Nat.card ((R ⊓ E : Subgroup G)) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hB_le_RE)
    rw [hk, hk0] at hcardB
    norm_num at hcardB
    rw [hBcard] at hcardB
    omega
  have hk2 : k = 1 := by
    by_contra h
    have hk2' : k = 2 := by omega
    have hcard9 : Nat.card ((R ⊓ E : Subgroup G)) = 9 := by rw [hk, hk2']; norm_num
    have : (R ⊓ E : Subgroup G) = E := Subgroup.eq_of_le_of_card_ge hRE_le_E (by omega)
    exact hRE_ne_E this
  refine le_antisymm ?_ hB_le_RE
  by_contra hnot
  have hne : B ≠ (R ⊓ E : Subgroup G) := by
    intro h
    exact hnot (h ▸ le_rfl)
  have hlt : B < (R ⊓ E : Subgroup G) := lt_of_le_of_ne hB_le_RE hne
  have hcard_lt : Nat.card B < Nat.card ((R ⊓ E : Subgroup G)) := Subgroup.card_lt_of_lt hlt
  rw [hBcard, hk, hk2] at hcard_lt
  norm_num at hcard_lt

private theorem mem_B_of_pow_three_eq_one {B Dsub R E K P : Subgroup G}
    (hPX : IsSylowOf 3 P (centralizer (B : Set G)))
    (hRX : R ≤ centralizer (B : Set G))
    (hXleR : centralizer (B : Set G) ≤ normalizer (R : Set G))
    (hRK : R ⊓ K = ⊥)
    (hEall : ∀ y ∈ P, y ^ 3 = 1 → y ∈ E)
    (hRE : (R ⊓ E : Subgroup G) = B)
    {x : G} (hxR : x ∈ R) (hx3 : x ^ 3 = 1) :
    x ∈ B := by
  have hxX : x ∈ centralizer (B : Set G) := hRX hxR
  obtain ⟨k, hkX, hyP⟩ := exists_conj_mem_P_of_pow_three_eq_one hPX hxX hx3
  have hy3 : (k⁻¹ * x * k) ^ 3 = 1 := by
    have h : k⁻¹ * x * k = k⁻¹ * x * (k⁻¹)⁻¹ := by simp
    rw [h, conj_pow, hx3, mul_one]
    simp
  have hyE : k⁻¹ * x * k ∈ E := hEall _ hyP hy3
  have hyR : k⁻¹ * x * k ∈ R := by
    have hkNR : k ∈ normalizer (R : Set G) := hXleR hkX
    have hkinv : k⁻¹ ∈ normalizer (R : Set G) := (Subgroup.normalizer (R : Set G)).inv_mem hkNR
    have h := (Subgroup.mem_normalizer_iff.mp hkinv x).mp hxR
    simpa using h
  have hyB : k⁻¹ * x * k ∈ B := by
    rw [← hRE]
    exact ⟨hyR, hyE⟩
  have hkcent : k ∈ centralizer (B : Set G) := hkX
  have hy_comm : k * (k⁻¹ * x * k) * k⁻¹ = k⁻¹ * x * k := by
    have hcomm : k * (k⁻¹ * x * k) = (k⁻¹ * x * k) * k :=
      (Subgroup.mem_centralizer_iff.mp hkcent (k⁻¹ * x * k) hyB).symm
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hxB : x ∈ B := by
    have hx_eq : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
    rw [hx_eq, hy_comm]
    exact hyB
  exact hxB

private theorem D_le_E_and_B_le_E {B Dsub E P : Subgroup G}
    (hEall : ∀ y ∈ P, y ^ 3 = 1 → y ∈ E)
    (hBcard : Nat.card B = 3) (hDcard : Nat.card Dsub = 3)
    (hBP : B ≤ P) (hDP : Dsub ≤ P) :
    Dsub ≤ E ∧ B ≤ E := by
  constructor
  · intro d hd
    refine hEall d (hDP hd) ?_
    have h := pow_card_eq_one' (x := (⟨d, hd⟩ : Dsub))
    rw [hDcard] at h
    exact congrArg Subtype.val h
  · intro b hb
    refine hEall b (hBP hb) ?_
    haveI : IsCyclic B := isCyclic_of_prime_card (p := 3) hBcard
    have h := pow_card_eq_one' (x := (⟨b, hb⟩ : B))
    rw [hBcard] at h
    exact congrArg Subtype.val h

private theorem exists_le_centralizer_inputs {D : Data G} {L P B : Subgroup G} {p n : ℕ}
    (hK2 : KU45Syl3) (hSg : SigmaStd D) (h8103 : R8103At D L P p n)
    (hH : F08.Hyp8102 D L P p n) (hB : F08.NotationB8103 L P n B)
    (hX2 : pCoreOf 2 (centralizer (B : Set G)) = ⊥) :
    ∃ Dsub : Subgroup G,
      Dsub ≤ F08.KOf8103 L B ∧ Nat.card Dsub = 3 ∧
      (∀ x ∈ CFSG.fittingSubgroupOf (centralizer (B : Set G)),
        (∀ d ∈ Dsub, x * d = d * x) →
          x ∈ centralizer (F08.KOf8103 L B : Set G)) ∧
      (∀ x ∈ CFSG.fittingSubgroupOf (centralizer (B : Set G)),
        x ^ 3 = 1 → x ∈ B) := by
  let X := centralizer (B : Set G)
  let K := F08.KOf8103 L B
  let R := CFSG.fittingSubgroupOf X
  have hEven : Even n := h8103.1
  have hX : IsU45 (Bar2 L) n := isU45_of_hyp8102 hH hEven
  have hP : IsSylowOf 3 P L := hH.2.2.2.2
  have hPcent : P ≤ X := le_centralizer_of_notationB8103 hK2 hX hP hB
  have hP3 : IsSylowOf 3 P ⊤ := h8103.2.2.2.2.2.2.2
  have hPX : IsSylowOf 3 P X := hP3.of_le hPcent le_top
  have hBcard : Nat.card B = 3 := hB.1
  have hn2 : 2 ≤ n := two_le_n hSg h8103 hH
  have hRKbot : R ⊓ K = ⊥ :=
    R_inf_K_eq_bot hB.2.2 (by omega) K_le_normalizer_R (R_odd (B := B) hX2)
  obtain ⟨E, hEP, hEel, hEcard, hEall⟩ :=
    exists_elemAbelian_nine (L := L) (P := P) (n := n) hK2 hX hP
  obtain ⟨Dsub, hDsub_le, hDcard⟩ := exists_D (hK2 := hK2) (D := D) hH hB h8103
  have hDK : Dsub ≤ K := hDsub_le.trans inf_le_right
  have hDP : Dsub ≤ P := hDsub_le.trans inf_le_left
  have hBR : B ≤ R := B_le_R hBcard
  have hDE_BE := D_le_E_and_B_le_E hEall hBcard hDcard hB.2.1 hDP
  have hDE : Dsub ≤ E := hDE_BE.1
  have hBE : B ≤ E := hDE_BE.2
  have hBDE : B ⊔ Dsub = E :=
    B_sup_D_eq_E hBcard hDcard hBE hDE hEcard hBR hDK hRKbot
  have hRE : (R ⊓ E : Subgroup G) = B :=
    R_inf_E_eq_B hBcard hDcard hBR hDK hBDE hEcard hRKbot
  obtain ⟨A, hA⟩ := h8103.2.2.2.1
  refine ⟨Dsub, hDK, hDcard, ?_, ?_⟩
  · intro x hxR hxD
    exact mem_centralizer_K_of_commute_D (D := D) hSg hK2 h8103 hH hB
      (K := K) (R := R) (E := E) (Dsub := Dsub) (A := A)
      (by rfl) (Subgroup.map_subtype_le _) K_le_normalizer_R hRKbot hEall hBDE hA hxR hxD
  · intro x hxR hx3
    exact mem_B_of_pow_three_eq_one (B := B) (Dsub := Dsub) (R := R) (E := E) (K := K) (P := P)
      hPX (Subgroup.map_subtype_le _) (X_le_normalizer_R (B := B)) hRKbot hEall hRE hxR hx3

theorem fittingSubgroupOf_le_centralizer_at (hK2 : KU45Syl3) (hK462 : UCK.K462) {D : Data G}
    (hSg : SigmaStd D) {L P B : Subgroup G} {p n : ℕ} (h8103 : R8103At D L P p n)
    (hH : F08.Hyp8102 D L P p n) (hB : F08.NotationB8103 L P n B)
    (hX2 : pCoreOf 2 (centralizer (B : Set G)) = ⊥) :
    CFSG.fittingSubgroupOf (centralizer (B : Set G)) ≤
      centralizer (F08.KOf8103 L B : Set G) := by
  let K := F08.KOf8103 L B
  let R := CFSG.fittingSubgroupOf (centralizer (B : Set G))
  have hB1 : B ≠ ⊥ := by
    intro h
    have h1 : Nat.card B = 1 := by rw [h, Subgroup.card_bot]
    have h3 : Nat.card B = 3 := hB.1
    omega
  haveI : Group.IsPerfect ↥K := K_isPerfect (L := L) (B := B)
  have hKperf : ⁅K, K⁆ = K :=
    CFSG.GroupTheory.commutator_eq_self_of_isPerfect_subgroup (P := K)
  have hKk : CFSG.Open.IsKGroup ↥K := K_isKGroup (D := D) hB1
  have hL2 : IsL2 (Bar2 K) (2 * n) := hB.2.2
  have hRK : K ≤ normalizer (R : Set G) := K_le_normalizer_R
  have hRs : IsSolvable ↥R := R_solvable (B := B)
  have hRodd : Odd (Nat.card R) := R_odd (B := B) hX2
  have hBcard : Nat.card B = 3 := hB.1
  have hn2 : 2 ≤ n := two_le_n hSg h8103 hH
  have hm4 : 4 ≤ 2 * n := by omega
  have hme : Even (2 * n) := even_two_mul n
  obtain ⟨Dsub, hDK, hDcard, hCD, hB0R⟩ :=
    exists_le_centralizer_inputs (D := D) hK2 hSg h8103 hH hB hX2
  exact le_centralizer_of_odd hK462 hKperf hKk (m := 2 * n) hm4 hme hL2 hRK hRs hRodd
    hBcard hB0R hDK hDcard hCD

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
