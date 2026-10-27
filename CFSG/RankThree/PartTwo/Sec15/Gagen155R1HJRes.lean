module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T114
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
public import CFSG.GroupTheory.CoprimeCosetFixed
public import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.GH74.GLS.C3.Layer1.St1Iv251
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.GroupTheory.PermSylowTwo.SymCore
public import CFSG.RankThree.PartTwo.Sec14.Item146General
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Defs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1VDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_pPrimeCore_of_commute_quotient {C : Subgroup G} {c : G}
    {c' g0 : ↥C} (hc' : (c' : G) = c) {t : ↥C ⧸ CFSG.pPrimeCore 3 ↥C}
    (htc : Commute t (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) c'))
    (hg0 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) g0 = t) :
    (g0 : G)⁻¹ * (c * (g0 : G) * c⁻¹) ∈ pPrimeCoreOf 3 C := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : ↥C →* ↥C ⧸ CFSG.pPrimeCore 3 ↥C := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)
  have hcommt : t * π c' = π c' * t := by
    simpa [π, hg0] using htc.eq
  have hq : π (g0⁻¹ * c' * g0 * c'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg0]
    rw [show t⁻¹ * π c' * t * (π c')⁻¹ = t⁻¹ * (π c' * t) * (π c')⁻¹ by group]
    rw [← hcommt]
    group
  rw [QuotientGroup.mk'_apply] at hq
  have hmem : g0⁻¹ * c' * g0 * c'⁻¹ ∈ CFSG.pPrimeCore 3 ↥C := by
    rwa [QuotientGroup.eq_one_iff] at hq
  have hmemG : ((g0⁻¹ * c' * g0 * c'⁻¹ : ↥C) : G) ∈ pPrimeCoreOf 3 C :=
    Subgroup.mem_map_of_mem C.subtype hmem
  simpa [hc', mul_assoc] using hmemG

private theorem sec14Std_c_mem_res1C {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L) :
    c ∈ Res1C A L := by
  have hAab : CFSG.Assembly.IsElemAbelian 3 A := hS.mem_partTwoF.1
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp hS.zpowers_mem_omegaA).1
  haveI : IsMulCommutative ↥A := hAab.1
  exact (Subgroup.le_centralizer A).trans
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left)) hcA

theorem exists_fixed_mem_coset_of_pPrimeCore {C : Subgroup G} {c : G}
    (hcC : c ∈ C) (hc3 : orderOf c = 3) {g0 : ↥C}
    (hg : (g0 : G)⁻¹ * (c * (g0 : G) * c⁻¹) ∈ pPrimeCoreOf 3 C) :
    ∃ n ∈ pPrimeCoreOf 3 C, c * ((g0 : G) * n) * c⁻¹ = (g0 : G) * n := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Θ : Subgroup G := pPrimeCoreOf 3 C
  have hN : ∀ n ∈ Θ, c * n * c⁻¹ ∈ Θ := by
    intro n hn
    exact (Subgroup.mem_normalizer_iff.mp (Sec14.le_normalizer_pPrimeCoreOf 3 C hcC) n).mp hn
  have hcop : Nat.Coprime (orderOf c) (Nat.card Θ) := by
    rw [hc3]
    simpa [Θ] using coprime_card_pPrimeCoreOf 3 C
  exact CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime Θ hN hg hcop

private theorem res1_exists_centralizing_lift {A L : Subgroup G} {c : G}
    (hS : Sec14Std G A c L) (hA : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    {t : Res1Q A L} {g0 : ↥(Res1C A L)}
    (hg0 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) g0 = t)
    (hg : (g0 : G)⁻¹ * (c * (g0 : G) * c⁻¹) ∈ pPrimeCoreOf 3 (Res1C A L)) :
    ∃ g : ↥(Res1C A L), (g : G) ∈ Subgroup.centralizer (A : Set G) ∧
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) g = t := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := Res1C A L
  let π : ↥(Res1C A L) →* ↥(Res1C A L) ⧸ CFSG.pPrimeCore 3 ↥(Res1C A L) :=
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L))
  let Θ : Subgroup G := pPrimeCoreOf 3 C
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact (zpowers_mem_omegaA_iff.mp hS.zpowers_mem_omegaA).2.1
  have hcC : c ∈ C := by simpa [C] using sec14Std_c_mem_res1C hS
  obtain ⟨n, hnΘ, hfix⟩ := exists_fixed_mem_coset_of_pPrimeCore hcC hc3 hg
  obtain ⟨nC, hnC, hnCval⟩ := Subgroup.mem_map.mp hnΘ
  let g : ↥C := g0 * nC
  have hnCcoe : (nC : G) = n := by simpa using hnCval
  have hgval : (g : G) = (g0 : G) * n := by
    change (g0 : G) * (nC : G) = (g0 : G) * n
    rw [hnCcoe]
  have hfix' : c * (g : G) * c⁻¹ = (g : G) := by
    rw [hgval]
    exact hfix
  have hgcomm : c * (g : G) = (g : G) * c := by
    calc c * (g : G) = (c * (g : G) * c⁻¹) * c := by group
      _ = (g : G) * c := by rw [hfix']
  have hgB : (g : G) ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) := g.2
  have hgc : (g : G) ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hgcomm.symm
  have hgA : (g : G) ∈ Subgroup.centralizer (A : Set G) := by
    refine Sec14.mem_centralizer_of_le_sup (B := A ⊓ L) (c := c) ?_ hgB hgc
    rw [sup_comm, ← hA]
  have hnCker : π nC = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hnC
  have hgmap : π g = t := by simp [g, π, map_mul, hg0, hnCker]
  exact ⟨g, hgA, hgmap⟩

theorem res1_exists_five_lift {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    (hA : A = Subgroup.zpowers c ⊔ (A ⊓ L)) {c' : ↥(Res1C A L)} (hc' : (c' : G) = c)
    {t : Res1Q A L} (ht5 : orderOf t = 5)
    (htc : Commute t (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) c')) :
    ∃ f : ↥(Res1C A L), (f : G) ∈ Subgroup.centralizer (A : Set G) ∧
      (∃ k : ℕ, orderOf f = 5 ^ k) ∧ QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) f = t := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := Res1C A L
  let π : ↥(Res1C A L) →* ↥(Res1C A L) ⧸ CFSG.pPrimeCore 3 ↥(Res1C A L) :=
    QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L))
  obtain ⟨g0, hg0⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥C) t
  have hgmem := conj_mem_pPrimeCore_of_commute_quotient (C := C) hc' htc hg0
  obtain ⟨g, hgA, hgmap⟩ := res1_exists_centralizing_lift hS hA hg0 hgmem
  have hn0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨a, r, hr5, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 5 (by norm_num)
  have hrpos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · rw [hr, mul_zero] at hord
      exact absurd hord hn0
    · exact hr
  have h5dvd : 5 ∣ orderOf g := by
    have hmap : orderOf (π g) ∣ orderOf g := orderOf_map_dvd π g
    rwa [hgmap, ht5] at hmap
  have hcopr : Nat.Coprime r (orderOf t) := by
    rw [ht5]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hr5).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := t) (n := r) hcopr
  let gr : ↥C := g ^ r
  let f : ↥C := gr ^ m
  refine ⟨f, ?_, ?_, ?_⟩
  · have hfg : (f : G) = (g : G) ^ (r * m) := by
      simp [f, gr, pow_mul]
    rw [hfg]
    exact Subgroup.pow_mem (Subgroup.centralizer (A : Set G)) hgA (r * m)
  · have hordgr : orderOf gr = 5 ^ a := by
      have hdvd : r ∣ orderOf g := ⟨5 ^ a, by rw [hord, mul_comm]⟩
      rw [show gr = g ^ r from rfl, orderOf_pow_of_dvd hrpos.ne' hdvd, hord,
        mul_comm (5 ^ a) r, Nat.mul_div_right _ hrpos]
    have hdiv : orderOf f ∣ 5 ^ a := by
      simpa [f, hordgr] using orderOf_pow_dvd (x := gr) m
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hdiv
    exact ⟨k, hk⟩
  · have hfpi : π f = t := by
      simp [f, gr, π, map_pow, hgmap, hm]
    simpa [π] using hfpi

theorem sup_eq_of_isHyperplane_of_ne {A B B' : Subgroup G} (hA : Nat.card A = 27)
    (hB : IsHyperplane A B) (hB' : IsHyperplane A B') (hne : B ≠ B') :
    B ⊔ B' = A := by
  have hB9 : Nat.card B = 9 := by have := hB.2; omega
  have hB'9 : Nat.card B' = 9 := by have := hB'.2; omega
  have hle : B ⊔ B' ≤ A := sup_le hB.1 hB'.1
  have hlt : B < B ⊔ B' := by
    refine lt_of_le_of_ne le_sup_left fun h => hne ?_
    have hB'B : B' ≤ B := by
      rw [h]
      exact le_sup_right
    have hcard : Nat.card B ≤ Nat.card B' := by rw [hB9, hB'9]
    exact (Subgroup.eq_of_le_of_card_ge hB'B hcard).symm
  have hcard_gt : 9 < Nat.card (B ⊔ B' : Subgroup G) := by
    rw [← hB9]
    exact Subgroup.card_lt_of_lt hlt
  have hdvd : Nat.card (B ⊔ B' : Subgroup G) ∣ 27 := by
    rw [← hA]
    exact Subgroup.card_dvd_of_le hle
  have hdvd' : Nat.card (B ⊔ B' : Subgroup G) ∣ 3 ^ 3 := by simpa using hdvd
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd'
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0] at hk
      rw [hk] at hcard_gt
      norm_num at hcard_gt
    · exact hkpos
  have hk3' : k = 3 := by
    interval_cases k <;> norm_num at hk hcard_gt ⊢ <;> omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hA, hk, hk3']; norm_num)

private theorem mem_pPrimeCore_centralizer_of_mem_pPrimeCore_of_mem_centralizer
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    (hhyp : IsHyperplane A (A ⊓ L)) {B : Subgroup G} (hB : IsHyperplane A B)
    (hne : B ≠ A ⊓ L) {theta : G}
    (hthetaΘ : theta ∈ pPrimeCoreOf 3 (Res1C A L))
    (hthetaB : theta ∈ Subgroup.centralizer (B : Set G)) :
    theta ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := Res1C A L
  let Θ : Subgroup G := pPrimeCoreOf 3 C
  let D : Subgroup G := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
  have hE27 : Late.IsE27 A := Late.isE27_of_mem_partTwoE hS.mem_partTwoE
  have hA27 : Nat.card A = 27 := hE27.2
  have hsup : B ⊔ (A ⊓ L) = A := sup_eq_of_isHyperplane_of_ne hA27 hB hhyp hne
  have hthetaC : theta ∈ C := Sec14.pPrimeCoreOf_le 3 C hthetaΘ
  have hthetaBL : theta ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) := hthetaC
  have hthetaA : theta ∈ Subgroup.centralizer (A : Set G) := by
    have hK : Subgroup.zpowers theta ≤ Subgroup.centralizer (A : Set G) := by
      rw [← hsup]
      exact CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers
        (Subgroup.zpowers_le.mpr hthetaB) (Subgroup.zpowers_le.mpr hthetaBL)
    exact hK (Subgroup.mem_zpowers theta)
  have htheta3 : ¬ 3 ∣ Nat.card (Subgroup.zpowers theta) := by
    have horddvd : orderOf theta ∣ Nat.card Θ := Subgroup.orderOf_dvd_natCard _ hthetaΘ
    have hcop3 : Nat.Coprime 3 (Nat.card Θ) := by
      simpa [Θ] using coprime_card_pPrimeCoreOf 3 C
    rw [Nat.card_zpowers]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Nat.Coprime.coprime_dvd_right horddvd hcop3)
  have hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A :=
    ⟨hE27.1, fun y hy hAy => (hS.mem_partTwoF.2.1 y hy hAy).le⟩
  have hle := Sec14.inf_centralizer_le_xA (A := A) (Q := Subgroup.zpowers theta)
    hAmax htheta3
  exact hle ⟨Subgroup.mem_zpowers theta, hthetaA⟩

private theorem exists_mem_pPrimeCore_mul_of_mem_sup_of_mem_centralizer
    {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    (hhyp : IsHyperplane A (A ⊓ L)) {B : Subgroup G} (hB : IsHyperplane A B)
    (hne : B ≠ A ⊓ L) {w : G}
    (hwSup : w ∈ pPrimeCoreOf 3 (Res1C A L) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
    (hwCB : w ∈ Subgroup.centralizer (B : Set G)) :
    ∃ theta ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)),
      ∃ d ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)), theta * d = w := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := Res1C A L
  let Θ : Subgroup G := pPrimeCoreOf 3 C
  let D : Subgroup G := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
  have hDleC : D ≤ C :=
    (Sec14.pPrimeCoreOf_le 3 (Subgroup.centralizer (A : Set G))).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left))
  have hDnorm : D ≤ Subgroup.normalizer (Θ : Set G) := by
    simpa [Θ] using hDleC.trans (Sec14.le_normalizer_pPrimeCoreOf 3 C)
  have hcoe : ((Θ ⊔ D : Subgroup G) : Set G) = (Θ : Set G) * (D : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Θ D hDnorm
  have hwMul : w ∈ (Θ : Set G) * (D : Set G) := by
    rw [← hcoe]
    exact hwSup
  obtain ⟨theta, hthetaΘ, d, hdD, hwd⟩ := Set.mem_mul.mp hwMul
  have hthetaB : theta ∈ Subgroup.centralizer (B : Set G) := by
    have htheta : theta = w * d⁻¹ := by
      calc theta = theta * d * d⁻¹ := by group
        _ = w * d⁻¹ := by rw [hwd]
    rw [htheta]
    exact Subgroup.mul_mem _ hwCB
      (Subgroup.inv_mem _ ((Sec14.pPrimeCoreOf_le 3 (Subgroup.centralizer (A : Set G))).trans
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hB.1)) hdD))
  have hthetaD : theta ∈ D :=
    mem_pPrimeCore_centralizer_of_mem_pPrimeCore_of_mem_centralizer hS hhyp hB hne hthetaΘ hthetaB
  exact ⟨theta, hthetaD, d, hdD, hwd⟩

theorem mem_scriptQ_of_le_sup {A L : Subgroup G} {c : G} (hS : Sec14Std G A c L)
    (hhyp : IsHyperplane A (A ⊓ L)) {Q : Subgroup G}
    (hQA : A ≤ Subgroup.normalizer (Q : Set G)) (hQ3 : ¬ 3 ∣ Nat.card Q)
    (hQ : Q ≤ pPrimeCoreOf 3 (Res1C A L) ⊔ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :
    Q ∈ scriptQ A (lB A) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := Res1C A L
  let Θ : Subgroup G := pPrimeCoreOf 3 C
  let D : Subgroup G := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
  have hE27 : Late.IsE27 A := Late.isE27_of_mem_partTwoE hS.mem_partTwoE
  have hA27 : Nat.card A = 27 := hE27.2
  refine mem_scriptQ_iff.mpr ⟨(isPiSubgroup_piCompl_iff Nat.prime_three Q).mpr hQ3, hQA, ?_⟩
  intro B hB
  by_cases hBeq : B = A ⊓ L
  · subst B
    have hle : Θ ⊔ D ≤ qBound A (lB A) (A ⊓ L) := by
      unfold qBound
      exact le_sup_left
    exact (inf_le_left.trans hQ).trans hle
  · intro w hw
    have hwSup : w ∈ Θ ⊔ D := hQ hw.1
    obtain ⟨theta, hthetaD, d, hdD, hwd⟩ :=
      exists_mem_pPrimeCore_mul_of_mem_sup_of_mem_centralizer hS hhyp hB hBeq hwSup hw.2
    have hwD : w ∈ D := by
      rw [← hwd]
      exact D.mul_mem hthetaD hdD
    have hDq : D ≤ qBound A (lB A) B := by
      unfold qBound
      exact (le_sup_right : D ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ D).trans le_sup_left
    exact hDq hwD

private theorem wE155_normalizer_le_res1C {A L X K Y M T : Subgroup G}
    (hC : Ctx155 A X K Y M T) (hLX : L ≤ X) :
    A ≤ Subgroup.normalizer ((wE155 A M : Subgroup G) : Set G) ∧
      wE155 A M ≤ Res1C A L ∧ IsPGroup 2 (wE155 A M) := by
  have hAM : A ≤ M := fun a ha => hC.mem_m.2 (le_sup_left (b := Y) ha)
  have hAE : A ≤ Subgroup.normalizer
      ((oPrimeResidualOf 3 (delta A (lB A) M) : Subgroup G) : Set G) :=
    Sec14.le_normalizer_oPrimeResidualOf (Sec14.le_normalizer_delta (A := A) (LB := lB A) M)
  have hAW : A ≤ Subgroup.normalizer ((wE155 A M : Subgroup G) : Set G) :=
    Late.le_normalizer_inf (hAM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      fun a ha => CFSG.GH74.GLS.C3.Layer1.Iv251.mem_normalizer_centralizer (hAE ha)
  have hWleC : wE155 A M ≤ Res1C A L :=
    (inf_le_right : wE155 A M ≤ Subgroup.centralizer
      ((oPrimeResidualOf 3 (delta A (lB A) M) : Subgroup G) : Set G)).trans
      ((Subgroup.centralizer_le
          (SetLike.coe_subset_coe.mpr (Sylow155R1.x_le_oPrimeResidualOf_delta hC))).trans
        ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hLX)).trans
          (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right))))
  have hW2 : IsPGroup 2 (wE155 A M) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left
  exact ⟨hAW, hWleC, hW2⟩

private theorem mem_sup_pPrimeCore_of_wE155_conj_mem {A L : Subgroup G} {c : G}
    {M : Subgroup G} (hS : Sec14Std G A c L) (hA : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hWleC : wE155 A M ≤ Res1C A L)
    (hQ3 : ¬ 3 ∣ Nat.card (wE155 A M ⊔ pPrimeCoreOf 3 (Res1C A L) : Subgroup G))
    {w : G} (hwW : w ∈ wE155 A M)
    (hconj : w⁻¹ * (c * w * c⁻¹) ∈ pPrimeCoreOf 3 (Res1C A L)) :
    w ∈ pPrimeCoreOf 3 (Res1C A L) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := Res1C A L
  let Θ : Subgroup G := pPrimeCoreOf 3 C
  let D : Subgroup G := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
  let W : Subgroup G := wE155 A M
  have hE27 : Late.IsE27 A := Late.isE27_of_mem_partTwoE hS.mem_partTwoE
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact (zpowers_mem_omegaA_iff.mp hS.zpowers_mem_omegaA).2.1
  have hcC : c ∈ C := by simpa [C] using sec14Std_c_mem_res1C hS
  have hwC : w ∈ C := hWleC hwW
  obtain ⟨n, hnΘ, hfix⟩ := exists_fixed_mem_coset_of_pPrimeCore (C := C) hcC hc3
    (g0 := ⟨w, hwC⟩) (by simpa using hconj)
  let g : G := w * n
  have hgC : g ∈ C := C.mul_mem (hWleC hwW) (Sec14.pPrimeCoreOf_le 3 C hnΘ)
  have hfix' : c * g * c⁻¹ = g := hfix
  have hgcomm : c * g = g * c := by
    calc c * g = (c * g * c⁻¹) * c := by group
      _ = g * c := by rw [hfix']
  have hgB : g ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) := hgC
  have hgc : g ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hgcomm.symm
  have hgA : g ∈ Subgroup.centralizer (A : Set G) := by
    refine Sec14.mem_centralizer_of_le_sup (B := A ⊓ L) (c := c) ?_ hgB hgc
    rw [sup_comm, ← hA]
  have hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A :=
    ⟨hE27.1, fun y hy hAy => (hS.mem_partTwoF.2.1 y hy hAy).le⟩
  have hgQ : g ∈ W ⊔ Θ := Subgroup.mul_mem_sup hwW hnΘ
  have hgD : g ∈ D := by
    have hle := Sec14.inf_centralizer_le_xA (A := A) (Q := W ⊔ Θ) hAmax hQ3
    exact hle ⟨hgQ, hgA⟩
  have hw_eq : w = g * n⁻¹ := by
    change w = w * n * n⁻¹
    group
  have hwDΘ : w ∈ D ⊔ Θ := by
    rw [hw_eq]
    exact Subgroup.mul_mem_sup hgD (Θ.inv_mem hnΘ)
  rwa [sup_comm] at hwDΘ

private theorem wE155_le_sup_of_forall_conj {A L : Subgroup G} {c : G} {M : Subgroup G}
    (hS : Sec14Std G A c L) (hA : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hWleC : wE155 A M ≤ Res1C A L) (hW3 : ¬ 3 ∣ Nat.card (wE155 A M))
    (hcon : ∀ w ∈ wE155 A M, ∀ x : ↥(Res1C A L), (x : G) = w * c * w⁻¹ * c⁻¹ →
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x = 1) :
    wE155 A M ≤ pPrimeCoreOf 3 (Res1C A L) ⊔
      pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup G := Res1C A L
  let Θ : Subgroup G := pPrimeCoreOf 3 C
  let W : Subgroup G := wE155 A M
  have hΘ3 : ¬ 3 ∣ Nat.card Θ := by
    simpa [Θ] using
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 C)
  have hWnormΘ : W ≤ Subgroup.normalizer (Θ : Set G) := by
    simpa [Θ] using hWleC.trans (Sec14.le_normalizer_pPrimeCoreOf 3 C)
  have hQ3 : ¬ 3 ∣ Nat.card (W ⊔ Θ : Subgroup G) := by
    have hcard := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := W) (K := Θ) hWnormΘ
    intro hdvd
    have hprod : 3 ∣ Nat.card W * Nat.card Θ := by
      rw [← hcard]
      exact dvd_mul_of_dvd_left hdvd _
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hprod with h | h
    · exact hW3 h
    · exact hΘ3 h
  have hcC : c ∈ C := by simpa [C] using sec14Std_c_mem_res1C hS
  intro w hwW
  have hwC : w ∈ C := hWleC hwW
  have hwInvC : w⁻¹ ∈ C := C.inv_mem hwC
  let uC : ↥C := ⟨w⁻¹ * (c * w * c⁻¹),
    C.mul_mem hwInvC (C.mul_mem (C.mul_mem hcC hwC) (C.inv_mem hcC))⟩
  have hπu : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) uC = 1 := by
    apply hcon w⁻¹ (W.inv_mem hwW) uC
    simp only [uC]
    group
  have huΘ : (uC : G) ∈ Θ := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπu
    exact Subgroup.mem_map_of_mem C.subtype hπu
  exact mem_sup_pPrimeCore_of_wE155_conj_mem hS hA hWleC hQ3 hwW huΘ

theorem res1_exists_commutator_ne_one {A L : Subgroup G} {c : G} {X K Y M T : Subgroup G}
    (hS : Sec14Std G A c L) (hhyp : IsHyperplane A (A ⊓ L))
    (hA : A = Subgroup.zpowers c ⊔ (A ⊓ L)) (hC : Ctx155 A X K Y M T) (hLX : L ≤ X)
    (hW : wE155 A M ∉ scriptQ A (lB A)) :
    ∃ w ∈ wE155 A M, ∃ x : ↥(Res1C A L), (x : G) = w * c * w⁻¹ * c⁻¹ ∧
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x ≠ 1 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hAW, hWleC, hW2⟩ := wE155_normalizer_le_res1C (A := A) (L := L) (M := M) hC hLX
  have hW3 : ¬ 3 ∣ Nat.card (wE155 A M) :=
    CFSG.GroupTheory.PermSylowTwo.not_three_dvd_card_of_isPGroup_two hW2
  have hWle := wE155_le_sup_of_forall_conj (M := M) hS hA hWleC hW3 hcon
  exact hW (mem_scriptQ_of_le_sup hS hhyp hAW hW3 hWle)

end CFSG.RankThree.PartTwo.Sec15.Gagen155R1HJ
