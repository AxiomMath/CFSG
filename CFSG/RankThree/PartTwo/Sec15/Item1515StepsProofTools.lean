module

import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Late.Transitivity
public import CFSG.RankThree.PartTwo.Sec15.Item157

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1515

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Generic

variable {X : Type*} [Group X] [Finite X]

theorem card_quotient_le_of_le {N M : Subgroup X} (h : N ≤ M) :
    Nat.card (X ⧸ M) ≤ Nat.card (X ⧸ N) :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le h)

theorem surjective_of_coprime_ker {Q : Type*} [Group Q] [Finite Q] (f : X →* Q)
    (hker : Nat.Coprime 3 (Nat.card f.ker))
    (hcard : Nat.card Q ≤ Nat.card (X ⧸ CFSG.pPrimeCore 3 X)) : Function.Surjective f := by
  have hle : f.ker ≤ CFSG.pPrimeCore 3 X := le_sSup ⟨f.normal_ker, hker⟩
  have h1 := card_quotient_le_of_le hle
  have h2 : Nat.card (X ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have h3 : Nat.card f.range = Nat.card Q :=
    le_antisymm (Subgroup.card_le_card_group _) (by omega)
  exact MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_card_eq _ h3)

end Generic

variable {G : Type} [Group G] [Finite G]

theorem eq_sup_pCoreOf_two_of_card {X Y : Subgroup G} (hXY : X ≤ Y)
    (hcard : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X)) :
    Y = X ⊔ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hXY) with hf
  have hK : IsPGroup 2 f.ker := by
    intro x
    have hx : Subgroup.inclusion hXY (x : ↥X) ∈ CFSG.pCore 2 ↥Y := by
      have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (Subgroup.inclusion hXY (x : ↥X)) = 1 :=
        x.2
      exact (QuotientGroup.eq_one_iff _).mp h1
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (⟨_, hx⟩ : CFSG.pCore 2 ↥Y)
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : CFSG.pCore 2 ↥Y => ((z : ↥Y) : G)) hk
    simpa using this
  have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hK
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hsurj := surjective_of_coprime_ker f hcop hcard
  refine le_antisymm (fun y hy => ?_) (sup_le hXY (CFSG.LieType.BorelTits.pCoreOf_le 2 Y))
  obtain ⟨x, hx⟩ := hsurj (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨y, hy⟩)
  rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at hx
  have hmem : ((Subgroup.inclusion hXY x)⁻¹ * ⟨y, hy⟩ : ↥Y) ∈ CFSG.Open.pCore 2 ↥Y := by
    exact hx
  have hy' : y = (x : G) * (((Subgroup.inclusion hXY x)⁻¹ * ⟨y, hy⟩ : ↥Y) : G) := by simp
  rw [hy']
  exact mul_mem (Subgroup.mem_sup_left x.2) (Subgroup.mem_sup_right ⟨_, hmem, rfl⟩)

theorem eq_sup_theta_of_card {X L : Subgroup G} (hXL : X ≤ L)
    (hcard : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≤
      Nat.card (↥X ⧸ CFSG.pPrimeCore 3 ↥X)) :
    L = X ⊔ (aschbacherSolvableCore 3 ↥L).map L.subtype := by
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set f := (QuotientGroup.mk' θ).comp (Subgroup.inclusion hXL) with hf
  have hmap : f.ker.map (Subgroup.inclusion hXL) ≤ θ := by
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mp hx
  have hdvd : Nat.card f.ker ∣ Nat.card θ := by
    rw [← Subgroup.card_map_of_injective (Subgroup.inclusion_injective hXL)]
    exact Subgroup.card_dvd_of_le hmap
  have hcop : Nat.Coprime 3 (Nat.card f.ker) :=
    Nat.Coprime.coprime_dvd_right hdvd ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      CFSG.RankThree.three_not_dvd_card_aschbacherSolvableCore)
  have hsurj := surjective_of_coprime_ker f hcop hcard
  refine le_antisymm (fun l hl => ?_) (sup_le hXL (Subgroup.map_subtype_le _))
  obtain ⟨x, hx⟩ := hsurj (QuotientGroup.mk' θ ⟨l, hl⟩)
  rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at hx
  have hl' : l = (x : G) * (((Subgroup.inclusion hXL x)⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
  rw [hl']
  exact mul_mem (Subgroup.mem_sup_left x.2) (Subgroup.mem_sup_right ⟨_, hx, rfl⟩)

theorem not_dvd_card_quotient_subgroupOf {M L O' : Subgroup G} (hMLO : M ≤ L ⊔ O')
    (hO' : ¬ 3 ∣ Nat.card O') (hLO' : L ≤ Subgroup.normalizer (O' : Set G))
    (hO'L : O' ≤ Subgroup.normalizer (L : Set G)) :
    ¬ 3 ∣ Nat.card (↥M ⧸ L.subgroupOf M) := by
  set J := L ⊔ O' with hJ
  have hJL : J ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hO'L
  have hN : (L.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hJL
  set χ := (QuotientGroup.mk' (L.subgroupOf J)).comp (Subgroup.inclusion hMLO) with hχ
  have hker : χ.ker = L.subgroupOf M := by
    ext m
    rw [MonoidHom.mem_ker, hχ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      Subgroup.coe_inclusion]
  have hcard : Nat.card (↥M ⧸ L.subgroupOf M) = Nat.card χ.range := by
    rw [← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange χ).toEquiv
  have hdvd : Nat.card χ.range ∣ L.relIndex J := Subgroup.card_subgroup_dvd_card _
  intro h3
  exact not_dvd_relIndex_sup_of_le_normalizer hO' hLO' (h3.trans (hcard ▸ hdvd))

theorem eq_inf_sup_of_le_sup {Y M L O O' : Subgroup G} (hYres : Y = oPrimeResidualOf 3 Y)
    (hOY : O ≤ Y) (hYO : Y ≤ Subgroup.normalizer (O : Set G)) (hY : Y ≤ O ⊔ M) (hMY : M ≤ Y)
    (hML : M ≤ Subgroup.normalizer (L : Set G)) (hMLO : M ≤ L ⊔ O')
    (hO' : ¬ 3 ∣ Nat.card O') (hLO' : L ≤ Subgroup.normalizer (O' : Set G))
    (hO'L : O' ≤ Subgroup.normalizer (L : Set G)) :
    Y = (Y ⊓ L) ⊔ O := by
  set N := (M ⊓ L) ⊔ O with hNdef
  have hNY : N ≤ Y := sup_le (inf_le_left.trans hMY) hOY
  have hMN : M ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_sup (Late.le_normalizer_inf Subgroup.le_normalizer hML) (hMY.trans hYO)
  have hON : O ≤ Subgroup.normalizer (N : Set G) := (le_sup_right : O ≤ N).trans
    Subgroup.le_normalizer
  have hYN : Y ≤ Subgroup.normalizer (N : Set G) := hY.trans (sup_le hON hMN)
  have hNn : (N.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr hYN
  set ψ := (QuotientGroup.mk' (N.subgroupOf Y)).comp (Subgroup.inclusion hMY) with hψ
  have hMO : M ≤ Subgroup.normalizer (O : Set G) := hMY.trans hYO
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf Y) q
    have hy : (y : G) ∈ ((O ⊔ M : Subgroup G) : Set G) := hY y.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left O M hMO] at hy
    obtain ⟨o, ho, m, hm, hom⟩ := hy
    refine ⟨⟨m, hm⟩, ?_⟩
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : ((Subgroup.inclusion hMY ⟨m, hm⟩)⁻¹ * y : ↥Y) = m⁻¹ * o * m := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hom]
      group
    rw [this]
    exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff''.mp (hMO hm) o).mp ho)
  have hker : L.subgroupOf M ≤ ψ.ker := by
    intro m hm
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    exact Subgroup.mem_sup_left ⟨m.2, Subgroup.mem_subgroupOf.mp hm⟩
  have hcard : Nat.card (↥Y ⧸ N.subgroupOf Y) ∣ Nat.card (↥M ⧸ L.subgroupOf M) := by
    have h1 : Nat.card (↥Y ⧸ N.subgroupOf Y) = Nat.card (↥M ⧸ ψ.ker) :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj).toEquiv).symm
    rw [h1]
    exact Subgroup.index_dvd_of_le hker
  have h3 := not_dvd_card_quotient_subgroupOf hMLO hO' hLO' hO'L
  have htop : N.subgroupOf Y = ⊤ := by
    by_contra hne
    exact h3 ((three_dvd_card_quotient_of_eq_oPrimeResidualOf hYres _ hne).trans hcard)
  refine le_antisymm (fun y hy => ?_) (sup_le inf_le_left hOY)
  have hyN : (⟨y, hy⟩ : ↥Y) ∈ N.subgroupOf Y := htop ▸ Subgroup.mem_top _
  exact (sup_le_sup_right (inf_le_inf_right L hMY) O) (Subgroup.mem_subgroupOf.mp hyN)

@[expose] def MultFree (S : Type) [Mul S] : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (Z : Subgroup X) [Z.Normal], Group.IsPerfect X →
    Z ≤ Subgroup.center X → Nat.Coprime 6 (Nat.card Z) → Nonempty (X ⧸ Z ≃* S) → Z = ⊥

theorem normal_eq_pCore_two_of {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.IsQuasisimple (Y ⧸ CFSG.pCore 2 Y)) {N : Subgroup Y} [N.Normal]
    (hN3 : Nat.Coprime 3 (Nat.card N)) (hO2 : CFSG.pCore 2 Y ≤ N) (hne : N ≠ ⊤)
    (hZ : ∀ (Z : Subgroup (Y ⧸ CFSG.pCore 2 Y)) [Z.Normal], Z ≤ Subgroup.center _ →
      Nat.Coprime 6 (Nat.card Z) → Nonempty ((Y ⧸ CFSG.pCore 2 Y) ⧸ Z ≃* Y ⧸ N) → Z = ⊥) :
    N = CFSG.pCore 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine le_antisymm ?_ hO2
  set Q := CFSG.pCore 2 Y with hQ
  set f := QuotientGroup.mk' Q with hf
  set Z := N.map f with hZdef
  have hZn : Z.Normal := (inferInstance : N.Normal).map f (QuotientGroup.mk'_surjective _)
  have hZc : Z ≤ Subgroup.center (Y ⧸ Q) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hZn with ht | hc
    · exfalso
      apply hne
      have hcomap := Subgroup.comap_map_eq f N
      rw [← hZdef, ht, Subgroup.comap_top, hf, QuotientGroup.ker_mk',
        sup_eq_left.mpr hO2] at hcomap
      exact hcomap.symm
    · exact hc
  have h3 : ¬ 3 ∣ Nat.card Z := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3 (h.trans (Subgroup.card_map_dvd _ f))
  have h2 : ¬ 2 ∣ Nat.card Z := by
    intro h
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 h
    have hzc : (z : Y ⧸ Q) ∈ Subgroup.center (Y ⧸ Q) := hZc z.2
    have hzn : (Subgroup.zpowers (z : Y ⧸ Q)).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzc)
    have hz2 : IsPGroup 2 (Subgroup.zpowers (z : Y ⧸ Q)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one])
    have hle : Subgroup.zpowers (z : Y ⧸ Q) ≤ CFSG.pCore 2 (Y ⧸ Q) := le_sSup ⟨hzn, hz2⟩
    rw [Sec18.pCore_quotient_pCore_eq_bot, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
    rw [show z = 1 from Subtype.ext hle, orderOf_one] at hz
    omega
  have hcop : Nat.Coprime 6 (Nat.card Z) := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num]
    exact Nat.coprime_mul_iff_left.mpr ⟨(Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2,
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3⟩
  have hZ1 := hZ Z hZc hcop ⟨QuotientGroup.quotientQuotientEquivQuotient Q _ hO2⟩
  rw [hZdef, Subgroup.map_eq_bot_iff, hf, QuotientGroup.ker_mk'] at hZ1
  exact hZ1

theorem pPrimeCore_three_eq_pCore_two_of {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.IsQuasisimple (Y ⧸ CFSG.pCore 2 Y)) (hne : CFSG.pPrimeCore 3 Y ≠ ⊤)
    (hZ : ∀ (Z : Subgroup (Y ⧸ CFSG.pCore 2 Y)) [Z.Normal], Z ≤ Subgroup.center _ →
      Nat.Coprime 6 (Nat.card Z) →
        Nonempty ((Y ⧸ CFSG.pCore 2 Y) ⧸ Z ≃* Y ⧸ CFSG.pPrimeCore 3 Y) → Z = ⊥) :
    CFSG.pPrimeCore 3 Y = CFSG.pCore 2 Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact normal_eq_pCore_two_of hq (CFSG.pPrimeCore_coprime_card (p := 3) (G := Y))
    pCore_two_le_pPrimeCore_three hne hZ

theorem theta_eq_pCore_two_of_multFree {L S : Type} [Group L] [Finite L] [Mul S]
    [Nontrivial S] (hq : CFSG.IsQuasisimple (L ⧸ CFSG.pCore 2 L))
    (hS : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* S)) (hmult : MultFree S) :
    aschbacherSolvableCore 3 L = CFSG.pCore 2 L := by
  obtain ⟨e⟩ := hS
  obtain ⟨-, hθc, hθ3, -, -, -, hcore⟩ :=
    solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have : (aschbacherSolvableCore 3 L).Characteristic := hθc
  have : (aschbacherSolvableCore 3 L).Normal := Subgroup.normal_of_characteristic _
  refine normal_eq_pCore_two_of hq ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3)
    (hcore 2 Nat.prime_two (by norm_num)) (fun htop => ?_) fun Z _ hZc hcop ⟨φ⟩ =>
    hmult _ Z hq.1 hZc hcop ⟨φ.trans e⟩
  have : Subsingleton (L ⧸ aschbacherSolvableCore 3 L) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton S e.surjective.subsingleton

theorem pPrimeCore_three_eq_pCore_two_of_multFree {Y S : Type} [Group Y] [Finite Y] [Mul S]
    [Nontrivial S] (hq : CFSG.IsQuasisimple (Y ⧸ CFSG.pCore 2 Y))
    (hS : Nonempty (Y ⧸ CFSG.pPrimeCore 3 Y ≃* S)) (hmult : MultFree S) :
    CFSG.pPrimeCore 3 Y = CFSG.pCore 2 Y := by
  obtain ⟨e⟩ := hS
  refine pPrimeCore_three_eq_pCore_two_of hq (fun htop => ?_) fun Z _ hZc hcop ⟨φ⟩ =>
    hmult _ Z hq.1 hZc hcop ⟨φ.trans e⟩
  have : Subsingleton (Y ⧸ CFSG.pPrimeCore 3 Y) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton S e.surjective.subsingleton

theorem pPrimeCore_three_eq_pCore_two_of_not_sq_dvd {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.IsQuasisimple (Y ⧸ CFSG.pCore 2 Y)) (hne : CFSG.pPrimeCore 3 Y ≠ ⊤)
    (hsq : ∀ p : ℕ, p.Prime → Nat.Coprime 6 p →
      ¬ p ^ 2 ∣ Nat.card (Y ⧸ CFSG.pPrimeCore 3 Y)) :
    CFSG.pPrimeCore 3 Y = CFSG.pCore 2 Y := by
  refine pPrimeCore_three_eq_pCore_two_of hq hne fun Z _ hZc hcop ⟨φ⟩ => ?_
  have : Group.IsPerfect (Y ⧸ CFSG.pCore 2 Y) := hq.1
  refine KFacts.KS14.eq_bot_of_isPerfect_of_not_sq_dvd hZc fun p hp hpZ => ?_
  rw [Nat.card_congr φ.toEquiv]
  exact hsq p hp (Nat.Coprime.coprime_dvd_right hpZ hcop).symm.symm

end CFSG.RankThree.PartTwo.Sec15.Proof1515
