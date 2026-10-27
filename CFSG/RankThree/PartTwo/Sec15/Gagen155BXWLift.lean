module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155INorm
public import CFSG.RankThree.PartTwo.Sec15.Gagen155BXWCover
import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofE81
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Proof155BXW

variable {G : Type} [Group G] [Finite G]

theorem inf_pPrimeCoreOf_le (p : ℕ) [Fact p.Prime] {X M : Subgroup G} (hXM : X ≤ M) :
    X ⊓ pPrimeCoreOf p M ≤ pPrimeCoreOf p X := by
  have hN : X ⊓ pPrimeCoreOf p M ≤ X := inf_le_left
  have hnorm : X ≤ Subgroup.normalizer (↑(X ⊓ pPrimeCoreOf p M) : Set G) :=
    Subgroup.le_normalizer_inf Subgroup.le_normalizer
      (hXM.trans (le_normalizer_pPrimeCoreOf p M))
  have hcop : Nat.Coprime p (Nat.card ↥(X ⊓ pPrimeCoreOf p M)) :=
    (coprime_card_pPrimeCoreOf p M).coprime_dvd_right
      (Subgroup.card_dvd_of_le inf_le_right)
  exact le_pPrimeCoreOf hN hnorm hcop

theorem mem_centralizerSection_of_commutator_mem {A : Subgroup G}
    {LB : Subgroup G → Subgroup G} {X : Subgroup G} (hX : X ∈ scriptY4 A LB) {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hc : ∀ x ∈ X, ⁅x, g⁆ ∈ pPrimeCoreOf 3 X) :
    g ∈ centralizerSection X (CFSG.Open.pCoreOf 2 X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := ↥X ⧸ CFSG.pCore 2 ↥X with hQ
  set q : ↥X →* Q := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hq
  set P : Subgroup ↥X := CFSG.pPrimeCore 3 ↥X with hP
  set N : Subgroup Q := P.map q with hNdef
  have hPnormal : P.Normal := CFSG.pPrimeCore_normal
  have hNnormal : N.Normal := hPnormal.map q (QuotientGroup.mk'_surjective _)
  have hXq : CFSG.IsQuasisimple Q := hX.2.2.2
  have hQperf : Group.IsPerfect Q := hXq.1
  obtain ⟨x, hxX, hx3, y, hyX, hxy⟩ := Proof153Twin.hasNonCentralThree_of_mem_scriptY4 hX
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hxy
    simp
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxO2 : x ∉ CFSG.Open.pCoreOf 2 X := by
    intro hxO2
    have h2P : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 X) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp h2P) ⟨x, hxO2⟩
    rw [Subgroup.orderOf_mk, hxord] at hn
    have hdiv : 3 ∣ 2 ^ n := hn ▸ dvd_rfl
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdiv) (by norm_num)
  let xX : ↥X := ⟨x, hxX⟩
  have hqx1 : q xX ≠ 1 := by
    intro h1
    apply hxO2
    have h2 : xX ∈ CFSG.pCore 2 ↥X := (QuotientGroup.eq_one_iff xX).mp h1
    rw [CFSG.Open.pCoreOf]
    exact Subgroup.mem_map_of_mem X.subtype h2
  have hNle : N ≤ Subgroup.center Q := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hXq hNnormal with htop | hle
    · exfalso
      have hqxN : q xX ∈ N := by rw [htop]; exact Subgroup.mem_top _
      have hqx3 : (q xX) ^ 3 = 1 := by
        rw [← map_pow]
        exact (congrArg q (Subtype.ext hx3)).trans (map_one q)
      have hord3 : orderOf (q xX) ∣ 3 := orderOf_dvd_of_pow_eq_one hqx3
      have hordN : orderOf (q xX) ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hqxN
      have hcop3P : Nat.Coprime 3 (Nat.card P) := CFSG.pPrimeCore_coprime_card
      have hcop3N : Nat.Coprime 3 (Nat.card N) :=
        hcop3P.coprime_dvd_right (Subgroup.card_map_dvd P q)
      have hcop : Nat.Coprime (orderOf (q xX)) (Nat.card N) :=
        Nat.Coprime.coprime_dvd_left hord3 hcop3N
      have hone : orderOf (q xX) = 1 := hcop.eq_one_of_dvd hordN
      exact hqx1 (orderOf_eq_one_iff.mp hone)
    · exact hle
  set m : ↥(Subgroup.normalizer (X : Set G)) := ⟨g, hg⟩ with hm
  set σ : MulAut Q := CFSG.RankThree.PartTwo.Sec17.Proof17Res6.actQ X m with hσ
  have hcentral : ∀ element : Q, element⁻¹ * σ element ∈ Subgroup.center Q := by
    intro element
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) element
    have hyX : (y : G) ∈ X := y.2
    have hqeq : (q y)⁻¹ * σ (q y) = q (y⁻¹ * ((X.normalizerMonoidHom m) y)) := by
      rw [CFSG.RankThree.PartTwo.Sec17.Proof17Res6.actQ_mk, ← map_inv, ← map_mul]
    rw [hqeq]
    apply hNle
    refine Subgroup.mem_map.mpr ⟨y⁻¹ * ((X.normalizerMonoidHom m) y), ?_, rfl⟩
    have hcoe : ((y⁻¹ * ((X.normalizerMonoidHom m) y) : ↥X) : G) = ⁅((y⁻¹ : ↥X) : G), g⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.normalizerMonoidHom_apply_apply_coe, commutatorElement_def, hm]
      group
    have hmemG : ((y⁻¹ * ((X.normalizerMonoidHom m) y) : ↥X) : G) ∈ pPrimeCoreOf 3 X := by
      rw [hcoe]
      exact hc ((y⁻¹ : ↥X) : G) (inv_mem hyX)
    exact (Subgroup.mem_map_iff_mem X.subtype_injective).mp (by
      simpa [CFSG.GH74.GLS.pPrimeCoreOf] using hmemG)
  have hid : σ.toMonoidHom = MonoidHom.id Q :=
    CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
      σ.toMonoidHom hcentral
  have hσ1 : σ = 1 := by
    ext z
    have := congrArg (fun f : Q →* Q => f z) hid
    simpa using this
  have hm1 : CFSG.RankThree.PartTwo.Sec17.Proof17Res6.actQ X m = 1 := hσ1
  refine ⟨hg, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X hg, ?_⟩
  intro k hk
  have hz : g * k⁻¹ * g⁻¹ * k ∈ CFSG.Open.pCoreOf 2 X := by
    simpa [hm] using Proof155w3.commutator_mem_of_actQ_eq_one hm1 k⁻¹ (inv_mem hk)
  have hnorm : k * (g * k⁻¹ * g⁻¹ * k) * k⁻¹ ∈ CFSG.Open.pCoreOf 2 X := by
    have hk' : k ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hk
    exact (Subgroup.mem_normalizer_iff.mp hk' _).mp hz
  have heq : ⁅k, g⁆ = k * (g * k⁻¹ * g⁻¹ * k) * k⁻¹ := by
    simp only [commutatorElement_def]
    group
  rwa [heq]

theorem mem_img148_b155_of_commute
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h148 : Item148 A (lB A)) (h149 : Item149 A (lB A)) {X M : Subgroup G}
    [(ker148 A M).Normal]
    (hM : M ∈ CFSG.maximalTwoLocalsContaining ((X ⊔ A : Subgroup G) : Set G))
    (hX : X ∈ scriptY4 A (lB A)) (hXM : X ∈ thetaComponentsIn M)
    {e : ↥(M ⊔ A) ⧸ ker148 A M} (he : e ∈ img148 A M (deltaZero A (lB A) M)) {k : ℕ}
    (hek : e ^ 3 ^ k = 1) (hcomm : ∀ y ∈ img148 A M X, y * e = e * y) :
    e ∈ img148 A M (b155 A M X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hXM', -, -, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
  obtain ⟨g, hgMA, hgDZ, hge⟩ := mem_img148_iff.mp he
  set q := QuotientGroup.mk' (ker148 A M) with hq
  have hk' : q (⟨g, hgMA⟩ : ↥(M ⊔ A)) ^ 3 ^ k = 1 := by
    rw [hq, hge]
    exact hek
  obtain ⟨n, ⟨a, hpowH⟩, hmap⟩ :=
    exists_pow_pElement_map_eq Nat.prime_three q ⟨g, hgMA⟩ hk'
  have hg3DZ : g ^ n ∈ deltaZero A (lB A) M := pow_mem hgDZ n
  have hg3Delta : g ^ n ∈ delta A (lB A) M := deltaZero_le_delta M hg3DZ
  have hg3M : g ^ n ∈ M := delta_le M hg3Delta
  have hg3MA : g ^ n ∈ M ⊔ A := Subgroup.mem_sup_left hg3M
  have hxHpow : (⟨g, hgMA⟩ : ↥(M ⊔ A)) ^ n = ⟨g ^ n, hg3MA⟩ := by
    apply Subtype.ext
    simp [Subgroup.coe_pow]
  have hpowG : (g ^ n) ^ 3 ^ a = 1 := by
    have h := congrArg Subtype.val hpowH
    simp only [hxHpow, Subgroup.coe_pow, Subgroup.coe_one] at h
    exact h
  have hg3O : g ^ n ∈ oPrimeResidualOf 3 (delta A (lB A) M) := by
    rw [oPrimeResidualOf_eq_closure]
    exact Subgroup.subset_closure ⟨hg3Delta, a, hpowG⟩
  have hg3N : g ^ n ∈ Subgroup.normalizer (X : Set G) :=
    Proof155INorm.oPrimeResidualOf_le_normalizer_of_item148 h h148 h149 hM hX hXM
      (delta_le M) hg3O
  have hqg3 : q ⟨g ^ n, hg3MA⟩ = e := by
    rw [← hxHpow, hmap, hge]
  have hcommX : ∀ x ∈ X, ⁅x, g ^ n⁆ ∈ pPrimeCoreOf 3 X := by
    intro x hx
    have hxMA : x ∈ M ⊔ A := Subgroup.mem_sup_left (hXM' hx)
    have hxinvN : g ^ n * x⁻¹ * (g ^ n)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hg3N x⁻¹).mp (inv_mem hx)
    have hmemX : ⁅x, g ^ n⁆ ∈ X := by
      rw [commutatorElement_def]
      simpa [mul_assoc] using X.mul_mem hx hxinvN
    have hmemMA : ⁅x, g ^ n⁆ ∈ M ⊔ A := Subgroup.mem_sup_left (hXM' hmemX)
    have hqx : q ⟨x, hxMA⟩ ∈ img148 A M X := mem_img148_iff.mpr ⟨x, hxMA, hx, rfl⟩
    have hqcomm : q ⟨x, hxMA⟩ * q ⟨g ^ n, hg3MA⟩ =
        q ⟨g ^ n, hg3MA⟩ * q ⟨x, hxMA⟩ := by
      rw [hqg3]
      exact hcomm _ hqx
    have hz : q ⟨⁅x, g ^ n⁆, hmemMA⟩ = 1 := by
      have heq : (⟨⁅x, g ^ n⁆, hmemMA⟩ : ↥(M ⊔ A)) =
          ⁅(⟨x, hxMA⟩ : ↥(M ⊔ A)), (⟨g ^ n, hg3MA⟩ : ↥(M ⊔ A))⁆ := by
        apply Subtype.ext
        simp [commutatorElement_def]
      rw [heq, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.mpr hqcomm]
    have hmemM : ⁅x, g ^ n⁆ ∈ pPrimeCoreOf 3 M := mk'_ker148_eq_one_iff.mp hz
    exact inf_pPrimeCoreOf_le 3 hXM' ⟨hmemX, hmemM⟩
  have hcent : g ^ n ∈ centralizerSection X (CFSG.Open.pCoreOf 2 X) :=
    mem_centralizerSection_of_commutator_mem hX hg3N hcommX
  have hu : g ^ n ∈ u155 A M X := ⟨hg3Delta, hcent⟩
  have hb : g ^ n ∈ b155 A M X := by
    rw [b155, oPrimeResidualOf_eq_closure]
    exact Subgroup.subset_closure ⟨hu, a, hpowG⟩
  exact mem_img148_iff.mpr ⟨g ^ n, hg3MA, hb, hqg3⟩

theorem inSubgroup_perfectResidual_subgroupOf {B H : Subgroup G} (hBH : B ≤ H) :
    (inSubgroup perfectResidual B).subgroupOf H = inSubgroup perfectResidual (B.subgroupOf H) := by
  unfold inSubgroup
  apply Subgroup.map_injective (Subgroup.subtype_injective H)
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_map]
  rw [inf_eq_left.mpr ((Subgroup.map_subtype_le (perfectResidual B)).trans hBH)]
  rw [← Subgroup.map_map,
    CFSG.SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map H.subtype (B.subgroupOf H),
    Subgroup.map_subgroupOf_eq_of_le hBH]

theorem le_img148_inSubgroup_perfectResidual {A M : Subgroup G} [(ker148 A M).Normal]
    {B : Subgroup G} (hBM : B ≤ M ⊔ A) {E : Subgroup (↥(M ⊔ A) ⧸ ker148 A M)}
    (hEp : Group.IsPerfect ↥E) (hEB : E ≤ img148 A M B) :
    E ≤ img148 A M (inSubgroup perfectResidual B) := by
  set Y := B.subgroupOf (M ⊔ A) with hYdef
  have himg : img148 A M B = Y.map (QuotientGroup.mk' (ker148 A M)) := rfl
  have hperf : img148 A M (inSubgroup perfectResidual B) =
      (perfectResidual (img148 A M B)).map (img148 A M B).subtype := by
    unfold img148
    rw [inSubgroup_perfectResidual_subgroupOf hBM]
    unfold CFSG.inSubgroup
    rw [CFSG.SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map
        (QuotientGroup.mk' (ker148 A M)) Y]
  rw [hperf]
  exact CFSG.SignalizerFunctorTheorem.Nonsolvable.le_perfectResidual_map_of_isPerfect hEp hEB

theorem oPrimeResidualOf_le_of_img148_le {A M : Subgroup G} [(ker148 A M).Normal]
    {K H I : Subgroup G} (hKI : oPrimeResidualOf 3 K ≤ I) (hHI : H ≤ I) (hIM : I ≤ M)
    (hIH : I ≤ Subgroup.normalizer (H : Set G))
    (hle : img148 A M (oPrimeResidualOf 3 K) ≤ img148 A M H) : oPrimeResidualOf 3 K ≤ H := by
  rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
  intro b hb
  simp only [Set.mem_setOf_eq] at hb
  obtain ⟨hbK, k, hbk⟩ := hb
  have hbO : b ∈ oPrimeResidualOf 3 K := by
    rw [oPrimeResidualOf_eq_closure]
    exact Subgroup.subset_closure ⟨hbK, k, hbk⟩
  have hbI : b ∈ I := hKI hbO
  have hbM : b ∈ M := hIM hbI
  have hbMA : b ∈ M ⊔ A := Subgroup.mem_sup_left hbM
  set q := QuotientGroup.mk' (ker148 A M) with hq
  have he : q ⟨b, hbMA⟩ ∈ img148 A M (oPrimeResidualOf 3 K) :=
    mem_img148_iff.mpr ⟨b, hbMA, hbO, rfl⟩
  have heH : q ⟨b, hbMA⟩ ∈ img148 A M H := hle he
  obtain ⟨y, hyMA, hyH, hqy⟩ := mem_img148_iff.mp heH
  have hk0 : y⁻¹ * b ∈ pPrimeCoreOf 3 M := by
    have h := mk'_ker148_eq_iff.mp (hqy.trans rfl)
    simpa using h
  have hk0I : y⁻¹ * b ∈ I := mul_mem (inv_mem (hHI hyH)) hbI
  set C := I ⊓ pPrimeCoreOf 3 M with hC
  have hk0C : y⁻¹ * b ∈ C := ⟨hk0I, hk0⟩
  have hCH : C ≤ Subgroup.normalizer (H : Set G) := inf_le_left.trans hIH
  have hbjoin : b ∈ H ⊔ C := by
    have hb_eq : b = y * (y⁻¹ * b) := by group
    rw [hb_eq]
    exact Subgroup.mul_mem (H ⊔ C) (Subgroup.mem_sup_left hyH) (Subgroup.mem_sup_right hk0C)
  have h3c : Nat.Coprime 3 (Nat.card C) :=
    (coprime_card_pPrimeCoreOf 3 M).coprime_dvd_right
      (Subgroup.card_dvd_of_le inf_le_right)
  have hcop : Nat.Coprime (orderOf b) (Nat.card C) :=
    (h3c.pow_left k).coprime_dvd_left (orderOf_dvd_of_pow_eq_one hbk)
  exact mem_left_of_coprime_orderOf hCH hbjoin hcop

end Proof155BXW

end CFSG.RankThree.PartTwo.Sec15
