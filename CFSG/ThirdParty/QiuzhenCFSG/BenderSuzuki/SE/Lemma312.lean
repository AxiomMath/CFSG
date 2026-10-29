module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingFusion
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.BaerCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities

namespace CFSG
end CFSG
open CFSG

/-!
# Lemma 3.12: the solvable strongly embedded case

This file records the literal fixed-coset hypothesis of Lemma 3.12 from
`docs/cfsg-vol4.tex` and connects it to the source Theorem 4(b) contract.
The latter connection is fully checked: odd-order elements use Theorem 4(b),
while an even-order element has an involution in its cyclic subgroup, whose
fixed coset is unique by strong embedding.
-/

noncomputable section

open scoped Pointwise IsMulCommutative

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u v

/-- The literal fixed-point hypothesis of Lemma 3.12: every nonidentity
element of `Y` inverted by `z` fixes a unique right coset of `Y`. -/
@[expose] public def Lemma312FixedPointCondition
    {H : Type u} [Group H] (Y : Subgroup H) (z : H) : Prop :=
  ∀ y : H, y ∈ Y → y ≠ 1 → z * y * z⁻¹ = y⁻¹ →
    ∃! omega : conjugateCosetSpace Y, y • omega = omega

private theorem mem_normalizer_zpowers_of_inverts
    {G : Type*} [Group G] {z y : G}
    (hz : IsInvolution z) (hinv : z * y * z⁻¹ = y⁻¹) :
    z ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  have hsemi : SemiconjBy z y y⁻¹ := by
    rw [SemiconjBy]
    calc
      z * y = (z * y * z⁻¹) * z := by simp [mul_assoc]
      _ = y⁻¹ * z := by rw [hinv]
  have hforward : ∀ x : G, x ∈ Subgroup.zpowers y →
      z * x * z⁻¹ ∈ Subgroup.zpowers y := by
    intro x hx
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨-n, ?_⟩
    have hpow := hsemi.zpow_right n
    rw [SemiconjBy] at hpow
    calc
      y ^ (-n) = (y⁻¹) ^ n := by simp
      _ = z * y ^ n * z⁻¹ := by
        symm
        calc
          z * y ^ n * z⁻¹ = (y⁻¹ ^ n * z) * z⁻¹ := by rw [hpow]
          _ = y⁻¹ ^ n := by simp
  intro x
  constructor
  · exact hforward x
  · intro hx
    have h2 := hforward (z * x * z⁻¹) hx
    have hzz : z * z = 1 := by
      simpa [pow_two] using hz.sq_eq_one
    have heq : z * (z * x * z⁻¹) * z⁻¹ = x := by
      rw [hz.inv_eq_self]
      calc
        z * (z * x * z) * z = (z * z) * x * (z * z) := by group
        _ = x := by rw [hzz]; simp
    rw [heq] at h2
    exact h2

private theorem not_zpowers_le_centralizer_of_odd_order_of_inverts
    {G : Type*} [Group G] [Finite G]
    {z y : G} (hyne : y ≠ 1) (hinv : z * y * z⁻¹ = y⁻¹)
    (hodd : Odd (orderOf y)) :
    ¬ Subgroup.zpowers y ≤ Subgroup.centralizer ({z} : Set G) := by
  intro hcentral
  have hycentral : y ∈ Subgroup.centralizer ({z} : Set G) :=
    hcentral (Subgroup.mem_zpowers y)
  have hcomm : z * y = y * z :=
    (Subgroup.mem_centralizer_singleton_iff.mp hycentral).symm
  have hyinv : y = y⁻¹ := by
    calc
      y = z * y * z⁻¹ := by rw [hcomm]; simp
      _ = y⁻¹ := hinv
  have hy2 : y ^ 2 = 1 := by
    calc
      y ^ 2 = y * y := by rw [pow_two]
      _ = y * y⁻¹ := congrArg (fun q : G => y * q) hyinv
      _ = 1 := by simp
  have hdvd : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hy2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with horder | horder
  · exact hyne (orderOf_eq_one_iff.mp horder)
  · exact hodd.not_two_dvd_nat (by simp [horder])

private theorem existsUnique_fixed_coset_of_odd_order_of_theorem4b
    {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    (h4b : Theorem4bAtBase M)
    {z y : G} (hzM : z ∈ M) (hz : IsInvolution z)
    (hyM : y ∈ M) (hyne : y ≠ 1)
    (hinv : z * y * z⁻¹ = y⁻¹) (hodd : Odd (orderOf y)) :
    ∃! omega : conjugateCosetSpace M, y • omega = omega := by
  let W : Subgroup G := Subgroup.zpowers y
  have hWodd : Odd (Nat.card W) := by
    simpa [W, Nat.card_zpowers] using hodd
  have hWM : W ≤ M := by
    dsimp [W]
    exact Subgroup.zpowers_le.mpr hyM
  have hzNorm : z ∈ Subgroup.normalizer (W : Set G) := by
    simpa [W] using mem_normalizer_zpowers_of_inverts hz hinv
  have hnot : ¬ W ≤ Subgroup.centralizer ({z} : Set G) := by
    simpa [W] using
      not_zpowers_le_centralizer_of_odd_order_of_inverts hyne hinv hodd
  obtain ⟨omega, homega, hunique⟩ :=
    h4b.existsUnique_fixedPoint_of_not_centralizes
      hz hzM hWodd hWM hzNorm hnot
  refine ⟨omega, ?_, ?_⟩
  · exact MulAction.mem_stabilizer_iff.mp
      (homega y (Subgroup.mem_zpowers y))
  · intro eta heta
    apply hunique eta
    intro w hw
    have hyStab : y ∈ MulAction.stabilizer G eta :=
      MulAction.mem_stabilizer_iff.mpr heta
    have hWStab : W ≤ MulAction.stabilizer G eta := by
      dsimp [W]
      exact Subgroup.zpowers_le.mpr hyStab
    exact MulAction.mem_stabilizer_iff.mp (hWStab hw)

private theorem existsUnique_fixed_coset_of_even_order
    {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    (hM : IsStronglyEmbedded M) {y : G} (hyM : y ∈ M)
    (heven : Even (orderOf y)) :
    ∃! omega : conjugateCosetSpace M, y • omega = omega := by
  classical
  let W : Subgroup G := Subgroup.zpowers y
  have htwo : 2 ∣ Nat.card W := by
    simpa [W, Nat.card_zpowers] using heven.two_dvd
  obtain ⟨w, hwOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := W) 2 htwo
  have hwOrderG : orderOf (w : G) = 2 := by
    rw [Subgroup.orderOf_coe, hwOrder]
  have hwdata :=
    (orderOf_eq_prime_iff (x := (w : G)) (p := 2)).mp hwOrderG
  have hw : IsInvolution (w : G) := ⟨hwdata.2, hwdata.1⟩
  obtain ⟨omega, homega, hunique⟩ :=
    hM.involution_fixed_coset_unique hw
  let alpha : conjugateCosetSpace M := QuotientGroup.mk 1
  have hyalpha : y • alpha = alpha := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [baseCoset_stabilizer M]
    exact hyM
  refine ⟨alpha, hyalpha, ?_⟩
  intro eta heta
  have hyStab : y ∈ MulAction.stabilizer G eta :=
    MulAction.mem_stabilizer_iff.mpr heta
  have hwStab : (w : G) ∈ MulAction.stabilizer G eta :=
    (Subgroup.zpowers_le.mpr hyStab) w.property
  have hweta : (w : G) • eta = eta :=
    MulAction.mem_stabilizer_iff.mp hwStab
  have hwalpha : (w : G) • alpha = alpha := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [baseCoset_stabilizer M]
    exact (Subgroup.zpowers_le.mpr hyM) w.property
  exact (hunique eta hweta).trans (hunique alpha hwalpha).symm

private theorem existsUnique_fixed_coset_of_theorem4b
    {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    (hM : IsStronglyEmbedded M) (h4b : Theorem4bAtBase M)
    {z y : G} (hzM : z ∈ M) (hz : IsInvolution z)
    (hyM : y ∈ M) (hyne : y ≠ 1)
    (hinv : z * y * z⁻¹ = y⁻¹) :
    ∃! omega : conjugateCosetSpace M, y • omega = omega := by
  rcases Nat.even_or_odd (orderOf y) with heven | hodd
  · exact existsUnique_fixed_coset_of_even_order hM hyM heven
  · exact existsUnique_fixed_coset_of_odd_order_of_theorem4b
      h4b hzM hz hyM hyne hinv hodd

private noncomputable def subgroupCosetMap
    {G : Type*} [Group G] (M H : Subgroup G) :
    conjugateCosetSpace (M.comap H.subtype) → conjugateCosetSpace M :=
  Quotient.lift (fun h : H => QuotientGroup.mk (h : G)) (by
    intro a b hab
    apply QuotientGroup.eq.mpr
    have habq :
        (QuotientGroup.mk a : conjugateCosetSpace (M.comap H.subtype)) =
          QuotientGroup.mk b := Quotient.sound hab
    have habY := QuotientGroup.eq.mp habq
    change ((a : G)⁻¹ * (b : G)) ∈ M at habY
    exact habY)

@[simp] private theorem subgroupCosetMap_mk
    {G : Type*} [Group G] (M H : Subgroup G) (h : H) :
    subgroupCosetMap M H
        (QuotientGroup.mk h : conjugateCosetSpace (M.comap H.subtype)) =
      (QuotientGroup.mk (h : G) : conjugateCosetSpace M) := by
  rfl

private theorem subgroupCosetMap_injective
    {G : Type*} [Group G] (M H : Subgroup G) :
    Function.Injective (subgroupCosetMap M H) := by
  intro omega eta h
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective omega
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective eta
  apply QuotientGroup.eq.mpr
  have hamb : (g : G)⁻¹ * (k : G) ∈ M := QuotientGroup.eq.mp h
  exact hamb

private theorem subgroupCosetMap_smul
    {G : Type*} [Group G] (M H : Subgroup G)
    (h : H) (omega : conjugateCosetSpace (M.comap H.subtype)) :
    subgroupCosetMap M H (h • omega) =
      (h : G) • subgroupCosetMap M H omega := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective omega
  rfl

private theorem existsUnique_fixed_coset_comap_of_ambient
    {G : Type*} [Group G] (M H : Subgroup G)
    (y : H) (hyM : y ∈ M.comap H.subtype)
    (hambient : ∃! omega : conjugateCosetSpace M,
      (y : G) • omega = omega) :
    ∃! omega : conjugateCosetSpace (M.comap H.subtype),
      y • omega = omega := by
  let alpha : conjugateCosetSpace (M.comap H.subtype) := QuotientGroup.mk 1
  have hyalpha : y • alpha = alpha := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [baseCoset_stabilizer]
    exact hyM
  refine ⟨alpha, hyalpha, ?_⟩
  intro eta heta
  apply subgroupCosetMap_injective M H
  obtain ⟨omegaG, homegaG, huniqueG⟩ := hambient
  apply (huniqueG (subgroupCosetMap M H eta) ?_).trans
    (huniqueG (subgroupCosetMap M H alpha) ?_).symm
  · rw [← subgroupCosetMap_smul M H y eta, heta]
  · rw [← subgroupCosetMap_smul M H y alpha, hyalpha]

/-- Theorem 4(b), together with strong embedding in the ambient group,
supplies the exact fixed-point hypothesis of Lemma 3.12 after restricting to
a subgroup. -/
public theorem lemma312_fixedPointCondition_of_theorem4b_comap
    {G : Type u} [Group G] [Finite G]
    (M H : Subgroup G) (hM : IsStronglyEmbedded M)
    (h4b : Theorem4bAtBase M)
    {z : H} (hzM : z ∈ M.comap H.subtype) (hz : IsInvolution z) :
    Lemma312FixedPointCondition (M.comap H.subtype) z := by
  intro y hyM hyne hinv
  have hzG : IsInvolution (z : G) :=
    IsInvolution.map_of_injective hz H.subtype Subtype.val_injective
  have hyGne : (y : G) ≠ 1 := by
    intro h
    exact hyne (Subtype.ext h)
  have hinvG : (z : G) * (y : G) * (z : G)⁻¹ = (y : G)⁻¹ := by
    simpa using congrArg H.subtype hinv
  apply existsUnique_fixed_coset_comap_of_ambient M H y hyM
  exact existsUnique_fixed_coset_of_theorem4b hM h4b
    hzM hzG hyM hyGne hinvG

/-- The literal Lemma 3.12 fixed-point condition restricts to every subgroup
containing the chosen involution. -/
private theorem lemma312_fixedPointCondition_comap
    {H : Type u} [Group H] [Finite H]
    (Y K : Subgroup H) {z : H} (hzK : z ∈ K)
    (hfixed : Lemma312FixedPointCondition Y z) :
    Lemma312FixedPointCondition (Y.comap K.subtype) (⟨z, hzK⟩ : K) := by
  intro y hyY hyne hinv
  have hyHne : (y : H) ≠ 1 := by
    intro h
    exact hyne (Subtype.ext h)
  have hinvH : z * (y : H) * z⁻¹ = (y : H)⁻¹ := by
    simpa using congrArg K.subtype hinv
  apply existsUnique_fixed_coset_comap_of_ambient Y K y hyY
  exact hfixed (y : H) hyY hyHne hinvH

/-- If a normal subgroup lies in `Y`, the literal fixed-point hypothesis
forces the chosen involution to centralize it. -/
private theorem lemma312_fixedPointCondition_centralizes_normal_le
    {H : Type u} [Group H]
    (Y : Subgroup H) (hYproper : Y ≠ ⊤)
    {z : H} (hz : IsInvolution z)
    (hfixed : Lemma312FixedPointCondition Y z)
    (N : Subgroup H) (hNnormal : N.Normal) (hNY : N ≤ Y) :
    z ∈ Subgroup.centralizer (N : Set H) := by
  rw [Subgroup.mem_centralizer_iff]
  intro n hnN
  let c : H := z * n * z⁻¹ * n⁻¹
  have hcN : c ∈ N := by
    dsimp [c]
    exact N.mul_mem (hNnormal.conj_mem n hnN z) (N.inv_mem hnN)
  have hcY : c ∈ Y := hNY hcN
  have hcinv : z * c * z⁻¹ = c⁻¹ := by
    have hzz : z * z = 1 := by
      simpa [pow_two] using hz.sq_eq_one
    dsimp [c]
    calc
      z * (z * n * z⁻¹ * n⁻¹) * z⁻¹ =
          (z * z) * n * z⁻¹ * n⁻¹ * z⁻¹ := by group
      _ = n * z⁻¹ * n⁻¹ * z⁻¹ := by rw [hzz]; simp
      _ = n * z * n⁻¹ * z⁻¹ := by rw [hz.inv_eq_self]
      _ = (z * n * z⁻¹ * n⁻¹)⁻¹ := by group
  have hc_one : c = 1 := by
    by_contra hcne
    obtain ⟨omega, homega, hunique⟩ := hfixed c hcY hcne hcinv
    let alpha : conjugateCosetSpace Y := QuotientGroup.mk 1
    have hcalpha : c • alpha = alpha := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [baseCoset_stabilizer]
      exact hcY
    have hYlt : Y < ⊤ := lt_top_iff_ne_top.mpr hYproper
    obtain ⟨g, _hgTop, hgY⟩ := SetLike.exists_of_lt hYlt
    let beta : conjugateCosetSpace Y := QuotientGroup.mk g
    have hcbeta : c • beta = beta := by
      rw [fixed_coset_iff_mem_rightConjugate]
      rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨g⁻¹ * c * g, ?_, ?_⟩
      · exact hNY (by simpa using hNnormal.conj_mem c hcN g⁻¹)
      · have hgc : g * (g⁻¹ * c * g) * g⁻¹ = c := by group
        simpa [MulAut.conj_apply] using hgc
    have hab : alpha = beta :=
      (hunique alpha hcalpha).trans (hunique beta hcbeta).symm
    have hgY' : g ∈ Y := by
      have := QuotientGroup.eq.mp hab
      simpa [alpha, beta] using this
    exact hgY hgY'
  have hconj : z * n * z⁻¹ = n := by
    have h := congrArg (fun q : H => q * n) hc_one
    simpa [c, mul_assoc] using h
  calc
    n * z = z * n := by
      calc
        n * z = (z * n * z⁻¹) * z := by rw [hconj]
        _ = z * n := by simp [mul_assoc]

/-- A normal subgroup contained in a strongly embedded subgroup has odd
cardinality. -/
private theorem lemma312_normal_le_stronglyEmbedded_card_odd
    {H : Type u} [Group H] [Finite H]
    {Y N : Subgroup H} (hY : IsStronglyEmbedded Y)
    (hNnormal : N.Normal) (hNY : N ≤ Y) :
    Odd (Nat.card N) := by
  apply Nat.not_even_iff_odd.mp
  intro hNeven
  obtain ⟨n, hnOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := N) 2
      (even_iff_two_dvd.mp hNeven)
  have hnOrderH : orderOf (n : H) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hnOrder
  have hnData := orderOf_eq_prime_iff.mp hnOrderH
  have hnInv : IsInvolution (n : H) := ⟨hnData.2, hnData.1⟩
  have hYlt : Y < ⊤ := lt_top_iff_ne_top.mpr hY.ne_top
  obtain ⟨g, _hgTop, hgY⟩ := SetLike.exists_of_lt hYlt
  have hconjN : g * (n : H) * g⁻¹ ∈ N :=
    hNnormal.conj_mem (n : H) n.property g
  have hnRight : (n : H) ∈ rightConjugate Y g := by
    have hmem := rightConjugateElem_mem_rightConjugate
      (g := g) (hNY hconjN)
    simpa [rightConjugateElem, mul_assoc] using hmem
  exact hY.2.2 hgY (hNY n.property) hnRight hnInv

/-- An ambient involution remains an involution after quotienting by a normal
odd-order subgroup. -/
private theorem lemma312_quotient_involution_of_odd_kernel
    {H : Type u} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (hNodd : Odd (Nat.card N))
    {z : H} (hz : IsInvolution z) :
    IsInvolution (QuotientGroup.mk' N z) := by
  constructor
  · intro hzq
    have hzN : z ∈ N :=
      (QuotientGroup.eq_one_iff (N := N) z).mp hzq
    let zN : N := ⟨z, hzN⟩
    have hzNI : IsInvolution zN := IsInvolution.subtype hz hzN
    have horder : orderOf zN = 2 :=
      orderOf_eq_prime hzNI.sq_eq_one hzNI.ne_one
    have hdvd : 2 ∣ Nat.card N := by
      rw [← horder]
      exact orderOf_dvd_natCard zN
    exact hNodd.not_two_dvd_nat hdvd
  · simpa using congrArg (QuotientGroup.mk' N) hz.sq_eq_one

private noncomputable def lemma312QuotientCosetMap
    {H : Type*} [Group H] (Y N : Subgroup H) [N.Normal] :
    conjugateCosetSpace Y →
      conjugateCosetSpace (Y.map (QuotientGroup.mk' N)) :=
  Quotient.lift
    (fun h : H => QuotientGroup.mk (QuotientGroup.mk' N h)) (by
      intro a b hab
      apply QuotientGroup.eq.mpr
      have habq :
          (QuotientGroup.mk a : conjugateCosetSpace Y) =
            QuotientGroup.mk b := Quotient.sound hab
      have habY := QuotientGroup.eq.mp habq
      exact Subgroup.mem_map_of_mem (QuotientGroup.mk' N) (by simpa using habY))

@[simp] private theorem lemma312QuotientCosetMap_mk
    {H : Type*} [Group H] (Y N : Subgroup H) [N.Normal] (h : H) :
    lemma312QuotientCosetMap Y N
        (QuotientGroup.mk h : conjugateCosetSpace Y) =
      (QuotientGroup.mk (QuotientGroup.mk' N h) :
        conjugateCosetSpace (Y.map (QuotientGroup.mk' N))) := by
  rfl

private theorem lemma312QuotientCosetMap_injective
    {H : Type*} [Group H] (Y N : Subgroup H) [N.Normal]
    (hNY : N ≤ Y) :
    Function.Injective (lemma312QuotientCosetMap Y N) := by
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  have hker : q.ker ≤ Y := by
    intro x hx
    apply hNY
    simpa [q, QuotientGroup.ker_mk'] using hx
  have hpre : (Y.map q).comap q = Y :=
    Subgroup.comap_map_eq_self hker
  intro omega eta h
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective omega
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective eta
  apply QuotientGroup.eq.mpr
  have hqmem : (q g)⁻¹ * q k ∈ Y.map q := QuotientGroup.eq.mp h
  have hgkpre : g⁻¹ * k ∈ (Y.map q).comap q := by
    change q (g⁻¹ * k) ∈ Y.map q
    simpa using hqmem
  rw [hpre] at hgkpre
  exact hgkpre

private theorem lemma312QuotientCosetMap_surjective
    {H : Type*} [Group H] (Y N : Subgroup H) [N.Normal] :
    Function.Surjective (lemma312QuotientCosetMap Y N) := by
  intro omega
  obtain ⟨xq, rfl⟩ := QuotientGroup.mk_surjective omega
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N xq
  refine ⟨(QuotientGroup.mk x : conjugateCosetSpace Y), ?_⟩
  simpa using congrArg
    (fun t : H ⧸ N =>
      (QuotientGroup.mk t :
        conjugateCosetSpace (Y.map (QuotientGroup.mk' N)))) hx

private theorem lemma312QuotientCosetMap_smul
    {H : Type*} [Group H] (Y N : Subgroup H) [N.Normal]
    (h : H) (omega : conjugateCosetSpace Y) :
    lemma312QuotientCosetMap Y N (h • omega) =
      QuotientGroup.mk' N h • lemma312QuotientCosetMap Y N omega := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective omega
  rfl

private theorem lemma312_existsUnique_fixed_coset_quotient_of_lift
    {H : Type*} [Group H] (Y N : Subgroup H) [N.Normal]
    (hNY : N ≤ Y) (y : H)
    (hambient : ∃! omega : conjugateCosetSpace Y,
      y • omega = omega) :
    ∃! omega : conjugateCosetSpace (Y.map (QuotientGroup.mk' N)),
      QuotientGroup.mk' N y • omega = omega := by
  obtain ⟨omega, homega, hunique⟩ := hambient
  refine ⟨lemma312QuotientCosetMap Y N omega, ?_, ?_⟩
  · calc
      QuotientGroup.mk' N y • lemma312QuotientCosetMap Y N omega =
          lemma312QuotientCosetMap Y N (y • omega) :=
        (lemma312QuotientCosetMap_smul Y N y omega).symm
      _ = lemma312QuotientCosetMap Y N omega := by rw [homega]
  · intro eta heta
    obtain ⟨etaH, hetaH⟩ := lemma312QuotientCosetMap_surjective Y N eta
    have hyetaH : y • etaH = etaH := by
      apply lemma312QuotientCosetMap_injective Y N hNY
      rw [lemma312QuotientCosetMap_smul, hetaH, heta]
    calc
      eta = lemma312QuotientCosetMap Y N etaH := hetaH.symm
      _ = lemma312QuotientCosetMap Y N omega := by rw [hunique etaH hyetaH]

private theorem lemma312_inverts_of_mul_isInvolution
    {H : Type*} [Group H] {z y : H}
    (hz : IsInvolution z) (hzy : IsInvolution (z * y)) :
    z * y * z⁻¹ = y⁻¹ := by
  have hprod : (z * y * z) * y = 1 := by
    simpa [pow_two, mul_assoc] using hzy.sq_eq_one
  have htmp : z * y * z = y⁻¹ :=
    mul_eq_one_iff_eq_inv.mp hprod
  simpa [hz.inv_eq_self] using htmp

private theorem lemma312_exists_involution_lift_of_odd_kernel
    {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (hNodd : Odd (Nat.card N))
    {xq : H ⧸ N} (hxq : IsInvolution xq) :
    ∃ x : H, IsInvolution x ∧ QuotientGroup.mk' N x = xq := by
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  let W : Subgroup (H ⧸ N) := Subgroup.zpowers xq
  let P : Subgroup H := W.comap q
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N xq
  have hxP : x ∈ P := by
    change q x ∈ W
    rw [hx]
    exact Subgroup.mem_zpowers xq
  let xP : P := ⟨x, hxP⟩
  have hxqOrder : orderOf xq = 2 :=
    orderOf_eq_prime hxq.sq_eq_one hxq.ne_one
  have htwoOrderX : 2 ∣ orderOf x := by
    rw [← hxqOrder, ← hx]
    exact orderOf_map_dvd q x
  have htwoCardP : 2 ∣ Nat.card P := by
    apply htwoOrderX.trans
    change orderOf (xP : H) ∣ Nat.card P
    rw [Subgroup.orderOf_coe]
    exact orderOf_dvd_natCard xP
  obtain ⟨t, htOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := P) 2 htwoCardP
  have htOrderH : orderOf (t : H) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact htOrder
  have htData := orderOf_eq_prime_iff.mp htOrderH
  have htInv : IsInvolution (t : H) := ⟨htData.2, htData.1⟩
  have hqtNe : q (t : H) ≠ 1 := by
    intro hqt
    have htN : (t : H) ∈ N :=
      (QuotientGroup.eq_one_iff (N := N) (t : H)).mp hqt
    let tN : N := ⟨(t : H), htN⟩
    have htNI : IsInvolution tN := IsInvolution.subtype htInv htN
    have htNOrder : orderOf tN = 2 :=
      orderOf_eq_prime htNI.sq_eq_one htNI.ne_one
    have hdvd : 2 ∣ Nat.card N := by
      rw [← htNOrder]
      exact orderOf_dvd_natCard tN
    exact hNodd.not_two_dvd_nat hdvd
  have hqtW : q (t : H) ∈ W := t.property
  have hxqW : xq ∈ W := Subgroup.mem_zpowers xq
  have hcardW : Nat.card W = 2 := by
    simpa [W, Nat.card_zpowers] using hxqOrder
  have huniqueW :
      ∀ a b : W, a ≠ 1 → b ≠ 1 → a = b := by
    obtain ⟨w, hwne, hwuniq⟩ :=
      (Nat.card_eq_two_iff' (1 : W)).mp hcardW
    intro a b ha hb
    exact (hwuniq a ha).trans (hwuniq b hb).symm
  have hqtEq : q (t : H) = xq := by
    have hsub : (⟨q (t : H), hqtW⟩ : W) = ⟨xq, hxqW⟩ := by
      apply huniqueW
      · intro h
        exact hqtNe (congrArg Subtype.val h)
      · intro h
        exact hxq.ne_one (congrArg Subtype.val h)
    exact congrArg Subtype.val hsub
  exact ⟨(t : H), htInv, hqtEq⟩

private theorem lemma312_fixedPointCondition_quotient_of_odd_kernel
    {H : Type*} [Group H] [Finite H]
    (Y N : Subgroup H) [N.Normal] (hNY : N ≤ Y)
    (hNodd : Odd (Nat.card N))
    {z : H} (hzY : z ∈ Y) (hz : IsInvolution z)
    (hfixed : Lemma312FixedPointCondition Y z) :
    Lemma312FixedPointCondition
      (Y.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N z) := by
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  have hker : q.ker ≤ Y := by
    intro x hx
    apply hNY
    simpa [q, QuotientGroup.ker_mk'] using hx
  have hpre : (Y.map q).comap q = Y :=
    Subgroup.comap_map_eq_self hker
  have hzq : IsInvolution (q z) :=
    lemma312_quotient_involution_of_odd_kernel N hNodd hz
  intro yq hyq hyqne hinvq
  rcases Subgroup.mem_map.mp hyq with ⟨y, hyY, rfl⟩
  change q y ≠ 1 at hyqne
  change q z * q y * (q z)⁻¹ = (q y)⁻¹ at hinvq
  let a : H ⧸ N := q z * q y
  have haSq : a ^ 2 = 1 := by
    dsimp [a]
    rw [pow_two]
    calc
      q z * q y * (q z * q y) =
          (q z * q y * (q z)⁻¹) * q y := by
            rw [hzq.inv_eq_self]
            group
      _ = (q y)⁻¹ * q y := by rw [hinvq]
      _ = 1 := by simp
  by_cases haOne : a = 1
  · have hyq_eq_zq : q y = q z := by
      have h := eq_inv_of_mul_eq_one_right (by simpa [a] using haOne)
      exact h.trans hzq.inv_eq_self
    have hz_inverted : z * z * z⁻¹ = z⁻¹ := by
      have hzz : z * z = 1 := by
        simpa [pow_two] using hz.sq_eq_one
      rw [hz.inv_eq_self, hzz]
      simp
    rw [hyq_eq_zq]
    exact lemma312_existsUnique_fixed_coset_quotient_of_lift
      Y N hNY z (hfixed z hzY hz.ne_one hz_inverted)
  · have haInv : IsInvolution a := ⟨haOne, haSq⟩
    obtain ⟨t, ht, hqt⟩ :=
      lemma312_exists_involution_lift_of_odd_kernel N hNodd haInv
    have htaYq : q t ∈ Y.map q := by
      rw [hqt]
      exact (Y.map q).mul_mem
        (Subgroup.mem_map_of_mem q hzY)
        (Subgroup.mem_map_of_mem q hyY)
    have htY : t ∈ Y := by
      have : t ∈ (Y.map q).comap q := htaYq
      rw [hpre] at this
      exact this
    let y' : H := z⁻¹ * t
    have hy'Y : y' ∈ Y := by
      dsimp [y']
      exact Y.mul_mem (Y.inv_mem hzY) htY
    have hy'q : q y' = q y := by
      dsimp [y']
      rw [map_mul, hqt]
      dsimp [a]
      simp
    have hy'ne : y' ≠ 1 := by
      intro h
      apply hyqne
      rw [← hy'q, h]
      simp
    have hy'inv : z * y' * z⁻¹ = y'⁻¹ := by
      apply lemma312_inverts_of_mul_isInvolution hz
      dsimp [y']
      simpa [mul_assoc] using ht
    rw [← hy'q]
    exact lemma312_existsUnique_fixed_coset_quotient_of_lift
      Y N hNY y' (hfixed y' hy'Y hy'ne hy'inv)

/-- Strong embedding descends through a normal odd-order subgroup contained
in the strongly embedded subgroup. -/
private theorem lemma312_quotient_stronglyEmbedded_of_odd_kernel
    {H : Type u} [Group H] [Finite H]
    (Y N : Subgroup H) [N.Normal] (hNY : N ≤ Y)
    (hNodd : Odd (Nat.card N)) (hY : IsStronglyEmbedded Y) :
    IsStronglyEmbedded (Y.map (QuotientGroup.mk' N)) := by
  classical
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  let Yq : Subgroup (H ⧸ N) := Y.map q
  have hker : q.ker ≤ Y := by
    simpa [q, QuotientGroup.ker_mk'] using hNY
  have hcomapY : Yq.comap q = Y := by
    exact Subgroup.comap_map_eq_self hker
  have hYqproper : Yq ≠ ⊤ := by
    intro htop
    apply hY.ne_top
    calc
      Y = Yq.comap q := hcomapY.symm
      _ = (⊤ : Subgroup (H ⧸ N)).comap q := by rw [htop]
      _ = ⊤ := Subgroup.comap_top q
  obtain ⟨z, hzY, hz⟩ := hY.exists_involution
  have hzq : IsInvolution (q z) :=
    lemma312_quotient_involution_of_odd_kernel N hNodd hz
  refine ⟨hYqproper, ⟨q z, Subgroup.mem_map_of_mem q hzY, hzq⟩, ?_⟩
  intro gq hgqYq xq hxqYq hxqRight hxq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gq
  have hgY : g ∉ Y := by
    intro hg
    exact hgqYq (Subgroup.mem_map_of_mem q hg)
  let Iq : Subgroup (H ⧸ N) :=
    Yq ⊓ rightConjugate Yq (q g)
  have hxqIq : xq ∈ Iq := ⟨hxqYq, hxqRight⟩
  obtain ⟨p, hpq⟩ := QuotientGroup.mk'_surjective N xq
  have hpIq : p ∈ Iq.comap q := by
    change q p ∈ Iq
    rw [hpq]
    exact hxqIq
  have hxqOrder : orderOf xq = 2 :=
    orderOf_eq_prime hxq.sq_eq_one hxq.ne_one
  have htwo_order_p : 2 ∣ orderOf p := by
    rw [← hxqOrder, ← hpq]
    exact orderOf_map_dvd q p
  let W : Subgroup H := Subgroup.zpowers p
  have htwo_cardW : 2 ∣ Nat.card W := by
    simpa [W, Nat.card_zpowers] using htwo_order_p
  obtain ⟨w, hwOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := W) 2 htwo_cardW
  have hwOrderH : orderOf (w : H) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hwOrder
  have hwData := orderOf_eq_prime_iff.mp hwOrderH
  have hwInv : IsInvolution (w : H) := ⟨hwData.2, hwData.1⟩
  have hWle : W ≤ Iq.comap q := Subgroup.zpowers_le.mpr hpIq
  have hwIq : (w : H) ∈ Iq.comap q := hWle w.property
  have hwY : (w : H) ∈ Y := by
    have : (w : H) ∈ Yq.comap q := hwIq.1
    rw [hcomapY] at this
    exact this
  have hmapRight :
      (rightConjugate Y g).map q = rightConjugate Yq (q g) := by
    rw [rightConjugate, rightConjugate]
    change
      (Y.map (MulAut.conj g⁻¹).toMonoidHom).map q =
        (Y.map q).map (MulAut.conj (q g)⁻¹).toMonoidHom
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨q y, ⟨y, hy, rfl⟩, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
    · rintro ⟨x, hx, rfl⟩
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨g⁻¹ * y * (g⁻¹)⁻¹, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr
          ⟨y, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
      · simp [MulAut.conj_apply, mul_assoc]
  have hNright : N ≤ rightConjugate Y g := by
    intro n hnN
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨g * n * g⁻¹, ?_, ?_⟩
    · exact hNY ((inferInstance : N.Normal).conj_mem n hnN g)
    · simp [mul_assoc]
  have hcomapRight :
      (rightConjugate Yq (q g)).comap q = rightConjugate Y g := by
    rw [← hmapRight]
    exact Subgroup.comap_map_eq_self (by
      simpa [q, QuotientGroup.ker_mk'] using hNright)
  have hwRight : (w : H) ∈ rightConjugate Y g := by
    have : (w : H) ∈ (rightConjugate Yq (q g)).comap q := hwIq.2
    rw [hcomapRight] at this
    exact this
  exact hY.2.2 hgY hwY hwRight hwInv

/-- A normal subgroup contained in a strongly embedded subgroup has odd
cardinality.  This is the reusable strong-embedding form of the local lemma
used in the quotient branch of Lemma 3.12. -/
public theorem IsStronglyEmbedded.normal_le_card_odd
    {H : Type u} [Group H] [Finite H]
    {Y N : Subgroup H} (hY : IsStronglyEmbedded Y)
    [N.Normal] (hNY : N ≤ Y) :
    Odd (Nat.card N) :=
  lemma312_normal_le_stronglyEmbedded_card_odd hY inferInstance hNY

/-- An involution remains an involution after quotienting by a normal
odd-order subgroup. -/
public theorem IsInvolution.quotient_mk_of_odd_kernel
    {H : Type u} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (hNodd : Odd (Nat.card N))
    {z : H} (hz : IsInvolution z) :
    IsInvolution (QuotientGroup.mk' N z) :=
  lemma312_quotient_involution_of_odd_kernel N hNodd hz

/-- A homomorphism carries a conjugate subgroup to the conjugate of its
image. -/
public theorem rightConjugate_map
    {G : Type u} {H : Type v} [Group G] [Group H]
    (Y : Subgroup G) (f : G →* H) (g : G) :
    (rightConjugate Y g).map f = rightConjugate (Y.map f) (f g) := by
  rw [rightConjugate, rightConjugate]
  change
    (Y.map (MulAut.conj g⁻¹).toMonoidHom).map f =
      (Y.map f).map (MulAut.conj (f g)⁻¹).toMonoidHom
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨f y, ⟨y, hy, rfl⟩, ?_⟩
    simp [mul_assoc]
  · rintro ⟨x, hx, rfl⟩
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨g⁻¹ * y * (g⁻¹)⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr
        ⟨y, hy, by simp [mul_assoc]⟩
    · simp [mul_assoc]

/-- Membership in the image of a subgroup modulo a contained normal kernel
is equivalent to membership in the original subgroup. -/
public theorem quotient_mk_mem_map_iff_of_le
    {G : Type u} [Group G]
    (N Y : Subgroup G) [N.Normal] (hNY : N ≤ Y) (x : G) :
    QuotientGroup.mk' N x ∈ Y.map (QuotientGroup.mk' N) ↔ x ∈ Y := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  change x ∈ (Y.map q).comap q ↔ x ∈ Y
  rw [Subgroup.comap_map_eq_self]
  simpa [q, QuotientGroup.ker_mk'] using hNY

/-- Conjugate-subgroup membership lifts exactly through a quotient by a
normal subgroup already contained in the original subgroup. -/
public theorem rightConjugate_map_quotient_comap_eq
    {G : Type u} [Group G]
    (N Y : Subgroup G) [N.Normal] (hNY : N ≤ Y) (g : G) :
    (rightConjugate (Y.map (QuotientGroup.mk' N))
        (QuotientGroup.mk' N g)).comap (QuotientGroup.mk' N) =
      rightConjugate Y g := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hNright : N ≤ rightConjugate Y g := by
    intro n hnN
    rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨g * n * g⁻¹, ?_, ?_⟩
    · exact hNY ((inferInstance : N.Normal).conj_mem n hnN g)
    · simp [mul_assoc]
  rw [← rightConjugate_map Y q g]
  exact Subgroup.comap_map_eq_self (by
    simpa [q, QuotientGroup.ker_mk'] using hNright)

/-- If an involution centralizes an odd normal subgroup, centralizing its
image modulo that subgroup already means centralizing the involution. -/
public theorem centralizer_comap_quotient_eq_of_odd_kernel
    {G : Type u} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (hKodd : Odd (Nat.card K))
    {u0 : G} (hu : IsInvolution u0)
    (hKcent : K ≤ Subgroup.centralizer ({u0} : Set G)) :
    (Subgroup.centralizer
        ({QuotientGroup.mk' K u0} : Set (G ⧸ K))).comap
      (QuotientGroup.mk' K) =
        Subgroup.centralizer ({u0} : Set G) := by
  apply le_antisymm
  · intro x hx
    have hxq : QuotientGroup.mk' K x * QuotientGroup.mk' K u0 =
        QuotientGroup.mk' K u0 * QuotientGroup.mk' K x :=
      Subgroup.mem_centralizer_singleton_iff.mp hx
    let c : G := x * u0 * x⁻¹ * u0⁻¹
    have hcK : c ∈ K := by
      rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' K c = 1
      rw [show QuotientGroup.mk' K c =
          QuotientGroup.mk' K x * QuotientGroup.mk' K u0 *
            (QuotientGroup.mk' K x)⁻¹ *
              (QuotientGroup.mk' K u0)⁻¹ by simp [c]]
      rw [hxq]
      group
    have hcu : c * u0 = u0 * c :=
      Subgroup.mem_centralizer_singleton_iff.mp (hKcent hcK)
    have huu : u0 * u0 = 1 := by
      simpa [pow_two] using hu.sq_eq_one
    have hconj : u0 * c * u0⁻¹ = c⁻¹ := by
      calc
        u0 * c * u0⁻¹ =
            u0 * x * u0 * x⁻¹ * (u0 * u0) := by
          dsimp [c]
          rw [hu.inv_eq_self]
          group
        _ = u0 * x * u0 * x⁻¹ := by rw [huu, mul_one]
        _ = c⁻¹ := by
          dsimp [c]
          simp only [mul_inv_rev, hu.inv_eq_self, inv_inv]
          group
    have hcEqInv : c = c⁻¹ := by
      calc
        c = u0 * c * u0⁻¹ := by
          rw [hu.inv_eq_self]
          calc
            c = (u0 * u0) * c := by rw [huu, one_mul]
            _ = u0 * (u0 * c) := by group
            _ = u0 * (c * u0) := by rw [hcu.symm]
            _ = u0 * c * u0 := by group
        _ = c⁻¹ := hconj
    have hcSq : c ^ 2 = 1 := by
      calc
        c ^ 2 = c * c := pow_two c
        _ = c * c⁻¹ := congrArg (fun z : G ↦ c * z) hcEqInv
        _ = 1 := mul_inv_cancel c
    have hcOne : c = 1 := by
      by_contra hcne
      let cK : K := ⟨c, hcK⟩
      have hcI : IsInvolution c := ⟨hcne, hcSq⟩
      have hcKI : IsInvolution cK := IsInvolution.subtype hcI hcK
      have horder : orderOf cK = 2 :=
        orderOf_eq_prime hcKI.sq_eq_one hcKI.ne_one
      have hdvd : 2 ∣ Nat.card K := by
        rw [← horder]
        exact orderOf_dvd_natCard cK
      exact hKodd.not_two_dvd_nat hdvd
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcdef : x * u0 * x⁻¹ * u0⁻¹ = 1 := by
      simpa [c] using hcOne
    have h := congrArg (fun z : G ↦ z * u0 * x) hcdef
    simpa [mul_assoc] using h
  · intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg (QuotientGroup.mk' K)
      (Subgroup.mem_centralizer_singleton_iff.mp hx)

/-- Strong embedding descends through a normal odd-order subgroup contained
in the strongly embedded subgroup. -/
public theorem IsStronglyEmbedded.map_quotient_of_odd_kernel
    {H : Type u} [Group H] [Finite H]
    {Y N : Subgroup H} (hY : IsStronglyEmbedded Y)
    [N.Normal] (hNY : N ≤ Y) (hNodd : Odd (Nat.card N)) :
    IsStronglyEmbedded (Y.map (QuotientGroup.mk' N)) :=
  lemma312_quotient_stronglyEmbedded_of_odd_kernel Y N hNY hNodd hY

/-- Equality of involutions lifts through an odd normal kernel centralized by
one of them. -/
private theorem lemma312_involution_eq_of_quotient_eq_of_odd_kernel
    {H : Type u} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (hNodd : Odd (Nat.card N))
    {y z : H} (hy : IsInvolution y) (hz : IsInvolution z)
    (hzCent : z ∈ Subgroup.centralizer (N : Set H))
    (hq : QuotientGroup.mk' N y = QuotientGroup.mk' N z) :
    y = z := by
  let d : H := y * z⁻¹
  have hdN : d ∈ N := by
    simpa [d, div_eq_mul_inv] using
      (QuotientGroup.eq_iff_div_mem (N := N)).mp hq
  have hcomm : d * z = z * d := by
    rw [Subgroup.mem_centralizer_iff] at hzCent
    exact hzCent d hdN
  have hy_eq : y = d * z := by
    dsimp [d]
    simp [mul_assoc]
  have hdsq : d ^ 2 = 1 := by
    have hdzsq : (d * z) ^ 2 = d ^ 2 := by
      rw [pow_two, pow_two]
      calc
        d * z * (d * z) = d * (z * d) * z := by simp [mul_assoc]
        _ = d * (d * z) * z := by rw [hcomm.symm]
        _ = d * d * (z * z) := by group
        _ = d * d := by
          have hzz : z * z = 1 := by
            simpa [pow_two] using hz.sq_eq_one
          rw [hzz]
          simp
    calc
      d ^ 2 = (d * z) ^ 2 := hdzsq.symm
      _ = y ^ 2 := by rw [← hy_eq]
      _ = 1 := hy.sq_eq_one
  have hd_one : d = 1 := by
    by_contra hdne
    let dN : N := ⟨d, hdN⟩
    have hdNI : IsInvolution dN := by
      constructor
      · intro h
        exact hdne (congrArg Subtype.val h)
      · apply Subtype.ext
        exact hdsq
    have horder : orderOf dN = 2 :=
      orderOf_eq_prime hdNI.sq_eq_one hdNI.ne_one
    have hdvd : 2 ∣ Nat.card N := by
      rw [← horder]
      exact orderOf_dvd_natCard dN
    exact hNodd.not_two_dvd_nat hdvd
  dsimp [d] at hd_one
  have h := congrArg (fun t : H => t * z) hd_one
  simpa [mul_assoc] using h

/-- An involution acting fixed-point freely on an abelian normal subgroup
acts on that subgroup by inversion. -/
private theorem lemma312_conjugates_eq_inv_of_fixedPoint_free_involution
    {H : Type u} [Group H] (N : Subgroup H) [N.Normal]
    (hNcomm : IsMulCommutative N) {y : H} (hy : IsInvolution y)
    (hfixedFree : N ⊓ Subgroup.centralizer ({y} : Set H) = ⊥) :
    ∀ n : H, n ∈ N → y * n * y⁻¹ = n⁻¹ := by
  intro n hn
  let d : H := n * (y * n * y⁻¹)
  have hynN : y * n * y⁻¹ ∈ N := by
    exact (inferInstance : N.Normal).conj_mem n hn y
  have hdN : d ∈ N := by
    exact N.mul_mem hn hynN
  have hcommN : ∀ a b : H, a ∈ N → b ∈ N → a * b = b * a := by
    intro a b ha hb
    letI : IsMulCommutative N := hNcomm
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : N) ⟨b, hb⟩)
  have hd_fix : y * d * y⁻¹ = d := by
    dsimp [d]
    have hy2 : y * y = 1 := by
      simpa [pow_two] using hy.sq_eq_one
    have hnn : n * (y * n * y⁻¹) = (y * n * y⁻¹) * n :=
      hcommN n (y * n * y⁻¹) hn hynN
    calc
      y * (n * (y * n * y⁻¹)) * y⁻¹ =
          y * ((y * n * y⁻¹) * n) * y⁻¹ := by rw [hnn]
      _ = n * (y * n * y⁻¹) := by
        rw [hy.inv_eq_self]
        calc
          y * (y * n * y * n) * y = (y * y) * n * (y * n * y) := by group
          _ = n * (y * n * y) := by rw [hy2]; simp
  have hdC : d ∈ Subgroup.centralizer ({y} : Set H) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hmul := congrArg (fun t : H => t * y) hd_fix
    simpa [mul_assoc] using hmul.symm
  have hd_bot : d ∈ (N ⊓ Subgroup.centralizer ({y} : Set H)) := ⟨hdN, hdC⟩
  have hd_one : d = 1 := by
    rw [hfixedFree] at hd_bot
    exact hd_bot
  dsimp [d] at hd_one
  have hn_eq : n = (y * n * y⁻¹)⁻¹ := mul_eq_one_iff_eq_inv.mp hd_one
  simpa using (congrArg Inv.inv hn_eq).symm

/-- The faithful maximal branch of Lemma 3.12.  The hypothesis says exactly
that the coset action has no nontrivial normal kernel inside `Y`. -/
private theorem lemma312_unique_involution_of_maximal_faithful
    {H : Type u} [Group H] [Finite H]
    (Y : Subgroup H) (hsolv : Group.IsSolvable H)
    (hY : IsStronglyEmbedded Y) (hmax : IsCoatom Y)
    {z : H} (hzY : z ∈ Y) (hz : IsInvolution z)
    (hfaith : ∀ N : Subgroup H, N.Normal → N ≤ Y → N ≠ ⊥ → False) :
    ∀ y : H, y ∈ Y → IsInvolution y → y = z := by
  classical
  have hnt : Nontrivial H := ⟨⟨z, 1, hz.ne_one⟩⟩
  obtain ⟨N, hNnormal, hNne, hNmin⟩ :=
    exists_minimal_normal (G := H) hsolv hnt
  letI : N.Normal := hNnormal
  letI : IsMinimalNormal N := {
    minimal := by
      intro K hKnormal hKN
      by_cases hKne : K = ⊥
      · exact Or.inl hKne
      · exact Or.inr (hNmin K hKnormal hKN hKne)
  }
  letI : Group.IsSolvable H := hsolv
  haveI : Group.IsSolvable N := by infer_instance
  have hNcomm : IsMulCommutative N :=
    minimalNormal_solvable_isMulCommutative N
  have hNnotle : ¬ N ≤ Y := by
    intro hNY
    exact hfaith N hNnormal hNY hNne
  have hYltSup : Y < N ⊔ Y := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro hEq
    apply hNnotle
    calc
      N ≤ N ⊔ Y := le_sup_left
      _ = Y := hEq.symm
  have hsup : N ⊔ Y = ⊤ := hmax.2 (N ⊔ Y) hYltSup

  let C : Subgroup H := Y ⊓ Subgroup.centralizer (N : Set H)
  have hconj_mem_C :
      ∀ a : H, a ∈ Y → ∀ c : H, c ∈ C → a * c * a⁻¹ ∈ C := by
    intro a haY c hcC
    have hcY : c ∈ Y := hcC.1
    have hcCent : c ∈ Subgroup.centralizer (N : Set H) := hcC.2
    constructor
    · exact Y.mul_mem (Y.mul_mem haY hcY) (Y.inv_mem haY)
    · change ∀ n : H, n ∈ N → n * (a * c * a⁻¹) = (a * c * a⁻¹) * n
      rw [Subgroup.mem_centralizer_iff] at hcCent
      intro n hnN
      have hn' : a⁻¹ * n * a ∈ N := by
        simpa using (inferInstance : N.Normal).conj_mem n hnN a⁻¹
      have hcomm := hcCent (a⁻¹ * n * a) hn'
      calc
        n * (a * c * a⁻¹) = a * ((a⁻¹ * n * a) * c) * a⁻¹ := by group
        _ = a * (c * (a⁻¹ * n * a)) * a⁻¹ := by rw [hcomm]
        _ = (a * c * a⁻¹) * n := by group
  have hYnormC : Y ≤ Subgroup.normalizer C := by
    intro a haY
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · exact hconj_mem_C a haY c
    · intro hc
      have hback := hconj_mem_C a⁻¹ (Y.inv_mem haY)
        (a * c * a⁻¹) hc
      simpa [mul_assoc] using hback
  have hNnormC : N ≤ Subgroup.normalizer C := by
    intro n hnN
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      have hcCent : c ∈ Subgroup.centralizer (N : Set H) := hc.2
      rw [Subgroup.mem_centralizer_iff] at hcCent
      have hcomm := hcCent n hnN
      have heq : n * c * n⁻¹ = c := by
        rw [hcomm]
        simp
      simpa [heq] using hc
    · intro hc
      have hcCent : n * c * n⁻¹ ∈ Subgroup.centralizer (N : Set H) := hc.2
      rw [Subgroup.mem_centralizer_iff] at hcCent
      have hcomm := hcCent n hnN
      have hc_eq : c = n * c * n⁻¹ := by
        calc
          c = n⁻¹ * (n * c * n⁻¹) * n := by group
          _ = n * c * n⁻¹ := by
            calc
              n⁻¹ * (n * c * n⁻¹) * n = n⁻¹ * ((n * c * n⁻¹) * n) := by
                simp [mul_assoc]
              _ = n⁻¹ * (n * (n * c * n⁻¹)) := by rw [hcomm]
              _ = n * c * n⁻¹ := by simp
      rw [hc_eq]
      exact hc
  have hCnormal : C.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_unique
    rw [← hsup]
    exact sup_le hNnormC hYnormC
  have hCbot : C = ⊥ := by
    by_contra hCne
    exact hfaith C hCnormal inf_le_left hCne
  have hNYbot : N ⊓ Y = ⊥ := by
    apply le_antisymm
    · intro n hn
      rw [← hCbot]
      refine ⟨hn.2, ?_⟩
      change ∀ m : H, m ∈ N → m * n = n * m
      intro m hmN
      letI : IsMulCommutative N := hNcomm
      exact congrArg Subtype.val (mul_comm (⟨m, hmN⟩ : N) ⟨n, hn.1⟩)
    · exact bot_le
  intro y hyY hy
  have hyFixedFree : N ⊓ Subgroup.centralizer ({y} : Set H) = ⊥ := by
    apply le_antisymm
    · intro n hn
      rw [Subgroup.mem_bot]
      have hnY : n ∈ Y := hY.centralizer_le hyY hy hn.2
      have : n ∈ N ⊓ Y := ⟨hn.1, hnY⟩
      rw [hNYbot] at this
      exact this
    · exact bot_le
  have hzFixedFree : N ⊓ Subgroup.centralizer ({z} : Set H) = ⊥ := by
    apply le_antisymm
    · intro n hn
      rw [Subgroup.mem_bot]
      have hnY : n ∈ Y := hY.centralizer_le hzY hz hn.2
      have : n ∈ N ⊓ Y := ⟨hn.1, hnY⟩
      rw [hNYbot] at this
      exact this
    · exact bot_le
  have hyInv : ∀ n : H, n ∈ N → y * n * y⁻¹ = n⁻¹ :=
    lemma312_conjugates_eq_inv_of_fixedPoint_free_involution
      N hNcomm hy hyFixedFree
  have hzInv : ∀ n : H, n ∈ N → z * n * z⁻¹ = n⁻¹ :=
    lemma312_conjugates_eq_inv_of_fixedPoint_free_involution
      N hNcomm hz hzFixedFree
  have hyzC : y * z ∈ C := by
    constructor
    · exact Y.mul_mem hyY hzY
    · change ∀ n : H, n ∈ N → n * (y * z) = (y * z) * n
      intro n hnN
      have hzn := hzInv n hnN
      have hninvN := N.inv_mem hnN
      have hy_ninv := hyInv n⁻¹ hninvN
      symm
      calc
        y * z * n = y * (z * n * z⁻¹) * z := by simp [mul_assoc]
        _ = y * n⁻¹ * z := by rw [hzn]
        _ = (y * n⁻¹ * y⁻¹) * y * z := by simp [mul_assoc]
        _ = n * (y * z) := by rw [hy_ninv]; simp [mul_assoc]
  have hyz_one : y * z = 1 := by
    rw [hCbot] at hyzC
    exact hyzC
  have hy_eq_zinv : y = z⁻¹ := mul_eq_one_iff_eq_inv.mp hyz_one
  simpa [hz.inv_eq_self] using hy_eq_zinv

/-- The quotient branch of Lemma 3.12 when a nontrivial minimal normal
subgroup lies inside `Y`.  The recursive argument is supplied only at the
strictly smaller quotient. -/
private theorem lemma312_unique_involution_of_minimalNormal_le
    {H : Type u} [Group H] [Finite H]
    (Y N : Subgroup H) [N.Normal] [IsMinimalNormal N]
    (_hNne : N ≠ ⊥) (hNY : N ≤ Y)
    (_hsolv : Group.IsSolvable H) (hY : IsStronglyEmbedded Y)
    {z : H} (hzY : z ∈ Y) (hz : IsInvolution z)
    (hfixed : Lemma312FixedPointCondition Y z)
    (ih :
      let q : H →* H ⧸ N := QuotientGroup.mk' N
      let Yq : Subgroup (H ⧸ N) := Y.map q
      let zq : H ⧸ N := q z
      IsStronglyEmbedded Yq → IsInvolution zq → zq ∈ Yq →
        Lemma312FixedPointCondition Yq zq →
          ∀ yq : H ⧸ N, yq ∈ Yq → IsInvolution yq → yq = zq) :
    ∀ y : H, y ∈ Y → IsInvolution y → y = z := by
  classical
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  let Yq : Subgroup (H ⧸ N) := Y.map q
  let zq : H ⧸ N := q z
  have hNodd : Odd (Nat.card N) :=
    lemma312_normal_le_stronglyEmbedded_card_odd hY
      (inferInstance : N.Normal) hNY
  have hzCent : z ∈ Subgroup.centralizer (N : Set H) :=
    lemma312_fixedPointCondition_centralizes_normal_le
      Y hY.ne_top hz hfixed N (inferInstance : N.Normal) hNY
  have hYq : IsStronglyEmbedded Yq :=
    lemma312_quotient_stronglyEmbedded_of_odd_kernel Y N hNY hNodd hY
  have hzq : IsInvolution zq :=
    lemma312_quotient_involution_of_odd_kernel N hNodd hz
  have hzqY : zq ∈ Yq := Subgroup.mem_map_of_mem q hzY
  have hfixedq : Lemma312FixedPointCondition Yq zq :=
    lemma312_fixedPointCondition_quotient_of_odd_kernel
      Y N hNY hNodd hzY hz hfixed
  have huniqQ :
      ∀ yq : H ⧸ N, yq ∈ Yq → IsInvolution yq → yq = zq :=
    ih hYq hzq hzqY hfixedq
  intro y hyY hy
  have hyq : IsInvolution (q y) :=
    lemma312_quotient_involution_of_odd_kernel N hNodd hy
  have hyqY : q y ∈ Yq := Subgroup.mem_map_of_mem q hyY
  exact lemma312_involution_eq_of_quotient_eq_of_odd_kernel
    N hNodd hy hz hzCent (huniqQ (q y) hyqY hyq)

private theorem lemma312_unique_involution_core_aux :
    ∀ n : ℕ, ∀ {H : Type u} [Group H] [Finite H],
      Nat.card H = n →
      ∀ (Y : Subgroup H), Group.IsSolvable H → Even (Nat.card H) →
        IsStronglyEmbedded Y →
        ∀ {z : H}, z ∈ Y → IsInvolution z →
          Lemma312FixedPointCondition Y z →
            ∀ y : H, y ∈ Y → IsInvolution y → y = z := by
  intro n
  refine Nat.strongRecOn
    (motive := fun n =>
      ∀ {H : Type u} [Group H] [Finite H],
        Nat.card H = n →
        ∀ (Y : Subgroup H), Group.IsSolvable H → Even (Nat.card H) →
          IsStronglyEmbedded Y →
          ∀ {z : H}, z ∈ Y → IsInvolution z →
            Lemma312FixedPointCondition Y z →
              ∀ y : H, y ∈ Y → IsInvolution y → y = z)
    n (fun n ih => by
      intro H _instGroup _instFinite hcard Y hsolv _hEven hY z hzY hz hfixed
      classical
      by_cases hmax : IsCoatom Y
      · by_cases hkernel :
          ∃ N : Subgroup H, N.Normal ∧ N ≤ Y ∧ N ≠ ⊥
        · obtain ⟨K, hKnormal, hKY, hKne⟩ := hkernel
          obtain ⟨N, hNnormal, hNK, hNne, hNmin⟩ :=
            exists_minimal_normal_le (G := H) K hKnormal hKne
          letI : N.Normal := hNnormal
          letI : IsMinimalNormal N := {
            minimal := by
              intro L hLnormal hLN
              by_cases hLne : L = ⊥
              · exact Or.inl hLne
              · exact Or.inr (hNmin L hLnormal hLN hLne)
          }
          apply lemma312_unique_involution_of_minimalNormal_le
            Y N hNne (hNK.trans hKY) hsolv hY hzY hz hfixed
          dsimp
          intro hYq hzq hzqY hfixedq
          letI : Group.IsSolvable H := hsolv
          have hsolvQ : Group.IsSolvable (H ⧸ N) := by infer_instance
          have hEvenQ : Even (Nat.card (H ⧸ N)) := by
            have horder : orderOf (QuotientGroup.mk' N z) = 2 :=
              orderOf_eq_prime hzq.sq_eq_one hzq.ne_one
            apply even_iff_two_dvd.mpr
            rw [← horder]
            exact orderOf_dvd_natCard (QuotientGroup.mk' N z)
          have hquot_lt : Nat.card (H ⧸ N) < n := by
            simpa [hcard] using card_quotient_lt_of_ne_bot (G := H) N hNne
          have hrec :=
            ih (Nat.card (H ⧸ N)) hquot_lt (H := H ⧸ N) rfl
              (Y.map (QuotientGroup.mk' N)) hsolvQ hEvenQ hYq
              hzqY hzq hfixedq
          exact hrec
        · exact lemma312_unique_involution_of_maximal_faithful
            Y hsolv hY hmax hzY hz (by
              intro N hNnormal hNY hNne
              exact hkernel ⟨N, hNnormal, hNY, hNne⟩)
      · have hYne : Y ≠ ⊤ := hY.ne_top
        rw [IsCoatom] at hmax
        push Not at hmax
        obtain ⟨K, hY_lt_K, hKne⟩ := hmax hYne
        have hKlt : K < (⊤ : Subgroup H) := lt_top_iff_ne_top.mpr hKne
        let YK : Subgroup K := Y.comap K.subtype
        have hzK : z ∈ K := hY_lt_K.le hzY
        let zK : K := ⟨z, hzK⟩
        have hYKproper : YK ≠ ⊤ := by
          intro htop
          have hKY : K ≤ Y := by
            intro k hk
            let kK : K := ⟨k, hk⟩
            have hkYK : kK ∈ YK := by
              rw [htop]
              exact Subgroup.mem_top kK
            exact hkYK
          exact (not_le_of_gt hY_lt_K) hKY
        have hzKinv : IsInvolution zK := IsInvolution.subtype hz hzK
        have hYKstrong : IsStronglyEmbedded YK :=
          hY.comap_of_injective K.subtype Subtype.val_injective hYKproper
            ⟨zK, hzY, hzKinv⟩
        letI : Group.IsSolvable H := hsolv
        have hsolvK : Group.IsSolvable K := by infer_instance
        have hfixedK : Lemma312FixedPointCondition YK zK :=
          lemma312_fixedPointCondition_comap Y K hzK hfixed
        have hEvenK : Even (Nat.card K) := by
          have horder : orderOf zK = 2 :=
            orderOf_eq_prime hzKinv.sq_eq_one hzKinv.ne_one
          apply even_iff_two_dvd.mpr
          rw [← horder]
          exact orderOf_dvd_natCard zK
        have hKcard_lt : Nat.card K < n := by
          simpa [hcard] using natCard_lt_of_subgroup_lt hKlt
        have hrec := ih (Nat.card K) hKcard_lt (H := K) rfl
          YK hsolvK hEvenK hYKstrong
          (show zK ∈ YK from hzY) hzKinv hfixedK
        intro y hyY hy
        have hyK : y ∈ K := hY_lt_K.le hyY
        let yK : K := ⟨y, hyK⟩
        have hyKinv : IsInvolution yK := IsInvolution.subtype hy hyK
        have hyK_eq : yK = zK := hrec yK hyY hyKinv
        exact congrArg Subtype.val hyK_eq)

/-- The hard induction core of Lemma 3.12: under the literal fixed-point
hypothesis, the chosen involution is the only involution in `Y`. -/
public theorem lemma312_unique_involution_core
    {H : Type u} [Group H] [Finite H]
    (Y : Subgroup H) (hsolv : Group.IsSolvable H)
    (hEven : Even (Nat.card H)) (hY : IsStronglyEmbedded Y)
    {z : H} (hzY : z ∈ Y) (hz : IsInvolution z)
    (hfixed : Lemma312FixedPointCondition Y z) :
    ∀ y : H, y ∈ Y → IsInvolution y → y = z := by
  exact lemma312_unique_involution_core_aux (Nat.card H) rfl
    Y hsolv hEven hY hzY hz hfixed

/-- Lemma 3.12 from `docs/cfsg-vol4.tex`. -/
public theorem lemma_3_12
    {H : Type u} [Group H] [Finite H]
    (Y : Subgroup H) (hsolv : Group.IsSolvable H)
    (hEven : Even (Nat.card H)) (hY : IsStronglyEmbedded Y)
    {z : H} (hzY : z ∈ Y) (hz : IsInvolution z)
    (hfixed : Lemma312FixedPointCondition Y z) :
    Y = Subgroup.centralizer ({z} : Set H) ∧
      ∀ y : H, y ∈ Y → IsInvolution y → y = z := by
  have hunique := lemma312_unique_involution_core
    Y hsolv hEven hY hzY hz hfixed
  refine ⟨?_, hunique⟩
  apply le_antisymm
  · intro y hyY
    let v : H := rightConjugateElem z y⁻¹
    have hvY : v ∈ Y := by
      simpa [v, rightConjugateElem, mul_assoc] using
        Y.mul_mem (Y.mul_mem hyY hzY) (Y.inv_mem hyY)
    have hv : IsInvolution v := isInvolution_rightConjugateElem hz
    have hvz : v = z := hunique v hvY hv
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hconj : y * z * y⁻¹ = z := by
      simpa [v, rightConjugateElem, mul_assoc] using hvz
    calc
      y * z = (y * z * y⁻¹) * y := by simp [mul_assoc]
      _ = z * y := by rw [hconj]
  · exact hY.centralizer_le hzY hz

end CFSG.BenderSuzuki
