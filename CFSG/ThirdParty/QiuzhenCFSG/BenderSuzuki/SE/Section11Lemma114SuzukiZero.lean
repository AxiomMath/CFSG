module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Core
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.V.proposition_1_2

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.4: the degenerate Suzuki model

This file proves the concrete facts about `Sz(2)` needed in Lemma 11.4.  Its
root subgroup is cyclic of order four, the Bruhat decomposition gives group
order twenty, and every product of two distinct involutions has order five.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open MatrixGroups PFAppendixIII External

universe u

private theorem lemma114_binaryGaloisFieldOne_eq_zero_or_one
    (x : BinaryGaloisField 1) : x = 0 ∨ x = 1 := by
  apply eq_zero_or_one_of_sq_eq_self
  have hcard : Nat.card (BinaryGaloisField 1) = 2 := by
    simpa [BinaryGaloisField] using GaloisField.card 2 1 (by norm_num)
  letI : Fintype (BinaryGaloisField 1) := Fintype.ofFinite _
  have hx := FiniteField.pow_card x
  rw [Fintype.card_eq_nat_card, hcard] at hx
  simpa [pow_two] using hx

private theorem lemma114_binaryGaloisFieldOne_one_add_one :
    (1 + 1 : BinaryGaloisField 1) = 0 :=
  CharTwo.add_self_eq_zero 1

private noncomputable def lemma114_suzukiZeroRootGenerator :
    SuzukiMatrixGroup 0 :=
  ⟨SuzukiRootGL 0 1 0,
    Subgroup.subset_closure (Or.inl ⟨1, 0, rfl⟩)⟩

set_option maxHeartbeats 1200000 in
private theorem lemma114_suzukiZeroRootGenerator_order :
    orderOf lemma114_suzukiZeroRootGenerator = 4 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 4)]
  constructor
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lemma114_suzukiZeroRootGenerator, SuzukiRootGL,
        SuzukiRootMatrix, Matrix.mul_apply, Fin.sum_univ_four, pow_succ,
        lemma114_binaryGaloisFieldOne_one_add_one]
  · intro m hm4 hm0
    have hm : m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases hm with rfl | rfl | rfl
    · intro h
      have h01 := congrArg
        (fun A : SuzukiMatrixGroup 0 =>
          (((A : GL (Fin 4) (BinaryGaloisField 1)) :
            Matrix (Fin 4) (Fin 4) (BinaryGaloisField 1)) 0 1)) h
      simp [lemma114_suzukiZeroRootGenerator, SuzukiRootGL,
        SuzukiRootMatrix] at h01
    · intro h
      have h02 := congrArg
        (fun A : SuzukiMatrixGroup 0 =>
          (((A : GL (Fin 4) (BinaryGaloisField 1)) :
            Matrix (Fin 4) (Fin 4) (BinaryGaloisField 1)) 0 2)) h
      simp [lemma114_suzukiZeroRootGenerator, SuzukiRootGL,
        SuzukiRootMatrix, Matrix.mul_apply, Fin.sum_univ_four, pow_two] at h02
    · intro h
      have h01 := congrArg
        (fun A : SuzukiMatrixGroup 0 =>
          (((A : GL (Fin 4) (BinaryGaloisField 1)) :
            Matrix (Fin 4) (Fin 4) (BinaryGaloisField 1)) 0 1)) h
      simp [lemma114_suzukiZeroRootGenerator, SuzukiRootGL,
        SuzukiRootMatrix, Matrix.mul_apply, Fin.sum_univ_four, pow_succ,
        lemma114_binaryGaloisFieldOne_one_add_one] at h01

private noncomputable def lemma114_suzukiZeroRootSubgroup :
    Subgroup (SuzukiMatrixGroup 0) :=
  (Subgroup.closure
    {A | ∃ a b : BinaryGaloisField 1, A = SuzukiRootGL 0 a b}).comap
      (SuzukiMatrixGroup 0).subtype

private theorem lemma114_suzukiZeroRootSubgroup_eq_zpowers :
    lemma114_suzukiZeroRootSubgroup =
      Subgroup.zpowers lemma114_suzukiZeroRootGenerator := by
  let K := BinaryGaloisField 1
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 1
  have hpi : ∀ x : K, pi x = x ^ 2 := by
    intro x
    simpa [pi] using iterateFrobeniusEquiv_def K 2 1 x
  have hpiSq : ∀ x : K, pi (pi x) = x ^ 2 := by
    exact binaryGaloisField_tits_formula_sq 0 pi (by
      intro x
      simpa using hpi x)
  have hzle : Subgroup.zpowers lemma114_suzukiZeroRootGenerator ≤
      lemma114_suzukiZeroRootSubgroup := by
    apply Subgroup.zpowers_le.mpr
    change SuzukiRootGL 0 1 0 ∈ Subgroup.closure
      {A | ∃ a b : BinaryGaloisField 1, A = SuzukiRootGL 0 a b}
    exact Subgroup.subset_closure ⟨1, 0, rfl⟩
  let toF : K × K → lemma114_suzukiZeroRootSubgroup := fun z =>
    ⟨⟨SuzukiRootGL 0 z.1 z.2,
      Subgroup.subset_closure (Or.inl ⟨z.1, z.2, rfl⟩)⟩,
      Subgroup.subset_closure ⟨z.1, z.2, rfl⟩⟩
  have htoF : Function.Surjective toF := by
    intro x
    have hx : (x : GL (Fin 4) K) ∈ Subgroup.closure
        {A | ∃ a b : K, A = SuzukiRootGL 0 a b} := x.property
    rcases (suzukiRootGL_mem_closure_iff 0 pi hpiSq hpi
      (x : GL (Fin 4) K)).mp hx with ⟨a, b, hab⟩
    refine ⟨(a, b), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hab.symm
  have hKcard : Nat.card K = 2 := by
    simpa [K, BinaryGaloisField] using GaloisField.card 2 1 (by norm_num)
  have hFcard : Nat.card lemma114_suzukiZeroRootSubgroup ≤ 4 := by
    calc
      Nat.card lemma114_suzukiZeroRootSubgroup ≤ Nat.card (K × K) :=
        Nat.card_le_card_of_surjective toF htoF
      _ = 4 := by simp [Nat.card_prod, hKcard]
  have hzcard :
      Nat.card (Subgroup.zpowers lemma114_suzukiZeroRootGenerator) = 4 := by
    rw [Nat.card_zpowers, lemma114_suzukiZeroRootGenerator_order]
  exact (Subgroup.eq_of_le_of_card_ge hzle
    (by simpa [hzcard] using hFcard)).symm

private theorem lemma114_suzukiZeroRootSubgroup_card :
    Nat.card lemma114_suzukiZeroRootSubgroup = 4 := by
  rw [lemma114_suzukiZeroRootSubgroup_eq_zpowers, Nat.card_zpowers,
    lemma114_suzukiZeroRootGenerator_order]

private noncomputable def lemma114_suzukiZeroCentralInvolution :
    SuzukiMatrixGroup 0 :=
  ⟨SuzukiRootGL 0 0 1,
    Subgroup.subset_closure (Or.inl ⟨0, 1, rfl⟩)⟩

private noncomputable def lemma114_suzukiZeroWeyl :
    SuzukiMatrixGroup 0 :=
  ⟨SuzukiWeylGL 0,
    Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩

set_option maxHeartbeats 1200000 in
private theorem lemma114_suzukiZero_standard_pair_order :
    orderOf
      (lemma114_suzukiZeroCentralInvolution * lemma114_suzukiZeroWeyl) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime_iff.mpr
  constructor
  · apply Subtype.ext
    change
      (SuzukiRootGL 0 0 1 * SuzukiWeylGL 0) ^ 5 =
        (1 : GL (Fin 4) (BinaryGaloisField 1))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SuzukiRootGL, SuzukiRootMatrix, SuzukiWeylGL,
        SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four, pow_succ,
        lemma114_binaryGaloisFieldOne_one_add_one]
  · intro hpair
    have hGL :
        SuzukiRootGL 0 0 1 * SuzukiWeylGL 0 =
          (1 : GL (Fin 4) (BinaryGaloisField 1)) := by
      simpa [lemma114_suzukiZeroCentralInvolution,
        lemma114_suzukiZeroWeyl] using congrArg Subtype.val hpair
    have h03 := congrArg
      (fun A : GL (Fin 4) (BinaryGaloisField 1) =>
        ((A : Matrix (Fin 4) (Fin 4) (BinaryGaloisField 1)) 0 3)) hGL
    have h10 : (1 : BinaryGaloisField 1) = 0 := by
      simp [SuzukiRootGL, SuzukiRootMatrix, SuzukiWeylGL,
        SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four] at h03
    exact one_ne_zero h10

/-- The degenerate concrete Suzuki group over `GF(2)` has order twenty. -/
public theorem lemma114_suzukiZero_card :
    Nat.card (SuzukiMatrixGroup 0) = 20 := by
  let K := BinaryGaloisField 1
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 1
  have hpi : ∀ x : K, pi x = x ^ 2 := by
    intro x
    simpa [pi] using iterateFrobeniusEquiv_def K 2 1 x
  have hpiSq : ∀ x : K, pi (pi x) = x ^ 2 := by
    exact binaryGaloisField_tits_formula_sq 0 pi (by
      intro x
      simpa using hpi x)
  let F : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL 0 a b}
  let H : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL 0 u}
  let B : Subgroup (GL (Fin 4) K) := F ⊔ H
  have hFleG : F ≤ SuzukiMatrixGroup 0 := by
    dsimp only [F]
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inl hA)
  have hHbot : H = ⊥ := by
    apply bot_unique
    intro A hA
    rw [Subgroup.mem_bot]
    rcases (suzukiTorusGL_mem_closure_iff 0 A).mp hA with ⟨u, hu⟩
    have huOne : u = 1 := by
      apply Units.ext
      rcases lemma114_binaryGaloisFieldOne_eq_zero_or_one (u : K) with
        hu0 | hu1
      · exact (u.ne_zero hu0).elim
      · simpa using hu1
    calc
      A = SuzukiTorusGL 0 u := hu
      _ = SuzukiTorusGL 0 1 := by rw [huOne]
      _ = 1 := suzukiTorusGL_one 0
  have hB : B = F := by
    dsimp only [B]
    rw [hHbot, sup_bot_eq]
  let toG : Sum lemma114_suzukiZeroRootSubgroup
      (lemma114_suzukiZeroRootSubgroup ×
        lemma114_suzukiZeroRootSubgroup) → SuzukiMatrixGroup 0
    | Sum.inl r => r
    | Sum.inr z =>
        (z.1 : SuzukiMatrixGroup 0) * lemma114_suzukiZeroWeyl * z.2
  have htoG : Function.Surjective toG := by
    intro g
    rcases suzukiMatrixGroup_bruhat_decomposition 0 pi hpiSq hpi
        (g : GL (Fin 4) K) g.property with
      hgB | ⟨b, f, hbB, hfF, hgbf⟩
    · have hgF : (g : GL (Fin 4) K) ∈ F := by
        rw [← hB]
        exact hgB
      let r : lemma114_suzukiZeroRootSubgroup := ⟨g, hgF⟩
      exact ⟨Sum.inl r, rfl⟩
    · have hbF : b ∈ F := by
        rw [← hB]
        exact hbB
      let rb : lemma114_suzukiZeroRootSubgroup :=
        ⟨⟨b, hFleG hbF⟩, hbF⟩
      let rf : lemma114_suzukiZeroRootSubgroup :=
        ⟨⟨f, hFleG hfF⟩, hfF⟩
      refine ⟨Sum.inr (rb, rf), ?_⟩
      apply Subtype.ext
      simpa [toG, rb, rf, lemma114_suzukiZeroWeyl, K] using hgbf.symm
  have hupper : Nat.card (SuzukiMatrixGroup 0) ≤ 20 := by
    calc
      Nat.card (SuzukiMatrixGroup 0) ≤
          Nat.card (Sum lemma114_suzukiZeroRootSubgroup
            (lemma114_suzukiZeroRootSubgroup ×
              lemma114_suzukiZeroRootSubgroup)) :=
        Nat.card_le_card_of_surjective toG htoG
      _ = 20 := by simp [Nat.card_sum, Nat.card_prod,
        lemma114_suzukiZeroRootSubgroup_card]
  have hfour : 4 ∣ Nat.card (SuzukiMatrixGroup 0) := by
    simpa [lemma114_suzukiZeroRootGenerator_order] using
      orderOf_dvd_natCard lemma114_suzukiZeroRootGenerator
  have hfive : 5 ∣ Nat.card (SuzukiMatrixGroup 0) := by
    simpa [lemma114_suzukiZero_standard_pair_order] using
      orderOf_dvd_natCard
        (lemma114_suzukiZeroCentralInvolution * lemma114_suzukiZeroWeyl)
  have htwenty : 20 ∣ Nat.card (SuzukiMatrixGroup 0) := by
    simpa using
      (by norm_num : Nat.Coprime 4 5).mul_dvd_of_dvd_of_dvd hfour hfive
  have hlower : 20 ≤ Nat.card (SuzukiMatrixGroup 0) :=
    Nat.le_of_dvd Nat.card_pos htwenty
  omega

private theorem lemma114_suzukiZeroRootSubgroup_involution_eq_square
    {x : SuzukiMatrixGroup 0}
    (hxR : x ∈ lemma114_suzukiZeroRootSubgroup)
    (hx : IsInvolution x) :
    x = lemma114_suzukiZeroRootGenerator ^ 2 := by
  classical
  have hxmem : x ∈ Subgroup.zpowers lemma114_suzukiZeroRootGenerator := by
    rw [← lemma114_suzukiZeroRootSubgroup_eq_zpowers]
    exact hxR
  rw [mem_zpowers_iff_mem_range_orderOf,
    lemma114_suzukiZeroRootGenerator_order] at hxmem
  rcases Finset.mem_image.mp hxmem with ⟨n, hn, hnx⟩
  have hnlt : n < 4 := Finset.mem_range.mp hn
  have hxorder : orderOf x = 2 :=
    orderOf_eq_prime hx.sq_eq_one hx.ne_one
  interval_cases n
  · have hxone : x = 1 := by simpa using hnx.symm
    exact (hx.ne_one hxone).elim
  · have hbad : (4 : ℕ) = 2 := by
      calc
        4 = orderOf lemma114_suzukiZeroRootGenerator :=
          lemma114_suzukiZeroRootGenerator_order.symm
        _ = orderOf x := congrArg orderOf (by simpa using hnx)
        _ = 2 := hxorder
    omega
  · exact hnx.symm
  · have hpowOrder :
        orderOf (lemma114_suzukiZeroRootGenerator ^ 3) = 4 := by
      rw [orderOf_pow, lemma114_suzukiZeroRootGenerator_order]
      norm_num
    have hbad : (4 : ℕ) = 2 := by
      calc
        4 = orderOf (lemma114_suzukiZeroRootGenerator ^ 3) :=
          hpowOrder.symm
        _ = orderOf x := congrArg orderOf hnx
        _ = 2 := hxorder
    omega

private theorem lemma114_isPGroup_zpowers_of_involution
    {G : Type u} [Group G] [Finite G] {x : G} (hx : IsInvolution x) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  have horder : orderOf x = 2 := orderOf_eq_prime hx.sq_eq_one hx.ne_one
  apply IsPGroup.of_card (p := 2) (G := Subgroup.zpowers x) (n := 1)
  rw [Nat.card_zpowers, horder, pow_one]

private theorem lemma114_commuting_involutions_eq_of_sylow_unique
    {G : Type u} [Group G] [Finite G]
    (Q : Sylow 2 G)
    (hunique : ∀ x y : Q, IsInvolution x → IsInvolution y → x = y)
    {u v : G} (hu : IsInvolution u) (hv : IsInvolution v)
    (huv : Commute u v) : u = v := by
  have huP : IsPGroup 2 (Subgroup.zpowers u) :=
    lemma114_isPGroup_zpowers_of_involution hu
  have hvP : IsPGroup 2 (Subgroup.zpowers v) :=
    lemma114_isPGroup_zpowers_of_involution hv
  have hnorm : Subgroup.zpowers u ≤ Subgroup.normalizer (Subgroup.zpowers v) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor <;> intro hy
    · rcases hx with ⟨m, rfl⟩
      rcases hy with ⟨n, rfl⟩
      exact ⟨n, by rw [huv.zpow_zpow m n, mul_inv_cancel_right]⟩
    · rcases hx with ⟨m, rfl⟩
      rcases hy with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      change v ^ n = u ^ m * y * (u ^ m)⁻¹ at hn
      have hcomm := huv.zpow_zpow m n
      calc
        v ^ n = (u ^ m)⁻¹ * (u ^ m * v ^ n) := by group
        _ = (u ^ m)⁻¹ * (v ^ n * u ^ m) := by rw [hcomm.eq]
        _ = (u ^ m)⁻¹ * ((u ^ m * y * (u ^ m)⁻¹) * u ^ m) := by
          rw [hn]
        _ = y := by group
  have hsupP : IsPGroup 2
      (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' huP hvP hnorm
  obtain ⟨S, hsup_le_S⟩ := hsupP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  have huS : u ∈ (S : Subgroup G) :=
    hsup_le_S ((le_sup_left :
      Subgroup.zpowers u ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v)
        (Subgroup.mem_zpowers u))
  have hvS : v ∈ (S : Subgroup G) :=
    hsup_le_S ((le_sup_right :
      Subgroup.zpowers v ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v)
        (Subgroup.mem_zpowers v))
  have hcoe : ((g • S : Sylow 2 G) : Subgroup G) = (Q : Subgroup G) :=
    congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hg
  let ug : Q := ⟨g * u * g⁻¹, by
    have hmem : g * u * g⁻¹ ∈ ((g • S : Sylow 2 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Set.mem_smul_set.mpr ⟨u, huS, rfl⟩
    change g * u * g⁻¹ ∈ (Q : Subgroup G)
    simpa [hcoe] using hmem⟩
  let vg : Q := ⟨g * v * g⁻¹, by
    have hmem : g * v * g⁻¹ ∈ ((g • S : Sylow 2 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Set.mem_smul_set.mpr ⟨v, hvS, rfl⟩
    change g * v * g⁻¹ ∈ (Q : Subgroup G)
    simpa [hcoe] using hmem⟩
  have hugAmbient : IsInvolution (g * u * g⁻¹) := by
    simpa [rightConjugateElem] using
      isInvolution_rightConjugateElem (g := g⁻¹) hu
  have hvgAmbient : IsInvolution (g * v * g⁻¹) := by
    simpa [rightConjugateElem] using
      isInvolution_rightConjugateElem (g := g⁻¹) hv
  have hug : IsInvolution ug := by
    constructor
    · intro h
      apply hugAmbient.ne_one
      simpa [ug] using congrArg Subtype.val h
    · apply Subtype.ext
      simpa [ug] using hugAmbient.sq_eq_one
  have hvg : IsInvolution vg := by
    constructor
    · intro h
      apply hvgAmbient.ne_one
      simpa [vg] using congrArg Subtype.val h
    · apply Subtype.ext
      simpa [vg] using hvgAmbient.sq_eq_one
  have heq : ug = vg := hunique ug vg hug hvg
  have hcoe' : g * u * g⁻¹ = g * v * g⁻¹ := congrArg Subtype.val heq
  simpa using (mul_left_cancel (mul_right_cancel hcoe'))

private theorem lemma114_suzukiZero_involution_product_order
    {s t : SuzukiMatrixGroup 0}
    (hs : IsInvolution s) (ht : IsInvolution t) (hst : s ≠ t) :
    orderOf (s * t) = 5 := by
  have hRcard : Nat.card lemma114_suzukiZeroRootSubgroup = 4 :=
    lemma114_suzukiZeroRootSubgroup_card
  have hRp : IsPGroup 2 lemma114_suzukiZeroRootSubgroup := by
    apply IsPGroup.of_card
      (p := 2) (G := lemma114_suzukiZeroRootSubgroup) (n := 2)
    simpa using hRcard
  have hRindex : lemma114_suzukiZeroRootSubgroup.index = 5 := by
    have hmul := lemma114_suzukiZeroRootSubgroup.card_mul_index
    rw [hRcard, lemma114_suzukiZero_card] at hmul
    omega
  have hRindexOdd : ¬ 2 ∣ lemma114_suzukiZeroRootSubgroup.index := by
    rw [hRindex]
    norm_num
  let Q : Sylow 2 (SuzukiMatrixGroup 0) :=
    IsPGroup.toSylow hRp hRindexOdd
  have hQ : (Q : Subgroup (SuzukiMatrixGroup 0)) =
      lemma114_suzukiZeroRootSubgroup := by
    dsimp only [Q]
    exact IsPGroup.toSylow_coe hRp hRindexOdd
  have hunique : ∀ x y : Q,
      IsInvolution x → IsInvolution y → x = y := by
    intro x y hx hy
    have hxAmbient : IsInvolution (x : SuzukiMatrixGroup 0) :=
      IsInvolution.map_of_injective hx
        (Q : Subgroup (SuzukiMatrixGroup 0)).subtype
        (Q : Subgroup (SuzukiMatrixGroup 0)).subtype_injective
    have hyAmbient : IsInvolution (y : SuzukiMatrixGroup 0) :=
      IsInvolution.map_of_injective hy
        (Q : Subgroup (SuzukiMatrixGroup 0)).subtype
        (Q : Subgroup (SuzukiMatrixGroup 0)).subtype_injective
    have hxR : (x : SuzukiMatrixGroup 0) ∈
        lemma114_suzukiZeroRootSubgroup := by
      rw [← hQ]
      exact x.property
    have hyR : (y : SuzukiMatrixGroup 0) ∈
        lemma114_suzukiZeroRootSubgroup := by
      rw [← hQ]
      exact y.property
    apply Subtype.ext
    exact
      (lemma114_suzukiZeroRootSubgroup_involution_eq_square hxR hxAmbient).trans
        (lemma114_suzukiZeroRootSubgroup_involution_eq_square hyR hyAmbient).symm
  have hprod_ne : s * t ≠ 1 := by
    intro hprod
    apply hst
    calc
      s = s * 1 := by simp
      _ = s * (s * t) := by rw [hprod]
      _ = t := by
        rw [← mul_assoc]
        have hss : s * s = 1 := by simpa [pow_two] using hs.sq_eq_one
        rw [hss, one_mul]
  have hnotEven : ¬ Even (orderOf (s * t)) := by
    intro heven
    rcases heven with ⟨m, hm⟩
    have horder : orderOf (s * t) = 2 * m := by
      simpa [two_mul] using hm
    obtain ⟨hw, hws, hwt⟩ :=
      External.Suzuki.V.suzuki_ch5_proposition_1_2_iii
        hs ht hst horder
    have hwsEq : (s * t) ^ m = s :=
      lemma114_commuting_involutions_eq_of_sylow_unique Q hunique hw hs hws
    have hwtEq : (s * t) ^ m = t :=
      lemma114_commuting_involutions_eq_of_sylow_unique Q hunique hw ht hwt
    exact hst (hwsEq.symm.trans hwtEq)
  have hodd : Odd (orderOf (s * t)) := Nat.not_even_iff_odd.mp hnotEven
  have hdivTwenty : orderOf (s * t) ∣ 20 := by
    simpa [lemma114_suzukiZero_card] using orderOf_dvd_natCard (s * t)
  have hdivFive : orderOf (s * t) ∣ 5 := by
    have hcop : Nat.Coprime (orderOf (s * t)) (2 ^ 2) :=
      hodd.coprime_two_right.pow_right 2
    apply hcop.dvd_of_dvd_mul_left
    simpa using hdivTwenty
  have horder_ne_one : orderOf (s * t) ≠ 1 := by
    intro horder
    exact hprod_ne (orderOf_eq_one_iff.mp horder)
  exact ((Nat.dvd_prime Nat.prime_five).mp hdivFive).resolve_left
    horder_ne_one

/-- Distinct involutions in the involution core of `Sz(2)` have product
order five. -/
public theorem lemma114_suzukiZeroCore_involution_product_order
    {s t : involutionCore (SuzukiMatrixGroup 0)}
    (hs : IsInvolution s) (ht : IsInvolution t) (hst : s ≠ t) :
    orderOf (s * t) = 5 := by
  have hsAmbient : IsInvolution (s : SuzukiMatrixGroup 0) :=
    IsInvolution.map_of_injective hs
      (involutionCore (SuzukiMatrixGroup 0)).subtype
      (involutionCore (SuzukiMatrixGroup 0)).subtype_injective
  have htAmbient : IsInvolution (t : SuzukiMatrixGroup 0) :=
    IsInvolution.map_of_injective ht
      (involutionCore (SuzukiMatrixGroup 0)).subtype
      (involutionCore (SuzukiMatrixGroup 0)).subtype_injective
  have hstAmbient : (s : SuzukiMatrixGroup 0) ≠ t := by
    intro h
    exact hst (Subtype.ext h)
  have horder :=
    lemma114_suzukiZero_involution_product_order
      hsAmbient htAmbient hstAmbient
  calc
    orderOf (s * t) =
        orderOf (((s * t : involutionCore (SuzukiMatrixGroup 0)) :
          SuzukiMatrixGroup 0)) :=
      (Subgroup.orderOf_coe (s * t)).symm
    _ = orderOf ((s : SuzukiMatrixGroup 0) *
        (t : SuzukiMatrixGroup 0)) := by rfl
    _ = 5 := horder

end CFSG.BenderSuzuki
