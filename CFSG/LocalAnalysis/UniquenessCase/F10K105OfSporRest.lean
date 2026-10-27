module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporRest
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporOut
import CFSG.LocalAnalysis.UniquenessCase.UC22S216J1Hall
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallKGJ1
import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.OutNoOdd
import CFSG.ClassicalInvolution.Q3.Q3TLTShapeAb
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open Subgroup CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Pointwise

section Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem k105r_mem_of_inner {L : Subgroup G} [L.Normal]
    (hC : centralizer (L : Set G) ≤ L) {g : G}
    (h : MulAut.conjNormal g ∈ (MulAut.conj : ↥L →* MulAut ↥L).range) : g ∈ L := by
  obtain ⟨x, hx⟩ := h
  have hc : (x : G)⁻¹ * g ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    have h1 := congrArg (fun σ : MulAut ↥L => ((σ ⟨l, hl⟩ : ↥L) : G)) hx
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, coe_mul, coe_inv] at h1
    calc l * ((x : G)⁻¹ * g) = (x : G)⁻¹ * (x * l * (x : G)⁻¹) * g := by group
      _ = (x : G)⁻¹ * (g * l * g⁻¹) * g := by rw [h1]
      _ = (x : G)⁻¹ * g * l := by group
  have h2 : (x : G) * ((x : G)⁻¹ * g) ∈ L := L.mul_mem x.2 (hC hc)
  simpa using h2

omit [Finite G] in
private theorem k105r_le_of_odd {L B : Subgroup G} [L.Normal] (hC : centralizer (L : Set G) ≤ L)
    (hinn : ∀ σ : MulAut ↥L, Odd (orderOf σ) → σ ∈ (MulAut.conj : ↥L →* MulAut ↥L).range)
    (hBo : Odd (Nat.card ↥B)) : B ≤ L := by
  intro b hb
  refine k105r_mem_of_inner hC (hinn _ ?_)
  exact Odd.of_dvd_nat (Odd.of_dvd_nat hBo (Subgroup.orderOf_dvd_natCard B hb))
    (orderOf_map_dvd _ b)

private theorem k105r_isPGroup_three {L T B : Subgroup G} [L.Normal] (hK : K105Spor)
    {s : TauCeti.SporadicName} (hs : s ≠ .J1) (hL : IsSpor ↥L s)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hBab : IsMulCommutative ↥B)
    (hBo : Odd (Nat.card ↥B)) (hBT : Permutes B T) (hBL : B ≤ L) : IsPGroup 3 ↥B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ L) L :=
    hT.inf_of_le_normalizer le_top (normalizer_eq_top_iff.mpr inferInstance).ge
  obtain ⟨Q, hQ⟩ := hTL.exists_sylow_eq_subgroupOf
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (Q : Subgroup ↥L) ⊤ := by
    refine ⟨le_top, Q.isPGroup', ?_⟩
    change ¬ 2 ∣ (Q : Subgroup ↥L).relIndex ⊤
    rw [relIndex_top_right]
    exact Q.not_dvd_index
  have hperm : ((B.subgroupOf L : Subgroup ↥L) : Set ↥L) * ((Q : Subgroup ↥L) : Set ↥L) =
      ((Q : Subgroup ↥L) : Set ↥L) * ((B.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    rw [hQ]
    exact CFSG.Quasithin.H23P4.mul_comm_subgroupOf hBL inf_le_right
      (CFSG.Quasithin.H23P4.mul_comm_inf_of_le hBT.symm hBL).symm
  let e : ↥(B.subgroupOf L) ≃* ↥B := subgroupOfEquivOfLe hBL
  have := hBab
  have hBn : Group.IsNilpotent ↥(B.subgroupOf L) := Group.nilpotent_of_mulEquiv e.symm
  have hBo' : Odd (Nat.card ↥(B.subgroupOf L)) := by rwa [Nat.card_congr e.toEquiv]
  exact (isPGroup_three_of_permutes_spor hK hs hL hS hBn hBo' hperm).of_equiv e

omit [Finite G] in
private theorem k105r_dvd_21 {B : Subgroup G} (hG : IsJ1 G)
    (hprime : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥B → q = 3 ∨ q = 7) : Nat.card ↥B ∣ 21 := by
  obtain ⟨eJ⟩ := hG
  have hGc : Nat.card G = 175560 := by
    rw [Nat.card_congr (eJ.trans CFSG.Walter.walterJ1EquivNative.symm).toEquiv,
      CFSG.Walter.J1Props.card_walterJ1]
  have hdvd : Nat.card ↥B ∣ 21 * 8360 := by
    rw [show 21 * 8360 = 175560 by norm_num, ← hGc]
    exact Subgroup.card_subgroup_dvd_card B
  refine Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_of_dvd fun k hk hkB hk8 => ?_) hdvd
  rcases hprime k hk hkB with rfl | rfl <;> norm_num at hk8

private theorem k105r_card_ne_21 {B : Subgroup G} (hG : IsJ1 G) (hBab : IsMulCommutative ↥B) :
    Nat.card ↥B ≠ 21 := by
  intro h21
  have := CFSG.Adapters.certificate43_holds
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨eJ⟩ := hG
  let f : G ≃* walterJ1 := eJ.trans CFSG.Walter.walterJ1EquivNative.symm
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 7 (by rw [h21]; norm_num)
  have hz : orderOf (f y) = 7 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy]
  have hP : Nat.card (zpowers (f y)) = 7 := by rw [Nat.card_zpowers, hz]
  let S : Sylow 7 walterJ1 :=
    (IsPGroup.of_card (n := 1) (by rw [hP]; norm_num) : IsPGroup 7 (zpowers (f y))).toSylow
      (CFSG.Walter.J1Props.not_dvd_index_of_card (by norm_num) hP)
  have hC : centralizer (zpowers (f y) : Set walterJ1) = zpowers (f y) :=
    CFSG.Walter.J1Props.centralizer_sylow_eq (Or.inl rfl) S
  have hle : B.map f.toMonoidHom ≤ centralizer (zpowers (f y) : Set walterJ1) := by
    rw [le_centralizer_iff, zpowers_le, mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hyb : (y : G) * b = b * y :=
      congrArg Subtype.val (hBab.is_comm.comm y ⟨b, hb⟩)
    change f b * f y = f y * f b
    rw [← map_mul, ← map_mul, hyb]
  have h := Subgroup.card_dvd_of_le hle
  rw [hC, hP, Subgroup.card_map_of_injective f.injective, h21] at h
  norm_num at h

private theorem k105r_J1 {T B : Subgroup G} (hG : IsJ1 G)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hBab : IsMulCommutative ↥B)
    (hBo : Odd (Nat.card ↥B)) (hBT : Permutes B T) : IsPGroup 3 ↥B ∨ Nat.card ↥B = 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  have := hBab
  have hprime : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥B → q = 3 ∨ q = 7 := fun _ =>
    uc22s216_prime_eq_three_or_seven_of_permutes_J1 hG hS inferInstance hBo hBT
  have hmem : Nat.card ↥B ∈ Nat.divisors 21 :=
    Nat.mem_divisors.mpr ⟨k105r_dvd_21 hG hprime, by norm_num⟩
  rw [show Nat.divisors 21 = {1, 3, 7, 21} by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact Or.inl (IsPGroup.of_card (n := 0) (by rw [h, pow_zero]))
  · exact Or.inl (IsPGroup.of_card (n := 1) (by rw [h, pow_one]))
  · exact Or.inr h
  · exact absurd h (k105r_card_ne_21 hG hBab)

theorem k105_of_k105Spor_of_outer_two_pow (hK : K105Spor)
    (hout : ∀ (S : Type) [Group S] [Finite S], CFSG.Blueprint.NativeSporadic.SporadicRep S →
      ∃ k : ℕ, Nat.card (Outer S) ∣ 2 ^ k) : K105 := by
  intro G _ _ T B hB ⟨s, hs⟩
  obtain ⟨hT, hBab, hBo, hBT, -⟩ := hB
  have := CFSG.ClassicalInvolution.Q3.genFittingFStar_isNormal (X := G)
  have hC := CFSG.ClassicalInvolution.Q3.centralizer_genFittingFStar_le (X := G)
  by_cases hsJ : s = .J1
  · subst hsJ
    have htop : genFittingFStar G = ⊤ := eq_top_iff.mpr fun g _ =>
      k105r_mem_of_inner hC
        (CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small.s1667_kg_j1_aut_mem_range hs _)
    have hG : IsJ1 G := by
      obtain ⟨e⟩ := hs
      exact ⟨((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm.trans e⟩
    exact (k105r_J1 hG hT hBab hBo hBT).imp id fun h => ⟨hG, h⟩
  · obtain ⟨k, hk⟩ := hout _ ⟨s, hs⟩
    have hBL := k105r_le_of_odd hC (fun σ hσ =>
      CFSG.EvenSporadicStandard.HSStd.InvCent.mem_range_conj_of_odd_orderOf_of_card_outer_dvd hk
        hσ) hBo
    exact Or.inl (k105r_isPGroup_three hK hsJ hs hT hBab hBo hBT hBL)

end Helpers

theorem k105_of_k105SporRest
    (h : K105SporRest) : K105 :=
  k105_of_k105Spor_of_outer_two_pow (k105Spor_of_rest h)
    CFSG.ComponentClassification.HarrisLit.T1.SporRow.sporadic_outer_two_pow

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
