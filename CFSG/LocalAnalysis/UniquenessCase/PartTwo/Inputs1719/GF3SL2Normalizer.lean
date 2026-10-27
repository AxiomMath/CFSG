module

public import CFSG.GH74.GLS.LU.Local.SL2Sylow
public import CFSG.ClassicalInvolution.AschTight.S19COrd

public section

open scoped MatrixGroups commutatorElement
open Subgroup

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF3

open CFSG.Semidihedral.OddFieldSL2 CFSG.GH74.GLS.LU.Local.SL2

variable {F : Type} [Field F] [Finite F]

theorem card_sylow_two_sl2 (hF : Nat.card F % 8 = 3) (P : Sylow 2 SL(2, F)) :
    Nat.card P = 8 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card F) := by
    rw [Nat.odd_iff]
    omega
  have hq16 : Nat.card F % 16 = 3 ∨ Nat.card F % 16 = 11 := by omega
  have hq2' : (Nat.card F ^ 2 - 1) % 16 = 8 := by
    have hq2 : Nat.card F ^ 2 % 16 = 9 := by
      rcases hq16 with h | h <;> rw [Nat.pow_mod, h] <;> norm_num
    obtain ⟨k, hk⟩ : ∃ k, Nat.card F ^ 2 = 16 * k + 9 :=
      ⟨Nat.card F ^ 2 / 16, by have := Nat.div_add_mod (Nat.card F ^ 2) 16; omega⟩
    have hk' : Nat.card F ^ 2 - 1 = 16 * k + 8 := by omega
    rw [hk', Nat.mul_add_mod]
  have hne : Nat.card F ^ 2 - 1 ≠ 0 := by
    have h1 : 1 < Nat.card F := by omega
    have h2 : 1 < Nat.card F ^ 2 := by nlinarith
    omega
  have hfac : (Nat.card F ^ 2 - 1).factorization 2 = 3 := by
    refine le_antisymm ?_ ?_
    · by_contra h
      have h4 : 4 ≤ (Nat.card F ^ 2 - 1).factorization 2 := by omega
      have h16 : 16 ∣ Nat.card F ^ 2 - 1 := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
        exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mpr h4
      have h0 := Nat.mod_eq_zero_of_dvd h16
      rw [hq2'] at h0
      norm_num at h0
    · have h8 : 8 ∣ Nat.card F ^ 2 - 1 :=
        CFSG.ClassicalInvolution.Disconnected.AschTight.S19C.eight_dvd_sq_sub_one hodd
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp (by simpa using h8)
  have hfac2 : (Nat.card F * (Nat.card F ^ 2 - 1)).factorization 2 = 3 := by
    rw [CFSG.ClassicalInvolution.Disconnected.AschTight.S19C.factorization_two_mul_sq_sub_one hodd,
      hfac]
  calc Nat.card P = 2 ^ (Nat.card SL(2, F)).factorization 2 := Sylow.card_eq_multiplicity P
    _ = 2 ^ 3 := by
      rw [CFSG.ClassicalInvolution.Disconnected.AschTight.S19C.card_sl2 F, hfac2]
    _ = 8 := by norm_num

theorem card_normalizer_sylow_two_sl2 (hF : Nat.card F % 8 = 3) (P : Sylow 2 SL(2, F)) :
    Nat.card (normalizer ((P : Subgroup SL(2, F)) : Set SL(2, F))) = 24 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card F) := by
    rw [Nat.odd_iff]
    omega
  set Psub : Subgroup SL(2, F) := (P : Subgroup SL(2, F)) with hPsub
  have hPcard : Nat.card Psub = 8 := card_sylow_two_sl2 hF P
  obtain ⟨f, hf⟩ := exists_quaternion_embedding_in_sylow F hodd P
  have hbij : Function.Bijective f := by
    rw [Nat.bijective_iff_injective_and_card (f : QuaternionGroup 2 → ↥P)]
    refine ⟨hf, ?_⟩
    rw [show Nat.card (QuaternionGroup 2) = 8 by
      rw [Nat.card_eq_fintype_card, QuaternionGroup.card], card_sylow_two_sl2 hF P]
  let φ : ↥Psub ≃* QuaternionGroup 2 := (MulEquiv.ofBijective f hbij).symm
  have hker : Nat.card ↥(Psub.normalizerMonoidHom.ker) ≤ 2 :=
    ker_normalizerMonoidHom_card_le hodd P
  have hAut : Nat.card (MulAut ↥Psub) ≤ 24 := by
    rw [Nat.card_congr (MulAut.congr φ).toEquiv]
    exact card_mulAut_q8_le
  have hrange : Nat.card ↥(Psub.normalizerMonoidHom.range) ≤ 24 :=
    (Subgroup.card_le_card_group (H := Psub.normalizerMonoidHom.range)).trans hAut
  change Nat.card (normalizer (Psub : Set SL(2, F))) = 24
  set N : Subgroup SL(2, F) := normalizer (Psub : Set SL(2, F)) with hN
  have hprod : Nat.card ↥(Psub.normalizerMonoidHom.ker) *
      Nat.card ↥(Psub.normalizerMonoidHom.range) = Nat.card N := by
    rw [hN, ← Subgroup.card_mul_index Psub.normalizerMonoidHom.ker, Subgroup.index_ker]
  have hNle : Nat.card N ≤ 48 := by
    rw [← hprod]
    exact (Nat.mul_le_mul hker hrange).trans (by norm_num)
  have h8 : 8 ∣ Nat.card N := by
    rw [hN]
    have h := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := Psub))
    rwa [hPcard] at h
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card F hodd
  have h3 : 3 ∣ Nat.card N := by
    obtain ⟨g, hgN, hgord⟩ := q8_normalizer h2 P φ
    have h := Subgroup.orderOf_dvd_natCard N (by rwa [hN])
    rwa [hgord] at h
  have h24 : 24 ∣ Nat.card N :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8 h3
  have hPN : Psub ≤ N := by
    rw [hN]
    exact Subgroup.le_normalizer
  have hrel : Psub.relIndex N ∣ Psub.index := Subgroup.relIndex_dvd_index_of_le hPN
  have hrelnd : ¬ 2 ∣ Psub.relIndex N := fun h => P.not_dvd_index (h.trans hrel)
  obtain ⟨c, hc⟩ := h24
  have hc2 : c ≤ 2 := by
    rw [hc] at hNle
    have := Nat.card_pos (α := ↥N)
    omega
  have hcpos : 0 < c := by
    rw [hc] at hNle
    have := Nat.card_pos (α := ↥N)
    omega
  interval_cases c
  · simpa using hc
  · exfalso
    have hrel6 : Psub.relIndex N = 6 := by
      have h := Subgroup.relIndex_mul_card (H := Psub) (K := N)
      rw [inf_eq_left.mpr hPN, hc, hPcard] at h
      omega
    exact hrelnd (by rw [hrel6]; norm_num)

theorem sl2_mod_eight_three_facts {Y : Type} [Group Y] [Finite Y] {K Q : Subgroup Y}
    {F : Type} [Field F] [Finite F] (hF : Nat.card F % 8 = 3) (e : ↥K ≃* SL(2, F))
    (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q K) :
    (∀ x ∈ K ⊓ normalizer (Q : Set Y), x ^ 3 ∈ Q) ∧
    (∀ x ∈ K ⊓ normalizer (Q : Set Y), ∀ y ∈ K ⊓ normalizer (Q : Set Y),
      x * y * x⁻¹ * y⁻¹ ∈ Q) ∧
    (∃ a ∈ K ⊓ normalizer (Q : Set Y), orderOf a = 3) ∧
    (∀ c ∈ K, (∀ y ∈ K, c * y = y * c) → c * c = 1) ∧
    ¬ IsMulCommutative ↥K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card F) := by
    rw [Nat.odd_iff]
    omega
  have hQle : Q ≤ K := hQ.le
  let Qk : Subgroup ↥K := Q.subgroupOf K
  have hQkcard : Nat.card Qk = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv
  let Qe : Subgroup SL(2, F) := Qk.map e.toMonoidHom
  have hQecard : Nat.card Qe = Nat.card Qk := Subgroup.card_map_of_injective e.injective
  have hKcard : Nat.card ↥K = Nat.card SL(2, F) := Nat.card_congr e.toEquiv
  have hQe2 : Nat.card Qe = 2 ^ (Nat.card SL(2, F)).factorization 2 := by
    rw [hQecard, hQkcard, hQ.card_eq, hKcard]
  let P : Sylow 2 SL(2, F) := Sylow.ofCard Qe hQe2
  have hPcoe : (P : Subgroup SL(2, F)) = Qe := Sylow.coe_ofCard Qe hQe2
  have hPcard : Nat.card (P : Subgroup SL(2, F)) = 8 := card_sylow_two_sl2 hF P
  have hQcard : Nat.card Q = 8 := by
    rw [← hQkcard, ← hQecard, ← hPcoe, hPcard]
  let NK : Subgroup Y := K ⊓ normalizer (Q : Set Y)
  have hNKcard1 : Nat.card NK = Nat.card ((normalizer (Q : Set Y)).subgroupOf K) := by
    have hsub : NK.subgroupOf K = (normalizer (Q : Set Y)).subgroupOf K :=
      Subgroup.inf_subgroupOf_left (normalizer (Q : Set Y)) K
    rw [← hsub]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (K := K) (H := NK)
      (by intro x hx; exact hx.1))).symm
  have hNKcard : Nat.card NK = 24 := by
    rw [hNKcard1, Subgroup.subgroupOf_normalizer_eq hQle]
    have hmap : Nat.card (normalizer (Qk : Set ↥K)) =
        Nat.card ((normalizer (Qk : Set ↥K)).map e.toMonoidHom) :=
      Nat.card_congr (MulEquiv.subgroupMap e (normalizer (Qk : Set ↥K))).toEquiv
    rw [hmap, Subgroup.map_equiv_normalizer_eq]
    change Nat.card (normalizer (Qe : Set SL(2, F))) = 24
    rw [← hPcoe]
    exact card_normalizer_sylow_two_sl2 hF P
  have hQNK : Q ≤ NK := fun x hx => ⟨hQle hx, Subgroup.le_normalizer hx⟩
  let L : Subgroup ↥NK := Q.subgroupOf NK
  have hLcard : Nat.card L = 8 := by
    change Nat.card (Q.subgroupOf NK) = 8
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQNK).toEquiv, hQcard]
  have hLnorm : L.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := NK) (N := Q) inf_le_right
  have : L.Normal := hLnorm
  have hLidx : L.index = 3 := by
    have h := L.index_mul_card
    rw [hLcard, hNKcard] at h
    omega
  have hquot : Nat.card (↥NK ⧸ L) = 3 := by
    rw [← Subgroup.index_eq_card, hLidx]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    let g : ↥NK := ⟨x, hx⟩
    have hmem : g ^ 3 ∈ L := by
      have h := Subgroup.pow_index_mem L g
      rwa [hLidx] at h
    simpa [g] using Subgroup.mem_subgroupOf.mp hmem
  · intro x hx y hy
    let g : ↥NK := ⟨x, hx⟩
    let h : ↥NK := ⟨y, hy⟩
    have hcomm : IsMulCommutative (↥NK ⧸ L) := by
      have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      have : IsCyclic (↥NK ⧸ L) := isCyclic_of_prime_card hquot
      exact IsMulCommutative.of_comm fun a b =>
        (IsCyclic.commGroup (α := ↥NK ⧸ L)).mul_comm a b
    have hle : commutator ↥NK ≤ L :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
    have hmem : ⁅g, h⁆ ∈ commutator ↥NK := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤)
        (Subgroup.mem_top g) (Subgroup.mem_top h)
    have hmemL : ⁅g, h⁆ ∈ L := hle hmem
    simpa [L, g, h, commutatorElement_def] using Subgroup.mem_subgroupOf.mp hmemL
  · have h3 : 3 ∣ Nat.card ↥NK := by
      rw [hNKcard]
      norm_num
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 h3
    exact ⟨(a : Y), a.2, by simpa [Subgroup.orderOf_coe] using ha⟩
  · intro c hc hcent
    let g : ↥K := ⟨c, hc⟩
    have hcentK : g ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      exact (hcent w.1 w.2).symm
    have hmem : e g ∈ Subgroup.center SL(2, F) := by
      rw [← Subgroup.map_center_eq e]
      exact ⟨g, hcentK, rfl⟩
    have hsq : g * g = 1 := by
      rcases eq_one_or_minus_of_mem_center hmem with h | h
      · have hg : g = 1 := e.injective (by rw [h, map_one])
        rw [hg]
        simp
      · have hg : g = e.symm (minusIdentity F) := by
          simpa using congrArg e.symm h
        rw [hg]
        apply e.injective
        rw [map_mul, e.apply_symm_apply]
        simpa [pow_two] using minusIdentity_square F
    simpa [g] using congrArg (fun z : ↥K => (z : Y)) hsq
  · intro hK
    have hSL : ¬ IsMulCommutative SL(2, F) := by
      intro hSL'
      have := hSL'
      exact sylow_two_not_isMulCommutative F hodd P inferInstance
    refine hSL (IsMulCommutative.of_comm fun x y => ?_)
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    have := hK
    simpa [map_mul] using congrArg e ((IsMulCommutative.is_comm (M := ↥K)).comm a b)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF3
