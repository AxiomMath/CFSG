module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.Walter.J1Props.Extra
import CFSG.Walter.J1Props.Aut
import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic
import CFSG.GroupTheory.PermutingProducts
import CFSG.GroupTheory.SubgroupTransport
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBar

open Subgroup

variable {X : Type} [Group X] [Finite X]

theorem normal_of_card_eq_prime_mul {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    {p m : ℕ} (hp : p.Prime) (hG : Nat.card G = p * m) (hm : m < p)
    (hA : Nat.card A = p) : A.Normal := by
  have : Fact p.Prime := ⟨hp⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hG
    exact Nat.card_pos.ne' hG
  have hpdvd : ¬ p ∣ m := by
    intro hd
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hd
    omega
  have hfac : (p * m).factorization p = 1 := by
    rw [Nat.factorization_mul hp.ne_zero hm0, Finsupp.add_apply,
      Nat.Prime.factorization_self hp, Nat.factorization_eq_zero_of_not_dvd hpdvd]
  let P : Sylow p G := Sylow.ofCard A (by rw [hA, hG, hfac, pow_one])
  have hP : (P : Subgroup G) = A := Sylow.coe_ofCard A _
  have hPcard : Nat.card (P : Subgroup G) = p := by rw [hP, hA]
  have hidx : (P : Subgroup G).index = m := by
    have h := Subgroup.card_mul_index (P : Subgroup G)
    rw [hPcard, hG] at h
    exact Nat.mul_left_cancel hp.pos h
  have hdvd : Nat.card (Sylow p G) ∣ m := by
    have h := P.card_dvd_index
    rwa [hidx] at h
  have hcount : Nat.card (Sylow p G) = 1 := by
    have hmod : Nat.card (Sylow p G) % p = 1 % p := card_sylow_modEq_one p G
    have hle : Nat.card (Sylow p G) ≤ m :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd
    have hlt : Nat.card (Sylow p G) < p := by omega
    rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hp.one_lt] at hmod
    exact hmod
  let : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hcount).1
  rw [← hP]
  exact Sylow.normal_of_subsingleton P

theorem false_of_isJ1 (hX : UC22.IsJ1 X) {A U : Subgroup X}
    {r : ℕ} (hr : r.Prime) (h11 : 11 ≤ r) (hA : Nat.card A = r)
    (hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤) (hAU : UC22.Permutes A U) : False := by
  obtain ⟨e₀⟩ := hX
  let e : X ≃* CFSG.Open.walterJ1 := e₀.trans CFSG.Walter.walterJ1EquivNative.symm
  let A' : Subgroup CFSG.Open.walterJ1 := A.map e.toMonoidHom
  let U' : Subgroup CFSG.Open.walterJ1 := U.map e.toMonoidHom
  have hA' : Nat.card A' = r := by
    rw [Subgroup.card_map_of_injective e.injective, hA]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU' : CFSG.ABGLocalTools.IsSylowOf 2 U' ⊤ := by
    have h := (CFSG.GroupTheory.isSylowOf_map_mulEquiv (p := 2) e
      (P := U) (K := (⊤ : Subgroup X))).mpr hU
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at h
  have hperm' : UC22.Permutes A' U' := CFSG.GroupTheory.map_permutes_map e.toMonoidHom hAU
  have hU8 : Nat.card U' = 8 := by
    have hfac : (175560 : ℕ).factorization 2 = 3 := by
      rw [Nat.factorization_def _ Nat.prime_two]
      decide +kernel
    rw [CFSG.ABGLocalTools.IsSylowOf.card_eq hU', Subgroup.card_top,
      CFSG.Walter.J1Props.card_walterJ1, hfac]
    norm_num
  have hInf : A' ⊓ U' = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have h1 : Nat.card ↥(A' ⊓ U') ∣ r := by
      rw [← hA']
      exact Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(A' ⊓ U') ∣ 8 := by
      rw [← hU8]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hr).mp h1 with h | h
    · exact h
    · exfalso
      rw [h] at h2
      exact absurd h2 (by
        rintro ⟨k, hk⟩
        have hle : r ≤ 8 := Nat.le_of_dvd (by norm_num) ⟨k, hk⟩
        omega)
  have hHcard : Nat.card ↥(A' ⊔ U') = r * 8 := by
    rw [CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p2214_card_sup_of_permutes hperm' hInf,
      hA', hU8]
  have hSubNormal : (A'.subgroupOf (A' ⊔ U')).Normal := by
    have hsub : Nat.card (A'.subgroupOf (A' ⊔ U')) = r := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, hA']
    exact normal_of_card_eq_prime_mul (A := A'.subgroupOf (A' ⊔ U')) hr hHcard
      (by omega) hsub
  have hU_N : U' ≤ normalizer (A' : Set CFSG.Open.walterJ1) := by
    have hNH : (A' ⊔ U') ≤ normalizer (A' : Set CFSG.Open.walterJ1) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hSubNormal
    exact le_sup_right.trans hNH
  have hr19 : r = 11 ∨ r = 19 := by
    have hdvd : r ∣ 175560 := by
      rw [← hA', ← CFSG.Walter.J1Props.card_walterJ1]
      exact Subgroup.card_subgroup_dvd_card A'
    rcases CFSG.Walter.J1Props.prime_dvd_card hr hdvd with h | h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · exact Or.inl h
    · exact Or.inr h
  have hfac_r : (175560 : ℕ).factorization r = 1 := by
    rcases hr19 with rfl | rfl
    · rw [Nat.factorization_def _ (by norm_num : Nat.Prime 11)]
      decide +kernel
    · rw [Nat.factorization_def _ (by norm_num : Nat.Prime 19)]
      decide +kernel
  have : Fact r.Prime := ⟨hr⟩
  let P : Sylow r CFSG.Open.walterJ1 :=
    Sylow.ofCard A' (by rw [hA', CFSG.Walter.J1Props.card_walterJ1, hfac_r, pow_one])
  have hP : (P : Subgroup CFSG.Open.walterJ1) = A' := Sylow.coe_ofCard A' _
  have hC : centralizer (A' : Set CFSG.Open.walterJ1) = A' := by
    rw [← hP]
    exact CFSG.Walter.J1Props.centralizer_sylow_eq (p := r)
      (by rcases hr19 with rfl | rfl <;> simp) P
  let f : U' →* MulAut A' := A'.normalizerMonoidHom.comp (Subgroup.inclusion hU_N)
  have hker : f.ker = ⊥ := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hu
      have hu' : (⟨u, hU_N u.2⟩ : normalizer (A' : Set CFSG.Open.walterJ1)) ∈
          A'.normalizerMonoidHom.ker := hu
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hu'
      rw [hC] at hu'
      have hmem : (u : CFSG.Open.walterJ1) ∈ A' ⊓ U' := ⟨hu', u.2⟩
      rw [hInf, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    · intro hu
      rw [hu, map_one]
  have hdiv : Nat.card U' ∣ Nat.card (MulAut A') := by
    have hrange : Nat.card f.range ∣ Nat.card (MulAut A') := by
      have h := Subgroup.card_dvd_of_le (le_top : f.range ≤ ⊤)
      rwa [Subgroup.card_top] at h
    have hcard := Subgroup.card_ker_mul_card_range f
    rw [hker, Subgroup.card_bot, one_mul] at hcard
    rwa [hcard] at hrange
  have haut : Nat.card (MulAut A') = r - 1 := by
    have : IsCyclic A' := isCyclic_of_prime_card hA'
    rw [IsCyclic.card_mulAut, hA', Nat.totient_prime hr]
  have h8dvd : 8 ∣ r - 1 := by
    rw [← hU8, ← haut]
    exact hdiv
  rcases hr19 with rfl | rfl
  · obtain ⟨k, hk⟩ := h8dvd
    omega
  · obtain ⟨k, hk⟩ := h8dvd
    omega

theorem commutator_eq_bot_of_isJ1 {G : Type} [Group G] [Finite G]
    {L A : Subgroup G} (hL : UC22.IsJ1 ↥L) (hA : (Nat.card A).Prime)
    (hAL : A ≤ normalizer (L : Set G)) (hrL : ¬ Nat.card A ∣ Nat.card L) : ⁅L, A⁆ = ⊥ := by
  obtain ⟨e₀⟩ := hL
  let e : ↥L ≃* CFSG.Open.walterJ1 := e₀.trans CFSG.Walter.walterJ1EquivNative.symm
  have hinner : ∀ α : MulAut ↥L, ∃ l : ↥L, α = MulAut.conj l := by
    intro α
    obtain ⟨g, hg⟩ := CFSG.Walter.J1Props.J3_aut (e.symm.trans (α.trans e))
    refine ⟨e.symm g, ?_⟩
    apply MulEquiv.ext
    intro x
    apply e.injective
    have h1 := congrArg (fun f : MulAut CFSG.Open.walterJ1 => f (e x)) hg
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
    rw [h1]
    simp
  have hN : normalizer (L : Set G) ≤ L ⊔ centralizer (L : Set G) :=
    CFSG.EvenSporadicStandard.normalizer_le_sup_centralizer_of_mulAut_inner hinner
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  obtain ⟨l, hl, c, hc, rfl⟩ :=
    CFSG.EvenSporadicStandard.exists_mul_of_mem_sup_of_le_centralizer
      (A := L) (B := centralizer (L : Set G)) (le_refl _) (hN (hAL ha))
  have hcomm : Commute l c := (Subgroup.mem_centralizer_iff.1 hc) l hl
  have hpow : (l * c) ^ Nat.card A = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard A ha)
  have hkey : l ^ Nat.card A * c ^ Nat.card A = 1 := by
    rw [← hcomm.mul_pow]
    exact hpow
  have hlr_mem : l ^ Nat.card A ∈ centralizer (L : Set G) := by
    have hcr : c ^ Nat.card A ∈ centralizer (L : Set G) :=
      (centralizer (L : Set G)).pow_mem hc _
    have hlr : l ^ Nat.card A = (c ^ Nat.card A)⁻¹ := eq_inv_of_mul_eq_one_left hkey
    rw [hlr]
    exact (centralizer (L : Set G)).inv_mem hcr
  have hcop : Nat.Coprime (Nat.card A) (orderOf l) := by
    rw [hA.coprime_iff_not_dvd]
    intro hd
    exact hrL (hd.trans (Subgroup.orderOf_dvd_natCard L hl))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hlC : l ∈ centralizer (L : Set G) := by
    have hlz : l ∈ Subgroup.zpowers (l ^ Nat.card A) := by
      have h := Subgroup.npow_mem_zpowers (l ^ Nat.card A) m
      rwa [hm] at h
    exact (Subgroup.zpowers_le.mpr hlr_mem) hlz
  exact (centralizer (L : Set G)).mul_mem hlC hc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBar
