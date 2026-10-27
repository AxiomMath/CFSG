module

public import CFSG.Open.FusionDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Unitary.Overgroup
import CFSG.LocalAnalysis.ComponentClassification.OddCore
import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Arith
import CFSG.SignalizerFunctorTheorem.McBride.Models.Unitary.Bender
import CFSG.SignalizerFunctorTheorem.McBride.Models.Unitary.Reduction
import CFSG.SignalizerFunctorTheorem.McBride.Models.Unitary.Section
import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Sections
import CFSG.StronglyEmbedded.BenderNormalSeries
import CFSG.StronglyEmbedded.BenderUnitaryBorel

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.NearSolvable
open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryFrame

section Abstract

variable {G : Type*} [Group G] [Finite G]

theorem not_four_dvd_card_normalizer_of_card_three
    (hA : ∀ x s : G, orderOf s = 2 → x * s = s * x → ¬ 3 ∣ orderOf x) {Q : Subgroup G}
    (hQ : Nat.card Q = 3) : ¬ 4 ∣ Nat.card (Subgroup.normalizer (Q : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic Q := isCyclic_of_prime_card hQ
  set φ := Q.normalizerMonoidHom with hφ
  have hker : Odd (Nat.card φ.ker) := by
    by_contra hnodd
    have h2 : 2 ∣ Nat.card φ.ker := by
      rwa [Nat.not_odd_iff_even, even_iff_two_dvd] at hnodd
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := φ.ker) 2 h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Q) 3 (by rw [hQ])
    have hs2 : orderOf (((s : Subgroup.normalizer (Q : Set G)) : G)) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hs]
    have hsc : ((s : Subgroup.normalizer (Q : Set G)) : G) ∈
        Subgroup.centralizer (Q : Set G) :=
      (SetLike.ext_iff.mp (Subgroup.normalizerMonoidHom_ker (H := Q))
        (s : Subgroup.normalizer (Q : Set G))).mp s.2
    have hcomm : (x : G) * ((s : Subgroup.normalizer (Q : Set G)) : G) =
        ((s : Subgroup.normalizer (Q : Set G)) : G) * x :=
      (Subgroup.mem_centralizer_iff.mp hsc) x x.2
    refine hA (x : G) _ hs2 hcomm ?_
    rw [Subgroup.orderOf_coe, hx]
  have hquot : Nat.card (Subgroup.normalizer (Q : Set G) ⧸ φ.ker) ∣ 2 := by
    have h1 := Subgroup.card_dvd_of_injective _ (QuotientGroup.kerLift_injective φ)
    have h2 : Nat.card (MulAut Q) = 2 := by
      rw [IsCyclic.card_mulAut, hQ, Nat.totient_prime Nat.prime_three]
    rwa [h2] at h1
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  intro h4
  rw [hmul] at h4
  have hcop : Nat.Coprime 4 (Nat.card φ.ker) := by
    have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hker)
    simpa using this
  have h4q := hcop.dvd_of_dvd_mul_right h4
  have := Nat.le_of_dvd (by norm_num) (h4q.trans hquot)
  omega

theorem false_of_normal_section {P : Subgroup G} {t : G} {M N : Subgroup G} [M.Normal]
    [N.Normal] [(M.subgroupOf N).Normal] (hMN : M ≤ N) (hNo : Odd N.index)
    (hP9 : Nat.card P = 9) (h27 : ¬ 27 ∣ Nat.card G) (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (ht : orderOf t = 2) (hinv : ∀ u ∈ P, t * u * t⁻¹ = u⁻¹)
    (hA : ∀ x s : G, orderOf s = 2 → x * s = s * x → ¬ 3 ∣ orderOf x)
    (hb3 : 3 ∣ Nat.card (N ⧸ M.subgroupOf N)) (hb9 : ¬ 9 ∣ Nat.card (N ⧸ M.subgroupOf N))
    (hb32 : 32 ∣ Nat.card (N ⧸ M.subgroupOf N)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htN : t ∈ N := by
    have hq : QuotientGroup.mk' N t = 1 := by
      have h1 : orderOf (QuotientGroup.mk' N t) ∣ 2 := ht ▸ orderOf_map_dvd _ t
      have h2 : orderOf (QuotientGroup.mk' N t) ∣ N.index := by
        have := orderOf_dvd_natCard (QuotientGroup.mk' N t)
        rwa [← Subgroup.index_eq_card] at this
      have hcop : Nat.Coprime 2 N.index := Nat.coprime_two_left.mpr hNo
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    exact (QuotientGroup.eq_one_iff t).mp hq
  have hPN : P ≤ N := by
    intro u hu
    have h1 : t * u * t⁻¹ * u⁻¹ ∈ N := by
      have : t * (u * t⁻¹ * u⁻¹) ∈ N :=
        N.mul_mem htN ((inferInstance : N.Normal).conj_mem _ (N.inv_mem htN) u)
      simpa [mul_assoc] using this
    rw [hinv u hu] at h1
    have h2 : u ^ 2 ∈ N := by
      have := N.inv_mem h1
      simpa [pow_two] using this
    have h4 : u = (u ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_add, hP3 u hu, one_mul, pow_one]
    rw [h4]
    exact N.pow_mem h2 2
  have hN9 : 9 ∣ Nat.card N := hP9 ▸ Subgroup.card_dvd_of_le hPN
  have hN27 : ¬ 27 ∣ Nat.card N := fun h => h27 (h.trans (Subgroup.card_subgroup_dvd_card N))
  have hNM : Nat.card N = Nat.card (N ⧸ M.subgroupOf N) * Nat.card M := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (M.subgroupOf N)]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMN).toEquiv
  obtain ⟨b, hb⟩ := hb3
  have hb3' : ¬ 3 ∣ b := fun h => hb9 (by rw [hb]; omega)
  have h3M : 3 ∣ Nat.card M := by
    rw [hNM, hb] at hN9
    have h3 : 3 ∣ b * Nat.card M := by
      have : 3 * (b * Nat.card M) = 3 * b * Nat.card M := by ring
      omega
    exact ((Nat.Prime.dvd_mul Nat.prime_three).mp h3).resolve_left hb3'
  have h9M : ¬ 9 ∣ Nat.card M := by
    rintro ⟨c, hc⟩
    exact hN27 ⟨b * c, by rw [hNM, hb, hc]; ring⟩
  obtain ⟨Q₃⟩ : Nonempty (Sylow 3 M) := inferInstance
  have hQ₃ : Nat.card Q₃ = 3 := by
    rw [Sylow.card_eq_multiplicity]
    have h1 : 1 ≤ (Nat.card M).factorization 3 :=
      (Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' h3M)
    have h2 : (Nat.card M).factorization 3 < 2 := by
      by_contra hcon
      exact h9M ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
        Nat.card_pos.ne').mpr (not_lt.mp hcon))
    have : (Nat.card M).factorization 3 = 1 := by omega
    rw [this]
    norm_num
  set Q : Subgroup G := Subgroup.map M.subtype (Q₃ : Subgroup M) with hQdef
  have hQcard : Nat.card Q = 3 := by
    rw [hQdef, Subgroup.card_map_of_injective M.subtype_injective]
    exact hQ₃
  have hfr := Sylow.normalizer_sup_eq_top Q₃
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' M).comp (Subgroup.normalizer (Q : Set G)).subtype) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M x
    have hg : g ∈ Subgroup.normalizer (Q : Set G) ⊔ M := by
      rw [hfr]
      exact Subgroup.mem_top g
    obtain ⟨n, hn, m, hm, hnm⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    refine ⟨⟨n, hn⟩, ?_⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply]
    rw [← hnm, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff m).mpr hm, mul_one]
  have hdvd1 : Nat.card (G ⧸ M) ∣ Nat.card (Subgroup.normalizer (Q : Set G)) :=
    Subgroup.card_dvd_of_surjective hsurj
  have hGM : Nat.card (G ⧸ M) = Nat.card (N ⧸ M.subgroupOf N) * N.index := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup M
    have h2 := N.card_mul_index
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := M))
    rw [← h1, ← h2, hNM]
    ring
  have h4 : 4 ∣ Nat.card (Subgroup.normalizer (Q : Set G)) := by
    have h1 : Nat.card (N ⧸ M.subgroupOf N) ∣ Nat.card (G ⧸ M) := by
      rw [hGM]
      exact dvd_mul_right _ _
    exact ((show 4 ∣ 32 by norm_num).trans hb32).trans (h1.trans hdvd1)
  exact not_four_dvd_card_normalizer_of_card_three hA hQcard h4

theorem exists_normal_coprime_six_of_sylow_two_cyclic_or_quaternion {P : Subgroup G}
    (hP : Nat.card P = 9) (h27 : ¬ 27 ∣ Nat.card G)
    (hNP : Nat.card (Subgroup.normalizer (P : Set G)) ∣ 72)
    (hA : ∀ x t : G, orderOf t = 2 → x * t = t * x → ¬ 3 ∣ orderOf x)
    (heven : 2 ∣ Nat.card G)
    (hS : ∀ S : Sylow 2 G, IsCyclic S ∨
      ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup G) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    ∃ K₃ : Subgroup G, K₃.Normal ∧ Nat.Coprime (Nat.card K₃) 6 ∧
      ∀ y : G, Nat.Coprime (orderOf y) 6 → y ∈ K₃ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hindex : ¬ 3 ∣ P.index := by
    intro h3
    have hmul := P.card_mul_index
    rw [hP] at hmul
    obtain ⟨j, hj⟩ := h3
    exact h27 ⟨j, by rw [← hmul, hj]; ring⟩
  let P' : Sylow 3 G :=
    (IsPGroup.of_card (n := 2) (by rw [hP]; norm_num) : IsPGroup 3 P).toSylow hindex
  obtain ⟨t, ht, hdecomp⟩ := exists_involution_mul_centralizer heven hS
  set K := CFSG.oddCore G with hK
  have hKodd : Odd (Nat.card K) := CFSG.ComponentClassification.OddCore.odd_card G
  have hPK : P ≤ K := by
    intro x hx
    obtain ⟨m, hm, c, hc, rfl⟩ := hdecomp x
    have hdvdP : orderOf (m * c) ∣ 9 := hP ▸ Subgroup.orderOf_dvd_natCard _ hx
    let q := QuotientGroup.mk' K
    have hqm : q m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
    have hq : q (m * c) = q c := by rw [map_mul, hqm, one_mul]
    have h1 : orderOf (q c) ∣ 9 := by
      rw [← hq]
      exact (orderOf_map_dvd q _).trans hdvdP
    have h3 : ¬ 3 ∣ orderOf (q c) := fun h3 =>
      hA c t ht hc (h3.trans (orderOf_map_dvd q c))
    have hqc : q c = 1 := orderOf_eq_one_iff.mp (eq_one_of_dvd_nine h1 h3)
    exact (QuotientGroup.eq_one_iff _).mp (hq.trans hqc)
  have hfr : Subgroup.normalizer (P : Set G) ⊔ K = ⊤ := Sylow.normalizer_sup_eq_top' P' hPK
  have hKN : (K ⊓ Subgroup.normalizer (P : Set G) : Subgroup G) = P := by
    have hle : P ≤ K ⊓ Subgroup.normalizer (P : Set G) := le_inf hPK Subgroup.le_normalizer
    have hodd : Odd (Nat.card ↥(K ⊓ Subgroup.normalizer (P : Set G))) :=
      hKodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have hdvd72 : Nat.card ↥(K ⊓ Subgroup.normalizer (P : Set G)) ∣ 72 :=
      (Subgroup.card_dvd_of_le inf_le_right).trans hNP
    have h9 : 9 ∣ Nat.card ↥(K ⊓ Subgroup.normalizer (P : Set G)) :=
      hP ▸ Subgroup.card_dvd_of_le hle
    have hcard : Nat.card ↥(K ⊓ Subgroup.normalizer (P : Set G)) = 9 := by
      have hmem : Nat.card ↥(K ⊓ Subgroup.normalizer (P : Set G)) ∈ Nat.divisors 72 :=
        Nat.mem_divisors.mpr ⟨hdvd72, by norm_num⟩
      have h72 : Nat.divisors 72 = {1, 2, 3, 4, 6, 8, 9, 12, 18, 24, 36, 72} := by decide
      rw [h72] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      obtain ⟨j, hj⟩ := hodd
      omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hP])).symm
  have hquot3 : ¬ 3 ∣ Nat.card (G ⧸ K) := by
    intro h3
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    have h9K : 9 ∣ Nat.card K := hP ▸ Subgroup.card_dvd_of_le hPK
    exact h27 (by rw [h1]; exact mul_dvd_mul h3 h9K)
  have hquotN : Nat.card (G ⧸ K) ∣ Nat.card (Subgroup.normalizer (P : Set G)) := by
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' K).comp (Subgroup.normalizer (P : Set G)).subtype) := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K x
      have hg : g ∈ Subgroup.normalizer (P : Set G) ⊔ K := by
        rw [hfr]
        exact Subgroup.mem_top g
      obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_right.mp hg
      refine ⟨⟨n, hn⟩, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply]
      rw [← hnk, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff k).mpr hk, mul_one]
    exact Subgroup.card_dvd_of_surjective hsurj
  have hquot8 : Nat.card (G ⧸ K) ∣ 8 := by
    have h72 : Nat.card (G ⧸ K) ∣ 8 * 9 := by simpa using hquotN.trans hNP
    have hcop : Nat.Coprime (Nat.card (G ⧸ K)) 9 := by
      have : Nat.Coprime (Nat.card (G ⧸ K)) 3 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hquot3).symm
      simpa using this.pow_right 2
    exact hcop.dvd_of_dvd_mul_right h72
  have hGK : ∀ y : G, Odd (orderOf y) → y ∈ K := by
    intro y hy
    have h1 : Odd (orderOf (QuotientGroup.mk' K y)) :=
      hy.of_dvd_nat (orderOf_map_dvd _ y)
    have h2 : orderOf (QuotientGroup.mk' K y) ∣ 8 :=
      (orderOf_dvd_natCard _).trans hquot8
    have hcop : Nat.Coprime (orderOf (QuotientGroup.mk' K y)) 8 := by
      have := Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr h1)
      simpa using this
    have := Nat.Coprime.eq_one_of_dvd hcop h2
    exact (QuotientGroup.eq_one_iff y).mp (orderOf_eq_one_iff.mp this)
  let Pk : Sylow 3 K := P'.subtype hPK
  have hPkcard : Nat.card Pk = 9 := by
    have : Nat.card (P.subgroupOf K) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv
    exact this.trans hP
  have hPkcomm : IsMulCommutative (Pk : Subgroup K) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hPkcard]; norm_num)
  have hnorm : Subgroup.normalizer ((Pk : Subgroup K) : Set K) ≤
      Subgroup.centralizer ((Pk : Subgroup K) : Set K) := by
    intro y hy
    have hy' : y ∈ (Subgroup.normalizer (P : Set G)).subgroupOf K := by
      rw [Subgroup.subgroupOf_normalizer_eq hPK]
      exact hy
    have hyKP : (y : G) ∈ K ⊓ Subgroup.normalizer (P : Set G) := ⟨y.2, hy'⟩
    rw [hKN] at hyKP
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact congrArg Subtype.val (hPkcomm.is_comm.comm ⟨z, hz⟩ ⟨y, hyKP⟩)
  have hcompl := MonoidHom.ker_transferSylow_isComplement' Pk hnorm
  set τ := MonoidHom.transferSylow Pk hnorm with hτ
  have hker3 : ¬ 3 ∣ Nat.card τ.ker := MonoidHom.not_dvd_card_ker_transferSylow Pk hnorm
  have hmulcard : Nat.card τ.ker * Nat.card Pk = Nat.card K := hcompl.card_mul_card
  set K₃ : Subgroup G := τ.ker.map K.subtype with hK₃
  have hK₃card : Nat.card K₃ = Nat.card τ.ker :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hK₃odd : Odd (Nat.card K₃) := by
    rw [hK₃card]
    exact hKodd.of_dvd_nat (Dvd.intro _ hmulcard)
  have hK₃3 : ¬ 3 ∣ Nat.card K₃ := by
    rw [hK₃card]
    exact hker3
  have hcop : Nat.Coprime (Nat.card K₃) 6 := by
    have h2 : Nat.Coprime (Nat.card K₃) 2 := Nat.coprime_two_right.mpr hK₃odd
    have h3 : Nat.Coprime (Nat.card K₃) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hK₃3).symm
    simpa using Nat.Coprime.mul_right h2 h3
  have hK₃char : ∀ y : G, y ∈ K → ¬ 3 ∣ orderOf y → y ∈ K₃ := by
    intro y hy h3
    set y' : K := ⟨y, hy⟩ with hy'
    have hdvd9 : orderOf (τ y') ∣ 9 := hPkcard ▸ orderOf_dvd_natCard (τ y')
    have hd : orderOf (τ y') ∣ orderOf y' := orderOf_map_dvd τ y'
    have hy'ord : orderOf y' = orderOf y := Subgroup.orderOf_mk y hy
    have h1 : orderOf (τ y') = 1 :=
      eq_one_of_dvd_nine hdvd9 (fun h => h3 (hy'ord ▸ h.trans hd))
    exact ⟨y', orderOf_eq_one_iff.mp h1, rfl⟩
  have hK₃conj : ∀ g : G, ∀ x ∈ K₃, g * x * g⁻¹ ∈ K₃ := by
    intro g x hx
    have hxK : x ∈ K := Subgroup.map_subtype_le _ hx
    have hxdvd : orderOf x ∣ Nat.card K₃ := Subgroup.orderOf_dvd_natCard K₃ hx
    refine hK₃char _ ((inferInstance : K.Normal).conj_mem x hxK g) ?_
    rw [orderOf_conj_eq]
    exact fun h => hK₃3 (h.trans hxdvd)
  refine ⟨K₃, ⟨fun x hx g => hK₃conj g x hx⟩, hcop, fun y hy => ?_⟩
  have hodd : Odd (orderOf y) :=
    Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) hy)
  have h3 : ¬ 3 ∣ orderOf y := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) hy).symm h
  exact hK₃char y (hGK y hodd) h3

end Abstract

theorem conj_eq_inv_of_fixedData {p : ℕ} {C P : Subgroup (PSU3 2 p)} (hF : FixedData C P)
    {t : PSU3 2 p} (htC : t ∈ C) (ht : orderOf t = 2) {x : PSU3 2 p} (hx : x ∈ P) :
    t * x * t⁻¹ = x⁻¹ := by
  have hc := hF.isElemAbelian.1
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht, pow_two] at h
  have hti2 : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht2, inv_one]
  have hyP : t * x * t⁻¹ ∈ P := hF.normalizes t htC x hx
  have hzP : x * (t * x * t⁻¹) ∈ P := P.mul_mem hx hyP
  have hcomm : x * (t * x * t⁻¹) = (t * x * t⁻¹) * x :=
    congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨_, hyP⟩)
  have hyy : t * (t * x * t⁻¹) * t⁻¹ = x := by
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
      _ = x := by rw [ht2, hti2]; group
  have hzc : t * (x * (t * x * t⁻¹)) * t⁻¹ = x * (t * x * t⁻¹) := by
    calc t * (x * (t * x * t⁻¹)) * t⁻¹
        = (t * x * t⁻¹) * (t * (t * x * t⁻¹) * t⁻¹) := by group
      _ = (t * x * t⁻¹) * x := by rw [hyy]
      _ = x * (t * x * t⁻¹) := hcomm.symm
  have hz : t * (x * (t * x * t⁻¹)) = (x * (t * x * t⁻¹)) * t :=
    mul_inv_eq_iff_eq_mul.mp hzc
  have h1 : x * (t * x * t⁻¹) = 1 := by
    by_contra hne
    have htP := hF.mem_of_commute t htC _ hzP hne hz
    have hdvd : orderOf t ∣ 9 := hF.card_P ▸ Subgroup.orderOf_dvd_natCard P htP
    rw [ht] at hdvd
    omega
  exact eq_inv_of_mul_eq_one_right h1

theorem card_psl2Even_dvd_facts {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    3 ∣ 2 ^ p * ((2 ^ p) ^ 2 - 1) ∧ ¬ 9 ∣ 2 ^ p * ((2 ^ p) ^ 2 - 1) ∧
      32 ∣ 2 ^ p * ((2 ^ p) ^ 2 - 1) := by
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  refine ⟨(three_dvd_sq_sub_one (two_pow_mod_three hodd)).mul_left _,
    not_nine_dvd_psl2 (two_pow_mod_nine (prime_mod_six hp hp2 hp3)), ?_⟩
  exact (show 32 ∣ 2 ^ p from (pow_dvd_pow 2 h5 : 2 ^ 5 ∣ 2 ^ p)).mul_right _

theorem nonempty_mulEquiv_psl2Even_of_isBenderSection
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hnear : signalizerNearPSolvable p (PSU3 2 p)) {H : Subgroup (PSU3 2 p)} (hH : H ≠ ⊤)
    {M N : Subgroup ↥H} [M.Normal] [N.Normal] [(M.subgroupOf N).Normal]
    (hB : fusionIsBenderGroup (↥N ⧸ M.subgroupOf N)) :
    Nonempty ((↥N ⧸ M.subgroupOf N) ≃* PSL(2, GaloisField 2 p)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (↥N ⧸ M.subgroupOf N) := inferInstance
  have hsimple := CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  have hnab := exists_noncommuting_of_fusionIsBenderGroup hB
  have hsecH : CFSG.SignalizerFunctorTheorem.IsSectionOf (↥N ⧸ M.subgroupOf N) ↥H :=
    (CFSG.SignalizerFunctorTheorem.IsSectionOf.of_surjective (QuotientGroup.mk' (M.subgroupOf N))
      (QuotientGroup.mk'_surjective _)).trans
      (CFSG.SignalizerFunctorTheorem.IsSectionOf.of_subgroup N)
  have hsecY : CFSG.SignalizerFunctorTheorem.IsSectionOf (↥N ⧸ M.subgroupOf N) (PSU3 2 p) :=
    hsecH.of_injective H.subtype H.subtype_injective
  have hmodel := nearSimpleModel_of_isSectionOf hnear hnab hsecY
  exact nonempty_mulEquiv_psl2Even_of_dvd hp h5 hH hmodel (card_dvd_of_isSectionOf hsecH)

theorem exists_normal_coprime_six_of_overgroup
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hnear : signalizerNearPSolvable p (PSU3 2 p)) (inp : HeisenbergInput p)
    {C P : Subgroup (PSU3 2 p)} (hF : FixedData C P) {H : Subgroup (PSU3 2 p)}
    (hPH : P ≤ H) (htH : ∃ t ∈ H ⊓ C, orderOf t = 2) (hH : H ≠ ⊤) :
    ∃ N : Subgroup (PSU3 2 p), N ≤ H ∧ H ≤ Subgroup.normalizer (N : Set (PSU3 2 p)) ∧
      Nat.Coprime (Nat.card N) 6 ∧ ∀ y ∈ H, Nat.Coprime (orderOf y) 6 → y ∈ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htHC, ht2⟩ := htH
  have htH' : t ∈ H := htHC.1
  have htC : t ∈ C := htHC.2
  have hzp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2]; norm_num)
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  have hSE := (bender_psu3_borel_full p hp.two_le Q).1
  have h3H : 3 ∣ Nat.card H :=
    (show 3 ∣ 9 by norm_num).trans (hF.card_P ▸ Subgroup.card_dvd_of_le hPH)
  have hHB : ¬ H ≤ Subgroup.normalizer ((Q : Subgroup (PSU3 2 p)) : Set (PSU3 2 p)) :=
    fun hle => not_three_dvd_card_normalizer_sylow_two hp h5 Q
      (h3H.trans (Subgroup.card_dvd_of_le hle))
  have hev : ∃ v ∈ H ⊓ Subgroup.normalizer ((Q : Subgroup (PSU3 2 p)) : Set (PSU3 2 p)),
      orderOf v = 2 :=
    ⟨t, ⟨htH', Subgroup.le_normalizer (hQ (Subgroup.mem_zpowers _))⟩, ht2⟩
  have hSEH := fusionStronglyEmbedded_inf_subgroupOf hSE hHB hev
  have hP9 : Nat.card (P.subgroupOf H) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv).trans hF.card_P
  have h27 : ¬ 27 ∣ Nat.card H := fun h =>
    not_twentyseven_dvd_card_psu3 hp h5 (h.trans (Subgroup.card_subgroup_dvd_card H))
  have hA : ∀ x s : ↥H, orderOf s = 2 → x * s = s * x → ¬ 3 ∣ orderOf x := by
    intro x s hs hxs
    have := not_three_dvd_orderOf_of_commute_involution hp h5 (x := (x : PSU3 2 p))
      (t := (s : PSU3 2 p)) (by rwa [Subgroup.orderOf_coe]) (congrArg Subtype.val hxs)
    rwa [Subgroup.orderOf_coe] at this
  have hNP : Nat.card (Subgroup.normalizer ((P.subgroupOf H : Subgroup H) : Set ↥H)) ∣ 72 := by
    rw [← Subgroup.subgroupOf_normalizer_eq hPH]
    have h1 : Nat.card ((Subgroup.normalizer (P : Set (PSU3 2 p))).subgroupOf H) ∣
        Nat.card (Subgroup.normalizer (P : Set (PSU3 2 p))) := by
      rw [← Subgroup.card_map_of_injective H.subtype_injective, Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact h1.trans (inp.card_normalizer_dvd P hF.isElemAbelian hF.card_P)
  rcases bender_strongly_embedded_normal_series ↥H _ hSEH with
    hS | ⟨M, N, hM, hN, hMN', hMN, -, hNo, hBender⟩
  ·
    have heven : 2 ∣ Nat.card H := by
      have := Subgroup.orderOf_dvd_natCard H htH'
      rwa [ht2] at this
    obtain ⟨K₃, hK₃n, hK₃c, hK₃y⟩ :=
      exists_normal_coprime_six_of_sylow_two_cyclic_or_quaternion hP9 h27 hNP hA heven hS
    refine ⟨K₃.map H.subtype, Subgroup.map_subtype_le K₃, ?_, ?_, ?_⟩
    · intro h hh
      have hmem : (⟨h, hh⟩ : H) ∈ Subgroup.normalizer (K₃ : Set ↥H) := by
        rw [Subgroup.normalizer_eq_top_iff.mpr hK₃n]
        exact Subgroup.mem_top _
      exact Subgroup.le_normalizer_map H.subtype (Subgroup.mem_map_of_mem _ hmem)
    · rwa [Subgroup.card_map_of_injective H.subtype_injective]
    · intro y hy hcop
      have hy' : (⟨y, hy⟩ : H) ∈ K₃ := hK₃y ⟨y, hy⟩ (by rwa [Subgroup.orderOf_mk])
      exact Subgroup.mem_map_of_mem _ hy'
  ·
    exfalso
    obtain ⟨e⟩ := nonempty_mulEquiv_psl2Even_of_isBenderSection hp h5 hnear hH hBender
    have hcard : Nat.card (↥N ⧸ M.subgroupOf N) = 2 ^ p * ((2 ^ p) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv]
      exact card_psl2_even hp.ne_zero
    obtain ⟨h3, h9, h32⟩ := card_psl2Even_dvd_facts hp h5
    rw [← hcard] at h3 h9 h32
    refine false_of_normal_section (P := P.subgroupOf H) (t := (⟨t, htH'⟩ : ↥H)) hMN hNo hP9 h27
      (fun x hx => Subtype.ext (by simpa using hF.pow_three (x : PSU3 2 p) hx)) ?_ ?_ hA h3 h9 h32
    · rw [Subgroup.orderOf_mk]
      exact ht2
    · intro u hu
      exact Subtype.ext (by simpa using conj_eq_inv_of_fixedData hF htC ht2 hu)

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryFrame
