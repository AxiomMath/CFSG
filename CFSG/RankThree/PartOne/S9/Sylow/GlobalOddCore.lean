module

import CFSG.RankThree.GroupTheory.SteinbergCEOddCoreCommutator
import CFSG.RankThree.GroupTheory.SteinbergCDFixedNormalCentralComplement
import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
import CFSG.RankThree.GroupTheory.SteinbergCDRankOneAutPrimes
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalBridge

public section

namespace CFSG.RankThree.PartOne.Sec9B

open CFSG Subgroup CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

section OddCoreCommutator

variable {G : Type*} [Group G] [Finite G]

theorem commutator_le_inSubgroup_pCore_of_le_F {H D R : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hDF : D ≤ ((pCore q (↥H ⧸ pCore 2 ↥H)).comap (QuotientGroup.mk' (pCore 2 ↥H))).map
      H.subtype)
    (hD : IsPGroup q ↥D) (hRD : R ≤ Subgroup.normalizer (D : Set G)) (hRH : R ≤ H)
    (hRJ : R ≤ Subgroup.centralizer (inSubgroup (pCore 2) H : Set G)) :
    ⁅D, R⁆ ≤ inSubgroup (pCore q) H := by
  have hι := H.subtype_injective
  have hDH : D ≤ H := hDF.trans (Subgroup.map_subtype_le _)
  have hD' : (D.subgroupOf H).map H.subtype = D := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hDH]
  have hR' : (R.subgroupOf H).map H.subtype = R := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRH]
  have h1 := odd_core_commutator_after_two_core_centralization (H := ↥H) hq
    (D := D.subgroupOf H) (R := R.subgroupOf H)
    (by rw [← Subgroup.map_le_map_iff_of_injective hι, hD']; exact hDF)
    (by rw [← isPGroup_map_iff hι, hD']; exact hD)
    (by rw [← map_le_normalizer_map_iff hι, hD', hR']; exact hRD)
    (by rw [← map_le_centralizer_map_iff hι, hR']; exact hRJ)
  have := Subgroup.map_mono (f := H.subtype) h1
  rwa [Subgroup.map_commutator, hD', hR'] at this

end OddCoreCommutator

section Critical

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem normalizerConj_pow_apply (M : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (M : Set G)) (n : ℕ) (y : ↥M) :
    (((normalizerConj M g hg) ^ n) y : G) = g ^ n * y * (g ^ n)⁻¹ := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, normalizerConj_apply_coe]
    rw [pow_succ, mul_inv_rev]
    group

theorem exists_critical {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) {M : Subgroup G}
    (hM : IsPGroup s ↥M) (hM1 : M ≠ ⊥) :
    ∃ X : Subgroup G, X ≤ M ∧ X ≠ ⊥ ∧
      (∀ g ∈ Subgroup.normalizer (M : Set G), g ∈ Subgroup.normalizer (X : Set G)) ∧
      (∀ x ∈ X, x ^ s = 1) ∧ ⁅X, M⁆ ≤ X ⊓ Subgroup.centralizer (X : Set G) ∧
      ∀ g ∈ Subgroup.normalizer (M : Set G), (∀ x ∈ X, g * x * g⁻¹ = x) →
        Nat.Coprime (orderOf g) s → ∀ m ∈ M, g * m * g⁻¹ = m := by
  have : Fact s.Prime := ⟨hs⟩
  have : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM1
  obtain ⟨D', hDc, hD1, hDcomm, hDexp, hDfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hs2 hM
  have hX : (D'.map M.subtype).subgroupOf M = D' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective D'
  refine ⟨D'.map M.subtype, Subgroup.map_subtype_le _, fun h =>
    hD1 ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).mp h), ?_,
    (forall_pow_eq_one_map_iff M.subtype_injective).mpr hDexp, ?_, ?_⟩
  · intro g hg
    have hc : ((D'.map M.subtype).subgroupOf M).Characteristic := by
      rw [hX]; exact hDc
    exact mem_normalizer_of_characteristic (Subgroup.map_subtype_le _) hc hg
  · have hM_top : (⊤ : Subgroup ↥M).map M.subtype = M := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    have h1 := Subgroup.map_mono (f := M.subtype) hDcomm
    rw [Subgroup.map_commutator, map_inf_centralizer_map M.subtype_injective, hM_top] at h1
    exact h1
  · intro g hg hfix hcop m hm
    set φ := normalizerConj M g hg with hφ
    have hφfix : φ ∈ fixingSubgroup (MulAut ↥M) (D' : Set ↥M) := by
      rw [mem_fixingSubgroup_iff]
      intro d hd
      apply Subtype.ext
      rw [MulAut.smul_def, normalizerConj_apply_coe]
      exact hfix _ (Subgroup.mem_map_of_mem M.subtype hd)
    obtain ⟨k, hk⟩ := hDfix ⟨φ, hφfix⟩
    have hk' : φ ^ (s ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hn : φ ^ (orderOf g) = 1 := by
      refine MulEquiv.ext fun y => Subtype.ext ?_
      rw [MulAut.one_apply]
      have := normalizerConj_pow_apply M g hg (orderOf g) y
      rw [pow_orderOf_eq_one] at this
      simpa using this
    have hgcd : Nat.gcd (orderOf g) (s ^ k) = 1 := (Nat.Coprime.pow_right k hcop)
    have h1 : φ = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hn, hk'⟩
      rwa [hgcd, pow_one] at this
    have := congrArg (fun ψ : MulAut ↥M => ((ψ ⟨m, hm⟩ : ↥M) : G)) h1
    simpa [hφ] using this

end Critical

section CentralComplement

variable {G : Type*} [Group G] [Finite G]

theorem central_complement_of_fixed {K B N P : Subgroup G} (hK : Group.IsSolvable ↥K)
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥B))
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hNK : N ≤ K) (hPK : P ≤ K)
    (hNn : K ≤ Subgroup.normalizer (N : Set G)) (hPZ : ∀ x ∈ P, ∀ k ∈ K, x * k = k * x)
    (hBP : B ≤ Subgroup.normalizer (P : Set G)) (hBN : ∀ b ∈ B, ∀ x ∈ N, b * x * b⁻¹ = x)
    (hC : ∀ k ∈ K, (∀ x ∈ N, x * k = k * x) → k ∈ N ⊔ P) :
    ∀ k ∈ K, ∃ z ∈ K, (∀ k' ∈ K, z * k' = k' * z) ∧
      ∃ c ∈ K, (∀ b ∈ B, b * c = c * b) ∧ k = z * c := by
  let : MulDistribMulAction ↥B ↥K := MulDistribMulAction.compHom ↥K
    ({ toFun := fun b => normalizerConj K b (hBK b.2)
       map_one' := by ext; simp
       map_mul' := fun b₁ b₂ => by ext; simp [mul_assoc] } : ↥B →* MulAut ↥K)
  have hsmul : ∀ (b : ↥B) (x : ↥K), ((b • x : ↥K) : G) = b * x * (b : G)⁻¹ := fun b x => rfl
  have : (N.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hNn
  obtain ⟨-, -, hfac⟩ := coprime_fixed_normal_subgroup_central_complement (A := ↥B) hK
    (Nat.Coprime.symm hcop.symm) (N.subgroupOf K) (P.subgroupOf K)
    (fun x hx => Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hPZ x.1 hx g.1 g.2).symm)
    (fun a x hx => by
      change ((a • x : ↥K) : G) ∈ P
      rw [hsmul]
      exact (Subgroup.mem_normalizer_iff.mp (hBP a.2) x).mp hx)
    (fun a x hx => Subtype.ext (by rw [hsmul]; exact hBN a a.2 x hx))
    (fun k hk => by
      have hk' : (k : G) ∈ N ⊔ P := hC k k.2 fun x hx => by
        have := Subgroup.mem_centralizer_iff.mp hk ⟨x, hNK hx⟩ hx
        exact congrArg Subtype.val this
      rw [← Subgroup.subgroupOf_sup hNK hPK]
      exact hk')
  intro k hk
  obtain ⟨z, hz, c, hc, hkzc⟩ := hfac ⟨k, hk⟩
  refine ⟨z, z.2, fun k' hk' => ?_, c, c.2, fun b hb => ?_, congrArg Subtype.val hkzc⟩
  · exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz ⟨k', hk'⟩))).symm
  · have := congrArg Subtype.val (hc ⟨b, hb⟩)
    rw [hsmul] at this
    calc (b : G) * c = b * c * b⁻¹ * b := by group
      _ = c * b := by rw [this]

end CentralComplement

section Ranks

universe u

variable {G : Type u} [Group G] [Finite G]

theorem pRank_two_le_of_le {R C : Subgroup G} (hRC : R ≤ C) :
    CFSG.pRank 2 ↥R ≤ CFSG.pRank 2 ↥C := by
  rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_two,
    CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_two]
  exact CFSG.SectionRank.pRank_mono (by norm_num) hRC

theorem two_le_pRank_of_acts {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {A R : Subgroup G}
    (hApg : IsPGroup p ↥A) (hR2 : IsPGroup 2 ↥R) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hRA : ⁅R, A⁆ = R) (hR1 : R ≠ ⊥) : 2 ≤ CFSG.pRank 2 ↥R := by
  let : MulDistribMulAction ↥A ↥R := MulDistribMulAction.compHom ↥R
    ({ toFun := fun a => normalizerConj R a (hAR a.2)
       map_one' := by ext; simp
       map_mul' := fun a₁ a₂ => by ext; simp [mul_assoc] } : ↥A →* MulAut ↥R)
  refine (CFSG.RankThree.GroupTheory.rank_one_two_group_automorphism_prime_support.{0, u, u}.2
    p ↥A ↥R hp hp3 hApg hR2 ?_)
  by_contra hne
  have hne' : ∀ (a : ↥A) (x : ↥R), a • x = x := fun a x => by
    by_contra h
    exact hne ⟨a, x, h⟩
  apply hR1
  rw [← hRA, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro r hr
  refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
  have h1 : (a * r * a⁻¹ : G) = r := congrArg Subtype.val (hne' ⟨a, ha⟩ ⟨r, hr⟩)
  calc a * r = (a * r * a⁻¹) * a := by group
    _ = r * a := by rw [h1]

end Ranks

end CFSG.RankThree.PartOne.Sec9B
