module

import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.Quasithin.Background.C1GNBlocks
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.Quasithin.YS

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G]

structure S3Hyp [Finite G] (I T T₀ : Subgroup G) : Prop where
  sqtk : IsSQTKTC I
  charTwo : CharTwo I
  sylow : IsSylowTwoOf T₀ I
  hT : IsPGroup 2 T
  le : T₀ ≤ T
  rel : T₀.relIndex T = 2
  inter : T ⊓ I = T₀
  star : ∀ C : Subgroup G, C ≤ T₀ → C ≠ ⊥ → T ≤ Subgroup.normalizer (C : Set G) →
    I ⊓ Subgroup.normalizer (C : Set G) ≤ T₀
  relV : (pCoreOf 2 I).relIndex T₀ = 2

theorem normalizer_le_normalizer_centerOf' (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (centerOf X : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ z ∈ centerOf X, g * z * g⁻¹ ∈ centerOf X := by
    intro g hg z hz
    refine ⟨(Subgroup.mem_normalizer_iff.1 hg z).1 hz.1, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) y).1 hy
      simpa using this
    have hc : (g⁻¹ * y * g) * z = z * (g⁻¹ * y * g) := Subgroup.mem_centralizer_iff.1 hz.2 _ hy'
    calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc]
      _ = (g * z * g⁻¹) * y := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  exact ⟨key g hg z, fun hz => by simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hz⟩

theorem centerOf_ne_bot_of_pGroup [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) :
    centerOf P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP1
  have := hP.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center ↥P))
  intro h
  apply hz
  have hzc : ((z : ↥P) : G) ∈ centerOf P := by
    refine ⟨(z : ↥P).2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have := Subgroup.mem_center_iff.1 z.2 ⟨y, hy⟩
    exact congrArg Subtype.val this
  rw [h] at hzc
  have : ((z : ↥P) : G) = 1 := Subgroup.mem_bot.1 hzc
  apply Subtype.ext
  apply Subtype.ext
  simpa using this


theorem isSolvable_of_isCyclic_sylow_two' {K : Type*} [Group K] [Finite K] (P : Sylow 2 K)
    (hP : IsCyclic P) : Group.IsSolvable K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, ⟨hnormal, hodd, hindex, -⟩, -⟩ := CFSG.cyclic_sylow_normal_odd_complement P hP
  have hs1 : Group.IsSolvable (CFSG.pPrimeCore 2 K) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : (CFSG.pPrimeCore 2 K).Normal := hnormal
  have hs2 : Group.IsSolvable (K ⧸ CFSG.pPrimeCore 2 K) := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    have hq : IsPGroup 2 (K ⧸ CFSG.pPrimeCore 2 K) :=
      IsPGroup.of_card (n := n) (by rw [← Subgroup.index_eq_card, hindex, hn])
    have := hq.isNilpotent
    infer_instance
  exact Group.isSolvable_of_subgroup_quotient (CFSG.pPrimeCore 2 K)

namespace S3Hyp

variable [Finite G] {I T T₀ : Subgroup G} (h : S3Hyp I T T₀)
include h

theorem T_le_normalizer : T ≤ Subgroup.normalizer (T₀ : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mp (Subgroup.normal_of_index_eq_two h.rel)

theorem V_le : pCoreOf 2 I ≤ T₀ := h.sylow.pCoreOf_le

theorem T₀_ne_bot : T₀ ≠ ⊥ := by
  intro hbot
  have h2 := h.relV
  rw [hbot] at h2
  simp at h2

theorem normalizer_T₀_le : I ⊓ Subgroup.normalizer (T₀ : Set G) ≤ T₀ := by
  have hc : centerOf T₀ ≠ ⊥ := centerOf_ne_bot_of_pGroup h.sylow.isPGroup h.T₀_ne_bot
  have hle : centerOf T₀ ≤ T₀ := inf_le_left
  have hTN : T ≤ Subgroup.normalizer (centerOf T₀ : Set G) :=
    h.T_le_normalizer.trans (normalizer_le_normalizer_centerOf' T₀)
  exact (inf_le_inf_left I (normalizer_le_normalizer_centerOf' T₀)).trans (h.star _ hle hc hTN)


theorem isSolvable : Group.IsSolvable ↥I := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup G := pCoreOf 2 I with hV
  have hVI : V ≤ I := pCoreOf_le 2 I
  have hVn : (V.subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVI).2 (le_normalizer_pCoreOf 2 I)
  have hV2 : IsPGroup 2 V := pCoreOf_isPGroup 2 I
  have hVs : Group.IsSolvable ↥(V.subgroupOf I) := by
    have : IsPGroup 2 ↥(V.subgroupOf I) := hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVI).symm
    have := this.isNilpotent
    infer_instance
  have hT₀I : T₀ ≤ I := h.sylow.le
  set T₁ : Subgroup ↥I := T₀.subgroupOf I with hT₁
  set π : ↥I →* (↥I ⧸ V.subgroupOf I) := QuotientGroup.mk' (V.subgroupOf I) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ T₁ := by
    rw [hπ, QuotientGroup.ker_mk']
    exact fun x hx => Subgroup.mem_subgroupOf.2 (h.V_le (Subgroup.mem_subgroupOf.1 hx))
  have hT₁2 : IsPGroup 2 ↥T₁ := h.sylow.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hT₀I).symm
  have hP₀2 : IsPGroup 2 ↥(T₁.map π) := by
    have := hT₁2.map π
    exact this
  have hidx : (T₁.map π).index = T₁.index := Subgroup.index_map_eq T₁ hπs hker
  have hodd : ¬ 2 ∣ (T₁.map π).index := by
    rw [hidx]
    exact h.sylow.2.2
  let P : Sylow 2 (↥I ⧸ V.subgroupOf I) := hP₀2.toSylow hodd
  have hcardI : Nat.card ↥I = Nat.card (↥I ⧸ V.subgroupOf I) * Nat.card ↥(V.subgroupOf I) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hcardQ : Nat.card (↥I ⧸ V.subgroupOf I) = (T₁.map π).index * Nat.card ↥(T₁.map π) :=
    (Subgroup.index_mul_card (T₁.map π)).symm
  have hcardIT : Nat.card ↥I = T₁.index * Nat.card ↥T₁ := (Subgroup.index_mul_card T₁).symm
  have hVsub : Nat.card ↥(V.subgroupOf I) = Nat.card ↥V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVI).toEquiv
  have hT₁card : Nat.card ↥T₁ = Nat.card ↥T₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT₀I).toEquiv
  have hT₀V : Nat.card ↥T₀ = Nat.card ↥V * 2 := by
    have := C5.card_eq_card_mul_relIndex h.V_le
    rw [h.relV] at this
    exact this
  have hP₀card : Nat.card ↥(T₁.map π) = 2 := by
    have hpos : 0 < T₁.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hVpos : 0 < Nat.card ↥V := Nat.card_pos
    have h1 : T₁.index * Nat.card ↥T₁ = T₁.index * (Nat.card ↥(T₁.map π) * Nat.card ↥V) := by
      rw [← hcardIT, hcardI, hcardQ, hidx, hVsub]; ring
    have h2 := Nat.eq_of_mul_eq_mul_left hpos h1
    rw [hT₁card, hT₀V] at h2
    have h3 : Nat.card ↥V * 2 = Nat.card ↥V * Nat.card ↥(T₁.map π) := by rw [h2]; ring
    exact (Nat.eq_of_mul_eq_mul_left hVpos h3).symm
  have hcyc : IsCyclic ↥P := by
    have hc : Nat.card ↥P = 2 := hP₀card
    exact isCyclic_of_prime_card (p := 2) hc
  have hQs : Group.IsSolvable (↥I ⧸ V.subgroupOf I) := isSolvable_of_isCyclic_sylow_two' P hcyc
  exact Group.isSolvable_of_subgroup_quotient (V.subgroupOf I)

end S3Hyp

end CFSG.Quasithin.YS
