module

public import CFSG.RankThree.PartTwo.Sec3.Sims321Action
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.PartTwo.KFacts.L34OuterThreeFixed
import CFSG.RankThree.PartTwo.Sec19.Hyp1921CentralQ
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Fixed
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Image
import CFSG.RankThree.PartTwo.Sec19.Hyp1921NotLeM
public import CFSG.RankThree.PartTwo.Sec20.OneBasics

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {A M N L : Subgroup G}

theorem Hyp1921.map_inf_eq_normalizer
    (hET : partTwoE G ⊆ partTwoT G) (h : Hyp1921 G A M N L)
    {Q : Subgroup G} (hQ : IsSylowOf 3 Q N) (hAQ : A ≤ Q) :
    ((L ⊓ M).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) =
      Subgroup.normalizer ((((Q ⊓ L).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :
          Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  obtain ⟨c, hc, hc1⟩ := h.exists_ne_one_mem_sectionCentralizer
  exact h.map_inf_eq_normalizer_of (B := Q ⊓ L) inf_le_right (h.card_inf_Q hQ)
    (h.normalizer_inf_Q_le hET hQ hAQ hc hc1) (h.not_le_M hET) h.pCoreOf_le_M

theorem Hyp1921.relIndex_inf_eq
    (hET : partTwoE G ⊆ partTwoT G) (h : Hyp1921 G A M N L) : (L ⊓ M).relIndex L = 280 := by
  obtain ⟨Q, hQ, hAQ⟩ := h.exists_isSylowOf_ge
  obtain ⟨c, hc, hc1⟩ := h.exists_ne_one_mem_sectionCentralizer
  exact h.relIndex_inf_eq_of (B := Q ⊓ L) inf_le_right (h.card_inf_Q hQ)
    (h.normalizer_inf_Q_le hET hQ hAQ hc hc1) (h.not_le_M hET) h.pCoreOf_le_M

theorem Hyp1921.mem_normalizer_of_fixed
    (hET : partTwoE G ⊆ partTwoT G) (h : Hyp1921 G A M N L)
    {Q : Subgroup G} (hQ : IsSylowOf 3 Q N) (hAQ : A ≤ Q) {X : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (L : Set G)) (hX3 : IsPGroup 3 X)
    (hXM : Subgroup.normalizer (X : Set G) ≤ M) {y : ↥L ⧸ CFSG.pCore 2 ↥L}
    (hy : ∀ (x : G) (hx : x ∈ X), Sec3.Sims321.barAut L ⟨x, hXN hx⟩ y = y) :
    y ∈ Subgroup.normalizer ((((Q ⊓ L).subgroupOf L).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :
          Set (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  rw [← h.map_inf_eq_normalizer hET hQ hAQ]
  exact mem_map_inf_of_fixed h.pCoreOf_le_M hXN hX3 hXM hy

theorem Hyp1921.isCyclic_sectionCentralizer (h : Hyp1921 G A M N L) {Q : Subgroup G}
    (hQ : IsSylowOf 3 Q N) {K : Subgroup G}
    (hK : (K : Set G) = sectionCentralizer Q L (CFSG.Open.pCoreOf 2 L)) : IsCyclic K :=
  h.isCyclic_sectionCentralizer_of h.le_normalizer
    (fun _ hx hc => h.mem_pCoreOf_of_commutator_mem hx hc) hQ (h.card_inf_Q hQ)
    (h.isElemAbelian_inf_Q hQ) (h.inf_pCoreOf_eq_bot_Q hQ) hK

theorem Hyp1921.mul_comm_of_mem (h : Hyp1921 G A M N L) {Q : Subgroup G}
    (hQ : IsSylowOf 3 Q N) (hAQ : A ≤ Q) {c : G}
    (hc : sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G)) :
    ∀ q ∈ Q, q * c = c * q := by
  obtain ⟨K, -, hK⟩ := exists_subgroup_sectionCentralizer (hQ.le.trans h.le_normalizer)
  exact h.mul_comm_of_mem_of h.le_normalizer hQ hAQ hK (h.isCyclic_sectionCentralizer hQ hK) hc
    (h.orderOf_eq_three hc)

theorem Hyp1921.card_map_inf_Q (h : Hyp1921 G A M N L) {Q : Subgroup G}
    (hQ : IsSylowOf 3 Q N) :
    Nat.card (((Q ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) = 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB3 : IsPGroup 3 (Q ⊓ L : Subgroup G) := hQ.isPGroup.to_inf_left
  have hB'card : Nat.card ((Q ⊓ L).subgroupOf L) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Q ⊓ L ≤ L)).toEquiv,
      h.card_inf_Q hQ]
  have h1 := Sec20.card_eq_card_map_mul_inf_ker (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    ((Q ⊓ L).subgroupOf L)
  have hB'3 : IsPGroup 3 ((Q ⊓ L).subgroupOf L) := hB3.comap_subtype
  rw [QuotientGroup.ker_mk', Sec20.card_inf_eq_one_of_isPGroup hB'3
    CFSG.pCore_isPGroup, mul_one, hB'card] at h1
  exact h1.symm

private theorem barAut_of_mem {L : Subgroup G} (l : L) :
    Sec3.Sims321.barAut L ⟨(l : G), Subgroup.le_normalizer l.2⟩ =
      MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥L) l) := by
  ext y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
  rw [QuotientGroup.mk'_apply, Sec3.Sims321.barAut_mk, MulAut.conj_apply]
  rfl

theorem Hyp1921.barAut_eq_one_iff (h : Hyp1921 G A M N L) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    Sec3.Sims321.barAut L ⟨x, hx⟩ = 1 ↔
      ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
  obtain ⟨φ⟩ := h.quotient_iso
  have hrho : Sec3.Sims321.rho φ ⟨x, hx⟩ = MulAut.congr
      (φ.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)))
      (Sec3.Sims321.barAut L ⟨x, hx⟩) := rfl
  rw [← Sec3.Sims321.rho_eq_one_iff φ ⟨x, hx⟩, hrho]
  exact (MulEquiv.map_eq_one_iff _).symm

private theorem eq_of_isPGroup_three_of_card_nine {X : Type*} [Group X] [Finite X]
    (hX : Nat.card X = 20160) {E S : Subgroup X} (hE : Nat.card E = 9) (hS : IsPGroup 3 S)
    (hES : E ≤ S) : S = E := by
  obtain ⟨k, hk⟩ := hS.exists_card_eq
  have hdvd : 3 ^ k ∣ 20160 := hk ▸ hX ▸ Subgroup.card_subgroup_dvd_card S
  have hk2 : k ≤ 2 := by
    by_contra hk3
    have h27 : 3 ^ 3 ∣ 20160 := (Nat.pow_dvd_pow 3 (by omega : 3 ≤ k)).trans hdvd
    norm_num at h27
  have hle : Nat.card S ≤ Nat.card E := by
    rw [hk, hE]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hES hle).symm

private theorem mul_comm_of_mem_sectionCentralizer_inf (h : Hyp1921 G A M N L)
    {Q : Subgroup G} (hQ : IsSylowOf 3 Q N) {f : G}
    (hf : f ∈ sectionCentralizer Q L (CFSG.Open.pCoreOf 2 L)) {b : G}
    (hb : b ∈ (Q ⊓ L : Subgroup G)) : f * b = b * f := by
  obtain ⟨hfQ, hfc⟩ := hf
  have hfN : f ∈ Subgroup.normalizer (L : Set G) := h.le_normalizer (hQ.le hfQ)
  have h1 : f * b * f⁻¹ * b⁻¹ ∈ (Q ⊓ L : Subgroup G) :=
    ⟨Q.mul_mem (Q.mul_mem (Q.mul_mem hfQ hb.1) (Q.inv_mem hfQ)) (Q.inv_mem hb.1),
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp hfN b).mp hb.2) (L.inv_mem hb.2)⟩
  have h2 : f * b * f⁻¹ * b⁻¹ = 1 := by
    have h3 : f * b * f⁻¹ * b⁻¹ ∈ (Q ⊓ L : Subgroup G) ⊓ CFSG.Open.pCoreOf 2 L :=
      ⟨h1, hfc b hb.2⟩
    rw [h.inf_pCoreOf_eq_bot_Q hQ, Subgroup.mem_bot] at h3
    exact h3
  calc f * b = (f * b * f⁻¹ * b⁻¹)⁻¹⁻¹ * (b * f) := by group
    _ = b * f := by rw [h2, inv_one, inv_one, one_mul]

private theorem mem_zpowers_of_isCyclic_of_pow_three {K : Subgroup G} (hK : IsCyclic K) {c : G}
    (hcK : c ∈ K) (hc3 : orderOf c = 3) {x : G} (hxK : x ∈ K) (hx3 : x ^ 3 = 1) :
    x ∈ Subgroup.zpowers c := by
  by_cases hx1 : x = 1
  · rw [hx1]
    exact Subgroup.one_mem _
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hc'3 : orderOf (⟨c, hcK⟩ : K) = 3 := by rw [Subgroup.orderOf_mk c hcK, hc3]
  have hx'3 : orderOf (⟨x, hxK⟩ : K) = 3 := by rw [Subgroup.orderOf_mk x hxK, hxo]
  have heq : Subgroup.zpowers (⟨c, hcK⟩ : K) = Subgroup.zpowers (⟨x, hxK⟩ : K) :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hc'3, hx'3])
  have hx'mem : (⟨x, hxK⟩ : K) ∈ Subgroup.zpowers (⟨c, hcK⟩ : K) := by
    rw [heq]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx'mem
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem zpowers_le_normalizer_zpowers_of_commute {c x : G} (hcomm : x * c = c * x) :
    Subgroup.zpowers x ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
  refine Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  exact (Commute.zpow_left (show Commute c x from hcomm.symm) i).eq

theorem Hyp1921.mem_sup_of_inner (h : Hyp1921 G A M N L) {Q : Subgroup G}
    (hQ : IsSylowOf 3 Q N) (hAQ : A ≤ Q) {c : G}
    (hc : sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G))
    {q : G} (hqQ : q ∈ Q) (hqN : q ∈ Subgroup.normalizer (L : Set G)) (hq3 : q ^ 3 = 1)
    (hinn : Sec3.Sims321.barAut L ⟨q, hqN⟩ ∈
      (MulAut.conj : (↥L ⧸ CFSG.pCore 2 ↥L) →* MulAut (↥L ⧸ CFSG.pCore 2 ↥L)).range) :
    q ∈ Subgroup.zpowers c ⊔ (Q ⊓ L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ⟩ := h.quotient_iso
  have hQN : Q ≤ Subgroup.normalizer (L : Set G) := hQ.le.trans h.le_normalizer
  obtain ⟨z, hz⟩ := hinn
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  set B' : Subgroup L := (Q ⊓ L).subgroupOf L with hB'
  set Bb := B'.map π with hBb
  have hBb9 : Nat.card Bb = 9 := h.card_map_inf_Q hQ
  have hX : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 20160 := by
    rw [Nat.card_congr φ.toEquiv, KFacts.L34.card_projSL]
  have hznorm : ∀ n ∈ Bb, z * n * z⁻¹ ∈ Bb := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 : z * π b * z⁻¹ = Sec3.Sims321.barAut L ⟨q, hqN⟩ (π b) := by
      rw [← hz, MulAut.conj_apply]
    rw [h1, hπ, QuotientGroup.mk'_apply, Sec3.Sims321.barAut_mk]
    have hb' := Subgroup.mem_subgroupOf.mp hb
    refine ⟨⟨q * b * q⁻¹, (Subgroup.mem_normalizer_iff.mp hqN b).mp b.2⟩, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr ⟨Q.mul_mem (Q.mul_mem hqQ hb'.1) (Q.inv_mem hqQ),
      (Subgroup.mem_normalizer_iff.mp hqN b).mp b.2⟩
  have hz3 : z ^ 3 = 1 := by
    have h1 : (MulAut.conj z) ^ 3 = 1 := by
      have e : (⟨q, hqN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hq3)
      rw [show (MulAut.conj z : MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) =
        Sec3.Sims321.barAut L ⟨q, hqN⟩ from hz, ← map_pow, e, map_one]
    have h2 : MulAut.conj (z ^ 3) = 1 := by rw [map_pow]; exact h1
    have h3 : z ^ 3 ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun σ : MulAut (↥L ⧸ CFSG.pCore 2 ↥L) => σ g) h2
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * z ^ 3 = (z ^ 3 * g * (z ^ 3)⁻¹) * z ^ 3 := by rw [this]
        _ = z ^ 3 * g := by group
    rw [h.center_quot_eq_bot, Subgroup.mem_bot] at h3
    exact h3
  have hzB : z ∈ Bb := by
    have hBb3 : IsPGroup 3 Bb := IsPGroup.of_card (n := 2) (by rw [hBb9]; norm_num)
    have hz3' : IsPGroup 3 (Subgroup.zpowers z) :=
      (CFSG.Open.isElemAbelian_zpowers hz3).isPGroup
    have hznormB : Subgroup.zpowers z ≤ Subgroup.normalizer (Bb : Set (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_fintype hznorm)
    have hS3 : IsPGroup 3 (Bb ⊔ Subgroup.zpowers z : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      hBb3.to_sup_of_normal_left' hz3' hznormB
    have := eq_of_isPGroup_three_of_card_nine hX hBb9 hS3 le_sup_left
    rw [← this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  obtain ⟨b', hb', hbz⟩ := Subgroup.mem_map.mp hzB
  have hbQL : (b' : G) ∈ (Q ⊓ L : Subgroup G) := Subgroup.mem_subgroupOf.mp hb'
  have hq'Q : q * (b' : G)⁻¹ ∈ Q := Q.mul_mem hqQ (Q.inv_mem hbQL.1)
  have hq'N : q * (b' : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) := hQN hq'Q
  have hq'1 : Sec3.Sims321.barAut L ⟨q * (b' : G)⁻¹, hq'N⟩ = 1 := by
    have e : (⟨q * (b' : G)⁻¹, hq'N⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨q, hqN⟩ * (⟨(b' : G), Subgroup.le_normalizer b'.2⟩ :
          Subgroup.normalizer (L : Set G))⁻¹ := rfl
    rw [e, map_mul, map_inv, barAut_of_mem b', hbz, ← show (MulAut.conj z : MulAut _) =
      Sec3.Sims321.barAut L ⟨q, hqN⟩ from hz, mul_inv_cancel]
  have hq'S : q * (b' : G)⁻¹ ∈ sectionCentralizer Q L (CFSG.Open.pCoreOf 2 L) :=
    ⟨hq'Q, (h.barAut_eq_one_iff hq'N).mp hq'1⟩
  have hcomm : q * (b' : G)⁻¹ * b' = b' * (q * (b' : G)⁻¹) :=
    mul_comm_of_mem_sectionCentralizer_inf h hQ hq'S hbQL
  have hb3 : (b' : G) ^ 3 = 1 := (h.isElemAbelian_inf_Q hQ).2 _ hbQL
  have hq'3 : (q * (b' : G)⁻¹) ^ 3 = 1 := by
    have hq : q = q * (b' : G)⁻¹ * b' := by group
    have h1 : q ^ 3 = (q * (b' : G)⁻¹) ^ 3 * (b' : G) ^ 3 := by
      conv_lhs => rw [hq]
      exact (Commute.mul_pow (hcomm : Commute (q * (b' : G)⁻¹) b') 3)
    rw [hb3, mul_one, hq3] at h1
    exact h1.symm
  obtain ⟨K, -, hK⟩ := exists_subgroup_sectionCentralizer hQN
  have hcyc : IsCyclic K := h.isCyclic_sectionCentralizer hQ hK
  have hcmem : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) := by
    rw [hc]; exact Subgroup.mem_zpowers c
  have hcK : c ∈ K := by
    rw [← SetLike.mem_coe, hK]
    exact ⟨hAQ hcmem.1, hcmem.2⟩
  have hq'K : q * (b' : G)⁻¹ ∈ K := by
    rw [← SetLike.mem_coe, hK]; exact hq'S
  have hmem := mem_zpowers_of_isCyclic_of_pow_three hcyc hcK (h.orderOf_eq_three hc) hq'K hq'3
  have := Subgroup.mul_mem_sup hmem hbQL
  simpa using this

open scoped Pointwise in
theorem Hyp1921.barAut_mem_range
    (hET : partTwoE G ⊆ partTwoT G) (h : Hyp1921 G A M N L)
    {Q : Subgroup G} (hQ : IsSylowOf 3 Q N) (hAQ : A ≤ Q) {c : G}
    (hc : sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G))
    {q : G} (hqQ : q ∈ Q) (hqN : q ∈ Subgroup.normalizer (L : Set G)) (hq3 : q ^ 3 = 1)
    (hqM : Subgroup.normalizer ((Subgroup.zpowers c ⊔ Subgroup.zpowers q : Subgroup G) :
      Set G) ≤ M) :
    Sec3.Sims321.barAut L ⟨q, hqN⟩ ∈
      (MulAut.conj : (↥L ⧸ CFSG.pCore 2 ↥L) →* MulAut (↥L ⧸ CFSG.pCore 2 ↥L)).range := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hout
  obtain ⟨φ⟩ := h.quotient_iso
  set α := Sec3.Sims321.barAut L ⟨q, hqN⟩ with hα
  have hα3 : α ^ 3 = 1 := by
    have e : (⟨q, hqN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hq3)
    rw [hα, ← map_pow, e, map_one]
  have hα1 : α ≠ 1 := fun h1 => hout ⟨1, by rw [map_one, h1]⟩
  have hαord : orderOf α = 3 := orderOf_eq_prime hα3 hα1
  obtain ⟨y, hy57, hαy⟩ := KFacts.L34.exists_orderOf_five_or_seven_fixed_projSL φ hαord hout
  have hcmem : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) := by
    rw [hc]; exact Subgroup.mem_zpowers c
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := h.le_normalizer (h.le_N hcmem.1)
  have hc3 : c ^ 3 = 1 := by simpa using h.isE27.1.2 c hcmem.1
  have hbc1 : Sec3.Sims321.barAut L ⟨c, hcN⟩ = 1 := (h.barAut_eq_one_iff hcN).mpr hcmem.2
  have hle : Subgroup.zpowers q ≤ Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) :=
    zpowers_le_normalizer_zpowers_of_commute (h.mul_comm_of_mem hQ hAQ hc q hqQ)
  set X : Subgroup G := Subgroup.zpowers c ⊔ Subgroup.zpowers q with hX
  have hXN : X ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hcN) (Subgroup.zpowers_le.mpr hqN)
  have hX3 : IsPGroup 3 X :=
    (CFSG.Open.isElemAbelian_zpowers hc3).isPGroup.to_sup_of_normal_left'
      (CFSG.Open.isElemAbelian_zpowers hq3).isPGroup hle
  have hfix : ∀ (x : G) (hx : x ∈ X), Sec3.Sims321.barAut L ⟨x, hXN hx⟩ y = y := by
    intro x hx
    have hx' : x ∈ ((Subgroup.zpowers c : Set G) * (Subgroup.zpowers q : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers c)
        (Subgroup.zpowers q) hle]
      exact hx
    obtain ⟨u, hu, v, hv, rfl⟩ := hx'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have e : (⟨c ^ i * q ^ j, hXN hx⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨c, hcN⟩ ^ i * ⟨q, hqN⟩ ^ j := Subtype.ext (by simp)
    have hstab : α ^ j ∈ MulAction.stabilizer (MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) y :=
      Subgroup.zpow_mem _ (MulAction.mem_stabilizer_iff.mpr hαy) j
    have hstab' := MulAction.mem_stabilizer_iff.mp hstab
    rw [e, map_mul, map_zpow, map_zpow, hbc1, one_zpow, one_mul]
    exact hstab'
  have hyN := h.mem_normalizer_of_fixed hET hQ hAQ hXN hX3 hqM hfix
  have h72 := KFacts.L34Max.card_normalizer_of_card_eq_nine φ (h.card_map_inf_Q hQ)
  have hdvd : orderOf y ∣ 72 := h72 ▸ Subgroup.orderOf_dvd_natCard _ hyN
  rcases hy57 with h5 | h7
  · rw [h5] at hdvd; norm_num at hdvd
  · rw [h7] at hdvd; norm_num at hdvd

end CFSG.RankThree.PartTwo.Late
