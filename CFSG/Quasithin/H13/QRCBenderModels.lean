module

public import CFSG.Quasithin.H13.QRCBenderCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelPointStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSuzukiOddCore
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG.Open CFSG.Blueprint CFSG.LieType.Ree CFSG.ShultStronglyClosedTI
  CFSG.GorensteinWalter CFSG.BenderSuzuki.MatrixGroups CFSG.Quasithin.SteinbergBS
open scoped LinearAlgebra.Projectivization

structure BenderData (G : Type*) [Group G] (U : Subgroup G) (n : ℕ) : Prop where
  isPGroup : IsPGroup 2 U
  not_dvd_index : ¬ 2 ∣ U.index
  stronglyEmbedded : fusionStronglyEmbedded (normalizer (U : Set G))
  isCoatom : IsCoatom (normalizer (U : Set G))
  centralizer_isPGroup : ∀ g : G, orderOf g = 2 → IsPGroup 2 (centralizer ({g} : Set G))
  sq_comm : ∀ u ∈ U, u ^ 2 = 1 → ∀ v ∈ U, u * v = v * u
  relIndex : U.relIndex (normalizer (U : Set G)) = 2 ^ n - 1

theorem BenderData.map {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    {U : Subgroup G} {n : ℕ} (h : BenderData G U n) (e : G ≃* G') :
    BenderData G' (U.map e.toMonoidHom) n where
  isPGroup := h.isPGroup.map _
  not_dvd_index := by
    rw [index_map_of_bijective e.bijective]
    exact h.not_dvd_index
  stronglyEmbedded := by
    rw [← map_equiv_normalizer_eq]
    exact h.stronglyEmbedded.map_mulEquiv e
  isCoatom := by
    rw [← map_equiv_normalizer_eq]
    exact (OrderIso.isCoatom_iff e.mapSubgroup _).2 h.isCoatom
  centralizer_isPGroup := by
    intro g hg
    have hg' : orderOf (e.symm g) = 2 :=
      (orderOf_injective e.symm.toMonoidHom e.symm.injective g).trans hg
    have hC := h.centralizer_isPGroup _ hg'
    rintro ⟨x, hx⟩
    have hx' : e.symm x ∈ centralizer ({e.symm g} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hx ⊢
      rw [← map_mul, ← map_mul, hx]
    obtain ⟨k, hk⟩ := hC ⟨_, hx'⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hk' : (e.symm x) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have : x ^ 2 ^ k = e ((e.symm x) ^ 2 ^ k) := by rw [map_pow, MulEquiv.apply_symm_apply]
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [this, hk', map_one]
  sq_comm := by
    rintro _ ⟨u, hu, rfl⟩ hu2 _ ⟨v, hv, rfl⟩
    have hu2' : u ^ 2 = 1 := by
      apply e.injective
      rw [map_pow, map_one]
      exact hu2
    change e u * e v = e v * e u
    rw [← map_mul, ← map_mul, h.sq_comm u hu hu2' v hv]
  relIndex := by
    rw [← map_equiv_normalizer_eq, relIndex_map_map, show (e.toMonoidHom).ker = ⊥ from
      (MonoidHom.ker_eq_bot_iff _).2 e.injective, sup_bot_eq, sup_bot_eq]
    exact h.relIndex

theorem normalizer_le_of_stronglyEmbedded {G : Type*} [Group G] [Finite G] {M U : Subgroup G}
    (hM : fusionStronglyEmbedded M) (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥) (hUM : U ≤ M) :
    normalizer (U : Set G) ≤ M := by
  intro g hg
  refine mem_of_le_inf_conjugate hM hU hU1 fun u hu => ⟨hUM hu, mem_conjugate_iff.2 ?_⟩
  exact hUM ((mem_normalizer_iff.1 hg u).1 hu)

theorem relIndex_eq_card_of_complement {G : Type*} [Group G] {U T B : Subgroup G}
    (hUB : U ≤ B) (hTB : T ≤ B) (hTN : T ≤ normalizer (U : Set G)) (hinf : U ⊓ T = ⊥)
    (hsup : U ⊔ T = B) : U.relIndex B = Nat.card T := by
  have hn : (U.subgroupOf B).Normal :=
    (normal_subgroupOf_iff_le_normalizer hUB).2 (hsup ▸ sup_le le_normalizer hTN)
  let φ : T →* B ⧸ U.subgroupOf B := (QuotientGroup.mk' _).comp (inclusion hTB)
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro t ht
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf] at ht
    have h1 : (t : G) ∈ U ⊓ T := ⟨ht, t.2⟩
    rw [hinf, mem_bot] at h1
    exact Subtype.ext h1
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have hb : (b : G) ∈ U ⊔ T := hsup ▸ b.2
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left U T hTN] at hb
    obtain ⟨u, hu, t, ht, hut⟩ := hb
    refine ⟨⟨t, ht⟩, ?_⟩
    change QuotientGroup.mk' _ (inclusion hTB ⟨t, ht⟩) = QuotientGroup.mk' _ b
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
    simp only [coe_mul, coe_inv, coe_inclusion]
    rw [← hut]
    have : t⁻¹ * (u * t) = t⁻¹ * u * t := by group
    rw [this]
    have h2 := (mem_normalizer_iff.1 (hTN (T.inv_mem ht)) u).1 hu
    rwa [inv_inv] at h2
  rw [relIndex, index_eq_card]
  exact (Nat.card_congr (MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).toEquiv).symm

section Linear

variable {k : Type} [Field k] [Finite k]

omit [Finite k] in
theorem psl2_normalizer_rootGroup :
    normalizer (psl2UpperUnipotentSubgroup k : Set (PSL2MatrixGroup k)) = psl2Borel k :=
  psl2UpperUnipotent_normalizer_eq_borel k

theorem benderData_psl2 {n : ℕ} (hcard : Nat.card k = 2 ^ n) :
    BenderData (PSL2MatrixGroup k) (psl2UpperUnipotentSubgroup k) n where
  isPGroup := by
    obtain ⟨S, hS⟩ := LinearModel.exists_sylow_eq_rootGroup hcard
    rw [← hS]
    exact S.isPGroup'
  not_dvd_index := by
    obtain ⟨S, hS⟩ := LinearModel.exists_sylow_eq_rootGroup hcard
    rw [← hS]
    exact S.not_dvd_index
  stronglyEmbedded := by
    rw [psl2_normalizer_rootGroup]
    exact LinearModel.psl2Borel_stronglyEmbedded hcard
  isCoatom := by
    rw [psl2_normalizer_rootGroup]
    have : MulAction.IsPreprimitive (PSL2MatrixGroup k) (ℙ k (Fin 2 → k)) :=
      MulAction.isPreprimitive_of_is_two_pretransitive (psl2_projectiveLine_two_pretransitive k)
    have : Nontrivial (ℙ k (Fin 2 → k)) :=
      ⟨⟨_, _, LinearModel.infinity_ne_zero (K := k)⟩⟩
    exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (PSL2MatrixGroup k)
      (psl2ProjectiveInfinity k)
  centralizer_isPGroup := by
    have : CharP k 2 := LinearModel.charP_two_of_card hcard
    exact fun g hg => CFSG.Walter.psl2_centralizer_isPGroup_of_charTwo hg
  sq_comm := fun u hu _ v hv => (LinearModel.rootGroup_commute hu hv).eq
  relIndex := by
    have : CharP k 2 := LinearModel.charP_two_of_card hcard
    rw [psl2_normalizer_rootGroup, relIndex_eq_card_of_complement psl2UpperUnipotent_le_borel
      LinearModel.torus_le_borel (LinearModel.torus_le_borel.trans
        (psl2_normalizer_rootGroup (k := k)).ge) LinearModel.rootGroup_inf_torus
      LinearModel.rootGroup_sup_torus, LinearModel.card_torus, hcard]

omit [Finite k] in
theorem psl2_rootGroup_comm {x y : PSL2MatrixGroup k} (hx : x ∈ psl2UpperUnipotentSubgroup k)
    (hy : y ∈ psl2UpperUnipotentSubgroup k) : x * y = y * x :=
  (LinearModel.rootGroup_commute hx hy).eq

end Linear

section Suzuki

variable {a : ℕ} {k : Type} [Field k] [Finite k]

theorem suzuki_normalizer_suzukiU
    (hK : Nat.card k = 2 ^ (2 * a + 1)) :
    normalizer (suzukiU a k : Set (suzukiGroup a k)) = suzukiB a k := by
  apply le_antisymm
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨P, hP⟩ := SuzukiModel.exists_sylow_eq_suzukiU hK
    refine normalizer_le_of_stronglyEmbedded (SuzukiModel.fusionStronglyEmbedded_suzukiB hK)
      (hP ▸ P.isPGroup') ?_ (suzukiU_le_suzukiB a k)
    intro h
    have h1 := (suzuki_unipotent_structure hK).2.1
    rw [h, card_bot] at h1
    have : 1 < (2 ^ (2 * a + 1)) ^ 2 :=
      Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
    omega
  · exact (normal_subgroupOf_iff_le_normalizer (suzukiU_le_suzukiB a k)).1
      (SuzukiModel.suzukiB_semidirect hK).1

theorem benderData_suzuki
    (ha : 1 ≤ a) (hK : Nat.card k = 2 ^ (2 * a + 1)) :
    BenderData (suzukiGroup a k) (suzukiU a k) (2 * a + 1) where
  isPGroup := by
    obtain ⟨P, hP⟩ := SuzukiModel.exists_sylow_eq_suzukiU hK
    rw [← hP]
    exact P.isPGroup'
  not_dvd_index := by
    obtain ⟨P, hP⟩ := SuzukiModel.exists_sylow_eq_suzukiU hK
    rw [← hP]
    exact P.not_dvd_index
  stronglyEmbedded := by
    rw [suzuki_normalizer_suzukiU hK]
    exact SuzukiModel.fusionStronglyEmbedded_suzukiB hK
  isCoatom := by
    obtain ⟨-, h2tr, -, -, hne, -, hB, -⟩ := SuzukiModel.suzuki_rank_one_point_structure ha hK
    rw [suzuki_normalizer_suzukiU hK, ← hB]
    have : MulAction.IsPreprimitive (suzukiGroup a k) (suzukiOmegaSub hK) :=
      MulAction.isPreprimitive_of_is_two_pretransitive h2tr
    have : Nontrivial (suzukiOmegaSub hK) :=
      ⟨⟨⟨_, suzukiInfty_mem_suzukiOmega a k⟩, ⟨_, suzukiLine_mem_suzukiOmega a k 0 0⟩,
        fun h => hne (congrArg Subtype.val h)⟩⟩
    exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive (suzukiGroup a k)
      (⟨suzukiInfty k, suzukiInfty_mem_suzukiOmega a k⟩ : suzukiOmegaSub hK)
  centralizer_isPGroup := by
    intro g hg
    obtain ⟨S, hS⟩ :=
      CFSG.ComponentClassification.UnbalancedGS.SuzukiOddCore.suzuki_involution_centralizer_sylow
        hK g hg
    rw [← hS]
    exact S.isPGroup'
  sq_comm := by
    intro u hu hu2 v hv
    by_cases hu1 : u = 1
    · rw [hu1, one_mul, mul_one]
    · have hord : orderOf u = 2 := orderOf_eq_prime hu2 hu1
      obtain ⟨w, -, rfl⟩ := (SuzukiModel.mem_suzukiB_and_orderOf_eq_two_iff hK).1
        ⟨suzukiU_le_suzukiB a k hu, hord⟩
      obtain ⟨c, d, rfl⟩ := (mem_suzukiU_iff hK).1 hv
      exact suzukiSElt_zero_commute hK w c d
  relIndex := by
    have h1 := relIndex_mul_card (suzukiU a k) (suzukiB a k)
    rw [inf_eq_left.2 (suzukiU_le_suzukiB a k), (suzuki_unipotent_structure hK).2.1,
      (suzuki_borel_structure hK).2.2.2.2.2.2.2] at h1
    rw [suzuki_normalizer_suzukiU hK]
    exact Nat.eq_of_mul_eq_mul_right (by positivity) (h1.trans (mul_comm _ _))

theorem not_three_dvd_card_suzukiGroup
    (hK : Nat.card k = 2 ^ (2 * a + 1)) :
    ¬ 3 ∣ Nat.card (suzukiGroup a k) := by
  rw [suzuki_order hK]
  have h4 : ∀ m : ℕ, 4 ^ m % 3 = 1 := fun m => by
    rw [Nat.pow_mod]
    simp
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, show (2 : ℕ) ^ 2 = 4 by norm_num, Nat.mul_mod, h4]
  have h1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by omega)
    · omega
  · have : ((2 ^ (2 * a + 1)) ^ 2 + 1) % 3 = 2 := by
      rw [Nat.add_mod, Nat.pow_mod, hq]
    omega

end Suzuki

end CFSG.Quasithin.H13.QRC
