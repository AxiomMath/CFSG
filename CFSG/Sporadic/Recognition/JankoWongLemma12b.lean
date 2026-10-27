module

public import CFSG.Sporadic.Recognition.JankoWongLemma13
public import CFSG.Sporadic.Recognition.JankoWongPSL
public import CFSG.Sporadic.Recognition.JankoWongQuotient
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCoreQuotient

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

theorem le_oddCore_of_normal_odd {Q : Type*} [Group Q] (N : Subgroup Q) (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N ≤ CFSG.oddCore Q := by
  unfold CFSG.oddCore
  exact le_sSup ⟨hN, hodd⟩

@[expose] def conjEquiv {M : Type*} [Group M] (K : Subgroup M) (n : M)
    (hn : ∀ y ∈ K, n * y * n⁻¹ ∈ K) (hn' : ∀ y ∈ K, n⁻¹ * y * n ∈ K) : K ≃* K where
  toFun y := ⟨n * y * n⁻¹, hn y y.2⟩
  invFun y := ⟨n⁻¹ * y * n, hn' y y.2⟩
  left_inv y := Subtype.ext (by show n⁻¹ * (n * y * n⁻¹) * n = y; group)
  right_inv y := Subtype.ext (by show n * (n⁻¹ * y * n) * n⁻¹ = y; group)
  map_mul' x y := Subtype.ext (by
    show n * (x * y) * n⁻¹ = n * x * n⁻¹ * (n * y * n⁻¹); group)

theorem oddCore_conj_mem {M : Type*} [Group M] [Finite M] (K : Subgroup M) (n : M)
    (hn : ∀ y ∈ K, n * y * n⁻¹ ∈ K) (hn' : ∀ y ∈ K, n⁻¹ * y * n ∈ K) :
    ∀ y ∈ (CFSG.oddCore K).map K.subtype, n * y * n⁻¹ ∈ (CFSG.oddCore K).map K.subtype := by
  rintro _ ⟨o, ho, rfl⟩
  let e := conjEquiv K n hn hn'
  have hN : ((CFSG.oddCore K).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance _ e.surjective
  have hodd : Odd (Nat.card ((CFSG.oddCore K).map e.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact CFSG.ABGDGroups.odd_card_oddCore K
  have hle := le_oddCore_of_normal_odd _ hN hodd
  exact ⟨e o, hle ⟨o, ho, rfl⟩, rfl⟩

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} (c : Ctx S)

@[expose] def zC : ↥c.Cg := ⟨S.z, c.z_mem_cg⟩

@[expose] def tC : ↥c.Cg := ⟨(c.t : G), c.tC_mem⟩

@[expose] def sC : ↥c.Cg := ⟨c.s, c.mem_cg_iff.mpr (by group)⟩

theorem zC_sq : c.zC ^ 2 = 1 := Subtype.ext (by simpa [zC] using z_sq (S := S))

theorem zC_ne_one : c.zC ≠ 1 := fun e => z_ne_one' (S := S) (congrArg Subtype.val e)

theorem oddCore_Cg_map : (CFSG.oddCore ↥c.Cg).map c.Cg.subtype = c.OG := by
  apply le_antisymm
  · refine c.le_OG_of_odd_normal ?_ ?_ ?_
    · rintro _ ⟨y, -, rfl⟩
      exact c.cg_le_ng y.2
    · intro n hn y hy
      exact oddCore_conj_mem c.Cg n (fun y hy => c.conj_mem_Cg hn hy) (fun y hy => by
        have := c.conj_mem_Cg (c.Ng.inv_mem hn) hy
        simpa using this) y hy
    · rw [Subgroup.card_map_of_injective c.Cg.subtype_injective]
      exact CFSG.ABGDGroups.odd_card_oddCore _
  · intro y hy
    have hyC : y ∈ c.Cg := c.OG_le_Cg hy
    refine ⟨⟨y, hyC⟩, ?_, rfl⟩
    have hn : (c.OG.subgroupOf c.Cg).Normal := ⟨fun n hn g =>
      Subgroup.mem_subgroupOf.mpr
        (c.OG_normalized g (c.cg_le_ng g.2) n (Subgroup.mem_subgroupOf.mp hn))⟩
    have hodd : Odd (Nat.card (c.OG.subgroupOf c.Cg)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.OG_le_Cg).toEquiv]
      exact c.odd_card_OG
    exact le_oddCore_of_normal_odd _ hn hodd (Subgroup.mem_subgroupOf.mpr hy)

theorem card_oddCore_Cg : Nat.card (CFSG.oddCore ↥c.Cg) = Nat.card c.OG := by
  rw [← c.oddCore_Cg_map, Subgroup.card_map_of_injective c.Cg.subtype_injective]

theorem h4_Cg : 2 ^ 2 ∣ Nat.card c.Cg ∧ ¬ 2 ^ 3 ∣ Nat.card c.Cg := by
  have hf := c.card_Cg_factorization_two
  have hne0 : Nat.card c.Cg ≠ 0 := Nat.card_pos.ne'
  constructor
  · exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne0).mpr (by omega)
  · intro h
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne0).mp h
    omega

theorem card_Cg_of_hasNormalPComplement (h81 : Nat.card c.OG = 81)
    (hN : CFSG.HasNormalPComplement 2 ↥c.Cg) : Nat.card c.Cg = 324 := by
  obtain ⟨XG, hXGO, -, hCcard, hodd_mem⟩ := c.exists_odd_complement hN
  have hOX : c.OG ≤ XG := fun y hy => by
    refine hodd_mem y (c.OG_le_Cg hy) ?_
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp c.isPGroup_three_OG ⟨y, hy⟩
    have : orderOf y = 3 ^ m := by rw [← hm, ← Subgroup.orderOf_coe]
    rw [this]
    exact Odd.pow (by decide)
  have hXG : XG = c.OG := le_antisymm hXGO hOX
  rw [hCcard, hXG, h81]

theorem card_oddCore_inf_centralizer_zC (h81 : Nat.card c.OG = 81) :
    Nat.card (CFSG.oddCore ↥c.Cg ⊓ centralizer ({c.zC} : Set ↥c.Cg) : Subgroup ↥c.Cg) = 9 := by
  have hmap : (CFSG.oddCore ↥c.Cg ⊓ centralizer ({c.zC} : Set ↥c.Cg) : Subgroup ↥c.Cg).map
      c.Cg.subtype = c.CO S.z := by
    ext y
    constructor
    · rintro ⟨y', ⟨hO, hz⟩, rfl⟩
      refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      · rw [← c.oddCore_Cg_map]
        exact ⟨y', hO, rfl⟩
      · exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hz)
    · rintro ⟨hyO, hyz⟩
      rw [← c.oddCore_Cg_map] at hyO
      obtain ⟨y', hy', rfl⟩ := hyO
      refine ⟨y', ⟨hy', Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)⟩, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mp hyz
  rw [← Subgroup.card_map_of_injective c.Cg.subtype_injective, hmap]
  exact (c.card_CO_z_t h81).1

theorem card_centralizer_zC : Nat.card (centralizer ({c.zC} : Set ↥c.Cg)) = 36 := by
  rw [card_centralizer_subtype c.zC]
  exact S.card_inf_centralizer_involution c.x_cube c.x_type (z_sq (S := S))
    (z_ne_one' (S := S)) c.z_comm_s

theorem card_Cg_of_not_hasNormalPComplement
    (h81 : Nat.card c.OG = 81) (hN : ¬ CFSG.HasNormalPComplement 2 ↥c.Cg) :
    Nat.card c.Cg = 972 := by
  have hz2 := c.zC_sq
  have ht2 : c.tC ^ 2 = 1 := Subtype.ext (by simpa [tC] using c.tG_sq')
  have hzt : c.zC * c.tC = c.tC * c.zC := Subtype.ext c.t_comm_z.symm
  have ht1 : c.tC ≠ 1 := fun e => c.tG_ne_one (congrArg Subtype.val e)
  have hne : c.zC ≠ c.tC := fun e => c.t_ne_z (Subtype.ext (congrArg Subtype.val e).symm)
  have hK3 := hasDihedralSylowTwo_quotient_oddCore hz2 ht2 hzt c.zC_ne_one ht1 hne c.h4_Cg
  have hK2 := not_hasNormalPComplement_quotient_oddCore hN
  have hKO : CFSG.oddCore (↥c.Cg ⧸ CFSG.oddCore ↥c.Cg) = ⊥ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_quotient_eq_bot
  have hu2 : (QuotientGroup.mk c.zC : ↥c.Cg ⧸ CFSG.oddCore ↥c.Cg) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, hz2, QuotientGroup.mk_one]
  have hu1 : (QuotientGroup.mk c.zC : ↥c.Cg ⧸ CFSG.oddCore ↥c.Cg) ≠ 1 := by
    intro e
    have hmem : c.zC ∈ CFSG.oddCore ↥c.Cg := (QuotientGroup.eq_one_iff _).mp e
    have h1 : orderOf (⟨c.zC, hmem⟩ : CFSG.oddCore ↥c.Cg) ∣ Nat.card (CFSG.oddCore ↥c.Cg) :=
      orderOf_dvd_natCard _
    have hord : orderOf c.zC = 2 := orderOf_eq_prime hz2 c.zC_ne_one
    rw [Subgroup.orderOf_mk, hord] at h1
    have hodd : Odd (Nat.card (CFSG.oddCore ↥c.Cg)) := CFSG.ABGDGroups.odd_card_oddCore _
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h1)
  have hcu : Nat.card (centralizer ({(QuotientGroup.mk c.zC :
      ↥c.Cg ⧸ CFSG.oddCore ↥c.Cg)} : Set (↥c.Cg ⧸ CFSG.oddCore ↥c.Cg))) = 4 := by
    have h := card_centralizer_mk_oddCore_of_sq hz2
    rw [c.card_oddCore_inf_centralizer_zC h81, c.card_centralizer_zC] at h
    omega
  rcases card_eq_of_psl_step_four hK3.1 hK3.2 hK2 hKO hu2 hu1 hcu with h12 | ⟨h60, hsimp⟩
  · have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥c.Cg)
    rw [c.card_oddCore_Cg, h81, h12] at h
    omega
  · exfalso
    have hsO : c.sC ∈ CFSG.oddCore ↥c.Cg := by
      have : c.s ∈ (CFSG.oddCore ↥c.Cg).map c.Cg.subtype := by
        rw [c.oddCore_Cg_map]
        exact c.zpowers_le_OG (Subgroup.mem_zpowers c.s)
      obtain ⟨o, ho, hoe⟩ := this
      have : o = c.sC := Subtype.ext hoe
      rwa [this] at ho
    refine false_of_simple_sixty_quotient (O := CFSG.oddCore ↥c.Cg)
      (by rw [c.card_oddCore_Cg, h81]) hsO (fun e => c.s_ne_one (congrArg Subtype.val e))
      (fun g => ?_) h60 hsimp hz2 ?_
    · exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
    · by_contra hcon
      push Not at hcon
      have hle : c.OG ≤ c.CO S.z := fun y hy => by
        refine ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        rw [← c.oddCore_Cg_map] at hy
        obtain ⟨o, ho, rfl⟩ := hy
        exact congrArg Subtype.val (hcon o ho).symm
      have := Subgroup.card_le_of_le hle
      rw [h81, (c.card_CO_z_t h81).1] at this
      omega

theorem card_Cg_cases :
    (CFSG.HasNormalPComplement 2 ↥c.Cg ∧ Nat.card c.Cg = 324) ∨
      (¬ CFSG.HasNormalPComplement 2 ↥c.Cg ∧ Nat.card c.Cg = 972) := by
  have h81 := c.card_OG_eq_81
  by_cases hN : CFSG.HasNormalPComplement 2 ↥c.Cg
  · exact Or.inl ⟨hN, c.card_Cg_of_hasNormalPComplement h81 hN⟩
  · exact Or.inr ⟨hN, c.card_Cg_of_not_hasNormalPComplement h81 hN⟩

end Ctx

end Setup

end CFSG.Sporadic.Recognition.JankoWong
