module

public import CFSG.Sporadic.Recognition.JankoWongLemma12b

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} (c : Ctx S)

@[expose] def CP : Subgroup G := centralizer (c.PG : Set G)

theorem mem_CP_iff {y : G} : y ∈ c.CP ↔ ∀ p ∈ c.PG, p * y = y * p :=
  Subgroup.mem_centralizer_iff

theorem a_mem_PG : (c.a : G) ∈ c.PG := ⟨c.a, c.haP, rfl⟩

theorem CP_le_Cg : c.CP ≤ c.Cg := fun y hy => c.mem_cg_iff.mpr (by
  have h := (c.mem_CP_iff.mp hy) c.s c.s_mem_PG
  calc y * c.s * y⁻¹ = (c.s * y) * y⁻¹ := by rw [h]
    _ = c.s := by group)

theorem OG_le_CP (h81 : Nat.card c.OG = 81) : c.OG ≤ c.CP := fun y hy =>
  c.mem_CP_iff.mpr (fun p hp => (c.OG_comm_PG h81 p hp y hy).symm)

theorem z_mem_CP : S.z ∈ c.CP := c.mem_CP_iff.mpr (by
  rintro _ ⟨p, hp, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp p.2)

theorem t_not_mem_CP : (c.t : G) ∉ c.CP := fun h =>
  c.t_not_comm_a (c.mem_CP_iff.mp h _ c.a_mem_PG)

theorem not_four_dvd_card_CP (h81 : Nat.card c.OG = 81) : ¬ 4 ∣ Nat.card c.CP := by
  intro h4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let z' : ↥c.CP := ⟨S.z, c.z_mem_CP⟩
  have hz'2 : z' ^ 2 = 1 := Subtype.ext (by simpa [z'] using z_sq (S := S))
  have hz'1 : z' ≠ 1 := fun e => z_ne_one' (S := S) (congrArg Subtype.val e)
  have hz'o : orderOf z' = 2 := orderOf_eq_prime hz'2 hz'1
  have hzp : IsPGroup 2 (zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'o]; norm_num)
  obtain ⟨T, hT⟩ := hzp.exists_le_sylow
  have hTcard : Nat.card T = 4 := by
    rw [T.card_eq_multiplicity]
    have hne : Nat.card c.CP ≠ 0 := Nat.card_pos.ne'
    have hle : (Nat.card c.CP).factorization 2 ≤ (Nat.card c.Cg).factorization 2 :=
      (Nat.factorization_le_iff_dvd hne Nat.card_pos.ne').mpr
        (Subgroup.card_dvd_of_le c.CP_le_Cg) 2
    have hge : 2 ≤ (Nat.card c.CP).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp (by simpa using h4)
    have h2 := c.card_Cg_factorization_two
    have : (Nat.card c.CP).factorization 2 = 2 := by omega
    rw [this]
    norm_num
  have hTab : IsMulCommutative ↥(T : Subgroup ↥c.CP) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := ↥(T : Subgroup ↥c.CP))
      (by rw [hTcard]; norm_num)
  have hz'T : z' ∈ (T : Subgroup ↥c.CP) := hT (Subgroup.mem_zpowers z')
  set TG : Subgroup G := (T : Subgroup ↥c.CP).map c.CP.subtype with hTG
  have hTGcard : Nat.card TG = 4 := by
    rw [hTG, Subgroup.card_map_of_injective c.CP.subtype_injective]
    exact hTcard
  have hTGz : TG ≤ centralizer ({S.z} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have := hTab.is_comm.comm ⟨y, hy⟩ ⟨z', hz'T⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg (fun w : T => ((w : c.CP) : G))
      this)
  have hTGCP : TG ≤ c.CP := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hTGC : TG ≤ c.Cg := hTGCP.trans c.CP_le_Cg
  have hPGC : c.PG ≤ c.Cg ⊓ centralizer ({S.z} : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨c.mem_cg_iff.mpr ?_, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp p.2)⟩
    have h := c.P_comm_s hp
    calc (p : G) * c.s * (p : G)⁻¹ = c.s * (p : G) * (p : G)⁻¹ := by rw [h]
      _ = c.s := by group
  have hCH : Nat.card ↥(c.Cg ⊓ centralizer ({S.z} : Set G)) = 36 :=
    S.card_inf_centralizer_involution c.x_cube c.x_type (z_sq (S := S)) (z_ne_one' (S := S))
      c.z_comm_s
  have hsup : c.PG ⊔ TG ≤ c.Cg ⊓ centralizer ({S.z} : Set G) :=
    sup_le hPGC (le_inf hTGC hTGz)
  have h9 : 9 ∣ Nat.card ↥(c.PG ⊔ TG) := by
    rw [← c.card_PG]; exact Subgroup.card_dvd_of_le le_sup_left
  have h4' : 4 ∣ Nat.card ↥(c.PG ⊔ TG) := by
    rw [← hTGcard]; exact Subgroup.card_dvd_of_le le_sup_right
  have h36 : 36 ∣ Nat.card ↥(c.PG ⊔ TG) :=
    (show Nat.Coprime 9 4 by norm_num).mul_dvd_of_dvd_of_dvd h9 h4'
  have hsupcard : Nat.card ↥(c.PG ⊔ TG) = 36 := by
    have h1 := Subgroup.card_dvd_of_le hsup
    rw [hCH] at h1
    exact Nat.dvd_antisymm h1 h36
  have hsupeq : c.PG ⊔ TG = c.Cg ⊓ centralizer ({S.z} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hsup (by rw [hCH, hsupcard])
  have htmem : (c.t : G) ∈ c.PG ⊔ TG := by
    rw [hsupeq]
    exact ⟨c.tC_mem, Subgroup.mem_centralizer_singleton_iff.mpr c.t_comm_z⟩
  have hPGa : c.PG ⊔ TG ≤ centralizer ({(c.a : G)} : Set G) := by
    refine sup_le ?_ ?_
    · intro p hp
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (c.OG_comm_PG h81 _ c.a_mem_PG p (c.PG_le_OG h81 hp))
    · intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((c.mem_CP_iff.mp (hTGCP hy) _ c.a_mem_PG).symm)
  exact c.t_not_comm_a (Subgroup.mem_centralizer_singleton_iff.mp (hPGa htmem)).symm

theorem OG_sup_z_le_CP (h81 : Nat.card c.OG = 81) : c.OG ⊔ zpowers S.z ≤ c.CP :=
  sup_le (c.OG_le_CP h81) (by rw [Subgroup.zpowers_le]; exact c.z_mem_CP)

theorem card_dvd_OG_sup_z (h81 : Nat.card c.OG = 81) :
    162 ∣ Nat.card ↥(c.OG ⊔ zpowers S.z) := by
  have h81d : 81 ∣ Nat.card ↥(c.OG ⊔ zpowers S.z) := by
    rw [← h81]; exact Subgroup.card_dvd_of_le le_sup_left
  have h2d : 2 ∣ Nat.card ↥(c.OG ⊔ zpowers S.z) := by
    have := Subgroup.card_dvd_of_le (le_sup_right : zpowers S.z ≤ c.OG ⊔ zpowers S.z)
    rwa [Nat.card_zpowers, S.order_z] at this
  exact (show Nat.Coprime 81 2 by norm_num).mul_dvd_of_dvd_of_dvd h81d h2d

theorem false_of_index_two_CP (hN : ¬ CFSG.HasNormalPComplement 2 ↥c.Cg)
    (hidx : (c.CP.subgroupOf c.Cg).index = 2) : False := by
  have hn : (c.CP.subgroupOf c.Cg).Normal := Subgroup.normal_of_index_eq_two hidx
  obtain ⟨x, hx⟩ := c.exists_conj_z_of_not_hasNormalPComplement hN
  have hz : c.zC ∈ c.CP.subgroupOf c.Cg := Subgroup.mem_subgroupOf.mpr c.z_mem_CP
  have hmem : (x : G) * S.z * (x : G)⁻¹ ∈ c.CP :=
    Subgroup.mem_subgroupOf.mp (hn.conj_mem _ hz x)
  rcases hx with hx | hx
  · rw [hx] at hmem
    exact c.t_not_mem_CP hmem
  · rw [hx] at hmem
    apply c.t_not_mem_CP
    have := c.CP.mul_mem (c.CP.inv_mem c.z_mem_CP) hmem
    simpa using this

theorem card_CP :
    Nat.card c.CP = 162 := by
  have h81 := c.card_OG_eq_81
  have hdvd162 : 162 ∣ Nat.card c.CP :=
    (c.card_dvd_OG_sup_z h81).trans (Subgroup.card_dvd_of_le (c.OG_sup_z_le_CP h81))
  have hdvdCg : Nat.card c.CP ∣ Nat.card c.Cg := Subgroup.card_dvd_of_le c.CP_le_Cg
  have hn4 := c.not_four_dvd_card_CP h81
  have hpos : 0 < Nat.card c.CP := Nat.card_pos
  obtain ⟨m, hm⟩ := hdvd162
  rw [hm] at hdvdCg hn4 hpos ⊢
  rcases c.card_Cg_cases with ⟨-, hC⟩ | ⟨hN, hC⟩
  · rw [hC] at hdvdCg
    have hm_le : m ≤ 2 := by
      have := Nat.le_of_dvd (by norm_num) hdvdCg
      omega
    interval_cases m <;> omega
  · rw [hC] at hdvdCg
    have hm_le : m ≤ 6 := by
      have := Nat.le_of_dvd (by norm_num) hdvdCg
      omega
    interval_cases m
    · omega
    · rfl
    · omega
    · exfalso
      refine c.false_of_index_two_CP hN ?_
      have h1 := Subgroup.card_mul_index (c.CP.subgroupOf c.Cg)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.CP_le_Cg).toEquiv, hm, hC] at h1
      omega
    · omega
    · omega
    · omega

theorem CP_eq :
    c.CP = c.OG ⊔ zpowers S.z := by
  have h81 := c.card_OG_eq_81
  refine (Subgroup.eq_of_le_of_card_ge (c.OG_sup_z_le_CP h81) ?_).symm
  have hpos : 0 < Nat.card ↥(c.OG ⊔ zpowers S.z) := Nat.card_pos
  have := Nat.le_of_dvd hpos (c.card_dvd_OG_sup_z h81)
  rw [c.card_CP]
  exact this

theorem index_OG_CP :
    (c.OG.subgroupOf c.CP).index = 2 := by
  have h81 := c.card_OG_eq_81
  have h1 := Subgroup.card_mul_index (c.OG.subgroupOf c.CP)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (c.OG_le_CP h81)).toEquiv, h81,
    c.card_CP] at h1
  omega

theorem mem_OG_of_odd_order
    {y : G} (hy : y ∈ c.CP) (hodd : Odd (orderOf y)) : y ∈ c.OG := by
  have hsq : (⟨y, hy⟩ : ↥c.CP) * ⟨y, hy⟩ ∈ c.OG.subgroupOf c.CP :=
    Subgroup.mul_self_mem_of_index_two c.index_OG_CP _
  have hsq' : y * y ∈ c.OG := Subgroup.mem_subgroupOf.mp hsq
  obtain ⟨k, hk⟩ := hodd
  have h1 : y ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
  have e : (y * y) ^ (k + 1) = y := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, h1, one_mul]
  rw [← e]
  exact c.OG.pow_mem hsq' (k + 1)

theorem OG_normalized_of_normalizes_PG
    {g : G} (hg : g ∈ normalizer (c.PG : Set G)) : ∀ y ∈ c.OG, g * y * g⁻¹ ∈ c.OG := by
  have h81 := c.card_OG_eq_81
  intro y hy
  have hyCP : y ∈ c.CP := c.OG_le_CP h81 hy
  have hconj : g * y * g⁻¹ ∈ c.CP := by
    rw [c.mem_CP_iff]
    intro p hp
    have hginv : g⁻¹ ∈ normalizer (c.PG : Set G) := (normalizer (c.PG : Set G)).inv_mem hg
    have hp' : g⁻¹ * p * g ∈ c.PG := by
      have := (Subgroup.mem_normalizer_iff.mp hginv p).mp hp
      simpa using this
    have h1 := c.mem_CP_iff.mp hyCP _ hp'
    calc p * (g * y * g⁻¹) = g * ((g⁻¹ * p * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * p * g)) * g⁻¹ := by rw [h1]
      _ = g * y * g⁻¹ * p := by group
  refine c.mem_OG_of_odd_order hconj ?_
  have hc : orderOf (g * y * g⁻¹) = orderOf y := by
    have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
    exact h
  rw [hc]
  have h2 : orderOf (⟨y, hy⟩ : c.OG) ∣ Nat.card c.OG := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at h2
  exact Odd.of_dvd_nat c.odd_card_OG h2

end Ctx

end Setup

end CFSG.Sporadic.Recognition.JankoWong
