module

public import CFSG.Sporadic.Recognition.JankoWongCentralizerC
public import CFSG.Sporadic.Recognition.JankoWongPGL
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCoreQuotient
public import CFSG.Sporadic.Recognition.JankoWongInvolutionData

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS
open scoped Pointwise

theorem nonempty_closure_dihedral {M : Type*} [Group M] [Finite M] {ρ σ : M}
    (hσ : σ ^ 2 = 1) (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (hσρ : σ ∉ zpowers ρ) :
    Nonempty (closure ({ρ, σ} : Set M) ≃* DihedralGroup (orderOf ρ)) := by
  have hρH : ρ ∈ closure ({ρ, σ} : Set M) := subset_closure (by simp)
  have hσH : σ ∈ closure ({ρ, σ} : Set M) := subset_closure (by simp)
  have hgen : (⊤ : Subgroup (closure ({ρ, σ} : Set M))) =
      zpowers ⟨ρ, hρH⟩ ⊔ zpowers ⟨σ, hσH⟩ := by
    rw [zpowers_eq_closure, zpowers_eq_closure, ← Subgroup.closure_union,
      ← closure_closure_coe_preimage (k := ({ρ, σ} : Set M))]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  have h := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem
    (D := closure ({ρ, σ} : Set M)) ⟨ρ, hρH⟩ ⟨σ, hσH⟩ hgen (Subtype.ext (by simpa using hσ))
    (Subtype.ext (by simpa using hrel)) (fun hmem => hσρ (by
      obtain ⟨k, hk⟩ := (mem_zpowers_iff).mp hmem
      exact (mem_zpowers_iff).mpr ⟨k, by simpa using congrArg Subtype.val hk⟩))
  rwa [Subgroup.orderOf_mk] at h

namespace Setup

variable {G : Type} [Group G] [Finite G]

structure Ctx (S : Setup G) where
  a : S.H
  b : S.H
  t : S.H
  d : S.H
  P : Subgroup S.H
  ha : S.ρ a = permA3
  hb : S.ρ b = permB3
  ha3 : a ^ 3 = 1
  hb3 : b ^ 3 = 1
  hab : a * b = b * a
  hP : IsPGroup 3 P
  hP9 : Nat.card P = 9
  haP : a ∈ P
  hbP : b ∈ P
  ht2 : t ^ 2 = 1
  hd2 : d ^ 2 = 1
  ht : S.ρ t = permT
  hd : S.ρ d = permD
  htx : t * (a * b) = (a * b) * t
  hdx : d * (a * b) * d⁻¹ = (a * b)⁻¹
  hdt : (d * t) ^ 2 = zIn S.z

theorem exists_ctx (S : Setup G) : Nonempty (Ctx S) := by
  obtain ⟨a, b, P, ha, hb, ha3, hb3, hab, hP, hP9, haP, hbP⟩ := S.exists_std_sylow3
  obtain ⟨t, d, ht2, hd2, ht, hd, htx, hdx, hdt⟩ := S.exists_dihedral_data ha hb ha3 hb3 hab
  exact ⟨⟨a, b, t, d, P, ha, hb, ha3, hb3, hab, hP, hP9, haP, hbP, ht2, hd2, ht, hd, htx, hdx,
    hdt⟩⟩

namespace Ctx

variable {S : Setup G} (c : Ctx S)

@[expose] def x : S.H := c.a * c.b

@[expose] def s : G := (c.x : G)

@[expose] def Cg : Subgroup G := centralizer ({c.s} : Set G)

@[expose] def Ng : Subgroup G := normalizer ((zpowers c.s : Subgroup G) : Set G)

theorem x_cube : c.x ^ 3 = 1 := by
  unfold x
  rw [Commute.mul_pow c.hab, c.ha3, c.hb3, one_mul]

theorem x_type : (S.ρ c.x).cycleType = {3, 3} := by
  unfold x
  rw [map_mul, c.ha, c.hb]
  exact cycleType_permA3B3

theorem x_ne_one : c.x ≠ 1 := fun e => by
  have := c.x_type
  rw [e, map_one, cycleType_one] at this
  simp at this

theorem s_cube : c.s ^ 3 = 1 := by
  have := congrArg Subtype.val c.x_cube
  simpa [s] using this

theorem s_ne_one : c.s ≠ 1 := fun e => c.x_ne_one (Subtype.ext e)

theorem orderOf_s : orderOf c.s = 3 := orderOf_eq_prime c.s_cube c.s_ne_one

theorem s_inv_ne : c.s⁻¹ ≠ c.s := fun e => by
  have h1 : c.s * c.s = 1 := by
    calc c.s * c.s = c.s⁻¹ * c.s := by rw [e]
      _ = 1 := inv_mul_cancel c.s
  have := orderOf_dvd_of_pow_eq_one (show c.s ^ 2 = 1 by rwa [pow_two])
  rw [c.orderOf_s] at this
  norm_num at this

theorem t_ne_one : c.t ≠ 1 := fun e => by
  have := c.ht
  rw [e, map_one] at this
  have h2 := congrArg Perm.cycleType this
  rw [cycleType_one, cycleType_permT] at h2
  simp at h2

theorem t_ne_z : c.t ≠ zIn S.z := fun e => by
  have h1 := S.cover.rho_z
  have : S.ρ (zIn S.z) = 1 := h1
  rw [← e, c.ht] at this
  have h2 := congrArg Perm.cycleType this
  rw [cycleType_one, cycleType_permT] at h2
  simp at h2

theorem d_comm_z : (c.d : G) * S.z = S.z * (c.d : G) :=
  Subgroup.mem_centralizer_singleton_iff.mp c.d.2

theorem t_comm_z : (c.t : G) * S.z = S.z * (c.t : G) :=
  Subgroup.mem_centralizer_singleton_iff.mp c.t.2

theorem d_inv_s : (c.d : G) * c.s * (c.d : G)⁻¹ = c.s⁻¹ := by
  have := congrArg Subtype.val c.hdx
  simpa [s, x] using this

theorem t_comm_s : (c.t : G) * c.s = c.s * (c.t : G) := by
  have := congrArg Subtype.val c.htx
  simpa [s, x] using this

theorem z_comm_s : S.z * c.s = c.s * S.z := by
  have := Subgroup.mem_centralizer_singleton_iff.mp c.x.2
  exact this.symm

theorem cg_le_ng : c.Cg ≤ c.Ng := by
  unfold Cg Ng
  have h := Subgroup.centralizer_le_normalizer (G := G) ((zpowers c.s : Subgroup G) : Set G)
  have e : centralizer (((zpowers c.s : Subgroup G)) : Set G) = centralizer ({c.s} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rwa [e] at h

theorem conj_eq_or_inv {g : G} (hg : g ∈ c.Ng) : g * c.s * g⁻¹ = c.s ∨ g * c.s * g⁻¹ = c.s⁻¹ := by
  have hmem : g * c.s * g⁻¹ ∈ zpowers c.s :=
    (Subgroup.mem_normalizer_iff.mp hg c.s).mp (Subgroup.mem_zpowers c.s)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hmod : c.s ^ (n % 3) = c.s ^ n := by
    have := zpow_mod_orderOf c.s n
    rwa [c.orderOf_s] at this
  have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h3 with h | h | h
  · exfalso
    rw [h] at hmod
    have h1 : g * c.s * g⁻¹ = 1 := by rw [← hn, ← hmod]; simp
    apply c.s_ne_one
    calc c.s = g⁻¹ * (g * c.s * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · left
    rw [h] at hmod
    rw [← hn, ← hmod]; simp
  · right
    rw [h] at hmod
    rw [← hn, ← hmod]
    have h2 : c.s ^ 2 * c.s = 1 := by rw [← pow_succ]; exact c.s_cube
    calc c.s ^ ((2 : ℤ)) = c.s ^ 2 := by norm_cast
      _ = c.s⁻¹ := eq_inv_of_mul_eq_one_left h2

theorem d_inv_conj_s : (c.d : G)⁻¹ * c.s * (c.d : G) = c.s⁻¹ := by
  have e : c.s = (c.d : G)⁻¹ * ((c.d : G) * c.s * (c.d : G)⁻¹) * (c.d : G) := by group
  rw [c.d_inv_s] at e
  calc (c.d : G)⁻¹ * c.s * (c.d : G) = ((c.d : G)⁻¹ * c.s⁻¹ * (c.d : G))⁻¹ := by group
    _ = c.s⁻¹ := by rw [← e]

theorem d_mem_ng : (c.d : G) ∈ c.Ng := by
  unfold Ng
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have : (c.d : G) * c.s ^ n * (c.d : G)⁻¹ = (c.s⁻¹) ^ n := by
      rw [← c.d_inv_s]; exact (conj_zpow).symm
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers c.s)) n
  · intro hh
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hh
    have : h = (c.s⁻¹) ^ m := by
      calc h = (c.d : G)⁻¹ * ((c.d : G) * h * (c.d : G)⁻¹) * (c.d : G) := by group
        _ = (c.d : G)⁻¹ * c.s ^ m * (c.d : G) := by rw [hm]
        _ = ((c.d : G)⁻¹ * c.s * (c.d : G)) ^ m := by
            have := conj_zpow (a := (c.d : G)⁻¹) (b := c.s) (i := m)
            simpa using this.symm
        _ = (c.s⁻¹) ^ m := by rw [c.d_inv_conj_s]
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers c.s)) m

theorem mem_cg_iff {g : G} : g ∈ c.Cg ↔ g * c.s * g⁻¹ = c.s := by
  unfold Cg
  rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]

theorem mem_ng_of_mem_cg {g : G} (hg : g ∈ c.Cg) : g ∈ c.Ng := c.cg_le_ng hg

theorem conj_mul_d (B : G) :
    (B * (c.d : G)) * c.s * (B * (c.d : G))⁻¹ = (B * c.s * B⁻¹)⁻¹ := by
  calc (B * (c.d : G)) * c.s * (B * (c.d : G))⁻¹
      = B * ((c.d : G) * c.s * (c.d : G)⁻¹) * B⁻¹ := by group
    _ = B * c.s⁻¹ * B⁻¹ := by rw [c.d_inv_s]
    _ = (B * c.s * B⁻¹)⁻¹ := by group

theorem index_two_of (U : Subgroup G) (hdU : (c.d : G) ∈ U) (hUN : U ≤ c.Ng) :
    ((c.Cg ⊓ U).subgroupOf U).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨(c.d : G), hdU⟩, ?_⟩
  intro b
  have hbd : ((b * ⟨(c.d : G), hdU⟩ : U) : G) = (b : G) * (c.d : G) := rfl
  have hiff : ∀ y : U, y ∈ (c.Cg ⊓ U).subgroupOf U ↔ (y : G) ∈ c.Cg := fun y => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩
  rcases c.conj_eq_or_inv (hUN b.2) with hb | hb
  · refine Or.inr ⟨(hiff b).mpr (c.mem_cg_iff.mpr hb), ?_⟩
    intro hmem
    have h1 := c.mem_cg_iff.mp ((hiff _).mp hmem)
    rw [hbd, c.conj_mul_d, hb] at h1
    exact c.s_inv_ne h1
  · refine Or.inl ⟨?_, ?_⟩
    · apply (hiff _).mpr
      apply c.mem_cg_iff.mpr
      rw [hbd, c.conj_mul_d, hb, inv_inv]
    · intro hmem
      have h1 := c.mem_cg_iff.mp ((hiff _).mp hmem)
      rw [hb] at h1
      exact c.s_inv_ne h1

theorem index_two : (c.Cg.subgroupOf c.Ng).index = 2 := by
  have := c.index_two_of c.Ng c.d_mem_ng le_rfl
  rwa [inf_eq_left.mpr c.cg_le_ng] at this

theorem card_ng : Nat.card c.Ng = 2 * Nat.card c.Cg := by
  have h1 := Subgroup.index_mul_card (c.Cg.subgroupOf c.Ng)
  rw [c.index_two, Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.cg_le_ng).toEquiv] at h1
  exact h1.symm

theorem card_sylow_ng (T : Sylow 2 ↥c.Ng) : Nat.card T = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T'⟩ : Nonempty (Sylow 2 ↥c.Cg) := inferInstance
  have h4 : Nat.card T' = 4 := S.card_sylow_centralizer_type33 c.x_cube c.x_type T'
  rw [T'.card_eq_multiplicity] at h4
  have hf : (Nat.card c.Cg).factorization 2 = 2 := by
    have : (2 : ℕ) ^ ((Nat.card c.Cg).factorization 2) = 2 ^ 2 := by rw [h4]; norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  rw [T.card_eq_multiplicity, c.card_ng,
    Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply, hf]
  rw [Nat.Prime.factorization_self Nat.prime_two]
  norm_num

theorem card_ng_inf_H (hz1 : S.z ^ 2 = 1) (hz : S.z ≠ 1) :
    Nat.card (c.Ng ⊓ S.H : Subgroup G) = 72 := by
  have hdU : (c.d : G) ∈ c.Ng ⊓ S.H := ⟨c.d_mem_ng, c.d.2⟩
  have hidx := c.index_two_of (c.Ng ⊓ S.H) hdU inf_le_left
  have h1 := Subgroup.index_mul_card ((c.Cg ⊓ (c.Ng ⊓ S.H)).subgroupOf (c.Ng ⊓ S.H))
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
    c.Cg ⊓ (c.Ng ⊓ S.H) ≤ c.Ng ⊓ S.H)).toEquiv] at h1
  have h2 : c.Cg ⊓ (c.Ng ⊓ S.H) = c.Cg ⊓ S.H := by
    ext g
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, c.cg_le_ng h.1, h.2⟩⟩
  have hz2 : S.z * c.s = c.s * S.z := c.z_comm_s
  have h36 : Nat.card (c.Cg ⊓ S.H : Subgroup G) = 36 :=
    S.card_inf_centralizer_involution c.x_cube c.x_type (v := S.z) hz1 hz hz2
  rw [h2, h36] at h1
  omega

theorem mem_cg_of_odd {g : G} (hg : g ∈ c.Ng) (hodd : Odd (orderOf g)) : g ∈ c.Cg := by
  rcases c.conj_eq_or_inv hg with h | h
  · exact c.mem_cg_iff.mpr h
  · exfalso
    have h2 : g ^ 2 * c.s * (g ^ 2)⁻¹ = c.s := by
      calc g ^ 2 * c.s * (g ^ 2)⁻¹ = g * g * c.s * (g * g)⁻¹ := by rw [pow_two]
        _ = g * (g * c.s * g⁻¹) * g⁻¹ := by group
        _ = g * c.s⁻¹ * g⁻¹ := by rw [h]
        _ = (g * c.s * g⁻¹)⁻¹ := by group
        _ = c.s := by rw [h, inv_inv]
    obtain ⟨k, hk⟩ := hodd
    have hg1 : g ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one g
    have hg_eq : g = (g ^ 2) ^ (k + 1) := by
      calc g = 1 * g := (one_mul g).symm
        _ = g ^ (2 * k + 1) * g := by rw [hg1]
        _ = g ^ (2 * k + 1 + 1) := (pow_succ g _).symm
        _ = (g ^ 2) ^ (k + 1) := by rw [← pow_mul]; congr 1
    have hgC : g ∈ c.Cg := by
      rw [hg_eq]
      exact pow_mem (c.mem_cg_iff.mpr h2) (k + 1)
    have := c.mem_cg_iff.mp hgC
    rw [h] at this
    exact c.s_inv_ne this

@[expose] def OG : Subgroup G := (CFSG.oddCore ↥c.Ng).map c.Ng.subtype

theorem odd_card_OG : Odd (Nat.card c.OG) := by
  unfold OG
  rw [Subgroup.card_map_of_injective c.Ng.subtype_injective]
  exact CFSG.ABGDGroups.odd_card_oddCore ↥c.Ng

theorem OG_le_Cg : c.OG ≤ c.Cg := by
  rintro _ ⟨o, ho, rfl⟩
  apply c.mem_cg_of_odd o.2
  have h1 : orderOf (⟨o, ho⟩ : CFSG.oddCore ↥c.Ng) ∣ Nat.card (CFSG.oddCore ↥c.Ng) :=
    orderOf_dvd_natCard _
  have h2 : orderOf o = orderOf (⟨o, ho⟩ : CFSG.oddCore ↥c.Ng) := (Subgroup.orderOf_mk o ho).symm
  have h3 : orderOf (o : G) = orderOf o := Subgroup.orderOf_coe o
  rw [h3, h2]
  exact Odd.of_dvd_nat (CFSG.ABGDGroups.odd_card_oddCore ↥c.Ng) h1

theorem OG_normalized : ∀ g ∈ c.Ng, ∀ y ∈ c.OG, g * y * g⁻¹ ∈ c.OG := by
  rintro g hg _ ⟨o, ho, rfl⟩
  refine ⟨⟨g, hg⟩ * o * ⟨g, hg⟩⁻¹, ?_, rfl⟩
  exact (CFSG.oddCore_normal ↥c.Ng).conj_mem o ho ⟨g, hg⟩

theorem zpowers_le_OG : zpowers c.s ≤ c.OG := by
  have hle : zpowers c.s ≤ c.Ng := Subgroup.le_normalizer
  have hnorm : ((zpowers c.s).subgroupOf c.Ng).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hle]
    intro h k hh hk
    exact (Subgroup.mem_normalizer_iff.mp hk h).mp hh
  have hodd : Odd (Nat.card ((zpowers c.s).subgroupOf c.Ng)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, c.orderOf_s]
    exact ⟨1, rfl⟩
  have hle2 : (zpowers c.s).subgroupOf c.Ng ≤ CFSG.oddCore ↥c.Ng := by
    unfold CFSG.oddCore
    exact le_sSup ⟨hnorm, hodd⟩
  have := Subgroup.map_mono (f := c.Ng.subtype) hle2
  rwa [Subgroup.map_subgroupOf_eq_of_le hle] at this

theorem isPGroup_three_OG : IsPGroup 3 c.OG :=
  S.isPGroup_three_of_odd_normal_G (x := c.x) (t := c.t) c.x_cube c.x_type c.ht2 c.t_ne_one
    c.t_ne_z c.htx c.OG_le_Cg (fun g hg => c.OG_normalized g (c.cg_le_ng hg)) c.odd_card_OG

theorem permT_not_comm_permA3 : permT * permA3 ≠ permA3 * permT := by
  unfold permT permA3; decide

theorem P_comm_s {p : S.H} (hp : p ∈ c.P) : (p : G) * c.s = c.s * (p : G) := by
  have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := c.P) (by
    rw [c.hP9]; norm_num)
  have hxP : c.x ∈ c.P := c.P.mul_mem c.haP c.hbP
  have := hcomm.is_comm.comm ⟨p, hp⟩ ⟨c.x, hxP⟩
  exact congrArg (fun w : c.P => ((w : S.H) : G)) this

theorem card_OG_eq_three (h27 : ¬ 27 ∣ Nat.card G) : Nat.card c.OG = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbound : ∀ R : Subgroup G, IsPGroup 3 R → Nat.card R ≤ 9 := fun R hR =>
    card_le_nine_of_not_dvd h27 hR
  have h9 : Nat.card c.OG ≤ 9 := hbound _ c.isPGroup_three_OG
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp c.isPGroup_three_OG
  have h3 : 3 ≤ Nat.card c.OG := by
    have := Subgroup.card_le_of_le c.zpowers_le_OG
    rwa [Nat.card_zpowers, c.orderOf_s] at this
  have hk12 : k = 1 ∨ k = 2 := by
    rcases k with _ | _ | _ | k
    · rw [pow_zero] at hk; omega
    · left; rfl
    · right; rfl
    · exfalso
      have : 3 ^ 3 ≤ Nat.card c.OG := by
        rw [hk]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at this
      omega
  rcases hk12 with rfl | rfl
  · simpa using hk
  · exfalso
    have hOG9 : Nat.card c.OG = 9 := by simpa using hk
    set PG : Subgroup G := c.P.map S.H.subtype with hPG
    have hPGp : IsPGroup 3 PG := c.hP.map _
    have hPG9 : Nat.card PG = 9 := by
      rw [hPG, Subgroup.card_map_of_injective S.H.subtype_injective, c.hP9]
    have hPGC : PG ≤ c.Cg := by
      rintro _ ⟨p, hp, rfl⟩
      exact c.mem_cg_iff.mpr (by
        have := c.P_comm_s hp
        calc (p : G) * c.s * (p : G)⁻¹ = c.s * (p : G) * (p : G)⁻¹ := by rw [this]
          _ = c.s := by group)
    obtain ⟨Q_P, hQ_P⟩ := exists_sylow_of_card_nine hPGp hPGC hPG9 hbound
    obtain ⟨Q_O, hQ_O⟩ := exists_sylow_of_card_nine c.isPGroup_three_OG c.OG_le_Cg hOG9 hbound
    obtain ⟨g, hg⟩ := sylow_conj_mem Q_P Q_O
    have hPleOG : PG ≤ c.OG := by
      intro p hp
      have hpC : p ∈ c.Cg := hPGC hp
      have h1 : (⟨(g : G) * p * (g : G)⁻¹, c.Cg.mul_mem (c.Cg.mul_mem g.2 hpC)
          (c.Cg.inv_mem g.2)⟩ : c.Cg) ∈ (Q_O : Subgroup c.Cg) := by
        rw [hg, hQ_P, Subgroup.mem_subgroupOf]
        have e : (g : G)⁻¹ * ((g : G) * p * (g : G)⁻¹) * (g : G) = p := by group
        show (g : G)⁻¹ * ((g : G) * p * (g : G)⁻¹) * (g : G) ∈ PG
        rw [e]; exact hp
      rw [hQ_O, Subgroup.mem_subgroupOf] at h1
      have h1' : (g : G) * p * (g : G)⁻¹ ∈ c.OG := h1
      have h2 := c.OG_normalized (g : G)⁻¹ (c.cg_le_ng (c.Cg.inv_mem g.2)) _ h1'
      have e : (g : G)⁻¹ * ((g : G) * p * (g : G)⁻¹) * (g : G)⁻¹⁻¹ = p := by group
      rw [e] at h2
      exact h2
    have hPGeq : PG = c.OG := Subgroup.eq_of_le_of_card_ge hPleOG (by rw [hOG9, hPG9])
    obtain ⟨e, hex, hez⟩ := S.exists_conj_to_z h27 c.ha c.hb c.ha3 c.hb3 c.hab c.hP c.hP9 c.haP
      c.hbP c.ht2 c.t_ne_one c.htx
    have heC : e ∈ c.Cg := by
      rw [c.mem_cg_iff]
      show e * ((c.x : S.H) : G) * e⁻¹ = ((c.x : S.H) : G)
      rw [mul_inv_eq_iff_eq_mul]; exact hex
    have haPG : ((c.a : S.H) : G) ∈ PG := ⟨c.a, c.haP, rfl⟩
    have h1 : e⁻¹ * (c.a : G) * e ∈ c.OG := by
      have := c.OG_normalized e⁻¹ (c.cg_le_ng (c.Cg.inv_mem heC)) (c.a : G)
        (by rw [← hPGeq]; exact haPG)
      rwa [inv_inv] at this
    rw [← hPGeq] at h1
    obtain ⟨q, hq, hqe⟩ := h1
    have hqz : (q : G) * S.z = S.z * (q : G) := Subgroup.mem_centralizer_singleton_iff.mp q.2
    have hcomm : (c.t : G) * (c.a : G) = (c.a : G) * (c.t : G) := by
      have hq' : (q : G) = e⁻¹ * (c.a : G) * e := hqe
      calc (c.t : G) * (c.a : G) = (e * S.z * e⁻¹) * (c.a : G) := by rw [hez]
        _ = e * (S.z * (e⁻¹ * (c.a : G) * e)) * e⁻¹ := by group
        _ = e * ((e⁻¹ * (c.a : G) * e) * S.z) * e⁻¹ := by rw [← hq', ← hqz]
        _ = (c.a : G) * (e * S.z * e⁻¹) := by group
        _ = (c.a : G) * (c.t : G) := by rw [hez]
    have hcomm' : c.t * c.a = c.a * c.t := Subtype.ext hcomm
    have := congrArg S.ρ hcomm'
    rw [map_mul, map_mul, c.ht, c.ha] at this
    exact permT_not_comm_permA3 this

abbrev Kq : Type := ↥c.Ng ⧸ CFSG.oddCore ↥c.Ng

abbrev piK : ↥c.Ng →* c.Kq := QuotientGroup.mk' (CFSG.oddCore ↥c.Ng)

theorem card_oddCoreNg (h3 : Nat.card c.OG = 3) : Nat.card (CFSG.oddCore ↥c.Ng) = 3 := by
  have := h3
  unfold OG at this
  rwa [Subgroup.card_map_of_injective c.Ng.subtype_injective] at this

theorem card_Kq_mul (h3 : Nat.card c.OG = 3) : Nat.card c.Kq * 3 = Nat.card c.Ng := by
  have := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥c.Ng)
  rw [c.card_oddCoreNg h3] at this
  exact this.symm

theorem factorization_ng : (Nat.card c.Ng).factorization 2 = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥c.Ng) := inferInstance
  have h8 := c.card_sylow_ng T
  rw [T.card_eq_multiplicity] at h8
  have : (2 : ℕ) ^ ((Nat.card c.Ng).factorization 2) = 2 ^ 3 := by rw [h8]; norm_num
  exact Nat.pow_right_injective (le_refl 2) this

theorem factorization_Kq (h3 : Nat.card c.OG = 3) : (Nat.card c.Kq).factorization 2 = 3 := by
  have h := c.card_Kq_mul h3
  have hf := c.factorization_ng
  rw [← h, Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Finsupp.add_apply] at hf
  have h3 : (3 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  rw [h3] at hf
  simpa using hf

theorem h8_Kq (h3 : Nat.card c.OG = 3) : 2 ^ 3 ∣ Nat.card c.Kq ∧ ¬ 2 ^ 4 ∣ Nat.card c.Kq := by
  have hf := c.factorization_Kq h3
  have hne : Nat.card c.Kq ≠ 0 := Nat.card_pos.ne'
  refine ⟨(Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mpr (by omega), fun h => ?_⟩
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp h
  omega

theorem oddCore_Kq : CFSG.oddCore c.Kq = ⊥ :=
  CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_quotient_eq_bot

theorem z_mem_cg : S.z ∈ c.Cg := c.mem_cg_iff.mpr (by
  have := c.z_comm_s
  calc S.z * c.s * S.z⁻¹ = c.s * S.z * S.z⁻¹ := by rw [this]
    _ = c.s := by group)

@[expose] def zN : ↥c.Ng := ⟨S.z, c.cg_le_ng c.z_mem_cg⟩

theorem zN_sq : c.zN ^ 2 = 1 := by
  apply Subtype.ext
  have : S.z ^ 2 = 1 := by rw [← S.order_z]; exact pow_orderOf_eq_one S.z
  simpa [zN] using this

theorem zN_ne_one : c.zN ≠ 1 := fun e => by
  have := congrArg Subtype.val e
  exact S.cover.ne_one (Subtype.ext this)

theorem zN_not_mem_oddCore (h3 : Nat.card c.OG = 3) : c.zN ∉ CFSG.oddCore ↥c.Ng := by
  intro h
  have h1 : orderOf (⟨c.zN, h⟩ : CFSG.oddCore ↥c.Ng) ∣ Nat.card (CFSG.oddCore ↥c.Ng) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, c.card_oddCoreNg h3] at h1
  have h2 : orderOf c.zN = 2 := orderOf_eq_prime c.zN_sq c.zN_ne_one
  rw [h2] at h1
  norm_num at h1

@[expose] def uK : c.Kq := c.piK c.zN

theorem uK_sq : c.uK ^ 2 = 1 := by
  unfold uK
  rw [← map_pow, c.zN_sq, map_one]

theorem uK_ne_one (h3 : Nat.card c.OG = 3) : c.uK ≠ 1 := fun e => by
  unfold uK at e
  exact c.zN_not_mem_oddCore h3 ((QuotientGroup.eq_one_iff c.zN).mp e)

@[expose] def JK : Subgroup c.Kq := (c.Cg.subgroupOf c.Ng).map c.piK

theorem oddCore_le_Cg_subgroupOf : CFSG.oddCore ↥c.Ng ≤ c.Cg.subgroupOf c.Ng := by
  intro o ho
  exact c.OG_le_Cg ⟨o, ho, rfl⟩

theorem index_JK : c.JK.index = 2 := by
  unfold JK
  rw [Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) (by
    rw [QuotientGroup.ker_mk']; exact c.oddCore_le_Cg_subgroupOf)]
  exact c.index_two

theorem OG_eq_zpowers (h3 : Nat.card c.OG = 3) : zpowers c.s = c.OG :=
  Subgroup.eq_of_le_of_card_ge c.zpowers_le_OG (by
    rw [h3, Nat.card_zpowers, c.orderOf_s])

theorem oddCore_le_centralizer_zN (h3 : Nat.card c.OG = 3) :
    CFSG.oddCore ↥c.Ng ≤ centralizer ({c.zN} : Set ↥c.Ng) := by
  intro o ho
  have hmem : (o : G) ∈ zpowers c.s := by
    rw [c.OG_eq_zpowers h3]; exact ⟨o, ho, rfl⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  show (o : G) * S.z = S.z * (o : G)
  rw [← hn]
  exact ((Commute.zpow_left (show Commute c.s S.z from c.z_comm_s.symm) n)).eq

theorem card_centralizer_zN : Nat.card (centralizer ({c.zN} : Set ↥c.Ng)) = 72 := by
  have hz2 : S.z ^ 2 = 1 := by rw [← S.order_z]; exact pow_orderOf_eq_one S.z
  have hz1 : S.z ≠ 1 := fun e => S.cover.ne_one (Subtype.ext e)
  rw [card_centralizer_subtype c.zN]
  exact c.card_ng_inf_H hz2 hz1

theorem centralizer_piK_of_sq {w : ↥c.Ng} (hw : w ^ 2 = 1) :
    centralizer ({c.piK w} : Set c.Kq) = (centralizer ({w} : Set ↥c.Ng)).map c.piK := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hy
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective y
    let α := {m : ↥c.Ng // c.piK m = c.piK n}
    have hcard : Nat.card α = Nat.card (CFSG.oddCore ↥c.Ng) := by
      refine Nat.card_congr
        { toFun := fun m => ⟨n⁻¹ * m.1, by
            have h := m.2
            simp only [QuotientGroup.mk'_apply] at h
            exact (QuotientGroup.eq_one_iff _).mp (by
              rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h, inv_mul_cancel])⟩
          invFun := fun k => ⟨n * k.1, by
            have h1 : (k.1 : c.Kq) = 1 := (QuotientGroup.eq_one_iff _).mpr k.2
            simp only [QuotientGroup.mk'_apply]
            rw [QuotientGroup.mk_mul, h1, mul_one]⟩
          left_inv := fun m => by apply Subtype.ext; simp
          right_inv := fun k => by apply Subtype.ext; simp }
    have hodd : Odd (Nat.card α) := by
      rw [hcard]; exact CFSG.ABGDGroups.odd_card_oddCore ↥c.Ng
    let f : α → α := fun m => ⟨w * m.1 * w⁻¹, by
      have h1 : c.piK (w * m.1 * w⁻¹) = c.piK w * c.piK m.1 * (c.piK w)⁻¹ := by simp
      rw [h1, m.2]
      have : c.piK n * c.piK w = c.piK w * c.piK n := hy
      calc c.piK w * c.piK n * (c.piK w)⁻¹ = (c.piK w * c.piK n) * (c.piK w)⁻¹ := rfl
        _ = (c.piK n * c.piK w) * (c.piK w)⁻¹ := by rw [this]
        _ = c.piK n := by group⟩
    have hf : ∀ m, f (f m) = m := by
      intro m
      apply Subtype.ext
      show w * (w * m.1 * w⁻¹) * w⁻¹ = m.1
      have h2 : w * w = 1 := by rw [← pow_two]; exact hw
      calc w * (w * m.1 * w⁻¹) * w⁻¹ = (w * w) * m.1 * (w * w)⁻¹ := by group
        _ = m.1 := by rw [h2]; group
    obtain ⟨m, hm⟩ := exists_fixed_of_sq_eq_one_odd hf hodd
    have := congrArg Subtype.val hm
    have h3 : w * m.1 * w⁻¹ = m.1 := this
    refine ⟨m.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_, m.2⟩
    calc m.1 * w = (w * m.1 * w⁻¹) * w := by rw [h3]
      _ = w * m.1 := by group
  · rintro ⟨m, hm, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp hm
    rw [← map_mul, ← map_mul, this]

theorem centralizer_uK :
    centralizer ({c.uK} : Set c.Kq) = (centralizer ({c.zN} : Set ↥c.Ng)).map c.piK :=
  c.centralizer_piK_of_sq c.zN_sq

theorem card_centralizer_uK (h3 : Nat.card c.OG = 3) :
    Nat.card (centralizer ({c.uK} : Set c.Kq)) = 24 := by
  rw [c.centralizer_uK]
  set Zc : Subgroup ↥c.Ng := centralizer ({c.zN} : Set ↥c.Ng) with hZc
  have hle := c.oddCore_le_centralizer_zN h3
  set π' : ↥Zc →* c.Kq := c.piK.domRestrict Zc with hπ'
  have hrange : π'.range = Zc.map c.piK := MonoidHom.domRestrict_range Zc c.piK
  have hker : π'.ker = (CFSG.oddCore ↥c.Ng).subgroupOf Zc := by
    rw [hπ', MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π'.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange π').toEquiv, hrange, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, c.card_oddCoreNg h3] at h1
  have h72 : Nat.card ↥Zc = 72 := c.card_centralizer_zN
  have h2 : Nat.card ↥Zc = Nat.card ↥Zc := rfl
  omega

theorem not_hasNormalPComplement_Kq (h3 : Nat.card c.OG = 3)
    (hNCg : ¬ CFSG.HasNormalPComplement 2 ↥c.Cg) : ¬ CFSG.HasNormalPComplement 2 c.Kq := by
  rintro ⟨Xb, hXbn, hcop, hq⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup ↥c.Ng := Xb.comap c.piK
  have hXn : X.Normal := hXbn.comap c.piK
  have hidx : X.index = Xb.index :=
    Subgroup.index_comap_of_surjective Xb (QuotientGroup.mk'_surjective _)
  have hcardX : Nat.card X = 3 * Nat.card Xb := by
    have h1 := Subgroup.card_mul_index X
    have h2 := Subgroup.card_mul_index Xb
    rw [hidx] at h1
    have h3k := c.card_Kq_mul h3
    have hpos : 0 < Xb.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have : Nat.card X * Xb.index = (3 * Nat.card Xb) * Xb.index := by
      calc Nat.card X * Xb.index = Nat.card c.Ng := h1
        _ = Nat.card c.Kq * 3 := h3k.symm
        _ = (Nat.card Xb * Xb.index) * 3 := by rw [h2]
        _ = (3 * Nat.card Xb) * Xb.index := by ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hXodd : Odd (Nat.card X) := by
    rw [hcardX]
    exact Odd.mul ⟨1, rfl⟩ (Nat.coprime_two_left.mp hcop)
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hq
  have hidx2 : X.index = 2 ^ j := by rw [hidx, Subgroup.index_eq_card]; exact hj
  have hNg : Nat.card c.Ng = Nat.card X * 2 ^ j := by
    rw [← hidx2]; exact (Subgroup.card_mul_index X).symm
  have hj3 : j = 3 := by
    have hf := c.factorization_ng
    rw [hNg, Nat.factorization_mul Nat.card_pos.ne' (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two] at hf
    have h0 : (Nat.card X).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (fun h =>
        (Nat.not_even_iff_odd.mpr hXodd) (even_iff_two_dvd.mpr h))
    simp [h0] at hf
    exact hf
  have hXC : X.map c.Ng.subtype ≤ c.Cg := by
    rintro _ ⟨x, hx, rfl⟩
    apply c.mem_cg_of_odd x.2
    have h1 : orderOf (⟨x, hx⟩ : X) ∣ Nat.card X := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hXodd h1
  have hXG_norm : ∀ g ∈ c.Cg, ∀ y ∈ X.map c.Ng.subtype, g * y * g⁻¹ ∈ X.map c.Ng.subtype := by
    rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨⟨g, c.cg_le_ng hg⟩ * x * ⟨g, c.cg_le_ng hg⟩⁻¹, hXn.conj_mem x hx _, rfl⟩
  have hnormC : ((X.map c.Ng.subtype).subgroupOf c.Cg).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr (hXG_norm g g.2 n (Subgroup.mem_subgroupOf.mp hn))⟩
  have hcardXC : Nat.card ((X.map c.Ng.subtype).subgroupOf c.Cg) = Nat.card X := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXC).toEquiv,
      Subgroup.card_map_of_injective c.Ng.subtype_injective]
  have hcardC : Nat.card c.Cg = Nat.card X * 4 := by
    have := c.card_ng
    rw [hNg, hj3] at this
    omega
  have hquot : Nat.card (↥c.Cg ⧸ (X.map c.Ng.subtype).subgroupOf c.Cg) = 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((X.map c.Ng.subtype).subgroupOf c.Cg)
    rw [hcardXC, hcardC] at h1
    have hpos : 0 < Nat.card X := Nat.card_pos
    nlinarith
  have hcopC : Nat.Coprime 2 (Nat.card ((X.map c.Ng.subtype).subgroupOf c.Cg)) := by
    rw [hcardXC]; exact Nat.coprime_two_left.mpr hXodd
  have hpC : IsPGroup 2 (↥c.Cg ⧸ (X.map c.Ng.subtype).subgroupOf c.Cg) :=
    IsPGroup.of_card (n := 2) (by rw [hquot]; norm_num)
  have hNC : CFSG.HasNormalPComplement 2 ↥c.Cg :=
    show ∃ (N : Subgroup ↥c.Cg) (_ : N.Normal), Nat.Coprime 2 (Nat.card N) ∧
      IsPGroup 2 (↥c.Cg ⧸ N) from
    ⟨(X.map c.Ng.subtype).subgroupOf c.Cg, hnormC, hcopC, hpC⟩
  exact hNCg hNC

@[expose] def tN : ↥c.Ng := ⟨(c.t : G), c.cg_le_ng (c.mem_cg_iff.mpr (by
  have := c.t_comm_s
  calc (c.t : G) * c.s * (c.t : G)⁻¹ = c.s * (c.t : G) * (c.t : G)⁻¹ := by rw [this]
    _ = c.s := by group))⟩

@[expose] def dN : ↥c.Ng := ⟨(c.d : G), c.d_mem_ng⟩

@[expose] def wN : ↥c.Ng := c.dN * c.tN

theorem tG_sq : (c.t : G) * (c.t : G) = 1 := by
  have := congrArg Subtype.val c.ht2
  simpa [pow_two] using this

theorem dG_sq : (c.d : G) * (c.d : G) = 1 := by
  have := congrArg Subtype.val c.hd2
  simpa [pow_two] using this

theorem tN_sq : c.tN ^ 2 = 1 := Subtype.ext (by simpa [pow_two, tN] using c.tG_sq)

theorem wN_sq : c.wN ^ 2 = c.zN := by
  apply Subtype.ext
  have h : ((c.d : G) * c.t) * ((c.d : G) * c.t) = S.z := by
    have := congrArg Subtype.val c.hdt
    simp only [pow_two, Subgroup.coe_mul] at this
    exact this
  rw [pow_two]
  exact h

theorem tN_conj : c.tN * c.wN * c.tN⁻¹ = c.wN⁻¹ := by
  apply Subtype.ext
  have htinv : (c.t : G)⁻¹ = c.t := inv_eq_of_mul_eq_one_right c.tG_sq
  have hdinv : (c.d : G)⁻¹ = c.d := inv_eq_of_mul_eq_one_right c.dG_sq
  show (c.t : G) * ((c.d : G) * (c.t : G)) * (c.t : G)⁻¹ = ((c.d : G) * (c.t : G))⁻¹
  rw [mul_inv_rev, htinv, hdinv]
  calc (c.t : G) * ((c.d : G) * (c.t : G)) * (c.t : G)
      = (c.t : G) * (c.d : G) * ((c.t : G) * (c.t : G)) := by group
    _ = (c.t : G) * (c.d : G) := by rw [c.tG_sq, mul_one]

theorem orderOf_wN : orderOf c.wN = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ¬ c.wN ^ 2 ^ 1 = 1 := by
    rw [pow_one, c.wN_sq]; exact c.zN_ne_one
  have h2 : c.wN ^ 2 ^ (1 + 1) = 1 := by
    have : (2 : ℕ) ^ (1 + 1) = 2 * 2 := by norm_num
    rw [this, pow_mul, c.wN_sq, c.zN_sq]
  have := orderOf_eq_prime_pow h1 h2
  simpa using this

theorem permDT_zpow (n : ℤ) :
    (permD * permT) ^ n = 1 ∨ (permD * permT) ^ n = permD * permT := by
  have hsq : (permD * permT) ^ 2 = 1 := sq_eq_one_of_type22 cycleType_permD_mul_permT
  rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul]
    have : (permD * permT) ^ (2 : ℤ) = 1 := by simpa using hsq
    rw [this, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul]
    have : (permD * permT) ^ (2 : ℤ) = 1 := by simpa using hsq
    rw [this, one_zpow, one_mul]

theorem tN_not_mem_zpowers : c.tN ∉ zpowers c.wN := by
  intro h
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
  have h1 : (c.t : G) = (((c.d * c.t : S.H) ^ n : S.H) : G) := by
    have := congrArg Subtype.val hn
    simpa [wN, dN, tN] using this.symm
  have h2 : c.t = (c.d * c.t) ^ n := Subtype.ext h1
  have h3 : permT = (permD * permT) ^ n := by
    have := congrArg S.ρ h2
    rwa [map_zpow, map_mul, c.ht, c.hd] at this
  rcases permDT_zpow n with h4 | h4
  · rw [h4] at h3
    have := congrArg Perm.cycleType h3
    rw [cycleType_permT, cycleType_one] at this
    simp at this
  · rw [h4] at h3
    have := congrArg Perm.cycleType h3
    rw [cycleType_permT, cycleType_permD_mul_permT] at this
    have := congrArg Multiset.card this
    simp at this

theorem exists_dihedral_sylow_ng : ∃ D : Subgroup ↥c.Ng, Nat.card D = 8 ∧
    Nonempty (D ≃* DihedralGroup 4) ∧ ∃ Q : Sylow 2 ↥c.Ng, (Q : Subgroup ↥c.Ng) = D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_closure_dihedral (ρ := c.wN) (σ := c.tN) c.tN_sq c.tN_conj
    c.tN_not_mem_zpowers
  rw [c.orderOf_wN] at e
  set D : Subgroup ↥c.Ng := closure ({c.wN, c.tN} : Set ↥c.Ng) with hD
  have hcard : Nat.card D = 8 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hDp : IsPGroup 2 D := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  obtain ⟨Q, hQ⟩ := hDp.exists_le_sylow
  have hQcard := c.card_sylow_ng Q
  have hDQ : D = (Q : Subgroup ↥c.Ng) := Subgroup.eq_of_le_of_card_ge hQ (by rw [hQcard, hcard])
  exact ⟨D, hcard, ⟨e⟩, Q, hDQ.symm⟩

theorem hasDihedralSylowTwo_Kq (h3 : Nat.card c.OG = 3) :
    CFSG.GorensteinWalter.HasDihedralSylowTwo c.Kq := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, hDcard, ⟨eD⟩, Q, hQ⟩ := c.exists_dihedral_sylow_ng
  have hinj : Function.Injective (c.piK.domRestrict D) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : ↥c.Ng) ∈ CFSG.oddCore ↥c.Ng :=
      (QuotientGroup.eq_one_iff _).mp ha
    have h2 : orderOf (⟨(a : ↥c.Ng), h1⟩ : CFSG.oddCore ↥c.Ng) ∣ 3 := by
      have := orderOf_dvd_natCard (⟨(a : ↥c.Ng), h1⟩ : CFSG.oddCore ↥c.Ng)
      rwa [c.card_oddCoreNg h3] at this
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at h2
    have h3 : orderOf a ∣ 8 := by
      have := orderOf_dvd_natCard a
      rwa [hDcard] at this
    have h4 : orderOf a ∣ Nat.gcd 3 8 := Nat.dvd_gcd h2 h3
    have h5 : orderOf a = 1 := by simpa using h4
    exact orderOf_eq_one_iff.mp h5
  let T' : Sylow 2 c.Kq := Sylow.mapSurjective (QuotientGroup.mk'_surjective _) Q
  have hT'' : (T' : Subgroup c.Kq) = D.map c.piK := by
    show ((Q : Subgroup ↥c.Ng).map c.piK) = D.map c.piK
    rw [hQ]
  let e1 : D ≃* (c.piK.domRestrict D).range := MonoidHom.ofInjective hinj
  let e2 : (c.piK.domRestrict D).range ≃* D.map c.piK :=
    MulEquiv.subgroupCongr (MonoidHom.domRestrict_range D c.piK)
  let eT' : ↥(T' : Subgroup c.Kq) ≃* DihedralGroup 4 :=
    (MulEquiv.subgroupCongr hT'').trans (e2.symm.trans (e1.symm.trans eD))
  intro S'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq c.Kq T' S'
  have hS' : (S' : Subgroup c.Kq) = MulAut.conj g • (T' : Subgroup c.Kq) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  refine ⟨2, by norm_num, ⟨?_⟩⟩
  exact (MulEquiv.subgroupCongr hS').trans
    ((Subgroup.equivSMul (MulAut.conj g) (T' : Subgroup c.Kq)).symm.trans eT')

theorem pow_three_eq_one_of_mem_oddCore (h3 : Nat.card c.OG = 3) {o : ↥c.Ng}
    (ho : o ∈ CFSG.oddCore ↥c.Ng) : o ^ 3 = 1 := by
  have := pow_card_eq_one' (G := CFSG.oddCore ↥c.Ng) (x := ⟨o, ho⟩)
  rw [c.card_oddCoreNg h3] at this
  exact congrArg Subtype.val this

theorem sq_mem_oddCore {n : ↥c.Ng} {y : c.Kq} (hn : c.piK n = y) (hy : y ^ 2 = 1) :
    n ^ 2 ∈ CFSG.oddCore ↥c.Ng := by
  rw [← QuotientGroup.eq_one_iff]
  have : (c.piK (n ^ 2)) = 1 := by rw [map_pow, hn, hy]
  exact this

theorem exists_lift_commuting {w : ↥c.Ng} (hw : w ^ 2 = 1) {y : c.Kq}
    (hy : y * c.piK w = c.piK w * y) : ∃ n : ↥c.Ng, c.piK n = y ∧ n * w = w * n := by
  have hmem : y ∈ centralizer ({c.piK w} : Set c.Kq) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hy
  rw [c.centralizer_piK_of_sq hw] at hmem
  obtain ⟨m, hm, hmy⟩ := hmem
  exact ⟨m, hmy, Subgroup.mem_centralizer_singleton_iff.mp hm⟩

theorem mem_Cg_of_mem_JK {n : ↥c.Ng} (hn : c.piK n ∈ c.JK) :
    n ∈ c.Cg.subgroupOf c.Ng := by
  obtain ⟨m, hm, hmn⟩ := hn
  have hker : m⁻¹ * n ∈ CFSG.oddCore ↥c.Ng := by
    rw [← QuotientGroup.eq_one_iff]
    have : c.piK (m⁻¹ * n) = 1 := by rw [map_mul, map_inv, hmn, inv_mul_cancel]
    exact this
  have h1 : m⁻¹ * n ∈ c.Cg.subgroupOf c.Ng := c.oddCore_le_Cg_subgroupOf hker
  have h2 : m * (m⁻¹ * n) ∈ c.Cg.subgroupOf c.Ng := (c.Cg.subgroupOf c.Ng).mul_mem hm h1
  simpa using h2

theorem commute_of_mem_Cg_oddCore (h3 : Nat.card c.OG = 3) {n o : ↥c.Ng}
    (hn : n ∈ c.Cg.subgroupOf c.Ng) (ho : o ∈ CFSG.oddCore ↥c.Ng) : n * o = o * n := by
  have hmem : (o : G) ∈ zpowers c.s := by
    rw [c.OG_eq_zpowers h3]; exact ⟨o, ho, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hnC : (n : G) * c.s = c.s * (n : G) := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hn)
    exact this
  apply Subtype.ext
  show (n : G) * (o : G) = (o : G) * (n : G)
  rw [← hk]
  exact (Commute.zpow_right (show Commute (n : G) c.s from hnC) k).eq

theorem exists_configuration
    (h3 : Nat.card c.OG = 3)
    (hNCg : ¬ CFSG.HasNormalPComplement 2 ↥c.Cg) :
    ∃ (d₀ r₁ e₁ : ↥c.Ng) (p : ℕ), (p = 5 ∨ p = 7) ∧ d₀ ^ 2 = 1 ∧ d₀ ≠ 1 ∧ e₁ ^ 2 = 1 ∧
      orderOf r₁ = p ∧ d₀ * r₁ = r₁ * d₀ ∧ d₀ * e₁ = e₁ * d₀ ∧ e₁ * r₁ * e₁⁻¹ = r₁⁻¹ := by
  obtain ⟨db, rb, eb, hdJ, hd2, he2, hr, hdr, hde, her, hrJ, heJ⟩ :=
    exists_outer_involution_dihedral_centralizer (K := c.Kq)
      (c.hasDihedralSylowTwo_Kq h3) (c.h8_Kq h3) (c.not_hasNormalPComplement_Kq h3 hNCg)
      c.oddCore_Kq c.index_JK c.uK_sq (c.uK_ne_one h3) (c.card_centralizer_uK h3)
  obtain ⟨n₀, hn₀⟩ := QuotientGroup.mk_surjective db
  have hn₀' : c.piK n₀ = db := hn₀
  have hsq := c.sq_mem_oddCore hn₀' hd2
  have h3c := c.pow_three_eq_one_of_mem_oddCore h3 hsq
  set d₀ : ↥c.Ng := n₀ ^ 3 with hd₀
  have hd₀sq : d₀ ^ 2 = 1 := by
    rw [hd₀, ← pow_mul, mul_comm, pow_mul, h3c]
  have hd₀pi : c.piK d₀ = db := by
    rw [hd₀, map_pow, hn₀', pow_succ, hd2, one_mul]
  have hd₀1 : d₀ ≠ 1 := fun e => by
    apply hdJ
    have : c.piK d₀ = 1 := by rw [e, map_one]
    rw [← hd₀pi, this]
    exact one_mem _
  obtain ⟨r₀, hr₀pi, hr₀d⟩ := c.exists_lift_commuting hd₀sq (y := rb) (by
    rw [hd₀pi]; exact hdr.symm)
  obtain ⟨e₀, he₀pi, he₀d⟩ := c.exists_lift_commuting hd₀sq (y := eb) (by
    rw [hd₀pi]; exact hde.symm)
  have hr₀J : r₀ ∈ c.Cg.subgroupOf c.Ng := c.mem_Cg_of_mem_JK (by rw [hr₀pi]; exact hrJ)
  obtain ⟨p, hp, hpo⟩ : ∃ p : ℕ, (p = 5 ∨ p = 7) ∧ orderOf rb = p := ⟨orderOf rb, hr, rfl⟩
  have hpprime : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hp3 : Nat.Coprime p 3 := by rcases hp with rfl | rfl <;> norm_num
  have hr₀p : r₀ ^ p ∈ CFSG.oddCore ↥c.Ng := by
    rw [← QuotientGroup.eq_one_iff]
    have : c.piK (r₀ ^ p) = 1 := by
      rw [map_pow, hr₀pi, ← hpo]; exact pow_orderOf_eq_one rb
    exact this
  have hr₁p : (r₀ ^ 3) ^ p = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; exact c.pow_three_eq_one_of_mem_oddCore h3 hr₀p
  have hr₁ne : r₀ ^ 3 ≠ 1 := fun e => by
    have h3 : rb ^ 3 = 1 := by rw [← hr₀pi, ← map_pow, e, map_one]
    have h1 := orderOf_dvd_of_pow_eq_one h3
    rw [hpo] at h1
    rcases hp with rfl | rfl <;> norm_num at h1
  have hr₁ord : orderOf (r₀ ^ 3) = p := by
    rcases (Nat.dvd_prime hpprime).mp (orderOf_dvd_of_pow_eq_one hr₁p) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hr₁ne
    · exact h
  have he₀sq := c.sq_mem_oddCore he₀pi he2
  have he₁sq : (e₀ ^ 3) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; exact c.pow_three_eq_one_of_mem_oddCore h3 he₀sq
  have he₁pi : c.piK (e₀ ^ 3) = eb := by
    rw [map_pow, he₀pi, pow_succ, he2, one_mul]
  have hr₁pi : c.piK (r₀ ^ 3) = rb ^ 3 := by rw [map_pow, hr₀pi]
  have hr₁J : r₀ ^ 3 ∈ c.Cg.subgroupOf c.Ng := (c.Cg.subgroupOf c.Ng).pow_mem hr₀J 3
  have hrel : e₀ ^ 3 * r₀ ^ 3 * (e₀ ^ 3)⁻¹ = (r₀ ^ 3)⁻¹ := by
    have hopi : c.piK (r₀ ^ 3 * (e₀ ^ 3 * r₀ ^ 3 * (e₀ ^ 3)⁻¹)) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, he₁pi, hr₁pi]
      have h1 : eb * rb ^ 3 * eb⁻¹ = (rb⁻¹) ^ 3 := by
        have := conj_pow (a := eb) (b := rb) (i := 3)
        rw [← this, her]
      rw [h1, inv_pow, mul_inv_cancel]
    have hoO : r₀ ^ 3 * (e₀ ^ 3 * r₀ ^ 3 * (e₀ ^ 3)⁻¹) ∈ CFSG.oddCore ↥c.Ng :=
      (QuotientGroup.eq_one_iff _).mp hopi
    have ho3 := c.pow_three_eq_one_of_mem_oddCore h3 hoO
    have hco : Commute (r₀ ^ 3)⁻¹ (r₀ ^ 3 * (e₀ ^ 3 * r₀ ^ 3 * (e₀ ^ 3)⁻¹)) :=
      (Commute.inv_left (c.commute_of_mem_Cg_oddCore h3 hr₁J hoO))
    have hord : orderOf (e₀ ^ 3 * r₀ ^ 3 * (e₀ ^ 3)⁻¹) = p := by
      have h := orderOf_injective (MulAut.conj (e₀ ^ 3)).toMonoidHom
        (MulAut.conj (e₀ ^ 3)).injective (r₀ ^ 3)
      exact h.trans hr₁ord
    have hprod : e₀ ^ 3 * r₀ ^ 3 * (e₀ ^ 3)⁻¹ =
        (r₀ ^ 3)⁻¹ * (r₀ ^ 3 * (e₀ ^ 3 * r₀ ^ 3 * (e₀ ^ 3)⁻¹)) := by group
    have hdvd3 : orderOf (r₀ ^ 3 * (e₀ ^ 3 * r₀ ^ 3 * (e₀ ^ 3)⁻¹)) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one ho3
    have hcop : (orderOf (r₀ ^ 3)⁻¹).Coprime
        (orderOf (r₀ ^ 3 * (e₀ ^ 3 * r₀ ^ 3 * (e₀ ^ 3)⁻¹))) := by
      rw [orderOf_inv, hr₁ord]
      exact Nat.Coprime.coprime_dvd_right hdvd3 hp3
    have hmul := hco.orderOf_mul_eq_mul_orderOf_of_coprime hcop
    rw [← hprod, hord, orderOf_inv, hr₁ord] at hmul
    have h1 : orderOf (r₀ ^ 3 * (e₀ ^ 3 * r₀ ^ 3 * (e₀ ^ 3)⁻¹)) = 1 := by
      have hppos : 0 < p := hpprime.pos
      nlinarith
    have h2 := orderOf_eq_one_iff.mp h1
    exact (eq_inv_of_mul_eq_one_right h2)
  refine ⟨d₀, r₀ ^ 3, e₀ ^ 3, p, hp, hd₀sq, hd₀1, he₁sq, hr₁ord, ?_, ?_, hrel⟩
  · exact ((Commute.pow_left (show Commute r₀ d₀ from hr₀d) 3).eq).symm
  · exact ((Commute.pow_left (show Commute e₀ d₀ from he₀d) 3).eq).symm

theorem false_of_card_OG_eq_three
    (h3 : Nat.card c.OG = 3)
    (hNCg : ¬ CFSG.HasNormalPComplement 2 ↥c.Cg) : False := by
  obtain ⟨d₀, r₁, e₁, p, hp, hd₀sq, hd₀1, he₁sq, hr₁ord, hdr, hde, hrel⟩ :=
    c.exists_configuration h3 hNCg
  have hD2 : ((d₀ : ↥c.Ng) : G) ^ 2 = 1 := by
    have := congrArg Subtype.val hd₀sq
    simpa using this
  have hD1 : ((d₀ : ↥c.Ng) : G) ≠ 1 := fun e => hd₀1 (Subtype.ext e)
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (S.oneClass ((d₀ : ↥c.Ng) : G) S.z (orderOf_eq_prime hD2 hD1) S.order_z)
  have hgD : g⁻¹ * S.z * g = ((d₀ : ↥c.Ng) : G) := by
    rw [← hg]; group
  have hRD : ((r₁ : ↥c.Ng) : G) * ((d₀ : ↥c.Ng) : G) = ((d₀ : ↥c.Ng) : G) * ((r₁ : ↥c.Ng) : G) :=
    congrArg Subtype.val hdr.symm
  have hED : ((e₁ : ↥c.Ng) : G) * ((d₀ : ↥c.Ng) : G) = ((d₀ : ↥c.Ng) : G) * ((e₁ : ↥c.Ng) : G) :=
    congrArg Subtype.val hde.symm
  have hrH : g * ((r₁ : ↥c.Ng) : G) * g⁻¹ ∈ S.H := by
    have := S.mem_H_of_commute (c := g⁻¹) (u := ((d₀ : ↥c.Ng) : G)) (y := ((r₁ : ↥c.Ng) : G))
      (by rw [inv_inv]; exact hgD) hRD
    simpa using this
  have heH : g * ((e₁ : ↥c.Ng) : G) * g⁻¹ ∈ S.H := by
    have := S.mem_H_of_commute (c := g⁻¹) (u := ((d₀ : ↥c.Ng) : G)) (y := ((e₁ : ↥c.Ng) : G))
      (by rw [inv_inv]; exact hgD) hED
    simpa using this
  have hE2 : ((e₁ : ↥c.Ng) : G) * ((e₁ : ↥c.Ng) : G) = 1 := by
    have := congrArg Subtype.val he₁sq
    simpa [pow_two] using this
  have hrelG : ((e₁ : ↥c.Ng) : G) * ((r₁ : ↥c.Ng) : G) * ((e₁ : ↥c.Ng) : G)⁻¹ =
      ((r₁ : ↥c.Ng) : G)⁻¹ := by
    have := congrArg Subtype.val hrel
    simpa using this
  have he2 : (⟨_, heH⟩ : S.H) ^ 2 = 1 := by
    apply Subtype.ext
    show (g * ((e₁ : ↥c.Ng) : G) * g⁻¹) ^ 2 = 1
    rw [pow_two]
    calc g * ((e₁ : ↥c.Ng) : G) * g⁻¹ * (g * ((e₁ : ↥c.Ng) : G) * g⁻¹)
        = g * (((e₁ : ↥c.Ng) : G) * ((e₁ : ↥c.Ng) : G)) * g⁻¹ := by group
      _ = 1 := by rw [hE2]; group
  have hinv : (⟨_, heH⟩ : S.H) * (⟨_, hrH⟩ : S.H) * (⟨_, heH⟩ : S.H)⁻¹ = (⟨_, hrH⟩ : S.H)⁻¹ := by
    apply Subtype.ext
    show g * ((e₁ : ↥c.Ng) : G) * g⁻¹ * (g * ((r₁ : ↥c.Ng) : G) * g⁻¹) *
      (g * ((e₁ : ↥c.Ng) : G) * g⁻¹)⁻¹ = (g * ((r₁ : ↥c.Ng) : G) * g⁻¹)⁻¹
    calc g * ((e₁ : ↥c.Ng) : G) * g⁻¹ * (g * ((r₁ : ↥c.Ng) : G) * g⁻¹) *
          (g * ((e₁ : ↥c.Ng) : G) * g⁻¹)⁻¹
        = g * (((e₁ : ↥c.Ng) : G) * ((r₁ : ↥c.Ng) : G) * ((e₁ : ↥c.Ng) : G)⁻¹) * g⁻¹ := by group
      _ = g * ((r₁ : ↥c.Ng) : G)⁻¹ * g⁻¹ := by rw [hrelG]
      _ = (g * ((r₁ : ↥c.Ng) : G) * g⁻¹)⁻¹ := by group
  have hord : orderOf (⟨_, hrH⟩ : S.H) = p := by
    rw [← Subgroup.orderOf_coe]
    show orderOf (g * ((r₁ : ↥c.Ng) : G) * g⁻¹) = p
    have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      ((r₁ : ↥c.Ng) : G)
    rw [Subgroup.orderOf_coe] at h
    exact h.trans hr₁ord
  exact S.cover.false_of_involution_inverts he2
    (by rcases hp with rfl | rfl; exact Or.inl hord; exact Or.inr hord) hinv

end Ctx



theorem twentySeven_dvd_card
    (S : Setup G) : 27 ∣ Nat.card G := by
  by_contra h27
  obtain ⟨c⟩ := S.exists_ctx
  have h3 := c.card_OG_eq_three h27
  have hNCg : ¬ CFSG.HasNormalPComplement 2 ↥c.Cg := fun hN =>
    S.false_of_hasNormalPComplement h27 c.x_cube c.x_type c.ht2 c.t_ne_one c.t_ne_z c.htx hN
  exact c.false_of_card_OG_eq_three h3 hNCg


end Setup

end CFSG.Sporadic.Recognition.JankoWong
