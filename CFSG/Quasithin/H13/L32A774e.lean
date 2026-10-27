module

public import CFSG.Quasithin.H13.L32A774d

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem perm5_center : ∀ σ : Equiv.Perm (Fin 5), (∀ τ : Equiv.Perm (Fin 5), σ * τ = τ * σ) →
    σ = 1 := by
  decide +kernel

theorem not_mem_pCoreOf_of_pow_three {H : Subgroup G} {x : G} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) : x ∉ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hxQ
  obtain ⟨k, hk'⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨x, hxQ⟩
  have h2k : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk'
  have hord : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2))
      (orderOf_dvd_of_pow_eq_one hx3) (orderOf_dvd_of_pow_eq_one h2k)
  exact hx1 (orderOf_eq_one_iff.mp hord)

namespace Ctx73

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx73 G T L V l₀)
include C

theorem mem_QH_of {n : G} (hnH : n ∈ hz T V) (hnU : ∀ u ∈ fsuU T V, n * u = u * n) :
    n ∈ pCoreOf 2 (hz T V) := by
  obtain ⟨φ, hs, hk⟩ := exists_phi C.hyp C.h63
  have hHU := C.hz_le_normalizer_fsuU
  have hφ1 : ∀ h : ↥(hz T V), φ h = 1 ↔ (h : G) ∈ pCoreOf 2 (hz T V) := fun h => by
    rw [← MonoidHom.mem_ker, hk, ← mem_pCoreOf_iff']
  let N : Subgroup ↥(hz T V) :=
    { carrier := {h | ∀ u ∈ fsuU T V, (h : G) * u = u * h}
      one_mem' := fun u _ => by simp
      mul_mem' := fun {a b} ha hb u hu => by
        rw [Subgroup.coe_mul, mul_assoc, hb u hu, ← mul_assoc, ha u hu, mul_assoc]
      inv_mem' := fun {a} ha u hu => by
        have h1 := ha u hu
        rw [Subgroup.coe_inv]
        calc (a : G)⁻¹ * u = (a : G)⁻¹ * (u * a) * (a : G)⁻¹ := by group
          _ = (a : G)⁻¹ * (a * u) * (a : G)⁻¹ := by rw [h1]
          _ = u * (a : G)⁻¹ := by group }
  have hNn : N.Normal := ⟨fun h hh g u hu => by
    have hu' : (g : G)⁻¹ * u * g ∈ fsuU T V := by
      have := (Subgroup.mem_normalizer_iff.mp (hHU (inv_mem g.2)) u).mp hu
      simpa using this
    have h1 := hh _ hu'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (g : G) * h * (g : G)⁻¹ * u = g * (h * ((g : G)⁻¹ * u * g)) * (g : G)⁻¹ := by group
      _ = g * (((g : G)⁻¹ * u * g) * h) * (g : G)⁻¹ := by rw [h1]
      _ = u * (g * h * (g : G)⁻¹) := by group⟩
  have hM : (N.map φ).Normal := hNn.map φ hs
  have hMA : ∀ σ ∈ N.map φ, σ ∈ alternatingGroup (Fin 5) → σ = 1 := by
    have hsimp : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hMn : ((N.map φ).subgroupOf (alternatingGroup (Fin 5))).Normal := hM.subgroupOf _
    rcases hMn.eq_bot_or_eq_top with hb | ht
    · intro σ hσ hσA
      have : (⟨σ, hσA⟩ : ↥(alternatingGroup (Fin 5))) ∈
          (N.map φ).subgroupOf (alternatingGroup (Fin 5)) := Subgroup.mem_subgroupOf.mpr hσ
      rw [hb] at this
      exact congrArg Subtype.val ((Subgroup.mem_bot).mp this)
    · exfalso
      obtain ⟨x, hxL1, hx3, hx1, -⟩ := C.exists_x3
      have hxH : x ∈ hz T V := le_sup_left.trans C.hF.L₁T_le_H hxL1
      have hxK : x ∈ kz T V := l1_le_kz C.hyp C.hMod hxL1
      have hxA : φ ⟨x, hxH⟩ ∈ alternatingGroup (Fin 5) := by
        rw [Equiv.Perm.mem_alternatingGroup]
        exact sign_phi_kz hxK
      have hxM : φ ⟨x, hxH⟩ ∈ N.map φ := by
        have : (⟨_, hxA⟩ : ↥(alternatingGroup (Fin 5))) ∈
            (N.map φ).subgroupOf (alternatingGroup (Fin 5)) := by
          rw [ht]
          exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
      obtain ⟨h, hhN, hhx⟩ := hxM
      have hq : ((h⁻¹ * ⟨x, hxH⟩ : ↥(hz T V)) : G) ∈ pCoreOf 2 (hz T V) :=
        (hφ1 _).mp (by rw [map_mul, map_inv, hhx, inv_mul_cancel])
      obtain ⟨u, hu, huV⟩ := C.exists_mem_fsuU C.u0_eq
      apply huV
      have hu1 : u ∈ fsuV1 T V := by
        refine C.mem_fsuV1_of_comm hxL1 hx3 hx1 hu ?_
        set q := ((h⁻¹ * ⟨x, hxH⟩ : ↥(hz T V)) : G) with hqdef
        have hxq : x = (h : G) * q := by rw [hqdef]; simp
        have hc := C.comm_mem_fsuV1 hq hu
        have hcU : q * u * q⁻¹ ∈ fsuU T V :=
          (Subgroup.mem_normalizer_iff.mp (hHU ((pCoreOf_le 2 _) hq)) u).mp hu
        have hh := hhN _ hcU
        rw [hxq, show (h : G) * q * u * ((h : G) * q)⁻¹ * u⁻¹ =
          ((h : G) * (q * u * q⁻¹)) * (h : G)⁻¹ * u⁻¹ by group, hh,
          show q * u * q⁻¹ * h * (h : G)⁻¹ * u⁻¹ = q * u * q⁻¹ * u⁻¹ by group]
        exact hc
      exact (Subgroup.mem_inf.mp hu1).1
  have hMc : ∀ σ ∈ N.map φ, σ = 1 := by
    intro σ hσ
    refine perm5_center σ fun τ => ?_
    have h1 : σ * τ * σ⁻¹ * τ⁻¹ ∈ N.map φ := by
      have := hM.conj_mem _ (inv_mem hσ) τ
      rw [show τ * σ⁻¹ * τ⁻¹ = (τ * σ⁻¹ * τ⁻¹) by rfl] at this
      exact mul_mem hσ this |> fun h => by rwa [show σ * (τ * σ⁻¹ * τ⁻¹) =
        σ * τ * σ⁻¹ * τ⁻¹ by group] at h
    have h2 : σ * τ * σ⁻¹ * τ⁻¹ ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul, map_mul, map_inv, map_inv]
      rw [mul_comm (Equiv.Perm.sign σ) (Equiv.Perm.sign τ)]
      group
    have h3 := hMA _ h1 h2
    calc σ * τ = (σ * τ * σ⁻¹ * τ⁻¹) * (τ * σ) := by group
      _ = τ * σ := by rw [h3, one_mul]
  have hn : φ ⟨n, hnH⟩ = 1 := hMc _ ⟨⟨n, hnH⟩, hnU, rfl⟩
  exact (hφ1 _).mp hn

theorem T_inf_kz_le_R1 : T ⊓ kz T V ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hs, hk⟩ := exists_phi C.hyp C.h63
  obtain ⟨-, h4⟩ := R1_le_kz_sup C.setting C.hF C.h63 C.h1222 C.h1332 C.h1334
  have hT := C.hyp.fsu.sylow
  have hTH : T ≤ hz T V := le_sup_right.trans C.hF.L₁T_le_H
  have hL1H : L₁Of L (fsuV1 T V) ≤ hz T V := le_sup_left.trans C.hF.L₁T_le_H
  have hR1T : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T := pCoreOf_le_of_le C.hyp le_sup_right
  have hR1H := hR1T.trans hTH
  have hTi : ¬ 2 ∣ (T.subgroupOf (hz T V)).index := by
    intro hd
    apply hT.2
    rw [← Subgroup.relIndex_mul_index hTH]
    exact Dvd.dvd.mul_right hd _
  have h8 := relIndex_phi_sylow hs hk hTH hT.1 hTi
  have hφ1 : ∀ h : ↥(hz T V), φ h = 1 ↔ (h : G) ∈ pCoreOf 2 (hz T V) := fun h => by
    rw [← MonoidHom.mem_ker, hk, ← mem_pCoreOf_iff']
  set ΦT := (T.subgroupOf (hz T V)).map φ with hΦT
  set ΦR := ((pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)).subgroupOf (hz T V)).map φ with hΦR
  have hcT : Nat.card ↥ΦT = 8 := by rw [card_map_phi hk hTH, h8]
  have hcR : Nat.card ↥ΦR = 4 := by rw [card_map_phi hk hR1H, h4]
  obtain ⟨x, hxL1, hx3, hx1, -⟩ := C.exists_x3
  have hxH : x ∈ hz T V := hL1H hxL1
  have hxQ : x ∉ pCoreOf 2 (hz T V) := not_mem_pCoreOf_of_pow_three hx3 hx1
  have hxR : x ∈ Subgroup.normalizer (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hxL1)
  have hRA : ΦR ≤ ΦT ⊓ alternatingGroup (Fin 5) := by
    rintro _ ⟨r, hr, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨⟨r, Subgroup.mem_subgroupOf.mpr
      (hR1T (Subgroup.mem_subgroupOf.mp hr)), rfl⟩, ?_⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    exact sign_phi_of_card_four hk hR1H h4 hxH hx3 hxQ hxR (Subgroup.mem_subgroupOf.mp hr)
  have hcA : Nat.card ↥(ΦT ⊓ alternatingGroup (Fin 5)) ≤ 4 := by
    have h1 : Nat.card ↥(ΦT ⊓ alternatingGroup (Fin 5)) ∣ 8 := by
      rw [← hcT]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(ΦT ⊓ alternatingGroup (Fin 5)) ∣ 60 := by
      have : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        rfl
      rw [← this]
      exact Subgroup.card_dvd_of_le inf_le_right
    have h3 : Nat.card ↥(ΦT ⊓ alternatingGroup (Fin 5)) ∣ 4 := by
      have := Nat.dvd_gcd h1 h2
      rwa [show Nat.gcd 8 60 = 4 by norm_num] at this
    exact Nat.le_of_dvd (by norm_num) h3
  have heq : ΦR = ΦT ⊓ alternatingGroup (Fin 5) :=
    Subgroup.eq_of_le_of_card_ge hRA (by rw [hcR]; exact hcA)
  intro t ht
  obtain ⟨htT, htK⟩ := Subgroup.mem_inf.mp ht
  have htH := hTH htT
  have htA : φ ⟨t, htH⟩ ∈ ΦT ⊓ alternatingGroup (Fin 5) := by
    refine Subgroup.mem_inf.mpr ⟨⟨⟨t, htH⟩, Subgroup.mem_subgroupOf.mpr htT, rfl⟩, ?_⟩
    rw [Equiv.Perm.mem_alternatingGroup]
    exact sign_phi_kz htK
  rw [← heq] at htA
  obtain ⟨r, hr, hrt⟩ := htA
  have hq : ((r⁻¹ * ⟨t, htH⟩ : ↥(hz T V)) : G) ∈ pCoreOf 2 (hz T V) :=
    (hφ1 _).mp (by rw [map_mul, map_inv, hrt, inv_mul_cancel])
  have hqR := C.QH_le_R1 hq
  have := mul_mem (Subgroup.mem_subgroupOf.mp hr) hqR
  simpa using this

end Ctx73

end CFSG.Quasithin.H13.L32A
