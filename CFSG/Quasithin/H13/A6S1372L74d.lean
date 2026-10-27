module

public import CFSG.Quasithin.H13.A6S1372L74c
public import CFSG.Quasithin.H13.U3L14Blk

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative

namespace A6L74

variable {G : Type} [Group G]

theorem comm_mul_inv_eq {A : Subgroup G} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {k N a : G}
    (hN : N ∈ A) (ha : a ∈ A) (hb : k * a * k⁻¹ ∈ A) (hkN : k * N * k⁻¹ = N) :
    k * (N * a⁻¹) * k⁻¹ * (N * a⁻¹)⁻¹ = (k * a * k⁻¹ * a⁻¹)⁻¹ := by
  obtain ⟨b, hbdef⟩ : ∃ b, b = k * a * k⁻¹ := ⟨_, rfl⟩
  rw [← hbdef] at hb ⊢
  have hNb : Commute N b := hA N hN b hb
  have hNa : Commute N a := hA N hN a ha
  have hab : Commute a b := hA a ha b hb
  have e1 : k * (N * a⁻¹) * k⁻¹ * (N * a⁻¹)⁻¹ = (k * N * k⁻¹) * (k * a * k⁻¹)⁻¹ * (a * N⁻¹) := by
    group
  rw [e1, hkN, ← hbdef]
  calc N * b⁻¹ * (a * N⁻¹) = b⁻¹ * N * (a * N⁻¹) := by rw [hNb.inv_right.eq]
    _ = b⁻¹ * (N * a) * N⁻¹ := by group
    _ = b⁻¹ * (a * N) * N⁻¹ := by rw [hNa.eq]
    _ = b⁻¹ * a := by group
    _ = a * b⁻¹ := (hab.inv_right.eq).symm
    _ = (b * a⁻¹)⁻¹ := by group

end A6L74

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

section Block

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz)
include hNS h13315 h1356two hH

theorem sixteen_mul_nu_U0_le (h13314 : Stmt13_3_14)
    (hhat : ¬ IsHatA6 L) (hab : IsElemAbelian 2 (conjClosure S.V3 H)) :
    16 * nu (S.cL1 hhat : G) (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) ≤
      nu (S.cL1 hhat : G) (pCoreOf 2 H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c : G := (S.cL1 hhat : G) with hcdef
  have hc3 : c ^ 3 = 1 := S.cL1_cube hhat
  have hcL : c ∈ S.L1 := S.cL1_mem hhat
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hL1H := S.L1_le_of_mem_Hz hNS h13315 h1356two hH
  have hcH : c ∈ H := hL1H hcL
  have hHQ : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hHU : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hQH : pCoreOf 2 H ≤ H := pCoreOf_le 2 H
  have hHCQ : pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G) ≤ pCoreOf 2 H :=
    inf_le_left
  have hNHC : cfix c (pCoreOf 2 H) ≤ Subgroup.normalizer ((pCoreOf 2 H ⊓
      Subgroup.centralizer (conjClosure S.V3 H : Set G) : Subgroup G) : Set G) := by
    intro x hx
    have hxH := hQH (mem_cfix.1 hx).1
    exact mem_normalizer_inf_of (hHQ hxH) (normalizes_of_conj_mem (X := H) (fun l hl y hy =>
      conj_centralizer_mem (hHU hl) hy) hxH)
  have hU0U : conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤
      conjClosure S.V3 H := inf_le_left
  have hNU0 : cfix c (conjClosure S.V3 H) ≤ Subgroup.normalizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) := by
    intro x hx
    have hxH := hQH (hF.conjClosure_Vp_le_pCoreOf (mem_cfix.1 hx).1)
    exact mem_normalizer_inf_of (hHU hxH) (normalizes_of_conj_mem (X := H) (fun l hl y hy =>
      conj_centralizer_mem (hHQ hl) hy) hxH)
  have hdual := nu_dual_F97 hF hab hcH hc3
  have hC : nu c (pCoreOf 2 H) =
      (cfix c (conjClosure S.V3 H) ⊔ (conjClosure S.V3 H ⊓
        Subgroup.centralizer (pCoreOf 2 H : Set G))).relIndex (conjClosure S.V3 H) *
      nu c (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)) := by
    rw [nu_mul c hHCQ hNHC, hdual]
  have hv2U : S.v2 ∈ conjClosure S.V3 H := S.v2_mem_UH H
  have hcU : c ∈ Subgroup.normalizer (conjClosure S.V3 H : Set G) := hHU hcH
  have hcU0 : c ∈ Subgroup.normalizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf_of hcU (normalizes_of_conj_mem (X := H) (fun l hl y hy =>
      conj_centralizer_mem (hHQ hl) hy) hcH)
  have hcv : c * S.v2 * c⁻¹ * S.v2⁻¹ ∉ conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    intro h
    have hV3 : c * S.v2 * c⁻¹ * S.v2⁻¹ ∈ S.V3 :=
      S.V3.mul_mem (S.conj_v2_mem_V3 (S.cL1_rho hhat)) (S.V3.inv_mem S.v2_mem_V3)
    exact S.comm_v2_not_mem_V1 (S.cL1_rho hhat)
      (S.V3_inf_centralizer_QH_le hNS h13315 h1356two hH h13314 ⟨hV3, h.2⟩)
  have hU2 : IsPGroup 2 ↥(conjClosure S.V3 H) :=
    (pCoreOf_isPGroup 2 H).to_le hF.conjClosure_Vp_le_pCoreOf
  have hD4 := four_mul_nu_le hc3 hU2 hU0U hcU hcU0 hNU0 ⟨S.v2, hv2U, hcv⟩
  have hpos : 0 < nu c (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) := by
    unfold nu
    exact Nat.pos_of_ne_zero (by
      show ((cfix c _).subgroupOf _).index ≠ 0
      exact Subgroup.index_ne_zero_of_finite)
  have hU := nu_mul c hU0U hNU0
  have hD : 4 ≤ (cfix c (conjClosure S.V3 H) ⊔ (conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G))).relIndex (conjClosure S.V3 H) := by
    rw [hU] at hD4
    exact Nat.le_of_mul_le_mul_right (by linarith) hpos
  have hUQC : conjClosure S.V3 H ≤
      pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G) := by
    refine le_inf hF.conjClosure_Vp_le_pCoreOf fun u hu => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := hab.1.is_comm.comm (⟨w, hw⟩ : ↥(conjClosure S.V3 H)) ⟨u, hu⟩
    exact congrArg Subtype.val this
  have hE2 : nu c (conjClosure S.V3 H) ≤
      nu c (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)) :=
    nu_le_nu hUQC fun x hx => hHU (hQH (mem_cfix.1 hx).1.1)
  rw [hC]
  set r := (cfix c (conjClosure S.V3 H) ⊔ (conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G))).relIndex (conjClosure S.V3 H) with hr
  set n := nu c (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) with hn
  rw [hU] at hE2
  calc 16 * n = 4 * (4 * n) := by ring
    _ ≤ r * (r * n) := by gcongr
    _ ≤ r * nu c (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure S.V3 H : Set G)) := by
      gcongr

theorem comm_U0_of_block (h1222 : Stmt12_2_2)
    (h323 : Stmt3_2_3) (h13314 : Stmt13_3_14) (hhat : ¬ IsHatA6 L)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (hB : H13.IsA6Block L) {x : G}
    (hx : x ∈ conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) :
    (S.cL1 hhat : G) * x = x * (S.cL1 hhat : G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c : G := (S.cL1 hhat : G) with hcdef
  have hc3 : c ^ 3 = 1 := S.cL1_cube hhat
  have hcL : c ∈ S.L1 := S.cL1_mem hhat
  obtain ⟨x₀, hx₀, hx₀3, -, hx₀N, hρx₀⟩ := U3.L15A.exists_X_nonhat S hhat
  have S14 := S14.set14_of h1222 h323 S S.isV2 (S14.plusData_L1 S hhat)
    (S14.bcase_of S (oTwoRes_le _ hx₀) hx₀3 hx₀N hρx₀) ⟨fun h => absurd h hhat, fun _ => rfl⟩
  have h16 := S14.relIndex_R1_le_sixteen (Or.inr hB) hcL hc3
  have hnuR : nu c (pCoreOf 2 (S.L1 ⊔ T)) =
      (Subgroup.centralizer ({c} : Set G)).relIndex (pCoreOf 2 (S.L1 ⊔ T)) := by
    rw [nu, cfix, inf_comm, Subgroup.inf_relIndex_right]
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_sylow S.h13.sylow hTH
  have hQR : pCoreOf 2 H ≤ pCoreOf 2 (S.L1 ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
      (hH.1.1.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  have hRH : pCoreOf 2 (S.L1 ⊔ T) ≤ H := (pCoreOf_le 2 _).trans hH.1.1
  have hle : nu c (pCoreOf 2 H) ≤ nu c (pCoreOf 2 (S.L1 ⊔ T)) :=
    nu_le_nu hQR fun y hy => le_normalizer_pCoreOf 2 H (hRH (mem_cfix.1 hy).1)
  have h16' := S.sixteen_mul_nu_U0_le hNS h13315 h1356two hH h13314 hhat hab
  rw [← hcdef] at h16'
  have hnu1 : nu c (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) ≤ 1 := by
    rw [hnuR] at hle
    omega
  have hnu : nu c (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) = 1 := by
    have hpos : 0 < nu c (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) := by
      unfold nu
      exact Nat.pos_of_ne_zero (by
        show ((cfix c _).subgroupOf _).index ≠ 0
        exact Subgroup.index_ne_zero_of_finite)
    omega
  have hmem : x ∈ cfix c (conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)) :=
    Subgroup.relIndex_eq_one.mp hnu hx
  exact (mem_cfix.1 hmem).2

theorem le_centralizer_V3_of_block (h1222 : Stmt12_2_2)
    (h323 : Stmt3_2_3) (h13314 : Stmt13_3_14) (hhat : ¬ IsHatA6 L)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) (hB : H13.IsA6Block L) {K : Subgroup G}
    (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hK2 : oTwoRes K = K)
    (hKC : K ≤ S.C74 H)
    (hKU : K ⊓ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) ≤ pCoreOf 2 K) :
    K ≤ Subgroup.centralizer (S.V3 : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c : G := (S.cL1 hhat : G) with hcdef
  have hc3 : c ^ 3 = 1 := S.cL1_cube hhat
  have hcL : c ∈ S.L1 := S.cL1_mem hhat
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hL1H := S.L1_le_of_mem_Hz hNS h13315 h1356two hH
  have hcH : c ∈ H := hL1H hcL
  have hcU0 := fun {x : G} (hx : x ∈ conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G)) =>
    S.comm_U0_of_block hNS h13315 h1356two hH h1222 h323 h13314 hhat hab hB hx
  rw [← hcdef] at hcU0
  have hHU : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hHU0 : H ≤ Subgroup.normalizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) :=
    S.le_normalizer_U0 (H := H)
  have hUab : ∀ x ∈ conjClosure S.V3 H, ∀ y ∈ conjClosure S.V3 H, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hV3U : S.V3 ≤ conjClosure S.V3 H := le_conjClosure S.V3 H
  have hcV : c ∈ Subgroup.normalizer (S.V3 : Set G) := S.L1T_le_NV3 (Subgroup.mem_sup_left hcL)
  have hOQ : pCoreOf 2 K ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
      (hHK.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  have hkV : ∀ k ∈ K, ∀ v ∈ S.V3, k * v * k⁻¹ * v⁻¹ ∈ fsuV1 T V := by
    intro k hk v hv
    have hkH : k ∈ H := hKH hk
    obtain ⟨hkH', hku⟩ := (S.mem_C74_iff).1 (hKC hk)
    have hqK : k * c * k⁻¹ * c⁻¹ ∈ K := by
      have h1 : c * k⁻¹ * c⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hHK hcH) k⁻¹).mp (K.inv_mem hk)
      have e : k * c * k⁻¹ * c⁻¹ = k * (c * k⁻¹ * c⁻¹) := by group
      rw [e]
      exact K.mul_mem hk h1
    have hqU : k * c * k⁻¹ * c⁻¹ ∈ Subgroup.centralizer ((conjClosure S.V3 H ⊓
        Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx1 : k⁻¹ * x * k⁻¹⁻¹ ∈ conjClosure S.V3 H ⊓
          Subgroup.centralizer (pCoreOf 2 H : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (hHU0 (H.inv_mem hkH)) x).mp hx
      have h1 := hcU0 hx
      have h2 := hcU0 hx1
      have h1' : c⁻¹ * x = x * c⁻¹ := by
        calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * x) * c⁻¹ := by rw [h1]
          _ = x * c⁻¹ := by group
      calc x * (k * c * k⁻¹ * c⁻¹) = k * ((k⁻¹ * x * k⁻¹⁻¹) * c) * k⁻¹ * c⁻¹ := by group
        _ = k * (c * (k⁻¹ * x * k⁻¹⁻¹)) * k⁻¹ * c⁻¹ := by rw [h2]
        _ = k * c * k⁻¹ * (x * c⁻¹) := by group
        _ = k * c * k⁻¹ * (c⁻¹ * x) := by rw [h1']
        _ = (k * c * k⁻¹ * c⁻¹) * x := by group
    have hqQ : k * c * k⁻¹ * c⁻¹ ∈ pCoreOf 2 H := hOQ (hKU ⟨hqK, hqU⟩)
    obtain ⟨v₁, hv₁⟩ : ∃ v₁, v₁ = c * v * c⁻¹ := ⟨_, rfl⟩
    obtain ⟨v₂, hv₂⟩ : ∃ v₂, v₂ = c * v₁ * c⁻¹ := ⟨_, rfl⟩
    have hv₁V : v₁ ∈ S.V3 := hv₁ ▸ (Subgroup.mem_normalizer_iff.mp hcV v).mp hv
    have hv₂V : v₂ ∈ S.V3 := hv₂ ▸ (Subgroup.mem_normalizer_iff.mp hcV v₁).mp hv₁V
    have hcv₂ : c * v₂ * c⁻¹ = v := by
      rw [hv₂, hv₁]
      have e : c * c * c = 1 := by rw [← pow_three', hc3]
      calc c * (c * (c * v * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * v * (c * c * c)⁻¹ := by group
        _ = v := by rw [e]; group
    obtain ⟨N, hNdef⟩ : ∃ N, N = v * v₁ * v₂ := ⟨_, rfl⟩
    have hNV : N ∈ S.V3 := hNdef ▸ S.V3.mul_mem (S.V3.mul_mem hv hv₁V) hv₂V
    have hab3 : ∀ x ∈ S.V3, ∀ y ∈ S.V3, x * y = y * x := fun x hx y hy =>
      hUab x (hV3U hx) y (hV3U hy)
    have hcN : c * N * c⁻¹ = N := by
      rw [hNdef]
      calc c * (v * v₁ * v₂) * c⁻¹ = (c * v * c⁻¹) * (c * v₁ * c⁻¹) * (c * v₂ * c⁻¹) := by group
        _ = v₁ * v₂ * v := by rw [← hv₁, ← hv₂, hcv₂]
        _ = v * v₁ * v₂ := by
          rw [hab3 _ (S.V3.mul_mem hv₁V hv₂V) v hv, mul_assoc]
    have hNV1 : N ∈ fsuV1 T V := by
      refine mem_V1_of_c012 (S.cL1_rho hhat) hNV ?_
      rw [← hcdef, hcN, mul_inv_cancel]
      exact Subgroup.one_mem _
    have hsq : v₁ * v₁ = 1 := by
      have := (hF.elemAbelian_Vp.2 v₁ hv₁V)
      rwa [pow_two] at this
    obtain ⟨a, hadef⟩ : ∃ a, a = c * v₁ * c⁻¹ * v₁⁻¹ := ⟨_, rfl⟩
    have haV : a ∈ S.V3 := hadef ▸ S.V3.mul_mem ((Subgroup.mem_normalizer_iff.mp hcV v₁).mp hv₁V)
      (S.V3.inv_mem hv₁V)
    have hvNa : v = N * a⁻¹ := by
      rw [hNdef, hadef, ← hv₂]
      calc v = v * (v₁ * v₁) := by rw [hsq, mul_one]
        _ = v * v₁ * (v₂ * v₁ * v₂⁻¹) := by
          rw [mul_assoc, hab3 v₂ hv₂V v₁ hv₁V]; group
        _ = v * v₁ * v₂ * (v₂ * v₁⁻¹)⁻¹ := by group
    have hka : k * a * k⁻¹ * a⁻¹ ∈ fsuV1 T V := by
      rw [hadef]
      refine A6L74.comm_comm_mem hUab (hHU hcH) (hHU hkH) (hV3U hv₁V) ?_ (fun b hb =>
        hF.commutator_mem_V₁ hqQ hb)
      have hu : k * v₁ * k⁻¹ * v₁⁻¹ ∈ conjClosure S.V3 H ⊓
          Subgroup.centralizer (pCoreOf 2 H : Set G) :=
        ⟨(conjClosure S.V3 H).mul_mem ((Subgroup.mem_normalizer_iff.mp (hHU hkH) v₁).mp
          (hV3U hv₁V)) ((conjClosure S.V3 H).inv_mem (hV3U hv₁V)), hku v₁ (hV3U hv₁V)⟩
      rw [hcU0 hu]
      group
    have hkN : k * N * k⁻¹ = N := hF.conj_eq_of_mem_V₁ hkH hNV1
    have hb : k * a * k⁻¹ ∈ conjClosure S.V3 H :=
      (Subgroup.mem_normalizer_iff.mp (hHU hkH) a).mp (hV3U haV)
    rw [hvNa, A6L74.comm_mul_inv_eq hUab (hV3U hNV) (hV3U haV) hb hkN]
    exact (fsuV1 T V).inv_mem hka
  rw [← hK2]
  refine (Subgroup.closure_le _).2 ?_
  rintro k ⟨hk, m, hm, hkm⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := A6L74.conj_eq_of_odd hF.elemAbelian_Vp (S.V1_le_V2.trans S.V2_le_V3)
    (fun w hw => hF.conj_eq_of_mem_V₁ (hKH hk) hw) (hkV k hk) hm hkm hv
  calc v * k = k * v * k⁻¹ * k := by rw [h1]
    _ = k * v := by group

theorem not_isA6Block_of (h1222 : Stmt12_2_2)
    (h323 : Stmt3_2_3) (h13314 : Stmt13_3_14) (hhat : ¬ IsHatA6 L)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) {K : Subgroup G}
    (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hK2 : oTwoRes K = K)
    (hKC : K ≤ S.C74 H)
    (hKU : K ⊓ Subgroup.centralizer ((conjClosure S.V3 H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) ≤ pCoreOf 2 K)
    (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G)) : ¬ H13.IsA6Block L := fun hB =>
  hKM ((S.le_centralizer_V3_of_block hNS h13315 h1356two hH h1222 h323 h13314 hhat hab hB hKH
    hHK hK2 hKC hKU).trans ((S.centralizer_V3_le h13315).trans S.NV_le_M))

end Block

end Setting4

end CFSG.Quasithin.H13.A6
