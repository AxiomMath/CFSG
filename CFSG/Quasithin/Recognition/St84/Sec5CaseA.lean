module

public import CFSG.Quasithin.Recognition.St84.Sec5Step7
public import CFSG.Quasithin.Recognition.St84.Nat16
public import CFSG.Quasithin.Background.GoldschmidtAmalgamPairBasic
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2TSpecial
import CFSG.Quasithin.Recognition.HSTypeK
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourSymmetricFourCentralizerOrderThree
import CFSG.GroupTheory.CommuteOfCommutator
import CFSG.GroupTheory.FixedCosetCommutator
import CFSG.GroupTheory.Commutator.RelIndexLeFour
public import CFSG.Quasithin.Background.GoldschmidtAmalgamNVertex
public import CFSG.Quasithin.Recognition.F112RShapes
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s n₀ : ℕ}

private theorem perm_commute_of_card_four {W : Type*} [Fintype W] (hW : Fintype.card W = 4)
    (β α τ : Equiv.Perm W) (hβ1 : β ≠ 1) (hβ3 : β ^ 3 = 1)
    (hαβ : α * β = β * α) (hτβ : τ * β = β * τ) : α * τ = τ * α := by
  let eM : Equiv.Perm W ≃* Equiv.Perm (Fin 4) :=
    Equiv.permCongrHom (Fintype.equivFinOfCardEq hW)
  have hβ'1 : eM β ≠ 1 := by
    intro h
    apply hβ1
    exact eM.injective (by simpa using h)
  have hβ'3 : (eM β) ^ 3 = 1 := by
    rw [← map_pow, hβ3, map_one]
  have hα'β' : eM α * eM β = eM β * eM α := by
    rw [← map_mul, ← map_mul, hαβ]
  have hτ'β' : eM τ * eM β = eM β * eM τ := by
    rw [← map_mul, ← map_mul, hτβ]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hβ'ord : orderOf (eM β) = 3 := orderOf_eq_prime hβ'3 hβ'1
  have hα'mem : eM α ∈ Subgroup.zpowers (eM β) := by
    rw [← CFSG.GorensteinWalter.sFour_centralizer_order_three_eq_zpowers hβ'ord,
      Subgroup.mem_centralizer_singleton_iff]
    exact hα'β'
  have hτ'mem : eM τ ∈ Subgroup.zpowers (eM β) := by
    rw [← CFSG.GorensteinWalter.sFour_centralizer_order_three_eq_zpowers hβ'ord,
      Subgroup.mem_centralizer_singleton_iff]
    exact hτ'β'
  have hατ : eM α * eM τ = eM τ * eM α := by
    have h := (Subgroup.zpowers_isMulCommutative (eM β)).is_comm.comm
      ⟨eM α, hα'mem⟩ ⟨eM τ, hτ'mem⟩
    exact congrArg Subtype.val h
  apply eM.injective
  simpa using hατ

private theorem false_of_trivial_quotient_action
    {Q C : Subgroup G} {k : G} [Finite ↥Q]
    (hCQ : C ≤ Q) (hCcard : Nat.card C = 8) (hQcard : Nat.card Q = 32)
    (hCnorm : ∀ q ∈ Q, ∀ c ∈ C, q * c * q⁻¹ ∈ C)
    (hkQ : k ∈ Subgroup.normalizer (Q : Set G)) (hk3 : k ^ 3 = 1)
    (hCk : ∀ q ∈ Q, k * q * k⁻¹ = q → q ∈ C)
    (hktriv : ∀ q ∈ Q, k * q * k⁻¹ * q⁻¹ ∈ C) : False := by
  haveI : Fintype ↥Q := Fintype.ofFinite ↥Q
  haveI hCfin : Finite ↥C :=
    Finite.of_injective (Subgroup.inclusion hCQ) (Subgroup.inclusion_injective hCQ)
  have hkCmap : ∀ c ∈ C, k * c * k⁻¹ ∈ C := by
    intro c hc
    have h1 : k * c * k⁻¹ * c⁻¹ ∈ C := hktriv c (hCQ hc)
    have h2 : k * c * k⁻¹ = (k * c * k⁻¹ * c⁻¹) * c := by group
    rw [h2]
    exact C.mul_mem h1 hc
  have hq₀ : ∃ q : ↥Q, (q : G) ∉ C := by
    by_contra h
    push Not at h
    have hQC : Q ≤ C := fun q hq => h ⟨q, hq⟩
    have := Subgroup.card_le_of_le hQC
    omega
  obtain ⟨q0, hq0⟩ := hq₀
  let S : Set ↥Q := {x | ∃ c ∈ C, (q0 : G) * (c : G) = (x : G)}
  have hS8 : Nat.card ↥S = 8 := by
    let f : ↥C → ↥S := fun c =>
      ⟨⟨(q0 : G) * (c : G), Q.mul_mem q0.2 (hCQ c.2)⟩, ⟨(c : G), c.2, rfl⟩⟩
    have hf_inj : Function.Injective f := by
      intro a b hab
      have h : (q0 : G) * (a : G) = (q0 : G) * (b : G) :=
        congrArg (fun x : ↥S => ((x : ↥Q) : G)) hab
      exact Subtype.ext (mul_left_cancel h)
    have hf_surj : Function.Surjective f := by
      intro x
      obtain ⟨c, hc, hxc⟩ := x.2
      refine ⟨⟨c, hc⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hxc
    have e : ↥C ≃ ↥S := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
    calc Nat.card ↥S = Nat.card ↥C := (Nat.card_congr e).symm
      _ = 8 := hCcard
  let σ : ↥Q → ↥Q := fun y =>
    ⟨k * (y : G) * k⁻¹, (Subgroup.mem_normalizer_iff.mp hkQ (y : G)).mp y.2⟩
  have hmap : ∀ y ∈ S, σ y ∈ S := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := hx
    have h1 : k * (x : G) * k⁻¹ = (k * (q0 : G) * k⁻¹) * (k * c * k⁻¹) := by
      rw [← hxc]; group
    have hc₁ : k * (q0 : G) * k⁻¹ * (q0 : G)⁻¹ ∈ C := hktriv (q0 : G) q0.2
    have hc₂ : k * c * k⁻¹ ∈ C := hkCmap c hc
    have hc₃ : (k * (q0 : G) * k⁻¹ * (q0 : G)⁻¹) *
        ((q0 : G) * (k * c * k⁻¹) * (q0 : G)⁻¹) ∈ C :=
      C.mul_mem hc₁ (hCnorm (q0 : G) q0.2 (k * c * k⁻¹) hc₂)
    have hc₄ : (q0 : G)⁻¹ * ((k * (q0 : G) * k⁻¹ * (q0 : G)⁻¹) *
        ((q0 : G) * (k * c * k⁻¹) * (q0 : G)⁻¹)) * ((q0 : G)⁻¹)⁻¹ ∈ C :=
      hCnorm (q0 : G)⁻¹ (Q.inv_mem q0.2) _ hc₃
    refine ⟨_, hc₄, ?_⟩
    show (q0 : G) * ((q0 : G)⁻¹ * ((k * (q0 : G) * k⁻¹ * (q0 : G)⁻¹) *
      ((q0 : G) * (k * c * k⁻¹) * (q0 : G)⁻¹)) * ((q0 : G)⁻¹)⁻¹) = k * (x : G) * k⁻¹
    rw [← hxc]
    group
  have hσ3 : ∀ y, σ (σ (σ y)) = y := by
    intro y
    apply Subtype.ext
    simp only [σ]
    have h : k * k * k = 1 := by
      rw [mul_assoc, ← pow_three]
      exact hk3
    calc k * (k * (k * (y : G) * k⁻¹) * k⁻¹) * k⁻¹
        = (k * k * k) * (y : G) * (k * k * k)⁻¹ := by group
      _ = (y : G) := by rw [h, one_mul, inv_one, mul_one]
  have hno : ∀ y ∈ S, σ y ≠ y := by
    intro y hyS hfix
    have hky : k * (y : G) * k⁻¹ = (y : G) := by
      simpa [σ] using congrArg Subtype.val hfix
    have hyC : (y : G) ∈ C := hCk (y : G) y.2 hky
    obtain ⟨c, hc, hxc⟩ := hyS
    have hq0C : (q0 : G) ∈ C := by
      have h1 : (q0 : G) = (y : G) * (c : G)⁻¹ := by
        rw [← hxc]; group
      rw [h1]
      exact C.mul_mem hyC (C.inv_mem hc)
    exact hq0 hq0C
  classical
  have hSfin : S.Finite := Set.toFinite S
  have h3dvd : 3 ∣ S.ncard := by
    rw [Set.ncard_eq_toFinset_card S hSfin]
    exact CFSG.Quasithin.HSType.prime_dvd_card_of_free hSfin.toFinset σ Nat.prime_three
      (fun a _ => hσ3 a)
      (fun a ha => hSfin.mem_toFinset.mpr (hmap a (hSfin.mem_toFinset.mp ha)))
      (fun a ha => hno a (hSfin.mem_toFinset.mp ha))
  rw [← Nat.card_coe_set_eq, hS8] at h3dvd
  omega

private theorem conj_eq_self_of_commutator_mem_centralizer {Q : Subgroup G} {x q : G}
    (hQ : IsPGroup 2 Q) (hxN : x ∈ Subgroup.normalizer (Q : Set G)) (hx3 : x ^ 3 = 1)
    (hq : q ∈ Q) (hc : x * q * x⁻¹ * q⁻¹ ∈ Subgroup.centralizer ({x} : Set G)) :
    x * q * x⁻¹ = q := by
  have hxa : Commute x ⁅x, q⁆ := by
    rw [commutatorElement_def]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
  have hQmem : ⁅x, q⁆ ∈ Q := by
    have h1 : x * q * x⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hxN q).mp hq
    have h2 : (x * q * x⁻¹) * q⁻¹ ∈ Q := Q.mul_mem h1 (Q.inv_mem hq)
    rwa [commutatorElement_def]
  obtain ⟨k, hk⟩ := hQ ⟨⁅x, q⁆, hQmem⟩
  have h2 : orderOf ⁅x, q⁆ ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have hcop : (orderOf x).Coprime (orderOf ⁅x, q⁆) :=
    Nat.Coprime.of_dvd h3 h2 (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2))
  have hcomm := CFSG.GroupTheory.commute_of_commute_commutatorElement hxa hcop
  calc x * q * x⁻¹ = (q * x) * x⁻¹ := by rw [hcomm.eq]
    _ = q := by group

namespace Setup

private theorem s_eq_five (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hr : Y.IsMaxRegLen 4) :
    s = 5 := by
  obtain ⟨r', hle, -, hr'⟩ := exists_isMaxRegLen Y H
  have h4 := hr.unique hr'
  have h5 := H.five_le
  omega

private theorem card_S_eq_sixtyfour (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    Nat.card Y.S = 2 ^ 6 := by
  obtain ⟨hn0, -, -, -⟩ := caseA_n Y H hZ h3 h4 hb he
  subst hn0
  have hs : s = 5 := s_eq_five Y H hr
  have h := card_S_of_isMaxRegLen_four Y H hr hs
  rw [h]
  norm_num

private theorem card_Q_zero_of_card_S (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hS : Nat.card Y.S = 2 ^ 6) (hn0 : n₀ = 2) : Nat.card (Y.Q 0) = 2 ^ 4 := by
  subst hn0
  have h := Y.card_S_eq_two_pow_mul_card_Q_zero H
  rw [hS] at h
  omega

private theorem card_Q_one_of_card_S (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hS : Nat.card Y.S = 2 ^ 6) : Nat.card (Y.Q 1) = 2 ^ 5 := by
  have h := Y.card_S_eq_two_mul_card_Q_one H
  rw [hS] at h
  omega

private theorem card_edgeSylow_one_of_card_S (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hS : Nat.card Y.S = 2 ^ 6) : Nat.card (Y.edgeSylow 1) = 2 ^ 6 := by
  rw [Y.card_edgeSylow_eq 1, Y.edgeSylow_zero, hS]

private theorem card_Q_two_of_card_S (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hS : Nat.card Y.S = 2 ^ 6) (hn0 : n₀ = 2) : Nat.card (Y.Q 2) = 2 ^ 4 := by
  subst hn0
  haveI : Finite ↥(Y.Gi 2) := Y.hyp.finite_stab (Y.vert 2)
  haveI := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 2)
  haveI := finite_of_le_stabilizer Y.hyp ((Y.isSylowTwoOf_edgeSylow 1).1.trans inf_le_left)
  have hS1 := card_edgeSylow_one_of_card_S Y H hS
  have hle : Y.Q 2 ≤ Y.edgeSylow 1 := by
    simpa [Setup.edgeSylow] using Y.Q_le_edgeSylow_right 2
  have h := Subgroup.relIndex_mul_card (H := Y.Q 2) (K := Y.edgeSylow 1)
  have hrel := Y.relIndex_Q_succ_edgeSylow (1:ℤ)
  norm_num at hrel
  rw [inf_of_le_left hle, hrel, Y.n_two, H.n_zero, hS1] at h
  norm_num at h ⊢
  omega

private theorem card_Z_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) : Nat.card (Y.Z 2) = 2 ^ 4 := by
  have hc := (caseA_card_Z Y H hZ h3 h4 hb he).2
  have hn0 := (caseA_n Y H hZ h3 h4 hb he).1
  subst hn0
  have hm : Y.Z (0 + 2 * (1 : ℤ)) = (Y.Z 0).map (MulAut.conj (Y.τ ^ (1 : ℤ))).toMonoidHom :=
    Y.Z_add 1 0
  rw [show (0 : ℤ) + 2 * 1 = 2 by norm_num] at hm
  rw [hm, Subgroup.card_map_of_injective (MulEquiv.injective _)]
  simpa using hc

private theorem Q_zero_eq_Z (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    Y.Q 0 = Y.Z 0 := by
  have hS := card_S_eq_sixtyfour Y H hZ h3 h4 hb he hr
  have hn0 := (caseA_n Y H hZ h3 h4 hb he).1
  have hQ := card_Q_zero_of_card_S Y H hS hn0
  have hZ0 : Nat.card (Y.Z 0) = 16 := by
    simpa [hn0] using (caseA_card_Z Y H hZ h3 h4 hb he).2
  haveI := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 0)
  refine (Subgroup.eq_of_le_of_card_ge (Y.Z_le_Q 0) ?_).symm
  rw [hQ, hZ0]
  norm_num

private theorem Q_two_eq_Z (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    Y.Q 2 = Y.Z 2 := by
  have hS := card_S_eq_sixtyfour Y H hZ h3 h4 hb he hr
  have hn0 := (caseA_n Y H hZ h3 h4 hb he).1
  have hQ := card_Q_two_of_card_S Y H hS hn0
  have hZ2 := card_Z_two Y H hZ h3 h4 hb he
  haveI := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 2)
  refine (Subgroup.eq_of_le_of_card_ge (Y.Z_le_Q 2) ?_).symm
  rw [hQ, hZ2]

private theorem Q_zero_inf_Q_two_eq_Z_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    Y.Q 0 ⊓ Y.Q 2 = Y.Z 1 := by
  rw [Q_zero_eq_Z Y H hZ h3 h4 hb he hr, Q_two_eq_Z Y H hZ h3 h4 hb he hr]
  exact Z_inf_Z_eq Y H h4 hb

private theorem card_Z_one_eq_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) :
    Nat.card (Y.Z 1) = 2 := (s52_step4 Y H hZ h3).2

private theorem card_Q_zero_inf_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    Nat.card ↥(Y.Q 0 ⊓ Y.Q 1) = 8 := by
  have hS := card_S_eq_sixtyfour Y H hZ h3 h4 hb he hr
  have hn0 := (caseA_n Y H hZ h3 h4 hb he).1
  have hQ0 := card_Q_zero_of_card_S Y H hS hn0
  have hQ1 := card_Q_one_of_card_S Y H hS
  have hsup : Y.Q 0 ⊔ Y.Q 1 = Y.S := Y.Q_zero_sup_Q_one_eq_S H
  have hZ0leG1 : Y.Z 0 ≤ Y.Gi 1 := by simpa using hb.1 1 (by norm_num)
  have hQ0leG1 : Y.Q 0 ≤ Y.Gi 1 := by
    rwa [Q_zero_eq_Z Y H hZ h3 h4 hb he hr]
  have hnorm : Y.Q 0 ≤ Subgroup.normalizer (Y.Q 1 : Set G) :=
    hQ0leG1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1))
  have hcard := CFSG.LocalAnalysis.EvenBN.Common.card_sup_mul_card_inf_eq
    (A := Y.Q 1) (B := Y.Q 0) hnorm
  rw [sup_comm, inf_comm, hsup, hS, hQ0, hQ1] at hcard
  norm_num at hcard ⊢
  omega

private theorem centralizer_K_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    Y.Q 1 ⊓ Subgroup.centralizer (Y.K : Set G) = Y.Z 1 := by
  have hQ01 := Q_zero_inf_Q_two_eq_Z_one Y H hZ h3 h4 hb he hr
  have hQ1pg : IsPGroup 2 ↥(Y.Q 1) := pCoreOf_isPGroup' (Y.Gi 1)
  have hKbot : ⁅Y.Z 1, Y.K⁆ = ⊥ := by
    change Y.Zt 1 = ⊥ at h3
    exact h3
  have hZ1cent : Y.Z 1 ≤ Subgroup.centralizer (Y.K : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKbot
  refine le_antisymm ?_ ?_
  · intro c hc
    obtain ⟨hcQ1, hcC⟩ := Subgroup.mem_inf.mp hc
    have hcC' : c ∈ Subgroup.centralizer (Y.K : Set G) := hcC
    have hcG0 : c ∈ Y.Gi 0 :=
      MulAction.mem_stabilizer_iff.mpr
        (Y.Q_fixes_neighbors_vert 1 (Y.vert 0) (by simpa using (Y.adj 0).symm) c hcQ1)
    have hcG2 : c ∈ Y.Gi 2 :=
      MulAction.mem_stabilizer_iff.mpr
        (Y.Q_fixes_neighbors_vert 1 (Y.vert 2) (Y.adj 1) c hcQ1)
    have hU0 : Subgroup.zpowers c ≤ Y.Gi 0 := Subgroup.zpowers_le.mpr hcG0
    have hU2 : Subgroup.zpowers c ≤ Y.Gi 2 := Subgroup.zpowers_le.mpr hcG2
    have hpU : IsPGroup 2 ↥(Subgroup.zpowers c) :=
      hQ1pg.to_le (Subgroup.zpowers_le.mpr hcQ1)
    have hcommU : ⁅Subgroup.zpowers c, Y.K⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.zpowers_le.mpr hcC')
    have hcQ2 : c ∈ Y.Q 2 :=
      le_Q_of_comm_K_eq_bot Y H (j := 2) (by norm_num) hU2 hpU hcommU
        (Subgroup.mem_zpowers c)
    have hcQ0 : c ∈ Y.Q 0 :=
      le_Q_of_comm_K_eq_bot Y H (j := 0) (by norm_num) hU0 hpU hcommU
        (Subgroup.mem_zpowers c)
    have : c ∈ Y.Q 0 ⊓ Y.Q 2 := Subgroup.mem_inf.mpr ⟨hcQ0, hcQ2⟩
    rwa [hQ01] at this
  · intro z hz
    exact Subgroup.mem_inf.mpr ⟨Y.Z_le_Q 1 hz, hZ1cent hz⟩

private theorem not_isMulCommutative_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    ¬ IsMulCommutative ↥(Y.Q 1) := by
  intro hcomm
  have hW := card_Q_zero_inf_Q_one Y H hZ h3 h4 hb he hr
  have hZcard := card_Z_one_eq_two Y H hZ h3
  have hWle : Y.Q 0 ⊓ Y.Q 1 ≤ Y.Z 1 := by
    intro x hx
    have hQ0 := Q_zero_eq_Z Y H hZ h3 h4 hb he hr
    have hxQ0 : x ∈ Y.Q 0 := hx.1
    have hxQ1 : x ∈ Y.Q 1 := hx.2
    have hxS : x ∈ Y.S := by
      have hsup : Y.Q 0 ⊔ Y.Q 1 = Y.S := Y.Q_zero_sup_Q_one_eq_S H
      rw [← hsup]
      exact Subgroup.mem_sup_left hxQ0
    have hxcent : x ∈ Subgroup.centralizer (Y.S : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hsup : Y.Q 0 ⊔ Y.Q 1 = Y.S := Y.Q_zero_sup_Q_one_eq_S H
      have hQ0leG1 : Y.Q 0 ≤ Y.Gi 1 := by
        have hZ0le : Y.Z 0 ≤ Y.Gi 1 := by simpa using hb.1 1 (by norm_num)
        exact hQ0 ▸ hZ0le
      have hnorm : Y.Q 0 ≤ Subgroup.normalizer (Y.Q 1 : Set G) :=
        hQ0leG1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1))
      have hmul : y ∈ ((Y.Q 0 : Set G) * (Y.Q 1 : Set G)) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm, hsup]
        exact hy
      obtain ⟨a, ha, b, hb', hab⟩ := hmul
      rw [← hab]
      have hxZ0 : x ∈ Y.Z 0 := hQ0 ▸ hxQ0
      have haZ0 : a ∈ Y.Z 0 := hQ0 ▸ ha
      have hxa : a * x = x * a := Y.Z_commute 0 a haZ0 x hxZ0
      have hxb : b * x = x * b :=
        congrArg (fun z : ↥(Y.Q 1) => (z : G)) (hcomm.is_comm.comm ⟨b, hb'⟩ ⟨x, hxQ1⟩)
      calc (a * b) * x = a * (b * x) := by group
        _ = a * (x * b) := by rw [hxb]
        _ = (a * x) * b := by group
        _ = (x * a) * b := by rw [hxa]
        _ = x * (a * b) := by group
    have hxcenter : x ∈ centerOf Y.S := by
      rw [centerOf]
      exact Subgroup.mem_inf.mpr ⟨hxS, hxcent⟩
    exact (center_S_le_Z Y H 1 (Or.inr rfl)).1 hxcenter
  haveI := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 1)
  haveI : Finite ↥(Y.Z 1) :=
    finite_of_le_stabilizer Y.hyp ((Y.Z_le_Q 1).trans (Y.Q_le_Gi 1))
  have hle := Subgroup.card_le_of_le hWle
  rw [hW, hZcard] at hle
  omega

private theorem inf_Q_one_le_normalizer (Y : Setup Γ G) :
    (Y.Q 0 ⊓ Y.Q 1 ≤ Subgroup.normalizer ((Y.Q 2 ⊓ Y.Q 1 : Subgroup G) : Set G)) ∧
      (Y.Q 2 ⊓ Y.Q 1 ≤ Subgroup.normalizer ((Y.Q 0 ⊓ Y.Q 1 : Subgroup G) : Set G)) := by
  have hQ1leG0 : Y.Q 1 ≤ Y.Gi 0 := by simpa using (Y.Q_le_Gi_adj 1).trans inf_le_left
  have hQ1leG2 : Y.Q 1 ≤ Y.Gi 2 := by simpa using (Y.Q_le_Gi_adj 1).trans inf_le_right
  have hW0G2 : Y.Q 0 ⊓ Y.Q 1 ≤ Y.Gi 2 :=
    (inf_le_right : Y.Q 0 ⊓ Y.Q 1 ≤ Y.Q 1).trans hQ1leG2
  have hW2G0 : Y.Q 2 ⊓ Y.Q 1 ≤ Y.Gi 0 :=
    (inf_le_right : Y.Q 2 ⊓ Y.Q 1 ≤ Y.Q 1).trans hQ1leG0
  have hW0NQ2 : Y.Q 0 ⊓ Y.Q 1 ≤ Subgroup.normalizer (Y.Q 2 : Set G) :=
    hW0G2.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 2))
  have hW2NQ0 : Y.Q 2 ⊓ Y.Q 1 ≤ Subgroup.normalizer (Y.Q 0 : Set G) :=
    hW2G0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0))
  refine ⟨F7.le_normalizer_inf hW0NQ2
      ((inf_le_right : Y.Q 0 ⊓ Y.Q 1 ≤ Y.Q 1).trans Subgroup.le_normalizer),
    F7.le_normalizer_inf hW2NQ0
      ((inf_le_right : Y.Q 2 ⊓ Y.Q 1 ≤ Y.Q 1).trans Subgroup.le_normalizer)⟩

private theorem commutator_Q_one_le_Z_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    ⁅Y.Q 1, Y.Q 1⁆ ≤ Y.Z 1 := by
  obtain ⟨hW0norm, hW2norm⟩ := inf_Q_one_le_normalizer Y
  have hWinf : Y.Q 0 ⊓ Y.Q 1 ⊓ (Y.Q 2 ⊓ Y.Q 1) = Y.Z 1 := by
    have h1 : Y.Q 0 ⊓ Y.Q 1 ⊓ (Y.Q 2 ⊓ Y.Q 1) = (Y.Q 0 ⊓ Y.Q 2) ⊓ Y.Q 1 := by
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    rw [h1, Q_zero_inf_Q_two_eq_Z_one Y H hZ h3 h4 hb he hr,
      inf_eq_left.mpr (Y.Z_le_Q 1)]
  have hcommW : ⁅Y.Q 0 ⊓ Y.Q 1, Y.Q 2 ⊓ Y.Q 1⁆ ≤ Y.Z 1 := by
    have h := F7.commutator_le_inf_of_normalizes hW0norm hW2norm
    rwa [hWinf] at h
  have hsup : Y.Q 1 = (Y.Q 0 ⊓ Y.Q 1) ⊔ (Y.Q 2 ⊓ Y.Q 1) := by simpa using Q_eq_sup_inf Y H 1
  have hZcent : Y.Z 1 ≤ centerOf (Y.Q 1) :=
    Y.Z_le_center 1
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hxmul : x ∈ ((Y.Q 0 ⊓ Y.Q 1 : Subgroup G) : Set G) *
      ((Y.Q 2 ⊓ Y.Q 1 : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hW0norm, ← hsup]
    exact hx
  have hymul : y ∈ ((Y.Q 0 ⊓ Y.Q 1 : Subgroup G) : Set G) *
      ((Y.Q 2 ⊓ Y.Q 1 : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hW0norm, ← hsup]
    exact hy
  obtain ⟨a, ha, b, hb', rfl⟩ := hxmul
  obtain ⟨c, hc, d, hd', rfl⟩ := hymul
  have hQ0eq := Q_zero_eq_Z Y H hZ h3 h4 hb he hr
  have hQ2eq := Q_two_eq_Z Y H hZ h3 h4 hb he hr
  have hab : a * c = c * a := by
    have hcomm : ∀ p ∈ Y.Q 0 ⊓ Y.Q 1, ∀ q ∈ Y.Q 0 ⊓ Y.Q 1, p * q = q * p := by
      intro p hp q hq
      exact Y.Z_commute 0 p (hQ0eq ▸ hp.1) q (hQ0eq ▸ hq.1)
    exact hcomm a ha c hc
  have hbd : b * d = d * b := by
    have hcomm : ∀ p ∈ Y.Q 2 ⊓ Y.Q 1, ∀ q ∈ Y.Q 2 ⊓ Y.Q 1, p * q = q * p := by
      intro p hp q hq
      exact Y.Z_commute 2 p (hQ2eq ▸ hp.1) q (hQ2eq ▸ hq.1)
    exact hcomm b hb' d hd'
  have hcommW' : ⁅Y.Q 2 ⊓ Y.Q 1, Y.Q 0 ⊓ Y.Q 1⁆ ≤ Y.Z 1 := by
    rwa [Subgroup.commutator_comm] at hcommW
  have hbc : ⁅b, c⁆ ∈ Y.Z 1 := hcommW' (Subgroup.commutator_mem_commutator hb' hc)
  have had : ⁅a, d⁆ ∈ Y.Z 1 := hcommW (Subgroup.commutator_mem_commutator ha hd')
  have hcent : ∀ z ∈ Y.Z 1, ∀ q ∈ Y.Q 1, z * q = q * z := by
    intro z hz q hq
    exact ((Subgroup.mem_inf.mp (hZcent hz)).2 q hq).symm
  have hconjbc : a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ := by
    have h := hcent _ hbc a ha.2
    calc a * ⁅b, c⁆ * a⁻¹ = (⁅b, c⁆ * a) * a⁻¹ := by rw [h]
      _ = ⁅b, c⁆ := by group
  have hconjad : c * ⁅a, d⁆ * c⁻¹ = ⁅a, d⁆ := by
    have h := hcent _ had c hc.2
    calc c * ⁅a, d⁆ * c⁻¹ = (⁅a, d⁆ * c) * c⁻¹ := by rw [h]
      _ = ⁅a, d⁆ := by group
  have hform : ⁅a * b, c * d⁆ = a * ⁅b, c * d⁆ * a⁻¹ * ⁅a, c * d⁆ :=
    commutatorElement_mul_left_eq_conj_mul a b (c * d)
  have hbcd : ⁅b, c * d⁆ = ⁅b, c⁆ * c * ⁅b, d⁆ * c⁻¹ :=
    commutatorElement_mul_right_eq_mul_conj b c d
  have hbd1 : ⁅b, d⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hbd
  have hacd : ⁅a, c * d⁆ = ⁅a, c⁆ * c * ⁅a, d⁆ * c⁻¹ :=
    commutatorElement_mul_right_eq_mul_conj a c d
  have hac1 : ⁅a, c⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hab
  rw [hform, hbcd, hbd1, mul_one, hacd, hac1, one_mul]
  have hmid : a * (⁅b, c⁆ * c * c⁻¹) * a⁻¹ = a * ⁅b, c⁆ * a⁻¹ := by group
  rw [hmid, hconjbc, hconjad]
  exact (Y.Z 1).mul_mem hbc had

private theorem commutator_Q_one_eq_Z_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    ⁅Y.Q 1, Y.Q 1⁆ = Y.Z 1 := by
  have hle := commutator_Q_one_le_Z_one Y H hZ h3 h4 hb he hr
  have hne : ⁅Y.Q 1, Y.Q 1⁆ ≠ ⊥ := by
    intro hbot
    exact not_isMulCommutative_Q_one Y H hZ h3 h4 hb he hr
      (Subgroup.commutator_self_eq_bot_iff.mp hbot)
  haveI := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 1)
  haveI : Finite ↥(⁅Y.Q 1, Y.Q 1⁆) :=
    finite_of_le_stabilizer Y.hyp
      (((Subgroup.commutator_le_sup (Y.Q 1) (Y.Q 1)).trans
        (le_of_eq (sup_idem (Y.Q 1)))).trans (Y.Q_le_Gi 1))
  haveI : Finite ↥(Y.Z 1) :=
    finite_of_le_stabilizer Y.hyp ((Y.Z_le_Q 1).trans (Y.Q_le_Gi 1))
  have hcardle : Nat.card ↥(⁅Y.Q 1, Y.Q 1⁆) ≤ 2 := by
    have h := Subgroup.card_le_of_le hle
    rwa [card_Z_one_eq_two Y H hZ h3] at h
  have hcardne : Nat.card ↥(⁅Y.Q 1, Y.Q 1⁆) ≠ 1 := by
    intro h1
    exact hne (Subgroup.card_eq_one.mp h1)
  have hcardpos : 0 < Nat.card ↥(⁅Y.Q 1, Y.Q 1⁆) := Nat.card_pos
  have hcard : Nat.card ↥(⁅Y.Q 1, Y.Q 1⁆) = 2 := by omega
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_Z_one_eq_two Y H hZ h3, hcard]

private theorem not_natSec_vertex_zero_subgroup (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) :
    ¬ NatSec ((Y.L 0).subgroupOf (Y.Gi 0)) ⊥ ((Y.Z 0).subgroupOf (Y.Gi 0)) := by
  let H0 := Y.Gi 0
  let L0 := Y.L 0
  let E := (Y.Z 0).subgroupOf H0
  have hAn := caseA_n Y H hZ h3 h4 hb he
  have hnot : ¬ NatSec L0 ⊥ (Y.Z 0) := hAn.2.2.2
  intro hsec
  unfold NatSec FixFree at hnot
  push Not at hnot
  obtain ⟨x, hxL, hx3, e, heZ, hec, hene⟩ := hnot
  have hxH : x ∈ H0 := Y.L_le_Gi 0 hxL
  have heH : e ∈ H0 := Y.Z_le_Gi 0 heZ
  let x' : ↥(L0.subgroupOf H0) := ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hxL⟩
  let e' : ↥E := ⟨⟨e, heH⟩, Subgroup.mem_subgroupOf.mpr heZ⟩
  have hx3' : orderOf (x' : ↥H0) = 3 := by
    simpa [x'] using hx3
  have hc' : ⁅(e' : ↥H0), (x' : ↥H0)⁆ ∈ (⊥ : Subgroup ↥H0) := by
    rw [Subgroup.mem_bot]
    have h1 : ((⁅(e' : ↥H0), (x' : ↥H0)⁆ : ↥H0) : G) = ⁅e, x⁆ := by
      change ⁅((e' : ↥H0) : G), ((x' : ↥H0) : G)⁆ = ⁅e, x⁆
      rfl
    apply Subtype.ext
    rw [h1]
    simpa using Subgroup.mem_bot.mp hec
  have hbot := hsec (x' : ↥H0) x'.2 hx3' (e' : ↥H0) e'.2 hc'
  exact hene (Subgroup.mem_bot.mpr (by
    simpa [e'] using congrArg (fun z : ↥H0 => (z : G)) (Subgroup.mem_bot.mp hbot)))

private theorem a5Pre_vertex_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    A5Pre (⊤ : Subgroup ↥(Y.Gi 0)) ((Y.L 0).subgroupOf (Y.Gi 0))
      ((Y.Z 0).subgroupOf (Y.Gi 0)) ⊥ := by
  let H0 := Y.Gi 0
  let L0 := Y.L 0
  haveI : Finite ↥H0 := Y.hyp.finite_stab (Y.vert 0)
  have hAn := caseA_n Y H hZ h3 h4 hb he
  have hQ0 := Q_zero_eq_Z Y H hZ h3 h4 hb he hr
  have hLleH : L0 ≤ H0 := Y.L_le_Gi 0
  have hLnorm : (L0.subgroupOf H0).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLleH]
    simpa [Setup.L] using CFSG.Quasithin.le_normalizer_oTwoPrime H0
  have hchar : CharTwo (⊤ : Subgroup ↥H0) := by
    have h := (CFSG.Quasithin.F6.GoldPair.charTwo_subgroupOf_iff
      (I := H0) (K := H0) le_rfl).mpr (H.char (Y.vert 0))
    simpa [Subgroup.subgroupOf_self] using h
  have hN : IsLocL2 Γ G (Y.vert 0) 2 L0 := by
    simpa [Setup.n, H.n_zero, hAn.1] using Y.hyp.isLocL2_oTwoPrime (Y.vert 0)
  obtain ⟨e0⟩ := hN.quot
  let eL := Subgroup.subgroupOfEquivOfLe hLleH
  let equot : oTwoQuot ↥(L0.subgroupOf H0) ≃* oTwoQuot ↥L0 :=
    QuotientGroup.congr (pCore 2 ↥(L0.subgroupOf H0)) (pCore 2 ↥L0) eL
      (CFSG.pCore_map_iso 2 eL)
  have hquot : IsL2Quot 2 (oTwoQuot ↥(L0.subgroupOf H0)) := ⟨equot.trans e0⟩
  have hpc : pCoreOf 2 (⊤ : Subgroup ↥H0) = (Y.Z 0).subgroupOf H0 := by
    rw [F6.GoldPair.pCoreOf_top_eq, ← CFSG.openPCoreOf_subgroupOf 2 H0,
      show pCoreOf 2 H0 = Y.Q 0 from rfl, hQ0]
  have hcard : Nat.card (pCoreOf 2 (⊤ : Subgroup ↥H0)) = 16 := by
    rw [hpc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Y.Z_le_Gi 0)).toEquiv, hAn.2.2.1]
    norm_num
  have hPL : (⊤ : Subgroup ↥H0) ≤
      Subgroup.normalizer ((L0.subgroupOf H0) : Set ↥H0) :=
    le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hLnorm).symm
  have hpre := a5Pre_pCoreOf (P := (⊤ : Subgroup ↥H0)) (L := L0.subgroupOf H0)
    le_top hPL hchar hquot hcard
  simpa [hpc] using hpre

private theorem card_Z_zero_inf_centralizer_S (Y : Setup Γ G)
    (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    Nat.card ↥(Y.Z 0 ⊓ Subgroup.centralizer (Y.S : Set G)) = 2 := by
  let H0 := Y.Gi 0
  haveI : Finite ↥H0 := Y.hyp.finite_stab (Y.vert 0)
  let L := (Y.L 0).subgroupOf H0
  let E := (Y.Z 0).subgroupOf H0
  let T := (Y.S).subgroupOf H0
  have hpre : A5Pre (⊤ : Subgroup ↥H0) L E ⊥ := by
    simpa [L, E, H0] using a5Pre_vertex_zero Y H hZ h3 h4 hb he hr
  have hT : IsSylowTwoOf T L := by
    simpa [T, L, H0, Y.edgeSylow_zero] using F6.GoldPair.isSylowTwoOf_subgroupOf (Y.L_le_Gi 0)
      (Y.isSylowTwoOf_edgeSylow_L 0)
  have hnot : ¬ NatSec L ⊥ E := by
    simpa [L, E, H0] using not_natSec_vertex_zero_subgroup Y H hZ h3 h4 hb he
  have h2 := (natSec_iff_card_centralizer hpre hT).2.mp hnot
  have hcent : Subgroup.centralizer (T : Set ↥H0) =
      (Subgroup.centralizer (Y.S : Set G)).subgroupOf H0 :=
    (CFSG.Sporadic.Schreier.Tits.centralizer_subgroupOf_eq (X := Y.S) (D := H0)
      ((Y.edgeSylow_le_L 0).trans (Y.L_le_Gi 0))).symm
  have hcardEq : Nat.card ↥(E ⊓ Subgroup.centralizer (T : Set ↥H0)) =
      Nat.card ↥(Y.Z 0 ⊓ Subgroup.centralizer (Y.S : Set G)) := by
    rw [hcent]
    exact F6.GoldPair.card_inf_subgroupOf (Y.Z_le_Gi 0)
  rw [hcardEq] at h2
  exact h2

private theorem card_K (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) : Nat.card ↥(Y.K) = 3 := by
  simp [Y.card_K_eq H, (caseA_n Y H hZ h3 h4 hb he).1]

private theorem card_center_modEq_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    Nat.card ↥(centerOf (Y.Q 1)) ≡ 2 [MOD 3] := by
  let C := centerOf (Y.Q 1)
  haveI := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 1)
  haveI : Finite ↥C :=
    finite_of_le_stabilizer Y.hyp ((inf_le_left : C ≤ Y.Q 1).trans (Y.Q_le_Gi 1))
  haveI : Finite ↥(Y.K) := finite_of_le_stabilizer Y.hyp (Y.K_le_Gi 0)
  have hKC : Y.K ≤ Subgroup.normalizer (centerOf (Y.Q 1) : Set G) :=
    ((Y.K_le_Gi 1).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1))).trans
      (CFSG.Quasithin.normalizer_le_normalizer_centerOf (Y.Q 1))
  letI : MulDistribMulAction ↥(Y.K) ↥C :=
    MulDistribMulAction.compHom C (C.normalizerMonoidHom.comp (Subgroup.inclusion hKC))
  have hsmul : ∀ (k : ↥(Y.K)) (c : ↥C),
      ((k • c : ↥C) : G) = (k : G) * (c : G) * (k : G)⁻¹ := by
    intro k c
    rfl
  have hfixset : MulAction.fixedPoints ↥(Y.K) ↥C = ((Y.Z 1).subgroupOf C : Set ↥C) := by
    ext c
    change (∀ k : ↥(Y.K), k • c = c) ↔ (c : ↥C) ∈ (Y.Z 1).subgroupOf C
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro hfix
      have hcK : (c : G) ∈ Subgroup.centralizer (Y.K : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have h : (k : G) * (c : G) * (k : G)⁻¹ = (c : G) := by
          simpa [hsmul] using congrArg (fun z : ↥C => (z : G)) (hfix ⟨k, hk⟩)
        calc k * (c : G) = (k * (c : G) * k⁻¹) * k := by group
          _ = (c : G) * k := by rw [h]
      have hcQ : (c : G) ∈ Y.Q 1 := (inf_le_left : C ≤ Y.Q 1) c.2
      have hcInf : (c : G) ∈ Y.Q 1 ⊓ Subgroup.centralizer (Y.K : Set G) :=
        Subgroup.mem_inf.mpr ⟨hcQ, hcK⟩
      have hEq := centralizer_K_Q_one Y H hZ h3 h4 hb he hr
      rw [hEq] at hcInf
      simpa using hcInf
    · intro hcZ
      have hzcent : (c : G) ∈ Subgroup.centralizer (Y.K : Set G) :=
        (Subgroup.mem_inf.mp (Z_one_le Y H hZ h3 hcZ)).2
      intro k
      apply Subtype.ext
      rw [hsmul]
      have h := Subgroup.mem_centralizer_iff.mp hzcent (k : G) k.2
      calc (k : G) * (c : G) * (k : G)⁻¹ = (c : G) * (k : G) * (k : G)⁻¹ := by rw [h]
        _ = (c : G) := by group
  have hK3 : IsPGroup 3 ↥(Y.K) := IsPGroup.of_card (n := 1) (by
    rw [card_K Y H hZ h3 h4 hb he]
    norm_num)
  have hmod := hK3.card_modEq_card_fixedPoints (α := ↥C)
  rw [hfixset] at hmod
  have hZ1leC : Y.Z 1 ≤ C := Y.Z_le_center 1
  have hcardfix : Nat.card ↥((Y.Z 1).subgroupOf C) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ1leC).toEquiv]
    exact card_Z_one_eq_two Y H hZ h3
  simpa [hcardfix] using hmod

private theorem isMulCommutative_centerOf_sup_Q_zero_inf_Q_one (Y : Setup Γ G)
    (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    IsMulCommutative ↥(centerOf (Y.Q 1) ⊔ (Y.Q 0 ⊓ Y.Q 1)) := by
  let C := centerOf (Y.Q 1)
  let W0 := Y.Q 0 ⊓ Y.Q 1
  have hCleQ : C ≤ Y.Q 1 := inf_le_left
  have hW0leQ : W0 ≤ Y.Q 1 := inf_le_right
  have hQ0eq := Q_zero_eq_Z Y H hZ h3 h4 hb he hr
  have hpair : ((C : Set G) ∪ (W0 : Set G)).Pairwise Commute := by
    intro a ha b hb' _
    rcases ha with ha | ha
    · have hacent : a ∈ Subgroup.centralizer (Y.Q 1 : Set G) := (Subgroup.mem_inf.mp ha).2
      rcases hb' with hb' | hb'
      · exact (Subgroup.mem_centralizer_iff.mp hacent b (hCleQ hb')).symm
      · exact (Subgroup.mem_centralizer_iff.mp hacent b (hW0leQ hb')).symm
    · rcases hb' with hb' | hb'
      · have hbcent : b ∈ Subgroup.centralizer (Y.Q 1 : Set G) := (Subgroup.mem_inf.mp hb').2
        exact Subgroup.mem_centralizer_iff.mp hbcent a (hW0leQ ha)
      · have haZ : a ∈ Y.Z 0 := by
          have : a ∈ Y.Q 0 := (Subgroup.mem_inf.mp ha).1
          rwa [hQ0eq] at this
        have hbZ : b ∈ Y.Z 0 := by
          have : b ∈ Y.Q 0 := (Subgroup.mem_inf.mp hb').1
          rwa [hQ0eq] at this
        exact Y.Z_commute 0 a haZ b hbZ
  rw [Subgroup.sup_eq_closure]
  exact Subgroup.isMulCommutative_closure hpair

private theorem center_inf_Q_zero_le_centralizer_S (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    centerOf (Y.Q 1) ⊓ Y.Q 0 ≤ Subgroup.centralizer (Y.S : Set G) := by
  intro z hz
  rw [Subgroup.mem_inf] at hz
  have hQ0eq := Q_zero_eq_Z Y H hZ h3 h4 hb he hr
  have hQ0G1 : Y.Q 0 ≤ Y.Gi 1 := by
    have hZ0le : Y.Z 0 ≤ Y.Gi 1 := by simpa using hb.1 1 (by norm_num)
    exact hQ0eq ▸ hZ0le
  have hQ0norm : Y.Q 0 ≤ Subgroup.normalizer (Y.Q 1 : Set G) :=
    hQ0G1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1))
  have hS : Y.Q 0 ⊔ Y.Q 1 = Y.S := Y.Q_zero_sup_Q_one_eq_S H
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hsmul : s ∈ ((Y.Q 0 : Set G) * (Y.Q 1 : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hQ0norm, hS]
    exact hs
  obtain ⟨a, ha, b, hb', hsab⟩ := Set.mem_mul.mp hsmul
  have hzZ0 : z ∈ Y.Z 0 := hQ0eq ▸ hz.2
  have haZ0 : a ∈ Y.Z 0 := hQ0eq ▸ ha
  have hza : z * a = a * z := Y.Z_commute 0 z hzZ0 a haZ0
  have hzb : z * b = b * z := by
    have hcent : z ∈ Subgroup.centralizer (Y.Q 1 : Set G) := (Subgroup.mem_inf.mp hz.1).2
    exact (Subgroup.mem_centralizer_iff.mp hcent b hb').symm
  calc s * z = (a * b) * z := by rw [hsab]
    _ = a * (b * z) := by group
    _ = a * (z * b) := by rw [hzb]
    _ = (a * z) * b := by group
    _ = (z * a) * b := by rw [hza]
    _ = z * (a * b) := by group
    _ = z * s := by rw [hsab]

private theorem center_Q_one_inf_Q_zero_eq_Z_one (Y : Setup Γ G)
    (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    centerOf (Y.Q 1) ⊓ Y.Q 0 = Y.Z 1 := by
  let C := centerOf (Y.Q 1)
  have hZ1le : Y.Z 1 ≤ C ⊓ Y.Q 0 := by
    intro z hz
    exact Subgroup.mem_inf.mpr ⟨Y.Z_le_center 1 hz, by
      exact (Q_zero_eq_Z Y H hZ h3 h4 hb he hr).symm ▸
        (Subgroup.mem_inf.mp (Z_one_le Y H hZ h3 hz)).1⟩
  have hle : C ⊓ Y.Q 0 ≤ Y.Z 0 ⊓ Subgroup.centralizer (Y.S : Set G) := by
    refine le_inf ?_ ?_
    · intro z hz
      exact (Q_zero_eq_Z Y H hZ h3 h4 hb he hr) ▸ (Subgroup.mem_inf.mp hz).2
    · exact center_inf_Q_zero_le_centralizer_S Y H hZ h3 h4 hb he hr
  haveI := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 1)
  haveI : Finite ↥(Y.Z 0) := finite_of_le_stabilizer Y.hyp (Y.Z_le_Gi 0)
  haveI : Finite ↥(C ⊓ Y.Q 0) :=
    finite_of_le_stabilizer Y.hyp
      (((inf_le_left : C ⊓ Y.Q 0 ≤ C).trans (inf_le_left : C ≤ Y.Q 1)).trans (Y.Q_le_Gi 1))
  haveI : Finite ↥(Y.Z 0 ⊓ Subgroup.centralizer (Y.S : Set G)) :=
    finite_of_le_stabilizer Y.hyp
      ((inf_le_left : Y.Z 0 ⊓ Subgroup.centralizer (Y.S : Set G) ≤ Y.Z 0).trans (Y.Z_le_Gi 0))
  haveI : Finite ↥(Y.Z 1) :=
    finite_of_le_stabilizer Y.hyp ((Y.Z_le_Q 1).trans (Y.Q_le_Gi 1))
  have hcardle : Nat.card ↥(C ⊓ Y.Q 0) ≤ 2 := by
    have h := Subgroup.card_le_of_le hle
    rwa [card_Z_zero_inf_centralizer_S Y H hZ h3 h4 hb he hr] at h
  have hZ1card := card_Z_one_eq_two Y H hZ h3
  have hEq := Subgroup.eq_of_le_of_card_ge hZ1le (by rw [hZ1card]; exact hcardle)
  exact hEq.symm

private theorem center_Q_one_eq_Z_one (Y : Setup Γ G)
    (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    centerOf (Y.Q 1) = Y.Z 1 := by
  let C := centerOf (Y.Q 1)
  let W0 := Y.Q 0 ⊓ Y.Q 1
  have hZ1le : Y.Z 1 ≤ C := Y.Z_le_center 1
  have hQ0eq := Q_zero_eq_Z Y H hZ h3 h4 hb he hr
  have hZ1Q0 : Y.Z 1 ≤ Y.Q 0 := by
    intro z hz
    exact hQ0eq ▸ (Subgroup.mem_inf.mp (Z_one_le Y H hZ h3 hz)).1
  have hZ1W0 : Y.Z 1 ≤ W0 := le_inf hZ1Q0 (Y.Z_le_Q 1)
  have hCinfQ0 : C ⊓ Y.Q 0 = Y.Z 1 := center_Q_one_inf_Q_zero_eq_Z_one Y H hZ h3 h4 hb he hr
  have hCinfW0 : C ⊓ W0 = Y.Z 1 := by
    refine le_antisymm ?_ ?_
    · intro x hx
      have hx' : x ∈ C ⊓ Y.Q 0 := Subgroup.mem_inf.mpr ⟨hx.1, hx.2.1⟩
      rwa [hCinfQ0] at hx'
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨hZ1le hx, hZ1W0 hx⟩
  by_contra hne
  have hCleQ : C ≤ Y.Q 1 := inf_le_left
  haveI := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 1)
  haveI : Finite ↥C := finite_of_le_stabilizer Y.hyp (hCleQ.trans (Y.Q_le_Gi 1))
  haveI : Finite ↥(Y.Z 1) :=
    finite_of_le_stabilizer Y.hyp ((Y.Z_le_Q 1).trans (Y.Q_le_Gi 1))
  have hS := card_S_eq_sixtyfour Y H hZ h3 h4 hb he hr
  have hQ1card : Nat.card ↥(Y.Q 1) = 32 := by
    simpa using card_Q_one_of_card_S Y H hS
  have hCdvd : Nat.card ↥C ∣ 32 := by
    rw [← hQ1card]
    exact Subgroup.card_dvd_of_le hCleQ
  have hZ1card := card_Z_one_eq_two Y H hZ h3
  have hmod := card_center_modEq_two Y H hZ h3 h4 hb he hr
  rcases (by decide : ∀ n ∈ Nat.divisors 32, n % 3 = 2 → n = 2 ∨ n = 8 ∨ n = 32)
    (Nat.card ↥C) (Nat.mem_divisors.2 ⟨hCdvd, by norm_num⟩)
    (by simpa [Nat.ModEq] using hmod) with h2 | h8 | h32
  · exfalso
    exact hne (Subgroup.eq_of_le_of_card_ge (H := Y.Z 1) (K := C) hZ1le
      (by rw [h2, hZ1card])).symm
  · exfalso
    have hW0card : Nat.card ↥W0 = 8 := card_Q_zero_inf_Q_one Y H hZ h3 h4 hb he hr
    have hQ1G0 : Y.Q 1 ≤ Y.Gi 0 := (Y.Q_le_Gi_adj 1).trans inf_le_left
    have hQ1NQ0 : Y.Q 1 ≤ Subgroup.normalizer (Y.Q 0 : Set G) :=
      hQ1G0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0))
    have hQ1NW0 : Y.Q 1 ≤ Subgroup.normalizer (W0 : Set G) :=
      F7.le_normalizer_inf hQ1NQ0 Subgroup.le_normalizer
    have hCnormW0 : C ≤ Subgroup.normalizer (W0 : Set G) := hCleQ.trans hQ1NW0
    have hprod := CFSG.LocalAnalysis.EvenBN.Common.card_sup_mul_card_inf_eq
      (A := W0) (B := C) hCnormW0
    rw [sup_comm, inf_comm, hCinfW0, hZ1card, h8, hW0card] at hprod
    have hsupcard : Nat.card ↥(C ⊔ W0) = 32 := by omega
    have hsup_le : C ⊔ W0 ≤ Y.Q 1 := sup_le hCleQ inf_le_right
    haveI : Finite ↥(C ⊔ W0) :=
      finite_of_le_stabilizer Y.hyp (hsup_le.trans (Y.Q_le_Gi 1))
    have hEq : C ⊔ W0 = Y.Q 1 :=
      Subgroup.eq_of_le_of_card_ge hsup_le (by rw [hQ1card, hsupcard])
    have habel := isMulCommutative_centerOf_sup_Q_zero_inf_Q_one Y H hZ h3 h4 hb he hr
    exact not_isMulCommutative_Q_one Y H hZ h3 h4 hb he hr (by
      rw [← hEq]
      exact habel)
  · exfalso
    have hCeq : C = Y.Q 1 := Subgroup.eq_of_le_of_card_ge hCleQ (by rw [h32, hQ1card])
    have hCabel : IsMulCommutative ↥C := by
      refine Subgroup.le_centralizer_iff_isMulCommutative.mp ?_
      intro c hc
      exact Subgroup.centralizer_le (fun x hx => hCleQ hx) (Subgroup.mem_inf.mp hc).2
    exact not_isMulCommutative_Q_one Y H hZ h3 h4 hb he hr (by
      rw [← hCeq]
      exact hCabel)

private theorem isElemAbelian_Z_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) : IsElemAbelian 2 (Y.Z 2) := by
  let e := MulAut.conj (Y.τ ^ (1 : ℤ))
  have hZ0elem : IsElemAbelian 2 (Y.Z 0) := (caseA_n Y H hZ h3 h4 hb he).2.1
  have hZ2eq : Y.Z 2 = (Y.Z 0).map e.toMonoidHom := by
    have h := Y.Z_add 1 0
    simpa [e, conjSub] using h
  rw [hZ2eq]
  exact hZ0elem.map e.toMonoidHom

private theorem sq_mem_Z_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4)
    {x : G} (hx : x ∈ Y.Q 1) : x ^ 2 ∈ Y.Z 1 := by
  let W0 := Y.Q 0 ⊓ Y.Q 1
  let W2 := Y.Q 2 ⊓ Y.Q 1
  obtain ⟨hW0norm, hW2norm⟩ := inf_Q_one_le_normalizer Y
  have hWinf : W0 ⊓ W2 = Y.Z 1 := by
    change (Y.Q 0 ⊓ Y.Q 1) ⊓ (Y.Q 2 ⊓ Y.Q 1) = Y.Z 1
    have h1 : (Y.Q 0 ⊓ Y.Q 1) ⊓ (Y.Q 2 ⊓ Y.Q 1) = (Y.Q 0 ⊓ Y.Q 2) ⊓ Y.Q 1 := by
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    rw [h1, Q_zero_inf_Q_two_eq_Z_one Y H hZ h3 h4 hb he hr,
      inf_eq_left.mpr (Y.Z_le_Q 1)]
  have hcommW : ⁅W0, W2⁆ ≤ Y.Z 1 := by
    have h := F7.commutator_le_inf_of_normalizes hW0norm hW2norm
    rwa [hWinf] at h
  have hsup : Y.Q 1 = W0 ⊔ W2 := by simpa using Q_eq_sup_inf Y H 1
  have hxmul : x ∈ (W0 : Set G) * (W2 : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hW0norm, ← hsup]
    exact hx
  obtain ⟨a, ha, b, hb', rfl⟩ := hxmul
  have hQ0eq := Q_zero_eq_Z Y H hZ h3 h4 hb he hr
  have hQ2eq := Q_two_eq_Z Y H hZ h3 h4 hb he hr
  have hZ0elem : IsElemAbelian 2 (Y.Z 0) := (caseA_n Y H hZ h3 h4 hb he).2.1
  have hZ2elem : IsElemAbelian 2 (Y.Z 2) := isElemAbelian_Z_two Y H hZ h3 h4 hb he
  have ha2 : a ^ 2 = 1 := hZ0elem.2 a (hQ0eq ▸ ha.1)
  have hb2 : b ^ 2 = 1 := hZ2elem.2 b (hQ2eq ▸ hb'.1)
  have hcommW' : ⁅W2, W0⁆ ≤ Y.Z 1 := by
    rwa [Subgroup.commutator_comm] at hcommW
  have hz : ⁅b, a⁆ ∈ Y.Z 1 := hcommW' (Subgroup.commutator_mem_commutator hb' ha)
  have hza : ⁅b, a⁆ * a = a * ⁅b, a⁆ := by
    have hcent := (Subgroup.mem_inf.mp (Y.Z_le_center 1 hz)).2
    exact (Subgroup.mem_centralizer_iff.mp hcent a ha.2).symm
  have hzb : ⁅b, a⁆ * b = b * ⁅b, a⁆ := by
    have hcent := (Subgroup.mem_inf.mp (Y.Z_le_center 1 hz)).2
    exact (Subgroup.mem_centralizer_iff.mp hcent b hb'.2).symm
  have hba : b * a = ⁅b, a⁆ * (a * b) := by
    rw [commutatorElement_def]
    group
  have hsq : (a * b) ^ 2 = ⁅b, a⁆ := by
    calc (a * b) ^ 2 = a * (b * a) * b := by rw [pow_two]; group
      _ = a * (⁅b, a⁆ * (a * b)) * b := by rw [hba]
      _ = (a * a) * (⁅b, a⁆ * b) * b := by
        calc a * (⁅b, a⁆ * (a * b)) * b
            = a * ((⁅b, a⁆ * a) * b) * b := by group
          _ = a * ((a * ⁅b, a⁆) * b) * b := by rw [hza]
          _ = (a * a) * (⁅b, a⁆ * b) * b := by group
      _ = (a * a) * (b * ⁅b, a⁆) * b := by rw [hzb]
      _ = ((a * a) * ⁅b, a⁆) * (b * b) := by
        rw [← hzb]
        group
      _ = (⁅b, a⁆ * (a * a)) * (b * b) := by
        have hza2 : (a * a) * ⁅b, a⁆ = ⁅b, a⁆ * (a * a) := by
          calc (a * a) * ⁅b, a⁆ = a * (a * ⁅b, a⁆) := by group
            _ = a * (⁅b, a⁆ * a) := by rw [← hza]
            _ = (a * ⁅b, a⁆) * a := by group
            _ = (⁅b, a⁆ * a) * a := by rw [← hza]
            _ = ⁅b, a⁆ * (a * a) := by group
        rw [hza2]
      _ = ⁅b, a⁆ * (a * a) * (b * b) := by group
      _ = ⁅b, a⁆ := by
        rw [show a * a = 1 by simpa [pow_two] using ha2,
          show b * b = 1 by simpa [pow_two] using hb2]
        group
  rw [hsq]
  exact hz

private theorem center_subgroupOf_Q_one (Y : Setup Γ G)
    (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    Subgroup.center ↥(Y.Q 1) = (Y.Z 1).subgroupOf (Y.Q 1) := by
  rw [← CFSG.Quasithin.C1GN.centerOf_subgroupOf, center_Q_one_eq_Z_one Y H hZ h3 h4 hb he hr]

private theorem isSpecialPow_Q_one (Y : Setup Γ G)
    (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    IsSpecialPow 2 2 2 ↥(Y.Q 1) := by
  let Z := (Y.Z 1).subgroupOf (Y.Q 1)
  haveI := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 1)
  have hP : IsPGroup 2 ↥(Y.Q 1) := pCoreOf_isPGroup' (Y.Gi 1)
  have hQ1card32 : Nat.card ↥(Y.Q 1) = 32 := by
    have hS := card_S_eq_sixtyfour Y H hZ h3 h4 hb he hr
    simpa using card_Q_one_of_card_S Y H hS
  have hcardQ : Nat.card ↥(Y.Q 1) = 2 ^ 5 := by rw [hQ1card32]; norm_num
  have hZcard : Nat.card ↥Z = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Y.Z_le_Q 1)).toEquiv]
    exact card_Z_one_eq_two Y H hZ h3
  have hcenter := center_subgroupOf_Q_one Y H hZ h3 h4 hb he hr
  have hZc : Z ≤ Subgroup.center ↥(Y.Q 1) := by rw [hcenter]
  have hcommZ : ⁅Y.Q 1, Y.Q 1⁆ = Y.Z 1 :=
    commutator_Q_one_eq_Z_one Y H hZ h3 h4 hb he hr
  have hcomm : ∀ x y : ↥(Y.Q 1), ⁅x, y⁆ ∈ Z := by
    intro x y
    rw [Subgroup.mem_subgroupOf]
    change ⁅(x : G), (y : G)⁆ ∈ Y.Z 1
    rw [← hcommZ]
    exact Subgroup.commutator_mem_commutator x.2 y.2
  have hsq : ∀ x : ↥(Y.Q 1), x ^ 2 ∈ Z := by
    intro x
    rw [Subgroup.mem_subgroupOf]
    exact sq_mem_Z_one Y H hZ h3 h4 hb he hr x.2
  have hcent : ∀ x : ↥(Y.Q 1), (∀ y : ↥(Y.Q 1), x * y = y * x) → x ∈ Z := by
    intro x hx
    dsimp only [Z]
    rw [← hcenter]
    exact Subgroup.mem_center_iff.mpr (fun y => (hx y).symm)
  have hnab : ∃ x : ↥(Y.Q 1), x ∉ Z := by
    by_contra h
    push Not at h
    have hsub : (⊤ : Subgroup ↥(Y.Q 1)) ≤ Z := fun x _ => h x
    have hQ1le : Y.Q 1 ≤ Y.Z 1 := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mp (hsub (Subgroup.mem_top ⟨x, hx⟩))
    have hQ1eq : Y.Q 1 = Y.Z 1 := le_antisymm hQ1le (Y.Z_le_Q 1)
    have hZ1abel : IsMulCommutative ↥(Y.Z 1) := by
      refine Subgroup.le_centralizer_iff_isMulCommutative.mp ?_
      intro z hz
      exact Subgroup.centralizer_le (fun x hx => Y.Z_le_Q 1 hx)
        (Subgroup.mem_inf.mp (Y.Z_le_center 1 hz)).2
    exact not_isMulCommutative_Q_one Y H hZ h3 h4 hb he hr (by
      rw [hQ1eq]
      exact hZ1abel)
  have hspecial : CFSG.Quasithin.F6.IsSpecialTwoOnePlusFour ↥(Y.Q 1) :=
    CFSG.Quasithin.F6.GoldAmL2T.isSpecialTwoOnePlusFour_of_center hP hcardQ hZcard hZc
      hcomm hsq hcent hnab
  exact isSpecialPow_of_isSpecialTwoOnePlusFour hspecial

private theorem hasB_one_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    Y.HasB 1 2 := by
  have hQ0eq := Q_zero_eq_Z Y H hZ h3 h4 hb he hr
  have hZ1Q0 : Y.Z 1 ≤ Y.Q 0 := hQ0eq ▸ ((Z_one_le Y H hZ h3).trans inf_le_left)
  have hZ1Q2 : Y.Z 1 ≤ Y.Q 2 := by
    rw [← Q_zero_inf_Q_two_eq_Z_one Y H hZ h3 h4 hb he hr]
    exact inf_le_right
  have hZ1Gm1 : Y.Z 1 ≤ Y.Gi (-1) := by
    simpa using hZ1Q0.trans ((Y.Q_le_Gi_adj 0).trans inf_le_left)
  have hZ1G3 : Y.Z 1 ≤ Y.Gi 3 := by
    simpa using hZ1Q2.trans ((Y.Q_le_Gi_adj 2).trans inf_le_right)
  have hZ1card := card_Z_one_eq_two Y H hZ h3
  have hZ1notGT : ¬ Y.Z 1 ≤ Y.GT := by
    intro hle
    have hdvd : 2 ∣ Nat.card ↥(Y.GT) := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [hZ1card] at h
    obtain ⟨m, hm⟩ := H.odd_GT
    rw [hm] at hdvd
    omega
  have harc13 : Y.Z 1 ≤ Y.arcStab (-1) 3 := by
    rw [Y.arcStab_eq_inf (by norm_num)]
    exact le_inf hZ1Gm1 hZ1G3
  have hnot4 : ¬ Y.Z 1 ≤ Y.Gi 4 := by
    intro hle4
    apply hZ1notGT
    have harc : Y.Z 1 ≤ Y.arcStab (-1) 4 := by
      rw [Y.arcStab_eq_inf (by norm_num)]
      exact le_inf hZ1Gm1 hle4
    have hGT : Y.arcStab (-1) 4 = Y.GT := by
      have h := hr.2 (-1) 5 (by norm_num)
      simpa using h
    rwa [hGT] at harc
  have hnotm2 : ¬ Y.Z 1 ≤ Y.Gi (-2) := by
    intro hlem2
    apply hZ1notGT
    have harc : Y.Z 1 ≤ Y.arcStab (-2) 3 := by
      rw [Y.arcStab_eq_inf (by norm_num)]
      exact le_inf hlem2 hZ1G3
    have hGT : Y.arcStab (-2) 3 = Y.GT := by
      have h := hr.2 (-2) 5 (by norm_num)
      simpa using h
    rwa [hGT] at harc
  refine ⟨?_, hnot4, hnotm2⟩
  intro j hj
  have hj' : -2 ≤ j ∧ j ≤ 2 := by omega
  have hle : Y.Z 1 ≤ Y.Gi (1 + j) := by
    refine harc13.trans (Y.arcStab_le_Gi_of_between ?_ ?_)
    · omega
    · omega
  simpa using hle

private theorem conj_eq_self_of_mem_center_two
    {G : Type*} [Group G] {Z : Subgroup G} (hZcard : Nat.card ↥Z = 2)
    {x q : G} (hx3 : x ^ 3 = 1)
    (hZx : ∀ z ∈ Z, x * z * x⁻¹ = z)
    (h : x * q * x⁻¹ * q⁻¹ ∈ Z) :
    x * q * x⁻¹ = q := by
  have hxq : ⁅x, q⁆ = 1 :=
    CFSG.GroupTheory.commutatorElement_eq_one_of_pow_three hx3
      (fun z hz => mul_inv_eq_iff_eq_mul.mp (hZx z hz))
      (fun z hz => by
        have h := pow_card_eq_one' (x := (⟨z, hz⟩ : ↥Z))
        rw [hZcard] at h
        simpa using congrArg Subtype.val h)
      (by rwa [commutatorElement_def])
  exact mul_inv_eq_iff_eq_mul.mpr (commutatorElement_eq_one_iff_mul_comm.mp hxq)

private theorem conj_mem_inf_centralizer_of_conj_mul_mem {G : Type*} [Group G]
    {Q Z : Subgroup G} {x y g : G} (hZcard : Nat.card Z = 2) (hx3 : x ^ 3 = 1)
    (hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z) (hQQ : ⁅Q, Q⁆ ≤ Z)
    (hgQ : g ∈ Subgroup.normalizer (Q : Set G)) (hy : y = x ∨ y = x⁻¹)
    (hgx : g * x * g⁻¹ * y⁻¹ ∈ Q) :
    ∀ c ∈ Q ⊓ Subgroup.centralizer ({x} : Set G),
      g * c * g⁻¹ ∈ Q ⊓ Subgroup.centralizer ({x} : Set G) := by
  rcases hy with hxy | hxy
  · have hgx' : g * x * g⁻¹ * x⁻¹ ∈ Q := by simpa [hxy] using hgx
    intro c hc
    obtain ⟨hcQ, hcx⟩ := Subgroup.mem_inf.mp hc
    have hcx' : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hcx
    have hcxc : x * c * x⁻¹ = c := by
      calc x * c * x⁻¹ = (c * x) * x⁻¹ := by rw [← hcx']
        _ = c := by group
    have hgcQ : g * c * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hgQ c).mp hcQ
    refine Subgroup.mem_inf.mpr ⟨hgcQ, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    set d : G := g * c * g⁻¹ with hd
    set s : G := g * x * g⁻¹ * x⁻¹ with hs
    have hsQ : s ∈ Q := hgx'
    have heq : d = (g * x * g⁻¹) * d * (g * x * g⁻¹)⁻¹ := by
      rw [hd]
      have h1 : (g * x * g⁻¹) * (g * c * g⁻¹) * (g * x * g⁻¹)⁻¹ =
          g * (x * c * x⁻¹) * g⁻¹ := by group
      rw [h1, hcxc]
    have hs_eq : g * x * g⁻¹ = s * x := by rw [hs]; group
    have hxd : x * d * x⁻¹ = s⁻¹ * d * s := by
      rw [hs_eq] at heq
      have hcomm : s * x * d = d * (s * x) := by
        have h := congrArg (fun t => t * (s * x)) heq
        simpa [mul_assoc] using h.symm
      calc x * d * x⁻¹ = s⁻¹ * (s * x * d) * x⁻¹ := by group
        _ = s⁻¹ * (d * (s * x)) * x⁻¹ := by rw [hcomm]
        _ = s⁻¹ * d * s := by group
    have hmem : x * d * x⁻¹ * d⁻¹ ∈ Z := by
      rw [hxd]
      exact hQQ (by simpa [commutatorElement_def] using
        Subgroup.commutator_mem_commutator (Q.inv_mem hsQ) hgcQ)
    have hconj : x * d * x⁻¹ = d :=
      conj_eq_self_of_mem_center_two hZcard hx3 hxZ hmem
    calc d * x = (x * d * x⁻¹) * x := by rw [hconj]
      _ = x * d := by group
  · have hgx' : g * x * g⁻¹ * x ∈ Q := by
      rw [hxy] at hgx
      simpa using hgx
    intro c hc
    obtain ⟨hcQ, hcx⟩ := Subgroup.mem_inf.mp hc
    have hcx' : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hcx
    have hcxc : x * c * x⁻¹ = c := by
      calc x * c * x⁻¹ = (c * x) * x⁻¹ := by rw [← hcx']
        _ = c := by group
    have hgcQ : g * c * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hgQ c).mp hcQ
    refine Subgroup.mem_inf.mpr ⟨hgcQ, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx3' : x⁻¹ ^ 3 = 1 := by
      rw [show x⁻¹ ^ 3 = (x ^ 3)⁻¹ by group, hx3, inv_one]
    have hxZ' : ∀ z ∈ Z, x⁻¹ * z * (x⁻¹)⁻¹ = z := by
      intro z hz
      rw [inv_inv]
      have h := hxZ z hz
      calc x⁻¹ * z * x = x⁻¹ * (x * z * x⁻¹) * x := by rw [h]
        _ = z := by group
    set d : G := g * c * g⁻¹ with hd
    set s : G := g * x * g⁻¹ * x with hs
    have hsQ : s ∈ Q := hgx'
    have heq : d = (g * x * g⁻¹) * d * (g * x * g⁻¹)⁻¹ := by
      rw [hd]
      have h1 : (g * x * g⁻¹) * (g * c * g⁻¹) * (g * x * g⁻¹)⁻¹ =
          g * (x * c * x⁻¹) * g⁻¹ := by group
      rw [h1, hcxc]
    have hs_eq : g * x * g⁻¹ = s * x⁻¹ := by rw [hs]; group
    have hxd : x⁻¹ * d * x = s⁻¹ * d * s := by
      rw [hs_eq] at heq
      have hcomm : s * x⁻¹ * d = d * (s * x⁻¹) := by
        have h := congrArg (fun t => t * (s * x⁻¹)) heq
        simpa [mul_assoc] using h.symm
      calc x⁻¹ * d * x = s⁻¹ * (s * x⁻¹ * d) * x := by group
        _ = s⁻¹ * (d * (s * x⁻¹)) * x := by rw [hcomm]
        _ = s⁻¹ * d * s := by group
    have hmem' : x⁻¹ * d * x * d⁻¹ ∈ Z := by
      rw [hxd]
      exact hQQ (by simpa [commutatorElement_def] using
        Subgroup.commutator_mem_commutator (Q.inv_mem hsQ) hgcQ)
    have hmem : x⁻¹ * d * (x⁻¹)⁻¹ * d⁻¹ ∈ Z := by simpa using hmem'
    have hconj : x⁻¹ * d * x = d := by
      simpa [inv_inv] using conj_eq_self_of_mem_center_two hZcard hx3' hxZ' hmem
    calc d * x = x * (x⁻¹ * d * x) := by group
      _ = x * d := by rw [hconj]

private def conjAut {G : Type*} [Group G] (Q : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) : MulAut ↥Q :=
  Subgroup.normalizerMonoidHom (H := Q) ⟨g, hg⟩

private lemma conjAut_apply {G : Type*} [Group G] (Q : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) (q : ↥Q) :
    conjAut Q hg q = ⟨g * (q : G) * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp hg (q : G)).mp q.2⟩ := by
  apply Subtype.ext
  rw [conjAut, Subgroup.normalizerMonoidHom_apply_apply_coe]

private lemma map_conjAut_subgroupOf {G : Type*} [Group G] (Q C : Subgroup G) {g : G}
    (hgQ : g ∈ Subgroup.normalizer (Q : Set G))
    (hgC : g ∈ Subgroup.normalizer (C : Set G)) :
    (C.subgroupOf Q).map (conjAut Q hgQ : ↥Q →* ↥Q) = C.subgroupOf Q := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ C := Subgroup.mem_subgroupOf.mp hy
    refine Subgroup.mem_subgroupOf.mpr ?_
    show g * (y : G) * g⁻¹ ∈ C
    exact (Subgroup.mem_normalizer_iff.mp hgC (y : G)).mp hy'
  · intro x hx
    have hxC : (x : G) ∈ C := Subgroup.mem_subgroupOf.mp hx
    have hxQ : (x : G) ∈ Q := x.2
    have hmemQ : g⁻¹ * (x : G) * (g⁻¹)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (Q : Set G)).inv_mem hgQ) (x : G)).mp hxQ
    refine Subgroup.mem_map.mpr ⟨⟨g⁻¹ * (x : G) * (g⁻¹)⁻¹, hmemQ⟩, ?_, ?_⟩
    · refine Subgroup.mem_subgroupOf.mpr ?_
      show g⁻¹ * (x : G) * (g⁻¹)⁻¹ ∈ C
      exact (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (C : Set G)).inv_mem hgC) (x : G)).mp hxC
    · apply Subtype.ext
      change ((conjAut Q hgQ ⟨g⁻¹ * (x : G) * (g⁻¹)⁻¹, hmemQ⟩ : ↥Q) : G) = (x : G)
      rw [conjAut_apply]
      show g * (g⁻¹ * (x : G) * (g⁻¹)⁻¹) * g⁻¹ = (x : G)
      group

private def conjQuotAut {G : Type*} [Group G] (Q C : Subgroup G) [(C.subgroupOf Q).Normal]
    {g : G}
    (hgQ : g ∈ Subgroup.normalizer (Q : Set G))
    (hgC : g ∈ Subgroup.normalizer (C : Set G)) :
    MulAut (↥Q ⧸ C.subgroupOf Q) :=
  QuotientGroup.congr (C.subgroupOf Q) (C.subgroupOf Q) (conjAut Q hgQ)
    (map_conjAut_subgroupOf Q C hgQ hgC)

private lemma conjQuotAut_mk {G : Type*} [Group G] (Q C : Subgroup G) [(C.subgroupOf Q).Normal]
    {g : G}
    (hgQ : g ∈ Subgroup.normalizer (Q : Set G))
    (hgC : g ∈ Subgroup.normalizer (C : Set G)) (q : ↥Q) :
    conjQuotAut Q C hgQ hgC (QuotientGroup.mk q) =
      QuotientGroup.mk (⟨g * (q : G) * g⁻¹,
        (Subgroup.mem_normalizer_iff.mp hgQ (q : G)).mp q.2⟩ : ↥Q) := by
  rw [conjQuotAut, QuotientGroup.congr_mk]
  exact congrArg QuotientGroup.mk (conjAut_apply Q hgQ q)

private def conjQuotHom {G : Type*} [Group G] (Q C M : Subgroup G) [(C.subgroupOf Q).Normal]
    (hMQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hMC : M ≤ Subgroup.normalizer (C : Set G)) :
    ↥M →* MulAut (↥Q ⧸ C.subgroupOf Q) where
  toFun m := conjQuotAut Q C (hMQ m.2) (hMC m.2)
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    rw [conjQuotAut_mk]
    simp
  map_mul' := by
    intro a b
    apply MulEquiv.ext
    intro x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MulAut.mul_apply, conjQuotAut_mk, conjQuotAut_mk, conjQuotAut_mk]
    congr 1
    exact Subtype.ext (by simp only [Subgroup.coe_mul]; group)

private lemma conjQuotHom_apply_mk {G : Type*} [Group G] (Q C M : Subgroup G)
    [(C.subgroupOf Q).Normal]
    (hMQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hMC : M ≤ Subgroup.normalizer (C : Set G)) (m : ↥M) (q : ↥Q) :
    conjQuotHom Q C M hMQ hMC m (QuotientGroup.mk q) = QuotientGroup.mk
      (⟨(m : G) * (q : G) * (m : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hMQ m.2) (q : G)).mp q.2⟩ : ↥Q) :=
  conjQuotAut_mk Q C (hMQ m.2) (hMC m.2) q

private theorem card_centralizer_Q_one (Y : Setup Γ G)
    (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4)
    {x : G} (hxL : x ∈ Y.L 1) (hx3 : orderOf x = 3) :
    Nat.card ↥(Y.Q 1 ⊓ Subgroup.centralizer ({x} : Set G)) = 2 ∨
      Nat.card ↥(Y.Q 1 ⊓ Subgroup.centralizer ({x} : Set G)) = 8 ∨
      Nat.card ↥(Y.Q 1 ⊓ Subgroup.centralizer ({x} : Set G)) = 32 := by
  haveI : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hQfin : Finite ↥(Y.Q 1) := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 1)
  have hS := card_S_eq_sixtyfour Y H hZ h3 h4 hb he hr
  have hQcard : Nat.card ↥(Y.Q 1) = 32 := by
    have h := card_Q_one_of_card_S Y H hS
    simpa using h
  have hxGi : x ∈ Y.Gi 1 := Y.L_le_Gi 1 hxL
  have hxN : x ∈ Subgroup.normalizer (Y.Q 1 : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1) hxGi
  have hx3' : x ^ 3 = 1 := by simpa [hx3] using pow_orderOf_eq_one x
  have hmod := F6.GoldAmN.card_modEq_card_inf_centralizer (Y.Q 1) hx3'
    (fun q hq => (Subgroup.mem_normalizer_iff.mp hxN q).mp hq)
  rw [hQcard] at hmod
  have hdvd : Nat.card ↥(Y.Q 1 ⊓ Subgroup.centralizer ({x} : Set G)) ∣ 32 := by
    rw [← hQcard]
    exact Subgroup.card_dvd_of_le
      (inf_le_left : Y.Q 1 ⊓ Subgroup.centralizer ({x} : Set G) ≤ Y.Q 1)
  exact (by decide : ∀ n ∈ Nat.divisors 32, n % 3 = 2 → n = 2 ∨ n = 8 ∨ n = 32)
    (Nat.card ↥(Y.Q 1 ⊓ Subgroup.centralizer ({x} : Set G)))
    (Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩)
    (by simpa [Nat.ModEq] using hmod.symm.trans (by decide : 32 ≡ 2 [MOD 3]))

private theorem centralizes_of_commutator_mem_Z
    (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    {x e : G} (hxL : x ∈ Y.L 1) (hx3 : orderOf x = 3)
    (hec : ⁅e, x⁆ ∈ Y.Z 1) : x * e * x⁻¹ = e := by
  have hZcard : Nat.card ↥(Y.Z 1) = 2 := card_Z_one_eq_two Y H hZ h3
  have hZ1centL : Y.Z 1 ≤ Subgroup.centralizer (Y.L 1 : Set G) := by
    rw [h4]
    exact inf_le_right
  have hZx : ∀ z ∈ Y.Z 1, x * z * x⁻¹ = z := by
    intro z hz
    have hcomm : x * z = z * x := Subgroup.mem_centralizer_iff.mp (hZ1centL hz) x hxL
    calc x * z * x⁻¹ = (z * x) * x⁻¹ := by rw [hcomm]
      _ = z := by group
  have hmem : x * e * x⁻¹ * e⁻¹ ∈ Y.Z 1 := by
    have h1 : ⁅e, x⁆⁻¹ ∈ Y.Z 1 := (Y.Z 1).inv_mem hec
    have h2 : ⁅e, x⁆⁻¹ = x * e * x⁻¹ * e⁻¹ := by
      rw [commutatorElement_def]
      group
    simpa [h2] using h1
  have hx3' : x ^ 3 = 1 := by
    simpa [hx3] using pow_orderOf_eq_one x
  exact conj_eq_self_of_mem_center_two hZcard hx3' hZx hmem

private theorem exists_mem_L_one_conj_mul_mem_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {x : G} (hxL : x ∈ Y.L 1) (hx3 : orderOf x = 3) :
    ∃ t : G, t ∈ Y.L 1 ∧ t * x * t⁻¹ * x ∈ Y.Q 1 := by
  haveI : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hLfin : Finite ↥(Y.L 1) :=
    Finite.of_injective (Subgroup.inclusion (Y.L_le_Gi 1))
      (Subgroup.inclusion_injective (Y.L_le_Gi 1))
  haveI hQfin : Finite ↥(Y.Q 1) := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 1)
  let xL : ↥(Y.L 1) := ⟨x, hxL⟩
  let xq : oTwoQuot ↥(Y.L 1) := QuotientGroup.mk xL
  have hxq3 : orderOf xq = 3 := by
    let xq' : oTwoQuot ↥(Y.L 1) := QuotientGroup.mk ⟨x, hxL⟩
    have h := orderOf_map_dvd (QuotientGroup.mk' (pCore 2 ↥(Y.L 1))) xL
    have hdvd : orderOf xq ∣ 3 := by
      rw [← hx3]
      simpa [xq, xL, xq', Subgroup.orderOf_coe] using h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      have hxQ : x ∈ Y.Q 1 := by
        have hker : xq = 1 := orderOf_eq_one_iff.mp h1
        have hxpc : xL ∈ pCore 2 ↥(Y.L 1) := by
          rw [← QuotientGroup.eq_one_iff]
          exact hker
        have hxpc' : (x : G) ∈ pCoreOf 2 (Y.L 1) := by
          exact Subgroup.mem_map.mpr ⟨xL, hxpc, rfl⟩
        rwa [(Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).pCoreOf_eq] at hxpc'
      exact F6.GoldAmN.not_mem_of_isPGroup_two (pCoreOf_isPGroup' (Y.Gi 1)) hx3 hxQ
    · exact h3
  have hquot : IsL2Quot 1 (oTwoQuot ↥(Y.L 1)) := by
    have hN := Y.hyp.isLocL2_oTwoPrime (Y.vert 1)
    rw [← H.n_one]
    exact hN.quot
  rcases hquot with ⟨e⟩
  let e' : oTwoQuot ↥(Y.L 1) ≃* Equiv.Perm (Fin 3) := e.trans CFSG.Quasithin.permThreeEquivPSL.symm
  have hσ3 : (e' xq) ^ 3 = 1 := by
    rw [← map_pow, show xq ^ 3 = 1 by rw [← hxq3]; exact pow_orderOf_eq_one xq, map_one]
  have hxq1 : xq ≠ 1 := by
    intro h
    rw [h] at hxq3
    simp at hxq3
  have hσ1 : e' xq ≠ 1 := (MulEquiv.map_ne_one_iff e').mpr hxq1
  let τ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  have hτinv : τ * (e' xq) * τ⁻¹ = (e' xq)⁻¹ :=
    F6.GoldAmN.perm3_inv_of_involution (e' xq) τ hσ3 hσ1 (by decide) (by decide)
  let τq : oTwoQuot ↥(Y.L 1) := e'.symm τ
  have hτq : τq * xq * τq⁻¹ = xq⁻¹ := by
    apply e'.injective
    simp only [τq, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hτinv
  obtain ⟨tL, htL⟩ := QuotientGroup.mk_surjective τq
  have htL' : QuotientGroup.mk' (pCore 2 ↥(Y.L 1)) tL = τq := htL
  have hxq' : QuotientGroup.mk' (pCore 2 ↥(Y.L 1)) xL = xq := rfl
  refine ⟨(tL : G), tL.2, ?_⟩
  let pL : ↥(Y.L 1) := tL * xL * tL⁻¹ * xL
  have hp1 : QuotientGroup.mk' (pCore 2 ↥(Y.L 1)) pL = 1 := by
    change QuotientGroup.mk' (pCore 2 ↥(Y.L 1)) (tL * xL * tL⁻¹ * xL) = 1
    rw [map_mul, map_mul, map_mul, map_inv]
    rw [htL', hxq']
    rw [hτq]
    group
  have hpP : pL ∈ pCore 2 ↥(Y.L 1) := by
    rw [← QuotientGroup.eq_one_iff]
    exact hp1
  have hpQ : (pL : G) ∈ pCoreOf 2 (Y.L 1) :=
    Subgroup.mem_map.mpr ⟨pL, hpP, rfl⟩
  rw [(Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).pCoreOf_eq] at hpQ
  simpa [pL, xL] using hpQ

private theorem false_of_card_inf_centralizer_eq_eight (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {r₀ : ℕ} (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4)
    {x : G} (hxL : x ∈ Y.L 1) (hx3 : orderOf x = 3)
    (hZC : Y.Z 1 ≤ Y.Q 1 ⊓ Subgroup.centralizer ({x} : Set G))
    (hC8 : Nat.card ↥(Y.Q 1 ⊓ Subgroup.centralizer ({x} : Set G)) = 8) : False := by
  haveI hQfin : Finite ↥(Y.Q 1) := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 1)
  let C : Subgroup G := Y.Q 1 ⊓ Subgroup.centralizer ({x} : Set G)
  have hZ1centL : Y.Z 1 ≤ Subgroup.centralizer (Y.L 1 : Set G) := by
    rw [h4]
    exact inf_le_right
  have hQcard : Nat.card ↥(Y.Q 1) = 32 := by
    simpa using card_Q_one_of_card_S Y H (card_S_eq_sixtyfour Y H hZ h3 h4 hb he hr)
  have hZcard : Nat.card ↥(Y.Z 1) = 2 := card_Z_one_eq_two Y H hZ h3
  have hKcard : Nat.card ↥(Y.K) = 3 := card_K Y H hZ h3 h4 hb he
  have hcommQ : ⁅Y.Q 1, Y.Q 1⁆ ≤ Y.Z 1 :=
    commutator_Q_one_le_Z_one Y H hZ h3 h4 hb he hr
  have hx3' : x ^ 3 = 1 := by
    simpa [hx3] using pow_orderOf_eq_one x
  have hxZ : ∀ z ∈ Y.Z 1, x * z * x⁻¹ = z := by
    intro z hz
    have hcomm : x * z = z * x := Subgroup.mem_centralizer_iff.mp (hZ1centL hz) x hxL
    calc x * z * x⁻¹ = (z * x) * x⁻¹ := by rw [hcomm]
      _ = z := by group
  haveI hCfin : Finite ↥C :=
    Finite.of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  have hCnorm : ∀ q ∈ Y.Q 1, ∀ c ∈ C, q * c * q⁻¹ ∈ C := by
    intro q hq c hc
    obtain ⟨hcQ, -⟩ := Subgroup.mem_inf.mp hc
    have hcc : ⁅q, c⁆ ∈ Y.Z 1 := hcommQ (Subgroup.commutator_mem_commutator hq hcQ)
    have hmem : q * c * q⁻¹ = ⁅q, c⁆ * c := by
      rw [commutatorElement_def]; group
    rw [hmem]
    exact C.mul_mem (hZC hcc) hc
  have hxN : x ∈ Subgroup.normalizer (Y.Q 1 : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1)) (Y.L_le_Gi 1 hxL)
  have hx_ne : ¬ ∀ q ∈ Y.Q 1, x * q * x⁻¹ * q⁻¹ ∈ C := by
    intro hxact
    have hxcent : ∀ q ∈ Y.Q 1, x * q * x⁻¹ = q := by
      intro q hq
      exact conj_eq_self_of_commutator_mem_centralizer (pCoreOf_isPGroup' (Y.Gi 1)) hxN hx3'
        hq (Subgroup.mem_inf.mp (hxact q hq)).2
    have hCeq : C = Y.Q 1 := by
      refine le_antisymm inf_le_left ?_
      intro q hq
      have hxq : x * q = q * x := by
        calc x * q = (x * q * x⁻¹) * x := by group
          _ = q * x := by rw [hxcent q hq]
      exact Subgroup.mem_inf.mpr ⟨hq, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hxq.symm⟩
    have hC8' : Nat.card ↥C = 8 := hC8
    have h32 : Nat.card ↥C = 32 := by rw [hCeq, hQcard]
    omega
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hKfin : Finite ↥(Y.K) := finite_of_le_stabilizer Y.hyp (Y.K_le_Gi 0)
  obtain ⟨k0, hk0ord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Y.K)) 3 (by simp [hKcard])
  let k : G := (k0 : G)
  have hkK : k ∈ Y.K := k0.2
  have hkord : orderOf k = 3 := by
    rw [show k = (k0 : G) from rfl, Subgroup.orderOf_coe]
    exact hk0ord
  have hk3 : k ^ 3 = 1 := by
    simpa [hkord] using pow_orderOf_eq_one k
  have hkQ : k ∈ Subgroup.normalizer (Y.Q 1 : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1)) (Y.K_le_Gi 1 hkK)
  have hKzp : Subgroup.zpowers k = Y.K := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hkK) ?_
    rw [Nat.card_zpowers, hkord, hKcard]
  have hCk : ∀ q ∈ Y.Q 1, k * q * k⁻¹ = q → q ∈ C := by
    intro q hq hfix
    have hqcent : q ∈ Subgroup.centralizer (Y.K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [← hKzp] at hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcommk : Commute (k : G) q := by
        show k * q = q * k
        calc k * q = (k * q * k⁻¹) * k := by group
          _ = q * k := by rw [hfix]
      exact (hcommk.zpow_left n).eq
    have hmem : q ∈ Y.Q 1 ⊓ Subgroup.centralizer (Y.K : Set G) :=
      Subgroup.mem_inf.mpr ⟨hq, hqcent⟩
    rw [centralizer_K_Q_one Y H hZ h3 h4 hb he hr] at hmem
    exact hZC hmem
  have hk_ne : ¬ ∀ q ∈ Y.Q 1, k * q * k⁻¹ * q⁻¹ ∈ C := by
    intro hktriv
    exact false_of_trivial_quotient_action (Q := Y.Q 1) (C := C) (k := k)
      inf_le_left hC8 hQcard hCnorm hkQ hk3 hCk hktriv
  have hxC : x ∈ Subgroup.normalizer (C : Set G) := by
    have hxcentC : x ∈ Subgroup.centralizer (C : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
    exact Subgroup.centralizer_le_normalizer (C : Set G) hxcentC
  have hkxQ : k * x * k⁻¹ * x⁻¹ ∈ Y.Q 1 :=
    comm_K_L_one_le Y H (Subgroup.commutator_mem_commutator hkK hxL)
  have hkC : k ∈ Subgroup.normalizer (C : Set G) :=
    CFSG.GH74.KGroups.mem_normalizer_of_conj_mem C k (fun c hc =>
      conj_mem_inf_centralizer_of_conj_mul_mem hZcard hx3' hxZ hcommQ hkQ (Or.inl rfl) hkxQ c hc)
  have hQ_le_NC : Y.Q 1 ≤ Subgroup.normalizer (C : Set G) :=
    fun q hq =>
      CFSG.GH74.KGroups.mem_normalizer_of_conj_mem C q (fun c hc => hCnorm q hq c hc)
  haveI hCn : (C.subgroupOf (Y.Q 1)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hQ_le_NC
  obtain ⟨t, htL, htx⟩ := exists_mem_L_one_conj_mul_mem_Q_one Y H hxL hx3
  have htQ : t ∈ Subgroup.normalizer (Y.Q 1 : Set G) :=
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1)) (Y.L_le_Gi 1 htL)
  have htC : t ∈ Subgroup.normalizer (C : Set G) :=
    CFSG.GH74.KGroups.mem_normalizer_of_conj_mem C t (fun c hc =>
      conj_mem_inf_centralizer_of_conj_mul_mem hZcard hx3' hxZ hcommQ htQ (Or.inr rfl)
        (by simpa using htx) c hc)
  let M : Subgroup G :=
    Subgroup.normalizer (Y.Q 1 : Set G) ⊓ Subgroup.normalizer (C : Set G)
  have hMQ : M ≤ Subgroup.normalizer (Y.Q 1 : Set G) := inf_le_left
  have hMC : M ≤ Subgroup.normalizer (C : Set G) := inf_le_right
  let φ : ↥M →* MulAut (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1)) :=
    conjQuotHom (Y.Q 1) C M hMQ hMC
  have hQM : Y.Q 1 ≤ M := fun q hq =>
    Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer (H := Y.Q 1) hq, hQ_le_NC hq⟩
  have hQtriv : ∀ (q : G) (hq : q ∈ Y.Q 1), φ ⟨q, hQM hq⟩ = 1 := by
    intro q hq
    apply MulEquiv.ext
    intro v
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    rw [conjQuotHom_apply_mk]
    simp only [MulAut.one_apply]
    have hcomm : q * (y : G) * q⁻¹ * (y : G)⁻¹ ∈ C :=
      hZC (hcommQ (Subgroup.commutator_mem_commutator hq y.2))
    rw [QuotientGroup.eq_iff_div_mem]
    refine Subgroup.mem_subgroupOf.mpr ?_
    simpa [div_eq_mul_inv] using hcomm
  have hxM : x ∈ M := Subgroup.mem_inf.mpr ⟨hxN, hxC⟩
  have hkM : k ∈ M := Subgroup.mem_inf.mpr ⟨hkQ, hkC⟩
  have htM : t ∈ M := Subgroup.mem_inf.mpr ⟨htQ, htC⟩
  let xM : ↥M := ⟨x, hxM⟩
  let kM : ↥M := ⟨k, hkM⟩
  let tM : ↥M := ⟨t, htM⟩
  have hσk_ne : (φ kM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) ≠ 1 := by
    intro h1
    apply hk_ne
    intro q hq
    have h2 : (φ kM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1)))
        (QuotientGroup.mk ⟨q, hq⟩) = QuotientGroup.mk ⟨q, hq⟩ := by
      rw [h1]; rfl
    have h3 : φ kM (QuotientGroup.mk ⟨q, hq⟩) = QuotientGroup.mk ⟨q, hq⟩ := by
      simpa using h2
    rw [conjQuotHom_apply_mk] at h3
    rw [QuotientGroup.eq_iff_div_mem] at h3
    have h4 := Subgroup.mem_subgroupOf.mp h3
    simpa [div_eq_mul_inv] using h4
  have hσx_ne : (φ xM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) ≠ 1 := by
    intro h1
    apply hx_ne
    intro q hq
    have h2 : (φ xM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1)))
        (QuotientGroup.mk ⟨q, hq⟩) = QuotientGroup.mk ⟨q, hq⟩ := by
      rw [h1]; rfl
    have h3 : φ xM (QuotientGroup.mk ⟨q, hq⟩) = QuotientGroup.mk ⟨q, hq⟩ := by
      simpa using h2
    rw [conjQuotHom_apply_mk] at h3
    rw [QuotientGroup.eq_iff_div_mem] at h3
    have h4 := Subgroup.mem_subgroupOf.mp h3
    simpa [div_eq_mul_inv] using h4
  haveI : Fintype (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1)) := Fintype.ofFinite _
  have hquot_card : Fintype.card (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1)) = 4 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    have hCsubcard : Nat.card ↥(C.subgroupOf (Y.Q 1)) = Nat.card ↥C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have h := Subgroup.index_mul_card (H := C.subgroupOf (Y.Q 1))
    rw [hCsubcard, hC8, hQcard] at h
    omega
  have hσk3 : (φ kM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) ^ 3 = 1 := by
    have h : (φ kM) ^ 3 = 1 := by
      rw [← map_pow]
      have hkM3 : kM ^ 3 = 1 := by
        apply Subtype.ext
        show k ^ 3 = (1 : G)
        rw [hk3]
      simpa using congrArg φ hkM3
    change ((φ kM ^ 3 : MulAut (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) :
      Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) = 1
    rw [h]
    rfl
  have hσx3 : (φ xM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) ^ 3 = 1 := by
    have h : (φ xM) ^ 3 = 1 := by
      rw [← map_pow]
      have hxM3 : xM ^ 3 = 1 := by
        apply Subtype.ext
        show x ^ 3 = (1 : G)
        rw [hx3']
      simpa using congrArg φ hxM3
    change ((φ xM ^ 3 : MulAut (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) :
      Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) = 1
    rw [h]
    rfl
  have hcomm_action : ∀ (a b : G) (haM : a ∈ M) (hbM : b ∈ M),
      a * b * a⁻¹ * b⁻¹ ∈ Y.Q 1 →
      φ ⟨a, haM⟩ * φ ⟨b, hbM⟩ = φ ⟨b, hbM⟩ * φ ⟨a, haM⟩ := by
    intro a b haM hbM hab
    have h1 : φ (⟨a, haM⟩ * ⟨b, hbM⟩ * ⟨a, haM⟩⁻¹ * ⟨b, hbM⟩⁻¹) = 1 := by
      have heq : (⟨a, haM⟩ * ⟨b, hbM⟩ * ⟨a, haM⟩⁻¹ * ⟨b, hbM⟩⁻¹ : ↥M) =
          ⟨a * b * a⁻¹ * b⁻¹, hQM hab⟩ := by
        ext
        rfl
      rw [heq]
      exact hQtriv (a * b * a⁻¹ * b⁻¹) hab
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 := congrArg (fun t => t * φ ⟨b, hbM⟩ * φ ⟨a, haM⟩) h1
    simpa [mul_assoc] using h2
  have hinv_action : ∀ (a b : G) (haM : a ∈ M) (hbM : b ∈ M),
      a * b * a⁻¹ * b ∈ Y.Q 1 →
      φ ⟨a, haM⟩ * φ ⟨b, hbM⟩ * (φ ⟨a, haM⟩)⁻¹ = (φ ⟨b, hbM⟩)⁻¹ := by
    intro a b haM hbM hab
    have h1 : φ (⟨a, haM⟩ * ⟨b, hbM⟩ * ⟨a, haM⟩⁻¹ * ⟨b, hbM⟩) = 1 := by
      have heq : (⟨a, haM⟩ * ⟨b, hbM⟩ * ⟨a, haM⟩⁻¹ * ⟨b, hbM⟩ : ↥M) =
          ⟨a * b * a⁻¹ * b, hQM hab⟩ := by
        ext
        rfl
      rw [heq]
      exact hQtriv (a * b * a⁻¹ * b) hab
    rw [map_mul, map_mul, map_mul, map_inv] at h1
    have h2 := congrArg (fun t => t * (φ ⟨b, hbM⟩)⁻¹) h1
    simpa [mul_assoc] using h2
  have hxkQ : x * k * x⁻¹ * k⁻¹ ∈ Y.Q 1 := by
    have h := (Y.Q 1).inv_mem hkxQ
    have h2 : (k * x * k⁻¹ * x⁻¹)⁻¹ = x * k * x⁻¹ * k⁻¹ := by group
    rwa [h2] at h
  have hαβ : (φ xM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) * (φ kM) =
      (φ kM) * (φ xM) := by
    rw [show (φ xM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) * (φ kM) =
        ((φ xM * φ kM : MulAut (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) :
          Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) from rfl,
      show (φ kM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) * (φ xM) =
        ((φ kM * φ xM : MulAut (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) :
          Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) from rfl,
      hcomm_action x k hxM hkM hxkQ]
  have hτβ : (φ tM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) * (φ kM) =
      (φ kM) * (φ tM) := by
    have htkQ : t * k * t⁻¹ * k⁻¹ ∈ Y.Q 1 := by
      have h := (Y.Q 1).inv_mem
        (comm_K_L_one_le Y H (Subgroup.commutator_mem_commutator hkK htL))
      have h2 : ⁅k, t⁆⁻¹ = t * k * t⁻¹ * k⁻¹ := by
        rw [commutatorElement_def]; group
      rwa [h2] at h
    rw [show (φ tM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) * (φ kM) =
        ((φ tM * φ kM : MulAut (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) :
          Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) from rfl,
      show (φ kM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) * (φ tM) =
        ((φ kM * φ tM : MulAut (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) :
          Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) from rfl,
      hcomm_action t k htM hkM htkQ]
  have hτinv : (φ tM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) * (φ xM) *
      (φ tM)⁻¹ = (φ xM)⁻¹ := by
    rw [show (φ tM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) * (φ xM) *
          (φ tM)⁻¹ =
        ((φ tM * φ xM * (φ tM)⁻¹ : MulAut (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) :
          Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) from rfl,
      show (φ xM)⁻¹ = (((φ xM)⁻¹ : MulAut (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) :
          Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) from rfl,
      hinv_action t x htM hxM htx]
  have hατ : (φ xM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) * (φ tM) =
      (φ tM) * (φ xM) :=
    perm_commute_of_card_four (W := ↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1)) hquot_card
      (φ kM) (φ xM) (φ tM) hσk_ne hσk3 hαβ hτβ
  have hα_eq : (φ xM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) = 1 := by
    have h3 : (φ tM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) * (φ xM) =
        (φ xM)⁻¹ * (φ tM) := by
      have h2 : (φ tM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) *
          (φ xM) =
          ((φ tM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) * (φ xM) *
            ((φ tM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))))⁻¹) * (φ tM) := by
        group
      rw [h2]
      exact congrArg (fun u => u * (φ tM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1)))) hτinv
    have h4 : (φ xM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) * (φ tM) =
        (φ xM)⁻¹ * (φ tM) := hατ.trans h3
    have h5 : (φ xM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) = (φ xM)⁻¹ :=
      mul_right_cancel h4
    have h6 : (φ xM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) ^ 2 = 1 := by
      rw [pow_two]
      calc (φ xM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) * (φ xM) =
          (φ xM)⁻¹ * (φ xM) := by rw [h5]
        _ = 1 := inv_mul_cancel (φ xM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1)))
    have h7 : (φ xM : Equiv.Perm (↥(Y.Q 1) ⧸ C.subgroupOf (Y.Q 1))) = 1 := by
      have h8 := hσx3
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, h6, one_mul] at h8
      exact h8
    exact h7
  exact hσx_ne hα_eq

private theorem natSec_Q_one (Y : Setup Γ G)
    (H : Y.Sec5Hyp s n₀) {r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    NatSec (Y.L 1) (centerOf (Y.Q 1)) (Y.Q 1) := by
  intro x hxL hx3 e heQ hec
  haveI : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hQfin : Finite ↥(Y.Q 1) := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 1)
  let C : Subgroup G := Y.Q 1 ⊓ Subgroup.centralizer ({x} : Set G)
  have hZ1centL : Y.Z 1 ≤ Subgroup.centralizer (Y.L 1 : Set G) := by
    rw [h4]
    exact inf_le_right
  have hZC : Y.Z 1 ≤ C := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨Y.Z_le_Q 1 hz, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hZ1centL hz) x hxL).symm
  have hecZ : ⁅e, x⁆ ∈ Y.Z 1 := by
    simpa [center_Q_one_eq_Z_one Y H hZ h3 h4 hb he hr] using hec
  have hxe : x * e = e * x := by
    have hconj := centralizes_of_commutator_mem_Z Y H hZ h3 h4 hxL hx3 hecZ
    calc x * e = (x * e * x⁻¹) * x := by group
      _ = e * x := by rw [hconj]
  have heC : e ∈ C := by
    refine Subgroup.mem_inf.mpr ⟨heQ, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hxe.symm
  have hCcard := card_centralizer_Q_one Y H hZ h3 h4 hb he hr hxL hx3
  rcases hCcard with hC2 | hC8 | hC32
  · haveI : Finite ↥C := Nat.finite_of_card_ne_zero (by rw [hC2]; norm_num)
    have hCZ : C = Y.Z 1 := by
      exact (Subgroup.eq_of_le_of_card_ge (H := Y.Z 1) (K := C) hZC (by
        rw [hC2, card_Z_one_eq_two Y H hZ h3])).symm
    rw [hCZ] at heC
    simpa [center_Q_one_eq_Z_one Y H hZ h3 h4 hb he hr] using heC
  · exfalso
    exact false_of_card_inf_centralizer_eq_eight Y H hZ h3 h4 hb he hr hxL hx3 hZC hC8
  · have hCQ : C = Y.Q 1 := by
      refine Subgroup.eq_of_le_of_card_ge (H := C) (K := Y.Q 1) inf_le_left ?_
      rw [hC32, card_Q_one_of_card_S Y H (card_S_eq_sixtyfour Y H hZ h3 h4 hb he hr)]
      norm_num
    have hxcentQ : x ∈ Subgroup.centralizer (Y.Q 1 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hqC : q ∈ C := by rw [hCQ]; exact hq
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hqC).2
    have hxGi : x ∈ Y.Gi 1 := Y.L_le_Gi 1 hxL
    have hxQ : x ∈ Y.Q 1 := by
      have hchar := H.char (Y.vert 1)
      exact hchar (Subgroup.mem_inf.mpr ⟨hxGi, hxcentQ⟩)
    exact absurd hxQ (F6.GoldAmN.not_mem_of_isPGroup_two (pCoreOf_isPGroup' (Y.Gi 1)) hx3)

private theorem commutator_le_of_perfect_quotient_action {G : Type*} [Group G]
    {Q Z L : Subgroup G} [Finite ↥Q] [Finite ↥L] [(Z.subgroupOf Q).Normal]
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G))
    (hQcomm : ⁅Q, Q⁆ ≤ Z)
    (hVcard : Nat.card (↥Q ⧸ (Z.subgroupOf Q)) = 4)
    (hperf : Group.IsPerfect (oTwoQuot ↥L))
    (hpQ : CFSG.pCore 2 ↥L ≤ Q.subgroupOf L) :
    ⁅Q, L⁆ ≤ Z := by
  let V := ↥Q ⧸ (Z.subgroupOf Q)
  haveI : Fintype V := Fintype.ofFinite V
  let φ : ↥L →* MulAut V := conjQuotHom Q Z L hLQ hLZ
  have hQker : Q.subgroupOf L ≤ φ.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro v
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    rw [conjQuotHom_apply_mk]
    simp only [MulAut.one_apply]
    have hcomm : (q : G) * (y : G) * (q : G)⁻¹ * (y : G)⁻¹ ∈ Z :=
      hQcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hq) y.2)
    rw [QuotientGroup.eq_iff_div_mem]
    exact Subgroup.mem_subgroupOf.mpr (by simpa [div_eq_mul_inv] using hcomm)
  have hpker : CFSG.pCore 2 ↥L ≤ φ.ker := hpQ.trans hQker
  let ψ : oTwoQuot ↥L →* MulAut V := QuotientGroup.lift _ φ hpker
  have hψ : ∀ l : ↥L, ψ (QuotientGroup.mk l) = φ l := fun l => rfl
  haveI : Group.IsPerfect (oTwoQuot ↥L) := hperf
  have hperf_range : Group.IsPerfect ↥ψ.range := Group.IsPerfect.range ψ
  have hsolv : Group.IsSolvable (MulAut V) := by
    haveI : Group.IsSolvable (Equiv.Perm V) :=
      Equiv.Perm.isSolvable (by rw [hVcard])
    have hf : Function.Injective (MulAction.toPermHom (MulAut V) V) :=
      MulAction.toPerm_injective
    exact Group.isSolvable_of_isSolvable_injective hf
  have hsolv_range : Group.IsSolvable ↥ψ.range :=
    Group.isSolvable_of_isSolvable_injective (f := ψ.range.subtype) ψ.range.subtype_injective
  have hsub : Subsingleton ↥ψ.range := by
    by_contra h
    haveI : Nontrivial ↥ψ.range := not_subsingleton_iff_nontrivial.mp h
    exact Group.IsPerfect.not_isSolvable ↥ψ.range hsolv_range
  have hbot : ψ.range = ⊥ := Subgroup.eq_bot_of_subsingleton ψ.range
  have hφ1 : ∀ l : ↥L, φ l = 1 := by
    intro l
    have hmem : ψ (QuotientGroup.mk l) ∈ ψ.range := ⟨QuotientGroup.mk l, rfl⟩
    rw [hbot] at hmem
    rw [Subgroup.mem_bot] at hmem
    rwa [hψ l] at hmem
  rw [Subgroup.commutator_le]
  intro q hq l hl
  have h2 : φ ⟨l, hl⟩ (QuotientGroup.mk ⟨q, hq⟩) = QuotientGroup.mk ⟨q, hq⟩ := by
    rw [hφ1 ⟨l, hl⟩]; rfl
  rw [conjQuotHom_apply_mk] at h2
  rw [QuotientGroup.eq_iff_div_mem] at h2
  have h3 := Subgroup.mem_subgroupOf.mp h2
  have h3' : l * q * l⁻¹ * q⁻¹ ∈ Z := by simpa [div_eq_mul_inv] using h3
  have h4 : ⁅q, l⁆ = (l * q * l⁻¹ * q⁻¹)⁻¹ := by
    rw [commutatorElement_def]; group
  rw [h4]
  exact Z.inv_mem h3'

private theorem commutator_Q_zero_L_zero_le_Z_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hVcard : Nat.card (↥(Y.Q 0) ⧸ (Y.Z 0).subgroupOf (Y.Q 0)) = 4) :
    ⁅Y.Q 0, Y.L 0⁆ ≤ Y.Z 0 := by
  haveI hQ0fin : Finite ↥(Y.Q 0) := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 0)
  haveI hL0fin : Finite ↥(Y.L 0) := finite_of_le_stabilizer Y.hyp (Y.L_le_Gi 0)
  have hZn : ((Y.Z 0).subgroupOf (Y.Q 0)).Normal := by
    refine Subgroup.normal_of_le_center ?_
    intro z hz
    have hc := Y.Z_le_center 0 (Subgroup.mem_subgroupOf.mp hz)
    have hcent : (z : G) ∈ Subgroup.centralizer (Y.Q 0 : Set G) := by
      rw [centerOf] at hc
      exact (Subgroup.mem_inf.mp hc).2
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simpa using Subgroup.mem_centralizer_iff.mp hcent (y : G) y.2
  have hQcomm : ⁅Y.Q 0, Y.Q 0⁆ ≤ Y.Z 0 :=
    CFSG.GroupTheory.commutator_le_of_relIndex_le_four
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Y.Z_le_Q 0)).mp hZn)
      (by rw [Subgroup.relIndex, Subgroup.index_eq_card, hVcard])
  have hpQ : CFSG.pCore 2 ↥(Y.L 0) ≤ (Y.Q 0).subgroupOf (Y.L 0) := by
    change CFSG.pCore 2 ↥(Y.L 0) ≤ Subgroup.comap (Y.L 0).subtype (Y.Q 0)
    rw [← Subgroup.map_le_iff_le_comap]
    rw [show (CFSG.pCore 2 ↥(Y.L 0)).map (Y.L 0).subtype = pCoreOf 2 (Y.L 0)
        from rfl, (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).pCoreOf_eq]
  have hperf : Group.IsPerfect (oTwoQuot ↥(Y.L 0)) :=
    CFSG.Quasithin.F112R.isPerfect_of_isL2Quot H.two_le (isL2Quot_L_zero Y H)
  haveI : ((Y.Z 0).subgroupOf (Y.Q 0)).Normal := hZn
  exact commutator_le_of_perfect_quotient_action (Q := Y.Q 0) (Z := Y.Z 0) (L := Y.L 0)
    (fun l hl => (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 0))
      (Y.L_le_Gi 0 hl))
    ((Y.L_le_Gi 0).trans (Y.Gi_le_normalizer_Z 0))
    hQcomm hVcard hperf hpQ

private theorem Q_zero_inf_Q_two_le_centralizer_K (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {r₀ : ℕ} (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀)
    (hQL : ⁅Y.Q 0, Y.L 0⁆ ≤ Y.Z 0) :
    Y.Q 0 ⊓ Y.Q 2 ≤ Subgroup.centralizer (Y.K : Set G) := by
  have hPK_Z0 : ⁅Y.Q 0 ⊓ Y.Q 2, Y.K⁆ ≤ Y.Z 0 :=
    (Subgroup.commutator_mono inf_le_left (Y.K_le_L_zero H)).trans hQL
  have hPK_Q2 : ⁅Y.Q 0 ⊓ Y.Q 2, Y.K⁆ ≤ Y.Q 2 :=
    (Subgroup.commutator_mono inf_le_right le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp ((Y.K_le_Gi 2).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 2))))
  have hPK_Z1 : ⁅Y.Q 0 ⊓ Y.Q 2, Y.K⁆ ≤ Y.Z 1 := by
    rw [← caseA_Z_inf_Q Y H h4 hb]
    exact le_inf hPK_Z0 hPK_Q2
  have hZ1card : Nat.card (Y.Z 1) = 2 := card_Z_one_eq_two Y H hZ h3
  have hZ1K : Y.Z 1 ≤ Subgroup.centralizer (Y.K : Set G) := by
    have h := h3
    change ⁅Y.Z 1, Y.K⁆ = ⊥ at h
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hKcard' : Nat.card ↥Y.K = 3 := card_K Y H hZ h3 h4 hb he
  have hPK_bot : ⁅Y.Q 0 ⊓ Y.Q 2, Y.K⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro p hp k hk
    rw [Subgroup.mem_bot]
    have hk3 : k ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (hKcard' ▸ Y.K.orderOf_dvd_natCard hk)
    have hc : ⁅p, k⁆ ∈ Y.Z 1 := hPK_Z1 (Subgroup.commutator_mem_commutator hp hk)
    have hc' : ⁅k, p⁆ ∈ Y.Z 1 := by
      rw [← commutatorElement_inv]
      exact (Y.Z 1).inv_mem hc
    have h1 : ⁅k, p⁆ = 1 :=
      CFSG.GroupTheory.commutatorElement_eq_one_of_pow_three hk3
        (fun z hz => Subgroup.mem_centralizer_iff.mp (hZ1K hz) k hk)
        (fun z hz => by
          have h := pow_card_eq_one' (x := (⟨z, hz⟩ : ↥(Y.Z 1)))
          rw [hZ1card] at h
          simpa using congrArg Subtype.val h)
        hc'
    rw [← commutatorElement_inv, h1, inv_one]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hPK_bot

private theorem card_Q_zero_inf_Q_two_le_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hb : Y.HasB 0 1) (hP : Y.Q 0 ⊓ Y.Q 2 ≤ Y.Qs 1) :
    Nat.card ↥(Y.Q 0 ⊓ Y.Q 2) ≤ 2 := by
  obtain ⟨d, hdJ, hd3⟩ := exists_J_three Y H
  have hP_Cd : Y.Q 0 ⊓ Y.Q 2 ≤ Subgroup.centralizer ({d} : Set G) := by
    have hnormal := (caseA_normal Y H hb).2
    have hcent : Y.Q 0 ⊓ Y.Q 2 ≤
        Subgroup.centralizer (pResidualOf 2 (Y.L 1) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hnormal
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hdres : d ∈ pResidualOf 2 (Y.L 1) := by
      have hJleL : Y.J 1 ≤ Y.L 1 := Y.J_le_L 1
      have hdL : d ∈ Y.L 1 := hJleL hdJ
      rw [pResidualOf]
      exact Subgroup.mem_map.mpr ⟨⟨d, hdL⟩, by
        refine CFSG.Quasithin.SteinbergCD.mem_pResidual_of_odd
          (x := (⟨d, hdL⟩ : ↥(Y.L 1))) ?_
        rw [Subgroup.orderOf_mk d hdL, hd3]
        exact ⟨1, by norm_num⟩, rfl⟩
    exact ((Subgroup.mem_centralizer_iff.mp (hcent hp)) d hdres).symm
  have hP_inf : Y.Q 0 ⊓ Y.Q 2 ≤
      Y.Qs 1 ⊓ Subgroup.centralizer ({d} : Set G) := le_inf hP hP_Cd
  have hle2 : Nat.card ↥(Y.Qs 1 ⊓ Subgroup.centralizer ({d} : Set G)) ≤ 2 :=
    card_Qs_inf_centralizer Y H hdJ hd3
  haveI : Finite ↥(Y.Gi 1) := Y.hyp.finite_stab (Y.vert 1)
  haveI hQsfin : Finite ↥(Y.Qs 1) :=
    Finite.of_injective (Subgroup.inclusion ((inf_le_left).trans (Y.Q_le_Gi 1)))
      (Subgroup.inclusion_injective ((inf_le_left).trans (Y.Q_le_Gi 1)))
  haveI : Finite ↥(Y.Qs 1 ⊓ Subgroup.centralizer ({d} : Set G)) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  haveI : Finite ↥(Y.Q 0 ⊓ Y.Q 2) :=
    Finite.of_injective (Subgroup.inclusion hP_inf) (Subgroup.inclusion_injective hP_inf)
  exact (Subgroup.card_le_of_le hP_inf).trans hle2

theorem caseA_r (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {r r₀ : ℕ}
    (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀)
    (h2 : Y.Step2Conclusion s r r₀) (hr : Y.IsMaxRegLen r) : r = 4 := by
  have hn0 : n₀ = 2 := (caseA_n Y H hZ h3 h4 hb he).1
  have hr0 : r₀ = 2 := (caseA_card_Z Y H hZ h3 h4 hb he).1
  have hZ0card : Nat.card (Y.Z 0) = 16 := by
    simpa [hn0] using (caseA_card_Z Y H hZ h3 h4 hb he).2
  rcases h2 with h2a | h2b | h2c
  · omega
  ·
    obtain ⟨hreq, hnotreg, hsr⟩ := h2b
    have hr6 : r = 6 := by omega
    subst hr6
    have hr' : Y.IsMaxRegLen 6 := hr
    have hs5 : s = 5 := by have := H.five_le; omega
    have h06 : Y.LeftTransAt 0 6 ∧ Y.RightTransAt 0 6 := by
      rcases regular_at_zero_or_one Y hr' with h | h
      · exact h
      · exact absurd h hnotreg
    have hS : Nat.card Y.S = 2 ^ 8 := by
      have h := card_S_of_isMaxRegLen_six_reg Y H hr' hs5 h06
      rw [hn0] at h
      exact h.trans (by norm_num : 4 * 2 ^ 6 = 2 ^ 8)
    haveI hQ0fin : Finite ↥(Y.Q 0) := finite_of_le_stabilizer Y.hyp (Y.Q_le_Gi 0)
    have hQ0 : Nat.card (Y.Q 0) = 2 ^ 6 := by
      have h := Subgroup.relIndex_mul_card (H := Y.Q 0) (K := Y.S)
      have hle : Y.Q 0 ≤ Y.S := by
        rw [← Y.edgeSylow_zero]
        exact Y.Q_le_edgeSylow_left 0
      have hrel : (Y.Q 0).relIndex Y.S = 2 ^ n₀ := by
        rw [← Y.edgeSylow_zero, Y.relIndex_Q_edgeSylow 0, H.n_zero]
      rw [inf_eq_left.mpr hle, hrel, hn0, hS] at h
      norm_num at h ⊢
      omega
    have hQ1 : Nat.card (Y.Q 1) = 2 ^ 7 := by
      have h := Subgroup.relIndex_mul_card (H := Y.Q 1) (K := Y.S)
      have hle : Y.Q 1 ≤ Y.S := by
        rw [← Y.edgeSylow_zero]
        exact Y.Q_le_edgeSylow_right 1
      have hrel : (Y.Q 1).relIndex Y.S = 2 ^ Y.n 1 := by
        rw [← Y.edgeSylow_zero]
        simpa using Y.relIndex_Q_succ_edgeSylow 0
      rw [inf_eq_left.mpr hle, hrel, H.n_one, hS] at h
      norm_num at h ⊢
      omega
    have hAleQ1 : Y.Q 0 ⊓ Y.Q 2 ≤ Y.Q 1 := by
      simpa using (Y.shift 1).Q_neg_one_inf_Q_one_le_Q_zero
    have hPcard : Nat.card ↥(Y.Q 0 ⊓ Y.Q 2) = 8 := by
      have hrel := Y.relIndex_inf_Q H 1
      rw [show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num] at hrel
      have hn2 : Y.n 2 = n₀ := by rw [Y.n_two, H.n_zero]
      rw [hn2, hn0] at hrel
      have h := Subgroup.relIndex_mul_card (H := Y.Q 0 ⊓ Y.Q 2) (K := Y.Q 1)
      rw [inf_eq_left.mpr hAleQ1, hrel, hQ1] at h
      norm_num at h ⊢
      omega
    haveI hZ0fin : Finite ↥(Y.Z 0) :=
      Nat.finite_of_card_ne_zero (by rw [hZ0card]; norm_num)
    haveI hL0fin : Finite ↥(Y.L 0) := finite_of_le_stabilizer Y.hyp (Y.L_le_Gi 0)
    have hVcard : Nat.card (↥(Y.Q 0) ⧸ (Y.Z 0).subgroupOf (Y.Q 0)) = 4 := by
      rw [← Subgroup.index_eq_card]
      have hZsubcard : Nat.card ↥((Y.Z 0).subgroupOf (Y.Q 0)) = 16 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Y.Z_le_Q 0)).toEquiv]
        exact hZ0card
      have h := Subgroup.index_mul_card (H := (Y.Z 0).subgroupOf (Y.Q 0))
      rw [hZsubcard, hQ0] at h
      omega
    have hQL : ⁅Y.Q 0, Y.L 0⁆ ≤ Y.Z 0 := commutator_Q_zero_L_zero_le_Z_zero Y H hVcard
    have hPcent : Y.Q 0 ⊓ Y.Q 2 ≤ Subgroup.centralizer (Y.K : Set G) :=
      Q_zero_inf_Q_two_le_centralizer_K Y H hZ h3 h4 hb he hQL
    have hP_Qs : Y.Q 0 ⊓ Y.Q 2 ≤ Y.Qs 1 := by
      have h := le_inf hAleQ1 hPcent
      simpa [Setup.Qs] using h
    have hle := card_Q_zero_inf_Q_two_le_two Y H hb hP_Qs
    rw [hPcard] at hle
    omega
  ·
    obtain ⟨-, -, -, hB2, -⟩ := h2c
    exact absurd (HasB.unique (X := Y) hb hB2) (by norm_num)

theorem caseA_struct (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {r₀ : ℕ} (hZ : Y.Zt 0 ≠ ⊥) (h3 : Y.Zt 1 = ⊥) (h4 : Y.Z 1 = centerOf (Y.L 1))
    (hb : Y.HasB 0 1) (he : Y.ZtExt 0 r₀ r₀) (hr : Y.IsMaxRegLen 4) :
    s = 5 ∧ Nat.card Y.S = 2 ^ 6 ∧ Y.Q 0 = Y.Z 0 ∧ Y.Q 0 ⊓ Y.Q 2 = Y.Z 1 ∧
      IsSpecialPow 2 2 2 ↥(Y.Q 1) ∧
      NatSec (Y.L 1) (centerOf (Y.Q 1)) (Y.Q 1) ∧ Y.HasB 1 2 :=
  ⟨s_eq_five Y H hr, card_S_eq_sixtyfour Y H hZ h3 h4 hb he hr,
    Q_zero_eq_Z Y H hZ h3 h4 hb he hr, Q_zero_inf_Q_two_eq_Z_one Y H hZ h3 h4 hb he hr,
    isSpecialPow_Q_one Y H hZ h3 h4 hb he hr, natSec_Q_one Y H hZ h3 h4 hb he hr,
    hasB_one_two Y H hZ h3 h4 hb he hr⟩

theorem treeU42_of_caseA (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 ≠ ⊥) (hHQ : HigmanQuad n₀) :
    n₀ = 2 ∧ s = 5 ∧ Y.swap.TreeU42Data := by
  obtain ⟨l, r₀, -, -, he0⟩ := exists_ZtExt Y H hZ
  obtain ⟨hlr, -⟩ := s52_step1 Y H hZ he0
  have he : Y.ZtExt 0 r₀ r₀ := hlr ▸ he0
  obtain ⟨r, -, -, hr⟩ := exists_isMaxRegLen Y H
  have h2 : Y.Step2Conclusion s r r₀ := s52_step2 Y H hZ hr he
  have h3 : Y.Zt 1 = ⊥ := s52_step3 Y H hZ hr he h2
  have h4 : Y.Z 1 = centerOf (Y.L 1) := (s52_step4 Y H hZ h3).1
  have h5a : ¬ Y.Z 0 ≤ Y.Gi (r₀ : ℤ) := s52_step5 Y H hZ h3 he hHQ
  have hev : Y.reverse.ZtExt 0 r₀ r₀ := he.reverse
  have hZrev : Y.reverse.Zt 0 ≠ ⊥ := by
    rw [Setup.reverse_Zt]
    simpa using hZ
  have h3rev : Y.reverse.Zt 1 = ⊥ := by
    rw [Setup.reverse_Zt]
    have h := Y.Zt_add_two (1 : ℤ) (-1)
    rw [show (1 : ℤ) + 2 * (-1) = -1 by norm_num] at h
    rw [h, h3, Subgroup.map_bot]
  have h5b : ¬ Y.Z 0 ≤ Y.Gi (-(r₀ : ℤ)) := by
    have h := s52_step5 Y.reverse H.reverse hZrev h3rev hev hHQ
    rwa [Setup.reverse_Z, Setup.reverse_Gi] at h
  have h6 := s52_step6 Y H hZ h3 hr he h2 ⟨h5a, h5b⟩
  have hb : Y.HasB 0 1 := s52_step7 Y H hZ h3 h4 hr he h2 ⟨h5a, h5b⟩ h6 hHQ
  have hr4 : r = 4 := caseA_r Y H hZ h3 h4 hb he h2 hr
  obtain ⟨hs, hS, hQ0, -, hspec, hnat, -⟩ := caseA_struct Y H hZ h3 h4 hb he (hr4 ▸ hr)
  have hAn := caseA_n Y H hZ h3 h4 hb he
  have hn0 : n₀ = 2 := hAn.1
  have hcardZ : Nat.card (Y.Z 0) = 2 ^ 4 := by
    simpa [hn0] using (caseA_card_Z Y H hZ h3 h4 hb he).2
  have hsq1 : Y.swap.Q 1 = Y.Q 0 := by rw [Setup.swap_Q]; norm_num
  have hsq0 : Y.swap.Q 0 = Y.Q 1 := by rw [Setup.swap_Q]; norm_num
  have hsl1 : Y.swap.L 1 = Y.L 0 := by rw [Setup.swap_L]; norm_num
  have hsl0 : Y.swap.L 0 = Y.L 1 := by rw [Setup.swap_L]; norm_num
  refine ⟨hn0, hs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Setup.swap_S] using hS
  · have h : Y.swap.Q 1 = Y.Z 0 := by rw [hsq1, hQ0]
    exact h.symm ▸ hAn.2.1
  · have h : Y.swap.Q 1 = Y.Z 0 := by rw [hsq1, hQ0]
    exact h.symm ▸ hcardZ
  · have h2 : Y.swap.Q 1 = Y.Z 0 := by rw [hsq1, hQ0]
    exact h2.symm ▸ (hsl1.symm ▸ hAn.2.2.2)
  · exact hsq0.symm ▸ hspec
  · exact hsq0.symm ▸ (hsl0.symm ▸ hnat)
  · have hnotle : ¬ Y.Q 0 ≤ Y.Q 1 := by
      intro hle
      have hZ0 : Y.Z 0 ≤ Y.Gi 2 := by
        refine (Y.Z_le_Q 0).trans (hle.trans ?_)
        intro x hx
        exact (Y.Q_le_Gi_adj 1 hx).2
      exact hb.2.1 (by simpa using hZ0)
    rw [hsq1, hsq0]
    exact hnotle
  · have hsup : Y.Q 0 ⊔ Y.Q 1 = Y.S := Y.Q_zero_sup_Q_one_eq_S H
    rw [hsq1, hsq0, Setup.swap_S]
    simpa [sup_comm] using hsup

end Setup

end CFSG.Quasithin.St84
