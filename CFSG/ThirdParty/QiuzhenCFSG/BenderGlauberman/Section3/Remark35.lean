module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Section 3 — Remark 3.5

Remark 3.5: if `U = B ⋬ G`, then `G1 := N_G(B)` is as in Theorem B
(a proper subgroup containing `H` with one class of involutions).
Proof: `H ≤ N_G(B)` since `U = O(H) ⊴ H`; `N_G(B) ≠ ⊤` by the
non-normality of `U = B`.  For one involution class, first note
`S = ⟨t1, t2⟩ ≤ C_G(U)`, so `B = U` is centralized by every involution
`x ∈ S`; if `x = g·t·g⁻¹`, then `g⁻¹·B·g` is an odd-order subgroup of
`H = B·S` whose image in the `2`-group quotient `H/B` is trivial, hence
`g⁻¹·B·g = B` and `g ∈ N_G(B)`.  Any involution of `N_G(B)` lies in a
Sylow `2`-subgroup of `N_G(B)`, which is `N_G(B)`-conjugate to `S`.
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character

-- Local instances matching `Theory.Character`'s subgroup-sum convention; see
-- `BenderGlauberman/ClassFunction.lean`.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u

section Section3

variable {G : Type u} [Group G] [Fintype G]
variable (c : Hyp11 G)

/-- `S = ⟨t1, t2⟩` in the dihedral Sylow `2`-subgroup. -/
private lemma S_eq_closure_t1_t2 (c : Hyp11 G) :
    (c.S : Subgroup G) = Subgroup.closure ({c.t1, c.t2} : Set G) := by
  classical
  apply le_antisymm
  · intro s hs
    let K : Subgroup G := Subgroup.closure ({c.t1, c.t2} : Set G)
    have hKleS : K ≤ (c.S : Subgroup G) := by
      exact (Subgroup.closure_le (c.S : Subgroup G)).2 (by
        intro x hx
        simp at hx
        rcases hx with rfl | rfl
        · exact c.t1_mem_S
        · exact c.t2_mem_S)
    have hS0leK : (c.S0 : Subgroup G) ≤ K := by
      rw [c.S0_eq_zpowers]
      exact (Subgroup.zpowers_le).2 (K.mul_mem (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)))
    have hKneS0 : K ≠ (c.S0 : Subgroup G) := by
      intro hEq
      exact c.t1_not_mem_S0 (by
        have ht1K : c.t1 ∈ K := Subgroup.subset_closure (by simp)
        simpa [hEq] using ht1K)
    let S0S : Subgroup ↥(c.S : Subgroup G) :=
      (c.S0 : Subgroup G).subgroupOf (c.S : Subgroup G)
    let KS : Subgroup ↥(c.S : Subgroup G) := K.subgroupOf (c.S : Subgroup G)
    have hS0S_le_KS : S0S ≤ KS := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hS0leK (Subgroup.mem_subgroupOf.mp hx))
    have hrel := Subgroup.relIndex_mul_index hS0S_le_KS
    have hrelS0 : S0S.relIndex KS = (c.S0 : Subgroup G).relIndex K :=
      Subgroup.relIndex_subgroupOf hKleS
    have hmul : (c.S0 : Subgroup G).relIndex K * KS.index = 2 := by
      rw [hrelS0] at hrel
      rw [S0_index c] at hrel
      exact hrel
    have hrelne : (c.S0 : Subgroup G).relIndex K ≠ 1 := by
      intro hEq1
      have hKleS0 : K ≤ (c.S0 : Subgroup G) := (Subgroup.relIndex_eq_one).mp hEq1
      exact hKneS0 (le_antisymm hKleS0 hS0leK)
    have hapos : 0 < (c.S0 : Subgroup G).relIndex K :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite
        (H := (c.S0 : Subgroup G).subgroupOf K))
    have hbpos : 0 < KS.index :=
      Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := KS))
    have hb1 : KS.index = 1 := by
      have hb_le2 : (c.S0 : Subgroup G).relIndex K ≤ 2 := by
        exact Nat.le_of_dvd (by norm_num : 0 < 2) ⟨KS.index, hmul.symm⟩
      have hb2 : (c.S0 : Subgroup G).relIndex K = 2 := by omega
      have : 2 * KS.index = 2 := by rwa [hb2] at hmul
      omega
    have hKstop : KS = ⊤ := (Subgroup.index_eq_one).mp hb1
    have hsK : (⟨s, hs⟩ : ↥(c.S : Subgroup G)) ∈ KS := by
      rw [hKstop]
      trivial
    simpa using (Subgroup.mem_subgroupOf.mp hsK)
  · exact (Subgroup.closure_le (c.S : Subgroup G)).2 (by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact c.t1_mem_S
      · exact c.t2_mem_S)

/-- From `U = B`, every element of `S` centralizes `U`. -/
private lemma S_le_centralizer_U (c : Hyp11 G) (hUB : c.U = c.B) :
    (c.S : Subgroup G) ≤ Subgroup.centralizer (c.U : Set G) := by
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have huB : u ∈ c.B := by simpa [hUB] using hu
  unfold Hyp11.B at huB
  have hcomm1 : c.t1 * u = u * c.t1 := by
    have huB1 : u ∈ c.B1 := (Subgroup.mem_inf.mp huB).1
    have huC1 : u ∈ Subgroup.centralizer ({c.t1} : Set G) := (Subgroup.mem_inf.mp huB1).2
    exact ((Subgroup.mem_centralizer_singleton_iff (g := c.t1) (k := u)).mp huC1).symm
  have hcomm2 : c.t2 * u = u * c.t2 := by
    have huB2 : u ∈ c.B2 := (Subgroup.mem_inf.mp huB).2
    have huC2 : u ∈ Subgroup.centralizer ({c.t2} : Set G) := (Subgroup.mem_inf.mp huB2).2
    exact ((Subgroup.mem_centralizer_singleton_iff (g := c.t2) (k := u)).mp huC2).symm
  have ht1C : c.t1 ∈ Subgroup.centralizer ({u} : Set G) :=
    (Subgroup.mem_centralizer_singleton_iff (g := u) (k := c.t1)).2 hcomm1
  have ht2C : c.t2 ∈ Subgroup.centralizer ({u} : Set G) :=
    (Subgroup.mem_centralizer_singleton_iff (g := u) (k := c.t2)).2 hcomm2
  have hclosure : Subgroup.closure ({c.t1, c.t2} : Set G) ≤
      Subgroup.centralizer ({u} : Set G) := by
    exact (Subgroup.closure_le (Subgroup.centralizer ({u} : Set G))).2 (by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact ht1C
      · exact ht2C)
  have hsC : s ∈ Subgroup.centralizer ({u} : Set G) := by
    apply hclosure
    rwa [S_eq_closure_t1_t2 c] at hs
  exact ((Subgroup.mem_centralizer_singleton_iff (g := u) (k := s)).mp hsC).symm

/-- From `U = B`, every element of `U` centralizes `S`. -/
private lemma U_le_centralizer_S (c : Hyp11 G) (hUB : c.U = c.B) :
    c.U ≤ Subgroup.centralizer ((c.S : Subgroup G) : Set G) := by
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hsC : s ∈ Subgroup.centralizer (c.U : Set G) := (S_le_centralizer_U c hUB) hs
  exact ((Subgroup.mem_centralizer_iff.mp hsC) u hu).symm

/-- `U = O(H)` is normal in `H`. -/
private lemma U_normal_in_H (c : Hyp11 G) : IsNormalIn c.U c.H := by
  constructor
  · intro u hu
    have huU : u ∈ (pPrimeCore 2 c.H).map c.H.subtype := by
      simpa [Hyp11.U, oddCoreOf] using hu
    exact SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)) huU
  · intro h hh u hu
    have huU : u ∈ (pPrimeCore 2 c.H).map c.H.subtype := by
      simpa [Hyp11.U, oddCoreOf] using hu
    rcases (Subgroup.mem_map.mp huU) with ⟨x, hx, hxeq⟩
    have huH : u ∈ c.H :=
      SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H)) huU
    have hxeq' : (⟨u, huH⟩ : ↥c.H) = x := by
      ext
      simpa using hxeq.symm
    have hconj : (⟨h, hh⟩ : ↥c.H) * x * (⟨h, hh⟩ : ↥c.H)⁻¹ ∈ pPrimeCore 2 c.H :=
      (pPrimeCore_normal (p := 2) (G := ↥c.H)).conj_mem x hx (⟨h, hh⟩ : ↥c.H)
    refine (Subgroup.mem_map.mpr ?_)
    refine ⟨(⟨h * u * h⁻¹, c.H.mul_mem (c.H.mul_mem hh huH) (c.H.inv_mem hh)⟩ : ↥c.H), ?_, rfl⟩
    have hcx : (⟨h, hh⟩ : ↥c.H) * x * (⟨h, hh⟩ : ↥c.H)⁻¹ =
        (⟨h * u * h⁻¹, c.H.mul_mem (c.H.mul_mem hh huH) (c.H.inv_mem hh)⟩ : ↥c.H) := by
      ext
      have hxval : (x : G) = u :=
        (congrArg (fun z : ↥c.H => (z : G)) hxeq').symm
      simp [hxval]
    rwa [← hcx]

/-- `H ≤ N_G(U)`. -/
private lemma H_le_normalizer_U (c : Hyp11 G) :
    c.H ≤ Subgroup.normalizer (c.U : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact (U_normal_in_H c).2 h hh u hu
  · intro hhu
    have hEq : h⁻¹ * (h * u * h⁻¹) * h = u := by group
    have huH : h⁻¹ * (h * u * h⁻¹) * h ∈ c.U := by
      simpa using (U_normal_in_H c).2 h⁻¹ (c.H.inv_mem hh) (h * u * h⁻¹) hhu
    rwa [hEq] at huH

/-- `H ≤ N_G(B)` (via `U = B`). -/
private lemma H_le_normalizerB (c : Hyp11 G) (hUB : c.U = c.B) : c.H ≤ normalizerB c := by
  intro h hh
  have hN : h ∈ Subgroup.normalizer (c.U : Set G) := H_le_normalizer_U c hh
  unfold normalizerB
  simpa [hUB] using hN

/-- `N_G(B) ≠ ⊤` when `U = B` is not normal in `G`. -/
private lemma normalizerB_ne_top (c : Hyp11 G) (hUB : c.U = c.B)
    (hUnormal : ¬ IsNormalIn c.U ⊤) : normalizerB c ≠ ⊤ := by
  intro htop
  have hBnormal : (c.B : Subgroup G).Normal := by
    unfold normalizerB at htop
    exact Subgroup.normalizer_eq_top_iff.mp htop
  have hUnormalG : (c.U : Subgroup G).Normal := by
    rw [hUB]
    exact hBnormal
  apply hUnormal
  constructor
  · intro g hg
    trivial
  · intro g hg u hu
    exact hUnormalG.conj_mem u hu g

/-- `B = U` has odd order. -/
private lemma B_odd_card (c : Hyp11 G) (hUB : c.U = c.B) :
    Nat.Coprime 2 (Nat.card ↥c.B) := by
  have h1 : Nat.card ↥c.U = Nat.card (pPrimeCore 2 c.H) := by
    dsimp [Hyp11.U]
    rw [oddCoreOf]
    exact Subgroup.card_map_of_injective (f := c.H.subtype)
      (K := pPrimeCore 2 c.H) (Subgroup.subtype_injective c.H)
  have hcop : Nat.Coprime 2 (Nat.card ↥c.U) := by
    rw [h1]
    exact pPrimeCore_coprime_card (p := 2) (G := c.H)
  rwa [hUB] at hcop

/-- `B ≤ C_G(S)`. -/
private lemma B_le_centralizer_S (c : Hyp11 G) (hUB : c.U = c.B) :
    (c.B : Subgroup G) ≤ Subgroup.centralizer ((c.S : Subgroup G) : Set G) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hbU : b ∈ c.U := by simpa [hUB] using hb
  have hsC : s ∈ Subgroup.centralizer (c.U : Set G) := (S_le_centralizer_U c hUB) hs
  exact ((Subgroup.mem_centralizer_iff.mp hsC) b hbU).symm

/-- Every element of `H = B·S` has a `2`-power power lying in `B`. -/
private lemma H_pow_mem_B (c : Hyp11 G) (hUB : c.U = c.B) :
    ∀ h : G, h ∈ c.H → ∃ n : ℕ, h ^ (2 ^ n) ∈ c.B := by
  classical
  intro h hh
  have hUleNS : c.U ≤ Subgroup.normalizer ((c.S : Subgroup G) : Set G) :=
    (U_le_centralizer_S c hUB).trans
      (Subgroup.centralizer_le_normalizer ((c.S : Subgroup G) : Set G))
  have hHset : (c.H : Set G) = (c.U : Set G) * ((c.S : Subgroup G) : Set G) := by
    rw [← c.H_eq_US]
    exact Subgroup.coe_mul_of_left_le_normalizer_right c.U (c.S : Subgroup G) hUleNS
  have hh' : h ∈ (c.U : Set G) * ((c.S : Subgroup G) : Set G) := by
    rw [← hHset]
    exact hh
  rcases hh' with ⟨u, hu, s, hs, hEq⟩
  refine ⟨c.m + 1, ?_⟩
  have hcomm : Commute u s := by
    have huC : u ∈ Subgroup.centralizer ((c.S : Subgroup G) : Set G) :=
      (U_le_centralizer_S c hUB) hu
    exact ((Subgroup.mem_centralizer_iff.mp huC) s hs).symm
  have hpowu : u ^ (2 ^ (c.m + 1)) ∈ c.U :=
    (c.U : Subgroup G).pow_mem hu (2 ^ (c.m + 1))
  have hpowuB : u ^ (2 ^ (c.m + 1)) ∈ c.B := by
    rwa [hUB] at hpowu
  have hs1 : s ^ (2 ^ (c.m + 1)) = 1 := by
    have hcard : Nat.card ↥(c.S : Subgroup G) = 2 ^ (c.m + 1) := by
      rw [S_nat_card c]
      ring
    have hs1' : (⟨s, hs⟩ : ↥(c.S : Subgroup G)) ^ (2 ^ (c.m + 1)) = 1 := by
      rw [← hcard]
      exact pow_card_eq_one' (G := ↥(c.S : Subgroup G)) (x := ⟨s, hs⟩)
    simpa [Subgroup.coe_pow] using congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hs1'
  have hEq' : h ^ (2 ^ (c.m + 1)) = u ^ (2 ^ (c.m + 1)) := by
    rw [← hEq]
    rw [hcomm.mul_pow, hs1, mul_one]
  rwa [hEq']

/-- If `x ∈ S` is an involution conjugate to `t` by `g`, then `g` normalizes `B`. -/
private lemma mem_normalizer_of_conj_t_in_S (c : Hyp11 G) (hUB : c.U = c.B)
    {x : G} (hxS : x ∈ (c.S : Subgroup G)) (_hx : IsInvolution x) :
    ∀ g : G, g * c.t * g⁻¹ = x → g ∈ Subgroup.normalizer ((c.B : Subgroup G) : Set G) := by
  classical
  intro g hg
  have hBleCx : (c.B : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hbC : b ∈ Subgroup.centralizer ((c.S : Subgroup G) : Set G) :=
      (B_le_centralizer_S c hUB) hb
    exact ((Subgroup.mem_centralizer_iff.mp hbC) x hxS).symm
  let f : G →* G := (MulAut.conj g⁻¹).toMonoidHom
  let K : Subgroup G := Subgroup.map f (c.B : Subgroup G)
  have hBleComap : (c.B : Subgroup G) ≤ Subgroup.comap f c.H := by
    intro b hb
    rw [Subgroup.mem_comap]
    rw [c.H_eq_centralizer]
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hbx : b * x = x * b := (Subgroup.mem_centralizer_singleton_iff.mp (hBleCx hb))
    have hgt : g * c.t = x * g := by
      rw [← hg]
      group
    have hgx : g⁻¹ * x = c.t * g⁻¹ := by
      rw [← hg]
      group
    have hcalc : (g⁻¹ * b * g) * c.t = c.t * (g⁻¹ * b * g) := by
      calc
        (g⁻¹ * b * g) * c.t = g⁻¹ * b * (g * c.t) := by group
        _ = g⁻¹ * b * (x * g) := by rw [hgt]
        _ = g⁻¹ * (b * x) * g := by group
        _ = g⁻¹ * (x * b) * g := by rw [hbx]
        _ = (g⁻¹ * x) * (b * g) := by group
        _ = (c.t * g⁻¹) * (b * g) := by rw [hgx]
        _ = c.t * (g⁻¹ * b * g) := by group
    simpa [f, MulAut.conj_apply] using hcalc
  have hKleH : K ≤ c.H := (Subgroup.map_le_iff_le_comap).2 hBleComap
  have hKleB : K ≤ c.B := by
    intro k hk
    have hodd : Nat.Coprime 2 (orderOf k) := by
      rcases (Subgroup.mem_map.mp hk) with ⟨b, hb, hkb⟩
      have hord_eq : orderOf k = orderOf b := by
        rw [← hkb]
        exact orderOf_injective f (MulEquiv.injective (MulAut.conj g⁻¹)) b
      have hord_sub : orderOf (⟨b, hb⟩ : ↥(c.B : Subgroup G)) ∣
          Fintype.card ↥(c.B : Subgroup G) := orderOf_dvd_card
      have hordB : orderOf b ∣ Fintype.card ↥(c.B : Subgroup G) := by
        have hEq : orderOf b = orderOf (⟨b, hb⟩ : ↥(c.B : Subgroup G)) := by
          simpa using (orderOf_injective (c.B : Subgroup G).subtype
            (Subgroup.subtype_injective (c.B : Subgroup G)) ⟨b, hb⟩).symm
        rwa [← hEq] at hord_sub
      have hcard : Fintype.card ↥(c.B : Subgroup G) = Nat.card ↥(c.B : Subgroup G) :=
        Nat.card_eq_fintype_card.symm
      rw [hcard] at hordB
      rw [hord_eq]
      exact Nat.Coprime.symm (Nat.Coprime.coprime_dvd_left hordB
        (Nat.Coprime.symm (B_odd_card c hUB)))
    have hBU : (c.B : Subgroup G) ≤ c.H := by
      have hUleH : c.U ≤ c.H :=
        SetLike.le_def.1 (Subgroup.map_subtype_le (H := c.H) (pPrimeCore 2 c.H))
      simpa [hUB] using hUleH
    have hBnorm : IsNormalIn c.B c.H := by
      simpa [hUB] using U_normal_in_H c
    let BH : Subgroup ↥c.H := (c.B : Subgroup G).subgroupOf c.H
    have : BH.Normal := (Subgroup.normal_subgroupOf_iff hBU).2 (by
      intro h b hb hh
      exact (hBnorm.2 b hh h hb))
    let q : ↥c.H →* (↥c.H ⧸ BH) := QuotientGroup.mk' BH
    let kH : ↥c.H := ⟨k, hKleH hk⟩
    rcases (H_pow_mem_B c hUB k (hKleH hk)) with ⟨n, hkn⟩
    have hqpow : q kH ^ (2 ^ n) = 1 := by
      have hkHpow : kH ^ (2 ^ n) ∈ BH := by
        apply Subgroup.mem_subgroupOf.mpr
        simpa [Subgroup.coe_pow] using hkn
      have hq : q (kH ^ (2 ^ n)) = 1 :=
        (QuotientGroup.eq_one_iff (x := kH ^ (2 ^ n))).mpr hkHpow
      simpa [map_pow] using hq
    have hdvd2 : orderOf (q kH) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hqpow
    have hkpow1 : kH ^ orderOf k = 1 := by
      apply Subtype.ext
      change (k : G) ^ orderOf k = 1
      exact pow_orderOf_eq_one k
    have hqpow2 : q kH ^ orderOf k = 1 := by
      have hq : q (kH ^ orderOf k) = 1 := by
        simpa using congrArg q hkpow1
      simpa [map_pow] using hq
    have hdvdk : orderOf (q kH) ∣ orderOf k := orderOf_dvd_of_pow_eq_one hqpow2
    have hcopq : Nat.Coprime 2 (orderOf (q kH)) :=
      Nat.Coprime.symm (Nat.Coprime.coprime_dvd_left hdvdk (Nat.Coprime.symm hodd))
    have hcopq' : Nat.Coprime (orderOf (q kH)) (2 ^ n) :=
      Nat.Coprime.pow_right n (Nat.Coprime.symm hcopq)
    have hord1 : orderOf (q kH) = 1 := Nat.Coprime.eq_one_of_dvd hcopq' hdvd2
    have hq1 : q kH = 1 := orderOf_eq_one_iff.mp hord1
    have hkHmem : kH ∈ BH := by
      rw [← QuotientGroup.ker_mk' BH]
      exact MonoidHom.mem_ker.mpr hq1
    simpa using (Subgroup.mem_subgroupOf.mp hkHmem)
  have hcardK : Nat.card ↥K = Nat.card ↥(c.B : Subgroup G) :=
    Subgroup.card_map_of_injective (K := c.B) (f := f)
      (MulEquiv.injective (MulAut.conj g⁻¹))
  have hK_eq_B : K = c.B := by
    apply Subgroup.eq_of_le_of_card_ge hKleB
    rw [hcardK]
  have hmapK : Subgroup.map (MulAut.conj g).toMonoidHom K = c.B := by
    calc
      Subgroup.map (MulAut.conj g).toMonoidHom K
          = Subgroup.map (MulAut.conj g).toMonoidHom
              (Subgroup.map f (c.B : Subgroup G)) := rfl
      _ = Subgroup.map ((MulAut.conj g).toMonoidHom.comp f) (c.B : Subgroup G) := by
            rw [Subgroup.map_map]
      _ = Subgroup.map (MonoidHom.id G) (c.B : Subgroup G) := by
            congr 1
            apply MonoidHom.ext
            intro a
            simp [f, MulAut.conj_apply]
            group
      _ = c.B := by simp
  have hmapB : Subgroup.map (MulAut.conj g).toMonoidHom (c.B : Subgroup G) = c.B := by
    rwa [hK_eq_B] at hmapK
  exact (Subgroup.mem_normalizer_iff_map_conj_eq).mpr hmapB

/-- Every involution of `N_G(B)` is `N_G(B)`-conjugate to `t`. -/
private lemma involution_normalizer_conj_to_t (c : Hyp11 G) (hUB : c.U = c.B)
    {w : G} (hwN : w ∈ normalizerB c) (hw : IsInvolution w) :
    ∃ cw : G, cw ∈ normalizerB c ∧ cw * c.t * cw⁻¹ = w := by
  classical
  let N : Subgroup G := normalizerB c
  have hSleN : (c.S : Subgroup G) ≤ N := (S_le_H c).trans (H_le_normalizerB c hUB)
  let SN : Sylow 2 ↥N := c.S.subtype hSleN
  let wN : ↥N := ⟨w, hwN⟩
  have hwne : wN ≠ 1 := by
    intro h
    apply hw.1
    exact congrArg (fun z : ↥N => (z : G)) h
  have hw2 : wN ^ 2 = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow, pow_two] using hw.2
  let Y : Subgroup ↥N := Subgroup.zpowers wN
  have hYp : IsPGroup 2 Y := by
    intro a
    refine ⟨1, ?_⟩
    have ha : (a : ↥N) ∈ Subgroup.zpowers wN := a.2
    rcases (Subgroup.mem_zpowers_iff.mp ha) with ⟨k, hk⟩
    have hpowN : (a : ↥N) ^ 2 = 1 := by
      rw [← hk]
      have hw2z : wN ^ (2 : ℤ) = 1 := by
        exact zpow_ofNat wN 2 ▸ hw2
      calc
        (wN ^ k) ^ 2 = (wN ^ k) * (wN ^ k) := by rw [pow_two]
        _ = wN ^ (k + k) := by rw [← zpow_add wN k k]
        _ = wN ^ (2 * k) := by ring_nf
        _ = (wN ^ (2 : ℤ)) ^ k := by rw [zpow_mul wN 2 k]
        _ = 1 := by rw [hw2z]; simp
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using hpowN
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  rcases (IsPGroup.exists_le_sylow (p := 2) (G := ↥N) (P := Y) hYp) with ⟨Q, hYleQ⟩
  rcases (MulAction.exists_smul_eq (M := ↥N) Q SN) with ⟨n, hn⟩
  have hwQ : wN ∈ Q := hYleQ (Subgroup.mem_zpowers wN)
  have hwconj : (n : ↥N) * wN * (n : ↥N)⁻¹ ∈ (SN : Subgroup ↥N) := by
    have hQmem : (MulAut.conj (n : ↥N)) wN ∈
        (Q : Subgroup ↥N).map (MulAut.conj (n : ↥N)).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj (n : ↥N)).toMonoidHom hwQ
    have hsub' : (Q : Subgroup ↥N).map (MulAut.conj (n : ↥N)).toMonoidHom =
        (SN : Subgroup ↥N) := by
      apply Subgroup.ext
      intro x
      constructor
      · intro hx
        rcases (Subgroup.mem_map.mp hx) with ⟨y, hyQ, hxy⟩
        have hyset : x ∈ (MulAut.conj (n : ↥N)) • (Q : Set ↥N) := by
          simpa [MulAut.smul_def, MulAut.conj_apply, hxy.symm] using
            (Set.smul_mem_smul_set (a := (MulAut.conj (n : ↥N)))
              (s := (Q : Set ↥N)) hyQ)
        have hc := congrArg (fun P : Sylow 2 ↥N => (P : Subgroup ↥N)) hn
        rw [Sylow.coe_subgroup_smul] at hc
        have hcset : (MulAut.conj (n : ↥N)) • (Q : Set ↥N) = (SN : Set ↥N) := by
          exact congrArg (fun H : Subgroup ↥N => (H : Set ↥N)) hc
        rwa [hcset] at hyset
      · intro hx
        have hc := congrArg (fun P : Sylow 2 ↥N => (P : Subgroup ↥N)) hn
        rw [Sylow.coe_subgroup_smul] at hc
        have hcset : (MulAut.conj (n : ↥N)) • (Q : Set ↥N) = (SN : Set ↥N) := by
          exact congrArg (fun H : Subgroup ↥N => (H : Set ↥N)) hc
        have hyset : x ∈ (MulAut.conj (n : ↥N)) • (Q : Set ↥N) := by
          rwa [hcset]
        rcases (Set.mem_smul_set.mp hyset) with ⟨y, hyQ, hxy⟩
        refine (Subgroup.mem_map.mpr ⟨y, hyQ, ?_⟩)
        simpa [MulAut.smul_def, MulAut.conj_apply] using hxy
    have hmem : (MulAut.conj (n : ↥N)) wN ∈ (SN : Subgroup ↥N) := by
      rwa [hsub'] at hQmem
    simpa [MulAut.conj_apply] using hmem
  let z : G := (n : G) * w * (n : G)⁻¹
  have hzS : z ∈ (c.S : Subgroup G) := by
    have hc : (SN : Subgroup ↥N) = (c.S : Subgroup G).subgroupOf N :=
      Sylow.coe_subtype c.S hSleN
    have hw' : (n : ↥N) * wN * (n : ↥N)⁻¹ ∈ (c.S : Subgroup G).subgroupOf N := by
      rwa [hc] at hwconj
    change (n : G) * w * (n : G)⁻¹ ∈ (c.S : Subgroup G)
    simpa [wN, Subgroup.coe_mul, Subgroup.coe_inv] using (Subgroup.mem_subgroupOf.mp hw')
  have hz : IsInvolution z := by
    constructor
    · intro hz1
      apply hw.1
      calc
        w = (n : G)⁻¹ * z * (n : G) := by simp [z]; group
        _ = (n : G)⁻¹ * 1 * (n : G) := by rw [hz1]
        _ = 1 := by simp
    · calc
        z ^ 2 = ((n : G) * w * (n : G)⁻¹) * ((n : G) * w * (n : G)⁻¹) := by
          dsimp [z]
          rw [pow_two]
        _ = (n : G) * (w * w) * (n : G)⁻¹ := by group
        _ = 1 := by
          rw [show w * w = 1 by simpa [pow_two] using hw.2]
          simp
  rcases (c.one_involution_class c.t z c.t_involution hz) with ⟨g0, hg0⟩
  have hg0N : g0 ∈ N := by
    change g0 ∈ normalizerB c
    unfold normalizerB
    exact (mem_normalizer_of_conj_t_in_S c hUB hzS hz) g0 hg0
  refine ⟨(n : G)⁻¹ * g0, ?_, ?_⟩
  · exact N.mul_mem (N.inv_mem n.2) hg0N
  · calc
      ((n : G)⁻¹ * g0) * c.t * ((n : G)⁻¹ * g0)⁻¹
          = (n : G)⁻¹ * (g0 * c.t * g0⁻¹) * (n : G) := by group
      _ = (n : G)⁻¹ * z * (n : G) := by rw [hg0]
      _ = w := by simp [z]; group

/-- `N_G(B)` has exactly one class of involutions. -/
private lemma one_involution_class_in_normalizerB (c : Hyp11 G) (hUB : c.U = c.B) :
    ∀ x y : G, IsInvolution x → IsInvolution y → x ∈ normalizerB c → y ∈ normalizerB c →
      ∃ g : G, g ∈ normalizerB c ∧ g * x * g⁻¹ = y := by
  classical
  intro x y hx hy hxN hyN
  rcases involution_normalizer_conj_to_t c hUB hxN hx with ⟨cx, hcxN, hcxt⟩
  rcases involution_normalizer_conj_to_t c hUB hyN hy with ⟨cy, hcyN, hcyt⟩
  refine ⟨cy * cx⁻¹, ?_, ?_⟩
  · exact (normalizerB c).mul_mem hcyN ((normalizerB c).inv_mem hcxN)
  · calc
      (cy * cx⁻¹) * x * (cy * cx⁻¹)⁻¹ = cy * (cx⁻¹ * x * cx) * cy⁻¹ := by group
      _ = cy * c.t * cy⁻¹ := by
        have hxeq : cx⁻¹ * x * cx = c.t := by
          calc
            cx⁻¹ * x * cx = cx⁻¹ * (cx * c.t * cx⁻¹) * cx := by rw [hcxt]
            _ = c.t := by group
        rw [hxeq]
      _ = y := hcyt

/-- Remark 3.5: if `U = B ⋬ G`, then `G1 := N_G(B)` is as in Theorem B
(i.e., a proper subgroup containing `H` with one class of involutions). -/
public theorem remark_3_5 (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hUB : c.U = c.B) (hUnormal : ¬ IsNormalIn c.U ⊤) :
    normalizerB c ≠ ⊤ ∧ c.H ≤ normalizerB c ∧
      (∀ x y : G, IsInvolution x → IsInvolution y → x ∈ normalizerB c →
        y ∈ normalizerB c → ∃ g : G, g ∈ normalizerB c ∧ g * x * g⁻¹ = y) := by
  constructor
  · exact normalizerB_ne_top c hUB hUnormal
  constructor
  · exact H_le_normalizerB c hUB
  · exact one_involution_class_in_normalizerB c hUB

end Section3

end CFSG.BenderGlauberman
