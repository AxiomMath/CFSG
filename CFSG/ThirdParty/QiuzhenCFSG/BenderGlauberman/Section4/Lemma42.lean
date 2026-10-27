module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.NuHatOrbit
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Section4.Basic
import all CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

namespace CFSG
end CFSG
open CFSG

/-!
# Bender--Glauberman: Lemma 4.2

For every Section-4 character `μ` there is a character `μ'` of `G` such that
`(δν, μ')_G` is odd exactly when `ν̂` and `μ̂` are conjugate under
`N_G(S)`.  The character is the induction to `G` of `μ̂`, inflated from
`B` to `C_G(S) = S × B`.
-/

noncomputable section

open scoped BigOperators
open scoped commutatorElement
open scoped Pointwise

namespace CFSG.BenderGlauberman

open GorensteinWalter
open Theory.Character
open Sylow

-- Local instances matching `Theory.Character`'s subgroup-sum convention; see
-- `BenderGlauberman/ClassFunction.lean`.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

universe u

section Section4

variable {G : Type u} [Group G] [Fintype G]
variable (c : Hyp11 G)

/-- In the Section-4 case `|S| = 4`, the Sylow subgroup `S` is abelian
(it is dihedral of order four). -/
private lemma S_abelian_s4 (hS4 : Section4Hyp c) :
    IsMulCommutative (↥(c.S : Subgroup G)) := by
  classical
  rcases c.dihedralEquiv with ⟨e⟩
  have hm : c.m = 1 := by
    have h : 2 * 2 ^ c.m = 4 := by
      have hS4' : Nat.card (↥(c.S : Subgroup G)) = 4 := by
        exact hS4
      rw [← S_nat_card c, hS4']
    have hpow : 2 ^ c.m = 2 := Nat.eq_of_mul_eq_mul_left (by norm_num) h
    have hcases : c.m = 0 ∨ c.m = 1 ∨ 2 ≤ c.m := by omega
    rcases hcases with h0 | h1 | h2
    · rw [h0] at hpow
      norm_num at hpow
    · exact h1
    · have hge : 4 ≤ 2 ^ c.m := Nat.pow_le_pow_right (by norm_num : 0 < 2) h2
      omega
  have hpowm : 2 ^ c.m = 2 := by
    rw [hm]
    norm_num
  have hD : IsMulCommutative (DihedralGroup (2 ^ c.m)) :=
    (DihedralGroup.commutative_iff).2 (Or.inr hpowm)
  rw [isMulCommutative_iff]
  intro a b
  apply e.injective
  rw [map_mul, map_mul]
  exact (isMulCommutative_iff.mp hD) (e a) (e b)

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

/-- `C_G(S)`, the centralizer of the Sylow `2`-subgroup `S`. -/
private noncomputable def centralizerS (c : Hyp11 G) : Subgroup G :=
  Subgroup.centralizer ((c.S : Subgroup G) : Set G)

/-- `S ≤ C_G(S)`. -/
private lemma S_le_centralizerS (hS4 : Section4Hyp c) :
    (c.S : Subgroup G) ≤ centralizerS c := by
  intro s hs
  change s ∈ Subgroup.centralizer ((c.S : Subgroup G) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hcomm : s * a = a * s :=
    congrArg Subtype.val ((isMulCommutative_iff.mp (S_abelian_s4 c hS4))
      ⟨s, hs⟩ ⟨a, ha⟩)
  exact hcomm.symm

/-- `B ≤ C_G(S)`. -/
private lemma B_le_centralizerS (c : Hyp11 G) :
    (c.B : Subgroup G) ≤ centralizerS c := by
  intro b hb
  change b ∈ Subgroup.centralizer ((c.S : Subgroup G) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hbB : b ∈ c.B := hb
  have hbB' : b ∈ Hyp11.B1 c ⊓ Hyp11.B2 c := by
    exact hbB
  have hb1 : c.t1 * b = b * c.t1 := by
    have hbB1 : b ∈ Hyp11.B1 c := (Subgroup.mem_inf.mp hbB').1
    have hbB1' : b ∈ c.U ⊓ Subgroup.centralizer ({c.t1} : Set G) := by
      simpa [Hyp11.B1, centralizerIn] using hbB1
    have hbC1 : b ∈ Subgroup.centralizer ({c.t1} : Set G) :=
      (Subgroup.mem_inf.mp hbB1').2
    exact ((Subgroup.mem_centralizer_singleton_iff (g := c.t1) (k := b)).mp hbC1).symm
  have hb2 : c.t2 * b = b * c.t2 := by
    have hbB2 : b ∈ Hyp11.B2 c := (Subgroup.mem_inf.mp hbB').2
    have hbB2' : b ∈ c.U ⊓ Subgroup.centralizer ({c.t2} : Set G) := by
      simpa [Hyp11.B2, centralizerIn] using hbB2
    have hbC2 : b ∈ Subgroup.centralizer ({c.t2} : Set G) :=
      (Subgroup.mem_inf.mp hbB2').2
    exact ((Subgroup.mem_centralizer_singleton_iff (g := c.t2) (k := b)).mp hbC2).symm
  have ht1C : c.t1 ∈ Subgroup.centralizer ({b} : Set G) :=
    (Subgroup.mem_centralizer_singleton_iff (g := b) (k := c.t1)).2 hb1
  have ht2C : c.t2 ∈ Subgroup.centralizer ({b} : Set G) :=
    (Subgroup.mem_centralizer_singleton_iff (g := b) (k := c.t2)).2 hb2
  have hclosure : Subgroup.closure ({c.t1, c.t2} : Set G) ≤
      Subgroup.centralizer ({b} : Set G) := by
    exact (Subgroup.closure_le (Subgroup.centralizer ({b} : Set G))).2 (by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact ht1C
      · exact ht2C)
  have hsC : s ∈ Subgroup.centralizer ({b} : Set G) := by
    apply hclosure
    rwa [S_eq_closure_t1_t2 c] at hs
  exact (Subgroup.mem_centralizer_singleton_iff (g := b) (k := s)).mp hsC

/-- `C_G(S) ≤ H = C_G(t)`. -/
private lemma centralizerS_le_H (c : Hyp11 G) : centralizerS c ≤ c.H := by
  intro x hx
  rw [c.H_eq_centralizer]
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzS : z = c.t := by simpa using hz
  rw [hzS]
  exact (Subgroup.mem_centralizer_iff.mp hx) c.t (c.S0_le_S c.t_mem_S0)

/-- `U ∩ S = 1` in the Section-4 case. -/
private lemma U_inter_S_eq_bot_s4 (hS4 : Section4Hyp c) {x : G}
    (hxU : x ∈ c.U) (hxS : x ∈ (c.S : Subgroup G)) : x = 1 := by
  classical
  have hordU : orderOf x ∣ Nat.card ↥c.U := by
    change orderOf (c.U.subtype (⟨x, hxU⟩ : ↥c.U)) ∣ Nat.card ↥c.U
    rw [orderOf_injective c.U.subtype (Subgroup.subtype_injective c.U) (⟨x, hxU⟩ : ↥c.U)]
    have hxU' : orderOf (⟨x, hxU⟩ : ↥c.U) ∣ Fintype.card ↥c.U :=
      orderOf_dvd_card (G := ↥c.U) (x := ⟨x, hxU⟩)
    rwa [← Nat.card_eq_fintype_card] at hxU'
  have hordS : orderOf x ∣ Nat.card (c.S : Subgroup G) := by
    change orderOf ((c.S : Subgroup G).subtype (⟨x, hxS⟩ : ↥(c.S : Subgroup G))) ∣
      Nat.card (c.S : Subgroup G)
    rw [orderOf_injective (c.S : Subgroup G).subtype
      (Subgroup.subtype_injective (c.S : Subgroup G)) (⟨x, hxS⟩ : ↥(c.S : Subgroup G))]
    have hxS' : orderOf (⟨x, hxS⟩ : ↥(c.S : Subgroup G)) ∣
        Fintype.card ↥(c.S : Subgroup G) :=
      orderOf_dvd_card (G := ↥(c.S : Subgroup G)) (x := ⟨x, hxS⟩)
    rwa [← Nat.card_eq_fintype_card] at hxS'
  have hcop4 : Nat.Coprime (Nat.card ↥c.U) 4 := by
    rw [Nat.coprime_comm]
    exact (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) 2 (Nat.card ↥c.U)).2
      (U_coprime_two c)
  have hcop : Nat.Coprime (Nat.card ↥c.U) (Nat.card (c.S : Subgroup G)) := by
    have hS4' : Nat.card (c.S : Subgroup G) = 4 := by
      exact hS4
    rw [hS4']
    exact hcop4
  have hdvd : orderOf x ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hordU hordS
  have h1 : orderOf x = 1 := Nat.dvd_one.mp hdvd
  exact orderOf_eq_one_iff.mp h1

/-- `B ≤ U`. -/
private lemma B_le_U (c : Hyp11 G) : (c.B : Subgroup G) ≤ c.U := by
  intro b hb
  have hbB' : b ∈ Hyp11.B1 c ⊓ Hyp11.B2 c := by
    exact hb
  have hbB1 : b ∈ Hyp11.B1 c := (Subgroup.mem_inf.mp hbB').1
  have hbB1' : b ∈ c.U ⊓ Subgroup.centralizer ({c.t1} : Set G) := by
    simpa [Hyp11.B1, centralizerIn] using hbB1
  exact (Subgroup.mem_inf.mp hbB1').1

/-- `S ∩ B = 1`. -/
private lemma S_inter_B_eq_bot_s4 (hS4 : Section4Hyp c) {x : G}
    (hxS : x ∈ (c.S : Subgroup G)) (hxB : x ∈ c.B) : x = 1 :=
  U_inter_S_eq_bot_s4 c hS4 (B_le_U c hxB) hxS

/-- Conjugation by `S` preserves `B` (because `B` centralizes `S`). -/
private lemma S_conj_mem_B (c : Hyp11 G) {s : G} (hs : s ∈ (c.S : Subgroup G))
    {b : G} (hb : b ∈ c.B) : s * b * s⁻¹ ∈ c.B := by
  have hbC : b ∈ centralizerS c := B_le_centralizerS c hb
  have hcomm : s * b = b * s :=
    (Subgroup.mem_centralizer_iff.mp hbC) s hs
  rw [hcomm]
  simpa using hb

/-- `S` normalizes `B` (because `B` centralizes `S`). -/
private lemma S_le_normalizer_B (c : Hyp11 G) :
    (c.S : Subgroup G) ≤ Subgroup.normalizer ((c.B : Subgroup G) : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · exact S_conj_mem_B c hs
  · intro hb
    have hs' : s⁻¹ ∈ (c.S : Subgroup G) := (c.S : Subgroup G).inv_mem hs
    have hb' : s⁻¹ * (s * b * s⁻¹) * (s⁻¹)⁻¹ ∈ c.B :=
      S_conj_mem_B c hs' hb
    have hEq : b = s⁻¹ * (s * b * s⁻¹) * (s⁻¹)⁻¹ := by group
    rwa [hEq]

/-- The carrier of `C_G(S)` is the product set `S · B` (with `B ≤ C_G(S)`). -/
private lemma centralizerS_eq_sup_s4 (hS4 : Section4Hyp c) :
    centralizerS c = (c.S : Subgroup G) ⊔ (c.B : Subgroup G) := by
  classical
  apply le_antisymm
  · intro c0 hc0
    have hcH : c0 ∈ c.H := centralizerS_le_H c hc0
    have hHset : (c.H : Set G) = (c.U : Set G) * ((c.S : Subgroup G) : Set G) := by
      rw [← c.H_eq_US]
      exact Subgroup.coe_mul_of_right_le_normalizer_left c.U (c.S : Subgroup G)
        (S4_S_le_normalizer_U c)
    have hc0' : c0 ∈ (c.U : Set G) * ((c.S : Subgroup G) : Set G) := by
      rw [← hHset]
      exact hcH
    rcases hc0' with ⟨u, hu, s, hs, hEq⟩
    have huC : u ∈ centralizerS c := by
      change u ∈ Subgroup.centralizer ((c.S : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hc0a : a * c0 = c0 * a :=
        (Subgroup.mem_centralizer_iff.mp hc0) a ha
      have hsa : s * a = a * s :=
        congrArg Subtype.val ((isMulCommutative_iff.mp (S_abelian_s4 c hS4))
          ⟨s, hs⟩ ⟨a, ha⟩)
      have hEq' : c0 = u * s := hEq.symm
      have hu_eq : u = c0 * s⁻¹ := by
        calc
          u = (u * s) * s⁻¹ := by group
          _ = c0 * s⁻¹ := by rw [hEq']
      calc
        a * u = a * (c0 * s⁻¹) := by rw [hu_eq]
        _ = a * c0 * s⁻¹ := by group
        _ = c0 * a * s⁻¹ := by rw [hc0a]
        _ = (c0 * s⁻¹) * a := by
          have hsa' : a * s⁻¹ = s⁻¹ * a := by
            calc
              a * s⁻¹ = s⁻¹ * (s * a) * s⁻¹ := by group
              _ = s⁻¹ * (a * s) * s⁻¹ := by rw [hsa]
              _ = s⁻¹ * a := by group
          calc
            c0 * a * s⁻¹ = c0 * (a * s⁻¹) := by group
            _ = c0 * (s⁻¹ * a) := by rw [hsa']
            _ = c0 * s⁻¹ * a := by group
        _ = u * a := by rw [hu_eq]
    have hb1 : u ∈ Hyp11.B1 c := by
      constructor
      · exact hu
      · change u ∈ Subgroup.centralizer ({c.t1} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hzt : z = c.t1 := by simpa using hz
        rw [hzt]
        exact (Subgroup.mem_centralizer_iff.mp huC) c.t1 c.t1_mem_S
    have hb2 : u ∈ Hyp11.B2 c := by
      constructor
      · exact hu
      · change u ∈ Subgroup.centralizer ({c.t2} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have hzt : z = c.t2 := by simpa using hz
        rw [hzt]
        exact (Subgroup.mem_centralizer_iff.mp huC) c.t2 c.t2_mem_S
    have huB : u ∈ c.B := by
      change u ∈ c.B1 ⊓ c.B2
      exact Subgroup.mem_inf.mpr ⟨hb1, hb2⟩
    have hcomm : s * u = u * s :=
      (Subgroup.mem_centralizer_iff.mp (B_le_centralizerS c huB)) s hs
    have hc0su : c0 = s * u := by
      calc
        c0 = u * s := hEq.symm
        _ = s * u := hcomm.symm
    have hc0sup : c0 ∈ (c.S : Subgroup G) ⊔ (c.B : Subgroup G) := by
      rw [hc0su]
      exact Subgroup.mul_mem_sup hs huB
    exact hc0sup
  · exact sup_le (S_le_centralizerS c hS4) (B_le_centralizerS c)

/-- Elements of `B` commute with elements of `S`. -/
private lemma B_comm_S (c : Hyp11 G) {s : G} (hs : s ∈ (c.S : Subgroup G))
    {b : G} (hb : b ∈ c.B) : s * b = b * s :=
  (Subgroup.mem_centralizer_iff.mp (B_le_centralizerS c hb)) s hs

/-- The multiplication map `S × B → C_G(S)`, a group isomorphism. -/
private noncomputable def centralizerS_equiv_inv (hS4 : Section4Hyp c) :
    ↥(c.S : Subgroup G) × ↥c.B ≃* ↥(centralizerS c) := by
  classical
  let f : (↥(c.S : Subgroup G) × ↥c.B) →* ↥(centralizerS c) :=
    { toFun := fun p : ↥(c.S : Subgroup G) × ↥c.B =>
        ⟨(p.1 : G) * (p.2 : G), (centralizerS c).mul_mem
          (S_le_centralizerS c hS4 p.1.2) (B_le_centralizerS c p.2.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro p q
        apply Subtype.ext
        change ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G)) =
          ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
        have hcomm : (q.1 : G) * (p.2 : G) = (p.2 : G) * (q.1 : G) :=
          B_comm_S c q.1.2 p.2.2
        calc
          ((p.1 : G) * (q.1 : G)) * ((p.2 : G) * (q.2 : G))
              = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by group
          _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by rw [hcomm]
          _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by group }
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro p q h
    have hEq := congrArg Subtype.val h
    change (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) at hEq
    have hleftS : (q.1 : G)⁻¹ * (p.1 : G) ∈ (c.S : Subgroup G) :=
      (c.S : Subgroup G).mul_mem ((c.S : Subgroup G).inv_mem q.1.2) p.1.2
    have hleftB : (q.1 : G)⁻¹ * (p.1 : G) ∈ c.B := by
      have hEq' : (q.1 : G)⁻¹ * (p.1 : G) = (q.2 : G) * (p.2 : G)⁻¹ := by
        calc
          (q.1 : G)⁻¹ * (p.1 : G)
              = (q.1 : G)⁻¹ * ((p.1 : G) * (p.2 : G)) * (p.2 : G)⁻¹ := by group
          _ = (q.1 : G)⁻¹ * ((q.1 : G) * (q.2 : G)) * (p.2 : G)⁻¹ := by rw [hEq]
          _ = (q.2 : G) * (p.2 : G)⁻¹ := by group
      rw [hEq']
      exact (c.B : Subgroup G).mul_mem q.2.2 ((c.B : Subgroup G).inv_mem p.2.2)
    have h1 : (q.1 : G)⁻¹ * (p.1 : G) = 1 :=
      S_inter_B_eq_bot_s4 c hS4 hleftS hleftB
    have hp : p.1 = q.1 := by
      apply Subtype.ext
      calc
        (p.1 : G) = (q.1 : G) * ((q.1 : G)⁻¹ * (p.1 : G)) := by group
        _ = (q.1 : G) := by rw [h1]; simp
    have h2 : (p.2 : G) * (q.2 : G)⁻¹ = 1 := by
      have hEq' : (q.1 : G)⁻¹ * (p.1 : G) = (q.2 : G) * (p.2 : G)⁻¹ := by
        calc
          (q.1 : G)⁻¹ * (p.1 : G)
              = (q.1 : G)⁻¹ * ((p.1 : G) * (p.2 : G)) * (p.2 : G)⁻¹ := by group
          _ = (q.1 : G)⁻¹ * ((q.1 : G) * (q.2 : G)) * (p.2 : G)⁻¹ := by rw [hEq]
          _ = (q.2 : G) * (p.2 : G)⁻¹ := by group
      have hq : (q.2 : G) * (p.2 : G)⁻¹ = 1 := by
        rw [← hEq']
        exact h1
      calc
        (p.2 : G) * (q.2 : G)⁻¹
            = ((q.2 : G) * (p.2 : G)⁻¹)⁻¹ := by group
        _ = (1 : G)⁻¹ := by rw [hq]
        _ = 1 := by group
    have hq : p.2 = q.2 := by
      apply Subtype.ext
      calc
        (p.2 : G) = ((p.2 : G) * (q.2 : G)⁻¹) * (q.2 : G) := by group
        _ = 1 * (q.2 : G) := by rw [h2]
        _ = (q.2 : G) := by simp
    ext
    · exact congrArg (fun z : ↥(c.S : Subgroup G) => (z : G)) hp
    · exact congrArg (fun z : ↥c.B => (z : G)) hq
  · intro x
    have hxSup : (x : G) ∈ ((((c.S : Subgroup G) ⊔ (c.B : Subgroup G)) : Subgroup G) : Set G) := by
      rw [← centralizerS_eq_sup_s4 c hS4]
      exact x.2
    have hSB : ((((c.S : Subgroup G) ⊔ (c.B : Subgroup G)) : Subgroup G) : Set G) =
        ((c.S : Subgroup G) : Set G) * ((c.B : Subgroup G) : Set G) := by
      exact Subgroup.coe_mul_of_left_le_normalizer_right (c.S : Subgroup G)
        (c.B : Subgroup G) (S_le_normalizer_B c)
    rw [hSB] at hxSup
    rcases hxSup with ⟨s, hs, b, hb, hEq⟩
    refine ⟨(⟨s, hs⟩, ⟨b, hb⟩), ?_⟩
    apply Subtype.ext
    exact hEq

/-- `C_G(S) ≃ S × B`. -/
private noncomputable def centralizerS_equiv (hS4 : Section4Hyp c) :
    ↥(centralizerS c) ≃* ↥(c.S : Subgroup G) × ↥c.B :=
  (centralizerS_equiv_inv c hS4).symm

/-- In the Section-4 case the parameter `m` with `|S| = 2·2^m` is `1`. -/
private lemma S_m_eq_one_s4 (hS4 : Section4Hyp c) : c.m = 1 := by
  have h : 2 * 2 ^ c.m = 4 := by
    have hS4' : Nat.card (↥(c.S : Subgroup G)) = 4 := hS4
    rw [← S_nat_card c, hS4']
  have hpow : 2 ^ c.m = 2 := Nat.eq_of_mul_eq_mul_left (by norm_num) h
  have hcases : c.m = 0 ∨ c.m = 1 ∨ 2 ≤ c.m := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0] at hpow
    norm_num at hpow
  · exact h1
  · have hge : 4 ≤ 2 ^ c.m := Nat.pow_le_pow_right (by norm_num : 0 < 2) h2
    omega

/-- In the Section-4 case `S` is a Klein four group. -/
private lemma S_isKleinFour_s4 (hS4 : Section4Hyp c) :
    IsKleinFour (↥(c.S : Subgroup G)) := by
  classical
  rcases c.dihedralEquiv with ⟨e0⟩
  have hm : c.m = 1 := S_m_eq_one_s4 c hS4
  have e : ↥(c.S : Subgroup G) ≃* DihedralGroup 2 := by
    rw [hm] at e0
    simpa using e0
  refine ⟨hS4, ?_⟩
  rw [Monoid.exponent_eq_of_mulEquiv e]
  exact (inferInstance : IsKleinFour (DihedralGroup 2)).exponent_two

/-- `t1 ≠ t2` in the Section-4 case. -/
private lemma t1_ne_t2_s4 (hS4 : Section4Hyp c) : c.t1 ≠ c.t2 := by
  intro h
  have hS0card : Nat.card (c.S0 : Subgroup G) = 2 := by
    have hm : c.m = 1 := S_m_eq_one_s4 c hS4
    rw [S0_nat_card c, hm]
    norm_num
  have hr1 : c.t1 * c.t2 = 1 := by
    have hsq : c.t1 * c.t1 = 1 := by simpa [pow_two] using c.t1_involution.2
    simpa [h] using hsq
  have hS0 : (c.S0 : Subgroup G) = ⊥ := by
    rw [c.S0_eq_zpowers, hr1]
    simp
  have hcard : Nat.card ((⊥ : Subgroup G) : Subgroup G) = 1 := by simp
  rw [hS0, hcard] at hS0card
  norm_num at hS0card

/-- `t ≠ t1` in the Section-4 case. -/
private lemma t_ne_t1_s4 (c : Hyp11 G) : c.t ≠ c.t1 := by
  intro h
  have ht1S0 : c.t1 ∈ c.S0 := by simpa [h] using c.t_mem_S0
  exact c.t1_not_mem_S0 ht1S0

/-- `t ≠ t2` in the Section-4 case. -/
private lemma t_ne_t2_s4 (c : Hyp11 G) : c.t ≠ c.t2 := by
  intro h
  have ht2S0 : c.t2 ∈ c.S0 := by simpa [h] using c.t_mem_S0
  exact c.t2_not_mem_S0 ht2S0

/-- In the Section-4 case `t = t1·t2` (both are the nonidentity element of
the order-two subgroup `S0 = ⟨t1·t2⟩`). -/
private lemma t_eq_t1_mul_t2_s4 (hS4 : Section4Hyp c) :
    c.t = c.t1 * c.t2 := by
  classical
  have hm : c.m = 1 := S_m_eq_one_s4 c hS4
  have hord : orderOf (c.t1 * c.t2) = 2 := by
    change orderOf (S0_generator c) = 2
    rw [S0_generator_orderOf c, hm]
    norm_num
  have htmem : c.t ∈ Subgroup.zpowers (c.t1 * c.t2) := by
    rw [← c.S0_eq_zpowers]
    exact c.t_mem_S0
  rcases (Subgroup.mem_zpowers_iff).mp htmem with ⟨k, hk⟩
  have ht1 : c.t ≠ 1 := c.t_involution.1
  have hknot2 : ¬ (2 : ℤ) ∣ k := by
    intro h2
    have hk1 : (c.t1 * c.t2) ^ k = 1 := by
      rw [zpow_eq_one_iff_modEq]
      rw [Int.modEq_zero_iff_dvd]
      simpa [hord] using h2
    exact ht1 (by rwa [← hk])
  rcases Int.even_or_odd k with heven | hodd
  · rcases heven with ⟨m, hmk⟩
    exact False.elim (hknot2 ⟨m, by omega⟩)
  · rcases hodd with ⟨m, hmk⟩
    have hmod : k ≡ 1 [ZMOD 2] := by
      rw [Int.modEq_iff_dvd]
      use -m
      omega
    have hpow : (c.t1 * c.t2) ^ k = c.t1 * c.t2 := by
      have hpow' : (c.t1 * c.t2) ^ k = (c.t1 * c.t2) ^ (1 : ℤ) := by
        rw [zpow_eq_zpow_iff_modEq (x := c.t1 * c.t2) (m := k) (n := 1)]
        simpa [hord] using hmod
      simpa using hpow'
    exact hk.symm.trans hpow

/-- For every nonidentity element `s` of `S`, some element of `N_G(S)`
conjugates `t` to `s` (single involution class plus Sylow fusion). -/
private lemma exists_normalizer_conj_t (hS4 : Section4Hyp c)
    (s : ↥(c.S : Subgroup G)) (hs1 : s ≠ 1) :
    ∃ n : G, n ∈ normalizerS c ∧ n * c.t * n⁻¹ = (s : G) := by
  classical
  have hInvG : IsInvolution (s : G) := by
    have : IsKleinFour (↥(c.S : Subgroup G)) := S_isKleinFour_s4 c hS4
    constructor
    · exact (by simpa using hs1)
    · have hsq := IsKleinFour.mul_self s
      have hsqG : (s : G) * (s : G) = 1 := congrArg Subtype.val hsq
      simpa [pow_two] using hsqG
  rcases c.one_involution_class c.t (s : G) c.t_involution hInvG with ⟨g, hg⟩
  have hn := Sylow.conj_eq_normalizer_conj_of_mem (P := c.S) (x := c.t) (g := g⁻¹)
    (_hP := S_abelian_s4 c hS4) (by exact c.S0_le_S c.t_mem_S0)
    (by
      change (g⁻¹)⁻¹ * c.t * g⁻¹ ∈ (c.S : Subgroup G)
      simp [hg])
  rcases hn with ⟨n, hnN, hEq⟩
  refine ⟨n⁻¹, (normalizerS c).inv_mem hnN, ?_⟩
  calc
    n⁻¹ * c.t * (n⁻¹)⁻¹ = n⁻¹ * c.t * n := by simp
    _ = (g⁻¹)⁻¹ * c.t * g⁻¹ := hEq.symm
    _ = g * c.t * g⁻¹ := by simp
    _ = (s : G) := hg

/-- `C_G(S) ≤ N_G(S)`. -/
private lemma centralizerS_le_normalizerS (c : Hyp11 G) :
    centralizerS c ≤ normalizerS c :=
  Subgroup.centralizer_le_normalizer ((c.S : Subgroup G) : Set G)

/-- There is an element of `N_G(S)` which does not centralize `S` (it moves
`t1` to `t2`); this uses the single involution class and Sylow fusion into
the normalizer. -/
private lemma normalizerS_has_not_mem_centralizer_s4 (hS4 : Section4Hyp c) :
    ∃ n : G, n ∈ normalizerS c ∧ n ∉ centralizerS c := by
  classical
  rcases c.one_involution_class c.t1 c.t2 c.t1_involution c.t2_involution with ⟨h, hconj⟩
  have hn := Sylow.conj_eq_normalizer_conj_of_mem (P := c.S) (x := c.t1) (g := h⁻¹)
    (_hP := S_abelian_s4 c hS4) (by exact c.t1_mem_S)
    (by
      change (h⁻¹)⁻¹ * c.t1 * h⁻¹ ∈ (c.S : Subgroup G)
      simpa [hconj] using c.t2_mem_S)
  rcases hn with ⟨n, hnN, hEq⟩
  let n' : G := n⁻¹
  refine ⟨n', (normalizerS c).inv_mem hnN, ?_⟩
  intro hC
  have hmove : n' * c.t1 * n'⁻¹ = c.t2 := by
    calc
      n' * c.t1 * n'⁻¹ = n⁻¹ * c.t1 * (n⁻¹)⁻¹ := rfl
      _ = n⁻¹ * c.t1 * n := by simp
      _ = (h⁻¹)⁻¹ * c.t1 * h⁻¹ := hEq.symm
      _ = h * c.t1 * h⁻¹ := by simp
      _ = c.t2 := hconj
  have hfix : n' * c.t1 * n'⁻¹ = c.t1 := by
    have hcomm : c.t1 * n' = n' * c.t1 :=
      (Subgroup.mem_centralizer_iff.mp hC) c.t1 c.t1_mem_S
    calc
      n' * c.t1 * n'⁻¹ = c.t1 * n' * n'⁻¹ := by rw [hcomm]
      _ = c.t1 := by group
  exact t1_ne_t2_s4 c hS4 (by rw [← hfix, hmove])

/-- `|N_G(S) : C_G(S)| = 3`: the quotient embeds into the symmetric group on
the four elements of `S`, so its order divides `24`; it is not divisible by
`2` (it divides the Sylow index), and it is not `1`. -/
private lemma normalizerS_relIndex_eq_three (hS4 : Section4Hyp c) :
    (centralizerS c).relIndex (normalizerS c) = 3 := by
  classical
  let N : Subgroup G := normalizerS c
  let C : Subgroup G := centralizerS c
  let Sg : Type u := ↥(c.S : Subgroup G)
  let φ : ↥N →* MulAut Sg := (c.S : Subgroup G).normalizerMonoidHom
  let ψ : MulAut Sg →* Equiv.Perm Sg := MulAction.toPermHom (MulAut Sg) Sg
  let θ : ↥N →* Equiv.Perm Sg := ψ.comp φ
  have hφker : φ.ker = C.subgroupOf N := by
    exact Subgroup.normalizerMonoidHom_ker (c.S : Subgroup G)
  have hψinj : Function.Injective ψ := by
    exact MulAction.toPerm_injective
  have hθker : θ.ker = C.subgroupOf N := by
    apply Subgroup.ext
    intro x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change ψ (φ x) = 1 ↔ (x : G) ∈ C
    constructor
    · intro hψ
      have hφ : φ x = 1 := hψinj (by simpa [θ] using hψ)
      have hx : x ∈ φ.ker := by rw [MonoidHom.mem_ker]; exact hφ
      exact (Subgroup.mem_subgroupOf.mp (by rwa [hφker] at hx))
    · intro hxC
      have hx : x ∈ φ.ker := by rw [hφker]; exact Subgroup.mem_subgroupOf.mpr hxC
      have hφ : φ x = 1 := (MonoidHom.mem_ker.mp hx)
      simp [hφ]
  have hindex : θ.ker.index = (centralizerS c).relIndex (normalizerS c) := by
    rw [hθker]
    rfl
  have hcardrange : θ.ker.index = Nat.card ↥θ.range := Subgroup.index_ker θ
  have hdvdPerm : Nat.card ↥θ.range ∣ Nat.card (Equiv.Perm Sg) :=
    Subgroup.card_subgroup_dvd_card θ.range
  have h24 : (centralizerS c).relIndex (normalizerS c) ∣ 24 := by
    rw [← hindex, hcardrange]
    have hperm : Nat.card (Equiv.Perm Sg) = 24 := by
      rw [Nat.card_perm]
      rw [hS4]
      norm_num
    rwa [hperm] at hdvdPerm
  have hCdivS : (centralizerS c).relIndex (normalizerS c) ∣
      (c.S : Subgroup G).index := by
    have h1 : (centralizerS c).relIndex (normalizerS c) ∣
        (c.S : Subgroup G).relIndex (normalizerS c) :=
      Subgroup.relIndex_dvd_of_le_left (normalizerS c) (S_le_centralizerS c hS4)
    have h2 : (c.S : Subgroup G).relIndex (normalizerS c) ∣
        (c.S : Subgroup G).index :=
      Subgroup.relIndex_dvd_index_of_le (Subgroup.le_normalizer)
    exact h1.trans h2
  have hCodd : ¬ 2 ∣ (centralizerS c).relIndex (normalizerS c) := by
    intro h2
    exact (c.S : Sylow 2 G).not_dvd_index (h2.trans hCdivS)
  have hne1 : (centralizerS c).relIndex (normalizerS c) ≠ 1 := by
    intro h1
    have hNleC : normalizerS c ≤ centralizerS c := (Subgroup.relIndex_eq_one).mp h1
    rcases normalizerS_has_not_mem_centralizer_s4 c hS4 with ⟨n, hnN, hnC⟩
    exact hnC (hNleC hnN)
  have hdvd3 : (centralizerS c).relIndex (normalizerS c) ∣ 3 := by
    have hcop : Nat.Coprime ((centralizerS c).relIndex (normalizerS c)) (2 ^ 3) := by
      exact ((Nat.coprime_pow_right_iff (by norm_num) _ 2).2
        (Nat.prime_two.coprime_iff_not_dvd.mpr hCodd).symm)
    have h24' : (centralizerS c).relIndex (normalizerS c) ∣ 2 ^ 3 * 3 := by
      simpa using h24
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop h24'
  have hle : (centralizerS c).relIndex (normalizerS c) ≤ 3 :=
    Nat.le_of_dvd (by norm_num) hdvd3
  have hge : 1 ≤ (centralizerS c).relIndex (normalizerS c) :=
    Nat.succ_le_of_lt (Nat.pos_of_ne_zero (by
      intro h0
      exact hne1 (by omega)))
  interval_cases (centralizerS c).relIndex (normalizerS c) <;> omega

/-- A normalizer element moving `t` to `t1` (hence not centralizing `S`). -/
private noncomputable def normalizerGen (hS4 : Section4Hyp c) : G :=
  Classical.choose (exists_normalizer_conj_t c hS4
    ⟨c.t1, c.t1_mem_S⟩ (by simpa using c.t1_involution.1))

/-- The generator lies in `N_G(S)`. -/
private lemma normalizerGen_mem (hS4 : Section4Hyp c) :
    normalizerGen c hS4 ∈ normalizerS c :=
  (Classical.choose_spec (exists_normalizer_conj_t c hS4
    ⟨c.t1, c.t1_mem_S⟩ (by simpa using c.t1_involution.1))).1

/-- The generator conjugates `t` to `t1`. -/
private lemma normalizerGen_move (hS4 : Section4Hyp c) :
    normalizerGen c hS4 * c.t * (normalizerGen c hS4)⁻¹ = c.t1 :=
  (Classical.choose_spec (exists_normalizer_conj_t c hS4
    ⟨c.t1, c.t1_mem_S⟩ (by simpa using c.t1_involution.1))).2

/-- The generator does not centralize `S`. -/
private lemma normalizerGen_not_mem_centralizer (hS4 : Section4Hyp c) :
    normalizerGen c hS4 ∉ centralizerS c := by
  intro hC
  have hfix : normalizerGen c hS4 * c.t * (normalizerGen c hS4)⁻¹ = c.t := by
    have hcomm : c.t * normalizerGen c hS4 =
        normalizerGen c hS4 * c.t :=
      (Subgroup.mem_centralizer_iff.mp hC) c.t (c.S0_le_S c.t_mem_S0)
    calc
      normalizerGen c hS4 * c.t * (normalizerGen c hS4)⁻¹
          = c.t * normalizerGen c hS4 * (normalizerGen c hS4)⁻¹ := by rw [hcomm]
      _ = c.t := by group
  exact t_ne_t1_s4 c (by rw [← hfix, normalizerGen_move c hS4])

/-- The third power of the generator lies in `C_G(S)` (the quotient
`N_G(S)/C_G(S)` has order three). -/
private lemma normalizerGen_pow_three_mem_centralizer (hS4 : Section4Hyp c) :
    (normalizerGen c hS4) ^ 3 ∈ centralizerS c := by
  classical
  have : ((centralizerS c).subgroupOf (normalizerS c)).Normal :=
    Subgroup.normal_subgroupOf_centralizer_normalizer ((c.S : Subgroup G) : Set G)
  have h := Subgroup.pow_relIndex_mem
    (H := (centralizerS c).subgroupOf (normalizerS c)) (K := ⊤)
    (g := ⟨normalizerGen c hS4, normalizerGen_mem c hS4⟩) (by trivial)
  rw [Subgroup.relIndex_top_right] at h
  have h' : (normalizerGen c hS4) ^ ((centralizerS c).relIndex (normalizerS c)) ∈
      centralizerS c := Subgroup.mem_subgroupOf.mp h
  simpa [normalizerS_relIndex_eq_three c hS4] using h'

/-- Kernel of the permutation action of `N_G(S)` on `S` is `C_G(S)`. -/
private lemma normalizer_toPerm_ker (c : Hyp11 G) :
    (MulAction.toPermHom
      (↥(Subgroup.normalizer ((c.S : Subgroup G) : Set G)))
      (↥(c.S : Subgroup G))).ker =
      (centralizerS c).subgroupOf (Subgroup.normalizer ((c.S : Subgroup G) : Set G)) := by
  classical
  apply Subgroup.ext
  intro x
  rw [MonoidHom.mem_ker, Equiv.Perm.ext_iff, Subgroup.mem_subgroupOf]
  simp [MulAction.toPermHom, MulAction.toPerm_apply]
  constructor
  · intro h
    change (x : G) ∈ Subgroup.centralizer ((c.S : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hs : (x : G) * a * (x : G)⁻¹ = a := by
      have hs' := h a ha
      have hval : ↑((x : ↥(Subgroup.normalizer ((c.S : Subgroup G) : Set G))) •
          (⟨a, ha⟩ : ↥(c.S : Subgroup G))) = a := congrArg Subtype.val hs'
      have hcoef : ↑((x : ↥(Subgroup.normalizer ((c.S : Subgroup G) : Set G))) •
          (⟨a, ha⟩ : ↥(c.S : Subgroup G))) = (x : G) * a * (x : G)⁻¹ := by rfl
      rwa [hcoef] at hval
    have hEq : (x : G) * a = a * (x : G) := by
      calc
        (x : G) * a = (x : G) * a * (x : G)⁻¹ * (x : G) := by group
        _ = a * (x : G) := by rw [hs]
    exact hEq.symm
  · intro hx s hsS
    apply Subtype.ext
    change ↑((x : ↥(Subgroup.normalizer ((c.S : Subgroup G) : Set G))) •
        (⟨s, hsS⟩ : ↥(c.S : Subgroup G))) = s
    rw [show ↑((x : ↥(Subgroup.normalizer ((c.S : Subgroup G) : Set G))) •
        (⟨s, hsS⟩ : ↥(c.S : Subgroup G))) = (x : G) * s * (x : G)⁻¹ from rfl]
    have hcomm : (s : G) * (x : G) = (x : G) * (s : G) :=
      (Subgroup.mem_centralizer_iff.mp hx) (s : G) hsS
    calc
      (x : G) * (s : G) * (x : G)⁻¹ = (s : G) * (x : G) * (x : G)⁻¹ := by rw [hcomm]
      _ = (s : G) := by group

/-- The permutation of `S` induced by the normalizer generator. -/
private noncomputable def normalizerGenPerm (hS4 : Section4Hyp c) :
    Equiv.Perm (↥(c.S : Subgroup G)) :=
  MulAction.toPerm
    (⟨normalizerGen c hS4, by simpa [normalizerS] using normalizerGen_mem c hS4⟩ :
      ↥(Subgroup.normalizer ((c.S : Subgroup G) : Set G)))

/-- The generator acts on `S` with order three. -/
private lemma normalizerGenPerm_pow_three (hS4 : Section4Hyp c) :
    (normalizerGenPerm c hS4) ^ 3 = 1 := by
  classical
  let θ := MulAction.toPermHom
    (↥(Subgroup.normalizer ((c.S : Subgroup G) : Set G)))
    (↥(c.S : Subgroup G))
  have hC : normalizerGen c hS4 ^ 3 ∈ centralizerS c :=
    normalizerGen_pow_three_mem_centralizer c hS4
  have hmem : (⟨normalizerGen c hS4, normalizerGen_mem c hS4⟩ :
        ↥(Subgroup.normalizer ((c.S : Subgroup G) : Set G))) ^ 3 ∈ θ.ker := by
    rw [normalizer_toPerm_ker c]
    exact Subgroup.mem_subgroupOf.mpr hC
  have hθ3 : θ (⟨normalizerGen c hS4, normalizerGen_mem c hS4⟩ ^ 3) = 1 :=
    MonoidHom.mem_ker.mp hmem
  simpa [normalizerGenPerm, θ] using
    (map_pow θ ⟨normalizerGen c hS4, normalizerGen_mem c hS4⟩ 3).symm.trans hθ3

/-- The generator acts nontrivially on `S`. -/
private lemma normalizerGenPerm_ne_one (hS4 : Section4Hyp c) :
    normalizerGenPerm c hS4 ≠ 1 := by
  intro h
  let θ := MulAction.toPermHom
    (↥(Subgroup.normalizer ((c.S : Subgroup G) : Set G)))
    (↥(c.S : Subgroup G))
  have hker : (⟨normalizerGen c hS4, normalizerGen_mem c hS4⟩ :
        ↥(Subgroup.normalizer ((c.S : Subgroup G) : Set G))) ∈ θ.ker := by
    rw [MonoidHom.mem_ker]
    simpa [normalizerGenPerm, θ] using h
  have hC : normalizerGen c hS4 ∈ centralizerS c := by
    rw [normalizer_toPerm_ker c] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  exact normalizerGen_not_mem_centralizer c hS4 hC

/-- `orderOf` of the generator's permutation is `3`. -/
private lemma normalizerGenPerm_order (hS4 : Section4Hyp c) :
    orderOf (normalizerGenPerm c hS4) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact orderOf_eq_prime (normalizerGenPerm_pow_three c hS4)
    (normalizerGenPerm_ne_one c hS4)

/-- The generator's permutation of `S` is a three-cycle. -/
private lemma normalizerGenPerm_isCycle (hS4 : Section4Hyp c) :
    (normalizerGenPerm c hS4).IsCycle := by
  have h1 : Nat.Prime (orderOf (normalizerGenPerm c hS4)) := by
    rw [normalizerGenPerm_order c hS4]
    exact (by decide : Nat.Prime 3)
  have h2 : Fintype.card (↥(c.S : Subgroup G)) <
      2 * orderOf (normalizerGenPerm c hS4) := by
    rw [normalizerGenPerm_order c hS4, ← Nat.card_eq_fintype_card, hS4]
    norm_num
  exact Equiv.Perm.isCycle_of_prime_order' h1 h2

/-- The generator's permutation moves every nonidentity element of `S`. -/
private lemma normalizerGenPerm_moves_nonzero (hS4 : Section4Hyp c)
    {s : ↥(c.S : Subgroup G)} (hs : s ≠ 1) :
    normalizerGenPerm c hS4 s ≠ s := by
  classical
  let σ := normalizerGenPerm c hS4
  have hcyc : σ.IsCycle := normalizerGenPerm_isCycle c hS4
  have hcard : σ.support.card = 3 := by
    rw [← hcyc.orderOf, normalizerGenPerm_order c hS4]
  have h1not : (1 : ↥(c.S : Subgroup G)) ∉ σ.support := by
    intro hmem
    have hσ1 : σ 1 = 1 := by
      simp [σ, normalizerGenPerm, MulAction.toPerm_apply]
    exact (Equiv.Perm.mem_support.mp hmem) hσ1
  have hdisj : Disjoint σ.support ({1} : Finset (↥(c.S : Subgroup G))) := by
    rw [Finset.disjoint_left]
    intro x hx hx1
    have hxeq : x = 1 := by simpa using hx1
    exact h1not (by simpa [hxeq] using hx)
  have hcardunion : (σ.support ∪ ({1} : Finset (↥(c.S : Subgroup G)))).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisj, hcard]
    norm_num
  have huniv : σ.support ∪ ({1} : Finset (↥(c.S : Subgroup G))) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcardunion, ← Nat.card_eq_fintype_card, hS4]
  have hs' : s ∈ σ.support ∪ ({1} : Finset (↥(c.S : Subgroup G))) := by
    rw [huniv]
    exact Finset.mem_univ s
  have hsnot : s ∉ ({1} : Finset (↥(c.S : Subgroup G))) := by
    simpa using hs
  exact (Equiv.Perm.mem_support.mp (Finset.mem_union.mp hs' |>.resolve_right hsnot))

/-- The `k`-th power of the generator's permutation is conjugation by
`r^k` on `S`. -/
private lemma normalizerGenPerm_pow_apply (hS4 : Section4Hyp c) (k : ℕ)
    (s : ↥(c.S : Subgroup G)) :
    (normalizerGenPerm c hS4 ^ k) s =
      ⟨normalizerGen c hS4 ^ k * (s : G) * (normalizerGen c hS4 ^ k)⁻¹,
        by
          have hpow : normalizerGen c hS4 ^ k ∈ normalizerS c :=
            (normalizerS c).pow_mem (normalizerGen_mem c hS4) k
          exact (Subgroup.mem_normalizer_iff.mp
            (by simpa [normalizerS] using hpow) (s : G)).1 s.2⟩ := by
  let g : ↥(Subgroup.normalizer ((c.S : Subgroup G) : Set G)) :=
    ⟨normalizerGen c hS4, by simpa [normalizerS] using normalizerGen_mem c hS4⟩
  have hperm : (normalizerGenPerm c hS4 ^ k) = MulAction.toPerm (g ^ k) := by
    have hg : normalizerGenPerm c hS4 =
        MulAction.toPerm (β := ↥(c.S : Subgroup G)) g := by rfl
    have hpow : (MulAction.toPerm (β := ↥(c.S : Subgroup G)) g) ^ k =
        MulAction.toPerm (β := ↥(c.S : Subgroup G)) (g ^ k) := by
      rw [← MulAction.toPermHom_apply
        (↥(Subgroup.normalizer ((c.S : Subgroup G) : Set G))) (↥(c.S : Subgroup G)) g]
      change (MulAction.toPermHom
        (↥(Subgroup.normalizer ((c.S : Subgroup G) : Set G))) (↥(c.S : Subgroup G))) g ^ k =
        (MulAction.toPermHom
          (↥(Subgroup.normalizer ((c.S : Subgroup G) : Set G))) (↥(c.S : Subgroup G))) (g ^ k)
      rw [← map_pow (MulAction.toPermHom
        (↥(Subgroup.normalizer ((c.S : Subgroup G) : Set G))) (↥(c.S : Subgroup G))) g k]
    rw [hg, hpow]
  calc
    (normalizerGenPerm c hS4 ^ k) s =
        (MulAction.toPerm (β := ↥(c.S : Subgroup G)) (g ^ k)) s := by rw [hperm]
    _ = (g ^ k) • s := by rw [MulAction.toPerm_apply]
    _ = ⟨normalizerGen c hS4 ^ k * (s : G) * (normalizerGen c hS4 ^ k)⁻¹, by
          have hpow : normalizerGen c hS4 ^ k ∈ normalizerS c :=
            (normalizerS c).pow_mem (normalizerGen_mem c hS4) k
          exact (Subgroup.mem_normalizer_iff.mp
            (by simpa [normalizerS] using hpow) (s : G)).1 s.2⟩ := by
          rfl

/-- The generator's permutation powers for `k = 1, 2` move `t`. -/
private lemma normalizerGenPerm_pow_moves_t (hS4 : Section4Hyp c) (k : ℕ)
    (hk : k = 1 ∨ k = 2) :
    (normalizerGenPerm c hS4 ^ k) ⟨c.t, c.S0_le_S c.t_mem_S0⟩ ≠
      ⟨c.t, c.S0_le_S c.t_mem_S0⟩ := by
  have hcp : Nat.Coprime k (orderOf (normalizerGenPerm c hS4)) := by
    rcases hk with rfl | rfl
    · rw [normalizerGenPerm_order c hS4]
      norm_num
    · rw [normalizerGenPerm_order c hS4]
      norm_num
  have hsup := Equiv.Perm.support_pow_coprime (σ := normalizerGenPerm c hS4) hcp
  have ht : ⟨c.t, c.S0_le_S c.t_mem_S0⟩ ∈ (normalizerGenPerm c hS4).support := by
    exact Equiv.Perm.mem_support.mpr (normalizerGenPerm_moves_nonzero c hS4
      (by simpa using c.t_involution.1))
  have ht' : ⟨c.t, c.S0_le_S c.t_mem_S0⟩ ∈
      (normalizerGenPerm c hS4 ^ k).support := by
    rw [hsup]
    exact ht
  exact Equiv.Perm.mem_support.mp ht'

/-- `r^k·t·r⁻ᵏ ≠ t` for `k = 1, 2`. -/
private lemma normalizerGen_pow_t_ne (hS4 : Section4Hyp c) (k : ℕ)
    (hk : k = 1 ∨ k = 2) :
    normalizerGen c hS4 ^ k * c.t * (normalizerGen c hS4 ^ k)⁻¹ ≠ c.t := by
  intro h
  have hσ := normalizerGenPerm_pow_moves_t c hS4 k hk
  have hσ' : (normalizerGenPerm c hS4 ^ k) ⟨c.t, c.S0_le_S c.t_mem_S0⟩ =
      ⟨c.t, c.S0_le_S c.t_mem_S0⟩ := by
    rw [normalizerGenPerm_pow_apply c hS4 k ⟨c.t, c.S0_le_S c.t_mem_S0⟩]
    apply Subtype.ext
    exact h
  exact hσ hσ'

/-- The three images `rᵏ·t·r⁻ᵏ` (`k = 0,1,2`) are pairwise distinct. -/
private lemma normalizerGen_images_distinct (hS4 : Section4Hyp c) (i j : Fin 3)
    (hij : i ≠ j) :
    normalizerGen c hS4 ^ i.1 * c.t * (normalizerGen c hS4 ^ i.1)⁻¹ ≠
      normalizerGen c hS4 ^ j.1 * c.t * (normalizerGen c hS4 ^ j.1)⁻¹ := by
  intro h
  fin_cases i <;> fin_cases j <;> simp at h hij ⊢
  all_goals
    exfalso
    first
    | simpa using (normalizerGen_pow_t_ne c hS4 1 (Or.inl rfl) h)
    | simpa using (normalizerGen_pow_t_ne c hS4 2 (Or.inr rfl) h)
    | simpa using (normalizerGen_pow_t_ne c hS4 1 (Or.inl rfl) h.symm)
    | simpa using (normalizerGen_pow_t_ne c hS4 2 (Or.inr rfl) h.symm)
    | exact (t_ne_t1_s4 c h)
    | exact (t_ne_t1_s4 c h.symm)
    | exact (t_ne_t1_s4 c (by
        have h' : normalizerGen c hS4 * c.t * (normalizerGen c hS4)⁻¹ = c.t := h.symm
        rw [normalizerGen_move c hS4] at h'
        exact h'.symm))
    | exact (t_ne_t1_s4 c (by
        have h' : normalizerGen c hS4 * c.t * (normalizerGen c hS4)⁻¹ = c.t := h
        rw [normalizerGen_move c hS4] at h'
        exact h'.symm))
    | exact (t_ne_t1_s4 c (by
        have h' : c.t =
            normalizerGen c hS4 * c.t * (normalizerGen c hS4)⁻¹ := by
          calc
            c.t = (normalizerGen c hS4)⁻¹ *
                (normalizerGen c hS4 * c.t * (normalizerGen c hS4)⁻¹) *
                normalizerGen c hS4 := by group
            _ = (normalizerGen c hS4)⁻¹ *
                (normalizerGen c hS4 ^ 2 * c.t * (normalizerGen c hS4 ^ 2)⁻¹) *
                normalizerGen c hS4 := by rw [h]
            _ = normalizerGen c hS4 * c.t * (normalizerGen c hS4)⁻¹ := by group
        rw [normalizerGen_move c hS4] at h'
        exact h'))
/-- The three nonidentity elements of `S`, as a subtype, are indexed by
`Fin 3` via the powers of the normalizer generator. -/
private noncomputable def S_nonzero_enum (hS4 : Section4Hyp c) :
    {s : ↥(c.S : Subgroup G) // s ≠ 1} ≃ Fin 3 := by
  classical
  let r : G := normalizerGen c hS4
  let f : Fin 3 → {s : ↥(c.S : Subgroup G) // s ≠ 1} := fun i =>
    ⟨⟨r ^ i.1 * c.t * (r ^ i.1)⁻¹, by
        have hpow : r ^ i.1 ∈ normalizerS c :=
          (normalizerS c).pow_mem (normalizerGen_mem c hS4) i.1
        exact ((Subgroup.mem_normalizer_iff.mp
          (by simpa [normalizerS] using hpow)) c.t).1 (c.S0_le_S c.t_mem_S0)⟩,
      by
        intro h1
        have hval : r ^ i.1 * c.t * (r ^ i.1)⁻¹ = 1 := congrArg Subtype.val h1
        have ht : c.t = 1 := by
          calc
            c.t = (r ^ i.1)⁻¹ * (r ^ i.1 * c.t * (r ^ i.1)⁻¹) * r ^ i.1 := by group
            _ = 1 := by rw [hval]; simp
        exact c.t_involution.1 ht⟩
  refine (Equiv.ofBijective f ?_).symm
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j h
    by_cases hij : i = j
    · subst hij
      rfl
    · have hval : (f i : ↥(c.S : Subgroup G)) = (f j : ↥(c.S : Subgroup G)) :=
        congrArg Subtype.val h
      have hEq : r ^ i.1 * c.t * (r ^ i.1)⁻¹ =
          r ^ j.1 * c.t * (r ^ j.1)⁻¹ := by
        simpa [f] using congrArg Subtype.val hval
      exact False.elim (normalizerGen_images_distinct c hS4 i j hij hEq)
  · have hS4' : Fintype.card (↥(c.S : Subgroup G)) = 4 := by
      rw [← Nat.card_eq_fintype_card]
      exact hS4
    have hc1 : Fintype.card {x : ↥(c.S : Subgroup G) // x = 1} = 1 :=
      Fintype.card_subtype_eq 1
    have hc : Fintype.card {s : ↥(c.S : Subgroup G) // s ≠ 1} = 3 := by
      rw [Fintype.card_subtype_compl (p := fun x : ↥(c.S : Subgroup G) => x = 1)]
      rw [hc1, hS4']
    simpa using hc.symm

/-- The set `S` is the disjoint union of `{1}` and the three nonidentity
elements indexed by `Fin 3`. -/
private noncomputable def S_equiv_option (hS4 : Section4Hyp c) :
    Option (Fin 3) ≃ ↥(c.S : Subgroup G) := by
  classical
  refine Equiv.ofBijective
    (fun o : Option (Fin 3) =>
      o.elim 1 (fun i => ((S_nonzero_enum c hS4).symm i).1)) ?_
  constructor
  · intro o p h
    cases o with
    | none =>
      cases p with
      | none => rfl
      | some i =>
        exfalso
        exact ((S_nonzero_enum c hS4).symm i).2 (by simpa using h.symm)
    | some i =>
      cases p with
      | none =>
        exfalso
        exact ((S_nonzero_enum c hS4).symm i).2 (by simpa using h)
      | some j =>
        have h' : ((S_nonzero_enum c hS4).symm i).1 =
            ((S_nonzero_enum c hS4).symm j).1 := by
          simpa using congrArg Subtype.val h
        exact congrArg some ((S_nonzero_enum c hS4).symm.injective (Subtype.ext h'))
  · intro s
    by_cases hs : s = 1
    · exact ⟨none, by simp [hs]⟩
    · refine ⟨some ((S_nonzero_enum c hS4) ⟨s, hs⟩), ?_⟩
      apply Subtype.ext
      simp

/-- A set of three coset representatives of `C_G(S)` in `N_G(S)`: the three
powers of the normalizer generator. -/
private noncomputable def normalizerReps (hS4 : Section4Hyp c) (i : Fin 3) : G :=
  normalizerGen c hS4 ^ i.1

/-- Each chosen representative lies in `N_G(S)`. -/
private lemma normalizerReps_mem (hS4 : Section4Hyp c) (i : Fin 3) :
    normalizerReps c hS4 i ∈ normalizerS c :=
  (normalizerS c).pow_mem (normalizerGen_mem c hS4) i.1

/-- The chosen representative conjugates `t` to the corresponding nonidentity
element of `S`. -/
private lemma normalizerReps_conj_t (hS4 : Section4Hyp c) (i : Fin 3) :
    normalizerReps c hS4 i * c.t * (normalizerReps c hS4 i)⁻¹ =
      ((S_nonzero_enum c hS4).symm i : ↥(c.S : Subgroup G)) := by
  let f : Fin 3 → {s : ↥(c.S : Subgroup G) // s ≠ 1} := fun j =>
    ⟨⟨normalizerGen c hS4 ^ j.1 * c.t * (normalizerGen c hS4 ^ j.1)⁻¹, by
        have hpow : normalizerGen c hS4 ^ j.1 ∈ normalizerS c :=
          (normalizerS c).pow_mem (normalizerGen_mem c hS4) j.1
        exact ((Subgroup.mem_normalizer_iff.mp
          (by simpa [normalizerS] using hpow)) c.t).1 (c.S0_le_S c.t_mem_S0)⟩,
      by
        intro h1
        have hval : normalizerGen c hS4 ^ j.1 * c.t * (normalizerGen c hS4 ^ j.1)⁻¹ = 1 :=
          congrArg Subtype.val h1
        have ht : c.t = 1 := by
          calc
            c.t = (normalizerGen c hS4 ^ j.1)⁻¹ *
                (normalizerGen c hS4 ^ j.1 * c.t * (normalizerGen c hS4 ^ j.1)⁻¹) *
                normalizerGen c hS4 ^ j.1 := by group
            _ = 1 := by rw [hval]; simp
        exact c.t_involution.1 ht⟩
  have hleft : (S_nonzero_enum c hS4) (f i) = i := by
    simp [S_nonzero_enum, f]
  have hsymm : (S_nonzero_enum c hS4).symm i = f i := by
    exact (Equiv.symm_apply_eq (S_nonzero_enum c hS4)).mpr hleft.symm
  rw [hsymm]
  rfl

/-- The inverse of each chosen representative also lies in `N_G(S)`. -/
private lemma normalizerReps_inv_mem (hS4 : Section4Hyp c) (i : Fin 3) :
    (normalizerReps c hS4 i)⁻¹ ∈ normalizerS c :=
  (normalizerS c).inv_mem (normalizerReps_mem c hS4 i)

/-- `C_G(S)` is normal in `N_G(S)` (as a subgroup of `N_G(S)`). -/
private instance centralizerS_subgroupOf_normalizerS_normal (c : Hyp11 G) :
    ((centralizerS c).subgroupOf (normalizerS c)).Normal := by
  change ((Subgroup.centralizer ((c.S : Subgroup G) : Set G)).subgroupOf
    (Subgroup.normalizer ((c.S : Subgroup G) : Set G))).Normal
  infer_instance

/-- The three inverse representatives give three distinct cosets of
`C_G(S)` in `N_G(S)`. -/
private lemma normalizerReps_coset_injective (hS4 : Section4Hyp c) :
    Function.Injective (fun i : Fin 3 =>
      QuotientGroup.mk' ((centralizerS c).subgroupOf (normalizerS c))
        ⟨(normalizerReps c hS4 i)⁻¹, normalizerReps_inv_mem c hS4 i⟩) := by
  classical
  intro i j hij
  have hq : (⟨(normalizerReps c hS4 i)⁻¹, normalizerReps_inv_mem c hS4 i⟩ :
      ↥(normalizerS c))⁻¹ *
      ⟨(normalizerReps c hS4 j)⁻¹, normalizerReps_inv_mem c hS4 j⟩ ∈
      (centralizerS c).subgroupOf (normalizerS c) :=
    (QuotientGroup.eq.mp hij)
  have hC : normalizerReps c hS4 i * (normalizerReps c hS4 j)⁻¹ ∈ centralizerS c := by
    simpa using (Subgroup.mem_subgroupOf.mp hq)
  let sj : G := normalizerReps c hS4 j * c.t * (normalizerReps c hS4 j)⁻¹
  have hsjS : sj ∈ (c.S : Subgroup G) := by
    have hval : sj = ((S_nonzero_enum c hS4).symm j : ↥(c.S : Subgroup G)) :=
      normalizerReps_conj_t c hS4 j
    rw [hval]
    exact ((S_nonzero_enum c hS4).symm j).1.2
  have hCs : (normalizerReps c hS4 i * (normalizerReps c hS4 j)⁻¹) * sj =
      sj * (normalizerReps c hS4 i * (normalizerReps c hS4 j)⁻¹) :=
    ((Subgroup.mem_centralizer_iff.mp hC) sj hsjS).symm
  have h1 : normalizerReps c hS4 i * c.t * (normalizerReps c hS4 j)⁻¹ =
      normalizerReps c hS4 j * c.t * (normalizerReps c hS4 j)⁻¹ *
        normalizerReps c hS4 i * (normalizerReps c hS4 j)⁻¹ := by
    calc
      normalizerReps c hS4 i * c.t * (normalizerReps c hS4 j)⁻¹
          = (normalizerReps c hS4 i * (normalizerReps c hS4 j)⁻¹) *
              (normalizerReps c hS4 j * c.t * (normalizerReps c hS4 j)⁻¹) := by
              group
      _ = (normalizerReps c hS4 j * c.t * (normalizerReps c hS4 j)⁻¹) *
              (normalizerReps c hS4 i * (normalizerReps c hS4 j)⁻¹) := hCs
      _ = normalizerReps c hS4 j * c.t * (normalizerReps c hS4 j)⁻¹ *
              normalizerReps c hS4 i * (normalizerReps c hS4 j)⁻¹ := by
              group
  have h2 : c.t = (normalizerReps c hS4 i)⁻¹ *
      (normalizerReps c hS4 j * c.t * (normalizerReps c hS4 j)⁻¹) *
      normalizerReps c hS4 i := by
    calc
      c.t = (normalizerReps c hS4 i)⁻¹ *
          (normalizerReps c hS4 i * c.t * (normalizerReps c hS4 j)⁻¹) *
          normalizerReps c hS4 j := by group
      _ = (normalizerReps c hS4 i)⁻¹ *
          (normalizerReps c hS4 j * c.t * (normalizerReps c hS4 j)⁻¹ *
            normalizerReps c hS4 i * (normalizerReps c hS4 j)⁻¹) *
          normalizerReps c hS4 j := by rw [h1]
      _ = (normalizerReps c hS4 i)⁻¹ *
          (normalizerReps c hS4 j * c.t * (normalizerReps c hS4 j)⁻¹) *
          normalizerReps c hS4 i := by group
  have ht : normalizerReps c hS4 i * c.t * (normalizerReps c hS4 i)⁻¹ =
      normalizerReps c hS4 j * c.t * (normalizerReps c hS4 j)⁻¹ := by
    calc
      normalizerReps c hS4 i * c.t * (normalizerReps c hS4 i)⁻¹
          = normalizerReps c hS4 i *
              ((normalizerReps c hS4 i)⁻¹ *
                (normalizerReps c hS4 j * c.t * (normalizerReps c hS4 j)⁻¹) *
                normalizerReps c hS4 i) *
              (normalizerReps c hS4 i)⁻¹ :=
              congrArg (fun x : G => normalizerReps c hS4 i * x * (normalizerReps c hS4 i)⁻¹) h2
      _ = normalizerReps c hS4 j * c.t * (normalizerReps c hS4 j)⁻¹ := by group
  by_contra hijne
  exact normalizerGen_images_distinct c hS4 i j hijne ht

/-- The three inverse representatives form a transversal of `C_G(S)` in
`N_G(S)`: every normalizer element is `rᵢ⁻¹` times a centralizer element. -/
private lemma exists_normalizer_decomp (hS4 : Section4Hyp c) {g : G}
    (hg : g ∈ normalizerS c) :
    ∃ i : Fin 3, ∃ c0 : G, c0 ∈ centralizerS c ∧
      g = (normalizerReps c hS4 i)⁻¹ * c0 := by
  classical
  let N : Subgroup G := normalizerS c
  let K : Subgroup (↥N) := (centralizerS c).subgroupOf N
  let f : Fin 3 → ↥N ⧸ K := fun i =>
    QuotientGroup.mk' K ⟨(normalizerReps c hS4 i)⁻¹, normalizerReps_inv_mem c hS4 i⟩
  have hinj : Function.Injective f := by
    simpa [f, K] using (normalizerReps_coset_injective c hS4)
  have hrel : K.index = 3 := by
    change (centralizerS c).relIndex (normalizerS c) = 3
    exact normalizerS_relIndex_eq_three c hS4
  have hcard : Fintype.card (↥N ⧸ K) = 3 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index, hrel]
  have hcard' : Fintype.card (Fin 3) = Fintype.card (↥N ⧸ K) := by
    rw [hcard]
    norm_num
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard'⟩
  have hsurj : Function.Surjective f := hbij.2
  rcases hsurj (⟨g, hg⟩ : ↥N) with ⟨i, hi⟩
  have hq : (⟨(normalizerReps c hS4 i)⁻¹, normalizerReps_inv_mem c hS4 i⟩ :
      ↥N)⁻¹ * ⟨g, hg⟩ ∈ K := (QuotientGroup.eq.mp hi)
  have hC : normalizerReps c hS4 i * g ∈ centralizerS c := by
    simpa [K] using (Subgroup.mem_subgroupOf.mp hq)
  refine ⟨i, normalizerReps c hS4 i * g, hC, ?_⟩
  group

/-- The character value `ν` transported to `B` by the inverse of a normalizer
representative: `b ↦ ν((rᵢ)⁻¹·b·rᵢ)`. -/
private noncomputable def nuRepB (c : Hyp11 G) (_h12 : Hyp12 c)
    (hS4 : Section4Hyp c) (ν : Irr (↥c.H0)) (i : Fin 3) :
    ClassFunction (↥c.B) :=
  fun b => ν.1 ⟨(normalizerReps c hS4 i)⁻¹ * (b : G) * normalizerReps c hS4 i,
    U_le_H0 c (B_le_U c (by
      simpa using (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 i) b)))⟩

/-- Evaluation of a normalizer conjugate of an irreducible character of `B`. -/
private lemma conjIrrB_apply (c : Hyp11 G) {g : G}
    (hg : ∀ b : ↥c.B, g * (b : G) * g⁻¹ ∈ c.B) (β : Irr (↥c.B)) (b : ↥c.B) :
    (conjIrrB c hg β).1 b = β.1 ⟨g * (b : G) * g⁻¹, hg b⟩ := rfl

/-- Conjugation by equal elements is the same map on `Irr(B)`. -/
private lemma conjIrrB_congr (c : Hyp11 G) {g h : G} (hgh : g = h)
    (hg : ∀ b : ↥c.B, g * (b : G) * g⁻¹ ∈ c.B)
    (hh : ∀ b : ↥c.B, h * (b : G) * h⁻¹ ∈ c.B) (β : Irr (↥c.B)) :
    conjIrrB c hg β = conjIrrB c hh β := by
  apply Subtype.ext
  funext b
  apply congrArg β.1
  apply Subtype.ext
  change g * (b : G) * g⁻¹ = h * (b : G) * h⁻¹
  rw [hgh]

/-- Conjugation by a fixed normalizer element is injective on `Irr(B)`. -/
private lemma conjIrrB_injective (c : Hyp11 G) {g : G}
    (hg : g ∈ normalizerS c) :
    Function.Injective (fun β : Irr (↥c.B) =>
      conjIrrB c (B_conj_mem_of_normalizerS c hg) β) := by
  intro β β' h
  apply Subtype.ext
  funext b
  have hEq := congrFun (congrArg Subtype.val h)
    ⟨g⁻¹ * (b : G) * g, by
      simpa using (B_conj_mem_of_normalizerS c ((normalizerS c).inv_mem hg) b)⟩
  have hEq' : β.1 ⟨g * (g⁻¹ * (b : G) * g) * g⁻¹, by
      simpa using (B_conj_mem_of_normalizerS c hg
        ⟨g⁻¹ * (b : G) * g, by
          simpa using (B_conj_mem_of_normalizerS c ((normalizerS c).inv_mem hg) b)⟩)⟩ =
      β'.1 ⟨g * (g⁻¹ * (b : G) * g) * g⁻¹, by
      simpa using (B_conj_mem_of_normalizerS c hg
        ⟨g⁻¹ * (b : G) * g, by
          simpa using (B_conj_mem_of_normalizerS c ((normalizerS c).inv_mem hg) b)⟩)⟩ := by
    simpa [conjIrrB_apply] using hEq
  have hCarrier : g * (g⁻¹ * (b : G) * g) * g⁻¹ = (b : G) := by group
  simpa [hCarrier] using hEq'

/-- Conjugation by a product of normalizer elements composes. -/
private lemma conjIrrB_mul (c : Hyp11 G) {g h : G}
    (hg : g ∈ normalizerS c) (hh : h ∈ normalizerS c) (β : Irr (↥c.B)) :
    conjIrrB c (B_conj_mem_of_normalizerS c ((normalizerS c).mul_mem hg hh)) β =
      conjIrrB c (B_conj_mem_of_normalizerS c hh)
        (conjIrrB c (B_conj_mem_of_normalizerS c hg) β) := by
  apply Subtype.ext
  funext b
  simp [conjIrrB_apply]
  group

/-- Elements of `C_G(S)` act trivially on irreducible characters of `B`. -/
private lemma conjIrrB_mem_centralizerS_eq_self (hS4 : Section4Hyp c) {g : G}
    (hg : g ∈ centralizerS c) (β : Irr (↥c.B)) :
    conjIrrB c (B_conj_mem_of_normalizerS c (centralizerS_le_normalizerS c hg)) β = β := by
  apply Subtype.ext
  funext b
  simp [conjIrrB_apply]
  let gC : ↥(centralizerS c) := ⟨g, hg⟩
  let p : ↥(c.S : Subgroup G) × ↥c.B := (centralizerS_equiv_inv c hS4).symm gC
  let s : ↥(c.S : Subgroup G) := p.1
  let b0 : ↥c.B := p.2
  have hEq : (s : G) * (b0 : G) = (g : G) := by
    have hp := (centralizerS_equiv_inv c hS4).apply_symm_apply gC
    exact congrArg Subtype.val hp
  have hconv : g * (b : G) * g⁻¹ = b0 * (b : G) * b0⁻¹ := by
    have hsb : s * (b : G) = (b : G) * s := B_comm_S c s.2 b.2
    have hsb0 : s * (b0 : G) = (b0 : G) * s := B_comm_S c s.2 b0.2
    calc
      g * (b : G) * g⁻¹ =
          ((s : G) * (b0 : G)) * (b : G) * ((s : G) * (b0 : G))⁻¹ := by rw [hEq]
      _ = (b0 : G) * (b : G) * (b0 : G)⁻¹ := by
        have hsall : (s : G) * ((b0 : G) * (b : G) * (b0 : G)⁻¹) =
            ((b0 : G) * (b : G) * (b0 : G)⁻¹) * (s : G) := by
          calc
            (s : G) * ((b0 : G) * (b : G) * (b0 : G)⁻¹)
                = ((s : G) * (b0 : G)) * (b : G) * (b0 : G)⁻¹ := by group
            _ = ((b0 : G) * (s : G)) * (b : G) * (b0 : G)⁻¹ := by rw [hsb0]
            _ = (b0 : G) * ((s : G) * (b : G)) * (b0 : G)⁻¹ := by group
            _ = (b0 : G) * ((b : G) * (s : G)) * (b0 : G)⁻¹ := by rw [hsb]
            _ = ((b0 : G) * (b : G) * (b0 : G)⁻¹) * (s : G) := by
              have hsb0' : (b0 : G) * (s : G) = (s : G) * (b0 : G) := hsb0.symm
              have hsb0_inv : (s : G) * (b0 : G)⁻¹ = (b0 : G)⁻¹ * (s : G) := by
                calc
                  (s : G) * (b0 : G)⁻¹
                      = ((b0 : G)⁻¹ * (b0 : G)) * (s : G) * (b0 : G)⁻¹ := by group
                  _ = (b0 : G)⁻¹ * ((b0 : G) * (s : G)) * (b0 : G)⁻¹ := by group
                  _ = (b0 : G)⁻¹ * ((s : G) * (b0 : G)) * (b0 : G)⁻¹ := by rw [hsb0']
                  _ = (b0 : G)⁻¹ * (s : G) := by group
              calc
                (b0 : G) * ((b : G) * (s : G)) * (b0 : G)⁻¹
                    = ((b0 : G) * (b : G)) * (s : G) * (b0 : G)⁻¹ := by group
                _ = ((b0 : G) * (b : G)) * ((s : G) * (b0 : G)⁻¹) := by group
                _ = ((b0 : G) * (b : G)) * ((b0 : G)⁻¹ * (s : G)) := by rw [hsb0_inv]
                _ = ((b0 : G) * (b : G) * (b0 : G)⁻¹) * (s : G) := by group
        calc
          ((s : G) * (b0 : G)) * (b : G) * ((s : G) * (b0 : G))⁻¹
              = (s : G) * ((b0 : G) * (b : G) * (b0 : G)⁻¹) * (s : G)⁻¹ := by group
          _ = ((b0 : G) * (b : G) * (b0 : G)⁻¹) * (s : G) * (s : G)⁻¹ := by rw [hsall]
          _ = (b0 : G) * (b : G) * (b0 : G)⁻¹ := by group
  have hβ : β.1 ⟨b0 * (b : G) * b0⁻¹, B_conj_mem_of_normalizerS c
      (by
        exact (centralizerS_le_normalizerS c (B_le_centralizerS c b0.2))) b⟩ =
      β.1 b := by
    have hcf := irreducibleCharacter_isClassFunction β.2 b b0
    change β.1 ((b0 : ↥c.B) * b * (b0 : ↥c.B)⁻¹) = β.1 b
    exact hcf
  simpa [hconv] using hβ

/-- Conjugation by an element preserving `B`, as a group automorphism of `B`. -/
private noncomputable def conjBEquiv (c : Hyp11 G) {g : G}
    (hg : ∀ b : ↥c.B, g * (b : G) * g⁻¹ ∈ c.B) : ↥c.B ≃* ↥c.B := by
  classical
  let f : ↥c.B →* ↥c.B :=
    { toFun := fun b : ↥c.B => ⟨g * (b : G) * g⁻¹, hg b⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        change g * ((a : G) * (b : G)) * g⁻¹ =
          (g * (a : G) * g⁻¹) * (g * (b : G) * g⁻¹)
        group }
  have hinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    calc
      (a : G) = g⁻¹ * (g * (a : G) * g⁻¹) * g := by group
      _ = g⁻¹ * (g * (b : G) * g⁻¹) * g := by simpa [f] using h'
      _ = (b : G) := by group
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, rfl⟩
  exact MulEquiv.ofBijective f hbij

/-- `ν` restricted to `B`, then conjugated by a normalizer representative, is
a character of `B`. -/
private theorem nuRepB_isCharacter (c : Hyp11 G) (h12 : Hyp12 c)
    (hS4 : Section4Hyp c) (ν : Irr (↥c.H0)) (i : Fin 3) :
    IsCharacter (nuRepB c h12 hS4 ν i) := by
  classical
  let base : ClassFunction (↥c.B) := fun b => ν.1 ⟨(b : G), U_le_H0 c (B_le_U c b.2)⟩
  have hbase : IsCharacter base := by
    let eB : ↥(c.B.subgroupOf c.H0) ≃* ↥c.B :=
      Subgroup.subgroupOfEquivOfLe (show c.B ≤ c.H0 from fun b hb => U_le_H0 c (B_le_U c hb))
    have hres : IsCharacter (fun x : ↥(c.B.subgroupOf c.H0) => ν.1 (x : ↥c.H0)) :=
      isCharacter_restrict (H := c.B.subgroupOf c.H0) (χ := ν.1)
        (isCharacter_of_isIrreducibleCharacter ν.2)
    exact isCharacter_congr eB.symm hres
  let eB : ↥c.B ≃* ↥c.B := conjBEquiv c
    (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 i))
  have hchar : IsCharacter (fun b : ↥c.B => base (eB b)) := isCharacter_congr eB hbase
  convert hchar using 1
  funext b
  dsimp [nuRepB, base, eB, conjBEquiv]
  apply congrArg ν.1
  apply Subtype.ext
  simp [inv_inv]

/-- The normalizer conjugate of `ν̂` corresponding to the `i`-th
representative. -/
private noncomputable def conjNuHatB (c : Hyp11 G) (h12 : Hyp12 c)
    (hS4 : Section4Hyp c) (ν : Irr (↥c.H0)) (i : Fin 3) : Irr (↥c.B) :=
  conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 i))
    (nuHat c h12 ν)

/-- `ν((rᵢ)⁻¹·b·rᵢ)` is congruent to the corresponding conjugate of `ν̂`
modulo two. -/
private lemma nuRepB_congr (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {ν : Irr (↥c.H0)} (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1) (i : Fin 3) (b : ↥c.B) :
    CongruentModTwo (nuRepB c h12 hS4 ν i b)
      ((conjNuHatB c h12 hS4 ν i).1 b) := by
  let b' : ↥c.B := ⟨(normalizerReps c hS4 i)⁻¹ * (b : G) * normalizerReps c hS4 i,
    by simpa [inv_inv] using
      (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 i) b)⟩
  have hmem : (b' : G) ∈ c.H0 := U_le_H0 c (B_le_U c b'.2)
  have hc := nuHat_congruence c h12 hSC hS4 hνs hνt b' hmem
  simpa [conjNuHatB, conjIrrB_apply, nuRepB, b'] using hc.symm

/-- The zeroth normalizer conjugate is `ν̂` itself. -/
private lemma conjNuHatB_zero (h12 : Hyp12 c) (hS4 : Section4Hyp c) (ν : Irr (↥c.H0)) :
    conjNuHatB c h12 hS4 ν 0 = nuHat c h12 ν := by
  apply Subtype.ext
  funext b
  apply congrArg (nuHat c h12 ν).1
  apply Subtype.ext
  simp [normalizerReps]

/-- Squaring the first normalizer conjugate gives the second. -/
private lemma conjNuHatB_one_sq (h12 : Hyp12 c) (hS4 : Section4Hyp c) (ν : Irr (↥c.H0)) :
    conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1))
      (conjNuHatB c h12 hS4 ν 1) = conjNuHatB c h12 hS4 ν 2 := by
  let hmem2 : ∀ b : ↥c.B, (normalizerReps c hS4 1)⁻¹ * (normalizerReps c hS4 1)⁻¹ *
      (b : G) * ((normalizerReps c hS4 1)⁻¹ * (normalizerReps c hS4 1)⁻¹)⁻¹ ∈ c.B :=
    B_conj_mem_of_normalizerS c ((normalizerS c).mul_mem
      (normalizerReps_inv_mem c hS4 1) (normalizerReps_inv_mem c hS4 1))
  have hmul := conjIrrB_mul c
    (hg := normalizerReps_inv_mem c hS4 1)
    (hh := normalizerReps_inv_mem c hS4 1)
    (nuHat c h12 ν)
  have hEq : conjIrrB c hmem2 (nuHat c h12 ν) = conjNuHatB c h12 hS4 ν 2 := by
    apply Subtype.ext
    funext b
    apply congrArg (nuHat c h12 ν).1
    apply Subtype.ext
    change (normalizerReps c hS4 1)⁻¹ * (normalizerReps c hS4 1)⁻¹ * (b : G) *
        ((normalizerReps c hS4 1)⁻¹ * (normalizerReps c hS4 1)⁻¹)⁻¹ =
      (normalizerReps c hS4 2)⁻¹ * (b : G) * ((normalizerReps c hS4 2)⁻¹)⁻¹
    simp only [normalizerReps]
    change (normalizerGen c hS4 ^ 1)⁻¹ * (normalizerGen c hS4 ^ 1)⁻¹ * (b : G) *
        ((normalizerGen c hS4 ^ 1)⁻¹ * (normalizerGen c hS4 ^ 1)⁻¹)⁻¹ =
      (normalizerGen c hS4 ^ 2)⁻¹ * (b : G) * ((normalizerGen c hS4 ^ 2)⁻¹)⁻¹
    rw [pow_two, mul_inv_rev, inv_inv]
    norm_num
  have hLeft : conjIrrB c hmem2 (nuHat c h12 ν) =
      conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1))
        (conjNuHatB c h12 hS4 ν 1) := by
    simpa [hmem2, conjNuHatB] using hmul
  exact hLeft.symm.trans hEq

/-- The third power of the first normalizer conjugate is trivial. -/
private lemma conjNuHatB_one_cube (h12 : Hyp12 c) (hS4 : Section4Hyp c) (ν : Irr (↥c.H0)) :
    conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1))
      (conjNuHatB c h12 hS4 ν 2) = nuHat c h12 ν := by
  let hmem3 : ∀ b : ↥c.B, (normalizerReps c hS4 2)⁻¹ * (normalizerReps c hS4 1)⁻¹ *
      (b : G) * ((normalizerReps c hS4 2)⁻¹ * (normalizerReps c hS4 1)⁻¹)⁻¹ ∈ c.B :=
    B_conj_mem_of_normalizerS c ((normalizerS c).mul_mem
      (normalizerReps_inv_mem c hS4 2) (normalizerReps_inv_mem c hS4 1))
  have hmul := conjIrrB_mul c
    (hg := normalizerReps_inv_mem c hS4 2)
    (hh := normalizerReps_inv_mem c hS4 1)
    (nuHat c h12 ν)
  have hmemC : (normalizerReps c hS4 2)⁻¹ * (normalizerReps c hS4 1)⁻¹ ∈
      centralizerS c := by
    have h3 : normalizerGen c hS4 ^ 3 ∈ centralizerS c :=
      normalizerGen_pow_three_mem_centralizer c hS4
    have hneg : (normalizerGen c hS4 ^ 3)⁻¹ ∈ centralizerS c :=
      (centralizerS c).inv_mem h3
    simpa [normalizerReps, pow_two, pow_succ, mul_inv_rev, mul_assoc] using hneg
  have hfix := conjIrrB_mem_centralizerS_eq_self c hS4 hmemC (nuHat c h12 ν)
  have hEqC : conjIrrB c hmem3 (nuHat c h12 ν) =
      conjIrrB c (B_conj_mem_of_normalizerS c (centralizerS_le_normalizerS c hmemC))
        (nuHat c h12 ν) := by
    apply conjIrrB_congr c ?_ hmem3
      (B_conj_mem_of_normalizerS c (centralizerS_le_normalizerS c hmemC))
      (nuHat c h12 ν)
    simp [normalizerReps, pow_succ, mul_inv_rev, mul_assoc]
  calc
    conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1))
        (conjNuHatB c h12 hS4 ν 2)
        = conjIrrB c hmem3 (nuHat c h12 ν) := by
            simpa [hmem3, conjNuHatB] using hmul.symm
    _ = conjIrrB c (B_conj_mem_of_normalizerS c (centralizerS_le_normalizerS c hmemC))
          (nuHat c h12 ν) := hEqC
    _ = nuHat c h12 ν := hfix

/-- If two of the three normalizer conjugates of `ν̂` agree, then all three
agree. -/
private lemma conjNuHatB_pair_eq_all (h12 : Hyp12 c) (hS4 : Section4Hyp c)
    (ν : Irr (↥c.H0)) {i j : Fin 3} (hij : i ≠ j)
    (h : conjNuHatB c h12 hS4 ν i = conjNuHatB c h12 hS4 ν j) :
    conjNuHatB c h12 hS4 ν 0 = conjNuHatB c h12 hS4 ν 1 ∧
      conjNuHatB c h12 hS4 ν 1 = conjNuHatB c h12 hS4 ν 2 := by
  have hinj : Function.Injective (fun β : Irr (↥c.B) =>
      conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1)) β) :=
    conjIrrB_injective c (normalizerReps_inv_mem c hS4 1)
  have hAll_of_C1_fixed (h10 : conjNuHatB c h12 hS4 ν 1 = nuHat c h12 ν) :
      conjNuHatB c h12 hS4 ν 0 = conjNuHatB c h12 hS4 ν 1 ∧
        conjNuHatB c h12 hS4 ν 1 = conjNuHatB c h12 hS4 ν 2 := by
    constructor
    · rw [h10]
      exact conjNuHatB_zero c h12 hS4 ν
    · calc
        conjNuHatB c h12 hS4 ν 1
            = conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1))
                (nuHat c h12 ν) := rfl
        _ = conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1))
                (conjNuHatB c h12 hS4 ν 1) := by rw [← h10]
        _ = conjNuHatB c h12 hS4 ν 2 := conjNuHatB_one_sq c h12 hS4 ν
  fin_cases i <;> fin_cases j
  · exfalso
    exact hij rfl
  · have h10 : conjNuHatB c h12 hS4 ν 1 = nuHat c h12 ν :=
      h.symm.trans (conjNuHatB_zero c h12 hS4 ν)
    exact hAll_of_C1_fixed h10
  · have h20 : conjNuHatB c h12 hS4 ν 2 = nuHat c h12 ν :=
      h.symm.trans (conjNuHatB_zero c h12 hS4 ν)
    have hEq : conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1))
          (conjNuHatB c h12 hS4 ν 1) =
        conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1))
          (conjNuHatB c h12 hS4 ν 2) := by
      calc
        conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1))
            (conjNuHatB c h12 hS4 ν 1)
            = conjNuHatB c h12 hS4 ν 2 := conjNuHatB_one_sq c h12 hS4 ν
        _ = nuHat c h12 ν := h20
        _ = conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1))
              (conjNuHatB c h12 hS4 ν 2) := (conjNuHatB_one_cube c h12 hS4 ν).symm
    have h10 : conjNuHatB c h12 hS4 ν 1 = nuHat c h12 ν :=
      (hinj hEq).trans h20
    exact hAll_of_C1_fixed h10
  · have h10 : conjNuHatB c h12 hS4 ν 1 = nuHat c h12 ν :=
      h.trans (conjNuHatB_zero c h12 hS4 ν)
    exact hAll_of_C1_fixed h10
  · exfalso
    exact hij rfl
  · have hEq : conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1))
          (nuHat c h12 ν) =
        conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1))
          (conjNuHatB c h12 hS4 ν 1) :=
      h.trans (conjNuHatB_one_sq c h12 hS4 ν).symm
    have h10 : conjNuHatB c h12 hS4 ν 1 = nuHat c h12 ν := (hinj hEq).symm
    exact hAll_of_C1_fixed h10
  · have h20 : conjNuHatB c h12 hS4 ν 2 = nuHat c h12 ν :=
      h.trans (conjNuHatB_zero c h12 hS4 ν)
    have hEq : conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1))
          (conjNuHatB c h12 hS4 ν 1) =
        conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1))
          (conjNuHatB c h12 hS4 ν 2) := by
      calc
        conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1))
            (conjNuHatB c h12 hS4 ν 1)
            = conjNuHatB c h12 hS4 ν 2 := conjNuHatB_one_sq c h12 hS4 ν
        _ = nuHat c h12 ν := h20
        _ = conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1))
              (conjNuHatB c h12 hS4 ν 2) := (conjNuHatB_one_cube c h12 hS4 ν).symm
    have h10 : conjNuHatB c h12 hS4 ν 1 = nuHat c h12 ν :=
      (hinj hEq).trans h20
    exact hAll_of_C1_fixed h10
  · have hEq : conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1))
          (nuHat c h12 ν) =
        conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 1))
          (conjNuHatB c h12 hS4 ν 1) :=
      h.symm.trans (conjNuHatB_one_sq c h12 hS4 ν).symm
    have h10 : conjNuHatB c h12 hS4 ν 1 = nuHat c h12 ν := (hinj hEq).symm
    exact hAll_of_C1_fixed h10
  · exfalso
    exact hij rfl

/-- Every normalizer conjugate of `ν̂` is one of the three representatives'
conjugates. -/
private lemma exists_conjNuHatB_eq_of_normalizer (h12 : Hyp12 c) (hS4 : Section4Hyp c)
    {g : G} (hg : g ∈ normalizerS c) (ν : Irr (↥c.H0)) :
    ∃ i : Fin 3,
      conjIrrB c (B_conj_mem_of_normalizerS c hg) (nuHat c h12 ν) =
        conjNuHatB c h12 hS4 ν i := by
  classical
  rcases exists_normalizer_decomp c hS4 hg with ⟨i, c0, hc0, hdecomp⟩
  let hmem2 : ∀ b : ↥c.B, (normalizerReps c hS4 i)⁻¹ * c0 * (b : G) *
      ((normalizerReps c hS4 i)⁻¹ * c0)⁻¹ ∈ c.B :=
    B_conj_mem_of_normalizerS c ((normalizerS c).mul_mem
      (normalizerReps_inv_mem c hS4 i) (centralizerS_le_normalizerS c hc0))
  have hmul := conjIrrB_mul c
    (hg := normalizerReps_inv_mem c hS4 i)
    (hh := centralizerS_le_normalizerS c hc0)
    (nuHat c h12 ν)
  have hfix := conjIrrB_mem_centralizerS_eq_self c hS4 hc0
    (conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 i))
      (nuHat c h12 ν))
  have hEq0 : conjIrrB c (B_conj_mem_of_normalizerS c hg) (nuHat c h12 ν) =
      conjIrrB c hmem2 (nuHat c h12 ν) := by
    apply conjIrrB_congr c hdecomp (B_conj_mem_of_normalizerS c hg) hmem2 (nuHat c h12 ν)
  have hmain : conjIrrB c (B_conj_mem_of_normalizerS c hg) (nuHat c h12 ν) =
      conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 i))
        (nuHat c h12 ν) := by
    calc
      conjIrrB c (B_conj_mem_of_normalizerS c hg) (nuHat c h12 ν)
          = conjIrrB c hmem2 (nuHat c h12 ν) := hEq0
      _ = conjIrrB c (B_conj_mem_of_normalizerS c (centralizerS_le_normalizerS c hc0))
            (conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 i))
              (nuHat c h12 ν)) := by
            simpa [hmem2] using hmul
      _ = conjIrrB c (B_conj_mem_of_normalizerS c (normalizerReps_inv_mem c hS4 i))
            (nuHat c h12 ν) := hfix
  exact ⟨i, hmain⟩

/-- The `N_G(S)`-orbit of `ν̂` has size `1` or `3`: the quotient
`N_G(S)/C_G(S)` has order three and `C_G(S)` acts trivially on `Irr(B)`. -/
public theorem nuHatOrbit_card_eq_one_or_three (h12 : Hyp12 c) (hS4 : Section4Hyp c)
    (ν : Irr (↥c.H0)) :
    (nuHatOrbit c h12 (nuHat c h12 ν)).card = 1 ∨
      (nuHatOrbit c h12 (nuHat c h12 ν)).card = 3 := by
  classical
  let R : Fin 3 → Irr (↥c.B) := fun i => conjNuHatB c h12 hS4 ν i
  have hOrbitEq : nuHatOrbit c h12 (nuHat c h12 ν) = Finset.univ.image R := by
    ext β
    constructor
    · intro hβ
      rw [nuHatOrbit] at hβ
      rcases (Finset.mem_filter.mp hβ).2 with ⟨g, hg, hEq⟩
      rcases exists_conjNuHatB_eq_of_normalizer c h12 hS4 hg ν with ⟨i, hi⟩
      rw [Finset.mem_image]
      refine ⟨i, Finset.mem_univ i, ?_⟩
      rw [← hEq]
      exact hi.symm
    · intro hβ
      rw [Finset.mem_image] at hβ
      rcases hβ with ⟨i, hi, rfl⟩
      rw [nuHatOrbit]
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ (R i), ?_⟩
      exact ⟨(normalizerReps c hS4 i)⁻¹, normalizerReps_inv_mem c hS4 i, rfl⟩
  by_cases hinj : Function.Injective R
  · right
    rw [hOrbitEq]
    rw [Finset.card_image_of_injective Finset.univ hinj]
    simp
  · left
    rw [hOrbitEq]
    rcases Function.not_injective_iff.mp hinj with ⟨i, j, hEq, hij⟩
    have hAll := conjNuHatB_pair_eq_all c h12 hS4 ν hij hEq
    have himage : Finset.univ.image R = ({R 0} : Finset (Irr (↥c.B))) := by
      ext β
      rw [Finset.mem_image]
      constructor
      · rintro ⟨k, hk, rfl⟩
        rw [Finset.mem_singleton]
        fin_cases k <;> simp [R, hAll.1, hAll.2]
      · intro hβ
        rw [Finset.mem_singleton] at hβ
        exact ⟨0, Finset.mem_univ 0, hβ.symm⟩
    rw [himage]
    simp

/-- A `0/1`-valued count over three indices is odd exactly when at least one
index is chosen, provided two choices force all three. -/
private lemma fin3_count_odd_iff {P : Fin 3 → Prop} [DecidablePred P]
    (hP : ∀ ⦃i j : Fin 3⦄, P i → P j → i = j ∨ (∀ k : Fin 3, P k)) :
    Odd (∑ i : Fin 3, if P i then (1 : ℤ) else 0) ↔ ∃ i, P i := by
  classical
  constructor
  · intro hodd
    by_contra hnone
    have hnone' : ∀ i : Fin 3, ¬ P i := by
      intro i hi
      exact hnone ⟨i, hi⟩
    have hsum : (∑ i : Fin 3, if P i then (1 : ℤ) else 0) = 0 := by
      simp [hnone']
    rw [hsum] at hodd
    norm_num at hodd
  · rintro ⟨i, hi⟩
    by_cases hall : ∀ k : Fin 3, P k
    · have hsum : (∑ j : Fin 3, if P j then (1 : ℤ) else 0) = 3 := by
        norm_num [hall]
      rw [hsum]
      exact ⟨1, by norm_num⟩
    · have hnot : ∀ k : Fin 3, k ≠ i → ¬ P k := by
        intro k hk hkP
        rcases hP hi hkP with hik | hall'
        · exact hk hik.symm
        · exact hall hall'
      have hsum : (∑ j : Fin 3, if P j then (1 : ℤ) else 0) = 1 := by
        rw [Finset.sum_eq_single i]
        · simp [hi]
        · intro j _ hj
          simp [hnot j hj]
        · intro hmem
          simp at hmem
      rw [hsum]
      exact ⟨0, by norm_num⟩

/-- `|H0 : U| = |S0|` (the `H0 = U·S0` product decomposition). -/
private lemma U_index_eq_S0_card_s4 (c : Hyp11 G) (h12 : Hyp12 c) :
    (c.U.subgroupOf c.H0).index = Nat.card (c.S0 : Subgroup G) := by
  classical
  let f : ↥c.U × ↥c.S0 → ↥c.H0 := fun p =>
    ⟨(p.1 : G) * (p.2 : G), c.H0.mul_mem ((h12.U_normal_in_H0).1 p.1.2) (S0_le_H0 c p.2.2)⟩
  have hinj : Function.Injective f := by
    intro p q hEq
    have hEq' : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) := congrArg Subtype.val hEq
    have h₁ : (q.1 : G)⁻¹ * (p.1 : G) = (q.2 : G) * (p.2 : G)⁻¹ := by
      calc
        (q.1 : G)⁻¹ * (p.1 : G) = (q.1 : G)⁻¹ * ((p.1 : G) * (p.2 : G)) * (p.2 : G)⁻¹ := by group
        _ = (q.1 : G)⁻¹ * ((q.1 : G) * (q.2 : G)) * (p.2 : G)⁻¹ := by rw [hEq']
        _ = (q.2 : G) * (p.2 : G)⁻¹ := by group
    have hU : (q.1 : G)⁻¹ * (p.1 : G) ∈ c.U := (c.U).mul_mem ((c.U).inv_mem q.1.2) p.1.2
    have hS0 : (q.2 : G) * (p.2 : G)⁻¹ ∈ c.S0 := (c.S0).mul_mem q.2.2 ((c.S0).inv_mem p.2.2)
    have honeU : (q.1 : G)⁻¹ * (p.1 : G) = 1 := U_inter_S0_eq_bot c hU (by
      rw [h₁]
      exact hS0)
    have hS0inU : (q.2 : G) * (p.2 : G)⁻¹ ∈ c.U := by
      rw [← h₁]
      exact hU
    have honeS : (q.2 : G) * (p.2 : G)⁻¹ = 1 := U_inter_S0_eq_bot c hS0inU hS0
    apply Prod.ext
    · apply Subtype.ext
      exact mul_left_cancel (a := (q.1 : G)⁻¹) (by
        calc
          (q.1 : G)⁻¹ * (p.1 : G) = 1 := honeU
          _ = (q.1 : G)⁻¹ * (q.1 : G) := by group)
    · apply Subtype.ext
      exact (calc
        (q.2 : G) = (q.2 : G) * (p.2 : G)⁻¹ * (p.2 : G) := by group
        _ = (p.2 : G) := by rw [honeS]; simp).symm
  have hsurj : ∀ x : ↥c.H0, ∃ p : ↥c.U × ↥c.S0, f p = x := by
    intro x
    rcases H0_eq_U_mul_S0 c h12 (x := x) with ⟨u, r, hEq⟩
    refine ⟨(u, r), ?_⟩
    apply Subtype.ext
    exact hEq.symm
  have hcardcong : Nat.card (↥c.H0) = Nat.card (↥c.U) * Nat.card (↥c.S0) := by
    let e : ↥c.U × ↥c.S0 ≃ ↥c.H0 := Equiv.ofBijective f ⟨hinj, hsurj⟩
    have hc : Nat.card (↥c.U × ↥c.S0) = Nat.card (↥c.H0) := Nat.card_congr e
    rw [← hc]
    simp
  have hUcard : Nat.card (↥(c.U.subgroupOf c.H0)) = Nat.card (↥c.U) := by
    exact Nat.card_congr {
      toFun := fun x : ↥(c.U.subgroupOf c.H0) => ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
      invFun := fun y : ↥c.U => ⟨⟨(y : G), (h12.U_normal_in_H0).1 y.2⟩,
        Subgroup.mem_subgroupOf.mpr y.2⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  have hcm := Subgroup.card_mul_index (c.U.subgroupOf c.H0)
  have h1 : (c.U.subgroupOf c.H0).index * Nat.card (↥c.U) = Nat.card (↥c.H0) := by
    rw [← hUcard]
    rw [mul_comm]
    exact hcm
  have h2 : Nat.card (↥c.S0) * Nat.card (↥c.U) = Nat.card (↥c.H0) := by
    calc
      Nat.card (↥c.S0) * Nat.card (↥c.U) = Nat.card (↥c.U) * Nat.card (↥c.S0) := by rw [mul_comm]
      _ = Nat.card (↥c.H0) := hcardcong.symm
  exact mul_right_cancel₀ (b := Nat.card (↥c.U)) (Nat.card_pos (α := ↥c.U)).ne' (by
    calc
      (c.U.subgroupOf c.H0).index * Nat.card (↥c.U) = Nat.card (↥c.H0) := h1
      _ = Nat.card (↥c.S0) * Nat.card (↥c.U) := h2.symm)

/-- An odd-order element of `H0` lies in `U` (the quotient `H0/U ≅ S0`
is a `2`-group). -/
private lemma odd_order_mem_U_of_H0 (c : Hyp11 G) (h12 : Hyp12 c) {x : G}
    (hxH0 : x ∈ c.H0) (hxodd : Odd (orderOf x)) : x ∈ c.U := by
  classical
  let K : Subgroup (↥c.H0) := c.U.subgroupOf c.H0
  have hUleH0 : c.U ≤ c.H0 := U_le_H0 c
  have : K.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hUleH0]
    intro h k hU kH
    exact (h12.U_normal_in_H0).2 k kH h hU
  let q : ↥c.H0 →* (↥c.H0 ⧸ K) := QuotientGroup.mk' K
  let xH : ↥c.H0 := ⟨x, hxH0⟩
  have hqodd : Odd (orderOf (q xH)) := by
    have hdvd : orderOf (q xH) ∣ orderOf xH := orderOf_map_dvd q xH
    have hxord : orderOf xH = orderOf x := by
      simp [xH]
    exact hxodd.of_dvd_nat (by simpa [hxord] using hdvd)
  have hKcard : Nat.card (↥K) = Nat.card ↥c.U := by
    exact Nat.card_congr {
      toFun := fun y : ↥K => ⟨(y : G), Subgroup.mem_subgroupOf.mp y.2⟩
      invFun := fun y : ↥c.U => ⟨⟨(y : G), U_le_H0 c y.2⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
      left_inv := by intro y; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  have hcm := Subgroup.card_mul_index K
  have hH' : Nat.card (↥K) * K.index = Nat.card (↥c.H0) := hcm
  have hH'' : Nat.card ↥c.U * K.index = Nat.card (↥c.H0) := by
    rwa [hKcard] at hH'
  have hKindex : K.index = Nat.card (c.S0 : Subgroup G) :=
    U_index_eq_S0_card_s4 c h12
  have hquotCard : Nat.card (↥c.H0 ⧸ K) = Nat.card (c.S0 : Subgroup G) := by
    rw [← Subgroup.index_eq_card, hKindex]
  have hqpow : orderOf (q xH) ∣ Nat.card (c.S0 : Subgroup G) := by
    rw [← hquotCard]
    exact orderOf_dvd_natCard (q xH)
  have hS2 : Nat.Coprime (orderOf (q xH)) (Nat.card (c.S0 : Subgroup G)) := by
    have hcop2 : Nat.Coprime 2 (orderOf (q xH)) := by
      have hnot2 : ¬ 2 ∣ orderOf (q xH) := by
        rw [← even_iff_two_dvd]
        exact Nat.not_even_iff_odd.mpr hqodd
      exact Nat.prime_two.coprime_iff_not_dvd.mpr hnot2
    have hS0p : IsPGroup 2 ↥(c.S0 : Subgroup G) :=
      IsPGroup.of_card (n := c.m) (S0_nat_card c)
    rcases hS0p.exists_card_eq with ⟨k, hk⟩
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.Coprime.symm hcop2)
  have hq1 : orderOf (q xH) = 1 := Nat.Coprime.eq_one_of_dvd hS2 hqpow
  have hq : q xH = 1 := orderOf_eq_one_iff.mp hq1
  have hxK : xH ∈ K := by
    rw [← QuotientGroup.ker_mk' K]
    exact MonoidHom.mem_ker.mpr hq
  exact Subgroup.mem_subgroupOf.mp hxK

/-- In the Section-4 case, `S' = 1`. -/
private lemma SPrime_eq_bot_s4 (hS4 : Section4Hyp c) : SPrime c = ⊥ := by
  classical
  have hm : c.m = 1 := by
    have h : 2 * 2 ^ c.m = 4 := by
      have hS4' : Nat.card (↥(c.S : Subgroup G)) = 4 := by exact hS4
      rw [← S_nat_card c, hS4']
    have hpow : 2 ^ c.m = 2 := Nat.eq_of_mul_eq_mul_left (by norm_num) h
    have hcases : c.m = 0 ∨ c.m = 1 ∨ 2 ≤ c.m := by omega
    rcases hcases with h0 | h1 | h2
    · rw [h0] at hpow
      norm_num at hpow
    · exact h1
    · have hge : 4 ≤ 2 ^ c.m := Nat.pow_le_pow_right (by norm_num : 0 < 2) h2
      omega
  have hS0card : Nat.card (c.S0 : Subgroup G) = 2 := by
    rw [S0_nat_card c, hm]
    norm_num
  have hSPcard : Nat.card (SPrime c : Subgroup G) = 1 := by
    have hEqCard : Nat.card ↥((SPrime c).subgroupOf (c.S0 : Subgroup G)) =
        Nat.card (SPrime c : Subgroup G) := by
      exact Nat.card_congr {
        toFun := fun x : ↥((SPrime c).subgroupOf (c.S0 : Subgroup G)) =>
          ⟨(x : G), Subgroup.mem_subgroupOf.mp x.2⟩
        invFun := fun y : ↥(SPrime c : Subgroup G) =>
          ⟨⟨(y : G), SPrime_le_S0 c y.2⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
        left_inv := by intro x; apply Subtype.ext; rfl
        right_inv := by intro y; apply Subtype.ext; rfl }
    have hcm := Subgroup.card_mul_index ((SPrime c).subgroupOf (c.S0 : Subgroup G))
    have hcm' : Nat.card (SPrime c : Subgroup G) * 2 = 2 := by
      rw [hEqCard] at hcm
      rw [SPrime_index c, hS0card] at hcm
      exact hcm
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) hcm'
  exact Subgroup.card_eq_one.mp hSPcard

/-- `t ∉ X = S'·U` in the Section-4 case. -/
private lemma tH0_not_mem_extensionSubgroup_s4 (hS4 : Section4Hyp c) :
    ((tH0 c : ↥c.H0) : G) ∉ extensionSubgroup c := by
  intro htX
  have hSPbot : SPrime c = ⊥ := SPrime_eq_bot_s4 c hS4
  have hext : extensionSubgroup c = c.U := by
    unfold extensionSubgroup
    rw [hSPbot]
    simp
  have htU : (tH0 c : G) ∈ c.U := by
    rwa [hext] at htX
  exact t_not_mem_U c htU

/-- `λ₂(t) = -1` in the Section-4 case. -/
private theorem lambdaTwo_val_tH0_neg_one (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c) :
    ((lambdaTwo c h12).1 (tH0 c) : ℂ) = -1 :=
  by
    simpa using (lambdaTwo_val_neg_one_of_not_mem_extensionSubgroup c h12 hSC (tH0 c)
      (tH0_not_mem_extensionSubgroup_s4 c hS4))

/-- `μ̂`, inflated to `C_G(S) = S × B` (trivial on `S`). -/
private noncomputable def muHatOnC (c : Hyp11 G) (h12 : Hyp12 c)
    (hS4 : Section4Hyp c) (μ : Irr (↥c.H0)) :
    ClassFunction (↥(centralizerS c)) :=
  fun x => (nuHat c h12 μ).1 ((centralizerS_equiv c hS4 x).2)

/-- The trivial character is irreducible. -/
private theorem trivial_isIrreducible_char (G : Type u) [Group G] [Fintype G] :
    IsIrreducibleCharacter (1 : ClassFunction G) :=
  (isLinearCharacter_one (G := G)).1

/-- Schur: for a central element `t` with `t² = 1` acting on an irreducible
representation `ρ`, there is a scalar `a` with `a² = 1` and `ρ(t) = a·1`. -/
private theorem rep_apply_central_scalar {G : Type u} [Group G] [Fintype G]
    {t : G} (htc : ∀ g : G, t * g = g * t)
    (ht2 : t ^ 2 = 1) {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ))
    (hρirr : Representation.IsIrreducible ρ) :
    ∃ a : ℂ, ρ t = a • (1 : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∧ a ^ 2 = 1 := by
  classical
  let : Representation.IsIrreducible ρ := hρirr
  have hcomm (g : G) : ρ t * ρ g = ρ g * ρ t := by
    rw [← map_mul, ← map_mul, htc g]
  let τ : Representation.IntertwiningMap ρ ρ := ⟨ρ t, by
    intro g
    apply LinearMap.ext
    intro v
    exact congrArg (fun f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) => f v) (hcomm g)⟩
  have hfin : Module.finrank ℂ (Representation.IntertwiningMap ρ ρ) = 1 :=
    (irreducible_iff_end_dimension_one (ρ := ρ)).1 hρirr
  have : Nontrivial (Fin n → ℂ) := irreducible_nontrivial (ρ := ρ)
  have hone_ne_zero : (1 : Representation.IntertwiningMap ρ ρ) ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → ℂ)
    have hvzero : v = 0 := by
      simpa using congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) h
    exact hv hvzero
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a • (1 : Representation.IntertwiningMap ρ ρ) = τ :=
    (finrank_eq_one_iff_of_nonzero' (K := ℂ)
      (V := Representation.IntertwiningMap ρ ρ)
      (1 : Representation.IntertwiningMap ρ ρ) hone_ne_zero).mp hfin τ
  have hscalar : ρ t = a • (1 : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) := by
    have htm := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f.toLinearMap) ha
    change τ.toLinearMap = (a • (1 : Representation.IntertwiningMap ρ ρ)).toLinearMap
    exact htm.symm
  have ha2 : a ^ 2 = 1 := by
    have hunit : (ρ t) * (ρ t) = 1 := by
      rw [← map_mul]
      have ht2' : t * t = 1 := by simpa [pow_two] using ht2
      rw [ht2', map_one]
    have hsq : (a • (1 : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) * (a • 1) = 1 := by
      rw [← hscalar]
      exact hunit
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → ℂ)
    have hv2 : (a • (a • v)) = v := by
      have h := congrArg (fun f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) => f v) hsq
      simpa using h
    have hsmul : (a ^ 2) • v = v := by
      simpa [smul_smul, pow_two] using hv2
    have hsmul' : (a ^ 2) • v = (1 : ℂ) • v := by
      rw [one_smul]
      exact hsmul
    exact smul_left_injective ℂ hv hsmul'
  exact ⟨a, hscalar, ha2⟩

/-- `μ̂` on `C_G(S)` is a character. -/
private theorem muHatOnC_isCharacter (c : Hyp11 G) (h12 : Hyp12 c)
    (hS4 : Section4Hyp c) (μ : Irr (↥c.H0)) :
    IsCharacter (muHatOnC c h12 hS4 μ) := by
  classical
  let χ : ClassFunction (↥(c.S : Subgroup G) × ↥c.B) :=
    prodChar (1 : ClassFunction (↥(c.S : Subgroup G))) (nuHat c h12 μ).1
  have hχ : IsCharacter χ :=
    prodChar_isCharacter _ _
      (isCharacter_of_isIrreducibleCharacter (trivial_isIrreducible_char (↥(c.S : Subgroup G))))
      (isCharacter_of_isIrreducibleCharacter (nuHat c h12 μ).2)
  have hEq : muHatOnC c h12 hS4 μ = fun x => χ (centralizerS_equiv c hS4 x) := by
    funext x
    dsimp [muHatOnC, χ, prodChar]
    simp
  rw [hEq]
  exact isCharacter_congr (centralizerS_equiv c hS4) hχ

/-- `μ̂` on `C_G(S)` is irreducible. -/
private theorem muHatOnC_isIrreducible (c : Hyp11 G) (h12 : Hyp12 c)
    (hS4 : Section4Hyp c) (μ : Irr (↥c.H0)) :
    IsIrreducibleCharacter (muHatOnC c h12 hS4 μ) := by
  classical
  let χ : ClassFunction (↥(c.S : Subgroup G) × ↥c.B) :=
    prodChar (1 : ClassFunction (↥(c.S : Subgroup G))) (nuHat c h12 μ).1
  have hχ : IsIrreducibleCharacter χ :=
    prodChar_isIrreducible _ _
      (trivial_isIrreducible_char (↥(c.S : Subgroup G))) (nuHat c h12 μ).2
  have hEq : muHatOnC c h12 hS4 μ = fun x => χ (centralizerS_equiv c hS4 x) := by
    funext x
    dsimp [muHatOnC, χ, prodChar]
    simp
  rw [hEq]
  exact isIrreducibleCharacter_congr (centralizerS_equiv c hS4) hχ

/-- The character `μ'` of Lemma 4.2: induction of `μ̂` from `C_G(S)` to `G`. -/
private noncomputable def lemma42_mu' (c : Hyp11 G) (h12 : Hyp12 c)
    (hS4 : Section4Hyp c) (μ : Irr (↥c.H0)) : ClassFunction G :=
  inducedClassFunction (centralizerS c) (muHatOnC c h12 hS4 μ)

/-- `μ'` is a character. -/
private theorem lemma42_mu'_isCharacter (c : Hyp11 G) (h12 : Hyp12 c)
    (hS4 : Section4Hyp c) (μ : Irr (↥c.H0)) :
    IsCharacter (lemma42_mu' c h12 hS4 μ) :=
  isCharacter_induced (centralizerS c) (muHatOnC_isCharacter c h12 hS4 μ)

/-- An irreducible character with value equal to its degree at a central
involution is trivial on that involution. -/
private lemma irreducible_char_mul_central_involution {G : Type u} [Group G] [Fintype G]
    {t : G} (htc : ∀ g : G, t * g = g * t) (ht2 : t ^ 2 = 1)
    {χ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (hdeg : χ t = χ 1) (u : G) : χ (t * u) = χ u := by
  classical
  rcases hχ with ⟨n, ρ, hρ, hχeq⟩
  let : Representation.IsIrreducible ρ := hρ
  have : Nontrivial (Fin n → ℂ) := irreducible_nontrivial (ρ := ρ)
  rcases rep_apply_central_scalar htc ht2 ρ hρ with ⟨a, hscalar, ha2⟩
  have hχ1ne : χ 1 ≠ 0 := irreducible_char_one_ne_zero ⟨n, ρ, hρ, hχeq⟩
  have ht' : a * χ 1 = χ 1 := by
    calc
      a * χ 1 = a * (LinearMap.trace ℂ (Fin n → ℂ) (ρ 1)) := by
        rw [hχeq]
        rfl
      _ = LinearMap.trace ℂ (Fin n → ℂ) (ρ t) := by
        rw [hscalar]
        simp [smul_eq_mul]
      _ = χ t := by
        rw [hχeq]
        rfl
      _ = χ 1 := hdeg
  have ha : a = 1 := mul_left_cancel₀ hχ1ne (by simpa [mul_comm] using ht')
  have htu : ρ (t * u) = ρ u := by
    rw [map_mul, hscalar, ha]
    simp
  calc
    χ (t * u) = LinearMap.trace ℂ (Fin n → ℂ) (ρ (t * u)) := by
      rw [hχeq]
      rfl
    _ = LinearMap.trace ℂ (Fin n → ℂ) (ρ u) := by rw [htu]
    _ = χ u := by
      rw [hχeq]
      rfl

/-- `ν(t·u) = ν(u)` for `u ∈ U` and Section-4 `ν`. -/
private lemma nu_t_mul_u (c : Hyp11 G) (_h12 : Hyp12 c)
    {ν : Irr (↥c.H0)} (hνt : ν.1 (tH0 c) = ν.1 1)
    {u : G} (huU : u ∈ c.U) :
    ν.1 ⟨c.t * u, c.H0.mul_mem (S0_le_H0 c c.t_mem_S0) (U_le_H0 c huU)⟩ =
      ν.1 ⟨u, U_le_H0 c huU⟩ := by
  let uH : ↥c.H0 := ⟨u, U_le_H0 c huU⟩
  have h := irreducible_char_mul_central_involution
    (G := ↥c.H0) (t := tH0 c)
    (htc := by intro g; simpa [tH0] using t_central_H0' c g)
    (ht2 := t_H0_sq c) ν.2 hνt uH
  have hsub : (⟨c.t * u, c.H0.mul_mem (S0_le_H0 c c.t_mem_S0) (U_le_H0 c huU)⟩ : ↥c.H0) =
      tH0 c * uH := by
    apply Subtype.ext
    change c.t * u = c.t * u
    rfl
  rw [hsub]
  exact h

/-- `(λ₂ν)(t·u) = -ν(u)` for `u ∈ U` and Section-4 `ν`. -/
private lemma lambdaTwoNu_t_mul_u (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {ν : Irr (↥c.H0)} (hνt : ν.1 (tH0 c) = ν.1 1)
    {u : G} (huU : u ∈ c.U) :
    (LambdaChar (lambdaTwo c h12).1 * ν.1)
      ⟨c.t * u, c.H0.mul_mem (S0_le_H0 c c.t_mem_S0) (U_le_H0 c huU)⟩ =
      - ν.1 ⟨u, U_le_H0 c huU⟩ := by
  let uH : ↥c.H0 := ⟨u, U_le_H0 c huU⟩
  have h_lam_t : ((lambdaTwo c h12).1 (tH0 c) : ℂ) = -1 :=
    lambdaTwo_val_tH0_neg_one c h12 hSC hS4
  have h_lam_u : ((lambdaTwo c h12).1 uH : ℂ) = 1 := by
    have hu := (lambdaTwo c h12).2 uH huU
    exact congrArg (fun u : ℂˣ => (u : ℂ)) hu
  have h_lam_tu : ((lambdaTwo c h12).1 ⟨c.t * u,
      c.H0.mul_mem (S0_le_H0 c c.t_mem_S0) (U_le_H0 c huU)⟩ : ℂ) = -1 := by
    have hsub : (⟨c.t * u,
        c.H0.mul_mem (S0_le_H0 c c.t_mem_S0) (U_le_H0 c huU)⟩ : ↥c.H0) =
        tH0 c * uH := by
      apply Subtype.ext
      change c.t * u = c.t * u
      rfl
    rw [hsub, map_mul]
    simp [h_lam_t, h_lam_u]
  have hνtu := nu_t_mul_u c h12 hνt huU
  simp [LambdaChar, h_lam_tu, hνtu]

/-- A difference of irreducible characters is a class function. -/
private lemma isClassFunction_sub_irr {G : Type u} [Group G] [Fintype G]
    {χ ψ : ClassFunction G} (hχ : IsIrreducibleCharacter χ)
    (hψ : IsIrreducibleCharacter ψ) : IsClassFunction (χ - ψ) := by
  intro x g
  have hχ' := irreducibleCharacter_isClassFunction hχ x g
  have hψ' := irreducibleCharacter_isClassFunction hψ x g
  simp [hχ', hψ']

/-- Orbits are symmetric: `μ ∈ orbit ν` implies `ν ∈ orbit μ`. -/
private lemma orbit_symm (c : Hyp11 G)
    [Fintype ↥(LambdaHom c.H0 c.U)] {ν μ : ClassFunction (↥c.H0)}
    (hμ : μ ∈ orbit c.H0 c.U ν) : ν ∈ orbit c.H0 c.U μ := by
  classical
  rcases (Finset.mem_image.mp hμ) with ⟨l, hl, hEq⟩
  have hL : LambdaChar l.1 * ν = μ := hEq
  refine Finset.mem_image.mpr ⟨l⁻¹, Finset.mem_univ _, ?_⟩
  rw [← hL]
  ext x
  simp [LambdaChar]

/-- On `T`, `δν` is the difference of the two induced characters to `H`. -/
private lemma deltaNu_on_T (c : Hyp11 G) (h12 : Hyp12 c)
    (hH0le : c.H0 ≤ c.H) {ν : Irr (↥c.H0)} (g : G) (hgT : g ∈ c.T)
    (hg : g ∈ c.H) :
    deltaNu c h12 ν g =
      (inducedFromSub hH0le ν.1 -
        inducedFromSub hH0le (lambdaTwoMul c h12 ν).1) ⟨g, hg⟩ := by
  let lam : Irr (↥c.H0) := lambdaTwoMul c h12 ν
  have h_nu_lam : ν.1 ∈ orbit c.H0 c.U (lambdaTwoMul c h12 ν).1 :=
    orbit_symm c (ν := ν.1) (μ := LambdaChar (lambdaTwo c h12).1 * ν.1)
      (lambdaTwoMul_equiv c h12 ν)
  have h := tildeNu_on_T c h12 h_nu_lam g hgT hg
  unfold deltaNu
  simpa [lam] using h

/-- Every element of `B` has odd order. -/
private lemma odd_order_of_mem_B (c : Hyp11 G) {b : G} (hbB : b ∈ c.B) :
    Odd (orderOf b) := by
  have hbU : b ∈ c.U := B_le_U c hbB
  have hcop : Nat.Coprime 2 (Nat.card ↥c.U) := U_coprime_two c
  have hoddU : Odd (Nat.card ↥c.U) := Nat.coprime_two_left.mp hcop
  have hdvd : orderOf b ∣ Nat.card ↥c.U := by
    change orderOf (c.U.subtype (⟨b, hbU⟩ : ↥c.U)) ∣ Nat.card ↥c.U
    rw [orderOf_injective c.U.subtype (Subgroup.subtype_injective c.U) (⟨b, hbU⟩ : ↥c.U)]
    have hb' : orderOf (⟨b, hbU⟩ : ↥c.U) ∣ Fintype.card ↥c.U :=
      orderOf_dvd_card (G := ↥c.U) (x := ⟨b, hbU⟩)
    rwa [← Nat.card_eq_fintype_card] at hb'
  exact Odd.of_dvd_nat hoddU hdvd

/-- `δν` vanishes on `B`. -/
private lemma deltaNu_zero_on_B (c : Hyp11 G) (h12 : Hyp12 c)
    (_hSC : Section3Hyp c) (_hS4 : Section4Hyp c)
    {ν : Irr (↥c.H0)} (_hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (_hνt : ν.1 (tH0 c) = ν.1 1) {b : G} (hbB : b ∈ c.B) :
    deltaNu c h12 ν b = 0 := by
  classical
  rw [deltaNu_eq_induced c h12 ν]
  unfold inducedClassFunction
  have hsum : (∑ x : G, if hx : x⁻¹ * b * x ∈ c.H0 then
      (ν.1 - LambdaChar (lambdaTwo c h12).1 * ν.1) ⟨x⁻¹ * b * x, hx⟩ else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hx0 : x⁻¹ * b * x ∈ c.H0
    · have hodd : Odd (orderOf (x⁻¹ * b * x)) := by
        have hbodd := odd_order_of_mem_B c hbB
        have hbodd' : Odd (orderOf (x⁻¹ * b * (x⁻¹)⁻¹)) := by
          rw [orderOf_conj_eq x⁻¹ b]
          exact hbodd
        simpa using hbodd'
      have hyU : x⁻¹ * b * x ∈ c.U := odd_order_mem_U_of_H0 c h12 hx0 hodd
      have hlam : ((lambdaTwo c h12).1 ⟨x⁻¹ * b * x, hx0⟩ : ℂ) = 1 := by
        have hu := (lambdaTwo c h12).2 ⟨x⁻¹ * b * x, hx0⟩ hyU
        exact congrArg (fun u : ℂˣ => (u : ℂ)) hu
      have hφ : (ν.1 - LambdaChar (lambdaTwo c h12).1 * ν.1)
          ⟨x⁻¹ * b * x, hx0⟩ = 0 := by
        simp [LambdaChar, hlam]
      simp [hx0, hφ]
    · simp [hx0]
  rw [hsum]
  simp

/-- `t·b ∈ T` for `b ∈ B`. -/
private lemma t_mul_b_mem_T (c : Hyp11 G) {b : G} (hbB : b ∈ c.B) :
    (c.t * b : G) ∈ c.T := by
  constructor
  · exact c.H0.mul_mem (S0_le_H0 c c.t_mem_S0) (U_le_H0 c (B_le_U c hbB))
  · intro hU
    have hbU : b ∈ c.U := B_le_U c hbB
    have htU : c.t ∈ c.U := by
      have h := c.U.mul_mem hU ((c.U).inv_mem hbU)
      have hEq : (c.t * b) * b⁻¹ = c.t := by group
      rwa [hEq] at h
    exact t_not_mem_U c htU

/-- `δν(t·b) = 4ν(b)` for `b ∈ B` and Section-4 `ν`. -/
private lemma deltaNu_at_t_mul_B (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {ν : Irr (↥c.H0)} (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1) {b : G} (hbB : b ∈ c.B) :
    deltaNu c h12 ν (c.t * b) = 4 * ν.1 ⟨b, U_le_H0 c (B_le_U c hbB)⟩ := by
  classical
  let phi : ClassFunction (↥c.H0) :=
    ν.1 - LambdaChar (lambdaTwo c h12).1 * ν.1
  let hH0le : c.H0 ≤ c.H := h12.H0_normal_in_H.1
  have hH0 : c.t * b ∈ c.H0 := (t_mul_b_mem_T c hbB).1
  have hT : c.t * b ∈ c.T := t_mul_b_mem_T c hbB
  have hsh : c.s * (c.t * b) * c.s⁻¹ ∈ c.H0 :=
    (h12.H0_normal_in_H).2 c.s (s_mem_H c) (c.t * b) hH0
  have hνc : IsClassFunction ν.1 := irreducibleCharacter_isClassFunction ν.2
  have h_lam_irr : IsIrreducibleCharacter (LambdaChar (lambdaTwo c h12).1 * ν.1) :=
    isIrreducibleCharacter_mul_linear (isLinearCharacter_of_hom (lambdaTwo c h12).1) ν.2
  have h_lam_c : IsClassFunction (LambdaChar (lambdaTwo c h12).1 * ν.1) :=
    irreducibleCharacter_isClassFunction h_lam_irr
  have hφc : IsClassFunction phi := isClassFunction_sub_irr ν.2 h_lam_irr
  have hδeq := deltaNu_on_T c h12 hH0le (ν := ν) (c.t * b) hT (hH0le hH0)
  have hνind := inducedFromSub_eq_add_conj_index_two c.H0 c.H hH0le
    (H0_index c h12) (s := c.s) (s_mem_H c) (s_not_mem_H0' c h12)
    ν.1 hνc (h := c.t * b) hH0 hsh
  have h_lam_ind := inducedFromSub_eq_add_conj_index_two c.H0 c.H hH0le
    (H0_index c h12) (s := c.s) (s_mem_H c) (s_not_mem_H0' c h12)
    (lambdaTwoMul c h12 ν).1 h_lam_c (h := c.t * b) hH0 hsh
  have hcalc : deltaNu c h12 ν (c.t * b) =
      (ν.1 ⟨c.t * b, hH0⟩ - (LambdaChar (lambdaTwo c h12).1 * ν.1) ⟨c.t * b, hH0⟩) +
        (ν.1 ⟨c.s * (c.t * b) * c.s⁻¹, hsh⟩ -
          (LambdaChar (lambdaTwo c h12).1 * ν.1)
            ⟨c.s * (c.t * b) * c.s⁻¹, hsh⟩) := by
    rw [hδeq]
    change (inducedFromSub hH0le ν.1 ⟨c.t * b, hH0le hH0⟩) -
        (inducedFromSub hH0le (lambdaTwoMul c h12 ν).1 ⟨c.t * b, hH0le hH0⟩) =
      (ν.1 ⟨c.t * b, hH0⟩ - (LambdaChar (lambdaTwo c h12).1 * ν.1) ⟨c.t * b, hH0⟩) +
        (ν.1 ⟨c.s * (c.t * b) * c.s⁻¹, hsh⟩ -
          (LambdaChar (lambdaTwo c h12).1 * ν.1)
            ⟨c.s * (c.t * b) * c.s⁻¹, hsh⟩)
    rw [hνind, h_lam_ind]
    simp [lambdaTwoMul]
    ring
  have hbU : b ∈ c.U := B_le_U c hbB
  have hφ_tb : ν.1 ⟨c.t * b, hH0⟩ -
      (LambdaChar (lambdaTwo c h12).1 * ν.1) ⟨c.t * b, hH0⟩ =
      2 * ν.1 ⟨b, U_le_H0 c hbU⟩ := by
    have h1 := nu_t_mul_u c h12 hνt hbU
    have h2 := lambdaTwoNu_t_mul_u c h12 hSC hS4 hνt hbU
    rw [h1, h2]
    ring
  let b' : G := c.s * b * c.s⁻¹
  have hb'U : b' ∈ c.U := S_normalizes_U c c.s c.s_mem_S b hbU
  have hH0' : c.t * b' ∈ c.H0 :=
    c.H0.mul_mem (S0_le_H0 c c.t_mem_S0) (U_le_H0 c hb'U)
  have hconj_eq : (⟨c.s * (c.t * b) * c.s⁻¹, hsh⟩ : ↥c.H0) =
      ⟨c.t * b', hH0'⟩ := by
    apply Subtype.ext
    change c.s * (c.t * b) * c.s⁻¹ = c.t * (c.s * b * c.s⁻¹)
    calc
      c.s * (c.t * b) * c.s⁻¹ = (c.s * c.t * c.s⁻¹) * (c.s * b * c.s⁻¹) := by group
      _ = c.t * (c.s * b * c.s⁻¹) := by rw [s_conj_t c]
  have hνb' : ν.1 ⟨b', U_le_H0 c hb'U⟩ = ν.1 ⟨b, U_le_H0 c hbU⟩ := by
    have hc := congrFun hνs ⟨b, U_le_H0 c hbU⟩
    have hsub : (⟨c.s * b * c.s⁻¹,
        s_normalizes_H0 c h12 ⟨b, U_le_H0 c hbU⟩⟩ : ↥c.H0) =
        ⟨b', U_le_H0 c hb'U⟩ := by
      apply Subtype.ext
      rfl
    simpa [conjChar, conjMonoidHom, b', hsub] using hc
  have hφ_conj : ν.1 ⟨c.s * (c.t * b) * c.s⁻¹, hsh⟩ -
      (LambdaChar (lambdaTwo c h12).1 * ν.1)
        ⟨c.s * (c.t * b) * c.s⁻¹, hsh⟩ =
      2 * ν.1 ⟨b, U_le_H0 c hbU⟩ := by
    have h1 := nu_t_mul_u c h12 hνt hb'U
    have h2 := lambdaTwoNu_t_mul_u c h12 hSC hS4 hνt hb'U
    rw [hconj_eq, h1, h2, hνb']
    ring
  rw [hcalc, hφ_tb, hφ_conj]
  ring

/-- `δν` is a class function. -/
private lemma deltaNu_isClassFunction (c : Hyp11 G) (h12 : Hyp12 c)
    {ν : Irr (↥c.H0)} : IsClassFunction (deltaNu c h12 ν) := by
  intro x g
  have h1 := isClassFunction_of_isGeneralizedCharacter (tildeNu_isGeneralized c h12 ν) x g
  have h2 := isClassFunction_of_isGeneralizedCharacter
    (tildeNu_isGeneralized c h12 (lambdaTwoMul c h12 ν)) x g
  simp [deltaNu, h1, h2]

/-- `δν(x·t·x⁻¹·b) = 4ν(b^{x⁻¹})` for `x ∈ N_G(S)`, `b ∈ B`. -/
private lemma deltaNu_at_conj_involution_mul_B (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {ν : Irr (↥c.H0)} (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1) {x : G} (hxN : x ∈ normalizerS c)
    {b : G} (hbB : b ∈ c.B) :
    deltaNu c h12 ν (x * c.t * x⁻¹ * b) =
      4 * ν.1 ⟨x⁻¹ * b * x, U_le_H0 c (B_le_U c (by
        simpa using (B_conj_mem_of_normalizerS c ((normalizerS c).inv_mem hxN) ⟨b, hbB⟩)))⟩ := by
  classical
  have hb'B : x⁻¹ * b * x ∈ c.B :=
    by
      simpa using (B_conj_mem_of_normalizerS c ((normalizerS c).inv_mem hxN) ⟨b, hbB⟩)
  have hb'H0 : x⁻¹ * b * x ∈ c.H0 := U_le_H0 c (B_le_U c hb'B)
  have hδ := deltaNu_at_t_mul_B c h12 hSC hS4 hνs hνt hb'B
  have hcf := deltaNu_isClassFunction c h12 (ν := ν) (c.t * (x⁻¹ * b * x)) x
  have hEqArg : x * (c.t * (x⁻¹ * b * x)) * x⁻¹ = x * c.t * x⁻¹ * b := by
    group
  rw [hEqArg] at hcf
  rw [hcf, hδ]

/-- `δν` pulled back along `S × B ≃ C_G(S)`. -/
private noncomputable def deltaSB (c : Hyp11 G) (h12 : Hyp12 c)
    (hS4 : Section4Hyp c) (ν : Irr (↥c.H0)) :
    ClassFunction (↥(c.S : Subgroup G) × ↥c.B) :=
  fun p => deltaNu c h12 ν
    ((centralizerS_equiv_inv c hS4 p : ↥(centralizerS c)) : G)

/-- `μ̂`, viewed on `S × B`. -/
private noncomputable def muHatSB (c : Hyp11 G) (h12 : Hyp12 c)
    (μ : Irr (↥c.H0)) : ClassFunction (↥(c.S : Subgroup G) × ↥c.B) :=
  fun p => (nuHat c h12 μ).1 p.2

/-- `μ̂` on `S × B` is the pullback of `μ̂` on `C_G(S)`. -/
private lemma muHatOnC_equiv_apply (h12 : Hyp12 c) (hS4 : Section4Hyp c)
    (μ : Irr (↥c.H0)) (p : ↥(c.S : Subgroup G) × ↥c.B) :
    muHatOnC c h12 hS4 μ
        ((centralizerS_equiv_inv c hS4 p : ↥(centralizerS c))) =
      (nuHat c h12 μ).1 p.2 := by
  dsimp [muHatOnC, centralizerS_equiv]
  simp

/-- Frobenius reciprocity and the centralizer isomorphism give
`(δν, μ')_G = (δν|_{S×B}, μ̂)_{S×B}`. -/
private lemma scalarProduct_delta_muPrime_eq_SB (h12 : Hyp12 c) (hS4 : Section4Hyp c)
    (ν μ : Irr (↥c.H0)) :
    scalarProduct G (deltaNu c h12 ν) (lemma42_mu' c h12 hS4 μ) =
      scalarProduct (↥(c.S : Subgroup G) × ↥c.B)
        (deltaSB c h12 hS4 ν) (muHatSB c h12 μ) := by
  classical
  let δ : ClassFunction (↥(centralizerS c)) := fun x => deltaNu c h12 ν (x : G)
  let μC : ClassFunction (↥(centralizerS c)) := muHatOnC c h12 hS4 μ
  have hRec := frobenius_reciprocity (G := G) (H := centralizerS c) μC
    (hχ := deltaNu_isClassFunction c h12 (ν := ν))
  have hstar := congrArg star hRec
  have h1 : scalarProduct G (deltaNu c h12 ν) (lemma42_mu' c h12 hS4 μ) =
      scalarProduct (↥(centralizerS c)) δ μC := by
    calc
      scalarProduct G (deltaNu c h12 ν) (lemma42_mu' c h12 hS4 μ)
          = star (scalarProduct G (lemma42_mu' c h12 hS4 μ)
              (deltaNu c h12 ν)) :=
              (scalarProduct_conj (lemma42_mu' c h12 hS4 μ) (deltaNu c h12 ν)).symm
      _ = star (scalarProduct (↥(centralizerS c)) μC δ) := by
            simpa [lemma42_mu', μC, δ] using hstar
      _ = scalarProduct (↥(centralizerS c)) δ μC :=
            scalarProduct_conj μC δ
  have hEq := scalarProduct_equiv_invariance (G := ↥(centralizerS c))
    (H := ↥(c.S : Subgroup G) × ↥c.B)
    (centralizerS_equiv c hS4) (deltaSB c h12 hS4 ν) (muHatSB c h12 μ)
  have hfun1 : (fun x : ↥(centralizerS c) =>
      deltaSB c h12 hS4 ν (centralizerS_equiv c hS4 x)) = δ := by
    funext x
    dsimp [deltaSB, centralizerS_equiv, δ]
    simp
  have hfun2 : (fun x : ↥(centralizerS c) =>
      muHatSB c h12 μ (centralizerS_equiv c hS4 x)) = μC := by
    funext x
    dsimp [muHatSB, μC]
    have h := muHatOnC_equiv_apply c h12 hS4 μ (centralizerS_equiv c hS4 x)
    simpa [centralizerS_equiv] using h.symm
  rw [hfun1, hfun2] at hEq
  exact h1.trans hEq.symm

/-- Expanding the scalar product on `S × B` as a double sum over `S` and
`B`. -/
private lemma scalarProduct_SB_expand (h12 : Hyp12 c) (hS4 : Section4Hyp c)
    (ν μ : Irr (↥c.H0)) :
    scalarProduct (↥(c.S : Subgroup G) × ↥c.B)
        (deltaSB c h12 hS4 ν) (muHatSB c h12 μ) =
      ((Nat.card (↥(c.S : Subgroup G)) * Nat.card (↥c.B) : ℂ)⁻¹) *
        (∑ s : ↥(c.S : Subgroup G), ∑ b : ↥c.B,
          deltaNu c h12 ν
            ((centralizerS_equiv_inv c hS4 (s, b) : ↥(centralizerS c)) : G) *
          star ((nuHat c h12 μ).1 b)) := by
  classical
  unfold scalarProduct
  rw [Nat.card_prod]
  rw [Nat.cast_mul]
  rw [Fintype.sum_prod_type]
  simp [deltaSB, muHatSB]

/-- On the representative cosets, `δν(r·t·r⁻¹·b) = 4ν(r⁻¹·b·r)`. -/
private lemma deltaNu_at_rep_mul_B (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {ν : Irr (↥c.H0)} (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1) (i : Fin 3) (b : ↥c.B) :
    deltaNu c h12 ν
        ((normalizerReps c hS4 i * c.t * (normalizerReps c hS4 i)⁻¹) * (b : G)) =
      4 * nuRepB c h12 hS4 ν i b := by
  have h := deltaNu_at_conj_involution_mul_B c h12 hSC hS4 hνs hνt
    (normalizerReps_mem c hS4 i) b.2
  simpa [nuRepB] using h

set_option backward.isDefEq.respectTransparency false in
/-- The double sum over `S × B` reduces to four times the sum over the three
representative cosets: the identity coset contributes zero, and each of the
three nonidentity elements of `S` is `rᵢ·t·rᵢ⁻¹`. -/
private lemma sum_deltaSB_eq_four_sum (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {ν : Irr (↥c.H0)} (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1) (μ : Irr (↥c.H0)) :
    (∑ s : ↥(c.S : Subgroup G), ∑ b : ↥c.B,
          deltaNu c h12 ν
            ((centralizerS_equiv_inv c hS4 (s, b) : ↥(centralizerS c)) : G) *
          star ((nuHat c h12 μ).1 b)) =
      4 * (∑ i : Fin 3, ∑ b : ↥c.B,
          nuRepB c h12 hS4 ν i b * star ((nuHat c h12 μ).1 b)) := by
  classical
  let F : ↥(c.S : Subgroup G) → ↥c.B → ℂ := fun s b =>
    deltaNu c h12 ν
      ((centralizerS_equiv_inv c hS4 (s, b) : ↥(centralizerS c)) : G) *
    star ((nuHat c h12 μ).1 b)
  have hsumS : (∑ s : ↥(c.S : Subgroup G), ∑ b : ↥c.B, F s b) =
      ∑ o : Option (Fin 3), ∑ b : ↥c.B,
        F (S_equiv_option c hS4 o) b := by
    exact (Fintype.sum_equiv (S_equiv_option c hS4)
      (fun o : Option (Fin 3) => ∑ b : ↥c.B,
        F (S_equiv_option c hS4 o) b)
      (fun s : ↥(c.S : Subgroup G) => ∑ b : ↥c.B, F s b)
      (by intro o; rfl)).symm
  rw [hsumS]
  rw [Fintype.sum_option]
  have hnone : (∑ b : ↥c.B, F (S_equiv_option c hS4 none) b) = 0 := by
    apply Finset.sum_eq_zero
    intro b hb
    have h1 : deltaNu c h12 ν
        ((centralizerS_equiv_inv c hS4 ((S_equiv_option c hS4 none), b)
          : ↥(centralizerS c)) : G) = 0 := by
      have hs : ((S_equiv_option c hS4 none : ↥(c.S : Subgroup G)) : G) = 1 := by
        rfl
      have harg : ((centralizerS_equiv_inv c hS4 ((S_equiv_option c hS4 none), b)
          : ↥(centralizerS c)) : G) = (b : G) := by
        -- product decomposition: s*b with s=1 is b
        simp [centralizerS_equiv_inv, hs]
      rw [harg]
      exact deltaNu_zero_on_B c h12 hSC hS4 hνs hνt b.2
    simp [F, h1]
  rw [hnone, zero_add]
  -- for each i, the summand is 4 times the `B`-sum
  have hsome : ∀ i : Fin 3,
      (∑ b : ↥c.B, F (S_equiv_option c hS4 (some i)) b) =
        4 * (∑ b : ↥c.B,
          nuRepB c h12 hS4 ν i b * star ((nuHat c h12 μ).1 b)) := by
    intro i
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro b hb
    have harg : ((S_equiv_option c hS4 (some i) : ↥(c.S : Subgroup G)) : G) =
        normalizerReps c hS4 i * c.t * (normalizerReps c hS4 i)⁻¹ := by
      change (((S_nonzero_enum c hS4).symm i : ↥(c.S : Subgroup G)) : G) =
        normalizerReps c hS4 i * c.t * (normalizerReps c hS4 i)⁻¹
      exact (normalizerReps_conj_t c hS4 i).symm
    have hδ : deltaNu c h12 ν
        ((centralizerS_equiv_inv c hS4 ((S_equiv_option c hS4 (some i)), b)
          : ↥(centralizerS c)) : G) = 4 * nuRepB c h12 hS4 ν i b := by
      have harg' : ((centralizerS_equiv_inv c hS4
          ((S_equiv_option c hS4 (some i)), b) : ↥(centralizerS c)) : G) =
          (normalizerReps c hS4 i * c.t * (normalizerReps c hS4 i)⁻¹) * (b : G) := by
        simp [centralizerS_equiv_inv, harg]
      rw [harg']
      exact deltaNu_at_rep_mul_B c h12 hSC hS4 hνs hνt i b
    have hEq : deltaNu c h12 ν
        ((centralizerS_equiv_inv c hS4 ((S_equiv_option c hS4 (some i)), b)
          : ↥(centralizerS c)) : G) *
        star ((nuHat c h12 μ).1 b) =
        (4 * nuRepB c h12 hS4 ν i b) * star ((nuHat c h12 μ).1 b) := by
      rw [hδ, mul_assoc]
    simpa [F, mul_assoc] using hEq
  rw [Finset.sum_congr rfl (by intro i hi; exact hsome i)]
  rw [Finset.mul_sum]

/-- The scalar product `(δν, μ')_G` is the sum over the three representative
cosets of the unnormalized `B`-scalar products. -/
private lemma scalarProduct_delta_muPrime_eq_sum (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {ν : Irr (↥c.H0)} (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1) (μ : Irr (↥c.H0)) :
    scalarProduct G (deltaNu c h12 ν) (lemma42_mu' c h12 hS4 μ) =
      ∑ i : Fin 3,
        scalarProduct (↥c.B) (nuRepB c h12 hS4 ν i) (nuHat c h12 μ).1 := by
  classical
  let sumB : ℂ := (∑ i : Fin 3, ∑ b : ↥c.B,
    nuRepB c h12 hS4 ν i b * star ((nuHat c h12 μ).1 b))
  have hB0 : (Nat.card (↥c.B) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := ↥c.B)).ne'
  calc
    scalarProduct G (deltaNu c h12 ν) (lemma42_mu' c h12 hS4 μ)
        = scalarProduct (↥(c.S : Subgroup G) × ↥c.B)
            (deltaSB c h12 hS4 ν) (muHatSB c h12 μ) :=
            scalarProduct_delta_muPrime_eq_SB c h12 hS4 ν μ
    _ = ((Nat.card (↥(c.S : Subgroup G)) * Nat.card (↥c.B) : ℂ)⁻¹) *
          (∑ s : ↥(c.S : Subgroup G), ∑ b : ↥c.B,
            deltaNu c h12 ν
              ((centralizerS_equiv_inv c hS4 (s, b) : ↥(centralizerS c)) : G) *
            star ((nuHat c h12 μ).1 b)) :=
            scalarProduct_SB_expand c h12 hS4 ν μ
    _ = ((Nat.card (↥(c.S : Subgroup G)) * Nat.card (↥c.B) : ℂ)⁻¹) *
          (4 * sumB) := by
          rw [sum_deltaSB_eq_four_sum c h12 hSC hS4 hνs hνt μ]
    _ = ((4 * Nat.card (↥c.B) : ℂ)⁻¹) * (4 * sumB) := by
          congr 1
          rw [hS4]
          norm_num
    _ = (Nat.card (↥c.B) : ℂ)⁻¹ * sumB := by
          field_simp [hB0]
    _ = ∑ i : Fin 3,
          scalarProduct (↥c.B) (nuRepB c h12 hS4 ν i) (nuHat c h12 μ).1 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          unfold scalarProduct
          rfl

/-- If `α` and `β` agree modulo `2` pointwise, then their scalar products
with an irreducible character agree modulo `2` (for a group of odd order). -/
private lemma scalarProduct_congr_of_congr {H : Type u} [Group H] [Fintype H]
    {α β γ : ClassFunction H}
    (hα : IsCharacter α) (hβ : IsCharacter β) (hγ : IsIrreducibleCharacter γ)
    (hαβ : ∀ x : H, CongruentModTwo (α x) (β x))
    (hHodd : Odd (Nat.card H)) :
    CongruentModTwo (scalarProduct H α γ) (scalarProduct H β γ) := by
  classical
  have hγchar : IsCharacter γ := isCharacter_of_isIrreducibleCharacter hγ
  rcases scalarProduct_irr_char_nat (χ := γ) (ψ := α) hγ hα with ⟨r, hr⟩
  rcases scalarProduct_irr_char_nat (χ := γ) (ψ := β) hγ hβ with ⟨m, hm⟩
  have hr' : (r : ℂ) = scalarProduct H α γ := by
    have hstar : star (scalarProduct H α γ) = (r : ℂ) := by
      simpa [hr] using (scalarProduct_conj α γ)
    calc
      (r : ℂ) = star (r : ℂ) := by simp
      _ = star (star (scalarProduct H α γ)) := by rw [← hstar]
      _ = scalarProduct H α γ := by simp
  have hm' : (m : ℂ) = scalarProduct H β γ := by
    have hstar : star (scalarProduct H β γ) = (m : ℂ) := by
      simpa [hm] using (scalarProduct_conj β γ)
    calc
      (m : ℂ) = star (m : ℂ) := by simp
      _ = star (star (scalarProduct H β γ)) := by rw [← hstar]
      _ = scalarProduct H β γ := by simp
  have hG0 : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  have hsum : (∑ x : H, (α x - β x) * star (γ x)) =
      (Nat.card H : ℂ) * (scalarProduct H α γ - scalarProduct H β γ) := by
    calc
      (∑ x : H, (α x - β x) * star (γ x))
          = (∑ x : H, α x * star (γ x)) -
              (∑ x : H, β x * star (γ x)) := by
              simp [sub_mul, Finset.sum_sub_distrib]
      _ = (Nat.card H : ℂ) * scalarProduct H α γ -
              (Nat.card H : ℂ) * scalarProduct H β γ := by
              unfold scalarProduct
              field_simp [hG0]
      _ = (Nat.card H : ℂ) * (scalarProduct H α γ - scalarProduct H β γ) := by ring
  have hterm : ∀ x : H, CongruentModTwo ((α x - β x) * star (γ x)) 0 := by
    intro x
    have hsub : CongruentModTwo (α x - β x) 0 := by
      simpa using (CongruentModTwo.sub (hαβ x) (CongruentModTwo.refl (β x)))
    have hstarInt : IsIntegral ℤ (star (γ x)) := by
      have hstar := star_char_eq_char_inv hγchar x
      rw [hstar]
      rcases hγ with ⟨n, ρ, hρ, rfl⟩
      exact character_value_isIntegral ρ (x⁻¹)
    exact CongruentModTwo.mul_zero_left hsub hstarInt
  have hsumCongr : CongruentModTwo (∑ x : H, (α x - β x) * star (γ x)) 0 :=
    CongruentModTwo.sum_zero hterm
  have hMain : CongruentModTwo
      ((Nat.card H : ℂ) * (scalarProduct H α γ - scalarProduct H β γ)) 0 := by
    exact (CongruentModTwo.of_eq hsum.symm).trans hsumCongr
  have hd : (r - m : ℤ) = scalarProduct H α γ - scalarProduct H β γ := by
    norm_num [hr', hm']
  have hMain' : CongruentModTwo ((Nat.card H : ℂ) * ((r - m : ℤ) : ℂ)) 0 := by
    simpa [hd] using hMain
  have hOdd : CongruentModTwo ((Nat.card H : ℂ) * ((r - m : ℤ) : ℂ))
      ((r - m : ℤ) : ℂ) :=
    CongruentModTwo.odd_mul_congr (n := Nat.card H) hHodd (isIntegral_intCast (r - m))
  have hdiff : CongruentModTwo (scalarProduct H α γ) (scalarProduct H β γ) := by
    have h0 : CongruentModTwo (((r - m : ℤ) : ℂ)) 0 :=
      hOdd.symm.trans hMain'
    have h01 : CongruentModTwo (scalarProduct H α γ - scalarProduct H β γ) 0 := by
      exact (CongruentModTwo.of_eq hd.symm).trans h0
    have htmp := CongruentModTwo.add h01 (CongruentModTwo.refl (scalarProduct H β γ))
    have htmp' : CongruentModTwo (0 + scalarProduct H β γ) (scalarProduct H β γ) := by
      simpa using (CongruentModTwo.refl (scalarProduct H β γ))
    exact (CongruentModTwo.of_eq (by ring : scalarProduct H α γ =
        scalarProduct H α γ - scalarProduct H β γ + scalarProduct H β γ)).trans
      (htmp.trans htmp')
  exact hdiff

/-- `|B|` is odd. -/
private lemma B_card_odd (c : Hyp11 G) : Odd (Nat.card (↥c.B)) := by
  have hEq : Nat.card (↥c.B) = Nat.card (↥(fixedSubgroup (c.S : Subgroup G) c.U)) :=
    Nat.card_congr (B_fixedSubgroup_equiv c).toEquiv
  have hdiv : Nat.card (↥(fixedSubgroup (c.S : Subgroup G) c.U)) ∣ Nat.card (↥c.U) :=
    Subgroup.card_subgroup_dvd_card (fixedSubgroup (c.S : Subgroup G) c.U)
  have hcop : Nat.Coprime 2 (Nat.card (↥c.B)) := by
    rw [hEq]
    exact Nat.Coprime.of_dvd_right hdiv (U_coprime_two c)
  exact (Nat.coprime_two_left.mp hcop)

/-- The scalar product `(δν, μ')_G` is odd exactly when one of the three
normalizer conjugates of `ν̂` equals `μ̂`. -/
private lemma lemma42_scalarProduct_parity (c : Hyp11 G) (h12 : Hyp12 c)
    (hSC : Section3Hyp c) (hS4 : Section4Hyp c)
    {ν : Irr (↥c.H0)} (hνs : conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1)
    (hνt : ν.1 (tH0 c) = ν.1 1) (μ : Irr (↥c.H0)) :
    (∃ n : ℤ, (n : ℂ) = scalarProduct G (deltaNu c h12 ν) (lemma42_mu' c h12 hS4 μ) ∧ Odd n) ↔
      ∃ i : Fin 3, conjNuHatB c h12 hS4 ν i = nuHat c h12 μ := by
  classical
  let P : Fin 3 → Prop := fun i => conjNuHatB c h12 hS4 ν i = nuHat c h12 μ
  let S : ℂ := ∑ i : Fin 3,
    scalarProduct (↥c.B) (nuRepB c h12 hS4 ν i) (nuHat c h12 μ).1
  let C : ℤ := ∑ i : Fin 3, if P i then (1 : ℤ) else 0
  have hS : scalarProduct G (deltaNu c h12 ν) (lemma42_mu' c h12 hS4 μ) = S :=
    scalarProduct_delta_muPrime_eq_sum c h12 hSC hS4 hνs hνt μ
  have hsp_congr : ∀ i : Fin 3,
      CongruentModTwo
        (scalarProduct (↥c.B) (nuRepB c h12 hS4 ν i) (nuHat c h12 μ).1)
        (if P i then (1 : ℂ) else 0) := by
    intro i
    have hchar : IsCharacter (nuRepB c h12 hS4 ν i) := nuRepB_isCharacter c h12 hS4 ν i
    have hβchar : IsCharacter (conjNuHatB c h12 hS4 ν i).1 :=
      isCharacter_of_isIrreducibleCharacter (conjNuHatB c h12 hS4 ν i).2
    have hγ : IsIrreducibleCharacter (nuHat c h12 μ).1 := (nuHat c h12 μ).2
    have hcong := scalarProduct_congr_of_congr (H := ↥c.B) hchar hβchar hγ
      (nuRepB_congr c h12 hSC hS4 hνs hνt i) (B_card_odd c)
    have hite : scalarProduct (↥c.B) (conjNuHatB c h12 hS4 ν i).1 (nuHat c h12 μ).1 =
        if (conjNuHatB c h12 hS4 ν i).1 = (nuHat c h12 μ).1 then (1 : ℂ) else 0 :=
      scalarProduct_irr_ite (conjNuHatB c h12 hS4 ν i).2 (nuHat c h12 μ).2
    have hite' : scalarProduct (↥c.B) (conjNuHatB c h12 hS4 ν i).1 (nuHat c h12 μ).1 =
        if P i then (1 : ℂ) else 0 := by
      rw [hite]
      congr 1
      exact propext ((Subtype.ext_iff (a1 := conjNuHatB c h12 hS4 ν i)
        (a2 := nuHat c h12 μ)).symm)
    simpa [hite'] using hcong
  have hsum_congr : CongruentModTwo S ((C : ℤ) : ℂ) := by
    dsimp [S, C]
    change CongruentModTwo
      (∑ i : Fin 3, scalarProduct (↥c.B) (nuRepB c h12 hS4 ν i) (nuHat c h12 μ).1)
      ((Int.castRingHom ℂ) (∑ i : Fin 3, if P i then (1 : ℤ) else 0))
    rw [map_sum]
    refine CongruentModTwo.sum (fun i => ?_)
    simpa using hsp_congr i
  have hPpair : ∀ ⦃i j : Fin 3⦄, P i → P j → i = j ∨ (∀ k : Fin 3, P k) := by
    intro i j hi hj
    by_cases hij : i = j
    · exact Or.inl hij
    · have hEq : conjNuHatB c h12 hS4 ν i = conjNuHatB c h12 hS4 ν j := hi.trans hj.symm
      have hall := conjNuHatB_pair_eq_all c h12 hS4 ν hij hEq
      have hC1 : conjNuHatB c h12 hS4 ν 1 = nuHat c h12 μ := by
        fin_cases i
        · exact hall.1.symm.trans hi
        · exact hi
        · exact hall.2.trans hi
      refine Or.inr ?_
      intro k
      fin_cases k
      · exact hall.1.trans hC1
      · exact hC1
      · exact hall.2.symm.trans hC1
  have hCodd_iff : Odd C ↔ ∃ i, P i := by
    simpa [C] using (fin3_count_odd_iff (P := P) hPpair)
  constructor
  · rintro ⟨n, hnEq, hnOdd⟩
    have hnS : (n : ℂ) = S := hnEq.trans hS
    have hcongNC : CongruentModTwo ((n : ℂ)) ((C : ℤ) : ℂ) :=
      (CongruentModTwo.of_eq hnS).trans hsum_congr
    have hdvd : (2 : ℤ) ∣ n - C := CongruentModTwo.eq_of_int hcongNC
    have hCodd : Odd C := by
      rcases hdvd with ⟨k, hk⟩
      rcases hnOdd with ⟨t, ht⟩
      refine ⟨t - k, ?_⟩
      omega
    exact hCodd_iff.mp hCodd
  · rintro ⟨i, hi⟩
    have hCodd : Odd C := hCodd_iff.mpr ⟨i, hi⟩
    have hnat : ∀ i : Fin 3, ∃ r : ℕ,
        (r : ℂ) = scalarProduct (↥c.B) (nuRepB c h12 hS4 ν i) (nuHat c h12 μ).1 :=
      fun i => by
        rcases scalarProduct_irr_char_nat (χ := (nuHat c h12 μ).1)
          (ψ := nuRepB c h12 hS4 ν i) (nuHat c h12 μ).2
          (nuRepB_isCharacter c h12 hS4 ν i) with ⟨r, hr⟩
        refine ⟨r, ?_⟩
        calc
          (r : ℂ) = scalarProduct (↥c.B) (nuHat c h12 μ).1 (nuRepB c h12 hS4 ν i) := hr
          _ = star (scalarProduct (↥c.B) (nuHat c h12 μ).1 (nuRepB c h12 hS4 ν i)) := by
                rw [← hr]
                simp
          _ = scalarProduct (↥c.B) (nuRepB c h12 hS4 ν i) (nuHat c h12 μ).1 :=
                scalarProduct_conj (nuHat c h12 μ).1 (nuRepB c h12 hS4 ν i)
    choose r hri using hnat
    let N : ℤ := ∑ i : Fin 3, (r i : ℤ)
    have hN : (N : ℂ) = S := by
      dsimp [N, S]
      change ((Int.castRingHom ℂ) (∑ i : Fin 3, (r i : ℤ))) =
        ∑ i : Fin 3, scalarProduct (↥c.B) (nuRepB c h12 hS4 ν i) (nuHat c h12 μ).1
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      norm_num [hri i]
    have hcongNC : CongruentModTwo ((N : ℂ)) ((C : ℤ) : ℂ) :=
      (CongruentModTwo.of_eq hN).trans hsum_congr
    have hdvd : (2 : ℤ) ∣ N - C := CongruentModTwo.eq_of_int hcongNC
    have hNodd : Odd N := by
      rcases hdvd with ⟨k, hk⟩
      rcases hCodd with ⟨t, ht⟩
      refine ⟨t + k, ?_⟩
      omega
    refine ⟨N, hN.trans hS.symm, hNodd⟩

/-- Lemma 4.2: there is a character `μ'` of `G` whose scalar product with
`δν` is odd exactly when `ν̂` is `N_G(S)`-conjugate to `μ̂`.  The proof is
independent of `μ`'s behaviour under `s` and at `t`, so the statement takes
an arbitrary `μ : Irr(H0)`. -/
public theorem lemma_4_2 (c : Hyp11 G) (h12 : Hyp12 c) (hSC : Section3Hyp c)
    (hS4 : Section4Hyp c) [Fintype ↥(LambdaHom c.H0 c.U)] {μ : Irr (↥c.H0)} :
    ∃ μ' : ClassFunction G, IsCharacter μ' ∧
       ∀ ν : Irr (↥c.H0),
         conjChar c.H0 (s_normalizes_H0 c h12) ν.1 = ν.1 →
         ν.1 (tH0 c) = ν.1 1 →
         ((∃ n : ℤ, (n : ℂ) = scalarProduct G (deltaNu c h12 ν) μ' ∧ Odd n) ↔
           ∃ g : G, ∃ hg : g ∈ normalizerS c,
             conjIrrB c (B_conj_mem_of_normalizerS c hg) (nuHat c h12 ν) = nuHat c h12 μ) := by
  refine ⟨lemma42_mu' c h12 hS4 μ, lemma42_mu'_isCharacter c h12 hS4 μ, ?_⟩
  intro ν hνs hνt
  have hpar := lemma42_scalarProduct_parity c h12 hSC hS4 hνs hνt μ
  rw [hpar]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨(normalizerReps c hS4 i)⁻¹, normalizerReps_inv_mem c hS4 i, ?_⟩
    simpa [conjNuHatB] using hi
  · rintro ⟨g, hg, hEq⟩
    rcases exists_conjNuHatB_eq_of_normalizer c h12 hS4 hg ν with ⟨i, hEq'⟩
    exact ⟨i, hEq'.symm.trans hEq⟩

end Section4

end CFSG.BenderGlauberman
