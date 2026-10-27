module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CStmt
import CFSG.RankThree.GF2n.Stroth80.Sec311Conj
import CFSG.RankThree.GF2n.Stroth80.Sec711Step3
public import CFSG.RankThree.GF2n.Stroth80.Sec34TI
public import CFSG.RankThree.GF2n.Stroth80.Sec5Main
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace KS93

structure Hyp (hc : Ctx M Q Z B) (n : ℕ) (t r : G) (Z0 : Subgroup G) (s z : G) : Prop where
  hs : Sec9Hyp hc n t
  hr : Sec7A hc t r
  hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q
  hsc : StronglyClosedMod M Z0 (LB M Q B)
  hT1 : Sec9T1 M Q Z0 s z
  h1 : ∀ m ∈ M, conjSubgroup m B ⊔ Z ≤ Vt M (LB M Q B) B Z t →
    ∃ ρ ∈ Rt M (LB M Q B) t, conjSubgroup m B ⊔ Z = conjSubgroup ρ B ⊔ Z
  h2 : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅z * s * z⁻¹, v⁆ ∈ Z
  h3 : ∀ h ∈ M, LB M Q B ⊓ conjSubgroup h (LB M Q B) ≠ Q →
    Z0 ⊓ (LB M Q B ⊓ conjSubgroup h (LB M Q B)) ≠ Q
  hC : HS9.Centre95 hc t Z0

variable {hc : Ctx M Q Z B} {n : ℕ} {t r : G} {Z0 : Subgroup G} {s z : G}

namespace Hyp

variable (H : Hyp hc n t r Z0 s z)
include H

theorem z_mem : z ∈ M := H.hT1.z_mem

theorem s_mem : s ∈ Z0 := H.hT1.s_mem

theorem t_mem : t ∈ LB M Q B := H.hs.toSec5.mem

theorem Q_le : Q ≤ Z0 := hc.Q_le_centre H.t_mem H.hZ0

theorem Z0_le_LB : Z0 ≤ LB M Q B := fun _ hx => (H.hC.1 hx).1

theorem s_mem_LB : s ∈ LB M Q B := H.Z0_le_LB H.s_mem

theorem s_mem_M : s ∈ M := hc.LB_le_M H.s_mem_LB

theorem s_not_mem_Q : s ∉ Q := fun hsQ =>
  H.hT1.not_mem (H.Q_le (n12l3_normalizes_Q hc H.z_mem hsQ))

theorem conj_mem_Z0 {ρ : G} (hρ : ρ ∈ Rt M (LB M Q B) t) {x : G} (hx : x ∈ Z0) :
    ρ * x * ρ⁻¹ ∈ Z0 :=
  (Subgroup.mem_normalizer_iff.mp (H.hZ0.mem_normalizer
    (fun _ hρ' _ hy => n12l3_normalizes_Q hc (hc.Rt_le_M t hρ') hy) hρ) x).mp hx

theorem s_mem_LB_conj {ρ : G} (hρ : ρ ∈ Rt M (LB M Q B) t) :
    s ∈ conjSubgroup ρ (LB M Q B) := by
  rw [mem_conjSubgroup]
  have h := H.conj_mem_Z0 (inv_mem hρ) H.s_mem
  rw [inv_inv] at h
  exact H.Z0_le_LB h

theorem conj_LB_ne {ρ ρ' : G} (hρ : ρ ∈ Rt M (LB M Q B) t) (hρ' : ρ' ∈ Rt M (LB M Q B) t) :
    conjSubgroup (z * ρ) (LB M Q B) ≠ conjSubgroup ρ' (LB M Q B) := by
  intro heq
  have h1 : z * s * z⁻¹ ∈ conjSubgroup (z * ρ) (LB M Q B) := by
    rw [mem_conjSubgroup, show (z * ρ)⁻¹ * (z * s * z⁻¹) * (z * ρ) = ρ⁻¹ * s * ρ by group]
    exact mem_conjSubgroup.mp (H.s_mem_LB_conj hρ)
  rw [heq, mem_conjSubgroup] at h1
  have hρ'M : ρ' ∈ M := hc.Rt_le_M t hρ'
  have hg : ρ'⁻¹ * z ∈ M := M.mul_mem (M.inv_mem hρ'M) H.z_mem
  have e1 : (ρ'⁻¹ * z) * s * (ρ'⁻¹ * z)⁻¹ = ρ'⁻¹ * (z * s * z⁻¹) * ρ' := by group
  have h2 : (ρ'⁻¹ * z) * s * (ρ'⁻¹ * z)⁻¹ ∈ Z0 := H.hsc s H.s_mem _ hg (by rw [e1]; exact h1)
  have h3 := H.conj_mem_Z0 hρ' h2
  apply H.hT1.not_mem
  rwa [show ρ' * ((ρ'⁻¹ * z) * s * (ρ'⁻¹ * z)⁻¹) * ρ'⁻¹ = z * s * z⁻¹ by group] at h3

theorem not_conj_le {ρ : G} (hρ : ρ ∈ Rt M (LB M Q B) t) :
    ¬ conjSubgroup (z * ρ) B ≤ Vt M (LB M Q B) B Z t := by
  intro hle
  have hzρ : z * ρ ∈ M := M.mul_mem H.z_mem (hc.Rt_le_M t hρ)
  obtain ⟨ρ', hρ', heq⟩ := H.h1 _ hzρ (sup_le hle sec39_Z_le_Vt)
  exact H.conj_LB_ne hρ hρ' (hc.conj_LB_eq_of_conj_BZ hzρ (hc.Rt_le_M t hρ') heq)

theorem not_D_le : ¬ conjSubgroup z⁻¹ B ≤ Vt M (LB M Q B) B Z t := by
  intro hle
  obtain ⟨ρ, hρ, heq⟩ := H.h1 z⁻¹ (M.inv_mem H.z_mem) (sup_le hle sec39_Z_le_Vt)
  have hL := hc.conj_LB_eq_of_conj_BZ (M.inv_mem H.z_mem) (hc.Rt_le_M t hρ) heq
  apply H.conj_LB_ne hρ (Subgroup.one_mem _)
  rw [conjSubgroup_one, conjSubgroup_mul, ← hL, ← conjSubgroup_mul, mul_inv_cancel,
    conjSubgroup_one]

theorem hcD : Ctx M Q Z (conjSubgroup z⁻¹ B) := hc.conj_of_mem (M.inv_mem H.z_mem)

theorem comm_conj {x : G} (hx : x ∈ conjSubgroup z⁻¹ (Vt M (LB M Q B) B Z t)) :
    ⁅s, x⁆ ∈ Z := by
  rw [mem_conjSubgroup, inv_inv] at hx
  have h := H.h2 _ hx
  have e : ⁅s, x⁆ = z⁻¹ * ⁅z * s * z⁻¹, z * x * z⁻¹⁆ * z⁻¹⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem H.z_mem)) _).mp h

theorem conj_D_le : conjSubgroup s (conjSubgroup z⁻¹ B) ≤ conjSubgroup z⁻¹ B ⊔ Z := by
  intro y hy
  rw [mem_conjSubgroup] at hy
  have hdV : s⁻¹ * y * s ∈ conjSubgroup z⁻¹ (Vt M (LB M Q B) B Z t) := by
    rw [mem_conjSubgroup] at hy ⊢
    exact hc.B_le_Vt H.t_mem hy
  have e : y = ⁅s, s⁻¹ * y * s⁆ * (s⁻¹ * y * s) := by simp only [commutatorElement_def]; group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (H.comm_conj hdV)) (Subgroup.mem_sup_left hy)

theorem conj_LD :
    conjSubgroup s (LB M Q (conjSubgroup z⁻¹ B)) = LB M Q (conjSubgroup z⁻¹ B) :=
  H.hcD.conj_LB_eq_of_le_sup_Z H.s_mem_M H.conj_D_le

theorem conj_QQBD {x : G} (hx : x ∈ Q ⊓ QB (conjSubgroup z⁻¹ B)) :
    s * x * s⁻¹ ∈ Q ⊓ QB (conjSubgroup z⁻¹ B) := by
  set D := conjSubgroup z⁻¹ B with hD
  have hcD : Ctx M Q Z D := H.hcD
  have hle : conjSubgroup s D ≤ Z ⊔ D := by rw [sup_comm]; exact H.conj_D_le
  obtain ⟨p, hpQ, hp⟩ := hcD.exists_conj_of_le_ZB (hcD.conj_of_mem H.s_mem_M) hle
  have hQB : QB (conjSubgroup (p⁻¹ * s) D) = QB D := by
    rw [conjSubgroup_mul, ← hp, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  rw [QB_conj] at hQB
  have hpM : p ∈ M := hc.hyp.Q_normal.1 hpQ
  have hy : (p⁻¹ * s) * x * (p⁻¹ * s)⁻¹ ∈ QB D := by
    rw [← hQB, mem_conjSubgroup,
      show (p⁻¹ * s)⁻¹ * ((p⁻¹ * s) * x * (p⁻¹ * s)⁻¹) * (p⁻¹ * s) = x by group]
    exact hx.2
  have hyQ : (p⁻¹ * s) * x * (p⁻¹ * s)⁻¹ ∈ Q :=
    n12l3_normalizes_Q hc (M.mul_mem (M.inv_mem hpM) H.s_mem_M) hx.1
  have e : s * x * s⁻¹ = ⁅p, (p⁻¹ * s) * x * (p⁻¹ * s)⁻¹⁆ * ((p⁻¹ * s) * x * (p⁻¹ * s)⁻¹) := by
    simp only [commutatorElement_def]; group
  have hZD : Z ≤ Q ⊓ QB D := le_inf hc.Z_le_Q hcD.Z_le_QB.1
  rw [e]
  exact (Q ⊓ QB D).mul_mem (hZD (hc.hyp.toHyp79.comm_mem_V hpQ hyQ)) ⟨hyQ, hy⟩

theorem inf_LB_eq_Q {ρ : G} (hρ : ρ ∈ Rt M (LB M Q B) t)
    (h6 : Z0 ⊓ conjSubgroup (z * ρ) (LB M Q B) ≤ Q) :
    LB M Q (conjSubgroup z⁻¹ B) ⊓ LB M Q (conjSubgroup ρ B) = Q := by
  have hρM : ρ ∈ M := hc.Rt_le_M t hρ
  have hzρ : z * ρ ∈ M := M.mul_mem H.z_mem hρM
  have hQL : Q ≤ LB M Q B := sec39_Q_le_LB
  have key : LB M Q B ⊓ conjSubgroup (z * ρ) (LB M Q B) = Q := by
    by_contra hne
    apply H.h3 _ hzρ hne
    refine le_antisymm (fun x hx => h6 ⟨hx.1, hx.2.2⟩) (le_inf H.Q_le (le_inf hQL ?_))
    intro x hx
    rw [mem_conjSubgroup]
    have h := n12l3_normalizes_Q hc (M.inv_mem hzρ) hx
    rw [inv_inv] at h
    exact hQL h
  rw [hc.LB_conj (M.inv_mem H.z_mem), hc.LB_conj hρM]
  have e : conjSubgroup ρ (LB M Q B) = conjSubgroup z⁻¹ (conjSubgroup (z * ρ) (LB M Q B)) := by
    rw [← conjSubgroup_mul, inv_mul_cancel_left]
  rw [e, ← conjSubgroup_inf, key, hc.conj_Q_eq (M.inv_mem H.z_mem)]

end Hyp

end KS93

end CFSG.RankThree.GF2n.Stroth80
