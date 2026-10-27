module

public import CFSG.Quasithin.Background.F420Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6Out
public import Certificates.Certificate110

public section

namespace CFSG.Quasithin.F420

open CFSG.Open (quasithinIsSylowTwo)
open Equiv CFSG.Sporadic.Bridge

abbrev M11G : Type := ↥CFSG.Blueprint.NativeSporadic.M11

@[expose] def m11rWord : List (ℕ × Bool) :=
  [(0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true)]

@[expose] def m11rP : Perm (Fin 11) := wordProd M11.gen m11rWord

@[expose] def m11sP : Perm (Fin 11) := wordProd M11.gen [(0, true)]

@[expose] def m11r : M11G := ⟨m11rP, M11.nativeWord_mem _⟩

@[expose] def m11s : M11G := ⟨m11sP, M11.nativeWord_mem _⟩

theorem m11r_coe : (m11r : Perm (Fin 11)) = m11rP := rfl

theorem m11s_coe : (m11s : Perm (Fin 11)) = m11sP := rfl

theorem m11rP_pow_eight : m11rP ^ 8 = 1 := by decide +kernel

theorem m11sP_sq : m11sP ^ 2 = 1 := by decide +kernel

theorem m11sP_conj : m11sP * m11rP * m11sP⁻¹ = m11rP ^ 3 := by decide +kernel

theorem isPGroup_m11T : IsPGroup 2 (Subgroup.closure {m11r, m11s}) :=
  isPGroup_closure_pair (n := 3) (k := 3)
    (Subtype.ext (by rw [Subgroup.coe_pow, m11r_coe, Subgroup.coe_one]; exact m11rP_pow_eight))
    (Subtype.ext (by rw [Subgroup.coe_pow, m11s_coe, Subgroup.coe_one]; exact m11sP_sq))
    (Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, m11r_coe,
        m11s_coe]
      exact m11sP_conj))

theorem m11_check : ∀ c : Fin 11, (m11rP ^ 4) c ≠ c →
    (∀ j : Fin 8, ∀ k : Fin 8, m11sP ((m11rP ^ (j : ℕ)) 0) = (m11rP ^ (k : ℕ)) 0 →
      m11sP ((m11rP ^ (j : ℕ)) c) = (m11rP ^ (k : ℕ)) c) → c = 0 ∨ c = 2 := by
  decide +kernel

theorem m11_base : (m11rP ^ 0) 0 = 0 ∧ (m11rP ^ 6) 0 = 1 ∧ (m11rP ^ 4) 0 = 2 ∧
    (m11rP ^ 5) 0 = 3 := by
  decide +kernel

theorem apply_pow_of_commute {x : Perm (Fin 11)} (hx : x * m11rP = m11rP * x) (j : ℕ) :
    x ((m11rP ^ j) 0) = (m11rP ^ j) (x 0) := by
  have h : x * m11rP ^ j = m11rP ^ j * x := (Commute.pow_right hx j).eq
  exact congrFun (congrArg DFunLike.coe h) 0

theorem eq_one_of_commute_r
    {x : Perm (Fin 11)} (hxM : x ∈ CFSG.Blueprint.NativeSporadic.M11)
    (hx : x * m11rP = m11rP * x) (h0 : x 0 = 0) : x = 1 := by
  obtain ⟨b0, b1, b2, b3⟩ := m11_base
  have hfix : ∀ j : ℕ, x ((m11rP ^ j) 0) = (m11rP ^ j) 0 := by
    intro j
    rw [apply_pow_of_commute hx j, h0]
  refine CFSG.QuasithinUnique.Unc25G2.m11_eq_one_of_fix_base hxM ?_ ?_ ?_ ?_
  · rw [← b0]; exact hfix 0
  · rw [← b1]; exact hfix 6
  · rw [← b2]; exact hfix 4
  · rw [← b3]; exact hfix 5

theorem centralizer_T_m11
    (x : M11G) (hr : x * m11r = m11r * x) (hs : x * m11s = m11s * x) :
    x = 1 ∨ x = m11r ^ 4 := by
  have hr' : (x : Perm (Fin 11)) * m11rP = m11rP * x := by
    have h := congrArg Subtype.val hr
    rw [Subgroup.coe_mul, Subgroup.coe_mul, m11r_coe] at h
    exact h
  have hs' : (x : Perm (Fin 11)) * m11sP = m11sP * x := by
    have h := congrArg Subtype.val hs
    rw [Subgroup.coe_mul, Subgroup.coe_mul, m11s_coe] at h
    exact h
  have happ := apply_pow_of_commute hr'
  have hmoved : (m11rP ^ 4) ((x : Perm (Fin 11)) 0) ≠ (x : Perm (Fin 11)) 0 := by
    intro h
    rw [← happ 4] at h
    have h2 := (x : Perm (Fin 11)).injective h
    rw [m11_base.2.2.1] at h2
    exact absurd h2 (by decide)
  have hcompat : ∀ j : Fin 8, ∀ k : Fin 8, m11sP ((m11rP ^ (j : ℕ)) 0) = (m11rP ^ (k : ℕ)) 0 →
      m11sP ((m11rP ^ (j : ℕ)) ((x : Perm (Fin 11)) 0)) =
        (m11rP ^ (k : ℕ)) ((x : Perm (Fin 11)) 0) := by
    intro j k hjk
    have h1 : (x : Perm (Fin 11)) (m11sP ((m11rP ^ (j : ℕ)) 0)) =
        m11sP ((x : Perm (Fin 11)) ((m11rP ^ (j : ℕ)) 0)) :=
      congrFun (congrArg DFunLike.coe hs') _
    rw [hjk, happ, happ] at h1
    exact h1.symm
  rcases m11_check _ hmoved hcompat with h0 | h2
  · left
    exact Subtype.ext (eq_one_of_commute_r x.2 hr' h0)
  · right
    set z : M11G := m11r ^ 4 with hz
    have hzc : ((z : M11G) : Perm (Fin 11)) = m11rP ^ 4 := by
      rw [hz, Subgroup.coe_pow, m11r_coe]
    have hzr : z * m11r = m11r * z := by
      rw [hz, ← pow_succ, ← pow_succ']
    have hyr : (z⁻¹ * x) * m11r = m11r * (z⁻¹ * x) := by
      calc z⁻¹ * x * m11r = z⁻¹ * (m11r * x) := by rw [mul_assoc, hr]
        _ = (z⁻¹ * m11r) * x := by group
        _ = (m11r * z⁻¹) * x := by rw [(Commute.inv_left hzr).eq]
        _ = m11r * (z⁻¹ * x) := by group
    have hyr' : ((z⁻¹ * x : M11G) : Perm (Fin 11)) * m11rP =
        m11rP * ((z⁻¹ * x : M11G) : Perm (Fin 11)) := by
      have h := congrArg Subtype.val hyr
      simp only [Subgroup.coe_mul, m11r_coe] at h ⊢
      exact h
    have hy0 : ((z⁻¹ * x : M11G) : Perm (Fin 11)) 0 = 0 := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply, h2, hzc, Perm.inv_eq_iff_eq,
        m11_base.2.2.1]
    have hy1 : z⁻¹ * x = 1 := Subtype.ext (eq_one_of_commute_r (z⁻¹ * x).2 hyr' hy0)
    rw [inv_mul_eq_one] at hy1
    exact hy1.symm

theorem smallCentralizerWitness_m11
    : SmallCentralizerWitness M11G := by
  refine ⟨Subgroup.closure {m11r, m11s}, m11r ^ 4, isPGroup_m11T, fun x hx => ?_⟩
  exact centralizer_T_m11 x (hx _ (Subgroup.subset_closure (Set.mem_insert _ _)))
    (hx _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))

theorem noFourCentralizing_m11 : NoFourCentralizing M11G := by
  have : Finite M11G := Nat.finite_of_card_ne_zero (by
    rw [CFSG.Semidihedral.GL2Recognition.card_nativeM11]
    norm_num)
  refine noFourCentralizing_of_inner (fun S _ α _ => ?_) smallCentralizerWitness_m11
  obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.Unc25G2.aut_inner α
  exact ⟨g⁻¹, fun y => by rw [hg, inv_inv]⟩

theorem center_m11_eq_bot : Subgroup.center M11G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_center_iff] at hx
  rcases centralizer_T_m11 x (hx m11r).symm (hx m11s).symm with h | h
  · exact h
  · exfalso
    let b : M11G := ⟨M11.gen 1, M11.gen_mem 1⟩
    have hb := congrArg Subtype.val (hx b)
    rw [h] at hb
    change M11.gen 1 * m11rP ^ 4 = m11rP ^ 4 * M11.gen 1 at hb
    exact absurd hb (by decide +kernel)

end CFSG.Quasithin.F420
