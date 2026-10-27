module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Aut
import CFSG.LocalAnalysis.UniquenessCase.UC22K148Vocab
import CFSG.LocalAnalysis.SteinbergCCSymplecticFourCenterFusion
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bTensor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K147SpU

open Subgroup
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

section Model

variable {K : Type} [Field K] [CharP K 2]

theorem exists_conj_commute_ne [Finite K] (hK : 2 < Nat.card K) {s : antiSp K} (hs : s * s = 1)
    (hs1 : s ≠ 1) : ∃ l : antiSp K, l * s * l⁻¹ ≠ s ∧ s * (l * s * l⁻¹) = l * s * l⁻¹ * s := by
  obtain ⟨g, b, c, hbc⟩ := SymplecticFourFusion.exists_conj_mem_center hs
  obtain ⟨x, hx0, hx1⟩ := X7b.exists_ne_zero_ne hK 1
  have hxx : x * x - 1 ≠ 0 := by
    intro h
    rcases _root_.mul_self_eq_one_iff.mp (sub_eq_zero.mp h) with h1 | h1
    · exact hx1 h1.symm
    · exact hx1 (h1.trans (CharTwo.neg_eq 1)).symm
  obtain ⟨d, hd⟩ : ∃ d : antiSp K, d * uElt 0 b c 0 * d⁻¹ = uElt 0 (x * x * b) (x ^ 2 * c) 0 := by
    refine ⟨Fin257.Sp4.dSp (Units.mk0 x hx0) (Units.mk0 x hx0), ?_⟩
    rw [Fin257.Sp4.dSp_conj_uElt]
    simp only [Units.val_mk0, mul_zero]
  have hconj : g⁻¹ * d * g * s * (g⁻¹ * d * g)⁻¹ = g⁻¹ * uElt 0 (x * x * b) (x ^ 2 * c) 0 * g := by
    rw [← hd, ← hbc]
    group
  have hs' : s = g⁻¹ * uElt 0 b c 0 * g := by
    rw [← hbc]
    group
  refine ⟨g⁻¹ * d * g, ?_, ?_⟩
  · rw [hconj]
    intro h
    have h2 : uElt 0 (x * x * b) (x ^ 2 * c) 0 = uElt (0 : K) b c 0 := by
      rw [← hbc, ← h]
      group
    obtain ⟨-, hb, hc, -⟩ := X7b.uElt_inj h2
    have hb0 : b = 0 := by
      have : (x * x - 1) * b = 0 := by linear_combination hb
      exact (mul_eq_zero.mp this).resolve_left hxx
    have hc0 : c = 0 := by
      have : (x * x - 1) * c = 0 := by linear_combination hc
      exact (mul_eq_zero.mp this).resolve_left hxx
    apply hs1
    rw [hs', hb0, hc0, X7b.uElt_zero_eq_one]
    group
  · rw [hconj, hs']
    have hcomm := antiUnipotentCenter_comm (⟨b, c, rfl⟩ : uElt (0 : K) b c 0 ∈ antiUnipotentCenter K)
      (uElt_mem_antiUnipotent 0 (x * x * b) (x ^ 2 * c) 0)
    calc g⁻¹ * uElt 0 b c 0 * g * (g⁻¹ * uElt 0 (x * x * b) (x ^ 2 * c) 0 * g)
        = g⁻¹ * (uElt 0 b c 0 * uElt 0 (x * x * b) (x ^ 2 * c) 0) * g := by group
      _ = g⁻¹ * (uElt 0 (x * x * b) (x ^ 2 * c) 0 * uElt 0 b c 0) * g := by rw [hcomm]
      _ = g⁻¹ * uElt 0 (x * x * b) (x ^ 2 * c) 0 * g * (g⁻¹ * uElt 0 b c 0 * g) := by group

theorem minorAut_pow_odd_lowUSp [Finite K] {n : ℕ} (hodd : Odd n) :
    (minorAut K ^ n) (X7b.lowUSp 0 1 0 0) = X7b.lowUSp 0 0 0 1 := by
  obtain ⟨m, rfl⟩ := hodd
  rw [X7b.minorAut_pow_two_mul_add_one_lowUSp]
  simp

theorem lowUSp_inv_mul_lowUSp :
    (X7b.lowUSp (0 : K) 0 0 1)⁻¹ * X7b.lowUSp 0 1 0 0 = X7b.lowUSp 0 1 0 1 := by
  rw [X7b.lowUSp_inv, X7b.lowUSp_mul]
  simp

theorem lowUSp_zero_one_zero_one_mul_self : X7b.lowUSp (0 : K) 1 0 1 * X7b.lowUSp 0 1 0 1 = 1 := by
  rw [X7b.lowUSp_mul, ← X7b.lowUSp_zero]
  have h : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero (1 : K)
  simp [h]

theorem lowUSp_zero_one_zero_one_ne_one : X7b.lowUSp (0 : K) 1 0 1 ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : antiSp K => glMat (g : GL (Fin 4) K) 2 0) h
  simp [X7b.glMat_lowUSp, X7b.lowU] at h1

theorem exists_involution_of_outer [Finite K] {n : ℕ} (hodd : Odd n) (c : antiSp K)
    {α : MulAut (antiSp K)} (hα : α = MulAut.conj c * minorAut K ^ n * (MulAut.conj c)⁻¹) :
    ∃ l : antiSp K, (α l)⁻¹ * l ≠ 1 ∧ (α l)⁻¹ * l * ((α l)⁻¹ * l) = 1 := by
  subst hα
  refine ⟨c * X7b.lowUSp 0 1 0 0 * c⁻¹, ?_⟩
  have h1 : (MulAut.conj c * minorAut K ^ n * (MulAut.conj c)⁻¹) (c * X7b.lowUSp 0 1 0 0 * c⁻¹) =
      c * X7b.lowUSp 0 0 0 1 * c⁻¹ := by
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply,
      show c⁻¹ * (c * X7b.lowUSp 0 1 0 0 * c⁻¹) * c = X7b.lowUSp 0 1 0 0 by group,
      minorAut_pow_odd_lowUSp hodd, MulAut.conj_apply]
  have h2 : (c * X7b.lowUSp (0 : K) 0 0 1 * c⁻¹)⁻¹ * (c * X7b.lowUSp 0 1 0 0 * c⁻¹) =
      c * X7b.lowUSp 0 1 0 1 * c⁻¹ := by
    rw [← lowUSp_inv_mul_lowUSp]
    group
  rw [h1, h2]
  refine ⟨fun h => lowUSp_zero_one_zero_one_ne_one (K := K) ?_, ?_⟩
  · calc X7b.lowUSp (0 : K) 1 0 1 = c⁻¹ * (c * X7b.lowUSp 0 1 0 1 * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group
  · rw [show c * X7b.lowUSp (0 : K) 1 0 1 * c⁻¹ * (c * X7b.lowUSp 0 1 0 1 * c⁻¹) =
        c * (X7b.lowUSp 0 1 0 1 * X7b.lowUSp 0 1 0 1) * c⁻¹ by group,
      lowUSp_zero_one_zero_one_mul_self, mul_one, mul_inv_cancel]

theorem exists_involution_of_aut [Finite K] {n : ℕ} (hn : 2 ≤ n) (hodd : Odd n)
    (hK : Nat.card K = 2 ^ n) (α : MulAut (antiSp K)) (hα : α * α = 1) (hα1 : α ≠ 1) :
    ∃ l : antiSp K, (α l)⁻¹ * l ≠ 1 ∧ (α l)⁻¹ * l * ((α l)⁻¹ * l) = 1 := by
  by_cases hinn : α ∈ inner (antiSp K)
  · obtain ⟨s, rfl⟩ := hinn
    have hs : s * s = 1 := X7b.conj_injective (by rw [map_mul, hα, map_one])
    have hs1 : s ≠ 1 := by
      rintro rfl
      exact hα1 (map_one _)
    have h2 : 2 < Nat.card K := by
      have := K148.four_le_card hn hK
      omega
    obtain ⟨l, hl1, hl2⟩ := exists_conj_commute_ne h2 hs hs1
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
    have key : (MulAut.conj s l⁻¹)⁻¹ * l⁻¹ = s * (l * s * l⁻¹) := by
      rw [MulAut.conj_apply]
      calc (s * l⁻¹ * s⁻¹)⁻¹ * l⁻¹ = s * l * s⁻¹ * l⁻¹ := by group
        _ = s * (l * s * l⁻¹) := by rw [hsinv]; group
    have hs' : l * s * l⁻¹ * (l * s * l⁻¹) = 1 := by
      rw [show l * s * l⁻¹ * (l * s * l⁻¹) = l * (s * s) * l⁻¹ by group, hs, mul_one, mul_inv_cancel]
    refine ⟨l⁻¹, ?_, ?_⟩
    · rw [key]
      intro h
      apply hl1
      rw [eq_inv_of_mul_eq_one_right h, hsinv]
    · rw [key]
      calc s * (l * s * l⁻¹) * (s * (l * s * l⁻¹)) = s * (l * s * l⁻¹ * s) * (l * s * l⁻¹) := by group
        _ = s * (s * (l * s * l⁻¹)) * (l * s * l⁻¹) := by rw [← hl2]
        _ = s * s * (l * s * l⁻¹ * (l * s * l⁻¹)) := by group
        _ = 1 := by rw [hs, hs', mul_one]
  · obtain ⟨c, hc⟩ := X7b.outer_involution_conj hn hK α hα hinn
    exact exists_involution_of_outer hodd c hc

end Model

variable {G : Type} [Group G]

theorem exists_mul_conj_involution {L : Subgroup G} {n : ℕ} (hSp : IsSp4 ↥L n) (hodd : Odd n) {t : G}
    (htN : t ∈ normalizer (L : Set G)) (ht : t * t = 1) (htc : ∃ x ∈ L, t * x ≠ x * t) :
    ∃ l ∈ L, t * (l⁻¹ * t * l) ∈ L ∧ t * (l⁻¹ * t * l) ≠ 1 ∧
      t * (l⁻¹ * t * l) * (t * (l⁻¹ * t * l)) = 1 := by
  obtain ⟨hn, K, _, _, _, hK, ⟨e⟩⟩ := K148.exists_antiSp_of_isSp4 hSp
  let b : ↥(normalizer (L : Set G)) := ⟨t, htN⟩
  let α : MulAut (antiSp K) := MulAut.congr e (K148.AutAux.condHom L b)
  have hαe : ∀ x : ↥L, α (e x) = e (K148.AutAux.condHom L b x) := fun x => by
    show e (K148.AutAux.condHom L b (e.symm (e x))) = _
    rw [MulEquiv.symm_apply_apply]
  have hαα : α * α = 1 := by
    show MulAut.congr e (K148.AutAux.condHom L b) * MulAut.congr e (K148.AutAux.condHom L b) = 1
    rw [← map_mul, ← map_mul, show b * b = 1 from Subtype.ext ht, map_one, map_one]
  have hα1 : α ≠ 1 := by
    obtain ⟨x, hx, hxt⟩ := htc
    intro h1
    apply hxt
    have h2 := hαe ⟨x, hx⟩
    rw [h1, MulAut.one_apply] at h2
    have h3 : x = t * x * t⁻¹ := by
      have := congrArg Subtype.val (e.injective h2)
      rwa [K148.AutAux.condHom_apply] at this
    calc t * x = t * x * t⁻¹ * t := by group
      _ = x * t := by rw [← h3]
  obtain ⟨l, hl1, hl2⟩ := exists_involution_of_aut hn hodd hK α hαα hα1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : e.symm (α l) = K148.AutAux.condHom L b (e.symm l) := by
    rw [MulEquiv.symm_apply_eq, ← hαe, MulEquiv.apply_symm_apply]
  have key : t * (((e.symm l : ↥L) : G)⁻¹ * t * (e.symm l : ↥L)) =
      ((e.symm ((α l)⁻¹ * l) : ↥L) : G) := by
    rw [map_mul e.symm, map_inv e.symm, h1, Subgroup.coe_mul, Subgroup.coe_inv,
      K148.AutAux.condHom_apply]
    show t * (((e.symm l : ↥L) : G)⁻¹ * t * (e.symm l : ↥L)) =
      (t * (e.symm l : ↥L) * t⁻¹)⁻¹ * (e.symm l : ↥L)
    simp only [mul_inv_rev, inv_inv, htinv]
    group
  refine ⟨(e.symm l : G), (e.symm l).2, ?_, ?_, ?_⟩
  · rw [key]
    exact (e.symm _).2
  · rw [key]
    intro h
    apply hl1
    have : e.symm ((α l)⁻¹ * l) = 1 := Subtype.ext h
    rwa [MulEquiv.map_eq_one_iff] at this
  · rw [key, ← Subgroup.coe_mul, ← map_mul, hl2, map_one, Subgroup.coe_one]

end CFSG.LocalAnalysis.UniquenessCase.UC22.K147SpU
