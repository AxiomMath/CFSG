module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Centralizer
import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Helpers

private theorem ggLieSU3Fixed_slTwo_scalars_subgroupOf_bot {K : Type} [Field K] [CharP K 2] :
    (LargeEvenScalars (Fin 2) K).subgroupOf (LargeEvenSLGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨c, hc⟩ := hg
  have hdet : Matrix.GeneralLinearGroup.det (g : GL (Fin 2) K) = 1 := g.2
  rw [← hc, Matrix.GeneralLinearGroup.det_scalar] at hdet
  simp only [Fintype.card_fin] at hdet
  have h1 : (c : K) ^ 2 = 1 := by simpa using congrArg Units.val hdet
  have h2 : ((c : K) - 1) ^ 2 = 0 := by
    have : ((c : K) - 1) ^ 2 = (c : K) ^ 2 - 2 * c + 1 := by ring
    have two0 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    rw [this, h1, two0]
    linear_combination two0
  have h3 : (c : K) = 1 := sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h2)
  have hc1 : c = 1 := Units.ext h3
  rw [hc1, map_one] at hc
  exact Subgroup.mem_bot.mpr (Subtype.ext hc.symm)

private theorem ggLieSU3Fixed_slTwo_projMk_injective {K : Type} [Field K] [CharP K 2] :
    Function.Injective (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)).ker :=
    MonoidHom.mem_ker.mpr hg
  rw [QuotientGroup.ker_mk', ggLieSU3Fixed_slTwo_scalars_subgroupOf_bot] at hmem
  exact Subgroup.mem_bot.mp hmem

private theorem ggLieSU3Fixed_slTwo_conj_mem {K : Type} [Field K] (A : GL (Fin 2) K)
    (h : ↥(LargeEvenSLGroup (Fin 2) K)) :
    A * (h : GL (Fin 2) K) * A⁻¹ ∈ LargeEvenSLGroup (Fin 2) K := by
  have hdet : Matrix.GeneralLinearGroup.det (h : GL (Fin 2) K) = 1 := h.2
  change Matrix.GeneralLinearGroup.det (A * (h : GL (Fin 2) K) * A⁻¹) = 1
  rw [map_mul, map_mul, map_inv, hdet, mul_one, mul_inv_cancel]

private theorem ggLieSU3Fixed_slTwo_hom_eq_one {H Q : Type} [Group H] [Group Q]
    (f : H →* Q) (hperf : commutator H = ⊤)
    (hcomm : ∀ a b : H, f a * f b = f b * f a) :
    f = 1 := by
  have hle : commutator H ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm a b
  have htop : f.ker = ⊤ := top_le_iff.mp (hperf ▸ hle)
  exact MonoidHom.ker_eq_top_iff.mp htop

end Helpers

theorem ggLieSU3Fixed_false_of_slTwo {X : Type} [Group X] [Finite X] (hX : commutator X = ⊤)
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X} (hl : GGAutLocal A δ J)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2)
    (θ : X ⧸ Subgroup.center X ≃* LargeEvenProj (LargeEvenSLGroup (Fin 2) K))
    (hInn : GGInducedInn A θ
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)) Set.univ)) :
    False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let SL : Subgroup (GL (Fin 2) K) := LargeEvenSLGroup (Fin 2) K
  let π : ↥SL →* LargeEvenProj SL := LargeEvenProjMk SL
  have hπinj : Function.Injective π := ggLieSU3Fixed_slTwo_projMk_injective
  obtain ⟨A₀, -, hA₀⟩ := hInn δ hl.2.1
  by_cases hsc : (A₀ : Matrix (Fin 2) (Fin 2) K) ∈ Set.range (Matrix.scalar (Fin 2))
  ·
    obtain ⟨c, hc⟩ := hsc
    have hcomm : ∀ g : GL (Fin 2) K, A₀ * g = g * A₀ := by
      intro g
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, ← hc]
      exact Matrix.scalar_comm c (fun r' => mul_comm c r') (g : Matrix (Fin 2) (Fin 2) K)
    have hphi : ∀ h : ↥SL, ggInducedAut θ δ (π h) = π h := by
      intro h
      let h' : ↥SL := ⟨A₀ * (h : GL (Fin 2) K) * A₀⁻¹,
        ggLieSU3Fixed_slTwo_conj_mem A₀ h⟩
      have hrel : (h' : GL (Fin 2) K) = A₀ * (h : GL (Fin 2) K) * A₀⁻¹ := rfl
      have hAh : ggInducedAut θ δ (π h) = π h' := hA₀ h h' hrel
      have hh' : h' = h := by
        apply Subtype.ext
        dsimp only [h']
        rw [hcomm (h : GL (Fin 2) K)]
        group
      rw [hh'] at hAh
      exact hAh
    have hφ1 : ggInducedAut θ δ = 1 := by
      ext r
      obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective
        ((LargeEvenScalars (Fin 2) K).subgroupOf SL) r
      rw [← hh]
      exact hphi h
    exact hl.2.2.1 (ggInducedAut_injective_of_perfect hX θ (by rw [hφ1, map_one]))
  ·
    haveI hCcomm : IsMulCommutative
        ↥(Subgroup.centralizer ({A₀} : Set (GL (Fin 2) K))) :=
      TauCeti.isMulCommutative_centralizer_of_notMem_range_scalar (g := A₀) hsc
    have hlift : ∀ j : ↥J, ∃ h : ↥SL,
        π h = θ (j : X ⧸ Subgroup.center X) ∧
          (h : GL (Fin 2) K) ∈ Subgroup.centralizer ({A₀} : Set (GL (Fin 2) K)) := by
      intro j
      obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective
        ((LargeEvenScalars (Fin 2) K).subgroupOf SL) (θ (j : X ⧸ Subgroup.center X))
      refine ⟨h, hh, ?_⟩
      have hfixj : δ (j : X) = (j : X) :=
        (mem_ggAutFixedSubgroup δ (j : X)).mp (hl.2.2.2.1.1 j.2)
      have hφh : ggInducedAut θ δ (π h) = π h := by
        rw [hh, ggInducedAut_apply, hfixj]
      let h' : ↥SL := ⟨A₀ * (h : GL (Fin 2) K) * A₀⁻¹,
        ggLieSU3Fixed_slTwo_conj_mem A₀ h⟩
      have hrel : (h' : GL (Fin 2) K) = A₀ * (h : GL (Fin 2) K) * A₀⁻¹ := rfl
      have hAh : ggInducedAut θ δ (π h) = π h' := hA₀ h h' hrel
      have heq : π h' = π h := by rw [← hAh, hφh]
      have hh' : h' = h := hπinj heq
      have hAh' : (h' : GL (Fin 2) K) = (h : GL (Fin 2) K) :=
        congrArg (fun x : ↥SL => (x : GL (Fin 2) K)) hh'
      have hmul : A₀ * (h : GL (Fin 2) K) * A₀⁻¹ = (h : GL (Fin 2) K) := by
        rw [← hrel]; exact hAh'
      have hcommA₀ : A₀ * (h : GL (Fin 2) K) = (h : GL (Fin 2) K) * A₀ :=
        mul_inv_eq_iff_eq_mul.mp hmul
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hcommA₀
    let lift : ↥J → ↥SL := fun j => Classical.choose (hlift j)
    have lift_spec : ∀ j : ↥J,
        π (lift j) = θ (j : X ⧸ Subgroup.center X) ∧
          (lift j : GL (Fin 2) K) ∈ Subgroup.centralizer ({A₀} : Set (GL (Fin 2) K)) :=
      fun j => Classical.choose_spec (hlift j)
    have hcommlift : ∀ a b : ↥J, lift a * lift b = lift b * lift a := by
      intro a b
      apply Subtype.ext
      have h := mul_comm'
        (⟨(lift a : GL (Fin 2) K), (lift_spec a).2⟩ :
          ↥(Subgroup.centralizer ({A₀} : Set (GL (Fin 2) K))))
        (⟨(lift b : GL (Fin 2) K), (lift_spec b).2⟩ :
          ↥(Subgroup.centralizer ({A₀} : Set (GL (Fin 2) K))))
      simpa using congrArg
        (fun x : ↥(Subgroup.centralizer ({A₀} : Set (GL (Fin 2) K))) =>
          (x : GL (Fin 2) K)) h
    let f : ↥J →* X ⧸ Subgroup.center X :=
      (QuotientGroup.mk' (Subgroup.center X)).comp J.subtype
    have hf_comm : ∀ a b : ↥J, f a * f b = f b * f a := by
      intro a b
      have hfa : θ (f a) = π (lift a) := ((lift_spec a).1).symm
      have hfb : θ (f b) = π (lift b) := ((lift_spec b).1).symm
      apply θ.injective
      calc θ (f a * f b) = θ (f a) * θ (f b) := by rw [map_mul]
        _ = π (lift a) * π (lift b) := by rw [hfa, hfb]
        _ = π (lift a * lift b) := by rw [map_mul]
        _ = π (lift b * lift a) := by rw [hcommlift a b]
        _ = π (lift b) * π (lift a) := by rw [map_mul]
        _ = θ (f b) * θ (f a) := by rw [hfb, hfa]
        _ = θ (f b * f a) := by rw [map_mul]
    have hf1 : f = 1 :=
      ggLieSU3Fixed_slTwo_hom_eq_one f hl.2.2.2.1.2.2.1 hf_comm
    have hJcenter : ∀ j : ↥J, (j : X) ∈ Subgroup.center X := by
      intro j
      have hfj : f j = 1 := by rw [hf1]; rfl
      exact (QuotientGroup.eq_one_iff (N := Subgroup.center X) (j : X)).mp hfj
    have hcentertop : Subgroup.center ↥J = ⊤ := by
      rw [eq_top_iff]
      intro j _
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp (hJcenter j)) (k : X)
    haveI : IsMulCommutative ↥J := Subgroup.center_eq_top_iff.mp hcentertop
    haveI : Subsingleton (↥J ⧸ Subgroup.center ↥J) :=
      QuotientGroup.subsingleton_iff.mpr hcentertop
    haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hl.2.2.2.1.2.2.2
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥J ⧸ Subgroup.center ↥J)
    exact hab (Subsingleton.elim a b)

end CFSG.StandardType
