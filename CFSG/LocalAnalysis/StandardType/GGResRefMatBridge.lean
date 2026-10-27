module

public import CFSG.LocalAnalysis.StandardType.GGResICellBasic

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option autoImplicit false

variable {p N : ℕ} [Fact p.Prime]

private def ggFBridgeAlpha (T : Fin N → Vector (ZMod p) (N + 1)) (k : Fin N) :
    Module.Dual (ZMod p) (Fin N → ZMod p) :=
  { toFun := fun v => ∑ l, (T k).get l.castSucc * v l
    map_add' := by
      intro a b
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro c v
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring }

private def ggFBridgeBasis (l : Fin N) : Fin N → ZMod p := Pi.single l 1

private theorem ggFBridgeAlpha_basis {T : Fin N → Vector (ZMod p) (N + 1)} (k : Fin N) :
    ggFBridgeAlpha (p := p) T k (ggFBridgeBasis (N := N) k) = (T k).get k.castSucc := by
  show (∑ l : Fin N, (T k).get l.castSucc * (ggFBridgeBasis (N := N) k) l) = _
  rw [Finset.sum_eq_single k]
  · simp [ggFBridgeBasis]
  · intro l _ hl
    rw [ggFBridgeBasis, Pi.single_eq_of_ne hl]
    simp
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private theorem ggFBridge_pi_apply (z : Vector (ZMod p) (N + 1)) (m : Fin N) :
    ggFPi (RingHom.id (ZMod p)) (ggFBridgeBasis (N := N)) 0 z m = z.get m.castSucc := by
  classical
  rw [ggFPi]
  simp only [RingHom.id_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    smul_zero, add_zero]
  rw [Finset.sum_eq_single m]
  · simp [ggFBridgeBasis]
  · intro l _ hl
    rw [ggFBridgeBasis, Pi.single_eq_of_ne' hl]
    simp
  · intro hm
    exact absurd (Finset.mem_univ m) hm

private theorem ggFBridge_table {T : Fin N → Vector (ZMod p) (N + 1)}
    (hx : ∀ k, (T k).get (Fin.last N) = 0) :
    GGFTable (RingHom.id (ZMod p)) T (ggFBridgeBasis (N := N)) 0
      (ggFBridgeAlpha (p := p) T) := by
  constructor
  · intro k l
    show (∑ i : Fin N, (T k).get i.castSucc * (ggFBridgeBasis (N := N) l) i) =
      (RingHom.id (ZMod p)) ((T k).get l.castSucc)
    rw [Finset.sum_eq_single l]
    · simp [ggFBridgeBasis]
    · intro i _ hi
      rw [ggFBridgeBasis, Pi.single_eq_of_ne' (Ne.symm hi)]
      simp
    · intro hl
      exact absurd (Finset.mem_univ l) hl
  · intro k
    show (∑ i : Fin N, (T k).get i.castSucc * (0 : Fin N → ZMod p) i) =
      (RingHom.id (ZMod p)) ((T k).get (Fin.last N))
    simp [hx k]

private def ggFBridgeRefl {T : Fin N → Vector (ZMod p) (N + 1)} (k : Fin N) :
    (Fin N → ZMod p) →ₗ[ZMod p] (Fin N → ZMod p) :=
  LinearMap.transvection (-(ggFBridgeAlpha (p := p) T k)) (ggFBridgeBasis (N := N) k)

private theorem ggFBridgeRefl_apply {T : Fin N → Vector (ZMod p) (N + 1)} (k : Fin N)
    (w : Fin N → ZMod p) :
    ggFBridgeRefl (p := p) (T := T) k w =
      w - ggFBridgeAlpha (p := p) T k w • ggFBridgeBasis (N := N) k := by
  rw [ggFBridgeRefl, LinearMap.transvection.apply]
  simp [sub_eq_add_neg]

private theorem ggFBridgeRefl_involutive {T : Fin N → Vector (ZMod p) (N + 1)}
    (h2 : ∀ k, (T k).get k.castSucc = 2) (k : Fin N) :
    Function.Involutive (ggFBridgeRefl (p := p) (T := T) k) := by
  intro w
  rw [ggFBridgeRefl_apply, ggFBridgeRefl_apply]
  have hαh : ggFBridgeAlpha (p := p) T k (ggFBridgeBasis (N := N) k) = 2 := by
    rw [ggFBridgeAlpha_basis, h2 k]
  simp only [map_sub, map_smul, hαh]
  module

private def ggFBridgeEquiv {T : Fin N → Vector (ZMod p) (N + 1)}
    (h2 : ∀ k, (T k).get k.castSucc = 2) (k : Fin N) :
    (Fin N → ZMod p) ≃ₗ[ZMod p] (Fin N → ZMod p) :=
  { toLinearMap := ggFBridgeRefl (p := p) (T := T) k
    invFun := ggFBridgeRefl (p := p) (T := T) k
    left_inv := ggFBridgeRefl_involutive (p := p) h2 k
    right_inv := ggFBridgeRefl_involutive (p := p) h2 k }

private theorem ggFBridgeEquiv_apply {T : Fin N → Vector (ZMod p) (N + 1)}
    (h2 : ∀ k, (T k).get k.castSucc = 2) (k : Fin N) (w : Fin N → ZMod p) :
    ggFBridgeEquiv (p := p) h2 k w =
      w - ggFBridgeAlpha (p := p) T k w • ggFBridgeBasis (N := N) k := by
  change ggFBridgeRefl (p := p) (T := T) k w = _
  exact ggFBridgeRefl_apply (p := p) k w

private theorem ggFBridge_conjWord_prod {T : Fin N → Vector (ZMod p) (N + 1)}
    (h2 : ∀ k, (T k).get k.castSucc = 2) (t : Fin N × List (Fin N)) :
    ((ggConjWord t).map (ggFBridgeEquiv (p := p) h2)).prod =
      (t.2.map (ggFBridgeEquiv (p := p) h2)).prod * ggFBridgeEquiv (p := p) h2 t.1 *
        ((t.2.map (ggFBridgeEquiv (p := p) h2)).prod)⁻¹ := by
  have hg : ∀ k w, ggFBridgeEquiv (p := p) h2 k w =
      w - ggFBridgeAlpha (p := p) T k w • ggFBridgeBasis (N := N) k :=
    ggFBridgeEquiv_apply (p := p) h2
  have h2a : ∀ k, ggFBridgeAlpha (p := p) T k (ggFBridgeBasis (N := N) k) = 2 := by
    intro k
    rw [ggFBridgeAlpha_basis, h2 k]
  rw [ggConjWord, List.map_append, List.prod_append, List.map_cons, List.prod_cons]
  rw [← ggF_word_inv hg h2a t.2]
  group

theorem ggFMat_conjWord_eq_ggFRefMat {T : Fin N → Vector (ZMod p) (N + 1)}
    (h2 : ∀ k, (T k).get k.castSucc = 2)
    (hx : ∀ k, (T k).get (Fin.last N) = 0) (t : Fin N × List (Fin N)) :
    ggFMat T (ggConjWord t) = ggFRefMat T t := by
  classical
  have hT : GGFTable (RingHom.id (ZMod p)) T (ggFBridgeBasis (N := N)) 0
      (ggFBridgeAlpha (p := p) T) := ggFBridge_table hx
  have h2a : ∀ k, ggFBridgeAlpha (p := p) T k (ggFBridgeBasis (N := N) k) = 2 := by
    intro k
    rw [ggFBridgeAlpha_basis, h2 k]
  have hg : ∀ k w, ggFBridgeEquiv (p := p) h2 k w =
      w - ggFBridgeAlpha (p := p) T k w • ggFBridgeBasis (N := N) k :=
    ggFBridgeEquiv_apply (p := p) h2
  rw [ggFRefMat_eq_map, ggFMat]
  refine List.map_congr_left fun l _ => ?_
  refine List.map_congr_left fun m _ => ?_
  have hconj := ggF_conj' hT hg h2a t (ggFBridgeBasis (N := N) l)
  have hword := ggFPi_word hT hg (ggConjWord t) (ggFUnit l.castSucc)
  rw [ggFPi_unit] at hword
  rw [ggFBridge_conjWord_prod h2 t] at hword
  rw [hword] at hconj
  rw [ggFFun_coroot hT] at hconj
  have hcoord := congrArg (fun v : Fin N → ZMod p => v m) hconj
  simp only [ggFBridge_pi_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hcoord
  simpa [ggFBridgeBasis, Pi.single_apply, ggFH, eq_comm, sub_eq_add_neg] using hcoord

theorem ggConjWord_cons {N : ℕ} (t : Fin N × List (Fin N)) (j : Fin N) :
    [j] ++ ggConjWord t ++ [j] = ggConjWord (t.1, j :: t.2) := by
  simp [ggConjWord, List.append_assoc]

end CFSG.StandardType
