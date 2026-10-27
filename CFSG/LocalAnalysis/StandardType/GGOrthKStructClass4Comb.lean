module

public import CFSG.LocalAnalysis.StandardType.GGOrthKStructDefs
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen
import CFSG.LocalAnalysis.StandardType.GGOrthKStructClass4CombAux
import CFSG.LocalAnalysis.StandardType.GGOrthKStructClass4CombAux2
import CFSG.LocalAnalysis.StandardType.GGOrthKStructClass4CombAux3

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf CFSG.StandardType.SpJoin
  CFSG.LieType.Universal.SpecialLinear Matrix

theorem ggOrthKStruct_class4_comb {k : ℕ} (hk : k = 4) (h : ↥(spSignedGroup k 3))
    (hh : (h : Equiv.Perm (Fin k → Multiplicative (ZMod 3))) *
      (h : Equiv.Perm (Fin k → Multiplicative (ZMod 3))) = 1)
    (hfix : Nat.card {a : Fin k → Multiplicative (ZMod 3) //
      (h : Equiv.Perm (Fin k → Multiplicative (ZMod 3))) a = a} * 3 = 3 ^ k)
    (hcls : Nat.card {h' : ↥(spSignedGroup k 3) // IsConj h h'} = 4)
    (a : Fin k → Multiplicative (ZMod 3)) (ha : ∀ j, a j ≠ 1) :
    (h : Equiv.Perm (Fin k → Multiplicative (ZMod 3))) a ≠ a := by
  subst hk
  intro hha
  let T : Finset (Fin 4) := Finset.univ.filter (fun j => a j = Multiplicative.ofAdd 2)
  let d : okCl_Wsub := ⟨okCl_flip 4 3 T, okCl_flip_mem_spSignedGroup 4 3 T⟩
  have hd : (d : Equiv.Perm okCl_V) a = okCl_a0 := by
    funext t
    show okCl_flip 4 3 T a t = okCl_a0 t
    rw [okCl_flip_apply]
    by_cases ht : t ∈ T
    · rw [if_pos ht]
      have ht' : a t = Multiplicative.ofAdd 2 := by simpa [T] using ht
      rw [ht']
      exact okCl_ofAdd_two_inv.trans (okCl_a0_apply t).symm
    · rw [if_neg ht]
      have hne2 : a t ≠ Multiplicative.ofAdd 2 := by
        intro hc
        exact ht (by simpa [T] using hc)
      exact okCl_eq_of_ne_one_ne_two (a t) (ha t) hne2
  let h' : okCl_Wsub := d * h * d⁻¹
  have hconj : IsConj h h' := isConj_iff.mpr ⟨d, rfl⟩
  have hhW : h' * h' = 1 := by
    change d * h * d⁻¹ * (d * h * d⁻¹) = 1
    rw [show d * h * d⁻¹ * (d * h * d⁻¹) = d * (h * h) * d⁻¹ from by group,
      show h * h = 1 from
        Subtype.ext (by simpa only [Subgroup.coe_mul, Subgroup.coe_one] using hh)]
    group
  have hh' : (h' : Equiv.Perm okCl_V) * (h' : Equiv.Perm okCl_V) = 1 := by
    have := congrArg (fun x : okCl_Wsub => (x : Equiv.Perm okCl_V)) hhW
    simpa only [Subgroup.coe_mul, Subgroup.coe_one] using this
  have hfix27 : Nat.card {v : okCl_V // (h : Equiv.Perm okCl_V) v = v} = 27 := by
    have htrans : Nat.card {v : okCl_V // (h : Equiv.Perm okCl_V) v = v} =
        Nat.card {a : Fin 4 → Multiplicative (ZMod 3) //
          (h : Equiv.Perm (Fin 4 → Multiplicative (ZMod 3))) a = a} := rfl
    rw [htrans]
    have h81 : (3 : ℕ) ^ 4 = 81 := by norm_num
    rw [h81] at hfix
    omega
  have hfix' : Nat.card {v : okCl_V // (h' : Equiv.Perm okCl_V) v = v} = 27 := by
    have he : Nat.card {v : okCl_V // (h : Equiv.Perm okCl_V) v = v} =
        Nat.card {v : okCl_V // (h' : Equiv.Perm okCl_V) v = v} :=
      Nat.card_congr (Equiv.subtypeEquiv (d : Equiv.Perm okCl_V) (fun v => by
        show ((h : Equiv.Perm okCl_V) v = v) ↔
          ((h' : Equiv.Perm okCl_V) ((d : Equiv.Perm okCl_V) v) = (d : Equiv.Perm okCl_V) v)
        have hD : (h' : Equiv.Perm okCl_V) ((d : Equiv.Perm okCl_V) v) =
            (d : Equiv.Perm okCl_V) ((h : Equiv.Perm okCl_V) v) := by
          change ((d : Equiv.Perm okCl_V) * (h : Equiv.Perm okCl_V) *
              (d : Equiv.Perm okCl_V)⁻¹) ((d : Equiv.Perm okCl_V) v) =
            (d : Equiv.Perm okCl_V) ((h : Equiv.Perm okCl_V) v)
          rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
            Equiv.symm_apply_apply]
        rw [hD]
        constructor
        · intro hv
          rw [hv]
        · intro hv
          exact Equiv.injective (d : Equiv.Perm okCl_V) hv))
    rw [he.symm, hfix27]
  have hDinv : (d : Equiv.Perm okCl_V)⁻¹ okCl_a0 = a := by
    rw [Equiv.Perm.inv_def, ← hd, Equiv.symm_apply_apply]
  have h'a0 : (h' : Equiv.Perm okCl_V) okCl_a0 = okCl_a0 := by
    change ((d : Equiv.Perm okCl_V) * (h : Equiv.Perm okCl_V) *
        (d : Equiv.Perm okCl_V)⁻¹) okCl_a0 = okCl_a0
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hDinv, hha, hd]
  obtain ⟨π, s, hs⟩ := okCl_IsSigned_closure 4 3 h'.2
  have hsfalse : ∀ j, s j = false := by
    intro j
    have hval := hs okCl_a0 j
    rw [h'a0] at hval
    simp only [okCl_a0_apply, okCl_ofAdd_one_inv] at hval
    by_cases hsj : s j = true
    · exfalso
      rw [hsj] at hval
      simp at hval
      exact okCl_ofAdd_one_ne_two hval
    · cases h : s j
      · rfl
      · exact absurd h hsj
  have hcoord : (h' : Equiv.Perm okCl_V) = coordPerm 4 3 π := by
    ext v t
    have hthis := hs v (π.symm t)
    rw [hsfalse (π.symm t)] at hthis
    simp only [Bool.false_eq_true, if_false] at hthis
    rw [Equiv.apply_symm_apply] at hthis
    rw [hthis, coordPerm_apply]
  have hππ : π * π = 1 := by
    apply okCl_coordPerm_injective 4
    rw [okCl_coordPerm_mul, okCl_coordPerm_one, ← hcoord]
    exact hh'
  have hfixπnat : Nat.card {v : okCl_V // coordPerm 4 3 π v = v} = 27 := by
    rw [← hfix']
    exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl okCl_V) (fun v => by
      show (coordPerm 4 3 π v = v) ↔ ((h' : Equiv.Perm okCl_V) v = v)
      rw [hcoord]))
  have hfixπ : Fintype.card {v : okCl_V // coordPerm 4 3 π v = v} = 27 := by
    rw [← Nat.card_eq_fintype_card]
    exact hfixπnat
  obtain ⟨i, j, hij, hswap⟩ := okCl_classify_coordPerm π hππ hfixπ
  have hpi : (h' : Equiv.Perm okCl_V) = coordPerm 4 3 (Equiv.swap i j) := by
    rw [hcoord, hswap]
  obtain ⟨f, hf⟩ := okCl_class_bound hconj hij hpi
  have hle : Nat.card okCl_Idx ≤ Nat.card {x : okCl_Wsub // IsConj h x} :=
    Nat.card_le_card_of_injective f hf
  rw [okCl_idx_card, hcls] at hle
  omega

end CFSG.StandardType

end
