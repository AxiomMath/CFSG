module

public import CFSG.RankThree.CentralCover.SteinbergBNLinearTorus
public import CFSG.RankThree.PartOne.K159.CoverLift
public import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore

public section

namespace CFSG.RankThree.PartOne.K159

open Matrix CFSG.RankThree.Classical2 CFSG.RankThree.Classical CFSG.SectionRank.OddCover
  CFSG.RankThree.CentralCover
open scoped MatrixGroups

section Inv

variable {k : Type} [Field k] {p : ℕ} [NeZero p]

omit [NeZero p] in
theorem torusExp_single_comp_swap_last {m : ℕ} (j : Fin m) :
    torusExp (Pi.single j (1 : ZMod p)) ∘ Equiv.swap j.castSucc (Fin.last m) =
      torusExp (Pi.single j (-1 : ZMod p)) := by
  funext i
  refine Fin.lastCases ?_ (fun l => ?_) i
  · rw [Function.comp_apply, Equiv.swap_apply_right, torusExp_castSucc, torusExp_last,
      Finset.sum_pi_single']
    simp
  · rw [Function.comp_apply, torusExp_castSucc]
    by_cases hl : l = j
    · subst hl
      rw [Equiv.swap_apply_left, torusExp_last, Finset.sum_pi_single']
      simp
    · rw [Equiv.swap_apply_of_ne_of_ne (Fin.castSucc_injective m |>.ne hl)
        (Fin.castSucc_lt_last l).ne, torusExp_castSucc]
      simp [hl]

@[expose] noncomputable def invElem {m : ℕ} (j : Fin m) : SL(m + 1, k) :=
  ⟨((permGL (Equiv.swap j.castSucc (Fin.last m)) *
      diagHom (m + 1) (Function.update 1 (Fin.last m) (-1)) : GL (Fin (m + 1)) k) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) k), by
    rw [Units.val_mul, det_mul, det_permGL, det_diagHom,
      Equiv.Perm.sign_swap (Fin.castSucc_lt_last j).ne, prod_update_neg_one]
    simp⟩

theorem toGL_invElem {m : ℕ} (j : Fin m) :
    Matrix.SpecialLinearGroup.toGL (invElem (k := k) j) =
      permGL (Equiv.swap j.castSucc (Fin.last m)) *
        diagHom (m + 1) (Function.update 1 (Fin.last m) (-1)) := Units.ext rfl

theorem torusElem_neg (ζ : kˣ) (hζ : ζ ^ p = 1) {m : ℕ} (a : Fin m → ZMod p) :
    torusElem ζ hζ (-a) = (torusElem ζ hζ a)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← torusElem_add, neg_add_cancel, torusElem_zero]

theorem invElem_conj (ζ : kˣ) (hζ : ζ ^ p = 1) {m : ℕ} (j : Fin m) :
    invElem (k := k) j * torusElem ζ hζ (Pi.single j 1) * (invElem (k := k) j)⁻¹ =
      (torusElem ζ hζ (Pi.single j 1))⁻¹ := by
  rw [← torusElem_neg, ← Pi.single_neg]
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, map_inv, toGL_invElem, toGL_torusElem, toGL_torusElem, _root_.mul_inv_rev]
  set c : Fin (m + 1) → kˣ := Function.update 1 (Fin.last m) (-1)
  set σ := Equiv.swap j.castSucc (Fin.last m)
  have h1 : permGL σ * diagHom (m + 1) c * diagHom (m + 1) (torusEntries ζ hζ (Pi.single j 1)) *
      ((diagHom (m + 1) c)⁻¹ * (permGL σ)⁻¹) = permGL σ *
      (diagHom (m + 1) c * diagHom (m + 1) (torusEntries ζ hζ (Pi.single j 1)) *
        (diagHom (m + 1) c)⁻¹) * (permGL σ)⁻¹ := by group
  rw [h1, (diagHom_commute _ _).eq, mul_inv_cancel_right, permGL_mul_diagHom_mul_inv]
  congr 1
  rw [Equiv.symm_swap]
  funext i
  simp only [torusEntries, Function.comp_apply]
  rw [← torusExp_single_comp_swap_last j]
  rfl

end Inv

section Main

variable {k : Type} [Field k] {p : ℕ}

theorem exists_elemAbelian_psl {Y : Type*} [Group Y] [Finite Y] (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) {m : ℕ} (hm : 2 ≤ m)
    {φ : Y →* PSL(m + 1, k)} (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    (hodd : Odd (Nat.card φ.ker)) {z : Y} (hz : z ∈ φ.ker) (hz1 : z ≠ 1) (hzp : z ^ p = 1) :
    ∃ B : Subgroup Y, (∀ b ∈ B, b ^ p = 1) ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
      p ^ (m - (if p ∣ m + 1 then 1 else 0) + 1) ≤ Nat.card B := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨hDp, hF, hDcard⟩ := torusPSL_package (Y := Y) hp hp2 hζo hζ (by omega : 1 ≤ m) hφ hker
  set θ := torusPSL ζ hζ m with hθ
  set S : Set PSL(m + 1, k) := Set.range fun j : Fin m => θ (Multiplicative.ofAdd (Pi.single j 1))
    with hS
  have hcl : Subgroup.closure S = θ.range := by
    have h1 : (Subgroup.closure (Set.range fun j : Fin m =>
        (Multiplicative.ofAdd (Pi.single j (1 : ZMod p)) :
          Multiplicative (Fin m → ZMod p)))).map θ = Subgroup.closure S := by
      rw [MonoidHom.map_closure, hS, ← Set.range_comp]
      rfl
    rw [← h1, closure_range_ofAdd_single, ← MonoidHom.range_eq_map]
  have hSp : ∀ s ∈ S, s ^ p = 1 := fun s hs => hDp s (by
    rw [← hcl]
    exact Subgroup.subset_closure hs)
  have hSinv : ∀ s ∈ S, ∃ g : PSL(m + 1, k), g * s * g⁻¹ = s⁻¹ := by
    rintro _ ⟨j, rfl⟩
    refine ⟨QuotientGroup.mk' _ (invElem j), ?_⟩
    have h1 : θ (Multiplicative.ofAdd (Pi.single j 1)) =
        QuotientGroup.mk' (Subgroup.center SL(m + 1, k)) (torusElem ζ hζ (Pi.single j 1)) := rfl
    show QuotientGroup.mk' _ (invElem j) * θ (Multiplicative.ofAdd (Pi.single j 1)) *
      (QuotientGroup.mk' _ (invElem j))⁻¹ = (θ (Multiplicative.ofAdd (Pi.single j 1)))⁻¹
    rw [h1, ← map_inv, ← map_inv, ← map_mul, ← map_mul, invElem_conj ζ hζ j]
  have hF' : ∀ x ∈ (Subgroup.closure S).comap φ, ∀ y ∈ (Subgroup.closure S).comap φ,
      x * y = y * x := by
    rw [hcl]
    exact hF
  obtain ⟨B, hBp, hBc, hBcard⟩ := exists_elemAbelian_card_ge hφ hker hodd hp S hSp hSinv hF' hz hz1
    hzp
  refine ⟨B, hBp, hBc, ?_⟩
  rw [hcl] at hBcard
  calc p ^ (m - (if p ∣ m + 1 then 1 else 0) + 1)
      = p * p ^ (m - (if p ∣ m + 1 then 1 else 0)) := by rw [pow_succ, mul_comm]
    _ ≤ p * Nat.card θ.range := Nat.mul_le_mul_left _ hDcard
    _ ≤ Nat.card B := hBcard

end Main

end CFSG.RankThree.PartOne.K159
