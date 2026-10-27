module

public import CFSG.RankThree.PartOne.N143.TorusLift
public import CFSG.RankThree.PartOne.K159.CoverPSL

public section

namespace CFSG.RankThree.PartOne.N143

open Matrix CFSG.RankThree.CentralCover CFSG.RankThree.PartOne.K159
open CFSG.Assembly.RankThreeEven (localRank)
open scoped MatrixGroups

@[expose] def shiftHom (p r : ℕ) :
    Multiplicative (Fin r → ZMod p) →* Multiplicative (Fin (r + 2) → ZMod p) where
  toFun a := Multiplicative.ofAdd fun i =>
    if h : 2 ≤ i.val then Multiplicative.toAdd a ⟨i.val - 2, by omega⟩ else 0
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    funext i
    by_cases h : 2 ≤ i.val <;> simp [h]

theorem shiftHom_apply {p r : ℕ} (a : Multiplicative (Fin r → ZMod p)) (i : Fin (r + 2)) :
    Multiplicative.toAdd (shiftHom p r a) i =
      if h : 2 ≤ i.val then Multiplicative.toAdd a ⟨i.val - 2, by omega⟩ else 0 := rfl

theorem shiftHom_single {p r : ℕ} (j : Fin r) :
    shiftHom p r (Multiplicative.ofAdd (Pi.single j 1)) =
      Multiplicative.ofAdd (Pi.single (⟨j.val + 2, by omega⟩ : Fin (r + 2)) (1 : ZMod p)) := by
  apply Multiplicative.toAdd.injective
  funext i
  rw [shiftHom_apply]
  by_cases h : 2 ≤ i.val
  · simp only [h, dite_true, toAdd_ofAdd, Pi.single_apply]
    have : (⟨i.val - 2, by omega⟩ : Fin r) = j ↔ i = (⟨j.val + 2, by omega⟩ : Fin (r + 2)) := by
      simp only [Fin.ext_iff]
      omega
    simp only [this]
  · simp only [h, dite_false, toAdd_ofAdd, Pi.single_apply]
    have : i ≠ (⟨j.val + 2, by omega⟩ : Fin (r + 2)) := by
      intro hh
      apply h
      rw [hh]
      show 2 ≤ j.val + 2
      omega
    simp [this]

variable {k : Type} [Field k]

theorem succ_le_localRank_psl_even [CharP k 2] {Y : Type} [Group Y] [Finite Y] {ζ : kˣ}
    (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) {r : ℕ} (φ : Y →* PSL(r + 2 + 1, k))
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    (h3 : 3 ∣ Nat.card φ.ker) : r + 1 ≤ localRank 3 Y := by
  classical
  set θ0 : Multiplicative (Fin r → ZMod 3) →* PSL(r + 2 + 1, k) :=
    (torusPSL ζ hζ (r + 2)).comp (shiftHom 3 r) with hθ0
  let J : Fin r → Fin (r + 2) := fun j => ⟨j.val + 2, by omega⟩
  have hJ : Function.Injective J := fun j j' h => by
    simp only [J, Fin.ext_iff] at h
    exact Fin.ext (by omega)
  have hθ0single : ∀ j, θ0 (Multiplicative.ofAdd (Pi.single j 1)) =
      QuotientGroup.mk' (Subgroup.center SL(r + 2 + 1, k)) (torusElem ζ hζ (Pi.single (J j) 1)) := by
    intro j
    simp only [hθ0, MonoidHom.comp_apply, shiftHom_single]
    rfl
  have hinj : Function.Injective θ0 := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h := torusExp_eq_of_mem_ker hζo hζ (m := r + 2) (a := shiftHom 3 r a) ha
    apply Multiplicative.toAdd.injective
    funext j
    have h1 := h (Fin.castSucc ⟨0, by omega⟩) (Fin.castSucc (J j))
    rw [torusExp_castSucc, torusExp_castSucc, shiftHom_apply, shiftHom_apply] at h1
    simp only [J, Nat.le_add_left, dite_true, Nat.add_sub_cancel] at h1
    rw [toAdd_one, Pi.zero_apply]
    exact h1.symm
  have hswap : ∀ j j' : Fin r, j ≠ j' → ∃ w : PSL(r + 2 + 1, k),
      w * θ0 (Multiplicative.ofAdd (Pi.single j 1)) * w⁻¹ =
        θ0 (Multiplicative.ofAdd (Pi.single j' 1)) ∧
      w * θ0 (Multiplicative.ofAdd (Pi.single j' 1)) * w⁻¹ =
        θ0 (Multiplicative.ofAdd (Pi.single j 1)) := by
    intro j j' hjj
    have hJk : J j ≠ J j' := fun h => hjj (hJ h)
    refine ⟨QuotientGroup.mk' _ (swapElem (J j) (J j') hJk), ?_, ?_⟩
    · rw [hθ0single, hθ0single]
      change QuotientGroup.mk' _ (swapElem (J j) (J j') hJk * torusElem ζ hζ (Pi.single (J j) 1) *
        (swapElem (J j) (J j') hJk)⁻¹) = _
      rw [swapElem_conj]
    · rw [hθ0single, hθ0single]
      change QuotientGroup.mk' _ (swapElem (J j) (J j') hJk * torusElem ζ hζ (Pi.single (J j') 1) *
        (swapElem (J j) (J j') hJk)⁻¹) = _
      rw [swapElem_comm, swapElem_conj]
  have hinv : ∀ j : Fin r, ∃ w : PSL(r + 2 + 1, k),
      w * θ0 (Multiplicative.ofAdd (Pi.single j 1)) * w⁻¹ =
        (θ0 (Multiplicative.ofAdd (Pi.single j 1)))⁻¹ := by
    intro j
    refine ⟨QuotientGroup.mk' _ (invElem (J j)), ?_⟩
    rw [hθ0single]
    change QuotientGroup.mk' _ (invElem (J j) * torusElem ζ hζ (Pi.single (J j) 1) *
      (invElem (J j))⁻¹) = _
    rw [invElem_conj, map_inv]
  have h01 : (⟨0, by omega⟩ : Fin (r + 2 + 1)) ≠ ⟨1, by omega⟩ := by simp
  set tt : SL(r + 2 + 1, k) := rootElem h01 (1 : k) with htt
  have ht1 : QuotientGroup.mk' (Subgroup.center SL(r + 2 + 1, k)) tt ≠ 1 := by
    intro h
    exact rootElem_not_mem_center h01 one_ne_zero ((QuotientGroup.eq_one_iff _).1 h)
  have ht2 : (QuotientGroup.mk' (Subgroup.center SL(r + 2 + 1, k)) tt) ^ 2 = 1 := by
    rw [← map_pow, pow_two, htt, ← rootElem_add, CharTwo.add_self_eq_zero, rootElem_zero, map_one]
  have htE : ∀ a, Commute (QuotientGroup.mk' (Subgroup.center SL(r + 2 + 1, k)) tt) (θ0 a) := by
    intro a
    have hd : (torusEntries ζ hζ (Multiplicative.toAdd (shiftHom 3 r a)) ⟨0, by omega⟩ : k) *
        (torusEntries ζ hζ (Multiplicative.toAdd (shiftHom 3 r a)) ⟨1, by omega⟩ : k)⁻¹ = 1 := by
      have e0 : torusEntries ζ hζ (Multiplicative.toAdd (shiftHom 3 r a)) ⟨0, by omega⟩ = 1 := by
        have := torusExp_castSucc (Multiplicative.toAdd (shiftHom 3 r a)) ⟨0, by omega⟩
        simp only [torusEntries]
        rw [show (⟨0, by omega⟩ : Fin (r + 2 + 1)) = Fin.castSucc ⟨0, by omega⟩ from rfl, this,
          shiftHom_apply]
        simp
      have e1 : torusEntries ζ hζ (Multiplicative.toAdd (shiftHom 3 r a)) ⟨1, by omega⟩ = 1 := by
        have := torusExp_castSucc (Multiplicative.toAdd (shiftHom 3 r a)) ⟨1, by omega⟩
        simp only [torusEntries]
        rw [show (⟨1, by omega⟩ : Fin (r + 2 + 1)) = Fin.castSucc ⟨1, by omega⟩ from rfl, this,
          shiftHom_apply]
        simp
      rw [e0, e1]
      simp
    have hcomm : torusElem ζ hζ (Multiplicative.toAdd (shiftHom 3 r a)) * tt *
        (torusElem ζ hζ (Multiplicative.toAdd (shiftHom 3 r a)))⁻¹ = tt := by
      rw [htt, diag_conj_rootElem h01 (torusEntries ζ hζ (Multiplicative.toAdd (shiftHom 3 r a)))
        (1 : k) _ (coe_torusElem ζ hζ _), hd, one_mul]
    have hθa : θ0 a = QuotientGroup.mk' (Subgroup.center SL(r + 2 + 1, k))
        (torusElem ζ hζ (Multiplicative.toAdd (shiftHom 3 r a))) := rfl
    rw [hθa]
    have h2 : torusElem ζ hζ (Multiplicative.toAdd (shiftHom 3 r a)) * tt =
        tt * torusElem ζ hζ (Multiplicative.toAdd (shiftHom 3 r a)) :=
      mul_inv_eq_iff_eq_mul.1 hcomm
    exact (Commute.map (show Commute (torusElem ζ hζ (Multiplicative.toAdd (shiftHom 3 r a))) tt
      from h2) (QuotientGroup.mk' (Subgroup.center SL(r + 2 + 1, k)))).symm
  exact succ_le_localRank_of_torus hφ hker Nat.prime_three (by norm_num) h3 θ0 hinj hswap hinv
    ht1 ht2 htE

end CFSG.RankThree.PartOne.N143
