module

public import CFSG.LocalAnalysis.StandardType.GGHalfWeylTorusCoord
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockPerm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf SpJoin

namespace GGHalf

private theorem mulSingle_ofAdd_eq_pow_gen {p k : ℕ} [NeZero p] (i : Fin k) (c : ZMod p) :
    (Pi.mulSingle i (Multiplicative.ofAdd c) : Fin k → Multiplicative (ZMod p)) =
      Pi.mulSingle i (Multiplicative.ofAdd 1) ^ c.val := by
  rw [← Pi.mulSingle_pow, ← ofAdd_nsmul]
  congr 1
  congr 1
  rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

private theorem hom_ext_mulSingle_gen {p k : ℕ} [NeZero p] {M : Type*} [Monoid M]
    {F₁ F₂ : (Fin k → Multiplicative (ZMod p)) →* M}
    (h : ∀ i, F₁ (Pi.mulSingle i (Multiplicative.ofAdd 1)) =
              F₂ (Pi.mulSingle i (Multiplicative.ofAdd 1))) : F₁ = F₂ := by
  refine MonoidHom.pi_ext fun i x => ?_
  rw [← ofAdd_toAdd x, mulSingle_ofAdd_eq_pow_gen, map_pow, map_pow, h i]

private theorem coordPerm_mulSingle_gen {p k : ℕ} (σ : Equiv.Perm (Fin k))
    (i : Fin k) (g : Multiplicative (ZMod p)) :
    coordPerm k p σ (Pi.mulSingle i g) = Pi.mulSingle (σ i) g := by
  funext t
  simp only [coordPerm_apply, Pi.mulSingle_apply, Equiv.symm_apply_eq]

private noncomputable def coordPermHom (p k : ℕ) (σ : Equiv.Perm (Fin k)) :
    (Fin k → Multiplicative (ZMod p)) →* (Fin k → Multiplicative (ZMod p)) where
  toFun := coordPerm k p σ
  map_one' := by funext t; rfl
  map_mul' v w := by funext t; rfl

private theorem coordPermHom_apply (p k : ℕ) (σ : Equiv.Perm (Fin k))
    (v : Fin k → Multiplicative (ZMod p)) :
    coordPermHom p k σ v = coordPerm k p σ v := rfl

private noncomputable def coordInvAut (p k : ℕ) (i : Fin k) :
    MulAut (Fin k → Multiplicative (ZMod p)) where
  toFun f := Function.update f i (f i)⁻¹
  invFun f := Function.update f i (f i)⁻¹
  left_inv f := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  right_inv f := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj]
  map_mul' f g := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [mul_comm]
    · simp [Function.update_of_ne hj]

private noncomputable def coordInvHom (p k : ℕ) (j : Fin k) :
    (Fin k → Multiplicative (ZMod p)) →* (Fin k → Multiplicative (ZMod p)) :=
  (coordInvAut p k j).toMonoidHom

private theorem coordInvHom_apply (p k : ℕ) (j : Fin k)
    (v : Fin k → Multiplicative (ZMod p)) :
    coordInvHom p k j v = coordInv k p j v := rfl

private theorem coordInv_mulSingle_self {p k : ℕ} (i : Fin k) :
    coordInv k p i (Pi.mulSingle i (Multiplicative.ofAdd 1)) =
      (Pi.mulSingle i (Multiplicative.ofAdd 1))⁻¹ := by
  funext t
  by_cases ht : t = i <;> simp [coordInv_apply, Pi.mulSingle_apply, ht]

private theorem coordInv_mulSingle_of_ne {p k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    coordInv k p j (Pi.mulSingle i (Multiplicative.ofAdd 1)) =
      Pi.mulSingle i (Multiplicative.ofAdd 1) := by
  funext t
  by_cases ht : t = j <;> simp [coordInv_apply, Pi.mulSingle_apply, ht, Ne.symm hij]

private noncomputable def blk (n : ℕ) (m : Fin ((n + 1) / 2)) : Fin n :=
  ⟨2 * m.val, two_mul_lt_of_lt_half m.isLt⟩

private theorem blk_castSucc_val (n : ℕ) (m : Fin ((n + 1) / 2)) :
    ((blk n m).castSucc : Fin (n + 1)).val = 2 * m.val := rfl

private theorem blk_succ_val (n : ℕ) (m : Fin ((n + 1) / 2)) :
    ((blk n m).succ : Fin (n + 1)).val = 2 * m.val + 1 := rfl

private theorem blk_castSucc_ne_succ (n : ℕ) (m j : Fin ((n + 1) / 2)) :
    (blk n m).castSucc ≠ (blk n j).succ := by
  intro h; have := congrArg Fin.val h
  rw [blk_castSucc_val, blk_succ_val] at this; omega

private theorem blk_succ_ne_castSucc (n : ℕ) (m j : Fin ((n + 1) / 2)) :
    (blk n m).succ ≠ (blk n j).castSucc := by
  intro h; have := congrArg Fin.val h
  rw [blk_succ_val, blk_castSucc_val] at this; omega

private theorem blk_castSucc_ne_castSucc (n : ℕ) {m j : Fin ((n + 1) / 2)} (h : m ≠ j) :
    (blk n m).castSucc ≠ (blk n j).castSucc := by
  intro hh; apply h; apply Fin.ext
  have := congrArg Fin.val hh; rw [blk_castSucc_val, blk_castSucc_val] at this; omega

private theorem blk_succ_ne_succ (n : ℕ) {m j : Fin ((n + 1) / 2)} (h : m ≠ j) :
    (blk n m).succ ≠ (blk n j).succ := by
  intro hh; apply h; apply Fin.ext
  have := congrArg Fin.val hh; rw [blk_succ_val, blk_succ_val] at this; omega

private theorem conj_coordPerm (n : ℕ)
    (Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n))
    (hΦ : ∀ j : Fin ((n + 1) / 2),
      ((Φ (Pi.mulSingle j (Multiplicative.ofAdd 1)) : ↥(halfTorus n)) :
        SpecialLinearGroup (Fin (n + 1)) F2) =
        omegaBlock n ⟨2 * j.val, two_mul_lt_of_lt_half j.isLt⟩)
    (j : Fin ((n + 1) / 2)) (hj : j.val + 1 < (n + 1) / 2) :
    ∃ e : SpecialLinearGroup (Fin (n + 1)) F2,
      ∀ a, e * (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * e⁻¹ =
        (Φ (coordPerm ((n + 1) / 2) 3 (Equiv.swap j ⟨j.val + 1, hj⟩) a) :
          SpecialLinearGroup (Fin (n + 1)) F2) := by
  set j' : Fin ((n + 1) / 2) := ⟨j.val + 1, hj⟩ with hj'def
  set σ : Equiv.Perm (Fin ((n + 1) / 2)) := Equiv.swap j j' with hσdef
  set π : Equiv.Perm (Fin (n + 1)) :=
    Equiv.swap (blk n j).castSucc (blk n j').castSucc *
      Equiv.swap (blk n j).succ (blk n j').succ with hπdef
  have hcast : ∀ m : Fin ((n + 1) / 2), π (blk n m).castSucc = (blk n (σ m)).castSucc := by
    intro m
    rw [hπdef, Equiv.Perm.mul_apply]
    have hfix : Equiv.swap (blk n j).succ (blk n j').succ (blk n m).castSucc =
        (blk n m).castSucc :=
      Equiv.swap_apply_of_ne_of_ne (blk_castSucc_ne_succ n m j) (blk_castSucc_ne_succ n m j')
    rw [hfix]
    by_cases hmj : m = j
    · rw [hmj, Equiv.swap_apply_left]
      have hs : σ j = j' := Equiv.swap_apply_left j j'
      rw [hs]
    · by_cases hmj' : m = j'
      · rw [hmj', Equiv.swap_apply_right]
        have hs : σ j' = j := Equiv.swap_apply_right j j'
        rw [hs]
      · rw [Equiv.swap_apply_of_ne_of_ne (blk_castSucc_ne_castSucc n hmj)
            (blk_castSucc_ne_castSucc n hmj')]
        have hs : σ m = m := Equiv.swap_apply_of_ne_of_ne hmj hmj'
        rw [hs]
  have hsucc : ∀ m : Fin ((n + 1) / 2), π (blk n m).succ = (blk n (σ m)).succ := by
    intro m
    rw [hπdef, Equiv.Perm.mul_apply]
    by_cases hmj : m = j
    · rw [hmj, Equiv.swap_apply_left]
      rw [Equiv.swap_apply_of_ne_of_ne (blk_succ_ne_castSucc n j' j)
        (blk_succ_ne_castSucc n j' j')]
      have hs : σ j = j' := Equiv.swap_apply_left j j'
      rw [hs]
    · by_cases hmj' : m = j'
      · rw [hmj', Equiv.swap_apply_right]
        rw [Equiv.swap_apply_of_ne_of_ne (blk_succ_ne_castSucc n j j)
          (blk_succ_ne_castSucc n j j')]
        have hs : σ j' = j := Equiv.swap_apply_right j j'
        rw [hs]
      · have hfix : Equiv.swap (blk n j).succ (blk n j').succ (blk n m).succ =
            (blk n m).succ :=
          Equiv.swap_apply_of_ne_of_ne (blk_succ_ne_succ n hmj) (blk_succ_ne_succ n hmj')
        rw [hfix, Equiv.swap_apply_of_ne_of_ne (blk_succ_ne_castSucc n m j)
          (blk_succ_ne_castSucc n m j')]
        have hs : σ m = m := Equiv.swap_apply_of_ne_of_ne hmj hmj'
        rw [hs]
  have key : ∀ m : Fin ((n + 1) / 2),
      slPerm gf2_two π * omegaBlock n (blk n m) * (slPerm gf2_two π)⁻¹ =
        omegaBlock n (blk n (σ m)) := fun m =>
    slPerm_conj_omegaBlock π (hcast m) (hsucc m)
  refine ⟨slPerm gf2_two π, ?_⟩
  have hFG : ((MulAut.conj (slPerm gf2_two π)).toMonoidHom.comp
        ((Subgroup.subtype (halfTorus n)).comp Φ.toMonoidHom)) =
      ((Subgroup.subtype (halfTorus n)).comp
        (Φ.toMonoidHom.comp (coordPermHom 3 ((n + 1) / 2) σ))) := by
    refine hom_ext_mulSingle_gen (p := 3) fun i => ?_
    have h1 : ((Φ (Pi.mulSingle i (Multiplicative.ofAdd 1)) : ↥(halfTorus n)) :
        SpecialLinearGroup (Fin (n + 1)) F2) = omegaBlock n (blk n i) := hΦ i
    have h2 : ((Φ (Pi.mulSingle (σ i) (Multiplicative.ofAdd 1)) : ↥(halfTorus n)) :
        SpecialLinearGroup (Fin (n + 1)) F2) = omegaBlock n (blk n (σ i)) := hΦ (σ i)
    have hL : ((MulAut.conj (slPerm gf2_two π)).toMonoidHom.comp
        ((Subgroup.subtype (halfTorus n)).comp Φ.toMonoidHom))
        (Pi.mulSingle i (Multiplicative.ofAdd 1)) =
        slPerm gf2_two π * omegaBlock n (blk n i) * (slPerm gf2_two π)⁻¹ := by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        Subgroup.subtype_apply, h1]
    have hR : ((Subgroup.subtype (halfTorus n)).comp
        (Φ.toMonoidHom.comp (coordPermHom 3 ((n + 1) / 2) σ)))
        (Pi.mulSingle i (Multiplicative.ofAdd 1)) =
        omegaBlock n (blk n (σ i)) := by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coordPermHom_apply,
        coordPerm_mulSingle_gen, Subgroup.subtype_apply, h2]
    rw [hL, hR]
    exact key i
  intro a
  exact DFunLike.congr_fun hFG a

private theorem conj_coordInv (n : ℕ)
    (Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n))
    (hΦ : ∀ j : Fin ((n + 1) / 2),
      ((Φ (Pi.mulSingle j (Multiplicative.ofAdd 1)) : ↥(halfTorus n)) :
        SpecialLinearGroup (Fin (n + 1)) F2) =
        omegaBlock n ⟨2 * j.val, two_mul_lt_of_lt_half j.isLt⟩)
    (j : Fin ((n + 1) / 2)) (hj : ¬ j.val + 1 < (n + 1) / 2) :
    ∃ e : SpecialLinearGroup (Fin (n + 1)) F2,
      ∀ a, e * (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * e⁻¹ =
        (Φ (coordInv ((n + 1) / 2) 3 j a) :
          SpecialLinearGroup (Fin (n + 1)) F2) := by
  set π : Equiv.Perm (Fin (n + 1)) := Equiv.swap (blk n j).castSucc (blk n j).succ with hπdef
  have keyj : slPerm gf2_two π * omegaBlock n (blk n j) * (slPerm gf2_two π)⁻¹ =
      (omegaBlock n (blk n j))⁻¹ := by
    apply slPerm_conj_omegaBlock_inv π
    · rw [hπdef, Equiv.swap_apply_left]
    · rw [hπdef, Equiv.swap_apply_right]
  have keyother : ∀ m : Fin ((n + 1) / 2), m ≠ j →
      slPerm gf2_two π * omegaBlock n (blk n m) * (slPerm gf2_two π)⁻¹ =
        omegaBlock n (blk n m) := by
    intro m hm
    apply slPerm_conj_omegaBlock π
    · rw [hπdef]
      exact Equiv.swap_apply_of_ne_of_ne (blk_castSucc_ne_castSucc n hm)
        (blk_castSucc_ne_succ n m j)
    · rw [hπdef]
      exact Equiv.swap_apply_of_ne_of_ne (blk_succ_ne_castSucc n m j) (blk_succ_ne_succ n hm)
  refine ⟨slPerm gf2_two π, ?_⟩
  have hFG : ((MulAut.conj (slPerm gf2_two π)).toMonoidHom.comp
        ((Subgroup.subtype (halfTorus n)).comp Φ.toMonoidHom)) =
      ((Subgroup.subtype (halfTorus n)).comp
        (Φ.toMonoidHom.comp (coordInvHom 3 ((n + 1) / 2) j))) := by
    refine hom_ext_mulSingle_gen (p := 3) fun i => ?_
    by_cases hij : i = j
    · rw [hij]
      have h1 : ((Φ (Pi.mulSingle j (Multiplicative.ofAdd 1)) : ↥(halfTorus n)) :
          SpecialLinearGroup (Fin (n + 1)) F2) = omegaBlock n (blk n j) := hΦ j
      have hL : ((MulAut.conj (slPerm gf2_two π)).toMonoidHom.comp
          ((Subgroup.subtype (halfTorus n)).comp Φ.toMonoidHom))
          (Pi.mulSingle j (Multiplicative.ofAdd 1)) =
          slPerm gf2_two π * omegaBlock n (blk n j) * (slPerm gf2_two π)⁻¹ := by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        Subgroup.subtype_apply, h1]
      have hR : ((Subgroup.subtype (halfTorus n)).comp
          (Φ.toMonoidHom.comp (coordInvHom 3 ((n + 1) / 2) j)))
          (Pi.mulSingle j (Multiplicative.ofAdd 1)) =
          (omegaBlock n (blk n j))⁻¹ := by
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, coordInvHom_apply,
          coordInv_mulSingle_self]
        rw [map_inv (Φ.toMonoidHom) (Pi.mulSingle j (Multiplicative.ofAdd 1))]
        simp only [Subgroup.coe_inv, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply, h1]
      rw [hL, hR, keyj]
    · have h1 : ((Φ (Pi.mulSingle i (Multiplicative.ofAdd 1)) : ↥(halfTorus n)) :
          SpecialLinearGroup (Fin (n + 1)) F2) = omegaBlock n (blk n i) := hΦ i
      have hL : ((MulAut.conj (slPerm gf2_two π)).toMonoidHom.comp
          ((Subgroup.subtype (halfTorus n)).comp Φ.toMonoidHom))
          (Pi.mulSingle i (Multiplicative.ofAdd 1)) =
          slPerm gf2_two π * omegaBlock n (blk n i) * (slPerm gf2_two π)⁻¹ := by
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        Subgroup.subtype_apply, h1]
      have hR : ((Subgroup.subtype (halfTorus n)).comp
          (Φ.toMonoidHom.comp (coordInvHom 3 ((n + 1) / 2) j)))
          (Pi.mulSingle i (Multiplicative.ofAdd 1)) =
          omegaBlock n (blk n i) := by
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, coordInvHom_apply,
          coordInv_mulSingle_of_ne hij, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply, h1]
      rw [hL, hR, keyother i hij]
  intro a
  exact DFunLike.congr_fun hFG a

theorem exists_conj_of_spSigned (n : ℕ)
    (Φ : (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) ≃* ↥(halfTorus n))
    (hΦ : ∀ j : Fin ((n + 1) / 2),
      ((Φ (Pi.mulSingle j (Multiplicative.ofAdd 1)) : ↥(halfTorus n)) :
        SpecialLinearGroup (Fin (n + 1)) F2) =
        omegaBlock n ⟨2 * j.val, two_mul_lt_of_lt_half j.isLt⟩)
    (h : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)))
    (hh : h ∈ spSignedGroup ((n + 1) / 2) 3) :
    ∃ e : SpecialLinearGroup (Fin (n + 1)) F2, ∀ a,
      e * (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * e⁻¹ =
        (Φ (h a) : SpecialLinearGroup (Fin (n + 1)) F2) := by
  rw [spSignedGroup] at hh
  let P : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) → Prop :=
    fun h => ∃ e : SpecialLinearGroup (Fin (n + 1)) F2, ∀ a,
      e * (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * e⁻¹ =
        (Φ (h a) : SpecialLinearGroup (Fin (n + 1)) F2)
  change P h
  refine Subgroup.closure_induction (p := fun x _ => P x) ?_ ?_ ?_ ?_ hh
  · rintro x ⟨j, rfl⟩
    by_cases hj : j.val + 1 < (n + 1) / 2
    · rw [spReflPerm_of_lt ((n + 1) / 2) 3 j hj]
      exact conj_coordPerm n Φ hΦ j hj
    · rw [spReflPerm_of_not_lt ((n + 1) / 2) 3 j hj]
      exact conj_coordInv n Φ hΦ j hj
  · exact ⟨1, fun a => by simp⟩
  · rintro x y hx hy ⟨e₁, he₁⟩ ⟨e₂, he₂⟩
    refine ⟨e₁ * e₂, fun a => ?_⟩
    have h : (e₁ * e₂) * (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * (e₁ * e₂)⁻¹ =
        e₁ * (e₂ * (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * e₂⁻¹) * e₁⁻¹ := by group
    rw [h, he₂ a, he₁ (y a), Equiv.Perm.mul_apply]
  · rintro x hx ⟨e, he⟩
    refine ⟨e⁻¹, fun a => ?_⟩
    have he' : e * (Φ (x⁻¹ a) : SpecialLinearGroup (Fin (n + 1)) F2) * e⁻¹ =
        (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) := by
      rw [he (x⁻¹ a), Equiv.Perm.inv_def, Equiv.apply_symm_apply]
    rw [show (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) =
        e * (Φ (x⁻¹ a) : SpecialLinearGroup (Fin (n + 1)) F2) * e⁻¹ from he'.symm]
    group

end GGHalf

end CFSG.StandardType

end
