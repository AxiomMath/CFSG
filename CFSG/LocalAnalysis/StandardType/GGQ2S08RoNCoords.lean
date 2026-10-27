module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNCmp
public import CFSG.LocalAnalysis.StandardType.GGQ2S08PermLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TestLin E6QTwo

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}

theorem ggQ2_card_bstar_centralizer_le {B D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ 27 := by
  have hconf : GGConfig 3 B Bs x L D J := hS.1.1
  have hBstar : GGBstar 3 B Bs := hconf.2.1
  have hstd : LargeEvenStdSub 3 B x L D J := hconf.2.2
  have hpre : LargeEvenStdSubPre 3 B x L D J := hstd.1
  have hBle : B ≤ Bs := hBstar.1
  have hcardBs : Nat.card Bs ≤ 3 * Nat.card B := hBstar.2.2.1
  have hDleB : D ≤ B := hpre.1
  have hcardD : Nat.card D = 3 ^ 2 := hpre.2.2.1
  have hDinf : D = B ⊓ Subgroup.centralizer (J : Set G) := hpre.2.2.2.2.2.2
  let C : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
  change Nat.card ↥C ≤ 27
  have hBC : B ⊓ C = D := by
    change B ⊓ (Bs ⊓ Subgroup.centralizer (J : Set G)) = D
    rw [← inf_assoc, inf_eq_left.mpr hBle, ← hDinf]
  have hcardBC : Nat.card ↥(B ⊓ C) = 9 := by
    rw [hBC, hcardD]; norm_num
  have hidxBs : B.relIndex Bs ≤ 3 := by
    have h1 : B.relIndex Bs * Nat.card ↥(B ⊓ Bs) = Nat.card ↥Bs :=
      Subgroup.relIndex_mul_card B Bs
    rw [inf_eq_left.mpr hBle] at h1
    have hpos : 0 < Nat.card ↥B := Nat.card_pos
    nlinarith [h1, hcardBs, hpos]
  have hrelC : B.relIndex C ≤ B.relIndex Bs := by
    refine Subgroup.relIndex_le_of_le_right (H := B) (K := C) (L := Bs) ?_ ?_
    · exact inf_le_left
    · intro h
      have h1 : B.relIndex Bs * Nat.card ↥(B ⊓ Bs) = Nat.card ↥Bs :=
        Subgroup.relIndex_mul_card B Bs
      rw [inf_eq_left.mpr hBle] at h1
      rw [h, zero_mul] at h1
      have hpos : 0 < Nat.card ↥Bs := Nat.card_pos
      omega
  calc Nat.card ↥C
      = B.relIndex C * Nat.card ↥(B ⊓ C) := (Subgroup.relIndex_mul_card B C).symm
    _ ≤ 3 * 9 := Nat.mul_le_mul (hrelC.trans hidxBs) (le_of_eq hcardBC)
    _ = 27 := by norm_num

namespace E6QTwo.GGQ2S08RoN

variable {n : ℕ}

theorem vdiag_eq_iff_coords (c : GGQ2S08RoN n Bs L x) (M : GGQ2LDatum 3 Bs L x)
    (κ : M.V ≃ₗ[ZMod 3] Vn (n + 1)) (hκx : κ M.xV = oneN (n + 1))
    (w : Fin (n + 1) ≃ Fin (n + 1))
    (hw : ∀ j : Fin (n + 1),
      (∀ i i', i ≠ w j → i' ≠ w j →
        c.vdiag M (κ.symm (Pi.single j 1)) i = c.vdiag M (κ.symm (Pi.single j 1)) i') ∧
      ∀ i, i ≠ w j →
        c.vdiag M (κ.symm (Pi.single j 1)) i ≠ c.vdiag M (κ.symm (Pi.single j 1)) (w j))
    (v : M.V) (i i' : Fin (n + 1)) :
    c.vdiag M v i = c.vdiag M v i' ↔ κ v (w.symm i) = κ v (w.symm i') := by
  classical
  by_cases hii : i = i'
  · subst i'
    simp
  set a : Fin (n + 1) := w.symm i with ha
  set a' : Fin (n + 1) := w.symm i' with ha'
  have hwa : w a = i := by rw [ha]; exact Equiv.apply_symm_apply w i
  have hwa' : w a' = i' := by rw [ha']; exact Equiv.apply_symm_apply w i'
  have haa' : a ≠ a' := by
    intro h
    apply hii
    rw [← hwa, ← hwa', h]
  let f : Fin (n + 1) → M.V := fun j => κ.symm (Pi.single j 1)
  have hκf : ∀ j, κ (f j) = Pi.single j 1 := fun j => κ.apply_symm_apply _
  let χ : M.V → c.Kˣ := fun v => c.vdiag M v i * (c.vdiag M v i')⁻¹
  have hdecomp : ∀ u : M.V, u = ∑ j, κ u j • f j := by
    intro u
    apply κ.injective
    rw [map_sum]
    simp only [map_smul, hκf]
    funext p
    rw [Finset.sum_apply, Finset.sum_eq_single p]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hp
      exact absurd (Finset.mem_univ p) hp
  have hχ_add : ∀ u w : M.V, χ (u + w) = χ u * χ w := by
    intro u w
    rw [show χ (u + w) = c.vdiag M (u + w) i * (c.vdiag M (u + w) i')⁻¹ from rfl]
    rw [c.vdiag_add M u w, Pi.mul_apply, Pi.mul_apply, mul_inv_rev]
    simp [χ, mul_comm, mul_assoc, mul_left_comm]
  have hχ_smul : ∀ (r : ZMod 3) (u : M.V), χ (r • u) = χ u ^ r.val := by
    intro r u
    rw [show χ (r • u) = c.vdiag M (r • u) i * (c.vdiag M (r • u) i')⁻¹ from rfl]
    rw [c.vdiag_smul M r u, Pi.pow_apply, Pi.pow_apply, mul_pow, inv_pow]
  have hχ_zero : χ 0 = 1 := by
    simp [χ, c.vdiag_zero]
  have hχ_sum : ∀ (s : Finset (Fin (n + 1))) (g : Fin (n + 1) → M.V),
      χ (∑ j ∈ s, g j) = ∏ j ∈ s, χ (g j) := by
    intro s g
    induction s using Finset.induction_on with
    | empty => simp [hχ_zero]
    | insert j s hj ih =>
        rw [Finset.sum_insert hj, Finset.prod_insert hj, hχ_add, ih]
  have hχf_other : ∀ j, j ≠ a → j ≠ a' → χ (f j) = 1 := by
    intro j hja hja'
    have hji : w j ≠ i := fun h => hja (w.injective (by rw [h, hwa]))
    have hji' : w j ≠ i' := fun h => hja' (w.injective (by rw [h, hwa']))
    have h1 : c.vdiag M (f j) i = c.vdiag M (f j) i' :=
      (hw j).1 i i' (Ne.symm hji) (Ne.symm hji')
    simp [χ, f, h1]
  have hχfa_ne : χ (f a) ≠ 1 := by
    intro h
    have h1 : c.vdiag M (f a) i = c.vdiag M (f a) i' := by
      simpa [χ] using mul_inv_eq_one.mp h
    have hne : c.vdiag M (f a) i' ≠ c.vdiag M (f a) (w a) :=
      (hw a).2 i' (by rw [hwa]; exact Ne.symm hii)
    rw [hwa] at hne
    exact hne h1.symm
  have hχfa'_ne : χ (f a') ≠ 1 := by
    intro h
    have h1 : c.vdiag M (f a') i = c.vdiag M (f a') i' := by
      simpa [χ] using mul_inv_eq_one.mp h
    have hne : c.vdiag M (f a') i ≠ c.vdiag M (f a') (w a') :=
      (hw a').2 i (by rw [hwa']; exact hii)
    rw [hwa'] at hne
    exact hne h1
  have hprod : ∏ j, χ (f j) = χ (f a) * χ (f a') := by
    rw [← Finset.insert_erase (Finset.mem_univ a), Finset.prod_insert (Finset.notMem_erase a _)]
    have herase : ∏ j ∈ Finset.univ.erase a, χ (f j) = χ (f a') := by
      refine Finset.prod_eq_single_of_mem a' ?_ ?_
      · exact Finset.mem_erase.mpr ⟨haa'.symm, Finset.mem_univ a'⟩
      · intro j hj hja'
        exact hχf_other j (Finset.ne_of_mem_erase hj) hja'
    rw [herase]
  have hχx : χ M.xV = 1 := by
    have hvx : c.vdiag M M.xV = 1 := by
      rw [c.vdiag_eq_one_iff]
      exact Submodule.mem_span_singleton_self M.xV
    simp [χ, hvx]
  have hχx_prod : χ M.xV = χ (f a) * χ (f a') := by
    have hvx : M.xV = ∑ j, κ M.xV j • f j := hdecomp M.xV
    rw [hvx]
    rw [hχ_sum Finset.univ (fun j => κ M.xV j • f j)]
    calc ∏ j ∈ Finset.univ, χ (κ M.xV j • f j) = ∏ j ∈ Finset.univ, χ (f j) := by
          apply Finset.prod_congr rfl
          intro j _
          rw [hχ_smul]
          have h1 : κ M.xV j = 1 := by rw [hκx]; rfl
          rw [h1, ZMod.val_one, pow_one]
      _ = χ (f a) * χ (f a') := hprod
  have hζζ' : χ (f a) * χ (f a') = 1 := by rw [← hχx_prod]; exact hχx
  have hζ' : χ (f a') = (χ (f a))⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    simpa [mul_comm] using hζζ'
  have hχ_v_form : χ v = χ (f a) ^ (κ v a).val * χ (f a') ^ (κ v a').val := by
    have hv : v = ∑ j, κ v j • f j := hdecomp v
    calc χ v = χ (∑ j, κ v j • f j) := by conv_lhs => rw [hv]
      _ = ∏ j, χ (κ v j • f j) := by rw [hχ_sum Finset.univ]
      _ = ∏ j, χ (f j) ^ (κ v j).val := by
            apply Finset.prod_congr rfl
            intro j _
            rw [hχ_smul]
      _ = χ (f a) ^ (κ v a).val * χ (f a') ^ (κ v a').val := by
            rw [← Finset.insert_erase (Finset.mem_univ a),
                Finset.prod_insert (Finset.notMem_erase a _)]
            have herase : ∏ j ∈ Finset.univ.erase a, χ (f j) ^ (κ v j).val =
                χ (f a') ^ (κ v a').val := by
              refine Finset.prod_eq_single_of_mem a' ?_ ?_
              · exact Finset.mem_erase.mpr ⟨haa'.symm, Finset.mem_univ a'⟩
              · intro j hj hja'
                rw [hχf_other j (Finset.ne_of_mem_erase hj) hja', one_pow]
            rw [herase]
  have hχ_eq_one : χ v = 1 ↔ χ (f a) ^ (κ v a).val = χ (f a) ^ (κ v a').val := by
    constructor
    · intro h
      have h1 : χ (f a) ^ (κ v a).val * χ (f a') ^ (κ v a').val = 1 := by
        rw [← hχ_v_form]; exact h
      rw [hζ', inv_pow, mul_inv_eq_one] at h1
      exact h1
    · intro h
      rw [hχ_v_form, hζ', inv_pow, mul_inv_eq_one]
      exact h
  have hpow : χ (f a) ^ (κ v a).val = χ (f a) ^ (κ v a').val ↔ κ v a = κ v a' := by
    constructor
    · intro h
      have hk : (κ v a).val = (κ v a').val := by
        have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        have hcube : χ (f a) ^ 3 = 1 := c.cube _
        have hord : orderOf (χ (f a)) = 3 :=
          orderOf_eq_prime (p := 3) (hp := hfact) hcube hχfa_ne
        rw [IsOfFinOrder.pow_inj_mod (isOfFinOrder_of_finite (χ (f a))), hord] at h
        rw [Nat.mod_eq_of_lt (ZMod.val_lt (κ v a)), Nat.mod_eq_of_lt (ZMod.val_lt (κ v a'))] at h
        exact h
      exact ZMod.val_injective 3 hk
    · intro h
      rw [h]
  have hvdiag : c.vdiag M v i = c.vdiag M v i' ↔ χ v = 1 := by
    rw [show χ v = c.vdiag M v i * (c.vdiag M v i')⁻¹ from rfl, mul_inv_eq_one]
  rw [hvdiag, hχ_eq_one, hpow]

end E6QTwo.GGQ2S08RoN

end CFSG.StandardType

end
