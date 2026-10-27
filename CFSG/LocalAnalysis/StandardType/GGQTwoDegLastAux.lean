module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDegDefs
import CFSG.LocalAnalysis.StandardType.GGSpJoinReflPairing
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open

variable {G : Type} [Group G] [Finite G]

private def qTwoDegLastAux_pr_A_par (r : ℕ) (i : Fin r) : Fin r :=
  ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

private theorem qTwoDegLastAux_pr_A_par_eq (r : ℕ) (i j : Fin r) (hi : i.val ≠ 0) :
    qTwoDegLastAux_pr_A_par r i = j ↔ i.val = j.val + 1 := by
  rw [Fin.ext_iff]
  simp only [qTwoDegLastAux_pr_A_par]
  omega

private theorem qTwoDegLastAux_pr_A_neg_one (r : ℕ) (i j : Fin r) :
    CartanMatrix.A r i j = -1 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  rw [CartanMatrix.A, Matrix.of_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg h]
    by_cases h2 : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · rw [if_pos h2]; exact iff_of_true rfl h2
    · rw [if_neg h2]; exact iff_of_false (by norm_num) h2

private theorem qTwoDegLastAux_pr_A_hsl (r : ℕ) (i j : Fin r) (hij : i ≠ j) :
    CartanMatrix.A r i j = 0 ∨ CartanMatrix.A r i j = -1 := by
  rw [CartanMatrix.A, Matrix.of_apply, if_neg hij]
  by_cases h2 : i.val + 1 = j.val ∨ j.val + 1 = i.val
  · rw [if_pos h2]; exact Or.inr rfl
  · rw [if_neg h2]; exact Or.inl rfl

private theorem qTwoDegLastAux_pr_A_hpar (r : ℕ) (hr : 1 ≤ r) (i j : Fin r) (hij : i ≠ j) :
    (CartanMatrix.A r i j = -1 ↔
      ((i ≠ (⟨0, hr⟩ : Fin r) ∧ qTwoDegLastAux_pr_A_par r i = j) ∨
        (j ≠ (⟨0, hr⟩ : Fin r) ∧ qTwoDegLastAux_pr_A_par r j = i))) := by
  rw [qTwoDegLastAux_pr_A_neg_one]
  have hroot : ∀ i : Fin r, (i ≠ (⟨0, hr⟩ : Fin r)) ↔ i.val ≠ 0 := by
    intro i
    simp [Fin.ext_iff]
  constructor
  · intro h
    rcases h with h | h
    · right
      refine ⟨(hroot j).mpr (by omega), ?_⟩
      rw [qTwoDegLastAux_pr_A_par_eq r j i (by omega)]
      omega
    · left
      refine ⟨(hroot i).mpr (by omega), ?_⟩
      rw [qTwoDegLastAux_pr_A_par_eq r i j (by omega)]
      omega
  · rintro (⟨hi, hpi⟩ | ⟨hj, hpj⟩)
    · rw [qTwoDegLastAux_pr_A_par_eq r i j ((hroot i).mp hi)] at hpi
      omega
    · rw [qTwoDegLastAux_pr_A_par_eq r j i ((hroot j).mp hj)] at hpj
      omega

private theorem qTwoDegLastAux_pr_A_hdepth (r : ℕ) (hr : 1 ≤ r) (i : Fin r)
    (hi : i ≠ (⟨0, hr⟩ : Fin r)) : (qTwoDegLastAux_pr_A_par r i).val < i.val := by
  have hroot : i.val ≠ 0 := by
    intro h0; exact hi (Fin.ext h0)
  simp only [qTwoDegLastAux_pr_A_par, Fin.val_mk]
  omega

theorem qTwoDegLastAux_datum {Bs : Subgroup G} (hNT : GGNoTransvection 3 Bs)
    {A : Subgroup (MulAut ↥Bs)} (hA : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) {r : ℕ} (hr : 1 ≤ r)
    (hW : GGWeylOfType 3 (CoxeterMatrix.A r) A) {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (ιV : Additive ↥Bs ≃+ V) :
    ∃ (e : (CoxeterMatrix.A r).Group ≃* ↥A) (h : Fin r → V)
      (α : Fin r → Module.Dual (ZMod 3) V) (hα : ∀ i, α i (h i) = 2),
      (∀ i, ggLin (p := 3) ιV ((e ((CoxeterMatrix.A r).simple i) : ↥A) : MulAut ↥Bs) =
        Module.reflection (hα i)) ∧
      ∀ i j, α i (h j) = (CartanMatrix.A r i j : ZMod 3) := by
  exact SpJoinRefl.exists_cartan_pairing_of_weylOfType (p := 3) (M := CoxeterMatrix.A r)
    (C := CartanMatrix.A r) (by norm_num) hNT (ggIntCartan_A r) (qTwoDegLastAux_pr_A_hsl r)
    (qTwoDegLastAux_pr_A_par r) (⟨0, hr⟩) (fun i => i.val) (qTwoDegLastAux_pr_A_hpar r hr)
    (fun i hi => qTwoDegLastAux_pr_A_hdepth r hr i hi) hW hA ιV

theorem qTwoDegLastAux_linearIndependent {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {r : ℕ}
    (hr : ¬ 3 ∣ r + 1) (h : Fin r → V) (α : Fin r → Module.Dual (ZMod 3) V)
    (hP : ∀ i j, α i (h j) = (CartanMatrix.A r i j : ZMod 3)) :
    LinearIndependent (ZMod 3) h := by
  refine linearIndependent_of_det_ne_zero h α ?_
  have hmap : (Matrix.of fun i j => α i (h j)) =
      (CartanMatrix.A r).map (fun x : ℤ => (x : ZMod 3)) := by
    ext i j
    rw [Matrix.map_apply]
    exact hP i j
  rw [hmap, ← Int.cast_det (CartanMatrix.A r), CartanMatrix.A_det]
  intro h0
  have h1 : (3 : ℤ) ∣ ((r : ℤ) + 1) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd ((r : ℤ) + 1) 3).mp h0
  have h2 : ((r : ℤ) + 1) = ((r + 1 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [h2] at h1
  exact hr (Int.natCast_dvd_natCast.mp h1)

theorem qTwoDegLastAux_card_commSpace_ge {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (ιV : Additive ↥Bs ≃+ V) {n : ℕ} (h : Fin n → V)
    (hind : LinearIndependent (ZMod 3) h) (α : Fin n → Module.Dual (ZMod 3) V)
    (hα : ∀ i, α i (h i) = 2) (φ : Fin n → MulAut ↥Bs)
    (hφ : ∀ i, ggLin (p := 3) ιV (φ i) = Module.reflection (hα i))
    (U : Subgroup (MulAut ↥Bs)) (S : Finset (Fin n)) (hS : ∀ i ∈ S, φ i ∈ U) :
    3 ^ S.card ≤ Nat.card ↥(ggCommSpace Bs U) := by
  classical
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ιV.toEquiv
  let b : Fin n → ↥Bs := fun i => Additive.toMul (ιV.symm (h i))
  have hbι : ∀ i, ιV (Additive.ofMul (b i)) = h i := by
    intro i
    simp [b]
  have hbgen : ∀ i ∈ S, b i ∈ ggCommSpace Bs U := by
    intro i hi
    refine Subgroup.subset_closure ⟨φ i, hS i hi, b i, ?_⟩
    symm
    apply Additive.ofMul.injective
    apply ιV.injective
    rw [ofMul_mul, ofMul_inv, map_add, map_neg]
    have h1 : ιV (Additive.ofMul (φ i (b i))) = -h i := by
      rw [← ggLin_apply_ofMul (p := 3) ιV (φ i) (b i), hbι i, hφ i]
      exact Module.reflection_apply_self (hα i)
    rw [h1, hbι i]
    have h2 : (-h i : V) = (2 : ZMod 3) • h i := by
      rw [show (2 : ZMod 3) = -1 by decide]
      exact (neg_one_smul (R := ZMod 3) (x := h i)).symm
    rw [h2, ← add_smul]
    rw [show (2 : ZMod 3) + 2 = 1 by decide, one_smul]
  let Wc : Submodule (ZMod 3) V :=
    { carrier := {v | Additive.toMul (ιV.symm v) ∈ ggCommSpace Bs U}
      add_mem' := fun {v w} hv hw => by
        change Additive.toMul (ιV.symm (v + w)) ∈ ggCommSpace Bs U
        rw [map_add, toMul_add]
        exact (ggCommSpace Bs U).mul_mem hv hw
      zero_mem' := by
        change Additive.toMul (ιV.symm 0) ∈ ggCommSpace Bs U
        rw [map_zero, toMul_zero]
        exact (ggCommSpace Bs U).one_mem
      smul_mem' := fun c {v} hv => by
        change Additive.toMul (ιV.symm (c • v)) ∈ ggCommSpace Bs U
        have hcv : c • v = c.val • v := by
          rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
        rw [hcv, map_nsmul, toMul_nsmul]
        exact (ggCommSpace Bs U).pow_mem hv c.val }
  have hmem : ∀ i ∈ S, h i ∈ Wc := by
    intro i hi
    exact hbgen i hi
  set W : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range (fun i : S => h i))
    with hW
  have hWle : W ≤ Wc := by
    rw [hW]
    refine Submodule.span_le.mpr ?_
    rintro v ⟨i, rfl⟩
    exact hmem i i.2
  have hindS : LinearIndependent (ZMod 3) (fun i : S => h i) :=
    hind.comp (Subtype.val) Subtype.val_injective
  have hfinrank : Module.finrank (ZMod 3) W = S.card := by
    rw [hW, finrank_span_eq_card hindS, Fintype.card_coe]
  have hcardW : Nat.card W = 3 ^ S.card := by
    rw [← FiniteField.pow_finrank_eq_natCard 3 W, hfinrank]
  let f : W → ↥(ggCommSpace Bs U) := fun v =>
    ⟨Additive.toMul (ιV.symm v.1), hWle v.2⟩
  have hf : Function.Injective f := by
    intro v w hvw
    have h0 : Additive.toMul (ιV.symm v.1) = Additive.toMul (ιV.symm w.1) :=
      congrArg Subtype.val hvw
    apply Subtype.ext
    exact ιV.symm.injective (Additive.toMul.injective h0)
  calc 3 ^ S.card = Nat.card W := hcardW.symm
    _ ≤ Nat.card ↥(ggCommSpace Bs U) := Nat.card_le_card_of_injective f hf

theorem qTwoDegLastAux_card_commSpace_conj {Bs : Subgroup G} (U : Subgroup (MulAut ↥Bs))
    (g : MulAut ↥Bs) :
    Nat.card ↥(ggCommSpace Bs (U.map (MulAut.conj g).toMonoidHom)) =
      Nat.card ↥(ggCommSpace Bs U) := by
  have hmap : ggCommSpace Bs (U.map (MulAut.conj g).toMonoidHom) =
      (ggCommSpace Bs U).map g.toMonoidHom := by
    apply le_antisymm
    · unfold ggCommSpace
      rw [Subgroup.closure_le]
      rintro c ⟨a, ha, b, rfl⟩
      obtain ⟨a₀, ha₀, rfl⟩ := ha
      have h1 : (MulAut.conj g).toMonoidHom a₀ b * b⁻¹ =
          g.toMonoidHom (a₀ (g⁻¹ b) * (g⁻¹ b)⁻¹) := by
        change (MulAut.conj g a₀) b * b⁻¹ = g (a₀ (g⁻¹ b) * (g⁻¹ b)⁻¹)
        simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv,
          MulAut.apply_inv_self]
      rw [h1]
      exact Subgroup.mem_map_of_mem g.toMonoidHom
        (Subgroup.subset_closure ⟨a₀, ha₀, g⁻¹ b, rfl⟩)
    · unfold ggCommSpace
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro c ⟨d, ⟨a, ha, b, rfl⟩, rfl⟩
      have h2 : g.toMonoidHom (a b * b⁻¹) =
          (MulAut.conj g).toMonoidHom a (g b) * (g b)⁻¹ := by
        change g (a b * b⁻¹) = (MulAut.conj g a) (g b) * (g b)⁻¹
        simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv,
          MulAut.inv_apply_self]
      rw [h2]
      exact Subgroup.subset_closure
        ⟨(MulAut.conj g).toMonoidHom a, ⟨a, ha, rfl⟩, g b, rfl⟩
  rw [hmap, Subgroup.card_map_of_injective g.injective]

end CFSG.StandardType.QTwo

end
