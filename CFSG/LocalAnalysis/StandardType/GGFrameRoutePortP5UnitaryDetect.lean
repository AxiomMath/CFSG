module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5UnitaryFix
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks
public import CFSG.Open.StatedAPI
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.FrameRoute.UnitaryModel

open CFSG.Assembly CFSG.SeitzReduction.UnitaryPilot CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K] {d : ℕ}

private theorem diagGL_conj_eq_self_of_mem_unitaryBlock (h : UnitaryFieldData 2 1 K)
    {ζ : Kˣ} {w : Fin d → ZMod 3} {I : Finset (Fin d)}
    (hw : ∀ i ∈ I, ∀ i' ∈ I, w i = w i')
    {g : unitarySU 2 1 K d} (hg : g ∈ unitaryBlock h I) :
    TauCeti.diagGL (fun i => ζ ^ (w i).val) * (g : GL (Fin d) K) *
        (TauCeti.diagGL (fun i => ζ ^ (w i).val))⁻¹ = (g : GL (Fin d) K) := by
  let G : GL (Fin d) K := (g : GL (Fin d) K)
  let GM : Matrix (Fin d) (Fin d) K := (G : Matrix (Fin d) (Fin d) K)
  change TauCeti.diagGL (fun i => ζ ^ (w i).val) * G *
      (TauCeti.diagGL (fun i => ζ ^ (w i).val))⁻¹ = G
  apply Units.ext
  ext a b
  have hGentry := diagGL_mul_mul_inv_apply (fun i => ζ ^ (w i).val) G a b
  rw [hGentry]
  change ((fun i => ζ ^ (w i).val) a : K) * GM a b *
      (((fun i => ζ ^ (w i).val) b : K))⁻¹ = GM a b
  by_cases hI : a ∈ I ∧ b ∈ I
  · have hwab : w a = w b := hw a hI.1 b hI.2
    simp only [hwab]
    have he0 : ((fun i => ζ ^ (w i).val) b : K) ≠ 0 := Units.ne_zero _
    field_simp [he0]
  · have hg0 : GM a b = (1 : Matrix (Fin d) (Fin d) K) a b := by
      simpa only [GM, G] using
        (mem_unitaryBlock (h := h) (I := I)).mp hg a b (not_and_or.mp hI)
    rw [hg0]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq]
      have he0 : ((fun i => ζ ^ (w i).val) a : K) ≠ 0 := Units.ne_zero _
      field_simp [he0]
    · rw [Matrix.one_apply_ne hab]
      simp

private theorem permSU_swap_eq_permutationGL (h : UnitaryFieldData 2 1 K) (i i' : Fin d) :
    (permSU h (Equiv.swap i i') : GL (Fin d) K) =
      TauCeti.permutationGL (Equiv.swap i i') := by
  apply Units.ext
  rw [TauCeti.permutationGL_coe, Equiv.swap_inv]
  exact coe_permSU h (Equiv.swap i i')

private theorem diagConj_permutationGL (w : Fin d → Kˣ) (σ : Equiv.Perm (Fin d)) :
    TauCeti.diagGL w * TauCeti.permutationGL σ * (TauCeti.diagGL w)⁻¹ =
      TauCeti.permutationGL σ * TauCeti.diagGL ((fun i => w (σ i)) * w⁻¹) := by
  rw [TauCeti.diagGL_mul_permutationGL, mul_assoc, ← map_inv, ← map_mul]

private theorem permSU_swap_mem_unitaryBlock (h : UnitaryFieldData 2 1 K)
    {I : Finset (Fin d)} {i i' : Fin d} (hi : i ∈ I) (hi' : i' ∈ I) :
    permSU h (Equiv.swap i i') ∈ unitaryBlock h I := by
  rw [mem_unitaryBlock]
  intro a b hab
  rw [coe_permSU, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_eq, Matrix.submatrix_apply,
    Matrix.one_apply, Matrix.one_apply]
  by_cases hab' : a = b
  · subst hab'
    have ha : a ∉ I := by
      rcases hab with h | h
      · exact h
      · exact h
    have hai : a ≠ i := fun h => ha (h ▸ hi)
    have hai' : a ≠ i' := fun h => ha (h ▸ hi')
    simp [Equiv.swap_apply_of_ne_of_ne hai hai']
  · have hne : Equiv.swap i i' a ≠ b := by
      intro hb
      rcases hab with ha | hb'
      · have hai : a ≠ i := fun h => ha (h ▸ hi)
        have hai' : a ≠ i' := fun h => ha (h ▸ hi')
        rw [Equiv.swap_apply_of_ne_of_ne hai hai'] at hb
        exact hab' hb
      · have hbi : b ≠ i := fun h => hb' (h ▸ hi)
        have hbi' : b ≠ i' := fun h => hb' (h ▸ hi')
        have hbswap : Equiv.swap i i' b = b := Equiv.swap_apply_of_ne_of_ne hbi hbi'
        have : a = b := by
          calc a = Equiv.swap i i' (Equiv.swap i i' a) :=
                (Equiv.swap_apply_self i i' a).symm
            _ = Equiv.swap i i' b := by rw [hb]
            _ = b := hbswap
        exact hab' this
    simp [hab', hne]

private theorem zmod3_eq_of_pow_ratio_eq {ζ : Kˣ} (hζ : orderOf ζ = 3) {a b : ZMod 3}
    (h : ζ ^ a.val * (ζ ^ b.val)⁻¹ = ζ ^ b.val * (ζ ^ a.val)⁻¹) : a = b := by
  have hsq : (ζ ^ a.val) ^ 2 = (ζ ^ b.val) ^ 2 := by
    rw [pow_two, pow_two]
    exact div_eq_div_iff_mul_eq_mul.mp h
  have hsq' : (ζ ^ 2) ^ a.val = (ζ ^ 2) ^ b.val := by
    rw [← pow_mul, ← pow_mul]
    simpa [← pow_mul, Nat.mul_comm] using hsq
  have hord : orderOf (ζ ^ 2) = 3 := by
    rw [orderOf_pow' (x := ζ) (n := 2) (by norm_num), hζ]
    norm_num
  have hmod : a.val ≡ b.val [MOD 3] := by
    have := (pow_eq_pow_iff_modEq (x := ζ ^ 2) (n := a.val) (m := b.val)).mp hsq'
    rwa [hord] at this
  exact ZMod.val_injective 3
    (Nat.ModEq.eq_of_lt_of_lt hmod (ZMod.val_lt a) (ZMod.val_lt b))

private theorem exists_scalar_diagConj_swap_of_fix (hK : Nat.card K = 4) {ζ : Kˣ}
    (hζ : orderOf ζ = 3) {I : Finset (Fin d)} {w : Fin d → ZMod 3}
    {ψ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2))}
    (hψ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))
      (fun h h' => (h' : GL (Fin d) K) =
        TauCeti.diagGL (fun i => ζ ^ (w i).val) * (h : GL (Fin d) K) *
          (TauCeti.diagGL (fun i => ζ ^ (w i).val))⁻¹) ψ)
    (hfix : ∀ j ∈ suBlock hK I, ψ j = j)
    {i i' : Fin d} (hi : i ∈ I) (hi' : i' ∈ I) :
    ∃ u : Kˣ, TauCeti.diagGL
      ((fun k => ζ ^ (w (Equiv.swap i i' k)).val) * (fun k => ζ ^ (w k).val)⁻¹) =
      Matrix.GeneralLinearGroup.scalar (Fin d) u := by
  let h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, hK⟩
  let w' : Fin d → Kˣ := fun k => ζ ^ (w k).val
  let n : ↥(unitarySU 2 1 K d) := permSU h (Equiv.swap i i')
  let nL : ↥(LargeEvenSUGroup (Fin d) K 2) := ⟨(n : GL (Fin d) K), n.2⟩
  have hnGL : (nL : GL (Fin d) K) = TauCeti.permutationGL (Equiv.swap i i') := by
    simpa [nL, n] using permSU_swap_eq_permutationGL h i i'
  have hnmem : n ∈ unitaryBlock h I := by
    simpa [n] using permSU_swap_mem_unitaryBlock h hi hi'
  have hcoen : (n : ↥(LargeEvenSUGroup (Fin d) K 2)) = nL := rfl
  have hfixn : ψ (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2) nL) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2) nL := by
    simpa [hcoen] using hfix _ (by
      rw [suBlock]
      exact Subgroup.mem_map_of_mem _ hnmem)
  let D : GL (Fin d) K := TauCeti.diagGL w'
  have he : ∀ k, w' k ^ (2 + 1) = 1 := fun k => by
    rw [show (2 + 1 : ℕ) = 3 by norm_num, ← pow_mul, pow_mul' ζ (w k).val 3,
      (hζ ▸ pow_orderOf_eq_one ζ : ζ ^ 3 = 1), one_pow]
  let n' : ↥(LargeEvenSUGroup (Fin d) K 2) :=
    ⟨D * (nL : GL (Fin d) K) * D⁻¹,
      diagGL_mul_mul_inv_mem_largeEvenSUGroup (q := 2) (e := w') he nL.2⟩
  have hgraph : ψ (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2) nL) =
      LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2) n' := hψ nL n' rfl
  obtain ⟨u, hu⟩ :=
    (CFSG.Open.StatedAPI.statedProj_mk_eq_iff (LargeEvenSUGroup (Fin d) K 2) nL n').mp
      (hfixn.symm.trans hgraph)
  have huGL : (n' : GL (Fin d) K) = (nL : GL (Fin d) K) *
      Matrix.GeneralLinearGroup.scalar (Fin d) u := by
    apply Units.ext
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal] using hu
  have hDn : D * (nL : GL (Fin d) K) * D⁻¹ = (nL : GL (Fin d) K) *
      Matrix.GeneralLinearGroup.scalar (Fin d) u := by
    rw [show D * (nL : GL (Fin d) K) * D⁻¹ = (n' : GL (Fin d) K) from rfl, huGL]
  have hconjN : D * (nL : GL (Fin d) K) * D⁻¹ = (nL : GL (Fin d) K) *
      TauCeti.diagGL ((fun k => w' (Equiv.swap i i' k)) * w'⁻¹) := by
    simpa [D, ← hnGL] using diagConj_permutationGL w' (Equiv.swap i i')
  exact ⟨u, mul_left_cancel (hconjN.symm.trans hDn)⟩

private theorem unit_ratio_eq_of_fix_swap (hK : Nat.card K = 4) {ζ : Kˣ} (hζ : orderOf ζ = 3)
    {I : Finset (Fin d)} {w : Fin d → ZMod 3}
    {ψ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2))}
    (hψ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))
      (fun h h' => (h' : GL (Fin d) K) =
        TauCeti.diagGL (fun i => ζ ^ (w i).val) * (h : GL (Fin d) K) *
          (TauCeti.diagGL (fun i => ζ ^ (w i).val))⁻¹) ψ)
    (hfix : ∀ j ∈ suBlock hK I, ψ j = j)
    {i i' : Fin d} (hi : i ∈ I) (hi' : i' ∈ I) :
    ζ ^ (w i).val * (ζ ^ (w i').val)⁻¹ = ζ ^ (w i').val * (ζ ^ (w i).val)⁻¹ := by
  obtain ⟨u, hu⟩ := exists_scalar_diagConj_swap_of_fix hK hζ hψ hfix hi hi'
  have hc : (fun k => ζ ^ (w (Equiv.swap i i' k)).val) * (fun k => ζ ^ (w k).val)⁻¹ =
      (fun _ => u) := by
    apply TauCeti.diagGL_injective
    simpa [TauCeti.diagGL_const] using hu
  have h1 : ζ ^ (w i').val * (ζ ^ (w i).val)⁻¹ = u := by
    simpa [Equiv.swap_apply_left] using congrFun hc i
  have h2 : ζ ^ (w i).val * (ζ ^ (w i').val)⁻¹ = u := by
    simpa [Equiv.swap_apply_right] using congrFun hc i'
  exact h2.trans h1.symm

theorem forall_mem_suBlock_apply_eq_iff (hK : Nat.card K = 4) {ζ : Kˣ} (hζ : orderOf ζ = 3)
    (I : Finset (Fin d)) (w : Fin d → ZMod 3)
    {ψ : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K 2))}
    (hψ : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K 2))
      (fun h h' => (h' : GL (Fin d) K) =
        TauCeti.diagGL (fun i => ζ ^ (w i).val) * (h : GL (Fin d) K) *
          (TauCeti.diagGL (fun i => ζ ^ (w i).val))⁻¹) ψ) :
    (∀ j ∈ suBlock hK I, ψ j = j) ↔ ∀ i ∈ I, ∀ i' ∈ I, w i = w i' := by
  let h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, le_rfl, hK⟩
  constructor
  · intro hfix i hi i' hi'
    exact zmod3_eq_of_pow_ratio_eq hζ
      (unit_ratio_eq_of_fix_swap hK hζ hψ hfix hi hi')
  · intro hw j hj
    rw [suBlock] at hj
    obtain ⟨g, hg, rfl⟩ := hj
    exact hψ g g (diagGL_conj_eq_self_of_mem_unitaryBlock h hw hg).symm

end CFSG.StandardType.FrameRoute.UnitaryModel
