module

public import CFSG.Quasithin.Background.G9GolayTransport
public import CFSG.Quasithin.Background.SmithB45MatM22
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Bridge
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Toolkit

public section

namespace CFSG.Quasithin.G11

open CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

theorem exists_golayRelabel_pair {x y : Fin 24} (hxy : x ≠ y) :
    ∃ T : Equiv.Perm (Fin 24),
      (∀ w : GolayAmbient, w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode ↔
        permAct T w ∈ CFSG.Monster.Code.C) ∧ T 0 = x ∧ T 1 = y := by
  obtain ⟨τ, hτ, hτ0, hτ1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two x y hxy
  refine ⟨τ * golayRelabel, ?_, ?_, ?_⟩
  · exact source_iff_permAct_mul_mem_C mem_sourceGolayCode_iff_permAct_golayRelabel_mem_C hτ
  · rw [Equiv.Perm.mul_apply, golayRelabel_zero, hτ0]
  · rw [Equiv.Perm.mul_apply, golayRelabel_one, hτ1]

theorem golay22_group_iff {T : Equiv.Perm (Fin 24)} {x y : Fin 24}
    (hsrc : ∀ w : GolayAmbient, w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode ↔
      permAct T w ∈ CFSG.Monster.Code.C) (h0 : T 0 = x) (h1 : T 1 = y)
    (g : Equiv.Perm (Fin 24)) :
    g ∈ CFSG.Monster.Code.AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
        MulAction.stabilizer (Equiv.Perm (Fin 24)) y ↔
      ((∀ w : GolayAmbient, w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode ↔
          permAct (T⁻¹ * g * T) w ∈ CFSG.Blueprint.EvenSource.sourceGolayCode) ∧
        (true = true → (T⁻¹ * g * T) 0 = 0 ∧ (T⁻¹ * g * T) 1 = 1)) := by
  have hfix0 : (T⁻¹ * g * T) 0 = 0 ↔ g x = x := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h0, Equiv.Perm.inv_eq_iff_eq, h0]
  have hfix1 : (T⁻¹ * g * T) 1 = 1 ↔ g y = y := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, Equiv.Perm.inv_eq_iff_eq, h1]
  rw [Subgroup.mem_inf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, Equiv.Perm.smul_def,
    mem_AutPerm_iff_conj_preserves_source hsrc g, hfix0, hfix1]
  constructor
  · rintro ⟨⟨hA, hx⟩, hy⟩
    exact ⟨hA, fun _ => ⟨hx, hy⟩⟩
  · rintro ⟨hA, hrest⟩
    exact ⟨⟨hA, (hrest rfl).1⟩, (hrest rfl).2⟩

theorem card_golay22_group_le
    {x y : Fin 24} (hxy : x ≠ y) :
    Nat.card ↥(CFSG.Monster.Code.AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
        MulAction.stabilizer (Equiv.Perm (Fin 24)) y) ≤
      Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 := by
  obtain ⟨τ, hτ, hτ0, hτ1⟩ := CFSG.Monster.B.TwoA.autPerm_maps_two x y hxy
  let Γ : Subgroup (Equiv.Perm (Fin 24)) :=
    CFSG.Monster.Code.AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 24)) y
  change Nat.card ↥Γ ≤ Nat.card ↥CFSG.Blueprint.NativeSporadic.M22
  have hle : Nat.card ↥Γ ≤ Nat.card ↥CFSG.Quasithin.H.Mathieu.mog22 := by
    have hmem : ∀ g : ↥Γ, τ⁻¹ * (g : Equiv.Perm (Fin 24)) * τ ∈
        CFSG.Quasithin.H.Mathieu.mog22 := by
      intro g
      have hg : (g : Equiv.Perm (Fin 24)) ∈
          CFSG.Monster.Code.AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
            MulAction.stabilizer (Equiv.Perm (Fin 24)) y := g.2
      rw [Subgroup.mem_inf, Subgroup.mem_inf] at hg
      have hgx : (g : Equiv.Perm (Fin 24)) x = x :=
        (CFSG.Quasithin.H.Mathieu.mem_stab_iff x (g : Equiv.Perm (Fin 24))).1 hg.1.2
      have hgy : (g : Equiv.Perm (Fin 24)) y = y :=
        (CFSG.Quasithin.H.Mathieu.mem_stab_iff y (g : Equiv.Perm (Fin 24))).1 hg.2
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact CFSG.Monster.Code.AutPerm.mul_mem
          (CFSG.Monster.Code.AutPerm.mul_mem (CFSG.Monster.Code.AutPerm.inv_mem hτ) hg.1.1) hτ
      · exact (CFSG.Quasithin.H.Mathieu.mem_stab_iff 0
          (τ⁻¹ * (g : Equiv.Perm (Fin 24)) * τ)).2 (by
            rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτ0, hgx, ← hτ0]
            exact Equiv.symm_apply_apply τ 0)
      · exact (CFSG.Quasithin.H.Mathieu.mem_stab_iff 1
          (τ⁻¹ * (g : Equiv.Perm (Fin 24)) * τ)).2 (by
            rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτ1, hgy, ← hτ1]
            exact Equiv.symm_apply_apply τ 1)
    refine Nat.card_le_card_of_injective
      (fun g : ↥Γ => (⟨τ⁻¹ * (g : Equiv.Perm (Fin 24)) * τ, hmem g⟩ :
        ↥CFSG.Quasithin.H.Mathieu.mog22)) ?_
    intro a b hab
    have h : τ⁻¹ * (a : Equiv.Perm (Fin 24)) * τ =
        τ⁻¹ * (b : Equiv.Perm (Fin 24)) * τ := congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
  calc Nat.card ↥Γ ≤ Nat.card ↥CFSG.Quasithin.H.Mathieu.mog22 := hle
    _ = Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 :=
        Nat.card_congr (CFSG.Quasithin.H.Mathieu.mog22EquivM22).toEquiv

theorem mathieu22_golay_realization
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] {H : Subgroup (GLV V)} (irreducible : IsIrr H ⊤)
    (marking : Nonempty (↥H ≃* ↥CFSG.Blueprint.NativeSporadic.M22))
    (dimension : Module.finrank (ZMod 2) V = 10) : IsMathieu22CodeOrCocode H := by
  obtain ⟨m₀⟩ := marking
  have hcard : Nat.card (Multiplicative V) ≤ 2 ^ 30 := by
    rw [natCard_multiplicative]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases mathieuSmallIrr22_holds (Multiplicative V) mul_self_eq_one_multiplicative (toMulSub H)
      ⟨(toMulSubEquiv H).symm.trans m₀⟩ (isIrrOn_toMulSub irreducible).2 hcard with
    ⟨x, y, hxy, h⟩ | ⟨x, y, hxy, h⟩
  · obtain ⟨T, hsrc, h0, h1⟩ := exists_golayRelabel_pair hxy
    exact Or.inl (isGolaySectionModule_of_realizes m₀ true T (golay22_group_iff hsrc h0 h1)
      ((golayCorr_source hsrc).inf (golayCorr_pairKernel h0 h1)) (golayCorr_constantLine T) h
      (card_golay22_group_le hxy))
  · obtain ⟨T, hsrc, h0, h1⟩ := exists_golayRelabel_pair hxy
    exact Or.inr (isGolaySectionModule_of_realizes m₀ true T (golay22_group_iff hsrc h0 h1)
      (golayCorr_permCore T) ((golayCorr_source hsrc).sup (golayCorr_pairLine h0 h1)) h
      (card_golay22_group_le hxy))

end CFSG.Quasithin.G11
