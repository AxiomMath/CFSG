module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1FieldCentL2Descent

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.FieldCent

open scoped MatrixGroups
open CFSG.GorensteinWalter
open CFSG.Assembly.RankThreeEven (projSL)

theorem simpleFixedRank_of_equiv_L2 {p e : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (he : 1 ≤ e)
    {X : Type} [Group X] [Finite X] {α : MulAut X}
    (h : Nonempty (Sec11.fixedSub α ≃* projSL 2 (GaloisField p e))) : SimpleFixedRank X α p e := by
  obtain ⟨φ0⟩ := h
  set F₀ := GaloisField p e with hF₀
  let φ : Sec11.fixedSub α ≃* PSL2 F₀ := φ0.trans (Sec4.projSLEquivPSL F₀)
  have hcard : Nat.card F₀ = p ^ e := GaloisField.card p e (by omega)
  have h4 : 4 ≤ Nat.card F₀ := by
    rw [hcard]
    exact le_trans (by omega) (Nat.le_self_pow (by omega : e ≠ 0) p)
  have hsimple : IsSimpleGroup (PSL2 F₀) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  have h3 : ((3 : ℕ) : F₀) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F₀ p]
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have h2 : ((2 : ℕ) : F₀) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F₀ p]
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have h2' : (2 : F₀) ≠ 0 := by simpa using h2
  have h2sq : (2 : F₀) ^ 2 ≠ 1 := by
    intro hh
    apply h3
    have h0 : (2 : F₀) ^ 2 - 1 = 0 := sub_eq_zero.2 hh
    have e3 : ((3 : ℕ) : F₀) = (2 : F₀) ^ 2 - 1 := by norm_num
    rw [e3, h0]
  have hperf : Group.IsPerfect (PSL2 F₀) :=
    ⟨SL2Simple.PSL_commutator_eq_top ⟨2, h2', h2sq⟩⟩
  have hperfK : Group.IsPerfect (Sec11.fixedSub α) :=
    Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  have hsimpleK : IsSimpleGroup (Sec11.fixedSub α) := MulEquiv.isSimpleGroup φ
  have hres : inSubgroup perfectResidual (Sec11.fixedSub α) = Sec11.fixedSub α := by
    have htop : perfectResidual (Sec11.fixedSub α) = ⊤ := by
      simp [perfectResidual, Group.IsPerfect.derivedSeries_eq_top]
    rw [inSubgroup, htop, Subgroup.map_top, Subgroup.range_subtype]
  have hnc : ¬ (∀ x y : Sec11.fixedSub α, x * y = y * x) := by
    intro hcomm
    haveI : IsMulCommutative (Sec11.fixedSub α) := ⟨⟨fun x y => hcomm x y⟩⟩
    exact Group.IsPerfect.not_isMulCommutative _ this
  have hrank : HasPRank (Sec11.fixedSub α) p e := by
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    let tv : Multiplicative F₀ →* SL(2, F₀) :=
      { toFun := fun t => Matrix.SpecialLinearGroup.transvection h01 (Multiplicative.toAdd t)
        map_one' := by
          have h := Matrix.SpecialLinearGroup.transvection_add h01 (0 : F₀) 0
          rw [add_zero] at h
          exact (mul_eq_left.1 h.symm)
        map_mul' := fun a b => Matrix.SpecialLinearGroup.transvection_add h01 _ _ }
    let u : Multiplicative F₀ →* PSL2 F₀ := (QuotientGroup.mk' (Subgroup.center SL(2, F₀))).comp tv
    have hu : Function.Injective u := by
      rw [injective_iff_map_eq_one]
      intro t ht
      have h1 : tv t ∈ Subgroup.center SL(2, F₀) := (QuotientGroup.eq_one_iff _).1 ht
      have h2 := (Matrix.SpecialLinearGroup.transvection_mem_center_iff h01 _).1 h1
      exact Multiplicative.toAdd.injective (by simpa using h2)
    let g : Multiplicative F₀ →* X :=
      (Sec11.fixedSub α).subtype.comp (φ.symm.toMonoidHom.comp u)
    have hg : Function.Injective g :=
      Subtype.val_injective.comp (φ.symm.injective.comp hu)
    refine ⟨g.range, ?_, ?_, ?_⟩
    · rintro _ ⟨t, rfl⟩
      exact (φ.symm (u t)).2
    · refine IsPGroup.of_card (n := e) ?_
      rw [← Nat.card_congr (MonoidHom.ofInjective hg).toEquiv]
      exact hcard
    · let lin : F₀ ≃ₗ[ZMod p] (Fin e → ZMod p) :=
        (Module.finBasisOfFinrankEq (ZMod p) F₀ (GaloisField.finrank p (by omega))).equivFun
      refine ⟨((AddEquiv.toMultiplicative lin.toAddEquiv).toMonoidHom).comp
        (MonoidHom.ofInjective hg).symm.toMonoidHom, ?_⟩
      exact (AddEquiv.toMultiplicative lin.toAddEquiv).surjective.comp
        (MonoidHom.ofInjective hg).symm.surjective
  unfold SimpleFixedRank
  rw [hres]
  exact ⟨hsimpleK, hnc, hrank⟩

theorem factFieldCentralizerL2Odd_holds : FactFieldCentralizerL2Odd := by
  intro p e _ hp he X _ _ hX α hα hαi
  exact simpleFixedRank_of_equiv_L2 hp he (nonempty_fixedSub_equiv_L2Odd hp he hX hα hαi)

end CFSG.RankThree.PartTwo.Sec11.SimsR1.FieldCent
