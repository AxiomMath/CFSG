module

public import CFSG.RankThree.PartOne.K159.RowFourType
public import CFSG.RankThree.PartOne.K159.FamilyModel
public import CFSG.RankThree.PartOne.S15K.OrthFixedModel

public section

namespace CFSG.RankThree.PartOne.K159

open Polynomial Module CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.GroupTheory.WeirSylow QuadraticMap

section FixedSect

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

noncomputable def isometryTop (Q : QuadraticForm K V) :
    Q.IsometryEquiv (Q.comp (⊤ : Submodule K V).subtype) where
  toLinearEquiv := (LinearEquiv.ofTop ⊤ rfl).symm
  map_app' _ := rfl

theorem fixed_type (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) (hdim : finrank K V = 8) (hV : ¬ IsPlusType Q) (hx1 : x ≠ 1) :
    finrank K (fixedSpace x) = 2 ∨
      (finrank K (fixedSpace x) = 4 ∧ ¬ IsPlusType (Q.comp (fixedSpace x).subtype)) ∨
      (finrank K (fixedSpace x) = 6 ∧ IsPlusType (Q.comp (fixedSpace x).subtype)) := by
  classical
  obtain ⟨hcompl, horth⟩ := hx.fixed_others
  set W := fixedSpace x with hW
  set R := othersSpace x.toLinearMap (X - 1) with hR
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  obtain ⟨m, hm⟩ := hx.even_finrank_fixed
  have hRbot : R ≠ ⊥ := by
    intro hRb
    apply hx1
    have hW' : W = ⊤ := by
      have := hcompl.sup_eq_top
      rwa [hRb, sup_bot_eq] at this
    ext v
    have : v ∈ W := hW' ▸ Submodule.mem_top
    exact mem_fixedSpace.1 this
  have hRpos : 0 < finrank K R := by
    rcases Nat.eq_zero_or_pos (finrank K R) with h0 | h0
    · exact absurd (Submodule.finrank_eq_zero.1 h0) hRbot
    · exact h0
  have hRinv : ∀ u ∈ R, x u ∈ R := by
    intro u hu
    have hmap : R.map x.toLinearMap ≤ R := by
      rw [hR]
      unfold othersSpace
      rw [Submodule.map_iSup]
      refine iSup_le fun k => ?_
      rw [Submodule.map_iSup]
      refine iSup_le fun hk => ?_
      refine le_iSup₂_of_le k hk ?_
      rintro _ ⟨v, hv, rfl⟩
      exact apply_mem_primaryComponent (Commute.refl _) hv
    exact hmap ⟨u, hu, rfl⟩
  have hRfix : ∀ u ∈ R, x u = u → u = 0 := by
    intro u hu hxu
    have hW' : u ∈ W := mem_fixedSpace.2 hxu
    exact (Submodule.disjoint_def.1 hcompl.disjoint) u hW' hu
  have hRreg : RegOn Q R := by
    intro u hu hperp
    refine hx.regular u fun v => ?_
    obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hcompl v
    rw [QuadraticMap.polar_add_right, hperp r hr, QuadraticMap.polar_comm Q u w,
      horth w hw u hu, add_zero]
  have hR2 : Even (finrank K R) := by
    have : Even (finrank K W + finrank K R) := by rw [hsum, hdim]; exact ⟨4, rfl⟩
    exact (Nat.even_add.1 this).1 hx.even_finrank_fixed
  obtain ⟨k, hk⟩ := hR2
  have hRdim : finrank K R = 2 * k := by omega
  have hRtype := isPlusType_iff_even_of_fixedFree hx hp hp2 hpq k R hRinv hRreg hRfix hRdim
  by_cases h0 : finrank K W = 0
  · exfalso
    have hWb : W = ⊥ := Submodule.finrank_eq_zero.1 h0
    have hRtop : ⊤ = R := by
      have h := hcompl.sup_eq_top
      rw [hWb, bot_sup_eq] at h
      exact h.symm
    have hk4 : k = 4 := by omega
    subst hk4
    have hplus : IsPlusType (Q.comp R.subtype) := hRtype.2 ⟨2, rfl⟩
    exact hV ((isPlusType_congr ((isometryTop Q).trans (isometryOfEq Q hRtop))).2 hplus)
  · have hWpos : 1 ≤ finrank K W / 2 := by
      obtain ⟨m, hm'⟩ := hx.even_finrank_fixed
      omega
    have hWdim : finrank K W = 2 * (finrank K W / 2) := by
      obtain ⟨m, hm'⟩ := hx.even_finrank_fixed
      omega
    have hk1 : 1 ≤ k := by omega
    have eV : Q.IsometryEquiv ((Q.comp W.subtype).prod (Q.comp R.subtype)) :=
      (isometryTop Q).trans ((isometryOfEq Q hcompl.sup_eq_top.symm).trans
        (isometryEquivSup Q W R hcompl.disjoint horth))
    have htype : IsPlusType Q ↔ (IsPlusType (Q.comp W.subtype) ↔ IsPlusType (Q.comp R.subtype)) :=
      (isPlusType_congr eV).trans
        (isPlusType_prod_iff hx.polarBilin_fixed_nondegenerate (nondegenerate_of_regOn hRreg) hWpos
          hk1 hWdim hRdim)
    have hk3 : k ≤ 3 := by omega
    interval_cases k
    ·
      right; right
      refine ⟨by omega, ?_⟩
      by_contra hnW
      apply hV
      rw [htype]
      refine ⟨fun h => absurd h hnW, fun h => absurd (hRtype.1 h) (by decide)⟩
    ·
      right; left
      refine ⟨by omega, ?_⟩
      intro hpW
      apply hV
      rw [htype]
      exact ⟨fun _ => hRtype.2 ⟨1, rfl⟩, fun _ => hpW⟩
    · left
      omega

theorem exists_orthDerived_four_sl2 {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (R : QuadraticForm K W) (hR : (polarBilin R).Nondegenerate) (hdim : finrank K W = 4)
    (hts : ∀ U : Submodule K W, finrank K U = 2 → ∃ u ∈ U, R u ≠ 0) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2), Nat.card E = Nat.card K ^ 2 ∧
      Nonempty (↥(orthDerived R) ≃* Matrix.SpecialLinearGroup (Fin 2) E) := by
  obtain ⟨E, _, _, D, ψ, hψ⟩ := exists_evenMinus_model R hR (n := 2) (by norm_num) (by omega) hts
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) :=
    Finite.of_injective (fun g : W ≃ₗ[K] W => (g : W → W)) DFunLike.coe_injective
  have : CharP E 2 := charP_two_of_algebra (K := K)
  have := D.finite_E
  let e1 : R.IsometryEquiv (evenNormTailForm D.N 1) :=
    { toLinearEquiv := ψ
      map_app' := fun w => hψ w }
  let e2 : R.IsometryEquiv (hermFourForm D) := e1.trans (hermFourIsometry D)
  obtain ⟨-, -, -, -, -, -, -, -, hinj, -, -, -, -, -, -, -, hcomm, -⟩ :=
    even_minus_four_hermitian_derived_model D
  have hrange : orthDerived (hermFourForm D) = (hermFourRho D).range := hcomm
  let e3 : Matrix.SpecialLinearGroup (Fin 2) E ≃* ↥(orthDerived (hermFourForm D)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange.symm)
  exact ⟨E, inferInstance, inferInstance, inferInstance, D.card_E,
    ⟨(e3.trans (orthDerivedEquiv e2).symm).symm⟩⟩

theorem blockModelFour_fixedLayer_component (hQ : (polarBilin Q).Nondegenerate)
    (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2) {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1) (hdim : finrank K V = 8) (hV : ¬ IsPlusType Q)
    (hx1 : x ≠ 1) {n : ℕ} {C : Fin n → Subgroup (ProjOrthDerived Q)}
    (hCsup : (⨆ i, C i) = fixedLayerImage Q x)
    (hC : ∀ i, CFSG.IsQuasisimple ↥(C i) ∧ C i ≤ centralizerImage Q x ∧
      ((C i).subgroupOf (centralizerImage Q x)).IsSubnormal) (i : Fin n) :
    BlockModelFour p ↥(C i) := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  have hCi := hC i
  have hnb : C i ≠ ⊥ := ne_bot_of_isQuasisimple hCi.1
  have hlist : FixedLayerListed Q x := by
    by_contra hnl
    apply hnb
    have h0 : fixedLayerImage Q x = ⊥ := by simp [fixedLayerImage, hnl]
    rw [eq_bot_iff, ← h0, ← hCsup]
    exact le_iSup C i
  have hL : fixedLayerImage Q x = fixedComponentImage Q x := fixedLayerImage_of_listed hlist
  have h3 := hlist.1
  have hWnd := hx.polarBilin_fixed_nondegenerate
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  let φ₁ := fixedComponentImageEquiv hQ hx
  have hLN : fixedComponentImage Q x ≤ centralizerImage Q x := fixedComponentImage_le_centralizerImage
  have hLsub := hx.normal_fixedComponentImage.isSubnormal
  have hCc : IsComponent ((C i).subgroupOf (centralizerImage Q x)) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCi.2.1).symm hCi.1,
      hCi.2.2⟩
  have hCiL : C i ≤ fixedComponentImage Q x := by
    rw [← hL, ← hCsup]
    exact le_iSup C i
  have hEqOf : CFSG.IsQuasisimple ↥(fixedComponentImage Q x) → C i = fixedComponentImage Q x :=
    fun hLq => S15K.eq_of_isComponent_le hCi.2.1 hLN hCc
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLN).symm hLq,
        hLsub⟩ hCiL
  rcases fixed_type hx hp hp2 hpq' hdim hV hx1 with h2 | ⟨h4, hnp⟩ | ⟨h6, hpl⟩
  · omega
  ·
    have hd : finrank K (fixedSpace x) = 4 ∨ finrank K (fixedSpace x) = 6 := Or.inl h4
    have hts : ∀ U : Submodule K (fixedSpace x), finrank K U = finrank K (fixedSpace x) / 2 →
        ∃ u ∈ U, (Q.comp (fixedSpace x).subtype) u ≠ 0 := by
      intro U hU
      by_contra hcon
      push Not at hcon
      exact hnp ⟨U, by omega, hcon⟩
    obtain ⟨hqL, -⟩ := nonsplit_quasisimple_dicksonDerived (Q.comp (fixedSpace x).subtype) hWnd hd hts
    have hLq : CFSG.IsQuasisimple ↥(fixedComponentImage Q x) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv φ₁.symm hqL
    have hEq := hEqOf hLq
    obtain ⟨E, _, _, _, hE, ⟨e⟩⟩ := exists_orthDerived_four_sl2 (Q.comp (fixedSpace x).subtype) hWnd h4
      (fun U hU => hts U (by omega))
    refine Or.inl ⟨E, inferInstance, inferInstance, inferInstance, ?_,
      ⟨((MulEquiv.subgroupCongr hEq).trans φ₁).trans e⟩⟩
    rw [hE, hK, ← pow_mul]
    have h1 : 2 ^ f ∣ 2 ^ (f * 2) := pow_dvd_pow 2 (by omega)
    have h2 : p ∣ (2 ^ f) ^ 2 - 1 := by
      have : (2 ^ f + 1) ∣ (2 ^ f) ^ 2 - 1 := by
        refine ⟨2 ^ f - 1, ?_⟩
        have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
        obtain ⟨a, ha⟩ : ∃ a, 2 ^ f = a + 1 := ⟨2 ^ f - 1, by omega⟩
        rw [ha]
        simp only [Nat.add_sub_cancel]
        apply Nat.sub_eq_of_eq_add
        ring
      exact hpq.trans this
    rw [← pow_mul] at h2
    exact h2
  ·
    have hT : ∃ U : Submodule K (fixedSpace x), finrank K U = 3 ∧
        ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0 := by
      obtain ⟨U, hU, hUs⟩ := hpl
      exact ⟨U, by omega, hUs⟩
    have hLq := hx.isQuasisimple_fixedComponentImage hT
    have hEq := hEqOf hLq
    have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    obtain ⟨κ⟩ := Klein.klein_commutator_orthogonal_six (Q.comp (fixedSpace x).subtype) hWnd h6 hT hK4
    refine Or.inr ⟨K, inferInstance, inferInstance, inferInstance, ?_,
      ⟨(((MulEquiv.subgroupCongr hEq).trans φ₁).trans
        ((orthDerivedEquivCommutator _).symm.trans κ)).trans
          (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K).symm⟩⟩
    rw [hK]
    exact hpq

end FixedSect

end CFSG.RankThree.PartOne.K159
