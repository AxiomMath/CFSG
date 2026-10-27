module

public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveOrthMinusHolds

public section

namespace CFSG.StandardType

namespace OPlusEight

open Polynomial Module CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2 CFSG.StandardType.OrthRestOdd
  CFSG.StandardType.IOneOrthEnd

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem fixes_of_commSpace_two (hK1 : ∀ c : K, c ^ 3 = 1 → c = 1)
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x)
    (hx2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace x) = 2) {Y : Submodule K V}
    (hYinv : ∀ y ∈ Y, x y ∈ Y) (hYQ : ∀ y ∈ Y, Q y = 0) : ∀ y ∈ Y, x y = y := by
  intro y hy
  by_contra hne
  set z := x y - y with hz
  have hz0 : z ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  have hzY : z ∈ Y := Y.sub_mem (hYinv y hy) hy
  have hzW : z ∈ CFSG.RankThree.PartOne.LIT.commSpace x :=
    CFSG.RankThree.PartOne.LIT.mem_commSpace.mpr ⟨y, rfl⟩
  have hc := CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hx.cast_ne_zero
    hx.pow_eq_one
  have h3 : ∀ v, x (x (x v)) = v := fun v => by
    have := congrArg (fun f : V ≃ₗ[K] V => f v) hx.pow_eq_one
    simpa [pow_succ] using this
  have hWinv : ∀ w ∈ CFSG.RankThree.PartOne.LIT.commSpace x,
      x w ∈ CFSG.RankThree.PartOne.LIT.commSpace x := by
    intro w hw
    obtain ⟨v, rfl⟩ := CFSG.RankThree.PartOne.LIT.mem_commSpace.mp hw
    exact CFSG.RankThree.PartOne.LIT.mem_commSpace.mpr ⟨x v, by rw [map_sub]⟩
  have horth : ∀ u ∈ CFSG.RankThree.PartOne.LIT.fixedSpace x,
      ∀ w ∈ CFSG.RankThree.PartOne.LIT.commSpace x, QuadraticMap.polar Q u w = 0 := by
    intro u hu w hw
    obtain ⟨v, rfl⟩ := CFSG.RankThree.PartOne.LIT.mem_commSpace.mp hw
    have hu' : x u = u := CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mp hu
    have h1 : QuadraticMap.polar Q u (x v) = QuadraticMap.polar Q u v := by
      rw [QuadraticMap.polar_comm, hx.polar_apply, QuadraticMap.polar_comm]
      have : x.symm u = u := by rw [LinearEquiv.symm_apply_eq]; exact hu'.symm
      rw [this]
    rw [QuadraticMap.polar_sub_right, h1, sub_self]
  have hfixcomm : CFSG.RankThree.PartOne.LIT.fixedSpace x ⊓
      CFSG.RankThree.PartOne.LIT.commSpace x = ⊥ := hc.inf_eq_bot
  have hsum : z + x z + x (x z) = 0 := by
    have hmem : z + x z + x (x z) ∈ CFSG.RankThree.PartOne.LIT.fixedSpace x ⊓
        CFSG.RankThree.PartOne.LIT.commSpace x := by
      refine ⟨CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mpr ?_, ?_⟩
      · rw [map_add, map_add, h3]
        abel
      · exact (CFSG.RankThree.PartOne.LIT.commSpace x).add_mem
          ((CFSG.RankThree.PartOne.LIT.commSpace x).add_mem hzW (hWinv z hzW))
          (hWinv _ (hWinv z hzW))
    rw [hfixcomm, Submodule.mem_bot] at hmem
    exact hmem
  have hxzW := hWinv z hzW
  have hli : LinearIndependent K ![z, x z] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hz0, rfl⟩
    · exfalso
      have hxz : x z = (-(s / t)) • z := by
        have : t • x z = -(s • z) := eq_neg_of_add_eq_zero_right hst
        calc x z = t⁻¹ • (t • x z) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = (-(s / t)) • z := by rw [this, smul_neg, smul_smul, ← neg_smul, div_eq_inv_mul]
      set c : K := -(s / t) with hcdef
      have hc3 : c ^ 3 = 1 := by
        have h31 : z = c ^ 3 • z := by
          calc z = x (x (x z)) := (h3 z).symm
            _ = c ^ 3 • z := by
              rw [hxz, map_smul, map_smul, hxz, map_smul, hxz, smul_smul, smul_smul]
              congr 1
              ring
        have : (c ^ 3 - 1) • z = 0 := by rw [sub_smul, one_smul, ← h31, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hz0)
      have hc1 := hK1 c hc3
      rw [hc1, one_smul] at hxz
      have : z ∈ CFSG.RankThree.PartOne.LIT.fixedSpace x ⊓
          CFSG.RankThree.PartOne.LIT.commSpace x :=
        ⟨CFSG.RankThree.PartOne.LIT.mem_fixedSpace.mpr hxz, hzW⟩
      rw [hfixcomm, Submodule.mem_bot] at this
      exact hz0 this
  have hspan : Submodule.span K (Set.range ![z, x z]) =
      CFSG.RankThree.PartOne.LIT.commSpace x := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hzW
      · exact hxzW
    · rw [finrank_span_eq_card hli, hx2]
      simp
  have hYp : ∀ a ∈ Y, ∀ b ∈ Y, QuadraticMap.polar Q a b = 0 := fun a ha b hb => by
    have h1 := hYQ (a + b) (Y.add_mem ha hb)
    rw [QuadraticMap.polar, h1, hYQ a ha, hYQ b hb]
    simp
  have hxzY : x z ∈ Y := hYinv z hzY
  apply hz0
  refine hx.regular z fun v => ?_
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add_of_isCompl hc v
  rw [QuadraticMap.polar_add_right, QuadraticMap.polar_comm, horth u hu z hzW, zero_add]
  rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at hw
  obtain ⟨f, rfl⟩ := hw
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right,
    polar_self_eq_zero Q z, hYp z hzY (x z) hxzY]
  simp

theorem exists_twoSubgroup_layer_eight (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hV : 8 ≤ finrank K V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {A : Subgroup (orthDerived Q)} (hA : IsElemAbelian p A)
    {t : orthDerived Q} (htA : t ∈ A)
    (ht2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace (t : V ≃ₗ[K] V)) = 2)
    {Y' : Submodule K V} (hY'0 : Y' ≠ ⊥) (hY'Q : ∀ y ∈ Y', Q y = 0)
    (hY'inv : ∀ a ∈ A, ∀ y ∈ Y', (a : V ≃ₗ[K] V) y ∈ Y')
    (hY'fix : ∀ y ∈ Y', (t : V ≃ₗ[K] V) y = y) :
    ∃ U : Subgroup (orthDerived Q),
      U ≤ LargeEvenLayer (Subgroup.centralizer ({t} : Set (orthDerived Q))) ∧ U ≠ ⊥ ∧
        IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set (orthDerived Q)) := by
  classical
  have htp : t ^ p = 1 := hA.2 t htA
  have hlay := layer_eq_of_commSpace_two hQ (by omega) hp hp2 hK1 htp ht2
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  set x : V ≃ₗ[K] V := ↑t with hxdef
  have hxp : x ^ p = 1 := by
    rw [hxdef, ← Subgroup.coe_pow, htp]
    rfl
  have hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup t.2
  have hx : OddOrderIsometry Q p x := ⟨hxO, hxp, hpK, fun v hv => hQ.1 v fun w => by
    rw [QuadraticMap.polarBilin_apply_apply]; exact hv w⟩
  have hc := CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hpK hxp
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hW6 : 6 ≤ finrank K (fixedSpace x) := by rw [fixedSpace_eq_lit]; omega
  set W : Submodule K V := fixedSpace x with hW
  set QW : QuadraticForm K W := Q.comp W.subtype with hQW
  have hQWnd : (QuadraticMap.polarBilin QW).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  have hY'W : Y' ≤ W := fun y hy => mem_fixedSpace.mpr (hY'fix y hy)
  set YW : Submodule K W := Y'.comap W.subtype with hYW
  have hmemYW : ∀ y : W, y ∈ YW ↔ (y : V) ∈ Y' := fun y => Iff.rfl
  have hYW0 : YW ≠ ⊥ := by
    intro h
    obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY'0
    have hmem : (⟨y, hY'W hyY⟩ : W) ∈ YW := hyY
    rw [h, Submodule.mem_bot] at hmem
    exact hy0 (congrArg Subtype.val hmem)
  have hYWQ : ∀ y ∈ YW, QW y = 0 := fun y hy => hY'Q (y : V) hy
  have hYWp : ∀ y ∈ YW, ∀ y' ∈ YW, QuadraticMap.polar QW y y' = 0 := by
    intro y hy y' hy'
    have h1 := hYWQ (y + y') (YW.add_mem hy hy')
    rw [QuadraticMap.polar, hYWQ y hy, hYWQ y' hy', h1]
    simp
  set H : Subgroup (W ≃ₗ[K] W) := orthDerived QW with hH
  set UW := LIDTwDF.radSub QW YW hYWp H with hUW
  obtain ⟨x₁, hx₁Y, w₁, hw₁P, hsing, hind⟩ := LIDTwDF.exists_siegel_pair hQWnd
    (by omega : 5 ≤ finrank K W) hYW0 hYWQ
  have hσH : OrthBstarOdd.siegEquiv hsing ∈ H := by
    by_cases hT : ∃ T : Submodule K W, finrank K T = 3 ∧ ∀ u ∈ T, QW u = 0
    · exact CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQWnd hT
        (OrthBstarOdd.siegEquiv_mem_omegaGroup hQWnd hsing)
    · push Not at hT
      obtain ⟨k, hk⟩ := even_finrank_of_regular QW hQWnd
      have h6 : finrank K W = 6 := by
        by_contra h6
        obtain ⟨T, hT3, hT0⟩ := exists_totallySingular_three QW hQWnd (by omega)
        obtain ⟨u, hu, hu0⟩ := hT T hT3
        exact hu0 (hT0 u hu)
      exact CFSG.SeitzReduction.OmegaPilot.omegaGroup_le_orthDerived_of_six hQWnd h6 hT
        (OrthBstarOdd.siegEquiv_mem_omegaGroup hQWnd hsing)
  have hσU : OrthBstarOdd.siegEquiv hsing ∈ UW :=
    LIDTwDF.siegEquiv_mem_radSub hsing hx₁Y hw₁P hσH
  have hσ1 : OrthBstarOdd.siegEquiv hsing ≠ 1 := OrthBstarOdd.siegEquiv_ne_one hQWnd hsing hind
  have hσO : OrthBstarOdd.siegEquiv hsing ∈ TauCeti.QuadraticMap.orthogonalGroup QW :=
    OrthBstarOdd.siegEquiv_mem_orthogonalGroup hsing
  set Ũ : Subgroup (V ≃ₗ[K] V) :=
    (UW.comap (restrictFixed Q x)).map (supportedBlock Q x (X - 1)).subtype with hŨ
  have hŨD : Ũ ≤ supportedFixedDerived Q x := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' : restrictFixed Q x g ∈ UW := hg
    exact ⟨g, hg'.1, rfl⟩
  have hŨΩ : Ũ ≤ orthDerived Q := hŨD.trans hx.supportedFixedDerived_le_orthDerived
  refine ⟨Ũ.subgroupOf (orthDerived Q), ?_, ?_, ?_, ?_⟩
  · rw [hlay]
    intro u hu
    exact hŨD (Subgroup.mem_subgroupOf.mp hu)
  · intro hbot
    obtain ⟨g, hg⟩ := restrictFixed_surjective hx _ hσO
    have hgU : (g : V ≃ₗ[K] V) ∈ Ũ := ⟨g, by simpa [hg] using hσU, rfl⟩
    have hmem : (⟨(g : V ≃ₗ[K] V), hŨΩ hgU⟩ : orthDerived Q) ∈ Ũ.subgroupOf (orthDerived Q) :=
      hgU
    rw [hbot, Subgroup.mem_bot] at hmem
    have hg1' : (g : V ≃ₗ[K] V) = 1 := congrArg Subtype.val hmem
    have hg1 : g = 1 := Subtype.ext hg1'
    rw [hg1, map_one] at hg
    exact hσ1 hg.symm
  · have h1 : IsPGroup 2 UW := LIDTwDF.isPGroup_radSub
    have h2 : IsPGroup 2 (UW.comap (restrictFixed Q x)) :=
      h1.comap_of_injective _ (restrictFixed_injective hx)
    have h3 : IsPGroup 2 Ũ := h2.map _
    exact h3.comap_of_injective (orthDerived Q).subtype (orthDerived Q).subtype_injective
  · rw [Subgroup.le_normalizer_iff]
    intro a ha u hu
    have hat : (a : V ≃ₗ[K] V) ∈ isometryCentralizer Q x := by
      rw [isometryCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      refine ⟨CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup a.2, ?_⟩
      exact congrArg Subtype.val (TableB.IsElemAbelian.comm hA ha htA)
    have hacent : (a : V ≃ₗ[K] V) ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) :=
      (Subgroup.mem_inf.mp hat).2
    have hW1 : ∀ w ∈ W, (a : V ≃ₗ[K] V) w ∈ W := fun w hw => mem_fixedSpace_of_apply hacent hw
    have hW2 : ∀ w ∈ W, (a : V ≃ₗ[K] V).symm w ∈ W := fun w hw =>
      mem_fixedSpace_of_apply (symm_mem_centralizer x hacent) hw
    set φ : W ≃ₗ[K] W := restrictEquiv W (a : V ≃ₗ[K] V) hW1 hW2 with hφ
    have hφapp : ∀ w : W, ((φ w : W) : V) = (a : V ≃ₗ[K] V) (w : V) := fun w => rfl
    have hφsymm : ∀ w : W, (((φ⁻¹) w : W) : V) = (a : V ≃ₗ[K] V).symm (w : V) := fun w => rfl
    have hφQ : ∀ w, QW (φ w) = QW w := fun w => by
      have := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup a.2)) (w : V)
      simpa [hQW, QuadraticMap.comp_apply, hφapp] using this
    have hφO : φ ∈ TauCeti.QuadraticMap.orthogonalGroup QW :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hφQ
    have hφY : ∀ y ∈ YW, φ y ∈ YW := fun y hy => hY'inv a ha (y : V) hy
    have hφYi : ∀ y ∈ YW, φ⁻¹ y ∈ YW := by
      intro y hy
      have : (a : V ≃ₗ[K] V).symm (y : V) = ((a⁻¹ : orthDerived Q) : V ≃ₗ[K] V) (y : V) := rfl
      rw [hmemYW, hφsymm, this]
      exact hY'inv a⁻¹ (A.inv_mem ha) (y : V) hy
    obtain ⟨g, hg, hgu⟩ := hu
    have hconj : (a : V ≃ₗ[K] V) * g.1 * (a : V ≃ₗ[K] V)⁻¹ ∈ supportedBlock Q x (X - 1) :=
      conj_mem_supportedBlock hat g.2
    have hrf : restrictFixed Q x ⟨(a : V ≃ₗ[K] V) * g.1 * (a : V ≃ₗ[K] V)⁻¹, hconj⟩ =
        φ * restrictFixed Q x g * φ⁻¹ := by
      refine LinearEquiv.ext fun w => Subtype.ext ?_
      rw [coe_restrictFixed]
      simp only [LinearEquiv.mul_apply, hφapp, hφsymm, coe_restrictFixed]
      rfl
    have hmemU : φ * restrictFixed Q x g * φ⁻¹ ∈ UW :=
      LIDTwDF.conj_mem_radSub hφQ hφY hφYi
        (fun h hh => conj_mem_orthDerived' hφO hh) hg
    have : (⟨(a : V ≃ₗ[K] V) * g.1 * (a : V ≃ₗ[K] V)⁻¹, hconj⟩ :
        ↥(supportedBlock Q x (X - 1))) ∈ UW.comap (restrictFixed Q x) := by
      show restrictFixed Q x _ ∈ UW
      rw [hrf]
      exact hmemU
    have hmemŨ : (a : V ≃ₗ[K] V) * g.1 * (a : V ≃ₗ[K] V)⁻¹ ∈ Ũ := ⟨_, this, rfl⟩
    show ((a * u * a⁻¹ : orthDerived Q) : V ≃ₗ[K] V) ∈ Ũ
    have hgu' : (u : V ≃ₗ[K] V) = g.1 := hgu.symm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hgu']
    exact hmemŨ


theorem exists_twoSubgroup_of_commSpace_two (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hV : 8 ≤ finrank K V) (hK1 : ∀ c : K, c ^ 3 = 1 → c = 1)
    {A : Subgroup (orthDerived Q)} (hA : IsElemAbelian 3 A)
    (hU : ∃ U : Subgroup (orthDerived Q), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      A ≤ Subgroup.normalizer (U : Set (orthDerived Q)))
    {t : orthDerived Q} (htA : t ∈ A)
    (ht2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace (t : V ≃ₗ[K] V)) = 2) :
    ∃ U : Subgroup (orthDerived Q),
      U ≤ LargeEvenLayer (Subgroup.centralizer ({t} : Set (orthDerived Q))) ∧ U ≠ ⊥ ∧
        IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set (orthDerived Q)) := by
  classical
  obtain ⟨V₀, hV₀1, hV₀2, hAV₀⟩ := hU
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hpK : ((3 : ℕ) : K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  set E := A.map (orthDerived Q).subtype with hEdef
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hEQ : ∀ g ∈ E, ∀ v, Q (g v) = Q v := by
    rintro _ ⟨a, -, rfl⟩ v
    exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup a.2)) v
  have hEp : ∀ g ∈ E, g ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA.2 a ha, map_one]
  obtain ⟨Y, hY0, hYinv, hYQ⟩ := OrthBstarOdd.exists_singular_of_two hQ hK1
    (S := V₀.map (orthDerived Q).subtype) (N := E) (hV₀2.map _)
    (by
      rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)]
      exact hV₀1)
    (by
      rintro _ ⟨s, -, rfl⟩ v
      exact (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup s.2)) v)
    (by
      rintro _ ⟨s, -, rfl⟩
      exact (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp
        (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ s.2)).2)
    hEQ hEp
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨v, hv, rfl⟩
      exact ⟨a * v * a⁻¹, Subgroup.le_normalizer_iff.mp hAV₀ a ha v hv, by simp⟩)
  have htp : t ^ 3 = 1 := hA.2 t htA
  have hxO : (t : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup t.2
  have hxp : (t : V ≃ₗ[K] V) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, htp]
    rfl
  have hx : OddOrderIsometry Q 3 (t : V ≃ₗ[K] V) := ⟨hxO, hxp, hpK, fun v hv => hQ.1 v fun w => by
    rw [QuadraticMap.polarBilin_apply_apply]; exact hv w⟩
  have hYfix : ∀ y ∈ Y, (t : V ≃ₗ[K] V) y = y :=
    fixes_of_commSpace_two hK1 hx ht2
      (fun y hy => hYinv _ ⟨t, htA, rfl⟩ y hy) hYQ
  exact exists_twoSubgroup_layer_eight hQ hV hp hp2 hK1 hA htA ht2 hY0 hYQ
    (fun a ha y hy => hYinv _ ⟨a, ha, rfl⟩ y hy) hYfix

end OPlusEight

end CFSG.StandardType

end
