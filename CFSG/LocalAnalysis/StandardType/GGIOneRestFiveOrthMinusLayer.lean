module

public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndElt
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDTwDFieldRad
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveOrthMinusCount
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega

public section

namespace CFSG.StandardType

namespace IOneOrthEnd

open Polynomial Module CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2 CFSG.StandardType.OrthRestOdd

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

open scoped commutatorElement in
theorem conj_mem_orthDerived' {W : Type} [AddCommGroup W] [Module K W] {R : QuadraticForm K W}
    {g x : W ≃ₗ[K] W} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup R) (hx : x ∈ orthDerived R) :
    g * x * g⁻¹ ∈ orthDerived R := by
  have hxO := CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup hx
  have e : g * x * g⁻¹ = ⁅g, x⁆ * x := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (Subgroup.commutator_mem_commutator hg hxO) hx

theorem layer_eq_of_commSpace_two (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hV : 8 ≤ finrank K V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {t : orthDerived Q} (htp : t ^ p = 1)
    (ht2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace (t : V ≃ₗ[K] V)) = 2) :
    LargeEvenLayer (Subgroup.centralizer ({t} : Set (orthDerived Q))) =
      (supportedFixedDerived Q (t : V ≃ₗ[K] V)).subgroupOf (orthDerived Q) := by
  classical
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
  obtain ⟨hq, hcenter, hodd⟩ := orthDerived_facts (Q.comp (fixedSpace x).subtype)
    hx.polarBilin_fixed_nondegenerate hW6
  set D₀ := supportedFixedDerived Q x with hD₀
  have hD₀Ω : D₀ ≤ orthDerived Q := hx.supportedFixedDerived_le_orthDerived
  set D : Subgroup (orthDerived Q) := D₀.subgroupOf (orthDerived Q) with hD
  have hmemC : ∀ y : orthDerived Q,
      y ∈ Subgroup.centralizer ({t} : Set (orthDerived Q)) ↔
        (y : V ≃ₗ[K] V) ∈ isometryCentralizer Q x := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff, isometryCentralizer, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup y.2,
        congrArg Subtype.val h⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext h
  have hDH : D ≤ Subgroup.centralizer ({t} : Set (orthDerived Q)) := by
    intro y hy
    rw [hmemC]
    exact supportedFixedDerived_le_isometryCentralizer (Subgroup.mem_subgroupOf.mp hy)
  have hcomm : ∀ g ∈ Subgroup.centralizer ({t} : Set (orthDerived Q)),
      ∀ h ∈ Subgroup.centralizer ({t} : Set (orthDerived Q)), g * h * g⁻¹ * h⁻¹ ∈ D := by
    intro g hg h hh
    rw [hD, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact commutator_mem_supportedFixedDerived hx hK1 ht2 ((hmemC g).mp hg) ((hmemC h).mp hh)
  have hDq : CFSG.IsQuasisimple D := by
    have e1 : D ≃* D₀ := Subgroup.subgroupOfEquivOfLe hD₀Ω
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (e1.trans (supportedFixedDerivedEquiv hx)).symm hq
  obtain ⟨hlay, -⟩ := TableBSymp.largeEvenLayer_eq_of_commutator_mem hDH hcomm hDq
  exact hlay

theorem exists_twoSubgroup_layer (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hV : 10 ≤ finrank K V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
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
  have hW8 : 8 ≤ finrank K (fixedSpace x) := by rw [fixedSpace_eq_lit]; omega
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
  have hT3 := exists_totallySingular_three QW hQWnd hW8
  have hσH : OrthBstarOdd.siegEquiv hsing ∈ H :=
    CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQWnd hT3
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

end IOneOrthEnd

end CFSG.StandardType
