module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
public import CFSG.RankThree.PartOne.AUTSL.FourData
public import CFSG.RankThree.PartOne.AUTSL.OmegaOut
public import CFSG.Quasithin.Background.BlueprintB2Defs
public import CFSG.RankThree.PartOne.KF1514B.Siegel
public import CFSG.RankThree.PartOne.KF1514B.Torus4

public section

namespace CFSG.StandardType

namespace OrthRestOdd

open Module CFSG.RankThree.Classical2 CFSG.Assembly

section Lin

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_isEndNode_of_isotropic (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hV : 8 ≤ finrank K V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {A : Subgroup (orthDerived Q)} (hA : IsElemAbelian p A)
    (hcard : p ^ (finrank K V / 2 - 1) ≤ Nat.card A) {Y : Submodule K V} (hY : Y ≠ ⊥)
    (hYinv : ∀ a ∈ A, ∀ y ∈ Y, (a : V ≃ₗ[K] V) y ∈ Y)
    (hYiso : ∀ y ∈ Y, ∀ y' ∈ Y, QuadraticMap.polar Q y y' = 0) :
    ∃ t, TableBOrth.IsEndNode A t := by
  classical
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  set E := A.map (orthDerived Q).subtype with hEdef
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hE : IsoGroup (QuadraticMap.polarBilin Q) p E :=
    { sep := hQ.1
      alt := fun v => by rw [QuadraticMap.polarBilin_apply_apply]; exact polar_self_eq_zero Q v
      comm := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        exact congrArg Subtype.val (TableB.IsElemAbelian.comm hA ha hb)
      pow := by
        rintro _ ⟨a, ha, rfl⟩
        rw [← map_pow, hA.2 a ha, map_one]
      pres := by
        rintro _ ⟨a, ha, rfl⟩ u w
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
        exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
          (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup a.2) u w }
  have hcardE : Nat.card E = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ Subtype.val_injective).toEquiv).symm
  obtain ⟨t', ⟨t, htA, rfl⟩, ht1, ht2⟩ := exists_commSpace_two_of_isotropic hp hpK hK1
    (by omega) hE hY (by rintro _ ⟨a, ha, rfl⟩ y hy; exact hYinv a ha y hy)
    (fun y hy y' hy' => by rw [QuadraticMap.polarBilin_apply_apply]; exact hYiso y hy y' hy')
    (hcardE ▸ hcard)
  exact ⟨t, isEndNode_of_commSpace_two hQ hV hp hp2 hK1 hA htA
    (fun h => ht1 (by rw [h]; rfl)) ht2⟩

omit [Finite K] [FiniteDimensional K V] in
theorem isotropic_of_involution {h : V ≃ₗ[K] V} (hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h2 : h * h = 1) (h1 : h ≠ 1) {A : Subgroup (orthDerived Q)}
    (hcomm : ∀ a ∈ A, (a : V ≃ₗ[K] V) * h = h * a) :
    CFSG.RankThree.PartOne.LIT.commSpace h ≠ ⊥ ∧
      (∀ a ∈ A, ∀ y ∈ CFSG.RankThree.PartOne.LIT.commSpace h,
        (a : V ≃ₗ[K] V) y ∈ CFSG.RankThree.PartOne.LIT.commSpace h) ∧
      ∀ y ∈ CFSG.RankThree.PartOne.LIT.commSpace h,
        ∀ y' ∈ CFSG.RankThree.PartOne.LIT.commSpace h, QuadraticMap.polar Q y y' = 0 := by
  refine ⟨commSpace_ne_bot h1, fun a ha y hy =>
    CFSG.RankThree.PartOne.LIT.map_mem_commSpace (hcomm a ha) hy, ?_⟩
  intro y hy y' hy'
  obtain ⟨u, rfl⟩ := CFSG.RankThree.PartOne.LIT.mem_commSpace.mp hy
  obtain ⟨v, rfl⟩ := CFSG.RankThree.PartOne.LIT.mem_commSpace.mp hy'
  have hpres := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hO
  have hhv : h (h v) = v := by
    rw [← LinearEquiv.mul_apply, h2]
    rfl
  have e1 : QuadraticMap.polar Q u (h v) = QuadraticMap.polar Q (h u) v := by
    rw [← hpres u (h v), hhv]
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_sub_right, QuadraticMap.polar_sub_right,
    hpres, e1]
  linear_combination (QuadraticMap.polar Q u v - QuadraticMap.polar Q (h u) v) * h2K

theorem isotropic_of_two_subgroup {V₀ : Subgroup (orthDerived Q)} (hV₀ : V₀ ≠ ⊥)
    (hV₀2 : IsPGroup 2 V₀)
    {A : Subgroup (orthDerived Q)} (hnorm : ∀ a ∈ A, ∀ v ∈ V₀, a * v * a⁻¹ ∈ V₀) :
    ∃ Y : Submodule K V, Y ≠ ⊥ ∧ (∀ a ∈ A, ∀ y ∈ Y, (a : V ≃ₗ[K] V) y ∈ Y) ∧
      ∀ y ∈ Y, ∀ y' ∈ Y, QuadraticMap.polar Q y y' = 0 := by
  classical
  have : Finite V := Module.finite_of_finite K
  set S := V₀.map (orthDerived Q).subtype with hS
  have hS2 : IsPGroup 2 S := hV₀2.map _
  have hBrefl : LinearMap.BilinForm.IsRefl (QuadraticMap.polarBilin Q) := fun u w h => by
    rw [QuadraticMap.polarBilin_apply_apply] at h ⊢
    rw [QuadraticMap.polar_comm]
    exact h
  let F : Submodule K V :=
    { carrier := {v | ∀ s ∈ S, s v = v}
      add_mem' := fun ha hb s hs => by rw [map_add, ha s hs, hb s hs]
      zero_mem' := fun s _ => map_zero s
      smul_mem' := fun c v hv s hs => by rw [map_smul, hv s hs] }
  have hmemF : ∀ v, v ∈ F ↔ ∀ s ∈ S, s v = v := fun v => Iff.rfl
  set F' := LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) F with hF'
  have hmemF' : ∀ v, v ∈ F' ↔ ∀ f ∈ F, QuadraticMap.polar Q f v = 0 := fun v => by
    rw [hF', LinearMap.BilinForm.mem_orthogonal_iff]
    rfl
  have hSpres : ∀ s ∈ S, ∀ u w, QuadraticMap.polar Q (s u) (s w) = QuadraticMap.polar Q u w := by
    rintro _ ⟨v, -, rfl⟩ u w
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
      (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup v.2) u w
  have hFinvS : ∀ s ∈ S, ∀ w ∈ F', s w ∈ F' := by
    intro s hs w hw
    rw [hmemF'] at hw ⊢
    intro f hf
    have h1 : s f = f := (hmemF f).mp hf s hs
    rw [← h1, hSpres s hs]
    exact hw f hf
  refine ⟨F ⊓ F', ?_, ?_, ?_⟩
  · intro hY
    have hdisj : Disjoint F F' := by rw [disjoint_iff]; exact hY
    have hc : IsCompl F F' :=
      (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hBrefl).mpr hdisj
    by_cases hF'0 : F' = ⊥
    · apply hV₀
      rw [Subgroup.eq_bot_iff_forall]
      intro v hv
      have hFtop : F = ⊤ := by rw [hF'0] at hc; exact eq_top_of_isCompl_bot hc
      apply Subtype.ext
      apply LinearEquiv.ext
      intro w
      have hw : w ∈ F := hFtop ▸ Submodule.mem_top
      exact (hmemF w).mp hw _ ⟨v, hv, rfl⟩
    · obtain ⟨w, hwF', hw0, hwfix⟩ :=
        CFSG.RankThree.PartOne.AUTSL.Four.exists_fixed_vector hS2 hF'0 hFinvS
      have hwF : w ∈ F := (hmemF w).mpr hwfix
      have : w ∈ F ⊓ F' := ⟨hwF, hwF'⟩
      rw [hY, Submodule.mem_bot] at this
      exact hw0 this
  · intro a ha y hy
    obtain ⟨hyF, hyF'⟩ := Submodule.mem_inf.mp hy
    have haS : ∀ s ∈ S, ((a : V ≃ₗ[K] V)⁻¹ * s * a) ∈ S := by
      rintro _ ⟨v, hv, rfl⟩
      exact ⟨a⁻¹ * v * a⁻¹⁻¹, hnorm _ (inv_mem ha) v hv, by simp⟩
    have haF : ∀ u ∈ F, (a : V ≃ₗ[K] V) u ∈ F := by
      intro u hu
      rw [hmemF] at hu ⊢
      intro s hs
      have h1 := hu _ (haS s hs)
      simp only [LinearEquiv.mul_apply] at h1
      have h2 := congrArg (a : V ≃ₗ[K] V) h1
      rw [← LinearEquiv.mul_apply, mul_inv_cancel] at h2
      exact h2
    refine Submodule.mem_inf.mpr ⟨haF y hyF, ?_⟩
    rw [hmemF'] at hyF' ⊢
    intro f hf
    have hpres := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
      (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup a.2)
    have hainv : (a : V ≃ₗ[K] V)⁻¹ f ∈ F := by
      rw [hmemF] at hf ⊢
      intro s hs
      have hs' : ((a : V ≃ₗ[K] V) * s * (a : V ≃ₗ[K] V)⁻¹) ∈ S := by
        obtain ⟨v, hv, rfl⟩ := hs
        exact ⟨a * v * a⁻¹, hnorm a ha v hv, by simp⟩
      have h1 := hf _ hs'
      simp only [LinearEquiv.mul_apply] at h1
      have h2 := congrArg (⇑((a : V ≃ₗ[K] V)⁻¹)) h1
      rw [← LinearEquiv.mul_apply ((a : V ≃ₗ[K] V)⁻¹) (a : V ≃ₗ[K] V), inv_mul_cancel] at h2
      exact h2
    have := hyF' _ hainv
    rw [← hpres, ← LinearEquiv.mul_apply, mul_inv_cancel] at this
    exact this
  · intro y hy y' hy'
    rw [QuadraticMap.polar_comm]
    exact (hmemF' y).mp (Submodule.mem_inf.mp hy).2 y' (Submodule.mem_inf.mp hy').1

end Lin

section Transport

variable {G H : Type*} [Group G] [Group H]

theorem isEndNode_of_map (e : G ≃* H) {A : Subgroup G} {t : H}
    (h : TableBOrth.IsEndNode (A.map e.toMonoidHom) t) : TableBOrth.IsEndNode A (e.symm t) := by
  have h1 := h.map e.symm
  rwa [Subgroup.map_map, show e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ from
    MonoidHom.ext fun x => e.symm_apply_apply x, Subgroup.map_id] at h1

theorem ggEndNodeEltAdm_of_isEndNode {p r : ℕ} {R : Type} [Group R]
    (h : ∀ A : Subgroup R, IsElemAbelian p A → p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
      (∃ U : Subgroup (MulAut R), U ≠ ⊥ ∧ IsPGroup 2 U ∧
        A.map (MulAut.conj : R →* MulAut R) ≤ Subgroup.normalizer (U : Set (MulAut R))) →
      ∃ t, TableBOrth.IsEndNode A t) : TableBUR.GGEndNodeEltAdm p r R := by
  intro A hA hr h3 hU
  obtain ⟨t, htA, ht1, hc, hs⟩ := h A hA hr h3 hU
  exact ⟨t, htA, ht1, hc, hs⟩

theorem ggEndNodeEltAdm_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R'] (φ : R ≃* R')
    (h : TableBUR.GGEndNodeEltAdm p r R) : TableBUR.GGEndNodeEltAdm p r R' := by
  refine ggEndNodeEltAdm_of_isEndNode fun A hA hr h3 ⟨U, hU1, hU2, hUN⟩ => ?_
  set A₀ := A.map φ.symm.toMonoidHom with hA₀
  have hcard : Nat.card A₀ = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ φ.symm.injective).toEquiv).symm
  set c := MulAut.congr φ with hc
  set U₀ := U.map c.symm.toMonoidHom with hU₀
  have hU₀1 : U₀ ≠ ⊥ := by
    intro h0
    apply hU1
    rw [eq_bot_iff]
    intro u hu
    have : c.symm u ∈ U₀ := ⟨u, hu, rfl⟩
    rw [h0, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot, ← c.apply_symm_apply u, this, map_one]
  have hU₀N : A₀.map (MulAut.conj : R →* MulAut R) ≤ Subgroup.normalizer (U₀ : Set (MulAut R)) := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    have hN := hUN ⟨a, ha, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro n
    have hconj : (MulAut.conj (φ.symm a) : MulAut R) = c.symm (MulAut.conj a) := by
      rw [MulEquiv.eq_symm_apply, hc, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj,
        MulEquiv.apply_symm_apply]
    have hn : ∀ m, m ∈ U₀ ↔ c m ∈ U := by
      intro m
      constructor
      · rintro ⟨u, hu, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
        exact hu
      · intro hm
        exact ⟨c m, hm, c.symm_apply_apply m⟩
    rw [MulEquiv.coe_toMonoidHom, hn, hn, hconj, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
    exact hN (c n)
  obtain ⟨t, htA, ht1, hcomp, hs⟩ := h A₀ (TableB.isElemAbelian_map hA _) (hcard ▸ hr)
    (hcard ▸ h3) ⟨U₀, hU₀1, hU2.map _, hU₀N⟩
  have hend : TableBOrth.IsEndNode A₀ t := ⟨htA, ht1, hcomp, hs⟩
  have := hend.map φ
  rw [hA₀, Subgroup.map_map, show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id R' from
    MonoidHom.ext fun x => φ.apply_symm_apply x, Subgroup.map_id] at this
  exact ⟨_, this⟩

end Transport

section Mat

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.AUTSL

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem exists_involution_of_conj (hZ : Subgroup.center (matrixDerived Q) = ⊥)
    {B : Subgroup (matrixDerived Q)} (g : matrixDerived Q) (r : matrixIsometries Q)
    (hr : r.val * r.val = 1)
    (hu1 : MulAut.conj g * conjAct Q (matrixIsometryInclusion Q r) ≠ 1)
    (hu2 : (MulAut.conj g * conjAct Q (matrixIsometryInclusion Q r)) ^ 2 = 1)
    (hcomm : ∀ b ∈ B, MulAut.conj b * (MulAut.conj g * conjAct Q (matrixIsometryInclusion Q r)) =
      (MulAut.conj g * conjAct Q (matrixIsometryInclusion Q r)) * MulAut.conj b) :
    g.val * r.val ∈ matrixIsometries Q ∧ (g.val * r.val) * (g.val * r.val) = 1 ∧
      g.val * r.val ≠ 1 ∧ ∀ b ∈ B, b.val * (g.val * r.val) = (g.val * r.val) * b.val := by
  set u := MulAut.conj g * conjAct Q (matrixIsometryInclusion Q r) with hu
  set h : GL (Fin d) K := g.val * r.val with hh
  have hgO : g.val ∈ matrixIsometries Q := matrixDerived_le_isometries Q g.2
  have hhO : h ∈ matrixIsometries Q := mul_mem hgO r.2
  have hr' : r.val⁻¹ = r.val := inv_eq_of_mul_eq_one_right hr
  have huval : ∀ X : matrixDerived Q, (u X).val = h * X.val * h⁻¹ := by
    intro X
    rw [hu, MulAut.mul_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjAct_inclusion_val]
    rw [hh, _root_.mul_inv_rev]
    group
  have hconjΓ : ∀ X : matrixDerived Q, h * X.val * h⁻¹ ∈ matrixDerived Q := fun X =>
    huval X ▸ (u X).2
  have hh2Γ : h * h ∈ matrixDerived Q := by
    have h1 : (conjAct Q (matrixIsometryInclusion Q r) g).val = r.val * g.val * r.val⁻¹ :=
      conjAct_inclusion_val r g
    have : h * h = g.val * (r.val * g.val * r.val⁻¹) := by
      rw [hh, hr']
      group
    rw [this, ← h1]
    exact mul_mem g.2 (conjAct Q (matrixIsometryInclusion Q r) g).2
  have hcent : ∀ c : matrixDerived Q, (∀ X : matrixDerived Q, c.val * X.val * c.val⁻¹ = X.val) →
      c = 1 := by
    intro c hc
    have : c ∈ Subgroup.center (matrixDerived Q) := by
      rw [Subgroup.mem_center_iff]
      intro X
      apply Subtype.ext
      have := hc X
      simp only [Subgroup.coe_mul]
      calc X.val * c.val = c.val * X.val * c.val⁻¹ * c.val := by rw [this]
        _ = c.val * X.val := by group
    rw [hZ, Subgroup.mem_bot] at this
    exact this
  have hsq : h * h = 1 := by
    have h1 := hcent ⟨h * h, hh2Γ⟩ fun X => by
      have := congrArg (fun φ : MulAut (matrixDerived Q) => (φ X).val) hu2
      simp only [pow_two, MulAut.mul_apply, MulAut.one_apply] at this
      rw [huval, huval] at this
      calc (h * h) * X.val * (h * h)⁻¹ = h * (h * X.val * h⁻¹) * h⁻¹ := by group
        _ = X.val := this
    exact congrArg Subtype.val h1
  refine ⟨hhO, hsq, ?_, ?_⟩
  · intro h1
    apply hu1
    refine MulEquiv.ext fun X => Subtype.ext ?_
    rw [huval, h1, one_mul, inv_one, mul_one]
    rfl
  · intro b hb
    have hhinv : h⁻¹ = h := inv_eq_of_mul_eq_one_right hsq
    have hc : h⁻¹ * b.val⁻¹ * h * b.val ∈ matrixDerived Q := by
      have h1 := hconjΓ b⁻¹
      rw [Subgroup.coe_inv, hhinv] at h1
      rw [hhinv]
      exact mul_mem h1 b.2
    have h1 := hcent ⟨_, hc⟩ fun X => by
      have := congrArg (fun φ : MulAut (matrixDerived Q) => (φ X).val) (hcomm b hb)
      simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [huval, huval] at this
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      calc (h⁻¹ * b.val⁻¹ * h * b.val) * X.val * (h⁻¹ * b.val⁻¹ * h * b.val)⁻¹ =
          h⁻¹ * b.val⁻¹ * (h * (b.val * X.val * b.val⁻¹) * h⁻¹) * b.val * h := by group
        _ = h⁻¹ * b.val⁻¹ * (b.val * (h * X.val * h⁻¹) * b.val⁻¹) * b.val * h := by rw [this]
        _ = X.val := by group
    have h2 : h⁻¹ * b.val⁻¹ * h * b.val = 1 := congrArg Subtype.val h1
    calc b.val * h = b.val * h * (h⁻¹ * b.val⁻¹ * h * b.val) := by rw [h2, mul_one]
      _ = h * b.val := by group

end Mat
