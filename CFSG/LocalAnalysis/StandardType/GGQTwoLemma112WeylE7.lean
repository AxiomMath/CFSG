module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112K
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleE
public import CFSG.LocalAnalysis.StandardType.GGReflClosedIndep
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoInnerDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggQ2xKDf7_reindex_refl {ι : Type*} (M : CoxeterMatrix ι) :
    M.reindex (Equiv.refl ι) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

private lemma ggQ2xKDf7_range_simpleRefl {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    {ι : Type} (h : ι → U) (α : ι → Module.Dual (ZMod 3) U) (s : ι → U ≃ₗ[ZMod 3] U)
    (hs : ∀ i v, s i v = v - α i v • h i) :
    Set.range s = {t : U ≃ₗ[ZMod 3] U | ∃ j, ∀ v, t v = v - α j v • h j} := by
  ext t
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, hs i⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, LinearEquiv.ext fun v => by rw [hj v, hs j v]⟩

private lemma ggQ2xKDf7_isReflLin_form {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    [Fact (Nat.Prime 3)] (t : U ≃ₗ[ZMod 3] U) (ht : IsReflLin t) :
    ∃ (v : U) (f : Module.Dual (ZMod 3) U), ∀ x, t x = x - f x • v := by
  obtain ⟨c, φ, hφ, rfl⟩ := ht
  exact ⟨c, φ, fun x => Module.reflection_apply x hφ⟩

private lemma ggQ2xKDf7_sq_of_isReflLin {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    [Fact (Nat.Prime 3)] (t : U ≃ₗ[ZMod 3] U) (ht : IsReflLin t) : t ^ 2 = 1 := by
  obtain ⟨c, φ, hφ, rfl⟩ := ht
  ext x
  rw [pow_two, LinearEquiv.mul_apply]
  simpa using Module.involutive_reflection hφ x

private lemma ggQ2xKDf7_reflection_ne_one {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (c : U) (f : Module.Dual (ZMod 3) U) (hf : f c = 2) : Module.reflection hf ≠ 1 := by
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hf
    exact (by decide : (2 : ZMod 3) ≠ 0) hf.symm
  intro h1
  have h2 : Module.reflection hf c = c := by rw [h1]; rfl
  rw [Module.reflection_apply, hf] at h2
  have h3 : (2 : ZMod 3) • c = 0 := sub_eq_self.mp h2
  exact hc ((smul_eq_zero.mp h3).resolve_left (by decide))

private lemma ggQ2xKDf7_conj_mem {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    [Fact (Nat.Prime 3)] (hfin : Finite U) (h : Fin 7 → U) (hb : LinearIndependent (ZMod 3) h)
    (α : Fin 7 → Module.Dual (ZMod 3) U)
    (hα : ∀ i j, α i (h j) = ((CartanMatrix.E 7 i j : ℤ) : ZMod 3))
    (s : Fin 7 → U ≃ₗ[ZMod 3] U) (hs : ∀ i v, s i v = v - α i v • h i)
    (S : U ≃ₗ[ZMod 3] U)
    (hS : ∀ x ∈ Subgroup.closure (Set.range s), S * x * S⁻¹ ∈ Subgroup.closure (Set.range s)) :
    ∀ t ∈ ggReflConj s, S * t * S⁻¹ ∈ ggReflConj s := by
  have : Finite U := hfin
  have hFT : TauCeti.IsFiniteType (CartanMatrix.E 7) := by
    have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E7
    rwa [TauCeti.DynkinType.cartanMatrix_E7] at h
  have hclosed : GGReflClosed s :=
    ggReflClosed_of_indep (p := 3) (by norm_num) hFT ggIntCartan_E₇ h α
      (fun i j => by simpa using hα i j) hb s hs
  intro t ht
  obtain ⟨u, hu, k, rfl⟩ := ht
  have hself : α k (h k) = 2 := by rw [hα k k]; simp [CartanMatrix.E]
  have hsk : s k = Module.reflection hself :=
    LinearEquiv.ext fun v => by rw [hs k v, Module.reflection_apply]
  have huk : u * s k * u⁻¹ ∈ Subgroup.closure (Set.range s) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hu (Subgroup.subset_closure ⟨k, rfl⟩))
      (Subgroup.inv_mem _ hu)
  have hSuk : S * (u * s k * u⁻¹) * S⁻¹ ∈ Subgroup.closure (Set.range s) := hS _ huk
  have hrefl : IsReflLin (S * (u * s k * u⁻¹) * S⁻¹) := by
    have h1 : IsReflLin (s k) := ⟨h k, α k, hself, hsk⟩
    exact ggQ2_isReflLin_conj S (u * s k * u⁻¹) (ggQ2_isReflLin_conj u (s k) h1)
  have hne : S * (u * s k * u⁻¹) * S⁻¹ ≠ 1 := by
    have hsk1 : s k ≠ 1 := by
      rw [hsk]
      exact ggQ2xKDf7_reflection_ne_one (h k) (α k) hself
    intro h1
    have h2 : u * s k * u⁻¹ = 1 := by
      have := congrArg (fun x => S⁻¹ * x * S) h1
      simpa [mul_assoc] using this
    have h3 : s k = 1 := by
      have := congrArg (fun x => u⁻¹ * x * u) h2
      simpa [mul_assoc] using this
    exact hsk1 h3
  exact hclosed _ hSuk (ggQ2xKDf7_sq_of_isReflLin _ hrefl) hne
    (ggQ2xKDf7_isReflLin_form _ hrefl)

theorem ggQ2WeylInner_E7 : GGQ2WeylInner 7 (CartanMatrix.E 7) := by
  classical
  intro U instACG instMod h hb hspan α hα T hT
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfr : Module.finrank (ZMod 3) U = 7 := by
    have h1 := finrank_span_eq_card hb
    rw [hspan, finrank_top, Fintype.card_fin] at h1
    exact h1
  have hfin : Finite U := by
    have hmod : Module.Finite (ZMod 3) (↥(Submodule.span (ZMod 3) (Set.range h))) :=
      Module.Finite.span_of_finite (ZMod 3) (Set.finite_range h)
    rw [hspan] at hmod
    have : Module.Finite (ZMod 3) (↥(⊤ : Submodule (ZMod 3) U)) := hmod
    have : Finite (↥(⊤ : Submodule (ZMod 3) U)) := Module.finite_of_finite (ZMod 3)
    exact Finite.of_surjective (Subtype.val : ↥(⊤ : Submodule (ZMod 3) U) → U)
      (fun u => ⟨⟨u, Submodule.mem_top⟩, rfl⟩)
  let D' : GGQ2Lin 3 :=
    { ι := Fin 7
      coxeter := CoxeterMatrix.E₇
      cartan := CartanMatrix.E 7
      V := U
      coroot := h
      root := α
      a := ⟨6, by norm_num⟩
      b := ⟨0, by norm_num⟩
      a_ne_b := by decide
      a_leaf := by
        refine ⟨⟨5, by norm_num⟩, ⟨by decide, by decide⟩, ?_⟩
        intro y hy
        fin_cases y <;> simp_all [CartanMatrix.E]
      isWeyl := Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, (ggQ2xKDf7_reindex_refl _).symm⟩))
      isCartan := ggIntCartan_E₇
      pairing := fun i j => by simpa using hα i j }
  have hbas : D'.Basis := by
    change LinearIndependent (ZMod 3) h ∧ Fintype.card (Fin 7) = Module.finrank (ZMod 3) U
    exact ⟨hb, by simp [hfr]⟩
  have hE7 : ∃ e : Fin 7 ≃ D'.ι, D'.coxeter = CoxeterMatrix.E₇.reindex e :=
    ⟨Equiv.refl _, (ggQ2xKDf7_reindex_refl CoxeterMatrix.E₇).symm⟩
  have hgen : Set.range D'.simpleRefl =
      {t : U ≃ₗ[ZMod 3] U | ∃ j, ∀ v, t v = v - α j v • h j} :=
    ggQ2xKDf7_range_simpleRefl h α D'.simpleRefl (fun i v => by
      rw [GGQ2Lin.simpleRefl, Module.reflection_apply])
  have hWclos : D'.weyl = Subgroup.closure (Set.range D'.simpleRefl) := by
    rw [GGQ2Lin.weyl, GGQ2Lin.parab, Set.image_univ]
  have hweylEq : D'.weyl = ggQ2WeylOf h α := by
    rw [hWclos, hgen]
    rfl
  have hT' : T ∈ Subgroup.normalizer (D'.weyl : Set (U ≃ₗ[ZMod 3] U)) := by
    rwa [hweylEq]
  have hconjEq : ggReflConj D'.simpleRefl = ggQ2xQ_isConjRefl D' := by
    ext x
    constructor
    · rintro ⟨u, hu, i, rfl⟩
      exact ⟨i, u, hWclos.symm ▸ hu, rfl⟩
    · rintro ⟨i, u, hu, rfl⟩
      exact ⟨u, hWclos ▸ hu, i, rfl⟩
  have hconj_mem : ∀ S ∈ Subgroup.normalizer (D'.weyl : Set (U ≃ₗ[ZMod 3] U)),
      ∀ t ∈ ggQ2xQ_isConjRefl D', S * t * S⁻¹ ∈ ggQ2xQ_isConjRefl D' := by
    intro S hS t ht
    have hS' : ∀ x ∈ Subgroup.closure (Set.range D'.simpleRefl),
        S * x * S⁻¹ ∈ Subgroup.closure (Set.range D'.simpleRefl) := by
      intro x hx
      have hxW : x ∈ D'.weyl := hWclos.symm ▸ hx
      exact hWclos ▸ (Subgroup.mem_normalizer_iff.mp hS x).mp hxW
    exact hconjEq ▸ ggQ2xKDf7_conj_mem hfin h hb α hα D'.simpleRefl
      (fun i v => by rw [GGQ2Lin.simpleRefl, Module.reflection_apply]) S hS'
      t (hconjEq.symm ▸ ht)
  let π : (U ≃ₗ[ZMod 3] U) → (U ≃ₗ[ZMod 3] U) := fun t => T * t * T⁻¹
  have hπT : ∀ t ∈ ggQ2xQ_isConjRefl D', π t ∈ ggQ2xQ_isConjRefl D' := by
    intro t ht
    change T * t * T⁻¹ ∈ ggQ2xQ_isConjRefl D'
    exact hconj_mem T hT' t ht
  have hsurj : Set.SurjOn π (ggQ2xQ_isConjRefl D') (ggQ2xQ_isConjRefl D') := by
    intro b hb
    refine ⟨T⁻¹ * b * T, ?_, ?_⟩
    · change T⁻¹ * b * T ∈ ggQ2xQ_isConjRefl D'
      exact hconj_mem T⁻¹ (Subgroup.inv_mem _ hT') b hb
    · change T * (T⁻¹ * b * T) * T⁻¹ = b
      group
  have hinj : Set.InjOn π (ggQ2xQ_isConjRefl D') := by
    intro a _ b _ hab
    change T * a * T⁻¹ = T * b * T⁻¹ at hab
    have h := congrArg (fun x => T⁻¹ * x * T) hab
    simpa [mul_assoc] using h
  have hπ : ∀ s ∈ ggQ2xQ_isConjRefl D', ∀ t ∈ ggQ2xQ_isConjRefl D',
      π (s * t * s⁻¹) = π s * π t * (π s)⁻¹ := by
    intro s _ t _
    change T * (s * t * s⁻¹) * T⁻¹ =
      (T * s * T⁻¹) * (T * t * T⁻¹) * (T * s * T⁻¹)⁻¹
    group
  obtain ⟨g, hgW, hgconj⟩ :=
    ggQ2_quandle_aut_E D' hbas (Or.inr (Or.inl hE7)) π hπT hinj hsurj hπ
  refine ⟨g, hweylEq ▸ hgW, ?_⟩
  intro x hx
  have hx' : x ∈ Subgroup.closure (Set.range D'.simpleRefl) :=
    hWclos ▸ (hweylEq.symm ▸ hx)
  have hkey : ∀ y ∈ Subgroup.closure (Set.range D'.simpleRefl),
      T * y * T⁻¹ = g * y * g⁻¹ := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz =>
        obtain ⟨k, rfl⟩ := hz
        exact hgconj _ (ggQ2xQ_simpleRefl_mem_isConjRefl D' k)
    | one => group
    | mul y z _ _ ihy ihz =>
        rw [show T * (y * z) * T⁻¹ = (T * y * T⁻¹) * (T * z * T⁻¹) by group, ihy, ihz]
        group
    | inv y _ ihy =>
        rw [show T * y⁻¹ * T⁻¹ = (T * y * T⁻¹)⁻¹ by group, ihy]
        group
  exact hkey x hx'

end CFSG.StandardType

end
