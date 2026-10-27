module

public import CFSG.RankThree.PartOne.KE.TwoA2Exchange
public import CFSG.RankThree.PartOne.KF4.QPlusWeyl

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KE
open scoped Matrix Pointwise


section Factor

variable {L : Type} [Field L]

structure QPFactor (n : ModGL Tag.F4 L) (Φ : ModGL Tag.F4 L →* ModGL Tag.F4 L)
    (S : Set (Fin Tag.F4.rank → ℤ)) (P : Subgroup (ModGL Tag.F4 L)) : Prop where
  finite : Finite P
  quasi : CFSG.IsQuasisimple P
  eq : P = rootSpan Tag.F4 L S ⊓ twistedFixedPoints n Φ
  cent : ∀ y ∈ torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L S, y ∈ twistedFixedPoints n Φ →
    (∀ u ∈ P, y * u = u * y) → y ∈ torusGroup Tag.F4 L ∧
      y ∈ Subgroup.centralizer (rootSpan Tag.F4 L S : Set (ModGL Tag.F4 L))

@[expose] def QPFree (S : Set (Fin Tag.F4.rank → ℤ)) (P : Subgroup (ModGL Tag.F4 L)) : Prop :=
  ∀ y ∈ torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L S, (∀ u ∈ P, y * u = u * y) →
    y ∈ torusGroup Tag.F4 L ∧ y ∈ Subgroup.centralizer (rootSpan Tag.F4 L S : Set (ModGL Tag.F4 L))

theorem QPFactor.isSigmaFamily {n : ModGL Tag.F4 L} {Fr : L →+* L}
    {S : Set (Fin Tag.F4.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot Tag.F4 α)
    {P : Subgroup (ModGL Tag.F4 L)}
    (h : QPFactor n (Units.map (entrywiseHom Fr)) S P) :
    IsSigmaFamily n Fr S (fun _ : Unit => P) := by
  have hN : torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L S ≤
      Subgroup.normalizer (rootSpan Tag.F4 L S : Set (ModGL Tag.F4 L)) :=
    sup_le (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hS) Subgroup.le_normalizer
  refine ⟨fun _ => h.finite, fun _ => h.quasi, fun _ => ?_, fun _ => ?_, fun _ => ?_,
    fun _ y hy hyR u hu => ?_, fun y hy hyR hc => ?_⟩
  · rw [h.eq]; exact inf_le_left
  · rw [h.eq]; exact inf_le_right
  · rw [h.eq]; exact inf_le_left.trans (CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L S)
  · rw [h.eq] at hu ⊢
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hN hy) u).1 hu.1,
      mul_mem (mul_mem hyR hu.2) (inv_mem hyR)⟩
  · obtain ⟨hH, hC⟩ := h.cent y hy hyR (fun u hu => hc () u hu)
    exact Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hH, hyR⟩, hC⟩

end Factor

section Union

variable {L : Type} [Field L]

theorem qp_torus_sup_le_normalizers {S₁ S₂ : Set (Fin Tag.F4.rank → ℤ)}
    (hS₁ : ∀ α ∈ S₁, IsRoot Tag.F4 α) (hS₂ : ∀ α ∈ S₂, IsRoot Tag.F4 α)
    (hcomm : ∀ u ∈ rootSpan Tag.F4 L S₁, ∀ v ∈ rootSpan Tag.F4 L S₂, u * v = v * u) :
    torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L (S₁ ∪ S₂) ≤
      Subgroup.normalizer (rootSpan Tag.F4 L S₁ : Set (ModGL Tag.F4 L)) ⊓
        Subgroup.normalizer (rootSpan Tag.F4 L S₂ : Set (ModGL Tag.F4 L)) := by
  have hc1 : rootSpan Tag.F4 L S₂ ≤
      Subgroup.normalizer (rootSpan Tag.F4 L S₁ : Set (ModGL Tag.F4 L)) := by
    refine le_trans (fun g hg => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact hcomm u hu g hg
  have hc2 : rootSpan Tag.F4 L S₁ ≤
      Subgroup.normalizer (rootSpan Tag.F4 L S₂ : Set (ModGL Tag.F4 L)) := by
    refine le_trans (fun g hg => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (hcomm g hg u hu).symm
  refine sup_le (le_inf (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hS₁)
    (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hS₂)) ?_
  rw [rootSpan_union_eq]
  exact sup_le (le_inf Subgroup.le_normalizer hc2) (le_inf hc1 Subgroup.le_normalizer)

theorem qp_exists_decomp {S₁ S₂ : Set (Fin Tag.F4.rank → ℤ)}
    (hS₁ : ∀ α ∈ S₁, IsRoot Tag.F4 α) (hS₂ : ∀ α ∈ S₂, IsRoot Tag.F4 α)
    (hcomm : ∀ u ∈ rootSpan Tag.F4 L S₁, ∀ v ∈ rootSpan Tag.F4 L S₂, u * v = v * u)
    {y : ModGL Tag.F4 L} (hy : y ∈ torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L (S₁ ∪ S₂)) :
    ∃ h ∈ torusGroup Tag.F4 L, ∃ z₁ ∈ rootSpan Tag.F4 L S₁, ∃ z₂ ∈ rootSpan Tag.F4 L S₂,
      y = h * z₁ * z₂ := by
  have hS : ∀ r ∈ S₁ ∪ S₂, IsRoot Tag.F4 r := fun r hr => hr.elim (hS₁ r) (hS₂ r)
  have e := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup Tag.F4 L)
    (rootSpan Tag.F4 L (S₁ ∪ S₂)) (CFSG.LieType.Chevalley.torusGroup_le_normalizer_rootSpan hS)
  have hy' : y ∈ ((torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L (S₁ ∪ S₂) : Subgroup (ModGL Tag.F4 L)) :
    Set (ModGL Tag.F4 L)) := hy
  rw [e] at hy'
  obtain ⟨h, hh, q, hq, rfl⟩ := hy'
  rw [SetLike.mem_coe, rootSpan_union_eq] at hq
  have hle : rootSpan Tag.F4 L S₁ ≤
      Subgroup.normalizer (rootSpan Tag.F4 L S₂ : Set (ModGL Tag.F4 L)) := by
    refine le_trans (fun g hg => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (hcomm g hg u hu).symm
  have e2 := Subgroup.coe_mul_of_left_le_normalizer_right (rootSpan Tag.F4 L S₁)
    (rootSpan Tag.F4 L S₂) hle
  have hq' : q ∈ ((rootSpan Tag.F4 L S₁ ⊔ rootSpan Tag.F4 L S₂ : Subgroup (ModGL Tag.F4 L)) :
    Set (ModGL Tag.F4 L)) := hq
  rw [e2] at hq'
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := hq'
  exact ⟨h, hh, z₁, hz₁, z₂, hz₂, by group⟩

theorem qp_Fn_rootSpan_mem [CharP L 2] (Fr : L →+* L) {S : Set (Fin Tag.F4.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot Tag.F4 α) (hSn : ∀ α ∈ S, -α ∈ S)
    {u : ModGL Tag.F4 L} (hu : u ∈ rootSpan Tag.F4 L S) :
    qpRep L * Units.map (entrywiseHom Fr) u * (qpRep L)⁻¹ ∈ rootSpan Tag.F4 L S := by
  set Fn : ModGL Tag.F4 L →* ModGL Tag.F4 L :=
    (MulAut.conj (qpRep L)).toMonoidHom.comp (Units.map (entrywiseHom Fr)) with hFn
  have hle : rootSpan Tag.F4 L S ≤ (rootSpan Tag.F4 L S).comap Fn := by
    refine iSup₂_le fun α hα => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    have h1 : Fn (pinnedX Tag.F4 L α c) = pinnedX Tag.F4 L (-α) (Fr c) := by
      simp only [hFn, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [units_map_entrywiseHom_eq_baseChangeGL_self, baseChangeGL_pinnedX,
        qpRep_conj_pinnedX (hS α hα)]
    rw [h1]
    exact rootSubgroup_le_rootSpan (hSn α hα) (Subgroup.subset_closure ⟨Fr c, rfl⟩)
  have := hle hu
  rw [Subgroup.mem_comap] at this
  simpa [hFn, MulAut.conj_apply] using this

theorem qp_center_rootSL2 [CharP L 2] {α : Fin Tag.F4.rank → ℤ}
    {g : ModGL Tag.F4 L} (hg : g ∈ rootRankOneGroup Tag.F4 L α)
    (hc : ∀ h ∈ rootRankOneGroup Tag.F4 L α, g * h = h * g) : g = 1 := by
  obtain ⟨A, rfl⟩ := hg
  have hA : A ∈ Subgroup.center (SL2 L) := by
    rw [Subgroup.mem_center_iff]
    intro B
    have := hc (rootSL2 Tag.F4 L α B) ⟨B, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact (rootSL2_injective_of_field α this).symm
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have hr1 : r = 1 := by
    have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
    have : (r - 1) ^ 2 = 0 := by
      have : r ^ 2 = 1 := by simpa using hr
      linear_combination this + (1 - r) * h2
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  have hA1 : A = 1 := by
    apply Subtype.ext
    rw [← hrA, hr1, map_one]
    rfl
  rw [hA1, map_one]

theorem qp_union_family {n : ModGL Tag.F4 L} {Fr : L →+* L}
    {S₁ S₂ : Set (Fin Tag.F4.rank → ℤ)}
    (hS₁ : ∀ α ∈ S₁, IsRoot Tag.F4 α) (hS₂ : ∀ α ∈ S₂, IsRoot Tag.F4 α)
    (hcomm : ∀ u ∈ rootSpan Tag.F4 L S₁, ∀ v ∈ rootSpan Tag.F4 L S₂, u * v = v * u)
    {P₁ P₂ : Subgroup (ModGL Tag.F4 L)}
    (h₁ : QPFactor n (Units.map (entrywiseHom Fr)) S₁ P₁)
    (h₂ : QPFactor n (Units.map (entrywiseHom Fr)) S₂ P₂) (hfree : QPFree S₂ P₂) :
    IsSigmaFamily n Fr (S₁ ∪ S₂) (fun b : Bool => bif b then P₁ else P₂) := by
  have hnorm := qp_torus_sup_le_normalizers (L := L) hS₁ hS₂ hcomm
  have hsub₁ : rootSpan Tag.F4 L S₁ ≤ rootSpan Tag.F4 L (S₁ ∪ S₂) := by
    rw [rootSpan_union_eq]; exact le_sup_left
  have hsub₂ : rootSpan Tag.F4 L S₂ ≤ rootSpan Tag.F4 L (S₁ ∪ S₂) := by
    rw [rootSpan_union_eq]; exact le_sup_right
  have hS : ∀ r ∈ S₁ ∪ S₂, IsRoot Tag.F4 r := fun r hr => hr.elim (hS₁ r) (hS₂ r)
  refine ⟨fun b => ?_, fun b => ?_, fun b => ?_, fun b => ?_, fun b => ?_,
    fun b y hy hyR u hu => ?_, fun y hy hyR hc => ?_⟩
  · cases b
    · exact h₂.finite
    · exact h₁.finite
  · cases b
    · exact h₂.quasi
    · exact h₁.quasi
  · cases b
    · rw [h₂.eq]; exact inf_le_left.trans hsub₂
    · rw [h₁.eq]; exact inf_le_left.trans hsub₁
  · cases b
    · rw [h₂.eq]; exact inf_le_right
    · rw [h₁.eq]; exact inf_le_right
  · cases b
    · rw [h₂.eq]
      exact inf_le_left.trans ((hsub₂.trans (CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _)))
    · rw [h₁.eq]
      exact inf_le_left.trans ((hsub₁.trans (CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _)))
  · cases b
    · have hyN := (hnorm hy).2
      rw [h₂.eq] at hu ⊢
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hyN u).1 hu.1,
        mul_mem (mul_mem hyR hu.2) (inv_mem hyR)⟩
    · have hyN := (hnorm hy).1
      rw [h₁.eq] at hu ⊢
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hyN u).1 hu.1,
        mul_mem (mul_mem hyR hu.2) (inv_mem hyR)⟩
  · obtain ⟨h, hh, z₁, hz₁, z₂, hz₂, rfl⟩ := qp_exists_decomp hS₁ hS₂ hcomm hy
    have hc1 : ∀ u ∈ P₁, (h * z₁ * z₂) * u = u * (h * z₁ * z₂) := fun u hu => hc true u hu
    have hc2 : ∀ u ∈ P₂, (h * z₁ * z₂) * u = u * (h * z₁ * z₂) := fun u hu => hc false u hu
    have hy_eq : h * z₁ * z₂ = h * z₂ * z₁ := by
      rw [mul_assoc, hcomm z₁ hz₁ z₂ hz₂, ← mul_assoc]
    have hP₂Q : ∀ u ∈ P₂, u ∈ rootSpan Tag.F4 L S₂ := fun u hu => by
      rw [h₂.eq] at hu; exact hu.1
    have hcP₂ : ∀ u ∈ P₂, (h * z₂) * u = u * (h * z₂) := by
      intro u hu
      have h1 := hc2 u hu
      rw [hy_eq] at h1
      have h2 : z₁ * u = u * z₁ := hcomm z₁ hz₁ u (hP₂Q u hu)
      have h3 : ((h * z₂) * u) * z₁ = (u * (h * z₂)) * z₁ := by
        calc ((h * z₂) * u) * z₁ = (h * z₂) * (u * z₁) := by group
          _ = (h * z₂) * (z₁ * u) := by rw [h2]
          _ = (h * z₂ * z₁) * u := by group
          _ = u * (h * z₂ * z₁) := h1
          _ = (u * (h * z₂)) * z₁ := by group
      exact mul_right_cancel h3
    have hhz₂ : h * z₂ ∈ torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L S₂ :=
      mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hz₂)
    obtain ⟨hT', hC'⟩ := hfree _ hhz₂ hcP₂
    have hyQ₁ : (h * z₂) * z₁ ∈ torusGroup Tag.F4 L ⊔ rootSpan Tag.F4 L S₁ :=
      mul_mem (Subgroup.mem_sup_left hT') (Subgroup.mem_sup_right hz₁)
    rw [hy_eq] at hyR hc1
    obtain ⟨hyT, hyC₁⟩ := h₁.cent _ hyQ₁ hyR hc1
    have hyC₂ : (h * z₂) * z₁ ∈ Subgroup.centralizer
        (rootSpan Tag.F4 L S₂ : Set (ModGL Tag.F4 L)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have e1 : (h * z₂) * g = g * (h * z₂) := (Subgroup.mem_centralizer_iff.1 hC' g hg).symm
      have e2 : z₁ * g = g * z₁ := hcomm z₁ hz₁ g hg
      calc g * ((h * z₂) * z₁) = (g * (h * z₂)) * z₁ := by group
        _ = ((h * z₂) * g) * z₁ := by rw [e1]
        _ = (h * z₂) * (g * z₁) := by group
        _ = (h * z₂) * (z₁ * g) := by rw [e2]
        _ = ((h * z₂) * z₁) * g := by group
    have hyC : (h * z₂) * z₁ ∈ Subgroup.centralizer
        (rootSpan Tag.F4 L (S₁ ∪ S₂) : Set (ModGL Tag.F4 L)) := by
      rw [rootSpan_union_eq]
      have hle : rootSpan Tag.F4 L S₁ ⊔ rootSpan Tag.F4 L S₂ ≤
          Subgroup.centralizer ({(h * z₂) * z₁} : Set (ModGL Tag.F4 L)) := by
        refine sup_le (fun g hg => ?_) (fun g hg => ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hyC₁ g hg)
        · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hyC₂ g hg)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
    rw [hy_eq]
    exact Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hyT, hyR⟩, hyC⟩

theorem qp_union_fixed_eq [CharP L 2] (Fr : L →+* L) {S₁ S₂ : Set (Fin Tag.F4.rank → ℤ)}
    (hS₁ : ∀ α ∈ S₁, IsRoot Tag.F4 α) (hS₂ : ∀ α ∈ S₂, IsRoot Tag.F4 α)
    (hS₁n : ∀ α ∈ S₁, -α ∈ S₁) (hS₂n : ∀ α ∈ S₂, -α ∈ S₂)
    (hcomm : ∀ u ∈ rootSpan Tag.F4 L S₁, ∀ v ∈ rootSpan Tag.F4 L S₂, u * v = v * u)
    (hcen : ∀ g ∈ rootSpan Tag.F4 L S₂, (∀ h ∈ rootSpan Tag.F4 L S₂, g * h = h * g) → g = 1)
    {P₁ P₂ : Subgroup (ModGL Tag.F4 L)}
    (hP₁ : P₁ = rootSpan Tag.F4 L S₁ ⊓
      twistedFixedPoints (qpRep L) (Units.map (entrywiseHom Fr)))
    (hP₂ : P₂ = rootSpan Tag.F4 L S₂ ⊓
      twistedFixedPoints (qpRep L) (Units.map (entrywiseHom Fr))) :
    P₁ ⊔ P₂ = rootSpan Tag.F4 L (S₁ ∪ S₂) ⊓
      twistedFixedPoints (qpRep L) (Units.map (entrywiseHom Fr)) := by
  have hsub₁ : rootSpan Tag.F4 L S₁ ≤ rootSpan Tag.F4 L (S₁ ∪ S₂) := by
    rw [rootSpan_union_eq]; exact le_sup_left
  have hsub₂ : rootSpan Tag.F4 L S₂ ≤ rootSpan Tag.F4 L (S₁ ∪ S₂) := by
    rw [rootSpan_union_eq]; exact le_sup_right
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw [hP₁]; exact inf_le_inf_right _ hsub₁
    · rw [hP₂]; exact inf_le_inf_right _ hsub₂
  · intro u hu
    obtain ⟨huQ, huR⟩ := Subgroup.mem_inf.1 hu
    have hle : rootSpan Tag.F4 L S₁ ≤
        Subgroup.normalizer (rootSpan Tag.F4 L S₂ : Set (ModGL Tag.F4 L)) := by
      refine le_trans (fun g hg => ?_) (Subgroup.centralizer_le_normalizer _)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hcomm g hg v hv).symm
    have e := Subgroup.coe_mul_of_left_le_normalizer_right (rootSpan Tag.F4 L S₁)
      (rootSpan Tag.F4 L S₂) hle
    have hu' : u ∈ ((rootSpan Tag.F4 L S₁ ⊔ rootSpan Tag.F4 L S₂ : Subgroup (ModGL Tag.F4 L)) :
      Set (ModGL Tag.F4 L)) := by rw [← rootSpan_union_eq]; exact huQ
    rw [e] at hu'
    obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := hu'
    have hF₁ := qp_Fn_rootSpan_mem Fr hS₁ hS₁n hz₁
    have hF₂ := qp_Fn_rootSpan_mem Fr hS₂ hS₂n hz₂
    have hR : qpRep L * Units.map (entrywiseHom Fr) (z₁ * z₂) * (qpRep L)⁻¹ = z₁ * z₂ :=
      mem_twistedFixedPoints.1 huR
    set a : ModGL Tag.F4 L := qpRep L * Units.map (entrywiseHom Fr) z₁ * (qpRep L)⁻¹ with ha
    set b : ModGL Tag.F4 L := qpRep L * Units.map (entrywiseHom Fr) z₂ * (qpRep L)⁻¹ with hb
    have hab : a * b = z₁ * z₂ := by
      rw [← hR, map_mul]
      simp only [ha, hb]
      group
    have hd : a⁻¹ * z₁ = b * z₂⁻¹ := by
      have : a * b * z₂⁻¹ = z₁ := by rw [hab]; group
      calc a⁻¹ * z₁ = a⁻¹ * (a * b * z₂⁻¹) := by rw [this]
        _ = b * z₂⁻¹ := by group
    have hdQ₁ : a⁻¹ * z₁ ∈ rootSpan Tag.F4 L S₁ := mul_mem (inv_mem hF₁) hz₁
    have hdQ₂ : a⁻¹ * z₁ ∈ rootSpan Tag.F4 L S₂ := by
      rw [hd]; exact mul_mem hF₂ (inv_mem hz₂)
    have hd1 : a⁻¹ * z₁ = 1 := by
      refine hcen _ hdQ₂ fun g hg => ?_
      exact hcomm _ hdQ₁ g hg
    have ha1 : a = z₁ := by
      have : a⁻¹ * z₁ = 1 := hd1
      exact (inv_mul_eq_one.1 this)
    have hb1 : b = z₂ := by
      have h2 : b * z₂⁻¹ = 1 := by rw [← hd]; exact hd1
      exact mul_inv_eq_one.1 h2
    have hz₁R : z₁ ∈ twistedFixedPoints (qpRep L) (Units.map (entrywiseHom Fr)) :=
      mem_twistedFixedPoints.2 ha1
    have hz₂R : z₂ ∈ twistedFixedPoints (qpRep L) (Units.map (entrywiseHom Fr)) :=
      mem_twistedFixedPoints.2 hb1
    exact mul_mem (Subgroup.mem_sup_left (by rw [hP₁]; exact Subgroup.mem_inf.2 ⟨hz₁, hz₁R⟩))
      (Subgroup.mem_sup_right (by rw [hP₂]; exact Subgroup.mem_inf.2 ⟨hz₂, hz₂R⟩))

theorem qp_layer_sup_eq_top {G : Type*} [Group G] {P₁ P₂ : Subgroup G}
    (hq₁ : CFSG.IsQuasisimple P₁) (hq₂ : CFSG.IsQuasisimple P₂)
    (hcomm : ∀ u ∈ P₁, ∀ v ∈ P₂, u * v = v * u) : CFSG.layer ↥(P₁ ⊔ P₂) = ⊤ := by
  have h1 : P₁ ≤ P₁ ⊔ P₂ := le_sup_left
  have h2 : P₂ ≤ P₁ ⊔ P₂ := le_sup_right
  have hn₁ : P₂ ≤ Subgroup.normalizer (P₁ : Set G) := by
    refine le_trans (fun g hg => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact hcomm u hu g hg
  have hn₂ : P₁ ≤ Subgroup.normalizer (P₂ : Set G) := by
    refine le_trans (fun g hg => ?_) (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (hcomm g hg u hu).symm
  have hN₁ : (P₁.subgroupOf (P₁ ⊔ P₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h1).2 (sup_le Subgroup.le_normalizer hn₁)
  have hN₂ : (P₂.subgroupOf (P₁ ⊔ P₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h2).2 (sup_le hn₂ Subgroup.le_normalizer)
  refine eq_top_iff.2 ?_
  calc (⊤ : Subgroup ↥(P₁ ⊔ P₂)) = (P₁ ⊔ P₂).subgroupOf (P₁ ⊔ P₂) :=
        (Subgroup.subgroupOf_self _).symm
    _ = P₁.subgroupOf (P₁ ⊔ P₂) ⊔ P₂.subgroupOf (P₁ ⊔ P₂) := (Subgroup.subgroupOf_sup h1 h2)
    _ ≤ CFSG.layer ↥(P₁ ⊔ P₂) :=
      sup_le (CFSG.LocalCores.component_le_layer
        ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h1).symm hq₁,
          hN₁.isSubnormal⟩)
        (CFSG.LocalCores.component_le_layer
          ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h2).symm hq₂,
            hN₂.isSubnormal⟩)

end Union

end CFSG.RankThree.PartOne.KF4
