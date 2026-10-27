module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeBstar
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Descent
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Commute

public section

namespace CFSG.StandardType.E6IDB

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.E6Three RecipeExcLang

theorem isElemAbelian_comap {G H : Type*} [Group G] [Group H] {p : ℕ} {E : Subgroup H}
    (hE : IsElemAbelian p E) {f : G →* H} (hf : Function.Injective f) :
    IsElemAbelian p (E.comap f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact TableB.IsElemAbelian.comm hE a.2 b.2
  · rw [map_pow, hE.2 _ hx, map_one]

section Hat

variable {τ : Tag} {K : Type} [Field K]

theorem mem_hatGroup_iff_mem_inndiagGroup {w : ModGL τ K} :
    w ∈ hatGroup τ K ↔ w ∈ inndiagGroup τ K := by
  constructor
  · rintro ⟨g, hg, a, rfl⟩
    have h := conj_rootDiagUnit_mem_adjointGroup (K := K) a⁻¹ hg
    rw [← rootDiagUnit_inv, inv_inv] at h
    exact ⟨a, _, h, by group⟩
  · rintro ⟨b, j, hj, rfl⟩
    exact ⟨_, conj_rootDiagUnit_mem_adjointGroup b hj, b, by group⟩

theorem conj_mul_rootDiagAut_mem_range (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ) :
    MulAut.conj g * rootDiagAut τ K a ∈ (hatAut τ K).range := by
  refine ⟨⟨_, g, g.2, a, rfl⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
  rw [coe_hatAut_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    coe_rootDiagAut, Subgroup.coe_inv]
  group

variable (σ : K ≃+* K)

@[expose] noncomputable def subfieldAdj : adjointGroup τ (fixSubfield σ) →* adjointGroup τ K :=
  ((baseChangeGL (fixSubfield σ).subtype).comp (adjointGroup τ (fixSubfield σ)).subtype).codRestrict
    (adjointGroup τ K) fun g => baseChangeGL_mem_adjointGroup _ g.2

@[expose] noncomputable def subfieldHat : hatGroup τ (fixSubfield σ) →* hatGroup τ K :=
  ((baseChangeGL (fixSubfield σ).subtype).comp (hatGroup τ (fixSubfield σ)).subtype).codRestrict
    (hatGroup τ K) fun x => by
      obtain ⟨g, hg, a, hx⟩ := x.2
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hx, map_mul, baseChangeGL_rootDiagUnit]
      exact ⟨_, baseChangeGL_mem_adjointGroup _ hg, _, rfl⟩

theorem coe_subfieldAdj (g : adjointGroup τ (fixSubfield σ)) :
    (subfieldAdj σ g : ModGL τ K) = baseChangeGL (fixSubfield σ).subtype g :=
  rfl

theorem coe_subfieldHat (x : hatGroup τ (fixSubfield σ)) :
    (subfieldHat σ x : ModGL τ K) = baseChangeGL (fixSubfield σ).subtype x :=
  rfl

theorem subfieldAdj_injective : Function.Injective (subfieldAdj (τ := τ) σ) := fun _ _ h =>
  Subtype.ext (baseChangeGL_injective _ (congrArg Subtype.val h))

theorem subfieldHat_injective : Function.Injective (subfieldHat (τ := τ) σ) := fun _ _ h =>
  Subtype.ext (baseChangeGL_injective _ (congrArg Subtype.val h))

theorem hatAut_subfieldHat (x : hatGroup τ (fixSubfield σ)) (h : adjointGroup τ (fixSubfield σ)) :
    hatAut τ K (subfieldHat σ x) (subfieldAdj σ h) = subfieldAdj σ (hatAut τ _ x h) :=
  Subtype.ext (by
    rw [coe_hatAut_apply, coe_subfieldHat, coe_subfieldAdj, coe_subfieldAdj, coe_hatAut_apply,
      map_mul, map_mul, map_inv])

end Hat

section Cert


variable {τ : Tag} {K : Type} [Field K]

theorem hatAut_eq_inndiagConj (x : hatGroup τ K) :
    hatAut τ K x = inndiagConj τ K ⟨x, mem_hatGroup_iff_mem_inndiagGroup.1 x.2⟩ :=
  MulEquiv.ext fun h => Subtype.ext (by rw [coe_hatAut_apply, coe_inndiagConj])

theorem hatAut_injective [Finite K] (hK4 : 4 ≤ Nat.card K) : Function.Injective (hatAut τ K) := by
  refine (injective_iff_map_eq_one _).2 fun x h1 => Subtype.ext ?_
  refine eq_one_of_commute_adjointGroup hK4 (mem_hatGroup_iff_mem_inndiagGroup.1 x.2)
    fun h hh => ?_
  have e := congrArg Subtype.val (DFunLike.congr_fun h1 (⟨h, hh⟩ : adjointGroup τ K))
  rw [coe_hatAut_apply] at e
  calc (x : ModGL τ K) * h = x * h * (x : ModGL τ K)⁻¹ * x := by group
    _ = h * x := by rw [e]; rfl

theorem entrywiseAdjointAut_subfieldAdj (σ : K ≃+* K) (h : adjointGroup τ (fixSubfield σ)) :
    entrywiseAdjointAut τ σ (subfieldAdj σ h) = subfieldAdj σ h := by
  have hσk : σ.toRingHom.comp (fixSubfield σ).subtype = (fixSubfield σ).subtype :=
    RingHom.ext fun c => (mem_fixSubfield σ).1 c.2
  refine Subtype.ext ?_
  rw [coe_entrywiseAdjointAut, coe_subfieldAdj, units_map_entrywiseHom_eq_baseChangeGL,
    baseChangeGL_baseChangeGL, hσk]

theorem exists_subfieldHat_eq_of_commute [Finite K] {n e : ℕ} (hK : Nat.card K = 2 ^ n)
    (σ : K ≃+* K) (hk : Nat.card (fixSubfield σ) = 2 ^ e) (hK4 : 4 ≤ Nat.card K)
    (w : hatGroup τ K)
    (hc : hatAut τ K w * entrywiseAdjointAut τ σ = entrywiseAdjointAut τ σ * hatAut τ K w) :
    ∃ w₀, subfieldHat σ w₀ = w := by
  obtain ⟨w, hwh⟩ := w
  have hw : w ∈ inndiagGroup τ K := mem_hatGroup_iff_mem_inndiagGroup.1 hwh
  rw [hatAut_eq_inndiagConj] at hc
  have hfix : Units.map (entrywiseHom σ.toRingHom) w = w :=
    E6FieldFix.entrywise_inndiag_eq_of_commute hK4 σ _ hc
  obtain ⟨w₀, hw₀, he⟩ := E6FieldFix.exists_inndiagGroup_of_fixed hK σ hk hw hfix
  refine ⟨⟨w₀, mem_hatGroup_iff_mem_inndiagGroup.2 hw₀⟩, Subtype.ext ?_⟩
  rw [coe_subfieldHat]
  exact he

theorem normal_range_hatAut [Finite K] : (hatAut .E6 K).range.Normal := by
  obtain ⟨Θ, -, -, hker, -⟩ := ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
  have e : (hatAut .E6 K).range = Θ.ker := by
    ext α
    rw [hker]
    constructor
    · rintro ⟨⟨_, g, hg, a, rfl⟩, rfl⟩
      exact ⟨⟨g, hg⟩, a, fun h => by rw [coe_hatAut_apply]; group⟩
    · rintro ⟨g, a, hα⟩
      exact ⟨⟨_, g, g.2, a, rfl⟩, MulEquiv.ext fun h => Subtype.ext (by
        rw [coe_hatAut_apply, hα]
        group)⟩
  rw [e]
  infer_instance

end Cert

end CFSG.StandardType.E6IDB

end
