module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Odd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23_barSub_conj_equiv {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {x : G}
    (hx : x ∈ stabTil V₀ V) (L : Subgroup G) :
    Nonempty (↥(barSub V₀ V hV (conjSubgroup L x)) ≃* ↥(barSub V₀ V hV L)) := by
  rw [s15_Infra_barSub_conjSubgroup V₀ V hV hx L]
  exact ⟨(Subgroup.equivMapOfInjective _ _ (MulEquiv.injective _)).symm⟩

theorem c23_equiv_sup_prod {Γ : Type*} [Group Γ] {A₁ A₂ : Subgroup Γ}
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hinf : A₁ ⊓ A₂ = ⊥) (e : ↥A₂ ≃* ↥A₁) :
    Nonempty (↥(A₁ ⊔ A₂) ≃* ↥A₁ × ↥A₁) := by
  have hcomm' : ∀ a : ↥A₁, ∀ b : ↥A₂, Commute (A₁.subtype a) (A₂.subtype b) :=
    fun a b => hcomm (a : Γ) a.2 (b : Γ) b.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod A₁.subtype A₂.subtype hcomm') :=
    (MonoidHom.noncommCoprod_injective A₁.subtype A₂.subtype hcomm').2
      ⟨A₁.subtype_injective, A₂.subtype_injective, by
        rw [disjoint_iff, Subgroup.range_subtype, Subgroup.range_subtype]
        exact hinf⟩
  have hrange : (MonoidHom.noncommCoprod A₁.subtype A₂.subtype hcomm').range = A₁ ⊔ A₂ := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  exact ⟨((MulEquiv.prodCongr (MulEquiv.refl ↥A₁) e.symm).trans
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))).symm⟩

theorem c23_perm_barSub (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hs : s15 D.M V₀ V hV L = 2) {x : G} (hx : x ∈ D.M)
    (hxn : x ∉ nBar D.M V₀ V hV L) :
    ∀ φ ∈ Mbar D.M V₀ V hV,
      ((barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom = barSub V₀ V hV L ∧
        (barSub V₀ V hV (conjSubgroup L x)).map (MulAut.conj φ).toMonoidHom =
          barSub V₀ V hV (conjSubgroup L x)) ∨
      ((barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom = barSub V₀ V hV (conjSubgroup L x) ∧
        (barSub V₀ V hV (conjSubgroup L x)).map (MulAut.conj φ).toMonoidHom =
          barSub V₀ V hV L) := by
  intro φ hφ
  obtain ⟨g, hgM, hgφ⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
  have hm : (g : G) ∈ stabTil V₀ V := g.2
  have hgt : actTil V₀ V hV ⟨(g : G)⁻¹, (stabTil V₀ V).inv_mem hm⟩ =
      (actTil V₀ V hV g)⁻¹ := by
    rw [show (⟨(g : G)⁻¹, (stabTil V₀ V).inv_mem hm⟩ : stabTil V₀ V) = g⁻¹ from
      Subtype.ext rfl, map_inv]
  have hLmap : (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom =
      barSub V₀ V hV (conjSubgroup L (g : G)⁻¹) := by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV ((stabTil V₀ V).inv_mem hm) L, hgt, inv_inv,
      hgφ]
  have hKmap : (barSub V₀ V hV (conjSubgroup L x)).map (MulAut.conj φ).toMonoidHom =
      barSub V₀ V hV (conjSubgroup (conjSubgroup L x) (g : G)⁻¹) := by
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV ((stabTil V₀ V).inv_mem hm) (conjSubgroup L x),
      hgt, inv_inv, hgφ]
  rw [conjSubgroup_conjSubgroup] at hKmap
  have hLK : barSub V₀ V hV L ≠ barSub V₀ V hV (conjSubgroup L x) := by
    intro hc
    exact hxn ((s15_Infra_mem_nBar_iff h.hyp125 hV hx).2 hc.symm)
  have hL : (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom = barSub V₀ V hV L ∨
      (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom =
        barSub V₀ V hV (conjSubgroup L x) := by
    rw [hLmap]
    exact c23_barSub_conj_cases D h hV hs hx hxn (m := (g : G)⁻¹) (D.M.inv_mem hgM)
  have hK : (barSub V₀ V hV (conjSubgroup L x)).map (MulAut.conj φ).toMonoidHom =
        barSub V₀ V hV L ∨
      (barSub V₀ V hV (conjSubgroup L x)).map (MulAut.conj φ).toMonoidHom =
        barSub V₀ V hV (conjSubgroup L x) := by
    rw [hKmap]
    exact c23_barSub_conj_cases D h hV hs hx hxn (m := x * (g : G)⁻¹)
      (D.M.mul_mem hx (D.M.inv_mem hgM))
  rcases hL with hL | hL
  · rcases hK with hK | hK
    · exfalso
      exact hLK (Subgroup.map_injective (MulAut.conj φ).injective (hL.trans hK.symm))
    · exact Or.inl ⟨hL, hK⟩
  · rcases hK with hK | hK
    · exact Or.inr ⟨hL, hK⟩
    · exfalso
      exact hLK (Subgroup.map_injective (MulAut.conj φ).injective (hL.trans hK.symm))

theorem c23_Mbar_le_normalizer_sup (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hs : s15 D.M V₀ V hV L = 2) {x : G} (hx : x ∈ D.M)
    (hxn : x ∉ nBar D.M V₀ V hV L) :
    Mbar D.M V₀ V hV ≤
      normalizer ((barSub V₀ V hV L ⊔ barSub V₀ V hV (conjSubgroup L x) :
        Subgroup (MulAut (Vtil V₀ V hV))) : Set (MulAut (Vtil V₀ V hV))) := by
  intro φ hφ
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  show (barSub V₀ V hV L ⊔ barSub V₀ V hV (conjSubgroup L x)).map
    (MulAut.conj φ).toMonoidHom = barSub V₀ V hV L ⊔ barSub V₀ V hV (conjSubgroup L x)
  rw [Subgroup.map_sup]
  rcases c23_perm_barSub D h hV hs hx hxn φ hφ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂]
  · rw [h₁, h₂, sup_comm]

theorem c23_lift_pair (D : Data G) (h119 : R119W D) {V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hH : F11.Hyp11 D ⊥ V) (h : Hyp151 D ⊥ V L) (hs : s15 D.M ⊥ V hV L = 2)
    (hL3 : IsL3 ↥(barSub ⊥ V hV L) 1) {x : G} (hx : x ∈ D.M)
    (hxn : x ∉ nBar D.M ⊥ V hV L)
    (hcomm : ∀ a ∈ barSub ⊥ V hV L, ∀ b ∈ barSub ⊥ V hV (conjSubgroup L x), a * b = b * a)
    (hinf : barSub ⊥ V hV L ⊓ barSub ⊥ V hV (conjSubgroup L x) = ⊥) :
    ∃ K₁ K₂ : Subgroup G, K₁ ∈ calC D.M ∧ K₂ ∈ calC D.M ∧ K₁ ≠ K₂ ∧
      barSub ⊥ V hV (K₁ ⊔ K₂) = barSub ⊥ V hV L ⊔ barSub ⊥ V hV (conjSubgroup L x) ∧
      D.M ≤ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) ∧
      IsL3 ↥(barSub ⊥ V hV K₁) 1 ∧ IsL3 ↥(barSub ⊥ V hV K₂) 1 ∧
      K₁ ≤ normalizer (K₂ : Set G) ∧ K₂ ≤ normalizer (K₁ : Set G) := by
  have hMV : D.M ≤ normalizer (V : Set G) := h.hyp125.pairFacts.le_normalizer
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hAM : barSub ⊥ V hV L ⊔ barSub ⊥ V hV (conjSubgroup L x) ≤ Mbar D.M ⊥ V hV :=
    sup_le (barSub_mono ⊥ V hV h.le) (c23_barSub_conjSubgroup_le_Mbar D h hV hx)
  obtain ⟨e⟩ := c23_barSub_conj_equiv (V₀ := ⊥) hV (hMs hx) L
  obtain ⟨φ⟩ := c23_equiv_sup_prod hcomm hinf e
  exact s16c7_lift_factors D h119 hV hMV hH hAM
    (c23_Mbar_le_normalizer_sup D h hV hs hx hxn) hL3 φ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
