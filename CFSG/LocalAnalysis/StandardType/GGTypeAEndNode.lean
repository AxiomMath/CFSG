module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTypeA
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeAut
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeRel

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.RankThree.PartTwo.Sec21 Matrix SpecialLinear

section Config

variable {G : Type} [Group G] [Finite G]

@[expose] def GGTypeASplitNbr (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (n f : ℕ)
    (y : G) (K : Subgroup G) : Prop :=
  GGConfig p B Bs x L D J ∧ GGOpAutTrivial p Bs ∧ GGInnerDiagAll p B Bs x L D J ∧
    GGNoTransvection p Bs ∧
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSL (n + 1) 2 f ∧ p ∣ 2 ^ f - 1 ∧ 3 ≤ n ∧
    ¬ p ∣ n + 3 ∧ GGScalarsPmOne Bs ∧ GGNbr p B x D J y K ∧
    StatedClassicalModel (K ⧸ Subgroup.center K) .PSL (n + 1) 2 f ∧
    (∃ e : (CoxeterMatrix.A (n + 1)).Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs),
      ∀ i, GGIsReflection p ((e ((CoxeterMatrix.A (n + 1)).simple i) :
        ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)) : MulAut ↥Bs)) ∧
    GGSecFiveAllAJoin p B Bs x L D J

theorem exists_ggTypeASplitNbr {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (hA : GGTypeASplitConfig p B Bs x L D J n f) :
    ∃ (y : G) (K : Subgroup G), GGTypeASplitNbr p B Bs x L D J n f y K := by
  obtain ⟨hmod, hpq, hn, hp3, hsc, y, K, hnbr, hmodK, hW, hgate⟩ := hA
  exact ⟨y, K, hcfg, hOp, hInn, hNoTr, hmod, hpq, hn, hp3, hsc, hnbr, hmodK, hW, hgate⟩

end Config

@[expose] def GGTypeAEndBlockLInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeASplitNbr p B Bs x L D J n f y K →
    ∀ φ₁ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L →
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) →
      ∃ l ∈ L, (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range.map
        (MulAut.conj l).toMonoidHom = J

@[expose] def GGTypeAEndBlockKInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeASplitNbr p B Bs x L D J n f y K →
    ∃ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₂.range = K ∧
      φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      (φ₂.comp (slUpperBlockHom n (GaloisField 2 f))).range = J

@[expose] def GGTypeAFarCommuteInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeASplitNbr p B Bs x L D J n f y K →
    ∀ φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L →
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) →
      φ₂.range = K →
      φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) →
      (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J →
      φ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
        φ₂.comp (slUpperBlockHom n (GaloisField 2 f)) →
      ∀ i j : Fin n, i.val = 0 → j.val + 1 = n →
        Commute (φ₂ (weylRep n (GaloisField 2 f) j)) (φ₁ (weylRep n (GaloisField 2 f) i))

@[expose] def GGTypeAJoinInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeASplitNbr p B Bs x L D J n f y K →
    ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' → K' ≤ L ⊔ K

section Lifts

variable {n : ℕ} {F : Type} [Field F] {X : Type*} [Group X]

theorem range_mulAutConj_comp {H : Subgroup X} {l : X} (hl : l ∈ H)
    {φ : SpecialLinearGroup (Fin (n + 1)) F →* X} (hφ : φ.range = H) :
    ((MulAut.conj l).toMonoidHom.comp φ).range = H := by
  rw [MonoidHom.range_comp, hφ]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hl)

theorem ker_mulAutConj_comp (l : X) (φ : SpecialLinearGroup (Fin (n + 1)) F →* X) :
    ((MulAut.conj l).toMonoidHom.comp φ).ker = φ.ker := by
  ext g
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · intro h
    calc φ g = l⁻¹ * (l * φ g * l⁻¹) * l := by group
      _ = 1 := by rw [h]; group
  · intro h
    rw [h]
    group

theorem GGTypeAEndNode.of_conj {φ₁ : SpecialLinearGroup (Fin (n + 1)) F →* X} {l T : X}
    (h : GGTypeAEndNode ((MulAut.conj l).toMonoidHom.comp φ₁) T) :
    GGTypeAEndNode φ₁ (l⁻¹ * T * l) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h2 h3
  refine ⟨?_, ?_, ?_⟩
  · calc l⁻¹ * T * l * (l⁻¹ * T * l) = l⁻¹ * (T * T) * l := by group
      _ = 1 := by rw [h1]; group
  · intro j hj
    have e : l⁻¹ * T * l * φ₁ (weylRep n F j) =
        l⁻¹ * (T * (l * φ₁ (weylRep n F j) * l⁻¹)) * l⁻¹⁻¹ := by group
    rw [e, conj_pow, h2 j hj]
    group
  · intro a b hab ha hb c
    have e := h3 a b hab ha hb c
    calc l⁻¹ * T * l * φ₁ (Matrix.SpecialLinearGroup.transvection hab c)
        = l⁻¹ * (T * (l * φ₁ (Matrix.SpecialLinearGroup.transvection hab c) * l⁻¹)) * l := by
          group
      _ = l⁻¹ * ((l * φ₁ (Matrix.SpecialLinearGroup.transvection hab c) * l⁻¹) * T) * l := by
          rw [e]
      _ = φ₁ (Matrix.SpecialLinearGroup.transvection hab c) * (l⁻¹ * T * l) := by group

theorem injective_comp_slLowerBlockHom {φ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F)) :
    Function.Injective (φ.comp (slLowerBlockHom n F)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  exact eq_one_of_slLowerBlockHom_mem_center (hker hg)

theorem injective_comp_slUpperBlockHom {φ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F)) :
    Function.Injective (φ.comp (slUpperBlockHom n F)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  exact eq_one_of_slUpperBlockHom_mem_center (hker hg)

theorem exists_slCompat_lift [Finite F] (hn : 3 ≤ n)
    {φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker₁ : φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hker₂ : φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F))
    (hJ : (φ₁.comp (slLowerBlockHom n F)).range = (φ₂.comp (slUpperBlockHom n F)).range) :
    ∃ φ₂' : SpecialLinearGroup (Fin (n + 1)) F →* X, φ₂'.range = φ₂.range ∧
      φ₂'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F) ∧
      φ₁.comp (slLowerBlockHom n F) = φ₂'.comp (slUpperBlockHom n F) := by
  have hθ₁ := injective_comp_slLowerBlockHom hker₁
  have hθ₂ := injective_comp_slUpperBlockHom hker₂
  let β : MulAut (SpecialLinearGroup (Fin n) F) :=
    ((MonoidHom.ofInjective hθ₁).trans (MulEquiv.subgroupCongr hJ)).trans
      (MonoidHom.ofInjective hθ₂).symm
  have hβ : ∀ g, φ₂ (slUpperBlockHom n F (β g)) = φ₁ (slLowerBlockHom n F g) := by
    intro g
    have e := MulEquiv.apply_symm_apply (MonoidHom.ofInjective hθ₂)
      ((MulEquiv.subgroupCongr hJ) (MonoidHom.ofInjective hθ₁ g))
    have e' := congrArg Subtype.val e
    rw [MonoidHom.ofInjective_apply] at e'
    exact e'.trans (by rw [MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]; rfl)
  obtain ⟨β', hβ'⟩ := exists_mulAut_slUpperBlockHom hn β
  refine ⟨φ₂.comp β'.toMonoidHom, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr β'.surjective, ← MonoidHom.range_eq_map]
  · intro g hg
    have hc : β' g ∈ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F) := hker₂ hg
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro h
    apply β'.injective
    rw [map_mul, map_mul]
    exact hc (β' h)
  · ext g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hβ', hβ]

end Lifts

theorem ggTypeAEndNodeInput_of_inputs (hA : GGTypeAEndBlockLInput) (hB : GGTypeAEndBlockKInput)
    (hC : GGTypeAFarCommuteInput) (hD : GGTypeAJoinInput) : GGTypeAEndNodeInput := by
  intro G _ _ p B Bs x L D J n f hcfg hOp hInn hNoTr hsplit φ₁ hφL hker
  obtain ⟨y, K, hN⟩ := exists_ggTypeASplitNbr hcfg hOp hInn hNoTr hsplit
  obtain ⟨-, -, -, -, hmod, -, hn, -, -, hnbr, -⟩ := id hN
  have hf : 1 ≤ f := hmod.1.2.1
  have h2 : (2 : GaloisField 2 f) = 0 :=
    two_eq_zero_of_card (GaloisField.card 2 f (by omega)) hf
  obtain ⟨l, hlL, hJl⟩ := hA G p B Bs x L D J n f y K hN φ₁ hφL hker
  set ψ₁ := (MulAut.conj l).toMonoidHom.comp φ₁ with hψ₁
  have hψL : ψ₁.range = L := range_mulAutConj_comp hlL hφL
  have hψker : ψ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) := by
    rw [hψ₁, ker_mulAutConj_comp]
    exact hker
  have hψJ : (ψ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J := by
    rw [hψ₁, MonoidHom.comp_assoc, MonoidHom.range_comp, hJl]
  obtain ⟨φ₂₀, hφ₂K, hker₂, hJ₂⟩ := hB G p B Bs x L D J n f y K hN
  obtain ⟨φ₂, hφ₂K', hker₂', hcomp⟩ := exists_slCompat_lift hn hψker hker₂ (hψJ.trans hJ₂.symm)
  rw [hφ₂K] at hφ₂K'
  have hfar := hC G p B Bs x L D J n f y K hN ψ₁ φ₂ hψL hψker hφ₂K' hker₂' hψJ hcomp
    ⟨0, by omega⟩ ⟨n - 1, by omega⟩ rfl (by simp only; omega)
  have hT := ggTypeAEndNode_of_compat h2 hn hcomp hfar
  have hKle := slCompat_range_le h2 (by omega) hcomp
  rw [hψL, hφ₂K'] at hKle
  set T' := φ₂ (weylRep n (GaloisField 2 f) ⟨n - 1, by omega⟩) with hT'
  have hT'K : T' ∈ K := by
    rw [← hφ₂K']
    exact ⟨_, rfl⟩
  refine ⟨l⁻¹ * T' * l, ?_, GGTypeAEndNode.of_conj hT, ?_⟩
  · have hlG := le_ggG0_left p B x L D J hlL
    exact (ggG0 p B x L D J).mul_mem ((ggG0 p B x L D J).mul_mem
      ((ggG0 p B x L D J).inv_mem hlG) (le_ggG0_of_ggNbr (L := L) hnbr hT'K)) hlG
  · intro y' K' hK'
    refine (hD G p B Bs x L D J n f y K hN y' K' hK').trans
      (sup_le le_sup_left (hKle.trans (sup_le le_sup_left ?_)))
    intro z hz
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hz
    have e : (MulAut.conj T').toMonoidHom g =
        l * ((l⁻¹ * T' * l) * (l⁻¹ * g * l) * (l⁻¹ * T' * l)⁻¹) * l⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    have hm : (l⁻¹ * T' * l) * (l⁻¹ * g * l) * (l⁻¹ * T' * l)⁻¹ ∈
        L.map (MulAut.conj (l⁻¹ * T' * l)).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨l⁻¹ * g * l, L.mul_mem (L.mul_mem (L.inv_mem hlL) hg) hlL,
        by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hlL)
      (Subgroup.mem_sup_right hm)) (Subgroup.mem_sup_left (L.inv_mem hlL))

end CFSG.StandardType
