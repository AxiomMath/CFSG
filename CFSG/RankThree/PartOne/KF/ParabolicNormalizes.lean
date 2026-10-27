module

public import CFSG.LieType.Chevalley.SylowOpposition

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits

theorem exists_conj_le_of_normalizes {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (U S : Sylow p G) (B P : Subgroup G)
    (hB : B ≤ Subgroup.normalizer ((U : Subgroup G) : Set G))
    (hS : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ P) :
    ∃ g : G, B ≤ P.comap (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G U S
  refine ⟨g, ?_⟩
  rw [← Subgroup.map_le_iff_le_comap]
  calc B.map (MulAut.conj g).toMonoidHom
      ≤ (Subgroup.normalizer ((U : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hB
    _ = Subgroup.normalizer (((U : Subgroup G).map (MulAut.conj g).toMonoidHom : Subgroup G) :
          Set G) := Subgroup.map_equiv_normalizer_eq _ _
    _ = Subgroup.normalizer ((S : Subgroup G) : Set G) := by
      rw [← coe_smul_sylow_eq_map, hg]
    _ ≤ P := hS

section Borel

theorem borelGroup_le_adjointGroup' (τ : Tag) {K : Type} [Field K] :
    borelGroup τ K ≤ adjointGroup τ K :=
  ((triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.2 K).1

theorem borelGroup_subgroupOf_le_normalizer (τ : Tag) {K : Type} [Field K] :
    (borelGroup τ K).subgroupOf (adjointGroup τ K) ≤
      Subgroup.normalizer (((posUnipotent τ K).subgroupOf (adjointGroup τ K) :
        Subgroup (adjointGroup τ K)) : Set (adjointGroup τ K)) := by
  have hBC : borelGroup τ K ≤ adjointGroup τ K := borelGroup_le_adjointGroup' τ
  have hUB : posUnipotent τ K ≤ borelGroup τ K := le_sup_right
  have hBN : borelGroup τ K ≤ Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).1
      (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.1
  intro b hb
  have hb' : (b : ModGL τ K) ∈ borelGroup τ K := hb
  have : b ∈ (Subgroup.normalizer (posUnipotent τ K : Set (ModGL τ K))).subgroupOf
      (adjointGroup τ K) := hBN hb'
  rwa [Subgroup.subgroupOf_normalizer_eq (hUB.trans hBC)] at this

end Borel

section Parabolic

theorem exists_parabolic_of_borel_le (τ : Tag) {K : Type} [Field K]
    (P₁ : Subgroup (adjointGroup τ K))
    (hB : (borelGroup τ K).subgroupOf (adjointGroup τ K) ≤ P₁) (hP₁ : P₁ ≠ ⊤) :
    ∃ J : Set (Fin τ.rank), J ≠ Set.univ ∧
      ∀ y ∈ P₁, (y : ModGL τ K) ∈ parabolicSubgroup τ K J := by
  have hBC : borelGroup τ K ≤ adjointGroup τ K := borelGroup_le_adjointGroup' τ
  set A : Subgroup (ModGL τ K) := P₁.map (adjointGroup τ K).subtype
  have hBA : borelGroup τ K ≤ A := fun b hb =>
    ⟨⟨b, hBC hb⟩, hB (show (⟨b, hBC hb⟩ : adjointGroup τ K) ∈
      (borelGroup τ K).subgroupOf (adjointGroup τ K) from hb), rfl⟩
  have hAC : A ≤ adjointGroup τ K := Subgroup.map_subtype_le _
  have hAJ := (borel_overgroup_classification τ K).1 A hBA hAC
  refine ⟨{i | weylElt τ K i 1 ∈ A}, fun huniv => hP₁ ?_, fun y hy => ?_⟩
  · rw [eq_top_iff]
    intro y _
    have hy : (y : ModGL τ K) ∈ A := by
      rw [hAJ, huniv, (standard_parabolic_cells τ K).2.2.2.2.2.1]
      exact y.2
    obtain ⟨y', hy', hyy⟩ := hy
    have : y' = y := Subtype.ext hyy
    rwa [← this]
  · rw [← hAJ]
    exact ⟨y, hy, rfl⟩

theorem exists_hom_into_parabolic_of_normalizes (τ : Tag) {K : Type} [Field K] [Finite K]
    [CharP K 2] {U E : Subgroup (adjointGroup τ K)} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hE : E ≤ Subgroup.normalizer (U : Set (adjointGroup τ K))) :
    ∃ (J : Set (Fin τ.rank)) (φ : E →* ModGL τ K), J ≠ Set.univ ∧ Function.Injective φ ∧
      ∀ e, φ e ∈ parabolicSubgroup τ K J := by
  have hfin : Finite (ModGL τ K) := finite_modGL
  have hBC : borelGroup τ K ≤ adjointGroup τ K := borelGroup_le_adjointGroup' τ
  have hUC : posUnipotent τ K ≤ adjointGroup τ K := le_sup_right.trans hBC
  obtain ⟨S, P, hPtop, hNU, -, -, hNS⟩ := holds_adjointGroup_tag τ K 2 U hU hU2
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 hUC card_posUnipotent
  have hUc := IsPGroup.toSylow_coe hUp hUi
  obtain ⟨g, hg⟩ := exists_conj_le_of_normalizes (hUp.toSylow hUi) S
    ((borelGroup τ K).subgroupOf (adjointGroup τ K)) P
    (by rw [hUc]; exact borelGroup_subgroupOf_le_normalizer τ) hNS
  have hP₁top : P.comap (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    intro h
    apply hPtop
    rw [eq_top_iff]
    intro y _
    have hy : (MulAut.conj g).toMonoidHom ((MulAut.conj g).symm y) ∈ P :=
      Subgroup.mem_comap.1 (h ▸ Subgroup.mem_top _)
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hy
  obtain ⟨J, hJ, hJP⟩ := exists_parabolic_of_borel_le τ _ hg hP₁top
  have hE₁P : ∀ e : E, (MulAut.conj g⁻¹).toMonoidHom (e : adjointGroup τ K) ∈
      P.comap (MulAut.conj g).toMonoidHom := fun e => by
    rw [Subgroup.mem_comap]
    have h1 : (MulAut.conj g).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom (e : adjointGroup τ K)) =
        (e : adjointGroup τ K) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [h1]
    exact hNU (hE e.2)
  refine ⟨J, ((adjointGroup τ K).subtype.comp (MulAut.conj g⁻¹).toMonoidHom).comp E.subtype,
    hJ, (adjointGroup τ K).subtype_injective.comp ((MulAut.conj g⁻¹).injective.comp
      E.subtype_injective), fun e => ?_⟩
  exact hJP _ (hE₁P e)

theorem card_dvd_parabolic_of_normalizes (τ : Tag) {K : Type} [Field K] [Finite K] [CharP K 2]
    {U E : Subgroup (adjointGroup τ K)} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hE : E ≤ Subgroup.normalizer (U : Set (adjointGroup τ K))) :
    ∃ J : Set (Fin τ.rank), J ≠ Set.univ ∧ Nat.card E ∣ Nat.card (parabolicSubgroup τ K J) := by
  obtain ⟨J, φ, hJ, hφ, hmem⟩ := exists_hom_into_parabolic_of_normalizes τ hU hU2 hE
  refine ⟨J, hJ, ?_⟩
  have hfin : Finite (ModGL τ K) := finite_modGL
  have hle : φ.range ≤ parabolicSubgroup τ K J := by
    rintro _ ⟨e, rfl⟩
    exact hmem e
  have h1 := Subgroup.card_dvd_of_le hle
  rwa [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv] at h1

end Parabolic

end CFSG.RankThree.PartOne.KFU
