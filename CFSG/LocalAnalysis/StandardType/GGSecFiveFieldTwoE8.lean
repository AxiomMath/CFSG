module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoExc
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.BigCell
public import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.LocalAnalysis.StandardType.GGFinModelRat
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public section

namespace CFSG.StandardType

namespace FieldTwoE8

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
open CFSG.Open (StatedLieTag)

theorem injective_of_sl2Two {H : Type*} [Group H]
    (φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1) →* H) {A B : Subgroup H}
    (hA : A ≤ φ.range) (hB : B ≤ φ.range) (hA2 : Nat.card A = 2) (hB2 : Nat.card B = 2)
    (hAB : A ⊓ B = ⊥) : Function.Injective φ := by
  have h6 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) = 6 := by
    let := Fintype.ofFinite (GaloisField 2 1)
    have hK : Fintype.card (GaloisField 2 1) = 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card 2 1 one_ne_zero
    rw [Matrix.card_SL_field, hK]
    decide
  have hfin : Finite (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) :=
    Nat.finite_of_card_ne_zero (by rw [h6]; norm_num)
  have hrk : Nat.card φ.range * Nat.card φ.ker = 6 := by
    rw [← h6, Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hr0 : Nat.card φ.range ∣ 6 := Dvd.intro _ hrk
  have h2r : 2 ∣ Nat.card φ.range := by
    have h := Subgroup.card_dvd_of_le hA
    rwa [hA2] at h
  have hne : Nat.card φ.range ≠ 2 := by
    intro h
    have : Finite φ.range := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
    have hAr : A = φ.range := Subgroup.eq_of_le_of_card_ge hA (by rw [h, hA2])
    have hBr : B = φ.range := Subgroup.eq_of_le_of_card_ge hB (by rw [h, hB2])
    have hA1 : A = ⊥ := by rw [← hAB, hAr, hBr, inf_idem]
    rw [hA1, Subgroup.card_bot] at hA2
    norm_num at hA2
  have hle : Nat.card φ.range ≤ 6 := Nat.le_of_dvd (by norm_num) hr0
  have hk : Nat.card φ.ker = 1 := by
    interval_cases h : Nat.card φ.range <;> omega
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Subgroup.eq_bot_of_card_eq _ hk

theorem rootGroup_inf_rootGroup_neg
    {τ : Tag} {K : Type} [Field K] (F : RootOperatorFamily τ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    rootGroup F K γ ⊓ rootGroup F K (-γ) = ⊥ := by
  let φ : (Fin τ.rank → ℤ) →+ ℤ :=
    { toFun := fun v => ∑ i, γ i * v i
      map_zero' := by simp
      map_add' := fun v w => by simp [mul_add, Finset.sum_add_distrib] }
  have hpos : 0 < φ γ := by
    have hne : γ ≠ 0 := hγ.ne_zero
    obtain ⟨i, hi⟩ : ∃ i, γ i ≠ 0 := Function.ne_iff.mp hne
    have h1 : 0 < γ i * γ i := mul_self_pos.mpr hi
    have h2 : γ i * γ i ≤ ∑ j, γ j * γ j :=
      Finset.single_le_sum (f := fun j => γ j * γ j) (fun j _ => mul_self_nonneg (γ j))
        (Finset.mem_univ i)
    exact lt_of_lt_of_le h1 h2
  have h1 : rootGroup F K γ ≤ unip (K := K) φ := rootGroup_le_unip φ hpos
  have h2 : rootGroup F K (-γ) ≤ unip (K := K) (-φ) :=
    rootGroup_le_unip (-φ) (by simpa [φ] using hpos)
  exact eq_bot_iff.mpr ((inf_le_inf h1 h2).trans (unip_inf_unip_neg φ).le)

private theorem sl2Upper_eq_u2' {k : Type} [Field k] (c : k) : sl2Upper c = u2 c :=
  Subtype.ext (by rw [u2_coe]; rfl)

private theorem sl2Lower_eq_l2' {k : Type} [Field k] (c : k) : sl2Lower c = l2 c :=
  Subtype.ext (by rw [l2_coe]; rfl)

section Cert

theorem exists_selectedSL2Model_E8 :
    ∃ γ, Nonempty (SelectedRoot.SelectedSL2Model (ggU .E8 0 1).D (GaloisField 2 1) γ) := by
  have hγ : IsRoot Tag.E8 (Pi.single (0 : Fin (Tag.rank .E8)) 1) := isRoot_single _ _
  have hγn : IsRoot Tag.E8 (-Pi.single (0 : Fin (Tag.rank .E8)) 1) := isRoot_neg_single _ _
  obtain ⟨φ, ε₁, ε₂, hε₁, hε₂, hφ⟩ :=
    CFSG.LieType.SeitzGeneration.ExcOuterLeOne.exists_rootSL2 (K := GaloisField 2 1) hγ
  have hsq : ∀ ε : ℤ, (ε = 1 ∨ ε = -1) →
      (ε : GaloisField 2 1) * (ε : GaloisField 2 1) = 1 := by
    rintro ε (rfl | rfl) <;> simp
  set F := rootOperatorFamily Tag.E8
  have hup : (RankOneXfer.sl2UpperUniSub (GaloisField 2 1)).map φ =
      rootGroup F (GaloisField 2 1) (Pi.single 0 1) := by
    ext g
    constructor
    · rintro ⟨A, ⟨c, rfl⟩, rfl⟩
      rw [sl2Upper_eq_u2', (hφ c).1]
      exact xPar_mem hγ _
    · intro hg
      obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ g).1 hg
      refine ⟨sl2Upper ((ε₁ : GaloisField 2 1) * c), ⟨_, rfl⟩, ?_⟩
      change φ (sl2Upper _) = _
      rw [sl2Upper_eq_u2', (hφ _).1, ← mul_assoc, hsq ε₁ hε₁, one_mul]
  have hlow : (Subgroup.closure (Set.range (sl2Lower : GaloisField 2 1 → _))).map φ =
      rootGroup F (GaloisField 2 1) (-Pi.single 0 1) := by
    apply le_antisymm
    · rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
      rw [sl2Lower_eq_l2', (hφ c).2]
      exact xPar_mem hγn _
    · intro g hg
      obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγn g).1 hg
      refine ⟨sl2Lower ((ε₂ : GaloisField 2 1) * c), Subgroup.subset_closure ⟨_, rfl⟩, ?_⟩
      change φ (sl2Lower _) = _
      rw [sl2Lower_eq_l2', (hφ _).2, ← mul_assoc, hsq ε₂ hε₂, one_mul]
  have hcard : ∀ {δ : Fin (Tag.rank .E8) → ℤ}, IsRoot Tag.E8 δ →
      Nat.card (rootGroup F (GaloisField 2 1) δ) = 2 := by
    intro δ hδ
    have hK : Nat.card (GaloisField 2 1) = 2 := by
      rw [GaloisField.card 2 1 one_ne_zero, pow_one]
    refine (Nat.card_congr (Equiv.ofBijective (fun c => (⟨xPar F δ c, xPar_mem hδ c⟩ :
      rootGroup F (GaloisField 2 1) δ)) ⟨fun c d h => xPar_injective hδ (congrArg Subtype.val h),
        fun g => ?_⟩)).symm.trans hK
    obtain ⟨c, hc⟩ := (mem_rootGroup_iff hδ g.1).1 g.2
    exact ⟨c, Subtype.ext hc⟩
  have hinj : Function.Injective φ :=
    injective_of_sl2Two φ (hup ▸ Subgroup.map_le_range φ _) (hlow ▸ Subgroup.map_le_range φ _)
      (hcard hγ) (hcard hγn) (rootGroup_inf_rootGroup_neg F hγ)
  exact ⟨_, ⟨SelectedRoot.SelectedSL2Model.ofGF2Upper (ggU .E8 0 1).D _
    (mem_adjDatum_roots.2 hγ) φ hinj hup⟩⟩

variable {G : Type} [Group G]

theorem selected_of_member {t : StatedLieTag} {n f : ℕ} {L : Subgroup G}
    (ψ : (ggU t n f).K →* G) (hψ : Function.Injective ψ) {M : Subgroup (ggU t n f).K}
    (hML : M.map ψ = L) {t' : StatedLieTag} {n' : ℕ} (ψ₀ : (ggU t' n' 1).K →* (ggU t n f).K)
    (hadm : StatedLieAdmissible t' n' 2 1) (hrk : 2 ≤ (ggU t' n' 1).D.rank)
    (hker : ψ₀.ker ≤ Subgroup.center (ggU t' n' 1).K) (hrange : ψ₀.range = M)
    {δ : Fin (ggU t' n' 1).D.rank → ℤ}
    (model' : SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) δ)
    {γ : Fin (ggU t n f).D.rank → ℤ} (hγ : γ ∈ (ggU t n f).D.roots) (u₀ : (ggU t n f).K)
    (hroot : ((ggU t' n' 1).D.rootGroup δ).map ψ₀ =
      ((ggU t n f).D.rootGroup γ).map (MulAut.conj u₀).toMonoidHom) :
    ∃ (t' : StatedLieTag) (n' : ℕ) (ψ' : (ggU t' n' 1).K →* G),
      StatedLieAdmissible t' n' 2 1 ∧ 2 ≤ (ggU t' n' 1).D.rank ∧
        ψ'.ker ≤ Subgroup.center (ggU t' n' 1).K ∧ ψ'.range = L ∧
        ∃ (γ : Fin (ggU t n f).D.rank → ℤ) (δ : Fin (ggU t' n' 1).D.rank → ℤ)
          (model : SelectedRoot.SelectedSL2Model (ggU t n f).D (GaloisField 2 1) γ)
          (model' : SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) δ),
          ∃ u₀ : (ggU t n f).K,
            ((ψ.comp (MulAut.conj u₀).toMonoidHom).comp model.phi).range =
              (ψ'.comp model'.phi).range := by
  have hι : Function.Injective (ψ₀.comp model'.phi) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
      ← CFSG.Timmesfeld.RankOne.center_SL2_eq_bot (GaloisField 2 1)]
    intro A hA
    have hz : model'.phi A ∈ Subgroup.center (ggU t' n' 1).K := hker hA
    rw [Subgroup.mem_center_iff]
    intro B
    exact model'.injective (by rw [map_mul, map_mul]; exact Subgroup.mem_center_iff.mp hz _)
  let φ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1) →* (ggU t n f).K :=
    (MulAut.conj u₀⁻¹).toMonoidHom.comp (ψ₀.comp model'.phi)
  have hφ : Function.Injective φ := (MulAut.conj u₀⁻¹).injective.comp hι
  have hup : (RankOneXfer.sl2UpperUniSub (GaloisField 2 1)).map φ =
      (ggU t n f).D.rootGroup γ := by
    have h1 : (RankOneXfer.sl2UpperUniSub (GaloisField 2 1)).map φ =
        (((RankOneXfer.sl2UpperUniSub (GaloisField 2 1)).map model'.phi).map ψ₀).map
          (MulAut.conj u₀⁻¹).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    have h2 : (MulAut.conj u₀⁻¹).toMonoidHom.comp (MulAut.conj u₀).toMonoidHom =
        MonoidHom.id _ := by
      ext y
      simp [mul_assoc]
    rw [h1, model'.upper_eq, hroot, Subgroup.map_map, h2, Subgroup.map_id]
  refine ⟨t', n', ψ.comp ψ₀, hadm, hrk, ?_, ?_, γ, δ,
    SelectedRoot.SelectedSL2Model.ofGF2Upper _ γ hγ φ hφ hup, model', u₀, ?_⟩
  · intro y hy
    apply hker
    rw [MonoidHom.mem_ker] at hy ⊢
    exact hψ (by rw [← MonoidHom.comp_apply, hy, map_one])
  · rw [MonoidHom.range_comp, hrange, hML]
  · rw [SelectedRoot.SelectedSL2Model.ofGF2Upper_phi]
    congr 1
    ext A
    simp [φ, MulAut.conj_apply, mul_assoc]

end Cert

end FieldTwoE8

end CFSG.StandardType

end
