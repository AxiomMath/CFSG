module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitTorus
import CFSG.LocalAnalysis.StandardType.GGLangCorootPair
import CFSG.LocalAnalysis.StandardType.GGQTwoRationalWeyl
import CFSG.LocalAnalysis.StandardType.GGNTPlaneTableOrbits

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.LangRat
  CFSG.StandardType.NTPlane CFSG.StandardType.QTwoCav

noncomputable section

abbrev e6SplitPerm : Equiv.Perm (Fin Tag.E6.rank) := TwistTag.E6.perm

theorem isRoot_permLattice_e6SplitRoot (i : ExcRaw.Root 1) :
    IsRoot .E6 (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) := by
  have h : IsRoot .E6 (permLattice TwistTag.E6.perm (e6SplitRoot i)) :=
    (isRoot_e6SplitRoot i).permLattice (TwistTag.cartan_perm TwistTag.E6)
  exact h

theorem permLattice_permLattice_e6SplitRoot (i : ExcRaw.Root 1) :
    permLattice (τ := .E6) e6SplitPerm
        (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) = e6SplitRoot i := by
  revert i
  decide +kernel

theorem e6SplitRoot_fixed_iff (i : ExcRaw.Root 1) :
    permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i) = e6SplitRoot i ↔
      ExcRaw.tabFix1.getD i.val false = true := by
  revert i
  decide +kernel

theorem e6SplitShortFacts (i : ExcRaw.Root 1)
    (h : ExcRaw.tabFix1.getD i.val false = false) :
    iform (e6SplitRoot i)
        (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) = 0 ∧
      ¬ IsRoot .E6
        (e6SplitRoot i + permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) ∧
      ¬ IsRoot .E6
        (e6SplitRoot i - permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) := by
  revert i
  simp only [NTPlane.isRoot_iff_mem_e6RootList]
  decide +kernel


section CertDef


@[expose] noncomputable def e6SplitWeyl (L : Type) [Field L] (i : ExcRaw.Root 1) :
    ModGL .E6 L :=
  if ExcRaw.tabFix1.getD i.val false = true then rootSL2 .E6 L (e6SplitRoot i) WSL
  else rootSL2 .E6 L (e6SplitRoot i) WSL *
    rootSL2 .E6 L (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL


end CertDef

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
variable {S : LangSetup .E6 L p}

theorem e6SplitRho_eq (hS : E6SplitLangTwo S) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot .E6 γ) :
    S.ρ γ = -permLattice (τ := .E6) e6SplitPerm γ := by
  rw [hS.2.2 γ hγ]
  rfl


section Main


omit [IsAlgClosed L]
  in
private theorem rootSL2_neg_WSL [CharP L 2] {β : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot .E6 β) :
    rootSL2 .E6 L (-β) WSL = rootSL2 .E6 L β WSL := by
  have hβ' : IsRoot .E6 (-β) := IsRoot.neg hβ
  have e₁ : (WSL : SL2 L) = uSL 1 * vSL 1 * uSL 1 := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, coe_WSL]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
  have e₂ : (WSL : SL2 L) = vSL 1 * uSL 1 * vSL 1 := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_vSL, coe_WSL]
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
  calc rootSL2 .E6 L (-β) WSL
      = rootSL2 .E6 L (-β) (vSL 1 * uSL 1 * vSL 1) := by rw [e₂]
    _ = pinnedX .E6 L β 1 * pinnedX .E6 L (-β) 1 * pinnedX .E6 L β 1 := by
          rw [map_mul, map_mul, rootSL2_vSL_of_charTwo hβ' 1,
            rootSL2_uSL_of_charTwo hβ' 1]
          simp
    _ = rootSL2 .E6 L β (uSL 1 * vSL 1 * uSL 1) := by
          rw [map_mul, map_mul, rootSL2_uSL_of_charTwo hβ 1,
            rootSL2_vSL_of_charTwo hβ 1]
    _ = rootSL2 .E6 L β WSL := by rw [e₁]

omit [IsAlgClosed L]
  in
private theorem e6SplitWeyl_short_commute [CharP L 2] (i : ExcRaw.Root 1)
    (h : ExcRaw.tabFix1.getD i.val false = false) :
    rootSL2 .E6 L (e6SplitRoot i) WSL *
        rootSL2 .E6 L
          (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL =
      rootSL2 .E6 L
          (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL *
        rootSL2 .E6 L (e6SplitRoot i) WSL := by
  have hγ : IsRoot .E6 (e6SplitRoot i) := isRoot_e6SplitRoot i
  have hσ : IsRoot .E6
      (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) :=
    isRoot_permLattice_e6SplitRoot i
  have hs := e6SplitShortFacts i h
  exact exceptional_Lang_strongly_orthogonal_root_rank_one_commutation .E6 L hγ hσ hs.1
    hs.2.1 hs.2.2 _ ⟨WSL, rfl⟩ _ ⟨WSL, rfl⟩

omit [IsAlgClosed L]
  in
theorem e6SplitWeyl_mul_self [hchar : CharP L 2] (i : ExcRaw.Root 1) :
    e6SplitWeyl L i * e6SplitWeyl L i = 1 := by
  have hγ : IsRoot .E6 (e6SplitRoot i) := isRoot_e6SplitRoot i
  by_cases hfix : ExcRaw.tabFix1.getD i.val false = true
  · rw [e6SplitWeyl, if_pos hfix]
    exact rootSL2_WSL_mul_self (e6SplitRoot i)
  · have hfalse : ExcRaw.tabFix1.getD i.val false = false := by
      cases h : ExcRaw.tabFix1.getD i.val false <;> simp_all
    have hcomm := e6SplitWeyl_short_commute (L := L) i hfalse
    rw [e6SplitWeyl, if_neg hfix]
    calc (rootSL2 .E6 L (e6SplitRoot i) WSL *
          rootSL2 .E6 L
            (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL) *
        (rootSL2 .E6 L (e6SplitRoot i) WSL *
          rootSL2 .E6 L
            (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL)
        = rootSL2 .E6 L (e6SplitRoot i) WSL *
            (rootSL2 .E6 L
              (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL *
            rootSL2 .E6 L (e6SplitRoot i) WSL) *
            rootSL2 .E6 L
              (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL := by
            group
      _ = rootSL2 .E6 L (e6SplitRoot i) WSL *
            (rootSL2 .E6 L (e6SplitRoot i) WSL *
            rootSL2 .E6 L
              (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL) *
            rootSL2 .E6 L
              (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL := by
            rw [← hcomm]
      _ = (rootSL2 .E6 L (e6SplitRoot i) WSL *
            rootSL2 .E6 L (e6SplitRoot i) WSL) *
            (rootSL2 .E6 L
              (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL *
            rootSL2 .E6 L
              (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL) := by
            group
      _ = 1 := by
            rw [rootSL2_WSL_mul_self (e6SplitRoot i),
              rootSL2_WSL_mul_self
                (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)), one_mul]

private theorem e6SplitWeyl_mem_model [hchar : CharP L 2] (hS : E6SplitLangTwo S)
    (i : ExcRaw.Root 1) (h : ExcRaw.tabFix1.getD i.val false = false) :
    e6SplitWeyl L i ∈ S.D.model := by
  have hγ : IsRoot .E6 (e6SplitRoot i) := isRoot_e6SplitRoot i
  have hσ : IsRoot .E6
      (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) :=
    isRoot_permLattice_e6SplitRoot i
  have hnt : ¬ (ExcRaw.tabFix1.getD i.val false = true) := by rw [h]; simp
  have hρσ : S.ρ (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) =
      -e6SplitRoot i := by
    rw [e6SplitRho_eq hS hσ, permLattice_permLattice_e6SplitRoot]
  have hstepγ : S.D.step (rootSL2 .E6 L (e6SplitRoot i) WSL) =
      rootSL2 .E6 L
        (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL := by
    rw [step_rootSL2_WSL_of_charTwo S hγ, e6SplitRho_eq hS hγ]
    exact rootSL2_neg_WSL (L := L) hσ
  have hstepσ : S.D.step
      (rootSL2 .E6 L
        (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL) =
      rootSL2 .E6 L (e6SplitRoot i) WSL := by
    rw [step_rootSL2_WSL_of_charTwo S hσ, hρσ]
    exact rootSL2_neg_WSL (L := L) hγ
  have hcomm := e6SplitWeyl_short_commute (L := L) i h
  rw [e6SplitWeyl, if_neg hnt]
  refine S.D.mem_model.2 ⟨?_, ?_⟩
  · exact mul_mem (rootSL2_mem_adjointGroup _ _) (rootSL2_mem_adjointGroup _ _)
  · change S.D.step (rootSL2 .E6 L (e6SplitRoot i) WSL *
        rootSL2 .E6 L
          (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL) =
      rootSL2 .E6 L (e6SplitRoot i) WSL *
        rootSL2 .E6 L
          (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL
    rw [map_mul, hstepγ, hstepσ]
    exact hcomm.symm

theorem e6SplitWeyl_mem_Γ (hS : E6SplitLangTwo S) (i : ExcRaw.Root 1) :
    e6SplitWeyl L i ∈ S.Γ := by
  have hτ : Tag.E6 = .F4 ∨ Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 :=
    Or.inr (Or.inl rfl)
  have hq : S.D.q = 2 ^ 1 := by rw [hS.1, pow_one]
  have hchar : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow S hq
  have hγ : IsRoot .E6 (e6SplitRoot i) := isRoot_e6SplitRoot i
  by_cases hfix : ExcRaw.tabFix1.getD i.val false = true
  · rw [e6SplitWeyl, if_pos hfix]
    have hσ : permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i) = e6SplitRoot i :=
      (e6SplitRoot_fixed_iff i).2 hfix
    refine rootSL2_WSL_mem_Γ_of_rho S hτ hq hS.2.1 hγ (Or.inr ?_)
    rw [e6SplitRho_eq hS hγ, hσ]
  · have hfalse : ExcRaw.tabFix1.getD i.val false = false := by
      cases h : ExcRaw.tabFix1.getD i.val false <;> simp_all
    refine langModel_mem_Γ_of_sq_eq_one S hτ hq hS.2.1
      (e6SplitWeyl_mem_model (L := L) (hchar := hchar) hS i hfalse) ?_
    rw [pow_two]
    exact e6SplitWeyl_mul_self (L := L) (hchar := hchar) i

theorem e6SplitWeyl_conj_rootDiagUnit (S : LangSetup .E6 L p) (i : ExcRaw.Root 1)
    (b : Fin Tag.E6.rank → Lˣ) :
    e6SplitWeyl L i * rootDiagUnit .E6 b * (e6SplitWeyl L i)⁻¹ =
      rootDiagUnit .E6 (weylTuple (e6SplitRefl i) b) := by
  have hγ : IsRoot .E6 (e6SplitRoot i) := isRoot_e6SplitRoot i
  by_cases hfix : ExcRaw.tabFix1.getD i.val false = true
  · rw [e6SplitWeyl, e6SplitRefl, if_pos hfix, if_pos hfix]
    exact rootWeylSL2_conj_rootDiagUnit S hγ b
  · have hσ : IsRoot .E6
        (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) :=
      isRoot_permLattice_e6SplitRoot i
    rw [e6SplitWeyl, e6SplitRefl, if_neg hfix, if_neg hfix]
    have h₁ := rootWeylSL2_conj_rootDiagUnit S hσ b
    have h₂ := rootWeylSL2_conj_rootDiagUnit S hγ
      (weylTuple (rootReflection (permLattice (τ := .E6) e6SplitPerm
        (e6SplitRoot i))) b)
    calc rootSL2 .E6 L (e6SplitRoot i) WSL *
          rootSL2 .E6 L
            (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL *
          rootDiagUnit .E6 b *
          (rootSL2 .E6 L (e6SplitRoot i) WSL *
            rootSL2 .E6 L
              (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL)⁻¹
        = rootSL2 .E6 L (e6SplitRoot i) WSL *
            (rootSL2 .E6 L
              (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL *
              rootDiagUnit .E6 b *
              (rootSL2 .E6 L
                (permLattice (τ := .E6) e6SplitPerm (e6SplitRoot i)) WSL)⁻¹) *
            (rootSL2 .E6 L (e6SplitRoot i) WSL)⁻¹ := by
            rw [mul_inv_rev]
            group
      _ = rootSL2 .E6 L (e6SplitRoot i) WSL *
            rootDiagUnit .E6 (weylTuple
              (rootReflection (permLattice (τ := .E6) e6SplitPerm
                (e6SplitRoot i))) b) *
            (rootSL2 .E6 L (e6SplitRoot i) WSL)⁻¹ := by rw [h₁]
      _ = rootDiagUnit .E6 (weylTuple (rootReflection (e6SplitRoot i))
            (weylTuple (rootReflection (permLattice (τ := .E6) e6SplitPerm
              (e6SplitRoot i))) b)) := h₂
      _ = rootDiagUnit .E6 (weylTuple
            (rootReflection (e6SplitRoot i) *
              rootReflection (permLattice (τ := .E6) e6SplitPerm
                (e6SplitRoot i))) b) := by rw [weylTuple_weylTuple]

namespace E6SplitDatum

variable {T₀ : Subgroup (ModGL .E6 L)} (d : E6SplitDatum S T₀)
include d

theorem e6SplitWeyl_mem_normalizer (hS : E6SplitLangTwo S) (i : ExcRaw.Root 1) :
    e6SplitWeyl L i ∈ Subgroup.normalizer (T₀ : Set (ModGL .E6 L)) := by
  have hchar : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow S (by rw [hS.1, pow_one])
  have hinv : (e6SplitWeyl L i)⁻¹ = e6SplitWeyl L i :=
    inv_eq_of_mul_eq_one_right (e6SplitWeyl_mul_self (L := L) (hchar := hchar) i)
  have hforward : ∀ t : ModGL .E6 L, t ∈ T₀ →
      e6SplitWeyl L i * t * (e6SplitWeyl L i)⁻¹ ∈ T₀ := by
    intro t ht
    obtain ⟨b, hb⟩ := E6SplitDatum.exists_rootDiagUnit d ⟨t, ht⟩
    have hb' : t = rootDiagUnit .E6 b := hb
    have hbT : rootDiagUnit .E6 b ∈ T₀ := hb' ▸ ht
    obtain ⟨hh, -⟩ := E6SplitDatum.weylTuple_e6SplitRefl_mem d hS i hbT
    rw [show e6SplitWeyl L i * t * (e6SplitWeyl L i)⁻¹ =
        e6SplitWeyl L i * rootDiagUnit .E6 b * (e6SplitWeyl L i)⁻¹ by rw [hb'],
      e6SplitWeyl_conj_rootDiagUnit S i b]
    exact hh
  refine Subgroup.mem_normalizer_iff.2 fun t => ⟨hforward t, fun ht => ?_⟩
  set y := e6SplitWeyl L i * t * (e6SplitWeyl L i)⁻¹ with hy
  have h := hforward y ht
  have ht_eq : t = e6SplitWeyl L i * y * (e6SplitWeyl L i)⁻¹ := by
    rw [hy, hinv]
    have hn2 : e6SplitWeyl L i * e6SplitWeyl L i = 1 := e6SplitWeyl_mul_self i
    calc t = (e6SplitWeyl L i * e6SplitWeyl L i) * t *
          (e6SplitWeyl L i * e6SplitWeyl L i) := by rw [hn2]; group
      _ = e6SplitWeyl L i * (e6SplitWeyl L i * t * e6SplitWeyl L i) *
          e6SplitWeyl L i := by group
  rw [ht_eq]
  exact h

theorem ggLin_ggConjAut_e6SplitWeyl (hS : E6SplitLangTwo S) (i : ExcRaw.Root 1) :
    ggLin (p := 3) d.coord (ggConjAut T₀ (e6SplitWeyl_mem_normalizer d hS i)) =
      ExcRaw.reflection 1 i := by
  have hnN : e6SplitWeyl L i ∈ Subgroup.normalizer (T₀ : Set (ModGL .E6 L)) :=
    e6SplitWeyl_mem_normalizer d hS i
  refine LinearEquiv.ext fun v => ?_
  set t : ↥T₀ := Additive.toMul (d.coord.symm v) with ht
  have hv : d.coord (Additive.ofMul t) = v := by
    rw [ht]
    exact d.coord.apply_symm_apply v
  obtain ⟨b, hb⟩ := E6SplitDatum.exists_rootDiagUnit d t
  have hbT : rootDiagUnit .E6 b ∈ T₀ := hb ▸ t.2
  obtain ⟨hh, hcoord⟩ := E6SplitDatum.weylTuple_e6SplitRefl_mem d hS i hbT
  have ht_eq : (⟨rootDiagUnit .E6 b, hbT⟩ : ↥T₀) = t := Subtype.ext hb.symm
  have hAut : ggConjAut T₀ hnN t =
      ⟨rootDiagUnit .E6 (weylTuple (e6SplitRefl i) b), hh⟩ := by
    apply Subtype.ext
    rw [ggConjAut_apply, hb]
    exact e6SplitWeyl_conj_rootDiagUnit S i b
  calc ggLin (p := 3) d.coord (ggConjAut T₀ hnN) v
      = ggLin (p := 3) d.coord (ggConjAut T₀ hnN) (d.coord (Additive.ofMul t)) := by
          rw [hv]
    _ = d.coord (Additive.ofMul (ggConjAut T₀ hnN t)) := ggLin_apply_ofMul d.coord _ t
    _ = d.coord (Additive.ofMul
          ⟨rootDiagUnit .E6 (weylTuple (e6SplitRefl i) b), hh⟩) := by rw [hAut]
    _ = ExcRaw.reflection 1 i
          (d.coord (Additive.ofMul ⟨rootDiagUnit .E6 b, hbT⟩)) := hcoord
    _ = ExcRaw.reflection 1 i v := by rw [ht_eq, hv]

theorem reflection_mem_map_ggAutomizer (hS : E6SplitLangTwo S) (i : ExcRaw.Root 1) :
    ExcRaw.reflection 1 i ∈ (ggAutomizer S.Γ T₀).map (ggLin (p := 3) d.coord) :=
  Subgroup.mem_map.2 ⟨ggConjAut T₀ (e6SplitWeyl_mem_normalizer d hS i),
    ggConjAut_mem_ggAutomizer (e6SplitWeyl_mem_Γ hS i) (e6SplitWeyl_mem_normalizer d hS i),
    ggLin_ggConjAut_e6SplitWeyl d hS i⟩

theorem ambientNormalizer_le_map_ggAutomizer (hS : E6SplitLangTwo S) :
    ExcRaw.ambientNormalizer 1 ≤ (ggAutomizer S.Γ T₀).map (ggLin (p := 3) d.coord) := by
  rw [ExcRaw.ambientNormalizer]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  exact E6SplitDatum.reflection_mem_map_ggAutomizer d hS i

end E6SplitDatum

end Main

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
