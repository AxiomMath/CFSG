module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpRestr
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpRestrStd
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedNotShape
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedShapeSUCore
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.Open.StatedAPI
public import CFSG.LieType.Universal.SpecialLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec4Classical
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Nt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Main
public import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

private theorem ggA6ShapeSimple_statedSp {K : Type} [Field K] [Finite K] [CharP K 2]
    {n e : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ e) (hne : (n, 2 ^ e) ≠ (2, 2)) :
    GGA6CharTwoLie (StatedSp n K) ∧ IsSimpleGroup (StatedSp n K) := by
  have hK2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at hK; omega
    · exact h
  have hadm : StatedLieAdmissible .PSp n 2 e := ⟨Nat.prime_two, he, hn, hne⟩
  have hZ : Subgroup.center (StatedSp n K) = ⊥ :=
    CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := n) (F := K) (by omega)
  have hmodel : StatedClassicalModel
      (StatedSp n K ⧸ Subgroup.center (StatedSp n K)) .PSp n 2 e :=
    CFSG.LieType.Universal.Symplectic.statedClassicalModel_center_quotient (n := n) (F := K)
      hadm hK
  have q : StatedSp n K ≃* (StatedSp n K ⧸ Subgroup.center (StatedSp n K)) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have hclass : StatedClassicalModel (StatedSp n K) .PSp n 2 e :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv q.symm hmodel
  refine ⟨⟨.PSp, n, e, Or.inl ⟨by decide, hmodel⟩⟩, ?_⟩
  exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ n 2 e hclass

private theorem ggA6ShapeSimple_statedSp_one {K : Type} [Field K] [Finite K] [CharP K 2] {e : ℕ}
    (hK : Nat.card K = 2 ^ e) (h4 : 4 ≤ Nat.card K) :
    GGA6CharTwoLie (StatedSp 1 K) ∧ IsSimpleGroup (StatedSp 1 K) := by
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at hK; omega
    · exact h
  have hne2 : (2, 2 ^ e) ≠ (2, 2) := by
    rintro h
    have h2 : 2 ^ e = 2 := congrArg Prod.snd h
    rw [hK, h2] at h4
    omega
  have hne3 : (2, 2 ^ e) ≠ (2, 3) := by
    rintro h
    have h2 : 2 ^ e = 3 := congrArg Prod.snd h
    have hdvd : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
    rw [h2] at hdvd
    norm_num at hdvd
  have hadm : StatedLieAdmissible .PSL 2 2 e := ⟨Nat.prime_two, he, le_rfl, hne2, hne3⟩
  have hmodel :=
    CFSG.LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient 1 K hadm hK
  have hcenter : Subgroup.center (StatedSL 2 K) =
      (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) :=
    (Subgroup.map_center_eq (specialLinearGroupEquivStatedSL 2 K)).symm.trans
      (map_center_eq_statedScalars 2 K)
  let e2 : StatedSL 2 K ⧸ Subgroup.center (StatedSL 2 K) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hmodelSL : StatedClassicalModel
      (StatedSL 2 K ⧸ Subgroup.center (StatedSL 2 K)) .PSL 2 2 e :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e2.symm hmodel
  have hshapeSL : GGA6CharTwoLie (StatedSL 2 K) :=
    ⟨.PSL, 2, e, Or.inl ⟨by decide, hmodelSL⟩⟩
  have hshape : GGA6CharTwoLie (StatedSp 1 K) :=
    GGA6CharTwoLie.of_mulEquiv
      (CFSG.RankThree.GF2n.Stroth80.nonempty_statedSp_one_mulEquiv_statedSL_two K).some.symm hshapeSL
  have hZ : Subgroup.center (StatedSp 1 K) = ⊥ :=
    CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := 1) (F := K) (by omega)
  have hsub : (StatedScalars (Fin 1 ⊕ Fin 1) K).subgroupOf (StatedSp 1 K) = ⊥ := by
    rw [← CFSG.LieType.Universal.Symplectic.center_eq 1 K, hZ]
  have hproj : IsSimpleGroup (StatedProj (StatedSp 1 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 1 (by omega)
      (Or.inl (Or.inr h4))
  haveI : IsSimpleGroup
      (StatedSp 1 K ⧸ (StatedScalars (Fin 1 ⊕ Fin 1) K).subgroupOf (StatedSp 1 K)) := hproj
  have q : (StatedSp 1 K ⧸ (StatedScalars (Fin 1 ⊕ Fin 1) K).subgroupOf (StatedSp 1 K)) ≃*
      StatedSp 1 K :=
    (QuotientGroup.quotientMulEquivOfEq hsub).trans QuotientGroup.quotientBot
  exact ⟨hshape, MulEquiv.isSimpleGroup q.symm⟩

private theorem four_le_of_ne_two {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hcard : Nat.card F = 2 ^ f) (hne : Nat.card F ≠ 2) : 4 ≤ Nat.card F := by
  have h2 : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  have hf1 : 1 ≤ f := by
    by_contra h
    have : f = 0 := by omega
    rw [hcard, this, pow_zero] at h2
    omega
  have hf2 : 2 ≤ f := by
    by_contra h
    have : f = 1 := by omega
    rw [hcard, this, pow_one] at hne
    exact hne rfl
  rw [hcard]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2

private theorem false_of_a6_component {G : Type} [Group G] {J H : Subgroup G}
    (hJ : IsComponentOf J H) (hA6 : Nonempty (↥J ≃* alternatingGroup (Fin 6)))
    (hsimple : IsSimpleGroup ↥H) (hshape : GGA6CharTwoLie ↥H) : False := by
  have hJne : J ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥J = 1 := by
      rw [hbot]
      exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1, Subgroup.one_mem ⊥⟩⟩
    have hcard : Nat.card ↥J = 360 := by
      obtain ⟨eJ⟩ := hA6
      rw [Nat.card_congr eJ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    omega
  rcases CFSG.Assembly.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hJ.2.1 hsimple with h | h
  · exact hJne h
  · exact absurd (h.symm ▸ hshape)
      (ggA6_not_shape_of_a6 ↥J ↥J hA6 ⟨MulEquiv.refl _⟩)

theorem ggA6_spA6 {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [Finite F] [CharP F 2]
    [FiniteDimensional F V]
    (B : BilinForm F V) (hB : B.IsAlt) (hnd : B.Nondegenerate) (U : Submodule F V)
    (hU : (B.restrict U).Nondegenerate) {J : Subgroup (V ≃ₗ[F] V)}
    (hJ : IsComponentOf J (ggA6SpFixer B (B.orthogonal U)))
    (hA6 : Nonempty (↥J ≃* alternatingGroup (Fin 6))) :
    Module.finrank F U = 4 ∧ Nat.card F = 2 := by
  classical
  let H : Subgroup (V ≃ₗ[F] V) := ggA6SpFixer B (B.orthogonal U)
  have hJH : J ≤ H := hJ.1
  have hB' : (B.restrict U).IsAlt := fun x => hB x
  obtain ⟨r, b, hb⟩ :=
    LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J (B := B.restrict U) hB' hU
  have hdim : Module.finrank F U = 2 * r := by
    have h1 : Module.finrank F U = r + r := by
      simpa using Module.finrank_eq_card_basis b
    omega
  obtain ⟨e1, -⟩ := ggA6_sp_restr_equiv B hB hnd U hU
  obtain ⟨e2⟩ := ggA6_sp_std_equiv (V := V) (B.restrict U) hB' hU r hdim
  let e : H ≃* StatedSp r F := e1.trans e2
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨f, -, hfcard⟩ := FiniteField.card F 2
  have hcardF : Nat.card F = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hfcard]
  have hJcard : Nat.card ↥J = 360 := by
    obtain ⟨eJ⟩ := hA6
    rw [Nat.card_congr eJ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  by_cases hr0 : r = 0
  ·
    have hcardH : Nat.card ↥H = 1 := by
      rw [Nat.card_congr e.toEquiv, hr0,
        CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := F) 0]
      simp
    have hle : Nat.card ↥J ≤ Nat.card ↥H := Subgroup.card_le_of_le hJH
    omega
  by_cases hr1 : r = 1
  · subst hr1
    by_cases hF2 : Nat.card F = 2
    ·
      have hcardH : Nat.card ↥H = 6 := by
        rw [Nat.card_congr e.toEquiv,
          CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := F) 1, hF2]
        norm_num
      have hle : Nat.card ↥J ≤ Nat.card ↥H := Subgroup.card_le_of_le hJH
      omega
    ·
      have h4 : 4 ≤ Nat.card F := four_le_of_ne_two hcardF hF2
      obtain ⟨hshapeSp, hsimpleSp⟩ := ggA6ShapeSimple_statedSp_one (K := F) hcardF h4
      have hsimpleH : IsSimpleGroup ↥H := by
        haveI : IsSimpleGroup (StatedSp 1 F) := hsimpleSp
        exact MulEquiv.isSimpleGroup e
      exfalso
      exact false_of_a6_component hJ hA6 hsimpleH
        (GGA6CharTwoLie.of_mulEquiv e.symm hshapeSp)
  by_cases hr2 : r = 2
  · subst hr2
    by_cases hF2 : Nat.card F = 2
    ·
      exact ⟨by omega, hF2⟩
    ·
      have h4 : 4 ≤ Nat.card F := four_le_of_ne_two hcardF hF2
      have hne : (2, 2 ^ (f : ℕ)) ≠ (2, 2) := by
        intro h
        have h2 : 2 ^ (f : ℕ) = 2 := congrArg Prod.snd h
        exact hF2 (by rw [hcardF, h2])
      obtain ⟨hshapeSp, hsimpleSp⟩ :=
        ggA6ShapeSimple_statedSp (K := F) (n := 2) (e := (f : ℕ)) (by omega) hcardF hne
      have hsimpleH : IsSimpleGroup ↥H := by
        haveI : IsSimpleGroup (StatedSp 2 F) := hsimpleSp
        exact MulEquiv.isSimpleGroup e
      exfalso
      exact false_of_a6_component hJ hA6 hsimpleH
        (GGA6CharTwoLie.of_mulEquiv e.symm hshapeSp)
  ·
    have hne : (r, 2 ^ (f : ℕ)) ≠ (2, 2) := by
      intro h
      have h1 : r = 2 := congrArg Prod.fst h
      omega
    obtain ⟨hshapeSp, hsimpleSp⟩ :=
      ggA6ShapeSimple_statedSp (K := F) (n := r) (e := (f : ℕ)) (by omega) hcardF hne
    have hsimpleH : IsSimpleGroup ↥H := by
      haveI : IsSimpleGroup (StatedSp r F) := hsimpleSp
      exact MulEquiv.isSimpleGroup e
    exfalso
    exact false_of_a6_component hJ hA6 hsimpleH
      (GGA6CharTwoLie.of_mulEquiv e.symm hshapeSp)

end CFSG.StandardType.A6Red
