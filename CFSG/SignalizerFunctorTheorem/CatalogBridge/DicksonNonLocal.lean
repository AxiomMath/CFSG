module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocal
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearPSL2
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
import CFSG.LieType.SteinbergBRMulEquivCores
import CFSG.Assembly.OrderReductions.LinearOrders
import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinear
import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAction

public section

open CFSG.Open
open scoped MatrixGroups Pointwise

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem eq_bot_of_solvable_normal_of_simple_normal {G : Type*} [Group G] (S : Subgroup G)
    [S.Normal] [IsSimpleGroup S] (hS : ∃ a b : S, a * b ≠ b * a)
    (hC : Subgroup.centralizer (S : Set G) = ⊥) (R : Subgroup G) [R.Normal]
    (hR : Group.IsSolvable R) : R = ⊥ := by
  have hRS : R ⊓ S = ⊥ := by
    have hnorm : (R.subgroupOf S).Normal := (inferInstance : R.Normal).subgroupOf S
    rcases hnorm.eq_bot_or_eq_top with hbot | htop
    · rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hx.2⟩ : S) ∈ R.subgroupOf S := hx.1
      rw [hbot, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hx')
    · exfalso
      have hSR : S ≤ R := Subgroup.subgroupOf_eq_top.mp htop
      have : Group.IsSolvable S :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hSR)
          (Subgroup.inclusion_injective hSR)
      obtain ⟨a, b, hab⟩ := hS
      exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr this a b)
  rw [eq_bot_iff]
  intro r hr
  have hrC : r ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 : r * s * r⁻¹ * s⁻¹ ∈ R := by
      have : s * r⁻¹ * s⁻¹ ∈ R := (inferInstance : R.Normal).conj_mem _ (R.inv_mem hr) s
      simpa [mul_assoc] using R.mul_mem hr this
    have h2 : r * s * r⁻¹ * s⁻¹ ∈ S := by
      have : r * s * r⁻¹ ∈ S := (inferInstance : S.Normal).conj_mem s hs r
      exact S.mul_mem this (S.inv_mem hs)
    have h3 : r * s * r⁻¹ * s⁻¹ = 1 := by
      have := (Subgroup.mem_inf.mpr ⟨h1, h2⟩ : r * s * r⁻¹ * s⁻¹ ∈ R ⊓ S)
      rwa [hRS, Subgroup.mem_bot] at this
    calc s * r = (r * s * r⁻¹ * s⁻¹)⁻¹ * (r * s) := by group
      _ = r * s := by rw [h3]; simp
  rw [hC, Subgroup.mem_bot] at hrC
  exact Subgroup.mem_bot.mpr hrC

theorem eq_bot_of_solvable_normal_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hG : ∃ a b : G, a * b ≠ b * a) (R : Subgroup G) [R.Normal] (hR : Group.IsSolvable R) :
    R = ⊥ := by
  rcases (inferInstance : R.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    rw [h] at hR
    have : Group.IsSolvable G := Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom) (MulEquiv.surjective _)
    obtain ⟨a, b, hab⟩ := hG
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr this a b)

theorem eq_bot_of_solvable_normal_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ∀ R : Subgroup Y, R.Normal → Group.IsSolvable R → R = ⊥) (R : Subgroup X) [R.Normal]
    (hR : Group.IsSolvable R) : R = ⊥ := by
  have hn : (R.map e.toMonoidHom).Normal := Subgroup.Normal.map inferInstance e.toMonoidHom
    e.surjective
  have hs : Group.IsSolvable (R.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective
      (f := (R.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom) (MulEquiv.surjective _)
  exact (Subgroup.map_eq_bot_iff_of_injective R e.injective).mp (hY _ hn hs)

theorem psl2_simple_not_isSolvable {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ∧
      ¬ Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  have : Fintype F := Fintype.ofFinite F
  have hs4 : ∃ s : Finset F, s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨s, hs⟩
  obtain ⟨hnt, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) le_rfl
    (Or.inr hs4)
  have hperf := CFSG.LinearGroups.linear_projective_perfect (K := F) le_rfl (Or.inr hs4)
  exact ⟨hsimple, CFSG.LieType.SteinbergBR.not_isSolvable_of_isPerfect⟩

theorem solvable_normal_trivial_psl2 {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F)
    (R : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) [R.Normal]
    (hR : Group.IsSolvable R) : R = ⊥ := by
  obtain ⟨hs, hns⟩ := psl2_simple_not_isSolvable h4
  refine eq_bot_of_solvable_normal_of_simple ?_ R hR
  by_contra hcon
  push Not at hcon
  exact hns (Group.isSolvable_of_comm fun a b => hcon a b)

theorem solvable_normal_trivial_pgl2 {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F)
    (R : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F)) [R.Normal] (hR : Group.IsSolvable R) :
    R = ⊥ := by
  obtain ⟨hs, hns⟩ := psl2_simple_not_isSolvable h4
  let ι : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F →* Matrix.ProjGenLinGroup (Fin 2) F :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hinj : Function.Injective ι := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  let S : Subgroup (Matrix.ProjGenLinGroup (Fin 2) F) := ι.range
  have : S.Normal := CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglPSLRange_normal F
  let e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* S := MonoidHom.ofInjective hinj
  have : IsSimpleGroup S := e.symm.isSimpleGroup
  have hnonab : ∃ a b : S, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    apply hns
    exact Group.isSolvable_of_comm fun a b => e.injective (by
      rw [map_mul, map_mul]; exact hcon _ _)
  refine eq_bot_of_solvable_normal_of_simple_normal S hnonab ?_ R hR
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at hg
  rw [Subgroup.mem_bot]
  have hact : CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction F g = 1 := by
    ext x
    apply hinj
    rw [CFSG.ComponentClassification.CatalogueSchreierLinearTwo.toPGL_pglAction]
    have := hg (ι x) ⟨x, rfl⟩
    simp only [MulAut.one_apply]
    calc g * ι x * g⁻¹ = (ι x * g) * g⁻¹ := by rw [this]
      _ = ι x := by group
  have hinjact : Function.Injective
      (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction F) := by
    intro a b hab
    have h1 : CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction F
        (SemidirectProduct.inl a) =
        CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction F
          (SemidirectProduct.inl b) := by
      rw [CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inl,
        CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inl]
      exact hab
    exact SemidirectProduct.inl_injective
      (CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_injective F h1)
  exact hinjact (hact.trans (map_one _).symm)

theorem isSolvable_psl2_of_card_le_three {F : Type} [Field F] [Finite F] (h : Nat.card F ≤ 3) :
    Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hc := CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear F 2 (by norm_num)
  have h23 : Nat.card F = 2 ∨ Nat.card F = 3 := by omega
  rcases h23 with h2' | h3'
  · refine isSolvable_of_natCard_two_three (a := 1) (b := 1) ?_
    rw [hc, h2']
    norm_num
  · refine isSolvable_of_natCard_two_three (a := 2) (b := 1) ?_
    rw [hc, h3']
    norm_num

theorem isSolvable_pgl2_of_card_le_three {F : Type} [Field F] [Finite F] (h : Nat.card F ≤ 3) :
    Group.IsSolvable (Matrix.ProjGenLinGroup (Fin 2) F) := by
  have : Fintype F := Fintype.ofFinite F
  have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hc := Matrix.card_GL_field (𝔽 := F) 2
  rw [← Nat.card_eq_fintype_card] at hc
  have hGL : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) F) := by
    have h23 : Nat.card F = 2 ∨ Nat.card F = 3 := by omega
    rcases h23 with h2' | h3'
    · refine isSolvable_of_natCard_two_three (a := 1) (b := 1) ?_
      rw [hc, Fin.prod_univ_two, h2']
      norm_num
    · refine isSolvable_of_natCard_two_three (a := 4) (b := 1) ?_
      rw [hc, Fin.prod_univ_two, h3']
      norm_num
  exact Group.isSolvable_of_surjective (f := Matrix.ProjGenLinGroup.mk)
    Matrix.ProjGenLinGroup.mk_surjective

theorem solvable_normal_trivial_of_not_isSolvable_psl2
    {K : Type} [Field K] [Finite K]
    (N : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))
    (hN : ¬ Group.IsSolvable N) (R : Subgroup N) [R.Normal] (hR : Group.IsSolvable R) :
    R = ⊥ := by
  obtain ⟨ℓ, f', hℓ, hcharK, hf'1, hK⟩ := exists_char_card K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hK N with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, -, hNz, ⟨eD⟩⟩ | ⟨-, ⟨e4⟩⟩ | ⟨-, ⟨eS⟩⟩ | ⟨-, ⟨eA⟩⟩ |
      ⟨m, t, -, -, N₀, C, hN₀, hN₀el, -, hCcyc, -, -, hsup⟩ | ⟨m, hm, -, ⟨eP⟩⟩ |
      ⟨m, hm, -, ⟨eG⟩⟩
  · exact absurd (Group.isSolvable_of_comm fun a b => hEl.toIsMulCommutative.is_comm.comm a b) hN
  · have : CommGroup N := IsCyclic.commGroup
    exact absurd (inferInstance : Group.IsSolvable N) hN
  · have hz : NeZero z := ⟨fun h0 => by
      have hpos : 0 < Nat.card N := Nat.card_pos
      rw [hNz, h0] at hpos
      omega⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z
    exact absurd (isSolvable_of_mulEquiv' eD) hN
  · have : Nat.card (alternatingGroup (Fin 4)) = 2 ^ 2 * 3 ^ 1 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    have := isSolvable_of_natCard_two_three this
    exact absurd (isSolvable_of_mulEquiv' e4) hN
  · have : Nat.card (Equiv.Perm (Fin 4)) = 2 ^ 3 * 3 ^ 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      decide
    have := isSolvable_of_natCard_two_three this
    exact absurd (isSolvable_of_mulEquiv' eS) hN
  · have := alternatingGroup.isSimpleGroup (α := Fin 5) (by simp)
    have hA : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      have : IsMulCommutative (alternatingGroup (Fin 5)) := ⟨⟨fun a b => hcon a b⟩⟩
      have h3 := alternatingGroup.isMulCommutative_iff_card_le_three.1 this
      simp at h3
    exact eq_bot_of_solvable_normal_of_mulEquiv eA
      (fun R' _ hR' => eq_bot_of_solvable_normal_of_simple hA R' hR') R hR
  · have : IsMulCommutative N₀ := hN₀el.toIsMulCommutative
    have hNs : Group.IsSolvable N₀ := Group.isSolvable_of_comm fun a b => this.is_comm.comm a b
    have : N₀.Normal := hN₀
    have : CommGroup C := IsCyclic.commGroup
    have hsurj : Function.Surjective ((QuotientGroup.mk' N₀).comp C.subtype) := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N₀ y
      have hx : x ∈ N₀ ⊔ C := hsup ▸ Subgroup.mem_top x
      have hx' : x ∈ (N₀ : Set N) * (C : Set N) := by
        rw [← Subgroup.normal_mul]
        exact hx
      obtain ⟨n, hn, c, hc, rfl⟩ := hx'
      refine ⟨⟨c, hc⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
    have hQs : Group.IsSolvable (N ⧸ N₀) := Group.isSolvable_of_surjective hsurj
    exact absurd (Group.isSolvable_of_ker_le_range N₀.subtype (QuotientGroup.mk' N₀) (by
      rw [QuotientGroup.ker_mk', Subgroup.range_subtype])) hN
  · have hcardF : Nat.card (GaloisField ℓ m) = ℓ ^ m := GaloisField.card ℓ m hm
    by_cases h4 : 4 ≤ Nat.card (GaloisField ℓ m)
    · exact eq_bot_of_solvable_normal_of_mulEquiv eP
        (fun R' _ hR' => solvable_normal_trivial_psl2 h4 R' hR') R hR
    · have := isSolvable_psl2_of_card_le_three (F := GaloisField ℓ m) (by omega)
      exact absurd (isSolvable_of_mulEquiv' eP) hN
  · have hcardF : Nat.card (GaloisField ℓ m) = ℓ ^ m := GaloisField.card ℓ m hm
    by_cases h4 : 4 ≤ Nat.card (GaloisField ℓ m)
    · exact eq_bot_of_solvable_normal_of_mulEquiv eG
        (fun R' _ hR' => solvable_normal_trivial_pgl2 h4 R' hR') R hR
    · have := isSolvable_pgl2_of_card_le_three (F := GaloisField ℓ m) (by omega)
      exact absurd (isSolvable_of_mulEquiv' eG) hN

theorem nonLocalized_of_not_isSolvable_psl2
    {K : Type} [Field K] [Finite K]
    (C : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) (hC : ¬ Group.IsSolvable C) :
    NonLocalized C := by
  intro T hT hs hle
  set N := Subgroup.normalizer (T : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) with hNdef
  have hNns : ¬ Group.IsSolvable N := fun h =>
    hC (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle))
  have hRn : (T.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have hRs : Group.IsSolvable (T.subgroupOf N) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := T))).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := T))).injective
  have hbot := solvable_normal_trivial_of_not_isSolvable_psl2 N hNns (T.subgroupOf N) hRs
  apply hT
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, Subgroup.le_normalizer hx⟩ : N) ∈ T.subgroupOf N := hx
  rw [hbot, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hx')

end CFSG.SignalizerFunctorTheorem.CatalogBridge
