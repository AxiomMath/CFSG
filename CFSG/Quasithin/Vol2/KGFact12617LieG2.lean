module

public import CFSG.Quasithin.Vol2.KGFact12617LieW
public import CFSG.LieType.Chevalley.RootOps.Comm
public import CFSG.LieType.Chevalley.BorelOvergroups
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LieType.Chevalley.StandardParabolicCells
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.Blueprint.ChevalleyPinnedLemmas
public import CFSG.Blueprint.ChevalleyRoots
public import CFSG.Quasithin.Background.SmithB42G2Id
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Eq

public section

namespace CFSG.Quasithin.H13.KG12617Lie

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

theorem quasithinO2QuotientIso_map {G G' : Type*} [Group G] [Group G'] {B : Subgroup G}
    {X : Type*} [Group X] (f : G →* G') (hf : Function.Injective f)
    (h : quasithinO2QuotientIso B X) : quasithinO2QuotientIso (B.map f) X := by
  obtain ⟨φ, hφs, hφk⟩ := h
  let ι : ↥B ≃* ↥(B.map f) := B.equivMapOfInjective f hf
  refine ⟨φ.comp ι.symm.toMonoidHom, hφs.comp ι.symm.surjective, ?_⟩
  rw [← map_pCore_mulEquiv 2 ι, ← hφk]
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, Subgroup.mem_map,
    MulEquiv.coe_toMonoidHom]
  constructor
  · intro hx
    exact ⟨ι.symm x, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem commutator_mem_of_coe_eq_mul {G : Type*} [Group G] {U Q V : Subgroup G} (hQU : Q ≤ U)
    (hUQ : U ≤ Subgroup.normalizer (Q : Set G)) (hVU : V ≤ U)
    (hUQV : (U : Set G) = (Q : Set G) * (V : Set G)) (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    {x y : G} (hx : x ∈ U) (hy : y ∈ U) : ⁅x, y⁆ ∈ Q := by
  have hN : (Q.subgroupOf U).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQU).2 hUQ
  have hmk : ∀ z (hz : z ∈ U), ∃ v, ∃ hv : v ∈ V,
      (QuotientGroup.mk (⟨z, hz⟩ : ↥U) : ↥U ⧸ Q.subgroupOf U) = QuotientGroup.mk ⟨v, hVU hv⟩ := by
    intro z hz
    have hz' : z ∈ (Q : Set G) * (V : Set G) := hUQV ▸ hz
    obtain ⟨q, hq, v, hv, rfl⟩ := hz'
    refine ⟨v, hv, ?_⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : ((⟨q * v, hz⟩ : ↥U)⁻¹ * ⟨v, hVU hv⟩ : ↥U) = v⁻¹ * q⁻¹ * v := by
      simp [mul_assoc]
    rw [h1]
    have hv' : v⁻¹ ∈ U := U.inv_mem (hVU hv)
    have := (Subgroup.mem_normalizer_iff.mp (hUQ hv') q⁻¹).mp (Q.inv_mem hq)
    simpa [mul_assoc] using this
  obtain ⟨v₁, hv₁, h₁⟩ := hmk x hx
  obtain ⟨v₂, hv₂, h₂⟩ := hmk y hy
  have hc : (QuotientGroup.mk ⁅(⟨x, hx⟩ : ↥U), (⟨y, hy⟩ : ↥U)⁆ : ↥U ⧸ Q.subgroupOf U) = 1 := by
    rw [← QuotientGroup.mk'_apply, map_commutatorElement, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, h₁, h₂, ← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply,
      ← map_commutatorElement]
    have hcomm : ⁅(⟨v₁, hVU hv₁⟩ : ↥U), (⟨v₂, hVU hv₂⟩ : ↥U)⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (hV _ hv₁ _ hv₂)
    rw [hcomm, map_one]
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hc
  simpa [commutatorElement_def] using hc

section Chevalley

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

theorem eq_single_of_isRoot_G2 {α : Fin Tag.G2.rank → ℤ}
    (hα : IsRoot .G2 α) (hpos : 0 < height α) {i j : Fin Tag.G2.rank} (hji : j ≠ i)
    (hi : α i = 0) : α = Pi.single j 1 := by
  have key : ∀ β ∈ rootFinset Tag.G2, 0 < height β → ∀ i j : Fin Tag.G2.rank, j ≠ i →
      β i = 0 → β = Pi.single j 1 := by decide +kernel
  exact key α (mem_rootFinset.2 hα) hpos i j hji hi

@[expose] noncomputable def pinnedHom
    (R : Type) [CommRing R] (α : Fin Tag.G2.rank → ℤ) :
    Multiplicative R →* (Module.End R (RootModule Tag.G2 R))ˣ where
  toFun c := pinnedX Tag.G2 R α (Multiplicative.toAdd c)
  map_one' := pinnedX_zero Tag.G2 R α
  map_mul' _ _ := pinnedX_add Tag.G2 R α _ _

theorem rootSubgroup_eq_range
    (R : Type) [CommRing R] (α : Fin Tag.G2.rank → ℤ) :
    rootSubgroup Tag.G2 R α = (pinnedHom R α).range := by
  have hr : Set.range (pinnedX Tag.G2 R α) = ((pinnedHom R α).range : Set _) := by
    rw [MonoidHom.coe_range]
    ext g
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨Multiplicative.ofAdd c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨Multiplicative.toAdd c, rfl⟩
  rw [rootSubgroup, hr, Subgroup.closure_eq]

theorem rootSubgroup_comm
    (R : Type) [CommRing R] (α : Fin Tag.G2.rank → ℤ) :
    ∀ a ∈ rootSubgroup Tag.G2 R α, ∀ b ∈ rootSubgroup Tag.G2 R α, a * b = b * a := by
  rw [rootSubgroup_eq_range]
  rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem parabolicLeviUnipotent_comm
    {F : Type} [Field F] {J : Set (Fin Tag.G2.rank)} (hJ : J ≠ Set.univ) :
    ∀ a ∈ parabolicLeviUnipotent Tag.G2 F J, ∀ b ∈ parabolicLeviUnipotent Tag.G2 F J,
      a * b = b * a := by
  obtain ⟨i, hi⟩ : ∃ i, i ∉ J := by
    by_contra h
    push Not at h
    exact hJ (Set.eq_univ_of_forall h)
  obtain ⟨j, hji⟩ : ∃ j : Fin Tag.G2.rank, j ≠ i := by
    have key : ∀ i : Fin Tag.G2.rank, ∃ j, j ≠ i := by decide
    exact key i
  have hle : parabolicLeviUnipotent Tag.G2 F J ≤ rootSubgroup Tag.G2 F (Pi.single j 1) := by
    unfold parabolicLeviUnipotent rootSpan
    refine iSup₂_le fun α hα => ?_
    rw [eq_single_of_isRoot_G2 hα.1.1 hα.2.2 hji (hα.1.2 i hi)]
  intro a ha b hb
  exact rootSubgroup_comm F _ a (hle ha) b (hle hb)

theorem exists_le_conj {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {S₀ D : Subgroup G}
    (hS₀ : IsPGroup p ↥S₀) (hidx : ¬ p ∣ S₀.index) (hD : IsPGroup p ↥D) :
    ∃ h : G, D ≤ S₀.map (MulAut.conj h).toMonoidHom := by
  obtain ⟨S, hS⟩ := hD.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G (hS₀.toSylow hidx) S
  refine ⟨h, hS.trans ?_⟩
  rw [← hh, CFSG.LieType.Chevalley.coe_smul_sylow_eq_map]
  rfl

section MainG2

variable {F : Type} [Field F] [Finite F] [CharP F 2]

local notation "CG" => adjointGroup Tag.G2 F

theorem false_of_normalizes_adjointG2
    {B W : Subgroup ↥CG}
    (hBiso : quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6))) (hW : W ≠ ⊥)
    (hW2 : IsPGroup 2 ↥W) (hBW : B ≤ Subgroup.normalizer (W : Set ↥CG)) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := Tag.G2) (K := F)
  set U := posUnipotent Tag.G2 F with hU
  have hUC : U ≤ CG := posUnipotent_le_adjointGroup
  obtain ⟨S, P, hPne, hNP, -, -, hSP⟩ := holds_adjointGroup_tag Tag.G2 F 2 W hW hW2
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max fun w : WeylGroup Tag.G2 => (coxeterSystem Tag.G2).length w
  obtain ⟨P₀, hP₀⟩ := (exceptional_ordinary_Sylow_opposition Tag.G2 F 2 w₀ hw₀).1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥CG P₀ S
  set φ : ↥CG →* ↥CG := (MulAut.conj g⁻¹).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj g⁻¹).injective
  set P' := P.map φ with hP'
  set B' := B.map φ with hB'
  have hB'P' : B' ≤ P' := Subgroup.map_mono (hBW.trans hNP)
  have hcomp : φ.comp (MulAut.conj g).toMonoidHom = MonoidHom.id ↥CG := by
    ext x
    simp [hφ, mul_assoc]
  have hUS : U.subgroupOf CG = (S : Subgroup ↥CG).map φ := by
    rw [← hg, coe_smul_sylow_eq_map, Subgroup.map_map, hcomp, Subgroup.map_id, hP₀]
  have hNU : Subgroup.normalizer ((U.subgroupOf CG : Subgroup ↥CG) : Set ↥CG) ≤ P' := by
    rw [hUS, hφ, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hSP
  set A := P'.map (Subgroup.subtype CG) with hA
  have hBA : borelGroup Tag.G2 F ≤ A := by
    intro x hx
    have hxC : x ∈ CG := borelGroup_le_adjointGroup' hx
    refine ⟨⟨x, hxC⟩, hNU ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    have hxN : x ∈ Subgroup.normalizer (U : Set (ModGL Tag.G2 F)) := by
      refine (sup_le torusGroup_le_normalizer_posUnipotent (Subgroup.le_normalizer)) hx
    exact Subgroup.mem_normalizer_iff.mp hxN y
  have hAC : A ≤ CG := Subgroup.map_subtype_le _
  have hAeq := (borel_overgroup_classification Tag.G2 F).1 A hBA hAC
  set J := {i | weylElt Tag.G2 F i 1 ∈ A} with hJdef
  have hJ : J ≠ Set.univ := by
    intro hJu
    apply hPne
    have hAtop : A = CG := by
      rw [hAeq, hJu]
      exact (standard_parabolic_cells Tag.G2 F).2.2.2.2.2.1
    have hP'top : P' = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : (x : ModGL Tag.G2 F) ∈ A := by
        rw [hAtop]
        exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      rwa [Subtype.ext hyx] at hy
    apply Subgroup.map_injective hφinj
    rw [← hP', hP'top, Subgroup.map_top_of_surjective φ (MulAut.conj g⁻¹).surjective]
  set PJ := parabolicSubgroup Tag.G2 F J with hPJ
  set Q := parabolicRadical Tag.G2 F J with hQ
  set V := parabolicLeviUnipotent Tag.G2 F J with hV
  obtain ⟨hQP, hQn, -⟩ := parabolic_root_radical_Levi_factors Tag.G2 F J
  have hPQ : PJ ≤ Subgroup.normalizer (Q : Set (ModGL Tag.G2 F)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).1 hQn
  have hUPJ : U ≤ PJ := posUnipotent_le_parabolicSubgroup J
  have hPJC : PJ ≤ CG := parabolicSubgroup_le_adjointGroup Tag.G2 F J
  have hQU : Q ≤ U := parabolicRadical_le_posUnipotent J
  have hVU : V ≤ U := parabolicLeviUnipotent_le_posUnipotent J
  have hUQV := posUnipotent_eq_mul_parabolic (τ := Tag.G2) (K := F) J
  have hVc := parabolicLeviUnipotent_comm (F := F) hJ
  have := Fintype.ofFinite F
  obtain ⟨m, -, hm⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2 ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card, hm]
  have hQ2 : IsPGroup 2 ↥Q := by
    refine IsPGroup.of_card (n := (m : ℕ) * (parabolicRadicalRoots Tag.G2 J).ncard) ?_
    rw [card_parabolicRadical, hF, ← pow_mul]
  have hU2 : IsPGroup 2 ↥U := by
    refine IsPGroup.of_card
      (n := (m : ℕ) * {α : Fin Tag.G2.rank → ℤ | IsRoot Tag.G2 α ∧ 0 < height α}.ncard) ?_
    rw [card_posUnipotent, hF, ← pow_mul]
  have hUidxC : ¬ 2 ∣ U.relIndex CG := by
    have h := P₀.not_dvd_index
    rwa [hP₀] at h
  have hUidx : ¬ 2 ∣ (U.subgroupOf PJ).index := by
    intro h2
    apply hUidxC
    rw [← Subgroup.relIndex_mul_relIndex U PJ CG hUPJ hPJC]
    exact h2.mul_right _
  have hcommPJ : ∀ D : Subgroup (ModGL Tag.G2 F), D ≤ PJ → IsPGroup 2 ↥D →
      ∀ x ∈ D, ∀ y ∈ D, ⁅x, y⁆ ∈ Q := by
    intro D hDP hD2 x hx y hy
    have := finite_modGL (τ := Tag.G2) (K := F)
    obtain ⟨h, hh⟩ := exists_le_conj (G := ↥PJ) (hU2.comap_subtype) hUidx (hD2.comap_subtype)
    obtain ⟨x₀, hx₀, hxx₀⟩ := hh (show (⟨x, hDP hx⟩ : ↥PJ) ∈ D.subgroupOf PJ from hx)
    obtain ⟨y₀, hy₀, hyy₀⟩ := hh (show (⟨y, hDP hy⟩ : ↥PJ) ∈ D.subgroupOf PJ from hy)
    have hc := commutator_mem_of_coe_eq_mul hQU (hUPJ.trans hPQ) hVU hUQV hVc hx₀ hy₀
    have ex : x = (h : ModGL Tag.G2 F) * x₀ * (h : ModGL Tag.G2 F)⁻¹ := by
      have := congrArg Subtype.val hxx₀
      simpa using this.symm
    have ey : y = (h : ModGL Tag.G2 F) * y₀ * (h : ModGL Tag.G2 F)⁻¹ := by
      have := congrArg Subtype.val hyy₀
      simpa using this.symm
    have hconj : ⁅x, y⁆ = (h : ModGL Tag.G2 F) * ⁅(x₀ : ModGL Tag.G2 F), (y₀ : ModGL Tag.G2 F)⁆ *
        (h : ModGL Tag.G2 F)⁻¹ := by
      rw [ex, ey, commutatorElement_def, commutatorElement_def]
      group
    rw [hconj]
    exact (Subgroup.mem_normalizer_iff.mp (hPQ h.2) _).mp hc
  have hB'Q : B' ≤ Subgroup.normalizer ((Q.subgroupOf CG : Subgroup ↥CG) : Set ↥CG) := by
    intro b hb
    have hbA : (b : ModGL Tag.G2 F) ∈ A := ⟨b, hB'P' hb, rfl⟩
    rw [hAeq] at hbA
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hPQ hbA) y
  refine false_of_commutator_mem (quasithinO2QuotientIso_map φ hφinj hBiso) hQ2.comap_subtype
    hB'Q fun D hDB hD2 x hx y hy => ?_
  have hxy : ((⁅x, y⁆ : ↥CG) : ModGL Tag.G2 F) = ⁅(x : ModGL Tag.G2 F), (y : ModGL Tag.G2 F)⁆ :=
    map_commutatorElement (Subgroup.subtype CG) x y
  rw [Subgroup.mem_comap, Subgroup.coe_subtype, hxy]
  have hDA : D.map (Subgroup.subtype CG) ≤ PJ := by
    rw [← hAeq]
    exact Subgroup.map_mono (hDB.trans hB'P')
  exact hcommPJ (D.map (Subgroup.subtype CG)) hDA (hD2.map _) _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩

end MainG2

end Chevalley

theorem nonempty_adjointGroup_mulEquiv_quasithinG2
    {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) :
    Nonempty (↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 F) ≃* ↥(quasithinG2 F)) := by
  obtain ⟨ψ, -, hsurj, hker⟩ := CFSG.Quasithin.B42G2Id.exists_adjointGroup_hom_cayleyGroup hF hf
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, CFSG.LieType.Chevalley.center_adjointGroup_eq_bot]
  exact ⟨(MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).trans (MulEquiv.subgroupCongr
    (CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup (K := F))).symm⟩

theorem false_of_normalizes_g2
    {F : Type} [Field F] [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f)
    {B W : Subgroup ↥(quasithinG2 F)}
    (hBiso : quasithinO2QuotientIso B ↥(alternatingGroup (Fin 6))) (hW : W ≠ ⊥)
    (hW2 : IsPGroup 2 ↥W) (hBW : B ≤ Subgroup.normalizer (W : Set ↥(quasithinG2 F))) :
    False := by
  have : CharP F 2 := CFSG.Quasithin.B42G2Id.charP_two_of_card hF
  obtain ⟨e⟩ := nonempty_adjointGroup_mulEquiv_quasithinG2 hF hf
  refine false_of_normalizes_adjointG2 (F := F) (B := B.map e.symm.toMonoidHom)
    (W := W.map e.symm.toMonoidHom) (quasithinO2QuotientIso_map _ e.symm.injective hBiso)
    ?_ (hW2.map _) ?_
  · intro h
    apply hW
    rwa [Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective] at h
  · rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hBW

end CFSG.Quasithin.H13.KG12617Lie
