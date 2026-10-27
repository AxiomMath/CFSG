module

public import CFSG.Milestones.ASVolI.F429.Base
public import CFSG.Milestones.ASVolI.F429.aU5Chart
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExtSp4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExtL3
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section Generic

variable {G : Type} [Group G]

theorem burnsideF429a_of_model [Finite G] {Gp M : Subgroup G} {C : Type} [Group C]
    (Ψ : C ≃* ↥Gp) {P U : Subgroup C} (hP : M.subgroupOf Gp = P.map Ψ.toMonoidHom)
    (hU : ChF.IsSylowOf 2 U ⊤) (hUP : U ≤ perfectCore P) :
    (∀ S : Subgroup G, S ≤ Gp ⊓ M → IsPGroup 2 S → S ≤ perfectCore (Gp ⊓ M)) ∧
      oPPrime 2 (Gp ⊓ M) = perfectCore (Gp ⊓ M) := by
  have hUS : ChF.IsSylowOf 2 U P :=
    burnsideF429_isSylowOf_of_le hU (hUP.trans (perfectCore_le P)) le_top
  refine ⟨fun S hS hS2 => burnsideF429_le_perfectCore_of_model Ψ hP hUS hUP hS hS2, ?_⟩
  have hφ : Function.Injective (Gp.subtype.comp Ψ.toMonoidHom) :=
    Gp.subtype_injective.comp Ψ.injective
  have hinf := burnsideF429_inf_eq_map Ψ hP
  refine burnsideF429_oPPrime_eq_perfectCore (S := U.map (Gp.subtype.comp Ψ.toMonoidHom)) ?_ ?_
  · rw [hinf]
    exact burnsideF429_isSylowOf_map _ hφ hUS
  · rw [hinf, burnsideF429_perfectCore_map _ hφ]
    exact Subgroup.map_mono hUP

theorem burnsideF429a_sbar [Finite G] (Gp M₁ M₂ : Subgroup G) :
    IsPGroup 2 (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) ∧ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ Gp ⊓ M₁ ∧
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ Gp ⊓ M₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle := CFSG.LieType.BorelTits.pCoreOf_le 2 (Gp ⊓ (M₁ ⊓ M₂))
  exact ⟨CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _,
    hle.trans (inf_le_inf_left Gp inf_le_left), hle.trans (inf_le_inf_left Gp inf_le_right)⟩

theorem burnsideF429a_of_model₂ [Finite G] {Gp M₁ M₂ : Subgroup G} {C : Type} [Group C]
    (Ψ : C ≃* ↥Gp) {P₁ P₂ U : Subgroup C} (hP₁ : M₁.subgroupOf Gp = P₁.map Ψ.toMonoidHom)
    (hP₂ : M₂.subgroupOf Gp = P₂.map Ψ.toMonoidHom) (hU : ChF.IsSylowOf 2 U ⊤)
    (hUP₁ : U ≤ perfectCore P₁) (hUP₂ : U ≤ perfectCore P₂) :
    (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∧
        pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂)) ∧
      oPPrime 2 (Gp ⊓ M₁) = perfectCore (Gp ⊓ M₁) ∧
        oPPrime 2 (Gp ⊓ M₂) = perfectCore (Gp ⊓ M₂) := by
  obtain ⟨hS2, hS1, hS2'⟩ := burnsideF429a_sbar Gp M₁ M₂
  obtain ⟨k₁, e₁⟩ := burnsideF429a_of_model Ψ hP₁ hU hUP₁
  obtain ⟨k₂, e₂⟩ := burnsideF429a_of_model Ψ hP₂ hU hUP₂
  exact ⟨⟨k₁ _ hS1 hS2, k₂ _ hS2' hS2⟩, e₁, e₂⟩

end Generic

section U4

open CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin.H13.U4Par

theorem burnsideF429a_U4_pkg {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U4 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∧
        pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂)) ∧
      oPPrime 2 (Gp ⊓ M₁) = perfectCore (Gp ⊓ M₁) ∧
        oPPrime 2 (Gp ⊓ M₂) = perfectCore (Gp ⊓ M₂) := by
  haveI := hyp.finite
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U4) hyp.toHypF_4_4g
  obtain ⟨Φ, e1, e2⟩ := burnsideF4gU4_exists_equiv marking
  exact burnsideF429a_of_model₂ Φ (h1.trans e1) (h2.trans e2)
    (isSylowTwoOf_hypUnitriangular _) (hypUnitriangular_le_perfectCore_parP _ hf)
    (hypUnitriangular_le_perfectCore_parP2 _ hf)

theorem burnsideF429a_c3_U4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U4 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∧
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂) :=
  (burnsideF429a_U4_pkg hyp hf).1

end U4

section Sp4

open CFSG.QuasithinUnique.Setup.X7a CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

theorem burnsideF429a_Sp4_pkg {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∧
        pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂)) ∧
      oPPrime 2 (Gp ⊓ M₁) = perfectCore (Gp ⊓ M₁) ∧
        oPPrime 2 (Gp ⊓ M₂) = perfectCore (Gp ⊓ M₂) := by
  haveI := hyp.finite
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .Sp4) hyp.toHypF_4_4g
  obtain ⟨e, he⟩ := burnsideF4gSpOne_parabolic_eq marking
  have hK : Nat.card marking.field = 2 ^ f := by simpa using marking.field_card
  haveI : CharP marking.field 2 := burnsideF4gSp_charP_of_card hK
  have hpkg := CFSG.Quasithin.Rk2.rank2PkgExt_sp4 hK hf
  obtain ⟨P, hP⟩ := exists_sylow_projUnipotent (K := marking.field) 2 (r := 2) (by norm_num)
  have hU : ChF.IsSylowOf 2 (projUnipotent 2 marking.field) ⊤ := by
    rw [← hP]
    exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have e0 := he false
  have e1 := he true
  simp only [Bool.false_eq_true, if_false, if_true] at e0 e1
  exact burnsideF429a_of_model₂ e (h1.trans e0) (h2.trans e1) hU (hpkg.le_perfectCore 0)
    (hpkg.le_perfectCore 1)

theorem burnsideF429a_c3_Sp4 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .Sp4 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∧
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂) :=
  (burnsideF429a_Sp4_pkg hyp hf).1

end Sp4

section L3

open CFSG.ASVolI.ChF.ClassicalRoots CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a

private theorem burnsideF429a_L3_comap_nativeParabolic (q : ℕ) (K : Type) [Field K]
    (basis : GL (Fin 3) K) (hb : basis = 1) (b : Bool) :
    (nativeParabolic .L3 q K basis b).comap
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toMonoidHom =
      Q3 K (if b then 1 else 0) := by
  subst hb
  ext A
  have h1 : A ∈ (nativeParabolic .L3 q K 1 b).comap
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toMonoidHom ↔
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K A : GL (Fin 3) K)) ∈
        rawStabilizer ((fun vector =>
            ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec vector) ''
          coordinateSpace (if b then flagTwo .L3 else flagOne .L3 : Set (Fin 3))) :=
    Iff.rfl
  refine h1.trans ?_
  rw [burnsideF4d_Y1_mem_rawStabilizer, burnsideF4d_Y1_image_one, Q3,
    burnsideF4d_Y1_mem_stabilizer_iff]
  have key : ∀ (S : Set (Fin 3)) (i : ℕ), S = {p : Fin 3 | (p : ℕ) < i} →
      ((∀ v : Fin 3 → K, (A : Matrix (Fin 3) (Fin 3) K).mulVec v ∈ coordinateSpace S ↔
          v ∈ coordinateSpace S) ↔
        ∀ v : Fin 3 → K, (A : Matrix (Fin 3) (Fin 3) K).mulVec v ∈ flagSpace 3 K i ↔
          v ∈ flagSpace 3 K i) := by
    intro S i hS
    subst hS
    simp only [burnsideF4d_Y1_coordinateSpace_flag]
  cases b
  · exact key _ 1 (by ext p; simp [flagOne] <;> omega)
  · exact key _ 2 (by ext p; simp [flagTwo] <;> omega)

noncomputable def burnsideF429a_L3_Psi {f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .L3 2 f H) : projectiveSL 3 marking.field ≃* H :=
  (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 marking.field).trans
    marking.identification

private theorem burnsideF429a_L3_Psi_proj {f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .L3 2 f H)
    (A : Matrix.SpecialLinearGroup (Fin 3) marking.field) :
    burnsideF429a_L3_Psi marking (proj 3 marking.field A) =
      marking.transport
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 marking.field A) :=
  rfl

theorem burnsideF429a_L3_parabolic {f : ℕ} {H : Type} [Group H]
    (marking : ClassicalRoots.Marking .L3 2 f H) (b : Bool) :
    marking.parabolic b = ((Q3 marking.field (if b then 1 else 0)).map (proj 3 marking.field)).map
      (burnsideF429a_L3_Psi marking).toMonoidHom := by
  have hbasis : marking.basis = 1 := marking.basis_compatible
  have key := burnsideF429a_L3_comap_nativeParabolic (2 ^ f) marking.field marking.basis hbasis b
  have hsurj :=
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 marking.field).surjective
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨A, rfl⟩ := hsurj z
    refine ⟨proj 3 marking.field A, ⟨A, ?_, rfl⟩, burnsideF429a_L3_Psi_proj marking A⟩
    rw [← key]
    exact hz
  · rintro ⟨y, ⟨A, hA, rfl⟩, rfl⟩
    rw [← key] at hA
    exact ⟨_, hA, (burnsideF429a_L3_Psi_proj marking A).symm⟩

theorem burnsideF429a_L3_pkg {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∧
        pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂)) ∧
      oPPrime 2 (Gp ⊓ M₁) = perfectCore (Gp ⊓ M₁) ∧
        oPPrime 2 (Gp ⊓ M₂) = perfectCore (Gp ⊓ M₂) := by
  haveI := hyp.finite
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .L3) hyp.toHypF_4_4g
  have hK : Nat.card marking.field = 2 ^ f := by simpa using marking.field_card
  haveI : CharP marking.field 2 := burnsideF4gSp_charP_of_card hK
  have hpkg := CFSG.Quasithin.Rk2.rank2PkgExt_proj3 hK hf
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := marking.field) 2 (n := 3) (by norm_num)
  have hU : ChF.IsSylowOf 2 (projUnitriangular 3 marking.field) ⊤ := by
    rw [← hP]
    exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have e0 := burnsideF429a_L3_parabolic marking false
  have e1 := burnsideF429a_L3_parabolic marking true
  simp only [Bool.false_eq_true, if_false, if_true] at e0 e1
  exact burnsideF429a_of_model₂ (burnsideF429a_L3_Psi marking) (h1.trans e0) (h2.trans e1) hU
    (hpkg.le_perfectCore 0) (hpkg.le_perfectCore 1)

theorem burnsideF429a_c3_L3 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∧
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂) :=
  (burnsideF429a_L3_pkg hyp hf).1

end L3

section U5

open CFSG.ClassicalGroups.UnitaryFlag CFSG.Quasithin.H13.Sec53F.Unit

theorem burnsideF429a_U5_pkg {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∧
        pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂)) ∧
      oPPrime 2 (Gp ⊓ M₁) = perfectCore (Gp ⊓ M₁) ∧
        oPPrime 2 (Gp ⊓ M₂) = perfectCore (Gp ⊓ M₂) := by
  haveI := hyp.finite
  obtain ⟨marking, h1, h2⟩ := burnsideF4g_marking (c := .U5) hyp.toHypF_4_4g
  obtain ⟨Ψ, e1, e2⟩ := burnsideF429a_U5_equiv marking
  exact burnsideF429a_of_model₂ Ψ (h1.trans e1) (h2.trans e2) (u5_sylow _)
    (U_le_perfectCore_u5PtP hf) (U_le_perfectCore_u5LnP hf)

theorem burnsideF429a_c3_U5 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∧
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂) :=
  (burnsideF429a_U5_pkg hyp hf).1

end U5

section Classical

theorem burnsideF429a_c3_sbar_classical {κ : GLKind}
    (hκ : κ = .L3 ∨ κ = .Sp4 ∨ κ = .U4 ∨ κ = .U5) {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₁) ∧
      pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ perfectCore (Gp ⊓ M₂) := by
  rcases hκ with rfl | rfl | rfl | rfl
  · exact burnsideF429a_c3_L3 hyp hf
  · exact burnsideF429a_c3_Sp4 hyp hf
  · exact burnsideF429a_c3_U4 hyp hf
  · exact burnsideF429a_c3_U5 hyp hf

end Classical

end CFSG.ASVolI
