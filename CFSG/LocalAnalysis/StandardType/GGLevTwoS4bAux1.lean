module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoRoots
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE

public section

namespace CFSG.StandardType.LevTwo

open CFSG CFSG.Assembly CFSG.LieType.RootSystem LevTwoType

structure levTwoS4b_Ctx (G : Type) [Group G] [Finite G] where
  T : LevTwoType
  hT : T.Valid
  p : ℕ
  Bs : Subgroup G
  hp : p.Prime
  hp2 : p ≠ 2
  hEl : IsElemAbelian p Bs
  hNT : GGNoTransvection p Bs
  A : Subgroup (MulAut ↥Bs)
  hA : A ≤ ggInduced ⊤ Bs
  ρ : Wg T.rootFT ≃* ↥A
  hdict : ∀ a : MulAut ↥Bs, (a ∈ A ∧ GGIsReflection p a) ↔
      ∃ g ∈ Refl T.rootFT, ((ρ g : ↥A) : MulAut ↥Bs) = a
  AL : Subgroup (MulAut ↥Bs)
  ιL : Type
  fintype : Fintype ιL
  decEq : DecidableEq ιL
  ML : CoxeterMatrix ιL
  hAL : AL ≤ A
  hML : GGIsWeylMatrixAD ML ∨ GGIsWeylMatrixE ML
  hW : GGWeylOfType p ML AL

attribute [instance] levTwoS4b_Ctx.fintype levTwoS4b_Ctx.decEq

@[expose] def levTwoS4b_Phi {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) :
    Set (Fin c.T.n → ℤ) :=
  {β | IsRt c.T.rootFT β ∧ ((c.ρ (rRefl c.T.rootFT β) : ↥c.A) : MulAut ↥c.Bs) ∈ c.AL}

@[expose] noncomputable def levTwoS4b_eL {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) :
    c.ML.Group ≃* ↥c.AL :=
  Classical.choose c.hW

theorem levTwoS4b_eL_spec {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) (i : c.ιL) :
    GGIsReflection c.p (((levTwoS4b_eL c (c.ML.simple i) : ↥c.AL) : MulAut ↥c.Bs)) :=
  Classical.choose_spec c.hW i

theorem levTwoS4b_root_exists {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    (j : c.ιL) :
    ∃ β : Fin c.T.n → ℤ, IsRt c.T.rootFT β ∧
      ((c.ρ (rRefl c.T.rootFT β) : ↥c.A) : MulAut ↥c.Bs) =
        ((levTwoS4b_eL c (c.ML.simple j) : ↥c.AL) : MulAut ↥c.Bs) := by
  have ha : ((levTwoS4b_eL c (c.ML.simple j) : ↥c.AL) : MulAut ↥c.Bs) ∈ c.A :=
    c.hAL (levTwoS4b_eL c (c.ML.simple j)).2
  have hrefl : GGIsReflection c.p
      (((levTwoS4b_eL c (c.ML.simple j) : ↥c.AL) : MulAut ↥c.Bs)) :=
    levTwoS4b_eL_spec c j
  obtain ⟨g, hg, hgρ⟩ := (c.hdict _).1 ⟨ha, hrefl⟩
  obtain ⟨β, hβ, rfl⟩ := (mem_Refl_iff c.T.rootFT).1 hg
  exact ⟨β, hβ, hgρ⟩

@[expose] noncomputable def levTwoS4b_beta {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    (j : c.ιL) : Fin c.T.n → ℤ :=
  Classical.choose (levTwoS4b_root_exists c j)

theorem levTwoS4b_beta_isRt {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) (j : c.ιL) :
    IsRt c.T.rootFT (levTwoS4b_beta c j) :=
  (Classical.choose_spec (levTwoS4b_root_exists c j)).1

theorem levTwoS4b_beta_rho {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) (j : c.ιL) :
    ((c.ρ (rRefl c.T.rootFT (levTwoS4b_beta c j)) : ↥c.A) : MulAut ↥c.Bs) =
      ((levTwoS4b_eL c (c.ML.simple j) : ↥c.AL) : MulAut ↥c.Bs) :=
  (Classical.choose_spec (levTwoS4b_root_exists c j)).2

theorem levTwoS4b_beta_mem {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) (j : c.ιL) :
    levTwoS4b_beta c j ∈ levTwoS4b_Phi c :=
  ⟨levTwoS4b_beta_isRt c j,
    by rw [levTwoS4b_beta_rho c j]; exact (levTwoS4b_eL c (c.ML.simple j)).2⟩

@[expose] noncomputable def levTwoS4b_w {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) (j : c.ιL) :
    Wg c.T.rootFT :=
  Classical.choose (levTwoS4b_beta_isRt c j)

@[expose] noncomputable def levTwoS4b_i {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) (j : c.ιL) :
    Fin c.T.n :=
  Classical.choose (Classical.choose_spec (levTwoS4b_beta_isRt c j))

theorem levTwoS4b_beta_eq_weylAction {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G)
    (j : c.ιL) :
    weylAction c.T.rootFT (levTwoS4b_w c j) (Pi.single (levTwoS4b_i c j) 1) =
      levTwoS4b_beta c j :=
  Classical.choose_spec (Classical.choose_spec (levTwoS4b_beta_isRt c j))

theorem levTwoS4b_rRefl_eq {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) (j : c.ιL) :
    rRefl c.T.rootFT (levTwoS4b_beta c j) =
      levTwoS4b_w c j * sg c.T.rootFT (levTwoS4b_i c j) * (levTwoS4b_w c j)⁻¹ :=
  rRefl_eq_conj c.T.rootFT (levTwoS4b_beta_eq_weylAction c j)

theorem levTwoS4b_beta_injective {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) :
    Function.Injective (levTwoS4b_beta c) := by
  intro j k hjk
  have h1 : levTwoS4b_eL c (c.ML.simple j) = levTwoS4b_eL c (c.ML.simple k) := by
    apply Subtype.ext
    have hj := levTwoS4b_beta_rho c j
    have hk := levTwoS4b_beta_rho c k
    rw [hjk] at hj
    exact hj.symm.trans hk
  exact CoxeterSystem.simple_injective c.ML.toCoxeterSystem
    (by simpa only [CoxeterMatrix.toCoxeterSystem_simple] using (levTwoS4b_eL c).injective h1)

theorem levTwoS4b_card {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) :
    3 ≤ Fintype.card c.ιL := by
  rcases c.hML with hAD | hE
  · rcases hAD with ⟨n, e, hn, -⟩ | ⟨n, e, hn, -⟩
    · rw [Fintype.card_congr e.symm]; simpa using hn
    · rw [Fintype.card_congr e.symm, Fintype.card_fin]; omega
  · rcases hE with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · rw [Fintype.card_congr e.symm]; simp
    · rw [Fintype.card_congr e.symm]; simp
    · rw [Fintype.card_congr e.symm]; simp

theorem levTwoS4b_isWeylMatrix {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) :
    GGIsWeylMatrix c.ML :=
  c.hML.elim GGIsWeylMatrixAD.isWeylMatrix GGIsWeylMatrixE.isWeylMatrix

theorem levTwoS4b_le_three {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) (i j : c.ιL)
    (hij : i ≠ j) : c.ML.M i j ≤ 3 :=
  c.hML.elim (fun h => GGIsWeylMatrixAD.le_three h i j hij)
    (fun h => GGIsWeylMatrixE.le_three h i j hij)

theorem levTwoS4b_wsub {G : Type} [Group G] [Finite G] (c : levTwoS4b_Ctx G) :
    (Wsub c.T.rootFT (levTwoS4b_Phi c)).map (c.A.subtype.comp c.ρ.toMonoidHom) = c.AL := by
  apply le_antisymm
  · rw [Wsub, MonoidHom.map_closure]
    rw [Subgroup.closure_le]
    rintro x ⟨y, ⟨β, hβ, rfl⟩, rfl⟩
    change ((c.ρ (rRefl c.T.rootFT β) : ↥c.A) : MulAut ↥c.Bs) ∈ c.AL
    exact hβ.2
  · have hgen : (⊤ : Subgroup c.ML.Group) = Subgroup.closure (Set.range c.ML.simple) := by
      rw [← CoxeterSystem.subgroup_closure_range_simple c.ML.toCoxeterSystem,
        CoxeterMatrix.toCoxeterSystem_simple]
    have hrange : (c.AL.subtype.comp (levTwoS4b_eL c).toMonoidHom).range = c.AL := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact (levTwoS4b_eL c y).2
      · intro hx
        obtain ⟨y, hy⟩ := (levTwoS4b_eL c).surjective ⟨x, hx⟩
        exact ⟨y, by simpa using congrArg Subtype.val hy⟩
    have hmap : (⊤ : Subgroup c.ML.Group).map (c.AL.subtype.comp (levTwoS4b_eL c).toMonoidHom) =
        c.AL := by
      rw [Subgroup.map_top, hrange]
    calc c.AL = (⊤ : Subgroup c.ML.Group).map
            (c.AL.subtype.comp (levTwoS4b_eL c).toMonoidHom) := hmap.symm
      _ = (Subgroup.closure (Set.range c.ML.simple)).map
            (c.AL.subtype.comp (levTwoS4b_eL c).toMonoidHom) := by rw [← hgen]
      _ = Subgroup.closure ((c.AL.subtype.comp (levTwoS4b_eL c).toMonoidHom) ''
            Set.range c.ML.simple) := MonoidHom.map_closure _ _
      _ ≤ (Wsub c.T.rootFT (levTwoS4b_Phi c)).map
            (c.A.subtype.comp c.ρ.toMonoidHom) := by
          rw [Wsub, MonoidHom.map_closure]
          apply Subgroup.closure_mono
          rintro x ⟨j, ⟨⟨k, rfl⟩, rfl⟩⟩
          refine ⟨rRefl c.T.rootFT (levTwoS4b_beta c k),
            ⟨levTwoS4b_beta c k, levTwoS4b_beta_mem c k, rfl⟩, ?_⟩
          change ((c.ρ (rRefl c.T.rootFT (levTwoS4b_beta c k)) : ↥c.A) : MulAut ↥c.Bs) =
            ((levTwoS4b_eL c (c.ML.simple k) : ↥c.AL) : MulAut ↥c.Bs)
          exact levTwoS4b_beta_rho c k

end CFSG.StandardType.LevTwo
