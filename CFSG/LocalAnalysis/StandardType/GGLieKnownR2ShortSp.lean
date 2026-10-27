module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortTransport
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSpNorm
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSpGen
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSpRad
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSp

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.BorelTits CFSG.QuasithinUnique.B113Lie.Sp CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Matrix

theorem shortCores_Sp {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {β : Fin (Symplectic.rootDatum n F).rank → ℤ} (hβ : β ∈ (Symplectic.rootDatum n F).roots)
    (hs : ¬ GGLongRoot (Symplectic.rootDatum n F) β) (u : ↥(StatedSp n F))
    {Rr Rm Q : Subgroup ↥(StatedSp n F)}
    (hRr : Rr = ((Symplectic.rootDatum n F).rootGroup β).map (MulAut.conj u).toMonoidHom)
    (hRm : Rm = ((Symplectic.rootDatum n F).rootGroup (-β)).map (MulAut.conj u).toMonoidHom)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set ↥(StatedSp n F)))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ ∧ ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set ↥(StatedSp n F)) := by
  obtain ⟨a₁, a₂, b₁, b₂, h1, h2, ⟨h3, h4, h5, h6⟩, hA, hB⟩ :=
    Geo.exists_altSiegelGroup_eq_conj_rootGroup_Sp n F hβ hs u
  have hpp : SpPlanePair n F a₁ a₂ b₁ b₂ := ⟨h1, h2, h3, h4, h5, h6⟩
  have s1 : a₁ ⬝ᵥ (spJ n F *ᵥ a₁) = 0 := spForm_self n F a₁
  have s2 : a₂ ⬝ᵥ (spJ n F *ᵥ a₂) = 0 := spForm_self n F a₂
  have s12 : a₁ ⬝ᵥ (spJ n F *ᵥ a₂) = 0 := h3
  have s21 : a₂ ⬝ᵥ (spJ n F *ᵥ a₁) = 0 := (spForm n F).refl a₁ a₂ s12
  have hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂}) := by
    intro x hx y hy
    obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨d₁, d₂, rfl⟩ := Submodule.mem_span_pair.mp hy
    simp only [spForm_β, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, s1, s2, s12, s21]
    ring
  have hRr' : Rr = spAltSiegel n F a₁ a₂ := by
    rw [hRr, ← Subgroup.comap_map_eq_self_of_injective (StatedSp n F).subtype_injective
      (((Symplectic.rootDatum n F).rootGroup β).map (MulAut.conj u).toMonoidHom), hA]
    rfl
  have hRm' : Rm = spAltSiegel n F b₁ b₂ := by
    rw [hRm, ← Subgroup.comap_map_eq_self_of_injective (StatedSp n F).subtype_injective
      (((Symplectic.rootDatum n F).rootGroup (-β)).map (MulAut.conj u).toMonoidHom), hB]
    rfl
  have hN : Subgroup.normalizer (Rr : Set ↥(StatedSp n F)) =
      SymplecticFlag.stabilizer n F (Submodule.span F {a₁, a₂}) := by
    rw [hRr']
    exact normalizer_spAltSiegel_eq_stabilizer hpp
  have hQ' : Q = sprad (Submodule.span F {a₁, a₂}) hW := by
    rw [hQ, hN]
    refine le_antisymm (pCoreOf_stabilizer_le_sprad hpp) ?_
    refine GGRootNorm.le_pCoreOf_of_normalized sprad_le_stabilizer
      (rad_isPGroup (isIsometric_natRep_statedSp n F) (natRep_injective _) 2 hW) ?_
    intro m hm t ht
    exact (Subgroup.mem_normalizer_iff.mp (stabilizer_le_normalizer_sprad hm) t).mp ht
  refine ⟨?_, ?_, ?_⟩
  · rw [hQ', hRr', hRm']
    exact sprad_sup_spAltSiegel_eq_top hpp
  · rw [hQ', hRr']
    exact commutator_sprad_le_spAltSiegel hpp
  · rw [hQ', hRr']
    exact sprad_le_centralizer_spAltSiegel hpp

theorem rootGroup_isPGroup_PSp
    {n f : ℕ}
    {β : Fin (ggU .PSp n f).D.rank → ℤ} (hβ : β ∈ (ggU .PSp n f).D.roots)
    (u : (ggU .PSp n f).K) {Rr : Subgroup (ggU .PSp n f).K}
    (hRr : Rr = ggRootSub (ggU .PSp n f).D (MonoidHom.id (ggU .PSp n f).K) β u) :
    IsPGroup 2 Rr := by
  subst hRr
  have h : IsPGroup 2 ((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup β) :=
    GGRootSp.isPGroup_rootGroup hβ
  exact (h.map (MulAut.conj u).toMonoidHom).map (MonoidHom.id _)

theorem coreOne_PSp
    {n f : ℕ}
    {β : Fin (ggU .PSp n f).D.rank → ℤ} (hβ : β ∈ (ggU .PSp n f).D.roots)
    (hs : ¬ GGLongRoot (ggU .PSp n f).D β)
    (u : (ggU .PSp n f).K) {Rr Rm Q : Subgroup (ggU .PSp n f).K}
    (hRr : Rr = ggRootSub (ggU .PSp n f).D (MonoidHom.id (ggU .PSp n f).K) β u)
    (hRm : Rm = ggRootSub (ggU .PSp n f).D (MonoidHom.id (ggU .PSp n f).K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .PSp n f).K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  exact (shortCores_Sp (F := GaloisField 2 f) hβ hs u (hRr.trans (Subgroup.map_id _))
    (hRm.trans (Subgroup.map_id _)) hQ).1

theorem coreFour_PSp
    {n f : ℕ}
    {β : Fin (ggU .PSp n f).D.rank → ℤ} (hβ : β ∈ (ggU .PSp n f).D.roots)
    (hs : ¬ GGLongRoot (ggU .PSp n f).D β)
    (u : (ggU .PSp n f).K) {Rr Rm Q : Subgroup (ggU .PSp n f).K}
    (hRr : Rr = ggRootSub (ggU .PSp n f).D (MonoidHom.id (ggU .PSp n f).K) β u)
    (hRm : Rm = ggRootSub (ggU .PSp n f).D (MonoidHom.id (ggU .PSp n f).K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .PSp n f).K))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set (ggU .PSp n f).K) := by
  exact (shortCores_Sp (F := GaloisField 2 f) hβ hs u (hRr.trans (Subgroup.map_id _))
    (hRm.trans (Subgroup.map_id _)) hQ).2

theorem itemOne_PSp
    {n f : ℕ}
    {X : Type} [Group X] [Finite X] (ψ : (ggU .PSp n f).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (ggU .PSp n f).K) (hodd : Odd (Nat.card ψ.ker))
    {β : Fin (ggU .PSp n f).D.rank → ℤ} (hβ : β ∈ (ggU .PSp n f).D.roots)
    (hs : ¬ GGLongRoot (ggU .PSp n f).D β)
    (u : (ggU .PSp n f).K) {R Rm Q : Subgroup X}
    (hR : R = ggRootSub (ggU .PSp n f).D ψ β u)
    (hRm : Rm = ggRootSub (ggU .PSp n f).D ψ (-β) u)
    (hQ : Q = pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X))) :
    Q ⊔ (R ⊔ Rm) = ψ.range := by
  obtain rfl : R = (ggRootSub (ggU .PSp n f).D (MonoidHom.id (ggU .PSp n f).K) β u).map ψ :=
    hR.trans (ggRootSub_eq_map _ _ _ _)
  obtain rfl : Rm = (ggRootSub (ggU .PSp n f).D (MonoidHom.id (ggU .PSp n f).K) (-β) u).map ψ :=
    hRm.trans (ggRootSub_eq_map _ _ _ _)
  subst hQ
  exact itemOne_of_core hker hodd (rootGroup_isPGroup_PSp hβ u rfl)
    (coreOne_PSp hβ hs u rfl rfl rfl)

theorem itemFour_PSp
    {n f : ℕ}
    {X : Type} [Group X] [Finite X] (ψ : (ggU .PSp n f).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (ggU .PSp n f).K) (hodd : Odd (Nat.card ψ.ker))
    {β : Fin (ggU .PSp n f).D.rank → ℤ} (hβ : β ∈ (ggU .PSp n f).D.roots)
    (hs : ¬ GGLongRoot (ggU .PSp n f).D β)
    (u : (ggU .PSp n f).K) {R Rm Q : Subgroup X}
    (hR : R = ggRootSub (ggU .PSp n f).D ψ β u)
    (hRm : Rm = ggRootSub (ggU .PSp n f).D ψ (-β) u)
    (hQ : Q = pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X))) :
    ⁅Q, Q⁆ ≤ R ∧ Q ≤ Subgroup.centralizer (R : Set X) := by
  obtain rfl : R = (ggRootSub (ggU .PSp n f).D (MonoidHom.id (ggU .PSp n f).K) β u).map ψ :=
    hR.trans (ggRootSub_eq_map _ _ _ _)
  obtain rfl : Rm = (ggRootSub (ggU .PSp n f).D (MonoidHom.id (ggU .PSp n f).K) (-β) u).map ψ :=
    hRm.trans (ggRootSub_eq_map _ _ _ _)
  subst hQ
  exact itemFour_of_core hker hodd (rootGroup_isPGroup_PSp hβ u rfl)
    (coreFour_PSp hβ hs u rfl rfl rfl).1 (coreFour_PSp hβ hs u rfl rfl rfl).2

end CFSG.StandardType.LieKnownR2.Short
