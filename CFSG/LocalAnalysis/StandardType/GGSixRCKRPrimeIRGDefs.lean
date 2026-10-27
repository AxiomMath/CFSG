module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRG

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem ggLongRoot_mem_roots {U : Type*} [Group U] {D : UniversalRootDatum U}
    {γ : Fin D.rank → ℤ} (h : GGLongRoot D γ) : γ ∈ D.roots := by
  obtain ⟨w, γ₀, hγ₀, -, rfl⟩ := h
  exact CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀ w

abbrev IRGQuot
    (t : StatedLieTag) (n g : ℕ) : Type :=
  (ggU t n g).K ⧸ Subgroup.center (ggU t n g).K

@[expose] def IRGGoodRoot
    (t : StatedLieTag) (n g : ℕ) (β : Fin (ggU t n g).D.rank → ℤ) : Prop :=
  β ∈ (ggU t n g).D.roots ∧ (GGLongRoot (ggU t n g).D β ∨
    (((t = .PSp ∧ n = 2) ∨ t = .F4) ∧ 2 • β ∉ (ggU t n g).D.roots))

@[expose] def IRGPairClass
    (t : StatedLieTag) (n g : ℕ) {G : Type} [Group G] (φ : (ggU t n g).K →* G)
    (R Rm : Subgroup G) : Prop :=
  ∃ β, IRGGoodRoot t n g β ∧ ∃ u : (ggU t n g).K,
    R = ggRootSub (ggU t n g).D φ β u ∧ Rm = ggRootSub (ggU t n g).D φ (-β) u

@[expose] def IRGRootPairAut
    (t : StatedLieTag) (n g : ℕ) : Prop :=
  ∀ θ : MulAut (IRGQuot t n g), ∀ β' : Fin (ggU t n g).D.rank → ℤ,
    β' ∈ (ggU t n g).D.roots → GGLongRoot (ggU t n g).D β' → ∀ u' : (ggU t n g).K,
      ∃ β, IRGGoodRoot t n g β ∧ ∃ u : (ggU t n g).K,
        (ggRootSub (ggU t n g).D (QuotientGroup.mk' (Subgroup.center (ggU t n g).K)) β' u').map
            θ.toMonoidHom =
          ggRootSub (ggU t n g).D (QuotientGroup.mk' (Subgroup.center (ggU t n g).K)) β u ∧
        (ggRootSub (ggU t n g).D (QuotientGroup.mk' (Subgroup.center (ggU t n g).K)) (-β') u').map
            θ.toMonoidHom =
          ggRootSub (ggU t n g).D (QuotientGroup.mk' (Subgroup.center (ggU t n g).K)) (-β) u

@[expose] def IRGIsoCompat
    {t' : StatedLieTag} {m g' : ℕ} {t : StatedLieTag} {n g : ℕ}
    (e : (ggU t' m g').K ≃* (ggU t n g).K) : Prop :=
  ∀ β' : Fin (ggU t' m g').D.rank → ℤ, β' ∈ (ggU t' m g').D.roots →
    GGLongRoot (ggU t' m g').D β' →
    ∃ γ, IRGGoodRoot t n g γ ∧ ∃ w : (ggU t n g).K,
      ((ggU t' m g').D.rootGroup β').map e.toMonoidHom =
          ((ggU t n g).D.rootGroup γ).map (MulAut.conj w).toMonoidHom ∧
      ((ggU t' m g').D.rootGroup (-β')).map e.toMonoidHom =
          ((ggU t n g).D.rootGroup (-γ)).map (MulAut.conj w).toMonoidHom

theorem irg_exists_aut_of_center_eq_bot
    {K : Type*} [Group K] (hZ : Subgroup.center K = ⊥)
    (θ : MulAut (K ⧸ Subgroup.center K)) :
    ∃ α : MulAut K, ∀ g : K,
      θ (QuotientGroup.mk' (Subgroup.center K) g) =
        QuotientGroup.mk' (Subgroup.center K) (α g) := by
  let e : K ⧸ Subgroup.center K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have he : ∀ x : K, e (QuotientGroup.mk' (Subgroup.center K) x) = x := fun _ => rfl
  have hs : ∀ x : K, e.symm x = QuotientGroup.mk' (Subgroup.center K) x := by
    intro x
    exact e.injective (by rw [MulEquiv.apply_symm_apply, he x])
  refine ⟨e.symm.trans (θ.trans e), fun g => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hs g]
  rw [← hs (e (θ (QuotientGroup.mk' (Subgroup.center K) g))),
    MulEquiv.symm_apply_apply]

theorem irg_map_conj_subgroup_mulAut
    {G Q : Type*} [Group G] [Group Q]
    (mk : G →* Q) (θ : MulAut Q) (α : MulAut G)
    (hα : ∀ g : G, θ (mk g) = mk (α g))
    {A B : Subgroup G} {t u : G}
    (h : A.map α.toMonoidHom = B.map (MulAut.conj t).toMonoidHom) :
    (((A.map (MulAut.conj u).toMonoidHom).map mk).map θ.toMonoidHom) =
      (B.map (MulAut.conj (α u * t)).toMonoidHom).map mk := by
  have hcomp : θ.toMonoidHom.comp mk = mk.comp α.toMonoidHom := MonoidHom.ext hα
  have hconj : α.toMonoidHom.comp (MulAut.conj u).toMonoidHom =
      (MulAut.conj (α u)).toMonoidHom.comp α.toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv, MulAut.coe_mul, Function.comp_apply]
  calc
    (((A.map (MulAut.conj u).toMonoidHom).map mk).map θ.toMonoidHom)
        = (A.map (MulAut.conj u).toMonoidHom).map (θ.toMonoidHom.comp mk) := by
          simp only [Subgroup.map_map, MonoidHom.comp_assoc]
    _ = (A.map (MulAut.conj u).toMonoidHom).map (mk.comp α.toMonoidHom) := by rw [hcomp]
    _ = ((A.map (MulAut.conj u).toMonoidHom).map α.toMonoidHom).map mk := by
          simp only [Subgroup.map_map, MonoidHom.comp_assoc]
    _ = (A.map (α.toMonoidHom.comp (MulAut.conj u).toMonoidHom)).map mk := by
          simp only [Subgroup.map_map, MonoidHom.comp_assoc]
    _ = (A.map ((MulAut.conj (α u)).toMonoidHom.comp α.toMonoidHom)).map mk := by rw [hconj]
    _ = ((A.map α.toMonoidHom).map (MulAut.conj (α u)).toMonoidHom).map mk := by
          simp only [Subgroup.map_map, MonoidHom.comp_assoc]
    _ = ((B.map (MulAut.conj t).toMonoidHom).map (MulAut.conj (α u)).toMonoidHom).map mk := by
          rw [h]
    _ = (B.map ((MulAut.conj (α u)).toMonoidHom.comp (MulAut.conj t).toMonoidHom)).map mk := by
          simp only [Subgroup.map_map, MonoidHom.comp_assoc]
    _ = (B.map (MulAut.conj (α u * t)).toMonoidHom).map mk := by
          have hfun : (MulAut.conj (α u)).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
              (MulAut.conj (α u * t)).toMonoidHom := by
            ext x
            simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
              map_inv, MulAut.coe_mul, Function.comp_apply]
          rw [hfun]

end CFSG.StandardType.RCKRP
