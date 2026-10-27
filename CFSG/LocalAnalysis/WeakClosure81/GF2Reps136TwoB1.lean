module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136T
import CFSG.Quasithin.Background.ConjugateSectionAction

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W]

private theorem w1369_commutator_eq_self_of_isQuasisimple {G : Type*} [Group G]
    {L : Subgroup G} (h : CFSG.Open.IsQuasisimple ↥L) : ⁅L, L⁆ = L := by
  have h1 : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [h.1] at h1
  rw [← h1, Subgroup.map_top, Subgroup.range_subtype]

noncomputable abbrev Lc (L : Subgroup (MulAut W)) (g : MulAut W) : Subgroup (MulAut W) :=
  L.map (MulAut.conj g).toMonoidHom

structure Swap136 (Y : Subgroup (MulAut W)) (t : MulAut W) (L : Subgroup (MulAut W))
    (g : MulAut W) : Prop where
  ctx : Ctx136 Y t L
  hfix : ∀ I ∈ irrSet L, I.map t.toMonoidHom = I
  gY : g ∈ Y
  gN : g ∉ Subgroup.normalizer (L : Set (MulAut W))
  nontriv : commSub (Wd L) (Lc L g) ≠ ⊥

theorem swap_comp {Y : Subgroup (MulAut W)} {t : MulAut W} {L : Subgroup (MulAut W)}
    {g : MulAut W} (S : Swap136 Y t L g) :
    IsComponentOf (Lc L g) Y ∧ Lc L g ≠ L ∧ ⁅Lc L g, L⁆ = ⊥ ∧ ⁅Lc L g, Lc L g⁆ = Lc L g ∧
      Lc L g ≤ Y := by
  have hne : Lc L g ≠ L := by
    intro h
    exact S.gN ((Subgroup.mem_normalizer_iff_map_conj_eq).mpr h)
  have hcomp : IsComponentOf (Lc L g) Y :=
    CFSG.LargeExtraspecial.S5.isComponentOf_map_conj S.ctx.comp S.gY
  exact ⟨hcomp, hne,
    CFSG.LargeExtraspecial.S5.commute_of_isComponentOf_ne hcomp S.ctx.comp hne,
    w1369_commutator_eq_self_of_isQuasisimple hcomp.2.2, hcomp.1⟩

theorem swap_nontriv (hw2 : ∀ w : W, w * w = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} {g : MulAut W} (S : Swap136 Y t L g) :
    ¬ ∀ x ∈ Lc L g, ∀ u ∈ Wd L, x u * u⁻¹ ∈ Cd L := by
  intro h
  have hCd : Cd L ≤ fixV L := inf_le_right
  have hfix : commSub (Wd L) (Lc L g) ≤ fixV L := by
    rw [commSub, Subgroup.closure_le]
    rintro v ⟨x, hx, u, hu, rfl⟩
    exact hCd (h x hx u hu)
  have hLR : ⁅L, Lc L g⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact (swap_comp S).2.2.1
  have hbot := lemmaT hw2 (w1369_commutator_eq_self_of_isQuasisimple S.ctx.comp.2.2)
    (swap_comp S).2.2.2.1 hLR hfix
  exact S.nontriv hbot

theorem swap_ctx (hw2 : ∀ w : W, w ^ 2 = 1) {Y : Subgroup (MulAut W)} {t : MulAut W}
    {L : Subgroup (MulAut W)} {g : MulAut W} (S : Swap136 Y t L g) :
    Ctx136 Y (g * t * g⁻¹) (Lc L g) ∧
      ∀ I ∈ irrSet (Lc L g), I.map (g * t * g⁻¹).toMonoidHom = I := by
  have hzt : Subgroup.zpowers (g * t * g⁻¹) =
      (Subgroup.zpowers t).map (MulAut.conj g).toMonoidHom := by
    simpa [MulAut.conj_apply] using
      (MonoidHom.map_zpowers (MulAut.conj g).toMonoidHom t).symm
  have htY : g * t * g⁻¹ ∈ Y :=
    Y.mul_mem (Y.mul_mem S.gY S.ctx.std.tY) (Y.inv_mem S.gY)
  have ht2 : orderOf (g * t * g⁻¹) = 2 := by
    have hsem : SemiconjBy g t (g * t * g⁻¹) := by
      show g * t = (g * t * g⁻¹) * g
      simp [mul_assoc]
    exact (SemiconjBy.orderOf_eq g hsem).symm.trans S.ctx.std.t2
  have hcost : rk ↥(commSub ⊤ (Subgroup.zpowers (g * t * g⁻¹))) ≤ 3 := by
    have hZeq : commSub ⊤ (Subgroup.zpowers (g * t * g⁻¹)) =
        (commSub ⊤ (Subgroup.zpowers t)).map g.toMonoidHom := by
      rw [hzt]
      simpa using s15_Core_commSub_map_conj (⊤ : Subgroup W) (Subgroup.zpowers t) g
    rw [hZeq]
    have hcard : Nat.card ↥((commSub ⊤ (Subgroup.zpowers t)).map g.toMonoidHom) =
        Nat.card ↥(commSub ⊤ (Subgroup.zpowers t)) :=
      Subgroup.card_map_of_injective g.injective
    simpa only [rk, hcard] using S.ctx.std.cost
  have hlt : ⁅Lc L g, Subgroup.zpowers (g * t * g⁻¹)⁆ = Lc L g := by
    have h := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) S.ctx.Lt
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers] at h
    simpa [Lc, MulAut.conj_apply] using h
  have hF : ∀ p : ℕ, p.Prime → ⁅pCoreOf p Y, Subgroup.zpowers (g * t * g⁻¹)⁆ = ⊥ := by
    intro p hp
    have hpCoreInv : (pCoreOf p Y).map (MulAut.conj g).toMonoidHom = pCoreOf p Y := by
      simpa using (Subgroup.mem_normalizer_iff_map_conj_eq).mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p Y S.gY)
    have h := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) (S.ctx.hF p hp)
    rw [Subgroup.map_commutator, Subgroup.map_bot, MonoidHom.map_zpowers] at h
    rw [hpCoreInv] at h
    simpa [MulAut.conj_apply] using h
  have hfix : ∀ K : Subgroup (MulAut W), IsComponentOf K Y →
      K.map (MulAut.conj (g * t * g⁻¹)).toMonoidHom = K := by
    intro K hK
    have hKg : IsComponentOf (K.map (MulAut.conj g⁻¹).toMonoidHom) Y :=
      CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK (Y.inv_mem S.gY)
    have h := S.ctx.hfix _ hKg
    have h2 := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) h
    simp only [Subgroup.map_map] at h2
    have hgid : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id (MulAut W) := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [hgid, Subgroup.map_id] at h2
    have hcomp : (MulAut.conj (g * t * g⁻¹)).toMonoidHom =
        ((MulAut.conj g).toMonoidHom.comp (MulAut.conj t).toMonoidHom).comp
          (MulAut.conj g⁻¹).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp]
    exact h2
  refine ⟨?_, ?_⟩
  · refine ⟨?_, (swap_comp S).1, hlt, hF, hfix⟩
    exact ⟨S.ctx.std.isK, S.ctx.std.o2, S.ctx.std.basic, htY, ht2, hcost⟩
  · intro I hI
    have hRmap : (Lc L g).map (MulAut.conj g⁻¹).toMonoidHom = L := by
      rw [Lc, Subgroup.map_map]
      have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
          MonoidHom.id (MulAut W) := by
        ext x; simp [MulAut.conj_apply, mul_assoc]
      rw [this, Subgroup.map_id]
    have hJirr : I.map (g⁻¹).toMonoidHom ∈ irrSet L := by
      have h := CFSG.Quasithin.ConjugateSection.map_mem_irrSet_map_conj
        (H := Lc L g) (φ := g⁻¹) hI
      rwa [hRmap] at h
    have hJfix : (I.map (g⁻¹).toMonoidHom).map t.toMonoidHom = I.map (g⁻¹).toMonoidHom :=
      S.hfix _ hJirr
    have hJI : (I.map (g⁻¹).toMonoidHom).map g.toMonoidHom = I := by
      rw [Subgroup.map_map]
      have : g.toMonoidHom.comp (g⁻¹).toMonoidHom = MonoidHom.id W := by
        ext x; simp [MulAut.mul_apply, MulAut.apply_inv_self]
      rw [this, Subgroup.map_id]
    calc I.map (g * t * g⁻¹).toMonoidHom
        = ((I.map (g⁻¹).toMonoidHom).map g.toMonoidHom).map
            (g * t * g⁻¹).toMonoidHom := by
          rw [hJI]
      _ = (I.map (g⁻¹).toMonoidHom).map
            ((g * t * g⁻¹).toMonoidHom.comp g.toMonoidHom) := by
          rw [Subgroup.map_map]
      _ = (I.map (g⁻¹).toMonoidHom).map (g.toMonoidHom.comp t.toMonoidHom) := by
          congr 1
          ext x
          simp [MulAut.mul_apply, MulAut.inv_apply_self]
      _ = ((I.map (g⁻¹).toMonoidHom).map t.toMonoidHom).map g.toMonoidHom := by
          simp only [Subgroup.map_map, MonoidHom.comp_assoc]
      _ = (I.map (g⁻¹).toMonoidHom).map g.toMonoidHom := by rw [hJfix]
      _ = I := hJI

theorem swap_Wd (L : Subgroup (MulAut W)) (g : MulAut W) :
    Wd (Lc L g) = (Wd L).map g.toMonoidHom := by
  simpa [Wd, Lc] using s15_Core_commSub_map_conj (⊤ : Subgroup W) L g

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
