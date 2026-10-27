module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo

public section

namespace CFSG.Timmesfeld.RankTwo

open Matrix CFSG.SectionRank.EvenCover CFSG.LieType.Steinberg

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂] {k : Type*} [Field k]

@[expose] def rankOneRelsProd (R₁ : RankOneRels G₁ k) (R₂ : RankOneRels G₂ k) :
    RankOneRels (G₁ × G₂) k where
  x a := (R₁.x a, R₂.x a)
  y a := (R₁.y a, R₂.y a)
  x_add a b := Prod.ext (R₁.x_add a b) (R₂.x_add a b)
  y_add a b := Prod.ext (R₁.y_add a b) (R₂.y_add a b)
  conj_x t ht a := Prod.ext (by simpa using R₁.conj_x t ht a) (by simpa using R₂.conj_x t ht a)

theorem exists_hom_of_rankOneRels {k : Type} [Field k] [Finite k] (R : RankOneRels G₂ k) :
    ∃ Θ : SpecialLinearGroup (Fin 2) k →* G₂,
      (∀ a, Θ (sl2Upper a) = R.x a) ∧ ∀ a, Θ (sl2Lower a) = R.y a := by
  set P := rankOneRelsProd (sl2Rels k) R with hP
  have hinj : Set.InjOn (MonoidHom.fst (M := SpecialLinearGroup (Fin 2) k) (N := G₂)) P.sub :=
    P.injOn_sub (MonoidHom.fst _ _) (MonoidHom.id _) Function.injective_id (fun _ => rfl)
      (fun _ => rfl)
  have hmap : P.sub.map (MonoidHom.fst _ _) = ⊤ := by
    rw [RankOneRels.sub, MonoidHom.map_closure, ← sl2Rels_sub, RankOneRels.sub, Set.image_union]
    congr 2
    · ext g
      simp [P, rankOneRelsProd, sl2Rels_x]
    · ext g
      simp [P, rankOneRelsProd, sl2Rels_y]
  let f : P.sub →* SpecialLinearGroup (Fin 2) k := (MonoidHom.fst _ _).comp P.sub.subtype
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => Subtype.ext (hinj a.2 b.2 hab), fun g => ?_⟩
    have hg : g ∈ P.sub.map (MonoidHom.fst _ _) := by rw [hmap]; exact Subgroup.mem_top g
    obtain ⟨p, hp, rfl⟩ := hg
    exact ⟨⟨p, hp⟩, rfl⟩
  let e := MulEquiv.ofBijective f hf
  refine ⟨(MonoidHom.snd _ _).comp (P.sub.subtype.comp e.symm.toMonoidHom), fun a => ?_,
    fun a => ?_⟩
  · have hx : e.symm (sl2Upper a) = ⟨P.x a, P.x_mem_sub a⟩ :=
      e.symm_apply_eq.2 (Subtype.ext rfl)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx]
    rfl
  · have hy : e.symm (sl2Lower a) = ⟨P.y a, P.y_mem_sub a⟩ :=
      e.symm_apply_eq.2 (Subtype.ext rfl)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hy]
    rfl

end CFSG.Timmesfeld.RankTwo
