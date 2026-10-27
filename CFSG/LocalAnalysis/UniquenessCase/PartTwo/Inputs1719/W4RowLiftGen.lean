module

public import CFSG.Quasithin.Background.SmithB45ExcHSRuLift
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Engine
import CFSG.Quasithin.Background.SmithB42Disp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.Quasithin.B45Exc.HSRu CFSG.QuasithinUnique.Bridge.J2Excl

variable {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} {G : Type*} [Group G]
  {R P : Subgroup G}

theorem index_fixV_le_pow_of_genSet (ψ : Lift L Y R P) {t : MulAut W} (ht : t ∈ Y) {k : ℕ}
    (hgen : GenSet P k {((ψ.hom ⟨t, Subgroup.mem_sup_right ht⟩ : ↥R) : G)}) :
    (fixV L).index ≤ (fixV (Subgroup.zpowers t)).index ^ k := by
  classical
  obtain ⟨gs, hlen, hgsP, hle⟩ := hgen
  have hle' : P ≤ Subgroup.closure (CFSG.QuasithinUnique.Setup.X1.conjSet gs
      {ψ.toG ⟨t, Subgroup.mem_sup_right ht⟩}) := by
    simpa only [Lift.toG_apply] using hle
  have hpre : ∀ c : {c // c ∈ gs}, ∃ x : ↥(L ⊔ Y),
      (x : MulAut W) ∈ L ∧ ψ.toG x = c.1 := by
    intro c
    obtain ⟨x, hxL, hx⟩ := ψ.surj c.1 (hgsP c.1 c.2)
    exact ⟨x, hxL, by rwa [Lift.toG_apply]⟩
  choose x _ hx using hpre
  let xs : List ↥(L ⊔ Y) := gs.attach.map x
  let S : Set ↥(L ⊔ Y) := {y | ∃ h ∈ xs, y = h * ⟨t, Subgroup.mem_sup_right ht⟩ * h⁻¹}
  have hS : S.image ψ.toG =
      CFSG.QuasithinUnique.Setup.X1.conjSet gs {ψ.toG ⟨t, Subgroup.mem_sup_right ht⟩} := by
    ext y
    constructor
    · rintro ⟨a, ⟨h, hh, rfl⟩, rfl⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hh
      exact ⟨c.1, c.2, _, rfl, by simp only [map_mul, map_inv, hx]⟩
    · rintro ⟨c, hc, u, hu, rfl⟩
      rw [Set.mem_singleton_iff] at hu
      subst hu
      exact ⟨x ⟨c, hc⟩ * ⟨t, Subgroup.mem_sup_right ht⟩ * (x ⟨c, hc⟩)⁻¹,
        ⟨x ⟨c, hc⟩, List.mem_map_of_mem (List.mem_attach gs ⟨c, hc⟩), rfl⟩, by
          simp only [map_mul, map_inv, hx]⟩
  have hPle : P ≤ (Subgroup.closure S).map ψ.toG := by
    rw [MonoidHom.map_closure, hS]
    exact hle'
  set hs : List (MulAut W) := xs.map (fun h : ↥(L ⊔ Y) => (h : MulAut W)) with hhs
  have hgen_le : L ≤ Subgroup.closure {y : MulAut W | ∃ h ∈ hs, y = h * t * h⁻¹} := by
    intro l hl
    have hlP : ψ.toG ⟨l, Subgroup.mem_sup_left hl⟩ ∈ P := by
      rw [Lift.toG_apply]
      exact (ψ.mem_iff _).2 hl
    have hlS := (Subgroup.mem_map_iff_mem ψ.toG_injective).1 (hPle hlP)
    have h1 : l ∈ (Subgroup.closure S).map (L ⊔ Y).subtype := ⟨_, hlS, rfl⟩
    rw [MonoidHom.map_closure, Subgroup.coe_subtype] at h1
    refine Subgroup.closure_mono ?_ h1
    rintro y ⟨a, ha, rfl⟩
    obtain ⟨h, hh, rfl⟩ := ha
    have hmem : (h : MulAut W) ∈ xs.map (fun h : ↥(L ⊔ Y) => (h : MulAut W)) :=
      List.mem_map_of_mem (f := fun h : ↥(L ⊔ Y) => (h : MulAut W)) hh
    exact ⟨(h : MulAut W), by rwa [hhs], by simp⟩
  have hlen' : hs.length = k := by
    simp [hhs, xs, hlen]
  calc (fixV L).index
      ≤ (fixV (Subgroup.closure {y : MulAut W | ∃ h ∈ hs, y = h * t * h⁻¹})).index :=
        CFSG.QuasithinUnique.Setup.X5.index_fixV_antitone hgen_le
    _ ≤ (fixV (Subgroup.zpowers t)).index ^ hs.length :=
        CFSG.Quasithin.B42Disp.index_fixV_closure_conj_elt_le t hs
    _ = (fixV (Subgroup.zpowers t)).index ^ k := by rw [hlen']

omit [Finite W] in
theorem le_closure_centralizer_of_lift (ψ : Lift L Y R P) {d e : MulAut W} (hd : d ∈ Y)
    (he : e ∈ Y)
    (hgen : P ≤ Subgroup.closure
      (((P ⊓ Subgroup.centralizer {((ψ.hom ⟨d, Subgroup.mem_sup_right hd⟩ : ↥R) : G)} :
        Subgroup G) : Set G) ∪
        (P ⊓ Subgroup.centralizer {((ψ.hom ⟨e, Subgroup.mem_sup_right he⟩ : ↥R) : G)} :
          Subgroup G))) :
    L ≤ Subgroup.closure (((Subgroup.centralizer {d} : Subgroup (MulAut W)) : Set (MulAut W)) ∪
      (Subgroup.centralizer {e} : Subgroup (MulAut W))) := by
  classical
  have hcent : ∀ (u : MulAut W) (hu : u ∈ Y) (x' : ↥(L ⊔ Y)),
      ψ.toG x' ∈ Subgroup.centralizer {ψ.toG (⟨u, Subgroup.mem_sup_right hu⟩ : ↥(L ⊔ Y))} →
      (x' : MulAut W) ∈ Subgroup.centralizer {u} := by
    intro u hu x' hx'
    rw [Subgroup.mem_centralizer_singleton_iff] at hx' ⊢
    have h1 : ψ.toG (x' * ⟨u, Subgroup.mem_sup_right hu⟩) =
        ψ.toG (⟨u, Subgroup.mem_sup_right hu⟩ * x') := by
      rw [map_mul, map_mul]
      exact hx'
    simpa using congrArg (fun z : ↥(L ⊔ Y) => (z : MulAut W)) (ψ.eq_of_hom_eq h1)
  let S : Set ↥(L ⊔ Y) := {x | (x : MulAut W) ∈
    ((Subgroup.centralizer {d} : Subgroup (MulAut W)) : Set (MulAut W)) ∪
      (Subgroup.centralizer {e} : Subgroup (MulAut W))}
  have hA : ((P ⊓ Subgroup.centralizer {((ψ.hom ⟨d, Subgroup.mem_sup_right hd⟩ : ↥R) : G)} :
      Subgroup G) : Set G) ⊆ (Subgroup.closure S).map ψ.toG := by
    rintro x ⟨hxP, hxC⟩
    obtain ⟨x', _, hx'⟩ := ψ.surj x hxP
    have hx'T : ψ.toG x' = x := by rwa [Lift.toG_apply]
    refine ⟨x', Subgroup.subset_closure (Or.inl ?_), hx'T⟩
    refine hcent d hd x' ?_
    rw [hx'T, Lift.toG_apply]
    exact hxC
  have hB : ((P ⊓ Subgroup.centralizer {((ψ.hom ⟨e, Subgroup.mem_sup_right he⟩ : ↥R) : G)} :
      Subgroup G) : Set G) ⊆ (Subgroup.closure S).map ψ.toG := by
    rintro x ⟨hxP, hxC⟩
    obtain ⟨x', _, hx'⟩ := ψ.surj x hxP
    have hx'T : ψ.toG x' = x := by rwa [Lift.toG_apply]
    refine ⟨x', Subgroup.subset_closure (Or.inr ?_), hx'T⟩
    refine hcent e he x' ?_
    rw [hx'T, Lift.toG_apply]
    exact hxC
  have hPle : P ≤ (Subgroup.closure S).map ψ.toG := by
    refine hgen.trans ((Subgroup.closure_le _).2 ?_)
    rintro x (hx | hx)
    · exact hA hx
    · exact hB hx
  intro l hl
  have hlP : ψ.toG ⟨l, Subgroup.mem_sup_left hl⟩ ∈ P := by
    rw [Lift.toG_apply]
    exact (ψ.mem_iff _).2 hl
  have hlS := (Subgroup.mem_map_iff_mem ψ.toG_injective).1 (hPle hlP)
  have h1 : l ∈ (Subgroup.closure S).map (L ⊔ Y).subtype := ⟨_, hlS, rfl⟩
  rw [MonoidHom.map_closure, Subgroup.coe_subtype] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro y ⟨a, ha, rfl⟩
  exact ha

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
