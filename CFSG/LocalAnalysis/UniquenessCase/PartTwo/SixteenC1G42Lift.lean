module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c1G_mem_normalizer_of_forall_actTil_mem_imgTil {V U : Subgroup G}
    (hV : IsElemAbelian 2 V) (hUV : U ≤ V) {g : G} (hgs : g ∈ stabTil ⊥ V)
    (hmap : ∀ w ∈ imgTil ⊥ V hV U, actTil ⊥ V hV ⟨g, hgs⟩ w ∈ imgTil ⊥ V hV U) :
    g ∈ normalizer (U : Set G) := by
  have hconj : ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro u hu
    have huV : u ∈ V := hUV hu
    have hw : mkTil ⊥ V hV (IntMod.mk hV ⟨u, huV⟩) ∈ imgTil ⊥ V hV U :=
      (mem_imgTil ⊥ V hV U _).2 ⟨IntMod.mk hV ⟨u, huV⟩, hu, rfl⟩
    have h1 := hmap _ hw
    rw [actTil_mk] at h1
    obtain ⟨y, hyU, hy⟩ := (mem_imgTil ⊥ V hV U _).1 h1
    have h2 := (mkTil_eq_iff ⊥ V hV y
      (actStab ⊥ V hV ⟨g, hgs⟩ (IntMod.mk hV ⟨u, huV⟩))).1 hy
    rw [actStab_apply_val, Subgroup.mem_bot, mul_inv_eq_one] at h2
    have h2' : y.val = g * u * g⁻¹ := by
      rwa [show (IntMod.mk hV ⟨u, huV⟩).val = u from rfl] at h2
    rw [← h2']
    exact hyU
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => hconj x hx
  · intro hx
    let c : ↥U → ↥U := fun u => ⟨g * (u : G) * g⁻¹, hconj u u.2⟩
    have hc : Function.Injective c := by
      intro a b hab
      apply Subtype.ext
      have h : g * (a : G) * g⁻¹ = g * (b : G) * g⁻¹ := congrArg Subtype.val hab
      exact mul_left_cancel (mul_right_cancel h)
    obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.1 hc) ⟨g * x * g⁻¹, hx⟩
    have h2 : (w : G) = x := by
      have h3 : g * (w : G) * g⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hw
      exact mul_left_cancel (mul_right_cancel h3)
    rw [← h2]
    exact w.2

theorem s16c1G_exists_noncyclic_three_of_stable (D : Data G) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hP : PairFacts D.M ⊥ V) {U : Subgroup G} (hUV : U ≤ V)
    {E : Subgroup (MulAut (Vtil ⊥ V hV))} (hE : E ≤ Mbar D.M ⊥ V hV) (hE3 : IsPGroup 3 E)
    (hEnc : ¬ IsCyclic E) (hstab : StableUnder E (imgTil ⊥ V hV U)) :
    ∃ X : Subgroup G, X ≤ D.M ⊓ normalizer (U : Set G) ∧ IsPGroup 3 X ∧ ¬ IsCyclic X := by
  classical
  let N : Subgroup G := D.M ⊓ normalizer (U : Set G)
  have hNst : N ≤ stabTil ⊥ V :=
    le_stabTil (inf_le_left.trans hP.le_normalizer) (inf_le_left.trans hP.le_normalizer₀)
  let ψ : ↥N →* MulAut (Vtil ⊥ V hV) :=
    (actTil ⊥ V hV).comp (Subgroup.inclusion hNst)
  have hER : E ≤ ψ.range := by
    intro h hh
    obtain ⟨g, hgM, hgact⟩ := (mem_barSub ⊥ V hV D.M h).1 (hE hh)
    have hmap : ∀ w ∈ imgTil ⊥ V hV U, actTil ⊥ V hV g w ∈ imgTil ⊥ V hV U := by
      intro w hw
      rw [hgact]
      exact hstab h hh w hw
    have hgnorm : (g : G) ∈ normalizer (U : Set G) :=
      s16c1G_mem_normalizer_of_forall_actTil_mem_imgTil hV hUV g.2 hmap
    rw [MonoidHom.mem_range]
    refine ⟨⟨(g : G), Subgroup.mem_inf.2 ⟨hgM, hgnorm⟩⟩, ?_⟩
    have hx : (Subgroup.inclusion hNst
        (⟨(g : G), Subgroup.mem_inf.2 ⟨hgM, hgnorm⟩⟩ : ↥N) : stabTil ⊥ V) = g :=
      Subtype.ext rfl
    show actTil ⊥ V hV (Subgroup.inclusion hNst
      (⟨(g : G), Subgroup.mem_inf.2 ⟨hgM, hgnorm⟩⟩ : ↥N)) = h
    rw [hx]
    exact hgact
  obtain ⟨Q, hQ3, hQc, -⟩ := s15_Three_lift_sylow ψ hER hE3 hEnc
  refine ⟨Q.map N.subtype, ?_, hQ3.map N.subtype, ?_⟩
  · rintro - ⟨c, -, rfl⟩
    exact c.2
  · exact SpLift.not_isCyclic_map N.subtype (Subgroup.subtype_injective N) hQc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
