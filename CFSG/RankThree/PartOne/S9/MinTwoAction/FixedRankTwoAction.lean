module

public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankBridge

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.FixedRank36 SemidirectProduct
open scoped commutatorElement

theorem extraspecialThirtyTwoFixedRankTwoAction : ExtraspecialThirtyTwoFixedRankTwoAction := by
  intro G _ _ q A R D hq hq2 hq5 hAel hA25 hAR hRext hR32 ha hRAD hDq hDexp hDclass hfaith hrank
  have : Fact q.Prime := ⟨hq⟩
  have hRN : R ≤ Subgroup.normalizer (D : Set G) := le_sup_left.trans hRAD
  have hAN : A ≤ Subgroup.normalizer (D : Set G) := le_sup_right.trans hRAD
  set φ : ↥A →* MulAut ↥R := conjHom A R hAR with hφ
  set ρR : ↥R →* MulAut ↥D := conjHom R D hRN with hρR
  set ρA : ↥A →* MulAut ↥D := conjHom A D hAN with hρA
  have hcompat : ∀ a : ↥A, ρR.comp (φ a).toMonoidHom =
      (MulAut.conj (ρA a)).toMonoidHom.comp ρR := by
    intro a
    refine MonoidHom.ext fun r => MulEquiv.ext fun x => Subtype.ext ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MulAut.mul_apply]
    rw [hφ, hρR, hρA]
    simp only [coe_conjHom, coe_conjHom_inv]
    group
  let ρ : ↥R ⋊[φ] ↥A →* MulAut ↥D := SemidirectProduct.lift ρR ρA hcompat
  have hρinl : ∀ r : ↥R, ρ (inl r) = ρR r := fun r => SemidirectProduct.lift_inl _ _ _ r
  obtain ⟨z, hz, hz1, hzz⟩ := exists_center_generator hRext
  obtain ⟨a, haA, hafp⟩ := ha
  have hD : SAData ↥R ↥A φ z (⟨a, haA⟩ : ↥A) :=
    { ext := hRext
      card := hR32
      center_eq := hz
      ne_one := hz1
      sq := hzz
      pgroup := @IsElementaryAbelian.isPGroup 5 ↥A _ hAel
      comm := fun a b => hAel.toIsMulCommutative.is_comm.comm a b
      fpf := by
        intro s hs hcen
        have hsinv : ((s⁻¹ : ↥R) : G) ∉ inSubgroup Subgroup.center R := by
          intro hmem
          apply hs
          have hmem' : (s⁻¹ : ↥R) ∈ Subgroup.center ↥R :=
            (Subgroup.mem_map_iff_mem R.subtype_injective).1 hmem
          simpa using Subgroup.inv_mem _ hmem'
        refine hafp ((s⁻¹ : ↥R) : G) (s⁻¹).2 hsinv ?_
        refine Subgroup.mem_map.2 ⟨(φ ⟨a, haA⟩ s)⁻¹ * s, hcen, ?_⟩
        rw [hφ]
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjHom,
          commutatorElement_def]
        group }
  have hexp' : ∀ x : ↥D, x ^ q = 1 := fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hDexp x x.2)
  have hclass := commutator_le_center_of_commutator_eq_bot D hDclass
  have hfaith' : ∀ s : ↥R, ρ (inl s) = 1 → s = 1 := by
    intro s hs
    rw [hρinl, hρR] at hs
    have hmem : (s : G) ∈ R ⊓ Subgroup.centralizer (D : Set G) := by
      refine Subgroup.mem_inf.2 ⟨s.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
      have h := congrArg (fun f : MulAut ↥D => ((f ⟨g, hg⟩ : ↥D) : G)) hs
      simp only [coe_conjHom, MulAut.one_apply] at h
      calc g * (s : G) = ((s : G) * g * (s : G)⁻¹) * s := by rw [h]
        _ = s * g := by group
    rw [hfaith, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hrank' : ∀ s : ↥R, s ≠ 1 → CFSG.pRank q ↥(fixedSub (ρ (inl s))) ≤ 2 := by
    intro s hs1
    rw [hρinl, hρR]
    exact (pRank_fixedSub_conjHom_le R D hRN s).trans
      (hrank s s.2 (fun h => hs1 (Subtype.ext h)))
  obtain ⟨hgen, hcard4, hshape⟩ := fixedRank_core hq2 hq5 hDq hexp' hclass hD ρ hfaith' hrank'
  refine ⟨?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro d hd r hr
      have h := (Subgroup.mem_normalizer_iff.1 (hRN hr) d⁻¹).1 (D.inv_mem hd)
      have h' : ⁅d, r⁆ = d * (r * d⁻¹ * r⁻¹) := by rw [commutatorElement_def]; group
      rw [h']
      exact D.mul_mem hd h
    · intro y hy
      have hyclos : (⟨y, hy⟩ : ↥D) ∈ Subgroup.closure
          {x : ↥D | ∃ (d : ↥D) (s : ↥R), x = d⁻¹ * ρ (inl s) d} := hgen ▸ Subgroup.mem_top _
      have hle : Subgroup.closure {x : ↥D | ∃ (d : ↥D) (s : ↥R), x = d⁻¹ * ρ (inl s) d} ≤
          ⁅D, R⁆.comap D.subtype := by
        rw [Subgroup.closure_le]
        rintro _ ⟨d, s, rfl⟩
        show ((d⁻¹ * ρ (inl s) d : ↥D) : G) ∈ ⁅D, R⁆
        rw [hρinl, hρR]
        have h : ((d⁻¹ * conjHom R D hRN s d : ↥D) : G) = ⁅((d⁻¹ : ↥D) : G), (s : G)⁆ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjHom, commutatorElement_def]
          group
        rw [h]
        exact Subgroup.commutator_mem_commutator (d⁻¹).2 s.2
      exact hle hyclos
  · rw [relIndex_inSubgroup_frattini]
    exact hcard4
  · rcases hshape with ⟨hel, hcard⟩ | ⟨hcard5, hcomm, hcenter, hfrat⟩
    · exact Or.inl ⟨hel, hcard⟩
    · refine Or.inr ⟨hDexp, hcard5, ?_, ?_, ?_⟩
      · rw [← map_commutator_subtype, Subgroup.card_map_of_injective D.subtype_injective]
        exact hcomm
      · rw [← map_center_subtype, hcenter, map_commutator_subtype]
      · show (frattini ↥D).map D.subtype = ⁅D, D⁆
        rw [hfrat, map_commutator_subtype]

end CFSG.RankThree.PartOne
