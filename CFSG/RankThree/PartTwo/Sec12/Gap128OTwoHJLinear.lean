module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Janko
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Basic

public section

namespace CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ

open CFSG CFSG.Blueprint

variable {L : Type*} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]
  {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]

theorem false_of_finrank_le_four (π : L →* NativeSporadic.J2) (hπ : Function.Surjective π)
    (hdim : Module.finrank (ZMod p) V ≤ 4) (ρ : L →* Module.End (ZMod p) V)
    (hker : ∀ g, ρ g = 1 → π g = 1) : False := by
  set k := Module.finrank (ZMod p) V with hk
  have hW : Module.finrank (ZMod p) (V × (Fin (4 - k) → ZMod p)) = 4 := by
    rw [Module.finrank_prod, Module.finrank_fin_fun]
    omega
  let b := Module.finBasisOfFinrankEq (ZMod p) (V × (Fin (4 - k) → ZMod p)) hW
  let ψ : Module.End (ZMod p) V →* Module.End (ZMod p) (V × (Fin (4 - k) → ZMod p)) :=
    (LinearMap.prodMapAlgHom (ZMod p) V (Fin (4 - k) → ZMod p)).toMonoidHom.comp
      (MonoidHom.inl _ _)
  let χ : Module.End (ZMod p) (V × (Fin (4 - k) → ZMod p)) →* Matrix (Fin 4) (Fin 4) (ZMod p) :=
    (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom
  let ρ4 : L →* GL (Fin 4) (ZMod p) := (χ.comp (ψ.comp ρ)).toHomUnits
  have hker4 : ρ4.ker ≤ π.ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    apply hker
    have h1 : χ (ψ (ρ g)) = χ 1 := by
      rw [map_one]
      exact congrArg Units.val hg
    have h2 : ψ (ρ g) = 1 := (LinearMap.toMatrixAlgEquiv b).injective h1
    refine LinearMap.ext fun v => ?_
    have h3 := congrArg Prod.fst (LinearMap.congr_fun h2 (v, 0))
    simpa [ψ] using h3
  exact (Sec4.Census.isEmpty_mulEquiv_j2 ρ4 π hπ hker4).false (MulEquiv.refl _)

theorem forall_apply_eq_of_finrank_le_four [Group.IsPerfect L]
    (hJ : IsSimpleGroup NativeSporadic.J2) (π : L →* NativeSporadic.J2)
    (hπ : Function.Surjective π) (hK : Group.IsSolvable π.ker) (ρ : L →* Module.End (ZMod p) V)
    (U : Submodule (ZMod p) V) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U)
    (hdim : Module.finrank (ZMod p) U ≤ 4) : ∀ g, ∀ u ∈ U, ρ g u = u := by
  let ρU : L →* Module.End (ZMod p) U :=
    { toFun := fun g => (ρ g).restrict (hU g)
      map_one' := by
        refine LinearMap.ext fun u => Subtype.ext ?_
        simp
      map_mul' := fun g h => by
        refine LinearMap.ext fun u => Subtype.ext ?_
        simp [Module.End.mul_apply] }
  by_cases hN : ρU.ker ≤ π.ker
  · exact (false_of_finrank_le_four π hπ hdim ρU fun g hg => hN hg).elim
  · have hmap : ρU.ker.map π = ⊤ := by
      have hn : (ρU.ker.map π).Normal := (MonoidHom.normal_ker _).map π hπ
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρU.ker.map π) with h | h
      · refine absurd (fun g hg => ?_) hN
        have hg' : π g ∈ ρU.ker.map π := ⟨g, hg, rfl⟩
        rw [h, Subgroup.mem_bot] at hg'
        exact hg'
      · exact h
    have hNn : ρU.ker.Normal := MonoidHom.normal_ker _
    have htop : ρU.ker = ⊤ := by
      apply Sec4.Census.eq_top_of_isSolvable_quotient
      have hsurj : Function.Surjective ((QuotientGroup.mk' ρU.ker).comp π.ker.subtype) := by
        intro x
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
        have hg : π g ∈ ρU.ker.map π := by
          rw [hmap]
          trivial
        obtain ⟨n, hn, hng⟩ := hg
        refine ⟨⟨n⁻¹ * g, ?_⟩, ?_⟩
        · rw [MonoidHom.mem_ker, map_mul, map_inv, hng, inv_mul_cancel]
        · change (QuotientGroup.mk (n⁻¹ * g) : L ⧸ ρU.ker) = QuotientGroup.mk g
          rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (inv_mem hn), one_mul]
      exact Group.isSolvable_of_surjective hsurj
    intro g u hu
    have hg : ρU g = 1 := by
      rw [← MonoidHom.mem_ker, htop]
      trivial
    exact congrArg Subtype.val (LinearMap.congr_fun hg ⟨u, hu⟩)

end CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
