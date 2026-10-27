module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthIdentDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus SpCoord NbrOrth CFSG.Open
open CFSG.RankThree.Classical2 (orthDerived)

section Refl

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs Y : Subgroup G}
  (Φ : OrthFrameCore p Bs Y)

theorem qtwoOrth_exists_refl_acts (x : OmPlusIdx Φ.r) :
    ∃ ρ ∈ ggAutomizer Y Bs, GGIsReflection p ρ ∧ Φ.Acts ρ x := by
  classical
  have := Φ.finite_linearEquiv
  have hQ := Φ.Δ.polarBilin_nondegenerate_of_noFixed Φ.hfix
  have hdim := Φ.Δ.finrank_eq_two_mul_of_noFixed Φ.hfix
  have hT := CFSG.RankThree.PartOne.exists_threeSingular_of_dim Φ.Q hQ Φ.hr hdim
  have : Nontrivial Φ.V := CFSG.RankThree.PartOne.nontrivial_of_threeSingular hT
  have hZ' := CFSG.RankThree.PartOne.center_orthDerived_eq_bot hQ hT
  obtain ⟨⟨⟨a, b⟩, hab⟩, s⟩ := x
  have hne : a ≠ b := ne_of_lt hab
  cases s
  · obtain ⟨w, hw, hn⟩ := Φ.swapReal a b hne
    have hgY : Φ.ψ w ∈ Y := by
      have h : Φ.ψ w ∈ Φ.ψ.range := ⟨w, rfl⟩
      rwa [Φ.hrange] at h
    have ha : ∀ b' : ↥Bs, ((ggConjAut Bs hn b' : ↥Bs) : G) = Φ.ψ w * b' * (Φ.ψ w)⁻¹ :=
      fun b' => ggConjAut_apply Bs hn b'
    refine ⟨ggConjAut Bs hn, ggConjAut_mem_ggAutomizer hgY hn, ?_, ?_⟩
    · exact isReflection_of_inner Φ.ψ Φ.β Φ.hinj Φ.hcompat Φ.hβA Φ.hβsurj
        (Fact.out : p.Prime).one_lt ha (fun t ht => Φ.Δ.swap_sq_comm hw t ht)
        (fun t => Φ.Δ.mem_reflFixed_iff hw t) (Φ.Δ.card_reflFixed hne)
    · intro b' f hbf
      have hv := congrArg Subtype.val (Φ.beta_equivariant_of_inner hZ' w _ ha b')
      change (Φ.β (ggConjAut Bs hn b') : Φ.V ≃ₗ[Φ.F] Φ.V) =
        (w : Φ.V ≃ₗ[Φ.F] Φ.V) * (Φ.β b' : Φ.V ≃ₗ[Φ.F] Φ.V) * (w : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ at hv
      rw [hv, hbf, hw f]
      rfl
  · obtain ⟨ws, hws, hns⟩ := Φ.swapReal a b hne
    obtain ⟨wd, hwd, hnd⟩ := Φ.dinvReal a b hne
    have hw : ∀ f : Fin Φ.r → Multiplicative (ZMod p),
        ((wd * ws : ↥(orthDerived Φ.Q)) : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f *
          ((wd * ws : ↥(orthDerived Φ.Q)) : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
          Φ.Δ.τ (dinv a b (permAut (Equiv.swap a b) f)) := by
      intro f
      have h1 := hws f
      have h2 := hwd (permAut (Equiv.swap a b) f)
      rw [← h2, ← h1]
      simp only [Subgroup.coe_mul, mul_inv_rev]
      group
    have hn : Φ.ψ (wd * ws) ∈ Subgroup.normalizer (Bs : Set G) := by
      rw [map_mul]
      exact Subgroup.mul_mem _ hnd hns
    have hgY : Φ.ψ (wd * ws) ∈ Y := by
      have h : Φ.ψ (wd * ws) ∈ Φ.ψ.range := ⟨wd * ws, rfl⟩
      rwa [Φ.hrange] at h
    have ha : ∀ b' : ↥Bs, ((ggConjAut Bs hn b' : ↥Bs) : G) =
        Φ.ψ (wd * ws) * b' * (Φ.ψ (wd * ws))⁻¹ := fun b' => ggConjAut_apply Bs hn b'
    refine ⟨ggConjAut Bs hn, ggConjAut_mem_ggAutomizer hgY hn, ?_, ?_⟩
    · exact isReflection_of_inner Φ.ψ Φ.β Φ.hinj Φ.hcompat Φ.hβA Φ.hβsurj
        (Fact.out : p.Prime).one_lt ha (fun t ht => Φ.Δ.pos_sq_comm hne hw t ht)
        (fun t => Φ.Δ.mem_reflFixedPos_iff hne hw t) (Φ.Δ.card_reflFixedPos hne)
    · intro b' f hbf
      have hv := congrArg Subtype.val (Φ.beta_equivariant_of_inner hZ' (wd * ws) _ ha b')
      change (Φ.β (ggConjAut Bs hn b') : Φ.V ≃ₗ[Φ.F] Φ.V) =
        ((wd * ws : ↥(orthDerived Φ.Q)) : Φ.V ≃ₗ[Φ.F] Φ.V) * (Φ.β b' : Φ.V ≃ₗ[Φ.F] Φ.V) *
          ((wd * ws : ↥(orthDerived Φ.Q)) : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ at hv
      rw [hv, hbf, hw f]
      rfl

end Refl

end CFSG.StandardType.QTwo

end
