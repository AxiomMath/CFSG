module

public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.Quasithin.Background.A3Structure36AQuasi

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Quasithin

theorem nontrivial_specialLinear_two_zmod (n : ℕ) [Fact (1 < n)] :
    Nontrivial (Matrix.SpecialLinearGroup (Fin 2) (ZMod n)) := by
  refine ⟨⟨1, ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩, ?_⟩⟩
  intro h
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod n) =>
    (g : Matrix (Fin 2) (Fin 2) (ZMod n)) 0 1) h
  simp at this

theorem not_a36Case3_of_isQuasisimple {X : Type} [Group X] (hQ : CFSG.IsQuasisimple X) :
    ¬ A36Case3 X := by
  rintro ⟨p, hp, -, hgf, -, -, ψ, hsurj, hker, -⟩
  have : Fact p.Prime := ⟨hp⟩
  have htop : CFSG.fittingSubgroup X = ⊤ := hgf ▸ CFSG.Quasithin.A36A.generalizedFitting_eq_top hQ
  have hψ : ∀ x, ψ x = 1 := fun x => by
    have : x ∈ ψ.ker := by rw [hker, htop]; exact Subgroup.mem_top x
    exact this
  have := nontrivial_specialLinear_two_zmod p
  obtain ⟨y, hy⟩ := exists_ne (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
  obtain ⟨x, rfl⟩ := hsurj y
  exact hy (hψ x)

theorem not_a36Case4_of_isQuasisimple {X : Type} [Group X] (hQ : CFSG.IsQuasisimple X) :
    ¬ A36Case4 X := by
  rintro ⟨hgf, -, ⟨e⟩, -⟩
  have htop : CFSG.fittingSubgroup X = ⊤ := hgf ▸ CFSG.Quasithin.A36A.generalizedFitting_eq_top hQ
  have : Subsingleton (X ⧸ CFSG.fittingSubgroup X) := QuotientGroup.subsingleton_iff.mpr htop
  have : Fact (1 < 5) := ⟨by norm_num⟩
  have := nontrivial_specialLinear_two_zmod 5
  obtain ⟨y, hy⟩ := exists_ne (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))
  exact hy (e.symm.injective (Subsingleton.elim _ _))

theorem center_eq_bot_of_isSimpleGroup_of_isQuasisimple {X : Type} [Group X]
    (hQ : CFSG.IsQuasisimple X) (hs : IsSimpleGroup X) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    obtain ⟨-, -, a, b, hab⟩ := hQ
    have : Subsingleton (X ⧸ Subgroup.center X) := QuotientGroup.subsingleton_iff.mpr h
    exact hab (Subsingleton.elim _ _)

theorem card_eq_of_isHat {X S Y : Type} [Group X] [Group S] [Group Y] (hX : IsHat X S)
    (e : X ⧸ Subgroup.center X ≃* Y) : Nat.card S = Nat.card Y := by
  obtain ⟨f⟩ := hX.2.2
  exact (Nat.card_congr f.symm.toEquiv).trans (Nat.card_congr e.toEquiv)

end CFSG.Quasithin.S146zY
