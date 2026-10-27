module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTorusTBGroup_false_of_pRank_le_two {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (hrk : ∀ E : Subgroup R, IsElemAbelian p E → Nat.card E ≤ p ^ 2)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R} {A : Subgroup (MulAut L')}
    (hA : GGTorusTBGroup p r R I L' ψ A) : False := by
  classical
  obtain ⟨hψ, hker, hperf, hAe, hAI, _hr, h3, _hsc⟩ := hA
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
    have hφp : φ ^ p = 1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hk, hAe.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ hφI hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hAe e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hAe.2 _ he
  have hle : Nat.card E ≤ p ^ 2 := hrk E hEab
  rw [← hcardE] at h3
  exact absurd (le_trans h3 hle)
    (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))

end CFSG.StandardType
