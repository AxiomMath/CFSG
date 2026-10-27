module

public import CFSG.LocalAnalysis.WeakClosure81.W19TwelveE
public import CFSG.LocalAnalysis.WeakClosure81.W19TwelveX
public import CFSG.LocalAnalysis.WeakClosure81.W19TenA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap1912 (D : Data G) (V₀ V X : Subgroup G) : Prop :=
  ∀ I : Subgroup G, Is1911 D V₀ V I →
    ∀ k ∈ X ⊔ D.T, ∀ a ∈ I, ∀ b ∈ I, a * (k * b * k⁻¹) = k * b * k⁻¹ * a

@[expose] def Gap1912E0 (D : Data G) (V₀ V X : Subgroup G) : Prop :=
  ∀ I : Subgroup G, Is1911 D V₀ V I → ¬ ⁅X, CFSG.Quasithin.conjClosure I (X ⊔ D.T)⁆ ≤ V₀ →
    ∃ E₀ : Subgroup G, V₀ ≤ E₀ ∧ E₀ ≤ CFSG.Quasithin.conjClosure I (X ⊔ D.T) ∧
      X ⊔ D.T ≤ normalizer (E₀ : Set G) ∧
      (∀ U : Subgroup G, V₀ ≤ U → U ≤ E₀ → X ⊔ D.T ≤ normalizer (U : Set G) →
        U = V₀ ∨ U = E₀) ∧
      ¬ ⁅X, E₀⁆ ≤ V₀

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem false_of_E₀ (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G) (h4 : Card196Four D V p X)
    (h2 : Nat.card ↥V₀ = 2) {E₀ : Subgroup G} (hE : Hyp198 D X E₀ V₀)
    (hXE : ¬ ⁅X, E₀⁆ ≤ V₀) : False := by
  have hXM : X ≤ D.M := le_sup_left.trans c.hyp.le_M
  have hFE : V₀ < E₀ := by
    refine lt_of_le_of_ne hE.F_le fun h => hXE ?_
    rw [← h, Subgroup.commutator_comm, c.commutator_V₀_eq_bot h2 hXM]
    exact bot_le
  obtain ⟨g, hA, hAE⟩ := c.exists_conj_not_comm_le h4 hE hXE
  obtain ⟨-, B, -, hcard⟩ := Hyp198.nine c h162 h4 hE hFE hA hAE
  have hle : commEB E₀ V₀ B ≤ V₀ := by
    refine Subgroup.commutator_le.2 fun e he b hb => ?_
    exact ((mem_eB_iff hE.F_le fun x hx y hy => hE.isElemAbelian.comm hx hy).1 he).2 b hb
  have hcard' := Subgroup.card_le_of_le hle
  omega

theorem false_of_concl1911 (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G)
    (h4 : Card196Four D V p X) (h2 : Nat.card ↥V₀ = 2) (hc : Concl1911 D V₀ V)
    (h12 : Gap1912 D V₀ V X) (h12e : Gap1912E0 D V₀ V X) : False := by
  obtain ⟨I, hI⟩ := (concl1911_iff D V₀ V).1 hc
  have hIZ : I ≤ Z193 D V := hI.1
  have hEA : IsElemAbelian 2 (CFSG.Quasithin.conjClosure I (X ⊔ D.T)) :=
    isElemAbelian_conjClosure (IsElemAbelian.mono c.isElemAbelian_Z193 hIZ) (h12 I hI)
  have hXE₁ : ¬ ⁅X, CFSG.Quasithin.conjClosure I (X ⊔ D.T)⁆ ≤ V₀ := fun hle =>
    c.not_commutator_le_V₀ h2 hI
      ((Subgroup.commutator_mono le_rfl (CFSG.Quasithin.le_conjClosure I (X ⊔ D.T))).trans hle)
  obtain ⟨E₀, hVE, hEE, hn, hirr, hXE⟩ := h12e I hI hXE₁
  have hEH : E₀ ≤ X ⊔ D.T :=
    hEE.trans (conjClosure_le_of_le (hIZ.trans ((c.Z193_le_T).trans le_sup_right)))
  have hFn : X ⊔ D.T ≤ normalizer (V₀ : Set G) := c.hyp.le_M.trans c.setting.pair.le_normalizer₀
  have hcomm : ⁅V₀, twoResidual (X ⊔ D.T)⁆ = ⊥ :=
    c.commutator_V₀_eq_bot h2 ((twoResidual_le _).trans c.hyp.le_M)
  exact c.false_of_E₀ h162 h4 h2
    ⟨hEH, IsElemAbelian.mono hEA hEE, hVE, hn, hFn, hirr, hcomm⟩ hXE

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end
