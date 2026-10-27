module

public import CFSG.Milestones.ASVolI.C31.J4NP.HCl

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
open CFSG.Quasithin.J4Loc (omegaZ)

@[expose] def burnsideJ4NP_VerdictAt (A₀ : Subgroup J) : Prop :=
  ∀ R : Subgroup J, burnsideJ4NP_Hyp R → ∀ c : J,
    A₀.map (MulAut.conj c).toMonoidHom ≤ omegaZ R →
    burnsideJ4NP_W R ≤ A₀.map (MulAut.conj c).toMonoidHom →
    ∃ d : J, burnsideJ4NP_F.map (MulAut.conj d).toMonoidHom ≤ burnsideJ4NP_W R

@[expose] def burnsideJ4NP_VerdictW (W₀ : Subgroup J) : Prop :=
  ∀ A₀ : Subgroup J, Subgroup.closure {x | x ∈ A₀ ∧ burnsideJ4NP_Is2A x} = W₀ →
    burnsideJ4NP_VerdictAt A₀

theorem burnsideJ4NP_verdictAt_map_conj {A₀ : Subgroup J} (h : burnsideJ4NP_VerdictAt A₀)
    (g : J) : burnsideJ4NP_VerdictAt (A₀.map (MulAut.conj g).toMonoidHom) := by
  intro R hR c hAZ hWA
  rw [burnsideJ4KW_map_conj_map_conj] at hAZ hWA
  exact h R hR (c * g) hAZ hWA

theorem burnsideJ4NP_verdictW_map_conj {W₀ : Subgroup J} (h : burnsideJ4NP_VerdictW W₀)
    (g : J) : burnsideJ4NP_VerdictW (W₀.map (MulAut.conj g).toMonoidHom) := by
  intro A₀ hA
  have hW : Subgroup.closure {x | x ∈ A₀.map (MulAut.conj g⁻¹).toMonoidHom ∧
      burnsideJ4NP_Is2A x} = W₀ := by
    rw [burnsideJ4NP_closure2A_map_conj, hA, burnsideJ4NP_map_conj_inv_map_conj]
  have e : (A₀.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A₀ := by
    simpa using burnsideJ4NP_map_conj_inv_map_conj A₀ g⁻¹
  rw [← e]
  exact burnsideJ4NP_verdictAt_map_conj (h _ hW) g

theorem burnsideJ4NP_verdictW_of_false {W₀ : Subgroup J}
    (h : ∀ A₀ : Subgroup J, Subgroup.closure {x | x ∈ A₀ ∧ burnsideJ4NP_Is2A x} = W₀ →
      ∀ R : Subgroup J, burnsideJ4NP_Hyp R → ∀ c : J,
        A₀.map (MulAut.conj c).toMonoidHom ≤ omegaZ R →
        burnsideJ4NP_W R ≤ A₀.map (MulAut.conj c).toMonoidHom → False) :
    burnsideJ4NP_VerdictW W₀ :=
  fun A₀ hA R hR c hAZ hWA => (h A₀ hA R hR c hAZ hWA).elim

theorem burnsideJ4NP_verdictW_F {W₀ : Subgroup J} {d : J}
    (hF : burnsideJ4NP_F.map (MulAut.conj d).toMonoidHom ≤ W₀) : burnsideJ4NP_VerdictW W₀ :=
  fun A₀ hA R _ c hAZ hWA => burnsideJ4NP_verdict_F (hA ▸ hF) R c hAZ hWA

theorem burnsideJ4NP_verdictW_np
    {W₀ : Subgroup J} {g : J}
    (hg : P0.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (W₀ : Set J)) :
    burnsideJ4NP_VerdictW W₀ :=
  burnsideJ4NP_verdictW_of_false fun _ hA _ hR c hAZ hWA =>
    burnsideJ4NP_verdict_np (hA ▸ hg) hR c hAZ hWA

@[expose] def burnsideJ4NP_VerdictAtH (A₀ : Subgroup J) : Prop :=
  ∀ R : Subgroup J, burnsideJ4NP_Hyp R → ∀ c ∈ Hj,
    A₀.map (MulAut.conj c).toMonoidHom ≤ omegaZ R →
    burnsideJ4NP_W R ≤ A₀.map (MulAut.conj c).toMonoidHom →
    ∃ d : J, burnsideJ4NP_F.map (MulAut.conj d).toMonoidHom ≤ burnsideJ4NP_W R

@[expose] def burnsideJ4NP_VerdictWH (W₀ : Subgroup J) : Prop :=
  ∀ A₀ : Subgroup J, Subgroup.closure {x | x ∈ A₀ ∧ burnsideJ4NP_Is2A x} = W₀ →
    burnsideJ4NP_VerdictAtH A₀

theorem burnsideJ4NP_verdictWH_of_verdictW {W₀ : Subgroup J} (h : burnsideJ4NP_VerdictW W₀) :
    burnsideJ4NP_VerdictWH W₀ :=
  fun A₀ hA R hR c _ hAZ hWA => h A₀ hA R hR c hAZ hWA

theorem burnsideJ4NP_verdictAtH_map_conj {A₀ : Subgroup J} (h : burnsideJ4NP_VerdictAtH A₀)
    {g : J} (hg : g ∈ Hj) : burnsideJ4NP_VerdictAtH (A₀.map (MulAut.conj g).toMonoidHom) := by
  intro R hR c hc hAZ hWA
  rw [burnsideJ4KW_map_conj_map_conj] at hAZ hWA
  exact h R hR (c * g) (Hj.mul_mem hc hg) hAZ hWA

theorem burnsideJ4NP_verdictWH_map_conj {W₀ : Subgroup J} (h : burnsideJ4NP_VerdictWH W₀)
    {g : J} (hg : g ∈ Hj) : burnsideJ4NP_VerdictWH (W₀.map (MulAut.conj g).toMonoidHom) := by
  intro A₀ hA
  have hW : Subgroup.closure {x | x ∈ A₀.map (MulAut.conj g⁻¹).toMonoidHom ∧
      burnsideJ4NP_Is2A x} = W₀ := by
    rw [burnsideJ4NP_closure2A_map_conj, hA, burnsideJ4NP_map_conj_inv_map_conj]
  have e : (A₀.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A₀ := by
    simpa using burnsideJ4NP_map_conj_inv_map_conj A₀ g⁻¹
  rw [← e]
  exact burnsideJ4NP_verdictAtH_map_conj (h _ hW) hg

theorem burnsideJ4NP_hverdict_of_verdictWH (Rep Wv : ℕ → Subgroup J) (N : ℕ)
    (hW : ∀ k < N, ∃ g ∈ Hj, Subgroup.closure {x | x ∈ Rep k ∧ burnsideJ4NP_Is2A x} =
      (Wv k).map (MulAut.conj g).toMonoidHom)
    (hv : ∀ k < N, burnsideJ4NP_VerdictWH (Wv k)) :
    ∀ k < N, ∀ R : Subgroup J, burnsideJ4NP_Hyp R → ∀ h ∈ Hj,
      (Rep k).map (MulAut.conj h).toMonoidHom ≤ omegaZ R →
      burnsideJ4NP_W R ≤ (Rep k).map (MulAut.conj h).toMonoidHom →
      ∃ c : J, burnsideJ4NP_F.map (MulAut.conj c).toMonoidHom ≤ burnsideJ4NP_W R := by
  intro k hk R hR h hh hAZ hWA
  obtain ⟨g, hg, hgW⟩ := hW k hk
  exact burnsideJ4NP_verdictWH_map_conj (hv k hk) hg (Rep k) hgW R hR h hh hAZ hWA

end CFSG.ASVolI
