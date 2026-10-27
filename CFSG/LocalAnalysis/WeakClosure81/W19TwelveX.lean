module

public import CFSG.LocalAnalysis.WeakClosure81.W19ElevenEnd
public import CFSG.LocalAnalysis.WeakClosure81.W19Chief

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Is1911 (D : Data G) (V₀ V I : Subgroup G) : Prop :=
  I ≤ Z193 D V ∧ Nat.card ↥I = 4 ∧ V₀ ≤ I ∧
    normalizer (Z193 D V : Set G) ≤ normalizer (I : Set G) ∧
    ∃ g ∈ normalizer (Z193 D V : Set G), g ∉ D.M ∧ g ^ 2 ∈ D.M

theorem concl1911_iff (D : Data G) (V₀ V : Subgroup G) :
    Concl1911 D V₀ V ↔ ∃ I : Subgroup G, Is1911 D V₀ V I :=
  Iff.rfl

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem V₀_le_conj_M (c : MinCex193 D V₀ V p X) (h2 : Nat.card V₀ = 2) {n : G}
    (hn : n ∈ normalizer (Z193 D V : Set G)) : V₀ ≤ conjSubgroup D.M n := by
  intro v hv
  rw [mem_conjSubgroup_iff]
  have hvZ : v ∈ Z193 D V := c.V₀_le_Z193 h2 hv
  exact D.sylowM.le (c.Z193_le_T ((Subgroup.mem_normalizer_iff.1 hn v).1 hvZ))

theorem commutator_V₀_eq_bot (c : MinCex193 D V₀ V p X) (h2 : Nat.card V₀ = 2)
    {K : Subgroup G} (hK : K ≤ D.M) : ⁅V₀, K⁆ = ⊥ := by
  obtain ⟨v, hvV, hv1, hV₀⟩ := c.exists_v₀ h2
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  rcases hV₀ x hx with h | h
  · rw [h]
    simp
  · rw [h]
    have hk' := c.conj_eq_of_mem_M hvV hv1 hV₀ (hK hk)
    calc k * v = k * v * k⁻¹ * k := by group
      _ = v * k := by rw [hk']

theorem not_commutator_le_V₀ (c : MinCex193 D V₀ V p X) (h2 : Nat.card V₀ = 2) {I : Subgroup G}
    (hI : Is1911 D V₀ V I) : ¬ ⁅X, I⁆ ≤ V₀ := by
  intro hle
  obtain ⟨-, -, hV₀I, hNI, g, hgN, hgM, -⟩ := hI
  obtain ⟨v, hvV, hv1, hV₀⟩ := c.exists_v₀ h2
  have haI : g * v * g⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.1 (hNI hgN) v).1 (hV₀I hvV)
  have ha1 : g * v * g⁻¹ ≠ 1 := by
    intro h
    apply hv1
    have e : v = g⁻¹ * (g * v * g⁻¹) * g := by group
    rw [e, h]
    group
  have haM : g * v * g⁻¹ ∈ conjSubgroup V₀ g⁻¹ := by
    rw [mem_conjSubgroup_iff]
    have e : g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v := by group
    rw [e]
    exact hvV
  have hXa : ∀ x ∈ X, x * (g * v * g⁻¹) = g * v * g⁻¹ * x := by
    intro x hx
    have hc : ⁅x, g * v * g⁻¹⁆ ∈ V₀ := hle (Subgroup.commutator_mem_commutator hx haI)
    have hxM : x ∈ D.M := c.hyp.le_M (Subgroup.mem_sup_left hx)
    have hxf : x * ⁅x, g * v * g⁻¹⁆ = ⁅x, g * v * g⁻¹⁆ * x := by
      rcases hV₀ _ hc with h | h
      · rw [h]
        simp
      · rw [h]
        have hx' := c.conj_eq_of_mem_M hvV hv1 hV₀ hxM
        calc x * v = x * v * x⁻¹ * x := by group
          _ = v * x := by rw [hx']
    have hf2 : ⁅x, g * v * g⁻¹⁆ ^ 2 = 1 :=
      c.isElemAbelian_Z193.2 _ (c.V₀_le_Z193 h2 hc)
    exact mul_comm_of_comm_commutator c.hyp.prime c.hyp.odd (c.hyp.exponent x hx) hxf hf2
  have hXle : X ≤ conjSubgroup D.M g⁻¹ := fun x hx =>
    centralizer_le_conj_M c.setting c.ne_bot g⁻¹ haM ha1
      (Subgroup.mem_centralizer_singleton_iff.2 (hXa x hx))
  have hgM' : g⁻¹ ∉ D.M := fun h => hgM (by simpa using D.M.inv_mem h)
  have hbot := c.hyp.inf_eq_bot g⁻¹ hgM' (c.V₀_le_conj_M h2 ((normalizer _).inv_mem hgN))
  have hX : X ≤ ⊥ := by
    have h1 : X ≤ X ⊓ conjSubgroup D.M g⁻¹ := le_inf le_rfl hXle
    rwa [hbot] at h1
  apply c.hyp.noncyclic
  rw [le_bot_iff.1 hX]
  infer_instance

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end
