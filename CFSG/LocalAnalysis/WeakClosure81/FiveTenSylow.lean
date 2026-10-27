module

public import CFSG.LocalAnalysis.WeakClosure81.FiveTenWeak
public import CFSG.LocalAnalysis.WeakClosure81.FiveTenDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem FiveTenHyp.le_M {H M T : Subgroup G} {Ω : Set (Subgroup G)} (h : FiveTenHyp H M T Ω) :
    T ≤ M := fun t ht =>
  h.normalizer_le ⟨h.sylow.le ht, le_normalizer_weakClosure_of_isInvColl h.invColl h.sylow.le ht⟩

theorem FiveTenHyp.odd_relIndex {H M T : Subgroup G} {Ω : Set (Subgroup G)}
    (h : FiveTenHyp H M T Ω) : Odd (M.relIndex H) := by
  have hdvd : M.relIndex H ∣ T.relIndex H := Subgroup.relIndex_dvd_of_le_left H h.le_M
  have hnd : ¬ 2 ∣ T.relIndex H := h.sylow.not_dvd_relIndex
  by_contra hodd
  exact hnd ((even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)).trans hdvd)

theorem FiveTenHyp.exists_ne_bot {H M T : Subgroup G} {Ω : Set (Subgroup G)}
    (h : FiveTenHyp H M T Ω) : ∃ A ∈ Ω, A ≤ T ∧ A ≠ ⊥ := by
  by_contra hcon
  have hall : ∀ A ∈ Ω, A ≤ T → A = ⊥ := fun A hA hAT => by
    by_contra hne
    exact hcon ⟨A, hA, hAT, hne⟩
  have hW : E1.weakClosure T Ω = ⊥ :=
    le_bot_iff.1 (iSup₂_le fun A hA => iSup_le fun hAT => (hall A hA hAT).le)
  apply h.not_le
  intro x hx
  apply h.normalizer_le
  refine ⟨hx, ?_⟩
  have hbot : normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.2 inferInstance
  rw [hW, hbot]
  trivial

theorem isSylowIn_inf_of_le {H T M : Subgroup G} (hT : IsSylowIn 2 T H) (hTM : T ≤ M) :
    IsSylowIn 2 T (M ⊓ H) :=
  E1.isSylowIn_two_iff.2 (B6.isSylowTwoOf_mono (E1.isSylowIn_two_iff.1 hT) (le_inf hTM hT.le)
    inf_le_right)

theorem exists_conjSub_le_of_isSylowIn {H T M S : Subgroup G} (hT : IsSylowIn 2 T H)
    (hTM : T ≤ M) (hS : IsPGroup 2 S) (hSM : S ≤ M) (hSH : S ≤ H) :
    ∃ m ∈ M ⊓ H, A1b.conjSub m S ≤ T := by
  have hT' : IsSylowIn 2 T (M ⊓ H) := isSylowIn_inf_of_le hT hTM
  obtain ⟨S', hS', hSS'⟩ := B6.exists_isSylowTwoOf_ge hS (le_inf hSM hSH)
  obtain ⟨g, hg, hgS⟩ := B6.isSylowTwoOf_exists_conj hS' (E1.isSylowIn_two_iff.1 hT')
  refine ⟨g, hg, ?_⟩
  have : A1b.conjSub g S ≤ A1b.conjSub g S' := A1b.conjSub_mono g hSS'
  exact hgS ▸ this

theorem conjSub_le_iff_of_mem {M X : Subgroup G} {m : G} (hm : m ∈ M) :
    A1b.conjSub m X ≤ M ↔ X ≤ M := by
  constructor
  · intro h x hx
    have h1 : m * x * m⁻¹ ∈ M := h (A1b.mem_conjSub_of_mem hx)
    have h2 : m⁻¹ * (m * x * m⁻¹) * m ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hm) h1) hm
    simpa [mul_assoc] using h2
  · intro h x hx
    rw [A1b.mem_conjSub_iff] at hx
    have h1 : m * (m⁻¹ * x * m) * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm (h hx)) (M.inv_mem hm)
    simpa [mul_assoc] using h1

theorem inf_normalizer_conjSub {H U : Subgroup G} {m : G} (hm : m ∈ H) :
    H ⊓ normalizer (A1b.conjSub m U : Set G) = A1b.conjSub m (H ⊓ normalizer (U : Set G)) := by
  have h1 : A1b.conjSub m H = H := B6.conjSub_eq_self (Subgroup.le_normalizer hm)
  have h2 : A1b.conjSub m (H ⊓ normalizer (U : Set G)) =
      A1b.conjSub m H ⊓ A1b.conjSub m (normalizer (U : Set G)) :=
    Subgroup.map_inf _ _ _ (MulAut.conj m).injective
  rw [h2, h1, A1b.conjSub_normalizer]

end CFSG.LocalAnalysis.WeakClosure81
