module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutFixSyl

public section

namespace CFSG.Quasithin.H13.F431.D4q.Out

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.D4q.Struct CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K) {f e : ℕ} (hf : 1 ≤ f) (hfe : f = 2 * e)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ f))
  (hδ : ∀ c, δ c = c ^ 2 ^ (3 * e))

include hf hfe hK hσ hδ in
theorem isSylowTwoOf_Tg_Ng {Kb : Subgroup (MulAut (Cm σ))}
    (hinn : (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ Kb) {S2 : Subgroup (K ≃+* K)}
    (hS2 : IsSylowTwoOf S2 (Kb.map (theta σ hf hK hσ))) {T : Subgroup (MulAut (Cm σ))}
    (hT : ∀ α : MulAut (Cm σ), α ∈ T ↔ ∃ u ∈ Ust σ, ∃ δ' ∈ S2, α = MulAut.conj u *
      fieldActor σ δ') (P : Subgroup (Cm σ)) (hUP : Ust σ ≤ P)
    (hPself : Subgroup.normalizer (P : Set (Cm σ)) = P)
    (hPstab : ∀ δ' : K ≃+* K, (fieldActor σ δ' : MulAut (Cm σ)) ∈ autStab P) :
    IsSylowTwoOf (Tg σ δ T) (Ng σ δ Kb P) := by
  have hf' := hf
  subst hfe
  have he : 1 ≤ e := by omega
  have : Finite (Cm σ) := inferInstance
  have : Finite (MulAut (Cm σ)) :=
    Finite.of_injective (fun φ : MulAut (Cm σ) => (φ : Cm σ → Cm σ)) fun a b h =>
      MulEquiv.ext (congrFun h)
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun φ : K ≃+* K => (φ : K → K)) fun a b h => RingEquiv.ext (congrFun h)
  have hUg := card_Ug σ δ he hK hσ hδ
  have hJ := isSylowTwoOf_Ug_Jfix σ δ he hK hσ hδ
  have hTN : Tg σ δ T ≤ Ng σ δ Kb P := by
    intro α hα
    obtain ⟨u, hu, δ', hδ', rfl⟩ := (mem_Tg_iff σ δ hT α).1 hα
    refine ⟨⟨(conj_mul_fieldActor_mem_iff σ hf' hK hσ hinn u δ').2 (hS2.1 hδ'), ?_⟩, hα.2⟩
    exact (autStab P).mul_mem ((conj_mem_autStab_iff P u).2 (by rw [hPself]; exact hUP hu.1))
      (hPstab δ')
  have hcT := card_Tg σ δ hf' hK hσ hT
  have hcN := card_Ng σ δ hf' hK hσ Kb P hinn hPself hPstab
  have hUgPJ : IsSylowTwoOf (Ug σ δ) (P ⊓ Jfix σ δ) :=
    isSylowTwoOf_of_le_of_le hJ (le_inf (inf_le_left.trans hUP) (Ug_le_Jfix σ δ)) inf_le_right
  have h1 := Subgroup.relIndex_mul_card (Ug σ δ) (P ⊓ Jfix σ δ)
  rw [inf_of_le_left hUgPJ.1] at h1
  have h2 := Subgroup.relIndex_mul_card S2 (Kb.map (theta σ hf' hK hσ))
  rw [inf_of_le_left hS2.1] at h2
  obtain ⟨k, hk⟩ := hS2.2.1.exists_card_eq
  refine isSylowTwoOf_of_card hTN ?_ (m := (Ug σ δ).relIndex (P ⊓ Jfix σ δ) *
    S2.relIndex (Kb.map (theta σ hf' hK hσ))) ?_ ?_
  · refine IsPGroup.of_card (n := 12 * e + k) ?_
    rw [hcT, hUg, hk, ← pow_mul, ← pow_add]
    ring_nf
  · intro hdvd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hdvd with h | h
    · exact hUgPJ.2.2 h
    · exact hS2.2.2 h
  · rw [hcN, hcT, ← h1, ← h2]
    ring

end CFSG.Quasithin.H13.F431.D4q.Out
