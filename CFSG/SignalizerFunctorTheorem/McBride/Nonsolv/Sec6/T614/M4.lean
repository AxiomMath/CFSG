module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.M3

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E : Subgroup G}

theorem kOf_inf_thetaOf_eq
    (h : Counterexample p A θ) (S : Setting614 p A θ E)
    {B T : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) (hEB : E ⊓ B = ⊥)
    (hT : T ∈ signalizerFunctorEk p 2 A) (hET : E ⊓ T = ⊥) :
    kOf (thetaOf θ B) ⊓ thetaOf θ E = kOf (thetaOf θ T) ⊓ thetaOf θ E := by
  have key : ∀ B' : Subgroup G, B' ∈ signalizerFunctorEk p 2 A → E ⊓ B' = ⊥ → ∀ f ∈ B', f ≠ 1 →
      kOf (thetaOf θ B') ⊓ thetaOf θ E = kOf (θ f) ⊓ thetaOf θ A := by
    intro B' hB' hEB' f hf hf1
    obtain ⟨b', hb', hb'n, hbasis⟩ := h.exists_basis hB' hf hf1
    have hb'1 : b' ≠ 1 := fun e => hb'n (e ▸ one_mem _)
    have hK : kOf (θ f) ⊓ Subgroup.centralizer {b'} = kOf (thetaOf θ B') := by
      rw [h.kOf_apply_inf_centralizer_eq S hB' hEB' hf hb' hf1 hb'1 hb'n, hbasis]
    have hDA : thetaOf θ A ≤ thetaOf θ E := thetaOf_anti S.mem.1
    have hDc : thetaOf θ A ≤ Subgroup.centralizer {b'} :=
      (h.isFunctor.thetaOf_le_centralizer le_rfl).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (hB'.1 hb')))
    apply le_antisymm
    · rintro x ⟨hxK, hxE⟩
      have hxK' : x ∈ kOf (θ f) := by
        rw [← hK] at hxK
        exact hxK.1
      refine ⟨hxK', ?_⟩
      have hxB : x ∈ thetaOf θ B' ⊓ Subgroup.centralizer (E : Set G) :=
        ⟨kOf_le _ hxK, h.isFunctor.thetaOf_le_centralizer S.mem.1 hxE⟩
      have := h.thetaOf_inf_centralizer_le hB'.1 (h.ne_bot_of_mem_E2 hB') S.mem.1 hxB
      rwa [sup_comm, S.sup_eq h hB' hEB'] at this
    · rintro x ⟨hxK, hxD⟩
      refine ⟨?_, hDA hxD⟩
      rw [← hK]
      exact ⟨hxK, hDc hxD⟩
  by_cases hBT : B = T
  · rw [hBT]
  · obtain ⟨f, hf, hf1⟩ := h.exists_ne_one_of_mem_E1 (h.inf_mem_E1_of_ne_E2 hB hT hBT)
    rw [key B hB hEB f hf.1 hf1, key T hT hET f hf.2 hf1]

theorem wTilde_eq
    (h : Counterexample p A θ) (S : Setting614 p A θ E)
    {B T : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A) (hEB : E ⊓ B = ⊥)
    (hT : T ∈ signalizerFunctorEk p 2 A) (hET : E ⊓ T = ⊥) :
    wTilde θ E B = wTilde θ E T := by
  obtain ⟨-, hprojB, hdpB⟩ := h.wTilde_properties S hB hEB
  obtain ⟨-, hprojT, hdpT⟩ := h.wTilde_properties S hT hET
  have hX := h.kOf_inf_thetaOf_eq S hB hEB hT hET
  have e1 : {Y | ∃ J ∈ lcal (thetaOf θ E), Y = wTilde θ E B ⊓ jTilde (thetaOf θ E) J} =
      {Y | ∃ J ∈ lcal (thetaOf θ E), Y = projIn (jTilde (thetaOf θ E) '' lcal (thetaOf θ E))
        (jTilde (thetaOf θ E) J) (kOf (thetaOf θ B) ⊓ thetaOf θ E)} := by
    ext Y
    constructor
    · rintro ⟨J, hJ, rfl⟩
      exact ⟨J, hJ, hprojB J hJ⟩
    · rintro ⟨J, hJ, rfl⟩
      exact ⟨J, hJ, (hprojB J hJ).symm⟩
  have e2 : {Y | ∃ J ∈ lcal (thetaOf θ E), Y = wTilde θ E T ⊓ jTilde (thetaOf θ E) J} =
      {Y | ∃ J ∈ lcal (thetaOf θ E), Y = projIn (jTilde (thetaOf θ E) '' lcal (thetaOf θ E))
        (jTilde (thetaOf θ E) J) (kOf (thetaOf θ T) ⊓ thetaOf θ E)} := by
    ext Y
    constructor
    · rintro ⟨J, hJ, rfl⟩
      exact ⟨J, hJ, hprojT J hJ⟩
    · rintro ⟨J, hJ, rfl⟩
      exact ⟨J, hJ, (hprojT J hJ).symm⟩
  calc wTilde θ E B
      = sSup {Y | ∃ J ∈ lcal (thetaOf θ E), Y = wTilde θ E B ⊓ jTilde (thetaOf θ E) J} :=
        hdpB.sSup_eq.symm
    _ = sSup {Y | ∃ J ∈ lcal (thetaOf θ E), Y = projIn
        (jTilde (thetaOf θ E) '' lcal (thetaOf θ E)) (jTilde (thetaOf θ E) J)
          (kOf (thetaOf θ B) ⊓ thetaOf θ E)} := by rw [e1]
    _ = sSup {Y | ∃ J ∈ lcal (thetaOf θ E), Y = projIn
        (jTilde (thetaOf θ E) '' lcal (thetaOf θ E)) (jTilde (thetaOf θ E) J)
          (kOf (thetaOf θ T) ⊓ thetaOf θ E)} := by rw [hX]
    _ = sSup {Y | ∃ J ∈ lcal (thetaOf θ E), Y = wTilde θ E T ⊓ jTilde (thetaOf θ E) J} := by
        rw [e2]
    _ = wTilde θ E T := hdpT.sSup_eq

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
