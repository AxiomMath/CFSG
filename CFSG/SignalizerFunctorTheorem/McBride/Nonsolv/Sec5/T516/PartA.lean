module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.CentralizerK
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T516.Quot
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T516.KDown

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T516

open AChief SolQuot

section Aux

variable {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {A G : Subgroup Γ}

theorem sol_mem_nsSet (h : KSetting p A G) : sol G ∈ nsSet p A G :=
  mem_nsSet_of_isDAInvariant h.elemAbelian
    (CFSG.SignalizerFunctor.Helpers.mcBrideHypothesisB_of_le p (sol_le G) h.hypB)
    ⟨sol_le G, inf_le_left.trans (le_nrm_sol G),
      h.normalizes.trans (normalizer_le_nrm_sol G)⟩
    (isSolvable_of_le inf_le_left (isSolvable_sol G))

theorem kOf_mem_nsSet (h : KSetting p A G) (hM : mcalA G A = ∅) : kOf G ∈ nsSet p A G :=
  mem_nsSet_of_isDAInvariant h.elemAbelian
    (CFSG.SignalizerFunctor.Helpers.mcBrideHypothesisB_of_le p (kOf_le G) h.hypB)
    ⟨kOf_le G, inf_le_left.trans (le_normalizer_kOf G),
      le_normalizer_kOf_of_le_normalizer h.normalizes⟩
    (isSolvable_inf_centralizer_kOf h hM)

theorem eq_bot_of_mcalA_eq_empty (h : KSetting p A G) (hM : mcalA G A = ∅)
    (hbot : ∀ N ∈ nsSet p A G, G ≤ Subgroup.normalizer (N : Set Γ) → N = ⊥) : G = ⊥ :=
  (kOf_eq_bot_iff G).mp (hbot _ (kOf_mem_nsSet h hM) (le_normalizer_kOf G))

end Aux

theorem isSolvable_inf_centralizer_of_nsOf_eq (n : ℕ) :
    ∀ {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {A G : Subgroup Γ}, Nat.card G = n →
      KSetting p A G → nsOf p A G = G →
      Group.IsSolvable ↥(G ⊓ Subgroup.centralizer (A : Set Γ)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Γ _ _ p A G hn h hns
  by_cases hex : ∃ N ∈ nsSet p A G, N ≠ ⊥ ∧ G ≤ Subgroup.normalizer (N : Set Γ)
  · obtain ⟨N, hN, hne, hG⟩ := hex
    have hA : A ≤ nrm N := hN.2.2.1
    have hcard : Nat.card (qimg N G) < n := hn ▸ card_qimg_lt hN.1 hG hne
    have hnsbar : nsOf p (qimg N A) (qimg N G) = qimg N G := by
      rw [← nsOf_qimg h hG hA hN, hns]
    have hsolbar := ih _ hcard rfl (kSetting_qimg h hG) hnsbar
    rw [← AChief.qimg_inf_centralizer h.prime h.elemAbelian h.normalizes hA hG h.hypB.2.1]
      at hsolbar
    have hk : Group.IsSolvable ↥((G ⊓ Subgroup.centralizer (A : Set Γ)) ⊓ N) :=
      isSolvable_of_le (fun x hx => Subgroup.mem_inf.mpr ⟨hx.2, hx.1.2⟩) hN.2.2.2.2.2
    exact (isSolvable_qimg_iff_of_inf hk (inf_le_left.trans hG)).mp hsolbar
  · have hbot : ∀ N ∈ nsSet p A G, G ≤ Subgroup.normalizer (N : Set Γ) → N = ⊥ :=
      fun N hN hnorm => by_contra fun hne => hex ⟨N, hN, hne, hnorm⟩
    have hkd : kDown G A = G := by
      refine le_antisymm (kDown_le G A) ?_
      conv_lhs => rw [← hns]
      exact iSup₂_le fun Y hY =>
        theorem_5_15_a h (isDAInvariant_of_mem_nsSet hY) hY.2.2.2.2.2
    have hG : G = ⊥ := eq_bot_of_mcalA_eq_empty h (mcalA_eq_empty_of_kDown_eq_self hkd) hbot
    rw [hG, bot_inf_eq]
    infer_instance

theorem nsOf_mem_nsSet
    {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {A G : Subgroup Γ}
    (h : KSetting p A G) : nsOf p A G ∈ nsSet p A G := by
  have hset : KSetting p A (nsOf p A G) :=
    ⟨h.prime, h.elemAbelian, le_normalizer_nsOf p A G,
      CFSG.SignalizerFunctor.Helpers.mcBrideHypothesisB_of_le p (nsOf_le p A G) h.hypB⟩
  have hns : nsOf p A (nsOf p A G) = nsOf p A G := by
    refine le_antisymm (nsOf_le p A _) (iSup₂_le fun Y hY => ?_)
    exact le_nsOf (mem_nsSet_of_le (nsOf_le p A G) hY (le_nsOf hY))
  exact nsOf_mem_nsSet_of_isSolvable h (isSolvable_inf_centralizer_of_nsOf_eq _ rfl hset hns)

theorem nsOf_eq_of_le
    {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {A G T : Subgroup Γ}
    (h : KSetting p A G) (hT : IsDAInvariant A G T) (hle : nsOf p A G ≤ T) :
    nsOf p A T = nsOf p A G := by
  have hset : KSetting p A T :=
    ⟨h.prime, h.elemAbelian, hT.2.2,
      CFSG.SignalizerFunctor.Helpers.mcBrideHypothesisB_of_le p hT.1 h.hypB⟩
  refine le_antisymm ?_ (iSup₂_le fun Y hY =>
    le_nsOf (mem_nsSet_of_le hT.1 hY ((le_nsOf hY).trans hle)))
  have hmem : nsOf p A T ∈ nsSet p A T := nsOf_mem_nsSet hset
  have hDN : G ⊓ Subgroup.centralizer (A : Set Γ) ≤ Subgroup.normalizer (nsOf p A T : Set Γ) := by
    intro d hd
    have e : nsOf p A T = sSup (nsSet p A T) := sSup_eq_iSup.symm
    rw [e]
    exact L514.mem_normalizer_sSup (fun J hJ => map_conj_mem_nsSet hT hd hJ)
      (fun J hJ => map_conj_mem_nsSet hT (inv_mem hd) hJ)
  exact le_nsOf ⟨(nsOf_le p A T).trans hT.1, hDN, le_normalizer_nsOf p A T, hmem.2.2.2⟩

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T516
