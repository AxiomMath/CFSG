module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515cd
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T516.KGroup
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T516.KUp
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T516.PartA

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T516

open AChief SolQuot

theorem card_lt_of_ne {Γ : Type u} [Group Γ] [Finite Γ] {T G : Subgroup Γ} (hle : T ≤ G)
    (hne : T ≠ G) : Nat.card T < Nat.card G :=
  lt_of_le_of_ne (Subgroup.card_le_of_le hle) fun heq =>
    hne (Subgroup.eq_of_le_of_card_ge hle heq.ge)

theorem normalizer_nsOf_of_kOf_eq_self (n : ℕ) :
    ∀ {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {A G X : Subgroup Γ}, Nat.card G = n →
      KSetting p A G → IsDAInvariant A G X → kOf X = X →
      X ≤ Subgroup.normalizer (nsOf p A G : Set Γ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Γ _ _ p A G X hn h hX hK
  by_cases hex : ∃ N ∈ nsSet p A G, N ≠ ⊥ ∧ G ≤ Subgroup.normalizer (N : Set Γ)
  ·
    obtain ⟨N, hN, hne, hG⟩ := hex
    have hA : A ≤ nrm N := hN.2.2.1
    have hih := ih _ (hn ▸ card_qimg_lt hN.1 hG hne) rfl (kSetting_qimg h hG)
      (isDAInvariant_qimg h hG hA hX) (kOf_qimg_eq_self (hX.1.trans hG) hK)
    rw [← nsOf_qimg h hG hA hN] at hih
    exact (qimg_le_normalizer_iff (nsOf_le p A G) (inf_le_right.trans (le_nsOf hN)) hG
      hX.1).mp hih
  · have hbot : ∀ N ∈ nsSet p A G, G ≤ Subgroup.normalizer (N : Set Γ) → N = ⊥ :=
      fun N hN hnorm => by_contra fun hne => hex ⟨N, hN, hne, hnorm⟩
    have hsol : sol G = ⊥ := hbot _ (sol_mem_nsSet h) (le_nrm_sol G)
    by_cases hM : mcalA G A = ∅
    · have hG : G = ⊥ := eq_bot_of_mcalA_eq_empty h hM hbot
      have hX0 : X = ⊥ := le_bot_iff.mp (hX.1.trans hG.le)
      rw [hX0]
      exact bot_le
    ·
      have hTDA : IsDAInvariant A G (kDown G A) := isDAInvariant_kDown h hsol
      have hTle : kDown G A ≤ G := kDown_le G A
      have hns : nsOf p A G ≤ kDown G A := iSup₂_le fun Y hY =>
        theorem_5_15_a h (isDAInvariant_of_mem_nsSet hY) hY.2.2.2.2.2
      have hTne : kDown G A ≠ G := fun heq => hM (mcalA_eq_empty_of_kDown_eq_self heq)
      have hTset : KSetting p A (kDown G A) :=
        ⟨h.prime, h.elemAbelian, hTDA.2.2,
          CFSG.SignalizerFunctor.Helpers.mcBrideHypothesisB_of_le p hTle h.hypB⟩
      have hpair := isDirectPair_kDown_kUp (A := A) hsol
      have hXW : X ≤ kDown G A ⊔ kUp G A := by
        intro x hx
        obtain ⟨y, hy, z, hz, rfl⟩ := theorem_5_15_d h hX hK x hx
        exact mul_mem (Subgroup.mem_sup_right hy) (Subgroup.mem_sup_left hz)
      have hXsDA : IsDAInvariant A (kDown G A) (proj (kDown G A) (kUp G A) X) := by
        refine ⟨proj_le_left _ _ _, fun d hd => ?_, fun a ha => ?_⟩
        · have hdG : d ∈ G ⊓ Subgroup.centralizer (A : Set Γ) := ⟨hTle hd.1, hd.2⟩
          exact mem_normalizer_proj_of_normalizes hpair.commute (Subgroup.le_normalizer hd.1)
            (mem_normalizer_kUp hsol (Subgroup.le_normalizer hdG.1)
              (Subgroup.centralizer_le_normalizer (A : Set Γ) hd.2)) (hX.2.1 hdG)
        · exact mem_normalizer_proj_of_normalizes hpair.commute (hTDA.2.2 ha)
            (mem_normalizer_kUp hsol (h.normalizes ha) (Subgroup.le_normalizer ha)) (hX.2.2 ha)
      have hih := ih _ (hn ▸ card_lt_of_ne hTle hTne) rfl hTset hXsDA
        (kOf_proj_eq_self hpair hXW hK)
      rw [nsOf_eq_of_le h hTDA hns] at hih
      intro x hx
      obtain ⟨l, hl, hzl⟩ := pairProj_spec hpair ⟨x, hXW hx⟩
      have hzXs : ((pairProj hpair ⟨x, hXW hx⟩ : kDown G A) : Γ) ∈
          proj (kDown G A) (kUp G A) X :=
        (mem_proj_iff hpair.commute).mpr ⟨(pairProj hpair ⟨x, hXW hx⟩).2, l, hl, by
          rw [hzl]
          exact hx⟩
      have hlN : l ∈ Subgroup.normalizer (nsOf p A G : Set Γ) := by
        refine Subgroup.centralizer_le_normalizer (nsOf p A G : Set Γ) ?_
        rw [Subgroup.mem_centralizer_iff]
        exact fun m hm => mul_comm_of_mem_kDown hsol (hns hm) hl
      have hx' : x = ((pairProj hpair ⟨x, hXW hx⟩ : kDown G A) : Γ) * l := hzl.symm
      rw [hx']
      exact mul_mem (hih hzXs) hlN

theorem normalizer_nsOf
    {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {A G X : Subgroup Γ}
    (h : KSetting p A G) (hX : IsDAInvariant A G X) (hK : kOf X = X) :
    X ≤ Subgroup.normalizer (nsOf p A G : Set Γ) :=
  normalizer_nsOf_of_kOf_eq_self _ rfl h hX hK

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T516
