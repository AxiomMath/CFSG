module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105In
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporK105InThompson
import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporOdd
import CFSG.LocalAnalysis.UniquenessCase.UCFront10Alt
import CFSG.Sporadic.Th.Max3.Rank
import CFSG.Sporadic.Th.Max3.AllConjFinal
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Sporadic.Th.Max3.Quotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG CFSG.QuasithinUnique Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3

theorem k105SporAt_Th :
    K105SporAt .Th := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCz : centralizer ({z} : Set J) = M := by
    rw [z_eq_a]
    exact centralizer_a_eq_M_kernel
  obtain ⟨P, hQP⟩ := AltQuot.isPGroup_Q_subgroupOf_M.exists_le_sylow
  obtain ⟨T, hTdef⟩ : ∃ T : Subgroup J, T = (P : Subgroup ↥M).map M.subtype := ⟨_, rfl⟩
  have hTM : T ≤ M := hTdef ▸ Subgroup.map_subtype_le _
  have hQT : Q ≤ T := by
    have h := Subgroup.map_mono (f := M.subtype) hQP
    rwa [Subgroup.map_subgroupOf_eq_of_le Q_le_M, ← hTdef] at h
  have hTp : IsPGroup 2 T := hTdef ▸ P.isPGroup'.map _
  have hT : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hTp, ?_⟩
    change ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right, hTdef, Subgroup.index_map_subtype]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
    · exact P.not_dvd_index h
    · have hMi := Subgroup.card_mul_index M
      rw [card_M, natCard_J] at hMi
      omega
  have hzT : z ∈ T := hQT z_mem_Q
  have hz : z ∈ CFSG.Open.quasithinOmegaOneCenter T := by
    unfold CFSG.Open.quasithinOmegaOneCenter
    refine Subgroup.subset_closure ⟨Subgroup.mem_inf.2 ⟨hzT, ?_⟩, ?_⟩
    · exact Subgroup.mem_centralizer_iff.2 fun t ht => (commute_z_of_mem_M (hTM ht)).symm.eq
    · rw [sq]
      exact z_mul_self
  have hZ : ∀ w ∈ centralizer (Q : Set J) ⊓ M, w = 1 ∨ w = z := fun w hw => by
    rw [centralizer_Q_inf_M] at hw
    exact Rank.eq_one_or_eq_z hw
  have hZT : ∀ t ∈ T, (∀ s ∈ T, s * t = t * s) → t = 1 ∨ t = z := fun t ht hc =>
    hZ t (Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun s hs => hc s (hQT hs), hTM ht⟩)
  have hC : K105In (centralizer {z}) T := by
    rw [hCz]
    refine k105In_of_quotient hT hTM (Q.subgroupOf M) ?_ kappa
      fun S H hS hSH _ h3 => le_of_isSylowTwoOf_of_not_three_dvd_alt (by norm_num)
        (MulEquiv.refl _) hS hSH h3
    rw [Subgroup.map_subgroupOf_eq_of_le Q_le_M]
    exact hQT
  have hJT : CFSG.Quasithin.thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hQJ : Q ≤ CFSG.Quasithin.thompsonJ T :=
    le_thompsonJ_of_rank (m := 5) hQT
      (fun A hA hEA => (Rank.card_le_of_le_M (hA.trans hTM) hEA).trans (by norm_num))
      Rank.le_iSup_card_eq
  have hCQ : centralizer (Q : Set J) ≤ Q := fun w hwc => by
    have hwz : w ∈ centralizer ({z} : Set J) :=
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hwc z z_mem_Q).symm
    rw [hCz] at hwz
    rcases hZ w (Subgroup.mem_inf.2 ⟨hwc, hwz⟩) with rfl | rfl
    · exact Q.one_mem
    · exact z_mem_Q
  have hJ : K105In (normalizer (CFSG.Quasithin.thompsonJ T : Set J)) T :=
    hC.mono (normalizer_le_centralizer_of_le (hTp.to_le hJT) hQJ hCQ
      fun w hwQ hwc => hZ w (Subgroup.mem_inf.2 ⟨hwc, Q_le_M hwQ⟩))
  have hT15 : 2 ^ 15 ∣ Nat.card T := by
    rw [hTdef, Subgroup.card_map_of_injective M.subtype_injective]
    exact P.pow_dvd_card_of_pow_dvd_card (by rw [card_M]; norm_num)
  have hodd : ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ A : Subgroup J, CFSG.Open.IsElemAbelian p A →
      A ≠ ⊥ → T ≤ normalizer (A : Set J) → A ⊓ centralizer {z} ≠ ⊥ := by
    intro p hp hp5 A hA hA1 hTA hAz
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hn⟩ := hA.isPGroup.exists_card_eq
    have h2 : 2 ^ 15 ∣ Nat.card (GL (Fin n) (ZMod p)) := hT15.trans
      (card_dvd_card_GL_of_inf_centralizer_eq_bot hp (by omega) hTp hzT z_mul_self hZT hA hn hA1
        hTA hAz)
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hA1 (Subgroup.card_eq_one.1 (by rw [hn, pow_zero]))
    have hfac : (90745943887872000 : ℕ) = 2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31 := by
      norm_num
    have hdvdJ : p ^ n ∣ 2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31 := by
      rw [← hfac, ← natCard_J, ← hn]
      exact Subgroup.card_subgroup_dvd_card A
    have hpq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq h =>
      (Nat.prime_dvd_prime_iff_eq hp hq).1 h
    have hp' : p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 19 ∨ p = 31 := by
      rcases (Nat.Prime.dvd_mul hp).1 ((dvd_pow_self p hn0).trans hdvdJ) with h | h31
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h19
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h13
          · rcases (Nat.Prime.dvd_mul hp).1 h with h | h7
            · rcases (Nat.Prime.dvd_mul hp).1 h with h | h5
              · rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h3
                · have := hpq 2 Nat.prime_two (hp.dvd_of_dvd_pow h2)
                  omega
                · have := hpq 3 Nat.prime_three (hp.dvd_of_dvd_pow h3)
                  omega
              · exact Or.inl (hpq 5 (by norm_num) (hp.dvd_of_dvd_pow h5))
            · exact Or.inr (Or.inl (hpq 7 (by norm_num) (hp.dvd_of_dvd_pow h7)))
          · exact Or.inr (Or.inr (Or.inl (hpq 13 (by norm_num) h13)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (hpq 19 (by norm_num) h19))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (hpq 31 (by norm_num) h31))))
    have hle : ∀ k : ℕ, ¬ p ^ (k + 1) ∣ 2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31 →
        n ≤ k := fun k hk => by
      by_contra h
      exact hk ((pow_dvd_pow p (by omega)).trans hdvdJ)
    rcases hp' with rfl | rfl | rfl | rfl | rfl
    · have hn3 := hle 3 (by norm_num)
      interval_cases n <;> rw [Matrix.card_GL_field] at h2 <;>
        norm_num [ZMod.card, Fin.prod_univ_succ] at h2
    · have hn2 := hle 2 (by norm_num)
      interval_cases n <;> rw [Matrix.card_GL_field] at h2 <;>
        norm_num [ZMod.card, Fin.prod_univ_succ] at h2
    · have hn1 := hle 1 (by norm_num)
      interval_cases n <;> rw [Matrix.card_GL_field] at h2 <;>
        norm_num [ZMod.card, Fin.prod_univ_succ] at h2
    · have hn1 := hle 1 (by norm_num)
      interval_cases n <;> rw [Matrix.card_GL_field] at h2 <;>
        norm_num [ZMod.card, Fin.prod_univ_succ] at h2
    · have hn1 := hle 1 (by norm_num)
      interval_cases n <;> rw [Matrix.card_GL_field] at h2 <;>
        norm_num [ZMod.card, Fin.prod_univ_succ] at h2
  exact k105SporAt_of_k105In hT (k105In_top_of_thompson hT hz hC hJ hodd) thEquivJ

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
