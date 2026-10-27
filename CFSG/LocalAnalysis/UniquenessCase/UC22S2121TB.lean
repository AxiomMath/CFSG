module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213TDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229N
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22wj
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ud
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UsePair
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214h
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213b
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213Tb
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213Tc
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213Td
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213c
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Ui
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xl
import CFSG.Adapters.StatedPSLTwo
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214e2
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_21TB (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, c.B ≠ ⊥ → Hyp2120 D c → ∀ p ∈ D.sig,
    Hinf D.M = Opp p (oTwoEOf D.M) ∧
    ∃ n : ℕ,
      (IsL2Square (Bar2 (Opp p (oTwoEOf D.M))) n ∨
        ∃ (A B : Type) (_ : Group A) (_ : Group B),
          Nonempty (Bar2 (Opp p (oTwoEOf D.M)) ≃* A × B) ∧ IsU3 A n ∧ IsL2 B n) ∧
      IsPowTwo n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] ∧ ∀ r ∈ piSet c.B, r ∣ 2 ^ n - 1

theorem uc22p2213t_of_hyp2120TB (D : Data G) (Ch : Choice2011 G) (h21 : S21_21TB D Ch)
    (hV : S22_V D Ch) (h1930 : H1930 D) (c : Ctx22b D Ch) (hn : 2 ≤ c.n)
    (hH : Hyp2120 D { c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl }) {p : ℕ}
    (hp : p ∈ D.sig) : ∃ (K : Subgroup G) (n : ℕ), K2213 D c p K n := by
  obtain ⟨hinf, n, hsh, hpow, hcong, -⟩ :=
    h21 h1930 _ (uc22s13xl_B0_ne_bot c.toCtx21 hn) hH p hp
  have hex : ∃ (A B : Type) (_ : Group A) (_ : Group B),
      Nonempty (Bar2 (Hinf D.M) ≃* A × B) ∧ (IsL2 A n ∨ IsU3 A n) ∧ IsL2 B n := by
    rw [hinf]
    rcases hsh with ⟨A, B, _, _, he, hA, hB⟩ | ⟨A, B, _, _, he, hA, hB⟩
    · exact ⟨A, B, _, _, he, Or.inl hA, hB⟩
    · exact ⟨A, B, _, _, he, Or.inr hA, hB⟩
  obtain ⟨A, B, _, _, ⟨e⟩, hA, hB⟩ := hex
  have hpn : p ∣ 2 ^ n + 1 := by
    have h := hcong.symm.dvd
    rw [sub_neg_eq_add] at h
    exact_mod_cast h
  obtain ⟨K, hK, hKV, hKs⟩ := uc22p2213t_exists_not_le_centralizer D Ch hV h1930 c hp hpn e hA hB
  haveI : IsSimpleGroup (Bar2 K) := hKs.elim
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_PSU3
    CFSG.Blueprint.LieModel.isSimpleGroup_psl_two
  obtain ⟨eK⟩ := uc22p2213c_bar2_equiv D hV h1930 c hK hKV
  refine ⟨K, n, hK, Or.inr (Or.inl hcong), Or.inr (Or.inr (Or.inr ⟨hH, ?_, hpow⟩))⟩
  rcases hKs with h | h
  · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv eK h)
  · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv eK h)

theorem uc22p2214_clause4TB (D : Data G) (Ch : Choice2011 G) (h2121 : S21_21TB D Ch)
    (h1930 : H1930 D) (c : Ctx22b D Ch) {p : ℕ} (hp : p ∈ D.sig) {n : ℕ}
    (hH : Hyp2120 D { c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl }) (hpow : IsPowTwo n)
    (hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) : c.n ≤ n := by
  have hn1 : 0 < n := by
    obtain ⟨k, rfl⟩ := hpow
    exact Nat.two_pow_pos k
  rcases Nat.lt_or_ge c.n 2 with hlt | hn2
  · omega
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  obtain ⟨-, n', -, hpow', hpn', hrB⟩ :=
    h2121 h1930 _ (uc22s13xl_B0_ne_bot c.toCtx21 hn2) hH p hp
  have hnn : n = n' := uc22p2214_eq_of_isPowTwo hpP hp2 hpow hpow' hpn hpn'
  subst hnn
  have hdvd : c.n ∣ n := by
    refine uc22p22i_dvd_of_forall_prime (by omega) fun r hr hrm => hrB r ?_
    show r ∈ piSet c.B0
    rw [c.hpi]
    exact ⟨hr, hrm⟩
  exact Nat.le_of_dvd hn1 hdvd

theorem uc22p2214_s22_14_ofTBN (D : Data G) (Ch : Choice2011 G)
    (h869N : F08.R869N D) (h17 : S21_17 D Ch) (hn : SpU3NotList D) (hJ : J1NotSp4SU3)
    (hJL : J1NotL2Sz) (hJ1 : uc22p22d_J1Nontrivial) (h8 : S22_8 D Ch)
    (hSg : UC6S846.SigmaStd D) (hV : S22_V D Ch) (hn3 : ∀ c : Ctx22b D Ch, 3 ≤ c.n)
    (h846 : F08.R846 D) (h2121 : S21_21TB D Ch) : S22_14 D Ch := by
  intro h1930 c p hp K n hK
  obtain ⟨hKC, hpre, hcl⟩ := hK
  have hmain : ((IsSp4 ↥(mbarImage D.M c.V K) n ∧ Odd n) ∨
      (IsSU3 ↥(mbarImage D.M c.V K) n ∧ n ≡ 1 [MOD 6]) ∨
      ((IsL2 ↥(mbarImage D.M c.V K) n ∨ IsSz ↥(mbarImage D.M c.V K) n) ∧
        (conjSetOf D.M K).ncard = 2)) → c.n ≤ n := fun hcl' => by
    obtain ⟨hKV, -, -, hfix, hthin⟩ := uc22p2214_case_data D Ch h17 hn hV h1930 c hKC hcl'
    exact uc22p2214_s22_14_main_faith D Ch h17 hn hJ hJL h8 hSg hV hn3 h846 h1930 c hp hKC hpre
      hcl' fun _ hb hb1 =>
        uc22p2214_faith_of_R869N D Ch h869N hV h1930 c hKC hKV hthin hfix hb hb1
  rcases hcl with ⟨hsp, hodd, -⟩ | ⟨hsu, hmod⟩ | ⟨⟨-, hLS⟩ | ⟨hJK, hn3'⟩, hc2⟩ | ⟨hH, -, hpow⟩
  · exact hmain (Or.inl ⟨hsp, hodd⟩)
  · exact hmain (Or.inr (Or.inl ⟨hsu, hmod⟩))
  · exact hmain (Or.inr (Or.inr ⟨hLS, hc2⟩))
  · exact uc22p2214_j1 D Ch h17 hJ hJL hV h1930 c hKC hJK hJ1 hn3' hc2
  · have hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] := by
      rcases hpre with ⟨-, rfl, -, -⟩ | h | ⟨hSz, -⟩
      · exact absurd hpow (uc22p22a_not_isPowTwo_of_odd (by decide) (by decide))
      · exact h
      · obtain ⟨-, -, -, -, hodd', h3⟩ := CFSG.Blueprint.LieModel.admissible hSz
        exact absurd hpow (uc22p22a_not_isPowTwo_of_odd hodd' (by omega))
    exact uc22p2214_clause4TB D Ch h2121 h1930 c hp hH hpow hpn

end CFSG.LocalAnalysis.UniquenessCase.UC22
