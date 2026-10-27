module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2122NPGen
import CFSG.LocalAnalysis.UniquenessCase.UC22S2122NPJ2
import CFSG.LocalAnalysis.UniquenessCase.UC22S2122NPJ3
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4Exc
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFiveStrong
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VJ1
import CFSG.GroupTheory.PElementSubgroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22s2122np_false_of_J1 {D : Data G} {Ch : Choice2011 G}
    (h211 : S21_1 D Ch) (h1930 : H1930 D) (c : Ctx21 D Ch)
    {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M)
    (hL0 : c.L0 ≤ H₁ ⊓ H₂)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    {L : Subgroup G} (hL : L ∈ calC D.M) (h2 : (conjSetOf D.M L).ncard = 2)
    (hJ1 : IsJ1 (Bar2 L)) (hn3 : c.n = 3) (hOpp : conjClosure D.M L = Opp 7 D.M)
    (hU : ∀ A : Subgroup G, A ≤ L → Nat.card A = 7 → A ∈ uniqueSet D.M) : False := by
  classical
  have h7pi : 7 ∈ piSet c.B0 := by
    rw [c.hpi, hn3]
    exact ⟨by norm_num, by norm_num⟩
  obtain ⟨b0, hbo⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) 7 h7pi.2
  let b : G := (b0 : G)
  have hbo' : orderOf b = 7 := by
    show orderOf ((b0 : c.B0) : G) = 7
    rw [Subgroup.orderOf_coe, hbo]
  have hb7 : b ^ 7 = 1 := by
    rw [← hbo']
    exact pow_orderOf_eq_one b
  have hb1 : b ≠ 1 := by
    intro h
    have h1 : orderOf b = 1 := orderOf_eq_one_iff.mpr h
    omega
  have hbL0 : b ∈ c.L0 := c.hB0.1 b0.2
  have hbT : b ∈ normalizer (D.T : Set G) :=
    Ctx21.B0_le_normalizer c (by rw [hn3]; decide) b0.2
  have hbM : b ∈ D.M := c.hBM b0.2
  have hbOpp : b ∈ Opp 7 D.M := by
    have hz : IsPGroup 7 (Subgroup.zpowers b) := by
      refine IsPGroup.of_card_dvd_pow (n := 1) ?_
      simp [Nat.card_zpowers, hbo']
    exact le_pElementSubgroup_of_isPGroup (by norm_num) hz (Subgroup.zpowers_le.mpr hbM)
      (Subgroup.mem_zpowers b)
  have hbK : b ∈ conjClosure D.M L := by simpa [hOpp] using hbOpp
  obtain ⟨K, hKne, hset, hKC⟩ := uc22s21ru4e_exists_second_member h2 hL
  have hKmem : K ∈ conjSetOf D.M L := by
    rw [hset]
    simp
  have hJ1K : IsJ1 (Bar2 K) := uc22s217v_isJ1_of_mem hJ1 hKmem
  obtain ⟨hclosure, -⟩ := uc22s21ru4e_conjClosure_eq_sup_mul hset hL hKC hKne
  obtain ⟨Ē, hĒcard, hĒT, hbĒ, hĒL⟩ :=
    uc22s2122np_exists_barE_of_pair hL hKC hKne.symm hJ1 hJ1K hclosure hbM hbT hbK hb7
  obtain ⟨E, hEM, hEp, hEcard, hET, hbE, X, hXE, hXcard, hXU⟩ :=
    uc22s2122np_exists_E_of_barE hL hU hĒcard hĒT hbM hb7 hbĒ hĒL
  exact uc22s2122np_false_of_permutes h211 h1930 c hH₁ hH₂ hL0 hfX (p := 7)
    (by norm_num) (by norm_num) hEM hEp (by rw [hEcard]; norm_num) hET hbE hbL0 hb1
    hXE hXcard hXU

end CFSG.LocalAnalysis.UniquenessCase.UC22
