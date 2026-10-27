module

public import Certificates.Data.Fi22Twist
import Certificates.Kernel.Fi22Twist.CentClosed
import Certificates.Kernel.Fi22Twist.DjFacts
import Certificates.Kernel.Fi22Twist.CtFacts

public section

namespace Certificates

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.RankThree.Native
  CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative

structure Fi22TwistFacts : Prop where
  qk_le : ∀ k < 3, Subgroup.closure (permsA 3510 (qGens k)) ≤ fi22P
  qk_card : ∀ k < 3, Nat.card (Subgroup.closure (permsA 3510 (qGens k))) = [27, 81, 729][k]!
  qk_le_cent : ∀ k < 3, Subgroup.closure (permsA 3510 (qGens k)) ≤
    Subgroup.centralizer {permOfArr 3510 (tArr k)}
  dj_le : ∀ j < 5, Subgroup.closure
    {permOfArr 3510 (repX j), permOfArr 3510 (repY j), permOfArr 3510 (repZ j)} ≤ fi22P
  dj_card : ∀ j < 5, Nat.card (Subgroup.closure
    {permOfArr 3510 (repX j), permOfArr 3510 (repY j), permOfArr 3510 (repZ j)}) = 27
  e27_conj : ∀ k < 3, ∀ E : Subgroup (Equiv.Perm (Fin 3510)),
    E ≤ Subgroup.closure (permsA 3510 (qGens k)) → Nat.card E = 27 →
    (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → (∀ a ∈ E, a ^ 3 = 1) →
    ∃ g ∈ fi22P, ∃ j < 5, ∀ x ∈ E, g * x * g⁻¹ ∈ Subgroup.closure
      {permOfArr 3510 (repX j), permOfArr 3510 (repY j), permOfArr 3510 (repZ j)}
  cent_closed : ∀ j < 5,
    ∀ a ∈ fi22P ⊓ Subgroup.centralizer (Subgroup.closure
      {permOfArr 3510 (repX j), permOfArr 3510 (repY j), permOfArr 3510 (repZ j)} :
        Set (Equiv.Perm (Fin 3510))),
    ∀ b ∈ fi22P ⊓ Subgroup.centralizer (Subgroup.closure
      {permOfArr 3510 (repX j), permOfArr 3510 (repY j), permOfArr 3510 (repZ j)} :
        Set (Equiv.Perm (Fin 3510))),
    (∃ m, a ^ 3 ^ m = 1) → (∃ m, b ^ 3 ^ m = 1) → ∃ m, (a * b) ^ 3 ^ m = 1

end Certificates

public section

namespace Certificates

open CertificateChecks.KernelFi22Twist

theorem fi22TwistFacts : Certificates.Fi22TwistFacts where
  qk_le _ hk := qk_le_P hk
  qk_card k hk := by
    interval_cases k
    · exact q0_facts.1
    · exact q1_facts.1
    · exact q2_card
  qk_le_cent _ hk := qk_le_cent hk
  dj_le _ hj := dSub_le_P hj
  dj_card _ hj := dSub_card hj
  e27_conj k hk E hE hc hcomm hexp := by
    by_cases h2 : k = 2
    · subst h2
      obtain ⟨j, hj, g, hg, hx⟩ := q2_e27_conjP E hE hc hcomm hexp
      exact ⟨g, hg, j, hj, hx⟩
    · obtain ⟨g, hg, hx⟩ := q01_e27_conjP (k := k) (by omega) E hE hc hcomm hexp
      exact ⟨g, hg, k, by omega, hx⟩
  cent_closed _ hj := cent_closed hj

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.RankThree.Native
  CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative in
theorem certificate431009 : Fi22TwistFacts := fi22TwistFacts

end Certificates
