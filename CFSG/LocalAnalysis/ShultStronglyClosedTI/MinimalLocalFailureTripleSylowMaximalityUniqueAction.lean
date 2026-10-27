module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityAlgebra
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityPointTransport

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TripleSylowMaximality

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.OrderReductions.InvolutionGraph CFSG.OrderReductions.StrongEmbedding
open CFSG.OrderReductions.UniqueInvolutionAction

universe u v

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem unique_fixed_of_right_conjugate
    {Ω : Type v} [MulAction G Ω] {z x g : G}
    (hz : ∃! alpha : Ω, z • alpha = alpha)
    (hx : rightConjugateElem z g = x) :
    ∃! alpha : Ω, x • alpha = alpha := by
  obtain ⟨alpha, hza, huniq⟩ := hz
  have hconj : g⁻¹ * z * g = x := hx
  refine ⟨g⁻¹ • alpha, ?_, ?_⟩
  · rw [← hconj]
    simp only [mul_smul, smul_inv_smul, hza]
  · intro omega hfix
    have hzfix : z • (g • omega) = g • omega := by
      have h := congrArg (fun a : Ω => g • a) hfix
      rw [← hconj] at h
      simpa only [mul_smul, smul_inv_smul] using h
    have heq := huniq (g • omega) hzfix
    simpa only [inv_smul_smul] using congrArg (fun a : Ω => g⁻¹ • a) heq

theorem normal_join_all_involutions_unique_fixed
    {Ω : Type v} [MulAction G Ω]
    (L R : Subgroup G) [L.Normal] {p : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hRp : IsPGroup p R)
    (A : Subgroup L) (hA : IsStronglyEmbedded A)
    (z : L) (hz : orderOf z = 2)
    (hzunique : ∃! alpha : Ω, (z : G) • alpha = alpha) :
    ∀ x : Involution (L ⊔ R : Subgroup G),
      ∃! alpha : Ω, x.val • alpha = alpha := by
  intro x
  have hxL := normal_join_odd_prime_involution_mem L R hp hpodd hRp x.val x.property
  let xL : L := ⟨(x.val : G), hxL⟩
  have hxorder : orderOf xL = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact (Subgroup.orderOf_coe x.val).trans x.property
  have hzI : IsInvolution z := ⟨(orderOf_eq_prime_iff.mp hz).2,
    (orderOf_eq_prime_iff.mp hz).1⟩
  have hxI : IsInvolution xL := ⟨(orderOf_eq_prime_iff.mp hxorder).2,
    (orderOf_eq_prime_iff.mp hxorder).1⟩
  obtain ⟨g, hg⟩ := hA.involutions_conjugate hzI hxI
  have hgG : rightConjugateElem (z : G) (g : G) = (x.val : G) :=
    congrArg Subtype.val hg
  exact unique_fixed_of_right_conjugate (G := G) hzunique hgG

omit [Finite G] in
theorem normal_join_action_transitive
    {Ω : Type v} [MulAction G Ω] (L R : Subgroup G)
    (hLtrans : MulAction.IsPretransitive L Ω) :
    MulAction.IsPretransitive (L ⊔ R : Subgroup G) Ω := by
  constructor
  intro a b
  obtain ⟨l, hl⟩ := hLtrans.exists_smul_eq a b
  exact ⟨⟨l.val, (le_sup_left : L ≤ L ⊔ R) l.property⟩, hl⟩

theorem normal_join_stronglyEmbedded_double_transitive
    {Ω : Type v} [MulAction G Ω] [Finite Ω] [Nontrivial Ω]
    (L R : Subgroup G) [L.Normal] {p : ℕ} (hp : p.Prime)
    (hpodd : Odd p) (hRp : IsPGroup p R)
    (A : Subgroup L) (hA : IsStronglyEmbedded A)
    (hrank : TwoRankAtLeastTwo L)
    (hLtrans : MulAction.IsPretransitive L Ω)
    (z : L) (hz : orderOf z = 2)
    (hzunique : ∃! alpha : Ω, (z : G) • alpha = alpha)
    (alpha : Ω) :
    fusionStronglyEmbedded (MulAction.stabilizer (L ⊔ R : Subgroup G) alpha) ∧
      MulAction.IsMultiplyPretransitive (L ⊔ R : Subgroup G) Ω 2 := by
  let K := L ⊔ R
  let : MulAction.IsPretransitive K Ω := normal_join_action_transitive L R hLtrans
  let zK : K := ⟨z.val, (le_sup_left : L ≤ K) z.property⟩
  have hzK : orderOf zK = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact (Subgroup.orderOf_coe z).trans hz
  have heven : Even (Nat.card K) := even_iff_two_dvd.mpr (by
    rw [← hzK]
    exact orderOf_dvd_natCard zK)
  have hunique := normal_join_all_involutions_unique_fixed
    L R hp hpodd hRp A hA z hz hzunique
  have hstrong : fusionStronglyEmbedded (MulAction.stabilizer K alpha) :=
    (stronglyEmbedded_right_conjugate_iff _).mp
      (stronglyEmbedded_stabilizer_of_unique_fixed heven hunique alpha)
  have hKrank : TwoRankAtLeastTwo K := hrank.map_of_injective
    (Subgroup.inclusion (le_sup_left : L ≤ K)) (Subgroup.inclusion_injective _)
  exact ⟨hstrong, rank_two_stronglyEmbedded_action_double_transitive
    inferInstance alpha hstrong hKrank⟩

end CFSG.ShultStronglyClosedTI.TripleSylowMaximality
