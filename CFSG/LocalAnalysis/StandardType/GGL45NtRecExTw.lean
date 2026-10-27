module

public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTriDiag
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4Diag
public import CFSG.LocalAnalysis.StandardType.GGTriD4SchurHolds
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FieldFixReeModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggL45NtRecExTw_center_eq_bot_of_simple {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hnab : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center Q := by rw [h]; exact Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab

private theorem ggL45NtRecExTw_centerPrime_of_schur {p : ℕ} {R : Type} [Group R]
    (hp : p.Prime) (hZR : Subgroup.center R = ⊥)
    (hS : ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
      ∀ θ : X ⧸ Subgroup.center X ≃* R, Subgroup.center X = ⊥) :
    GGCenterPrime p R := by
  intro L' _ _ ψ hψ hker hperf hdvd
  have hZL : Subgroup.center L' ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have h1 : ψ z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [hZR, Subgroup.mem_bot] at h1
    exact h1
  have hkerZ : ψ.ker = Subgroup.center L' := le_antisymm hker hZL
  let e : L' ⧸ Subgroup.center L' ≃* R :=
    (QuotientGroup.quotientMulEquivOfEq hkerZ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have hzc : Subgroup.center L' = ⊥ := hS L' hperf e
  rw [hzc, Subgroup.card_bot] at hdvd
  exact hp.not_dvd_one hdvd

theorem ggL45NtRecOn_exTw :
    GGL45NtRecOn GGL45NtFamExTw := by
  intro p hp hp2 lab hlab hkg hS Q hQ
  obtain ⟨tag, rank, n⟩ := lab
  obtain ⟨-, htag⟩ := hS
  rcases htag with ht | ht
  ·
    subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    have hn : 1 ≤ n := hlab.1
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeTwisted] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ'⟩ := hQ
    refine ⟨K, hf, hfin, hK, hQ', ?_⟩
    intro hsimple hnab
    refine ⟨?_, ?_, ?_⟩
    ·
      intro r
      exact Subgroup.subset_closure (Or.inl ⟨r, rfl⟩)
    ·
      intro u hu _
      obtain ⟨r, hr⟩ := TableBExcSmallRest.chevIDImage_subset_inn_triD4 hn K hK hu
      exact ⟨r, hr.symm⟩
    ·
      exact ggL45NtRecExTw_centerPrime_of_schur hp
        (ggL45NtRecExTw_center_eq_bot_of_simple hnab)
        (ggTriD4SchurInput_holds n hn K hK hsimple)
  ·
    subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    obtain ⟨-, -, ⟨k, hk⟩, hn3⟩ := hlab
    have ha : 1 ≤ (n - 1) / 2 := by omega
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeTwF4] at hQ ⊢
    obtain ⟨K, hf, hfin, hK, hQ'⟩ := hQ
    haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := CFSG.StandardType.charP_two_of_card hK
    obtain ⟨eR⟩ := gff_nonempty_centerQuot_equiv_reeGamma (K := K) (a := (n - 1) / 2) ha hK
    have hZree :
        Subgroup.center (↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K ((n - 1) / 2))) = ⊥ :=
      CFSG.LieType.Ree.ReeTag.large_Ree_fixed_group_center_trivial ((n - 1) / 2) K hK
    let e : LargeEvenCenterQuot (LargeEvenTwF4H ((n - 1) / 2) K) ≃*
        LargeEvenCenterQuot (CFSG.LieType.Ree.ReeTag.F4.reeGamma K ((n - 1) / 2)) :=
      eR.trans (centerQuotEquivOfBot hZree).symm
    refine ⟨K, hf, hfin, hK, hQ', ?_⟩
    intro hsimple hnab
    refine ⟨?_, ?_, ?_⟩
    ·
      intro r
      exact Subgroup.subset_closure (Or.inl ⟨r, rfl⟩)
    ·
      intro u hu _
      obtain ⟨r, hr⟩ := chevIDImage_subset_inn_twF4 ha K hK hu
      exact ⟨r, hr.symm⟩
    ·
      refine ggL45NtRecExTw_centerPrime_of_schur hp
        (ggL45NtRecExTw_center_eq_bot_of_simple hnab) ?_
      intro X _ _ hperf θ
      exact gff_center_eq_bot_ree (K := K) (a := (n - 1) / 2) ha hK hperf (θ.trans e)

end CFSG.StandardType
