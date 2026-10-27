module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeNine

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nine3_comm_of_mem_omegaIn (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    {U : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) :
    ⁅nineI V K, U⁆ = U ⊓ pCoreOf 2 K := by
  obtain ⟨h, hh, hUh⟩ := hc.nineH_transitive hU
  have hhK : h ∈ K := Nine3Choice.nineH_le_K hh
  have h := congrArg (fun H : Subgroup G => conjSubgroup H h)
    (hI.comm A hc.core.A_mem_nineOmegaIn)
  rw [E3.conjSubgroup_commutator, E3.conjSubgroup_inf,
    Nine3Core.conjSubgroup_nineI hhK, Nine3Core.conjSubgroup_pCoreOf K hhK] at h
  simpa [hUh] using h

theorem nine3_relIndex_of_mem_omegaIn (hc : Nine3Choice V T A K S X p g x)
    {U : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) :
    (U ⊓ pCoreOf 2 K).relIndex U = 2 := by
  obtain ⟨h, hh, hUh⟩ := hc.nineH_transitive hU
  have hhK : h ∈ K := Nine3Choice.nineH_le_K hh
  have hbase : (pCoreOf 2 K).relIndex A = 2 :=
    nine_two_relIndex hc.core.hyp7 hc.core.rk_gt hc.core.hyp hc.core.A_mem_nineOmegaIn
  have hA : (A ⊓ pCoreOf 2 K).relIndex A = 2 := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact hbase
  have hmap := Subgroup.relIndex_map_map_of_injective (H := A ⊓ pCoreOf 2 K) (K := A)
    (f := (MulAut.conj h⁻¹).toMonoidHom) (MulAut.conj h⁻¹).injective
  have hleft : (conjSubgroup (A ⊓ pCoreOf 2 K) h).relIndex (conjSubgroup A h) =
      (A ⊓ pCoreOf 2 K).relIndex A := by
    simpa only [CFSG.Quasithin.conjSubgroup] using hmap
  rw [hUh, ← Nine3Core.conjSubgroup_pCoreOf K hhK, ← E3.conjSubgroup_inf]
  exact hleft.trans hA

theorem nine3_eq_of_le_sup_nineI (hc : Nine3Choice V T A K S X p g x) (hI : Nine3IFacts V K S)
    {U U' : Subgroup G} (hU : U ∈ omegaIn V K (nineE V K)) (hU' : U' ∈ omegaIn V K (nineE V K))
    (h : U' ≤ U ⊔ nineI V K) : U' = U := by
  have hUK : U ≤ K := hU.2
  have hUN : U ≤ normalizer (nineI V K : Set G) := fun u hu =>
    conjSubgroup_eq_iff_mem_normalizer.mp
      (Nine3Core.conjSubgroup_nineI (V := V) (K := K) (hUK hu))
  have hset : (↑(U ⊔ nineI V K) : Set G) = (U : Set G) * (nineI V K : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right U (nineI V K) hUN
  have hStepA : ∀ i ∈ nineI V K, ∀ y ∈ U ⊔ nineI V K, ⁅i, y⁆ ∈ U ⊓ pCoreOf 2 K := by
    intro i hi y hy
    have hy' : y ∈ (U : Set G) * (nineI V K : Set G) := by
      rw [← hset]; exact hy
    rw [Set.mem_mul] at hy'
    obtain ⟨u, hu, j, hj, rfl⟩ := hy'
    have hcommij : ⁅i, j⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val (hI.abelian.1.is_comm.comm ⟨i, hi⟩ ⟨j, hj⟩)
    rw [commutatorElement_mul_right_eq_mul_conj, hcommij]
    simp only [mul_one, mul_inv_cancel_right]
    rw [← nine3_comm_of_mem_omegaIn hc hI hU]
    exact Subgroup.commutator_mem_commutator hi hu
  have hStepA' : ⁅nineI V K, U ⊔ nineI V K⁆ ≤ U ⊓ pCoreOf 2 K :=
    Subgroup.commutator_le.mpr hStepA
  have hStepB : U' ⊓ pCoreOf 2 K ≤ U ⊓ pCoreOf 2 K := by
    rw [← nine3_comm_of_mem_omegaIn hc hI hU']
    exact (Subgroup.commutator_mono_right h).trans hStepA'
  have hU'card : Nat.card ↥U' = Nat.card V := by
    obtain ⟨b, hb, -, -⟩ := mem_omegaSet.mp hU'.1
    rw [hb]
    exact E3.card_conjSubgroup V b
  have hlt : 2 < Nat.card ↥U' := by rw [hU'card]; exact hc.core.hyp7.2.1
  have hrel : (U' ⊓ pCoreOf 2 K).relIndex U' = 2 :=
    nine3_relIndex_of_mem_omegaIn hc hU'
  have hcard : 2 * Nat.card ↥(U' ⊓ pCoreOf 2 K) = Nat.card ↥U' := by
    have hc0 := Subgroup.relIndex_mul_card (H := U' ⊓ pCoreOf 2 K) (K := U')
    rw [hrel, inf_eq_left.mpr inf_le_left] at hc0
    exact hc0
  have hne : U' ⊓ pCoreOf 2 K ≠ ⊥ := by
    intro hbot
    rw [hbot] at hcard
    simp only [Subgroup.card_bot, mul_one] at hcard
    omega
  have hInf : U' ⊓ U ≠ ⊥ := by
    intro hb
    apply hne
    rw [← le_bot_iff, ← hb]
    exact le_inf inf_le_left (hStepB.trans inf_le_left)
  obtain ⟨a, ha, -, -⟩ := mem_omegaSet.mp hU.1
  obtain ⟨b, hb, -, -⟩ := mem_omegaSet.mp hU'.1
  rcases inf_conjSubgroup_eq_bot_or_eq hc.core.hyp7.2.2 a b with hbot | heq
  · exfalso
    apply hInf
    rw [ha, hb, inf_comm, hbot]
  · rw [ha, hb]
    exact heq.symm

end CFSG.LocalAnalysis.WeakClosure81
