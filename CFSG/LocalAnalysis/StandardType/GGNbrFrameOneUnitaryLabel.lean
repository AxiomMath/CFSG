module

public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneUnitary
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneTransfer
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypCentral
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHyperbolic
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUCommute
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUBlocks
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUnitary

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Open
  Matrix TableB

theorem ggTorusFrameEltSC_statedProj_hyp {n p : ℕ} {F : Type} [Field F] [Finite F]
    (h : UnitaryFieldData 2 n F) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n - 1) :
    GGTorusFrameEltSC p (StatedProj (StatedSU 6 (2 ^ n) F)) := by
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 3) (ε := 0) h
  have hSU : GGTorusFrameEltSC p (StatedSU 6 (2 ^ n) F) :=
    ggTorusFrameEltSC_of_mulEquiv (hypTransport h hR).symm
      (ggTorusFrameEltSC_hypSU_three h hp hp2 hpq)
  refine ggTorusFrameEltSC_of_centralQuotient hp
    (QuotientGroup.mk' ((StatedScalars (Fin 6) F).subgroupOf (StatedSU 6 (2 ^ n) F)))
    (QuotientGroup.mk'_surjective _) ?_ ?_ hSU
  · rw [QuotientGroup.ker_mk']
    exact scalars_le_center_statedSU
  · exact fun hdvd => not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
      (hdvd.trans (card_center_statedSU_dvd h.card_eq_sq (by norm_num)))

theorem two_dvd_card_statedProj_statedSU {d f : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (hd : 2 ≤ d) : 2 ∣ Nat.card (StatedProj (StatedSU d (2 ^ f) K)) := by
  let i₀ : Fin d := ⟨0, by omega⟩
  let i₁ : Fin d := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by
    intro h
    have h' := congrArg Fin.val h
    simp [i₀, i₁] at h'
  obtain ⟨g, hg⟩ := CFSG.ComponentClassification.RankTwoClassical.exists_permMatrix_mem
    (K := K) (f := f) (k := d) (Equiv.swap i₀ i₁)
  have hgGL : (g : GL (Fin d) K) ^ 2 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, sq, hg, ← Matrix.permMatrix_mul,
      Equiv.swap_mul_self, Matrix.permMatrix_one]
  have hg2 : g ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hgGL
  have hnot : (QuotientGroup.mk g : StatedProj (StatedSU d (2 ^ f) K)) ≠ 1 := by
    intro h1
    have hmem : g ∈ (StatedScalars (Fin d) K).subgroupOf (StatedSU d (2 ^ f) K) :=
      (QuotientGroup.eq_one_iff g).mp h1
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hc' : (Matrix.GeneralLinearGroup.scalar (Fin d) c : GL (Fin d) K).val =
        (g : GL (Fin d) K).val := congrArg Units.val hc
    rw [GeneralLinearGroup.coe_scalar, hg] at hc'
    have h1 := congrArg (fun M : Matrix (Fin d) (Fin d) K => M i₀ i₀) hc'
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply] at h1
    simp only [Equiv.swap_apply_left, Option.mem_def, Option.some.injEq, if_neg hi] at h1
    exact c.ne_zero h1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (QuotientGroup.mk g : StatedProj (StatedSU d (2 ^ f) K)) = 2 :=
    orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, hg2, QuotientGroup.mk_one]) hnot
  have hdvd : orderOf (QuotientGroup.mk g : StatedProj (StatedSU d (2 ^ f) K)) ∣
      Nat.card (StatedProj (StatedSU d (2 ^ f) K)) := orderOf_dvd_natCard _
  rw [hord] at hdvd
  exact hdvd

section Certificates


theorem largeEvenLabelAll_frame_unitary {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twA ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpq⟩ := h
  subst ht
  subst hl
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have hpq' : ¬ p ∣ 2 ^ n + 1 := not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
  have hq4 : 4 ≤ 2 ^ n := four_le_two_pow_of_dvd_sub_one hp hp2 hn hpq
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hK
  have hZ : Subgroup.center
      (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n))) = ⊥ :=
    center_statedProj_statedSU_eq_bot hK (by norm_num)
  have hIp : GGOutdiagPrime p
      (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) :=
    fun φ hφ hφp => NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd hK hn (by omega) (by omega)
      hp hpq' φ hφ hφp
  have hcp : GGCenterPrime p (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n))) :=
    ggCenterPrime_psu_even hK (by decide) (by norm_num) hq4 hpq'
  have hfr : GGTorusFrameEltSC p
      (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n))) :=
    ggTorusFrameEltSC_statedProj_hyp (TableBU.unitaryFieldData_of_card hK hn) hp hp2 hpq
  refine ⟨K, inferInstance, inferInstance, hK, hQ', ?_⟩
  exact ⟨0, TypeA.ggTorusLift_zero
      (two_dvd_card_statedProj_statedSU (d := 6) (f := n) (K := K) (by norm_num)),
    ggTorusFrame_of_frameEltSC hp hp2 hZ hIp hcp hfr⟩

end Certificates

end CFSG.StandardType

end
