module

public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelAssembly
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresSU
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicLabels

public section

namespace CFSG.StandardType

namespace LayerCyc

open CFSG.Assembly Matrix LayerCores CFSG.ClassicalGroups.UnitaryFlag

theorem ggModelLayerCyclic_suNormalizerConj {d n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : GL (Fin d) K}
    (hA : A ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin d) K (2 ^ n) : Set (GL (Fin d) K))) :
    GGModelLayerCyclic p (ggMatConjAut hA) := by
  classical
  set h := TableBU.unitaryFieldData_of_card hK hn with hhdef
  have : CharP K 2 := h.charP
  refine ggModelLayerCyclic_of_cycCoreFamily fun _ hαp => ?_
  set H := LargeEvenSUGroup (Fin d) K (2 ^ n) with hHdef
  have hgen : ∀ (B : Subgroup.normalizer (H : Set (GL (Fin d) K))) (h : H),
      ((H.normalizerMonoidHom B h : H) : GL (Fin d) K) = B * h * B⁻¹ := fun _ _ => rfl
  have hpow : ∀ s ∈ H, A ^ p * s = s * A ^ p := by
    intro s hs
    have h1 := congrArg (fun φ : MulAut H => ((φ ⟨s, hs⟩ : H) : GL (Fin d) K)) hαp
    simp only [MulAut.one_apply] at h1
    rw [ggMatConjAut, ← map_pow, hgen] at h1
    simp only [SubgroupClass.coe_pow, Subgroup.coe_inv] at h1
    rwa [mul_inv_eq_iff_eq_mul] at h1
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd
    (show 2 ^ n + 1 ≠ 1 by have := Nat.one_le_two_pow (n := n); omega)
  have hsc : A ^ p ∈ LargeEvenScalars (Fin d) K := TableBUE.mem_scalars_of_commute h hq hqd hpow
  rw [largeEvenScalars_def, MonoidHom.mem_range] at hsc
  obtain ⟨c, hc⟩ := hsc
  have : Fintype K := Fintype.ofFinite K
  have hc1 : c ^ (Fintype.card K - 1) = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact FiniteField.pow_card_sub_one_eq_one _ c.ne_zero)
  have hA1 : A ^ (p * (Fintype.card K - 1)) = 1 := by
    rw [pow_mul, ← hc, ← map_pow, hc1, map_one]
  have hcard2 : Fintype.card K % 2 = 0 := FiniteField.even_card_iff_char_two.mp (ringChar.eq K 2)
  have hpos : 0 < Fintype.card K := Fintype.card_pos
  have hodd : Odd (p * (Fintype.card K - 1)) :=
    (hp.odd_of_ne_two hp2).mul (Nat.odd_iff.mpr (by omega))
  have hcard : (Nat.card (Subgroup.zpowers A) : K) ≠ 0 := by
    rw [Nat.card_zpowers, Ne, CharP.cast_eq_zero_iff K 2]
    intro h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr
      (h2.trans (orderOf_dvd_of_pow_eq_one hA1)))
  have hAN : Subgroup.zpowers A ≤ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) :=
    Subgroup.zpowers_le.mpr hA
  have hsymd : ∃ Y : Matrix (Fin d) (Fin d) K, (∀ g ∈ Subgroup.zpowers A,
      Y * (g : Matrix (Fin d) (Fin d) K) = (g : Matrix (Fin d) (Fin d) K) * Y) ∧
      Y + suAdj h Y = 1 := by
    obtain ⟨c, hc⟩ := exists_add_bar_eq_one h
    refine ⟨c • 1, fun g _ => by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one], ?_⟩
    rw [suAdj_smul_one, ← add_smul, hc, one_smul]
  obtain ⟨β, S, hS⟩ := exists_cycCoreFamily_adjCent hcard (isInvol_suAdj h)
    (fun X hX g hg => suAdj_mul_comm h hAN X hX hg) hsymd
  set H₀ : Subgroup (GL (Fin d) K) :=
    adjCent (Subgroup.zpowers A) (isInvol_suAdj (n := d) h) ⊓
      (Matrix.GeneralLinearGroup.det).ker with hH₀
  have hSdet : ∀ c, S c ≤ H₀ := by
    intro c
    refine le_inf (hS.1 c) ?_
    rw [← LayerFacts.ggCommutator_eq_of_isQuasisimple (hS.2.2.1 c)]
    exact (Subgroup.commutator_mono le_top le_top).trans (Abelianization.commutator_subset_ker _)
  have hS0 := hS.mono inf_le_left hSdet
  have hdet : ∀ g : GL (Fin d) K, g ∈ (Matrix.GeneralLinearGroup.det).ker ↔
      (g : Matrix (Fin d) (Fin d) K).det = 1 := fun g => by
    rw [MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  have hle : H₀ ≤ H.subtype.range := by
    intro g hg
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
    exact ⟨⟨g, (mem_unitarySU_iff_suAdj h).mpr ⟨(Subgroup.mem_inf.mp hg1).2, (hdet g).mp hg2⟩⟩,
      rfl⟩
  have hcent : ∀ x : GL (Fin d) K, x ∈ Subgroup.centralizer
      (Subgroup.zpowers A : Set (GL (Fin d) K)) ↔ A * x = x * A := by
    intro x
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff, eq_comm]
  have hC : H₀.comap H.subtype = ggFix (ggMatConjAut hA) := by
    ext x
    have hx := (mem_unitarySU_iff_suAdj h).mp x.2
    rw [Subgroup.mem_comap, hH₀, adjCent, Subgroup.mem_inf, Subgroup.mem_inf, hcent, mem_ggFix]
    constructor
    · rintro ⟨⟨hx1, -⟩, -⟩
      apply Subtype.ext
      rw [coe_ggMatConjAut]
      change A * (x : GL (Fin d) K) = (x : GL (Fin d) K) * A at hx1
      rw [hx1, mul_inv_cancel_right]
    · intro hx'
      have h1 := congrArg Subtype.val hx'
      rw [coe_ggMatConjAut, mul_inv_eq_iff_eq_mul] at h1
      exact ⟨⟨h1, hx.1⟩, (hdet _).mpr hx.2⟩
  have h2 := hS0.comap H.subtype H.subtype_injective hle
  rw [hC] at h2
  exact ⟨β, _, h2⟩

end LayerCyc

open LayerCyc in
theorem ggLayerUnitaryModelInput_holds : GGLayerUnitaryModelInput := by
  intro d n K _ _ hK hn _ _ p hp hp2 A hA _
  exact ggModelLayerCyclic_suNormalizerConj hK hn hp hp2 hA

end CFSG.StandardType

end
