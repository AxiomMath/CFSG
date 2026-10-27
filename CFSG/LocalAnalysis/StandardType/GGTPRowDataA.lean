module

public import CFSG.LocalAnalysis.StandardType.GGTPRowDataDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggTP_scalar_injective {d : ℕ} [Nonempty (Fin d)] {K : Type} [Field K] :
    Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin d) : Kˣ →* GL (Fin d) K) := by
  intro a b hab
  have h2 : (↑(Matrix.GeneralLinearGroup.scalar (Fin d) a) : Matrix (Fin d) (Fin d) K) =
      ↑(Matrix.GeneralLinearGroup.scalar (Fin d) b) := congrArg Units.val hab
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar] at h2
  exact Units.ext_iff.mpr (Matrix.scalar_inj.mp h2)

theorem ggTPRowData_A {r n : ℕ} (hr : r = 6 ∨ r = 11 ∨ r = 12) (h3 : r = 11 → 3 ∣ 2 ^ n + 1)
    {Y : Type} [Group Y] (hY : GGHasLabel ⟨.A, r, n⟩ Y) : GGTPRowDatum Y := by
  obtain ⟨K, hField, hFinite, hKcard, hIso⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 2 ^ n ∧
      Nonempty (Y ≃* LargeEvenProj (LargeEvenSLGroup (Fin (r + 1)) K)) := by
    simpa only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeLinear] using hY
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : Fintype K := Fintype.ofFinite K
  refine ⟨Fin (r + 1), inferInstance, inferInstance, K, hField, hFinite,
    LargeEvenSLGroup (Fin (r + 1)) K, hIso, ?_, ?_, ?_⟩
  · rcases hr with rfl | rfl | rfl <;> simp
  · exact charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      rw [← Nat.card_eq_fintype_card]; exact hKcard)
  · let H := LargeEvenSLGroup (Fin (r + 1)) K
    let Z := (LargeEvenScalars (Fin (r + 1)) K).subgroupOf H
    intro h3dvd
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Z) 3 h3dvd
    have hsc_inj := ggTP_scalar_injective (d := r + 1) (K := K)
    have hmem : (g.1 : GL (Fin (r + 1)) K) ∈
        (Matrix.GeneralLinearGroup.scalar (Fin (r + 1))).range := by
      have hh : (g.1 : GL (Fin (r + 1)) K) ∈ LargeEvenScalars (Fin (r + 1)) K := by
        have hm := g.2
        rwa [Subgroup.mem_subgroupOf] at hm
      simpa only [LargeEvenScalars, CFSG.Open.StatedScalars] using hh
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
    have hdet1 : (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) K →* Kˣ)
        (g.1 : GL (Fin (r + 1)) K) = 1 := by
      have hH : (g.1 : GL (Fin (r + 1)) K) ∈ LargeEvenSLGroup (Fin (r + 1)) K := (g.1).2
      rw [LargeEvenSLGroup] at hH
      exact MonoidHom.mem_ker.mp hH
    have hc_det : (Matrix.GeneralLinearGroup.det : GL (Fin (r + 1)) K →* Kˣ)
        (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) c) = 1 := by
      rw [hc]; exact hdet1
    have hc_pow : c ^ (r + 1) = 1 := by
      have := hc_det
      rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at this
      exact this
    have h2 : orderOf (g.1 : GL (Fin (r + 1)) K) = orderOf g := by
      have h := orderOf_injective ((H.subtype).comp Z.subtype)
        ((Subgroup.subtype_injective H).comp (Subgroup.subtype_injective Z)) g
      simpa using h
    have hco : orderOf c = 3 := by
      have h1 : orderOf (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) c) = orderOf c :=
        orderOf_injective _ hsc_inj c
      rw [← h1, hc, h2, hg]
    have h3d : 3 ∣ r + 1 := by
      rw [← hco]
      exact orderOf_dvd_iff_pow_eq_one.mpr hc_pow
    have h3units : 3 ∣ Nat.card Kˣ := by
      rw [← hco]
      exact orderOf_dvd_natCard c
    have h3n : 3 ∣ 2 ^ n - 1 := by
      rw [Nat.card_units] at h3units
      rwa [hKcard] at h3units
    rcases hr with h6 | h11 | h12
    · rw [h6] at h3d
      obtain ⟨k, hk⟩ := h3d
      omega
    · have h32 : 3 ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub (h3 h11) h3n
      have hval : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
        have : 0 < 2 ^ n := pow_pos (by norm_num) n
        omega
      rw [hval] at h32
      obtain ⟨k, hk⟩ := h32
      omega
    · rw [h12] at h3d
      obtain ⟨k, hk⟩ := h3d
      omega

end CFSG.StandardType

end
