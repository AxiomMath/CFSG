module

public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmall

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggLayerCenterCyclic_of_subset_inn_of_not_dvd {p : ℕ} (hp : p.Prime) {R : Type}
    [Group R] [Finite R] {I : Set (MulAut R)} (hI : I ⊆ LargeEvenInnSet R)
    (hpR : ¬ p ∣ Nat.card R) : GGLayerCenterCyclic p R I :=
  ggLayerCenterCyclic_of_isSolvable_fix fun φ hφ hφ1 hφp => by
    exfalso
    obtain ⟨r, rfl⟩ := hI hφ
    apply hφ1
    have h1 : orderOf (MulAut.conj r) ∣ p := orderOf_dvd_of_pow_eq_one hφp
    have h2 : orderOf (MulAut.conj r) ∣ Nat.card R :=
      (orderOf_map_dvd MulAut.conj r).trans (orderOf_dvd_natCard r)
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd (h ▸ h2) hpR

theorem largeEvenLabelAll_layerCenterCyclic_twB2 {p : ℕ}
    (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twB2)
    (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGLayerCenterCyclic p R I) := by
  have hpn := TableBExc.dvd_of_largeEvenSplit_twB2 ht hlab hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab hpn ⊢
  subst ht
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hn3 : 3 ≤ n := hlab.2.2.2
    have : 2 ∣ 1 := (Nat.dvd_add_right (dvd_pow_self 2 (by omega))).mp hpn
    omega
  obtain ⟨k, hk⟩ := hlab.2.2.1
  have hk' : n = 2 * k + 1 := hk
  have hna : 2 * ((n - 1) / 2) + 1 = n := by omega
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq'⟩ := hQ
  refine ⟨K, i1, i2, hK, hq', fun _ _ => ?_⟩
  have : Finite (LargeEvenSzGroup ((n - 1) / 2) K) := Subtype.finite
  have : Finite (LargeEvenCenterQuot (LargeEvenSzGroup ((n - 1) / 2) K)) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  refine ggLayerCenterCyclic_of_subset_inn_of_not_dvd hp subset_rfl fun hdvd => ?_
  apply TableBExc.not_dvd_card_suzuki hp hp2 hpn
  refine hdvd.trans ((Subgroup.card_quotient_dvd_card _).trans ?_)
  rw [largeEvenSzGroup_eq _ K, CFSG.LieType.Ree.suzuki_order hK, hna]

end CFSG.StandardType

end
