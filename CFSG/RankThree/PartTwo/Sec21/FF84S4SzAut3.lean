module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43d
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.LocalAnalysis.AGLEmbedding.ThreeOrFiveDvd
import CFSG.LocalAnalysis.SteinbergCFCComponentSolvableActions

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Assembly (InCatalog)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem three_dvd_card_range_of_ne_one {Q M : Type*} [Group Q] [Group M] [Finite Q]
    (hQ : Group.IsPerfect Q) (hS : IsSimpleGroup (Q ⧸ Subgroup.center Q))
    (h3 : 3 ∣ Nat.card (Q ⧸ Subgroup.center Q)) {ψ : Q →* M} (hψ : ψ ≠ 1) :
    3 ∣ Nat.card ψ.range := by
  classical
  by_cases hNZ : ψ.ker ≤ Subgroup.center Q
  · have h1 : (Subgroup.center Q).index ∣ ψ.ker.index := Subgroup.index_dvd_of_le hNZ
    rw [Subgroup.index_ker] at h1
    exact h3.trans h1
  · exfalso
    apply hψ
    set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
    have hnorm : (ψ.ker.map π).Normal := Subgroup.Normal.map inferInstance π
      (QuotientGroup.mk'_surjective _)
    have hmap : ψ.ker.map π = ⊤ := by
      haveI := hnorm
      rcases hS.eq_bot_or_eq_top_of_normal (ψ.ker.map π) with h | h
      · exfalso
        apply hNZ
        intro n hn
        have : π n ∈ ψ.ker.map π := ⟨n, hn, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        exact (QuotientGroup.eq_one_iff n).mp this
      · exact h
    have hdec : ∀ x : Q, ∃ z ∈ Subgroup.center Q, ψ x = ψ z := by
      intro x
      have hx : π x ∈ ψ.ker.map π := by rw [hmap]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := hx
      have hz : n⁻¹ * x ∈ Subgroup.center Q := QuotientGroup.eq.mp hnx
      refine ⟨n⁻¹ * x, hz, ?_⟩
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp hn, inv_one, one_mul]
    have hcomm : ∀ x y : Q, ψ x * ψ y = ψ y * ψ x := by
      intro x y
      obtain ⟨z, hz, hxz⟩ := hdec x
      obtain ⟨z', hz', hyz⟩ := hdec y
      rw [hxz, hyz, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz z').symm]
    have hle : commutator Q ≤ ψ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm x y
    rw [hQ.commutator_eq_top, top_le_iff, MonoidHom.ker_eq_top_iff] at hle
    exact hle

theorem lemmaSzAut3_of_schreier (hSch : SchreierFor InCatalog) : LemmaSzAut3 := by
  intro H _ _ hHs hHnab hHK h3H Q _ _ hQ hQs _ h3Q φ
  classical
  by_contra hφ
  haveI := hHs
  have hHcat : InCatalog H :=
    KCore.KGroupNonab.catalogue_self CFSG.Assembly.inCatalog_isoInvariant hHK hHnab
  haveI hsol : Group.IsSolvable (Outer H) := hSch H hHnab hHcat
  set π := QuotientGroup.mk' (inner H) with hπ
  have hout : ∀ q : Q, φ q ∈ inner H := by
    have hperf : Group.IsPerfect (π.comp φ).range :=
      Group.IsPerfect.ofSurjective (f := (π.comp φ).rangeRestrict)
        (π.comp φ).rangeRestrict_surjective
    have hsolR : Group.IsSolvable (π.comp φ).range := inferInstance
    have hbot : (π.comp φ).range = ⊥ :=
      CFSG.LocalAnalysis.eq_bot_of_isPerfect_of_isSolvable hperf hsolR
    intro q
    have : (π.comp φ) q ∈ (π.comp φ).range := ⟨q, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff (φ q)).mp this
  have hrange : φ.range ≤ inner H := by
    rintro _ ⟨q, rfl⟩
    exact hout q
  have hdvd : Nat.card φ.range ∣ Nat.card H :=
    (Subgroup.card_dvd_of_le hrange).trans (Subgroup.card_range_dvd _)
  exact h3H ((three_dvd_card_range_of_ne_one hQ hQs h3Q hφ).trans hdvd)

theorem lemmaSzAut3_holds
    : LemmaSzAut3 :=
  lemmaSzAut3_of_schreier CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds

theorem lemmaSz_holds :
    LemmaSz := by
  intro H _ _ hHs hnab hK h3
  haveI := hHs
  exact (CFSG.AGLEmbedding.kFactThreeOrFiveDvd H hHs hnab
    (KCore.KGroupNonab.catalogue_self CFSG.Assembly.inCatalog_isoInvariant hK hnab)).resolve_left h3

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
