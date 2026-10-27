module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanQuotientBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanQuotientTools
public import CFSG.RankThree.GroupTheory.SteinbergBMCentralPreimageSylowLift
public import CFSG.GroupTheory.CentralCoverTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.RankThree.GroupTheory.SteinbergBM
open TauCeti.Subgroup (normalizerQuotient)

theorem le_pRank_normalizerQuotient_of_comap_comm {Y T : Type} [Group Y] [Finite Y]
    [Group T] {φ : Y →* T} (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    {r k : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {D : Subgroup T}
    (hDr : ∀ x ∈ D, x ^ r = 1)
    (hDc : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x) (hk : r ^ k ≤ Nat.card D)
    {U : Subgroup T} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hDU : D ≤ Subgroup.normalizer (U : Set T))
    (S : Subgroup Y) (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) :
    k ≤ CFSG.Open.pRank r (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient S)) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite T := Finite.of_surjective φ hφ
  obtain ⟨V, hVD, hVab, hVcard, -⟩ :=
    CFSG.RankThree.Classical2.exists_elemAbelian_le_centralizer (Y := Y) hφ hker hr hr2 hDr hDc hk
      (u := 1) (one_pow 2) (fun x _ => by rw [map_one]; exact Commute.one_left x)
  have hU2 : IsPGroup 2 U := hU.2.1
  have hUle : U ≤ φ.range := by
    rw [MonoidHom.range_eq_top.mpr hφ]
    exact le_top
  obtain ⟨-, -, -, P, -, hPinv⟩ :=
    central_preimage_two_group_characteristic_sylow_lift_comap φ hker hU2 hUle
  set R : Subgroup Y := (P : Subgroup (U.comap φ)).map (U.comap φ).subtype with hR
  have hBN : D.comap φ ≤ Subgroup.normalizer (U.comap φ : Set Y) :=
    (Subgroup.comap_mono hDU).trans (Subgroup.le_normalizer_comap φ)
  have hPconj : ∀ x ∈ D.comap φ, (U.comap φ).map (MulAut.conj x) = U.comap φ :=
    fun x hx => Subgroup.mem_normalizer_iff_map_conj_eq.1 (hBN hx)
  have hVR : V ≤ Subgroup.normalizer (R : Set Y) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hPinv (MulAut.conj v) (hPconj v (hVD hv))
  have hR2 : IsPGroup 2 R := P.isPGroup'.map (U.comap φ).subtype
  have hUidx : ¬ 2 ∣ U.index := by
    rw [← Subgroup.relIndex_top_right (H := U)]
    exact hU.2.2
  have hRidx : ¬ 2 ∣ R.index := by
    rw [hR]
    exact CFSG.GroupTheory.not_dvd_index_map_comap_sylow_two hφ hUidx P
  have hRsyl : IsSylowTwoOf R ⊤ := by
    refine ⟨le_top, hR2, ?_⟩
    show ¬ 2 ∣ R.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hRidx
  have hkR : k ≤ CFSG.Open.pRank r
      (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient R)) :=
    (le_pRank_normalizerQuotient_of_le_normalizer hr hr2 hR2 hVR hVab hVcard).1
  obtain ⟨eN⟩ := normalizerQuotient_equiv_of_isSylowTwoOf (Y := Y) (Y' := Y) (S := S) (S' := R)
    (MulEquiv.refl Y) hS hRsyl
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt eN]
  exact hkR

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
