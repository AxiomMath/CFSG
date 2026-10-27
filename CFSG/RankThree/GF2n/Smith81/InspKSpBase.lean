module

public import CFSG.LargeExtraspecial.A2ModOrdFrame
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSpFixed
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerSUSp
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSp
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGSpCent
public import CFSG.Timmesfeld.ARS.Sec5Maximal
public import CFSG.Timmesfeld.ARS.Sec5Ten
public import CFSG.Timmesfeld.RankOne

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp.KFact

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.LargeExtraspecial.A2Mod.Frame

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  haveI := Fintype.ofFinite K
  have hp := ringChar.charP K
  obtain ⟨n, hprime, hn⟩ := FiniteField.card K (ringChar K)
  have h1 : (ringChar K) ∣ 2 ^ f := by
    rw [← hK, Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self _ n.ne_zero
  have h2 : ringChar K = 2 :=
    (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp (hprime.dvd_of_dvd_pow h1)
  rw [h2] at hp
  exact hp

theorem lt_of_nslType_cartanC {n : ℕ} {i₀ : Fin n}
    (h : NSLType n (Symplectic.cartanC n) i₀) : i₀.val + 1 < n := by
  generalize hA : Symplectic.cartanC n = A at h
  cases h with
  | symplectic hn i₀ hi₀ => exact hi₀
  | orthogonal hm i₀ hi₀ => exact absurd hA.symm (cartanB_ne_cartanC (by omega))
  | g2 i₀ hi₀ => exact absurd hA.symm cartan_G2_ne_cartanC
  | f4 i₀ hi₀ => exact absurd hA.symm cartan_F4_ne_cartanC


open CFSG.StandardType CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.SeitzReduction.SymplecticPilot in
theorem exists_conj_twoCentralElt_of_short {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    {i₀ : Fin (m + 3)} (hi : i₀.val + 1 < m + 3) {x : StatedSp (m + 3) F}
    (hx : x ∈ (Symplectic.rootDatum (m + 3) F).rootGroup (Pi.single i₀ 1)) (hx1 : x ≠ 1) :
    ∃ g : StatedSp (m + 3) F, x = g * twoCentralElt (m + 3) 1 2 (0 : F) 1 * g⁻¹ := by
  have hr := stdVec_shortPos_eq (n := m + 3) (k := i₀) hi
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hr).mp hx
  have hc : c ≠ 0 := by
    rintro rfl
    exact hx1 (elt_zero _)
  have hne : i₀ ≠ ⟨i₀.val + 1, hi⟩ := ne_succ' hi
  obtain ⟨h, hh⟩ := AutPSp.exists_conj_elt_one (K := F)
    (TauCeti.GLSymplecticFin.RootSubgroupIndex.difference i₀ ⟨i₀.val + 1, hi⟩ hne) hc
  obtain ⟨g', hg'⟩ := RCSTSp.exists_conj_one_two (F := F) (n := m) hne
  refine ⟨h * (CFSG.RankThree.PartOne.KFCL.Sp.permSp (K := F) _
    (RootCentSp.swap_plane_mem_Hp ⟨i₀.val + 1, hi⟩))⁻¹ * g', ?_⟩
  rw [hh, RootCentSp.elt_difference_one hne, RootCentSp.cj_eq_conj, hg']
  group


end CFSG.RankThree.GF2n.Smith81.Insp.KFact
