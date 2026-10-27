module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpLFrameMp
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoPlacement
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.LocalAnalysis.StandardType.GGClassicalCentralImageLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseRows
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelCore
import CFSG.LocalAnalysis.StandardType.GGTBE6
import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom
import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagLin
import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagRoot
import CFSG.LocalAnalysis.StandardType.GGTypeAFarRealize
import CFSG.LocalAnalysis.StandardType.GGF4H4Psl64Holds
import CFSG.LocalAnalysis.StandardType.GGF4H4JBlockAux1
import CFSG.LocalAnalysis.StandardType.GGF4H4ListLinHolds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped MatrixGroups

section Chart


theorem ggSecFiveBPermLin_J_chart (hMp : GGInnerDiagMpInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hLA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1) {ψ : SL(n, GaloisField 2 f) →* G}
    (hker : ψ.ker ≤ Subgroup.center SL(n, GaloisField 2 f)) (hrange : ψ.range = L)
    {K : Subgroup G} (hK𝒦 : K ∈ 𝒦) {i0 : Fin n}
    (hKA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0) :
    ∃ σJ : SL(n - 1, GaloisField 2 f) →* G, Function.Injective σJ ∧ σJ.range = J ∧
      GGHasLabel ⟨.A, n - 2, f⟩ (↥J ⧸ Subgroup.center ↥J) ∧ p ∣ Nat.card ↥J := by
  classical
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  have hp : p.Prime := hR.1.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hR.1.1.1.2.2.2.2.2.1.2.1
  obtain ⟨σ, χ, hLF⟩ := exists_ggSecFiveBPermSpLFrame hMp hp hp2
    hR.1.1.2.1.2.1 hR.1.1.2.1.2.2.2 hR.1.2.2.1.1
    hR.1.1.card_bstar_inf_centralizer_L.le (by omega) eta hLA (by omega) hker hrange r
    (Equiv.swap 0 i0)
  have hJ := ggSecFiveBPerm_original_J_eq_block hR hK𝒦 hKA (Equiv.swap 0 i0)
    (Equiv.swap_apply_left 0 i0) hLF
  let σJ : SL(r + 1, GaloisField 2 f) →* G :=
    σ.comp (slLowerBlockHom (r + 1) (GaloisField 2 f))
  have hσJ : σJ.range = J := by
    rw [hJ, MonoidHom.range_comp, range_slLowerBlockHom, blockSpecialLinear_eq_coordBlockSL]
  refine ⟨σJ, injective_comp_slLowerBlockHom (n := r + 1) hLF.1, hσJ, ?_, ?_⟩
  · simpa using ggHasLabel_J_of_lift (n := r + 1) (by omega) (by omega) hLF.1 hσJ
  · have hpF : p ∣ Nat.card (GaloisField 2 f)ˣ := by
      rw [Nat.card_units, GaloisField.card 2 f (by omega)]
      exact hpf
    have h := prime_dvd_card_range_comp_slLowerBlockHom (n := r + 1) hp hpF (by omega) hLF.1
    rwa [hσJ] at h

end Chart

theorem ggSecFiveBPermLin_tableP (hTPn : GGNbrTablePNbrInputNarrow) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hInnL : GGInnerDiagOn Bs L) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hInnK : GGInnerDiagOn Bs K) {n f : ℕ} (hn : 4 ≤ n)
    (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1)
    (hL : GGHasLabel ⟨.A, n - 1, f⟩ (↥L ⧸ Subgroup.center ↥L))
    (hJ : GGHasLabel ⟨.A, n - 2, f⟩ (↥J ⧸ Subgroup.center ↥J))
    {labK : LargeEvenLabel} (hΛK : LargeEvenInLambda2 labK)
    (hK : GGHasLabel labK (↥K ⧸ Subgroup.center ↥K)) :
    ∃ labK' : LargeEvenLabel, LargeEvenInLambda2 labK' ∧
      GGHasLabel labK' (↥K ⧸ Subgroup.center ↥K) ∧
      (GGTablePRow p ⟨.A, n - 2, f⟩ labK' ∨ (n = 5 ∧ GGTablePRow p ⟨.D, 3, f⟩ labK')) := by
  have hΛL : LargeEvenInLambda2 (⟨.A, n - 1, f⟩ : LargeEvenLabel) :=
    ⟨by show 1 ≤ f; omega, by show 1 ≤ n - 1; omega, fun _ => hf⟩
  have hΛJ : LargeEvenInLambda2 (⟨.A, n - 2, f⟩ : LargeEvenLabel) :=
    ⟨by show 1 ≤ f; omega, by show 1 ≤ n - 2; omega, fun _ => hf⟩
  have hsub : (n - 1) - 1 = n - 2 := by omega
  have hreg : GGRegimeTypeAL p (Nat.card Bs) ⟨.A, n - 1, f⟩ ⟨.A, n - 2, f⟩ labK :=
    ⟨rfl, by show 3 ≤ n - 1; omega, hf, hpf, by rw [hsub]⟩
  obtain ⟨labJ', labK', hΛJ', hΛK', hrow, hJ', hK'⟩ :=
    hTPn.toTypeAL G p B Bs x L D J y K hcfg hInnL hInnK hnb
      ⟨.A, n - 1, f⟩ ⟨.A, n - 2, f⟩ labK hΛL hΛJ hΛK hreg hL hJ hK
  rcases ggLabelIso_typeA_cases hRig (r := n - 2) (by omega) hΛJ' hΛJ hJ' hJ with
    rfl | ⟨h3, rfl⟩
  · exact ⟨labK', hΛK', hK', Or.inl hrow⟩
  · exact ⟨labK', hΛK', hK', Or.inr ⟨by omega, hrow⟩⟩

private theorem tableP_row_A_cases {p n f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 4 ≤ n) (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1) {X : LargeEvenLabel}
    (h : GGTablePRow p ⟨.A, n - 2, f⟩ X) :
    (X.tag = .A ∧
      (X = ⟨.A, n - 1, f⟩ ∨ (X = ⟨.A, n, f⟩ ∧ p ∣ n + 1) ∨
        ((X.rank = 2 * (n - 2) + 1 ∨ X.rank = 2 * (n - 2) + 2) ∧
          2 * X.n = f ∧ p ∣ 2 ^ X.n + 1) ∨
        (n = 4 ∧ f = 3 ∧ p = 7 ∧ X = ⟨.A, 8, 1⟩) ∨
        (n = 4 ∧ f = 4 ∧ p = 5 ∧ X = ⟨.A, 5, 2⟩))) ∨
      (X.tag = .C ∧ X = ⟨.C, n - 1, f⟩) ∨
      (X.tag = .D ∧ X = ⟨.D, n - 1, f⟩) ∨
      (X.tag = .twD ∧ X = ⟨.twD, n, f⟩) ∨
      (X.tag = .E6 ∧ n = 7 ∧ X = ⟨.E6, 0, f⟩) ∨
      (X.tag = .E7 ∧ n = 8 ∧ X = ⟨.E7, 0, f⟩) ∨
      (X.tag = .E8 ∧ ((n = 9 ∧ p ≠ 3) ∨ (n = 10 ∧ p = 3)) ∧ X = ⟨.E8, 0, f⟩) ∨
      (X.tag = .twA ∧ n = 4 ∧ X.rank = 5 ∧ 2 * X.n = f ∧ p ∣ 2 ^ X.n - 1) := by
  obtain ⟨tX, rX, nX⟩ := X
  unfold GGTablePRow at h
  cases tX <;>
    simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, true_and, false_and, and_false,
      or_false, false_or] at h
  case A =>
    rcases h with ⟨-, -, hmain⟩ | hrow2 | hspec1 | hspec2 | hspec3 | hspec4
    · refine Or.inl ⟨rfl, ?_⟩
      rcases hmain with ⟨hr, hn⟩ | ⟨⟨hr, hn⟩, hpdiv⟩ | ⟨hr, h2n, hpdvd⟩
      · exact Or.inl (by rw [hr, hn]; congr 1; omega)
      · refine Or.inr (Or.inl ⟨?_, ?_⟩)
        · rw [hr, hn]; congr 1; omega
        · rwa [show n - 2 + 3 = n + 1 by omega] at hpdiv
      · exact Or.inr (Or.inr (Or.inl ⟨hr, h2n, hpdvd⟩))
    · exfalso
      exact F4H4Lin.not_dvd_both hp hp2 hpf hrow2.1
    · obtain ⟨⟨hn2, hf3⟩, hp7, hr8, hn1⟩ := hspec1
      have hn4 : n = 4 := by omega
      subst hn4
      exact Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl
        ⟨rfl, hf3, hp7, by rw [hr8, hn1]⟩)))⟩
    · obtain ⟨⟨hn2, hf4⟩, hp5, hr5, hn2'⟩ := hspec2
      have hn4 : n = 4 := by omega
      subst hn4
      exact Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr
        ⟨rfl, hf4, hp5, by rw [hr5, hn2']⟩)))⟩
    · omega
    · omega
  case twA =>
    obtain ⟨-, -, hn2, hr5, h2n, hpdvd⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rfl, by omega, hr5, h2n, hpdvd⟩))))))
  case C =>
    obtain ⟨-, -, hr, hn⟩ := h
    exact Or.inr (Or.inl ⟨rfl, by rw [hr, hn]; congr 1; omega⟩)
  case D =>
    obtain ⟨-, -, hr, hn⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by rw [hr, hn]; congr 1; omega⟩))
  case twD =>
    obtain ⟨-, -, hr, hn⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by rw [hr, hn]; congr 1; omega⟩)))
  case E6 =>
    rcases h with ⟨-, -, hn5, hr0, hn⟩ | hrow2
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨rfl, by omega, by rw [hr0, hn]⟩))))
    · exfalso
      exact F4H4Lin.not_dvd_both hp hp2 hpf hrow2.1
  case E7 =>
    obtain ⟨-, -, hn6, hr0, hn⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, by omega, by rw [hr0, hn]⟩)))))
  case E8 =>
    obtain ⟨-, -, h8⟩ := h
    rcases h8 with ⟨hn7, hp3, hr0, hn⟩ | ⟨hn8, hp3, hr0, hn⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨rfl, Or.inl ⟨by omega, hp3⟩, by rw [hr0, hn]⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨rfl, Or.inr ⟨by omega, hp3⟩, by rw [hr0, hn]⟩))))))

private theorem tableP_row_D3_cases {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpf : p ∣ 2 ^ f - 1) {X : LargeEvenLabel}
    (h : GGTablePRow p ⟨.D, 3, f⟩ X) : X = ⟨.D, 4, f⟩ := by
  obtain ⟨tX, rX, nX⟩ := X
  unfold GGTablePRow at h
  cases tX <;>
    simp only [LargeEvenLabel.mk.injEq, reduceCtorEq, true_and, false_and, and_false,
      or_false, false_or] at h
  case D =>
    obtain ⟨-, hr, hn⟩ := h
    rw [hr, hn]
  case twD =>
    exfalso
    exact F4H4Lin.not_dvd_both hp hp2 hpf h.1
  all_goals omega

theorem ggSecFiveBPermLin_not_psl64 {G : Type} [Group G] [Finite G] {J K : Subgroup G}
    (hJK : J ≤ K) {σJ : SL(3, GaloisField 2 4) →* G} (hσ : Function.Injective σJ)
    (hσJ : σJ.range = J) (hJ : GGHasLabel ⟨.A, 2, 4⟩ (↥J ⧸ Subgroup.center ↥J))
    (hK : GGHasLabel ⟨.A, 5, 2⟩ (↥K ⧸ Subgroup.center ↥K))
    (hKc : Subgroup.center ↥K = ⊥) : False := by
  let e : SL(3, GaloisField 2 4) ≃* ↥J :=
    (MonoidHom.ofInjective hσ).trans (MulEquiv.subgroupCongr hσJ)
  have hZ : Nat.card ↥(Subgroup.center ↥J) = 3 := by
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv,
      ggF4JBx_card_center_SL_three 4 (GaloisField.card 2 4 (by norm_num))]
    norm_num
  obtain ⟨-, h13, h17⟩ := ggF4H4Psl64_dvd_card_of_hasLabel (by norm_num) (dvd_refl 4) hJ
  exact ggF4H4Psl64_false_of_le hJK hK hKc h13 h17 (by simp [hZ])

theorem ggSecFiveBPermLin_label_K
    (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hT : GGTBTorAll)
    (hLift : GGTBTorLiftRows) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hpf : p ∣ 2 ^ f - 1) (hL : GGHasLabel ⟨.A, n - 1, f⟩ (↥L ⧸ Subgroup.center ↥L))
    {σJ : SL(n - 1, GaloisField 2 f) →* G} (hσ : Function.Injective σJ) (hσJ : σJ.range = J)
    (hJ : GGHasLabel ⟨.A, n - 2, f⟩ (↥J ⧸ Subgroup.center ↥J))
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {i0 : Fin n} {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hJK : J ≤ K)
    (hKA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0) :
    ∃ lab : LargeEvenLabel, GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) ∧
      GGSecFiveBPermLinNbrLabel p n f lab := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  have hp : p.Prime := hR.1.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hR.1.1.1.2.2.2.2.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hInnL : GGInnerDiagOn Bs L := hR.1.2.2.1.1
  have hInnK : GGInnerDiagOn Bs K := hR.1.2.2.1.2 y K hnb
  obtain ⟨lab₀, R, _, I, F, θ, hΛ₀, hhas₀, -, -, -, -, hHS₀⟩ :=
    ggNbr_sameMarking_of_innerDiag hRig hraw hiso hcfg hnb hInnK
  obtain ⟨labX, hΛX, hX, hrow⟩ :=
    ggSecFiveBPermLin_tableP hTPn hRig hcfg hInnL hnb hInnK hn hf hpf hL hJ hΛ₀ hhas₀
  have killA : ∀ {r : ℕ}, 3 ≤ r → GGHasLabel ⟨.A, r, f⟩ (↥K ⧸ Subgroup.center ↥K) →
      LargeEvenInLambda2 (⟨.A, r, f⟩ : LargeEvenLabel) → ¬ (n = 4 ∧ r = 5) → False := by
    intro r hr3 hXr hΛr hnot
    have hcov : GGTBTorCov p ⟨.A, r, f⟩ :=
      ggTBTorCov_of_untwisted_dvd_sub_one hp hp2 hΛr (by simp [LargeEvenUntwisted])
        (by omega) hpf (by simp [ggRowP_Small]; omega)
    have hKmark := ggInnerDiagOn_relabel hRig hInnK hΛr hXr
    have hres := ggSecFiveBCoordBLabel_nbr_of_coordB_four hT hLift hcfg hnb hn eta i0
      hΛr hcov hKmark hKA
    rcases hres with hBC | hD | ⟨hn4, hr5, -⟩
    · exact absurd hBC.1 (by simp)
    · exact absurd hD.1 (by simp)
    · exact hnot ⟨hn4, hr5⟩
  have killE : ∀ {lab : LargeEvenLabel}, LargeEvenUntwisted lab.tag →
      (lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8) → 2 ≤ lab.n →
      p ∣ 2 ^ lab.n - 1 → ¬ ggRowP_Small p lab → GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) →
      LargeEvenInLambda2 lab → False := by
    intro lab hu htag hn2 hpq hsmall hXlab hΛlab
    have hcov := ggTBTorCov_of_untwisted_dvd_sub_one hp hp2 hΛlab hu hn2 hpq hsmall
    have hKmark := ggInnerDiagOn_relabel hRig hInnK hΛlab hXlab
    have hres := ggSecFiveBCoordBLabel_nbr_of_coordB_four hT hLift hcfg hnb hn eta i0
      hΛlab hcov hKmark hKA
    rcases hres with hBC | hD | ⟨-, -, hA5⟩
    · exact absurd hBC.1 (by rcases htag with h | h | h <;> simp [h])
    · exact absurd hD.1 (by rcases htag with h | h | h <;> simp [h])
    · exact absurd hA5 (by rcases htag with h | h | h <;> simp [h])
  have extCase : ∀ (rX a : ℕ), labX = ⟨.A, rX, a⟩ → 2 * a = f → p ∣ 2 ^ a + 1 →
      (rX = 2 * (n - 2) + 1 ∨ rX = 2 * (n - 2) + 2) →
      GGSecFiveBPermLinNbrLabel p n f labX := by
    intro rX a hlabX h2a hpdiv hr
    have hΛX' : LargeEvenInLambda2 (⟨.A, rX, a⟩ : LargeEvenLabel) := hlabX ▸ hΛX
    have hX' : GGHasLabel (⟨.A, rX, a⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K) :=
      hlabX ▸ hX
    rcases ggLabelIso_typeA_cases hRig (r := rX) (by omega) hΛ₀ hΛX' hhas₀ hX' with
      hlo | ⟨hr3, hlo⟩
    · subst hlo
      rcases F4H4Lin.halfSplit_A rfl hHS₀ with hsub | ⟨ha1, hp3⟩ |
        ⟨hr5, ha2, hc, hp5⟩ | ⟨hr8, ha1, hp7⟩
      · exfalso
        exact F4H4Lin.not_dvd_both hp hp2 hsub hpdiv
      · have ha1' : a = 1 := ha1
        have hf2 : f = 2 := by rw [← h2a, ha1']
        have hlab1 : labX = ⟨.A, rX, 1⟩ := by
          rw [hlabX, ha1']
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hp3, hf2, ?_⟩)))
        rcases hr with hr | hr
        · left
          rw [hlab1]
          congr 1
          omega
        · right
          rw [hlab1]
          congr 1
          omega
      · exfalso
        have hr5' : rX = 5 := hr5
        have ha2' : a = 2 := ha2
        have hf4 : f = 4 := by rw [← h2a, ha2']
        subst hr5'
        have hn4 : n = 4 := by rcases hr with hr | hr <;> omega
        subst hn4
        subst hf4
        subst ha2'
        subst hp5
        exact ggSecFiveBPermLin_not_psl64 hJK hσ hσJ (by simpa using hJ)
          (by simpa [hlabX] using hX) hc
      · exfalso
        have ha1' : a = 1 := ha1
        have hp7' : p = 7 := hp7
        subst ha1'
        subst hp7'
        norm_num at hpdiv
    · omega
  rcases hrow with hrowA | ⟨hn5, hrowD3⟩
  · have hpred : GGSecFiveBPermLinNbrLabel p n f labX := by
      rcases tableP_row_A_cases hp hp2 hn hf hpf hrowA with
        hAg | hCg | hDg | htwDg | hE6g | hE7g | hE8g | htwAg
      · obtain ⟨htagX, hcases⟩ := hAg
        rcases hcases with h0 | h1 | h2 | h3 | h4
        · subst h0
          exact (killA (by omega) hX hΛX (by omega)).elim
        · obtain ⟨h1eq, hpdvd⟩ := h1
          subst h1eq
          exact (killA (by omega) hX hΛX (by omega)).elim
        · obtain ⟨hr, h2n, hpdvd⟩ := h2
          exact extCase labX.rank labX.n (F4H4Lin.label_eq htagX rfl rfl) h2n hpdvd hr
        · obtain ⟨hn4, hf3, hp7, hXeq⟩ := h3
          subst hXeq
          subst hn4
          subst hf3
          subst hp7
          obtain ⟨χ, hχ⟩ := hA8 G B Bs x L D J hcfg hR.1.2.2.1 y K hnb hX
          exfalso
          exact (not_ggReflGenerated_of_hom_three χ hχ) (hR.2.1 y K hnb)
        · obtain ⟨hn4, hf4, hp5, hXeq⟩ := h4
          subst hXeq
          subst hn4
          subst hf4
          subst hp5
          exact extCase 5 2 rfl (by norm_num) (by norm_num) (Or.inl (by norm_num))
      · exact Or.inl hCg.2
      · obtain ⟨-, hXeq⟩ := hDg
        subst hXeq
        have hΛD : LargeEvenInLambda2 (⟨.D, n - 1, f⟩ : LargeEvenLabel) :=
          ⟨by show 1 ≤ f; omega, by show 3 ≤ n - 1; omega⟩
        have hcov : GGTBTorCov p ⟨.D, n - 1, f⟩ :=
          ggTBTorCov_of_untwisted_dvd_sub_one hp hp2 hΛD (by simp [LargeEvenUntwisted])
            (by omega) hpf (by simp [ggRowP_Small])
        have hKmark := ggInnerDiagOn_relabel hRig hInnK hΛD hX
        have hres := ggSecFiveBCoordBLabel_nbr_of_coordB_four hT hLift hcfg hnb hn eta i0
          hΛD hcov hKmark hKA
        rcases hres with hBC | hDres | ⟨hn4, hr5, -⟩
        · exact absurd hBC.1 (by simp)
        · have hbad : n - 1 = n := by simpa using hDres.2
          omega
        · have hbad : n - 1 = 5 := by simpa using hr5
          omega
      · exact Or.inr (Or.inr (Or.inl htwDg.2))
      · obtain ⟨-, hn7, hXeq⟩ := hE6g
        subst hXeq
        exact (killE (by simp [LargeEvenUntwisted]) (Or.inl rfl) (by omega) hpf
          (by simp [ggRowP_Small]) hX hΛX).elim
      · obtain ⟨-, hn8, hXeq⟩ := hE7g
        subst hXeq
        exact (killE (by simp [LargeEvenUntwisted]) (Or.inr (Or.inl rfl)) (by omega) hpf
          (by simp [ggRowP_Small]) hX hΛX).elim
      · obtain ⟨-, hE8, hXeq⟩ := hE8g
        subst hXeq
        exact (killE (by simp [LargeEvenUntwisted])
          (Or.inr (Or.inr rfl)) (by omega) hpf (by simp [ggRowP_Small]) hX hΛX).elim
      · obtain ⟨htwA, hn4, hr5, h2n, hpdiv⟩ := htwAg
        have ha2 : 2 ≤ labX.n := by
          have h1 : 1 ≤ labX.n := hΛX.1
          by_contra h
          have hn1 : labX.n = 1 := by omega
          rw [hn1] at hpdiv
          exact hp.not_dvd_one (by simpa using hpdiv)
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hn4, ?_⟩)))
        refine ⟨labX.n, h2n.symm, ha2, hpdiv, ?_⟩
        exact F4H4Lin.label_eq htwA hr5 rfl
    exact ⟨labX, hX, hpred⟩
  · subst hn5
    exfalso
    have hXeq := tableP_row_D3_cases hp hp2 hpf hrowD3
    subst hXeq
    have hΛD : LargeEvenInLambda2 (⟨.D, 4, f⟩ : LargeEvenLabel) :=
      ⟨by show 1 ≤ f; omega, by norm_num⟩
    have hcov : GGTBTorCov p ⟨.D, 4, f⟩ :=
      ggTBTorCov_of_untwisted_dvd_sub_one hp hp2 hΛD (by simp [LargeEvenUntwisted])
        (by omega) hpf (by simp [ggRowP_Small])
    have hKmark := ggInnerDiagOn_relabel hRig hInnK hΛD hX
    have hres := ggSecFiveBCoordBLabel_nbr_of_coordB_four hT hLift hcfg hnb hn eta i0
      hΛD hcov hKmark hKA
    rcases hres with hBC | hDres | ⟨hn4, hr5, -⟩
    · exact absurd hBC.1 (by simp)
    · have hbad : 4 = 5 := by simpa using hDres.2
      omega
    · omega


section Final


theorem ggSecFiveBPermLinNbrLabelInput_of_tableP (hRig : GGLabelRigidInput)
    (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) (hMp : GGInnerDiagMpInput) (hBal : GGLBalanceInput) :
    GGSecFiveBPermLinNbrLabelInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR _ n _ _ hn eta _ hLA _ _ f hf hlab K hK𝒦 i0 hKA
  obtain ⟨lab, -, ⟨⟨htag, hrank, hpf⟩, hlabn⟩, hlabL, -⟩ := hlab.exists_label_eq
  obtain rfl : lab = ⟨.A, n - 1, f⟩ := F4H4Lin.label_eq htag hrank hlabn
  obtain ⟨ψ, hψker, hψrange⟩ := exists_sl_centralImage_of_hasLabel hlab.1 hn hf hlabL
  obtain ⟨σJ, hσ, hσJ, hJ, hpJ⟩ :=
    ggSecFiveBPermLin_J_chart hMp hR hn eta hLA hf hpf hψker hψrange hK𝒦 hKA
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK𝒦
  exact ggSecFiveBPermLin_label_K hRig hTPn hA8 hraw hiso (ggTBTorAll_of_remaining trivial)
    ggTBTorLiftRows_holds hR hn hf hpf hlabL hσ hσJ hJ eta hnb
    (le_of_ggNbr hBal hR.1.1.1 hR.1.1.2.2 hpJ hnb) hKA

end Final

end CFSG.StandardType

end
