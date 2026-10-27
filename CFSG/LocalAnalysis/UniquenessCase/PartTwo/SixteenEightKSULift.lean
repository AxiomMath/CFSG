module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Pred
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Nat
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Red
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSUComm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSUGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverR119

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

theorem s16k_fixNc_statedSU_of_pRank {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {G : Type*} [Group G] [Finite G] {A : Subgroup G} {n : ℕ} (hn : 4 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (ρ : ↥A →* MulAut (Multiplicative (Fin n → K)))
    (hρ : Function.Injective ρ) (hρN : ∀ a : ↥A, ρ a ∈ s16gNorm (StatedSU n 2 K))
    (hrk : 3 ≤ CFSG.Open.pRank p A) : FixNc (StatedSU n 2 K) p := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨E, hEr, hE, hcard⟩ := s16g_exists_elem_of_le_pRank ρ hρ hp hrk
  have hEN : E ≤ s16gNorm (StatedSU n 2 K) := hEr.trans (s16g_range_le_norm hρN)
  have hA : ¬ p ∣ Nat.card (RingAut K) := by
    have h2 : Nat.card (RingAut K) = 2 :=
      (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
        (by rw [hK]; norm_num)).1
    rw [h2]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hU : ¬ p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  obtain ⟨F, hFN, hF, hFcard⟩ := s16g_exists_matrix_elem_of_lin hEN
    (s16g_le_lin_of_coprime (s16k_addCommutantScalar_statedSU hK (by omega)) hp hA hEN
      hE.isPGroup) hE
  have hFS : F ≤ StatedSU n 2 K := by
    intro x hx
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · have hφ := s16g_hom_eq_one_of_coprime hp hF.isPGroup hU
        ((Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).comp F.subtype)
      have hφx : (Matrix.GeneralLinearGroup.det x : Kˣ) = 1 := by
        simpa [MonoidHom.comp_apply, Subgroup.subtype_apply] using
          DFunLike.congr_fun hφ ⟨x, hx⟩
      have h1 := congrArg (fun u : Kˣ => (u : K)) hφx
      rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h1
    · exact s16k_normalizer_statedSU_unitary hK (by omega) (hFN hx)
  haveI := hF.1
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : F) ⟨y, hy⟩)
  have hcardF : p ^ 3 ≤ Nat.card F := by rw [hFcard]; exact hcard
  exact s16k_fixNc_statedSU_of_elem hK hn hp hp5 hFS hF.2 hFc hcardF

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
