module

public import CFSG.Quasithin.Background.GoldschmidtB69DeepLt

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank H H.PairG
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (proj_surjective)
open CFSG.QuasithinUnique.Lin2.Five (tauSp projEquiv)
open B6

namespace B69

theorem exists_twist_data_sp4 {V : Type} [CommGroup V] [Finite V] {X T M L : Subgroup (MulAut V)}
    (hmp : MinParabolic X T M) (hL : CFSG.Open.IsComponentOf L X) {W : Subgroup V}
    (hW : W ∈ IrrPlus L (⊤ : Subgroup V)) {n : ℕ} (hn : 2 ≤ n)
    (hnat : BinaryNaturalSp4 (autSec L W (W ⊓ fixV L)) ⊤ ⊥ n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      Nonempty (SpTwist L W K) := by
  obtain ⟨K, hKf, hKfin, hK, r, hr, -, -, e₁, he₁⟩ := natural_data_sp4_gen hW le_rfl hnat
  have hr' : Function.Surjective r := hr rfl
  have hCharP : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  refine ⟨K, hKf, hKfin, hCharP, hK, ?_⟩
  let π₀def : ↥L →* StatedProj (StatedSp 2 K) := (proj 2 K).comp r
  have hπ₀ : Function.Surjective (π₀def) := proj_surjective.comp hr'
  have : Nontrivial (StatedProj (StatedSp 2 K)) := by
    have h := even_natCard_statedProj_sp (K := K)
    rw [← Finite.one_lt_card_iff_nontrivial]
    have hpos : 0 < Nat.card (StatedProj (StatedSp 2 K)) := Nat.card_pos
    obtain ⟨m, hm⟩ := h
    omega
  obtain ⟨t, ht, ht', thb, hthb, hnot⟩ := exists_twist_element hmp hL swapGeo_sp4
    even_natCard_statedProj_sp (CFSG.QuasithinUnique.Lin2.Five.center_statedProj_eq_bot (F := K))
    π₀def hπ₀
  obtain ⟨A', σ, h⟩ := exists_tau_mat thb hnot
  refine ⟨⟨r, e₁, he₁, t, ht, ht', ⟨(A' : GL (Fin 2 ⊕ Fin 2) K), σ, fun l l' hl' => ?_⟩,
    fun Φ hΦ => not_exists_tau_iso Φ fun γ x => ?_, hnorm_of_surjective r hr'⟩⟩
  · rw [← h (r l)]
    have : (projEquiv K).symm (thb (projEquiv K (r l))) = r l' := by
      rw [MulEquiv.symm_apply_eq]
      exact hthb l l' hl'
    rw [this]
  · obtain ⟨l, rfl⟩ := hr' γ
    exact hΦ l x

theorem asB69NoRankTwoSp4_proved :
    AsB69NoRankTwoSp4 := by
  intro V _ _ hV X T M A L hH W hW hc
  obtain ⟨-, hmp, -, -, -, hA, hL, hLA⟩ := hH
  obtain ⟨⟨n, hnat, hHL⟩, -⟩ := hc
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hn0 : 1 ≤ n := by
    obtain ⟨K, hKf, hKfin, hK, -⟩ := hnat
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0, pow_zero] at hK
    have := Finite.one_lt_card (α := K)
    omega
  by_cases hn1 : n = 1
  · subst hn1
    have hAnL : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_of_commutator_eq hLA
    have hAn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl =>
      B19Aux.conj_mem_of_le_normalizer hAnL ha hl
    have hA₁ := a_stab_irr hV hA hLq hLA hW
    have hAW : A ≤ stabSub W := B1.le_stabSub_of_invariant hA₁
    have hAZ : A ≤ stabSub (W ⊓ fixV L) :=
      B1.le_stabSub_of_invariant (isInv_inf hA₁ (B1Red.fixV_inv_of_normalizes hAn))
    obtain ⟨hLW, hLZ⟩ := stab_of_irr hW
    have hGJ : wtLA A L W ≤ ffJ (wtLA A L W) :=
      FFC.le_of_binaryNaturalSp4_one
        (fun g hg h hh => (Subgroup.mem_normalizer_iff.1 (B6.le_normalizer_ffJ _ hg) _).1 hh) hnat
    have hLH : wtL L W ≤ ffJ (wtLA A L W) := (autSec_mono le_sup_left W _).trans hGJ
    have hnormH := normal_autSec_subgroupOf hAnL (sup_le hLW hAW) (sup_le hLZ hAZ)
      (B6.ffJ_le (wtLA A L W))
    obtain ⟨S⟩ := exists_twist_data_a6 hmp hL hW hLH hnat hnormH
    exact false_of_twist_lt hV hA hLq hLA le_rfl (by simp) hW S
  · have hHL' : ffJ (wtLA A L W) = wtL L W := hHL (by omega)
    have hnat' : BinaryNaturalSp4 (wtL L W) ⊤ ⊥ n := by
      rw [← hHL']
      exact hnat
    obtain ⟨K, _, _, _, hK, ⟨S⟩⟩ := exists_twist_data_sp4 hmp hL hW (by omega) hnat'
    exact false_of_twist_lt hV hA hLq hLA hn0 hK hW S

end B69

end CFSG.Quasithin
