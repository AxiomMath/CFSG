module

public import CFSG.RankThree.GF2n.Tim81.Cited.Sec7
import CFSG.RankThree.GF2n.Tim81.Cited.UnitaryTIModuleEven
import CFSG.RankThree.GF2n.Tim81.Cited.UnitaryTIModuleSL2
import CFSG.RankThree.GF2n.Tim81.Cited.UnitaryPerpCount

public section

namespace CFSG.RankThree.GF2n.Tim81

open Matrix CFSG.RankThree.FFModules CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.RankThree.GF2n.Tim81.TIModule

private theorem commSpan_map {G K W : Type*} [Group G] [Group K] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) K W) (Φ : G →* K) (T : Subgroup G) :
    commSpan ρ (T.map Φ) = commSpan (ρ.comp Φ) T := by
  have hS : {u | ∃ a ∈ T.map Φ, ∃ w, u = ρ a w - w} =
      {u | ∃ t ∈ T, ∃ w, u = (ρ.comp Φ) t w - w} := by
    ext u
    constructor
    · rintro ⟨a, ha, w, rfl⟩
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 ha
      exact ⟨t, ht, w, rfl⟩
    · rintro ⟨t, ht, w, rfl⟩
      exact ⟨Φ t, Subgroup.mem_map.2 ⟨t, ht, rfl⟩, w, rfl⟩
  change Submodule.span (ZMod 2) _ = Submodule.span (ZMod 2) _
  rw [hS]

theorem unitaryTIModule : UnitaryTIModule := by
  intro K _ _ X₀ Δ f n hf hn hf2 hX W _ _ _ ρ hnt hTI hcard U hU
  obtain ⟨Φ, hker, hrange, hΔ⟩ := hX
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hF : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := card_galoisField_two_mul hf
  have hσF := unitaryInvolution_involutive hF
  have htr : ∀ a, unitaryInvolution (GaloisField 2 (2 * f)) 2 f a = a →
      ∃ c, c + unitaryInvolution (GaloisField 2 (2 * f)) 2 f c = a :=
    fun a ha => exists_add_unitaryInvolution_eq hF ha
  set σ : Representation (ZMod 2)
    (SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) (m + 2)) W := ρ.comp Φ with hσdef
  have hσ : ∃ x w, σ x w ≠ w := by
    obtain ⟨x, hx, w, hw⟩ := hnt
    rw [← hrange] at hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨y, w, hw⟩
  have hUσ : ∀ x, ∀ u ∈ U, σ x u ∈ U := fun x u hu =>
    hU (Φ x) (hrange ▸ ⟨x, rfl⟩) ⟨u, hu, rfl⟩
  have hΔ' : ∀ A, A ∈ Δ ↔ ∃ x, A = (conjSub (Unitary.rootGroup
      (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) hσF (m + 2)
      (unitaryLongRoot (m + 2) (by omega))) x).map Φ := hΔ
  rcases Nat.even_or_odd m with heven | hodd
  ·
    have hTIσ : IsTIRep σ := by
      intro a b ha0 haa hb0 hbb
      have hA := SUTrans.map_mem hσF htr (by omega) hΔ' ha0 haa
        (isUTransGroup_transvGroup hσF haa)
      have hB := SUTrans.map_mem hσF htr (by omega) hΔ' hb0 hbb
        (isUTransGroup_transvGroup hσF hbb)
      have h : commSpan ρ ((transvGroup (unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
            (m + 2) a).map Φ) =
          commSpan ρ ((transvGroup (unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
            (m + 2) b).map Φ) ∨
          commSpan ρ ((transvGroup (unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
            (m + 2) a).map Φ) ⊓
          commSpan ρ ((transvGroup (unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
            (m + 2) b).map Φ) = ⊥ := hTI _ hA _ hB
      rwa [commSpan_map, commSpan_map] at h
    have hm : 2 ≤ m := by omega
    have h0r : (0 : Fin (m + 2)) ≠ Fin.rev 0 := by
      rw [Fin.rev_zero]
      intro h
      have := congrArg Fin.val h
      simp at this
    have hLr : Fin.last (m + 1) ≠ Fin.rev (Fin.last (m + 1)) := by
      rw [Fin.rev_last]
      intro h
      have := congrArg Fin.val h
      simp at this
    have he₀ : uForm (unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
        (Pi.single (0 : Fin (m + 2)) 1) (Pi.single 0 1) = 0 := uForm_single_self h0r
    have heL : uForm (unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
        (Pi.single (Fin.last (m + 1)) 1) (Pi.single (Fin.last (m + 1)) 1) = 0 :=
      uForm_single_self hLr
    have he₀L : uForm (unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
        (Pi.single (0 : Fin (m + 2)) 1) (Pi.single (Fin.last (m + 1)) 1) = 1 :=
      uForm_single_zero_last
    have hnp : ∀ c : GaloisField 2 (2 * f),
        (Pi.single (Fin.last (m + 1)) 1 : Fin (m + 2) → GaloisField 2 (2 * f)) ≠
          c • Pi.single 0 1 := by
      intro c h
      have := congrArg (uForm (unitaryInvolution (GaloisField 2 (2 * f)) 2 f)
        (Pi.single (0 : Fin (m + 2)) 1)) h
      rw [he₀L, uForm_smul_right, he₀, mul_zero] at this
      exact one_ne_zero this
    obtain ⟨w, hw, hwc⟩ := exists_mem_sup_conjSub_eq hσF he₀ heL he₀L
      (isUTransGroup_transvGroup hσF he₀) (isUTransGroup_transvGroup hσF heL)
    have hpow := exists_natCard_commSpan_eq_pow hF σ (isUTransGroup_transvGroup hσF he₀)
      (isUTransGroup_transvGroup hσF heL)
      (transvComm_le_fixSub_self hF hf2 hm hσ hTIσ he₀ heL he₀L)
      (commSpan_sup_inf_fixSub_eq_bot hF hf2 hm hσ hTIσ he₀ heL he₀L)
      (transvComm_inf_eq_bot hF hf2 hm hσ hTIσ (single_one_ne_zero 0) he₀
        (single_one_ne_zero _) heL hnp)
      (natCard_transvComm hF σ (by omega) (single_one_ne_zero 0) he₀ (single_one_ne_zero _) heL)
      hw hwc
    exact eq_bot_or_eq_top_SU_of_even hF hf2 hm heven hσ hTIσ hcard hpow hUσ
  ·
    have hodd' : Odd (m + 2) := by
      obtain ⟨j, hj⟩ := hodd
      exact ⟨j + 1, by omega⟩
    exact eq_bot_or_eq_top_SU_of_odd hF hf2 (by omega) hodd' σ hσ hcard.le hUσ

end CFSG.RankThree.GF2n.Tim81
