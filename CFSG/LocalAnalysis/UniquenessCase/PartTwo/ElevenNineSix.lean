module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ub
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace ElevenNine

theorem no_critical (D : Data G) (hSig : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h111 : F11.R111 D) (h112 : F11.R112 D)
    {V₀ V : Subgroup G} (hV : F11.Hyp11 D V₀ V) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {D₁ : Subgroup (Bar2 D.M)} [D₁.Normal]
    (hD₁N : D₁ ≤ barImage D.M (F11.CTilde D.M V₀ V)) (hD₁p : IsPGroup r ↥D₁)
    (hnc : ¬ IsCyclic ↥D₁) (hexp : ∀ x ∈ D₁, x ^ r = 1) (hcl : ⁅⁅D₁, D₁⁆, D₁⁆ = ⊥) : False := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨-, hO, hXM⟩ := hyp11_ctilde D hV
  have h112V := h112 V₀ V hV
  have h3 := h111 V₀ V hV
  by_cases hs2 : D.sig2.Nonempty
  · have h := h112V hs2
    have hN : barImage D.M (F11.CTilde D.M V₀ V) = ⊥ := by
      rw [h]
      exact uc22p22u_barImage_pCore D.M
    have hD1 : D₁ = ⊥ := le_bot_iff.1 (hN ▸ hD₁N)
    exact hnc (by rw [hD1]; infer_instance)
  · have hσ1 : D.sig ⊆ D.sig1 := by
      intro q hq
      have h4 : q ∈ D.sig1 ∪ D.sig2 ∪ D.sig3 := D.sig_sub ▸ hq
      rcases h4 with (h | h) | h
      · exact h
      · exact absurd ⟨q, h⟩ hs2
      · rw [h3] at h
        exact absurd h (Set.notMem_empty _)
    have hYX : barPreimage D.M D₁ ≤ F11.CTilde D.M V₀ V :=
      uc22p22u_barPreimage_le hO hD₁N
    have hYM : barPreimage D.M D₁ ≤ D.M := uc22p21c_barPreimage_le D.M D₁
    have hYn := uc22p22u_barPreimage_normalizes (D := D₁)
    obtain ⟨P, hPsyl, hPbar, hPK⟩ := uc22p22u_exists_lift hr hr2 hD₁p
    have hPY : P ≤ barPreimage D.M D₁ := (CFSG.ABGLocalTools.isSylowOf_iff.1 hPsyl).1
    have hPp : IsPGroup r ↥P := (CFSG.ABGLocalTools.isSylowOf_iff.1 hPsyl).2.1
    have hPX : P ≤ F11.CTilde D.M V₀ V := hPY.trans hYX
    have hPM : P ≤ D.M := hPX.trans hXM
    obtain ⟨hPe, hPc, hPnc⟩ := uc22p22u_lift_props (r := r) hPbar hPK hPM
    have hPexp := hPe hexp
    have hPcl := hPc hcl
    have hPnc' := hPnc hnc
    have hΓ : rankThreeGamma 1 r P ≤ D.M := by
      by_cases hrσ : r ∈ D.sig
      · exact gamma_le_of_stronglyEmbedded D hr (hSig.sig1_sp r (hσ1 hrσ)) hPM hPp
      · obtain ⟨p₁, hp₁⟩ := hSig.nonempty
        have hp₁1 : p₁ ∈ D.sig1 := hσ1 hp₁
        have hsp := hSig.sig1_sp p₁ hp₁1
        obtain ⟨hp₁pr, hp₁2⟩ := D.sig_prime p₁ hp₁
        have hcard := uc22p22u_card_barPreimage D.M D₁
        have hp₁Y : ¬ p₁ ∣ Nat.card ↥(barPreimage D.M D₁) := by
          rw [hcard]
          intro hd
          rcases (Nat.Prime.dvd_mul hp₁pr).1 hd with h | h
          · obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (uc22p21c_isPGroup_pCoreOf D.M)
            rw [hk] at h
            exact hp₁2 ((Nat.prime_dvd_prime_iff_eq hp₁pr Nat.prime_two).1
              (hp₁pr.dvd_of_dvd_pow h))
          · obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hD₁p
            rw [hk] at h
            have : p₁ = r := (Nat.prime_dvd_prime_iff_eq hp₁pr hr).1 (hp₁pr.dvd_of_dvd_pow h)
            exact hrσ (this ▸ hp₁)
        have hrank :=
          uc22p22u_pRank_le_normalizer_sylow hp₁pr hr (hYX.trans hXM) hYn hPsyl hp₁Y
        have hrank' : CFSG.Open.pRank p₁ (D.M ⊓ normalizer (P : Set G)) ≤
            CFSG.Open.pRank p₁ D.M := CFSG.SectionRank.pRank_mono hp₁pr.one_lt inf_le_left
        have hthree : 3 ≤ CFSG.Open.pRank p₁ D.M := hSig.three_le p₁ hp₁
        exact h77 hσ1 p₁ hp₁ hp₁2 hsp r hr hr2 hrσ P hPM hPp hPnc' hPexp hPcl (by omega)
          (le_antisymm hrank hrank')
    rcases card_le_four_or_eight_le D hV with h4 | h8
    · have h1 := isCyclic_inf_ctilde D h61 h63 hV h4 hr hr2 hPM hPp (Or.inl hΓ)
      have hPC : P ⊓ F11.CTilde D.M V₀ V = P := inf_eq_left.2 hPX
      rw [hPC] at h1
      exact hPnc' h1
    · have hD' : D₁ ≤ barImage D.M (P ⊔ pCoreOf 2 D.M) := by
        intro q hq
        rw [← hPbar] at hq
        obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hq
        exact uc22p21c_mem_barImage.2 ⟨m, Subgroup.mem_sup_left hm, rfl⟩
      have hYP : barPreimage D.M D₁ ≤ P ⊔ pCoreOf 2 D.M :=
        uc22p22u_barPreimage_le le_sup_right hD'
      have hperm : Permutes P D.T := permutes_of_le_sup_pCore D.sylowM hYM hYn hPY hYP
      exact (hV.2.2 h8).2 P ⟨r, hr, hr2, hPM, hPp, hPexp, hPnc', hperm, hΓ,
        Or.inr ⟨P, hPnc', exists_sylow_normalizer hr hYM hYn hPsyl, hΓ⟩⟩

theorem c116_of_hyp11 (D : Data G) (hSig : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h111 : F11.R111 D) (h112 : F11.R112 D)
    {V₀ V : Subgroup G} (hV : F11.Hyp11 D V₀ V) : C116 D V₀ V := by
  have hn : D.M ≤ normalizer ((F11.CTilde D.M V₀ V : Subgroup G) : Set G) :=
    (hyp11_ctilde D hV).1
  haveI hNn : (barImage D.M (F11.CTilde D.M V₀ V)).Normal := uc22p22u_barImage_normal hn
  have hQ2 : CFSG.pCore 2 (Bar2 D.M) = ⊥ :=
    CFSG.RankThree.PartTwo.Sec11.pCore_quotient_pCore ↥D.M 2
  have hcyc : IsCyclic ↥(CFSG.fittingSubgroup ↥(barImage D.M (F11.CTilde D.M V₀ V))) :=
    uc22p22u_fitting_isCyclic _ hQ2 fun r hr hr2 D₁ hD₁n hD₁N hD₁p hnc hexp hcl =>
      haveI := hD₁n
      no_critical D hSig h61 h63 h77 h111 h112 hV hr hr2 hD₁N hD₁p hnc hexp hcl
  refine ⟨hcyc, ?_⟩
  haveI : ((CFSG.fittingSubgroup ↥(barImage D.M (F11.CTilde D.M V₀ V))).map
      (barImage D.M (F11.CTilde D.M V₀ V)).subtype).Normal := inferInstance
  haveI : IsCyclic ↥((CFSG.fittingSubgroup ↥(barImage D.M (F11.CTilde D.M V₀ V))).map
      (barImage D.M (F11.CTilde D.M V₀ V)).subtype) :=
    (uc22p22u_isCyclic_map_iff _ (Subgroup.subtype_injective _) _).2 hcyc
  exact uc22p21c_commutator_le_centralizer_of_cyclic _

end ElevenNine

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
