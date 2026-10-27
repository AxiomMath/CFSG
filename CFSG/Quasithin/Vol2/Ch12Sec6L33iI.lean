module

public import CFSG.Quasithin.Vol2.Ch12Sec6L33h
public import CFSG.Quasithin.Vol2.Ch12Sec6L33Claim
public import CFSG.Quasithin.Vol2.Ch12Sec6L33FFI
public import CFSG.Quasithin.Background.F918C8

public section

namespace CFSG.Quasithin.H13.L1233

open CFSG.Open CFSG.Quasithin S126 F126

attribute [local instance] commGroupOfFact

theorem claim12_6_33ab_of_I (hFF : FFSteps12633I) (hD36 : D36)
    (hD37 : D37) (hD321 : D321) (hI5 : Insp5a) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) :
    Claim12_6_33ab := by
  intro G _ _ T L V _ F hH hZ H K hIs h2 h918 t ht htK
  have h := h918.toHypF98.toHypF91
  have hO2 : pCoreOf 2 H ≠ ⊥ := fun h0 => h.V₁_ne_bot (le_bot_iff.1 (h0 ▸
    h.V₁_le_Vp.trans ((le_conjClosure _ _).trans h.conjClosure_Vp_le_pCoreOf)))
  have hSQ : SQTKGroup ↥H :=
    sqtkGroup_of_pCoreOf_ne_bot hH.hyp.qtke hH.hyp.simple hH.hyp.nonabelian hO2
  obtain ⟨I, hV₁I, hIU, W, hW, hirr⟩ := exists_isIrrPlusTildeU h918
  have hI := isIrrPlusTilde_of_module h918 hV₁I hIU (isIrrPlusTildeT_of_ambient h918 hIU W hW hirr)
  have ht' : t⁻¹ ∈ T := T.inv_mem ht
  have htK' : t⁻¹ ∉ Subgroup.normalizer (K : Set G) := fun h' =>
    htK (by simpa using Subgroup.inv_mem _ h')
  have h5 := (F918_5' h918 hSQ h2.1 hV₁I hIU W hW hirr hD36 hD37 hD321 hI5 hA37 hA38).2 t⁻¹ ht'
    htK'
  have hIHU : conjClosure I H ≤ conjClosure F.V5 H := conjClosure_le_conjClosure_U hIU le_rfl
  have hV₁IH : F.V1 ≤ conjClosure I H := hV₁I.trans (le_conjClosure I H)
  have hIHN : conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    sup_le (h918.K₀_le_H.trans (le_normalizer_conjClosure I H))
      (h918.T_le_H.trans (le_normalizer_conjClosure I H))
  have h6 := h918.F918_6 hV₁IH hIHU hIHN (tildeOf_conjClosure_ne_bot h918 hIU hI)
    (h918.tilde_commutator_conjClosure hIU hI)
  obtain ⟨⟨hs1a, hs1b⟩, hs2, hs3⟩ :=
    hFF G T L V F hH hZ H K hIs h2 h918 I hV₁I hIHU hIHN
      (tildeOf_conjClosure_ne_bot h918 hIU hI) (h918.tilde_commutator_conjClosure hIU hI)
  have hUK := tilde_commutator_eq F h918 h2
  have key : tildeOf F.V1 (conjClosure I H) = tildeOf F.V1 (conjClosure F.V5 H) ∨
      (IsFFInt (tildeOf F.V1 (conjClosure K T ⊔ T)) (tildeOf F.V1 (conjClosure I H))
          (h918.isElemAbelian_tilde_of_le hIHU) ∧
        IsFFInt (secImg (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)
            (conjClosure K T ⊔ T))
          (secImg (Subgroup.normalizer (conjClosure I H : Set G)) (conjClosure I H)
            (conjClosure F.V5 H))
          (h918.isElemAbelian_quotient (conjClosure I H))) := by
    rcases h6 with ha | hb | hc
    · exact Or.inl (ha.trans hUK)
    · exact Or.inr hb
    · exact (hc.elim hs1a hs1b).elim
  have hKH : K ≤ H := le_of_mem_cComp h918.K_cComp
  have hK₂H : conjSub t⁻¹ K ≤ H := by
    rintro _ ⟨k, hk, rfl⟩
    exact H.mul_mem (H.mul_mem (H.inv_mem (h918.T_le_H ht)) (hKH hk))
      (H.inv_mem (H.inv_mem (h918.T_le_H ht)))
  have hUa : ⁅⁅conjClosure F.V5 H, K⁆, conjSub t⁻¹ K⁆ ≤ conjClosure I H := by
    rcases key with he | ⟨-, hff⟩
    · have hUN : conjClosure F.V5 H ≤ Subgroup.normalizer (F.V1 : Set G) :=
        h918.conjClosure_le_normalizer_V₁ (le_conjClosure F.V5 H)
      have hXU : ⁅⁅conjClosure F.V5 H, K⁆, conjSub t⁻¹ K⁆ ≤ conjClosure F.V5 H :=
        commutator_le_conjClosure (commutator_le_conjClosure le_rfl hKH) hK₂H
      exact le_of_tildeOf_le (hXU.trans hUN) hV₁IH ((secImg_mono hXU).trans he.ge)
    · exact hs3 hff hUK t ht htK
  have := factElem h918 hIU
  have hconj : conjAutSub (actH h918.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
      ⟨t⁻¹, h918.T_le_H ht'⟩) (autIH F.V1 I H K) = autIH F.V1 I H (conjSub t⁻¹ K) := by
    rw [autIH_eq_map h918 hKH, autIH_eq_map h918 hK₂H]
    exact conjAutSub_map_subgroupOf _ _
  have hdvd : Nat.card ↥(autIH F.V1 I H K) ∣ 60 := by
    have hd := card_autIH_dvd h918 hIU hKH
    obtain ⟨e₁⟩ := h2.2.1
    rwa [Nat.card_congr e₁.toEquiv, S126.card_alternatingGroup_five] at hd
  rcases h5 with ⟨hV, -, n, hPSL, hO⟩ | ⟨hV, -, hPSL, -⟩ | hiii | hiii
  ·
    have hO' := omega4_of_autSub_eq_top hV hO
    have hn := eq_two_of_isPSL_of_dvd (isPSL_of_autSub_top hV hPSL) hdvd
    subst hn
    right
    rcases key with he | ⟨hff, -⟩
    · exact omega4_autOn_congr _ _ he hO'
    · exact (hs2 hO' hff).elim
  ·
    exact (false_of_isPSL_three_two_of_dvd (isPSL_of_autSub_top hV hPSL) hdvd).elim
  ·
    left
    refine ⟨I, hV₁I, hIU, hI, hUa, ?_⟩
    have hs := hiii.2.1
    rw [hconj] at hs
    exact comm_comm_le_of_commV_le h918 hIU hKH hK₂H hs
  ·
    left
    refine ⟨I, hV₁I, hIU, hI, hUa, ?_⟩
    have hs := hiii.2.1
    rw [conjAutSub_inv_conjAutSub, hconj] at hs
    exact comm_comm_swap h918 h2 ht htK (le_normalizer_conjClosure I H)
      (comm_comm_le_of_commV_le h918 hIU hK₂H hKH hs)

end CFSG.Quasithin.H13.L1233
