module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3Row
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3Row8T
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3E9Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s1614e3_row8_false (D : Data G) (hx : DataExt D) (hSg : UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h1219 : D.sig = D.sig1)
    {V L : Subgroup G} (hV : IsElemAbelian 2 V) (hc : Counterex16 D ⊥ V L hV)
    (h8 : Case168_8 D ⊥ V hV) (hM : 1 < mBar D.M ⊥ V hV) {U : Subgroup G}
    (hU : Min1614 D V U) (hUΓ : U ∉ gammaEleven D.M V) : False := by
  have h3σ : (3 : ℕ) ∈ D.sig := by rw [h8.2.2]; exact Set.mem_singleton 3
  have hk1 : D.k = 1 := Data.k_eq_one_of_three_mem D hSg h1219 h3σ
  have hrk8 : rk (Vtil ⊥ V hV) = 8 := by
    have := h8.2.1
    rwa [rk_top] at this
  have hT := s15_Infra_vtil_sq_eq_one (⊥ : Subgroup G) V hV
  have hind := TwelveSeventeen.isIndivisible D hx h61 h127 h1214 hc.setting.hyp16.hyp125
  have hAX : fstarBar D.M ⊥ V hV ≤ Mbar D.M ⊥ V hV := Subgroup.map_subtype_le _
  have hn : ∀ g ∈ Mbar D.M ⊥ V hV, ∀ a ∈ fstarBar D.M ⊥ V hV,
      g * a * g⁻¹ ∈ fstarBar D.M ⊥ V hV := fun g hg a ha => s16t_fstarBar_conj_mem D hV hg ha
  have hcc : ∀ g ∈ Mbar D.M ⊥ V hV, (∀ a ∈ fstarBar D.M ⊥ V hV, g * a = a * g) →
      g ∈ fstarBar D.M ⊥ V hV := fun g hg hcomm => s16t_fstarBar_selfCentralizing D hV hg hcomm
  have hAcard : Nat.card (fstarBar D.M ⊥ V hV) = 9 := by
    rw [s16c167_card_isElemAbelianOfRank h8.1]; norm_num
  have hfix : fixV (fstarBar D.M ⊥ V hV) = ⊥ := by
    refine s16t_fixV_eq_bot_of_indivisible hT hind hn ?_ ?_
    · rw [hAcard]; decide
    · intro h; rw [h, Subgroup.card_bot] at hAcard; omega
  refine s1614e3_false_of_row D hx h61 h127 hV hc hU hUΓ (by omega) (by omega) ?_
  intro t ht ht2 hkt W hW hWr
  right
  refine ⟨3, h3σ, s1614e3_row8_pRank hAX h8.1 hn hcc, ?_⟩
  intro E hEX hE
  obtain ⟨e, heE, he1, heA⟩ := s1614e3_row8_inter hAX h8.1 hn hcc hEX hE
  have ht2' : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht2, pow_two] at this
    exact this
  have hnc : ∃ a ∈ fstarBar D.M ⊥ V hV, t * a ≠ a * t := by
    by_contra hcon
    push Not at hcon
    have htA := hcc t ht (fun a ha => hcon a ha)
    have hdvd : orderOf t ∣ Nat.card (fstarBar D.M ⊥ V hV) := by
      have := Subgroup.orderOf_dvd_natCard (fstarBar D.M ⊥ V hV) htA
      simpa using this
    rw [ht2, hAcard] at hdvd
    omega
  refine ⟨e, heE, he1, ?_⟩
  exact s1614e3_row8_witness hT h8.2.1 h8.1 hfix ht2' (fun a ha => hn t ht a ha) hnc hW
    (by omega) heA

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
