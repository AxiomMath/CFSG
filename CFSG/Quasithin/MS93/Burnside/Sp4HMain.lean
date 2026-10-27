module

public import CFSG.Quasithin.MS93.Burnside.Sp4HQQ

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideSp4H_commSp_le_of_lam (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {μ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) μ (baseA _))
    (hμβ : geo (puAmalgam h.le) (baseA _) μ 1 = baseB _)
    {F : Type} [Field F] [Fintype F] [CharP F 2] {φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSp 2 F)}
    (hφ : IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L)
      (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) φ false 1)
    (hΛ : Module.finrank F (MSP.fixSp
      (((S33.pre h.le (ZM _ μ)).subgroupOf (L ⊔ pCoreOf 2 M)).map φ)) ≤ 2) :
    MSP.commSp (((S33.pre h.le (burnsideSp4A_zstar h μ)).subgroupOf (L ⊔ pCoreOf 2 M)).map φ) ≤
      MSP.commSp (((S33.pre h.le (ZM _ μ)).subgroupOf (L ⊔ pCoreOf 2 M)).map φ) := by
  have hKM : L ⊔ pCoreOf 2 M ≤ M := sup_le h.L_le (pCoreOf_le' M)
  have hμK := pre_zm_le_flat_sp h hU hc hμβ
  obtain ⟨hWK, hWab, hUW, hEW, -⟩ := burnsideSp4H_pre_zstar h hU hb hc hμβ
  obtain ⟨hEab, hE2, hUE, -, -⟩ := S33.pre_zm_props h hc
  have hφ' : IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L) (Uq M T L ⊓ Zq M L) φ
      false 1 := by
    rw [h.Uq_inf_Zq]
    exact hφ
  obtain ⟨-, -, β, hβ, hβker, hβα⟩ := hφ'
  have hAβ := S33.isCoordAct_of_natSp hβα
  have hΓ2 : IsPGroup 2 (((S33.pre h.le (ZM _ μ)).subgroupOf (L ⊔ pCoreOf 2 M)).map φ) := by
    rintro ⟨_, e, he, rfl⟩
    exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, ← map_pow,
      show e ^ 2 = 1 from Subtype.ext (by simpa using hE2 _ (Subgroup.mem_subgroupOf.1 he)),
      map_one, Subgroup.coe_one])⟩
  have hqE := S33.commSp_le_fixSp_of_quadratic h hKM hβ hβker hAβ hμK hEab hUE
  have hqW := S33.commSp_le_fixSp_of_quadratic h hKM hβ hβker hAβ hWK hWab hUW
  obtain ⟨-, -, hcf⟩ := S33.line_of_quadratic hΓ2 hqE hΛ
  have hΓΔ : ((S33.pre h.le (ZM _ μ)).subgroupOf (L ⊔ pCoreOf 2 M)).map φ ≤
      ((S33.pre h.le (burnsideSp4A_zstar h μ)).subgroupOf (L ⊔ pCoreOf 2 M)).map φ :=
    Subgroup.map_mono fun x hx => hEW hx
  exact hqW.trans ((MSP.fixSp_antitone hΓΔ).trans hcf.symm.le)

theorem burnsideSp4H_exists_ne_zero_neg_one {F : Type} [Field F] [Fintype F]
    (hF : 4 ≤ Fintype.card F) : ∃ l : F, l ≠ 0 ∧ l ≠ -1 := by
  classical
  by_contra hall
  push Not at hall
  have hsub : (Finset.univ : Finset F) ⊆ {0, -1} := fun l _ => by
    by_cases hl : l = 0
    · simp [hl]
    · simp [hall l hl]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ] at h1
  have h2 : ({0, -1} : Finset F).card ≤ 2 := Finset.card_le_two
  omega

theorem burnsideSp4H_exists_comm_zstar_le (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hU : IsSp4U M T L) (hF : ¬ IsSp4Full M T L) :
    ∃ μ : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) μ (baseA _) ∧
      ⁅burnsideSp4A_zstar h μ, ZM _ (baseA _)⁆ ≤ ZM _ μ := by
  have hUE := S34F.isSp4UEven_of_nonfull h hU hF
  obtain ⟨m, F, _, _, φ, hm, hcard, hφs, hφ⟩ := IsSp4UEven.exists_natural_flat h hUE
  have hcard' : Fintype.card F = 2 ^ (2 * m) := by rw [hcard, S34F.four_pow_eq]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hk : 2 ≤ 2 * m := by omega
  have hF4 : 4 ≤ Fintype.card F := by
    rw [hcard']
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨μ, hc, hμβ⟩ := burnsideSp4A_exists_crit h
  refine ⟨μ, hc, burnsideSp4H_comm_zstar_le_of_commSp_le h hUE hb hc hμβ hcard' hk hφs hφ ?_⟩
  have hKM : L ⊔ pCoreOf 2 M ≤ M := sup_le h.L_le (pCoreOf_le' M)
  have hμK := pre_zm_le_flat_sp h hUE hc hμβ
  have hφ' : IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L) (Uq M T L ⊓ Zq M L) φ
      false 1 := by
    rw [h.Uq_inf_Zq]
    exact hφ
  have hα := burnsideSp4A_rig_surj_L h hφs hφ'
  have hnatL : IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Zq M L)
      (φ.comp (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ pCoreOf 2 M))) false 1 := by
    obtain ⟨hN, hZV, β, hβs, hβk, hβe⟩ := hφ'
    exact ⟨fun a ha => hN ((le_sup_left : L ≤ L ⊔ pCoreOf 2 M) ha), hZV, β, hβs, hβk,
      fun a u v huv i => hβe (Subgroup.inclusion le_sup_left a) u v huv i⟩
  have hc' := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
  obtain ⟨μ', hμ', hrel₁, hrel₂⟩ := S33.exists_conj_vertex h hc'
  obtain ⟨α₁, hnat₁⟩ := S33.natural_data_of_sp h hcard' hF4 hα hnatL hμ'
  rcases S33.shapes_at h hc' hμ' hrel₁ hrel₂ (sup_le h.L_le (S33.pre_le h.le _)) hnat₁
      le_sup_right hKM hφ' hμK with ⟨-, ⟨p, hp, hpe⟩, hq1, -⟩ | ⟨-, -, -, hfix⟩
  ·
    have hW := burnsideSp4H_map_pre_zstar_le_xPoint h hUE hb hc hμβ
      (burnsideSp4H_exists_ne_zero_neg_one hF4) hφ hp hpe hq1
    exact (MSP.commSp_mono hW).trans (le_of_eq (congrArg MSP.commSp hpe.symm))
  ·
    exact burnsideSp4H_commSp_le_of_lam h hUE hb hc hμβ hφ hfix

theorem burnsideSp4H_g2star : burnsideSp4A_G2star := by
  intro G _ _ M T L h hmin hb hU hF
  obtain ⟨μ, hc, hcomm⟩ := burnsideSp4H_exists_comm_zstar_le h hb hU hF
  have hUE := S34F.isSp4UEven_of_nonfull h hU hF
  have hUl : Uloc h.le L (baseA _) = imM h.le (Uq M T L) := puTrans_baseA h.le (S4A.Uq_normal h)
  have hDl : Dloc h.le L (baseA _) = imM h.le (Dq M L) := puTrans_baseA h.le (S4A.Dq_normal h)
  have hUD : Uloc h.le L (baseA _) ⊔ Dloc h.le L (baseA _) = imM h.le (Uq M T L ⊔ Dq M L) := by
    rw [hUl, hDl, ← S33.imM_sup h.le (Uq_le h.L_le) (inf_le_left.trans (pCoreOf_le' M))]
  have hR1 : ZM (puAmalgam h.le) (baseA _) ≤ Uloc h.le L (baseA _) ⊔ Dloc h.le L (baseA _) := by
    rw [puAmalgam.zm_baseA, hUD]
    exact imM_mono h.le (burnsideSp4A_zq_le burnsideSp4A_lemmaC burnsideSp4A_lemmaR h hUE)
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ hc.1 (PU.isMVtx_baseA (puAmalgam h.le))
  refine ⟨g • baseA _, ?_, ?_⟩
  · have := (isCritical_smul _ g μ (baseA _)).mpr hc
    rwa [hg] at this
  · have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hcomm
    rw [Subgroup.map_commutator, ← burnsideSp4H_zstar_smul, ← zm_smul, ← zm_smul, hg] at h1
    exact h1.trans hR1

theorem burnsideSp4H_noNonlinSp4 : NoNonlinSp4 :=
  burnsideSp4A_noNonlinSp4_of_g2star burnsideSp4H_g2star

theorem burnsideSp4H_noNonlinSpGt4 : NoNonlinSpGt4 :=
  burnsideSp4A_noNonlinSpGt4_of_g2star burnsideSp4H_g2star

end CFSG.Quasithin.MS93.S4L
