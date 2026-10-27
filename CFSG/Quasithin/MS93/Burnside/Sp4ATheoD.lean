module

public import CFSG.Quasithin.MS93.Burnside.Sp4ARig

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideSp4A_uq_inf_le_comm (h : PUHyp M T L) {k : ℕ} {F : Type} [Field F] [Fintype F]
    [CharP F 2] (hcard : Fintype.card F = 2 ^ k) (hk : 2 ≤ k)
    {φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSp 2 F)} (hφs : Function.Surjective φ)
    (hφ : IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L)
      (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) φ false 1)
    {ν : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) ν (baseA _))
    (hνK : S33.pre h.le (ZM _ ν) ≤ L ⊔ pCoreOf 2 M) :
    Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤ ⁅Uq M T L, S33.pre h.le (ZM _ ν)⁆ := by
  have hF4 : 4 ≤ Fintype.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hFn : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
  have hφ' : IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L) (Uq M T L ⊓ Zq M L) φ
      false 1 := by
    rw [h.Uq_inf_Zq]
    exact hφ
  have hKM : L ⊔ pCoreOf 2 M ≤ M := sup_le h.L_le (pCoreOf_le' M)
  obtain ⟨-, -, β, hβ, hβker, hβα⟩ := id hφ'
  have hAβ := S33.isCoordAct_of_natSp hβα
  have hCfix : ∀ a ∈ L ⊔ pCoreOf 2 M, ∀ z ∈ Uq M T L ⊓ Zq M L, a * z * a⁻¹ = z := by
    have hle : L ⊔ pCoreOf 2 M ≤
        Subgroup.centralizer ((Uq M T L ⊓ Zq M L : Subgroup G) : Set G) := by
      refine sup_le (fun l hl => ?_) (fun t ht => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (Subgroup.mem_centralizer_iff.mp hz.2.2 l hl).symm
      · exact Subgroup.centralizer_le inf_le_left (S34F.pCoreOf_le_centralizer_Uq h ht)
    intro a ha z hz
    rw [(Subgroup.mem_centralizer_iff.mp (hle ha) z hz).symm, mul_inv_cancel_right]
  by_contra hnle
  have hnle' : ¬ Uq M T L ⊓ Zq M L ≤ ⁅Uq M T L, S33.pre h.le (ZM _ ν)⁆ := by
    rwa [h.Uq_inf_Zq]
  obtain ⟨Q, hQ, hΓQ⟩ := S33.le_orthSp_of_not_le h hKM hβ hβker hAβ (by omega) hcard
    le_sup_left hφs hCfix hnle'
  have hα := burnsideSp4A_rig_surj_L h hφs hφ'
  have hnatL : IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Zq M L)
      (φ.comp (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ pCoreOf 2 M))) false 1 := by
    obtain ⟨hN, hZV, β', hβs, hβk, hβe⟩ := hφ'
    exact ⟨fun a ha => hN ((le_sup_left : L ≤ L ⊔ pCoreOf 2 M) ha), hZV, β', hβs, hβk,
      fun a u v huv i => hβe (Subgroup.inclusion le_sup_left a) u v huv i⟩
  have hc' := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
  obtain ⟨μ, hμ, hrel₁, hrel₂⟩ := S33.exists_conj_vertex h hc'
  obtain ⟨α₁, hnat₁⟩ := S33.natural_data_of_sp h hcard hF4 hα hnatL hμ
  set Γ := ((S33.pre h.le (ZM _ ν)).subgroupOf (L ⊔ pCoreOf 2 M)).map φ with hΓ
  rcases S33.shapes_at h hc' hμ hrel₁ hrel₂ (sup_le h.L_le (S33.pre_le h.le _)) hnat₁
      le_sup_right hKM hφ' hνK with ⟨-, ⟨p, hp, hpe⟩, -, -⟩ | ⟨-, hq2, -, hfix⟩
  ·
    have hpe' : Γ = MSP.xPoint p := hpe
    have hle : Nat.card Γ ≤ 2 := by
      refine le_trans (Subgroup.card_le_of_le (le_inf (le_of_eq hpe') hΓQ)) ?_
      exact MSP.card_xPoint_inf_orthSp_le hQ hp
    rw [hpe', MSP.card_xPoint hp, hFn] at hle
    omega
  obtain ⟨c₂⟩ := MSP.nonempty_natCoord hφ'
  have hΓcard : Nat.card Γ = (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ ν) := by
    rw [hΓ, S33.card_image_eq_relIndex h hKM c₂ hνK, S33.relIndex_qv_zm_eq h hc]
  obtain ⟨hEab, hE2, hUE, -, -⟩ := S33.pre_zm_props h hc
  have hq := S33.commSp_le_fixSp_of_quadratic h hKM hβ hβker hAβ hνK hEab hUE
  have hΓq : Fintype.card F ^ 2 ≤ Nat.card Γ := by
    rw [hΓcard]
    exact hq2
  have hΓ2 : IsPGroup 2 Γ := by
    rintro ⟨_, e, he, rfl⟩
    exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, ← map_pow,
      show e ^ 2 = 1 from Subtype.ext (by simpa using hE2 _ (Subgroup.mem_subgroupOf.1 he)),
      map_one, Subgroup.coe_one])⟩
  obtain ⟨hl, hΓl, -⟩ := S33.line_of_quadratic hΓ2 hq hfix
  have hle : Nat.card Γ ≤ 2 * Nat.card F :=
    le_trans (Subgroup.card_le_of_le (le_inf hΓl hΓQ)) (MSP.card_qLine_inf_orthSp_le hQ hl).1
  rw [hFn] at hle
  have h4q : 4 * Fintype.card F ≤ Fintype.card F ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul_right _ hF4
  omega

end CFSG.Quasithin.MS93.S4L
