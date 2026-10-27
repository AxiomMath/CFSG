module

public import CFSG.Quasithin.MS93.S512NCoc
public import CFSG.Quasithin.MS93.S33SpShape
public import CFSG.Quasithin.MS93.S33LamM
public import CFSG.Quasithin.MS93.S34FFlat

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem burnsideSp4A_rig_phi_eq_one (h : PUHyp M T L) {F : Type} [Field F]
    {φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSp 2 F)}
    (hφ : IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L) (Uq M T L ⊓ Zq M L) φ false 1)
    (x : ↥(L ⊔ pCoreOf 2 M)) (hx : (x : G) ∈ pCoreOf 2 M) : φ x = 1 := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hφ
  refine (S33.image_eq_one_iff h (sup_le h.L_le (pCoreOf_le' M)) c x).2
    ⟨pCoreOf_le' M hx, fun u hu => ?_⟩
  have hc := Subgroup.mem_centralizer_iff.mp (S34F.pCoreOf_le_centralizer_Uq h hx) u hu
  rw [commutatorElement_eq_one_iff_mul_comm.2 hc]
  exact one_mem _

theorem burnsideSp4A_rig_surj_L (h : PUHyp M T L) {F : Type} [Field F]
    {φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSp 2 F)} (hφs : Function.Surjective φ)
    (hφ : IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L) (Uq M T L ⊓ Zq M L) φ false 1) :
    Function.Surjective (φ.comp (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ pCoreOf 2 M))) := by
  intro y
  obtain ⟨x, rfl⟩ := hφs y
  have hx : (x : G) ∈ ((L ⊔ pCoreOf 2 M : Subgroup G) : Set G) := x.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L (pCoreOf 2 M)
    (h.L_le.trans (MS93.le_normalizer_pCoreOf M))] at hx
  obtain ⟨l, hl, t, ht, hlt⟩ := hx
  refine ⟨⟨l, hl⟩, ?_⟩
  have htK : t ∈ L ⊔ pCoreOf 2 M := Subgroup.mem_sup_right ht
  have e : x = Subgroup.inclusion (le_sup_left : L ≤ L ⊔ pCoreOf 2 M) ⟨l, hl⟩ * ⟨t, htK⟩ :=
    Subtype.ext hlt.symm
  rw [e, map_mul, burnsideSp4A_rig_phi_eq_one h hφ ⟨t, htK⟩ ht, mul_one]
  rfl

theorem burnsideSp4A_rigid_pre_zm (h : PUHyp M T L) {k : ℕ} {F : Type} [Field F] [Fintype F]
    [CharP F 2] (hcard : Fintype.card F = 2 ^ k) (hk : 2 ≤ k)
    {φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSp 2 F)} (hφs : Function.Surjective φ)
    (hφ : IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L)
      (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) φ false 1)
    {ν : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) ν (baseA _))
    (hνK : S33.pre h.le (ZM _ ν) ≤ L ⊔ pCoreOf 2 M) :
    S512N.Rigid (((S33.pre h.le (ZM _ ν)).subgroupOf (L ⊔ pCoreOf 2 M)).map φ) := by
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
  have hα := burnsideSp4A_rig_surj_L h hφs hφ'
  have hnatL : IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Zq M L)
      (φ.comp (Subgroup.inclusion (le_sup_left : L ≤ L ⊔ pCoreOf 2 M))) false 1 := by
    obtain ⟨hN, hZV, β, hβs, hβk, hβe⟩ := hφ'
    exact ⟨fun a ha => hN ((le_sup_left : L ≤ L ⊔ pCoreOf 2 M) ha), hZV, β, hβs, hβk,
      fun a u v huv i => hβe (Subgroup.inclusion le_sup_left a) u v huv i⟩
  have hc' := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
  obtain ⟨μ, hμ, hrel₁, hrel₂⟩ := S33.exists_conj_vertex h hc'
  obtain ⟨α₁, hnat₁⟩ := S33.natural_data_of_sp h hcard hF4 hα hnatL hμ
  rcases S33.shapes_at h hc' hμ hrel₁ hrel₂ (sup_le h.L_le (S33.pre_le h.le _)) hnat₁
      le_sup_right hKM hφ' hνK with ⟨-, ⟨p, hp, hpe⟩, -, -⟩ | ⟨-, hq2, -, hfix⟩
  ·
    rw [hpe]
    exact S512N.rigid_xPoint (by rw [hFn]; omega) hp
  obtain ⟨c₂⟩ := MSP.nonempty_natCoord hφ'
  have hΓcard : Nat.card (((S33.pre h.le (ZM _ ν)).subgroupOf (L ⊔ pCoreOf 2 M)).map φ) =
      (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ ν) := by
    rw [S33.card_image_eq_relIndex h hKM c₂ hνK, S33.relIndex_qv_zm_eq h hc]
  obtain ⟨hEab, hE2, hUE, -, -⟩ := S33.pre_zm_props h hc
  obtain ⟨-, -, β, hβ, hβker, hβα⟩ := id hφ'
  have hAβ := S33.isCoordAct_of_natSp hβα
  have hq := S33.commSp_le_fixSp_of_quadratic h hKM hβ hβker hAβ hνK hEab hUE
  set Γ := ((S33.pre h.le (ZM _ ν)).subgroupOf (L ⊔ pCoreOf 2 M)).map φ with hΓ
  have hΓq : Fintype.card F ^ 2 ≤ Nat.card Γ := by
    rw [hΓcard]
    exact hq2
  have hΓ2 : IsPGroup 2 Γ := by
    rintro ⟨_, e, he, rfl⟩
    exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, ← map_pow,
      show e ^ 2 = 1 from Subtype.ext (by simpa using hE2 _ (Subgroup.mem_subgroupOf.1 he)),
      map_one, Subgroup.coe_one])⟩
  obtain ⟨hl, hΓl, -⟩ := S33.line_of_quadratic hΓ2 hq hfix
  intro B m hvan
  by_contra hB0
  obtain ⟨g₀, hg₀⟩ := MSP.exists_map_ln₀_eq hl
  rw [← hg₀, MSP.qLine_map_eq] at hΓl
  set J₀ := Γ.map (MulAut.conj g₀⁻¹).toMonoidHom with hJ₀
  have hJ₀eq : J₀.map (MulAut.conj g₀).toMonoidHom = Γ := by
    rw [hJ₀, Subgroup.map_map]
    have : ((MulAut.conj g₀).toMonoidHom.comp (MulAut.conj g₀⁻¹).toMonoidHom) =
        MonoidHom.id _ := by
      refine MonoidHom.ext fun y => ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
        MonoidHom.id_apply]
      group
    rw [this, Subgroup.map_id]
  have hJ₀Q : J₀ ≤ MSP.Q₁ F := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have := hΓl hz
    rw [MSP.mem_map_conj] at this
    simpa using this
  have hvan₀ := S5.cform_vanish_of_conj (S512N.cform_mul B m) (fun _ => rfl) (A := J₀)
    (g₀ := g₀) (by rw [hJ₀eq]; exact hvan)
  have hcJ : Nat.card J₀ = Nat.card Γ :=
    Subgroup.card_map_of_injective (MulAut.conj g₀⁻¹).injective
  have hle := S5.card_le_of_cform_Q₁ hB0 (S := (J₀ : Set (MSP.Sp4 F))) (fun y hy => hJ₀Q hy)
    hvan₀
  have hJc : Nat.card (J₀ : Set (MSP.Sp4 F)) = Nat.card J₀ := rfl
  rw [hJc, hcJ, hFn] at hle
  have h4q : 4 * Fintype.card F ≤ Fintype.card F ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul_right _ hF4
  omega

end CFSG.Quasithin.MS93.S4L
