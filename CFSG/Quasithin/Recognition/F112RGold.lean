module

public import CFSG.Quasithin.Recognition.F112RDefs
public import CFSG.Quasithin.Recognition.F112RShapes
public import CFSG.Quasithin.Background.F6GoldschmidtListCat
public import CFSG.Quasithin.EmptyFaithful.S1422Main

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace F112R

noncomputable def pCoreOfSubgroupOfEquiv {G : Type*} [Group G] (G0 K : Subgroup G) (h : K ≤ G0) :
    ↥(pCoreOf 2 (K.subgroupOf G0)) ≃* ↥(pCoreOf 2 K) :=
  (Subgroup.equivMapOfInjective (Open.pCore 2 ↥(K.subgroupOf G0)) (K.subgroupOf G0).subtype
      (K.subgroupOf G0).subtype_injective).symm.trans
    (((Subgroup.subgroupOfEquivOfLe h).subgroupMap _).trans
      ((MulEquiv.subgroupCongr (map_pCore_mulEquiv 2 (Subgroup.subgroupOfEquivOfLe h))).trans
        (Subgroup.equivMapOfInjective (Open.pCore 2 ↥K) K.subtype K.subtype_injective)))

noncomputable def quotPCoreEquiv {K L : Type*} [Group K] [Group L] (e : K ≃* L) :
    (K ⧸ Open.pCore 2 K) ≃* (L ⧸ Open.pCore 2 L) :=
  QuotientGroup.congr (Open.pCore 2 K) (Open.pCore 2 L) e (map_pCore_mulEquiv 2 e)

noncomputable def ofSubgroupsSubgroupOfIso {G : Type} [Group G] (G0 K₁ K₂ : Subgroup G)
    (h₁ : K₁ ≤ G0) (h₂ : K₂ ≤ G0) :
    (RankTwoAmalgam.ofSubgroups K₁ K₂).Iso
      (RankTwoAmalgam.ofSubgroups (K₁.subgroupOf G0) (K₂.subgroupOf G0)) where
  φ1 := (Subgroup.subgroupOfEquivOfLe h₁).symm
  φ12 := (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans h₁ : K₁ ⊓ K₂ ≤ G0)).symm.trans
    (MulEquiv.subgroupCongr (Subgroup.comap_inf K₁ K₂ G0.subtype))
  φ2 := (Subgroup.subgroupOfEquivOfLe h₂).symm
  comm1 _ := Subtype.ext rfl
  comm2 _ := Subtype.ext rfl

def isoTrans {α β γ : RankTwoAmalgam.{u}} (e : α.Iso β) (f : β.Iso γ) : α.Iso γ where
  φ1 := e.φ1.trans f.φ1
  φ12 := e.φ12.trans f.φ12
  φ2 := e.φ2.trans f.φ2
  comm1 g := by
    simp only [MulEquiv.trans_apply]
    rw [f.comm1, e.comm1]
  comm2 g := by
    simp only [MulEquiv.trans_apply]
    rw [f.comm2, e.comm2]

theorem isAmalgamOfGroup_of_subgroupOf {G : Type} [Group G] {G0 K₁ K₂ : Subgroup G}
    (h₁ : K₁ ≤ G0) (h₂ : K₂ ≤ G0) {P : ∀ (Y : Type) [Group Y], Prop}
    (h : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (K₁.subgroupOf G0) (K₂.subgroupOf G0)) P) :
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups K₁ K₂) P := by
  obtain ⟨Y, _, hP, T, M₁, M₂, hpair, ⟨e⟩⟩ := h
  exact ⟨Y, inferInstance, hP, T, M₁, M₂, hpair, ⟨isoTrans (ofSubgroupsSubgroupOfIso G0 K₁ K₂ h₁ h₂) e⟩⟩

end F112R

namespace Setting1422

variable {G : Type} [Group G] [Finite G] {T M Y H : Subgroup G}
variable (hSz : Nat.card ↥(Sz 0) = 20)
include hSz

theorem isGoldschmidtAmalgam (S : Setting1422 T M Y H)
    (hS3 : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3))) :
    IsGoldschmidtAmalgam (H.subgroupOf (H ⊔ (Y ⊔ T))) ((Y ⊔ T).subgroupOf (H ⊔ (Y ⊔ T))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := S.exists_sylow
  have hT₀ : T ≤ H ⊔ (Y ⊔ T) := S.T_le_H.trans le_sup_left
  exact
    { gen := by
        rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
      quotient₁ := ⟨(F112R.quotPCoreEquiv
        (Subgroup.subgroupOfEquivOfLe (le_sup_left : H ≤ H ⊔ (Y ⊔ T)))).trans hS3.some⟩
      quotient₂ := ⟨(F112R.quotPCoreEquiv
        (Subgroup.subgroupOfEquivOfLe (le_sup_right : Y ⊔ T ≤ H ⊔ (Y ⊔ T)))).trans
          S.data.quot.some⟩
      sylow := by
        have hS : (P : Subgroup G) ≤ H ⊔ (Y ⊔ T) := hP ▸ hT₀
        refine ⟨P.subtype hS, ?_⟩
        have h1 : H.subgroupOf (H ⊔ (Y ⊔ T)) ⊓ (Y ⊔ T).subgroupOf (H ⊔ (Y ⊔ T)) =
            (H ⊓ (Y ⊔ T)).subgroupOf (H ⊔ (Y ⊔ T)) := (Subgroup.comap_inf _ _ _).symm
        rw [Sylow.coe_subtype, h1, S.H_inf_YT hSz, hP]
      pCore_eq_bot := by
        have h := (S.hyp111 hSz).o2
        rw [sup_eq_left.mpr hT₀] at h
        exact (Subgroup.map_eq_bot_iff_of_injective _ (H ⊔ (Y ⊔ T)).subtype_injective).mp h }

theorem goldCaseVI (hlist : F6.GoldschmidtS3ListCat.{0}) (S : Setting1422 T M Y H)
    (hS3 : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3))) :
    F6.IsGoldCaseVICat (H.subgroupOf (H ⊔ (Y ⊔ T))) ((Y ⊔ T).subgroupOf (H ⊔ (Y ⊔ T))) ∨
      F6.IsGoldCaseVICat ((Y ⊔ T).subgroupOf (H ⊔ (Y ⊔ T))) (H.subgroupOf (H ⊔ (Y ⊔ T))) := by
  have hc₁ : CharTwo (H.subgroupOf (H ⊔ (Y ⊔ T))) :=
    F6.charTwo_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : H ≤ H ⊔ (Y ⊔ T))).symm S.charTwo_H
  have hc₂ : CharTwo ((Y ⊔ T).subgroupOf (H ⊔ (Y ⊔ T))) :=
    F6.charTwo_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (le_sup_right : Y ⊔ T ≤ H ⊔ (Y ⊔ T))).symm S.charTwo_YT
  exact F6.isGoldCaseVICat_of_charTwo (hlist _ _ _ (S.isGoldschmidtAmalgam hSz hS3)) hc₁ hc₂

omit hSz in
theorem pCoreOf_YT_ne_bot (S : Setting1422 T M Y H) : pCoreOf 2 (Y ⊔ T) ≠ ⊥ := by
  intro hbot
  have hc := S.charTwo_YT
  have hYT : Y ⊔ T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxc : x ∈ Subgroup.centralizer (pCoreOf 2 (Y ⊔ T) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hbot] at hy
      have : y = 1 := by simpa using hy
      rw [this]
      simp
    have := hc ⟨hx, hxc⟩
    rw [hbot] at this
    exact this
  have h6 := S.card_quot_YT
  have hle : Nat.card (OTwoQuot (Y ⊔ T)) ≤ Nat.card ↥(Y ⊔ T) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk_surjective)
  have hcard1 : Nat.card ↥(Y ⊔ T) = 1 := by
    rw [hYT]
    exact Subgroup.card_bot
  omega

omit hSz in
theorem nontrivial_pCoreOf_YT' (S : Setting1422 T M Y H) :
    Nontrivial ↥(pCoreOf 2 ((Y ⊔ T).subgroupOf (H ⊔ (Y ⊔ T)))) := by
  have hne := S.pCoreOf_YT_ne_bot
  have : Nontrivial ↥(pCoreOf 2 (Y ⊔ T)) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  exact (F112R.pCoreOfSubgroupOfEquiv (H ⊔ (Y ⊔ T)) (Y ⊔ T) le_sup_right).toEquiv.nontrivial

omit hSz in
theorem false_of_atMostOneInvolution (S : Setting1422 T M Y H)
    (h : F6.AtMostOneInvolution
      (centerOf (pCoreOf 2 ((Y ⊔ T).subgroupOf (H ⊔ (Y ⊔ T)))))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G0 := H ⊔ (Y ⊔ T) with hG0
  set K := (Y ⊔ T).subgroupOf G0 with hK
  set R := pCoreOf 2 K with hR
  have : Nontrivial ↥R := S.nontrivial_pCoreOf_YT'
  have hRp : IsPGroup 2 ↥R := pCoreOf_isPGroup 2 K
  have : Nontrivial ↥(Subgroup.center ↥R) := hRp.center_nontrivial
  have hZp : IsPGroup 2 ↥(Subgroup.center ↥R) := hRp.to_subgroup _
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Nat.card_eq_one_iff_unique] at hk
    obtain ⟨hsub, ⟨-⟩⟩ := hk
    obtain ⟨a, b, hab⟩ := exists_pair_ne ↥(Subgroup.center ↥R)
    exact hab (Subsingleton.elim a b)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥R)) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    omega
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  set w : ↥G0 := ((z : ↥R) : ↥G0) with hw
  have hwR : w ∈ R := (z : ↥R).2
  have hwc : ∀ r ∈ R, r * w = w * r := fun r hr => by
    have := Subgroup.mem_center_iff.mp z.2 ⟨r, hr⟩
    exact congrArg Subtype.val this
  have hw1 : w ≠ 1 := by
    intro h1
    apply hz1
    apply Subtype.ext
    apply Subtype.ext
    exact h1
  have hw2 : w ^ 2 = 1 := by
    have := congrArg (fun x : ↥(Subgroup.center ↥R) => ((x : ↥R) : ↥G0)) hz2
    simpa using this
  have hwZ : w ∈ centerOf R :=
    Subgroup.mem_inf.mpr ⟨hwR, Subgroup.mem_centralizer_iff.mpr fun r hr => hwc r hr⟩
  have hcentral : ∀ g ∈ K, g * w = w * g := by
    intro g hg
    have hnorm : ∀ x, x ∈ R ↔ g * x * g⁻¹ ∈ R :=
      fun x => Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hg) x
    have hgwZ : g * w * g⁻¹ ∈ centerOf R := by
      refine Subgroup.mem_inf.mpr ⟨(hnorm w).mp hwR, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro r hr
      have hr' : g⁻¹ * r * g ∈ R := by
        refine (hnorm (g⁻¹ * r * g)).mpr ?_
        have : g * (g⁻¹ * r * g) * g⁻¹ = r := by group
        rw [this]
        exact hr
      have hc := hwc _ hr'
      calc r * (g * w * g⁻¹) = g * ((g⁻¹ * r * g) * w) * g⁻¹ := by group
        _ = g * (w * (g⁻¹ * r * g)) * g⁻¹ := by rw [hc]
        _ = g * w * g⁻¹ * r := by group
    have hsq : (g * w * g⁻¹) ^ 2 = 1 := by
      rw [conj_pow, hw2]
      group
    have hne : g * w * g⁻¹ ≠ 1 := by
      intro h1
      apply hw1
      have : w = g⁻¹ * (g * w * g⁻¹) * g := by group
      rw [this, h1]
      group
    have := h _ hgwZ w hwZ hsq hw2 hne hw1
    calc g * w = (g * w * g⁻¹) * g := by group
      _ = w * g := by rw [this]
  have hwYT : (w : G) ∈ Y ⊔ T := pCoreOf_le 2 K hwR
  have hYG0 : Y ⊔ T ≤ G0 := le_sup_right
  apply hw1
  apply Subtype.ext
  exact S.center_YT (w : G) hwYT (fun y hy => by
    have hy' : (⟨y, hYG0 hy⟩ : ↥G0) ∈ K := hy
    have := hcentral ⟨y, hYG0 hy⟩ hy'
    exact (congrArg Subtype.val this).symm)

omit hSz in
theorem not_goldCaseVI_swapped (S : Setting1422 T M Y H) :
    ¬ F6.IsGoldCaseVICat ((Y ⊔ T).subgroupOf (H ⊔ (Y ⊔ T))) (H.subgroupOf (H ⊔ (Y ⊔ T))) := by
  intro h
  rcases h with ⟨-, -, ⟨e₁⟩, ⟨e₂⟩⟩ | ⟨-, -, ⟨e₁⟩, ⟨e₂⟩⟩ | ⟨-, -, -, -, hsp, -⟩ |
    ⟨-, -, -, -, hcp, -⟩ | ⟨-, -, -, -, hcp, -⟩ | ⟨-, -, -, -, -, -, hZ2, -⟩
  · exact S.H_not_iso_perm_four.false
      ((Subgroup.subgroupOfEquivOfLe (le_sup_left : H ≤ H ⊔ (Y ⊔ T))).symm.trans e₂)
  · exact S.YT_not_iso_z2_perm_four.false
      ((Subgroup.subgroupOfEquivOfLe (le_sup_right : Y ⊔ T ≤ H ⊔ (Y ⊔ T))).symm.trans e₁)
  · exact S.false_of_atMostOneInvolution (F6.atMostOneInvolution_of_isSpecial hsp)
  · exact S.false_of_atMostOneInvolution (F6.atMostOneInvolution_of_z4_q8 hcp)
  · exact S.false_of_atMostOneInvolution (F6.atMostOneInvolution_of_q8_q8 hcp)
  · exact S.false_of_atMostOneInvolution (F6.atMostOneInvolution_of_card_eq_two hZ2)

end Setting1422

@[expose] def F6YBridge (IsY : ∀ (W : Type) [Group W], Prop) (P : ∀ (Y : Type) [Group Y], Prop) :
    Prop :=
  ∀ (D : Type) [Group D] [Finite D] (H₁ H₂ : Subgroup D),
    F6.IsYAmalgam IsY H₁ H₂ → IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups H₁ H₂) P

structure R2aBridges : Prop where
  g22 : F6YBridge F6.IsG22 (IsG2Over 1)
  g22Prime : F6YBridge F6.IsG22Prime (fun Y _ => Nonempty (Y ≃* PSU3 3 1))
  m12 : F6YBridge F6.IsM12 (fun Y _ => Nonempty (Y ≃* quasithinM12))
  autM12 : F6YBridge F6.IsAutM12 (fun Y _ => Nonempty (Y ≃* MulAut quasithinM12))

namespace Setting1422

variable {G : Type} [Group G] [Finite G] {T M Y H : Subgroup G}

theorem caseG2_of_gold (hb : F6YBridge F6.IsG22 (IsG2Over 1)) (S : Setting1422 T M Y H)
    (hS3 : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3)))
    (h : F6.IsGoldCaseG22 (H.subgroupOf (H ⊔ (Y ⊔ T))) ((Y ⊔ T).subgroupOf (H ⊔ (Y ⊔ T)))) :
    CaseG2 H (Y ⊔ T) := by
  obtain ⟨hY, -, -, -, hsp, hcard⟩ := h
  refine ⟨F112R.isAmalgamOfGroup_of_subgroupOf le_sup_left le_sup_right (hb _ _ _ hY),
    IsL2Quot.of_perm_three hS3.some, IsL2Quot.of_perm_three S.data.quot.some,
    IsSpecialPow.of_mulEquiv (F112R.pCoreOfSubgroupOfEquiv (H ⊔ (Y ⊔ T)) H le_sup_left)
      (isSpecialPow_of_isSpecialTwoOnePlusFour hsp),
    (Nat.card_congr
      (F112R.pCoreOfSubgroupOfEquiv (H ⊔ (Y ⊔ T)) (Y ⊔ T) le_sup_right).toEquiv).symm.trans hcard⟩

theorem caseG22P_of_gold (hb : F6YBridge F6.IsG22Prime (fun Y _ => Nonempty (Y ≃* PSU3 3 1)))
    (S : Setting1422 T M Y H) (hS3 : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3)))
    (h : F6.IsGoldCaseG22Prime (H.subgroupOf (H ⊔ (Y ⊔ T)))
      ((Y ⊔ T).subgroupOf (H ⊔ (Y ⊔ T)))) : CaseG22P H (Y ⊔ T) := by
  obtain ⟨hY, -, -, -, hcp, hZ4⟩ := h
  refine ⟨F112R.isAmalgamOfGroup_of_subgroupOf le_sup_left le_sup_right (hb _ _ _ hY),
    IsL2Quot.of_perm_three hS3.some, IsL2Quot.of_perm_three S.data.quot.some,
    IsZ4StarQ8.of_mulEquiv (F112R.pCoreOfSubgroupOfEquiv (H ⊔ (Y ⊔ T)) H le_sup_left)
      (isZ4StarQ8_of_centralProduct₂ hcp),
    IsZ4Sq.of_mulEquiv
      (F112R.pCoreOfSubgroupOfEquiv (H ⊔ (Y ⊔ T)) (Y ⊔ T) le_sup_right) hZ4⟩

theorem caseM12_of_gold (hb : F6YBridge F6.IsM12 (fun Y _ => Nonempty (Y ≃* quasithinM12)))
    (S : Setting1422 T M Y H) (hS3 : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3)))
    (h : F6.IsGoldCaseM12 (H.subgroupOf (H ⊔ (Y ⊔ T))) ((Y ⊔ T).subgroupOf (H ⊔ (Y ⊔ T)))) :
    CaseM12 H (Y ⊔ T) := by
  obtain ⟨hY, -, -, -, hcp, hcard⟩ := h
  refine ⟨F112R.isAmalgamOfGroup_of_subgroupOf le_sup_left le_sup_right (hb _ _ _ hY),
    IsL2Quot.of_perm_three hS3.some,
    IsQ8Sq.of_mulEquiv (F112R.pCoreOfSubgroupOfEquiv (H ⊔ (Y ⊔ T)) H le_sup_left)
      (isQ8Sq_of_centralProduct₂ hcp),
    IsL2Quot.of_perm_three S.data.quot.some,
    (Nat.card_congr
      (F112R.pCoreOfSubgroupOfEquiv (H ⊔ (Y ⊔ T)) (Y ⊔ T) le_sup_right).toEquiv).symm.trans hcard⟩

theorem caseAutM12_of_gold
    (hb : F6YBridge F6.IsAutM12 (fun Y _ => Nonempty (Y ≃* MulAut quasithinM12)))
    (S : Setting1422 T M Y H) (hS3 : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3)))
    (h : F6.IsGoldCaseAutM12Cat (H.subgroupOf (H ⊔ (Y ⊔ T)))
      ((Y ⊔ T).subgroupOf (H ⊔ (Y ⊔ T)))) : CaseAutM12 H (Y ⊔ T) := by
  obtain ⟨hY, -, -, -, hext, hc1, hz, hc2⟩ := h
  have eH := Subgroup.subgroupOfEquivOfLe (le_sup_left : H ≤ H ⊔ (Y ⊔ T))
  have ePH := F112R.pCoreOfSubgroupOfEquiv (H ⊔ (Y ⊔ T)) H le_sup_left
  refine ⟨F112R.isAmalgamOfGroup_of_subgroupOf le_sup_left le_sup_right (hb _ _ _ hY),
    IsL2Quot.of_perm_three hS3.some,
    ⟨exists_surjective_ker_isQ8Sq_of_isExtensionWith eH hext,
      (Nat.card_congr ePH.toEquiv).symm.trans hc1, ?_⟩,
    IsL2Quot.of_perm_three S.data.quot.some,
    (Nat.card_congr
      (F112R.pCoreOfSubgroupOfEquiv (H ⊔ (Y ⊔ T)) (Y ⊔ T) le_sup_right).toEquiv).symm.trans hc2⟩
  rw [card_centerOf_eq_card_center, ← F6.card_centerOf_of_mulEquiv ePH]
  exact hz

variable (hSz : Nat.card ↥(Sz 0) = 20)
include hSz

theorem four_cases_of_goldschmidt (hlist : F6.GoldschmidtS3ListCat.{0}) (hBr : R2aBridges)
    (S : Setting1422 T M Y H) (hS3 : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3))) :
    CaseG2 H (Y ⊔ T) ∨ CaseG22P H (Y ⊔ T) ∨ CaseM12 H (Y ⊔ T) ∨ CaseAutM12 H (Y ⊔ T) := by
  rcases S.goldCaseVI hSz hlist hS3 with h | h
  · rcases h with hL32 | hSp42 | hG22 | hG22P | hM12 | hAut
    · exfalso
      obtain ⟨-, -, ⟨e₁⟩, -⟩ := hL32
      exact S.H_not_iso_perm_four.false
        ((Subgroup.subgroupOfEquivOfLe (le_sup_left : H ≤ H ⊔ (Y ⊔ T))).symm.trans e₁)
    · exfalso
      obtain ⟨-, -, -, ⟨e₂⟩⟩ := hSp42
      exact S.YT_not_iso_z2_perm_four.false
        ((Subgroup.subgroupOfEquivOfLe (le_sup_right : Y ⊔ T ≤ H ⊔ (Y ⊔ T))).symm.trans e₂)
    · exact Or.inl (caseG2_of_gold hBr.g22 S hS3 hG22)
    · exact Or.inr (Or.inl (caseG22P_of_gold hBr.g22Prime S hS3 hG22P))
    · exact Or.inr (Or.inr (Or.inl (caseM12_of_gold hBr.m12 S hS3 hM12)))
    · exact Or.inr (Or.inr (Or.inr (caseAutM12_of_gold hBr.autM12 S hS3 hAut)))
  · exact (S.not_goldCaseVI_swapped h).elim

theorem six_cases_of_inputs (hlist : F6.GoldschmidtS3ListCat.{0}) (hBr : R2aBridges)
    (hR2b : F112R2bStatement) (S : Setting1422 T M Y H) :
    CaseTits H (Y ⊔ T) ∨ Case2F4 H (Y ⊔ T) ∨ CaseG2 H (Y ⊔ T) ∨ CaseG22P H (Y ⊔ T) ∨
      CaseM12 H (Y ⊔ T) ∨ CaseAutM12 H (Y ⊔ T) := by
  rcases S.small with h | h | h
  · rcases hR2b G T M Y H S (Or.inl h) with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases hR2b G T M Y H S (Or.inr h) with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases S.four_cases_of_goldschmidt hSz hlist hBr h with h' | h' | h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h'))))

end Setting1422

theorem stageTheorem14220_of_R (hGold : F6.GoldschmidtS3ListCat.{0}) (hBr : R2aBridges)
    (hR2b : F112R2bStatement)
    (hData : Stage1422Data) (hV : Stage1426VleQ) (hLoc : Lemma14221Local)
    (hF431 : F431Statement) (hNS : ModelNotSimple) (hABG : ABGWreathedRecognition)
    (hG22p : G22pAmalgamFacts) (hI46 : CFSG.GH74.M12.S_Asc03_simple)
    (hM12 : M12AmalgamFacts) (hAut : AutM12AmalgamFacts) : StageTheorem14220 := by
  intro G _ _ T M h H hH
  have hSz := card_Sz_zero
  obtain ⟨Y, hY⟩ := hData G T M h
  have hVH : VZ T M ≤ pCoreOf 2 H := hV G T M h H hH
  constructor
  ·
    intro hsmall
    have S : Setting1422 T M Y H := ⟨h, hH, hY, hsmall.elim Or.inl fun h' => Or.inr (Or.inl h')⟩
    rcases S.six_cases_of_inputs hSz hGold hBr hR2b with hC | hC | hC | hC | hC | hC
    · exact Setting1422.tits_case hF431 S (hLoc.tits G T M Y H S hC) hC
    · exact (Setting1422.twoF4_case hF431 hNS S (hLoc.twoF4 G T M Y H S hC) hC).elim
    · exact (Setting1422.g2_case hF431 hNS S (hLoc.g2 G T M Y H S hC) hC).elim
    · exact (false_of_isL2Quot_one_of_card hSz hsmall hC.2.1).elim
    · exact (false_of_isL2Quot_one_of_card hSz hsmall hC.2.1).elim
    · exact (S.autm12_case hSz hAut (hLoc.autM12 G T M Y H S hC) hC).elim
  ·
    intro hsmall
    have S : Setting1422 T M Y H := ⟨h, hH, hY, Or.inr (Or.inr hsmall)⟩
    rcases S.six_cases_of_inputs hSz hGold hBr hR2b with hC | hC | hC | hC | hC | hC
    · exact (false_of_perm_three_of_card hSz hsmall hC.2.1).elim
    · exact (false_of_perm_three_of_card hSz hsmall (Or.inr hC.2.1)).elim
    · exact (Setting1422.g2_case hF431 hNS S (hLoc.g2 G T M Y H S hC) hC).elim
    · exact Or.inr (Setting1422.g22p_case hSz hABG hG22p hVH S (hLoc.g22p G T M Y H S hC) hC)
    · exact Or.inl (Setting1422.m12_case hI46 hM12 hVH S (hLoc.m12 G T M Y H S hC) hC)
    · exact (S.autm12_case hSz hAut (hLoc.autM12 G T M Y H S hC) hC).elim

end CFSG.Quasithin
