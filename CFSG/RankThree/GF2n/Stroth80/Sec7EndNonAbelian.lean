module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EndOmega
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndPerfect
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndRoot
public import CFSG.Timmesfeld.CorollaryB
public import CFSG.LargeExtraspecial.S8CorBUniv
public import CFSG.GH74.Orders.LieType
public import CFSG.LargeExtraspecial.A2ModOrdCard
public import CFSG.GH74.Orders.Sporadic
public import CFSG.ClassicalInvolution.AschTight.StronglyClosed

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section NonAbPieces

theorem endg_card_rootGroup_image {G G' : Type} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Injective f) (D : Set G) (d : G) :
    Nat.card ↥(CFSG.Timmesfeld.rootGroup (f '' D) (f d)) =
      Nat.card ↥(CFSG.Timmesfeld.rootGroup D d) := by
  have hset : CFSG.Timmesfeld.rootSet (f '' D) (f d) = f '' CFSG.Timmesfeld.rootSet D d := by
    have hc : ∀ a b : G, Commute (f a) (f b) ↔ Commute a b := fun a b =>
      ⟨fun h => by
        have := h.eq
        rw [← map_mul, ← map_mul] at this
        exact hf this, fun h => h.map f⟩
    ext x
    constructor
    · rintro ⟨⟨e, he, rfl⟩, hx⟩
      refine ⟨e, ⟨he, fun g hg => ?_⟩, rfl⟩
      rw [← hc, ← hc]
      exact hx (f g) ⟨g, hg, rfl⟩
    · rintro ⟨e, ⟨he, hx⟩, rfl⟩
      refine ⟨⟨e, he, rfl⟩, ?_⟩
      rintro _ ⟨g, hg, rfl⟩
      rw [hc, hc]
      exact hx g hg
  have : CFSG.Timmesfeld.rootGroup (f '' D) (f d) =
      (CFSG.Timmesfeld.rootGroup D d).map f := by
    unfold CFSG.Timmesfeld.rootGroup
    rw [hset, MonoidHom.map_closure]
  rw [this]
  exact Subgroup.card_map_of_injective hf

end NonAbPieces

section NonAbOrders



theorem endg_card_outcome_two {G : Type} [Group G] {D : Set G}
    (hO4 : CFSG.Timmesfeld.CorB.OutcomeTwo G D) (b : ℕ)
    (hroot : ∀ d ∈ D, Nat.card ↥(CFSG.Timmesfeld.rootGroup D d) = 2 ^ b) :
    Nat.card G = ordA 2 (2 ^ b) ∨ Nat.card G = ordG2 (2 ^ b) ∨
      Nat.card G = ordTrialityD4 (2 ^ b) ∨ Nat.card G = 6048 ∨ Nat.card G = 360 ∨
        Nat.card G = 604800 := by
  rcases hO4 with ⟨f, -, ⟨d, hd, hdf⟩, hL⟩ | ⟨f, -, ⟨d, hd, hdf⟩, hL⟩ |
    ⟨f, -, ⟨d, hd, hdf⟩, hL⟩ | hU | ⟨hA⟩ | hJ
  · have hfb : f = b := Nat.pow_right_injective (le_refl 2) (hdf.symm.trans (hroot d hd))
    subst hfb
    exact Or.inl (CFSG.GH74.card_of_lieModel_PSL (by norm_num) hL)
  · have hfb : f = b := Nat.pow_right_injective (le_refl 2) (hdf.symm.trans (hroot d hd))
    subst hfb
    have := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two
      (CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL)
    exact Or.inr (Or.inl this)
  · have hfb : f = b := Nat.pow_right_injective (le_refl 2) (hdf.symm.trans (hroot d hd))
    subst hfb
    have := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two
      (CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hL)
    exact Or.inr (Or.inr (Or.inl this))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (CFSG.LargeExtraspecial.A2Mod.Ord.card_of_lieModel_PSU33 hU))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    obtain ⟨e⟩ := hA
    rw [Nat.card_congr e.toEquiv]
    rw [nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    rw [CFSG.GH74.card_of_isSporadic_J2 hJ]
    norm_num

end NonAbOrders

section NonAbMain



variable {X : Type} [Group X] [Finite X] {A R N H : Subgroup X} {t : X}

theorem endg_nonabelian_of (h : EndgameHyp X A R N H t) (hTI : IsTIOf A)
    (hE : ⁅EgenX A, EgenX A⁆ ≤ A) (hne : ⁅EgenX A, EgenX A⁆ ≠ ⊥)
    (hK : ∃ K : Subgroup X, K ≤ R ∧ ⁅K, K⁆ = K ∧ K ≠ ⊥ ∧ R ≤ K ⊔ N ∧
      (∀ g : X, g ∈ Subgroup.normalizer (R : Set X) → g ∈ Subgroup.normalizer (K : Set X)) ∧
      ∀ J : Subgroup X, J ≤ K → (J.subgroupOf K).Normal → J ≠ K →
        16 ∣ (J.subgroupOf K).index)
    (hFacts : CFSG.LargeExtraspecial.S8.CorBListFacts)
    (hArith : ∀ b : ℕ, 2 ≤ b → ∃ p : ℕ, p.Prime ∧ 13 ≤ p ∧ p ∣ (2 ^ b) ^ 2 + 1 ∧
      ¬ p ∣ ordA 2 (2 ^ b) ∧ ¬ p ∣ ordG2 (2 ^ b) ∧ ¬ p ∣ ordTrialityD4 (2 ^ b) ∧
      ¬ p ∣ 6048 ∧ ¬ p ∣ 360 ∧ ¬ p ∣ 604800) : False := by
  classical
  haveI := h.H_normal
  obtain ⟨S, _, π, hπs, hπk, hS, h16, hprime⟩ := h.quot
  obtain ⟨Kp, hKR, hKperf, hKne, hRK, hKnorm, hKidx⟩ := hK
  have hA1 : A ≠ ⊥ := fun hb => h.t_ne (by
    have := h.t_mem
    rw [hb, Subgroup.mem_bot] at this
    exact this)
  have hO : EndOmegaHyp A := ⟨hA1, h.A_sq, h.A_comm, hTI, h.N1, hE⟩
  have F := endg_omegaPart1 hO
  have G := endg_omegaPart2 hO
  have hsetup := endg_corB_setup hO F G hne h.t_mem h.t_ne
  set U : Subgroup X := Subgroup.normalClosure ({t} : Set X) with hU
  haveI hUn : U.Normal := Subgroup.normalClosure_normal
  have htU : t ∈ U := Subgroup.subset_normalClosure (Set.mem_singleton t)
  have hUH : U ≤ H :=
    Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr (h.R_le_H (h.A_le_R h.t_mem)))
  have hcenU : Subgroup.center ↥U = ⊥ := endg_center_eq_bot_of_normal h.o2 h.F5 hUn hUH
  have hOdd : goldschmidtOddCore ↥U = ⊥ := endg_goldschmidtOddCore_eq_bot h.F5 hUn hUH
  have htbot : U = ⊥ → False := fun hUbot => h.t_ne (by
    have := htU
    rw [hUbot, Subgroup.mem_bot] at this
    exact this)
  have hUA : U ⊓ A ≠ ⊥ := by
    intro hb
    have : t ∈ U ⊓ A := ⟨htU, h.t_mem⟩
    rw [hb, Subgroup.mem_bot] at this
    exact h.t_ne this
  have hKU_bot : Kp ⊓ Subgroup.centralizer (U : Set X) = ⊥ := by
    have := endg_R_inf_centralizer_eq_bot h hUn hUA
    rw [eq_bot_iff] at this ⊢
    exact fun x hx => this ⟨hKR hx.1, hx.2⟩
  have hcommon : CFSG.LargeExtraspecial.S8.CorBList (↥U ⧸ Subgroup.center ↥U) →
      ∃ φ : ↥Kp →* ↥U, Function.Injective φ ∧
        ∀ k : ↥Kp, (φ k : X) * t = t * (φ k : X) := by
    intro hlist
    obtain ⟨hsimp, hder, -⟩ := hFacts X U hUn hlist
    have hperfU : ⁅U, U⁆ = U :=
      CFSG.LargeExtraspecial.S8.commutator_normalClosure_eq_of_isConj_mul
        hsetup.orderOf_eq hsetup.fusion hsimp
    obtain ⟨k, hk⟩ := hder hperfU
    have hKder : ∀ n : ℕ, Kp ≤ derivedSeries X n := by
      intro n
      induction n with
      | zero => exact le_top
      | succ n ih =>
        rw [derivedSeries_succ]
        calc Kp = ⁅Kp, Kp⁆ := hKperf.symm
          _ ≤ ⁅derivedSeries X n, derivedSeries X n⁆ := Subgroup.commutator_mono ih ih
    set C : Subgroup X := Subgroup.centralizer (U : Set X) with hC
    have hKUC : Kp ≤ U ⊔ C := (hKder k).trans hk
    have hUC : ∀ l ∈ U, ∀ c ∈ C, l * c = c * l := fun l hl c hc =>
      Subgroup.mem_centralizer_iff.mp hc l hl
    have hCU : ∀ c ∈ C, ∀ l ∈ U, c * l = l * c := fun c hc l hl => (hUC l hl c hc).symm
    have hUCbot : U ⊓ C = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxU, hxC⟩
      have hxz : (⟨x, hxU⟩ : ↥U) ∈ Subgroup.center ↥U := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (hCU x hxC g g.2).symm
      rw [hcenU, Subgroup.mem_bot] at hxz
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxz)
    have hsplit : ∀ k ∈ Kp, ∃ l ∈ U, ∃ c ∈ C, k = l * c := fun k hk =>
      endg_mem_sup_of_commute hUC (hKUC hk)
    obtain ⟨φ, hφ1, hφ2⟩ := endg_split_hom hCU hUCbot hsplit
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      intro k hk
      have hkC : (k : X) ∈ C := (hφ2 k).mp hk
      have : (k : X) ∈ Kp ⊓ C := ⟨k.2, hkC⟩
      rw [hKU_bot, Subgroup.mem_bot] at this
      exact Subtype.ext this
    refine ⟨φ, hinj, fun k => ?_⟩
    obtain ⟨c, hc, hkc⟩ := hφ1 k
    have hφk : (φ k : X) = (k : X) * c⁻¹ := by rw [hkc]; group
    have hct : c * t = t * c := hCU c hc t htU
    have hct' : c⁻¹ * t = t * c⁻¹ := by
      calc c⁻¹ * t = c⁻¹ * (t * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * t) * c⁻¹ := by rw [hct]
        _ = t * c⁻¹ := by group
    have hkt : (k : X) * t = t * (k : X) := (h.A_cent t h.t_mem k (hKR k.2)).symm
    rw [hφk]
    calc (k : X) * c⁻¹ * t = (k : X) * (c⁻¹ * t) := by group
      _ = (k : X) * (t * c⁻¹) := by rw [hct']
      _ = ((k : X) * t) * c⁻¹ := by group
      _ = (t * (k : X)) * c⁻¹ := by rw [hkt]
      _ = t * ((k : X) * c⁻¹) := by group
  have hinjQ : Function.Injective (QuotientGroup.mk' (Subgroup.center ↥U)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcenU]
  rcases CFSG.Timmesfeld.CorB.main hsetup with ⟨Kodd, hKodd1, hKodd2, hKodd3, hUeq⟩ | hel |
    ⟨-, hB⟩ | ⟨-, hO4⟩
  ·
    have hodd : Odd (Nat.card ↥(Kodd.subgroupOf U)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKodd1).toEquiv]
      exact hKodd3
    have hle : Kodd.subgroupOf U ≤ goldschmidtOddCore ↥U := le_sSup ⟨hKodd2, hodd⟩
    rw [hOdd] at hle
    have hKb : Kodd = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hKodd1 hx⟩ : ↥U) ∈ Kodd.subgroupOf U := hx
      have := hle hx'
      rw [Subgroup.mem_bot] at this ⊢
      exact congrArg Subtype.val this
    rw [hKb, bot_sup_eq] at hUeq
    have hUz : U = Subgroup.zpowers t := hUeq
    have hpU : IsPGroup 2 ↥U := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [hUz, Nat.card_zpowers, hsetup.orderOf_eq]
      norm_num
    have hle2 : U ≤ pCore 2 X := le_sSup ⟨hUn, hpU⟩
    rw [h.o2] at hle2
    exact htbot (le_bot_iff.mp hle2)
  ·
    exact htbot (endg_eq_bot_of_normal_abelian h.o2 h.F5 hUn hUH
      (fun a ha b hb => (hel a ha b hb).1))
  ·
    obtain ⟨φ, hφi, hφt⟩ := hcommon (CFSG.Timmesfeld.CorB.corBList_of_isBenderGroup hB)
    let e : ↥U ≃* (↥U ⧸ Subgroup.center ↥U) :=
      ((QuotientGroup.quotientMulEquivOfEq hcenU).trans QuotientGroup.quotientBot).symm
    let tU : ↥U := ⟨t, htU⟩
    have hord : orderOf (e tU) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hsetup.orderOf_eq
    haveI := CFSG.ClassicalInvolution.Disconnected.AschTight.isSolvable_centralizer_of_isBenderGroup
      hB hord
    have hmem : ∀ k : ↥Kp, (e.toMonoidHom.comp φ) k ∈ Subgroup.centralizer ({e tU} : Set _) := by
      intro k
      rw [Subgroup.mem_centralizer_singleton_iff]
      show e (φ k) * e tU = e tU * e (φ k)
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hφt k)
    let ψ : ↥Kp →* ↥(Subgroup.centralizer ({e tU} : Set _)) :=
      (e.toMonoidHom.comp φ).codRestrict _ hmem
    have hψ : Function.Injective ψ := by
      intro a b hab
      have := congrArg Subtype.val hab
      exact hφi (e.injective this)
    haveI : Group.IsSolvable ↥Kp := Group.isSolvable_of_isSolvable_injective hψ
    haveI : Group.IsPerfect ↥Kp := Subgroup.isPerfect_iff.mpr hKperf
    haveI : Nontrivial ↥Kp := (Subgroup.nontrivial_iff_ne_bot Kp).mpr hKne
    exact Group.IsPerfect.not_isSolvable ↥Kp inferInstance
  ·
    obtain ⟨φ, hφi, -⟩ := hcommon (CFSG.Timmesfeld.CorB.corBList_of_outcomeTwo hO4)
    obtain ⟨b, hb2, hb⟩ := h.A_card
    obtain ⟨p, hp, hp13, hpdvd, hnA, hnG2, hnD4, hn6048, hn360, hn604800⟩ := hArith b hb2
    have hpS : p ∣ Nat.card S := hprime p hp (by rw [hb]; exact hpdvd)
    have hSK : Nat.card S ∣ Nat.card ↥Kp := by
      let πK : ↥Kp →* S := π.comp (Subgroup.inclusion hKR)
      refine Subgroup.card_dvd_of_surjective (f := πK) ?_
      intro s
      obtain ⟨r, rfl⟩ := hπs s
      have hr : (r : X) ∈ N ⊔ Kp := by
        rw [sup_comm]; exact hRK r.2
      have hKN : Kp ≤ Subgroup.normalizer (N : Set X) := fun k hk =>
        (h.F0 k (h.A_cent t h.t_mem k (hKR hk)).symm).2
      obtain ⟨n, hn, k, hk, hnk⟩ := endg_mem_sup_of_normalizer hKN hr
      refine ⟨⟨k, hk⟩, ?_⟩
      show π ⟨k, hKR hk⟩ = π r
      have h1 : π (⟨n, h.N_le hn⟩ : ↥R) = 1 := (hπk _).mpr hn
      have : (r : ↥R) = ⟨n, h.N_le hn⟩ * ⟨k, hKR hk⟩ := Subtype.ext hnk
      rw [this, map_mul, h1, one_mul]
    have hKUd : Nat.card ↥Kp ∣ Nat.card ↥U := by
      rw [Nat.card_congr (MonoidHom.ofInjective hφi).toEquiv]
      exact Subgroup.card_subgroup_dvd_card φ.range
    have hUZ : Nat.card ↥U = Nat.card (↥U ⧸ Subgroup.center ↥U) := by
      refine Nat.card_congr (Equiv.symm ?_)
      exact (QuotientGroup.quotientMulEquivOfEq hcenU).toEquiv.trans
        QuotientGroup.quotientBot.toEquiv
    have hpU : p ∣ Nat.card (↥U ⧸ Subgroup.center ↥U) :=
      hUZ ▸ hpS.trans (hSK.trans hKUd)
    have hclass : ∀ d : ↥U, d ∈ CFSG.Timmesfeld.CorB.clsIn t →
        Nat.card ↥(CFSG.Timmesfeld.rootGroup (CFSG.Timmesfeld.CorB.clsIn t) d) = 2 ^ b := by
      intro d hd
      have h1 := endg_card_rootGroup_image U.subtype U.subtype_injective
        (CFSG.Timmesfeld.CorB.clsIn t) d
      have himg : U.subtype '' CFSG.Timmesfeld.CorB.clsIn t = {x : X | IsConj t x} := by
        ext x
        constructor
        · rintro ⟨u, hu, rfl⟩
          exact hu
        · intro hx
          exact ⟨⟨x, CFSG.Timmesfeld.CorB.cls_subset t hx⟩, hx, rfl⟩
      rw [himg] at h1
      rw [← h1]
      exact (endg_eight_one_card hO F G hne h.t_mem h.t_ne (d : X) hd).trans hb
    have hroot : ∀ d ∈ (QuotientGroup.mk' (Subgroup.center ↥U) ''
        CFSG.Timmesfeld.CorB.clsIn t),
        Nat.card ↥(CFSG.Timmesfeld.rootGroup (QuotientGroup.mk' (Subgroup.center ↥U) ''
          CFSG.Timmesfeld.CorB.clsIn t) d) = 2 ^ b := by
      rintro _ ⟨d, hd, rfl⟩
      rw [endg_card_rootGroup_image _ hinjQ]
      exact hclass d hd
    rcases endg_card_outcome_two hO4 b hroot with hc | hc | hc | hc | hc | hc <;>
      rw [hc] at hpU
    · exact hnA hpU
    · exact hnG2 hpU
    · exact hnD4 hpU
    · exact hn6048 hpU
    · exact hn360 hpU
    · exact hn604800 hpU

end NonAbMain

end CFSG.RankThree.GF2n.Stroth80
