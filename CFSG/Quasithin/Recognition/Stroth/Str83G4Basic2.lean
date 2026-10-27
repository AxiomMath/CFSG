module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Recognition.Stroth.Str83CartanTools
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Frame
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerMap

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.CGT.Timmesfeld75
open CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str83G4_w_mul_self_mem_q2
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) :
    d.w * d.w ∈ Q2 L1 L2 S := by
  classical
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  let H : Subgroup G := u3H L1 L2 S
  have hH_eq : H = L2 ⊔ S := by
    rw [show H = L2 ⊔ Q2 L1 L2 S from rfl]
    have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
      eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) := congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  have hcore : pCoreOf 2 H = Q2 L1 L2 S := by
    rw [show H = u3H L1 L2 S from rfl]
    exact str86_pCoreOf_u3H hF
  have hQ2S : Q2 L1 L2 S ≤ S := by
    have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
      eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hSH : IsSylowTwoOf S H := by
    rw [hH_eq]
    have h := isSylowTwoOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
      (by
        have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
          eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
        simpa [Q1, Q2, P1, P2, bigB_comm] using hS2)
    have hQ : Q1 L2 L1 S = Q2 L1 L2 S := by simp [Q1, Q2, P1, P2, bigB_comm]
    rw [hQ] at h
    have hsup : L2 ⊔ Q2 L1 L2 S = L2 ⊔ S := by
      rw [← hH_eq, show H = L2 ⊔ Q2 L1 L2 S from rfl]
    rwa [hsup] at h
  have hD2L2 : d.D2 ≤ L2 := d.hD2hall.1.trans (F1.borelOf_le L2 S)
  have hD2H : d.D2 ≤ H := by rw [hH_eq]; exact hD2L2.trans le_sup_left
  have hQ2H : Q2 L1 L2 S ≤ H := by
    rw [show H = L2 ⊔ Q2 L1 L2 S from rfl]
    exact le_sup_right
  have hBt2 : BenderType (oTwoQuot ↥L2) (2 * a + 1) 1 1 :=
    BenderType.linear (2 * a + 1) (by omega) (Classical.choice hL2)
  have hD2card : Nat.card d.D2 = 2 ^ (2 * a + 1) - 1 :=
    (card_isCyclic_of_hallTwoPrime (i := 1) hF.1.h2.sylow d.hD2hall d.hD2sup hBt2).1
  have hD2ne : d.D2 ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hD2card
    have hpow : 8 ≤ 2 ^ (2 * a + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hD2infQ2 : Q2 L1 L2 S ⊓ d.D2 = ⊥ :=
    RonanF13.inf_eq_bot_of_odd (pCoreOf_isPGroup 2 (P2 L1 L2 S)) d.hD2hall.2.1
  let K := oTwoQuot ↥H
  let π : ↥H →* K := QuotientGroup.mk' (pCore 2 ↥H)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = (Q2 L1 L2 S).subgroupOf H := by
    rw [QuotientGroup.ker_mk', ← CFSG.openPCoreOf_subgroupOf 2 H, hcore]
  have hSHp : IsPGroup 2 (S.subgroupOf H) :=
    hSH.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSH.1).symm
  let SH : Sylow 2 ↥H := hSHp.toSylow hSH.2.2
  have hSHcoe : (SH : Subgroup ↥H) = S.subgroupOf H := IsPGroup.toSylow_coe _ _
  let Q : Sylow 2 K := SH.mapSurjective hπsurj
  have hQcoe : (Q : Subgroup K) = (S.subgroupOf H).map π := by
    change ((SH.mapSurjective hπsurj : Sylow 2 K) : Subgroup K) = (S.subgroupOf H).map π
    rw [Sylow.coe_mapSurjective, hSHcoe]
  let Dbar : Subgroup K := (d.D2.subgroupOf H).map π
  have hSleH : S ≤ H := by rw [hH_eq]; exact le_sup_right
  have hS2leH : S ⊓ L2 ≤ H := inf_le_right.trans (by rw [hH_eq]; exact le_sup_left)
  have hcomapQ : Subgroup.comap π ((S.subgroupOf H).map π) = S.subgroupOf H := by
    rw [Subgroup.comap_map_eq, hker]
    exact sup_eq_left.mpr (Subgroup.subgroupOf_mono H hQ2S)
  have hB2leH : borelOf L2 S ≤ H :=
    (F1.borelOf_le L2 S).trans (by rw [hH_eq]; exact le_sup_left)
  have hC5 : H ⊓ Subgroup.normalizer (S : Set G) = borelOf L2 S ⊔ Q2 L1 L2 S :=
    normalizer_inf_eq_borel_sup_q2 hF hB ha hSz hL2 H hH_eq
  have hborel_comap : Subgroup.comap π (CFSG.GH74.Uniqueness.Bender.borel Q) =
      (H ⊓ Subgroup.normalizer (S : Set G)).subgroupOf H := by
    rw [CFSG.GH74.Uniqueness.Bender.borel,
      Subgroup.comap_normalizer_eq_of_surjective (H := (Q : Subgroup K)) hπsurj]
    rw [hQcoe, hcomapQ, ← CFSG.Quasithin.RonanE611.subgroupOf_normalizer_eq hSleH]
  have hborel_comap' : (borelOf L2 S ⊔ Q2 L1 L2 S).subgroupOf H =
      Subgroup.comap π (CFSG.GH74.Uniqueness.Bender.borel Q) := by
    rw [← hC5, ← hborel_comap]
  have hborel_eq : CFSG.GH74.Uniqueness.Bender.borel Q =
      ((borelOf L2 S ⊔ Q2 L1 L2 S).subgroupOf H).map π := by
    rw [hborel_comap']
    exact (Subgroup.map_comap_eq_self_of_surjective hπsurj _).symm
  have hD2sup_le : d.D2 ≤ borelOf L2 S ⊔ Q2 L1 L2 S :=
    d.hD2hall.1.trans le_sup_left
  have hDbar_le_borel : Dbar ≤ CFSG.GH74.Uniqueness.Bender.borel Q := by
    rw [hborel_eq]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hD2sup_le)
  have hDbar_card : Nat.card Dbar = Nat.card d.D2 := by
    let f : ↥d.D2 → Dbar := fun x =>
      ⟨π ⟨x.1, hD2H x.2⟩, Subgroup.mem_map.mpr
        ⟨⟨x.1, hD2H x.2⟩, x.2, rfl⟩⟩
    have hfinj : Function.Injective f := by
      intro a b hab
      have hπeq : π ⟨a.1, hD2H a.2⟩ = π ⟨b.1, hD2H b.2⟩ := congrArg Subtype.val hab
      have hq1 : π (⟨a.1, hD2H a.2⟩ * ⟨b.1, hD2H b.2⟩⁻¹) = 1 := by
        rw [map_mul, map_inv, hπeq, mul_inv_cancel]
      have hmk : (⟨a.1, hD2H a.2⟩ * ⟨b.1, hD2H b.2⟩⁻¹ : ↥H) ∈ π.ker := hq1
      rw [hker] at hmk
      have hmemQ : a.1 * (b.1)⁻¹ ∈ Q2 L1 L2 S := Subgroup.mem_subgroupOf.mp hmk
      have hmemD : a.1 * (b.1)⁻¹ ∈ d.D2 := d.D2.mul_mem a.2 (d.D2.inv_mem b.2)
      have hbot : a.1 * (b.1)⁻¹ ∈ Q2 L1 L2 S ⊓ d.D2 := ⟨hmemQ, hmemD⟩
      rw [hD2infQ2] at hbot
      have h1 : a.1 * (b.1)⁻¹ = 1 := Subgroup.mem_bot.mp hbot
      exact Subtype.ext (mul_inv_eq_one.mp h1)
    have hfsurj : Function.Surjective f := by
      intro y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      refine ⟨⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
      exact Subtype.ext hxy
    exact (Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)).symm
  have hDbar_odd : Odd (Nat.card Dbar) := by
    rw [hDbar_card]
    exact d.hD2hall.2.1
  have hDbar_card' : Nat.card Dbar = 2 ^ (2 * a + 1) - 1 := by
    rw [hDbar_card]; exact hD2card
  have hQ2mapbot : ((Q2 L1 L2 S).subgroupOf H).map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hker]
  have hSmap : (Q : Subgroup K) = ((S ⊓ L2).subgroupOf H).map π := by
    rw [hQcoe]
    change (S.subgroupOf H).map π = ((S ⊓ L2).subgroupOf H).map π
    have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
      eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
    conv_lhs => rw [hS2]
    rw [Subgroup.subgroupOf_sup hS2leH hQ2H, Subgroup.map_sup, hQ2mapbot, sup_bot_eq]
  have hB2map : ((borelOf L2 S).subgroupOf H).map π =
      ((S ⊓ L2).subgroupOf H).map π ⊔ Dbar := by
    rw [d.hD2sup, Subgroup.subgroupOf_sup hS2leH hD2H, Subgroup.map_sup]
  have hQ_sup_Dbar : (Q : Subgroup K) ⊔ Dbar = CFSG.GH74.Uniqueness.Bender.borel Q := by
    conv_lhs => rw [hSmap]
    rw [hborel_eq, Subgroup.subgroupOf_sup hB2leH hQ2H, Subgroup.map_sup,
      hQ2mapbot, sup_bot_eq]
    exact hB2map.symm
  have hBT : BenderType K (2 * a + 1) 1 1 :=
    BenderType.of_mulEquiv hBt2 (str86_oTwoQuot_u3H_equiv hF).symm
  obtain ⟨t, ht2, htB, htInv, -⟩ :=
    exists_inverting_involution_of_cartan_linear hBT Q hDbar_le_borel hDbar_odd hQ_sup_Dbar
  have hcore_t : BenderCore (2 ^ (2 * a + 1)) 1 1 (Q : Subgroup K) t :=
    BenderType.benderCore hBT Q ht2 htB
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hcart_card : Nat.card ↥(CFSG.GH74.Uniqueness.Bender.cartan (Q : Subgroup K) t) =
      2 ^ (2 * a + 1) - 1 := by
    rw [hcore_t.card_cartan, mul_one]
  have hDbar_le_cartan : Dbar ≤ CFSG.GH74.Uniqueness.Bender.cartan (Q : Subgroup K) t := by
    intro x hx
    rw [CFSG.GH74.Uniqueness.Bender.cartan, Subgroup.mem_inf]
    refine ⟨hDbar_le_borel hx, ?_⟩
    rw [mem_conjugate_iff]
    rw [htInv x hx]
    exact hDbar_le_borel (Dbar.inv_mem hx)
  have hDbar_eq_cartan : Dbar = CFSG.GH74.Uniqueness.Bender.cartan (Q : Subgroup K) t := by
    refine Subgroup.eq_of_le_of_card_ge hDbar_le_cartan ?_
    rw [hcart_card, hDbar_card']
  have hwH : d.w ∈ H := by rw [hH_eq]; exact d.hwH2
  let wbar : K := π ⟨d.w, hwH⟩
  have hwbar_inv : ∀ x ∈ Dbar, wbar * x * wbar⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    calc wbar * π y * wbar⁻¹
        = π (⟨d.w, hwH⟩ * y * ⟨d.w, hwH⟩⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = π (⟨d.w * (y : G) * d.w⁻¹, _⟩ : ↥H) := rfl
      _ = π y⁻¹ := by
          congr 1
          exact Subtype.ext (d.hwInv (y : G) hy)
      _ = (π y)⁻¹ := map_inv π y
  have hD2card_gt : 1 < Nat.card ↥d.D2 := by
    rw [hD2card]
    have hpow : 8 ≤ 2 ^ (2 * a + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  haveI hD2nt : Nontrivial ↥d.D2 := (Finite.one_lt_card_iff_nontrivial).mp hD2card_gt
  obtain ⟨x0, hx0ne⟩ := exists_ne (1 : ↥d.D2)
  have hx0D : (x0 : G) ∈ d.D2 := x0.2
  have hx0H : (x0 : G) ∈ H := hD2H hx0D
  let xbar : K := π ⟨(x0 : G), hx0H⟩
  have hxbarD : xbar ∈ Dbar :=
    Subgroup.mem_map.mpr ⟨⟨(x0 : G), hx0H⟩, x0.2, rfl⟩
  have hxbarne : xbar ≠ 1 := by
    intro h1
    have hmk : (⟨(x0 : G), hx0H⟩ : ↥H) ∈ π.ker := h1
    rw [hker] at hmk
    have hmemQ : (x0 : G) ∈ Q2 L1 L2 S := Subgroup.mem_subgroupOf.mp hmk
    have hbot : (x0 : G) ∈ Q2 L1 L2 S ⊓ d.D2 := ⟨hmemQ, hx0D⟩
    rw [hD2infQ2] at hbot
    have hx01 : (x0 : G) = 1 := Subgroup.mem_bot.mp hbot
    exact hx0ne (Subtype.ext hx01)
  have hxbar_cartan : xbar ∈ CFSG.GH74.Uniqueness.Bender.cartan (Q : Subgroup K) t := by
    rw [← hDbar_eq_cartan]
    exact hxbarD
  let c : K := wbar⁻¹ * t
  have hc_cent : c * xbar = xbar * c := by
    have hcx : c * xbar * c⁻¹ = xbar := by
      calc c * xbar * c⁻¹ = wbar⁻¹ * (t * xbar * t⁻¹) * wbar := by
            show (wbar⁻¹ * t) * xbar * (wbar⁻¹ * t)⁻¹ = _
            group
        _ = wbar⁻¹ * xbar⁻¹ * wbar := by rw [htInv xbar hxbarD]
        _ = wbar⁻¹ * (wbar * xbar * wbar⁻¹) * wbar := by
            rw [hwbar_inv xbar hxbarD]
        _ = xbar := by group
    calc c * xbar = (c * xbar * c⁻¹) * c := by group
      _ = xbar * c := by rw [hcx]
  have hc_cartan : c ∈ CFSG.GH74.Uniqueness.Bender.cartan (Q : Subgroup K) t := by
    rw [← hcore_t.centralizer_cartan_eq Q.isPGroup' hxbar_cartan hxbarne]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hc_cent
  have hc_Dbar : c ∈ Dbar := by
    rw [hDbar_eq_cartan]
    exact hc_cartan
  let dbar : K := c
  have hdbarD : dbar ∈ Dbar := hc_Dbar
  have hwbar_sq : wbar * wbar = 1 := by
    have hwbar_eq : wbar = t * dbar⁻¹ := by
      have h1 : wbar⁻¹ = dbar * t := by
        show wbar⁻¹ = c * t
        rw [show c = wbar⁻¹ * t from rfl]
        rw [show (wbar⁻¹ * t) * t = wbar⁻¹ * (t * t) by group, ht2, mul_one]
      calc wbar = (wbar⁻¹)⁻¹ := by group
        _ = (dbar * t)⁻¹ := by rw [h1]
        _ = t⁻¹ * dbar⁻¹ := by group
        _ = t * dbar⁻¹ := by rw [hti]
    rw [hwbar_eq]
    have hd : t * dbar⁻¹ * t = dbar := by
      have h := htInv dbar hdbarD
      calc t * dbar⁻¹ * t = t * dbar⁻¹ * t⁻¹ := by rw [hti]
        _ = (t * dbar * t⁻¹)⁻¹ := by
            simp only [mul_inv_rev, hti]
            group
        _ = (dbar⁻¹)⁻¹ := by rw [h]
        _ = dbar := by group
    have hdt : dbar⁻¹ * t = t * dbar := by
      have h1 : t * (t * dbar⁻¹ * t) = (t * t) * dbar⁻¹ * t := by group
      calc dbar⁻¹ * t = t * (t * dbar⁻¹ * t) := by
            rw [h1, ht2, one_mul]
        _ = t * dbar := by rw [hd]
    calc (t * dbar⁻¹) * (t * dbar⁻¹) = t * (dbar⁻¹ * t) * dbar⁻¹ := by group
      _ = t * (t * dbar) * dbar⁻¹ := by rw [hdt]
      _ = 1 := by rw [← mul_assoc, ht2, one_mul, mul_inv_cancel]
  have hw2H : d.w * d.w ∈ H := H.mul_mem hwH hwH
  have hw2eq : (⟨d.w * d.w, hw2H⟩ : ↥H) = ⟨d.w, hwH⟩ * ⟨d.w, hwH⟩ := Subtype.ext rfl
  have hπw2 : π ⟨d.w * d.w, hw2H⟩ = 1 := by
    rw [hw2eq, map_mul]
    change wbar * wbar = 1
    exact hwbar_sq
  have hkerw2 : (⟨d.w * d.w, hw2H⟩ : ↥H) ∈ π.ker := hπw2
  rw [hker] at hkerw2
  exact Subgroup.mem_subgroupOf.mp hkerw2

theorem str83G4_z1_inf_conjugate_w
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) :
    Z1 L1 L2 S ⊓ CFSG.conjugate (Z1 L1 L2 S) d.w = ⊥ := by
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨hZ1eq, hZ1Z2, hZ2bot, -, -⟩ := str83_caseI_basics hF hB ha hSz hL2 hZI
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := by
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2 L1 L2 S) := congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  have hZ1C : Z1 L1 L2 S ≤ Subgroup.centralizer (S : Set G) := by
    rw [hZ1eq]
    exact (A4.omegaOneCenterOf_le_centerOf S).trans (A4.centerOf_le_centralizer S)
  have hZ1wC : CFSG.conjugate (Z1 L1 L2 S) d.w ≤
      Subgroup.centralizer (CFSG.conjugate S d.w : Set G) :=
    CFSG.GorensteinWalter.centralizer_map_le_of_hom (MulAut.conj d.w⁻¹).toMonoidHom
      S (Z1 L1 L2 S) hZ1C
  have hC : Z1 L1 L2 S ⊓ CFSG.conjugate (Z1 L1 L2 S) d.w ≤
      Subgroup.centralizer ((S ⊔ CFSG.conjugate S d.w : Subgroup G) : Set G) := by
    refine CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers ?_ ?_
    · exact inf_le_left.trans hZ1C
    · exact inf_le_right.trans hZ1wC
  rw [d.hwTop, hsup2] at hC
  have hZ2w : CFSG.conjugate (Z2 L1 L2 S) d.w = Z2 L1 L2 S := by
    apply conjugate_eq_self_of_mem_normalizer
    have hwP2 : d.w ∈ P2 L1 L2 S :=
      (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)) d.hwH2
    exact SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf (P2 L1 L2 S) hwP2
  have hZ2le : Z1 L1 L2 S ⊓ CFSG.conjugate (Z1 L1 L2 S) d.w ≤ Z2 L1 L2 S :=
    inf_le_left.trans hZ1Z2
  have hbot : Z1 L1 L2 S ⊓ CFSG.conjugate (Z1 L1 L2 S) d.w ≤
      Z2 L1 L2 S ⊓ Subgroup.centralizer ((L2 ⊔ Q2 L1 L2 S : Subgroup G) : Set G) :=
    le_inf hZ2le hC
  rw [hZ2bot] at hbot
  exact le_bot_iff.mp hbot

end CFSG.Quasithin.Stroth

end

