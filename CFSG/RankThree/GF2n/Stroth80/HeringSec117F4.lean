module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec117F4Producer
import CFSG.GH74.Generic.GKFCover
import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
import CFSG.LieType.Steinberg.CentralExt.GriessFFourTwo
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118NotTTransportHom
public import CFSG.RankThree.GF2n.Stroth80.HeringSec11Action

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley
open CFSG.LieType.Steinberg.CentralExt CFSG.HardMathSupport.Kantor79


theorem isPerfect_and_card_griessHopfMultiplier_dvd_two_f4 {X : Type} [Group X] {x : ℕ}
    (h : CFSG.Blueprint.LieModel X .F4 0 2 x) :
    commutator X = ⊤ ∧ Nat.card (griessHopfMultiplier X) ∣ 2 := by
  obtain ⟨-, hch⟩ := GriessNative.chevalley_of_lieModel h (by decide)
  have hx : 1 ≤ x := hch.1.2.1
  have hcard : ∀ k : ℕ, Nat.card (Multiplicative (ZMod k)) = k := fun k =>
    (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod k)
  by_cases hx1 : x = 1
  · subst hx1
    obtain ⟨hX, ⟨e⟩⟩ := GriessExceptional.f4_two_native_row hch
    refine ⟨hX, ?_⟩
    rw [Nat.card_congr e.toEquiv]
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
      Nat.card_prod, hcard]
    decide
  · have hq : 3 ≤ 2 ^ x := calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨hX, ⟨e⟩⟩ := GriessNative.f4_row hch hq
    refine ⟨hX, ?_⟩
    rw [Nat.card_congr e.toEquiv]
    simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
      Nat.card_prod, hcard]
    have hg : CFSG.Blueprint.Multiplier.genericOrders .F4 0 2 x = (1, 1) := rfl
    have hex : CFSG.Blueprint.Multiplier.exceptionalOrders .F4 0 2 x = (1, 1) := by
      unfold CFSG.Blueprint.Multiplier.exceptionalOrders
      split <;> simp_all
    rw [hg, hex]
    norm_num

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.center_Xbar_eq_bot_of_lieModel_f4 (hc : Ctx M Q Z B) {x : ℕ}
    (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .F4 0 2 x) :
    Subgroup.center ↥(Xbar M Q Z B) = ⊥ := by
  obtain ⟨hperf, hdvd⟩ := isPerfect_and_card_griessHopfMultiplier_dvd_two_f4 h
  have hcomm := hc.commutator_Xbar_eq_top_of_isPerfect_xbarMod (Group.isPerfect_def.2 hperf)
  have : Group.IsPerfect ↥(Xbar M Q Z B) := Group.isPerfect_def.2 hcomm
  have hker : (QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B))).ker =
      Subgroup.center ↥(Xbar M Q Z B) := QuotientGroup.ker_mk' _
  have h1 := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier inferInstance
    (QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B))) (QuotientGroup.mk'_surjective _)
    hker.le
  rw [hker, ← Nat.card_congr
    (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess (XbarMod M Q Z B)).toEquiv] at h1
  have h2 := h1.trans hdvd
  have hodd := hc.odd_card_center_Xbar
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h3 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h3
  · rw [h3] at hodd
    exact absurd hodd (by decide)

theorem Ctx.exists_mulEquiv_adjointGroup_f4 (hc : Ctx M Q Z B) {x : ℕ}
    (h : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .F4 0 2 x) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (_ : CharP K' 2),
      Nonempty (↥(Xbar M Q Z B) ≃* ↥(adjointGroup .F4 K')) := by
  have hcenter := hc.center_Xbar_eq_bot_of_lieModel_f4 h
  obtain ⟨-, hch⟩ := GriessNative.chevalley_of_lieModel h (by decide)
  have hx : 1 ≤ x := hch.1.2.1
  have hU : CFSG.Blueprint.UntwistedChevalleyModel (XbarMod M Q Z B) .F4 (2 ^ x) := hch.2
  obtain ⟨K', hKf, hKfin, hK, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .F4 hU
  have hchar : CharP K' 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hx hK
  have hquot : XbarMod M Q Z B ≃* Xbar M Q Z B :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
  exact ⟨K', hKf, hKfin, hchar, ⟨hquot.symm.trans e⟩⟩

theorem Ctx.not_lieModel_f4_of (hF1 : F4ExclStatement) (hF2 : F4GenStatement)
    (hc : Ctx M Q Z B) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {x : ℕ}
    (hLie : CFSG.Blueprint.LieModel (XbarMod M Q Z B) .F4 0 2 x) : False := by
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ, hφπ, hφk, hφQ⟩ := exists_actionHom_H0 hc.hyp hD
  obtain ⟨K', _, _, _, ⟨ψ₀⟩⟩ := hc.exists_mulEquiv_adjointGroup_f4 hLie
  set Θ : ↥(XbarH M Q Z B) →* ↥(adjointGroup .F4 K') :=
    ψ₀.toMonoidHom.comp (xbarHToXbar M Q Z B) with hΘ
  have hΘs : Function.Surjective Θ := ψ₀.surjective.comp (xbarHToXbar_surjective hc)
  have hΘk : ∀ s, Θ s = 1 ↔ ((s : ↥(H0 M Z)) : G) ∈ Q := fun s => by
    rw [hΘ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      xbarHToXbar_eq_one_iff]
  obtain ⟨ρV, hρV⟩ := hc.exists_rho_factor_group φ Θ hΘs
    (fun s hs => (hφk (s : ↥(H0 M Z))).mpr ((hΘk s).mp hs))
  obtain ⟨hnd, hiso, -, -, hsieg⟩ := hc.cmComm_kantor_instance ha2 hD φ hφπ hφQ
  have hρQ : ∀ g v, cmCommQf B φ (ρV g v) = cmCommQf B φ v := fun g v => by
    obtain ⟨s, rfl⟩ := hΘs g
    rw [hρV s]
    exact hiso s v
  have hρinj : Function.Injective ρV := by
    refine (injective_iff_map_eq_one ρV).mpr fun g hg => ?_
    obtain ⟨s, rfl⟩ := hΘs g
    rw [hρV s] at hg
    exact (hΘk s).mpr (hc.mem_Q_of_cmCommAct_eq_one hD φ hφπ hφk hφQ hg)
  obtain ⟨a, haL, haA⟩ := ha2
  obtain ⟨s₀, hs₀a, -⟩ := hc.exists_lift_a2 (a := ⟨a, hc.LB_le_M haL⟩) (h := ⟨haL, haA⟩)
  have ht₀ : IsLongRootElement (cmCommQf B φ) (ρV (Θ s₀)) := by
    rw [hρV s₀]
    exact hsieg s₀ (hs₀a ▸ haL) (hs₀a ▸ haA)
  exact false_of_f4 hnd ρV hρinj hρQ (MulEquiv.refl _) ht₀ hF1 hF2

omit [Finite G] [(Q.subgroupOf M).Normal] in
theorem cmF4Width_of (hF1 : F4ExclStatement) (hF2 : F4GenStatement) : CMF4Width := by
  intro G _ _ M Q Z B _ hc n _ _ ha2 ⟨x, hLie⟩
  exact (hc.not_lieModel_f4_of hF1 hF2 ha2 hLie).elim

end CFSG.RankThree.GF2n.Stroth80
