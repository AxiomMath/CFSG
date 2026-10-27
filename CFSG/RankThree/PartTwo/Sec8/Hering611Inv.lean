module

public import CFSG.RankThree.PartTwo.Sec8.Hering611Lift
public import CFSG.RankThree.PartTwo.Sec8.Hering611Syl
public import CFSG.RankThree.PartTwo.Sec8.Hering611L2
public import CFSG.RankThree.PartTwo.Sec8.Hering611Defs
import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofThree
import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofTools
import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofInvol
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.KFacts.K71Lift
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.RankThree.PartTwo.Sec6.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL)


variable {G : Type} [Group G] [Finite G]

theorem exists_centralized_lift {L : Subgroup G} {t : G}
    (htN : t ∈ Subgroup.normalizer (L : Set G)) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hθodd : Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3) L)))
    {P : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} (hP : IsPGroup 3 P)
    (hfix : ∀ x ∈ P, actHom L ⟨t, htN⟩ x = x) :
    ∃ R₀ : Subgroup G, R₀ ≤ L ∧ IsPGroup 3 R₀ ∧ Nat.card R₀ = Nat.card P ∧
      ∀ r ∈ R₀, t * r = r * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hT2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (G := Subgroup.zpowers t) (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hE3 : IsPGroup 3 (⊥ : Subgroup G) :=
    IsPGroup.of_card (G := (⊥ : Subgroup G)) (n := 0) (by rw [Subgroup.card_bot, pow_zero])
  have htmem : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
  have hinv : (⊥ : Subgroup G) ⊔ Subgroup.zpowers t ≤ Sec6.Res611Res4.invG L P := by
    rw [bot_sup_eq, Subgroup.zpowers_le]
    refine Sec6.Res611Res4.fixG_le_invG L P ?_
    rw [Sec6.Res611Res4.mem_fixG_iff]
    exact ⟨htN, fun x hx => hfix x hx⟩
  obtain ⟨R, hRL, hR3, hRN, hRcov⟩ := Sec6.Res611Res7.exists_lift_invariant hθodd hE3 hT2
    bot_le (by rw [bot_sup_eq]; exact Subgroup.zpowers_le.mpr htN) hP hinv
  have htR : t ∈ Subgroup.normalizer (R : Set G) :=
    hRN (Subgroup.mem_sup_right htmem)
  set Phat : Subgroup G := (P.comap (qL L)).map L.subtype with hPhat
  have hmemPhat : ∀ y : L, (y : G) ∈ Phat ↔ qL L y ∈ P := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy'⟩
      rw [← Subtype.ext hyy']
      exact hy'
    · intro hy
      exact ⟨y, hy, rfl⟩
  set R₀ : Subgroup G := R ⊓ Phat with hR₀
  have hR₀L : R₀ ≤ L := inf_le_left.trans hRL
  have hR₀3 : IsPGroup 3 R₀ := hR3.to_le inf_le_left
  refine ⟨R₀, hR₀L, hR₀3, ?_, ?_⟩
  ·
    have himg : (R₀.subgroupOf L).map (qL L) = P := by
      apply le_antisymm
      · rintro _ ⟨y, hy, rfl⟩
        exact (hmemPhat y).mp (Subgroup.mem_subgroupOf.mp hy).2
      · intro x hx
        obtain ⟨r, hrR, hrx⟩ := hRcov x hx
        refine ⟨r, Subgroup.mem_subgroupOf.mpr ⟨hrR, (hmemPhat r).mpr ?_⟩, hrx⟩
        change (r : L ⧸ aschbacherSolvableCore 3 L) ∈ P
        rw [hrx]
        exact hx
    rw [← Sec6.Res611Res4.card_map_mk_of_isPGroup hR₀3 hR₀L]
    exact congrArg Nat.card (congrArg (fun H : Subgroup _ => (↥H : Type)) himg)
  ·
    intro r hr
    obtain ⟨hrR, hrP⟩ := hr
    obtain ⟨r', hr'P, hr'r⟩ := hrP
    have htr : t * r * t⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp htR r).mp hrR
    obtain ⟨u, hu⟩ : ∃ u : G, u = t * r * t⁻¹ * r⁻¹ := ⟨_, rfl⟩
    have huR : u ∈ R := hu ▸ R.mul_mem htr (R.inv_mem hrR)
    have huL : u ∈ L := hRL huR
    have hu' : (⟨u, huL⟩ : L) = compAction L ⟨t, htN⟩ r' * r'⁻¹ := by
      apply Subtype.ext
      change u = ((compAction L ⟨t, htN⟩ r' : L) : G) * ((r' : L) : G)⁻¹
      rw [coe_compAction, show ((r' : L) : G) = r from hr'r]
      exact hu
    have hq1 : qL L ⟨u, huL⟩ = 1 := by
      rw [hu', map_mul, map_inv, ← actHom_qL, hfix _ hr'P, mul_inv_cancel]
    have hθ : (⟨u, huL⟩ : L) ∈ aschbacherSolvableCore 3 L := (QuotientGroup.eq_one_iff _).mp hq1
    obtain ⟨k, hk⟩ := hR3 ⟨u, huR⟩
    have hk' : (⟨u, huL⟩ : L) ^ 3 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have hu1 : (⟨u, huL⟩ : L) = 1 := KFacts.eq_one_of_mem_aschbacherSolvableCore_of_pow hθ hk'
    have hu1' : u = 1 := congrArg Subtype.val hu1
    have : t * r * t⁻¹ = r := by
      have h1 : t * r * t⁻¹ * r⁻¹ = 1 := hu ▸ hu1'
      exact mul_inv_eq_one.mp h1
    calc t * r = t * r * t⁻¹ * t := by group
      _ = r * t := by rw [this]

section Certs


variable {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}

theorem Frame611.c_not_mem_L (F : Frame611 G A c L E T d) : c ∉ L := by
  obtain ⟨φ⟩ := F.iso_L
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := F.mem_S.1.1
  have hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
    CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv
      (φ.trans (Sec4.projSLEquivPSL (GaloisField 3 (3 * 2))))
      (CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField 3 (3 * 2)))
  have hcC : c ∈ thetaQuotCentralizer L := by
    have h : c ∈ A ⊓ thetaQuotCentralizer L := by rw [F.cent_L]; exact Subgroup.mem_zpowers c
    exact h.2
  intro hcL
  have hc3' : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers c) :=
    Sec5.isElemAbelian_of_le hAe (Subgroup.zpowers_le.mpr F.c_mem)
  have hbot := Sec6.Res611Res7.inf_thetaQuotCentralizer_eq_bot_of_center
    (Subgroup.zpowers_le.mpr hcL) hc3' hZ
  have hmem : c ∈ Subgroup.zpowers c ⊓ thetaQuotCentralizer L :=
    ⟨Subgroup.mem_zpowers c, hcC⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact F.c_ne_one hmem

theorem false_of_field_involution (h45 : Sec4.Item4_5) (h611 : Sec6.Item6_11_1)
    (F : Frame611 G A c L E T d) {t : G} (ht2 : t ^ 2 = 1)
    (hind : KFacts.InducesKindPSL2 (GaloisField 3 (3 * 2)) L t .field) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := F.standing
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := F.mem_S.1.1
  have hcA := F.c_mem
  have hc1 := F.c_ne_one
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c F.mem_L
  obtain ⟨φ⟩ := F.iso_L
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hAe hcA hc1 L hLc
  have hθodd := Sec6.Res611Res3.odd_card_theta hst.evenRank_eq hAe (by rw [F.card_A]) hAL
  set ψ := φ.trans (Sec4.projSLEquivPSL (GaloisField 3 (3 * 2))) with hψ
  obtain ⟨htN, hfield⟩ := (KFacts.inducesKindPSL2_iff L ψ t .field).1 hind
  have hτ2 : KFacts.inducedAutHom L ψ ⟨t, htN⟩ * KFacts.inducedAutHom L ψ ⟨t, htN⟩ = 1 := by
    rw [← pow_two]
    exact KFacts.inducedAutHom_pow_eq_one L ψ htN ht2
  have hcardF : Nat.card (GaloisField 3 (3 * 2)) = 3 ^ 6 := by
    rw [GaloisField.card 3 (3 * 2) (by omega)]
  have ht1 : t ≠ 1 := by
    intro h
    obtain ⟨φ', -, hφ'1, d', -, hτ'⟩ := hfield
    have h1 : KFacts.inducedAutHom L ψ ⟨t, htN⟩ = 1 := by
      rw [show (⟨t, htN⟩ : Subgroup.normalizer (L : Set G)) = 1 from Subtype.ext h, map_one]
    apply hφ'1
    calc φ' = d'⁻¹ * (d' * φ' * d'⁻¹) * d' := by group
      _ = 1 := by rw [← hτ', h1]; group
  obtain ⟨Q, hQe, hQcard, hQfix⟩ := exists_fixed_E27 hcardF hfield hτ2
  set P : Subgroup (L ⧸ aschbacherSolvableCore 3 L) := Q.map ψ.symm.toMonoidHom with hP
  have hPe : CFSG.Assembly.IsElemAbelian 3 P :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ Q hQe
  have hP3 : IsPGroup 3 P := Sec5.isPGroup_of_isElemAbelian hPe
  have hPcard : Nat.card P = 27 := by
    rw [hP, Subgroup.card_map_of_injective ψ.symm.injective]
    exact hQcard
  have hfixP : ∀ x ∈ P, actHom L ⟨t, htN⟩ x = x := by
    rintro _ ⟨q, hq, rfl⟩
    have h2 : ψ (actHom L ⟨t, htN⟩ (ψ.symm q)) = q := hQfix q hq
    exact (ψ.eq_symm_apply.mpr h2 : actHom L ⟨t, htN⟩ (ψ.symm q) = ψ.symm q)
  obtain ⟨R₀, hR₀L, hR₀3, hR₀card, hR₀t⟩ := exists_centralized_lift htN ht2 ht1 hθodd hP3 hfixP
  have hR₀27 : Nat.card R₀ = 27 := hR₀card.trans hPcard
  obtain ⟨S₀, hR₀S₀, hS₀L, hS₀e, hS₀card⟩ := exists_elemAbelian_sylow φ hR₀L hR₀3
  have hR₀e : CFSG.Assembly.IsElemAbelian 3 R₀ := Sec5.isElemAbelian_of_le hS₀e hR₀S₀
  have hT2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (G := Subgroup.zpowers t) (n := 1)
      (by rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1, pow_one])
  have hR₀N : R₀ ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
    have hC : R₀ ≤ Subgroup.centralizer ({t} : Set G) := fun r hr =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hR₀t r hr).symm
    refine hC.trans ?_
    rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer ((Subgroup.zpowers t : Subgroup G) : Set G)
  have hR₀E : R₀ ∈ partTwoE G :=
    ⟨hR₀e, hR₀27, Subgroup.zpowers t, mt Subgroup.zpowers_eq_bot.mp ht1, hT2, hR₀N⟩
  have hLcC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hS₀c : ∀ a ∈ S₀, a * c = c * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLcC (hS₀L ha))
  obtain ⟨hBe, hBcard⟩ := Sec5.isElemAbelian_sup_zpowers hS₀e
    (fun h => F.c_not_mem_L (hS₀L h)) hc3 hS₀c
  obtain ⟨A₁, hBA₁, hA₁max⟩ :=
    Finite.exists_le_maximal (p := fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) hBe
  have hA₁F : A₁ ∈ partTwoF G :=
    ⟨hA₁max.prop, fun B hB hAB => le_antisymm (hA₁max.2 hB hAB) hAB, R₀, hR₀E,
      (hR₀S₀.trans le_sup_left).trans hBA₁⟩
  have hrk := h611 G hst A₁ hA₁F
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (Sec5.isPGroup_of_isElemAbelian hA₁max.prop)
  have hm4 : m ≤ 4 := by
    have := Sec5.le_pRank_of_elemAbelian Nat.prime_three (le_refl A₁) hA₁max.prop hm
    omega
  have hle := Subgroup.card_le_of_le hBA₁
  rw [hBcard, hS₀card, hm] at hle
  have h7 : (3 : ℕ) ^ 6 * 3 ≤ 3 ^ 4 :=
    hle.trans (Nat.pow_le_pow_right (by norm_num) hm4)
  norm_num at h7

end Certs

end CFSG.RankThree.PartTwo.Sec8.Hering611
