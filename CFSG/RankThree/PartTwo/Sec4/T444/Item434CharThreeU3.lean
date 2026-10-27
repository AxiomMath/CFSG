module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThree
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeU3Tools
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores Matrix
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace Item434CharThree

@[expose] def CharThreeU3CenterFree : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (e : ℕ), 2 ≤ e → e ≤ 3 → IsQuasisimple L →
    IsPGroup 3 (Subgroup.center L) → Nonempty (L ⧸ Subgroup.center L ≃* projSU 3 3 e) →
      Subgroup.center L = ⊥

theorem charThreeU3CenterFree_of_griess
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    CharThreeU3CenterFree := by
  intro L _ _ e he2 he3 hL _ ⟨θ⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmodel : CFSG.Models.LieModel (projSU 3 3 e) .PSU 3 3 e := by
    have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 3 3 e := by
      refine ⟨Nat.prime_three, by omega, le_rfl, ?_⟩
      intro h
      have h1 : 3 ^ e = 2 := (Prod.mk.inj h).2
      have : 3 ^ 1 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact ⟨hadm, Or.inl ⟨hadm, GaloisField 3 (2 * e), inferInstance, inferInstance,
      card_galois_two_mul (by omega), ⟨Sec4.projSUEquivStatedProj 3 3 e⟩⟩⟩
  obtain ⟨-, ⟨eM⟩⟩ := hGA (projSU 3 3 e) .PSU 3 3 e hmodel
  have hg : Nat.gcd 3 (3 ^ e + 1) = 1 := by
    rw [← Nat.Coprime, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    have h1 : 3 ∣ 3 ^ e := dvd_pow_self 3 (by omega)
    omega
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 3 3 e = (1, 1) := by
    simp [CFSG.Blueprint.Multiplier.exceptionalOrders]
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSU 3 3 e = (1, 1) := by
    simp [CFSG.Blueprint.Multiplier.genericOrders, hg]
  have hcardM : Nat.card (CFSG.Open.griessHopfMultiplier (projSU 3 3 e)) = 1 := by
    rw [Nat.card_congr eM.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod]
    simp only [hexc, hgen]
    simp
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hL θ
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
    (projSU 3 3 e)).toEquiv, hcardM] at hdvd
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp hdvd)

theorem center_eq_bot_of_quasisimple_quotient {L X : Type} [Group L] [Group X]
    (hL : IsQuasisimple L) (θ : L ⧸ Subgroup.center L ≃* X) : Subgroup.center X = ⊥ := by
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.1
  obtain ⟨a, b, hab⟩ := hL.2.2
  have hC : Subgroup.center (L ⧸ Subgroup.center L) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (L ⧸ Subgroup.center L))
      with h | h
    · exact h
    · exfalso
      have ha : a ∈ Subgroup.center (L ⧸ Subgroup.center L) := h ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  rw [eq_bot_iff]
  intro x hx
  have hx' : θ.symm x ∈ Subgroup.center (L ⧸ Subgroup.center L) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply θ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp hx (θ y)
  rw [hC, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot, ← θ.apply_symm_apply x, hx', map_one]

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem false_of_projSU_three_large (hU : CharThreeU3CenterFree) (h : Ctx434Core G A M Q)
    {e : ℕ} (he2 : 2 ≤ e) (he3 : e ≤ 3)
    (e₀ : layer G ⧸ Subgroup.center (layer G) ≃* projSU 3 3 e) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := GaloisField 3 (2 * e) with hK
  have hF : Nat.card K = (3 ^ e) ^ 2 := card_galois_two_mul (by omega)
  set σ := unitaryInvolution K 3 e with hσdef
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  set θ : layer G ⧸ Subgroup.center (layer G) ≃* SU σ 3 :=
    e₀.trans (suEquivProjSU (by omega)).symm with hθ
  have hZ : Subgroup.center (layer G) = ⊥ :=
    hU (layer G) e he2 he3 h.isQuasisimple h.isPGroup_center_layer ⟨e₀⟩
  have hq : 81 ≤ (3 ^ e) ^ 2 := by
    calc 81 = (3 ^ 2) ^ 2 := by norm_num
      _ ≤ (3 ^ e) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) he2) 2
  have hR := card_lineU_ge hF (a₀ := (1 : K)) one_ne_zero
  have hRe := isElemAbelian_lineU (hσ := unitaryInvolution_involutive hF) (1 : K)
  have : Finite (SU σ 3) := Finite.of_injective _ Subtype.val_injective
  obtain ⟨k, hk⟩ := (Sec5.isPGroup_of_isElemAbelian hRe).exists_card_eq
  obtain ⟨D₀, hD₀⟩ := Sylow.exists_subgroup_card_pow_prime 3
    (G := lineU (unitaryInvolution_involutive hF) (1 : K)) (n := 3) (by
      rw [hk]
      refine pow_dvd_pow 3 ?_
      by_contra hk3
      have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega)
  have hD : CFSG.Assembly.IsElemAbelian 3
      (D₀.map (lineU (unitaryInvolution_involutive hF) (1 : K)).subtype) :=
    Source.isElemAbelian_of_le hRe (Subgroup.map_subtype_le D₀)
  have hD27 : Nat.card (D₀.map (lineU (unitaryInvolution_involutive hF) (1 : K)).subtype) =
      27 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hD₀]
    norm_num
  have hCA := Item434Kit.inf_centralizer_layer_eq_bot h hZ θ hD hD27
  have hA27 := Item434Kit.card_map_quotConj h hCA θ
  have hAe := Item434Kit.isElemAbelian_map_quotConj h θ
  set Astar := A.map (Item434Alt.quotConj θ) with hAstar
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner (SU σ 3) with hI
  have h9 : 9 ≤ Nat.card (Astar ⊓ I : Subgroup (MulAut (SU σ 3))) := by
    have hsplit := Item434Alt.card_eq_card_inf_ker_mul_card_map (QuotientGroup.mk' I) Astar
    rw [QuotientGroup.ker_mk', hA27] at hsplit
    have hd1 : Nat.card (Astar.map (QuotientGroup.mk' I)) ∣ 27 :=
      hA27 ▸ Subgroup.card_map_dvd _ _
    have hd2 : Nat.card (Astar.map (QuotientGroup.mk' I)) ∣ 2 * e * (3 ^ e + 1) :=
      (Subgroup.card_subgroup_dvd_card _).trans (card_outer_SU_three_dvd (by omega))
    have hN : 2 * e * (3 ^ e + 1) = 40 ∨ 2 * e * (3 ^ e + 1) = 168 := by
      rcases (show e = 2 ∨ e = 3 by omega) with h2 | h3
      · left; rw [h2]; norm_num
      · right; rw [h3]; norm_num
    have hg := Nat.dvd_gcd hd1 hd2
    have hle : Nat.card (Astar.map (QuotientGroup.mk' I)) ≤ 3 := by
      rcases hN with hN | hN
      · rw [hN, show Nat.gcd 27 40 = 1 by norm_num] at hg
        exact (Nat.le_of_dvd (by norm_num) hg).trans (by norm_num)
      · rw [hN, show Nat.gcd 27 168 = 3 by norm_num] at hg
        exact Nat.le_of_dvd (by norm_num) hg
    by_contra hlt
    push Not at hlt
    have : Nat.card (Astar ⊓ I : Subgroup (MulAut (SU σ 3))) *
        Nat.card (Astar.map (QuotientGroup.mk' I)) ≤ 8 * 3 := Nat.mul_le_mul (by omega) hle
    omega
  have hinj := Item434Kit.conj_injective_of_center_eq_bot
    (center_eq_bot_of_quasisimple_quotient h.isQuasisimple θ)
  set P : Subgroup (SU σ 3) := (Astar ⊓ I).comap (MulAut.conj : SU σ 3 →* MulAut (SU σ 3))
    with hP
  have hPmap : P.map (MulAut.conj : SU σ 3 →* MulAut (SU σ 3)) = Astar ⊓ I :=
    Subgroup.map_comap_eq_self inf_le_right
  have hPe : CFSG.Assembly.IsElemAbelian 3 P :=
    Item434Kit.isElemAbelian_of_map_injective hinj
      (by rw [hPmap]; exact Source.isElemAbelian_of_le hAe inf_le_left)
  have hPp : IsPGroup 3 P := Sec5.isPGroup_of_isElemAbelian hPe
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card
    (P₀ := heisU (unitaryInvolution_involutive hF))
    (by rw [card_heisU hF, factorization_card_SU_three (by omega), ← pow_mul, mul_comm]) hPp
  have hPg : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ heisU (unitaryInvolution_involutive hF) :=
    Item434AltPerm.map_conj_inv_le hg
  have hPgc : ∀ x ∈ P.map (MulAut.conj g⁻¹).toMonoidHom,
      ∀ y ∈ P.map (MulAut.conj g⁻¹).toMonoidHom, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hPe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  obtain ⟨a₀, ha₀, hle⟩ := exists_le_lineU hPg hPgc
  set D := (lineU (unitaryInvolution_involutive hF) a₀).map (MulAut.conj g).toMonoidHom
    with hDdef
  have hDe : CFSG.Assembly.IsElemAbelian 3 D :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ (isElemAbelian_lineU a₀)
  have h81 : 81 ≤ Nat.card D := by
    rw [hDdef, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hq.trans (card_lineU_ge hF ha₀)
  have hB9 := h9.trans (Item434Kit.card_le_card_inf_comap θ (inf_le_left : Astar ⊓ I ≤ Astar))
  refine Item434Kit.false_of_fixed h hZ θ inf_le_left hB9 hDe h81 ?_
  rintro b ⟨-, hb⟩ d hd
  obtain ⟨p, hp⟩ := hb.2
  have hpP : p ∈ P := by
    change MulAut.conj p ∈ Astar ⊓ I
    rw [hp]
    exact hb
  rw [← hp, MulAut.conj_apply]
  obtain ⟨d', hd', rfl⟩ := hd
  have hp' : g⁻¹ * p * g⁻¹⁻¹ ∈ lineU (unitaryInvolution_involutive hF) a₀ :=
    hle ⟨p, hpP, rfl⟩
  have hcomm := lineU_commute hp' hd'
  change p * (g * d' * g⁻¹) * p⁻¹ = g * d' * g⁻¹
  have hpe : p = g * (g⁻¹ * p * g⁻¹⁻¹) * g⁻¹ := by group
  rw [hpe]
  calc g * (g⁻¹ * p * g⁻¹⁻¹) * g⁻¹ * (g * d' * g⁻¹) * (g * (g⁻¹ * p * g⁻¹⁻¹) * g⁻¹)⁻¹ =
      g * ((g⁻¹ * p * g⁻¹⁻¹) * d') * (g⁻¹ * p * g⁻¹⁻¹)⁻¹ * g⁻¹ := by group
    _ = g * (d' * (g⁻¹ * p * g⁻¹⁻¹)) * (g⁻¹ * p * g⁻¹⁻¹)⁻¹ * g⁻¹ := by rw [hcomm]
    _ = g * d' * g⁻¹ := by group

end Item434CharThree

open Item434CharThree

section Families


theorem item434CharThreeU3Large_of_centerFree (hU : CharThreeU3CenterFree) :
    Item434CharThreeU3Large := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL
  obtain ⟨e, he2, he3, ⟨e₀⟩⟩ := hL
  exact (false_of_projSU_three_large hU hc he2 he3 e₀).elim

theorem item434CharThreeU3Large_of_griess
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) :
    Item434CharThreeU3Large :=
  item434CharThreeU3Large_of_centerFree (charThreeU3CenterFree_of_griess hGA)

end Families

end CFSG.RankThree.PartTwo.Sec4
