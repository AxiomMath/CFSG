module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwistedNonsplit
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivExcRound
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsExcAssembly
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviAut
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.SeitzReduction

namespace TwE6Toral

theorem ordTwistedA_five_eq (b : ℕ) :
    CFSG.Open.ordTwistedA 5 (2 ^ b) =
      ((2 ^ b) ^ 15 * (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 + 1) * ((2 ^ b) ^ 4 - 1) *
        ((2 ^ b) ^ 5 + 1) * ((2 ^ b) ^ 6 - 1))) / Nat.gcd 6 (2 ^ b + 1) := by
  have hq : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  rw [CFSG.Open.ordTwistedA, show Finset.Icc 2 (5 + 1) = {2, 3, 4, 5, 6} by rfl,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_pair (by decide),
    CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_even hq (by decide),
    CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_odd (by decide),
    CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_even hq (by decide),
    CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_odd (by decide),
    CFSG.Timmesfeld.Orders.toNat_pow_sub_neg_one_pow_of_even hq (by decide),
    show 5 * (5 + 1) / 2 = 15 by rfl]
  congr 1
  ring

theorem dvd_ordTwistedA_five {b p : ℕ} (hb : 1 ≤ b) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ b - 1 ∨ p ∣ 2 ^ b + 1) : p ∣ CFSG.Open.ordTwistedA 5 (2 ^ b) := by
  rw [ordTwistedA_five_eq]
  have hodd : Odd (2 ^ b + 1) := Even.add_one ((Nat.even_pow' (by omega)).mpr even_two)
  generalize 2 ^ b = q at hpq hodd ⊢
  refine Nat.dvd_div_of_mul_dvd ?_
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    have h := Nat.sq_sub_sq q 1
    rwa [one_pow] at h
  have hq3 : q + 1 ∣ q ^ 3 + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)
    rwa [one_pow] at h
  have hN : ∀ {m : ℕ}, m ∣ (q ^ 2 - 1) * (q ^ 3 + 1) → m ∣ q ^ 15 * ((q ^ 2 - 1) * (q ^ 3 + 1) *
      (q ^ 4 - 1) * (q ^ 5 + 1) * (q ^ 6 - 1)) := fun h =>
    h.trans ⟨q ^ 15 * ((q ^ 4 - 1) * (q ^ 5 + 1) * (q ^ 6 - 1)), by ring⟩
  have hd : Nat.gcd 6 (q + 1) ∣ q + 1 := Nat.gcd_dvd_right _ _
  have hdN := hN ((hd.trans ⟨q - 1, hsq⟩).mul_right (q ^ 3 + 1))
  have hpsq : p ∣ q ^ 2 - 1 := by
    rcases hpq with h | h
    · exact h.trans ⟨q + 1, by rw [hsq, mul_comm]⟩
    · exact h.trans ⟨q - 1, hsq⟩
  by_cases hcop : Nat.Coprime p (Nat.gcd 6 (q + 1))
  · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop.symm hdN (hN (hpsq.mul_right _))
  · have hpd : p ∣ Nat.gcd 6 (q + 1) := (Nat.Prime.dvd_iff_not_coprime hp).mpr hcop
    have hp6 : p ∣ 6 := hpd.trans (Nat.gcd_dvd_left _ _)
    have hp3 : p = 3 := by
      have h6 : p ∣ 2 * 3 := hp6
      rcases (Nat.Prime.dvd_mul hp).mp h6 with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
      · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
    subst hp3
    have h3q : 3 ∣ q + 1 := hpd.trans hd
    have hd3 : Nat.gcd 6 (q + 1) = 3 := by
      have hdodd : Odd (Nat.gcd 6 (q + 1)) := Odd.of_dvd_nat hodd hd
      have hd6 : Nat.gcd 6 (q + 1) ∣ 6 := Nat.gcd_dvd_left _ _
      have hle : Nat.gcd 6 (q + 1) ≤ 6 := Nat.le_of_dvd (by norm_num) hd6
      rw [Nat.odd_iff] at hdodd
      interval_cases h : Nat.gcd 6 (q + 1) <;> omega
    rw [hd3]
    exact hN (Nat.mul_dvd_mul (h3q.trans ⟨q - 1, hsq⟩) (h3q.trans hq3))

theorem map_conj_map_conj_inv {L : Type} [Group L] (g : L) (A' : Subgroup L) :
    (A'.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A' := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id A'
  refine MonoidHom.ext fun x => ?_
  change g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x
  group

end TwE6Toral

section Defs

@[expose] def GGTwE6InndiagHighSplit (f : ℕ)
    (A : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : Algebra k (GaloisField 2 (2 * f))), Nat.card k = 2 ^ f ∧
    ∃ (g : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (Y : Subgroup (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))),
      Y ≤ E6GraphLevi.thetaTorus (algebraMap k (GaloisField 2 (2 * f))) ∧ Y ≠ ⊥ ∧
        A = ((Y.subgroupOf (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f))).map (MulAut.conj g⁻¹).toMonoidHom).map MulAut.conj

end Defs

namespace TwE6Toral

section Pilot

variable {f : ℕ}

theorem su6Levi_subgroupOf_props (hf : 1 ≤ f) {k : Type} [Field k]
    [Algebra k (GaloisField 2 (2 * f))] (hk : Nat.card k = 2 ^ f) :
    CFSG.IsQuasisimple ((TwistedE6Pilot.su6Levi (frobQ 2 f)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) ∧
      Subgroup.center ((TwistedE6Pilot.su6Levi (frobQ 2 f)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) = ⊥ ∧
      Nat.card ((TwistedE6Pilot.su6Levi (frobQ 2 f)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) =
          CFSG.Open.ordTwistedA 5 (2 ^ f) := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f := fun c => frobQ_apply 2 f c
  have : IsSimpleGroup (TwistedE6Pilot.su6Levi (frobQ 2 f)) :=
    TwistedE6Pilot.isSimpleGroup_su6Levi (k := k) hf hk hK hσ
  have hq := TwistedE6Pilot.isQuasisimple_su6Levi_subgroupOf (k := k) hf hk hK hσ
  have hZ : Subgroup.center ((TwistedE6Pilot.su6Levi (frobQ 2 f)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))) = ⊥ := by
    have hnc : ∃ a b : TwistedE6Pilot.su6Levi (frobQ 2 f), a * b ≠ b * a := by
      by_contra hc
      push Not at hc
      have := TwistedE6Pilot.isPerfect_su6Levi (k := k) hf hk hK hσ
      exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun a b => hc a b⟩⟩
    exact F4Pilot.center_eq_bot_congr
      (Subgroup.subgroupOfEquivOfLe (TwistedE6Pilot.su6Levi_le_graphFixedRootGroup _)).symm
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).2
  have hcard := TwistedE6Pilot.card_su6Levi_map_conj (k := k) hf hk hK hσ 1
  rw [Subgroup.card_map_of_injective (MulAut.conj _).injective] at hcard
  exact ⟨hq, hZ, hcard⟩

theorem centralizer_subgroupOf_highSplit (hf : 1 ≤ f) {k : Type} [Field k]
    [Algebra k (GaloisField 2 (2 * f))] (hk : Nat.card k = 2 ^ f)
    {Y : Subgroup (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))}
    (hYT : Y ≤ E6GraphLevi.thetaTorus (algebraMap k (GaloisField 2 (2 * f)))) (hY1 : Y ≠ ⊥) :
    Subgroup.centralizer ((Y.subgroupOf (graphFixedRootGroup TwistTag.E6
        (GaloisField 2 (2 * f)) (frobQ 2 f)) : Subgroup _) : Set _) =
      (E6GraphLevi.thetaTorus (algebraMap k (GaloisField 2 (2 * f)))).subgroupOf
          (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) ⊔
        (TwistedE6Pilot.su6Levi (frobQ 2 f)).subgroupOf
          (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) ∧
      (∀ a ∈ (E6GraphLevi.thetaTorus (algebraMap k (GaloisField 2 (2 * f)))).subgroupOf
          (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
        ∀ b ∈ (E6GraphLevi.thetaTorus (algebraMap k (GaloisField 2 (2 * f)))).subgroupOf
          (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
          a * b = b * a) ∧
      (E6GraphLevi.thetaTorus (algebraMap k (GaloisField 2 (2 * f)))).subgroupOf
          (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) ≤
        Subgroup.centralizer (((TwistedE6Pilot.su6Levi (frobQ 2 f)).subgroupOf
          (graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :
            Subgroup _) : Set _) := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f := fun c => frobQ_apply 2 f c
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hk2 : (2 : k) = 0 := CFSG.LieType.Chevalley.E6GraphHighestRoot.two_eq_zero_of_card hf hk
  obtain ⟨-, -, -, hcomm, -, -, -⟩ := TwistedE6Pilot.su6Levi_facts hf hk hK hσ
  have hTC := TwistedE6Pilot.thetaTorus_le_C0 hf hk hK hσ
  obtain ⟨⟨y, hyY⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hY1
  obtain ⟨c, hc⟩ := hYT hyY
  have hc1 : c ≠ 1 := by
    rintro rfl
    have hy : y = 1 := by rw [← hc, map_one]
    exact hy1 (Subtype.ext hy)
  have hc3 : 3 ≤ orderOf c := by
    have h0 : 0 < orderOf c := orderOf_pos c
    have h1 : orderOf c ≠ 1 := fun h => hc1 (orderOf_eq_one_iff.mp h)
    have h2 : orderOf c ≠ 2 := by
      intro h
      have hc2 : c ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one c
      have hck : (c : k) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hc2, Units.val_one]
      have h3 : ((c : k) - 1) ^ 2 = 0 := by linear_combination hck + (1 - (c : k)) * hk2
      exact hc1 (Units.ext (by simpa [sub_eq_zero] using h3))
    omega
  have hC : Subgroup.centralizer (Y : Set (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) ⊓
      graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f) =
        E6GraphLevi.thetaTorus (algebraMap k (GaloisField 2 (2 * f))) ⊔
          TwistedE6Pilot.su6Levi (frobQ 2 f) := by
    apply le_antisymm
    · intro g' hg'
      obtain ⟨hgc, hgC⟩ := Subgroup.mem_inf.mp hg'
      have hyc := Subgroup.mem_centralizer_iff.mp hgc y hyY
      rw [← hc] at hyc
      have h1 := TwistedE6Pilot.centralizer_highDiag_inf_le hf hk hK hσ hc3 hyc.symm hgC
      rwa [sup_comm] at h1
    · refine sup_le (le_inf ((TwistedE6Pilot.thetaTorus_le_centralizer_self _).trans
        (Subgroup.centralizer_le hYT)) hTC) (le_inf ?_
          (TwistedE6Pilot.su6Levi_le_graphFixedRootGroup _))
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (hcomm l hl h (hYT hh)).symm
  refine ⟨TwistedE6Pilot.centralizer_subgroupOf_eq_sup (hYT.trans hTC) hTC
    (TwistedE6Pilot.su6Levi_le_graphFixedRootGroup _) hC, fun a ha b hb => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (TwistedE6Pilot.thetaTorus_le_centralizer_self _ hb) _ ha),
    fun x hx => ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact hcomm d hd x hx

theorem exists_subCoreFamily_autFix_highSplit (hf : 1 ≤ f)
    (A : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))) (h : GGTwE6InndiagHighSplit f A) :
    ∃ (β : Type) (S : β → Subgroup ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))), LayerCores.IsSubCoreFamily (LayerSixE.autFix A) S := by
  obtain ⟨k, _, _, hk, g, Y₀, hYT, hY1, rfl⟩ := h
  rw [LayerSixE.autFix_map_conj]
  refine LayerExc.exists_subCoreFamily_centralizer_of_conj g _ ?_
  rw [map_conj_map_conj_inv]
  obtain ⟨hq, hZ, -⟩ := su6Levi_subgroupOf_props hf hk
  obtain ⟨hC, hWc, hWD⟩ := centralizer_subgroupOf_highSplit hf hk hYT hY1
  rw [hC]
  exact ⟨Unit, _, LayerExc.isSubCoreFamily_sup_of_centralizer hWc hWD hq hZ⟩

end Pilot

end TwE6Toral

section Rest

@[expose] def GGTwE6InndiagCoreRestTwoInput : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ A : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))), IsPGroup p A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      A ≤ LayerSixE.twInndiagAut f → ¬ GGTwE6InndiagHighNonsplit f A →
        ¬ GGTwE6InndiagHighSplit f A →
          ∃ (β : Type) (S : β → Subgroup ↥(graphFixedRootGroup TwistTag.E6
            (GaloisField 2 (2 * f)) (frobQ 2 f))),
            LayerCores.IsSubCoreFamily (LayerSixE.autFix A) S

theorem ggTwE6InndiagCoreRestInput_of_two (h : GGTwE6InndiagCoreRestTwoInput) :
    GGTwE6InndiagCoreRestInput := by
  intro f hf p hp hp2 A hA hAc hAD hn
  by_cases hs : GGTwE6InndiagHighSplit f A
  · exact TwE6Toral.exists_subCoreFamily_autFix_highSplit hf A hs
  · exact h f hf p hp hp2 A hA hAc hAD hn hs

theorem ggTwE6InndiagCoreRestTwoInput_of_rest (h : GGTwE6InndiagCoreRestInput) :
    GGTwE6InndiagCoreRestTwoInput :=
  fun f hf p hp hp2 A hA hAc hAD hn _ => h f hf p hp hp2 A hA hAc hAD hn

end Rest

end CFSG.StandardType
