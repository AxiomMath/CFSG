module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res4ProofKill
import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofRee
import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldReeF4Core
public import CFSG.LieType.Simplicity.TitsSimple

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
open CFSG.HardMathSupport.Timmesfeld.CrossChar (isQuasisimple_commutator_reeGamma
  commutator_reeGamma_eq_top map_commutator_mulEquiv)

namespace Item424Res4


theorem mem_commutator_reeGamma_zero {k : Type} [Field k] [Finite k] [CharP k F4.prime]
    (hk : Nat.card k = 2) {w : F4.reeGamma k 0} (hw : w ^ 3 = 1) :
    w ∈ commutator (F4.reeGamma k 0) := by
  set e := reeFixedEquivReeGamma k 0 with he
  set D := commutator (reeFixed F4 k 0) with hDdef
  have hmapD : D.map e.toMonoidHom = commutator (F4.reeGamma k 0) := map_commutator_mulEquiv e
  have hq := isQuasisimple_commutator_reeGamma (b := 0) (k := k) (by simpa using hk)
  have hD : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.map_bot] at hmapD
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt hmapD.symm
  rcases CFSG.LieType.Simplicity.eq_bot_or_sup_eq_top_of_card_eq_two hk D with h | h
  · exact absurd h hD
  · have h2 := CFSG.LieType.Simplicity.isPGroup_quotient_of_sup_eq_top hk D h
    set w' := e.symm w with hw'
    have hw'3 : (QuotientGroup.mk' D w') ^ 3 = 1 := by
      rw [← map_pow, hw', ← map_pow, hw, map_one, map_one]
    obtain ⟨n, hn⟩ := h2 (QuotientGroup.mk' D w')
    have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
    have hdvd : orderOf (QuotientGroup.mk' D w') ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hw'3) (orderOf_dvd_of_pow_eq_one hn)
    have h1 : QuotientGroup.mk' D w' = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rw [← hmapD]
    exact ⟨w', h1, e.apply_symm_apply w⟩

theorem not_hasType424_reeGamma {b : ℕ} {k : Type} [Field k] [Finite k] [CharP k F4.prime]
    (hk : Nat.card k = 2 ^ (2 * b + 1)) :
    ¬ Sec11.KS11Lie2Proof.HasType424 (F4.reeGamma k b) := by
  have hq := isQuasisimple_commutator_reeGamma hk
  obtain ⟨u, v, hu1, hu3, hv3, huv, hvu⟩ := Sec8.Item8KFactsProof.reeGamma_exists_e9 b k hk
  have hmem : ∀ w : F4.reeGamma k b, w ^ 3 = 1 → w ∈ commutator (F4.reeGamma k b) := by
    intro w hw
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact mem_commutator_reeGamma_zero (by simpa using hk) hw
    · rw [commutator_reeGamma_eq_top hb hk]
      exact Subgroup.mem_top w
  refine not_hasType424_of_quasisimple (commutator (F4.reeGamma k b)) hq (fun x y => ?_)
    (hmem u hu3) (hmem v hv3) hu1 hu3 hv3 huv hvu
  have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  rw [commutatorElement_def] at h1
  rwa [commutator_def]

end Item424Res4

open Item424Res4

theorem k424FieldCentLargeRee_holds :
    K424FieldCentLargeRee := by
  intro G _ _ L K c a F _ _ _ ha hF h hc3 hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e, hcN, _, ⟨β, rfl⟩, hφ1, d, -, hτ⟩ := h
  have hτ3 := KFacts.inducedAutHom_pow_eq_one L e hcN hc3
  rw [hτ, conj_pow, mul_inv_eq_one, mul_eq_left] at hτ3
  obtain ⟨-, hfaith⟩ := KFacts.largeRee_automorphism_normal_form ha hF
  have h4 : F4.reeGammaFieldAut F a (β ^ 3) = 1 := by
    rw [← reeGammaFieldAutHom_apply, map_pow, hτ3]
  have hβ3 : β ^ 3 = 1 := hfaith _ (by rw [h4]; exact ⟨1, map_one _⟩)
  have hβ1 : β ≠ 1 := fun h1 => hφ1 (by rw [h1, map_one])
  have hβ : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
  obtain ⟨b, hchar, hcard, -, ι, hιinj, hιrange⟩ :=
    Sec8.Item8KFactsProof.exists_fixedPoints_reeGammaFieldAut hF β hβ
  have : Finite (CFSG.LieType.Chevalley.fixSubfield β) := Subtype.finite
  have hrange : ι.range = Item426.fixSub (F4.reeGammaFieldAutHom F a β) := by
    ext z
    rw [hιrange, Item426.mem_fixSub, reeGammaFieldAutHom_apply]
  have e' : F4.reeGamma (CFSG.LieType.Chevalley.fixSubfield β) b ≃*
      Item426.fixSub (F4.reeGammaFieldAutHom F a β) :=
    (MonoidHom.ofInjective hιinj).trans (MulEquiv.subgroupCongr hrange)
  exact not_isType424_of_inducedAut_eq e hcN hc3 hK hτ
    (fun h => not_hasType424_reeGamma hcard (h.of_mulEquiv e'.symm))

end CFSG.RankThree.PartTwo.Sec4
