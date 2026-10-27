module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148COpenLie
public import CFSG.RankThree.PartTwo.Sec4.Item47Unitary

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148C

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)

open CFSG.Assembly.RankThreeEven (projSL projSU)


theorem rowS148_of_coreFree {S : Type} [Group S]
    (hcore : ∀ x ∈ innerAut S, orderOf x = 3 → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
      CFSG.Open.GLAPPrimeCoreOf 3 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥)
    (hmeet : ∀ E : Subgroup (MulAut S), (∀ a ∈ E, a ^ 3 = 1) → Nat.card E = 9 →
      ∃ x ∈ E ⊓ innerAut S, x ≠ 1) :
    RowS148 S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro F E X R hc
  obtain ⟨x, ⟨hxE, hxin⟩, hx1⟩ := hmeet E (fun a ha => hc.isE27.1.2 a (hc.le ha)) hc.card
  have hx3 : orderOf x = 3 := orderOf_eq_prime (hc.isE27.1.2 x (hc.le hxE)) hx1
  have h0 := hcore x hxin hx3 X hc.inner_le
  exact le_bot_iff.mp (h0 ▸ hc.le_core x hxE hx1)

theorem exists_inner_of_not_nine_dvd {S : Type} [Group S] (h9 : ¬ 9 ∣ Nat.card (Outer S))
    (E : Subgroup (MulAut S)) (hE : Nat.card E = 9) : ∃ x ∈ E ⊓ innerAut S, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  apply h9
  let f : E →* Outer S := (QuotientGroup.mk' (inner S)).comp E.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : ((x : MulAut S) : Outer S) = 1 := hx
    have hxin : (x : MulAut S) ∈ inner S := (QuotientGroup.eq_one_iff _).mp hx'
    exact Subtype.ext (hcon x ⟨x.2, hxin⟩)
  rw [← hE]
  exact Subgroup.card_dvd_of_injective f hf

section Certs


theorem rowSOf148_projSL_char_three {r e : ℕ} (hr : 2 ≤ r) (he : 1 ≤ e)
    (h9 : ¬ 9 ∣ 2 * e * Nat.gcd (r + 1) (3 ^ e - 1)) :
    RowSOf148 (projSL (r + 1) (GaloisField 3 e)) := by
  intro S _ _ hs hna ⟨eS⟩
  let q : TauCeti.PrimePower := ⟨3, e, Nat.prime_three, he⟩
  haveI : Fact (Nat.Prime q.p) := ⟨Nat.prime_three⟩
  have hq3 : 3 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.le_self_pow (by omega : e ≠ 0) 3
  have hv : (TauCeti.LieTypeIndex.A r q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨by omega, fun h => by omega⟩, ?_⟩
    rintro (⟨h1, -⟩ | ⟨-, h2⟩ | ⟨-, h2⟩) <;> omega
  let eCat : S ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group :=
    eS.trans ((projSLEquivPSLn (r + 1) (GaloisField 3 e)).trans
      (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).symm)
  refine rowS148_of_coreFree (fun x hx hxo H hH => ?_) (fun E _ hE => ?_)
  · exact CFSG.HardMathSupport.Timmesfeld.DefChar.defCharInnerCoreFreeFamA S hs hna
      ⟨.A r q, hv⟩ ⟨r, q, rfl⟩ ⟨eCat⟩ 3 Nat.prime_three (by norm_num)
      (TauCeti.LieTypeIndex.characteristic_A r q) x hx hxo H hH
  · refine exists_inner_of_not_nine_dvd ?_ E hE
    have hd :=
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.higher_linear_outer_order_divides_field_gcd_bound
        (k := GaloisField 3 e) Nat.prime_three he (by omega : 3 ≤ r + 1)
        (GaloisField.card 3 e (by omega))
    rw [Nat.card_congr
      (equivalence (eS.trans (projSLEquivProjectiveSL (r + 1) (GaloisField 3 e)))).toEquiv]
    exact fun h => h9 (h.trans hd)

theorem rowSOf148_projSU_char_three {r e : ℕ} (hr : 2 ≤ r) (he : 1 ≤ e)
    (h9 : ¬ 9 ∣ 2 * e * (3 ^ e + 1)) : RowSOf148 (projSU (r + 1) 3 e) := by
  intro S _ _ hs hna ⟨eS⟩
  let q : TauCeti.PrimePower := ⟨3, e, Nat.prime_three, he⟩
  haveI : Fact (Nat.Prime q.p) := ⟨Nat.prime_three⟩
  have hq3 : 3 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.le_self_pow (by omega : e ≠ 0) 3
  have hv : (TauCeti.LieTypeIndex.twistedA r q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    refine ⟨?_, by simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]⟩
    rw [TauCeti.LieTypeIndex.inStandardRange_iff]
    exact ⟨hr, fun _ => hq3⟩
  let eCat : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group :=
    eS.trans (CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU r q hv).symm
  refine rowS148_of_coreFree (fun x hx hxo H hH => ?_) (fun E _ hE => ?_)
  · exact CFSG.HardMathSupport.Timmesfeld.DefChar.defCharInnerCoreFreeFamTwistedA S hs hna
      ⟨.twistedA r q, hv⟩ ⟨r, q, rfl⟩ ⟨eCat⟩ 3 Nat.prime_three (by norm_num)
      (TauCeti.LieTypeIndex.characteristic_twistedA r q) x hx hxo H hH
  · refine exists_inner_of_not_nine_dvd ?_ E hE
    have hd := card_outer_projSU_dvd (r + 1) 3 e he (by omega) (fun h => by
      have : 3 ≤ 3 ^ e := Nat.le_self_pow (by omega : e ≠ 0) 3
      omega)
    rw [Nat.card_congr (equivalence eS).toEquiv]
    exact fun h => h9 (h.trans hd)

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree in
theorem rowSOf148_nine_G2 : RowSOf148 (TauCeti.CFSGIndex.lie g2ThreeIndex).Group := by
  intro S _ _ hs hna ⟨eS⟩
  refine rowS148_of_coreFree (fun x hx hxo H hH => ?_) (fun E hE3 hE => ?_)
  · exact CFSG.HardMathSupport.Timmesfeld.DefChar.defCharInnerCoreFreeFamG2 S hs hna g2ThreeIndex
      ⟨_, rfl⟩ ⟨eS⟩ 3 Nat.prime_three (by norm_num)
      (TauCeti.LieTypeIndex.characteristic_G2 ⟨3, 1, Nat.prime_three, Nat.one_pos⟩) x hx hxo H hH
  · let q : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩
    haveI : Fact q.p.Prime := ⟨Nat.prime_three⟩
    have hK : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
      GaloisField.card _ _ q.exponent_pos.ne'
    have hK' : Nat.card (GaloisField q.p q.exponent) = q.card := by
      rw [hK, TauCeti.PrimePower.card_def]
    obtain ⟨b⟩ := (CFSG.TauCetiBridge.Even.chevalleyBridgesAll).g2 q g2ThreeIndex.2
      (GaloisField q.p q.exponent) hK'
    let e : S ≃* adjointGroup .G2 (GaloisField q.p q.exponent) :=
      eS.trans (b.symm.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot))
    haveI hchar : CharP (GaloisField q.p q.exponent) ReeTag.G2.prime :=
      (inferInstance : CharP (GaloisField 3 1) 3)
    obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ :=
      G2_three_exact_automorphism_normal_form q.exponent_pos (GaloisField q.p q.exponent) hK
    haveI : NeZero (2 * q.exponent) := ⟨by norm_num [q]⟩
    exact CFSG.HardMathSupport.Timmesfeld.DefChar.exists_inner_of_cyclic_quotient
      (A := Multiplicative (ZMod (2 * q.exponent))) e Θ hker Nat.prime_three E hE3
      (by rw [hE]; norm_num)

open CFSG.Open CFSG.Blueprint CFSG.LieType.Ree in
open CFSG.ComponentClassification.LiteratureLocal.SmallRee (frobeniusΓ
  exists_eq_conj_mul_frobeniusΓ_pow) 
in
theorem rowSOf148_three : ∀ hr : (TauCeti.LieTypeIndex.reeG2 1).Valid,
    RowSOf148 (TauCeti.CFSGIndex.lie ⟨.reeG2 1, hr⟩).Group := by
  intro hr S _ _ hs hna ⟨eS⟩
  refine rowS148_of_coreFree (fun x hx hxo H hH => ?_) (fun E hE3 hE => ?_)
  · exact CFSG.HardMathSupport.Timmesfeld.DefChar.defCharInnerCoreFreeFamReeG2 S hs hna
      ⟨.reeG2 1, hr⟩ ⟨1, rfl⟩ ⟨eS⟩ 3 Nat.prime_three (by norm_num)
      (TauCeti.LieTypeIndex.characteristic_reeG2 1) x hx hxo H hH
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hK : Nat.card (GaloisField 3 (2 * 1 + 1)) = 3 ^ (2 * 1 + 1) :=
      GaloisField.card 3 (2 * 1 + 1) (by omega)
    have : CharP (GaloisField 3 (2 * 1 + 1)) ReeTag.G2.prime :=
      (inferInstance : CharP (GaloisField 3 (2 * 1 + 1)) 3)
    obtain ⟨b⟩ := CFSG.TauCetiBridge.reeG2Bridge 1 hr (GaloisField 3 (2 * 1 + 1)) hK
    have e1 : DerivedCentralQuotient (reeFixedGroup .G2 (GaloisField 3 (2 * 1 + 1)) reeG2Perm
        fun i => if i ∈ reeG2Long then 3 ^ 1 else 3 ^ (1 + 1)) ≃*
          DerivedCentralQuotient (ReeTag.G2.reeGamma (GaloisField 3 (2 * 1 + 1)) 1) := by
      rw [ReeTag.reeGamma_eq_reeFixedGroup]
      exact MulEquiv.refl _
    obtain ⟨E'⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2
      (K := GaloisField 3 (2 * 1 + 1)) le_rfl hK
    let e : S ≃* ReeTag.G2.reeGamma (GaloisField 3 (2 * 1 + 1)) 1 :=
      ((eS.trans b.symm).trans e1).trans E'
    set φ := MulAut.congr e with hφ
    obtain ⟨x', ⟨hx'D, hx'I⟩, hx'1⟩ :=
      CFSG.HardMathSupport.Timmesfeld.DefChar.exists_inner_of_elemAbelian_of_outerCyclic
        (frobeniusΓ : MulAut (ReeTag.G2.reeGamma (GaloisField 3 (2 * 1 + 1)) 1))
        (exists_eq_conj_mul_frobeniusΓ_pow le_rfl hK) Nat.prime_three (E.map φ.toMonoidHom)
        (by
          rintro _ ⟨a, ha, rfl⟩
          change φ a ^ 3 = 1
          rw [← map_pow, hE3 a ha, map_one])
        (by rw [Subgroup.card_map_of_injective φ.injective, hE]; norm_num)
    obtain ⟨x, hxE, rfl⟩ := hx'D
    obtain ⟨g, hg⟩ := hx'I
    refine ⟨x, ⟨hxE, e.symm g, ?_⟩, fun h => hx'1 (by simp [h])⟩
    apply φ.injective
    change _ = φ.toMonoidHom x
    rw [← hg]
    ext s
    simp [hφ, MulAut.congr_apply]

theorem k148OpenRowsLie_holds : K148OpenRowsLie where
  three := rowSOf148_three
  nine_SL3 e he he3 := by
    refine rowSOf148_projSL_char_three (r := 2) le_rfl he ?_
    obtain rfl | rfl | rfl : e = 1 ∨ e = 2 ∨ e = 3 := by omega
    all_goals norm_num
  nine_SU3 e he he3 := by
    refine rowSOf148_projSU_char_three (r := 2) le_rfl he ?_
    obtain rfl | rfl | rfl : e = 1 ∨ e = 2 ∨ e = 3 := by omega
    all_goals norm_num
  nine_G2 := rowSOf148_nine_G2
  nine_SL4 := rowSOf148_projSL_char_three (r := 3) (by norm_num) le_rfl (by norm_num)
  nine_SU4 := rowSOf148_projSU_char_three (r := 3) (by norm_num) le_rfl (by norm_num)

end Certs

end CFSG.RankThree.PartTwo.Sec4.Ronan148C
