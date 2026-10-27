module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Delta
public import CFSG.Quasithin.Recognition.Stroth.Str83CartanTools
public import CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits
open CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G]

theorem str83G4_conj_w_eq {L1 L2 S : Subgroup G} (d : Str83G4Data L1 L2 S)
    (hw : d.w ∈ Subgroup.centralizer
      (centralizerMod (pCoreOf 2 L2) (d.D1 ⊔ d.D2) L2 : Set G))
    {x δ : G} (hx : x ∈ d.D1) (hδ : δ ∈ d.D2)
    (hxδ : ∀ l ∈ L2, (x * δ⁻¹) * l * (x * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L2) :
    d.w⁻¹ * x * d.w = x * δ⁻¹ * δ⁻¹ := by
  classical
  set H2 : Subgroup G := centralizerMod (pCoreOf 2 L2) (d.D1 ⊔ d.D2) L2 with hH2
  have hw' : d.w ∈ Subgroup.centralizer (H2 : Set G) := by rwa [hH2]
  have hVle : pCoreOf 2 L2 ≤ L2 := pCoreOf_le 2 L2
  have hgNL2 : x * δ⁻¹ ∈ Subgroup.normalizer (L2 : Set G) := by
    have hmap_le : Subgroup.map (MulAut.conj (x * δ⁻¹)).toMonoidHom L2 ≤ L2 := by
      intro y hy
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hy
      change (x * δ⁻¹) * l * (x * δ⁻¹)⁻¹ ∈ L2
      have hmem : (x * δ⁻¹) * l * (x * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L2 := hxδ l hl
      have heq : (x * δ⁻¹) * l * (x * δ⁻¹)⁻¹ =
          ((x * δ⁻¹) * l * (x * δ⁻¹)⁻¹ * l⁻¹) * l := by group
      rw [heq]
      exact L2.mul_mem (hVle hmem) hl
    have hcard : Nat.card ↥(Subgroup.map (MulAut.conj (x * δ⁻¹)).toMonoidHom L2) =
        Nat.card ↥L2 :=
      Subgroup.card_map_of_injective (f := (MulAut.conj (x * δ⁻¹)).toMonoidHom)
        (MulAut.conj (x * δ⁻¹)).injective
    have hmap : Subgroup.map (MulAut.conj (x * δ⁻¹)).toMonoidHom L2 = L2 :=
      Subgroup.eq_of_le_of_card_ge hmap_le (le_of_eq hcard.symm)
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  have hgN : x * δ⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    (normalizer_le_normalizer_pCoreOf 2 L2) hgNL2
  have hxδD : x * δ⁻¹ ∈ d.D1 ⊔ d.D2 :=
    Subgroup.mul_mem_sup hx (d.D2.inv_mem hδ)
  have hxδH2 : x * δ⁻¹ ∈ H2 := by
    rw [hH2]
    exact mem_centralizerMod.mpr ⟨hxδD, hgN, hxδ⟩
  have hcomm : (x * δ⁻¹) * d.w = d.w * (x * δ⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp hw' (x * δ⁻¹) hxδH2)
  have hwconjh : d.w⁻¹ * (x * δ⁻¹) * d.w = x * δ⁻¹ := by
    calc d.w⁻¹ * (x * δ⁻¹) * d.w = d.w⁻¹ * ((x * δ⁻¹) * d.w) := by group
      _ = d.w⁻¹ * (d.w * (x * δ⁻¹)) := by rw [hcomm]
      _ = x * δ⁻¹ := by group
  have hwδ : d.w⁻¹ * δ * d.w = δ⁻¹ := by
    have hδ' : δ = d.w⁻¹ * δ⁻¹ * d.w := by
      have h := congrArg (fun t => d.w⁻¹ * t * d.w) (d.hwInv δ hδ)
      simpa [mul_assoc] using h
    have h := congrArg Inv.inv hδ'
    simpa [mul_assoc] using h.symm
  calc d.w⁻¹ * x * d.w
      = d.w⁻¹ * ((x * δ⁻¹) * δ) * d.w := by group
    _ = (d.w⁻¹ * (x * δ⁻¹) * d.w) * (d.w⁻¹ * δ * d.w) := by group
    _ = (x * δ⁻¹) * δ⁻¹ := by rw [hwconjh, hwδ]
    _ = x * δ⁻¹ * δ⁻¹ := by group

theorem str83G4_d2_inf_h2_eq_bot {L1 L2 S : Subgroup G} {a : ℕ}
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S) :
    d.D2 ⊓ centralizerMod (pCoreOf 2 L2) (d.D1 ⊔ d.D2) L2 = ⊥ := by
  classical
  obtain ⟨-, -, -, -, hL2, -⟩ := hfr
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  intro c hc
  have hcD : c ∈ d.D2 := hc.1
  have hcH2 : c ∈ centralizerMod (pCoreOf 2 L2) (d.D1 ⊔ d.D2) L2 := hc.2
  rw [mem_centralizerMod] at hcH2
  have hcL : c ∈ L2 := d.hD2hall.1.trans (CFSG.Quasithin.F1.borelOf_le L2 S) hcD
  have hcV : c ∈ pCoreOf 2 L2 := by
    let π : ↥L2 →* oTwoQuot ↥L2 := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L2)
    have hcent : π ⟨c, hcL⟩ ∈ Subgroup.center (oTwoQuot ↥L2) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ g
      have hcomm_el : (⟨c, hcL⟩ * l * ⟨c, hcL⟩⁻¹ * l⁻¹ : ↥L2) ∈ CFSG.Open.pCore 2 ↥L2 := by
        rw [CFSG.Quasithin.F1.mem_pCore_iff_coe]
        simpa using hcH2.2.2 l l.2
      have hcommq : π (⟨c, hcL⟩ * l * ⟨c, hcL⟩⁻¹ * l⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hcomm_el
      have hq : π ⟨c, hcL⟩ * π l * (π ⟨c, hcL⟩)⁻¹ * (π l)⁻¹ = 1 := by
        calc π ⟨c, hcL⟩ * π l * (π ⟨c, hcL⟩)⁻¹ * (π l)⁻¹
            = π (⟨c, hcL⟩ * l * ⟨c, hcL⟩⁻¹ * l⁻¹) := by
              rw [map_mul, map_mul, map_mul, map_inv, map_inv]
          _ = 1 := hcommq
      have hcomm : π ⟨c, hcL⟩ * π l = π l * π ⟨c, hcL⟩ := by
        calc π ⟨c, hcL⟩ * π l
            = (π ⟨c, hcL⟩ * π l * (π ⟨c, hcL⟩)⁻¹ * (π l)⁻¹) *
                (π l * π ⟨c, hcL⟩) := by group
          _ = 1 * (π l * π ⟨c, hcL⟩) := by rw [hq]
          _ = π l * π ⟨c, hcL⟩ := one_mul _
      exact hcomm.symm
    have hZ : Subgroup.center (oTwoQuot ↥L2) = ⊥ := by
      obtain ⟨e⟩ := hL2
      exact CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv e
        (CFSG.GorensteinWalter.psl2_center_eq_bot _)
    rw [hZ, Subgroup.mem_bot] at hcent
    have hmemCore : (⟨c, hcL⟩ : ↥L2) ∈ CFSG.Open.pCore 2 ↥L2 :=
      (QuotientGroup.eq_one_iff _).mp hcent
    exact (CFSG.Quasithin.F1.mem_pCore_iff_coe _).mp hmemCore
  have hbot : c ∈ pCoreOf 2 L2 ⊓ d.D2 := ⟨hcV, hcD⟩
  rw [RonanF13.inf_eq_bot_of_odd (pCoreOf_isPGroup 2 L2) d.hD2hall.2.1] at hbot
  exact Subgroup.mem_bot.mp hbot

theorem str83G4_d2_sup_h2_eq
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) :
    d.D2 ⊔ centralizerMod (pCoreOf 2 L2) (d.D1 ⊔ d.D2) L2 = d.D1 ⊔ d.D2 := by
  have hfr' := hfr
  obtain ⟨hF, -, -, -, -, -⟩ := hfr
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hbigBV : bigB L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    ((F1.bigB_le_normalizer_left hR).2).trans (normalizer_le_normalizer_pCoreOf 2 L2)
  have hD1B : d.D1 ≤ bigB L1 L2 S :=
    d.hD1hall.1.trans (le_sup_left.trans le_sup_left)
  have hD2B : d.D2 ≤ bigB L1 L2 S :=
    d.hD2hall.1.trans (le_sup_right.trans le_sup_left)
  apply le_antisymm
  · exact sup_le le_sup_right (centralizerMod_le_left _ _ _)
  · refine sup_le ?_ le_sup_left
    intro x hx
    obtain ⟨δ, hδD, hxδ⟩ := str83G4_exists_delta_two hfr' d hx
    have hxδD : x * δ⁻¹ ∈ d.D1 ⊔ d.D2 :=
      Subgroup.mul_mem_sup hx (d.D2.inv_mem hδD)
    have hxδB : x * δ⁻¹ ∈ bigB L1 L2 S :=
      (bigB L1 L2 S).mul_mem (hD1B hx) ((bigB L1 L2 S).inv_mem (hD2B hδD))
    have hxδH2 : x * δ⁻¹ ∈ centralizerMod (pCoreOf 2 L2) (d.D1 ⊔ d.D2) L2 :=
      mem_centralizerMod.mpr ⟨hxδD, hbigBV hxδB, hxδ⟩
    have hxeq : x = (x * δ⁻¹) * δ := by group
    rw [hxeq, sup_comm]
    exact Subgroup.mul_mem_sup hxδH2 hδD

theorem str83G4_d1_sup_conjugate_d1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S)
    (hw : d.w ∈ Subgroup.centralizer
      (centralizerMod (pCoreOf 2 L2) (d.D1 ⊔ d.D2) L2 : Set G))
    (hsurj : ∀ δ ∈ d.D2, ∃ x ∈ d.D1,
      ∀ l ∈ L2, (x * δ⁻¹) * l * (x * δ⁻¹)⁻¹ * l⁻¹ ∈ pCoreOf 2 L2) :
    d.D1 ⊔ CFSG.conjugate d.D1 d.w = d.D1 ⊔ d.D2 := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [CFSG.conjugate]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨δ, hδ, hxδ⟩ := str83G4_exists_delta_two hfr d hx
    have hconj := str83G4_conj_w_eq d hw hx hδ hxδ
    have hmem : (MulAut.conj d.w⁻¹) x ∈ d.D1 ⊔ d.D2 := by
      rw [MulAut.conj_apply, inv_inv]
      rw [hconj]
      rw [show x * δ⁻¹ * δ⁻¹ = x * (δ⁻¹ * δ⁻¹) by group]
      exact Subgroup.mul_mem_sup hx
        (d.D2.mul_mem (d.D2.inv_mem hδ) (d.D2.inv_mem hδ))
    exact hmem
  · refine sup_le le_sup_left ?_
    intro y hy
    obtain ⟨x, hx, hxδ⟩ := hsurj y hy
    have hconj := str83G4_conj_w_eq d hw hx hy hxδ
    have hxw : d.w⁻¹ * x * d.w ∈ CFSG.conjugate d.D1 d.w := by
      rw [CFSG.conjugate]
      refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
      change (MulAut.conj d.w⁻¹) x = d.w⁻¹ * x * d.w
      rw [MulAut.conj_apply, inv_inv]
    have hsqneg : y⁻¹ * y⁻¹ ∈ d.D1 ⊔ CFSG.conjugate d.D1 d.w := by
      have heq : y⁻¹ * y⁻¹ = x⁻¹ * (d.w⁻¹ * x * d.w) := by
        rw [hconj]
        group
      rw [heq]
      exact Subgroup.mul_mem_sup (d.D1.inv_mem hx) hxw
    have hsq : y * y ∈ d.D1 ⊔ CFSG.conjugate d.D1 d.w := by
      simpa [mul_inv_rev, inv_inv] using Subgroup.inv_mem _ hsqneg
    have hodd : Odd (orderOf y) :=
      d.hD2hall.2.1.of_dvd_nat (Subgroup.orderOf_dvd_natCard d.D2 hy)
    obtain ⟨k, hk⟩ := hodd
    have hyeq : y = (y * y) ^ (k + 1) := by
      have hord : orderOf y = 2 * k + 1 := hk
      have hpow : y = y ^ (2 * k + 2) := by
        rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, pow_succ,
          show y ^ (2 * k + 1) = 1 by rw [← hord]; exact pow_orderOf_eq_one y]
        group
      rw [hpow, ← pow_two, ← pow_mul]
      congr 1
    rw [hyeq]
    exact Subgroup.pow_mem _ hsq (k + 1)

theorem str83G4_exists_data_centralizer
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) :
    ∃ d' : Str83G4Data L1 L2 S, d'.D1 = d.D1 ∧ d'.D2 = d.D2 ∧
      d'.w ∈ Subgroup.centralizer
        (centralizerMod (pCoreOf 2 L2) (d.D1 ⊔ d.D2) L2 : Set G) := by
  classical
  obtain ⟨hF, hB, ha, hSz, hL2, -⟩ := hfr
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H2 : Subgroup G := centralizerMod (pCoreOf 2 L2) (d.D1 ⊔ d.D2) L2 with hH2def
  set C2 : Subgroup G := Subgroup.centralizer (H2 : Set G) with hC2def
  set Q2' : Subgroup G := Q2 L1 L2 S with hQ2def
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hS2 : S = (S ⊓ L2) ⊔ Q2' := by
    rw [hQ2def]
    exact eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hQ2S : Q2' ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hL2S_eq : L2 ⊔ S = L2 ⊔ Q2' := by
    have h1 : L2 ⊔ S = L2 ⊔ ((S ⊓ L2) ⊔ Q2') := congrArg (fun X => L2 ⊔ X) hS2
    rw [h1, ← sup_assoc, show L2 ⊔ (S ⊓ L2) = L2 from sup_eq_left.mpr inf_le_right]
  have hB1B : borelOf L1 S ≤ bigB L1 L2 S :=
    (le_sup_left : borelOf L1 S ≤ borelOf L1 S ⊔ borelOf L2 S).trans le_sup_left
  have hB2B : borelOf L2 S ≤ bigB L1 L2 S :=
    (le_sup_right : borelOf L2 S ≤ borelOf L1 S ⊔ borelOf L2 S).trans le_sup_left
  have hbigBP2 : bigB L1 L2 S ≤ P2 L1 L2 S := le_sup_right
  have hSP2 : S ≤ P2 L1 L2 S := (le_sup_right : S ≤ bigB L1 L2 S).trans hbigBP2
  have hD1B : d.D1 ≤ bigB L1 L2 S := d.hD1hall.1.trans hB1B
  have hD2B : d.D2 ≤ bigB L1 L2 S := d.hD2hall.1.trans hB2B
  have hH2B : H2 ≤ bigB L1 L2 S :=
    (centralizerMod_le_left _ _ _).trans (sup_le hD1B hD2B)
  have hP2NQ2 : P2 L1 L2 S ≤ Subgroup.normalizer (Q2' : Set G) :=
    le_normalizer_pCoreOf 2 (P2 L1 L2 S)
  have hH2NQ2 : H2 ≤ Subgroup.normalizer (Q2' : Set G) :=
    hH2B.trans (hbigBP2.trans hP2NQ2)
  have hBt2 : BenderType (oTwoQuot ↥L2) (2 * a + 1) 1 1 :=
    BenderType.linear (2 * a + 1) (by omega) (Classical.choice hL2)
  have hD2cyc : IsCyclic ↥d.D2 :=
    (card_isCyclic_of_hallTwoPrime (i := 1) hF.1.h2.sylow d.hD2hall d.hD2sup hBt2).2
  have hD1centD2 : d.D1 ≤ Subgroup.centralizer (d.D2 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (d.hcomm x hx y hy).symm
  have hD2centD2 : d.D2 ≤ Subgroup.centralizer (d.D2 : Set G) := by
    letI : CommGroup ↥d.D2 := hD2cyc.commGroup
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (mul_comm (⟨y, hy⟩ : ↥d.D2) ⟨x, hx⟩)
  have hH2centD2 : H2 ≤ Subgroup.centralizer (d.D2 : Set G) :=
    (centralizerMod_le_left _ _ _).trans (sup_le hD1centD2 hD2centD2)
  have hD2centH2 : d.D2 ≤ Subgroup.centralizer (H2 : Set G) :=
    Subgroup.le_centralizer_iff.mp hH2centD2
  have hD2infQ2 : d.D2 ⊓ Q2' = ⊥ := by
    rw [inf_comm, hQ2def]
    exact RonanF13.inf_eq_bot_of_odd (pCoreOf_isPGroup 2 (P2 L1 L2 S)) d.hD2hall.2.1
  have hD2ND1 : d.D2 ≤ Subgroup.normalizer (d.D1 : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy x hx
    have heq : y * x * y⁻¹ = x := by
      calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [← d.hcomm x hx y hy]
        _ = x := by group
    rwa [heq]
  have hdvdsup : Nat.card ↥(d.D1 ⊔ d.D2) ∣ Nat.card d.D1 * Nat.card d.D2 :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalizingJoinCardDividesProduct.card_dvd_product
      d.D1 d.D2 hD2ND1
  have hH2odd : Odd (Nat.card H2) :=
    Odd.of_dvd_nat (d.hD1hall.2.1.mul d.hD2hall.2.1)
      ((Subgroup.card_dvd_of_le (centralizerMod_le_left _ _ _)).trans hdvdsup)
  have hsolvQ2 : Group.IsSolvable ↥Q2' := by
    have := (pCoreOf_isPGroup 2 (P2 L1 L2 S)).isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card H2) (Nat.card Q2') := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (pCoreOf_isPGroup 2 (P2 L1 L2 S))
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hH2odd)
  have hP2NL2 : P2 L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) := by
    rw [P2]
    exact sup_le Subgroup.le_normalizer ((F1.bigB_le_normalizer_left hR).2)
  have hP2NV : P2 L1 L2 S ≤ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    hP2NL2.trans (normalizer_le_normalizer_pCoreOf 2 L2)
  have hVleQ2 : pCoreOf 2 L2 ≤ Q2' :=
    le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_le 2 L2).trans (le_sup_left : L2 ≤ P2 L1 L2 S))
      hP2NV (pCoreOf_isPGroup 2 L2)
  have hL2NQ2 : L2 ≤ Subgroup.normalizer (Q2' : Set G) :=
    (le_sup_left : L2 ≤ P2 L1 L2 S).trans hP2NQ2
  have hcommL2 : ∀ h ∈ H2, ∀ l ∈ L2, h * l * h⁻¹ * l⁻¹ ∈ Q2' := by
    intro h hh l hl
    have hh' := hh
    rw [hH2def, mem_centralizerMod] at hh'
    exact hVleQ2 (hh'.2.2 l hl)
  have hcommQ2 : ∀ h ∈ H2, ∀ q ∈ Q2', h * q * h⁻¹ * q⁻¹ ∈ Q2' := by
    intro h hh q hq
    have hq' : h * q * h⁻¹ ∈ Q2' :=
      (Subgroup.mem_normalizer_iff.mp (hH2NQ2 hh) q).mp hq
    have heq : h * q * h⁻¹ * q⁻¹ = (h * q * h⁻¹) * q⁻¹ := by group
    rw [heq]
    exact Q2'.mul_mem hq' (Q2'.inv_mem hq)
  have hcommL2S : ∀ h ∈ H2, ∀ y ∈ L2 ⊔ S, h * y * h⁻¹ * y⁻¹ ∈ Q2' := by
    intro h hh y hy
    have hy' : y ∈ Q2' ⊔ L2 := by rw [sup_comm, ← hL2S_eq]; exact hy
    obtain ⟨q, hq, l, hl, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hL2NQ2).mp hy'
    have heq : h * (q * l) * h⁻¹ * (q * l)⁻¹ =
        (h * q * h⁻¹ * q⁻¹) * q * (h * l * h⁻¹ * l⁻¹) * q⁻¹ := by group
    rw [heq]
    exact Q2'.mul_mem (Q2'.mul_mem (Q2'.mul_mem (hcommQ2 h hh q hq) hq)
      (hcommL2 h hh l hl)) (Q2'.inv_mem hq)
  have hw0P2 : d.w ∈ P2 L1 L2 S := (sup_le le_sup_left hSP2) d.hwH2
  have hw0NQ2 : d.w ∈ Subgroup.normalizer (Q2' : Set G) := hP2NQ2 hw0P2
  have hg : ∀ h ∈ H2, d.w⁻¹ * (h * d.w * h⁻¹) ∈ Q2' := by
    intro h hh
    have hc : h * d.w * h⁻¹ * d.w⁻¹ ∈ Q2' := hcommL2S h hh d.w d.hwH2
    have heq : d.w⁻¹ * (h * d.w * h⁻¹) =
        d.w⁻¹ * (h * d.w * h⁻¹ * d.w⁻¹) * d.w := by group
    rw [heq]
    simpa [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hw0NQ2) _).mp hc
  obtain ⟨m, hmQ, hw1C⟩ :=
    CFSG.ABGTheoremB.V4.exists_mul_mem_centralizer_of_coprime hH2NQ2 hsolvQ2 hcop hg
  set w1 : G := d.w * m with hw1eq
  set P : Subgroup G := Q2' ⊓ C2 with hPdef
  set Y : Subgroup G := P ⊔ d.D2 with hYdef
  set E : Subgroup G := CFSG.conjugate d.D2 w1 with hEdef
  have hD2P2 : d.D2 ≤ P2 L1 L2 S := hD2B.trans hbigBP2
  have hw1P2 : w1 ∈ P2 L1 L2 S :=
    (P2 L1 L2 S).mul_mem hw0P2 ((pCoreOf_le 2 (P2 L1 L2 S)) hmQ)
  have hw1NQ2 : w1 ∈ Subgroup.normalizer (Q2' : Set G) := hP2NQ2 hw1P2
  have hD2NQ2 : d.D2 ≤ Subgroup.normalizer (Q2' : Set G) :=
    hD2B.trans (hbigBP2.trans hP2NQ2)
  have hD2NC2 : d.D2 ≤ Subgroup.normalizer (C2 : Set G) := by
    have h1 : d.D2 ≤ Subgroup.normalizer (H2 : Set G) :=
      hD2centH2.trans (Subgroup.centralizer_le_normalizer (H2 : Set G))
    have h2 : d.D2 ≤ Subgroup.normalizer (Subgroup.centralizer (H2 : Set G) : Set G) :=
      h1.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (H2 : Subgroup G))
    simpa [hC2def] using h2
  have hD2NP : d.D2 ≤ Subgroup.normalizer (P : Set G) := by
    rw [hPdef]
    exact (le_inf hD2NQ2 hD2NC2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hw1C2 : w1 ∈ C2 := by rw [hC2def]; exact hw1C
  have hw1NC2 : w1 ∈ Subgroup.normalizer (C2 : Set G) := by
    have h1 : w1 ∈ Subgroup.normalizer (H2 : Set G) :=
      (Subgroup.centralizer_le_normalizer (H2 : Set G)) hw1C
    simpa [hC2def] using (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (H2 : Subgroup G)) h1
  have hw1NP : w1 ∈ Subgroup.normalizer (P : Set G) := by
    rw [hPdef]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hw1NQ2, hw1NC2⟩
  have hEcard : Nat.card E = Nat.card d.D2 := by
    rw [hEdef, CFSG.conjugate]
    exact Subgroup.card_map_of_injective (f := (MulAut.conj w1⁻¹).toMonoidHom)
      (MulAut.conj w1⁻¹).injective
  have hE_eq_conj_m : E = CFSG.conjugate d.D2 m := by
    rw [hEdef, hw1eq, ← CFSG.conjugate_conjugate,
      CFSG.conjugate_eq_self_of_mem_normalizer d.hwD2]
  have hE_le_D2Q2 : E ≤ Q2' ⊔ d.D2 := by
    have hmQ2 : m ∈ Q2' ⊔ d.D2 := Subgroup.mem_sup_left hmQ
    have hfix : Subgroup.map (MulAut.conj m⁻¹).toMonoidHom (Q2' ⊔ d.D2) = Q2' ⊔ d.D2 :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.le_normalizer ((Q2' ⊔ d.D2).inv_mem hmQ2))
    calc E = CFSG.conjugate d.D2 m := hE_eq_conj_m
      _ = Subgroup.map (MulAut.conj m⁻¹).toMonoidHom d.D2 := rfl
      _ ≤ Subgroup.map (MulAut.conj m⁻¹).toMonoidHom (Q2' ⊔ d.D2) :=
          Subgroup.map_mono le_sup_right
      _ = Q2' ⊔ d.D2 := hfix
  have hE_le_C2 : E ≤ C2 := by
    rw [hEdef, CFSG.conjugate]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hD2C2 : d.D2 ≤ C2 := by rw [hC2def]; exact hD2centH2
    have h1 : w1⁻¹ ∈ C2 := C2.inv_mem hw1C2
    have h2 : w1⁻¹ * y ∈ C2 := C2.mul_mem h1 (hD2C2 hy)
    change (MulAut.conj w1⁻¹) y ∈ C2
    rw [MulAut.conj_apply, inv_inv]
    exact C2.mul_mem h2 hw1C2
  have hE_le_Y : E ≤ Y := by
    intro e he
    have he_sup : e ∈ Q2' ⊔ d.D2 := hE_le_D2Q2 he
    obtain ⟨q, hqQ, δ, hδD, heq⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hD2NQ2).mp he_sup
    have heC : e ∈ C2 := hE_le_C2 he
    have hqC : q ∈ C2 := by
      have hqeq : q = e * δ⁻¹ := by rw [heq]; group
      rw [hqeq]
      exact C2.mul_mem heC (C2.inv_mem (hD2centH2 hδD))
    have hqP : q ∈ P := by rw [hPdef]; exact ⟨hqQ, hqC⟩
    rw [heq, hYdef]
    exact Subgroup.mul_mem_sup hqP hδD
  have hPinfE : P ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxP : x ∈ P := hx.1
    have hxE : x ∈ E := hx.2
    rw [hPdef] at hxP
    have hxQ : x ∈ Q2' := hxP.1
    have hxE' : w1 * x * w1⁻¹ ∈ d.D2 := (CFSG.mem_conjugate_iff d.D2 w1 x).mp hxE
    have hxQ' : w1 * x * w1⁻¹ ∈ Q2' :=
      (Subgroup.mem_normalizer_iff.mp hw1NQ2 x).mp hxQ
    have hbot : w1 * x * w1⁻¹ ∈ d.D2 ⊓ Q2' := ⟨hxE', hxQ'⟩
    rw [hD2infQ2, Subgroup.mem_bot] at hbot
    have hx1 : x = 1 := by
      calc x = w1⁻¹ * (w1 * x * w1⁻¹) * w1 := by group
        _ = 1 := by rw [hbot]; group
    exact Subgroup.mem_bot.mpr hx1
  have hEinfP : E ⊓ P = ⊥ := by rw [inf_comm]; exact hPinfE
  have hD2infP : d.D2 ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxP := hx.2
    rw [hPdef] at hxP
    have hbot : x ∈ d.D2 ⊓ Q2' := ⟨hx.1, hxP.1⟩
    rw [hD2infQ2] at hbot
    exact Subgroup.mem_bot.mp hbot
  have hYcard : Nat.card Y = Nat.card d.D2 * Nat.card P := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := d.D2) (K := P) hD2NP
    rw [sup_comm d.D2 P, ← hYdef, hD2infP, Subgroup.card_bot, mul_one] at h
    exact h
  have hPY : P ≤ Y := by rw [hYdef]; exact le_sup_left
  have hrelD2 : P.relIndex Y = Nat.card d.D2 := by
    have hrel : P.relIndex Y * Nat.card P = Nat.card Y := by
      have h := Subgroup.relIndex_mul_card (H := P) (K := Y)
      rwa [inf_of_le_left hPY] at h
    exact Nat.mul_right_cancel (Nat.card_pos (α := ↥P)) (by rw [hrel, hYcard])
  have hOddIndex : Odd (P.relIndex Y) := by
    rw [hrelD2]
    exact d.hD2hall.2.1
  have hYN : Y ≤ Subgroup.normalizer (P : Set G) := by
    rw [hYdef]
    exact sup_le Subgroup.le_normalizer hD2NP
  have hP2p : IsPGroup 2 ↥P :=
    (pCoreOf_isPGroup 2 (P2 L1 L2 S)).to_le (by rw [hPdef]; exact inf_le_left)
  have hE2NQ2 : E ≤ Subgroup.normalizer (Q2' : Set G) := by
    have hE2P2 : E ≤ P2 L1 L2 S := by
      rw [hEdef, CFSG.conjugate]
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
      have h1 : w1⁻¹ ∈ P2 L1 L2 S := (P2 L1 L2 S).inv_mem hw1P2
      have h2 : w1⁻¹ * y ∈ P2 L1 L2 S := (P2 L1 L2 S).mul_mem h1 (hD2P2 hy)
      change (MulAut.conj w1⁻¹) y ∈ P2 L1 L2 S
      rw [MulAut.conj_apply, inv_inv]
      exact (P2 L1 L2 S).mul_mem h2 hw1P2
    exact hE2P2.trans hP2NQ2
  have hE2NC2 : E ≤ Subgroup.normalizer (C2 : Set G) := by
    rw [hEdef, CFSG.conjugate]
    calc Subgroup.map (MulAut.conj w1⁻¹).toMonoidHom d.D2
        ≤ Subgroup.map (MulAut.conj w1⁻¹).toMonoidHom (Subgroup.normalizer (C2 : Set G)) :=
          Subgroup.map_mono hD2NC2
      _ = Subgroup.normalizer
            (Subgroup.map (MulAut.conj w1⁻¹).toMonoidHom C2 : Subgroup G) :=
          Subgroup.map_equiv_normalizer_eq C2 (MulAut.conj w1⁻¹)
      _ = Subgroup.normalizer (C2 : Set G) := by
          have hmap : Subgroup.map (MulAut.conj w1⁻¹).toMonoidHom C2 = C2 :=
            Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ hw1NC2)
          rw [hmap]
  have hE2NP : E ≤ Subgroup.normalizer (P : Set G) := by
    rw [hPdef]
    exact (le_inf hE2NQ2 hE2NC2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hE2sup : P ⊔ E = Y := by
    have hprodE : Nat.card ↥(E ⊔ P) = Nat.card d.D2 * Nat.card P := by
      have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := E) (K := P) hE2NP
      rw [show E ⊓ P = ⊥ from hEinfP, Subgroup.card_bot, mul_one, hEcard] at h
      exact h
    have hle : P ⊔ E ≤ Y := sup_le hPY hE_le_Y
    have hcard : Nat.card ↥(P ⊔ E) = Nat.card Y := by
      rw [show P ⊔ E = E ⊔ P from sup_comm P E, hprodE, ← hYcard]
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  obtain ⟨x, hxP, hxE⟩ :=
    CFSG.Quasithin.H13.exists_mem_conj_of_complements hPY hYN hP2p hOddIndex
      (by rw [hYdef]; exact le_sup_right) (by rw [inf_comm]; exact hD2infP) hYdef.symm
      hE_le_Y hPinfE hE2sup
  set w : G := w1 * x with hweq
  have hxQ : x ∈ Q2' := (Subgroup.mem_inf.mp (by rwa [hPdef] at hxP)).1
  have hxP2 : x ∈ P2 L1 L2 S := (pCoreOf_le 2 (P2 L1 L2 S)) hxQ
  have hxNQ2 : x ∈ Subgroup.normalizer (Q2' : Set G) := hP2NQ2 hxP2
  have hwP2 : w ∈ P2 L1 L2 S := (P2 L1 L2 S).mul_mem hw1P2 hxP2
  have hwNQ2 : w ∈ Subgroup.normalizer (Q2' : Set G) := hP2NQ2 hwP2
  have hxC2 : x ∈ C2 := (Subgroup.mem_inf.mp (by rwa [hPdef] at hxP)).2
  have hwC2 : w ∈ C2 := C2.mul_mem hw1C hxC2
  have hEeq : E = Subgroup.map (MulAut.conj x) d.D2 := hxE
  have hE_as : E = CFSG.conjugate d.D2 x⁻¹ := by
    simpa [CFSG.conjugate, inv_inv] using hEeq
  have hconjE : CFSG.conjugate E x = d.D2 := by
    rw [hE_as, CFSG.conjugate_conjugate, inv_mul_cancel]
    exact CFSG.conjugate_eq_self_of_mem_normalizer
      (Subgroup.one_mem (Subgroup.normalizer (d.D2 : Set G)))
  have hwD2 : w ∈ Subgroup.normalizer (d.D2 : Set G) := by
    have hconj_w : CFSG.conjugate d.D2 w = d.D2 := by
      rw [hweq, ← CFSG.conjugate_conjugate, ← hEdef]
      exact hconjE
    have hmap : Subgroup.map (MulAut.conj w⁻¹).toMonoidHom d.D2 = d.D2 := by
      simpa [CFSG.conjugate] using hconj_w
    simpa using Subgroup.inv_mem _
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap)
  have hqQ : m * x ∈ Q2' := Q2'.mul_mem hmQ hxQ
  have hqP2 : m * x ∈ P2 L1 L2 S := (pCoreOf_le 2 (P2 L1 L2 S)) hqQ
  have hwq : w = d.w * (m * x) := by rw [hweq, hw1eq]; group
  have hwInv : ∀ δ ∈ d.D2, w * δ * w⁻¹ = δ⁻¹ := by
    intro δ hδ
    have hδP2 : δ ∈ P2 L1 L2 S := hD2P2 hδ
    let π : ↥(P2 L1 L2 S) →* oTwoQuot ↥(P2 L1 L2 S) :=
      QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(P2 L1 L2 S))
    let w0P : ↥(P2 L1 L2 S) := ⟨d.w, hw0P2⟩
    let wP : ↥(P2 L1 L2 S) := ⟨w, hwP2⟩
    let δP : ↥(P2 L1 L2 S) := ⟨δ, hδP2⟩
    let qP : ↥(P2 L1 L2 S) := ⟨m * x, hqP2⟩
    have hπq : π qP = 1 :=
      (QuotientGroup.eq_one_iff qP).mpr
        ((F1.mem_pCore_iff_coe qP).mpr (by rwa [hQ2def] at hqQ))
    have hwP_eq : wP = w0P * qP := Subtype.ext hwq
    have hπw_eq : π wP = π w0P := by
      rw [hwP_eq, map_mul, hπq, mul_one]
    have hsub : w0P * δP * w0P⁻¹ = δP⁻¹ := by
      apply Subtype.ext
      show d.w * δ * d.w⁻¹ = δ⁻¹
      exact d.hwInv δ hδ
    have hπδinv : π w0P * π δP * (π w0P)⁻¹ = (π δP)⁻¹ := by
      calc π w0P * π δP * (π w0P)⁻¹
          = π (w0P * δP * w0P⁻¹) := by rw [map_mul, map_mul, map_inv]
        _ = π δP⁻¹ := by rw [hsub]
        _ = (π δP)⁻¹ := map_inv π δP
    have hπmain : π (wP * δP * wP⁻¹ * δP) = 1 := by
      calc π (wP * δP * wP⁻¹ * δP)
          = π wP * π δP * (π wP)⁻¹ * π δP := by
              rw [map_mul, map_mul, map_mul, map_inv]
        _ = π w0P * π δP * (π w0P)⁻¹ * π δP := by rw [hπw_eq]
        _ = (π δP)⁻¹ * π δP := by rw [hπδinv]
        _ = 1 := inv_mul_cancel (π δP)
    have hmemCore : (wP * δP * wP⁻¹ * δP : ↥(P2 L1 L2 S)) ∈
        CFSG.Open.pCore 2 ↥(P2 L1 L2 S) := (QuotientGroup.eq_one_iff _).mp hπmain
    have hmemQ : w * δ * w⁻¹ * δ ∈ Q2' := by
      have h := (F1.mem_pCore_iff_coe (wP * δP * wP⁻¹ * δP)).mp hmemCore
      rwa [hQ2def]
    have hwδD : w * δ * w⁻¹ ∈ d.D2 :=
      (Subgroup.mem_normalizer_iff.mp hwD2 δ).mp hδ
    have hprodD : w * δ * w⁻¹ * δ ∈ d.D2 := d.D2.mul_mem hwδD hδ
    have hbot : w * δ * w⁻¹ * δ ∈ d.D2 ⊓ Q2' := ⟨hprodD, hmemQ⟩
    rw [hD2infQ2, Subgroup.mem_bot] at hbot
    have h1 : w * δ * w⁻¹ * δ = 1 := by
      calc w * δ * w⁻¹ * δ = w * (δ * (w⁻¹ * δ)) := by group
        _ = 1 := by simpa [mul_assoc] using hbot
    exact eq_inv_of_mul_eq_one_left h1
  have hwH2 : w ∈ L2 ⊔ S := by
    have hmS : m ∈ S := hQ2S hmQ
    have hxS : x ∈ S := hQ2S hxQ
    have hw1H : w1 ∈ L2 ⊔ S := by
      rw [hw1eq]
      exact (L2 ⊔ S).mul_mem d.hwH2 (Subgroup.mem_sup_right hmS)
    rw [hweq]
    exact (L2 ⊔ S).mul_mem hw1H (Subgroup.mem_sup_right hxS)
  have hqS : m * x ∈ S := hQ2S hqQ
  have hwNotN : w ∉ Subgroup.normalizer (S : Set G) := by
    intro hwN
    apply d.hwNotN
    have hqinvS : (m * x)⁻¹ ∈ Subgroup.normalizer (S : Set G) :=
      Subgroup.le_normalizer (S.inv_mem hqS)
    have heq : d.w = w * (m * x)⁻¹ := by rw [hwq]; group
    rw [heq]
    exact (Subgroup.normalizer (S : Set G)).mul_mem hwN hqinvS
  have hqH : m * x ∈ S ⊔ CFSG.conjugate S d.w := Subgroup.mem_sup_left hqS
  have hfixinv : Subgroup.map (MulAut.conj (m * x)⁻¹).toMonoidHom
      (S ⊔ CFSG.conjugate S d.w) = S ⊔ CFSG.conjugate S d.w :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer ((S ⊔ CFSG.conjugate S d.w).inv_mem hqH))
  have hcs : CFSG.conjugate (S ⊔ CFSG.conjugate S d.w) (m * x) =
      CFSG.conjugate S (m * x) ⊔ CFSG.conjugate (CFSG.conjugate S d.w) (m * x) := by
    simp only [CFSG.conjugate, Subgroup.map_sup]
  have hwTop : S ⊔ CFSG.conjugate S w = L2 ⊔ S := by
    calc S ⊔ CFSG.conjugate S w
        = S ⊔ CFSG.conjugate (CFSG.conjugate S d.w) (m * x) := by
            rw [hwq, ← CFSG.conjugate_conjugate]
      _ = CFSG.conjugate S (m * x) ⊔ CFSG.conjugate (CFSG.conjugate S d.w) (m * x) := by
            rw [CFSG.conjugate_eq_self_of_mem_normalizer (Subgroup.le_normalizer hqS)]
      _ = CFSG.conjugate (S ⊔ CFSG.conjugate S d.w) (m * x) := hcs.symm
      _ = S ⊔ CFSG.conjugate S d.w := hfixinv
      _ = L2 ⊔ S := d.hwTop
  let d' : Str83G4Data L1 L2 S :=
    { D1 := d.D1, D2 := d.D2, hD1hall := d.hD1hall, hD2hall := d.hD2hall,
      hD1sup := d.hD1sup, hD2sup := d.hD2sup, hcomm := d.hcomm, hBsplit := d.hBsplit,
      hdelta := d.hdelta, w := w, hwH2 := hwH2, hwD2 := hwD2, hwInv := hwInv,
      hwNotN := hwNotN, hwTop := hwTop }
  exact ⟨d', rfl, rfl, hwC2⟩

end CFSG.Quasithin.Stroth

end
