module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicAllData
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineCo3
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineFi24
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSuz
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSUFi22
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSUFi23
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCatU6
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.LocalAnalysis.ComponentClassification.FourExactOuterHN
public import CFSG.Sporadic.SuzOddCore.CTIComponents
public import CFSG.RankThree.PartOne.KP.Co3Aut
public import CFSG.RankThree.PartOne.SPOR.Outer

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.UnitaryPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Open (ordTwistedA)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (MonsterInnerInput MonsterLocalComponentsInput
  isComponent_map_mulEquiv exists_conj_or_not_mem_range)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)

theorem not_fixedCentralizerTwoSmall_of_pair {S : Type} [Group S] [Finite S] {σ : MulAut S}
    {D : Subgroup (fixedSubgroup σ)} {x y : S} (hx : x * x = 1) (hy : y * y = 1) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) (hxy : x ≠ y) (hc : x * y = y * x) (hxσ : x ∈ fixedSubgroup σ)
    (hyσ : y ∈ fixedSubgroup σ) (hxD : ∀ d ∈ D, ((d : fixedSubgroup σ) : S) * x = x * d)
    (hyD : ∀ d ∈ D, ((d : fixedSubgroup σ) : S) * y = y * d) :
    ¬ FixedCentralizerTwoSmall σ D := by
  intro hsmall
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq, hx]) hx1
  have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [sq, hy]) hy1
  have hX : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  have hY : IsPGroup 2 (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  have hXY : zpowers x ≤ Subgroup.normalizer ((zpowers y : Subgroup S) : Set S) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_le, mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (Commute.zpow_right (show Commute x y from hc) k).eq.symm
  have hU := hX.to_sup_of_normal_right' hY hXY
  have hle1 : zpowers x ⊔ zpowers y ≤
      centralizer ((D.map (fixedSubgroup σ).subtype : Subgroup S) : Set S) := by
    refine sup_le ?_ ?_ <;> rw [zpowers_le, mem_centralizer_iff] <;> rintro _ ⟨d, hd, rfl⟩
    · exact hxD d hd
    · exact hyD d hd
  have hle2 : zpowers x ⊔ zpowers y ≤ fixedSubgroup σ :=
    sup_le (zpowers_le.2 hxσ) (zpowers_le.2 hyσ)
  have h2 := hsmall _ hU hle1 hle2
  have heq : zpowers x = zpowers x ⊔ zpowers y :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [Nat.card_zpowers, hxo]; exact h2)
  have hymem : y ∈ zpowers x := heq ▸ (le_sup_right : zpowers y ≤ _) (mem_zpowers y)
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hymem
  rw [← zpow_mod_orderOf, hxo] at hy1 hxy
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · apply hy1
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
  · apply hxy
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]

theorem false_of_monster_PSU (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.M) {σ : MulAut S}
    (hσ : orderOf σ = 2) {m f : ℕ} {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSU m 2 f) : False := by
  obtain ⟨h41, h42⟩ :=
    OmegaPilot.monster_two_part_card_quotient_center hMinn hMcomp hS hna e hσ hD
  obtain ⟨hf, hm, -⟩ := admissible_of_lieModel_PSU hDm
  obtain ⟨r, hr, hO⟩ :=
    (Timmesfeld.Orders.profile_ordTwistedA (n := m - 1) (g := f) (by omega) hf).two
  have h := OmegaPilot.eq_forty_one_of_two_part hr
    ((card_of_lieModel_PSU_two_pow hDm).trans hO) h41 h42
  rw [show m - 1 + 1 = m by omega] at h
  have hm10 : m < 10 := by
    by_contra h'
    have h90 : 9 * 10 ≤ (m - 1) * m := Nat.mul_le_mul (by omega) (by omega)
    have : (m - 1) * m / 2 ≤ f * ((m - 1) * m / 2) := Nat.le_mul_of_pos_left _ hf
    omega
  interval_cases m <;> omega

@[expose] def sumSporadicResidual (m f : ℕ) (s : TauCeti.SporadicName) : Prop :=
  (m = 4 ∧ f = 1) ∨ (m = 4 ∧ (f = 2 ∨ f = 3) ∧ s = .B) ∨
    (m = 5 ∧ f = 1 ∧ (s = .Suz ∨ s = .Co1 ∨ s = .Co2 ∨ s = .Co3 ∨ s = .Fi22 ∨ s = .Fi23 ∨
      s = .Fi24Prime ∨ s = .HN ∨ s = .B)) ∨
    (m = 6 ∧ f = 1 ∧ (s = .Co1 ∨ s = .Co2 ∨ s = .Fi22 ∨ s = .Fi23 ∨ s = .Fi24Prime ∨ s = .B))

instance (m f : ℕ) (s : TauCeti.SporadicName) : Decidable (sumSporadicResidual m f s) := by
  unfold sumSporadicResidual
  infer_instance

theorem sumSporadicResidual_of_check {m f N : ℕ} {s : TauCeti.SporadicName} (hm : 4 ≤ m)
    (hf : 1 ≤ f) (hdvd : ordTwistedA (m - 1) (2 ^ f) ∣ N) (h47 : ¬ 2 ^ 47 ∣ N)
    (hcheck : ∀ m ∈ Finset.range 11, ∀ f ∈ Finset.range 8, 4 ≤ m → 1 ≤ f →
      f * ((m - 1) * m / 2) ≤ 46 → sumSporadicResidual m f s ∨
        ¬ ordTwistedA (m - 1) (2 ^ f) ∣ N) :
    sumSporadicResidual m f s := by
  have hb := (ordTwistedA_two_pow_bounds (n := m - 1) (by omega) hf).1
  rw [show m - 1 + 1 = m by omega] at hb
  have h2 : f * ((m - 1) * m / 2) ≤ 46 := by
    by_contra h
    exact h47 ((Nat.pow_dvd_pow 2 (by omega)).trans (hb.trans hdvd))
  have hm11 : m < 11 := by
    by_contra h
    have h110 : 10 * 11 ≤ (m - 1) * m := Nat.mul_le_mul (by omega) (by omega)
    have : (m - 1) * m / 2 ≤ f * ((m - 1) * m / 2) := Nat.le_mul_of_pos_left _ hf
    omega
  have hf8 : f < 8 := by
    have h12 : 3 * 4 ≤ (m - 1) * m := Nat.mul_le_mul (by omega) hm
    have : f * 6 ≤ f * ((m - 1) * m / 2) := Nat.mul_le_mul_left f (by omega)
    omega
  rcases hcheck m (Finset.mem_range.mpr hm11) f (Finset.mem_range.mpr hf8) hm hf h2 with h | h
  · exact h
  · exact absurd hdvd h

section Orders


theorem sumSporadicResidual_of_dvd {m f : ℕ} (hm : 4 ≤ m) (hf : 1 ≤ f)
    {s : TauCeti.SporadicName} (hs : s ≠ .M)
    (hdvd : ordTwistedA (m - 1) (2 ^ f) ∣ Nat.card (NativeSporadic.Carrier s)) :
    sumSporadicResidual m f s := by
  have gen : ∀ N : ℕ, Nat.card (NativeSporadic.Carrier s) = N → ¬ 2 ^ 47 ∣ N →
      (∀ m ∈ Finset.range 11, ∀ f ∈ Finset.range 8, 4 ≤ m → 1 ≤ f →
        f * ((m - 1) * m / 2) ≤ 46 → sumSporadicResidual m f s ∨
          ¬ ordTwistedA (m - 1) (2 ^ f) ∣ N) →
      sumSporadicResidual m f s :=
    fun N hN h47 hcheck => sumSporadicResidual_of_check hm hf (hN ▸ hdvd) h47 hcheck
  cases s
  case M11 => exact gen _ Sporadic.Mathieu.card_M11 (by decide) (by decide)
  case M12 => exact gen _ Sporadic.Mathieu.card_M12 (by decide) (by decide)
  case M22 => exact gen _ Sporadic.Mathieu.card_M22 (by decide) (by decide)
  case M23 => exact gen _ EvenSmallLie.CatalogOrders.card_M23 (by decide) (by decide)
  case M24 => exact gen _ Sporadic.Mathieu.card_M24 (by decide) (by decide)
  case J1 => exact gen _ Sporadic.J1.card_J1 (by decide) (by decide)
  case J2 => exact gen _ Sporadic.J2.card_J2 (by decide) (by decide)
  case J3 => exact gen _ Sporadic.J3.card_J3 (by decide) (by decide)
  case J4 => exact gen _ Sporadic.J4.card_J4 (by decide) (by decide)
  case HS => exact gen _ Sporadic.HS.card_HS (by decide) (by decide)
  case McL => exact gen _ Sporadic.McL.card_McL (by decide) (by decide)
  case He => exact gen _ Sporadic.He.fam_he_order.1 (by decide) (by decide)
  case Ru => exact gen _ Sporadic.Ru.card_Ru (by decide) (by decide)
  case Suz => exact gen _ Sporadic.Suz.card_Suz (by decide) (by decide)
  case ONan => exact gen _ Sporadic.ON.card_ON (by decide) (by decide)
  case Co1 => exact gen _ Sporadic.Co1.card_Co1 (by decide) (by decide)
  case Co2 => exact gen _ Sporadic.Co2.card_Co2 (by decide) (by decide)
  case Co3 => exact gen _ Sporadic.Co3.card_Co3 (by decide) (by decide)
  case Fi22 => exact gen _ Sporadic.Fi22.card_Fi22 (by decide) (by decide)
  case Fi23 => exact gen _ Sporadic.Fi23.card_Fi23 (by decide) (by decide)
  case Fi24Prime => exact gen _ Sporadic.Fi24.card_Fi24prime (by decide) (by decide)
  case HN => exact gen _ Sporadic.HN.card_HN (by decide) (by decide)
  case Ly => exact gen _ Sporadic.Ly.card_Ly (by decide) (by decide)
  case Th => exact gen _ Monster.Existence.Compat.card_nativeTh (by decide) (by decide)
  case B => exact gen _ Monster.Existence.card_nativeB (by decide) (by decide)
  case M => exact absurd rfl hs

end Orders

section Co1


theorem co1_fixed_card_quotient {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Co1) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    Nat.card (D ⧸ center D) = 251596800 := by
  obtain ⟨u, rfl⟩ :=
    ComponentClassification.BMCase.inner_of_equiv e RankThree.PartOne.SPOR.allInner_Co1 σ
  obtain ⟨B, hB, hcard⟩ := OmegaPilot.exists_component_centralizer_of_conj u hD
  rw [← hcard]
  exact (ComponentClassification.RestrictedStd.Spor.co1LocalComponentsInput_holds S e u
    (OmegaPilot.orderOf_eq_two_of_conj hS hna hσ) B hB).1

end Co1

section Co3


theorem co3_fixed_card_quotient {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Co3) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    Nat.card (D ⧸ center D) = 1451520 ∨ Nat.card (D ⧸ center D) = 95040 := by
  obtain ⟨u, rfl⟩ := RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.2.2.2.2 S ⟨e⟩ σ
  obtain ⟨B, hB, hcard⟩ := OmegaPilot.exists_component_centralizer_of_conj u hD
  rw [← hcard]
  rcases SporadicRefine.co3_involution_component_card ⟨e⟩
      (OmegaPilot.orderOf_eq_two_of_conj hS hna hσ) hB with ⟨-, h⟩ | ⟨-, h⟩
  · exact .inl h
  · exact .inr h

end Co3

section HN


theorem hn_fixed_card_quotient {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .HN) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    Nat.card (D ⧸ center D) = 44352000 ∨ Nat.card (D ⧸ center D) ∣ 3628800 := by
  rcases exists_conj_or_not_mem_range σ with ⟨u, rfl⟩ | hout
  · obtain ⟨B, hB, hcard⟩ := OmegaPilot.exists_component_centralizer_of_conj u hD
    rw [← hcard]
    exact .inl (ComponentClassification.RestrictedStd.Spor.hnLocalComponentsInput_holds S e u
      (OmegaPilot.orderOf_eq_two_of_conj hS hna hσ) B hB)
  · obtain ⟨φ⟩ := ComponentClassification.RestrictedStd.Spor.hnOuterFixInput S e σ hσ hout
    have hfix : Nat.card (fixedSubgroup σ) = 3628800 := by
      have hfs : fixedSubgroup σ = Sporadic.Schreier.fixSub σ := by
        ext x
        exact Iff.rfl
      rw [Nat.card_congr (MulEquiv.subgroupCongr hfs).toEquiv, Nat.card_congr φ.toEquiv,
        Nat.card_perm, Nat.card_fin]
      rfl
    right
    rw [← hfix]
    exact (card_quotient_dvd_card _).trans (card_subgroup_dvd_card D)

end HN

section Co2


theorem co2_false_of_fixed_component {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Co2) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) : False := by
  obtain ⟨u, rfl⟩ :=
    ComponentClassification.BMCase.inner_of_equiv e RankThree.PartOne.SPOR.allInner_Co2 σ
  obtain ⟨B, hB, -⟩ := OmegaPilot.exists_component_centralizer_of_conj u hD
  exact Sporadic.Co2Schreier.CTI_Co2_involution_centralizers_have_no_components e u
    (OmegaPilot.orderOf_eq_two_of_conj hS hna hσ) B hB

end Co2

section Suz


theorem suz_fixed_card_quotient {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Suz) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    Nat.card (D ⧸ center D) = 20160 ∨ Nat.card (D ⧸ center D) ∣ 190080 ∨
      Nat.card (D ⧸ center D) ∣ 1209600 := by
  rcases exists_conj_or_not_mem_range σ with ⟨u, rfl⟩ | hout
  · obtain ⟨B, hB, hcard⟩ := OmegaPilot.exists_component_centralizer_of_conj u hD
    rw [← hcard]
    exact .inl (Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e u
      (OmegaPilot.orderOf_eq_two_of_conj hS hna hσ) B hB)
  · have hdvd : Nat.card (D ⧸ center D) ∣ Nat.card (fixedSubgroup σ) :=
      (card_quotient_dvd_card _).trans (card_subgroup_dvd_card D)
    rcases SporadicRefine.suz_outer_card_fixedSubgroup e hσ hout with h | h <;> rw [h] at hdvd
    · exact .inr (.inl hdvd)
    · exact .inr (.inr hdvd)

end Suz

section Fi22


theorem fi22_fixed_card_quotient {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Fi22) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    (σ ∈ (MulAut.conj : S →* MulAut S).range →
        Nat.card (D ⧸ center D) = 9196830720 ∧ Nat.card (center D) = 2) ∧
      (σ ∉ (MulAut.conj : S →* MulAut S).range →
        Nat.card (D ⧸ center D) = 174182400 ∨ Nat.card (D ⧸ center D) = 1451520) := by
  refine ⟨fun hin => ?_, fun hout => ?_⟩
  · obtain ⟨u, rfl⟩ := hin
    have hu := OmegaPilot.orderOf_eq_two_of_conj hS hna hσ
    let φ := MulEquiv.subgroupCongr (F4Pilot.fixedSubgroup_conj u)
    have hB := isComponent_map_mulEquiv φ hD
    have eD := D.equivMapOfInjective φ.toMonoidHom φ.injective
    refine ⟨?_, ?_⟩
    · rw [TwistedE6Pilot.card_quotient_center_eq_of_mulEquiv eD]
      exact Sporadic.FischerOddCore.CTI_Fi22_involution_local_components_unitary_quotient_order
        e u hu _ hB
    · rw [Nat.card_congr (Subgroup.centerCongr eD).toEquiv]
      exact fi22_involution_component_card_center e u hu _ hB
  · obtain ⟨B, hB, hcard⟩ := OmegaPilot.exists_component_fixSub σ hD
    rw [← hcard]
    exact Sporadic.FischerOddCore.fi22OuterComponentsInput_holds S ⟨e⟩ σ
      (by rw [← sq, ← hσ, pow_orderOf_eq_one]) hout B hB

end Fi22

section Fi23


theorem fi23_fixed_card_quotient {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Fi23) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D) :
    Nat.card (D ⧸ center D) = 64561751654400 ∨ Nat.card (D ⧸ center D) = 9196830720 := by
  obtain ⟨u, rfl⟩ :=
    ComponentClassification.BMCase.inner_of_equiv e Sporadic.FischerOddCore.fi23_mulAut_eq_conj σ
  obtain ⟨B, hB, hcard⟩ := OmegaPilot.exists_component_centralizer_of_conj u hD
  rw [← hcard]
  exact fi23_involution_component_card_quotient e u (OmegaPilot.orderOf_eq_two_of_conj hS hna hσ)
    B hB

theorem fi23_fixed_not_twoSmall {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Fi23) {σ : MulAut S}
    (hσ : orderOf σ = 2) {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hcard : Nat.card (D ⧸ center D) = 9196830720) : ¬ FixedCentralizerTwoSmall σ D := by
  obtain ⟨u, rfl⟩ :=
    ComponentClassification.BMCase.inner_of_equiv e Sporadic.FischerOddCore.fi23_mulAut_eq_conj σ
  have hu := OmegaPilot.orderOf_eq_two_of_conj hS hna hσ
  let φ := MulEquiv.subgroupCongr (F4Pilot.fixedSubgroup_conj u)
  have hB := isComponent_map_mulEquiv φ hD
  have hcB : Nat.card (D.map φ.toMonoidHom ⧸ center (D.map φ.toMonoidHom)) = 9196830720 := by
    rw [← TwistedE6Pilot.card_quotient_center_eq_of_mulEquiv
      (D.equivMapOfInjective φ.toMonoidHom φ.injective)]
    exact hcard
  obtain ⟨x, y, hx, hy, hx1, hy1, hxy, hc, hxyu, hBc⟩ :=
    fi23_involution_component_exists_pair e u hu _ hB hcB
  have hmem : ∀ z : S, z * u = u * z → z ∈ fixedSubgroup (MulAut.conj u) := fun z hz => by
    rw [F4Pilot.fixedSubgroup_conj, mem_centralizer_singleton_iff]
    exact hz
  refine not_fixedCentralizerTwoSmall_of_pair hx hy hx1 hy1 hxy hc (hmem x ?_) (hmem y ?_)
    (fun d hd => (hBc (φ d) ⟨d, hd, rfl⟩).1) (fun d hd => (hBc (φ d) ⟨d, hd, rfl⟩).2)
  · rw [← hxyu, ← mul_assoc, hx, one_mul, hc, mul_assoc, hx, mul_one]
  · rw [← hxyu, hc, ← mul_assoc, hy, one_mul, ← hc, mul_assoc, hy, mul_one]

end Fi23

section Clause

open CFSG.Sporadic.FischerOddCore
  (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven)


theorem false_of_sporadic_PSU (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (hsp : NativeSporadic.SporadicRep S) {σ : MulAut S}
    (hσ : orderOf σ = 2) {m f : ℕ} (hm : 4 ≤ m) (hmf : ¬ (m = 4 ∧ f = 1))
    {D : Subgroup (fixedSubgroup σ)} (hD : IsComponent D)
    (hDm : LieModel (D ⧸ center D) .PSU m 2 f)
    (hcond : (σ ∈ (MulAut.conj : S →* MulAut S).range ∧ FixedCentralizerTwoSmall σ D ∧
        Odd (Nat.card (center D))) ∨ FixedCentralizerTwoFree σ D) : False := by
  have := hS
  have hin : σ ∈ (MulAut.conj : S →* MulAut S).range →
      FixedCentralizerTwoSmall σ D ∧ Odd (Nat.card (center D)) := fun h =>
    hcond.elim (fun h' => h'.2)
      (fun h' => absurd h (LinearPilot.not_mem_range_conj_of_twoFree hna hσ h'))
  have hout : σ ∉ (MulAut.conj : S →* MulAut S).range → FixedCentralizerTwoFree σ D :=
    fun h => hcond.resolve_left fun h' => h h'.1
  obtain ⟨s, ⟨e⟩⟩ := hsp
  by_cases hsM : s = .M
  · subst hsM
    exact false_of_monster_PSU hMinn hMcomp hS hna e hσ hD hDm
  have hc := card_of_lieModel_PSU_two_pow hDm
  have hdvd : ordTwistedA (m - 1) (2 ^ f) ∣ Nat.card (NativeSporadic.Carrier s) := by
    rw [← hc, ← Nat.card_congr e.toEquiv]
    exact OmegaPilot.card_quotient_center_dvd_card_of_fixed D
  rcases sumSporadicResidual_of_dvd hm (admissible_of_lieModel_PSU hDm).1 hsM hdvd with
    ⟨rfl, rfl⟩ | ⟨rfl, hf, rfl⟩ | ⟨rfl, rfl, hs⟩ | ⟨rfl, rfl, hs⟩
  · exact hmf ⟨rfl, rfl⟩
  ·
    have hv : ordTwistedA (4 - 1) (2 ^ f) = 1018368000 ∨
        ordTwistedA (4 - 1) (2 ^ f) = 34693789777920 := by
      rcases hf with rfl | rfl
      · left; decide
      · right; decide
    rcases OmegaPilot.baby_card_quotient_center hS hna e hσ hD with h | h <;>
      rcases hv with h' | h' <;> rw [hc, h'] at h <;> norm_num at h
  ·
    have hv : ordTwistedA (5 - 1) (2 ^ 1) = 13685760 := by decide
    rw [hv] at hc
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rcases suz_fixed_card_quotient hS hna e hσ hD with h | h | h <;> rw [hc] at h <;>
        norm_num at h
    · have h := co1_fixed_card_quotient hS hna e hσ hD
      rw [hc] at h
      norm_num at h
    · exact co2_false_of_fixed_component hS hna e hσ hD
    · rcases co3_fixed_card_quotient hS hna e hσ hD with h | h <;> rw [hc] at h <;> norm_num at h
    · by_cases hσin : σ ∈ (MulAut.conj : S →* MulAut S).range
      · have h := ((fi22_fixed_card_quotient hS hna e hσ hD).1 hσin).1
        rw [hc] at h
        norm_num at h
      · rcases (fi22_fixed_card_quotient hS hna e hσ hD).2 hσin with h | h <;> rw [hc] at h <;>
          norm_num at h
    · rcases fi23_fixed_card_quotient hS hna e hσ hD with h | h <;> rw [hc] at h <;>
        norm_num at h
    · rcases OmegaPilot.fi24_card_quotient_center hS hna e hσ hD with h | h | h <;>
        rw [hc] at h <;> norm_num at h
    · rcases hn_fixed_card_quotient hS hna e hσ hD with h | h <;> rw [hc] at h <;> norm_num at h
    · rcases OmegaPilot.baby_card_quotient_center hS hna e hσ hD with h | h <;> rw [hc] at h <;>
        norm_num at h
  ·
    have hv : ordTwistedA (6 - 1) (2 ^ 1) = 9196830720 := by decide
    rw [hv] at hc
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · have h := co1_fixed_card_quotient hS hna e hσ hD
      rw [hc] at h
      norm_num at h
    · exact co2_false_of_fixed_component hS hna e hσ hD
    ·
      by_cases hσin : σ ∈ (MulAut.conj : S →* MulAut S).range
      · have h := ((fi22_fixed_card_quotient hS hna e hσ hD).1 hσin).2
        have hodd := (hin hσin).2
        rw [h] at hodd
        exact absurd hodd (by decide)
      · rcases (fi22_fixed_card_quotient hS hna e hσ hD).2 hσin with h | h <;> rw [hc] at h <;>
          norm_num at h
    ·
      have hσin : σ ∈ (MulAut.conj : S →* MulAut S).range := by
        obtain ⟨g, hg⟩ := ComponentClassification.BMCase.inner_of_equiv e
          Sporadic.FischerOddCore.fi23_mulAut_eq_conj σ
        exact ⟨g, hg.symm⟩
      exact fi23_fixed_not_twoSmall hS hna e hσ hD hc (hin hσin).1
    ·
      by_cases hσin : σ ∈ (MulAut.conj : S →* MulAut S).range
      · obtain ⟨u, rfl⟩ := hσin
        obtain ⟨B, hB, hcard⟩ := OmegaPilot.exists_component_centralizer_of_conj u hD
        have h := (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven
          e u (OmegaPilot.orderOf_eq_two_of_conj hS hna hσ) B hB).1
        rw [hcard, hc] at h
        norm_num at h
      · exact SporadicRefine.fi24_outer_not_twoFree_of_unitary e hσ hσin hD hc (hout hσin)
    · rcases OmegaPilot.baby_card_quotient_center hS hna e hσ hD with h | h <;> rw [hc] at h <;>
        norm_num at h

theorem catSUmSporadicAt_of_monster (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) {m : ℕ} (hm : 4 ≤ m) : CatSUmSporadicAt m := by
  intro S _ _ hS hna hsp σ hσ f D hD hDm hcond
  by_contra hmf
  exact false_of_sporadic_PSU hMinn hMcomp hS hna hsp hσ hm hmf hD hDm hcond

theorem catSUmSporadicAtF_six_one_of_monster (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) : TwistedE6Pilot.CatSUmSporadicAtF 6 1 :=
  TwistedE6Pilot.catSUmSporadicAt_iff.1 (catSUmSporadicAt_of_monster hMinn hMcomp (by norm_num)) 1

end Clause

end CFSG.SeitzReduction.UnitaryPilot
