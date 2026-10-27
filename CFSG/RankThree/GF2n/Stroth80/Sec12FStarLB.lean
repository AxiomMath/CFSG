module

public import CFSG.RankThree.GF2n.Stroth80.Sec12FStarIii
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerived
import CFSG.Holt.H78.Lemma17
import CFSG.RankThree.GF2n.Stroth80.Sec12TorusFpf
import CFSG.RankThree.GF2n.Stroth80.Sec123Torus
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCentralizer
import CFSG.RankThree.GF2n.Stroth80.Sec12Basic
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial.OuterDerived
open scoped commutatorElement

theorem exists_conj_eq_of_odd_outer_commutator {Γ : Type*} [Group Γ] {X : Subgroup Γ} [X.Normal]
    (hodd : Odd (Nat.card (commutator (Outer ↥X)))) {c t : Γ} {k : ℕ}
    (hk : ⁅c, t⁆ ^ 2 ^ k = 1) :
    ∃ x ∈ X, ∀ w ∈ X, ⁅c, t⁆ * w * ⁅c, t⁆⁻¹ = x * w * x⁻¹ := by
  set φ : Γ →* Outer ↥X := (QuotientGroup.mk' (inner ↥X)).comp MulAut.conjNormal with hφ
  have hmem : φ ⁅c, t⁆ ∈ commutator (Outer ↥X) := by
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have h1 : φ ⁅c, t⁆ = 1 := by
    set a : ↥(commutator (Outer ↥X)) := ⟨φ ⁅c, t⁆, hmem⟩ with ha
    have hak : a ^ 2 ^ k = 1 := Subtype.ext (by
      show (φ ⁅c, t⁆) ^ 2 ^ k = 1
      rw [← map_pow, hk, map_one])
    have hcop : Nat.Coprime (2 ^ k) (Nat.card (commutator (Outer ↥X))) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
    have hdvd : orderOf a ∣ Nat.gcd (2 ^ k) (Nat.card (commutator (Outer ↥X))) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hak) (orderOf_dvd_natCard a)
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
    exact congrArg Subtype.val hdvd
  have h2 : MulAut.conjNormal ⁅c, t⁆ ∈ inner ↥X := (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨x, hx⟩ := h2
  refine ⟨x, x.2, fun w hw => ?_⟩
  have h3 := congrArg (fun α : MulAut ↥X => ((α ⟨w, hw⟩ : ↥X) : Γ)) hx
  simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at h3
  exact h3.symm

theorem odd_card_commutator_outer_of_six_model {J : Type} [Group J] [IsSimpleGroup J] {r : ℕ}
    (hr : 1 ≤ r) (hna : ∃ a b : J, a * b ≠ b * a)
    (h : IsPSUModel 6 (2 ^ r) J ∨ IsPSLModel 6 (2 ^ r) J) :
    Odd (Nat.card (commutator (Outer J))) := by
  have hnc : ¬ IsMulCommutative J := fun hc => by
    obtain ⟨a, b, hab⟩ := hna
    exact hab (hc.is_comm.comm a b)
  haveI : Group.IsPerfect J := TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnc
  have hcen : Subgroup.center J = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna).2
  let eZ : J ⧸ Subgroup.center J ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  have heven : Even (2 ^ r) := (Nat.even_pow' (by omega)).mpr even_two
  rcases h with ⟨K, i₁, i₂, hK, ⟨e⟩⟩ | ⟨K, i₁, i₂, hK, ⟨e⟩⟩
  · obtain ⟨-, hcard, -⟩ := unitary_perfect_cover_outer_derived_diagonal_bound J 6 2 r
      ⟨⟨Nat.prime_two, hr, by norm_num, by simp⟩, K, i₁, i₂, hK, ⟨eZ.trans e⟩⟩
    exact heven.add_one.of_dvd_nat (hcard.trans (Nat.gcd_dvd_right _ _))
  · obtain ⟨-, hcard, -⟩ := linear_perfect_cover_outer_derived_diagonal_bound J 6 2 r
      ⟨⟨Nat.prime_two, hr, by norm_num, by simp, by simp⟩, K, i₁, i₂, hK, ⟨eZ.trans e⟩⟩
    exact (Nat.Even.sub_odd Nat.one_le_two_pow heven odd_one).of_dvd_nat
      (hcard.trans (Nat.gcd_dvd_right _ _))

theorem stroth12FStarLB_holds : Stroth12FStarLBStatement := by
  intro G _ _ M Q Z B hN hc n h12 t ht htQ hF
  classical
  set H := bar M Q (H0 M Z) with hHdef
  haveI hHn : H.Normal := hc.normal_bar_H0
  set X := inSubgroup generalizedFitting H with hXdef
  haveI hXn : X.Normal := normal_inSubgroup_fstar H
  obtain ⟨r, hr⟩ : ∃ r : ℕ, Nat.card Z = 2 ^ r := by
    obtain ⟨r, -, hr, -⟩ := hc.hyp.cp
    exact ⟨r, hr⟩
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [hr, h0] at hq4
      norm_num at hq4
    · exact h0
  have hmod : IsPSUModel 6 (2 ^ r) ↥(generalizedFitting ↥H) ∨
      IsPSLModel 6 (2 ^ r) ↥(generalizedFitting ↥H) := by
    rcases hF with ⟨-, hU⟩ | ⟨-, hL⟩
    · left
      unfold FStarU6 at hU
      rwa [hr] at hU
    · right
      unfold FStarL6 at hL
      rwa [hr] at hL
  have hsn : IsSimpleGroup ↥(generalizedFitting ↥H) ∧
      ∃ a b : ↥(generalizedFitting ↥H), a * b ≠ b * a := by
    rcases hmod with hU | hL
    · exact isSimpleGroup_of_isPSUModel hU
    · exact isSimpleGroup_of_isPSLModel hL
  obtain ⟨hs, hna⟩ := hsn
  haveI := hs
  have hFc : Subgroup.center ↥(generalizedFitting ↥H) = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna).2
  let eX : ↥(generalizedFitting ↥H) ≃* ↥X :=
    (generalizedFitting ↥H).equivMapOfInjective H.subtype H.subtype_injective
  haveI : IsSimpleGroup ↥X := eX.symm.isSimpleGroup
  have hnaX : ∃ a b : ↥X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨eX a, eX b, fun h => hab (eX.injective (by rw [map_mul, map_mul, h]))⟩
  have hmodX : IsPSUModel 6 (2 ^ r) ↥X ∨ IsPSLModel 6 (2 ^ r) ↥X := by
    rcases hmod with ⟨K, i₁, i₂, hK, ⟨e⟩⟩ | ⟨K, i₁, i₂, hK, ⟨e⟩⟩
    · exact Or.inl ⟨K, i₁, i₂, hK, ⟨eX.symm.trans e⟩⟩
    · exact Or.inr ⟨K, i₁, i₂, hK, ⟨eX.symm.trans e⟩⟩
  have hodd : Odd (Nat.card (commutator (Outer ↥X))) :=
    odd_card_commutator_outer_of_six_model hr1 hnaX hmodX
  obtain ⟨y, hyX, hyM, hyB, hyZ, -, hyreg⟩ := hc.exists_torusOrd
  have hreg1 : ∀ v ∈ Z, y * v = v * y → v = 1 := fun v hv h =>
    hyreg 1 one_pos (by omega) v hv (by simpa using h)
  set yb : Mbar M Q := QuotientGroup.mk' (Q.subgroupOf M) ⟨y, hyM⟩ with hyb
  have hLconj : ∀ g ∈ M, g ∈ Subgroup.normalizer (B : Set G) →
      ∀ c ∈ LB M Q B, g * c * g⁻¹ ∈ LB M Q B := by
    intro g hgM hgB c hc'
    have h1 := hc.LB_conj hgM
    rw [conjSubgroup_eq_self_iff.mpr hgB] at h1
    have h2 : g * c * g⁻¹ ∈ conjSubgroup g (LB M Q B) := mem_conjSubgroup.mpr (by
      have e : g⁻¹ * (g * c * g⁻¹) * g = c := by group
      rw [e]
      exact hc')
    rwa [← h1] at h2
  have hLnorm : ∀ (g : ↥M), (g : G) ∈ Subgroup.normalizer (B : Set G) →
      ∀ c ∈ bar M Q (LB M Q B), QuotientGroup.mk' (Q.subgroupOf M) g * c *
        (QuotientGroup.mk' (Q.subgroupOf M) g)⁻¹ ∈ bar M Q (LB M Q B) := by
    rintro g hgB _ ⟨c, hc', rfl⟩
    refine ⟨g * c * g⁻¹,
      Subgroup.mem_subgroupOf.mpr (hLconj _ g.2 hgB _ (Subgroup.mem_subgroupOf.mp hc')), ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hyN : yb ∈ Subgroup.normalizer ((bar M Q (LB M Q B) : Subgroup (Mbar M Q)) : Set _) := by
    refine Subgroup.mem_normalizer_iff.mpr fun c => ⟨hLnorm ⟨y, hyM⟩ hyB c, fun h => ?_⟩
    have h1 := hLnorm ⟨y, hyM⟩⁻¹ (Subgroup.inv_mem _ hyB) _ h
    rw [map_inv, inv_inv, ← hyb] at h1
    have e : yb⁻¹ * (yb * c * yb⁻¹) * yb = c := by group
    rwa [e] at h1
  have hLfix : ∀ c ∈ bar M Q (LB M Q B), yb * c * yb⁻¹ = c → c = 1 := by
    rintro _ ⟨c, hc', rfl⟩ h
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) (⟨y, hyM⟩ * c * (⟨y, hyM⟩ : ↥M)⁻¹ * c⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hyb, h, mul_inv_cancel]
    have h2 : y * (c : G) * y⁻¹ * (c : G)⁻¹ ∈ Q :=
      Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
    have h3 : (c : G) ∈ Q := hc.mem_Q_of_torus_comm_mem h12.width h12.n_gt h12.noA2 hyX hyM hyZ
      hyB hreg1 (Subgroup.mem_subgroupOf.mp hc') h2
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr h3)
  have hLH : bar M Q (LB M Q B) ≤ H := Subgroup.map_mono fun x hx => hc.LB_le_H0' hx
  intro l hl
  obtain ⟨w, -, hlw⟩ := CFSG.Holt.H78.L17.exists_eq_commutator_of_fixedPointFree hyN hLfix hl
  set c : Mbar M Q := w⁻¹ with hcw
  have hlc : l = ⁅c, yb⁆ := by
    rw [hlw, hcw, commutatorElement_def, inv_inv]
  subst hlc
  obtain ⟨k, hk⟩ := hc.isPGroup_bar_LB ⟨⁅c, yb⁆, hl⟩
  have hk' : ⁅c, yb⁆ ^ 2 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨x, hxX, hx⟩ := exists_conj_eq_of_odd_outer_commutator hodd hk'
  have hxH : x ∈ H := by
    obtain ⟨x', -, rfl⟩ := Subgroup.mem_map.mp hxX
    exact x'.2
  have heH : x⁻¹ * ⁅c, yb⁆ ∈ H := H.mul_mem (H.inv_mem hxH) (hLH hl)
  have hcent : ∀ w ∈ X, (x⁻¹ * ⁅c, yb⁆) * w = w * (x⁻¹ * ⁅c, yb⁆) := by
    intro w hw
    have h1 := hx w hw
    calc (x⁻¹ * ⁅c, yb⁆) * w = x⁻¹ * (⁅c, yb⁆ * w * ⁅c, yb⁆⁻¹) * ⁅c, yb⁆ := by group
      _ = x⁻¹ * (x * w * x⁻¹) * ⁅c, yb⁆ := by rw [h1]
      _ = w * (x⁻¹ * ⁅c, yb⁆) := by group
  have hFe : (⟨x⁻¹ * ⁅c, yb⁆, heH⟩ : ↥H) ∈ generalizedFitting ↥H := by
    refine CFSG.centralizer_generalizedFitting_le ↥H ?_
    refine Subgroup.mem_centralizer_iff.mpr fun f hf => ?_
    exact Subtype.ext (hcent _ ⟨f, hf, rfl⟩).symm
  have hz : (⟨⟨x⁻¹ * ⁅c, yb⁆, heH⟩, hFe⟩ : ↥(generalizedFitting ↥H)) ∈
      Subgroup.center ↥(generalizedFitting ↥H) := by
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    exact Subtype.ext (Subtype.ext (hcent _ ⟨g.1, g.2, rfl⟩).symm)
  rw [hFc, Subgroup.mem_bot] at hz
  have he1 : x⁻¹ * ⁅c, yb⁆ = 1 :=
    congrArg (fun z : ↥(generalizedFitting ↥H) => ((z : ↥H) : Mbar M Q)) hz
  rw [← inv_mul_eq_one.mp he1]
  exact hxX

end CFSG.RankThree.GF2n.Stroth80
