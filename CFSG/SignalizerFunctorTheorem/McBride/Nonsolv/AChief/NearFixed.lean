module

public import CFSG.SignalizerFunctorTheorem.NearModels.Main
public import CFSG.SignalizerFunctorTheorem.Inheritance.TransportA.NearPSolvable
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.UnitaryOuterSmall

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief

open CFSG.SignalizerFunctorTheorem.NearModels

theorem nontrivial_psl2 (R : Type*) [CommRing R] [Nontrivial R] :
    Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin 2) R) := by
  by_contra hcon
  rw [not_nontrivial_iff_subsingleton] at hcon
  let a : Matrix.SpecialLinearGroup (Fin 2) R :=
    ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let b : Matrix.SpecialLinearGroup (Fin 2) R :=
    ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have ha : a ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) R) := by
    have h1 : ((a : Matrix.SpecialLinearGroup (Fin 2) R) :
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) R) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff a).mp h1
  have hab := congrArg
    (fun z : Matrix.SpecialLinearGroup (Fin 2) R => (z : Matrix (Fin 2) (Fin 2) R) 0 0)
    (Subgroup.mem_center_iff.mp ha b)
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at hab
  simp [a, b] at hab

theorem nontrivial_sz_zero : Nontrivial (Sz 0) := by
  obtain ⟨e⟩ := Suzuki.nonempty_mulEquiv_suzukiGroup_zero_sz
  have : Finite (Sz 0) := Finite.of_equiv _ e.toEquiv
  have h : Nat.card (Sz 0) = 20 := by
    rw [← Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order (by simp)]
    norm_num
  exact Finite.one_lt_card_iff_nontrivial.mp (by rw [h]; norm_num)

theorem nontrivial_psu3_two_one : Nontrivial (PSU3 2 1) := by
  have h72 : Nat.card (PSU3 2 1) = 72 :=
    CFSG.ProperTwoGeneratedCore.Lemma37.UnitaryOuter.card_psu3Model_one
  have : Finite (PSU3 2 1) := Nat.finite_of_card_ne_zero (by rw [h72]; norm_num)
  exact Finite.one_lt_card_iff_nontrivial.mp (by rw [h72]; norm_num)

theorem signalizerFixedSubgroup_ne_bot_of_model
    {p : ℕ} (hp : p.Prime) {X : Type*} [Group X]
    [Finite X] (hX : signalizerNearSimpleModel p X) (hcop : Nat.Coprime p (Nat.card X))
    (f : MulAut X) (hf : orderOf f = p) : signalizerFixedSubgroup f ≠ ⊥ := by
  rw [← Subgroup.nontrivial_iff_ne_bot]
  rcases hX with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, rfl, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · obtain ⟨φ⟩ := psl2_fixedSubgroup_mulEquiv 2 hp (by rwa [← Nat.card_congr e.toEquiv])
      (MulAut.congr e f) (by rw [orderOf_mulAutCongr, hf])
    have := nontrivial_psl2 (ZMod 2)
    exact ((fixedSubgroupCongr e f).trans φ).symm.injective.nontrivial
  · obtain ⟨φ⟩ := psl2_fixedSubgroup_mulEquiv 3 hp (by rwa [← Nat.card_congr e.toEquiv])
      (MulAut.congr e f) (by rw [orderOf_mulAutCongr, hf])
    have := nontrivial_psl2 (ZMod 3)
    exact ((fixedSubgroupCongr e f).trans φ).symm.injective.nontrivial
  · obtain ⟨φ⟩ := sz_fixedSubgroup_mulEquiv n hp (by rwa [← Nat.card_congr e.toEquiv])
      (MulAut.congr e f) (by rw [orderOf_mulAutCongr, hf])
    have := nontrivial_sz_zero
    exact ((fixedSubgroupCongr e f).trans φ).symm.injective.nontrivial
  · obtain ⟨φ⟩ := psu3_fixedSubgroup_mulEquiv hp (by rwa [← Nat.card_congr e.toEquiv])
      (MulAut.congr e f) (by rw [orderOf_mulAutCongr, hf])
    have := nontrivial_psu3_two_one
    exact ((fixedSubgroupCongr e f).trans φ).symm.injective.nontrivial

theorem signalizerNearSimpleModel_of_nearPSolvable {p : ℕ} {X : Type*} [Group X]
    (hsimple : IsSimpleGroup X) (hnc : ∃ a b : X, a * b ≠ b * a)
    (hnear : signalizerNearPSolvable p X) : signalizerNearSimpleModel p X := by
  let e : (⊤ : Subgroup X) ⧸ (⊥ : Subgroup X).subgroupOf ⊤ ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf (⊤ : Subgroup X))).trans
      (QuotientGroup.quotientBot.trans Subgroup.topEquiv)
  have hs : IsSimpleGroup ((⊤ : Subgroup X) ⧸ (⊥ : Subgroup X).subgroupOf ⊤) :=
    e.isSimpleGroup
  have hnonab : ∃ a b : (⊤ : Subgroup X) ⧸ (⊥ : Subgroup X).subgroupOf ⊤, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩
  exact CFSG.SignalizerFunctorTheorem.TransportA.nearSimpleModel_of_mulEquiv e
    (hnear.2 ⊤ ⊥ bot_le hs hnonab)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief
