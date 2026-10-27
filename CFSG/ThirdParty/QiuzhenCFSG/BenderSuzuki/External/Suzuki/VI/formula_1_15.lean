module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Suzuki.VI.formula_1_7
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Divisibility

namespace CFSG
end CFSG
open CFSG

/-!
# Suzuki VI.(1.15)

The conjugacy-class multiplication coefficient formula.
-/

noncomputable section

open scoped BigOperators

namespace CFSG.BenderSuzuki
namespace External
namespace Suzuki
namespace VI

universe u v

private def conjugateCarrierEquiv
    {G : Type u} [Group G] (C : ConjClasses G) (c : G) :
    C.carrier ≃ C.carrier where
  toFun x := ⟨c * x.1 * c⁻¹, by
    apply ConjClasses.mem_carrier_iff_mk_eq.mpr
    exact ((ConjClasses.mk_eq_mk_iff_isConj.mpr
      (isConj_iff.mpr ⟨c, rfl⟩)).symm).trans
        (ConjClasses.mem_carrier_iff_mk_eq.mp x.2)⟩
  invFun x := ⟨c⁻¹ * x.1 * (c⁻¹)⁻¹, by
    apply ConjClasses.mem_carrier_iff_mk_eq.mpr
    exact ((ConjClasses.mk_eq_mk_iff_isConj.mpr
      (isConj_iff.mpr ⟨c⁻¹, rfl⟩)).symm).trans
        (ConjClasses.mem_carrier_iff_mk_eq.mp x.2)⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]

private theorem pairCount_eq_of_isConj
    {G : Type u} [Group G] [Finite G]
    (Ci Cj : ConjClasses G) {x y : G} (hxy : IsConj x y) :
    Nat.card {p : Ci.carrier × Cj.carrier // p.1.1 * p.2.1 = x} =
      Nat.card {p : Ci.carrier × Cj.carrier // p.1.1 * p.2.1 = y} := by
  rcases isConj_iff.mp hxy with ⟨c, hc⟩
  let ei := conjugateCarrierEquiv Ci c
  let ej := conjugateCarrierEquiv Cj c
  apply Nat.card_congr
  exact {
    toFun := fun p => ⟨(ei p.1.1, ej p.1.2), by
      dsimp [ei, ej, conjugateCarrierEquiv]
      have hprod :
          c * p.1.1.1 * c⁻¹ * (c * p.1.2.1 * c⁻¹) = c * x * c⁻¹ := by
        simpa [mul_assoc] using congrArg (fun z : G => c * z * c⁻¹) p.2
      exact hprod.trans hc⟩
    invFun := fun p => ⟨(ei.symm p.1.1, ej.symm p.1.2), by
      dsimp [ei, ej, conjugateCarrierEquiv]
      simpa [mul_assoc] using
        congrArg (fun z : G => c⁻¹ * z * (c⁻¹)⁻¹) (p.2.trans hc.symm)⟩
    left_inv := by
      intro p
      apply Subtype.ext
      apply Prod.ext <;> simp [ei, ej]
    right_inv := by
      intro p
      apply Subtype.ext
      apply Prod.ext <;> simp [ei, ej] }

private noncomputable def stabilizerCommuterEquiv
    {G : Type u} [Group G] (g : G) :
    MulAction.stabilizer (ConjAct G) g ≃ {x : G // x * g = g * x} where
  toFun x := ⟨ConjAct.ofConjAct x.1, by
    have hx : x.1 • g = g := x.2
    rw [ConjAct.smul_def] at hx
    exact mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hx)⟩
  invFun x := ⟨ConjAct.toConjAct x.1, by
    change ConjAct.toConjAct x.1 • g = g
    rw [ConjAct.toConjAct_smul]
    exact mul_inv_eq_of_eq_mul x.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

private theorem classCard_mul_commuterCard_eq_groupCard
    {G : Type u} [Group G] [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier *
        Nat.card {x : G // x * g = g * x} = Nat.card G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have hst := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g
  have hst' : Fintype.card (ConjClasses.mk g).carrier *
      Fintype.card (MulAction.stabilizer (ConjAct G) g) = Fintype.card G := by
    simpa [ConjAct.orbit_eq_carrier_conjClasses] using hst
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [Fintype.card_congr (stabilizerCommuterEquiv g)] at hst'
  exact hst'

/-- Suzuki, *Group Theory II*, Chapter 6, formula (1.15). -/
public theorem suzuki_ch6_formula_1_15
    {G : Type u} [Group G] [Finite G]
    {ι : Type v} [Fintype ι]
    (chi : ι → Theory.Character.ConjClassFunction G)
    (hchi : Theory.Character.IsCompleteIrreducibleCharacterFamily chi)
    (Ci Cj Ck : ConjClasses G) (xk : G) (hxk : xk ∈ Ck.carrier) :
    (Nat.card {p : Ci.carrier × Cj.carrier // p.1.1 * p.2.1 = xk} : ℂ) =
      ((Nat.card Ci.carrier : ℂ) * (Nat.card Cj.carrier : ℂ) /
          (Nat.card G : ℂ)) *
        ∑ mu : ι,
          chi mu Ci * chi mu Cj * star (chi mu Ck) /
            chi mu (ConjClasses.mk (1 : G)) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (ConjClasses G) := Fintype.ofFinite (ConjClasses G)
  let a : ConjClasses G → ConjClasses G → ConjClasses G → ℕ :=
    fun i j s => Nat.card {p : i.carrier × j.carrier //
      p.1.1 * p.2.1 = Quotient.out s}
  have hdata : ∀ i j s : ConjClasses G, ∀ x : G, x ∈ s.carrier →
      a i j s =
        Nat.card {p : i.carrier × j.carrier // p.1.1 * p.2.1 = x} := by
    intro i j s x hx
    apply pairCount_eq_of_isConj
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    exact (Quotient.out_eq s).trans
      (ConjClasses.mem_carrier_iff_mk_eq.mp hx).symm
  let n : ι → ℕ := fun mu => Classical.choose (hchi.1 mu).1
  let rho : (mu : ι) → Representation ℂ G (Fin (n mu) → ℂ) := fun mu =>
    Classical.choose (Classical.choose_spec (hchi.1 mu).1)
  have hchar (mu : ι) :
      chi mu = Theory.Character.characterClassFunction (rho mu) :=
    Classical.choose_spec (Classical.choose_spec (hchi.1 mu).1)
  have hirr (mu : ι) : Representation.IsIrreducible (rho mu) := by
    apply (Theory.Character.irreducible_iff_character_norm_one (ρ := rho mu)).2
    simpa [hchar mu] using (hchi.1 mu).2
  have hchar_out (mu : ι) (C : ConjClasses G) :
      chi mu C = (rho mu).character (Quotient.out C) := by
    calc
      chi mu C = chi mu (ConjClasses.mk (Quotient.out C)) :=
        congrArg (chi mu) (Quotient.out_eq C).symm
      _ = Theory.Character.characterClassFunction (rho mu)
          (ConjClasses.mk (Quotient.out C)) := congrFun (hchar mu) _
      _ = (rho mu).character (Quotient.out C) := rfl
  have hchar_one (mu : ι) :
      chi mu (ConjClasses.mk (1 : G)) = (rho mu).character 1 := by
    rw [hchar mu]
    rfl
  have homega (mu : ι) (C : ConjClasses G) :
      Theory.Character.classSumScalar (ρ := rho mu) C =
        (Nat.card C.carrier : ℂ) * chi mu C /
          chi mu (ConjClasses.mk (1 : G)) := by
    letI : Representation.IsIrreducible (rho mu) := hirr mu
    have h := Theory.Character.classSumScalar_eq_card_mul_character_div
      (ρ := rho mu) C
      (ConjClasses.mem_carrier_iff_mk_eq.mpr (Quotient.out_eq C))
    rw [hchar_out mu C, hchar_one mu]
    exact h
  have hdegree_ne (mu : ι) :
      chi mu (ConjClasses.mk (1 : G)) ≠ 0 := by
    rw [hchar_one mu]
    have hpos : 0 < Module.finrank ℂ (Fin (n mu) → ℂ) := by
      letI : Representation.IsIrreducible (rho mu) := hirr mu
      exact (Module.finrank_pos_iff (R := ℂ) (M := Fin (n mu) → ℂ)).2
        (Theory.Character.irreducible_nontrivial (ρ := rho mu))
    simpa [Representation.character] using
      (show (Module.finrank ℂ (Fin (n mu) → ℂ) : ℂ) ≠ 0 by
        exact_mod_cast hpos.ne')
  have hweighted (mu : ι) :
      (Nat.card Ci.carrier : ℂ) * (Nat.card Cj.carrier : ℂ) *
          (chi mu Ci * chi mu Cj * star (chi mu Ck) /
            chi mu (ConjClasses.mk (1 : G))) =
        ∑ s : ConjClasses G,
          (a Ci Cj s : ℂ) * (Nat.card s.carrier : ℂ) *
            chi mu s * star (chi mu Ck) := by
    letI : Representation.IsIrreducible (rho mu) := hirr mu
    have hs := Theory.Character.classSumScalar_mul_eq_sum_of_coefficients
      (ρ := rho mu) a hdata Ci Cj
    have hd := hdegree_ne mu
    calc
      (Nat.card Ci.carrier : ℂ) * (Nat.card Cj.carrier : ℂ) *
          (chi mu Ci * chi mu Cj * star (chi mu Ck) /
            chi mu (ConjClasses.mk (1 : G))) =
        (Theory.Character.classSumScalar (ρ := rho mu) Ci *
          Theory.Character.classSumScalar (ρ := rho mu) Cj) *
            chi mu (ConjClasses.mk (1 : G)) * star (chi mu Ck) := by
              rw [homega mu Ci, homega mu Cj]
              field_simp [hd]
      _ = (∑ s : ConjClasses G,
          (a Ci Cj s : ℂ) * Theory.Character.classSumScalar (ρ := rho mu) s) *
            chi mu (ConjClasses.mk (1 : G)) * star (chi mu Ck) := by
              rw [hs]
      _ = ∑ s : ConjClasses G,
          (a Ci Cj s : ℂ) * (Nat.card s.carrier : ℂ) *
            chi mu s * star (chi mu Ck) := by
              rw [Finset.sum_mul, Finset.sum_mul]
              refine Finset.sum_congr rfl ?_
              intro s _
              rw [homega mu s]
              field_simp [hd]
  have hxk_mk : ConjClasses.mk xk = Ck :=
    ConjClasses.mem_carrier_iff_mk_eq.mp hxk
  have hinv (mu : ι) :
      chi mu (ConjClasses.mk xk⁻¹) = star (chi mu Ck) := by
    rw [← hxk_mk, hchar mu]
    change (rho mu).character xk⁻¹ = star ((rho mu).character xk)
    exact Theory.Representation.representation_character_inv_eq_star_character (rho mu) xk
  have horth (s : ConjClasses G) :
      (∑ mu : ι, chi mu s * star (chi mu Ck)) =
        if s = Ck then (Nat.card {z : G // z * xk = xk * z} : ℂ) else 0 := by
    by_cases hs : s = Ck
    · subst s
      rw [if_pos rfl]
      have h := (suzuki_ch6_formula_1_7 chi hchi).2 xk xk |>.1 rfl
      simp_rw [hinv] at h
      simpa [hxk_mk] using h
    · rw [if_neg hs]
      have hout : ConjClasses.mk (Quotient.out s) = s := Quotient.out_eq s
      have hne : ConjClasses.mk (Quotient.out s) ≠ ConjClasses.mk xk := by
        intro h
        exact hs (hout.symm.trans (h.trans hxk_mk))
      have h := (suzuki_ch6_formula_1_7 chi hchi).2 (Quotient.out s) xk |>.2 hne
      simp_rw [hinv] at h
      simpa only [hout] using h
  have hsum :
      (Nat.card Ci.carrier : ℂ) * (Nat.card Cj.carrier : ℂ) *
          (∑ mu : ι, chi mu Ci * chi mu Cj * star (chi mu Ck) /
            chi mu (ConjClasses.mk (1 : G))) =
        ∑ s : ConjClasses G,
          (a Ci Cj s : ℂ) * (Nat.card s.carrier : ℂ) *
            (∑ mu : ι, chi mu s * star (chi mu Ck)) := by
    calc
      (Nat.card Ci.carrier : ℂ) * (Nat.card Cj.carrier : ℂ) *
          (∑ mu : ι, chi mu Ci * chi mu Cj * star (chi mu Ck) /
            chi mu (ConjClasses.mk (1 : G))) =
        ∑ mu : ι,
          (Nat.card Ci.carrier : ℂ) * (Nat.card Cj.carrier : ℂ) *
            (chi mu Ci * chi mu Cj * star (chi mu Ck) /
              chi mu (ConjClasses.mk (1 : G))) := by
                rw [Finset.mul_sum]
      _ = ∑ mu : ι, ∑ s : ConjClasses G,
          (a Ci Cj s : ℂ) * (Nat.card s.carrier : ℂ) *
            chi mu s * star (chi mu Ck) := by
              refine Finset.sum_congr rfl ?_
              intro mu _
              exact hweighted mu
      _ = ∑ s : ConjClasses G, ∑ mu : ι,
          (a Ci Cj s : ℂ) * (Nat.card s.carrier : ℂ) *
            chi mu s * star (chi mu Ck) := Finset.sum_comm
      _ = ∑ s : ConjClasses G,
          (a Ci Cj s : ℂ) * (Nat.card s.carrier : ℂ) *
            (∑ mu : ι, chi mu s * star (chi mu Ck)) := by
              refine Finset.sum_congr rfl ?_
              intro s _
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro mu _
              ring
  have hcollapse :
      (∑ s : ConjClasses G,
          (a Ci Cj s : ℂ) * (Nat.card s.carrier : ℂ) *
            (∑ mu : ι, chi mu s * star (chi mu Ck))) =
        (a Ci Cj Ck : ℂ) * (Nat.card Ck.carrier : ℂ) *
          (Nat.card {z : G // z * xk = xk * z} : ℂ) := by
    simp_rw [horth]
    simp
  have hclassCard :
      Nat.card Ck.carrier * Nat.card {z : G // z * xk = xk * z} = Nat.card G := by
    simpa [hxk_mk] using classCard_mul_commuterCard_eq_groupCard xk
  have hclassCard_cast :
      (Nat.card Ck.carrier : ℂ) *
          (Nat.card {z : G // z * xk = xk * z} : ℂ) = (Nat.card G : ℂ) := by
    exact_mod_cast hclassCard
  have hsum_final :
      (Nat.card Ci.carrier : ℂ) * (Nat.card Cj.carrier : ℂ) *
          (∑ mu : ι, chi mu Ci * chi mu Cj * star (chi mu Ck) /
            chi mu (ConjClasses.mk (1 : G))) =
        (Nat.card {p : Ci.carrier × Cj.carrier // p.1.1 * p.2.1 = xk} : ℂ) *
          (Nat.card G : ℂ) := by
    calc
      _ = ∑ s : ConjClasses G,
          (a Ci Cj s : ℂ) * (Nat.card s.carrier : ℂ) *
            (∑ mu : ι, chi mu s * star (chi mu Ck)) := hsum
      _ = (a Ci Cj Ck : ℂ) * (Nat.card Ck.carrier : ℂ) *
          (Nat.card {z : G // z * xk = xk * z} : ℂ) := hcollapse
      _ = (Nat.card {p : Ci.carrier × Cj.carrier // p.1.1 * p.2.1 = xk} : ℂ) *
          (Nat.card G : ℂ) := by
            rw [mul_assoc, hdata Ci Cj Ck xk hxk, hclassCard_cast]
  have hG : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  rw [div_mul_eq_mul_div, eq_div_iff hG]
  exact hsum_final.symm

end VI
end Suzuki
end External
end CFSG.BenderSuzuki
