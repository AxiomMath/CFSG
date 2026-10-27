module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4RABranchDefs
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RALabels
public import CFSG.LocalAnalysis.StandardType.GGTCJDivUni
public import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaUniComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniScal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot

public section

namespace CFSG.StandardType.GGInnerD4RAParts

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA

theorem raUnitaryBranch_holds : RAUnitaryBranch := by
  intro R _ _ lab β Jb hcen hlam htag hβ3 hin hJb
  have hFam : Y10GField.FamUni lab := Or.inl htag
  obtain ⟨K, hKf, hKfin, d, τ, hτ, hτq, hcard, hd3, hd3n, A, u, e, hA, hαu, hgraph⟩ :=
    Y10GInnUni.innDiag_unitary_data hcen hFam hin
  letI : Field K := hKf
  letI : Finite K := hKfin
  have h2 : (2 : K) = 0 := Y10GInnUni.two_eq_zero_of_card hcard
  have hMEq : MulAut.congr e β = u := by
    ext r
    have h1 := hαu (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hpow : u ^ 3 = 1 := by
    rw [← hMEq, ← map_pow, hβ3, map_one]
  have hJ' : CFSG.Assembly.IsComponentOf (Jb.map e.toMonoidHom)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup u) := by
    have h := TCJ.tcjLin_component_transport e β hJb
    rwa [hMEq] at h
  have hdQ : (d, 2 ^ lab.n) ≠ (3, 2) := by
    intro h
    obtain ⟨hd, hQ⟩ := Prod.mk.inj h
    have h2n : 2 ≤ lab.n := hd3n hd
    have hle : 2 ^ 2 ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) h2n
    omega
  haveI hsimple : IsSimpleGroup (↥Jb ⧸ Subgroup.center ↥Jb) := hJb.2.2.2
  rcases TCJ.tcjUni_component_psu_fixed Y10GInnUni.uniScalar_holds hτ hτq hcard h2 hd3 hdQ
      A hA Nat.prime_three (by norm_num) u hgraph hpow (Jb.map e.toMonoidHom) hJ' with
    ⟨a, dd, E, hE, hEf, τ', hτ', ha2, hτ'Q, hcardE, ⟨φ⟩⟩ |
    ⟨b, ee, E, hE, hEf, hb2, hcardE, ⟨φ⟩⟩
  ·
    letI : Field E := hE
    letI : Finite E := hEf
    have hτ'm : ∀ x : E, τ' x = x ^ 2 ^ (lab.n * dd) := by
      intro x
      rw [pow_mul]
      exact hτ'Q x
    have hcardm : Nat.card E = (2 ^ (lab.n * dd)) ^ 2 := by
      rw [pow_mul]
      exact hcardE
    obtain ⟨ψ⟩ := Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv
      (Subgroup.equivMapOfInjective Jb e.toMonoidHom e.injective)
    obtain ⟨labC, htagC, hlamC, hlabC⟩ :=
      S2MathAs51600RALabels.admissible_label_of_heldSU_quot (Q := ↥Jb ⧸ Subgroup.center ↥Jb)
        (a := a) (m := lab.n * dd) (E := E) τ' hτ' ha2 hτ'm hcardm (ψ.trans φ)
    exact ⟨labC, hlamC, htagC, hlabC⟩
  ·
    letI : Field E := hE
    letI : Finite E := hEf
    have hcardm : Nat.card E = 2 ^ (lab.n * (2 * ee)) := by
      rw [pow_mul]
      exact hcardE
    obtain ⟨ψ⟩ := Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv
      (Subgroup.equivMapOfInjective Jb e.toMonoidHom e.injective)
    obtain ⟨hlamC, hlabC⟩ :=
      S2MathAs51600RALabels.admissible_typeA_of_psl (Q := ↥Jb ⧸ Subgroup.center ↥Jb)
        (a := b) (m := lab.n * (2 * ee)) (E := E) hb2 hcardm (ψ.trans φ)
    exact ⟨⟨.A, b - 1, lab.n * (2 * ee)⟩, hlamC, Or.inl rfl, hlabC⟩

theorem exists_unitary_component_label_of_dvd_add_one
    {R : Type} [Group R] [Finite R] {lab : LargeEvenLabel} {β : MulAut R}
    {Jb : Subgroup R} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcen : Subgroup.center R = ⊥) (htag : lab.tag = .twA)
    (hβp : β ^ p = 1) (hpq : p ∣ 2 ^ lab.n + 1) (hin : Y10GField.InnDiagKind R lab β)
    (hJb : CFSG.Assembly.IsComponentOf Jb (ggAutFixedSubgroup β)) :
    ∃ (dd : ℕ) (labC : LargeEvenLabel), dd ∣ p ∧ labC.n = lab.n * dd ∧
      LargeEvenInLambda2 labC ∧ (labC.tag = .A ∧ labC.rank = 1 ∨ labC.tag = .twA) ∧
      GGHasLabel labC (↥Jb ⧸ Subgroup.center ↥Jb) := by
  obtain ⟨K, hKf, hKfin, d, τ, hτ, hτq, hcard, hd3, hd3n, A, u, e, hA, hαu, hgraph⟩ :=
    Y10GInnUni.innDiag_unitary_data hcen (Or.inl htag) hin
  letI : Field K := hKf
  let : Finite K := hKfin
  have hMEq : MulAut.congr e β = u := by
    ext r
    have h1 := hαu (e.symm r)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1
  have hpow : u ^ p = 1 := by
    rw [← hMEq, ← map_pow, hβp, map_one]
  have hJ' : CFSG.Assembly.IsComponentOf (Jb.map e.toMonoidHom)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup u) := by
    have h := TCJ.tcjLin_component_transport e β hJb
    rwa [hMEq] at h
  have hdQ : (d, 2 ^ lab.n) ≠ (3, 2) := by
    intro h
    obtain ⟨hd, hQ⟩ := Prod.mk.inj h
    have h2n : 2 ≤ lab.n := hd3n hd
    have hle : 2 ^ 2 ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) h2n
    omega
  obtain ⟨a, dd, E, hE, hEf, τ', hτ', ha, hdd, hτ'Q, hcardE, ⟨φ⟩⟩ :=
    TCJ.tcjUniEnnola_component_psu_fixed Y10GInnUni.uniScalar_holds hτ hτq hcard
      ⟨lab.n, rfl⟩ hd3 hdQ A hA hp hp2 hpq u hgraph hpow (Jb.map e.toMonoidHom) hJ'
  letI : Field E := hE
  let : Finite E := hEf
  have hτ'm : ∀ x : E, τ' x = x ^ 2 ^ (lab.n * dd) := by
    intro x
    rw [pow_mul]
    exact hτ'Q x
  have hcardm : Nat.card E = (2 ^ (lab.n * dd)) ^ 2 := by
    rw [pow_mul]
    exact hcardE
  obtain ⟨ψ⟩ := Y10GCenterQuot.nonempty_centerQuot_of_mulEquiv
    (Subgroup.equivMapOfInjective Jb e.toMonoidHom e.injective)
  have : IsSimpleGroup (↥Jb ⧸ Subgroup.center ↥Jb) := hJb.2.2.2
  rcases S2MathAs51600RALabels.admissible_label_of_heldSU_quot_exact
      τ' hτ' ha hτ'm hcardm (ψ.trans φ) with ⟨rfl, hC, hΛC⟩ | ⟨ha3, hC, hΛC⟩
  · exact ⟨dd, ⟨.A, 1, lab.n * dd⟩, hdd, rfl, hΛC, Or.inl ⟨rfl, rfl⟩, hC⟩
  · exact ⟨dd, ⟨.twA, a - 1, lab.n * dd⟩, hdd, rfl, hΛC, Or.inr rfl, hC⟩

end CFSG.StandardType.GGInnerD4RAParts

end
