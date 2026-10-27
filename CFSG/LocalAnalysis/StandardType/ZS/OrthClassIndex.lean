module

public import CFSG.LocalAnalysis.StandardType.ZS.ClassReflClosure
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOrthogonalAbelianization
import CFSG.LocalAnalysis.StandardType.ZS.OrthReflect
import CFSG.LieType.Universal.SpinOmega.Reflections
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasThree
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open CFSG.ClassicalGroups.Orthogonal

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem inv_mul_mem_closure_classRefl [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (h5 : 5 ≤ Module.finrank (ZMod p) U) {Q : QuadraticForm (ZMod p) U}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {c : ZMod p} (hc : c ≠ 0)
    {g g' : U ≃ₗ[ZMod p] U} (hg : IsIsom p Q g) (hg' : IsIsom p Q g')
    (hgc : g ∉ Subgroup.closure (ClassRefl p Q c))
    (hgc' : g' ∉ Subgroup.closure (ClassRefl p Q c)) :
    g⁻¹ * g' ∈ Subgroup.closure (ClassRefl p Q c) := by
  classical
  let R : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure (ClassRefl p Q c)
  change g⁻¹ * g' ∈ R
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hRiso : ∀ x ∈ R, IsIsom p Q x := fun x hx =>
    isIsom_of_mem_closure_classRefl hx
  have hstep1 : ∀ {a : U} {μ : ZMod p}, μ ≠ 0 → Q a = c * μ ^ 2 →
      reflect Q a ∈ R := by
    intro a μ hμ hQa
    have hQb : Q (μ⁻¹ • a) = c := by
      rw [map_smul_eq_sq, hQa]
      field_simp [hμ]
    have hmem : reflect Q (μ⁻¹ • a) ∈ ClassRefl p Q c :=
      (mem_classRefl_iff hp hQ hc _).mpr ⟨μ⁻¹ • a, hQb, rfl⟩
    have hsub : reflect Q (μ⁻¹ • a) ∈ R := Subgroup.subset_closure hmem
    rwa [CFSG.LieType.Universal.Spin.reflect_smul_of_ne_zero (inv_ne_zero hμ) a] at hsub
  have hstep2 : ∀ {a b : U}, reflect Q a ∉ R → reflect Q b ∉ R →
      reflect Q a * reflect Q b ∈ R := by
    intro a b ha hb
    have hQa : Q a ≠ 0 := by
      intro h0
      exact ha (by rw [reflect_of_map_eq_zero h0]; exact Subgroup.one_mem _)
    have hQb : Q b ≠ 0 := by
      intro h0
      exact hb (by rw [reflect_of_map_eq_zero h0]; exact Subgroup.one_mem _)
    have hnsa : ¬ IsSquare (Q a / c) := by
      rintro ⟨μ, hμ⟩
      have hμ0 : μ ≠ 0 := by
        intro h0
        exact (div_ne_zero hQa hc) (by rw [hμ, h0, mul_zero])
      have hQa' : Q a = c * μ ^ 2 := by
        rw [← div_mul_cancel₀ (Q a) hc, hμ]
        ring
      exact ha (hstep1 hμ0 hQa')
    have hnsb : ¬ IsSquare (Q b / c) := by
      rintro ⟨μ, hμ⟩
      have hμ0 : μ ≠ 0 := by
        intro h0
        exact (div_ne_zero hQb hc) (by rw [hμ, h0, mul_zero])
      have hQb' : Q b = c * μ ^ 2 := by
        rw [← div_mul_cancel₀ (Q b) hc, hμ]
        ring
      exact hb (hstep1 hμ0 hQb')
    have hprod : IsSquare ((Q a / c) * (Q b / c)) :=
      CFSG.LocalAnalysis.ComponentInitial.isSquare_mul_of_not_isSquare
        (div_ne_zero hQa hc) (div_ne_zero hQb hc) hnsa hnsb
    have hx0 : Q a / c ≠ 0 := div_ne_zero hQa hc
    have hsq_ba : IsSquare (Q b / Q a) := by
      have h := hprod.div (IsSquare.mul_self (Q a / c))
      have he : ((Q a / c) * (Q b / c)) / ((Q a / c) * (Q a / c)) =
          Q b / Q a := by
        field_simp [hx0]
      rwa [he] at h
    obtain ⟨μ, hμ⟩ := hsq_ba
    have hμ0 : μ ≠ 0 := by
      intro h0
      have hzero : Q b / Q a = 0 := by rw [hμ, h0, mul_zero]
      exact (div_ne_zero hQb hQa) hzero
    have hQb_sq : Q b = (μ * μ) * Q a := by
      rw [← hμ, div_mul_cancel₀ (Q b) hQa]
    have hnorm : Q a = Q (μ⁻¹ • b) := by
      rw [map_smul_eq_sq, hQb_sq]
      field_simp [hμ0]
    have hrefl : reflect Q (μ⁻¹ • b) = reflect Q b :=
      CFSG.LieType.Universal.Spin.reflect_smul_of_ne_zero (inv_ne_zero hμ0) b
    have hmain := reflect_mul_reflect_mem_closure_classRefl hp h5 hQ hc hnorm
    rwa [hrefl] at hmain
  have hOgen : TauCeti.QuadraticMap.orthogonalGroup Q ≤
      Subgroup.closure (Set.range (reflect Q)) :=
    orthogonalGroup_le_closure_reflect h2 hQ
  have hgcl : g ∈ Subgroup.closure (Set.range (reflect Q)) :=
    hOgen (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hg)
  have hg'cl : g' ∈ Subgroup.closure (Set.range (reflect Q)) :=
    hOgen (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hg')
  have hex : ∃ b₀ : U, reflect Q b₀ ∉ R := by
    by_contra h
    have hall : ∀ b : U, reflect Q b ∈ R := fun b =>
      not_not.mp (not_exists.mp h b)
    exact hgc ((Subgroup.closure_le R).mpr (fun x hx => by
      obtain ⟨a, rfl⟩ := hx
      exact hall a) hgcl)
  obtain ⟨b₀, hb₀⟩ := hex
  let r₀ : U ≃ₗ[ZMod p] U := reflect Q b₀
  have hr₀_not : r₀ ∉ R := hb₀
  have hr₀_iso : IsIsom p Q r₀ := isIsom_reflect Q b₀
  have hr₀_sq : r₀ * r₀ = 1 := reflect_mul_self Q b₀
  have hr₀_inv : r₀⁻¹ = r₀ := reflect_inv Q b₀
  have hnot : ∀ {u : U ≃ₗ[ZMod p] U}, IsIsom p Q u → u * r₀ * u⁻¹ ∉ R := by
    intro u hu hmem
    have hconj : u⁻¹ * (u * r₀ * u⁻¹) * (u⁻¹)⁻¹ ∈ R :=
      conj_mem_closure_classRefl (isIsom_inv hu) hmem
    have hEq : u⁻¹ * (u * r₀ * u⁻¹) * (u⁻¹)⁻¹ = r₀ := by group
    rw [hEq] at hconj
    exact hr₀_not hconj
  have hkey : ∀ y ∈ Subgroup.closure (Set.range (reflect Q)), y ∈ R ∨ r₀ * y ∈ R := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨a, rfl⟩ := hs
      by_cases hsR : reflect Q a ∈ R
      · exact Or.inl hsR
      · exact Or.inr (by simpa [r₀] using hstep2 hb₀ hsR)
    | one => exact Or.inl (Subgroup.one_mem R)
    | mul a b ha hb iha ihb =>
      rcases iha with haR | haR <;> rcases ihb with hbR | hbR
      · exact Or.inl (R.mul_mem haR hbR)
      · refine Or.inr ?_
        have hconjR : r₀ * a * r₀⁻¹ ∈ R :=
          conj_mem_closure_classRefl hr₀_iso haR
        have heq : r₀ * (a * b) = (r₀ * a * r₀⁻¹) * (r₀ * b) := by group
        rw [heq]
        exact R.mul_mem hconjR hbR
      · refine Or.inr ?_
        have heq : r₀ * (a * b) = (r₀ * a) * b := by group
        rw [heq]
        exact R.mul_mem haR hbR
      · refine Or.inl ?_
        have hxiso : IsIsom p Q (r₀ * a) := hRiso _ haR
        have hxconj : (r₀ * a) * r₀ * (r₀ * a)⁻¹ ∉ R := hnot hxiso
        have hxconj_eq : (r₀ * a) * r₀ * (r₀ * a)⁻¹ =
            reflect Q ((r₀ * a) b₀) := by
          simpa [r₀] using reflect_conj
            (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hxiso) b₀
        have hxconj' : reflect Q ((r₀ * a) b₀) ∉ R := hxconj_eq ▸ hxconj
        have hxconjR : r₀ * ((r₀ * a) * r₀ * (r₀ * a)⁻¹) ∈ R := by
          rw [hxconj_eq]
          simpa [r₀] using hstep2 hb₀ hxconj'
        have hxyR : (r₀ * a) * (r₀ * b) ∈ R := R.mul_mem haR hbR
        have hab : a * b =
            (r₀ * ((r₀ * a) * r₀ * (r₀ * a)⁻¹)) *
              ((r₀ * a) * (r₀ * b)) := by
          have ha' : a = r₀ * (r₀ * a) := by rw [← mul_assoc, hr₀_sq, one_mul]
          have hb' : b = r₀ * (r₀ * b) := by rw [← mul_assoc, hr₀_sq, one_mul]
          conv_lhs => rw [ha', hb']
          group
        rw [hab]
        exact R.mul_mem hxconjR hxyR
    | inv a ha iha =>
      rcases iha with haR | haR
      · exact Or.inl (R.inv_mem haR)
      · refine Or.inr ?_
        have hconjR : r₀ * (r₀ * a)⁻¹ * r₀⁻¹ ∈ R :=
          conj_mem_closure_classRefl hr₀_iso (R.inv_mem haR)
        have heq : r₀ * (r₀ * a)⁻¹ * r₀⁻¹ = r₀ * a⁻¹ := by
          rw [mul_inv_rev, hr₀_inv]
          calc r₀ * (a⁻¹ * r₀) * r₀ = (r₀ * a⁻¹) * (r₀ * r₀) := by group
            _ = r₀ * a⁻¹ := by rw [hr₀_sq, mul_one]
        rwa [heq] at hconjR
  have hgR : r₀ * g ∈ R := by
    rcases hkey g hgcl with h | h
    · exact absurd h hgc
    · exact h
  have hg'R : r₀ * g' ∈ R := by
    rcases hkey g' hg'cl with h | h
    · exact absurd h hgc'
    · exact h
  have hcalc : (r₀ * g)⁻¹ * (r₀ * g') = g⁻¹ * g' := by
    rw [mul_inv_rev]
    group
  rw [← hcalc]
  exact R.mul_mem (R.inv_mem hgR) hg'R

end CFSG.StandardType.ZS

end
