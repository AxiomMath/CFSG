module

public import CFSG.RankThree.GF2n.Stroth80.Sec11CM
public import CFSG.ClassicalGroups.Alternating.I4SpDefs
import CFSG.ClassicalGroups.Alternating.I4SpPlaneCentralizer
import CFSG.RankThree.GF2n.Stroth80.Sec112
import CFSG.RankThree.GF2n.Stroth80.Sec118NotTLine
import CFSG.RankThree.GF2n.Stroth80.Sec34Trans

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Alternating
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable [(Q.subgroupOf M).Normal]

theorem Ctx.card_Z_le_card_of_lineElt (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    {a : ↥M} {h : (a : G) ∈ LB M Q B ∧ IsA2 Q Z (a : G)}
    {K : Type} [Field K] [Finite K] [CharP K 2] {N : Type} [AddCommGroup N] [Module K N]
    [FiniteDimensional K N] {BN : LinearMap.BilinForm K N} (hBN : BN.IsAlt)
    (hBNnd : BN.Nondegenerate) (h6 : 6 ≤ Module.finrank K N)
    (ρ : ↥(Xbar M Q Z B) →* Gsp BN) (hρ : Function.Bijective ρ)
    {a₁ c₁ : N} (hac : BN a₁ c₁ = 0) (hind : LinearIndependent K ![a₁, c₁])
    (hρa : ρ ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩ = lineElt hBN a₁ c₁) :
    Nat.card Z ≤ Nat.card K := by
  classical
  obtain ⟨y, hy⟩ := hc.exists_isLBTorus
  obtain ⟨U, hUle, hUcard, haU, hUelts, hUE⟩ := hc.exists_lbLine_subset_Ebar hy h
  set aX : ↥(Xbar M Q Z B) :=
    ⟨QuotientGroup.mk a, mk_mem_Xbar_of_LB M Q Z B a h.1 h.2⟩ with haX
  have hUX : U ≤ Xbar M Q Z B := fun u hu => by
    by_cases hu1 : u = 1
    · rw [hu1]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (hUE u hu hu1)
  have ht₀ : lineElt hBN a₁ c₁ * lineElt hBN a₁ c₁ = 1 := lineElt_mul_self hBN hac
  have hρinj : Function.Injective ρ := hρ.1
  obtain ⟨e₀, he₀, hcls⟩ := hc.ebarIsXbarClass hw hn ⟨a, h.1, h.2⟩
  have hEa : (QuotientGroup.mk a : Mbar M Q) ∈ Ebar M Q Z B := hc.mk_mem_Ebar h.1 h.2
  have hEconj : ∀ x : ↥(Xbar M Q Z B),
      ((x * aX * x⁻¹ : ↥(Xbar M Q Z B)) : Mbar M Q) ∈ Ebar M Q Z B := fun x =>
    hc.Ebar_conj hEa (x : Mbar M Q)
  have hconj : ∀ u : ↥(Xbar M Q Z B), (u : Mbar M Q) ∈ Ebar M Q Z B →
      ∃ w : ↥(Xbar M Q Z B), u = w * aX * w⁻¹ := by
    intro u hu
    obtain ⟨x₁, hx₁, hx₁'⟩ := (hcls _).1 hu
    obtain ⟨x₂, hx₂, hx₂'⟩ := (hcls _).1 hEa
    refine ⟨⟨x₁ * x₂⁻¹, Subgroup.mul_mem _ hx₁ (Subgroup.inv_mem _ hx₂)⟩, ?_⟩
    apply Subtype.ext
    show (u : Mbar M Q) = (x₁ * x₂⁻¹) * (QuotientGroup.mk a : Mbar M Q) * (x₁ * x₂⁻¹)⁻¹
    calc (u : Mbar M Q) = x₁ * e₀ * x₁⁻¹ := hx₁'
      _ = (x₁ * x₂⁻¹) * (x₂ * e₀ * x₂⁻¹) * (x₁ * x₂⁻¹)⁻¹ := by group
      _ = (x₁ * x₂⁻¹) * (QuotientGroup.mk a : Mbar M Q) * (x₁ * x₂⁻¹)⁻¹ := by rw [← hx₂']
  have hlineElt : ∀ u : ↥(Xbar M Q Z B), (u : Mbar M Q) ∈ Ebar M Q Z B →
      ∃ a' c' : N, BN a' c' = 0 ∧ LinearIndependent K ![a', c'] ∧ ρ u = lineElt hBN a' c' := by
    intro u hu
    obtain ⟨w, rfl⟩ := hconj u hu
    refine ⟨(ρ w).app a₁, (ρ w).app c₁, ?_, ?_, ?_⟩
    · rw [Gsp.form_app, hac]
    · rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 : (ρ w).lin (s • a₁ + t • c₁) = (ρ w).lin 0 := by
        rw [map_zero, map_add, map_smul, map_smul]
        exact hst
      exact hind.eq_zero_of_pair (Gsp.lin_injective (ρ w) h1)
    · rw [map_mul, map_mul, map_inv, hρa]
      exact conj_lineElt hBN (ρ w) a₁ c₁
  have hlift : ∀ a' c' : N, BN a' c' = 0 → LinearIndependent K ![a', c'] →
      ∃ x : ↥(Xbar M Q Z B), ρ (x * aX * x⁻¹) = lineElt hBN a' c' := by
    intro a' c' hac' hind'
    obtain ⟨g, hg⟩ := exists_conj_lineElt_eq hBN hBNnd hac hac' hind hind'
    obtain ⟨x, rfl⟩ := hρ.2 g
    exact ⟨x, by rw [map_mul, map_mul, map_inv, hρa]; exact hg⟩
  have hUab : ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u := fun u hu u' hu' =>
    congrArg Subtype.val (hc.isElemAbelian_bar_LB.1.is_comm.comm ⟨u, hUle hu⟩ ⟨u', hUle hu'⟩)
  have hDU : ∀ e : ↥(Xbar M Q Z B), (e : Mbar M Q) ∈ Ebar M Q Z B →
      (e : Mbar M Q) * (aX : Mbar M Q) = (aX : Mbar M Q) * (e : Mbar M Q) →
      (e : Mbar M Q) * (aX : Mbar M Q) ∈ Ebar M Q Z B →
      ∀ u ∈ U, (e : Mbar M Q) * u = u * (e : Mbar M Q) := by
    intro e he hea heaE u hu
    by_cases hu1 : u = 1
    · rw [hu1, mul_one, one_mul]
    · obtain ⟨i, m, hm, rfl⟩ := hUelts u hu hu1
      exact hc.mk_comm_of_mem_D hy h he hea heaE i m hm
  have hmem : ∀ u : ↥(Xbar M Q Z B), (u : Mbar M Q) ∈ U → ρ u ∈ lineGroup hBN a₁ c₁ := by
    intro u hu
    by_cases hu1 : u = 1
    · rw [hu1, map_one]
      exact Subgroup.one_mem _
    have hu1' : (u : Mbar M Q) ≠ 1 := fun h' => hu1 (Subtype.ext h')
    obtain ⟨a', c', hac', hind', hρu⟩ := hlineElt u (hUE _ hu hu1')
    rw [hρu]
    refine mem_lineGroup_of_commute_planeGroup hBN hBNnd h6 hac hind hac' hind' ?_
    intro π hπ hP h' hh'
    rw [← hρu]
    by_cases hh1 : h' = 1
    · rw [hh1, mul_one, one_mul]
    by_cases hht : h' = lineElt hBN a₁ c₁
    · rw [hht, ← hρa]
      have hcu : u * aX = aX * u := Subtype.ext (hUab _ hu _ haU)
      rw [← map_mul, ← map_mul, hcu]
    have ha₁π : a₁ ∈ π := hP (Submodule.subset_span (by simp))
    have hc₁π : c₁ ∈ π := hP (Submodule.subset_span (by simp))
    have ht₀π : lineElt hBN a₁ c₁ ∈ planeGroup hBN π := lineElt_mem_planeGroup hBN ha₁π hc₁π
    obtain ⟨a'', ha'', c'', hc'', hind'', hh''⟩ :=
      eq_lineElt_of_mem_planeGroup hBN hBNnd hπ hh' hh1
    obtain ⟨x, hx⟩ := hlift a'' c'' (hπ.1 a'' ha'' c'' hc'') hind''
    have hρe : ρ (x * aX * x⁻¹) = h' := by rw [hx, hh'']
    have hcomm' : h' * lineElt hBN a₁ c₁ = lineElt hBN a₁ c₁ * h' :=
      mul_comm_of_mem_planeGroup hBN hπ.1 hh' ht₀π
    have heaX : (x * aX * x⁻¹) * aX = aX * (x * aX * x⁻¹) := by
      apply hρinj
      rw [map_mul ρ (x * aX * x⁻¹) aX, map_mul ρ aX (x * aX * x⁻¹), hρe, hρa]
      exact hcomm'
    have hprod : h' * lineElt hBN a₁ c₁ ∈ planeGroup hBN π := (planeGroup hBN π).mul_mem hh' ht₀π
    have hprod1 : h' * lineElt hBN a₁ c₁ ≠ 1 := by
      intro h1
      apply hht
      rw [mul_eq_one_iff_eq_inv.mp h1, inv_eq_of_mul_eq_one_right ht₀]
    obtain ⟨a''', ha''', c''', hc''', hind''', hh'''⟩ :=
      eq_lineElt_of_mem_planeGroup hBN hBNnd hπ hprod hprod1
    obtain ⟨x', hx'⟩ := hlift a''' c''' (hπ.1 a''' ha''' c''' hc''') hind'''
    have heaXeq : (x * aX * x⁻¹) * aX = x' * aX * x'⁻¹ := by
      apply hρinj
      rw [map_mul, hρe, hρa, hx', hh''']
    have hEaE : ((x * aX * x⁻¹ : ↥(Xbar M Q Z B)) : Mbar M Q) * (aX : Mbar M Q) ∈
        Ebar M Q Z B := by
      have h2 := hEconj x'
      rw [← heaXeq] at h2
      exact h2
    have hcommU := hDU (x * aX * x⁻¹) (hEconj x) (congrArg Subtype.val heaX) hEaE
      (u : Mbar M Q) hu
    have hcommX : (x * aX * x⁻¹) * u = u * (x * aX * x⁻¹) := Subtype.ext hcommU
    rw [← hρe, ← map_mul, ← map_mul, hcommX]
  let f : ↥(U.subgroupOf (Xbar M Q Z B)) → ↥(lineGroup hBN a₁ c₁) := fun u =>
    ⟨ρ (u : ↥(Xbar M Q Z B)), hmem u u.2⟩
  have hf : Function.Injective f := fun u u' huu' =>
    Subtype.ext (hρinj (congrArg Subtype.val huu'))
  have hcardL : Nat.card (lineGroup hBN a₁ c₁) = Nat.card K := card_lineGroup hBN hBNnd hac hind
  have : Finite ↥(lineGroup hBN a₁ c₁) :=
    Nat.finite_of_card_ne_zero (by rw [hcardL]; exact Nat.card_pos.ne')
  calc Nat.card Z = Nat.card U := hUcard.symm
    _ = Nat.card (U.subgroupOf (Xbar M Q Z B)) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUX).toEquiv).symm
    _ ≤ Nat.card (lineGroup hBN a₁ c₁) := Nat.card_le_card_of_injective f hf
    _ = Nat.card K := hcardL

end CFSG.RankThree.GF2n.Stroth80
