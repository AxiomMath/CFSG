module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.H13.KGRu

variable {Γ : Type*} [Group Γ]

theorem conj_central {Z : Subgroup Γ} (hZ : Z ≤ Subgroup.center Γ) {s : Γ} (hs : s ∈ Z) (x : Γ) :
    x * s * x⁻¹ = s := by
  rw [Subgroup.mem_center_iff.mp (hZ hs) x, mul_inv_cancel_right]

theorem exists_bary [Finite Γ] {Z E M H : Subgroup Γ} (hZ : Z ≤ Subgroup.center Γ)
    (hE2 : ∀ e ∈ E, e * e = 1) (hEZ : E ⊓ Z = ⊥)
    (hM : ∀ g ∈ M, ∀ e ∈ E, ∃ e' ∈ E, e'⁻¹ * (g * e * g⁻¹) ∈ Z)
    (hHN : H ≤ Subgroup.normalizer (E : Set Γ)) (hodd : Odd (H.relIndex M)) :
    ∃ δ : Γ → Γ, (∀ e ∈ E, δ e ∈ Z) ∧ (∀ a ∈ E, ∀ b ∈ E, δ (a * b) = δ a * δ b) ∧
      ∀ g ∈ M, ∀ e ∈ E, ∃ e' ∈ E, g * e * g⁻¹ = e' * δ e' * (δ e)⁻¹ := by
  classical
  have hcen : ∀ s ∈ Z, ∀ x : Γ, x * s = s * x := fun s hs x =>
    Subgroup.mem_center_iff.mp (hZ hs) x
  let proj : Γ → Γ := fun x => if h : ∃ p ∈ E, p⁻¹ * x ∈ Z then h.choose else 1
  have hproj : ∀ x, (∃ p ∈ E, p⁻¹ * x ∈ Z) → proj x ∈ E ∧ (proj x)⁻¹ * x ∈ Z := by
    intro x hx
    simp only [proj, dite_eq_left hx]
    exact hx.choose_spec
  have huniq : ∀ x p q, p ∈ E → q ∈ E → p⁻¹ * x ∈ Z → q⁻¹ * x ∈ Z → p = q := by
    intro x p q hp hq hpx hqx
    have h1 : q⁻¹ * p ∈ E ⊓ Z := Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hq) hp, by
      have := mul_mem hqx (inv_mem hpx)
      rwa [show q⁻¹ * x * (p⁻¹ * x)⁻¹ = q⁻¹ * p by group] at this⟩
    rw [hEZ, Subgroup.mem_bot] at h1
    calc p = q * (q⁻¹ * p) := by group
      _ = q := by rw [h1, mul_one]
  have hproj_eq : ∀ x p, p ∈ E → p⁻¹ * x ∈ Z → proj x = p := fun x p hp hpx =>
    huniq x _ _ (hproj x ⟨p, hp, hpx⟩).1 hp (hproj x ⟨p, hp, hpx⟩).2 hpx
  have hex : ∀ r ∈ M, ∀ e ∈ E, ∃ p ∈ E, p⁻¹ * (r⁻¹ * e * r) ∈ Z := by
    intro r hr e he
    obtain ⟨e', he', h⟩ := hM r⁻¹ (inv_mem hr) e he
    exact ⟨e', he', by rwa [inv_inv] at h⟩
  let δr : Γ → Γ → Γ := fun r x => x⁻¹ * (r * proj (r⁻¹ * x * r) * r⁻¹)
  have hδr : ∀ r ∈ M, ∀ e ∈ E, r * proj (r⁻¹ * e * r) * r⁻¹ = e * δr r e := by
    intro r _ e _
    simp only [δr]
    group
  have hδrZ : ∀ r ∈ M, ∀ e ∈ E, δr r e ∈ Z := by
    intro r hr e he
    obtain ⟨hp, hs⟩ := hproj _ (hex r hr e he)
    set p := proj (r⁻¹ * e * r)
    set s := p⁻¹ * (r⁻¹ * e * r) with hs_def
    have hpe : p = r⁻¹ * e * r * s⁻¹ := by rw [hs_def]; group
    have : δr r e = r * s⁻¹ * r⁻¹ := by
      show e⁻¹ * (r * p * r⁻¹) = _
      rw [hpe]
      group
    rw [this, conj_central hZ (inv_mem hs)]
    exact inv_mem hs
  have hδrmul : ∀ r ∈ M, ∀ a ∈ E, ∀ b ∈ E, δr r (a * b) = δr r a * δr r b := by
    intro r hr a ha b hb
    obtain ⟨hpa, hsa⟩ := hproj _ (hex r hr a ha)
    obtain ⟨hpb, hsb⟩ := hproj _ (hex r hr b hb)
    have hab : proj (r⁻¹ * (a * b) * r) = proj (r⁻¹ * a * r) * proj (r⁻¹ * b * r) := by
      refine hproj_eq _ _ (mul_mem hpa hpb) ?_
      have e1 : (proj (r⁻¹ * a * r) * proj (r⁻¹ * b * r))⁻¹ * (r⁻¹ * (a * b) * r) =
          (proj (r⁻¹ * b * r))⁻¹ * ((proj (r⁻¹ * a * r))⁻¹ * (r⁻¹ * a * r)) * (r⁻¹ * b * r) := by
        group
      rw [e1, hcen _ hsa, mul_assoc]
      exact mul_mem hsa hsb
    have ha' := hδr r hr a ha
    have hb' := hδr r hr b hb
    have key : δr r (a * b) = (a * b)⁻¹ * ((r * proj (r⁻¹ * a * r) * r⁻¹) *
        (r * proj (r⁻¹ * b * r) * r⁻¹)) := by
      simp only [δr]
      rw [hab]
      group
    rw [key, ha', hb', show a * δr r a * (b * δr r b) = a * (δr r a * b) * δr r b by group,
      ← hcen _ (hδrZ r hr a ha) b]
    group
  let X := ↥M ⧸ H.subgroupOf M
  have : Fintype X := Fintype.ofFinite X
  let _ : CommGroup ↥Z :=
    { (inferInstance : Group ↥Z) with
      mul_comm := fun a b => Subtype.ext (hcen _ a.2 b).symm }
  let fac : Γ → X → ↥Z := fun x q =>
    if h : δr ((q.out : ↥M) : Γ) x ∈ Z then ⟨_, h⟩ else 1
  have hfac : ∀ e ∈ E, ∀ q : X, (fac e q : Γ) = δr ((q.out : ↥M) : Γ) e := by
    intro e he q
    simp only [fac, dite_eq_left (hδrZ _ (q.out : ↥M).2 e he)]
  let δ : Γ → Γ := fun x => ((∏ q : X, fac x q : ↥Z) : Γ)
  have hcardX : Odd (Fintype.card X) := by
    rw [Fintype.card_eq_nat_card]
    exact hodd
  refine ⟨δ, fun e _ => (∏ q : X, fac e q : ↥Z).2, ?_, ?_⟩
  · intro a ha b hb
    have : (∏ q : X, fac (a * b) q) = (∏ q : X, fac a q) * ∏ q : X, fac b q := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun q _ => Subtype.ext ?_
      rw [Subgroup.coe_mul, hfac _ (mul_mem ha hb), hfac _ ha, hfac _ hb]
      exact hδrmul _ (q.out : ↥M).2 a ha b hb
    simp only [δ]
    rw [this, Subgroup.coe_mul]
  · intro g hg e he
    obtain ⟨e', he', ht⟩ := hM g hg e he
    set t := e'⁻¹ * (g * e * g⁻¹) with ht_def
    refine ⟨e', he', ?_⟩
    have hgt : g * e * g⁻¹ = e' * t := by rw [ht_def]; group
    have ht2 : t * t = 1 := by
      have h1 : (g * e * g⁻¹) * (g * e * g⁻¹) = 1 := by
        rw [show g * e * g⁻¹ * (g * e * g⁻¹) = g * (e * e) * g⁻¹ by group, hE2 e he]
        group
      rw [hgt, show e' * t * (e' * t) = e' * (t * e') * t by group, ← hcen _ ht,
        show e' * (e' * t) * t = (e' * e') * (t * t) by group, hE2 e' he', one_mul] at h1
      exact h1
    let g' : ↥M := ⟨g, hg⟩
    have hpt : ∀ q : X, fac e' (g' • q) = ⟨t, ht⟩ * fac e q := by
      intro q
      apply Subtype.ext
      rw [Subgroup.coe_mul, hfac _ he', hfac _ he]
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (H.subgroupOf M) (g' * q.out)
      have hq : g' • q = (QuotientGroup.mk (g' * q.out) : X) := by
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      rw [hq, hh]
      have hhH : ((h : ↥M) : Γ) ∈ H := Subgroup.mem_subgroupOf.mp h.2
      set r : Γ := ((q.out : ↥M) : Γ)
      set k : Γ := ((h : ↥M) : Γ)
      have hr : r ∈ M := (q.out : ↥M).2
      show δr (g * r * k) e' = t * δr r e
      obtain ⟨hp, hs⟩ := hproj _ (hex r hr e he)
      set p := proj (r⁻¹ * e * r)
      set s := p⁻¹ * (r⁻¹ * e * r) with hs_def
      have hkp : k⁻¹ * p * k ∈ E := by
        have := (Subgroup.mem_normalizer_iff.mp (hHN (inv_mem hhH)) p).mp hp
        rwa [inv_inv] at this
      have he'g : g⁻¹ * e' * g = e * t⁻¹ := by
        have h1 : e' = g * e * g⁻¹ * t⁻¹ := by rw [hgt]; group
        rw [h1, show g⁻¹ * (g * e * g⁻¹ * t⁻¹) * g = e * (g⁻¹ * t⁻¹ * g) by group,
          show g⁻¹ * t⁻¹ * g = g⁻¹ * t⁻¹ * g⁻¹⁻¹ by rw [inv_inv],
          conj_central hZ (inv_mem ht)]
      have hproj' : proj ((g * r * k)⁻¹ * e' * (g * r * k)) = k⁻¹ * p * k := by
        refine hproj_eq _ _ hkp ?_
        have hpe : p = r⁻¹ * e * r * s⁻¹ := by rw [hs_def]; group
        have hee : e = r * p * s * r⁻¹ := by rw [hpe]; group
        have he1 : e' = g * e * g⁻¹ * t⁻¹ := by rw [hgt]; group
        have e1 : (k⁻¹ * p * k)⁻¹ * ((g * r * k)⁻¹ * e' * (g * r * k)) =
            k⁻¹ * (s * ((g * r)⁻¹ * t⁻¹ * (g * r)⁻¹⁻¹)) * k⁻¹⁻¹ := by
          rw [he1, hee]
          group
        rw [e1, conj_central hZ (inv_mem ht), conj_central hZ (mul_mem hs (inv_mem ht))]
        exact mul_mem hs (inv_mem ht)
      have hrpr := hδr r hr e he
      show e'⁻¹ * (g * r * k * proj ((g * r * k)⁻¹ * e' * (g * r * k)) * (g * r * k)⁻¹) =
        t * δr r e
      rw [hproj', show g * r * k * (k⁻¹ * p * k) * (g * r * k)⁻¹ = g * (r * p * r⁻¹) * g⁻¹ by
        group, hrpr, show g * (e * δr r e) * g⁻¹ = (g * e * g⁻¹) * (g * δr r e * g⁻¹) by group,
        conj_central hZ (hδrZ r hr e he), hgt]
      group
    have hprod : (∏ q : X, fac e' q) = ⟨t, ht⟩ * ∏ q : X, fac e q := by
      rw [← Fintype.prod_equiv (MulAction.toPerm g') (fun q => fac e' (g' • q)) (fac e')
        (fun q => rfl)]
      simp only [hpt]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      congr 1
      obtain ⟨m, hm⟩ := hcardX
      rw [hm, pow_succ, pow_mul, sq]
      have : (⟨t, ht⟩ : ↥Z) * ⟨t, ht⟩ = 1 := Subtype.ext ht2
      rw [this, one_pow, one_mul]
    have hδe' : δ e' = t * δ e := by
      simp only [δ]
      rw [hprod, Subgroup.coe_mul]
    rw [hδe', show e' * (t * δ e) * (δ e)⁻¹ = e' * t by group, hgt]

theorem delta_eq_one {E H : Subgroup Γ} {δ : Γ → Γ} (hE2 : ∀ e ∈ E, e * e = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hδ : ∀ a ∈ E, ∀ b ∈ E, δ (a * b) = δ a * δ b)
    (hδH : ∀ h ∈ H, ∀ e ∈ E, δ (h * e * h⁻¹) = δ e)
    (hHN : H ≤ Subgroup.normalizer (E : Set Γ)) {z s e₀ y : Γ} (hzE : z ∈ E) (hs : s ∈ H)
    (he₀ : e₀ ∈ E) (hsz : s * e₀ * s⁻¹ * e₀⁻¹ = z) (hy : y ∈ H) (hy3 : y ^ 3 = 1)
    (hfpf : ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ ∈ Subgroup.zpowers z → e ∈ Subgroup.zpowers z) :
    ∀ e ∈ E, δ e = 1 := by
  have hconj : ∀ h ∈ H, ∀ e ∈ E, h * e * h⁻¹ ∈ E := fun h hh e he =>
    (Subgroup.mem_normalizer_iff.mp (hHN hh) e).mp he
  have hδ1 : δ 1 = 1 := by
    have h := hδ 1 E.one_mem 1 E.one_mem
    rw [one_mul] at h
    exact (mul_eq_left.mp h.symm)
  have hinv : ∀ e ∈ E, e⁻¹ = e := fun e he => inv_eq_of_mul_eq_one_right (hE2 e he)
  have hcomm : ∀ h ∈ H, ∀ e ∈ E, δ (h * e * h⁻¹ * e⁻¹) = 1 := by
    intro h hh e he
    rw [hδ _ (hconj h hh e he) _ (inv_mem he), hδH h hh e he, hinv e he, ← hδ e he e he,
      hE2 e he, hδ1]
  have hz1 : δ z = 1 := by
    rw [← hsz]
    exact hcomm s hs e₀ he₀
  intro e he
  have hye : y * e * y⁻¹ ∈ E := hconj y hy e he
  have hy2e : y * (y * e * y⁻¹) * y⁻¹ ∈ E := hconj y hy _ hye
  obtain ⟨e1, he1⟩ : ∃ a, a = y * e * y⁻¹ := ⟨_, rfl⟩
  obtain ⟨e2, he2⟩ : ∃ a, a = y * e1 * y⁻¹ := ⟨_, rfl⟩
  rw [← he1] at hye hy2e
  rw [← he2] at hy2e
  have h3 : y * y * y = 1 := by rw [← hy3, pow_three, mul_assoc]
  have hye2 : y * e2 * y⁻¹ = e := by
    rw [he2, he1]
    calc y * (y * (y * e * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * e * (y * y * y)⁻¹ := by group
      _ = e := by rw [h3]; group
  obtain ⟨w, hw⟩ : ∃ a, a = e2 * e1 * e := ⟨_, rfl⟩
  have hwE : w ∈ E := hw ▸ mul_mem (mul_mem hy2e hye) he
  have hwc : y * w * y⁻¹ * w⁻¹ = 1 := by
    have h1 : y * w * y⁻¹ = e * e2 * e1 := by
      calc y * w * y⁻¹ = (y * e2 * y⁻¹) * (y * e1 * y⁻¹) * (y * e * y⁻¹) := by rw [hw]; group
        _ = e * e2 * e1 := by rw [hye2, ← he2, ← he1]
    rw [h1, mul_inv_eq_one, hw, hEc e he e2 hy2e, mul_assoc, hEc e he e1 hye, ← mul_assoc]
  have hwz : w ∈ Subgroup.zpowers z := hfpf w hwE (by rw [hwc]; exact Subgroup.one_mem _)
  have hδw : δ w = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwz
    have hz2 : z * z = 1 := hE2 z hzE
    rw [← hk]
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [show (m + m : ℤ) = 2 * m by ring, zpow_mul, zpow_two, hz2, one_zpow, hδ1]
    · rw [zpow_add_one, zpow_mul, zpow_two, hz2, one_zpow, one_mul, hz1]
  have hdecomp : (y * e1 * y⁻¹ * e1⁻¹) * w = e := by
    rw [← he2, hinv e1 hye, hw]
    calc e2 * e1 * (e2 * e1 * e) = e2 * (e1 * e2) * e1 * e := by group
      _ = e2 * (e2 * e1) * e1 * e := by rw [hEc e1 hye e2 hy2e]
      _ = (e2 * e2) * (e1 * e1) * e := by group
      _ = e := by rw [hE2 e2 hy2e, hE2 e1 hye]; group
  have hcE : y * e1 * y⁻¹ * e1⁻¹ ∈ E := mul_mem (hconj y hy e1 hye) (inv_mem hye)
  rw [← hdecomp, hδ _ hcE w hwE, hcomm y hy e1 hye, hδw, one_mul]

theorem le_normalizer_of_odd [Finite Γ] {Z E M : Subgroup Γ} (hZ : Z ≤ Subgroup.center Γ)
    (hE2 : ∀ e ∈ E, e * e = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEZ : E ⊓ Z = ⊥)
    (hM : ∀ g ∈ M, ∀ e ∈ E, ∃ e' ∈ E, e'⁻¹ * (g * e * g⁻¹) ∈ Z)
    (hodd : Odd ((M ⊓ Subgroup.normalizer (E : Set Γ)).relIndex M)) {z s e₀ y : Γ}
    (hzE : z ∈ E) (hs : s ∈ M ⊓ Subgroup.normalizer (E : Set Γ)) (he₀ : e₀ ∈ E)
    (hsz : s * e₀ * s⁻¹ * e₀⁻¹ = z) (hy : y ∈ M ⊓ Subgroup.normalizer (E : Set Γ))
    (hy3 : y ^ 3 = 1)
    (hfpf : ∀ e ∈ E, y * e * y⁻¹ * e⁻¹ ∈ Subgroup.zpowers z → e ∈ Subgroup.zpowers z) :
    M ≤ Subgroup.normalizer (E : Set Γ) := by
  set H := M ⊓ Subgroup.normalizer (E : Set Γ) with hH
  have hHM : H ≤ M := inf_le_left
  have hHN : H ≤ Subgroup.normalizer (E : Set Γ) := inf_le_right
  obtain ⟨δ, hδZ, hδ, hconj⟩ := exists_bary hZ hE2 hEZ hM hHN hodd
  have hδH : ∀ h ∈ H, ∀ e ∈ E, δ (h * e * h⁻¹) = δ e := by
    intro h hh e he
    obtain ⟨e', he', heq⟩ := hconj h (hHM hh) e he
    have hhe : h * e * h⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hHN hh) e).mp he
    have hmem : e'⁻¹ * (h * e * h⁻¹) ∈ E ⊓ Z := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem he') hhe, ?_⟩
      rw [heq, show e'⁻¹ * (e' * δ e' * (δ e)⁻¹) = δ e' * (δ e)⁻¹ by group]
      exact mul_mem (hδZ e' he') (inv_mem (hδZ e he))
    rw [hEZ, Subgroup.mem_bot] at hmem
    have h1 : e' = h * e * h⁻¹ := by
      calc e' = e' * (e'⁻¹ * (h * e * h⁻¹)) := by rw [hmem, mul_one]
        _ = h * e * h⁻¹ := by group
    rw [heq, show e'⁻¹ * (e' * δ e' * (δ e)⁻¹) = δ e' * (δ e)⁻¹ by group, mul_inv_eq_one] at hmem
    rw [← h1, hmem]
  have h1 := delta_eq_one hE2 hEc hδ hδH hHN hzE hs he₀ hsz hy hy3 hfpf
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro e
  constructor
  · intro he
    obtain ⟨e', he', heq⟩ := hconj g hg e he
    rw [heq, h1 e' he', h1 e he, mul_one, inv_one, mul_one]
    exact he'
  · intro he
    obtain ⟨e', he', heq⟩ := hconj g⁻¹ (inv_mem hg) _ he
    rw [h1 e' he', h1 _ he, mul_one, inv_one, mul_one,
      show g⁻¹ * (g * e * g⁻¹) * g⁻¹⁻¹ = e by group] at heq
    rw [heq]
    exact he'

end CFSG.Quasithin.H13.KGRu
