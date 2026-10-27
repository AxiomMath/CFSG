module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtSeven
public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassDim3Aux
public import CFSG.Quasithin.SteinbergBSBinaryCubeBound

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {G H B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}

private theorem card_quadratic_roots_le_two {p : ℕ} [Fact p.Prime] (b c : ZMod p) :
    (Finset.univ.filter (fun z : ZMod p => z ^ 2 + b * z + c = 0)).card ≤ 2 := by
  classical
  set S := Finset.univ.filter (fun z : ZMod p => z ^ 2 + b * z + c = 0) with hS
  by_cases h : ∃ z : ZMod p, z ^ 2 + b * z + c = 0
  · obtain ⟨z₀, hz₀⟩ := h
    have hsub : S ⊆ ({z₀, -b - z₀} : Finset (ZMod p)) := by
      intro z hz
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      have h1 : (z - z₀) * (z + z₀ + b) = 0 := by
        linear_combination hz - hz₀
      rcases mul_eq_zero.mp h1 with h2 | h2
      · rw [Finset.mem_insert, Finset.mem_singleton]
        left
        linear_combination h2
      · rw [Finset.mem_insert, Finset.mem_singleton]
        right
        linear_combination h2
    calc S.card ≤ ({z₀, -b - z₀} : Finset (ZMod p)).card := Finset.card_le_card hsub
      _ ≤ 2 := by
        rw [show ({z₀, -b - z₀} : Finset (ZMod p)) = insert z₀ {-b - z₀} from rfl]
        exact (Finset.card_insert_le _ _).trans (by simp)
  · push Not at h
    have hsub : S ⊆ (∅ : Finset (ZMod p)) := by
      intro z hz
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      exact absurd hz (h z)
    exact (Finset.card_le_card hsub).trans (by simp)

private theorem card_sq_eq_le_two {p : ℕ} [Fact p.Prime] (z : ZMod p) :
    (Finset.univ.filter (fun m : ZMod p => m ^ 2 = z)).card ≤ 2 := by
  convert card_quadratic_roots_le_two (p := p) (0 : ZMod p) (-z) using 2
  ext m
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; rw [h]; simp
  · intro h; linear_combination h

private def goodM {p : ℕ} [Fact p.Prime] (c d m : ZMod p) : Prop :=
  c + d * m ^ 2 ≠ 0 ∧ d * m ^ 2 - c ≠ 0 ∧ m ≠ 0 ∧
    (3 * (d * m ^ 2) - c) * (d * m ^ 2 - 3 * c) ≠ 0 ∧
    (d * m ^ 2) ^ 2 - 6 * c * (d * m ^ 2) + c ^ 2 ≠ 0

private def fiberSet {p : ℕ} [Fact p.Prime] (z : ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter (fun m : ZMod p => m ^ 2 = z)

private def TqSet {p : ℕ} [Fact p.Prime] (κ : ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter (fun z : ZMod p => z ^ 2 + (-(6 * κ)) * z + κ ^ 2 = 0)

private def TSet {p : ℕ} [Fact p.Prime] (κ : ZMod p) : Finset (ZMod p) :=
  ({0, -κ, κ, κ / 3, 3 * κ} : Finset (ZMod p)) ∪ TqSet κ

private theorem card_fiberSet_le_two {p : ℕ} [Fact p.Prime] (z : ZMod p) :
    (fiberSet z).card ≤ 2 := by
  rw [fiberSet]
  exact card_sq_eq_le_two z

private theorem card_TqSet_le_two {p : ℕ} [Fact p.Prime] (κ : ZMod p) :
    (TqSet κ).card ≤ 2 := by
  rw [TqSet]
  exact card_quadratic_roots_le_two (-(6 * κ)) (κ ^ 2)

private theorem card_TSet_le_seven {p : ℕ} [Fact p.Prime] (κ : ZMod p) :
    (TSet κ).card ≤ 7 := by
  rw [TSet]
  refine (Finset.card_union_le _ _).trans ?_
  have h5 : ({0, -κ, κ, κ / 3, 3 * κ} : Finset (ZMod p)).card ≤ 5 := by
    have h1 : ({0, -κ, κ, κ / 3, 3 * κ} : Finset (ZMod p)).card ≤
        ({-κ, κ, κ / 3, 3 * κ} : Finset (ZMod p)).card + 1 := Finset.card_insert_le _ _
    have h2 : ({-κ, κ, κ / 3, 3 * κ} : Finset (ZMod p)).card ≤
        ({κ, κ / 3, 3 * κ} : Finset (ZMod p)).card + 1 := Finset.card_insert_le _ _
    have h3 : ({κ, κ / 3, 3 * κ} : Finset (ZMod p)).card ≤
        ({κ / 3, 3 * κ} : Finset (ZMod p)).card + 1 := Finset.card_insert_le _ _
    have h4 : ({κ / 3, 3 * κ} : Finset (ZMod p)).card ≤
        ({3 * κ} : Finset (ZMod p)).card + 1 := Finset.card_insert_le _ _
    have h5 : ({3 * κ} : Finset (ZMod p)).card = 1 := Finset.card_singleton _
    omega
  have h2 := card_TqSet_le_two κ
  omega

private theorem mem_union_of_quartic {p : ℕ} [Fact p.Prime] {c d κ m : ZMod p}
    (hcκ : c = κ * d) (hd : d ≠ 0)
    (h : (d * m ^ 2) ^ 2 - 6 * c * (d * m ^ 2) + c ^ 2 = 0) :
    ∃ z ∈ TSet κ, m ∈ fiberSet z := by
  refine ⟨m ^ 2, ?_, by simp [fiberSet]⟩
  rw [TSet, Finset.mem_union]
  right
  rw [TqSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hm' : (d * m ^ 2) ^ 2 - 6 * (κ * d) * (d * m ^ 2) + (κ * d) ^ 2 = 0 := by
    rw [← hcκ]
    exact h
  have hfact : d ^ 2 * ((m ^ 2) ^ 2 + (-(6 * κ)) * (m ^ 2) + κ ^ 2) = 0 := by
    linear_combination hm'
  exact (mul_eq_zero.mp hfact).resolve_left (pow_ne_zero 2 hd)

private theorem bad_subset_union {p : ℕ} [Fact p.Prime] {c d κ m : ZMod p}
    (hcκ : c = κ * d) (hd : d ≠ 0) (h3 : (3 : ZMod p) ≠ 0) (hm : ¬ goodM c d m) :
    m ∈ (TSet κ).biUnion fiberSet := by
  rw [goodM] at hm
  have hdisj : c + d * m ^ 2 = 0 ∨ d * m ^ 2 - c = 0 ∨ m = 0 ∨
      (3 * (d * m ^ 2) - c) * (d * m ^ 2 - 3 * c) = 0 ∨
      (d * m ^ 2) ^ 2 - 6 * c * (d * m ^ 2) + c ^ 2 = 0 := by
    by_contra h
    push Not at h
    exact hm h
  rw [Finset.mem_biUnion]
  rcases hdisj with h | h | h | h | h
  · refine ⟨-κ, by simp [TSet], ?_⟩
    have h1 : m ^ 2 + κ = 0 := by
      have h2 : d * (m ^ 2 + κ) = 0 := by linear_combination h - hcκ
      exact (mul_eq_zero.mp h2).resolve_left hd
    rw [fiberSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by linear_combination h1⟩
  · refine ⟨κ, by simp [TSet], ?_⟩
    have h1 : m ^ 2 - κ = 0 := by
      have h2 : d * (m ^ 2 - κ) = 0 := by linear_combination h + hcκ
      exact (mul_eq_zero.mp h2).resolve_left hd
    rw [fiberSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by linear_combination h1⟩
  · subst h
    exact ⟨0, by simp [TSet], by simp [fiberSet]⟩
  · rcases mul_eq_zero.mp h with h | h
    · refine ⟨κ / 3, by simp [TSet], ?_⟩
      have h1 : 3 * m ^ 2 = κ := by
        have h2 : d * (3 * m ^ 2 - κ) = 0 := by linear_combination h + hcκ
        exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hd)
      rw [fiberSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [eq_div_iff h3]
      linear_combination h1
    · refine ⟨3 * κ, by simp [TSet], ?_⟩
      have h1 : m ^ 2 - 3 * κ = 0 := by
        have h2 : d * (m ^ 2 - 3 * κ) = 0 := by linear_combination h + 3 * hcκ
        exact (mul_eq_zero.mp h2).resolve_left hd
      rw [fiberSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by linear_combination h1⟩
  · exact mem_union_of_quartic hcκ hd h

private theorem exists_good_m_of_seventeen {p : ℕ} [Fact p.Prime] (hp : 17 ≤ p)
    {c d : ZMod p} (hc : c ≠ 0) (hd : d ≠ 0) :
    ∃ m : ZMod p, goodM c d m := by
  classical
  have h3 : (3 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 3 (by omega)
  set κ : ZMod p := c / d with hκ
  have hcκ : c = κ * d := by
    rw [hκ]
    field_simp
  set bad : Finset (ZMod p) := Finset.univ.filter (fun m : ZMod p => ¬ goodM c d m) with hbad
  have hsub : bad ⊆ (TSet κ).biUnion fiberSet := by
    intro m hm
    rw [hbad, Finset.mem_filter] at hm
    exact bad_subset_union hcκ hd h3 hm.2
  have hbadcard : bad.card ≤ 14 := by
    calc bad.card ≤ ((TSet κ).biUnion fiberSet).card := Finset.card_le_card hsub
      _ ≤ ∑ z ∈ TSet κ, (fiberSet z).card := Finset.card_biUnion_le
      _ ≤ ∑ z ∈ TSet κ, 2 := by
          refine Finset.sum_le_sum ?_
          intro z hz
          exact card_fiberSet_le_two z
      _ = (TSet κ).card * 2 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 14 := by
          have := card_TSet_le_seven κ
          omega
  have hlt : bad.card < Fintype.card (ZMod p) := by
    rw [ZMod.card]
    omega
  have hex : ∃ m : ZMod p, m ∉ bad := by
    by_contra h
    push Not at h
    have hbaduniv : bad = Finset.univ := Finset.eq_univ_of_forall h
    rw [hbaduniv, Finset.card_univ] at hlt
    exact absurd hlt (lt_irrefl _)
  obtain ⟨m, hm⟩ := hex
  exact ⟨m, by
    by_contra hgood
    exact hm (by rw [hbad, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hgood⟩)⟩

private theorem good_m_eleven (c d : ZMod 11) (hc : c ≠ 0) (hd : d ≠ 0) :
    ∃ m : ZMod 11, c + d * m ^ 2 ≠ 0 ∧ d * m ^ 2 - c ≠ 0 ∧ m ≠ 0 ∧
      (3 * (d * m ^ 2) - c) * (d * m ^ 2 - 3 * c) ≠ 0 ∧
      (d * m ^ 2) ^ 2 - 6 * c * (d * m ^ 2) + c ^ 2 ≠ 0 := by
  revert c d
  decide

private theorem good_m_thirteen (c d : ZMod 13) (hc : c ≠ 0) (hd : d ≠ 0) :
    ∃ m : ZMod 13, c + d * m ^ 2 ≠ 0 ∧ d * m ^ 2 - c ≠ 0 ∧ m ≠ 0 ∧
      (3 * (d * m ^ 2) - c) * (d * m ^ 2 - 3 * c) ≠ 0 ∧
      (d * m ^ 2) ^ 2 - 6 * c * (d * m ^ 2) + c ^ 2 ≠ 0 := by
  revert c d
  decide

private theorem exists_good_m {p : ℕ} [Fact p.Prime] (hp : 11 ≤ p)
    {c d : ZMod p} (hc : c ≠ 0) (hd : d ≠ 0) :
    ∃ m : ZMod p, c + d * m ^ 2 ≠ 0 ∧ d * m ^ 2 - c ≠ 0 ∧ m ≠ 0 ∧
      (3 * (d * m ^ 2) - c) * (d * m ^ 2 - 3 * c) ≠ 0 ∧
      (d * m ^ 2) ^ 2 - 6 * c * (d * m ^ 2) + c ^ 2 ≠ 0 := by
  by_cases h17 : 17 ≤ p
  · exact exists_good_m_of_seventeen h17 hc hd
  · push Not at h17
    interval_cases p
    · exact good_m_eleven c d hc hd
    · exact absurd (Fact.out : Nat.Prime 12) (by norm_num)
    · exact good_m_thirteen c d hc hd
    · exact absurd (Fact.out : Nat.Prime 14) (by norm_num)
    · exact absurd (Fact.out : Nat.Prime 15) (by norm_num)
    · exact absurd (Fact.out : Nat.Prime 16) (by norm_num)

private theorem quadratic_eq_of_polar_eq_zero {Q : QuadraticForm (ZMod p) U} {a a' : U}
    {c d : ZMod p} (hQa : Q a = c) (hQa' : Q a' = d)
    (hB : QuadraticMap.polar Q a a' = 0) (m : ZMod p)
    (hden : c + d * m ^ 2 ≠ 0) :
    Q ((c + d * m ^ 2)⁻¹ • ((c - d * m ^ 2) • a + (2 * c * m) • a')) = c := by
  have hcomb : Q ((c - d * m ^ 2) • a + (2 * c * m) • a') =
      c * (c + d * m ^ 2) ^ 2 := by
    rw [QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul, QuadraticMap.map_smul,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hB, smul_zero, smul_zero,
      add_zero]
    rw [smul_eq_mul, smul_eq_mul, hQa, hQa']
    ring
  rw [QuadraticMap.map_smul, hcomb, smul_eq_mul]
  field_simp [hden]

private theorem b_polar_eq {Q : QuadraticForm (ZMod p) U} {a a' : U} {c d : ZMod p}
    (hQa : Q a = c) (hB : QuadraticMap.polar Q a a' = 0) (m : ZMod p)
    (hden : c + d * m ^ 2 ≠ 0) (hc : c ≠ 0) :
    QuadraticMap.polarBilin Q a
        ((c + d * m ^ 2)⁻¹ • ((c - d * m ^ 2) • a + (2 * c * m) • a')) / c =
      2 * (c - d * m ^ 2) / (c + d * m ^ 2) := by
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_smul_right,
    QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right,
    hB, smul_zero, add_zero, CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul, hQa]
  rw [smul_eq_mul, smul_eq_mul]
  field_simp [hden, hc]

private theorem x_conditions {c d m : ZMod p}
    (h2 : (2 : ZMod p) ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (hm : m ≠ 0)
    (hden : c + d * m ^ 2 ≠ 0) (hN : d * m ^ 2 - c ≠ 0)
    (h3 : (3 * (d * m ^ 2) - c) * (d * m ^ 2 - 3 * c) ≠ 0)
    (hq : (d * m ^ 2) ^ 2 - 6 * c * (d * m ^ 2) + c ^ 2 ≠ 0) :
    2 * (c - d * m ^ 2) / (c + d * m ^ 2) ≠ 0 ∧
    (2 * (c - d * m ^ 2) / (c + d * m ^ 2)) ^ 2 ≠ 1 ∧
    (2 * (c - d * m ^ 2) / (c + d * m ^ 2)) ^ 2 ≠ 2 ∧
    (2 * (c - d * m ^ 2) / (c + d * m ^ 2)) ^ 2 ≠ 4 := by
  set x : ZMod p := 2 * (c - d * m ^ 2) / (c + d * m ^ 2) with hx
  have h16 : (16 : ZMod p) ≠ 0 := by
    have h : (16 : ZMod p) = 2 * 2 * 2 * 2 := by norm_num
    rw [h]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2
  have hx0 : x ≠ 0 := by
    intro h
    have hnum : 2 * (c - d * m ^ 2) = 0 := by
      have h' := congrArg (fun t => t * (c + d * m ^ 2)) h
      rwa [hx, div_mul_cancel₀ _ hden, zero_mul] at h'
    rcases mul_eq_zero.mp hnum with h' | h'
    · exact h2 h'
    · exact hN (by linear_combination -h')
  have hx4 : x ^ 2 ≠ 4 := by
    intro h
    rw [hx, div_pow] at h
    field_simp at h
    have h4cd : 16 * (c * d * m ^ 2) = 0 := by linear_combination -h
    have hcd : c * d * m ^ 2 = 0 := (mul_eq_zero.mp h4cd).resolve_left h16
    have hm2 : m ^ 2 = 0 := by
      rcases mul_eq_zero.mp hcd with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' hc
        · exact absurd h'' hd
      · exact h'
    exact hm (by simpa [pow_two] using hm2)
  have hx1 : x ^ 2 ≠ 1 := by
    intro h
    rw [hx, div_pow] at h
    field_simp at h
    exact h3 (by linear_combination h)
  have hx2 : x ^ 2 ≠ 2 := by
    intro h
    rw [hx, div_pow] at h
    field_simp at h
    exact hq (by linear_combination h)
  exact ⟨hx0, hx1, hx2, hx4⟩

private theorem reflStab_pair
    (hp : p ≠ 2) [Module.Finite (ZMod p) U] (h11 : 11 ≤ p)
    {Q : QuadraticForm (ZMod p) U} (_hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U} {E : Submodule (ZMod p) U}
    (hEpol : ClassicalGroups.Orthogonal.PolarNondegOn Q E)
    (hEfin : Module.finrank (ZMod p) E = 2)
    (hEker : E ≤ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))
    {c : ZMod p} (hc : c ≠ 0) {a : U} (haE : a ∈ E) (haQ : Q a = c)
    (hmemH : ∀ b ∈ E, Q b = c → CFSG.ClassicalGroups.Orthogonal.reflect Q b ∈ H) :
    ∃ x ∈ reflStab p H h, ∃ y ∈ reflStab p H h, IsRefl p x ∧ IsRefl p y ∧
      4 < orderOf (x * y) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hQa : Q a ≠ 0 := haQ ▸ hc
  have hpol := ClassicalGroups.Orthogonal.PolarNondegOn.inf_ker h2 hEpol haE hQa
  have hne : E ⊓ LinearMap.ker (QuadraticMap.polarBilin Q a) ≠ ⊥ := by
    intro hbot
    have hfin := ClassicalGroups.Orthogonal.finrank_inf_ker_polarBilin_add_one h2 haE hQa
    rw [hbot, finrank_bot] at hfin
    omega
  obtain ⟨a', ha', hQa'⟩ := hpol.exists_map_ne_zero hne
  have ha'E : a' ∈ E := ha'.1
  have hBaa' : QuadraticMap.polar Q a a' = 0 := by
    rw [← QuadraticMap.polarBilin_apply_apply]
    exact LinearMap.mem_ker.mp ha'.2
  set d : ZMod p := Q a' with hd
  have hd0 : d ≠ 0 := by rw [hd]; exact hQa'
  obtain ⟨m, hden, hN, hm0, h3, hq⟩ := exists_good_m h11 hc hd0
  set b : U := (c + d * m ^ 2)⁻¹ • ((c - d * m ^ 2) • a + (2 * c * m) • a') with hb
  have hbE : b ∈ E := by
    rw [hb]
    exact E.smul_mem _ (E.add_mem (E.smul_mem _ haE) (E.smul_mem _ ha'E))
  have hQb : Q b = c := quadratic_eq_of_polar_eq_zero haQ (by rw [hd]) hBaa' m hden
  have hbQ : Q b ≠ 0 := by rw [hQb]; exact hc
  have hxeq : QuadraticMap.polarBilin Q a b / c = 2 * (c - d * m ^ 2) / (c + d * m ^ 2) :=
    b_polar_eq haQ hBaa' m hden hc
  obtain ⟨hx0, hx1, hx2, hx4⟩ := x_conditions h2 hc hd0 hm0 hden hN h3 hq
  have : Finite U := Module.finite_of_finite (ZMod p)
  have hlt := owD3_order_criterion h2 Q hc hQa hbQ haQ hQb hxeq hx0 hx1 hx2 hx4
  have hra : owCr_orthRefl Q a hQa = CFSG.ClassicalGroups.Orthogonal.reflect Q a := by
    ext v
    rw [owCr_orthRefl_apply, CFSG.ClassicalGroups.Orthogonal.reflect_apply hQa,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm Q v a]
  have hrb : owCr_orthRefl Q b hbQ = CFSG.ClassicalGroups.Orthogonal.reflect Q b := by
    ext v
    rw [owCr_orthRefl_apply, CFSG.ClassicalGroups.Orthogonal.reflect_apply hbQ,
      QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm Q v b]
  rw [hra, hrb] at hlt
  exact ⟨_, reflect_mem_reflStab hp (hEker haE) hQa (hmemH a haE haQ),
    _, reflect_mem_reflStab hp (hEker hbE) hbQ (hmemH b hbE hQb),
    isRefl_reflect hp hQa, isRefl_reflect hp hbQ, hlt⟩

private theorem reflStab_pair_of_isOrthOn
    (hp : p ≠ 2) [Module.Finite (ZMod p) U] (h11 : 11 ≤ p)
    {Q : QuadraticForm (ZMod p) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U} (ho : IsOrthOn p Q H)
    {E : Submodule (ZMod p) U}
    (hEpol : ClassicalGroups.Orthogonal.PolarNondegOn Q E)
    (hEfin : Module.finrank (ZMod p) E = 2)
    (hEker : E ≤ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))
    (hEV : E ≤ HardMathSupport.Kantor79.commutatorSpace H) :
    ∃ x ∈ reflStab p H h, ∃ y ∈ reflStab p H h, IsRefl p x ∧ IsRefl p y ∧
      4 < orderOf (x * y) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hEne : E ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hEfin
    omega
  rcases ho with hfull | ⟨c, hc, hclass⟩
  · obtain ⟨a, haE, hQa⟩ := hEpol.exists_map_ne_zero hEne
    refine reflStab_pair (c := Q a) hp h11 hQ hEpol hEfin hEker hQa haE rfl ?_
    intro b hbE hbQ
    have hbQ' : Q b ≠ 0 := by rw [hbQ]; exact hQa
    rw [hfull]
    refine Subgroup.subset_closure ⟨isRefl_reflect hp hbQ', isIsom_reflect Q b, ?_⟩
    rw [movedSpace_reflect_eq_span hp hbQ']
    exact Submodule.span_le.mpr (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hEV hbE)
  · obtain ⟨a, haE, hQa⟩ := hEpol.exists_map_eq h2 (by omega) c
    refine reflStab_pair hp h11 hQ hEpol hEfin hEker hc haE hQa ?_
    intro b hbE hbQ
    have hbQ' : Q b ≠ 0 := by rw [hbQ]; exact hc
    rw [hclass]
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · rw [mem_classRefl_iff hp hQ hc]
      exact ⟨b, hbQ, rfl⟩
    · rw [movedSpace_reflect_eq_span hp hbQ']
      exact Submodule.span_le.mpr (fun x hx => by
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hEV hbE)

private theorem exists_four_lt_orderOf_reflStab_aux (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4) (h11 : 11 ≤ p) :
    ∃ x ∈ reflStab p H h, ∃ y ∈ reflStab p H h, IsRefl p x ∧ IsRefl p y ∧
      4 < orderOf (x * y) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hHsub := hD.setting.sub
  have hHsplit : SplitSupport H 3 := by
    have h := hHsub.2.1
    rwa [h4] at h
  have horth : IsOrthType p (movedGroup H) := hHsub.2.2.2.1
  obtain ⟨f, hfC, hf0⟩ := hHsplit.exists_mem_centralizerSpace_ne_zero (by omega)
  obtain ⟨Q, hQ, ho, hQf⟩ :=
    exists_isOrthOn_of_isOrthType_movedGroup hp (by simpa [h4] using hHsplit) horth hfC hf0
      (c := 1) one_ne_zero
  obtain ⟨e, hQe, hee⟩ := DimThree.exists_root_of_isRefl_isIsom hp hQ hD.isRefl (ho.isIsom hD.mem)
  have he0 : e ≠ 0 := fun h => hQe (by rw [h]; exact QuadraticMap.map_zero Q)
  have hh_eq : h = CFSG.ClassicalGroups.Orthogonal.reflect Q e :=
    DimThree.eq_of_isRefl_isIsom_of_apply_eq_neg hp hQ hD.isRefl (ho.isIsom hD.mem)
      (isRefl_reflect hp hQe) (isIsom_reflect Q e) he0 hee (reflect_apply_self hQe)
  have hker : LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) =
      LinearMap.ker (QuadraticMap.polarBilin Q e) := by
    rw [hh_eq]
    exact ker_reflect_sub_one_eq_ker_polar hQe
  have heV : e ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hD.mem
      (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg h2 hee)
  set E : Submodule (ZMod p) U := HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) with hE
  have hEeq : E = HardMathSupport.Kantor79.commutatorSpace H ⊓
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) :=
    commutatorSpace_reflStab hp hQ hHsplit le_rfl (by intro hp3; omega) ho hD.mem hD.isRefl
  have hEfin : Module.finrank (ZMod p) E = 2 := by
    rw [hEeq, hker]
    have hfr := ClassicalGroups.Orthogonal.finrank_inf_ker_polarBilin_add_one h2 heV hQe
    have hV3 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) = 3 :=
      hHsplit.2.1
    omega
  have hEpol : ClassicalGroups.Orthogonal.PolarNondegOn Q E := by
    rw [hEeq, hker]
    exact ClassicalGroups.Orthogonal.PolarNondegOn.inf_ker h2
      (polarNondegOn_commutatorSpace hQ (fun g hg => ho.isIsom hg) hHsplit.1) heV hQe
  have hEker : E ≤ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
    rw [hEeq]
    exact inf_le_right
  have hEV : E ≤ HardMathSupport.Kantor79.commutatorSpace H := by
    rw [hEeq]
    exact inf_le_left
  exact reflStab_pair_of_isOrthOn hp h11 hQ ho hEpol hEfin hEker hEV

private theorem false_of_p_five {U : Type} [Fact (Nat.Prime 5)] [AddCommGroup U]
    [Module (ZMod 5) U] [Module.Finite (ZMod 5) U] {B : Subgroup (U ≃ₗ[ZMod 5] U)}
    (hsplitB : SplitSupport B 3) (hcard : Nat.card (movedGroup B) = 336) : False := by
  have hV3 : Module.finrank (ZMod 5) (HardMathSupport.Kantor79.commutatorSpace B) = 3 :=
    hsplitB.2.1
  have hdvd : Nat.card (movedGroup B) ∣
      Nat.card (HardMathSupport.Kantor79.commutatorSpace B ≃ₗ[ZMod 5]
        HardMathSupport.Kantor79.commutatorSpace B) :=
    Subgroup.card_subgroup_dvd_card (movedGroup B)
  have hprod : Nat.card (HardMathSupport.Kantor79.commutatorSpace B ≃ₗ[ZMod 5]
      HardMathSupport.Kantor79.commutatorSpace B) = ∏ i : Fin 3, ((5:ℕ)^3 - 5^(i:ℕ)) := by
    rw [CFSG.Quasithin.SteinbergBS.card_linearEquiv_eq_card_GL, hV3,
      Matrix.card_GL_field, ZMod.card]
  rw [hcard, hprod] at hdvd
  have hnot : ¬ (336 ∣ ∏ i : Fin 3, ((5:ℕ)^3 - 5^(i:ℕ))) := by
    rw [Fin.prod_univ_three]
    norm_num
  exact hnot hdvd

private theorem false_of_p_ge_eleven (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4) (h11 : 11 ≤ p)
    (hsplitB : SplitSupport B 3) (hdm : DMax p (movedGroup B) 4) : False := by
  obtain ⟨x, hxS, y, hyS, hxr, hyr, hxy⟩ :=
    exists_four_lt_orderOf_reflStab_aux hp hD h4 h11
  have hxB : x ∈ B := hD.split.2.2.2.2 hxS
  have hyB : y ∈ B := hD.split.2.2.2.2 hyS
  let V := HardMathSupport.Kantor79.commutatorSpace B
  let φ := restrictHom B V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  have hinj : Function.Injective φ := restrictHom_injective_of_splitSupport hsplitB
  have hx1 : (⟨x, hxB⟩ : B) ≠ 1 := by
    intro hone
    exact hxr.ne_one (Subtype.ext_iff.mp hone)
  have hy1 : (⟨y, hyB⟩ : B) ≠ 1 := by
    intro hone
    exact hyr.ne_one (Subtype.ext_iff.mp hone)
  have hxR : IsRefl p (φ ⟨x, hxB⟩) :=
    (isRefl_restrictHom_or_eq_one (X := B) (t := ⟨x, hxB⟩) hxr).resolve_right
      (fun hone => hx1 (hinj (by rw [hone, map_one])))
  have hyR : IsRefl p (φ ⟨y, hyB⟩) :=
    (isRefl_restrictHom_or_eq_one (X := B) (t := ⟨y, hyB⟩) hyr).resolve_right
      (fun hone => hy1 (hinj (by rw [hone, map_one])))
  have hxmem : φ ⟨x, hxB⟩ ∈ movedGroup B := MonoidHom.mem_range.mpr ⟨⟨x, hxB⟩, rfl⟩
  have hymem : φ ⟨y, hyB⟩ ∈ movedGroup B := MonoidHom.mem_range.mpr ⟨⟨y, hyB⟩, rfl⟩
  have hord : orderOf (φ ⟨x, hxB⟩ * φ ⟨y, hyB⟩) = orderOf (x * y) := by
    rw [← map_mul, orderOf_injective φ hinj]
    rw [← orderOf_injective B.subtype B.subtype_injective]
    rfl
  have hle := hdm.1 (φ ⟨x, hxB⟩) hxmem (φ ⟨y, hyB⟩) hymem hxR hyR
  omega

private theorem false_of_card_movedGroup_eq_336_aux (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4) (hp7 : p ≠ 7)
    (hcard : Nat.card (movedGroup B) = 336) (hdm : DMax p (movedGroup B) 4) : False := by
  have hsplitB : SplitSupport B 3 := by
    have h := hD.split.2.2.1
    rwa [h4] at h
  have hp3 : p ≠ 3 := by
    intro h3
    have h5 := hD.setting.five_le_of_eq_three h3
    omega
  by_cases hp5 : p = 5
  · subst p
    exact false_of_p_five hsplitB hcard
  · have h11 : 11 ≤ p := by
      by_contra hlt
      push Not at hlt
      have hp2le : 2 ≤ p := (Fact.out : p.Prime).two_le
      interval_cases p
      · exact hp rfl
      · exact hp3 rfl
      · exact absurd (Fact.out : Nat.Prime 4) (by norm_num)
      · exact hp5 rfl
      · exact absurd (Fact.out : Nat.Prime 6) (by norm_num)
      · exact hp7 rfl
      · exact absurd (Fact.out : Nat.Prime 8) (by norm_num)
      · exact absurd (Fact.out : Nat.Prime 9) (by norm_num)
      · exact absurd (Fact.out : Nat.Prime 10) (by norm_num)
    exact false_of_p_ge_eleven hp hD h4 h11 hsplitB hdm

theorem false_of_card_movedGroup_eq_336 (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4) (hp7 : p ≠ 7)
    (hcard : Nat.card (movedGroup B) = 336) (hdm : DMax p (movedGroup B) 4) : False :=
  false_of_card_movedGroup_eq_336_aux hp hD h4 hp7 hcard hdm

end CFSG.StandardType.ZS

end
