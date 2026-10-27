module

public import CFSG.Monster.B.TwoA.Census.XiFusion
public import CFSG.Monster.VisCert.FrameOrbit
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import CFSG.Monster.B.TwoA.Census.SymTrace
public meta import CFSG.Monster.B.TwoA.Census.XiFusion
public import CFSG.Monster.B.TwoA.Census.LatticeInvInputs
public import Certificates.Certificate3021
public import Certificates.Certificate3020
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  Matrix

theorem smul_frameDelta {u : GLV}
    (hu : u ∈ OLvis) {x : L2} (hx : x ∈ frameDelta) :
    u • x ∈ frameDelta :=
  (smul_mem_frameDelta_iff (Hvis_eq_OLvis ▸ hu)).2 hx

theorem exists_fixed_frame {u : GLV}
    (hu : u ∈ OLvis) (huu : u * u = 1) :
    ∃ x ∈ frameDelta, u • x = x := by
  classical
  have : Fintype frameDelta := Fintype.ofFinite _
  by_contra hno
  simp only [not_exists, not_and] at hno
  have hinv : ∀ x : L2, u • u • x = x := fun x => by rw [← mul_smul, huu, one_smul]
  let σ : Equiv.Perm frameDelta :=
    { toFun := fun x => ⟨u • x.1, smul_frameDelta hu x.2⟩
      invFun := fun x => ⟨u • x.1, smul_frameDelta hu x.2⟩
      left_inv := fun x => Subtype.ext (hinv x.1)
      right_inv := fun x => Subtype.ext (hinv x.1) }
  have hσ2 : σ ^ 2 = 1 := by
    ext x
    simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.coe_one, id_eq]
    exact congrArg Subtype.val (Subtype.ext (hinv x.1) : σ (σ x) = x)
  have hsupp : σ.support = Finset.univ := by
    ext x
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    intro h
    exact hno x.1 x.2 (congrArg Subtype.val h)
  have h2 := Equiv.Perm.two_dvd_card_support hσ2
  rw [hsupp, Finset.card_univ, Set.fintypeCard_eq_ncard,
    ncard_frameDelta] at h2
  omega

theorem exists_conj_mem_Nvis {u : GLV}
    (hu : u ∈ OLvis) (huu : u * u = 1) :
    ∃ k ∈ OLvis, k⁻¹ * u * k ∈ Nvis := by
  obtain ⟨x, hx, hux⟩ := exists_fixed_frame hu huu
  obtain ⟨k, hk, hkx⟩ := exists_Kvis_smul_twoΩCls hx
  rw [Kvis_eq_OLvis] at hk
  refine ⟨k, hk, ?_⟩
  have hv : k⁻¹ * u * k ∈ Hvis := by
    rw [Hvis_eq_OLvis]
    exact OLvis.mul_mem (OLvis.mul_mem (OLvis.inv_mem hk) hu) hk
  refine (Hvis_stab_iff _ hv).1 ?_
  rw [mul_smul, mul_smul, hkx, hux, ← hkx, inv_smul_smul]

theorem conj_mul_self_eq_one {G : Type*} [Group G] {u : G} (k : G) (huu : u * u = 1) :
    k⁻¹ * u * k * (k⁻¹ * u * k) = 1 := by
  calc k⁻¹ * u * k * (k⁻¹ * u * k) = k⁻¹ * (u * u) * k := by group
    _ = 1 := by rw [huu]; group

theorem exists_conj_monoN_OLvis
    {u : GLV} (hu : u ∈ OLvis) (huu : u * u = 1) (hu1 : u ≠ 1) :
    ∃ i, 1 ≤ i ∧ i < 7 ∧ ∃ g ∈ OLvis, g * monoN i * g⁻¹ = u := by
  obtain ⟨k, hk, hkN⟩ := exists_conj_mem_Nvis hu huu
  obtain ⟨i, hi, g, hg, hgi⟩ := exists_conj_monoN hkN (conj_mul_self_eq_one k huu)
  have hgO : g ∈ OLvis := by
    rw [← Hvis_eq_OLvis]
    exact Nvis_le_Hvis hg
  refine ⟨i, ?_, hi, k * g, OLvis.mul_mem hk hgO, ?_⟩
  · by_contra h
    have h0 : i = 0 := by omega
    subst h0
    rw [monoN_eq (by norm_num), monoPt_zero, map_one, mul_one, mul_inv_cancel] at hgi
    apply hu1
    calc u = k * (k⁻¹ * u * k) * k⁻¹ := by group
      _ = 1 := by rw [← hgi]; group
  · calc k * g * monoN i * (k * g)⁻¹ = k * (g * monoN i * g⁻¹) * k⁻¹ := by group
      _ = u := by rw [hgi]; group

theorem fusion_pairs :
    ∀ st ∈ [((1 : ℕ), (3 : ℕ)), (2, 5), (2, 4)],
    ∃ w ∈ OLvis, w * monoN st.1 * w⁻¹ = monoN st.2 := by
  intro st hst
  rw [← xiEdges_eq, List.mem_map] at hst
  obtain ⟨e, he, rfl⟩ := hst
  exact xiEdge_fusion he

theorem conj_trans {u : GLV} {a b : ℕ}
    (hab : ∃ w ∈ OLvis, w * monoN a * w⁻¹ = monoN b)
    (hu : ∃ g ∈ OLvis, g * monoN b * g⁻¹ = u) : ∃ g ∈ OLvis, g * monoN a * g⁻¹ = u := by
  obtain ⟨w, hw, hwab⟩ := hab
  obtain ⟨g, hg, rfl⟩ := hu
  refine ⟨g * w, OLvis.mul_mem hg hw, ?_⟩
  rw [← hwab]
  group

theorem exists_conj_three
    {u : GLV} (hu : u ∈ OLvis)
    (huu : u * u = 1) (hu1 : u ≠ 1) :
    ∃ i ∈ ({1, 2, 6} : Finset ℕ), ∃ g ∈ OLvis, g * monoN i * g⁻¹ = u := by
  obtain ⟨i, hi1, hi7, h⟩ := exists_conj_monoN_OLvis hu huu hu1
  have f13 := fusion_pairs (1, 3) (by simp)
  have f25 := fusion_pairs (2, 5) (by simp)
  have f24 := fusion_pairs (2, 4) (by simp)
  interval_cases i
  · exact ⟨1, by simp, h⟩
  · exact ⟨2, by simp, h⟩
  · exact ⟨1, by simp, conj_trans f13 h⟩
  · exact ⟨2, by simp, conj_trans f24 h⟩
  · exact ⟨2, by simp, conj_trans f25 h⟩
  · exact ⟨6, by simp, h⟩

theorem mat_inv (h : latticeO) : mat h⁻¹ * mat h = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem chiF_conj (g h : latticeO) : chiF (mat (h⁻¹ * g * h)) = chiF (mat g) := by
  have e1 : trace (mat (h⁻¹ * g * h)) = trace (mat g) := by
    rw [mat_mul, mat_mul, trace_mul_cycle, ← mat_mul, ← mat_mul, mul_inv_cancel, one_mul]
  have e2 : mat (h⁻¹ * g * h) * mat (h⁻¹ * g * h) = mat (h⁻¹ * (g * g) * h) := by
    rw [← mat_mul]
    congr 1
    group
  have e3 : trace (mat (h⁻¹ * (g * g) * h)) = trace (mat g * mat g) := by
    rw [mat_mul, mat_mul, trace_mul_cycle, ← mat_mul, ← mat_mul, mul_inv_cancel, one_mul,
      mat_mul]
  rw [chiF, chiF, e1, e2, e3]

theorem chiF_neg (g : latticeO) : chiF (mat (negOneO * g)) = chiF (mat g) := by
  rw [chiF, chiF, mat_mul, mat_negOneO, neg_one_mul, trace_neg, neg_mul_neg, neg_sq]

theorem chiF_values : chiF (dsgn 255 * pmatA (seedA 0)) = 43 ∧
    chiF (dsgn 212822 * pmatA (seedA 0)) = 11 ∧ chiF (dsgn 3346236 * pmatA (seedA 2)) = -13 :=
  Certificates.certificate3021.1

theorem chiF_monoA :
    chiF (mat (monoAO 1)) = 43 ∧ chiF
    (mat (monoAO 2)) = 11 ∧
    chiF (mat (monoAO 6)) = -13 := by
  rw [mat_monoAO_eq, mat_monoAO_eq, mat_monoAO_eq]
  exact chiF_values

theorem chiF_eq_of_conj {a b : ℕ}
    (h : ∃ g ∈ OLvis, g * monoN a * g⁻¹ = monoN b) :
    chiF (mat (monoAO a)) = chiF (mat (monoAO b)) := by
  obtain ⟨g, hg, hab⟩ := h
  obtain ⟨k, rfl⟩ := mem_OLvis.1 hg
  have e : modTwoUnit (k⁻¹ * monoAO a * k) = modTwoUnit (monoAO b) := by
    rw [modTwoUnit_mul, modTwoUnit_mul, modTwoUnit_inv, ← monoN, ← monoN, ← hab]
    group
  rcases (modTwoUnit_eq_modTwoUnit_iff _ _).1 e with h1 | h1
  · rw [← h1, chiF_conj]
  · rw [← chiF_neg (monoAO b), ← h1, chiF_conj]

theorem monoN_conj_three
    {i k : ℕ} (hi : i ∈ ({1, 2, 6} : Finset ℕ))
    (hk : k ∈ ({1, 2, 6} : Finset ℕ)) (h : ∃ g ∈ OLvis, g * monoN i * g⁻¹ = monoN k) :
    i = k := by
  have hc := chiF_eq_of_conj h
  obtain ⟨c1, c2, c6⟩ := chiF_monoA
  have hv : ∀ j ∈ ({1, 2, 6} : Finset ℕ),
      chiF (mat (monoAO j)) = ([0, 43, 11, 0, 0, 0, -13] : List ℚ).getD j 0 := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl
    · exact c1
    · exact c2
    · exact c6
  have hinj : ∀ a ∈ ({1, 2, 6} : Finset ℕ), ∀ b ∈ ({1, 2, 6} : Finset ℕ),
      ([0, 43, 11, 0, 0, 0, -13] : List ℚ).getD a 0 =
        ([0, 43, 11, 0, 0, 0, -13] : List ℚ).getD b 0 → a = b := by
    decide
  rw [hv i hi, hv k hk] at hc
  exact hinj i hi k hk hc

theorem monoA_sq_check :
    (dsgn 255 * pmatA (seedA 0)) * (dsgn 255 * pmatA (seedA 0)) = 1 ∧
    (dsgn 212822 * pmatA (seedA 0)) * (dsgn 212822 * pmatA (seedA 0)) = 1 ∧
    (dsgn 3346236 * pmatA (seedA 2)) * (dsgn 3346236 * pmatA (seedA 2)) = -1 :=
  Certificates.certificate3021.2

theorem monoA_eq
    (i : ℕ) :
    monoA i = dsgn (monoSign.getD i 0) * pmatA (seedA (monoSeed.getD i 0)) := by
  rw [← mat_monoAO, mat_monoAO_eq]

theorem trace_symQuotConj_monoA
    (i : ℕ) :
    LinearMap.trace ℚ _ (symQuotConj (monoA i) (monoA_mul_transpose i)) =
      chiF (mat (monoAO i)) := by
  rw [trace_symQuotConj, chiF, mat_monoAO]

theorem lattice_quotient_three_involution_classes :
    (∀ g : latticeO, modTwoUnit g = 1 ↔ g = 1 ∨ g = negOneO) ∧
    (∀ u : GLV, u ∈ OLvis ↔ ∃ g : latticeO, modTwoUnit g = u) ∧
    (∀ i ∈ ({1, 2, 6} : Finset ℕ), monoN i ∈ OLvis ∧ monoN i * monoN i = 1 ∧ monoN i ≠ 1) ∧
    (∀ u ∈ OLvis, u * u = 1 → u ≠ 1 →
      ∃ i ∈ ({1, 2, 6} : Finset ℕ), ∃ g ∈ OLvis, g * monoN i * g⁻¹ = u) ∧
    (∀ i ∈ ({1, 2, 6} : Finset ℕ), ∀ k ∈ ({1, 2, 6} : Finset ℕ),
      (∃ g ∈ OLvis, g * monoN i * g⁻¹ = monoN k) → i = k) ∧
    LinearMap.trace ℚ _ (symQuotConj (monoA 1) (monoA_mul_transpose 1)) = 43 ∧
    LinearMap.trace ℚ _ (symQuotConj (monoA 2) (monoA_mul_transpose 2)) = 11 ∧
    LinearMap.trace ℚ _ (symQuotConj (monoA 6) (monoA_mul_transpose 6)) = -13 ∧
    monoA 1 * monoA 1 = 1 ∧ monoA 2 * monoA 2 = 1 ∧ monoA 6 * monoA 6 = -1 := by
  obtain ⟨c1, c2, c6⟩ := chiF_monoA
  obtain ⟨s1, s2, s6⟩ := monoA_sq_check
  have hcl := monomial_involution_classes
  refine ⟨modTwoUnit_eq_one_iff, fun u => mem_OLvis, ?_, fun u hu huu hu1 =>
    exists_conj_three hu huu hu1, fun i hi k hk h => monoN_conj_three hi hk h,
    by rw [trace_symQuotConj_monoA, c1], by rw [trace_symQuotConj_monoA, c2],
    by rw [trace_symQuotConj_monoA, c6], by rw [monoA_eq]; exact s1, by rw [monoA_eq]; exact s2,
    by rw [monoA_eq]; exact s6⟩
  intro i hi
  have hi' : 1 ≤ i ∧ i < 7 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    omega
  obtain ⟨hne, hsq⟩ := hcl.2.2.2.2.2.2.1 i hi'.1 hi'.2
  exact ⟨modTwoUnit_mem_OLvis _, hsq, hne⟩

end CFSG.Monster.B.TwoA.Census
