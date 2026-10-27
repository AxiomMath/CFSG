module

public import CFSG.RankThree.PartTwo.Sec21.Item2131One
public import CFSG.RankThree.PartTwo.Sec21.Item211ResProofSplitCoord

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2130SplitProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.KP14
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def v4mat : Fin 4 → Mat3 :=
  ![1, !![2, 0, 0; 0, 1, 0; 0, 0, 2], !![2, 0, 0; 0, 2, 0; 0, 0, 1], !![1, 0, 0; 0, 2, 0; 0, 0, 2]]

@[expose] def diagFour : Set (GL (Fin 3) (ZMod 3)) :=
  {g | ∃ i, ((g : GL (Fin 3) (ZMod 3)) : Mat3) = v4mat i}

theorem diagFour_mats : ((1 : GL (Fin 3) (ZMod 3)) : Mat3) = v4mat 0 ∧
    ((d0 * d2 : GL (Fin 3) (ZMod 3)) : Mat3) = v4mat 1 ∧
    ((d0 * d1 : GL (Fin 3) (ZMod 3)) : Mat3) = v4mat 2 ∧
    ((d1 * d2 : GL (Fin 3) (ZMod 3)) : Mat3) = v4mat 3 := by
  decide +kernel

theorem mat_diagFour_conj : ∀ π : Fin 3 → Fin 3, Function.Bijective π →
    ∀ s : Fin 3 → ZMod 3, (∀ j, s j ≠ 0) →
      ∀ i : Fin 4, ∃ j : Fin 4, signedMat π s * v4mat i = v4mat j * signedMat π s := by
  decide +kernel

theorem conj_mem_diagFour {g y : GL (Fin 3) (ZMod 3)} (hg : g ∈ monomial) (hy : y ∈ diagFour) :
    g * y * g⁻¹ ∈ diagFour := by
  obtain ⟨i, hi⟩ := hy
  obtain ⟨j, hj⟩ : ∃ j, (g : Mat3) * v4mat i = v4mat j * g :=
    forall_mem_monomial (P := fun M => ∀ i : Fin 4, ∃ j : Fin 4, M * v4mat i = v4mat j * M)
      mat_diagFour_conj hg i
  refine ⟨j, ?_⟩
  rw [Units.val_mul, Units.val_mul, hi, hj, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.mul_one]

theorem diagFour_fix : ∀ v : Fin 3 → ZMod 3, v4mat 1 *ᵥ v = v → v4mat 2 *ᵥ v = v → v = 0 := by
  decide +kernel

theorem cyc_relations : (cyc⁻¹ * cyc' : GL (Fin 3) (ZMod 3)) = d0 * d2 ∧
    cyc * (d0 * d2) * cyc⁻¹ = d0 * d1 ∧ (d0 * d2) * (d0 * d2) = 1 ∧ (d0 * d1) * (d0 * d1) = 1 ∧
    (d0 * d2) * (d0 * d1) = d1 * d2 ∧ (d0 * d1) * (d0 * d2) = d1 * d2 := by
  decide +kernel

variable {G : Type} [Group G] {A B N : Subgroup G}

theorem M1_eq_map (f : Multiplicative (Fin 3 → ZMod 3) ≃* B) :
    M1 N f = (starOf B N).map (coordGL f) := by
  rw [M1, starOf, Subgroup.map_map]
  rfl

theorem SplitHyp.avg_fixed (h : SplitHyp A B N) {u x : G} (hu : u ∈ N)
    (hu2 : ∀ a ∈ A, (u * u) * a * (u * u)⁻¹ = a) (hx : x ∈ A) :
    u * (x * (u * x * u⁻¹)) * u⁻¹ = x * (u * x * u⁻¹) := by
  calc u * (x * (u * x * u⁻¹)) * u⁻¹ = (u * x * u⁻¹) * ((u * u) * x * (u * u)⁻¹) := by group
    _ = (u * x * u⁻¹) * x := by rw [hu2 x hx]
    _ = x * (u * x * u⁻¹) := h.comm (h.conjA hu hx) hx

theorem fixed_avg {u u' x : G} (hux : u' * x * u'⁻¹ = x)
    (hcomm : (u' * u) * x * (u' * u)⁻¹ = (u * u') * x * (u * u')⁻¹) :
    u' * (x * (u * x * u⁻¹)) * u'⁻¹ = x * (u * x * u⁻¹) := by
  calc u' * (x * (u * x * u⁻¹)) * u'⁻¹ = (u' * x * u'⁻¹) * ((u' * u) * x * (u' * u)⁻¹) := by group
    _ = x * ((u * u') * x * (u * u')⁻¹) := by rw [hux, hcomm]
    _ = x * (u * (u' * x * u'⁻¹) * u⁻¹) := by group
    _ = x * (u * x * u⁻¹) := by rw [hux]

theorem SplitHyp.avg_mod (h : SplitHyp A B N) {u x : G} (hu : u ∈ N) (hq : TrivQ A B u)
    (hx : x ∈ A) : x * (u * x * u⁻¹) * (x * x)⁻¹ ∈ B := by
  have e : x * (u * x * u⁻¹) * (x * x)⁻¹ = u * x * u⁻¹ * x⁻¹ := by
    rw [h.comm hx (h.conjA hu hx)]
    group
  rw [e]
  exact hq x hx

theorem SplitHyp.mul_mod (h : SplitHyp A B N) {x x' y y' : G} (hx' : x' ∈ A) (hy : y ∈ A)
    (hy' : y' ∈ A) (hxx : x * x'⁻¹ ∈ B) (hyy : y * y'⁻¹ ∈ B) : (x * y) * (x' * y')⁻¹ ∈ B := by
  have hyA : y * y'⁻¹ ∈ A := A.mul_mem hy (A.inv_mem hy')
  have e : (x * y) * (x' * y')⁻¹ = (x * x'⁻¹) * (y * y'⁻¹) := by
    calc (x * y) * (x' * y')⁻¹ = x * ((y * y'⁻¹) * x'⁻¹) := by group
      _ = x * (x'⁻¹ * (y * y'⁻¹)) := by rw [h.comm hyA (A.inv_mem hx')]
      _ = (x * x'⁻¹) * (y * y'⁻¹) := by group
  rw [e]
  exact B.mul_mem hxx hyy

theorem SplitHyp.concl_of_bloomCaseC [Finite G] (h : SplitHyp A B N)
    (f : Multiplicative (Fin 3 → ZMod 3) ≃* B)
    (hfB : ∀ w ∈ N, (∀ b ∈ B, w * b * w⁻¹ = b) → ∀ a ∈ A, w * a * w⁻¹ = a)
    (hC : Toolkit.BloomCaseC (M1 N f)) : SplitConcl A B N := by
  rw [M1_eq_map] at hC
  obtain ⟨f', hmono, G₀, hG₀S, ⟨e⟩⟩ := Item2131One.exists_of_bloomCaseC f hC
  rw [← M1_eq_map] at hmono
  set G₀' : Subgroup (GL (Fin 3) (ZMod 3)) := G₀.map (coordGL f') with hG₀'
  have hG₀'M : G₀' ≤ M1 N f' := by
    rw [M1_eq_map]
    exact Subgroup.map_mono hG₀S
  let e' : G₀' ≃* alternatingGroup (Fin 4) :=
    (G₀.equivMapOfInjective _ (coordGL_injective f')).symm.trans e
  have hcyc : cyc ∈ M1 N f' :=
    hG₀'M (mem_of_pow_three_eq_one (hG₀'M.trans hmono) e' cyc_mem_monomial cyc_pow_three)
  have hcyc' : cyc' ∈ M1 N f' :=
    hG₀'M (mem_of_pow_three_eq_one (hG₀'M.trans hmono) e' cyc'_mem_monomial cyc'_pow_three)
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := cyc_relations
  obtain ⟨n₁, hn₁, hm₁⟩ := h.exists_of_mem_M1 f' hcyc
  obtain ⟨n₂, hn₂, hm₂⟩ := h.exists_of_mem_M1 f' hcyc'
  have hq₁ : TrivQ A B n₁ := h.trivQ_of_matB_pow f' hfB hn₁ (j := 1) (by
    rw [hm₁]; exact cyc_pow_three)
  have hq₂ : TrivQ A B n₂ := h.trivQ_of_matB_pow f' hfB hn₂ (j := 1) (by
    rw [hm₂]; exact cyc'_pow_three)
  set u := n₁⁻¹ * n₂ with hu
  have huN : u ∈ N := N.mul_mem (N.inv_mem hn₁) hn₂
  set u' := n₁ * u * n₁⁻¹ with hu'
  have hu'N : u' ∈ N := N.mul_mem (N.mul_mem hn₁ huN) (N.inv_mem hn₁)
  have hqu : TrivQ A B u := h.trivQ_mul hn₂ (h.trivQ_inv hn₁ hq₁) hq₂
  have hqu' : TrivQ A B u' :=
    h.trivQ_mul (N.inv_mem hn₁) (h.trivQ_mul huN hq₁ hqu) (h.trivQ_inv hn₁ hq₁)
  have hmu : matB f' (h.nb huN) = d0 * d2 := by
    rw [show h.nb huN = (h.nb hn₁)⁻¹ * h.nb hn₂ from rfl, map_mul, map_inv, hm₁, hm₂, r1]
  have hmu' : matB f' (h.nb hu'N) = d0 * d1 := by
    rw [show h.nb hu'N = h.nb hn₁ * h.nb huN * (h.nb hn₁)⁻¹ from rfl, map_mul, map_mul, map_inv,
      hm₁, hmu, r2]
  have hsame : ∀ {r s : G} (hr : r ∈ N) (hs : s ∈ N), matB f' (h.nb hr) = matB f' (h.nb hs) →
      ∀ a ∈ A, r * a * r⁻¹ = s * a * s⁻¹ := fun hr hs he => h.conj_eq_of_matB_eq f' hfB hr hs he
  have huu : ∀ a ∈ A, (u * u) * a * (u * u)⁻¹ = a := by
    intro a ha
    have h1 := hsame (N.mul_mem huN huN) N.one_mem (by
      rw [show h.nb (N.mul_mem huN huN) = h.nb huN * h.nb huN from rfl, map_mul, hmu, r3,
        show h.nb N.one_mem = 1 from rfl, map_one]) a ha
    rw [h1]
    group
  have hu'u' : ∀ a ∈ A, (u' * u') * a * (u' * u')⁻¹ = a := by
    intro a ha
    have h1 := hsame (N.mul_mem hu'N hu'N) N.one_mem (by
      rw [show h.nb (N.mul_mem hu'N hu'N) = h.nb hu'N * h.nb hu'N from rfl, map_mul, hmu', r4,
        show h.nb N.one_mem = 1 from rfl, map_one]) a ha
    rw [h1]
    group
  have huu'N : u * u' ∈ N := N.mul_mem huN hu'N
  have hu'uN : u' * u ∈ N := N.mul_mem hu'N huN
  have hmuu' : matB f' (h.nb huu'N) = d1 * d2 := by
    rw [show h.nb huu'N = h.nb huN * h.nb hu'N from rfl, map_mul, hmu, hmu', r5]
  have hmu'u : matB f' (h.nb hu'uN) = d1 * d2 := by
    rw [show h.nb hu'uN = h.nb hu'N * h.nb huN from rfl, map_mul, hmu, hmu', r6]
  have hcomm : ∀ a ∈ A, (u' * u) * a * (u' * u)⁻¹ = (u * u') * a * (u * u')⁻¹ :=
    hsame hu'uN huu'N (hmu'u.trans hmuu'.symm)
  obtain ⟨c₀, hc₀A, hc₀B⟩ := h.exists_not_mem
  obtain ⟨c₁, hc₁⟩ : ∃ x, x = c₀ * (u * c₀ * u⁻¹) := ⟨_, rfl⟩
  have hc₁A : c₁ ∈ A := hc₁ ▸ A.mul_mem hc₀A (h.conjA huN hc₀A)
  obtain ⟨c, hc⟩ : ∃ x, x = c₁ * (u' * c₁ * u'⁻¹) := ⟨_, rfl⟩
  have hcA : c ∈ A := hc ▸ A.mul_mem hc₁A (h.conjA hu'N hc₁A)
  have hu'c : u' * c * u'⁻¹ = c := by rw [hc]; exact h.avg_fixed hu'N hu'u' hc₁A
  have huc₁ : u * c₁ * u⁻¹ = c₁ := by rw [hc₁]; exact h.avg_fixed huN huu hc₀A
  have huc : u * c * u⁻¹ = c := by
    rw [hc]
    exact fixed_avg huc₁ (hcomm c₁ hc₁A).symm
  have hcB : c ∉ B := by
    intro hcB
    have h1 : c * (c₁ * c₁)⁻¹ ∈ B := by rw [hc]; exact h.avg_mod hu'N hqu' hc₁A
    have h2 : c₁ * (c₀ * c₀)⁻¹ ∈ B := by rw [hc₁]; exact h.avg_mod huN hqu hc₀A
    have h3 : (c₁ * c₁) * ((c₀ * c₀) * (c₀ * c₀))⁻¹ ∈ B :=
      h.mul_mod (A.mul_mem hc₀A hc₀A) hc₁A (A.mul_mem hc₀A hc₀A) h2 h2
    have h4 : (c₀ * c₀) * (c₀ * c₀) = c₀ := by
      calc (c₀ * c₀) * (c₀ * c₀) = c₀ ^ 3 * c₀ := by rw [pow_three]; simp only [mul_assoc]
        _ = c₀ := by rw [h.cube hc₀A, one_mul]
    rw [h4] at h3
    have h5 : c * c₀⁻¹ ∈ B := by
      have := B.mul_mem h1 h3
      rwa [show c * (c₁ * c₁)⁻¹ * ((c₁ * c₁) * c₀⁻¹) = c * c₀⁻¹ by group] at this
    apply hc₀B
    have := B.mul_mem (B.inv_mem h5) hcB
    rwa [show (c * c₀⁻¹)⁻¹ * c = c₀ by group] at this
  refine h.concl_of_matSet f' diagFour ?_ ?_ hcA hcB ?_
  · intro m hm y hy
    exact conj_mem_diagFour (hmono (h.matB_mem_M1 f' hm)) hy
  · intro v hv
    obtain ⟨-, e2, e3, -⟩ := diagFour_mats
    refine diagFour_fix v ?_ ?_
    · rw [← e2, ← hmu]
      exact hv u huN (by rw [hmu]; exact ⟨1, e2⟩)
    · rw [← e3, ← hmu']
      exact hv u' hu'N (by rw [hmu']; exact ⟨2, e3⟩)
  · intro r hr hrY
    obtain ⟨e0, e1, e2, e3⟩ := diagFour_mats
    obtain ⟨i, hi⟩ := hrY
    fin_cases i
    · have hr1 : matB f' (h.nb hr) = 1 := Units.ext (hi.trans e0.symm)
      rw [hsame hr N.one_mem (by rw [hr1, show h.nb N.one_mem = 1 from rfl, map_one]) c hcA]
      group
    · have hr1 : matB f' (h.nb hr) = d0 * d2 := Units.ext (hi.trans e1.symm)
      rw [hsame hr huN (hr1.trans hmu.symm) c hcA, huc]
    · have hr1 : matB f' (h.nb hr) = d0 * d1 := Units.ext (hi.trans e2.symm)
      rw [hsame hr hu'N (hr1.trans hmu'.symm) c hcA, hu'c]
    · have hr1 : matB f' (h.nb hr) = d1 * d2 := Units.ext (hi.trans e3.symm)
      rw [hsame hr huu'N (hr1.trans hmuu'.symm) c hcA]
      calc (u * u') * c * (u * u')⁻¹ = u * (u' * c * u'⁻¹) * u⁻¹ := by group
        _ = c := by rw [hu'c, huc]

end CFSG.RankThree.PartTwo.Sec21.Item2130SplitProof
