module

public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinusRank
public import CFSG.LieType.Universal.Spin.Twisted.Extras
public import CFSG.LieType.Universal.SpinOmega
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.LieType.Steinberg

namespace PsiDiag

@[expose] def scalarAct {G : Type*} [Group G] {k : Type*} [Field k] (y : k → G) : Subgroup G where
  carrier := {t | ∃ χ : kˣ, ∀ a, t * y a * t⁻¹ = y ((χ : k) * a)}
  one_mem' := ⟨1, fun a => by simp⟩
  mul_mem' := by
    rintro s t ⟨χs, hs⟩ ⟨χt, ht⟩
    refine ⟨χs * χt, fun a => ?_⟩
    calc s * t * y a * (s * t)⁻¹ = s * (t * y a * t⁻¹) * s⁻¹ := by group
      _ = y ((χs : k) * ((χt : k) * a)) := by rw [ht, hs]
      _ = y (((χs * χt : kˣ) : k) * a) := by rw [Units.val_mul, mul_assoc]
  inv_mem' := by
    rintro t ⟨χ, ht⟩
    refine ⟨χ⁻¹, fun a => ?_⟩
    have h := ht (((χ⁻¹ : kˣ) : k) * a)
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h
    rw [← h]
    group

theorem mem_scalarAct_iff {G : Type*} [Group G] {k : Type*} [Field k] {y : k → G} {t : G} :
    t ∈ scalarAct y ↔ ∃ χ : kˣ, ∀ a, t * y a * t⁻¹ = y ((χ : k) * a) :=
  Iff.rfl

namespace SpinM

variable {n : ℕ} {K : Type} [Field K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

@[expose] def DiagAct (g : spinGroup (quadMinus n K b c)) (χ : Fin (n - 1) → Kˣ) : Prop :=
  (∀ l, spinAction (quadMinus n K b c) g (minusVec n l true) = (χ l : K) • minusVec n l true) ∧
    (∀ l, spinAction (quadMinus n K b c) g (minusVec n l false) =
      (((χ l)⁻¹ : Kˣ) : K) • minusVec n l false) ∧
    ∀ p, spinAction (quadMinus n K b c) g (planeVec n p) = planeVec n p

theorem diagAct_one : DiagAct (1 : spinGroup (quadMinus n K b c)) 1 :=
  ⟨fun l => by simp, fun l => by simp, fun p => by simp⟩

theorem DiagAct.mul {g g' : spinGroup (quadMinus n K b c)} {χ χ' : Fin (n - 1) → Kˣ}
    (h : DiagAct g χ) (h' : DiagAct g' χ') : DiagAct (g * g') (χ * χ') := by
  refine ⟨fun l => ?_, fun l => ?_, fun p => ?_⟩
  · rw [map_mul, LinearEquiv.mul_apply, h'.1, map_smul, h.1, smul_smul, Pi.mul_apply,
      Units.val_mul, mul_comm]
  · rw [map_mul, LinearEquiv.mul_apply, h'.2.1, map_smul, h.2.1, smul_smul, Pi.mul_apply,
      mul_inv, Units.val_mul, mul_comm]
  · rw [map_mul, LinearEquiv.mul_apply, h'.2.2, h.2.2]

theorem DiagAct.congr {g : spinGroup (quadMinus n K b c)} {χ χ' : Fin (n - 1) → Kˣ}
    (h : DiagAct g χ) (hχ : χ = χ') : DiagAct g χ' :=
  hχ ▸ h

theorem diagAct_longTorus {j : Fin (n - 1)} (hj : j.val + 1 < n - 1) (τ : Kˣ) :
    DiagAct ((minusFrame n b c).longTorus (succ_ne_of_lt n hj) true false τ)
      (fun l => τ ^ longCoroot j ⟨j.val + 1, hj⟩ true false l true) := by
  refine ⟨fun l => ?_, fun l => spinAction_longTorus_minusVec_not n hj τ l,
    fun p => spinAction_longTorus_planeVec n (succ_ne_of_lt n hj) true false τ p⟩
  have h := (minusFrame n b c).spinAction_longTorus_vec (succ_ne_of_lt n hj) true false τ l true
  simpa only [minusFrame_vec] using h

theorem planeRefl_smul {ρ : K} (hρ : ρ ≠ 0) (a p : Fin 2 → K) :
    planeRefl b c (ρ • a) p = planeRefl b c a p := by
  rw [planeRefl, planeRefl, polarPlane_smul_right, planeNorm_smul, smul_smul]
  by_cases hN : planeNorm b c a = 0
  · rw [hN, mul_zero, div_zero, div_zero, zero_mul]
  · congr 2
    field_simp

theorem diagAct_shortTorusElt (k : Fin (n - 1)) (ρ : Kˣ) :
    DiagAct (shortTorusElt n hirr k ((ρ : K) • planeOne)) (Pi.mulSingle k (ρ ^ 2)) := by
  have ha : ((ρ : K) • planeOne : Fin 2 → K) ≠ 0 := smul_ne_zero ρ.ne_zero planeOne_ne_zero
  have hN : planeNorm b c ((ρ : K) • planeOne) = ((ρ ^ 2 : Kˣ) : K) := by
    rw [planeNorm_smul, planeNorm_planeOne, mul_one, Units.val_pow_eq_pow_val]
  refine ⟨fun l => ?_, fun l => ?_, fun p => ?_⟩
  · rw [spinAction_shortTorusElt_minusVec n hirr k ha l true, shortTorusScalar]
    by_cases hl : l = k
    · subst hl
      simp [hN]
    · simp [hl]
  · rw [spinAction_shortTorusElt_minusVec n hirr k ha l false, shortTorusScalar]
    by_cases hl : l = k
    · subst hl
      simp [hN]
    · simp [hl]
  · rw [spinAction_shortTorusElt_planeVec n hirr k ha, planeRefl_smul ρ.ne_zero,
      planeRefl_planeRefl planeNorm_planeOne_ne_zero]

theorem DiagAct.conj_long {g : spinGroup (quadMinus n K b c)} {χ : Fin (n - 1) → Kˣ}
    (h : DiagAct g χ) {i : Fin (n - 1)} (hi : i.val + 1 < n - 1) (a : K) :
    g * (minusFrame n b c).longRoot (succ_ne_of_lt n hi) true false (.ofAdd a) * g⁻¹ =
      (minusFrame n b c).longRoot (succ_ne_of_lt n hi) true false
        (.ofAdd ((χ i : K) * (((χ ⟨i.val + 1, hi⟩)⁻¹ : Kˣ) : K) * a)) :=
  (minusFrame n b c).conj_longRoot g (succ_ne_of_lt n hi) true false (succ_ne_of_lt n hi) true
    false (by simpa only [minusFrame_vec] using h.1 i)
    (by simpa only [minusFrame_vec] using h.2.1 ⟨i.val + 1, hi⟩) a

theorem DiagAct.conj_short {g : spinGroup (quadMinus n K b c)} {χ : Fin (n - 1) → Kˣ}
    (h : DiagAct g χ) (k : Fin (n - 1)) (t : ShortField b c) :
    g * shortX n hirr k t * g⁻¹ = shortX n hirr k (algebraMap K (ShortField b c) (χ k) * t) := by
  rw [shortX, shortX, fieldCoord_algebraMap_mul]
  exact conj_shortPosHom_of_eVec n hirr g k (h.1 k) (h.2.2 _)

theorem exists_sq_eq {k : Type*} [Field k] [Finite k] [CharP k 2] (r : kˣ) :
    ∃ ρ : kˣ, ρ ^ 2 = r := by
  have hsurj : Function.Surjective fun t : kˣ => t ^ (2 ^ 1) :=
    Finite.injective_iff_surjective.mp (pow_two_pow_injective (k := k) 1)
  obtain ⟨ρ, hρ⟩ := hsurj r
  exact ⟨ρ, by simpa using hρ⟩

variable [Finite K] [CharP K 2]

theorem exists_diagAct_mulSingle (m : Fin (n - 1)) (r : Kˣ) :
    ∃ g ∈ ⨆ j, minusTorus n hirr j, DiagAct g (Pi.mulSingle m r) := by
  suffices h : ∀ k : ℕ, ∀ m : Fin (n - 1), m.val + k = n - 2 → ∀ r : Kˣ,
      ∃ g ∈ ⨆ j, minusTorus n hirr j, DiagAct g (Pi.mulSingle m r) from
    h (n - 2 - m.val) m (by have := m.isLt; omega) r
  intro k
  induction k with
  | zero =>
    intro m hm r
    have hk : ¬ m.val + 1 < n - 1 := by omega
    obtain ⟨ρ, hρ⟩ := exists_sq_eq r
    refine ⟨_, Subgroup.mem_iSup_of_mem m ?_,
      (diagAct_shortTorusElt hirr m ρ).congr (by rw [hρ])⟩
    rw [minusTorus_of_not_lt n hirr hk]
    exact shortTorusElt_mem n hirr m (smul_ne_zero ρ.ne_zero planeOne_ne_zero)
  | succ k ih =>
    intro m hm r
    have hk : m.val + 1 < n - 1 := by omega
    obtain ⟨g, hg, hgd⟩ := ih ⟨m.val + 1, hk⟩ (by simp only; omega) r
    refine ⟨_, mul_mem (Subgroup.mem_iSup_of_mem m ?_) hg,
      ((diagAct_longTorus hk r).mul hgd).congr ?_⟩
    · rw [minusTorus_of_lt n hirr hk]
      exact ⟨r, rfl⟩
    · funext l
      have hne : (⟨m.val + 1, hk⟩ : Fin (n - 1)) ≠ m := (succ_ne_of_lt n hk).symm
      by_cases h1 : l = m
      · subst h1
        simp [longCoroot, hne.symm]
      · by_cases h2 : l = ⟨m.val + 1, hk⟩
        · subst h2
          simp [longCoroot, h1]
        · simp [longCoroot, h1, h2]

theorem exists_diagAct (χ : Fin (n - 1) → Kˣ) :
    ∃ g ∈ ⨆ j, minusTorus n hirr j, DiagAct g χ := by
  classical
  have h : ∀ S : Finset (Fin (n - 1)), ∃ g ∈ ⨆ j, minusTorus n hirr j,
      DiagAct g (∏ m ∈ S, Pi.mulSingle m (χ m)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, by rw [Finset.prod_empty]; exact diagAct_one⟩
    | insert m S hm ih =>
      obtain ⟨g, hg, hgd⟩ := ih
      obtain ⟨g', hg', hgd'⟩ := exists_diagAct_mulSingle hirr m (χ m)
      exact ⟨g' * g, mul_mem hg' hg, by rw [Finset.prod_insert hm]; exact hgd'.mul hgd⟩
  obtain ⟨g, hg, hgd⟩ := h Finset.univ
  exact ⟨g, hg, hgd.congr (Finset.univ_prod_mulSingle χ)⟩

omit [CharP K 2] in
theorem torus_le_scalarAct_long {i : Fin (n - 1)} (hi : i.val + 1 < n - 1) :
    ⨆ j, minusTorus n hirr j ≤ scalarAct (fun a : K =>
      (minusFrame n b c).longRoot (succ_ne_of_lt n hi) true false (.ofAdd a)) := by
  refine iSup_le fun j => ?_
  by_cases hj : j.val + 1 < n - 1
  · rw [minusTorus_of_lt n hirr hj]
    rintro _ ⟨τ, rfl⟩
    have h := diagAct_longTorus (b := b) (c := c) hj τ
    exact ⟨τ ^ longCoroot j ⟨j.val + 1, hj⟩ true false i true *
      (τ ^ longCoroot j ⟨j.val + 1, hj⟩ true false ⟨i.val + 1, hi⟩ true)⁻¹,
      fun a => by rw [h.conj_long hi a, Units.val_mul]⟩
  · rw [minusTorus_of_not_lt n hirr hj]
    intro g hg
    obtain ⟨a, ha, rfl⟩ := (mem_shortTorus_iff n hirr j).mp hg
    have hN : planeNorm b c a ≠ 0 := planeNorm_ne_zero hirr ha
    refine ⟨Units.mk0 (shortTorusScalar n b c j a i true *
      shortTorusScalar n b c j a ⟨i.val + 1, hi⟩ false) ?_, fun x => ?_⟩
    · refine mul_ne_zero ?_ ?_ <;> simp only [shortTorusScalar] <;> split_ifs <;> simp [hN]
    · rw [Units.val_mk0]
      exact shortTorusElt_conj_longRoot n hirr j ha (succ_ne_of_lt n hi) true false x

variable [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)]

omit [CharP K 2] in
theorem torus_le_scalarAct_short {k : Fin (n - 1)} (hk : ¬ k.val + 1 < n - 1) :
    ⨆ j, minusTorus n hirr j ≤ scalarAct (shortX n hirr k) := by
  refine iSup_le fun j => ?_
  by_cases hj : j.val + 1 < n - 1
  · rw [minusTorus_of_lt n hirr hj]
    rintro _ ⟨τ, rfl⟩
    have h := diagAct_longTorus (b := b) (c := c) hj τ
    exact ⟨Units.map (algebraMap K (ShortField b c)).toMonoidHom
      (τ ^ longCoroot j ⟨j.val + 1, hj⟩ true false k true),
      fun t => by rw [h.conj_short hirr k t]; rfl⟩
  · have hjk : j = k := Fin.ext (by have := j.isLt; have := k.isLt; omega)
    subst hjk
    rw [minusTorus_of_not_lt n hirr hj]
    intro g hg
    obtain ⟨a, ha, rfl⟩ := (mem_shortTorus_iff n hirr j).mp hg
    obtain ⟨t, ht, he⟩ := exists_shortRels_h_eq n hirr j ha
    refine ⟨Units.mk0 (t ^ 2) (pow_ne_zero 2 ht), fun s => ?_⟩
    rw [← he, Units.val_mk0]
    exact (shortRels n hirr j).h_conj_x ht s

omit [Finite K] [CharP K 2] [Fact (∀ r : K, r ^ 2 ≠ -c + b * r)] in
theorem prod_filter_le_succ (d : Fin (n - 1) → Kˣ) {i : Fin (n - 1)} (hi : i.val + 1 < n - 1) :
    ∏ j ∈ Finset.univ.filter (fun j : Fin (n - 1) => i.val ≤ j.val ∧ j.val + 1 < n - 1), d j =
      d i * ∏ j ∈ Finset.univ.filter
        (fun j : Fin (n - 1) => i.val + 1 ≤ j.val ∧ j.val + 1 < n - 1), d j := by
  rw [← Finset.prod_insert (s := Finset.univ.filter
    (fun j : Fin (n - 1) => i.val + 1 ≤ j.val ∧ j.val + 1 < n - 1)) (by simp)]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hji : j = i
    · exact Or.inl hji
    · have : j.val ≠ i.val := fun h => hji (Fin.ext h)
      exact Or.inr ⟨by omega, h2⟩
  · rintro (rfl | ⟨h1, h2⟩)
    · exact ⟨le_rfl, hi⟩
    · exact ⟨by omega, h2⟩

theorem exists_torus_conj {k : Fin (n - 1)} (hk : ¬ k.val + 1 < n - 1) (cl : Fin (n - 1) → Kˣ)
    (ν : (ShortField b c)ˣ) :
    ∃ t ∈ ⨆ j, minusTorus n hirr j,
      (∀ (i : Fin (n - 1)) (hi : i.val + 1 < n - 1) (a : K),
        t * (minusFrame n b c).longRoot (succ_ne_of_lt n hi) true false (.ofAdd a) * t⁻¹ =
          (minusFrame n b c).longRoot (succ_ne_of_lt n hi) true false (.ofAdd ((cl i : K) * a))) ∧
      ∀ s, t * shortX n hirr k s * t⁻¹ = shortX n hirr k ((ν : ShortField b c) * s) := by
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap (algebraMap K (ShortField b c)).injective 2
  have : Finite (ShortField b c) := finite_shortField
  obtain ⟨μ, hμ⟩ := exists_sq_eq ν
  have ha : fieldCoord (μ : ShortField b c) ≠ 0 := fieldCoord_ne_zero μ.ne_zero
  have hN : planeNorm b c (fieldCoord (μ : ShortField b c)) ≠ 0 := planeNorm_ne_zero hirr ha
  let d : Fin (n - 1) → Kˣ := fun i => cl i * (if i.val + 1 = k.val then Units.mk0 _ hN else 1)
  let χ : Fin (n - 1) → Kˣ := fun m =>
    ∏ i ∈ Finset.univ.filter (fun i : Fin (n - 1) => m.val ≤ i.val ∧ i.val + 1 < n - 1), d i
  obtain ⟨g, hg, hgd⟩ := exists_diagAct hirr χ
  have hkv : k.val + 1 = n - 1 := by have := k.isLt; omega
  refine ⟨shortTorusElt n hirr k (fieldCoord (μ : ShortField b c)) * g,
    mul_mem (Subgroup.mem_iSup_of_mem k ?_) hg, fun i hi x => ?_, fun s => ?_⟩
  · rw [minusTorus_of_not_lt n hirr hk]
    exact shortTorusElt_mem n hirr k ha
  · have hsuc : χ i = d i * χ ⟨i.val + 1, hi⟩ := prod_filter_le_succ d hi
    have hik : i ≠ k := fun h => hk (h ▸ hi)
    rw [show shortTorusElt n hirr k (fieldCoord (μ : ShortField b c)) * g *
        (minusFrame n b c).longRoot (succ_ne_of_lt n hi) true false (.ofAdd x) *
        (shortTorusElt n hirr k (fieldCoord (μ : ShortField b c)) * g)⁻¹ =
        shortTorusElt n hirr k (fieldCoord (μ : ShortField b c)) *
          (g * (minusFrame n b c).longRoot (succ_ne_of_lt n hi) true false (.ofAdd x) * g⁻¹) *
          (shortTorusElt n hirr k (fieldCoord (μ : ShortField b c)))⁻¹ by group,
      hgd.conj_long hi x, shortTorusElt_conj_longRoot n hirr k ha (succ_ne_of_lt n hi) true false]
    congr 2
    rw [hsuc]
    by_cases h1 : i.val + 1 = k.val
    · have h1' : (⟨i.val + 1, hi⟩ : Fin (n - 1)) = k := Fin.ext h1
      simp only [shortTorusScalar, d, ite_eq_right hik, ite_eq_left h1, h1', ite_true,
        Bool.false_eq_true, ite_false, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
      field_simp
    · have h1' : (⟨i.val + 1, hi⟩ : Fin (n - 1)) ≠ k := fun h => h1 (by rw [← h])
      simp only [shortTorusScalar, d, ite_eq_right hik, ite_eq_right h1, ite_eq_right h1', mul_one,
        Units.val_mul, Units.val_inv_eq_inv_val, one_mul]
      field_simp
  · have hχk : χ k = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      omega
    rw [show shortTorusElt n hirr k (fieldCoord (μ : ShortField b c)) * g * shortX n hirr k s *
        (shortTorusElt n hirr k (fieldCoord (μ : ShortField b c)) * g)⁻¹ =
        shortTorusElt n hirr k (fieldCoord (μ : ShortField b c)) *
          (g * shortX n hirr k s * g⁻¹) *
          (shortTorusElt n hirr k (fieldCoord (μ : ShortField b c)))⁻¹ by group,
      hgd.conj_short hirr k s, hχk, Units.val_one, map_one, one_mul, ← shortRels_h,
      ← hμ, Units.val_pow_eq_pow_val]
    exact (shortRels n hirr k).h_conj_x μ.ne_zero s

end SpinM

end PsiDiag

end CFSG.StandardType
