module

public import CFSG.Quasithin.H13.NQS1312M
public import CFSG.Quasithin.H13.U3Codim3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G] {V : Subgroup G} [IsElementaryAbelian 2 V]

@[expose] noncomputable def ptOf (Φ : Additive V ≃ₗ[ZMod 2] W6) (w : W6) : G :=
  ((Additive.toMul (Φ.symm w) : V) : G)

variable {Φ : Additive V ≃ₗ[ZMod 2] W6}

theorem ptOf_mem (w : W6) : ptOf Φ w ∈ V := (Additive.toMul (Φ.symm w)).2

theorem phi_ptOf (w : W6) : Φ (Additive.ofMul ⟨ptOf Φ w, ptOf_mem w⟩) = w := by
  change Φ (Additive.ofMul (Additive.toMul (Φ.symm w))) = w
  rw [ofMul_toMul, LinearEquiv.apply_symm_apply]

theorem eq_ptOf {x : G} (hx : x ∈ V) : x = ptOf Φ (Φ (Additive.ofMul ⟨x, hx⟩)) := by
  change x = ((Additive.toMul (Φ.symm (Φ (Additive.ofMul ⟨x, hx⟩))) : V) : G)
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem ptOf_injective {w w' : W6} (h : ptOf Φ w = ptOf Φ w') : w = w' := by
  rw [← phi_ptOf (Φ := Φ) w, ← phi_ptOf (Φ := Φ) w']
  congr 2
  exact Subtype.ext h

theorem ptOf_add (w w' : W6) : ptOf Φ (w + w') = ptOf Φ w * ptOf Φ w' := by
  change ((Additive.toMul (Φ.symm (w + w')) : V) : G) = _
  rw [map_add, toMul_add]
  rfl

theorem ptOf_zero : ptOf Φ (0 : W6) = 1 := by
  change ((Additive.toMul (Φ.symm 0) : V) : G) = 1
  rw [map_zero, toMul_zero]
  rfl

theorem conj_ptOf {n : G} (hn : n ∈ normalizer (V : Set G)) {k : GL (Fin 6) (ZMod 2)}
    (hk : linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hn⟩) = glLin k) (w : W6) :
    n * ptOf Φ w * n⁻¹ = ptOf Φ (glLin k w) := by
  have hx := ptOf_mem (Φ := Φ) w
  rw [eq_ptOf ((mem_normalizer_iff.1 hn _).1 hx), phi_conj hn hk hx, phi_ptOf]

theorem form_eq_b0
    {L : Subgroup G}
    (hLV : L ≤ normalizer (V : Set G))
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hLV hl⟩) = glLin j)
    (hV1 : V ≠ ⊥) {b : LinearMap.BilinForm (ZMod 2) (Additive V)} (hbn : b.Nondegenerate)
    (hbi : ∀ (n : normalizer (V : Set G)) (x y : Additive V),
      b (u3ConjLin V _ le_rfl n x) (u3ConjLin V _ le_rfl n y) = b x y) (x y : Additive V) :
    b x y = b0 (Φ x) (Φ y) := by
  set B : LinearMap.BilinForm (ZMod 2) W6 :=
    b.compl₁₂ (Φ.symm : W6 →ₗ[ZMod 2] Additive V) (Φ.symm : W6 →ₗ[ZMod 2] Additive V) with hB
  have hBapp : ∀ p q : W6, B p q = b (Φ.symm p) (Φ.symm q) := fun _ _ => rfl
  have hBinv : ∀ j ∈ J6, ∀ p q : W6, B (glLin j p) (glLin j q) = B p q := by
    intro j hj p q
    obtain ⟨l, hl, hlj⟩ := hΦLs j hj
    rw [hBapp, hBapp, ← hlj, linConj_apply, linConj_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, hbi]
  have hBne : B ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hV1
    have hx0 : Additive.ofMul a ≠ 0 := fun h => ha (by
      have := congrArg Additive.toMul h
      simpa using this)
    apply hx0
    refine hbn.1 _ fun y => ?_
    have := congrArg (fun C : LinearMap.BilinForm (ZMod 2) W6 =>
      C (Φ (Additive.ofMul a)) (Φ y)) h0
    simpa [hBapp] using this
  have hBb := bilin_eq_b0 B hBinv hBne
  have := congrArg (fun C : LinearMap.BilinForm (ZMod 2) W6 => C (Φ x) (Φ y)) hBb
  simpa [hBapp] using this

theorem eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

theorem exists_conj_line
    {L : Subgroup G}
    (hLV : L ≤ normalizer (V : Set G))
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hLV hl⟩) = glLin j)
    {u v : G} (hu : u ∈ V) (hv : v ∈ V)
    (huv : b0 (Φ (Additive.ofMul ⟨u, hu⟩)) (Φ (Additive.ofMul ⟨v, hv⟩)) ≠ 0) :
    ∃ l ∈ L, l * ptOf Φ (vecOf 15) * l⁻¹ = u ∧
      (l * ptOf Φ (vecOf 52) * l⁻¹ = v ∨ l * ptOf Φ (vecOf 52) * l⁻¹ = v * u) := by
  obtain ⟨j, hj, hj15, hj52⟩ := exists_J6_line (eq_one_of_ne_zero huv)
  obtain ⟨l, hl, hlj⟩ := hΦLs j hj
  refine ⟨l, hl, ?_, ?_⟩
  · rw [conj_ptOf (hLV hl) hlj, hj15, ← eq_ptOf hu]
  · rw [conj_ptOf (hLV hl) hlj]
    rcases hj52 with h | h
    · left
      rw [h, ← eq_ptOf hv]
    · right
      rw [h, ptOf_add, ← eq_ptOf hv, ← eq_ptOf hu]

theorem exists_k_mem_L {L : Subgroup G} (hLV : L ≤ normalizer (V : Set G))
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hLV hl⟩) = glLin j) :
    ∃ (k : G) (hk : k ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨k, hLV hk⟩) = glLin kGL ∧
      k * ptOf Φ (vecOf 15) * k⁻¹ = ptOf Φ (vecOf 15) ∧
        k * ptOf Φ (vecOf 52) * k⁻¹ = ptOf Φ (vecOf 52) := by
  obtain ⟨k, hk, hkj⟩ := hΦLs kGL kGL_mem_J6
  refine ⟨k, hk, hkj, ?_, ?_⟩
  · rw [conj_ptOf (hLV hk) hkj, glLin_vecOf_of_coe coe_kGL,
      ((kc_fix_iff 15 (by norm_num)).2 (by norm_num))]
  · rw [conj_ptOf (hLV hk) hkj, glLin_vecOf_of_coe coe_kGL,
      ((kc_fix_iff 52 (by norm_num)).2 (by norm_num))]

theorem exists_c6List_of_centralizes
    (hΦN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
      linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k)
    {n : G} (hn : n ∈ normalizer (V : Set G))
    (h15 : n * ptOf Φ (vecOf 15) * n⁻¹ = ptOf Φ (vecOf 15))
    (h52 : n * ptOf Φ (vecOf 52) * n⁻¹ = ptOf Φ (vecOf 52)) :
    ∃ k ∈ N6, linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hn⟩) = glLin k ∧
      ∃ e ∈ c6List, (k : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e := by
  obtain ⟨k, hk, hkn⟩ := hΦN ⟨n, hn⟩
  refine ⟨k, hk, hkn, exists_c6List_of_fix hk ?_ ?_⟩
  · rw [conj_ptOf hn hkn] at h15
    exact ptOf_injective h15
  · rw [conj_ptOf hn hkn] at h52
    exact ptOf_injective h52

end CFSG.Quasithin.H13.U3.NLine
