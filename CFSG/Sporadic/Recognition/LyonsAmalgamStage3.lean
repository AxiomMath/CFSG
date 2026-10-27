module

public import CFSG.Sporadic.Recognition.LyonsAmalgamStage2
public import CFSG.Sporadic.Recognition.LyonsAmalgamLines
public import CFSG.Sporadic.Recognition.LyonsAmalgamExtOuter


public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

section Generic3

variable {G : Type*} [Group G]

theorem mem_TrN_of_conj [Finite G] {a b c g : G} (ha : g * a * g⁻¹ ∈ A3 a b c)
    (hb : g * b * g⁻¹ ∈ A3 a b c) (hc : g * c * g⁻¹ ∈ A3 a b c) : g ∈ TrN a b c := by
  refine McLAS.mem_normalizer_closure (S := ({a, b, c} : Set G)) fun e he => ?_
  have he' : e = a ∨ e = b ∨ e = c := by simpa using he
  rcases he' with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hc

theorem mem_normalizer_zpowers_of_conj [Finite G] {a g : G} (h : g * a * g⁻¹ ∈ zpowers a) :
    g ∈ normalizer (zpowers a : Set G) := by
  rw [zpowers_eq_closure]
  exact McLAS.mem_normalizer_closure fun s hs => by
    rw [Set.mem_singleton_iff] at hs
    subst hs
    simpa [zpowers_eq_closure] using h

end Generic3

section Main3

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

set_option maxRecDepth 100000 in
theorem iA_perm : ∀ m : Fin 48, ∃ σ : Perm (Fin 3), (σ 0).val = (iA m).1.val / 2 ∧
    (σ 1).val = (iA m).2.1.val / 2 ∧ (σ 2).val = (iA m).2.2.val / 2 := by decide

omit [Finite G] in
theorem e6H_mem (j : Fin 6) (i : Fin 3) (h : i.val = j.val / 2) :
    (e6H x₁ x₂ x₃ j : G) ∈ zpowers (![(x₁ : G), (x₂ : G), (x₃ : G)] i) := by
  fin_cases j <;> fin_cases i <;> simp at h ⊢ <;>
    first | exact mem_zpowers _ | exact inv_mem (mem_zpowers _)

omit [Finite G] in
theorem notMem_zpowers {u v : G} (hu : u ^ 3 = 1) (h1 : v ≠ 1) (h2 : v ≠ u) (h3 : v ≠ u⁻¹) :
    v ∉ zpowers u := fun h => by
  rcases mem_zpowers_cases hu h with h | h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h

omit [Finite G] in
theorem lineData_x (S : LyStd ρ x₁ x₂ x₃) : LineData ![(x₁ : G), (x₂ : G), (x₃ : G)] := by
  have hp1 : (x₁ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val S.pow₁
  have hp2 : (x₂ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val S.pow₂
  have hp3 : (x₃ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val S.pow₃
  have hn1 : (x₁ : G) ≠ 1 := fun h => by
    have := LyData.orderOf_x₁ S (G := G); rw [h, orderOf_one] at this; omega
  have hn2 : (x₂ : G) ≠ 1 := fun h => by
    have := LyData.orderOf_x₂ S (G := G); rw [h, orderOf_one] at this; omega
  have hn3 : (x₃ : G) ≠ 1 := fun h => by
    have := LyData.orderOf_x₃ S (G := G); rw [h, orderOf_one] at this; omega
  obtain ⟨e21, e21', e31, e31', e32, e32'⟩ := ne_of_e6H S (G := G)
  refine ⟨fun i => ?_, fun i => ?_, fun i j hji => ?_⟩
  · fin_cases i <;> simp [hp1, hp2, hp3]
  · fin_cases i <;> simp [hn1, hn2, hn3]
  · fin_cases i <;> fin_cases j <;> simp at hji ⊢
    · exact notMem_zpowers hp1 hn2 e21 e21'
    · exact notMem_zpowers hp1 hn3 e31 e31'
    · exact notMem_zpowers hp2 hn1 (fun h => e21 h.symm) (fun h => e21' (by rw [h]; simp))
    · exact notMem_zpowers hp2 hn3 e32 e32'
    · exact notMem_zpowers hp3 hn1 (fun h => e31 h.symm) (fun h => e31' (by rw [h]; simp))
    · exact notMem_zpowers hp3 hn2 (fun h => e32 h.symm) (fun h => e32' (by rw [h]; simp))

theorem LyData.exists_linePerm (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {n : G}
    (hn : n ∈ TrN (x₁ : G) (x₂ : G) (x₃ : G)) :
    ∃ σ : Perm (Fin 3), LinePerm ![(x₁ : G), (x₂ : G), (x₃ : G)] n σ := by
  obtain ⟨m, hm1, hm2, hm3⟩ := D.exists_pA_of_mem_normalizer S hn
  obtain ⟨σ, hσ0, hσ1, hσ2⟩ := iA_perm m
  refine ⟨σ, fun i => ?_⟩
  fin_cases i
  · show n * (x₁ : G) * n⁻¹ ∈ zpowers (![(x₁ : G), (x₂ : G), (x₃ : G)] (σ 0))
    rw [hm1]
    exact e6H_mem (x₁ := x₁) (x₂ := x₂) (x₃ := x₃) (iA m).1 (σ 0) hσ0
  · show n * (x₂ : G) * n⁻¹ ∈ zpowers (![(x₁ : G), (x₂ : G), (x₃ : G)] (σ 1))
    rw [hm2]
    exact e6H_mem (x₁ := x₁) (x₂ := x₂) (x₃ := x₃) (iA m).2.1 (σ 1) hσ1
  · show n * (x₃ : G) * n⁻¹ ∈ zpowers (![(x₁ : G), (x₂ : G), (x₃ : G)] (σ 2))
    rw [hm3]
    exact e6H_mem (x₁ := x₁) (x₂ := x₂) (x₃ := x₃) (iA m).2.2 (σ 2) hσ2

omit [Finite G] in
theorem surjective_of_swaps {Q : Type*} [Group Q] (π : Q →* Perm (Fin 3))
    (h01 : ∃ q, π q = swap 0 1) (h12 : ∃ q, π q = swap 1 2) : Function.Surjective π := by
  have hle : Submonoid.closure (Set.range fun i : Fin 2 => swap i.castSucc i.succ) ≤
      π.range.toSubmonoid := by
    rw [Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · obtain ⟨q, hq⟩ := h01
      exact ⟨q, by simpa using hq⟩
    · obtain ⟨q, hq⟩ := h12
      exact ⟨q, by simpa using hq⟩
  rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hle
  intro σ
  exact hle (Submonoid.mem_top σ)

theorem LyData.TrN_le_permutingLines (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    TrN (x₁ : G) (x₂ : G) (x₃ : G) ≤
      permutingLines ![(x₁ : G), (x₂ : G), (x₃ : G)] (lineData_x S) :=
  fun _ hn => D.exists_linePerm S hn

@[expose] noncomputable def LyData.trLines (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G)) →* Perm (Fin 3) :=
  (lineHom _ (lineData_x S)).comp (Subgroup.inclusion (D.TrN_le_permutingLines S))

theorem LyData.trLines_spec (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (n : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) :
    LinePerm ![(x₁ : G), (x₂ : G), (x₃ : G)] (n : G) (D.trLines S n) :=
  lineHom_spec (lineData_x S) (Subgroup.inclusion (D.TrN_le_permutingLines S) n)

theorem LyData.trLines_eq_of_linePerm (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (n : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) {σ : Perm (Fin 3)}
    (h : LinePerm ![(x₁ : G), (x₂ : G), (x₃ : G)] (n : G) σ) : D.trLines S n = σ :=
  (lineData_x S).linePerm_unique (D.trLines_spec S n) h

theorem LyData.trLines_eq_one_iff (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    (n : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) :
    D.trLines S n = 1 ↔ (n : G) ∈ KN (x₁ : G) (x₂ : G) (x₃ : G) := by
  constructor
  · intro h
    have h' := (lineHom_eq_one_iff (lineData_x S)
      (Subgroup.inclusion (D.TrN_le_permutingLines S) n)).1 h
    exact mem_KN_iff.2 ⟨mem_normalizer_zpowers_of_conj (by simpa using h' 0),
      mem_normalizer_zpowers_of_conj (by simpa using h' 1),
      mem_normalizer_zpowers_of_conj (by simpa using h' 2)⟩
  · intro h
    obtain ⟨ha, hb, hc⟩ := mem_KN_iff.1 h
    refine D.trLines_eq_of_linePerm S n (σ := 1) fun i => ?_
    fin_cases i
    · exact conj_mem_zpowers_of_mem_normalizer ha
    · exact conj_mem_zpowers_of_mem_normalizer hb
    · exact conj_mem_zpowers_of_mem_normalizer hc

omit [Finite G] in
theorem swap_zero_one_apply : (swap (0 : Fin 3) 1) 0 = 1 ∧ (swap (0 : Fin 3) 1) 1 = 0 ∧
    (swap (0 : Fin 3) 1) 2 = 2 := by decide

omit [Finite G] in
theorem swap_one_two_apply : (swap (1 : Fin 3) 2) 0 = 0 ∧ (swap (1 : Fin 3) 2) 1 = 2 ∧
    (swap (1 : Fin 3) 2) 2 = 1 := by decide

omit [Finite G] in
theorem perm_fix_zero : ∀ σ : Perm (Fin 3), σ 0 = 0 → σ = 1 ∨ σ = swap 1 2 := by decide

theorem LyData.trLines_surjective (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Function.Surjective (D.trLines S) := by
  obtain ⟨s, hs1, hs2, hs3, -⟩ := D.exists_swap S
  obtain ⟨u, hu2, hu3, hu1, -⟩ := D.exists_swap23 S
  have hs1G : (s : G) * (x₁ : G) * (s : G)⁻¹ = (x₂ : G) := by
    simpa using congrArg Subtype.val hs1
  have hs2G : (s : G) * (x₂ : G) * (s : G)⁻¹ = (x₁ : G) := by
    simpa using congrArg Subtype.val hs2
  have hs3G : (s : G) * (x₃ : G) * (s : G)⁻¹ = (x₃ : G) := by
    simpa using congrArg Subtype.val hs3
  have hu2G : (u : G) * (x₂ : G) * (u : G)⁻¹ = (x₃ : G) := by
    simpa using congrArg Subtype.val hu2
  have hu3G : (u : G) * (x₃ : G) * (u : G)⁻¹ = (x₂ : G) := by
    simpa using congrArg Subtype.val hu3
  have hu1G : (u : G) * (x₁ : G) * (u : G)⁻¹ = (x₁ : G) := by
    simpa using congrArg Subtype.val hu1
  have hsTr : (s : G) ∈ TrN (x₁ : G) (x₂ : G) (x₃ : G) := swap_mem_TrN hs1G hs2G hs3G
  have huTr : (u : G) ∈ TrN (x₁ : G) (x₂ : G) (x₃ : G) := by
    refine mem_TrN_of_conj ?_ ?_ ?_
    · rw [hu1G]; exact Subgroup.subset_closure (by simp)
    · rw [hu2G]; exact Subgroup.subset_closure (by simp)
    · rw [hu3G]; exact Subgroup.subset_closure (by simp)
  have hπs : D.trLines S ⟨(s : G), hsTr⟩ = swap 0 1 := by
    refine D.trLines_eq_of_linePerm S _ fun i => ?_
    obtain ⟨e0, e1, e2⟩ := swap_zero_one_apply
    fin_cases i
    · show (s : G) * (x₁ : G) * (s : G)⁻¹ ∈ zpowers (![(x₁ : G), (x₂ : G), (x₃ : G)] (swap 0 1 0))
      rw [e0, hs1G]; exact mem_zpowers _
    · show (s : G) * (x₂ : G) * (s : G)⁻¹ ∈ zpowers (![(x₁ : G), (x₂ : G), (x₃ : G)] (swap 0 1 1))
      rw [e1, hs2G]; exact mem_zpowers _
    · show (s : G) * (x₃ : G) * (s : G)⁻¹ ∈ zpowers (![(x₁ : G), (x₂ : G), (x₃ : G)] (swap 0 1 2))
      rw [e2, hs3G]; exact mem_zpowers _
  have hπu : D.trLines S ⟨(u : G), huTr⟩ = swap 1 2 := by
    refine D.trLines_eq_of_linePerm S _ fun i => ?_
    obtain ⟨e0, e1, e2⟩ := swap_one_two_apply
    fin_cases i
    · show (u : G) * (x₁ : G) * (u : G)⁻¹ ∈ zpowers (![(x₁ : G), (x₂ : G), (x₃ : G)] (swap 1 2 0))
      rw [e0, hu1G]; exact mem_zpowers _
    · show (u : G) * (x₂ : G) * (u : G)⁻¹ ∈ zpowers (![(x₁ : G), (x₂ : G), (x₃ : G)] (swap 1 2 1))
      rw [e1, hu2G]; exact mem_zpowers _
    · show (u : G) * (x₃ : G) * (u : G)⁻¹ ∈ zpowers (![(x₁ : G), (x₂ : G), (x₃ : G)] (swap 1 2 2))
      rw [e2, hu3G]; exact mem_zpowers _
  exact surjective_of_swaps _ ⟨⟨(s : G), hsTr⟩, hπs⟩ ⟨⟨(u : G), huTr⟩, hπu⟩

theorem LyData.exists_mulEquiv_Tr (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃)
    {Tr0 : Type*} [Group Tr0] (π₂ : Tr0 →* Perm (Fin 3)) (hZ0 : center π₂.ker = ⊥)
    (φT : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G)) →* Tr0) (hφinj : Function.Injective φT)
    (hker : ∀ x : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G)),
      φT x ∈ π₂.ker ↔ (x : G) ∈ KN (x₁ : G) (x₂ : G) (x₃ : G))
    (honto : ∀ y ∈ π₂.ker, ∃ x : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G)),
      (x : G) ∈ KN (x₁ : G) (x₂ : G) (x₃ : G) ∧ φT x = y)
    (hfix : ∀ x : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G)), π₂ (φT x) 0 = 0)
    {k : G} (hkTr : k ∈ TrN (x₁ : G) (x₂ : G) (x₃ : G))
    (hk1 : k * (x₁ : G) * k⁻¹ ∈ zpowers (x₂ : G)) (hk2 : k * (x₂ : G) * k⁻¹ ∈ zpowers (x₁ : G))
    (hk3 : k * (x₃ : G) * k⁻¹ ∈ zpowers (x₃ : G))
    (hkK : ∀ g ∈ KN (x₁ : G) (x₂ : G) (x₃ : G), k * g * k⁻¹ ∈ KN (x₁ : G) (x₂ : G) (x₃ : G))
    (k₀ : Tr0) (hk₀ : π₂ k₀ = swap 0 1)
    (hcompat : ∀ (g : G) (hg : g ∈ KN (x₁ : G) (x₂ : G) (x₃ : G)),
      k₀ * φT ⟨g, KN_le_TxN _ _ _ hg⟩ * k₀⁻¹ = φT ⟨k * g * k⁻¹, KN_le_TxN _ _ _ (hkK g hg)⟩) :
    ∃ ψ : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G)) ≃* Tr0,
      (∀ x : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G)), ψ ⟨(x : G), x.2.1⟩ = φT x) ∧
        ψ ⟨k, hkTr⟩ = k₀ := by
  classical
  obtain ⟨u, hu2, hu3, hu1, -⟩ := D.exists_swap23 S
  have hu2G : (u : G) * (x₂ : G) * (u : G)⁻¹ = (x₃ : G) := by
    simpa using congrArg Subtype.val hu2
  have hu3G : (u : G) * (x₃ : G) * (u : G)⁻¹ = (x₂ : G) := by
    simpa using congrArg Subtype.val hu3
  have hu1G : (u : G) * (x₁ : G) * (u : G)⁻¹ = (x₁ : G) := by
    simpa using congrArg Subtype.val hu1
  have huTr : (u : G) ∈ TrN (x₁ : G) (x₂ : G) (x₃ : G) := by
    refine mem_TrN_of_conj ?_ ?_ ?_
    · rw [hu1G]; exact Subgroup.subset_closure (by simp)
    · rw [hu2G]; exact Subgroup.subset_closure (by simp)
    · rw [hu3G]; exact Subgroup.subset_closure (by simp)
  have huN : (u : G) ∈ normalizer (zpowers (x₁ : G) : Set G) :=
    mem_normalizer_zpowers_of_conj (by rw [hu1G]; exact mem_zpowers _)
  have hπu : D.trLines S ⟨(u : G), huTr⟩ = swap 1 2 := by
    refine D.trLines_eq_of_linePerm S _ fun i => ?_
    obtain ⟨e0, e1, e2⟩ := swap_one_two_apply
    fin_cases i
    · show (u : G) * (x₁ : G) * (u : G)⁻¹ ∈ zpowers (![(x₁ : G), (x₂ : G), (x₃ : G)] (swap 1 2 0))
      rw [e0, hu1G]; exact mem_zpowers _
    · show (u : G) * (x₂ : G) * (u : G)⁻¹ ∈ zpowers (![(x₁ : G), (x₂ : G), (x₃ : G)] (swap 1 2 1))
      rw [e1, hu2G]; exact mem_zpowers _
    · show (u : G) * (x₃ : G) * (u : G)⁻¹ ∈ zpowers (![(x₁ : G), (x₂ : G), (x₃ : G)] (swap 1 2 2))
      rw [e2, hu3G]; exact mem_zpowers _
  have hπk : D.trLines S ⟨k, hkTr⟩ = swap 0 1 := by
    refine D.trLines_eq_of_linePerm S _ fun i => ?_
    obtain ⟨e0, e1, e2⟩ := swap_zero_one_apply
    fin_cases i
    · show k * (x₁ : G) * k⁻¹ ∈ zpowers (![(x₁ : G), (x₂ : G), (x₃ : G)] (swap 0 1 0))
      rw [e0]; exact hk1
    · show k * (x₂ : G) * k⁻¹ ∈ zpowers (![(x₁ : G), (x₂ : G), (x₃ : G)] (swap 0 1 1))
      rw [e1]; exact hk2
    · show k * (x₃ : G) * k⁻¹ ∈ zpowers (![(x₁ : G), (x₂ : G), (x₃ : G)] (swap 0 1 2))
      rw [e2]; exact hk3
  have hsurj : Function.Surjective (D.trLines S) :=
    surjective_of_swaps _ ⟨⟨k, hkTr⟩, hπk⟩ ⟨⟨(u : G), huTr⟩, hπu⟩
  have hkerπ : ∀ n : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G)),
      n ∈ (D.trLines S).ker ↔ (n : G) ∈ KN (x₁ : G) (x₂ : G) (x₃ : G) := fun n =>
    (MonoidHom.mem_ker).trans (D.trLines_eq_one_iff S n)
  have hxK : ∀ x : ↥(D.trLines S).ker,
      ((x : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) : G) ∈ KN (x₁ : G) (x₂ : G) (x₃ : G) :=
    fun x => (hkerπ _).1 x.2
  have hxT : ∀ x : ↥(D.trLines S).ker,
      ((x : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) : G) ∈ TxN (x₁ : G) (x₂ : G) (x₃ : G) :=
    fun x => KN_le_TxN _ _ _ (hxK x)
  let θ₀ : ↥(D.trLines S).ker →* ↥π₂.ker :=
    { toFun := fun x => ⟨φT ⟨((x : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) : G), hxT x⟩,
        (hker _).2 (hxK x)⟩
      map_one' := by
        apply Subtype.ext
        have : (⟨((1 : ↥(D.trLines S).ker) : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))).1, hxT 1⟩ :
            ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G))) = 1 := rfl
        simp only [this, map_one]
        rfl
      map_mul' := by
        intro x y
        apply Subtype.ext
        have : (⟨(((x * y : ↥(D.trLines S).ker) : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) : G),
            hxT (x * y)⟩ : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G))) =
            ⟨((x : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) : G), hxT x⟩ *
              ⟨((y : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) : G), hxT y⟩ := rfl
        simp only [this, map_mul]
        rfl }
  have hθ₀ : ∀ x : ↥(D.trLines S).ker, ((θ₀ x : ↥π₂.ker) : Tr0) =
      φT ⟨((x : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) : G), hxT x⟩ := fun x => rfl
  have hθinj : Function.Injective θ₀ := by
    intro x y hxy
    have := hφinj (congrArg Subtype.val hxy)
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G)) => (z : G)) this
  have hθsurj : Function.Surjective θ₀ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hxk, hx⟩ := honto y hy
    refine ⟨⟨⟨(x : G), x.2.1⟩, (hkerπ _).2 hxk⟩, Subtype.ext ?_⟩
    exact hx
  let θ : ↥(D.trLines S).ker ≃* ↥π₂.ker := MulEquiv.ofBijective θ₀ ⟨hθinj, hθsurj⟩
  have hθ : ∀ x : ↥(D.trLines S).ker, ((θ x : ↥π₂.ker) : Tr0) =
      φT ⟨((x : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) : G), hxT x⟩ := fun x => rfl
  have hZ1 : center (D.trLines S).ker = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hzc : θ z ∈ center ↥π₂.ker := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨v, rfl⟩ := θ.surjective w
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz v)]
    rw [hZ0, Subgroup.mem_bot] at hzc
    exact θ.injective (hzc.trans (map_one θ).symm)
  have hpT : ∀ (q : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G)))
      (hq : (q : G) ∈ normalizer (zpowers (x₁ : G) : Set G)),
      OuterActionPair (D.trLines S) π₂ θ q (φT ⟨(q : G), q.2, hq⟩) := by
    intro q hq
    let qT : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G)) := ⟨(q : G), q.2, hq⟩
    refine ⟨?_, ?_⟩
    · by_cases hqK : (q : G) ∈ KN (x₁ : G) (x₂ : G) (x₃ : G)
      · have h1 : D.trLines S q = 1 := (D.trLines_eq_one_iff S q).2 hqK
        have h2 : π₂ (φT qT) = 1 := MonoidHom.mem_ker.1 ((hker qT).2 hqK)
        rw [h1, h2]
      · have h1' : D.trLines S q ≠ 1 := fun h => hqK ((D.trLines_eq_one_iff S q).1 h)
        have h2' : π₂ (φT qT) ≠ 1 := fun h =>
          hqK ((hker qT).1 (MonoidHom.mem_ker.2 h))
        have hx1 : (x₁ : G) ≠ 1 := fun h => by
          have := LyData.orderOf_x₁ S (G := G); rw [h, orderOf_one] at this; omega
        have hne : (q : G) * (x₁ : G) * (q : G)⁻¹ ≠ 1 := fun h => hx1 (by
          calc (x₁ : G) = (q : G)⁻¹ * ((q : G) * (x₁ : G) * (q : G)⁻¹) * (q : G) := by group
            _ = 1 := by rw [h]; group)
        have hz : D.trLines S q 0 = 0 := by
          have h := D.trLines_spec S q 0
          have h' : (q : G) * (![(x₁ : G), (x₂ : G), (x₃ : G)] 0) * (q : G)⁻¹ ∈
              zpowers (![(x₁ : G), (x₂ : G), (x₃ : G)] 0) :=
            conj_mem_zpowers_of_mem_normalizer hq
          exact (lineData_x S).eq_of_mem hne h h'
        rcases perm_fix_zero _ hz with h | h
        · exact absurd h h1'
        · rcases perm_fix_zero _ (hfix qT) with h2 | h2
          · exact absurd h2 h2'
          · rw [h, h2]
    · intro x
      apply Subtype.ext
      let xT : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G)) :=
        ⟨((x : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) : G), hxT x⟩
      have hqx : (⟨(((MulAut.conjNormal q x : ↥(D.trLines S).ker) :
          ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) : G),
          hxT (MulAut.conjNormal q x)⟩ : ↥(TxN (x₁ : G) (x₂ : G) (x₃ : G))) =
          qT * xT * qT⁻¹ := by
        apply Subtype.ext
        simp [MulAut.conjNormal_apply, qT, xT]
      rw [MulAut.conjNormal_apply]
      change φT qT * ((θ x : ↥π₂.ker) : Tr0) * (φT qT)⁻¹ =
        ((θ (MulAut.conjNormal q x) : ↥π₂.ker) : Tr0)
      rw [hθ x, hθ, hqx, map_mul, map_mul, map_inv]
  have hpK : OuterActionPair (D.trLines S) π₂ θ ⟨k, hkTr⟩ k₀ := by
    refine ⟨?_, ?_⟩
    · rw [hk₀, hπk]
    · intro x
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      change k₀ * ((θ x : ↥π₂.ker) : Tr0) * k₀⁻¹ =
        ((θ (MulAut.conjNormal ⟨k, hkTr⟩ x) : ↥π₂.ker) : Tr0)
      rw [hθ x, hθ]
      exact hcompat ((x : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) : G) (hxK x)
  let Sgen : Set ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G)) :=
    {q | (q : G) ∈ normalizer (zpowers (x₁ : G) : Set G)} ∪ {⟨k, hkTr⟩}
  have hgen : Subgroup.closure Sgen = ⊤ := by
    have hkH : (⟨k, hkTr⟩ : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) ∈ Subgroup.closure Sgen :=
      Subgroup.subset_closure (Or.inr rfl)
    have huH : (⟨(u : G), huTr⟩ : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) ∈
        Subgroup.closure Sgen := Subgroup.subset_closure (Or.inl huN)
    have hsurjH : Function.Surjective
        ((D.trLines S).comp (Subgroup.closure Sgen).subtype) :=
      surjective_of_swaps _ ⟨⟨_, hkH⟩, hπk⟩ ⟨⟨_, huH⟩, hπu⟩
    rw [eq_top_iff]
    intro n _
    obtain ⟨h, hh⟩ := hsurjH (D.trLines S n)
    have hmem : (h : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G)))⁻¹ * n ∈ (D.trLines S).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have : D.trLines S (h : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G))) = D.trLines S n := hh
      rw [this]; group
    have hin : (h : ↥(TrN (x₁ : G) (x₂ : G) (x₃ : G)))⁻¹ * n ∈ Subgroup.closure Sgen :=
      Subgroup.subset_closure (Or.inl (mem_KN_iff.1 ((hkerπ _).1 hmem)).1)
    have := Subgroup.mul_mem _ h.2 hin
    simpa using this
  obtain ⟨ψ, hψθ, hψπ⟩ := exists_mulEquiv_of_outer_action_of_closure (D.trLines S) π₂ θ hsurj hZ1
    hZ0 hgen (fun q hq => by
      rcases hq with hq | hq
      · exact ⟨_, hpT q hq⟩
      · rw [Set.mem_singleton_iff] at hq
        subst hq
        exact ⟨k₀, hpK⟩)
  have hψpartner : ∀ q, OuterActionPair (D.trLines S) π₂ θ q (ψ q) :=
    OuterActionPair.of_hom (ψ := ψ.toMonoidHom) hψθ hψπ
  refine ⟨ψ, fun x => ?_, ?_⟩
  · exact OuterActionPair.unique hZ0 (hψpartner _) (hpT ⟨(x : G), x.2.1⟩ x.2.2)
  · exact OuterActionPair.unique hZ0 (hψpartner _) hpK

end Main3

end CFSG.Sporadic.Recognition.LyonsSims
