module

public import CFSG.LocalAnalysis.SteinbergBQA7RepeatedTransvectionCenter
public import CFSG.Quasithin.SteinbergCGA7TreeReduction
public import CFSG.Quasithin.SteinbergBNA7PathModule
public import CFSG.Quasithin.SteinbergBNA7E6Word

public section

namespace CFSG.Quasithin.SteinbergBN

open Module CFSG.LocalAnalysis.SteinbergBV

namespace NoThreeS3

section Factors

variable {G : Type*} [Group G]

theorem exists_injective_of_factors (L : Fin 3 → Subgroup G)
    (hiso : ∀ i, Nonempty (L i ≃* Equiv.Perm (Fin 3)))
    (hcomm : ∀ i j, i ≠ j → ∀ g ∈ L i, ∀ h ∈ L j, g * h = h * g)
    (hind : ∀ g₀ ∈ L 0, ∀ g₁ ∈ L 1, ∀ g₂ ∈ L 2, g₀ * g₁ * g₂ = 1 → g₀ = 1 ∧ g₁ = 1 ∧ g₂ = 1) :
    ∃ χ : (Fin 3 → Equiv.Perm (Fin 3)) →* G, Function.Injective χ ∧
      ∀ σ, χ σ ∈ L 0 ⊔ L 1 ⊔ L 2 := by
  obtain ⟨e0⟩ := hiso 0
  obtain ⟨e1⟩ := hiso 1
  obtain ⟨e2⟩ := hiso 2
  let φ0 : Equiv.Perm (Fin 3) →* G := (L 0).subtype.comp e0.symm.toMonoidHom
  let φ1 : Equiv.Perm (Fin 3) →* G := (L 1).subtype.comp e1.symm.toMonoidHom
  let φ2 : Equiv.Perm (Fin 3) →* G := (L 2).subtype.comp e2.symm.toMonoidHom
  have hφ0 : ∀ a, φ0 a ∈ L 0 := fun a => (e0.symm a).2
  have hφ1 : ∀ a, φ1 a ∈ L 1 := fun a => (e1.symm a).2
  have hφ2 : ∀ a, φ2 a ∈ L 2 := fun a => (e2.symm a).2
  have c01 : ∀ a b, Commute (φ0 a) (φ1 b) := fun a b =>
    hcomm 0 1 (by decide) _ (hφ0 a) _ (hφ1 b)
  have c02 : ∀ a b, Commute (φ0 a) (φ2 b) := fun a b =>
    hcomm 0 2 (by decide) _ (hφ0 a) _ (hφ2 b)
  have c12 : ∀ a b, Commute (φ1 a) (φ2 b) := fun a b =>
    hcomm 1 2 (by decide) _ (hφ1 a) _ (hφ2 b)
  let g := (φ0.noncommCoprod φ1 c01).noncommCoprod φ2 fun p c =>
    (c02 p.1 c).mul_left (c12 p.2 c)
  let split : (Fin 3 → Equiv.Perm (Fin 3)) →*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) × Equiv.Perm (Fin 3) :=
    ((Pi.evalMonoidHom _ 0).prod (Pi.evalMonoidHom _ 1)).prod (Pi.evalMonoidHom _ 2)
  have hχ : ∀ σ, (g.comp split) σ = φ0 (σ 0) * φ1 (σ 1) * φ2 (σ 2) := fun σ => rfl
  refine ⟨g.comp split, ?_, fun σ => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro σ hσ
    rw [hχ] at hσ
    obtain ⟨h0, h1, h2⟩ := hind _ (hφ0 _) _ (hφ1 _) _ (hφ2 _) hσ
    have i0 : σ 0 = 1 := e0.symm.map_eq_one_iff.1 (Subtype.ext h0)
    have i1 : σ 1 = 1 := e1.symm.map_eq_one_iff.1 (Subtype.ext h1)
    have i2 : σ 2 = 1 := e2.symm.map_eq_one_iff.1 (Subtype.ext h2)
    funext k
    fin_cases k <;> simp [i0, i1, i2]
  · rw [hχ]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left (hφ0 _)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (hφ1 _)))) (Subgroup.mem_sup_right (hφ2 _))

theorem false_of_injective {N : Subgroup G}
    (hS3 : ∀ H ≤ N, IsEmpty (H ≃* (Fin 3 → Equiv.Perm (Fin 3))))
    {χ : (Fin 3 → Equiv.Perm (Fin 3)) →* G} (hχ : Function.Injective χ) (hle : χ.range ≤ N) :
    False :=
  (hS3 _ hle).false (MonoidHom.ofInjective hχ).symm

end Factors

section Six

@[expose] def sixMat : Matrix (Fin 6) (Fin 6) (ZMod 2) := fun i j =>
  if (i : ℕ) / 2 = (j : ℕ) / 2 ∧ i ≠ j then 1 else 0

theorem sixMat_self : ∀ x : Fin 6 → ZMod 2, ∑ i, ∑ j, x i * sixMat i j * x j = 0 := by
  decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem exists_injective_of_six_le_finrank (h6 : 6 ≤ finrank (ZMod 2) V) :
    ∃ χ : (Fin 3 → Equiv.Perm (Fin 3)) →* LinearMap.GeneralLinearGroup (ZMod 2) V,
      Function.Injective χ := by
  classical
  let b := Module.finBasis (ZMod 2) V
  let idx : Fin 6 → Fin (finrank (ZMod 2) V) := Fin.castLE h6
  let π : V →ₗ[ZMod 2] (Fin 6 → ZMod 2) := LinearMap.pi fun j => b.coord (idx j)
  let β : LinearMap.BilinForm (ZMod 2) V := (Matrix.toBilin' sixMat).compl₁₂ π π
  have hβapp : ∀ x y, β x y = Matrix.toBilin' sixMat (π x) (π y) := fun x y => rfl
  have hβ : β.IsAlt := fun x => by
    rw [hβapp, Matrix.toBilin'_apply]
    exact sixMat_self (π x)
  have hπ : ∀ j, π (b (idx j)) = Pi.single j 1 := by
    intro j
    funext k
    by_cases hkj : k = j
    · subst hkj
      simp [π]
    · have hne : idx j ≠ idx k := fun h => hkj (Fin.castLE_injective h6 h).symm
      simp [π, hkj, hne]
  have hpair : ∀ j k, β (b (idx j)) (b (idx k)) = sixMat j k := by
    intro j k
    rw [hβapp, hπ, hπ, Matrix.toBilin'_single]
  let pai : Fin 3 → Fin 6 := ![0, 2, 4]
  let pbi : Fin 3 → Fin 6 := ![1, 3, 5]
  let pa : Fin 3 → V := fun i => b (idx (pai i))
  let pb : Fin 3 → V := fun i => b (idx (pbi i))
  have h1 : ∀ i, β (pa i) (pb i) = 1 := by
    intro i
    simp only [pa, pb, hpair]
    revert i
    decide
  have h2 : ∀ i j, i ≠ j → β (pa i) (pa j) = 0 ∧ β (pa i) (pb j) = 0 ∧ β (pb i) (pa j) = 0 ∧
      β (pb i) (pb j) = 0 := by
    intro i j
    simp only [pa, pb, hpair]
    revert i j
    decide
  let W : Submodule (ZMod 2) V := LinearMap.ker π
  have hW : ∀ i, ∀ x ∈ W, β (pa i) x = 0 ∧ β (pb i) x = 0 := by
    intro i x hx
    have hx' : π x = 0 := hx
    rw [hβapp, hβapp, hx', map_zero, map_zero]
    exact ⟨rfl, rfl⟩
  have hmem : ∀ j, b (idx j) ∈ Submodule.span (ZMod 2) (Set.range pa ∪ Set.range pb) := by
    intro j
    apply Submodule.subset_span
    fin_cases j
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inr ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inr ⟨2, rfl⟩
  have hspan : Submodule.span (ZMod 2) (Set.range pa ∪ Set.range pb) ⊔ W = ⊤ := by
    rw [eq_top_iff]
    intro x _
    let y := ∑ j : Fin 6, π x j • b (idx j)
    have hyS : y ∈ Submodule.span (ZMod 2) (Set.range pa ∪ Set.range pb) :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem j)
    have hpy : π y = π x := by
      simp only [y, map_sum, map_smul, hπ]
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    have hxy : x - y ∈ W := by
      change π (x - y) = 0
      rw [map_sub, hpy]
      exact sub_self _
    exact Submodule.mem_sup.2 ⟨y, hyS, x - y, hxy, by abel⟩
  let e := MulEquiv.ofBijective (prodHom hβ h1 h2)
    ⟨prodHom_injective hβ h1 h2 W hspan hW, prodHom_surjective hβ h1 h2⟩
  exact ⟨(prodGroup hβ pa pb).subtype.comp e.symm.toMonoidHom,
    (prodGroup hβ pa pb).subtype_injective.comp e.symm.injective⟩

end Six

section Center

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}

theorem eq_transv_of_mem_isometryGroup (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    {n : LinearMap.GeneralLinearGroup (ZMod 2) V} (hn : n ∈ isometryGroup β) {u : V}
    {f : Dual (ZMod 2) V} (hu : u ≠ 0) (hf : f ≠ 0)
    (hnf : (n : Module.End (ZMod 2) V) = LinearMap.id + f.smulRight u) :
    n = transv hβ u := by
  have hnx : ∀ x, (n : V →ₗ[ZMod 2] V) x = x + f x • u := fun x => by
    rw [hnf]
    rfl
  obtain ⟨y, hy⟩ := BinaryTransvection.exists_eq_one_of_ne_zero hf
  have hker : ∀ x, f x = 0 → β u x = 0 := by
    intro x hx
    have h := mem_isometryGroup.1 hn x y
    rw [hnx, hnx, hx, hy, zero_smul, add_zero, one_smul, map_add, add_eq_left] at h
    rw [isAlt_apply_comm hβ]
    exact h
  obtain ⟨z, hz⟩ : ∃ z, β u z = 1 := by
    by_contra h
    push Not at h
    exact hu (hnd.1 u fun z => zmod_two_eq_zero_of_ne_one (h z))
  have hfz : f z = 1 := by
    by_contra h
    have h' := hker z (zmod_two_eq_zero_of_ne_one h)
    rw [hz] at h'
    exact one_ne_zero h'
  have hfeq : ∀ x, f x = β u x := by
    intro x
    rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (f x) with h | h
    · rw [h, hker x h]
    · have h' : f (x + z) = 0 := by
        rw [map_add, h, hfz]
        rfl
      have h'' := hker _ h'
      rw [map_add, hz] at h''
      rw [h, (show ∀ c : ZMod 2, c + 1 = 0 → c = 1 by decide) _ h'']
  refine Units.ext (LinearMap.ext fun x => ?_)
  rw [transv_apply, ← hfeq]
  exact hnx x

end Center

end NoThreeS3

open NoThreeS3 in
theorem no_three_S3_binary_transvection_group_linear_or_deleted_symmetric {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (hV : 2 ≤ finrank (ZMod 2) V) (N : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V))
    (hirr : ∀ U : Submodule (ZMod 2) V,
      (∀ n ∈ N, ∀ u ∈ U, (n : Module.End (ZMod 2) V) u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hgen : N = Subgroup.closure {n | n ∈ N ∧ IsBinaryTransvection n})
    (hS3 : ∀ H ≤ N, IsEmpty (H ≃* (Fin 3 → Equiv.Perm (Fin 3)))) :
    (N = ⊤ ∧ 2 ≤ finrank (ZMod 2) V ∧ finrank (ZMod 2) V ≤ 5) ∨
      ∃ m ∈ ({3, 5, 6, 7, 8} : Finset ℕ), ∃ (ψ : Equiv.Perm (Fin m) ≃* N)
        (f : V ≃ₗ[ZMod 2] deletedW m),
        (∀ σ v, f (((ψ σ : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v) =
          (wRep m σ : deletedW m →ₗ[ZMod 2] deletedW m) (f v)) ∧
        (N ≠ ⊤ → (∃! β : LinearMap.BilinForm (ZMod 2) V, β.IsAlt ∧ β.Nondegenerate ∧
            N ≤ isometryGroup β) ∧
          ∀ β : LinearMap.BilinForm (ZMod 2) V, β.IsAlt → β.Nondegenerate →
            N ≤ isometryGroup β → ∀ x y, wForm m (f x) (f y) = β x y) := by
  classical
  have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hfinV : Finite V := Module.finite_of_finite (ZMod 2)
  by_cases hN : N = ⊤
  · left
    refine ⟨hN, hV, ?_⟩
    by_contra h6
    obtain ⟨χ, hχ⟩ := exists_injective_of_six_le_finrank (V := V) (by omega)
    exact false_of_injective hS3 hχ (by rw [hN]; exact le_top)
  right
  obtain ⟨β, ⟨hβ, hnd, hNβ⟩, huniq⟩ :=
    (CFSG.LocalAnalysis.repeated_transvection_center_forces_full_binary_linear_group hV N hirr
      hgen).2 hN
  let I := {u : V // u ≠ 0 ∧ transv hβ u ∈ N}
  let a : I → V := Subtype.val
  have ha0 : ∀ i, a i ≠ 0 := fun i => i.2.1
  have hgenI : N = Subgroup.closure (Set.range fun i => transv hβ (a i)) := by
    apply le_antisymm
    · refine hgen.le.trans (Subgroup.closure_mono ?_)
      rintro n ⟨hnN, u, f, hu, hf, -, hnf⟩
      have hn := eq_transv_of_mem_isometryGroup hβ hnd (hNβ hnN) hu hf hnf
      exact ⟨⟨u, hu, hn ▸ hnN⟩, hn.symm⟩
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact i.2.2
  have hNbot : N ≠ ⊥ := by
    intro hbot
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    rcases hirr (Submodule.span (ZMod 2) {v}) (fun n hn u hu => by
      rw [hbot, Subgroup.mem_bot] at hn
      rw [hn]
      exact hu) with h | h
    · exact hv (Submodule.span_singleton_eq_bot.1 h)
    · have h1 := finrank_span_singleton (K := ZMod 2) hv
      rw [h, finrank_top] at h1
      omega
  obtain ⟨i₀⟩ : Nonempty I := by
    by_contra hI
    apply hNbot
    rw [hgenI, Set.range_eq_empty_iff.2 (not_nonempty_iff.1 hI), Subgroup.closure_empty]
  have hconjI : ∀ n ∈ N, ∀ i : I, ∃ j : I, a j = (n : V →ₗ[ZMod 2] V) (a i) := by
    intro n hn i
    refine ⟨⟨(n : V →ₗ[ZMod 2] V) (a i), fun h0 => ?_, ?_⟩, rfl⟩
    · apply ha0 i
      have h := gl_inv_apply_apply n (a i)
      rw [h0, map_zero] at h
      exact h.symm
    · rw [← conj_transv hβ (hNβ hn)]
      exact mul_mem (mul_mem hn i.2.2) (inv_mem hn)
  have hspan : Submodule.span (ZMod 2) (Set.range a) = ⊤ := by
    have hinv : ∀ n ∈ N, ∀ x ∈ Submodule.span (ZMod 2) (Set.range a),
        (n : Module.End (ZMod 2) V) x ∈ Submodule.span (ZMod 2) (Set.range a) := by
      intro n hn x hx
      have hx' : (n : Module.End (ZMod 2) V) x ∈
          (Submodule.span (ZMod 2) (Set.range a)).map (n : Module.End (ZMod 2) V) :=
        Submodule.mem_map_of_mem hx
      rw [Submodule.map_span] at hx'
      refine Submodule.span_mono ?_ hx'
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact hconjI n hn i
    rcases hirr _ hinv with h | h
    · exfalso
      have h0 : a i₀ ∈ Submodule.span (ZMod 2) (Set.range a) := Submodule.subset_span ⟨i₀, rfl⟩
      rw [h, Submodule.mem_bot] at h0
      exact ha0 i₀ h0
    · exact h
  have hinvN : ∀ U : Submodule (ZMod 2) V,
      (∀ i, ∀ x ∈ U, (transv hβ (a i) : V →ₗ[ZMod 2] V) x ∈ U) →
      ∀ n ∈ N, ∀ x ∈ U, (n : Module.End (ZMod 2) V) x ∈ U := by
    intro U hU n hn
    rw [hgenI] at hn
    induction hn using Subgroup.closure_induction'' with
    | mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      exact hU i
    | inv_mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      rw [transv_inv]
      exact hU i
    | one => exact fun x hx => hx
    | mul g h _ _ hg hh => exact fun x hx => hg _ (hh x hx)
  have hconn : (pairGraph hβ a).Connected := by
    rw [SimpleGraph.connected_iff]
    refine ⟨fun i j => ?_, ⟨i₀⟩⟩
    by_contra hij
    let C : Set I := {k | (pairGraph hβ a).Reachable i k}
    let U := Submodule.span (ZMod 2) (a '' C)
    have horth : ∀ k, k ∉ C → ∀ x ∈ U, β (a k) x = 0 := by
      intro k hk x hx
      have hle : U ≤ LinearMap.ker (β (a k)) := by
        rw [Submodule.span_le]
        rintro _ ⟨l, hl, rfl⟩
        have hl' : (pairGraph hβ a).Reachable i l := hl
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        apply zmod_two_eq_zero_of_ne_one
        intro h1
        apply hk
        exact hl'.trans ((pairGraph_adj hβ a).2 (by rw [isAlt_apply_comm hβ]; exact h1)).reachable
      exact hle hx
    have hinvU : ∀ k, ∀ x ∈ U, (transv hβ (a k) : V →ₗ[ZMod 2] V) x ∈ U := by
      intro k x hx
      by_cases hk : k ∈ C
      · rw [transv_apply]
        exact add_mem hx (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩))
      · rw [transv_apply, horth k hk x hx, zero_smul, add_zero]
        exact hx
    rcases hirr U (hinvN U hinvU) with h | h
    · have hi : a i ∈ U :=
        Submodule.subset_span ⟨i, SimpleGraph.Reachable.refl (G := pairGraph hβ a) i, rfl⟩
      rw [h, Submodule.mem_bot] at hi
      exact ha0 i hi
    · exact ha0 j (hnd.1 _ fun x => horth j hij x (by rw [h]; exact Submodule.mem_top))
  have : Fintype I := Fintype.ofFinite I
  have : Nonempty I := ⟨i₀⟩
  obtain ⟨k, l, -, -, htree, hl⟩ :=
    SteinbergCG.connected_indexed_transvection_graph_reduces_to_tree hβ a ha0 hconn
  obtain ⟨hb0, hbspan, hbcl⟩ := hl (Fin.last k)
  rw [hspan] at hbspan
  rw [← hgenI] at hbcl
  set b := l (Fin.last k) with hbdef
  have hE6 : IsEmpty (e6Tree ↪g pairGraph hβ b) := by
    refine ⟨fun emb => ?_⟩
    have he : pairGraph hβ (b ∘ emb) = e6Tree := by
      ext x y
      rw [pairGraph_adj]
      exact emb.map_adj_iff
    obtain ⟨-, -, -, -, -, -, hiso, -, hcomm, hind, hLN, -⟩ :=
      e6_transvection_word_three_S3_factors.{_, 0} hβ (b ∘ emb) he
    obtain ⟨χ, hχ, hχL⟩ := exists_injective_of_factors _ hiso hcomm hind
    refine false_of_injective hS3 hχ ?_
    rintro _ ⟨σ, rfl⟩
    rw [← hbcl]
    refine Subgroup.closure_mono ?_ (hLN (hχL σ))
    rintro _ ⟨x, rfl⟩
    exact ⟨emb x, rfl⟩
  obtain ⟨n, s, hn2, -, -, hpath, hspan', hcl'⟩ :=
    e6_free_tree_reduces_to_path hβ hnd b hb0 hbspan htree hE6
  rw [hbcl] at hcl'
  obtain ⟨-, -, -, -, -, -, -, -, -, m, hm3, hm4a, hm4b, ψ', hψ', hmap, hinj⟩ :=
    actual_transvection_path_fully_deleted_module hβ hnd hn2 (b ∘ s) (fun i => hb0 (s i))
      hspan' hpath
  set φ := LinearMap.GeneralLinearGroup.congrLinearEquiv ψ' with hφdef
  have hmap' : N.map φ.toMonoidHom = (wRep m).range := by
    rw [← hcl']
    exact hmap
  have hmemN : ∀ σ, φ.symm (wRep m σ) ∈ N := by
    intro σ
    obtain ⟨g, hg, hgσ⟩ : wRep m σ ∈ N.map φ.toMonoidHom := by
      rw [hmap']
      exact ⟨σ, rfl⟩
    rw [← hgσ]
    simpa using hg
  have hm8 : m ≤ 8 := by
    by_contra hm9
    have hcard : Fintype.card (Σ _ : Fin 3, Fin 3) ≤ Fintype.card (Fin m) := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      omega
    obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
    let ρ := (Equiv.Perm.viaEmbeddingHom ι).comp
      (Equiv.Perm.sigmaCongrRightHom fun _ : Fin 3 => Fin 3)
    have hρ : Function.Injective ρ :=
      (Equiv.Perm.viaEmbeddingHom_injective ι).comp Equiv.Perm.sigmaCongrRightHom_injective
    refine false_of_injective hS3 (χ := φ.symm.toMonoidHom.comp ((wRep m).comp ρ))
      (φ.symm.injective.comp (hinj.comp hρ)) ?_
    rintro _ ⟨σ, rfl⟩
    exact hmemN (ρ σ)
  have hmS : m ∈ ({3, 5, 6, 7, 8} : Finset ℕ) := by
    have hm4 : m ≠ 4 := by
      by_cases h : n + 1 = 4
      · rw [hm4a h]
        decide
      · rw [hm4b h]
        exact h
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  let ψ₀ : Equiv.Perm (Fin m) →* N := (φ.symm.toMonoidHom.comp (wRep m)).codRestrict N hmemN
  have hψ₀ : Function.Bijective ψ₀ := by
    refine ⟨fun σ τ h => hinj (φ.symm.injective (congrArg Subtype.val h)), fun g => ?_⟩
    obtain ⟨σ, hσ⟩ : φ g ∈ (wRep m).range := by
      rw [← hmap']
      exact ⟨g, g.2, rfl⟩
    exact ⟨σ, Subtype.ext (show φ.symm (wRep m σ) = g by rw [hσ, MulEquiv.symm_apply_apply])⟩
  refine ⟨m, hmS, MulEquiv.ofBijective ψ₀ hψ₀, ψ', fun σ v => ?_,
    fun _ => ⟨⟨β, ⟨hβ, hnd, hNβ⟩, huniq⟩, fun β' hβ' hnd' hNβ' x y => ?_⟩⟩
  · change ψ' (ψ'.symm ((wRep m σ : deletedW m →ₗ[ZMod 2] deletedW m) (ψ'.symm.symm v))) = _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_symm]
  · rw [huniq β' ⟨hβ', hnd', hNβ'⟩]
    exact hψ' x y

end CFSG.Quasithin.SteinbergBN
