module

public import CFSG.Timmesfeld.RankTwo.Positive
public import CFSG.Timmesfeld.RankTwo.GradedPresentation
public import CFSG.LieType.Steinberg.PartBHalfSpace

public section

namespace CFSG.Timmesfeld.Transvection.Pres

open CFSG.LieType CFSG.LieType.Steinberg CFSG.Timmesfeld
open scoped commutatorElement

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def halfSpace (Φ : Steinberg.RootSystem ι) (f : (ι → ℤ) →+ ℤ) : Set (ι → ℤ) :=
  {γ | γ ∈ Φ.roots ∧ 0 < f γ}

theorem wordAct_add (Φ : Steinberg.RootSystem ι) (w : List ι) (u v : ι → ℤ) :
    wordAct Φ.refl w (u + v) = wordAct Φ.refl w u + wordAct Φ.refl w v := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [wordAct_cons, wordAct_cons, wordAct_cons, ih, map_add]

omit [DecidableEq ι] in
theorem ht_add (u v : ι → ℤ) : ht (u + v) = ht u + ht v := by
  simp [ht, Finset.sum_add_distrib]

omit [DecidableEq ι] in
theorem ht_nsmul (c : ℕ) (u : ι → ℤ) : ht (c • u) = c * ht u := by
  simp [ht, Finset.mul_sum]

variable {K : Type*} [Group K] {G : Type*} [Group G]

@[expose] def CommCompat (Φ : Steinberg.RootSystem ι) (X : (ι → ℤ) → Subgroup K)
    (Ψ : ∀ γ, X γ →* G) : Prop :=
  ∀ γ ∈ Φ.roots, ∀ δ ∈ Φ.roots, γ ≠ δ → γ + δ ≠ 0 → ∀ (s : X γ) (t : X δ),
    ∃ (z₁ : X (γ + δ)) (z₂ : X (2 • γ + δ)) (z₃ : X (γ + 2 • δ)),
      ⁅(s : K), (t : K)⁆ = z₁ * z₂ * z₃ ∧ (γ + δ ∉ Φ.roots → (z₁ : K) = 1) ∧
      (2 • γ + δ ∉ Φ.roots → (z₂ : K) = 1) ∧ (γ + 2 • δ ∉ Φ.roots → (z₃ : K) = 1) ∧
      ⁅Ψ γ s, Ψ δ t⁆ = Ψ _ z₁ * Ψ _ z₂ * Ψ _ z₃

section HalfSpaceHom

variable [Finite K] {Φ : Steinberg.RootSystem ι} {X : (ι → ℤ) → Subgroup K} (n : ι → K)
  (hn : ∀ i, ∀ γ ∈ Φ.roots, ∀ x ∈ X γ, n i * x * (n i)⁻¹ ∈ X (Φ.refl i γ))
  (hprod : ∀ L : List (ι → ℤ), L.Nodup → (∀ γ ∈ L, γ ∈ Φ.roots ∧ 0 < ht γ) →
    L.Pairwise (fun γ δ => ht γ ≤ ht δ) → ProdInjectiveFor X L)
  (habel : ∀ γ ∈ Φ.roots, ∀ x ∈ X γ, ∀ y ∈ X γ, x * y = y * x)
  (Ψ : ∀ γ, X γ →* G) (hcomm : CommCompat Φ X Ψ)

include hn hprod habel hcomm in
theorem extendsToHom_halfSpace (f : (ι → ℤ) →+ ℤ) :
    ExtendsToHom X (halfSpace Φ f) (fun γ x => Ψ γ x) := by
  classical
  obtain ⟨w, hw⟩ := exists_word_nonneg_of_pos Φ f
  set S := halfSpace Φ f with hSdef
  have hSfin : S.Finite := Φ.finite_roots.subset fun γ hγ => hγ.1
  let _ : Fintype S := hSfin.fintype
  have hpos : ∀ γ ∈ S, wordAct Φ.refl w γ ∈ Φ.pos := fun γ hγ =>
    mem_pos_of_nonneg Φ (Φ.wordAct_mem w hγ.1) (hw γ hγ.1 hγ.2)
  let ht' : S → ℕ := fun γ => (ht (wordAct Φ.refl w γ.1)).toNat
  have ht'_eq : ∀ γ : S, (ht' γ : ℤ) = ht (wordAct Φ.refl w γ.1) := fun γ =>
    Int.toNat_of_nonneg (le_of_lt (hpos γ.1 γ.2).2)
  have hcomb : ∀ (a b : ℕ) (γ δ : ι → ℤ), ht (wordAct Φ.refl w (a • γ + b • δ)) =
      a * ht (wordAct Φ.refl w γ) + b * ht (wordAct Φ.refl w δ) := fun a b γ δ => by
    rw [wordAct_add, wordAct_nsmul, wordAct_nsmul, ht_add, ht_nsmul, ht_nsmul]
  let F : S → Type _ := fun γ => Additive (X γ.1)
  let _ : ∀ γ : S, Fintype (F γ) := fun γ => Fintype.ofFinite _
  let x : (Σ γ : S, F γ) → K := fun g => ((Additive.toMul g.2 : X g.1.1) : K)
  let φ : (Σ γ : S, F γ) → G := fun g => Ψ g.1.1 (Additive.toMul g.2)
  let fac : ∀ v : ι → ℤ, X v → FreeGroup (Σ γ : S, F γ) := fun v z =>
    if hv : v ∈ S then FreeGroup.of ⟨⟨v, hv⟩, Additive.ofMul z⟩ else 1
  have hroot : ∀ (a b : ℕ) (γ δ : ι → ℤ), γ ∈ S → δ ∈ S → 0 < a → 0 < b →
      a • γ + b • δ ∈ Φ.roots → a • γ + b • δ ∈ S := fun a b γ δ hγ hδ ha hb hr => by
    refine ⟨hr, ?_⟩
    rw [map_add, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul]
    have := hγ.2
    have := hδ.2
    have : (0 : ℤ) < a := by exact_mod_cast ha
    have : (0 : ℤ) < b := by exact_mod_cast hb
    positivity
  have lift_x_fac : ∀ (v : ι → ℤ) (z : X v), (v ∉ S → (z : K) = 1) →
      FreeGroup.lift x (fac v z) = z := fun v z hz => by
    by_cases hv : v ∈ S
    · simp only [fac, dite_eq_left hv, FreeGroup.lift_apply_of, x, toMul_ofMul]
    · simp only [fac, dite_eq_right hv, map_one, hz hv]
  have lift_φ_fac : ∀ (v : ι → ℤ) (z : X v), (v ∉ S → (z : K) = 1) →
      FreeGroup.lift φ (fac v z) = Ψ v z := fun v z hz => by
    by_cases hv : v ∈ S
    · simp only [fac, dite_eq_left hv, FreeGroup.lift_apply_of, φ, toMul_ofMul]
    · have : z = 1 := Subtype.ext (hz hv)
      simp only [fac, dite_eq_right hv, map_one, this]
  choose z₁ z₂ z₃ hz using hcomm
  have hne0 : ∀ α β : S, α.1 + β.1 ≠ 0 := fun α β h => by
    have h1 := α.2.2
    have h2 := β.2.2
    have : f (α.1 + β.1) = 0 := by rw [h, map_zero]
    rw [map_add] at this
    omega
  let cm : ∀ α (_ : F α) β (_ : F β), FreeGroup (Σ γ : S, F γ) := fun α s β t =>
    if h : α.1 ≠ β.1 then
      fac _ (z₁ α.1 α.2.1 β.1 β.2.1 h (hne0 α β) (Additive.toMul s) (Additive.toMul t)) *
        fac _ (z₂ α.1 α.2.1 β.1 β.2.1 h (hne0 α β) (Additive.toMul s) (Additive.toMul t)) *
        fac _ (z₃ α.1 α.2.1 β.1 β.2.1 h (hne0 α β) (Additive.toMul s) (Additive.toMul t))
    else 1
  have hoff : ∀ (a b : ℕ) (α β : S) (v : ι → ℤ) (z : X v), 0 < a → 0 < b →
      v = a • α.1 + b • β.1 → (v ∉ Φ.roots → (z : K) = 1) → v ∉ S → (z : K) = 1 :=
    fun a b α β v z ha hb hv hz hvS => hz fun hr => hvS (hv ▸ hroot a b α.1 β.1 α.2 β.2 ha hb
      (hv ▸ hr))
  have e11 : ∀ α β : S, α.1 + β.1 = 1 • α.1 + 1 • β.1 := fun α β => by rw [one_smul, one_smul]
  have e21 : ∀ α β : S, 2 • α.1 + β.1 = 2 • α.1 + 1 • β.1 := fun α β => by rw [one_smul]
  have e12 : ∀ α β : S, α.1 + 2 • β.1 = 1 • α.1 + 2 • β.1 := fun α β => by rw [one_smul]
  have lift_x_cm : ∀ α s β t (h : α.1 ≠ β.1), FreeGroup.lift x (cm α s β t) =
      ⁅((Additive.toMul s : X α.1) : K), ((Additive.toMul t : X β.1) : K)⁆ := by
    intro α s β t h
    obtain ⟨he, h1, h2, h3, -⟩ := hz α.1 α.2.1 β.1 β.2.1 h (hne0 α β) (Additive.toMul s)
      (Additive.toMul t)
    simp only [cm, dite_eq_left h, map_mul]
    rw [lift_x_fac _ _ (hoff 1 1 α β _ _ one_pos one_pos (e11 α β) h1),
      lift_x_fac _ _ (hoff 2 1 α β _ _ two_pos one_pos (e21 α β) h2),
      lift_x_fac _ _ (hoff 1 2 α β _ _ one_pos two_pos (e12 α β) h3), he]
  have lift_φ_cm : ∀ α s β t (h : α.1 ≠ β.1), FreeGroup.lift φ (cm α s β t) =
      ⁅Ψ α.1 (Additive.toMul s), Ψ β.1 (Additive.toMul t)⁆ := by
    intro α s β t h
    obtain ⟨-, h1, h2, h3, hc⟩ := hz α.1 α.2.1 β.1 β.2.1 h (hne0 α β) (Additive.toMul s)
      (Additive.toMul t)
    simp only [cm, dite_eq_left h, map_mul]
    rw [lift_φ_fac _ _ (hoff 1 1 α β _ _ one_pos one_pos (e11 α β) h1),
      lift_φ_fac _ _ (hoff 2 1 α β _ _ two_pos one_pos (e21 α β) h2),
      lift_φ_fac _ _ (hoff 1 2 α β _ _ one_pos two_pos (e12 α β) h3)]
    exact hc.symm
  have hgr : ∀ α s β t, cm α s β t ∈ GradedPresentation.above ht' (max (ht' α) (ht' β)) := by
    have hfac : ∀ (α β : S) (a b : ℕ) (v : ι → ℤ) (z : X v), 0 < a → 0 < b →
        v = a • α.1 + b • β.1 → fac v z ∈ GradedPresentation.above ht' (max (ht' α) (ht' β)) := by
      intro α β a b v z ha hb hv
      by_cases hvS : v ∈ S
      · simp only [fac, dite_eq_left hvS]
        refine Subgroup.subset_closure ⟨⟨⟨v, hvS⟩, Additive.ofMul z⟩, ?_, rfl⟩
        show max (ht' α) (ht' β) < ht' ⟨v, hvS⟩
        have h1 := ht'_eq α
        have h2 := ht'_eq β
        have h3 := ht'_eq ⟨v, hvS⟩
        have hα := (hpos α.1 α.2).2
        have hβ := (hpos β.1 β.2).2
        have h4 : ht (wordAct Φ.refl w v) =
            a * ht (wordAct Φ.refl w α.1) + b * ht (wordAct Φ.refl w β.1) := by rw [hv, hcomb]
        have h3 : (ht' ⟨v, hvS⟩ : ℤ) =
            a * ht (wordAct Φ.refl w α.1) + b * ht (wordAct Φ.refl w β.1) := h3.trans h4
        have : (1 : ℤ) ≤ a := by exact_mod_cast ha
        have : (1 : ℤ) ≤ b := by exact_mod_cast hb
        refine max_lt ?_ ?_
        · have : (ht' α : ℤ) < ht' ⟨v, hvS⟩ := by rw [h1, h3]; nlinarith
          exact_mod_cast this
        · have : (ht' β : ℤ) < ht' ⟨v, hvS⟩ := by rw [h2, h3]; nlinarith
          exact_mod_cast this
      · simp only [fac, dite_eq_right hvS]
        exact one_mem _
    intro α s β t
    by_cases h : α.1 ≠ β.1
    · simp only [cm, dite_eq_left h]
      exact mul_mem (mul_mem (hfac α β 1 1 _ _ one_pos one_pos (e11 α β))
        (hfac α β 2 1 _ _ two_pos one_pos (e21 α β))) (hfac α β 1 2 _ _ one_pos two_pos (e12 α β))
    · simp only [cm, dite_eq_right h]
      exact one_mem _
  have hx : ∀ r ∈ GradedPresentation.rels cm, FreeGroup.lift x r = 1 := by
    rintro r (⟨γ, c, d, rfl⟩ | ⟨α, s, β, t, rfl⟩)
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      exact mul_inv_eq_one.2 rfl
    · simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      by_cases h : α.1 ≠ β.1
      · rw [lift_x_cm α s β t h, mul_inv_cancel]
      · obtain rfl : α = β := Subtype.ext (not_not.1 h)
        simp only [cm, dite_eq_right h, map_one, inv_one, mul_one,
          commutatorElement_eq_one_iff_mul_comm, x]
        exact habel α.1 α.2.1 _ (Additive.toMul s).2 _ (Additive.toMul t).2
  have hφ : ∀ r ∈ GradedPresentation.rels cm, FreeGroup.lift φ r = 1 := by
    rintro r (⟨γ, c, d, rfl⟩ | ⟨α, s, β, t, rfl⟩)
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      exact mul_inv_eq_one.2 (map_mul (Ψ γ.1) _ _)
    · simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      by_cases h : α.1 ≠ β.1
      · rw [lift_φ_cm α s β t h, mul_inv_cancel]
      · obtain rfl : α = β := Subtype.ext (not_not.1 h)
        simp only [cm, dite_eq_right h, map_one, inv_one, mul_one,
          commutatorElement_eq_one_iff_mul_comm, φ, ← map_mul]
        congr 1
        exact Subtype.ext (habel α.1 α.2.1 _ (Additive.toMul s).2 _ (Additive.toMul t).2)
  obtain ⟨L, hLnd, hLmem, hLsort⟩ :=
    exists_sorted_list (S := (Set.univ : Set S)) Set.finite_univ (fun γ => (ht' γ : ℤ))
  have hinj : Function.Injective fun c : (∀ γ, F γ) => (L.map fun γ => x ⟨γ, c γ⟩).prod := by
    intro c c' hcc
    set N := (w.map n).prod
    let wv : S → (ι → ℤ) := fun γ => wordAct Φ.refl w γ.1
    have hwv : Function.Injective wv := fun γ δ h => Subtype.ext (by
      have := congrArg (wordAct Φ.refl w.reverse) h
      simpa only [wv, Φ.wordAct_reverse] using this)
    let fc : (∀ γ, F γ) → (ι → ℤ) → K := fun c v =>
      if h : ∃ γ : S, wv γ = v then N * x ⟨h.choose, c h.choose⟩ * N⁻¹ else 1
    have hxc : ∀ (c : ∀ γ, F γ) (γ' γ : S), γ' = γ → x ⟨γ', c γ'⟩ = x ⟨γ, c γ⟩ := by
      rintro c _ _ rfl
      rfl
    have hfc : ∀ c (γ : S), fc c (wv γ) = N * x ⟨γ, c γ⟩ * N⁻¹ := by
      intro c γ
      have h : ∃ γ' : S, wv γ' = wv γ := ⟨γ, rfl⟩
      simp only [fc, dite_eq_left h]
      rw [hxc c _ γ (hwv h.choose_spec)]
    have hprodc : ∀ c, ((L.map wv).map (fc c)).prod =
        N * (L.map fun γ => x ⟨γ, c γ⟩).prod * N⁻¹ := by
      intro c
      rw [List.map_map]
      have e : L.map ((fc c) ∘ wv) = (L.map fun γ => x ⟨γ, c γ⟩).map (MulAut.conj N) := by
        rw [List.map_map]
        exact List.map_congr_left fun γ _ => by simp [hfc, MulAut.conj_apply]
      rw [e, ← map_list_prod, MulAut.conj_apply]
    have hmem : ∀ c, ∀ v ∈ L.map wv, fc c v ∈ X v := by
      intro c v hv
      obtain ⟨γ, -, rfl⟩ := List.mem_map.1 hv
      rw [hfc]
      exact conj_mem_wordAct n hn w γ.2.1 (Additive.toMul (c γ)).2
    have hL2 := hprod (L.map wv) (hLnd.map hwv) (fun v hv => by
        obtain ⟨γ, -, rfl⟩ := List.mem_map.1 hv
        exact hpos γ.1 γ.2)
      (by
        rw [List.pairwise_map]
        refine hLsort.imp fun {γ δ} h => ?_
        have h1 := ht'_eq γ
        have h2 := ht'_eq δ
        simp only [wv]
        omega)
    have hcc' := hL2 (fc c) (fc c') (hmem c) (hmem c') (by
      rw [hprodc, hprodc]
      exact congrArg (fun z => N * z * N⁻¹) hcc)
    funext γ
    have h := hcc' (wv γ) (List.mem_map_of_mem ((hLmem γ).2 trivial))
    rw [hfc, hfc, mul_left_inj, mul_right_inj] at h
    exact Additive.toMul.injective (Subtype.ext h)
  obtain ⟨θ, hθ⟩ := GradedPresentation.exists_hom hgr x φ hx hφ L hinj
  exact ⟨Subgroup.closure (Set.range x), θ, fun γ hγ y =>
    ⟨Subgroup.subset_closure ⟨⟨⟨γ, hγ⟩, Additive.ofMul y⟩, rfl⟩, hθ ⟨⟨γ, hγ⟩, Additive.ofMul y⟩⟩⟩

end HalfSpaceHom

section Cones

variable {Φ : Steinberg.RootSystem ι} {X : (ι → ℤ) → Subgroup K}

theorem coneCompatible_of_halfSpace {φ : ∀ γ, X γ → G}
    (hhalf : ∀ f : (ι → ℤ) →+ ℤ, ExtendsToHom X (halfSpace Φ f) φ)
    (hrank : ∀ i, ExtendsToHom X {Pi.single i 1, -Pi.single i 1} φ) : ConeCompatible Φ X φ := by
  refine ⟨fun α hα β hβ hneg => ?_, hrank⟩
  obtain ⟨f, hf⟩ := exists_addHom_pos_on_cone Φ hα hβ hneg
  exact (hhalf f).mono fun γ hγ => ⟨hγ.1, hf γ hγ⟩

variable (n : ι → K) (hn : ∀ i, ∀ γ ∈ Φ.roots, ∀ x ∈ X γ, n i * x * (n i)⁻¹ ∈ X (Φ.refl i γ))
  (hprod : ∀ L : List (ι → ℤ), L.Nodup → (∀ γ ∈ L, γ ∈ Φ.roots ∧ 0 < ht γ) →
    L.Pairwise (fun γ δ => ht γ ≤ ht δ) → ProdInjectiveFor X L)

end Cones

section Conj

variable {Φ : Steinberg.RootSystem ι} {X : (ι → ℤ) → Subgroup K} {Ψ : ∀ γ, X γ →* G}

@[expose] def ConjCompat (Φ : Steinberg.RootSystem ι) (X : (ι → ℤ) → Subgroup K)
    (f : (ι → ℤ) →+ ℤ) {S : Subgroup K} (θ : S →* G) (g : K) (ĝ : G) : Prop :=
  ∀ y ∈ ⨆ γ ∈ halfSpace Φ f, X γ, ∃ (hy : y ∈ S) (hy' : g * y * g⁻¹ ∈ S),
    g * y * g⁻¹ ∈ ⨆ γ ∈ halfSpace Φ f, X γ ∧ ĝ * θ ⟨y, hy⟩ * ĝ⁻¹ = θ ⟨g * y * g⁻¹, hy'⟩

theorem ConjCompat.mul {f : (ι → ℤ) →+ ℤ} {S : Subgroup K} {θ : S →* G} {g g' : K} {ĝ ĝ' : G}
    (h : ConjCompat Φ X f θ g ĝ) (h' : ConjCompat Φ X f θ g' ĝ') :
    ConjCompat Φ X f θ (g * g') (ĝ * ĝ') := by
  intro y hy
  obtain ⟨hyS, hy'S, hyU, e⟩ := h' y hy
  obtain ⟨hy₀, hy''S, hyU', e'⟩ := h _ hyU
  have hg : g * g' * y * (g * g')⁻¹ = g * (g' * y * g'⁻¹) * g⁻¹ := by group
  refine ⟨hyS, hg ▸ hy''S, hg ▸ hyU', ?_⟩
  have e'' : (⟨g * g' * y * (g * g')⁻¹, hg ▸ hy''S⟩ : S) = ⟨g * (g' * y * g'⁻¹) * g⁻¹, hy''S⟩ :=
    Subtype.ext hg
  rw [e'', ← e', ← e]
  group

variable (hcomm : CommCompat Φ X Ψ)

include hcomm in
theorem conjCompat_of_root {f : (ι → ℤ) →+ ℤ} {S : Subgroup K} {θ : S →* G}
    (hθ : ∀ γ ∈ halfSpace Φ f, ∀ y : X γ, ∃ hy : (y : K) ∈ S, θ ⟨y, hy⟩ = Ψ γ y)
    {α : ι → ℤ} (hα : α ∈ Φ.roots) (hfα : f α = 0) (a : X α) :
    ConjCompat Φ X f θ a (Ψ α a) := by
  classical
  set U := ⨆ γ ∈ halfSpace Φ f, X γ with hUdef
  have hUS : U ≤ S := iSup₂_le fun γ hγ y hy => (hθ γ hγ ⟨y, hy⟩).1
  have hXU : ∀ γ ∈ halfSpace Φ f, X γ ≤ U := fun γ hγ =>
    le_iSup₂_of_le (f := fun γ (_ : γ ∈ halfSpace Φ f) => X γ) γ hγ le_rfl
  have hfac : ∀ (i j : ℕ) (γ v : ι → ℤ), γ ∈ halfSpace Φ f → 0 < j → v = i • α + j • γ →
      ∀ z : X v, (v ∉ Φ.roots → (z : K) = 1) → (z : K) ∈ U ∧ (v ∉ halfSpace Φ f → (z : K) = 1) := by
    intro i j γ v hγ hj hv z hz
    have hpos : v ∈ Φ.roots → v ∈ halfSpace Φ f := fun hr => by
      refine ⟨hr, ?_⟩
      rw [hv, map_add, map_nsmul, map_nsmul, hfα, smul_zero, zero_add, nsmul_eq_mul]
      have : (0 : ℤ) < j := by exact_mod_cast hj
      exact mul_pos this hγ.2
    by_cases hr : v ∈ Φ.roots
    · exact ⟨hXU _ (hpos hr) z.2, fun h => absurd (hpos hr) h⟩
    · rw [hz hr]
      exact ⟨one_mem _, fun _ => rfl⟩
  have hne : ∀ γ ∈ halfSpace Φ f, α ≠ γ ∧ α + γ ≠ 0 := fun γ hγ => by
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have := hγ.2
      rw [← e, hfα] at this
      exact lt_irrefl 0 this
    · have := hγ.2
      have h2 : f (α + γ) = 0 := by rw [e, map_zero]
      rw [map_add, hfα, zero_add] at h2
      omega
  have hgen : ∀ γ ∈ halfSpace Φ f, ∀ y : X γ, (a : K) * y * (a : K)⁻¹ ∈ U ∧
      ∃ h : (a : K) * y * (a : K)⁻¹ ∈ S, Ψ α a * Ψ γ y * (Ψ α a)⁻¹ = θ ⟨_, h⟩ := by
    intro γ hγ y
    obtain ⟨hαγ, hαγ0⟩ := hne γ hγ
    obtain ⟨z₁, z₂, z₃, he, h1, h2, h3, hc⟩ := hcomm α hα γ hγ.1 hαγ hαγ0 a y
    have e : (a : K) * y * (a : K)⁻¹ = z₁ * z₂ * z₃ * y := by
      rw [← he, commutatorElement_def]; group
    obtain ⟨m1, n1⟩ := hfac 1 1 γ _ hγ one_pos (by rw [one_smul, one_smul]) z₁ h1
    obtain ⟨m2, n2⟩ := hfac 2 1 γ _ hγ one_pos (by rw [one_smul]) z₂ h2
    obtain ⟨m3, n3⟩ := hfac 1 2 γ _ hγ two_pos (by rw [one_smul]) z₃ h3
    have my := hXU γ hγ y.2
    have hU : (a : K) * y * (a : K)⁻¹ ∈ U := e ▸ mul_mem (mul_mem (mul_mem m1 m2) m3) my
    refine ⟨hU, hUS hU, ?_⟩
    have hθz : ∀ (v : ι → ℤ) (z : X v), (v ∉ halfSpace Φ f → (z : K) = 1) →
        ∃ hz : (z : K) ∈ S, θ ⟨z, hz⟩ = Ψ v z := by
      intro v z hz
      by_cases hv : v ∈ halfSpace Φ f
      · exact hθ v hv z
      · have h1 : z = 1 := Subtype.ext (hz hv)
        subst h1
        exact ⟨one_mem _, by rw [map_one]; exact (map_one θ)⟩
    obtain ⟨s1, t1⟩ := hθz _ z₁ n1
    obtain ⟨s2, t2⟩ := hθz _ z₂ n2
    obtain ⟨s3, t3⟩ := hθz _ z₃ n3
    obtain ⟨sy, ty⟩ := hθ γ hγ y
    have hconj : Ψ α a * Ψ γ y * (Ψ α a)⁻¹ = ⁅Ψ α a, Ψ γ y⁆ * Ψ γ y := by
      rw [commutatorElement_def]; group
    rw [hconj, hc, ← t1, ← t2, ← t3, ← ty, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext e.symm
  intro y hy
  rw [iSup_subtype'] at hy
  refine Subgroup.iSup_induction _ hy (C := fun y => ∃ (hy : y ∈ S)
    (hy' : (a : K) * y * (a : K)⁻¹ ∈ S), (a : K) * y * (a : K)⁻¹ ∈ U ∧
      Ψ α a * θ ⟨y, hy⟩ * (Ψ α a)⁻¹ = θ ⟨_, hy'⟩) ?_ ?_ ?_
  · rintro ⟨γ, hγ⟩ z hz
    obtain ⟨hU, hS, e⟩ := hgen γ hγ ⟨z, hz⟩
    obtain ⟨hzS, hθz⟩ := hθ γ hγ ⟨z, hz⟩
    exact ⟨hzS, hS, hU, by rw [hθz]; exact e⟩
  · refine ⟨one_mem _, by simp, by simp, ?_⟩
    have e : (⟨(a : K) * 1 * (a : K)⁻¹, by simp⟩ : S) = 1 :=
      Subtype.ext (by simp)
    rw [e, show (⟨1, one_mem S⟩ : S) = 1 from rfl, map_one, mul_one, mul_inv_cancel]
  · rintro y z ⟨hyS, hy'S, hyU, ey⟩ ⟨hzS, hz'S, hzU, ez⟩
    have hm : (a : K) * (y * z) * (a : K)⁻¹ =
        ((a : K) * y * (a : K)⁻¹) * ((a : K) * z * (a : K)⁻¹) := by
      group
    refine ⟨mul_mem hyS hzS, hm ▸ mul_mem hy'S hz'S, hm ▸ mul_mem hyU hzU, ?_⟩
    have e1 : (⟨y * z, mul_mem hyS hzS⟩ : S) = ⟨y, hyS⟩ * ⟨z, hzS⟩ := rfl
    have e2 : (⟨(a : K) * (y * z) * (a : K)⁻¹, hm ▸ mul_mem hy'S hz'S⟩ : S) =
        ⟨_, hy'S⟩ * ⟨_, hz'S⟩ := Subtype.ext hm
    rw [e1, e2, map_mul, map_mul, ← ey, ← ez]
    group

include hcomm in
theorem conj_eq_of_halfSpace {f : (ι → ℤ) →+ ℤ}
    (hhalf : ExtendsToHom X (halfSpace Φ f) (fun γ x => Ψ γ x)) {α : ι → ℤ}
    (hα : α ∈ Φ.roots) (hfα : f α = 0) (a₁ a₃ : X α) (a₂ : X (-α)) {β β' : ι → ℤ}
    (hβ : β ∈ halfSpace Φ f) (hβ' : β' ∈ halfSpace Φ f) (y : X β) (y' : X β')
    (hy : (y' : K) = ((a₁ : K) * a₂ * a₃) * y * ((a₁ : K) * a₂ * a₃)⁻¹) :
    Ψ α a₁ * Ψ (-α) a₂ * Ψ α a₃ * Ψ β y * (Ψ α a₁ * Ψ (-α) a₂ * Ψ α a₃)⁻¹ = Ψ β' y' := by
  obtain ⟨S, θ, hθ⟩ := hhalf
  have hfα' : f (-α) = 0 := by rw [map_neg, hfα, neg_zero]
  have c := ((conjCompat_of_root hcomm hθ hα hfα a₁).mul
    (conjCompat_of_root hcomm hθ (Φ.neg_mem α hα) hfα' a₂)).mul
    (conjCompat_of_root hcomm hθ hα hfα a₃)
  have hyU : (y : K) ∈ ⨆ γ ∈ halfSpace Φ f, X γ :=
    le_iSup₂_of_le (f := fun γ (_ : γ ∈ halfSpace Φ f) => X γ) β hβ le_rfl y.2
  obtain ⟨hyS, hy'S, -, e⟩ := c y hyU
  obtain ⟨hyS₀, hθy⟩ := hθ β hβ y
  obtain ⟨hy'S₀, hθy'⟩ := hθ β' hβ' y'
  have e1 : (⟨y, hyS⟩ : S) = ⟨y, hyS₀⟩ := rfl
  have e2 : (⟨(a₁ : K) * a₂ * a₃ * y * ((a₁ : K) * a₂ * a₃)⁻¹, hy'S⟩ : S) = ⟨y', hy'S₀⟩ :=
    Subtype.ext hy.symm
  rw [e1, hθy, e2, hθy'] at e
  exact e

end Conj

section Transfer

variable {X : (ι → ℤ) → Subgroup K}

theorem conj_commutator {H : Type*} [Group H] (g x y : H) :
    g * ⁅x, y⁆ * g⁻¹ = ⁅g * x * g⁻¹, g * y * g⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem conj_commutator_mul {H : Type*} [Group H] (g x y z : H) :
    g * (⁅x, y⁆ * z) * g⁻¹ = ⁅g * x * g⁻¹, g * y * g⁻¹⁆ * (g * z * g⁻¹) := by
  simp only [commutatorElement_def]
  group

omit [Fintype ι] [DecidableEq ι] in
theorem commutator_mul_eq_of_extendsToHom {Ψ : Set (ι → ℤ)} {φ : ∀ γ, X γ → G}
    (h : ExtendsToHom X Ψ φ) {β₁ β₂ β₃ β₄ : ι → ℤ} (h₁ : β₁ ∈ Ψ) (h₂ : β₂ ∈ Ψ) (h₃ : β₃ ∈ Ψ)
    (h₄ : β₄ ∈ Ψ) (x₁ : X β₁) (x₂ : X β₂) (x₃ : X β₃) (y : X β₄)
    (hxy : ⁅(x₁ : K), (x₂ : K)⁆ * x₃ = y) : ⁅φ β₁ x₁, φ β₂ x₂⁆ * φ β₃ x₃ = φ β₄ y := by
  obtain ⟨S, θ, hθ⟩ := h
  obtain ⟨m₁, e₁⟩ := hθ β₁ h₁ x₁
  obtain ⟨m₂, e₂⟩ := hθ β₂ h₂ x₂
  obtain ⟨m₃, e₃⟩ := hθ β₃ h₃ x₃
  obtain ⟨m₄, e₄⟩ := hθ β₄ h₄ y
  have e : ⁅(⟨_, m₁⟩ : S), ⟨_, m₂⟩⁆ * ⟨_, m₃⟩ = (⟨_, m₄⟩ : S) :=
    Subtype.ext (by simpa [commutatorElement_def] using hxy)
  rw [← e₁, ← e₂, ← e₃, ← e₄, ← e, map_mul, map_commutatorElement]

omit [Fintype ι] [DecidableEq ι] in
theorem commutator_eq_of_extendsToHom {Ψ : Set (ι → ℤ)} {φ : ∀ γ, X γ → G}
    (h : ExtendsToHom X Ψ φ) {β₁ β₂ β₃ : ι → ℤ} (h₁ : β₁ ∈ Ψ) (h₂ : β₂ ∈ Ψ) (h₃ : β₃ ∈ Ψ)
    (x₁ : X β₁) (x₂ : X β₂) (y : X β₃) (hxy : ⁅(x₁ : K), (x₂ : K)⁆ = y) :
    ⁅φ β₁ x₁, φ β₂ x₂⁆ = φ β₃ y := by
  obtain ⟨S, θ, hθ⟩ := h
  obtain ⟨m₁, e₁⟩ := hθ β₁ h₁ x₁
  obtain ⟨m₂, e₂⟩ := hθ β₂ h₂ x₂
  obtain ⟨m₃, e₃⟩ := hθ β₃ h₃ y
  have e : ⁅(⟨_, m₁⟩ : S), ⟨_, m₂⟩⁆ = (⟨_, m₃⟩ : S) :=
    Subtype.ext (by simpa [commutatorElement_def] using hxy)
  rw [← e₁, ← e₂, ← e₃, ← e, map_commutatorElement]

end Transfer

end CFSG.Timmesfeld.Transvection.Pres
