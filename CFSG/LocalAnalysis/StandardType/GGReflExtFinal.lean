module

public import CFSG.LocalAnalysis.StandardType.GGReflExtTransport
public import CFSG.LocalAnalysis.StandardType.GGReflExtNorm

public section

namespace CFSG.ReflExt

open CFSG.TwoNodeSmall CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem core_classification
    (P0 : Pt) [Fact P0.p.Prime] {T : Tables} (hp2 : P0.p ≠ 2) (hok : verifyAll P0 T = true)
    {n : ℕ} (G : ℕ → Refl) (hgens : P0.gens = (List.range n).map G)
    {V : Type} [AddCommGroup V] [Module (ZMod P0.p) V] (ε : V ≃ₗ[ZMod P0.p] P0.V)
    (h : Fin n → V) (α : Fin n → Module.Dual (ZMod P0.p) V) (r : Fin n → (V ≃ₗ[ZMod P0.p] V))
    (hr : ∀ i v, r i v = v - α i v • h i) (A : Subgroup (V ≃ₗ[ZMod P0.p] V))
    (hrA : ∀ i, r i ∈ A) (hεh : ∀ i : Fin n, ε (h i) = P0.vec (G i).h)
    (hεα : ∀ (i : Fin n) w, α i w = P0.dot (P0.vec (G i).f) (ε w))
    (hrg : A = Subgroup.closure {s | s ∈ A ∧ GGLinRefl s}) (hnt : ∀ g ∈ A, ¬ IsTransv g)
    (hcard : Nat.card A ≤ P0.bound) (t : V ≃ₗ[ZMod P0.p] V) (htA : t ∈ A) (htr : GGLinRefl t)
    (htm : rxConj ε t (P0.vec P0.x) ≠ P0.vec P0.x) : ZS.LinWeyl P0.p A := by
  have hfr : ∀ r' ∈ P0.gens, ∃ g ∈ A,
      ∀ w : P0.V, ε (g (ε.symm w)) = w - P0.dot (P0.vec r'.f) w • P0.vec r'.h := by
    intro r' hr'
    rw [hgens] at hr'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr'
    have hi' : i < n := List.mem_range.mp hi
    refine ⟨r ⟨i, hi'⟩, hrA _, fun w => ?_⟩
    rw [hr, map_sub, map_smul, LinearEquiv.apply_symm_apply, hεh ⟨i, hi'⟩,
      hεα ⟨i, hi'⟩ (ε.symm w), LinearEquiv.apply_symm_apply]
  have hctx := ctx_of_conj hp2 hok ε A hfr hrg hnt hcard
  have hmem : rxConj ε t ∈ A.map (rxConj ε).toMonoidHom := Subgroup.mem_map.mpr ⟨t, htA, rfl⟩
  exact linWeyl_of_conj ε A (hctx.linWeyl hmem ((rxConj_isRefl ε t).mpr htr) htm)

theorem moving_conj {p : ℕ} [Fact p.Prime] {V W : Type} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup W] [Module (ZMod p) W] (ε : V ≃ₗ[ZMod p] W) (x : V) (xv : W) (c : ZMod p)
    (hc : c ≠ 0) (hεx : ε x = c • xv) (t : V ≃ₗ[ZMod p] V) (htm : t x ≠ x) :
    rxConj ε t xv ≠ xv := by
  intro heq
  apply htm
  have hxv : xv = c⁻¹ • ε x := by
    rw [hεx, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h1 : ε.symm xv = c⁻¹ • x := by
    rw [hxv, map_smul, LinearEquiv.symm_apply_apply]
  rw [rxConj_apply, h1, map_smul, map_smul, hxv] at heq
  exact ε.injective (smul_right_injective W (inv_ne_zero hc) heq)

theorem getD_append_left' (l₁ l₂ : List ℕ) (i : ℕ) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i 0 = l₁.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [List.length_append]; omega), List.getElem?_eq_getElem h]
  congr 1
  rw [List.getElem_append_left h]

theorem getD_append_right' (l₁ l₂ : List ℕ) (i : ℕ) (h : l₁.length ≤ i)
    (hi : i < (l₁ ++ l₂).length) : (l₁ ++ l₂).getD i 0 = l₂.getD (i - l₁.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (by rw [List.length_append] at hi; omega)]
  congr 1
  rw [List.getElem_append_right h]

theorem sum_single_id {n : ℕ} (a : Fin n → ZMod 3) :
    (∑ j : Fin n, a j • (Pi.single j (1 : ZMod 3) : Fin n → ZMod 3)) = a := by
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem sum_single_castSucc {n : ℕ} (a : Fin n → ZMod 3) :
    (∑ j : Fin n, a j • (Pi.single (Fin.castSucc j) (1 : ZMod 3) : Fin (n + 1) → ZMod 3)) =
      fun k : Fin (n + 1) => if hk : (k : ℕ) < n then a ⟨k, hk⟩ else 0 := by
  funext k
  refine Fin.lastCases ?_ (fun j' => ?_) k
  · simp [Finset.sum_apply, Pi.single_apply, Fin.castSucc_ne_last]
  · simp [Finset.sum_apply, Pi.single_apply]

theorem case_n {n : ℕ} (row : ℕ → Vec)
    (xl : Vec) (bound s₀ : ℕ) (C : Matrix (Fin n) (Fin n) (ZMod 3)) (x₀ : Fin n → ZMod 3)
    (hrow : ∀ i j : Fin n, (((row i).getD j 0 : ℕ) : ZMod 3) = C i j)
    (hxl : ∀ j : Fin n, ((xl.getD j 0 : ℕ) : ZMod 3) = x₀ j)
    (hc_n : ∃ T, verifyAll (mkFrame 3 n n row s₀ xl bound) T = true)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ε : V ≃ₗ[ZMod 3] (Fin n → ZMod 3))
    (h : Fin n → V) (α : Fin n → Module.Dual (ZMod 3) V) (x : V)
    (hεh : ∀ i, ε (h i) = Pi.single i 1) (hεα : ∀ i w, α i w = ∑ j, C i j * ε w j)
    (c : ZMod 3) (hc : c ≠ 0) (hεx : ε x = c • x₀) (r : Fin n → (V ≃ₗ[ZMod 3] V))
    (hr : ∀ i v, r i v = v - α i v • h i) (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hrA : ∀ i, r i ∈ A)
    (hrg : A = Subgroup.closure {s | s ∈ A ∧ GGLinRefl s}) (hnt : ∀ g ∈ A, ¬ IsTransv g)
    (hcard : Nat.card A ≤ bound) (t : V ≃ₗ[ZMod 3] V) (htA : t ∈ A) (htr : GGLinRefl t)
    (htm : t x ≠ x) : ZS.LinWeyl 3 A := by
  obtain ⟨T, hT⟩ := hc_n
  have hne : ¬ (n = n + 1) := by omega
  haveI : Fact (mkFrame 3 n n row s₀ xl bound).p.Prime := ⟨Nat.prime_three⟩
  refine core_classification (mkFrame 3 n n row s₀ xl bound) (by show (3 : ℕ) ≠ 2; decide) hT
    (fun i => ⟨row i ++ (if n = n + 1 then [if i = 0 then s₀ else 0] else []), unitV n i⟩)
    rfl ε h α r hr A hrA ?_ ?_ hrg hnt hcard t htA htr ?_
  · intro i
    rw [hεh i]
    exact (Pt.vec_unit (mkFrame 3 n n row s₀ xl bound) i).symm
  · intro i w
    rw [hεα i w]
    apply Finset.sum_congr rfl
    intro j _
    have : (mkFrame 3 n n row s₀ xl bound).vec (row i ++ (if n = n + 1 then [if (i : ℕ) = 0 then s₀ else 0] else [])) j =
        C i j := by
      show ((((row i ++ (if n = n + 1 then [if (i : ℕ) = 0 then s₀ else 0] else [])).getD j 0 : ℕ)) : ZMod 3) = C i j
      rw [if_neg hne, List.append_nil]
      exact hrow i j
    exact congrArg (· * ε w j) this.symm
  · have hvx : (mkFrame 3 n n row s₀ xl bound).vec (mkFrame 3 n n row s₀ xl bound).x = x₀ := by
      funext j
      show (((xl ++ (if n = n + 1 then [0] else [])).getD j 0 : ℕ) : ZMod 3) = x₀ j
      rw [if_neg hne, List.append_nil]
      exact hxl j
    rw [hvx]
    exact moving_conj ε x x₀ c hc hεx t htm

theorem case_succ {n : ℕ}
    (row : ℕ → Vec) (xl : Vec) (bound : ℕ) (C : Matrix (Fin n) (Fin n) (ZMod 3))
    (x₀ : Fin n → ZMod 3) (hrow : ∀ i j : Fin n, (((row i).getD j 0 : ℕ) : ZMod 3) = C i j)
    (hlen : ∀ i, (row i).length = n) (hxl : ∀ j : Fin n, ((xl.getD j 0 : ℕ) : ZMod 3) = x₀ j)
    (hxlen : xl.length = n) (s : ℕ)
    (hc_s : ∃ T, verifyAll (mkFrame 3 n (n + 1) row s xl bound) T = true)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ε : V ≃ₗ[ZMod 3] (Fin (n + 1) → ZMod 3))
    (h : Fin n → V) (α : Fin n → Module.Dual (ZMod 3) V) (x e : V) (i0 : Fin n)
    (hi0 : (i0 : ℕ) = 0) (hεh : ∀ i, ε (h i) = Pi.single (Fin.castSucc i) 1)
    (hεα : ∀ i w, α i w =
      ∑ j : Fin n, C i j * ε w (Fin.castSucc j) + α i e * ε w (Fin.last n))
    (hαe : ∀ i, α i e = if i = i0 then (s : ZMod 3) else 0) (c : ZMod 3) (hc : c ≠ 0)
    (hεx : ε x = fun k : Fin (n + 1) => if hk : (k : ℕ) < n then c * x₀ ⟨k, hk⟩ else 0)
    (r : Fin n → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hrA : ∀ i, r i ∈ A)
    (hrg : A = Subgroup.closure {s | s ∈ A ∧ GGLinRefl s}) (hnt : ∀ g ∈ A, ¬ IsTransv g)
    (hcard : Nat.card A ≤ bound) (t : V ≃ₗ[ZMod 3] V) (htA : t ∈ A) (htr : GGLinRefl t)
    (htm : t x ≠ x) : ZS.LinWeyl 3 A := by
  obtain ⟨T, hT⟩ := hc_s
  haveI : Fact (mkFrame 3 n (n + 1) row s xl bound).p.Prime := ⟨Nat.prime_three⟩
  refine core_classification (mkFrame 3 n (n + 1) row s xl bound) (by show (3 : ℕ) ≠ 2; decide) hT
    (fun i => ⟨row i ++ (if n + 1 = n + 1 then [if i = 0 then s else 0] else []),
      unitV (n + 1) i⟩) rfl ε h α r hr A hrA ?_ ?_ hrg hnt hcard t htA htr ?_
  · intro i
    rw [hεh i]
    exact (Pt.vec_unit (mkFrame 3 n (n + 1) row s xl bound) (Fin.castSucc i)).symm
  · intro i w
    rw [hεα i w, hαe i]
    show _ = ∑ k : Fin (n + 1), (mkFrame 3 n (n + 1) row s xl bound).vec _ k * ε w k
    rw [Fin.sum_univ_castSucc]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      have hj : (mkFrame 3 n (n + 1) row s xl bound).vec
          (row i ++ (if n + 1 = n + 1 then [if (i : ℕ) = 0 then s else 0] else []))
          (Fin.castSucc j) = C i j := by
        show (((row i ++ (if n + 1 = n + 1 then [if (i : ℕ) = 0 then s else 0] else [])).getD
          (Fin.castSucc j : ℕ) 0 : ℕ) : ZMod 3) = C i j
        rw [if_pos rfl, Fin.coe_castSucc, getD_append_left' _ _ _ (by rw [hlen i]; exact j.isLt)]
        exact hrow i j
      exact congrArg (· * ε w (Fin.castSucc j)) hj.symm
    · have hl : (mkFrame 3 n (n + 1) row s xl bound).vec
          (row i ++ (if n + 1 = n + 1 then [if (i : ℕ) = 0 then s else 0] else []))
          (Fin.last n) = if i = i0 then (s : ZMod 3) else 0 := by
        show (((row i ++ (if n + 1 = n + 1 then [if (i : ℕ) = 0 then s else 0] else [])).getD
          (Fin.last n : ℕ) 0 : ℕ) : ZMod 3) = if i = i0 then (s : ZMod 3) else 0
        rw [if_pos rfl, Fin.val_last,
          getD_append_right' _ _ _ (by rw [hlen i]) (by simp [hlen i]), hlen i, Nat.sub_self]
        by_cases hi : (i : ℕ) = 0
        · have hii : i = i0 := Fin.ext (by rw [hi, hi0])
          rw [if_pos hii]
          simp [hi]
        · have hii : i ≠ i0 := fun h' => hi (by rw [h', hi0])
          rw [if_neg hii]
          simp [hi]
      exact congrArg (· * ε w (Fin.last n)) hl.symm
  · have hvx : c • (mkFrame 3 n (n + 1) row s xl bound).vec (mkFrame 3 n (n + 1) row s xl bound).x =
        fun k : Fin (n + 1) => if hk : (k : ℕ) < n then c * x₀ ⟨k, hk⟩ else 0 := by
      funext k
      by_cases hk : (k : ℕ) < n
      · rw [dif_pos hk]
        show c * (((xl ++ (if n + 1 = n + 1 then [0] else [])).getD k 0 : ℕ) : ZMod 3) = _
        rw [if_pos rfl, getD_append_left' _ _ _ (by rw [hxlen]; exact hk), hxl ⟨k, hk⟩]
      · rw [dif_neg hk]
        have hkn : (k : ℕ) = n := by
          have hk' : (k : ℕ) < n + 1 := k.isLt
          omega
        show c * (((xl ++ (if n + 1 = n + 1 then [0] else [])).getD k 0 : ℕ) : ZMod 3) = 0
        rw [if_pos rfl, getD_append_right' _ _ _ (by rw [hxlen]; omega) (by simp [hxlen]; omega),
          hxlen, hkn]
        simp
    exact moving_conj ε x _ c hc (hεx.trans hvx.symm) t htm

theorem frame_classification {n : ℕ}
    (row : ℕ → Vec) (xl : Vec) (bound s₀ : ℕ) (C : Matrix (Fin n) (Fin n) (ZMod 3))
    (x₀ : Fin n → ZMod 3) (B : Matrix (Fin n) (Fin n) (ZMod 3)) (i0 : Fin n) (hi0 : (i0 : ℕ) = 0)
    (hrow : ∀ i j : Fin n, (((row i).getD j 0 : ℕ) : ZMod 3) = C i j)
    (hlen : ∀ i, (row i).length = n) (hxl : ∀ j : Fin n, ((xl.getD j 0 : ℕ) : ZMod 3) = x₀ j)
    (hxlen : xl.length = n) (hx0 : x₀ i0 = 1)
    (hker : ∀ y : Fin n → ZMod 3, C.mulVec y = 0 → ∃ c : ZMod 3, y = c • x₀)
    (hB : ∀ u : Fin n → ZMod 3, x₀ ⬝ᵥ u = 0 → C.mulVec (B.mulVec u) = u)
    (hc_n : ∃ T, verifyAll (mkFrame 3 n n row s₀ xl bound) T = true)
    (hc_1 : ∃ T, verifyAll (mkFrame 3 n (n + 1) row 1 xl bound) T = true)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (hdim : Module.finrank (ZMod 3) V ≤ n + 1) (h : Fin n → V)
    (α : Fin n → Module.Dual (ZMod 3) V) (x : V) (hpair : ∀ i j, α i (h j) = C i j)
    (hind : LinearIndependent (ZMod 3) h) (hxne : x ≠ 0) (hxker : ∀ i, α i x = 0)
    (hxmem : x ∈ Submodule.span (ZMod 3) (Set.range h))
    (hs0 : (∀ v, (∀ i, α i v = 0) → v ∈ Submodule.span (ZMod 3) {x}) ∨
      ∃ T, verifyAll (mkFrame 3 n (n + 1) row 0 xl bound) T = true)
    (r : Fin n → (V ≃ₗ[ZMod 3] V)) (hr : ∀ i v, r i v = v - α i v • h i)
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hrA : ∀ i, r i ∈ A)
    (hrg : A = Subgroup.closure {s | s ∈ A ∧ GGLinRefl s}) (hnt : ∀ g ∈ A, ¬ IsTransv g)
    (hcard : Nat.card A ≤ bound) (t : V ≃ₗ[ZMod 3] V) (htA : t ∈ A) (htr : GGLinRefl t)
    (htm : t x ≠ x) : ZS.LinWeyl 3 A := by
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hle : n ≤ Module.finrank (ZMod 3) V := by simpa using hind.fintype_card_le_finrank
  obtain ⟨c, hc, hxc⟩ := x_coords C x₀ hker h α hpair x hxne hxker hxmem
  by_cases hd : Module.finrank (ZMod 3) V = n
  · obtain ⟨ε, hεh, hεα⟩ := coords_dim_n C h α hpair hind hd
    have hεx : ε x = c • x₀ := by
      rw [hxc, map_sum]
      simp only [map_smul, hεh]
      rw [sum_single_id (fun j => c * x₀ j)]
      funext j
      simp
    exact case_n row xl bound s₀ C x₀ hrow hxl hc_n ε h α x hεh hεα c hc hεx r hr A hrA hrg hnt hcard
      t htA htr htm
  · have hd1 : Module.finrank (ZMod 3) V = n + 1 := by omega
    obtain ⟨e', he'⟩ : ∃ e' : V, e' ∉ Submodule.span (ZMod 3) (Set.range h) := by
      by_contra hcon
      push Not at hcon
      apply hd
      have hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤ :=
        eq_top_iff.mpr (fun v _ => hcon v)
      have := finrank_span_eq_card hind
      rw [hspan, finrank_top] at this
      simpa using this
    obtain ⟨l, s, w, hl, hs01, hs0iff, hα⟩ := normalize_e C B x₀ i0 hx0 hB h α hpair e'
    have hsum : (∑ j, w j • h j) ∈ Submodule.span (ZMod 3) (Set.range h) :=
      Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
    have he : (l • e' - ∑ j, w j • h j) ∉ Submodule.span (ZMod 3) (Set.range h) := by
      intro hmem
      apply he'
      have : e' = l⁻¹ • ((l • e' - ∑ j, w j • h j) + ∑ j, w j • h j) := by
        rw [sub_add_cancel, smul_smul, inv_mul_cancel₀ hl, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ hmem hsum)
    obtain ⟨ε, hεh, hεe, hεα⟩ := coords_dim_succ C h α hpair hind _ he hd1
    have hεx : ε x = fun k : Fin (n + 1) => if hk : (k : ℕ) < n then c * x₀ ⟨k, hk⟩ else 0 := by
      rw [hxc, map_sum]
      simp only [map_smul, hεh]
      exact sum_single_castSucc (fun j => c * x₀ j)
    rcases hs01 with rfl | rfl
    · rcases hs0 with hfix | hc0
      · exfalso
        have hker0 : ∀ i, α i (l • e' - ∑ j, w j • h j) = 0 := fun i => by
          rw [hα i]; simp
        have hmem := hfix _ hker0
        rw [Submodule.mem_span_singleton] at hmem
        obtain ⟨a, ha⟩ := hmem
        apply he
        rw [← ha]
        exact Submodule.smul_mem _ _ (by
          rw [Submodule.mem_span_range_iff_exists_fun]
          exact ⟨fun j => c * x₀ j, hxc.symm⟩)
      · exact case_succ row xl bound C x₀ hrow hlen hxl hxlen 0 hc0 ε h α x _ i0 hi0 hεh hεα
          (fun i => by rw [hα i]; simp) c hc hεx r hr A hrA hrg hnt hcard t htA htr htm
    · exact case_succ row xl bound C x₀ hrow hlen hxl hxlen 1 hc_1 ε h α x _ i0 hi0 hεh hεα
        (fun i => by rw [hα i]; simp) c hc hεx r hr A hrA hrg hnt hcard t htA htr htm

end CFSG.ReflExt

end
