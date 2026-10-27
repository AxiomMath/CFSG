module

public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix

section Torus

variable {F : Type} [Field F]

@[expose] noncomputable def torusPair (c : F) (i j : Fin 3) : Fin 3 → F :=
  fun l => if l = i ∨ l = j then c else (c * c)⁻¹

theorem prod_torusPair {c : F} (hc : c ≠ 0) {i j : Fin 3} (hij : i ≠ j) :
    ∏ l, torusPair c i j l = 1 := by
  have hcc : c * c ≠ 0 := mul_ne_zero hc hc
  rw [Fin.prod_univ_three]
  fin_cases i <;> fin_cases j <;> simp [torusPair] at hij ⊢ <;> field_simp

@[expose] noncomputable def torusSL (c : F) (hc : c ≠ 0) (i j : Fin 3) (hij : i ≠ j) :
    SpecialLinearGroup (Fin 3) F :=
  ⟨diagonal (torusPair c i j), by rw [det_diagonal]; exact prod_torusPair hc hij⟩

theorem torusSL_coe (c : F) (hc : c ≠ 0) (i j : Fin 3) (hij : i ≠ j) :
    (torusSL c hc i j hij : Matrix (Fin 3) (Fin 3) F) = diagonal (torusPair c i j) := rfl

theorem torusPair_ne_one {c : F} (hc1 : c ≠ 1) (hcc : c * c ≠ 1) (i j l : Fin 3) :
    torusPair c i j l ≠ 1 := by
  unfold torusPair
  split_ifs
  · exact hc1
  · exact fun h => hcc (inv_eq_one.mp h)

theorem eq_zero_of_torusPair_fixed {c : F} (hc1 : c ≠ 1) (hcc : c * c ≠ 1) {i j : Fin 3}
    {v : Fin 3 → F} (hv : (diagonal (torusPair c i j)).mulVec v = v) : v = 0 := by
  funext l
  have h := congrFun hv l
  rw [mulVec_diagonal] at h
  have hne := torusPair_ne_one hc1 hcc i j l
  have h2 : (torusPair c i j l - 1) * v l = 0 := by rw [sub_mul, h, one_mul, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hne
  · simpa using h3

theorem commute_of_diagonal {A B : SpecialLinearGroup (Fin 3) F}
    (hA : ∃ f, (A : Matrix (Fin 3) (Fin 3) F) = diagonal f)
    (hB : ∃ f, (B : Matrix (Fin 3) (Fin 3) F) = diagonal f) : A * B = B * A := by
  obtain ⟨f, hf⟩ := hA
  obtain ⟨g, hg⟩ := hB
  apply Subtype.ext
  change (A : Matrix (Fin 3) (Fin 3) F) * B = B * A
  rw [hf, hg, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext l
  exact mul_comm _ _

theorem torusSL_mul_transvection {c : F} (hc : c ≠ 0) {i j : Fin 3} (hij : i ≠ j) (b : F) :
    torusSL c hc i j hij * SpecialLinearGroup.transvection hij b =
      SpecialLinearGroup.transvection hij b * torusSL c hc i j hij := by
  apply Subtype.ext
  change (torusSL c hc i j hij : Matrix (Fin 3) (Fin 3) F) *
      (SpecialLinearGroup.transvection hij b : Matrix (Fin 3) (Fin 3) F) =
    (SpecialLinearGroup.transvection hij b : Matrix (Fin 3) (Fin 3) F) *
      (torusSL c hc i j hij : Matrix (Fin 3) (Fin 3) F)
  rw [torusSL_coe, SpecialLinearGroup.transvection_coe]
  ext a a'
  simp only [diagonal_mul, mul_diagonal, Matrix.add_apply, one_apply, single_apply]
  by_cases h : i = a ∧ j = a'
  · obtain ⟨rfl, rfl⟩ := h
    simp [hij, torusPair, mul_comm]
  · by_cases haa : a = a'
    · subst haa
      simp [h]
    · simp [h, haa]

end Torus

variable {G : Type} [Group G]

theorem exists_mul_mem_centralizer_of_natural {K N₀ : Subgroup G} {F : Type} [Field F] {k : ℕ}
    {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hcc : c * c ≠ 1)
    {α : ↥K →* ↥(StatedSL 3 F)} (hα : Function.Surjective α)
    (hN : IsSumOfNaturalModulesVia K N₀ ⊥ α false k) {x : G}
    (hxker : ∀ a : ↥K, α a = 1 → (a : G) * x = x * a)
    (hxK : ∀ g ∈ K, x⁻¹ * (g * x * g⁻¹) ∈ N₀) :
    ∃ n ∈ N₀, x * n ∈ Subgroup.centralizer (K : Set G) := by
  classical
  obtain ⟨hKN, -, β, hβ, hβker, hβeq⟩ := hN
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  set e := specialLinearGroupEquivStatedSL 3 F with he
  have hmat : ∀ (g : ↥K) (γ : SpecialLinearGroup (Fin 3) F), α g = e γ →
      ((α g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = γ := by
    intro g γ h
    rw [h]
    exact specialLinearGroupEquivStatedSL_coe 3 F γ
  let cj : ↥K → ↥N₀ → ↥N₀ := fun g u =>
    ⟨g * u * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKN g.2) u).mp u.2⟩
  have hcj : ∀ (g : ↥K) (u : ↥N₀) (m : Fin k),
      Multiplicative.toAdd (β (cj g u)) m =
        ((α g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (Multiplicative.toAdd (β u) m) := by
    intro g u m
    have h := hβeq g u (cj g u) rfl m
    simpa [moduleAct] using h
  have hkerN : ∀ a : ↥K, α a = 1 → ∀ u : ↥N₀, (a : G) * u * (a : G)⁻¹ = u := by
    intro a ha u
    have h1 : Multiplicative.toAdd (β (cj a u)) = Multiplicative.toAdd (β u) := by
      funext m
      rw [hcj, ha]
      simp
    exact congrArg Subtype.val (hβinj (Multiplicative.toAdd.injective h1))
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  set d₀ := torusSL c hc0 0 1 h01 with hd₀
  obtain ⟨k₀, hk₀⟩ := hα (e d₀)
  set n₀ : ↥N₀ := ⟨x⁻¹ * (k₀ * x * (k₀ : G)⁻¹), hxK k₀ k₀.2⟩ with hn₀
  set w : Fin k → Fin 3 → F := fun m l =>
    Multiplicative.toAdd (β n₀) m l / (1 - torusPair c 0 1 l) with hw
  obtain ⟨n, hn⟩ := hβ (Multiplicative.ofAdd w)
  have hfix0 : n₀ * cj k₀ n = n := by
    apply hβinj
    apply Multiplicative.toAdd.injective
    funext m l
    rw [map_mul, toAdd_mul, Pi.add_apply, Pi.add_apply, hcj, hmat k₀ d₀ hk₀, hn, toAdd_ofAdd,
      hd₀, torusSL_coe, mulVec_diagonal, hw]
    have hne : (1 : F) - torusPair c 0 1 l ≠ 0 :=
      sub_ne_zero.mpr (torusPair_ne_one hc1 hcc 0 1 l).symm
    field_simp
    ring
  set x' := x * (n : G) with hx'
  have hk₀x' : (k₀ : G) * x' * (k₀ : G)⁻¹ = x' := by
    have h1 : ((n₀ * cj k₀ n : ↥N₀) : G) = n := congrArg Subtype.val hfix0
    have h2 : ((n₀ * cj k₀ n : ↥N₀) : G) =
        x⁻¹ * (k₀ * x * (k₀ : G)⁻¹) * ((k₀ : G) * n * (k₀ : G)⁻¹) := rfl
    calc (k₀ : G) * x' * (k₀ : G)⁻¹ =
          x * (x⁻¹ * (k₀ * x * (k₀ : G)⁻¹) * ((k₀ : G) * n * (k₀ : G)⁻¹)) := by
          rw [hx']; group
      _ = x' := by rw [← h2, h1]
  have hkerx' : ∀ a : ↥K, α a = 1 → (a : G) * x' * (a : G)⁻¹ = x' := by
    intro a ha
    have h1 := hxker a ha
    have h2 := hkerN a ha n
    calc (a : G) * x' * (a : G)⁻¹ = ((a : G) * x * (a : G)⁻¹) * ((a : G) * n * (a : G)⁻¹) := by
          rw [hx']; group
      _ = x' := by rw [h2, h1, hx']; group
  have hlift : ∀ g g' : ↥K, α g = α g' →
      (g : G) * x' * (g : G)⁻¹ = (g' : G) * x' * (g' : G)⁻¹ := by
    intro g g' h
    have ha : α (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h1 := hkerx' (g⁻¹ * g') ha
    have e1 : ((g⁻¹ * g' : ↥K) : G) = (g : G)⁻¹ * g' := by simp
    rw [e1] at h1
    calc (g : G) * x' * (g : G)⁻¹ =
          (g : G) * ((g : G)⁻¹ * g' * x' * ((g : G)⁻¹ * g')⁻¹) * (g : G)⁻¹ := by rw [h1]
      _ = (g' : G) * x' * (g' : G)⁻¹ := by group
  let P : SpecialLinearGroup (Fin 3) F → Prop := fun γ =>
    ∀ g : ↥K, α g = e γ → (g : G) * x' * (g : G)⁻¹ = x'
  have hP0 : P d₀ := fun g hg => (hlift g k₀ (hg.trans hk₀.symm)).trans hk₀x'
  have hPmul : ∀ A B, P A → P B → P (A * B) := by
    intro A B hA hB g hg
    obtain ⟨a, ha⟩ := hα (e A)
    obtain ⟨b, hb⟩ := hα (e B)
    have hab : α g = α (a * b) := by rw [hg, map_mul, map_mul, ha, hb]
    rw [hlift g (a * b) hab]
    have h1 := hA a ha
    have h2 := hB b hb
    calc ((a * b : ↥K) : G) * x' * ((a * b : ↥K) : G)⁻¹ =
          (a : G) * ((b : G) * x' * (b : G)⁻¹) * (a : G)⁻¹ := by
          simp only [Subgroup.coe_mul, _root_.mul_inv_rev]; group
      _ = x' := by rw [h2, h1]
  have hkey : ∀ γ d : SpecialLinearGroup (Fin 3) F, γ * d = d * γ →
      (∀ v : Fin 3 → F, (d : Matrix (Fin 3) (Fin 3) F).mulVec v = v → v = 0) → P d → P γ := by
    intro γ d hγd hfp hd g hg
    obtain ⟨kd, hkd⟩ := hα (e d)
    have hδmem : x'⁻¹ * ((g : G) * x' * (g : G)⁻¹) ∈ N₀ := by
      have e1 : x'⁻¹ * ((g : G) * x' * (g : G)⁻¹) =
          (n : G)⁻¹ * (x⁻¹ * (g * x * (g : G)⁻¹)) * ((g : G) * n * (g : G)⁻¹) := by
        rw [hx']; group
      rw [e1]
      exact N₀.mul_mem (N₀.mul_mem (N₀.inv_mem n.2) (hxK g g.2)) (cj g n).2
    set δ : ↥N₀ := ⟨_, hδmem⟩ with hδ
    have hδfix : cj kd δ = δ := by
      apply Subtype.ext
      have hkdx := hd kd hkd
      have hcomm : α (kd * g) = α (g * kd) := by
        rw [map_mul, map_mul, hkd, hg, ← map_mul, ← map_mul, hγd]
      have h3 := hlift (kd * g) (g * kd) hcomm
      have e3 : ((kd * g : ↥K) : G) * x' * ((kd * g : ↥K) : G)⁻¹ =
          (g : G) * x' * (g : G)⁻¹ := by
        rw [h3]
        calc ((g * kd : ↥K) : G) * x' * ((g * kd : ↥K) : G)⁻¹ =
              (g : G) * ((kd : G) * x' * (kd : G)⁻¹) * (g : G)⁻¹ := by
              simp only [Subgroup.coe_mul, _root_.mul_inv_rev]; group
          _ = (g : G) * x' * (g : G)⁻¹ := by rw [hkdx]
      show (kd : G) * (x'⁻¹ * ((g : G) * x' * (g : G)⁻¹)) * (kd : G)⁻¹ =
        x'⁻¹ * ((g : G) * x' * (g : G)⁻¹)
      calc (kd : G) * (x'⁻¹ * ((g : G) * x' * (g : G)⁻¹)) * (kd : G)⁻¹ =
            ((kd : G) * x' * (kd : G)⁻¹)⁻¹ *
              (((kd * g : ↥K) : G) * x' * ((kd * g : ↥K) : G)⁻¹) := by
            simp only [Subgroup.coe_mul, _root_.mul_inv_rev]; group
        _ = x'⁻¹ * ((g : G) * x' * (g : G)⁻¹) := by rw [hkdx, e3]
    have hδ1 : δ = 1 := by
      apply hβinj
      rw [map_one]
      apply Multiplicative.toAdd.injective
      funext m
      have h1 := hcj kd δ m
      rw [hδfix, hmat kd d hkd] at h1
      rw [hfp _ h1.symm]
      rfl
    have h4 : x'⁻¹ * ((g : G) * x' * (g : G)⁻¹) = 1 := congrArg Subtype.val hδ1
    calc (g : G) * x' * (g : G)⁻¹ = x' * (x'⁻¹ * ((g : G) * x' * (g : G)⁻¹)) := by group
      _ = x' := by rw [h4, mul_one]
  have hd₀diag : ∃ f, (d₀ : Matrix (Fin 3) (Fin 3) F) = diagonal f := ⟨_, torusSL_coe _ _ _ _ _⟩
  have hd₀fp : ∀ v : Fin 3 → F, (d₀ : Matrix (Fin 3) (Fin 3) F).mulVec v = v → v = 0 :=
    fun v hv => eq_zero_of_torusPair_fixed hc1 hcc hv
  have hPdiag : ∀ γ : SpecialLinearGroup (Fin 3) F,
      (∃ f, (γ : Matrix (Fin 3) (Fin 3) F) = diagonal f) → P γ :=
    fun γ hγ => hkey γ d₀ (commute_of_diagonal hγ hd₀diag) hd₀fp hP0
  have hPtr : ∀ (i j : Fin 3) (hij : i ≠ j) (b : F),
      P (SpecialLinearGroup.transvection hij b) := by
    intro i j hij b
    refine hkey _ (torusSL c hc0 i j hij) (torusSL_mul_transvection hc0 hij b).symm
      (fun v hv => eq_zero_of_torusPair_fixed hc1 hcc hv) (hPdiag _ ⟨_, torusSL_coe _ _ _ _ _⟩)
  have hPall : ∀ γ, P γ := fun γ =>
    SpecialLinearGroup.diagonal_transvection_induction' P γ
      (fun i j hij c' hc' => hPdiag _ ⟨_, SpecialLinearGroup.diag2n_coe hij c' hc'⟩) hPtr hPmul
  refine ⟨n, n.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
  have h1 := hPall (e.symm (α ⟨g, hg⟩)) ⟨g, hg⟩ (by simp)
  calc g * x' = (g * x' * g⁻¹) * g := by group
    _ = x' * g := by rw [show g * x' * g⁻¹ = x' from h1]

section Irreducible

variable {F : Type} [Field F]

theorem transvection_mulVec {i j : Fin 3} (hij : i ≠ j) (b : F) (v : Fin 3 → F) :
    (SpecialLinearGroup.transvection hij b : Matrix (Fin 3) (Fin 3) F).mulVec v =
      v + Pi.single i (b * v j) := by
  rw [SpecialLinearGroup.transvection_coe, add_mulVec, one_mulVec, single_mulVec]
  rfl

theorem eq_top_of_transvection_invariant (X : AddSubgroup (Fin 3 → F))
    (hX : ∀ (i j : Fin 3) (hij : i ≠ j) (b : F) (v : Fin 3 → F), v ∈ X →
      (SpecialLinearGroup.transvection hij b : Matrix (Fin 3) (Fin 3) F).mulVec v ∈ X)
    {v : Fin 3 → F} (hv : v ∈ X) (hv0 : v ≠ 0) : X = ⊤ := by
  classical
  have hsingle : ∀ (i j : Fin 3) (hij : i ≠ j) (b : F) (u : Fin 3 → F), u ∈ X →
      Pi.single i (b * u j) ∈ X := by
    intro i j hij b u hu
    have h1 := X.sub_mem (hX i j hij b u hu) hu
    rwa [transvection_mulVec, add_sub_cancel_left] at h1
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  have hoff : ∀ i, i ≠ j → ∀ a : F, Pi.single i a ∈ X := by
    intro i hij a
    have h1 := hsingle i j hij (a / v j) v hv
    rwa [div_mul_cancel₀ a hj] at h1
  have hall : ∀ i (a : F), Pi.single i a ∈ X := by
    intro i a
    by_cases hij : i = j
    · subst hij
      obtain ⟨l, hl⟩ : ∃ l : Fin 3, l ≠ i := by
        by_cases h0 : i = 0
        · exact ⟨1, by rw [h0]; decide⟩
        · exact ⟨0, fun h => h0 h.symm⟩
      have h1 := hsingle i l (Ne.symm hl) a (Pi.single l 1) (hoff l hl 1)
      simpa using h1
    · exact hoff i hij a
  refine eq_top_iff.mpr fun u _ => ?_
  rw [pi_eq_sum_univ u]
  refine X.sum_mem fun i _ => ?_
  have h1 := hall i (u i)
  have h2 : (u i • fun j => if i = j then (1 : F) else 0) = Pi.single i (u i) := by
    funext l
    by_cases h : i = l
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [h2]
  exact h1

end Irreducible

theorem eq_zero_of_fixed_of_natural_le {K W N₀ L : Subgroup G} {F F₂ : Type} [Field F] [Fintype F]
    [Field F₂] [Fintype F₂] (hcard : Fintype.card F = Fintype.card F₂) {k : ℕ}
    {N' : Subgroup ↥K} {α' : ↥K →* ↥(StatedSL 3 F)} {β' : ↥W →* Multiplicative (Fin 3 → F)}
    (hW : IsNaturalSectionWith K W ⊥ N' (StatedSL 3 F) α' β')
    {α : ↥K →* ↥(StatedSL 3 F₂)} (hN : IsSumOfNaturalModulesVia K N₀ ⊥ α false k)
    (hWN : W ≤ N₀)
    (hfp' : ∀ v : Fin 3 → F, (∀ l : ↥K, (l : G) ∈ L →
      ((α' l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v = v) → v = 0)
    (u : Fin 3 → F₂) (hu : ∀ l : ↥K, (l : G) ∈ L →
      ((α l : GL (Fin 3) F₂) : Matrix (Fin 3) (Fin 3) F₂).mulVec u = u) : u = 0 := by
  classical
  obtain ⟨hKW, hα', -, hβ', hβ'ker, hβ'eq⟩ := hW
  obtain ⟨hKN, -, β, hβ, hβker, hβeq⟩ := hN
  have hβ'inj : Function.Injective β' := by
    rw [← MonoidHom.ker_eq_bot_iff, hβ'ker, Subgroup.bot_subgroupOf]
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  let ψ : (Fin 3 → F) → ↥W := fun v => Function.surjInv hβ' (Multiplicative.ofAdd v)
  have hψ : ∀ v, β' (ψ v) = Multiplicative.ofAdd v := fun v => Function.surjInv_eq hβ' _
  have hψadd : ∀ v v', ψ (v + v') = ψ v * ψ v' := by
    intro v v'
    apply hβ'inj
    rw [map_mul, hψ, hψ, hψ, ofAdd_add]
  let cW : ↥K → ↥W → ↥W := fun a w =>
    ⟨a * w * (a : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKW a.2) w).mp w.2⟩
  have hψeq : ∀ (a : ↥K) (v : Fin 3 → F),
      ψ (((α' a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v) = cW a (ψ v) := by
    intro a v
    apply hβ'inj
    rw [hψ]
    have h1 := hβ'eq a (ψ v) (cW a (ψ v)) rfl
    rw [hψ, toAdd_ofAdd] at h1
    rw [← h1, ofAdd_toAdd]
  let θ : Fin k → (Fin 3 → F) → (Fin 3 → F₂) := fun m v =>
    Multiplicative.toAdd (β ⟨ψ v, hWN (ψ v).2⟩) m
  have hθadd : ∀ m v v', θ m (v + v') = θ m v + θ m v' := by
    intro m v v'
    have e1 : (⟨ψ (v + v'), hWN (ψ (v + v')).2⟩ : ↥N₀) =
        ⟨ψ v, hWN (ψ v).2⟩ * ⟨ψ v', hWN (ψ v').2⟩ := by
      apply Subtype.ext
      rw [hψadd]
      rfl
    show Multiplicative.toAdd (β ⟨ψ (v + v'), hWN (ψ (v + v')).2⟩) m = _
    rw [e1, map_mul, toAdd_mul, Pi.add_apply]
  have hθ0 : ∀ m, θ m 0 = 0 := by
    intro m
    have h1 := hθadd m 0 0
    rw [add_zero] at h1
    exact left_eq_add.mp h1
  have hθeq : ∀ (m : Fin k) (a : ↥K) (v : Fin 3 → F),
      θ m (((α' a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v) =
        ((α a : GL (Fin 3) F₂) : Matrix (Fin 3) (Fin 3) F₂).mulVec (θ m v) := by
    intro m a v
    have e1 : (⟨ψ (((α' a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v),
        hWN (ψ _).2⟩ : ↥N₀) = ⟨a * ψ v * (a : G)⁻¹, hWN (cW a (ψ v)).2⟩ := by
      apply Subtype.ext
      rw [hψeq]
    have h2 := hβeq a ⟨ψ v, hWN (ψ v).2⟩ ⟨a * ψ v * (a : G)⁻¹, hWN (cW a (ψ v)).2⟩ rfl m
    show Multiplicative.toAdd (β ⟨ψ _, hWN (ψ _).2⟩) m = _
    rw [e1]
    simpa [moduleAct] using h2
  obtain ⟨m, hm⟩ : ∃ m, θ m (Pi.single 0 1) ≠ 0 := by
    by_contra h
    push Not at h
    have h1 : β ⟨ψ (Pi.single 0 1), hWN (ψ _).2⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      funext m'
      exact h m'
    have h2 := hβinj (h1.trans (map_one β).symm)
    have h3 : ψ (Pi.single 0 1) = 1 := Subtype.ext (by simpa using congrArg Subtype.val h2)
    have h4 := hψ (Pi.single 0 1)
    rw [h3, map_one] at h4
    have h5 : (Pi.single 0 1 : Fin 3 → F) = 0 := by
      have h6 := congrArg Multiplicative.toAdd h4
      simpa using h6.symm
    have h7 := congrFun h5 0
    simp at h7
  let X : AddSubgroup (Fin 3 → F) :=
    { carrier := {v | θ m v = 0}
      add_mem' := fun {a b} ha hb => by
        show θ m (a + b) = 0
        rw [hθadd]
        rw [show θ m a = 0 from ha, show θ m b = 0 from hb, add_zero]
      zero_mem' := hθ0 m
      neg_mem' := fun {a} ha => by
        show θ m (-a) = 0
        have h1 := hθadd m a (-a)
        rw [add_neg_cancel, hθ0, show θ m a = 0 from ha, zero_add] at h1
        exact h1.symm }
  have hXinv : ∀ (i j : Fin 3) (hij : i ≠ j) (b : F) (v : Fin 3 → F), v ∈ X →
      (SpecialLinearGroup.transvection hij b : Matrix (Fin 3) (Fin 3) F).mulVec v ∈ X := by
    intro i j hij b v hv
    obtain ⟨a, ha⟩ := hα' (specialLinearGroupEquivStatedSL 3 F
      (SpecialLinearGroup.transvection hij b))
    have hmat : ((α' a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (SpecialLinearGroup.transvection hij b : Matrix (Fin 3) (Fin 3) F) := by
      rw [ha]
      exact specialLinearGroupEquivStatedSL_coe 3 F _
    show θ m _ = 0
    rw [← hmat, hθeq, show θ m v = 0 from hv, mulVec_zero]
  have hX0 : ∀ v, θ m v = 0 → v = 0 := by
    intro v hv
    by_contra hv0
    have htop := eq_top_of_transvection_invariant X hXinv (show v ∈ X from hv) hv0
    have h1 : (Pi.single 0 1 : Fin 3 → F) ∈ X := by rw [htop]; trivial
    exact hm h1
  have hθinj : Function.Injective (θ m) := by
    intro v v' h
    have h1 : θ m (v - v') = 0 := by
      have h2 := hθadd m (v - v') v'
      rw [sub_add_cancel, h] at h2
      have h3 : θ m (v - v') = θ m (v - v') + θ m v' - θ m v' := by rw [add_sub_cancel_right]
      rw [← h2, sub_self] at h3
      exact h3
    exact sub_eq_zero.mp (hX0 _ h1)
  have hθsurj : Function.Surjective (θ m) := by
    have hc : Fintype.card (Fin 3 → F) = Fintype.card (Fin 3 → F₂) := by
      simp [hcard]
    exact (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hc)).mp hθinj
  obtain ⟨v₀, rfl⟩ := hθsurj u
  have hv₀ : v₀ = 0 := by
    refine hfp' v₀ fun l hl => hθinj ?_
    rw [hθeq, hu l hl]
  rw [hv₀, hθ0]
end CFSG.Quasithin.H13.Ch4
