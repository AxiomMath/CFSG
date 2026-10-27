module

public import CFSG.RankThree.SubgroupLists.SchurCommutant

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.RepresentationTheory

variable {K : Type*} [Field K] {n : ℕ} {σ : Type*} [Fintype σ] [DecidableEq σ]

@[expose] def IsInvariant (N : Subgroup (GL (σ) K)) (W : Submodule K (σ → K)) : Prop :=
  ∀ x ∈ N, ∀ w ∈ W, (x : Matrix (σ) (σ) K) *ᵥ w ∈ W

@[expose] noncomputable def translate (g : GL (σ) K) (W : Submodule K (σ → K)) :
    Submodule K (σ → K) :=
  W.map (Matrix.toLin' (g : Matrix (σ) (σ) K))

@[expose] def IsTransitiveMonomial (G : Subgroup (GL (Fin n) K)) : Prop :=
  ∃ L : Fin n → Submodule K (Fin n → K), DirectSum.IsInternal L ∧
    (∀ i, Module.finrank K (L i) = 1) ∧
    (∀ g ∈ G, ∀ i, ∃ j, translate g (L i) = L j) ∧
    (∀ i j, ∃ g ∈ G, translate g (L i) = L j)

@[expose] def eig (N : Subgroup (GL (σ) K)) (χ : GL (σ) K → K) :
    Submodule K (σ → K) where
  carrier := {v | ∀ x ∈ N, (x : Matrix (σ) (σ) K) *ᵥ v = χ x • v}
  add_mem' {a b} ha hb x hx := by
    change (x : Matrix (σ) (σ) K) *ᵥ (a + b) = χ x • (a + b)
    rw [Matrix.mulVec_add, ha x hx, hb x hx, smul_add]
  zero_mem' x _ := by simp
  smul_mem' c v hv x hx := by
    change (x : Matrix (σ) (σ) K) *ᵥ (c • v) = χ x • (c • v)
    rw [Matrix.mulVec_smul, hv x hx, smul_comm]

theorem mem_eig {N : Subgroup (GL (σ) K)} {χ : GL (σ) K → K} {v : σ → K} :
    v ∈ eig N χ ↔ ∀ x ∈ N, (x : Matrix (σ) (σ) K) *ᵥ v = χ x • v :=
  Iff.rfl

theorem mem_translate {g : GL (σ) K} {W : Submodule K (σ → K)} {u : σ → K} :
    u ∈ translate g W ↔ ∃ w ∈ W, (g : Matrix (σ) (σ) K) *ᵥ w = u := by
  simp [translate, Matrix.toLin'_apply]

theorem mulVec_mem_translate {g : GL (σ) K} {W : Submodule K (σ → K)} {w : σ → K}
    (hw : w ∈ W) : (g : Matrix (σ) (σ) K) *ᵥ w ∈ translate g W :=
  mem_translate.mpr ⟨w, hw, rfl⟩

theorem gl_mulVec_mul (a b : GL (σ) K) (v : σ → K) :
    ((a * b : GL (σ) K) : Matrix (σ) (σ) K) *ᵥ v =
      (a : Matrix (σ) (σ) K) *ᵥ ((b : Matrix (σ) (σ) K) *ᵥ v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem gl_inv_mulVec_mulVec (g : GL (σ) K) (v : σ → K) :
    ((g⁻¹ : GL (σ) K) : Matrix (σ) (σ) K) *ᵥ ((g : Matrix (σ) (σ) K) *ᵥ v) =
      v := by
  rw [← gl_mulVec_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem gl_mulVec_inv_mulVec (g : GL (σ) K) (v : σ → K) :
    (g : Matrix (σ) (σ) K) *ᵥ (((g⁻¹ : GL (σ) K) : Matrix (σ) (σ) K) *ᵥ v) =
      v := by
  rw [← gl_mulVec_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem translate_mul (g h : GL (σ) K) (W : Submodule K (σ → K)) :
    translate (g * h) W = translate g (translate h W) := by
  ext u
  simp only [mem_translate]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, (gl_mulVec_mul g h w).symm⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, gl_mulVec_mul g h w⟩

theorem translate_one (W : Submodule K (σ → K)) : translate 1 W = W := by
  ext u
  simp [mem_translate]

theorem finrank_translate (g : GL (σ) K) (W : Submodule K (σ → K)) :
    Module.finrank K (translate g W) = Module.finrank K W := by
  have hinj : Function.Injective (Matrix.toLin' (g : Matrix (σ) (σ) K)) := by
    intro a b hab
    simp only [Matrix.toLin'_apply] at hab
    rw [← gl_inv_mulVec_mulVec g a, hab, gl_inv_mulVec_mulVec]
  exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W).symm

theorem translate_mono {g : GL (σ) K} {A B : Submodule K (σ → K)} (h : A ≤ B) :
    translate g A ≤ translate g B :=
  Submodule.map_mono h

theorem translate_finsetSup_le {ι : Type*} {g : GL (σ) K} {s : Finset ι}
    {A : ι → Submodule K (σ → K)} {X : Submodule K (σ → K)}
    (h : ∀ i ∈ s, translate g (A i) ≤ X) : translate g (s.sup A) ≤ X :=
  Submodule.map_le_iff_le_comap.mpr
    (Finset.sup_le fun i hi => Submodule.map_le_iff_le_comap.mp (h i hi))

theorem translate_inv_translate (g : GL (σ) K) (W : Submodule K (σ → K)) :
    translate g⁻¹ (translate g W) = W := by
  rw [← translate_mul, inv_mul_cancel, translate_one]

theorem translate_bot (g : GL (σ) K) : translate g (⊥ : Submodule K (σ → K)) = ⊥ :=
  Submodule.map_bot _

theorem translate_inf (g : GL (σ) K) (A B : Submodule K (σ → K)) :
    translate g (A ⊓ B) = translate g A ⊓ translate g B := by
  apply le_antisymm (le_inf (translate_mono inf_le_left) (translate_mono inf_le_right))
  intro u ⟨hA, hB⟩
  obtain ⟨a, ha, rfl⟩ := mem_translate.mp hA
  obtain ⟨b, hb, hab⟩ := mem_translate.mp hB
  have : b = a := by rw [← gl_inv_mulVec_mulVec g b, hab, gl_inv_mulVec_mulVec]
  subst this
  exact mulVec_mem_translate ⟨ha, hb⟩

section Normalized

variable {G N : Subgroup (GL (σ) K)}

theorem isInvariant_translate (hN : ∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    {W : Submodule K (σ → K)} (hW : IsInvariant N W) {g : GL (σ) K} (hg : g ∈ G) :
    IsInvariant N (translate g W) := by
  intro x hx u hu
  obtain ⟨w, hw, rfl⟩ := mem_translate.mp hu
  have hx' : g⁻¹ * x * g ∈ N := by
    simpa using hN g⁻¹ (G.inv_mem hg) x hx
  refine mem_translate.mpr ⟨_, hW _ hx' w hw, ?_⟩
  rw [← gl_mulVec_mul, ← gl_mulVec_mul]
  congr 2
  group

theorem isInvariant_inf {A B : Submodule K (σ → K)} (hA : IsInvariant N A)
    (hB : IsInvariant N B) : IsInvariant N (A ⊓ B) :=
  fun x hx _ hw => ⟨hA x hx _ hw.1, hB x hx _ hw.2⟩

theorem isInvariant_iff_le_comap {W : Submodule K (σ → K)} :
    IsInvariant N W ↔ ∀ x ∈ N, W ≤ W.comap (Matrix.toLin' (x : Matrix (σ) (σ) K)) := by
  refine ⟨fun h x hx w hw => ?_, fun h x hx w hw => ?_⟩
  · rw [Submodule.mem_comap, Matrix.toLin'_apply]
    exact h x hx w hw
  · have := h x hx hw
    rwa [Submodule.mem_comap, Matrix.toLin'_apply] at this

theorem isInvariant_finsetSup {ι : Type*} (s : Finset ι) {A : ι → Submodule K (σ → K)}
    (hA : ∀ i, IsInvariant N (A i)) : IsInvariant N (s.sup A) := by
  rw [isInvariant_iff_le_comap]
  intro x hx
  exact Finset.sup_le fun i hi =>
    ((isInvariant_iff_le_comap.mp (hA i)) x hx).trans (Submodule.comap_mono (Finset.le_sup hi))

theorem translate_eig (hN : ∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N) {g : GL (σ) K} (hg : g ∈ G)
    (χ : GL (σ) K → K) :
    translate g (eig N χ) = eig N (fun x => χ (g⁻¹ * x * g)) := by
  ext u
  rw [mem_translate, mem_eig]
  constructor
  · rintro ⟨w, hw, rfl⟩ x hx
    have hx' : g⁻¹ * x * g ∈ N := by simpa using hN g⁻¹ (G.inv_mem hg) x hx
    have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    calc (x : Matrix (σ) (σ) K) *ᵥ ((g : Matrix (σ) (σ) K) *ᵥ w)
        = (g : Matrix (σ) (σ) K) *ᵥ
            (((g⁻¹ * x * g : GL (σ) K) : Matrix (σ) (σ) K) *ᵥ w) := by
          rw [← gl_mulVec_mul, ← gl_mulVec_mul]
          congr 2
          group
      _ = χ (g⁻¹ * x * g) • ((g : Matrix (σ) (σ) K) *ᵥ w) := by
          rw [mem_eig.mp hw _ hx', Matrix.mulVec_smul]
  · intro hu
    refine ⟨((g⁻¹ : GL (σ) K) : Matrix (σ) (σ) K) *ᵥ u, ?_, gl_mulVec_inv_mulVec g u⟩
    intro x hx
    have hx' : g * x * g⁻¹ ∈ N := hN g hg x hx
    calc (x : Matrix (σ) (σ) K) *ᵥ
          (((g⁻¹ : GL (σ) K) : Matrix (σ) (σ) K) *ᵥ u)
        = ((g⁻¹ : GL (σ) K) : Matrix (σ) (σ) K) *ᵥ
            (((g * x * g⁻¹ : GL (σ) K) : Matrix (σ) (σ) K) *ᵥ u) := by
          rw [← gl_mulVec_mul, ← gl_mulVec_mul]
          congr 2
          group
      _ = χ x • (((g⁻¹ : GL (σ) K) : Matrix (σ) (σ) K) *ᵥ u) := by
          rw [hu _ hx', Matrix.mulVec_smul]
          congr 2
          group

end Normalized

theorem disjoint_eig_finsetSup (N : Subgroup (GL (σ) K)) (ψ : GL (σ) K → K)
    (S : Finset (GL (σ) K → K)) (hS : ∀ χ ∈ S, ∃ x ∈ N, χ x ≠ ψ x) :
    Disjoint (eig N ψ) (S.sup (eig N)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert φ S hφ ih =>
    have ih := ih fun χ hχ => hS χ (Finset.mem_insert_of_mem hχ)
    obtain ⟨x, hx, hxφ⟩ := hS φ (Finset.mem_insert_self φ S)
    rw [Finset.sup_insert, Submodule.disjoint_def]
    intro v hv hv'
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hv'
    let f : Module.End K (σ → K) :=
      Matrix.toLin' (x : Matrix (σ) (σ) K) - φ x • LinearMap.id
    have hfeig : ∀ χ, ∀ y ∈ eig N χ, f y = (χ x - φ x) • y := by
      intro χ y hy
      simp [f, Matrix.toLin'_apply, mem_eig.mp hy x hx, sub_smul]
    have hfS : ∀ y ∈ S.sup (eig N), f y ∈ S.sup (eig N) := by
      have : S.sup (eig N) ≤ (S.sup (eig N)).comap f := Finset.sup_le fun χ hχ y hy => by
        rw [Submodule.mem_comap, hfeig χ y hy]
        exact Submodule.smul_mem _ _ (Finset.le_sup (f := eig N) hχ hy)
      exact fun y hy => this hy
    have hfv : f (w + u) = (ψ x - φ x) • (w + u) := hfeig ψ _ hv
    rw [map_add, hfeig φ w hw, sub_self, zero_smul, zero_add] at hfv
    have hmem : (ψ x - φ x) • (w + u) ∈ eig N ψ := Submodule.smul_mem _ _ hv
    rw [← hfv] at hmem
    have h0 := Submodule.disjoint_def.mp ih _ hmem (hfS u hu)
    rw [hfv] at h0
    exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm hxφ))

omit [DecidableEq σ] in
theorem exists_finrank_finsetSup_eq_mul {ι : Type*} [DecidableEq ι]
    (A : ι → Submodule K (σ → K)) (d : ℕ) (hd : ∀ i, Module.finrank K (A i) = d)
    (hA : ∀ (s : Finset ι) (a : ι), A a ≤ s.sup A ∨ Disjoint (A a) (s.sup A)) (s : Finset ι) :
    ∃ m, Module.finrank K (s.sup A : Submodule K (σ → K)) = m * d := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s _ ih =>
    obtain ⟨m, hm⟩ := ih
    rw [Finset.sup_insert]
    rcases hA s a with h | h
    · exact ⟨m, by rw [sup_eq_right.mpr h, hm]⟩
    · refine ⟨m + 1, ?_⟩
      have := Submodule.finrank_sup_add_finrank_inf_eq (A a) (s.sup A)
      rw [disjoint_iff.mp h, finrank_bot, add_zero, hd, hm] at this
      rw [this]
      ring

omit [DecidableEq σ] in
theorem finrank_finsetSup_eq_card_mul {ι : Type*} [DecidableEq ι]
    (A : ι → Submodule K (σ → K)) {d : ℕ} (hd0 : 0 < d)
    (hd : ∀ i, Module.finrank K (A i) = d)
    (hA : ∀ (s : Finset ι) (a : ι), A a ∈ s.image A ∨ Disjoint (A a) (s.sup A))
    (s : Finset ι) :
    Module.finrank K (s.sup A : Submodule K (σ → K)) = (s.image A).card * d := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s _ ih =>
    rw [Finset.sup_insert, Finset.image_insert]
    rcases hA s a with h | h
    · obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp h
      have hle : A a ≤ s.sup A := hba ▸ Finset.le_sup hb
      rw [sup_eq_right.mpr hle, Finset.insert_eq_of_mem h, ih]
    · have hnot : A a ∉ s.image A := by
        intro hmem
        obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hmem
        have hle : A a ≤ s.sup A := hba ▸ Finset.le_sup hb
        have h0 : A a = ⊥ := disjoint_self.mp (h.mono_right hle)
        have := hd a
        rw [h0, finrank_bot] at this
        omega
      have := Submodule.finrank_sup_add_finrank_inf_eq (A a) (s.sup A)
      rw [disjoint_iff.mp h, finrank_bot, add_zero, hd, ih] at this
      rw [this, Finset.card_insert_of_notMem hnot]
      ring


theorem eig_congr {N : Subgroup (GL (σ) K)} {χ ψ : GL (σ) K → K}
    (h : ∀ x ∈ N, χ x = ψ x) : eig N χ = eig N ψ := by
  ext v
  simp only [mem_eig]
  exact ⟨fun hv x hx => by rw [← h x hx]; exact hv x hx,
    fun hv x hx => by rw [h x hx]; exact hv x hx⟩

theorem scalar_mulVec (c : K) (v : σ → K) : Matrix.scalar σ c *ᵥ v = c • v := by
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem irreducible_or_scalar_or_transitiveMonomial (hn : n.Prime)
    {G N : Subgroup (GL (Fin n) K)} [Finite G] (hG : IsIrreducibleMatrixRep G.subtype)
    (hN : ∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N) :
    IsIrreducibleMatrixRep N.subtype ∨
      (∀ x ∈ N, ∃ c : K, (x : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) c) ∨
      IsTransitiveMonomial G := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : NeZero n := ⟨hn.ne_zero⟩
  have hGinv : ∀ X : Submodule K (Fin n → K), (∀ g ∈ G, translate g X ≤ X) → X ≠ ⊥ → X = ⊤ := by
    intro X hX hX0
    rcases hG X (fun g w hw => hX g g.2 (mulVec_mem_translate hw)) with h | h
    · exact absurd h hX0
    · exact h
  have hsum : ∀ W : Submodule K (Fin n → K), W ≠ ⊥ →
      (Finset.univ : Finset G).sup (fun g => translate (g : GL (Fin n) K) W) = ⊤ := by
    intro W hW0
    apply hGinv
    · intro g hg
      refine translate_finsetSup_le fun h _ => ?_
      rw [← translate_mul]
      have := Finset.le_sup (f := fun g : G => translate (g : GL (Fin n) K) W)
        (Finset.mem_univ (⟨g * h, G.mul_mem hg h.2⟩ : G))
      exact this
    · intro hbot
      apply hW0
      have h1 : translate ((1 : G) : GL (Fin n) K) W ≤
          (Finset.univ : Finset G).sup (fun g => translate (g : GL (Fin n) K) W) :=
        Finset.le_sup (f := fun g : G => translate (g : GL (Fin n) K) W) (Finset.mem_univ 1)
      rw [hbot, OneMemClass.coe_one, translate_one, le_bot_iff] at h1
      exact h1
  have hex : ∃ k, ∃ U : Submodule K (Fin n → K), U ≠ ⊥ ∧ IsInvariant N U ∧
      Module.finrank K U = k :=
    ⟨n, ⊤, top_ne_bot, fun _ _ _ _ => Submodule.mem_top, by simp⟩
  obtain ⟨W, hW0, hWinv, hWe⟩ := Nat.find_spec hex
  have hmin : ∀ U : Submodule K (Fin n → K), U ≠ ⊥ → IsInvariant N U →
      Nat.find hex ≤ Module.finrank K U :=
    fun U hU hUi => Nat.find_min' hex ⟨U, hU, hUi, rfl⟩
  have hatom : ∀ g ∈ G, ∀ X, IsInvariant N X →
      translate g W ≤ X ∨ Disjoint (translate g W) X := by
    intro g hg X hX
    by_cases h : translate g W ⊓ X = ⊥
    · exact Or.inr (disjoint_iff.mpr h)
    · left
      have hle : translate g W ⊓ X ≤ translate g W := inf_le_left
      have hfr := hmin _ h (isInvariant_inf (isInvariant_translate hN hWinv hg) hX)
      have heq : translate g W ⊓ X = translate g W :=
        Submodule.eq_of_le_of_finrank_le hle (by rw [finrank_translate, hWe]; exact hfr)
      exact heq ▸ inf_le_right
  have he : Nat.find hex ∣ n := by
    obtain ⟨m, hm⟩ := exists_finrank_finsetSup_eq_mul
      (fun g : G => translate (g : GL (Fin n) K) W) (Nat.find hex)
      (fun g => by rw [finrank_translate, hWe])
      (fun s a => hatom a a.2 _
        (isInvariant_finsetSup s fun g => isInvariant_translate hN hWinv g.2))
      Finset.univ
    rw [hsum W hW0, finrank_top, Module.finrank_fin_fun] at hm
    exact ⟨m, hm.trans (mul_comm _ _)⟩
  rcases (Nat.dvd_prime hn).mp he with he1 | hen
  swap
  ·
    left
    intro U hU
    by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    · right
      have := hmin U hU0 (fun x hx w hw => hU ⟨x, hx⟩ w hw)
      rw [hen] at this
      exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le U)
        (by rwa [Module.finrank_fin_fun]))
  right
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hWspan : W = K ∙ w := by
    symm
    apply Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hwW)
    rw [hWe, he1, finrank_span_singleton hw0]
  obtain ⟨i₀, hi₀⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (funext h)
  let χ : GL (Fin n) K → K := fun x => ((x : Matrix (Fin n) (Fin n) K) *ᵥ w) i₀ / w i₀
  have hχ : ∀ x ∈ N, (x : Matrix (Fin n) (Fin n) K) *ᵥ w = χ x • w := by
    intro x hx
    have hmem : (x : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ K ∙ w := hWspan ▸ hWinv x hx w hwW
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have : χ x = c := by
      simp only [χ]
      rw [← hc, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hi₀, mul_one]
    rw [this, hc]
  have hwE : w ∈ eig N χ := hχ
  have hE0 : eig N χ ≠ ⊥ := fun h => hw0 ((Submodule.mem_bot K).mp (h ▸ hwE))
  let A : G → Submodule K (Fin n → K) := fun g => translate (g : GL (Fin n) K) (eig N χ)
  let conj : G → GL (Fin n) K → K := fun g x => χ ((g : GL (Fin n) K)⁻¹ * x * g)
  have hA : ∀ g : G, A g = eig N (conj g) := fun g => translate_eig hN g.2 χ
  have hP : ∀ (s : Finset G) (a : G), A a ∈ s.image A ∨ Disjoint (A a) (s.sup A) := by
    intro s a
    by_cases h : A a ∈ s.image A
    · exact Or.inl h
    · right
      have hsup : s.sup A = (s.image conj).sup (eig N) := by
        rw [Finset.sup_image]
        exact Finset.sup_congr rfl fun g _ => hA g
      rw [hsup, hA a]
      apply disjoint_eig_finsetSup
      intro ψ hψ
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hψ
      by_contra hall
      push Not at hall
      exact h (Finset.mem_image.mpr ⟨g, hg, by rw [hA g, hA a]; exact eig_congr hall⟩)
  have hd0 : 0 < Module.finrank K (eig N χ) :=
    Nat.pos_of_ne_zero fun h => hE0 (Submodule.finrank_eq_zero.mp h)
  have hcount := finrank_finsetSup_eq_card_mul A hd0 (fun g => finrank_translate _ _) hP
    Finset.univ
  rw [hsum _ hE0, finrank_top, Module.finrank_fin_fun] at hcount
  rcases (Nat.dvd_prime hn).mp (Dvd.intro_left _ hcount.symm) with hd1 | hdn
  swap
  ·
    left
    have hEtop : eig N χ = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [hdn, Module.finrank_fin_fun])
    intro x hx
    refine ⟨χ x, ?_⟩
    rw [Matrix.ext_iff_mulVec]
    intro v
    have hv : v ∈ eig N χ := hEtop ▸ Submodule.mem_top
    rw [mem_eig.mp hv x hx, scalar_mulVec]
  right
  set 𝓔 := (Finset.univ : Finset G).image A with h𝓔
  have hcard : 𝓔.card = n := by rw [hd1, mul_one] at hcount; exact hcount.symm
  let e𝓔 : 𝓔 ≃ Fin n := 𝓔.equivFin.trans (finCongr hcard)
  let L : Fin n → Submodule K (Fin n → K) := fun i => (e𝓔.symm i : Submodule K (Fin n → K))
  have hLmem : ∀ i, ∃ g : G, A g = L i := fun i => by
    obtain ⟨g, -, hg⟩ := Finset.mem_image.mp (e𝓔.symm i).2
    exact ⟨g, hg⟩
  have hAL : ∀ g : G, ∃ i, L i = A g := fun g =>
    ⟨e𝓔 ⟨A g, Finset.mem_image_of_mem _ (Finset.mem_univ g)⟩, by simp [L]⟩
  have hLinj : Function.Injective L := fun i j h => e𝓔.symm.injective (Subtype.ext h)
  refine ⟨L, ?_, fun i => ?_, fun g hg i => ?_, fun i j => ?_⟩
  · apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · intro i
      obtain ⟨a, ha⟩ := hLmem i
      let s : Finset G := Finset.univ.filter fun g => A g ≠ L i
      have hnot : A a ∉ s.image A := by
        intro hmem
        obtain ⟨g, hg, hga⟩ := Finset.mem_image.mp hmem
        exact (Finset.mem_filter.mp hg).2 (hga.trans ha)
      have hdisj := (hP s a).resolve_left hnot
      rw [ha] at hdisj
      refine hdisj.mono_right (iSup₂_le fun j hj => ?_)
      obtain ⟨g, hg⟩ := hLmem j
      rw [← hg]
      refine Finset.le_sup (f := A) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      rw [hg]
      exact fun h => hj (hLinj h)
    · rw [eq_top_iff, ← hsum _ hE0]
      refine Finset.sup_le fun g _ => ?_
      obtain ⟨i, hi⟩ := hAL g
      have := le_iSup L i
      rw [hi] at this
      exact this
  · obtain ⟨g, hg⟩ := hLmem i
    rw [← hg, finrank_translate, hd1]
  · obtain ⟨h, hh⟩ := hLmem i
    obtain ⟨j, hj⟩ := hAL ⟨g * h, G.mul_mem hg h.2⟩
    refine ⟨j, ?_⟩
    rw [hj, ← hh]
    exact (translate_mul _ _ _).symm
  · obtain ⟨h, hh⟩ := hLmem i
    obtain ⟨h', hh'⟩ := hLmem j
    refine ⟨(h' : GL (Fin n) K) * (h : GL (Fin n) K)⁻¹, G.mul_mem h'.2 (G.inv_mem h.2), ?_⟩
    rw [← hh, ← hh']
    change translate _ (translate _ _) = translate _ _
    rw [← translate_mul, inv_mul_cancel_right]


theorem irreducible_prime_degree_reduction [Finite K] (hn : n.Prime)
    {G : Subgroup (GL (Fin n) K)} (hG : IsIrreducibleMatrixRep G.subtype) :
    (∃ H ≤ G, (∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) ∧ IsIrreducibleMatrixRep H.subtype ∧
        IsCyclic H ∧ Nat.card H ∣ Nat.card K ^ n - 1 ∧ ¬ Nat.card H ∣ Nat.card K - 1) ∨
      IsTransitiveMonomial G ∨
      ((∀ M : Matrix (Fin n) (Fin n) K, (∀ g ∈ G, (g : Matrix (Fin n) (Fin n) K) * M = M * g) →
          ∃ c : K, M = Matrix.scalar (Fin n) c) ∧
        (∀ N : Subgroup (GL (Fin n) K), (∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N) →
          IsIrreducibleMatrixRep N.subtype ∨
            ∀ x ∈ N, ∃ c : K, (x : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) c) ∧
        (∀ N ≤ G, (∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N) → (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) →
          ∀ x ∈ N, ∃ c : K, (x : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) c)) := by
  classical
  rcases scalar_commutant_or_cyclic hn hG with hscal | hcyc
  swap
  · exact Or.inl ⟨G, le_rfl, fun g hg x hx => G.mul_mem (G.mul_mem hg hx) (G.inv_mem hg), hG,
      hcyc⟩
  by_cases hmono : IsTransitiveMonomial G
  · exact Or.inr (Or.inl hmono)
  have hcliff : ∀ N : Subgroup (GL (Fin n) K), (∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N) →
      IsIrreducibleMatrixRep N.subtype ∨
        ∀ x ∈ N, ∃ c : K, (x : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) c :=
    fun N hN => (irreducible_or_scalar_or_transitiveMonomial hn hG hN).imp_right
      fun h => h.resolve_right hmono
  by_cases hab : ∃ N ≤ G, (∀ g ∈ G, ∀ x ∈ N, g * x * g⁻¹ ∈ N) ∧
      (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧ IsIrreducibleMatrixRep N.subtype
  · obtain ⟨N, hNG, hN, hcomm, hirr⟩ := hab
    exact Or.inl ⟨N, hNG, hN, hirr, cyclic_of_irreducible_of_commute hn hirr hcomm⟩
  · refine Or.inr (Or.inr ⟨hscal, hcliff, fun N hNG hN hcomm => ?_⟩)
    exact (hcliff N hN).resolve_left fun hirr => hab ⟨N, hNG, hN, hcomm, hirr⟩

end CFSG.RankThree.SubgroupLists
