module

public import CFSG.RankThree.PartOne.FIS.W4
public import CFSG.Fischer.Classification.Basic.Local

public section

namespace CFSG.RankThree.PartOne.FIS

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification Equiv Equiv.Perm

structure PermInput (n : ℕ) : Prop where
  eq_swaps : ∀ {T : Set (Perm (Fin n))}, (∀ t ∈ T, t * t = 1 ∧ t ≠ 1) →
    (∀ s ∈ T, ∀ t ∈ T, s * t * s⁻¹ ∈ T) → Subgroup.closure T = ⊤ →
    (∀ s ∈ T, ∀ t ∈ T, orderOf (s * t) ≤ 3) → T = {σ | σ.IsSwap}
  no_three : ∀ {a b c : Perm (Fin n)}, a.IsSwap → b.IsSwap → c.IsSwap → a ≠ b → a ≠ c → b ≠ c →
    a * b = b * a → a * c = c * a → b * c = c * b → False
  distinguish : 4 ≤ n → ∀ {a d : Perm (Fin n)}, a.IsSwap → d.IsSwap → a * d ≠ d * a →
    ∃ t : Perm (Fin n), t.IsSwap ∧ ¬ ((t ≠ d ∧ t * d = d * t) ↔ (t ≠ a ∧ t * a = a * t))
  star_char : ∀ {B : Set (Perm (Fin n))}, (∀ σ ∈ B, σ.IsSwap) → B.Nonempty →
    (∀ a ∈ B, ∀ b ∈ B, a ≠ b → a * b ≠ b * a) →
    (∀ f : Perm (Fin n), f.IsSwap → f ∉ B → ∀ e ∈ B, f * e * f⁻¹ ∈ B) →
    (∃ p : Fin n, B = {σ | σ.IsSwap ∧ σ p ≠ p}) ∨ (n = 3 ∧ B = {σ | σ.IsSwap})
  star_inj : ∀ {p q : Fin n}, {σ : Perm (Fin n) | σ.IsSwap ∧ σ p ≠ p} =
    {σ | σ.IsSwap ∧ σ q ≠ q} → p = q
  stab : ∀ (p : Fin n) {σ : Perm (Fin n)}, σ p = p →
    σ ∈ Subgroup.closure {τ : Perm (Fin n) | τ.IsSwap ∧ τ p = p}
  ncard : {σ : Perm (Fin n) | σ.IsSwap}.ncard = n * (n - 1) / 2
  noncomm_three : n = 3 → ∀ {a b : Perm (Fin n)}, a.IsSwap → b.IsSwap → a ≠ b → a * b ≠ b * a

structure LocalIso {X : Type} [Group X] (E : Set X) (d : X) (n : ℕ) where
  φ : ↥(LocalGroup E d) ≃* Perm (Fin n)
  isSwap_iff : ∀ t : ↥(LocalGroup E d), (t : X) ∈ LocalClass E d ↔ (φ t).IsSwap

variable {X : Type} [Group X] {E : Set X} {d : X} {n : ℕ}

section Local

theorem LocalIso.swap_of_mem (L : LocalIso E d n) {f : X} (hf : f ∈ LocalClass E d) :
    (L.φ ⟨f, mem_localGroup hf⟩).IsSwap :=
  (L.isSwap_iff ⟨f, mem_localGroup hf⟩).1 hf

theorem LocalIso.mem_of_swap (L : LocalIso E d n) {σ : Perm (Fin n)} (hσ : σ.IsSwap) :
    ((L.φ.symm σ : ↥(LocalGroup E d)) : X) ∈ LocalClass E d :=
  (L.isSwap_iff _).2 (by simpa using hσ)

theorem conj_mem_closure_insert (hP : Pair X E) :
    ∀ g ∈ Subgroup.closure (insert d (LocalClass E d)), ∀ e ∈ LocalClass E d,
      g * e * g⁻¹ ∈ LocalClass E d ∧ g⁻¹ * e * g ∈ LocalClass E d := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    intro e he
    rcases hy with hy | hy
    · rw [hy]
      have h1 : d * e * d⁻¹ = e := by rw [← he.2.2]; group
      have h2 : d⁻¹ * e * d = e := by
        calc d⁻¹ * e * d = d⁻¹ * (e * d) := by group
          _ = d⁻¹ * (d * e) := by rw [he.2.2]
          _ = e := by group
      exact ⟨by rw [h1]; exact he, by rw [h2]; exact he⟩
    · have hy' : y⁻¹ = y := Pair.inv_eq hP hy.1
      have h := Pair.conj_mem_localClass_of_mem hP (mem_localGroup hy) he
      rw [hy'] at h ⊢
      exact ⟨h, h⟩
  | one => intro e he; simpa using he
  | mul g h _ _ ihg ihh =>
    intro e he
    constructor
    · have := (ihg _ (ihh e he).1).1
      rwa [show g * (h * e * h⁻¹) * g⁻¹ = g * h * e * (g * h)⁻¹ by group] at this
    · have := (ihh _ (ihg e he).2).2
      rwa [show h⁻¹ * (g⁻¹ * e * g) * h = (g * h)⁻¹ * e * (g * h) by group] at this
  | inv g _ ihg =>
    intro e he
    exact ⟨by simpa using (ihg e he).2, by simpa using (ihg e he).1⟩

theorem no_three_at (hI : PermInput n) (hP : Pair X E) (hd : d ∈ E) (L : LocalIso E d n)
    {x : X} (hx : x ∈ E) {y₁ y₂ y₃ : X} (h1 : y₁ ∈ LocalClass E x) (h2 : y₂ ∈ LocalClass E x)
    (h3 : y₃ ∈ LocalClass E x) (h12 : y₁ ≠ y₂) (h13 : y₁ ≠ y₃) (h23 : y₂ ≠ y₃)
    (c12 : y₁ * y₂ = y₂ * y₁) (c13 : y₁ * y₃ = y₃ * y₁) (c23 : y₂ * y₃ = y₃ * y₂) : False := by
  obtain ⟨g, hg⟩ := isConj_iff.1 (Pair.isConj hP hd hx)
  have key : ∀ y ∈ LocalClass E x, g⁻¹ * y * g ∈ LocalClass E d := by
    intro y hy
    have := (Pair.conj_mem_localClass_iff hP g⁻¹ (e := x) (f := y)).2 hy
    rw [← hg, show g⁻¹ * (g * d * g⁻¹) * g⁻¹⁻¹ = d by group] at this
    simpa using this
  let img : ∀ y, y ∈ LocalClass E x → Perm (Fin n) :=
    fun y hy => L.φ ⟨g⁻¹ * y * g, mem_localGroup (key y hy)⟩
  have swp : ∀ y (hy : y ∈ LocalClass E x), (img y hy).IsSwap :=
    fun y hy => L.swap_of_mem (key y hy)
  have inj : ∀ y y' (hy : y ∈ LocalClass E x) (hy' : y' ∈ LocalClass E x), y ≠ y' →
      img y hy ≠ img y' hy' := by
    intro y y' hy hy' hne h
    have h' := L.φ.injective h
    have := congrArg Subtype.val h'
    apply hne
    have h'' : g⁻¹ * y * g = g⁻¹ * y' * g := this
    exact mul_left_cancel (mul_right_cancel h'')
  have com : ∀ y y' (hy : y ∈ LocalClass E x) (hy' : y' ∈ LocalClass E x), y * y' = y' * y →
      img y hy * img y' hy' = img y' hy' * img y hy := by
    intro y y' hy hy' h
    show L.φ _ * L.φ _ = L.φ _ * L.φ _
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show g⁻¹ * y * g * (g⁻¹ * y' * g) = g⁻¹ * y' * g * (g⁻¹ * y * g)
    calc g⁻¹ * y * g * (g⁻¹ * y' * g) = g⁻¹ * (y * y') * g := by group
      _ = g⁻¹ * (y' * y) * g := by rw [h]
      _ = g⁻¹ * y' * g * (g⁻¹ * y * g) := by group
  exact hI.no_three (swp y₁ h1) (swp y₂ h2) (swp y₃ h3) (inj _ _ h1 h2 h12) (inj _ _ h1 h3 h13)
    (inj _ _ h2 h3 h23) (com _ _ h1 h2 c12) (com _ _ h1 h3 c13) (com _ _ h2 h3 c23)

@[expose] def Bset (E : Set X) (d x : X) : Set X :=
  {e | e ∈ LocalClass E d ∧ e * x ≠ x * e}

theorem Bset_nonempty (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a)
    (hd : d ∈ E) {x : X} (hx : x ∈ farClass E d) : (Bset E d x).Nonempty := by
  have := Pair.finite hP
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hsub : LocalClass E d ⊆ LocalClass E x := by
    intro e he
    refine ⟨he.1, ?_, ?_⟩
    · intro hex
      rw [hex] at he
      exact hx.2 he.2.2
    · by_contra hne
      have : e ∈ Bset E d x := ⟨he, hne⟩
      rw [hempty] at this
      exact this
  have hle : (LocalClass E x).ncard ≤ (LocalClass E d).ncard :=
    (Pair.ncard_localClass_eq hP hx.1 hd).le
  have heq := Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)
  have hdx := Pair.eq_of_localClass_eq hP hZ hS (not_forall_commute hna) hd hx.1 heq
  exact hx.2 (by rw [hdx])

theorem ncard_localClass_three (hI : PermInput 3) (L : LocalIso E d 3) :
    (LocalClass E d).ncard = 3 := by
  have himg : LocalClass E d = Subtype.val '' (L.φ.symm '' {σ : Perm (Fin 3) | σ.IsSwap}) := by
    ext f
    constructor
    · intro hf
      refine ⟨⟨f, mem_localGroup hf⟩, ⟨L.φ ⟨f, mem_localGroup hf⟩, L.swap_of_mem hf, by simp⟩, rfl⟩
    · rintro ⟨t, ⟨σ, hσ, rfl⟩, rfl⟩
      exact L.mem_of_swap hσ
  rw [himg, Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_image_of_injective _ L.φ.symm.injective, hI.ncard]

theorem no_full_B (hI : PermInput 3) (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a)
    (hd : d ∈ E) (L : LocalIso E d 3) {x : X} (hx : x ∈ farClass E d)
    (hfull : ∀ e ∈ LocalClass E d, e * x ≠ x * e) : False := by
  have hfull' : ∀ x' ∈ farClass E d, ∀ e ∈ LocalClass E d, e * x' ≠ x' * e := by
    intro x' hx' e he
    obtain ⟨g, hg, hgx⟩ := Pair.exists_conj_far hP hZ hS hna hd hx.1 hx.2 x' hx'.1 hx'.2
    have hge := (conj_mem_closure_insert hP g hg e he).2
    have h1 := hfull _ hge
    rw [← hgx]
    intro h
    apply h1
    calc (g⁻¹ * e * g) * x = g⁻¹ * (e * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * e) * g := by rw [h]
      _ = x * (g⁻¹ * e * g) := by group
  have := Pair.finite hP
  have hswap : (swap (0 : Fin 3) 1).IsSwap := ⟨0, 1, by decide, rfl⟩
  set e₀ : X := ((L.φ.symm (swap (0 : Fin 3) 1) : ↥(LocalGroup E d)) : X) with he₀
  have he₀T : e₀ ∈ LocalClass E d := L.mem_of_swap hswap
  have hsub : LocalClass E e₀ ⊆ {d} := by
    intro y hy
    have hyd : y * d = d * y := by
      by_contra hne
      have hyfar : y ∈ farClass E d := ⟨hy.1, hne⟩
      exact hfull' y hyfar e₀ he₀T hy.2.2.symm
    by_cases hyd' : y = d
    · exact hyd'
    · exfalso
      have hyT : y ∈ LocalClass E d := ⟨hy.1, hyd', hyd⟩
      have hne : L.φ ⟨y, mem_localGroup hyT⟩ ≠ L.φ ⟨e₀, mem_localGroup he₀T⟩ := by
        intro h
        have h' := congrArg Subtype.val (L.φ.injective h)
        exact hy.2.1 h'
      have hnc := hI.noncomm_three rfl (L.swap_of_mem hyT) (L.swap_of_mem he₀T) hne
      apply hnc
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hy.2.2
  have hcard : (LocalClass E e₀).ncard = (LocalClass E d).ncard :=
    Pair.ncard_localClass_eq hP he₀T.1 hd
  have hle : (LocalClass E e₀).ncard ≤ ({d} : Set X).ncard :=
    Set.ncard_le_ncard hsub (Set.finite_singleton d)
  rw [hcard, ncard_localClass_three hI L, Set.ncard_singleton] at hle
  omega

theorem exists_star (hI : PermInput n) (h3 : 3 ≤ n) (hP : Pair X E)
    (hZ : Subgroup.center X = ⊥) (hS : IsSimpleGroup (commutator X))
    (hna : ∃ a b : commutator X, a * b ≠ b * a) (hd : d ∈ E) (L : LocalIso E d n)
    {x : X} (hx : x ∈ farClass E d) :
    ∃ p : Fin n, ∀ e (he : e ∈ LocalClass E d),
      (e * x ≠ x * e ↔ L.φ ⟨e, mem_localGroup he⟩ p ≠ p) := by
  set B : Set (Perm (Fin n)) :=
    {σ | ∃ e : ↥(LocalGroup E d), (e : X) ∈ Bset E d x ∧ L.φ e = σ} with hB
  have hBmem : ∀ e (he : e ∈ LocalClass E d),
      L.φ ⟨e, mem_localGroup he⟩ ∈ B ↔ e * x ≠ x * e := by
    intro e he
    constructor
    · rintro ⟨e', he', hee'⟩
      have : e' = ⟨e, mem_localGroup he⟩ := L.φ.injective hee'
      rw [this] at he'
      exact he'.2
    · intro h
      exact ⟨⟨e, mem_localGroup he⟩, ⟨he, h⟩, rfl⟩
  have hBsw : ∀ σ ∈ B, σ.IsSwap := by
    rintro σ ⟨e, he, rfl⟩
    exact (L.isSwap_iff e).1 he.1
  have hBne : B.Nonempty := by
    obtain ⟨e, he⟩ := Bset_nonempty hP hZ hS hna hd hx
    exact ⟨_, (hBmem e he.1).2 he.2⟩
  have hBnc : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → a * b ≠ b * a := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩ hne hcomm
    have hee' : e ≠ e' := fun h => hne (by rw [h])
    have hcomm' : e * e' = e' * e := L.φ.injective (by rw [map_mul, map_mul]; exact hcomm)
    have hc : (e : X) * (e' : X) = (e' : X) * (e : X) := congrArg Subtype.val hcomm'
    obtain ⟨y₁, h1, y₂, h2, y₃, h3', h12, h13, h23, c12, c13, c23⟩ :=
      w4 hP hx.1 hd he.1.1 he'.1.1 he.1.2.2.symm he'.1.2.2.symm hc he.1.2.1.symm he'.1.2.1.symm
        (fun h => hee' (Subtype.ext h)) hx.2 (fun h => he.2 h.symm) (fun h => he'.2 h.symm)
    exact no_three_at hI hP hd L hx.1 h1 h2 h3' h12 h13 h23 c12 c13 c23
  have hBinv : ∀ f : Perm (Fin n), f.IsSwap → f ∉ B → ∀ e ∈ B, f * e * f⁻¹ ∈ B := by
    rintro f hf hfB _ ⟨e, he, rfl⟩
    set fH : ↥(LocalGroup E d) := L.φ.symm f with hfH
    have hfT : (fH : X) ∈ LocalClass E d := L.mem_of_swap hf
    have hfx : (fH : X) * x = x * (fH : X) := by
      by_contra hne
      apply hfB
      refine ⟨fH, ⟨hfT, hne⟩, by simp [hfH]⟩
    refine ⟨fH * e * fH⁻¹, ⟨?_, ?_⟩, by simp [hfH]⟩
    · have := Pair.conj_mem_localClass_of_mem hP fH.2 he.1
      simpa using this
    · intro hcomm
      apply he.2
      have hcomm' : (fH : X) * (e : X) * (fH : X)⁻¹ * x =
          x * ((fH : X) * (e : X) * (fH : X)⁻¹) := by
        simpa using hcomm
      calc (e : X) * x = (fH : X)⁻¹ * ((fH : X) * (e : X) * (fH : X)⁻¹) * ((fH : X) * x) := by
            group
        _ = (fH : X)⁻¹ * ((fH : X) * (e : X) * (fH : X)⁻¹) * (x * (fH : X)) := by rw [hfx]
        _ = (fH : X)⁻¹ * (((fH : X) * (e : X) * (fH : X)⁻¹) * x) * (fH : X) := by group
        _ = (fH : X)⁻¹ * (x * ((fH : X) * (e : X) * (fH : X)⁻¹)) * (fH : X) := by rw [hcomm']
        _ = x * (e : X) := by
          calc (fH : X)⁻¹ * (x * ((fH : X) * (e : X) * (fH : X)⁻¹)) * (fH : X)
              = ((fH : X)⁻¹ * x * (fH : X)) * (e : X) := by group
            _ = x * (e : X) := by rw [show (fH : X)⁻¹ * x * (fH : X) = x by
                calc (fH : X)⁻¹ * x * (fH : X) = (fH : X)⁻¹ * (x * (fH : X)) := by group
                  _ = (fH : X)⁻¹ * ((fH : X) * x) := by rw [hfx]
                  _ = x := by group]
  rcases hI.star_char hBsw hBne hBnc hBinv with ⟨p, hp⟩ | ⟨hn3, hfull⟩
  · refine ⟨p, fun e he => ?_⟩
    rw [← hBmem e he, hp]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · intro h
      exact ⟨L.swap_of_mem he, h⟩
  · exfalso
    subst hn3
    refine no_full_B hI hP hZ hS hna hd L hx fun e he => ?_
    rw [← hBmem e he, hfull]
    exact L.swap_of_mem he

end Local

end CFSG.RankThree.PartOne.FIS
