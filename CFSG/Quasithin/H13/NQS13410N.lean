module

public import CFSG.Quasithin.H13.NQS13410M

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem l3_stab_fix : ∀ v w : L3.Vec, v ≠ 0 →
    (∀ γ : L3.Γ, L3.act γ v = v → L3.act γ w = w) → w = 0 ∨ w = v := by decide +kernel

theorem l3_trans : ∀ v w : L3.Vec, v ≠ 0 → w ≠ 0 → ∃ γ : L3.Γ, L3.act γ v = w := by
  decide +kernel

theorem l3_fix_all : ∀ w : L3.Vec, (∀ γ : L3.Γ, L3.act γ w = w) → w = 0 := by decide +kernel

theorem l3_exists_ne_one : ∃ γ : L3.Γ, γ ≠ 1 := by decide +kernel

variable {G : Type} [Group G]

namespace L3Coords

variable {K X : Subgroup G} (C : L3Coords K X)
include C

theorem exists_ne_one : ∃ x : ↥X, x ≠ 1 := by
  by_contra h
  push Not at h
  obtain ⟨γ, hγ⟩ := l3_exists_ne_one
  obtain ⟨g, -, hg⟩ := C.image_K γ
  apply hγ
  rw [← hg]
  refine (C.ker g).2 (mem_centralizer_iff.2 fun x hx => ?_)
  have := h ⟨x, hx⟩
  have hx1 : x = 1 := congrArg Subtype.val this
  rw [hx1, one_mul, mul_one]

theorem eq_one_or_eq_self (f : ↥X → ↥X)
    (hf : ∀ g : ↥(normalizer (X : Set G)), (g : G) ∈ K → ∀ x, f (conjAct X g x) =
      conjAct X g (f x)) :
    (∀ x, f x = 1) ∨ (∀ x, f x = x) := by
  have hpt : ∀ x, f x = 1 ∨ f x = x := by
    intro x
    by_cases hx : x = 1
    · left
      subst hx
      have h0 : C.c (f 1) = 0 := l3_fix_all _ fun γ => by
        obtain ⟨g, hgK, hg⟩ := C.image_K γ
        have h1 := hf g hgK 1
        rw [map_one] at h1
        rw [← hg, ← C.equiv, ← h1]
      exact C.c_inj (h0.trans C.c_one.symm)
    · rcases l3_stab_fix (C.c x) (C.c (f x)) (C.c_ne_zero hx) (fun γ hγ => by
          obtain ⟨g, hgK, hg⟩ := C.image_K γ
          have hgx : conjAct X g x = x := C.c_inj (by rw [C.equiv, hg, hγ])
          have h1 := hf g hgK x
          rw [hgx] at h1
          rw [← hg, ← C.equiv, ← h1]) with h | h
      · exact Or.inl (C.c_inj (h.trans C.c_one.symm))
      · exact Or.inr (C.c_inj h)
  by_cases hall : ∃ x₁, x₁ ≠ 1 ∧ f x₁ = 1
  · left
    obtain ⟨x₁, hx₁, hfx₁⟩ := hall
    intro x
    by_cases hx : x = 1
    · rcases hpt x with h | h
      · exact h
      · rw [h, hx]
    · obtain ⟨γ, hγ⟩ := l3_trans (C.c x₁) (C.c x) (C.c_ne_zero hx₁) (C.c_ne_zero hx)
      obtain ⟨g, hgK, hg⟩ := C.image_K γ
      have hgx : conjAct X g x₁ = x := C.c_inj (by rw [C.equiv, hg, hγ])
      have h1 := hf g hgK x₁
      rw [hgx, hfx₁, map_one] at h1
      exact h1
  · right
    push Not at hall
    intro x
    by_cases hx : x = 1
    · rcases hpt x with h | h
      · rw [h, hx]
      · exact h
    · rcases hpt x with h | h
      · exact absurd h (hall x hx)
      · exact h

theorem eq_bot_or_eq {Y : Subgroup G} (hYX : Y ≤ X) (hKY : K ≤ normalizer (Y : Set G)) :
    Y = ⊥ ∨ Y = X := by
  by_cases hY : Y = ⊥
  · exact Or.inl hY
  right
  obtain ⟨⟨y, hyY⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hY
  replace hy1 : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  refine le_antisymm hYX fun x hx => ?_
  by_cases hx1 : (⟨x, hx⟩ : ↥X) = 1
  · rw [show x = 1 from congrArg Subtype.val hx1]
    exact one_mem _
  have hy1' : (⟨y, hYX hyY⟩ : ↥X) ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  obtain ⟨γ, hγ⟩ := l3_trans _ _ (C.c_ne_zero hy1') (C.c_ne_zero hx1)
  obtain ⟨g, hgK, hg⟩ := C.image_K γ
  have hgx : conjAct X g ⟨y, hYX hyY⟩ = ⟨x, hx⟩ := C.c_inj (by rw [C.equiv, hg, hγ])
  have h1 := congrArg Subtype.val hgx
  rw [A5.conjAct_val] at h1
  have h2 : x = (g : G) * y * (g : G)⁻¹ := h1.symm
  rw [h2]
  exact (mem_normalizer_iff.mp (hKY hgK) y).mp hyY

end L3Coords

section TwoCopies

variable {K U I : Subgroup G}

theorem le_normalizer_sup_of (hIU : I ≤ normalizer (U : Set G)) {N : Subgroup G}
    (hNU : N ≤ normalizer (U : Set G)) (hNI : N ≤ normalizer (I : Set G)) :
    N ≤ normalizer ((U ⊔ I : Subgroup G) : Set G) :=
  A5.le_normalizer_of_forall_conj_mem fun k hk x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hIU hx
    have e : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.mp (hNU hk) a).mp ha))
      (mem_sup_right ((mem_normalizer_iff.mp (hNI hk) b).mp hb))

theorem conj_eq_or_eq_mul (C : L3Coords K U) (hUI : U ⊓ I = ⊥)
    (hIU : I ≤ normalizer (U : Set G)) (φ : ↥U ≃* ↥I)
    (hφ : ∀ k ∈ K, ∀ (u : ↥U) (hu : k * (u : G) * k⁻¹ ∈ U),
      ((φ ⟨k * u * k⁻¹, hu⟩ : ↥I) : G) = k * (φ u : G) * k⁻¹)
    {d : G} (hdU : d ∈ centralizer (U : Set G)) (hdI : ∀ i ∈ I, d * i * d⁻¹ ∈ U ⊔ I)
    (hdK : ∀ k ∈ K, ∀ w ∈ U ⊔ I, (d * k * d⁻¹) * w * (d * k * d⁻¹)⁻¹ = k * w * k⁻¹) :
    (∀ u : ↥U, d * (φ u : G) * d⁻¹ = φ u) ∨ (∀ u : ↥U, d * (φ u : G) * d⁻¹ = u * φ u) := by
  classical
  have hdec : ∀ u : ↥U, ∃ a : ↥U, ∃ b : ↥U, d * (φ u : G) * d⁻¹ = a * φ b := by
    intro u
    obtain ⟨a, ha, b, hb, hab⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hIU (hdI _ (φ u).2)
    exact ⟨⟨a, ha⟩, φ.symm ⟨b, hb⟩, by rw [hab, MulEquiv.apply_symm_apply]⟩
  choose α β hαβ using hdec
  have huniq : ∀ {a a' b b' : ↥U}, (a : G) * φ b = a' * φ b' → a = a' ∧ b = b' := by
    intro a a' b b' h
    obtain ⟨h1, h2⟩ := eq_of_mul_eq_mul hUI a'.2 a.2 (φ b').2 (φ b).2 h
    exact ⟨Subtype.ext h1, φ.injective (Subtype.ext h2)⟩
  have hequiv : ∀ g : ↥(normalizer (U : Set G)), (g : G) ∈ K → ∀ u : ↥U,
      α (conjAct U g u) = conjAct U g (α u) ∧ β (conjAct U g u) = conjAct U g (β u) := by
    intro g hgK u
    have hgu : (g : G) * u * (g : G)⁻¹ ∈ U := (mem_normalizer_iff.mp g.2 u).mp u.2
    have hgβ : (g : G) * (β u : G) * (g : G)⁻¹ ∈ U :=
      (mem_normalizer_iff.mp g.2 (β u)).mp (β u).2
    have hcu : conjAct U g u = ⟨g * u * (g : G)⁻¹, hgu⟩ := Subtype.ext (A5.conjAct_val U g u)
    have hw : (α u : G) * (φ (β u) : G) ∈ U ⊔ I :=
      mul_mem (mem_sup_left (α u).2) (mem_sup_right (φ (β u)).2)
    have key : ((conjAct U g (α u) : ↥U) : G) * (φ (conjAct U g (β u)) : G) =
        α (conjAct U g u) * φ (β (conjAct U g u)) := by
      rw [← hαβ, hcu, hφ g hgK u hgu]
      have e1 : d * ((g : G) * (φ u : G) * (g : G)⁻¹) * d⁻¹ =
          (d * g * d⁻¹) * (d * (φ u : G) * d⁻¹) * (d * g * d⁻¹)⁻¹ := by group
      rw [e1, hαβ u, hdK g hgK _ hw]
      have hcβ : conjAct U g (β u) = ⟨g * (β u : G) * (g : G)⁻¹, hgβ⟩ :=
        Subtype.ext (A5.conjAct_val U g (β u))
      rw [hcβ, hφ g hgK (β u) hgβ, A5.conjAct_val]
      group
    obtain ⟨h1, h2⟩ := huniq key
    exact ⟨h1.symm, h2.symm⟩
  rcases C.eq_one_or_eq_self β fun g hg u => (hequiv g hg u).2 with hβ | hβ
  ·
    exfalso
    obtain ⟨u, hu1⟩ := C.exists_ne_one
    have h1 := hαβ u
    rw [hβ u, map_one, Subgroup.coe_one, mul_one] at h1
    have h2 : (φ u : G) = α u := by
      have e : (φ u : G) = d⁻¹ * (d * (φ u : G) * d⁻¹) * d := by group
      rw [e, h1]
      have hc := mem_centralizer_iff.mp hdU (α u) (α u).2
      calc d⁻¹ * (α u : G) * d = d⁻¹ * (d * (α u : G)) := by rw [mul_assoc, hc]
        _ = α u := by group
    have h3 : (φ u : G) ∈ U ⊓ I := mem_inf.2 ⟨h2 ▸ (α u).2, (φ u).2⟩
    rw [hUI, mem_bot] at h3
    apply hu1
    apply φ.injective
    rw [map_one]
    exact Subtype.ext h3
  · rcases C.eq_one_or_eq_self α fun g hg u => (hequiv g hg u).1 with hα | hα
    · left
      intro u
      rw [hαβ u, hα u, hβ u, Subgroup.coe_one, one_mul]
    · right
      intro u
      rw [hαβ u, hα u, hβ u]

theorem exists_conj_phi (C : L3Coords K U) (hUI : U ⊓ I = ⊥)
    (hIU : I ≤ normalizer (U : Set G)) (hKU : K ≤ normalizer (U : Set G))
    (hKI : K ≤ normalizer (I : Set G)) (φ : ↥U ≃* ↥I)
    (hφ : ∀ k ∈ K, ∀ (u : ↥U) (hu : k * (u : G) * k⁻¹ ∈ U),
      ((φ ⟨k * u * k⁻¹, hu⟩ : ↥I) : G) = k * (φ u : G) * k⁻¹)
    (htop : autOn K U = ⊤) {a : G} (haU : a ∈ normalizer (U : Set G))
    (haW : a ∈ normalizer ((U ⊔ I : Subgroup G) : Set G)) (haK : a ∈ normalizer (K : Set G)) :
    ∃ k ∈ K, (∀ x ∈ U, a * x * a⁻¹ = k * x * k⁻¹) ∧
      ((∀ u : ↥U, a * (φ u : G) * a⁻¹ = k * (φ u : G) * k⁻¹) ∨
        (∀ u : ↥U, a * (φ u : G) * a⁻¹ = (k * (u : G) * k⁻¹) * (k * (φ u : G) * k⁻¹))) := by
  obtain ⟨k, hk, hka⟩ := exists_mem_eq_conj htop haU
  refine ⟨k, hk, hka, ?_⟩
  set d := k⁻¹ * a with hd
  have hKW : K ≤ normalizer ((U ⊔ I : Subgroup G) : Set G) := le_normalizer_sup_of hIU hKU hKI
  have hdU : d ∈ centralizer (U : Set G) := mem_centralizer_iff.2 fun x hx => by
    have h1 := hka x hx
    calc x * d = k⁻¹ * (k * x * k⁻¹) * k * k⁻¹ * a := by rw [hd]; group
      _ = k⁻¹ * (a * x * a⁻¹) * k * k⁻¹ * a := by rw [h1]
      _ = d * x := by rw [hd]; group
  have hdW : d ∈ normalizer ((U ⊔ I : Subgroup G) : Set G) :=
    mul_mem (inv_mem (hKW hk)) haW
  have hdI : ∀ i ∈ I, d * i * d⁻¹ ∈ U ⊔ I := fun i hi =>
    (mem_normalizer_iff.mp hdW i).mp (mem_sup_right hi)
  have hdN : d ∈ normalizer (K : Set G) := mul_mem (inv_mem (le_normalizer hk)) haK
  have hCW : ∀ c ∈ K, c ∈ centralizer (U : Set G) →
      c ∈ centralizer ((U ⊔ I : Subgroup G) : Set G) := by
    intro c hc hcU
    have hCI : I ≤ centralizer ({c} : Set G) := fun i hi => by
      rw [mem_centralizer_singleton_iff]
      set u : ↥U := φ.symm ⟨i, hi⟩ with hu
      have hφu : φ u = ⟨i, hi⟩ := by rw [hu, MulEquiv.apply_symm_apply]
      have hcu : c * (u : G) * c⁻¹ = u := by
        rw [← mem_centralizer_iff.mp hcU u u.2, mul_inv_cancel_right]
      have hcu' : c * (u : G) * c⁻¹ ∈ U := by rw [hcu]; exact u.2
      have h1 := hφ c hc u hcu'
      have h2 : (⟨c * (u : G) * c⁻¹, hcu'⟩ : ↥U) = u := Subtype.ext hcu
      rw [h2, hφu] at h1
      have h3 : c * i * c⁻¹ = i := h1.symm
      calc i * c = c * i * c⁻¹ * c := by rw [h3]
        _ = c * i := by group
    have hCU : U ≤ centralizer ({c} : Set G) := fun x hx => by
      rw [mem_centralizer_singleton_iff]
      exact (mem_centralizer_iff.mp hcU x hx)
    have hle : U ⊔ I ≤ centralizer ({c} : Set G) := sup_le hCU hCI
    exact mem_centralizer_iff.2 fun w hw => (mem_centralizer_singleton_iff.mp (hle hw))
  have hdK : ∀ k' ∈ K, ∀ w ∈ U ⊔ I, (d * k' * d⁻¹) * w * (d * k' * d⁻¹)⁻¹ = k' * w * k'⁻¹ := by
    intro k' hk' w hw
    set c := (d * k' * d⁻¹) * k'⁻¹ with hc
    have hcK : c ∈ K :=
      mul_mem ((mem_normalizer_iff.mp hdN k').mp hk') (inv_mem hk')
    have hcU : c ∈ centralizer (U : Set G) := mem_centralizer_iff.2 fun x hx => by
      have hx' : k'⁻¹ * x * k'⁻¹⁻¹ ∈ U := (mem_normalizer_iff.mp (hKU (inv_mem hk')) x).mp hx
      have h1 := mem_centralizer_iff.mp hdU _ hx'
      have h2 := mem_centralizer_iff.mp hdU x hx
      have e1 : d * (k'⁻¹ * x * k'⁻¹⁻¹) * d⁻¹ = k'⁻¹ * x * k'⁻¹⁻¹ := by
        rw [← h1, mul_inv_cancel_right]
      have e2 : d⁻¹ * x * d = x := by
        calc d⁻¹ * x * d = d⁻¹ * (x * d) := by group
          _ = d⁻¹ * (d * x) := by rw [h2]
          _ = x := by group
      calc x * c = x * (d * k' * d⁻¹) * k'⁻¹ := by rw [hc]; group
        _ = (d * k' * d⁻¹) * ((d * k' * d⁻¹)⁻¹ * x * (d * k' * d⁻¹)) * k'⁻¹ := by group
        _ = (d * k' * d⁻¹) * (d * (k'⁻¹ * (d⁻¹ * x * d) * k'⁻¹⁻¹) * d⁻¹) * k'⁻¹ := by group
        _ = (d * k' * d⁻¹) * (k'⁻¹ * x * k'⁻¹⁻¹) * k'⁻¹ := by rw [e2, e1]
        _ = c * x := by rw [hc]; group
    have hcW := hCW c hcK hcU
    have hkw : k' * w * k'⁻¹ ∈ U ⊔ I := (mem_normalizer_iff.mp (hKW hk') w).mp hw
    have h1 := mem_centralizer_iff.mp hcW _ hkw
    have e : d * k' * d⁻¹ = c * k' := by rw [hc]; group
    rw [e]
    calc c * k' * w * (c * k')⁻¹ = c * (k' * w * k'⁻¹) * c⁻¹ := by group
      _ = (k' * w * k'⁻¹) * c * c⁻¹ := by rw [← h1]
      _ = k' * w * k'⁻¹ := by group
  rcases conj_eq_or_eq_mul C hUI hIU φ hφ hdU hdI hdK with h | h
  · left
    intro u
    have h1 := h u
    calc a * (φ u : G) * a⁻¹ = k * (d * (φ u : G) * d⁻¹) * k⁻¹ := by rw [hd]; group
      _ = k * (φ u : G) * k⁻¹ := by rw [h1]
  · right
    intro u
    have h1 := h u
    calc a * (φ u : G) * a⁻¹ = k * (d * (φ u : G) * d⁻¹) * k⁻¹ := by rw [hd]; group
      _ = k * ((u : G) * φ u) * k⁻¹ := by rw [h1]
      _ = (k * (u : G) * k⁻¹) * (k * (φ u : G) * k⁻¹) := by group

end TwoCopies

end CFSG.Quasithin.H13.NQS134
