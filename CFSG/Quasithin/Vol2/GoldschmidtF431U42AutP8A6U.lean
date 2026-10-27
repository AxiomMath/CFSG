module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3 CFSG.QuasithinUnique.A6Facts Equiv

@[expose] def swapCands : List (List ℕ) :=
  Core.autL.filter fun a => Core.cmul a a == Core.cid && a != Core.cid &&
    (Core.cpslList a).length % 12 == 0

theorem swap_unique_check :
    (swapCands.all fun a => swapCands.all fun b =>
      a == b || ((Core.cpslList a).filter fun y => (Core.cpslList b).contains y).length < 12) =
      true := by
  decide +kernel

theorem card_psl29_centralizer2 {a b : P10} :
    Nat.card ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({a} : Set P10) ⊓
        Subgroup.centralizer ({b} : Set P10)) =
      ((Core.cpslList (code a)).filter fun y => (Core.cpslList (code b)).contains y).length := by
  refine card_eq_of_code_mem (E := (Core.cpslList (code a)).filter
    fun y => (Core.cpslList (code b)).contains y) ?_ ?_ ?_
  · unfold Core.cpslList
    exact (Core.psl_nodup.filter _).filter _
  · intro x
    simp only [Core.cpslList, List.mem_filter, Subgroup.mem_inf, mem_psl29_iff,
      Subgroup.mem_centralizer_singleton_iff, beq_iff_eq, List.contains_eq_any_beq,
      List.any_eq_true]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨h1, ?_⟩, code x, ⟨h1, ?_⟩, rfl⟩
      · rw [← code_mul, ← code_mul, h2]
      · rw [← code_mul, ← code_mul, h3]
    · rintro ⟨⟨h1, h2⟩, c, ⟨hc1, hc2⟩, hc3⟩
      have hcx : c = code x := (by simpa using hc3 : code x = c).symm
      subst hcx
      refine ⟨⟨h1, ?_⟩, ?_⟩
      · apply code_injective
        rw [code_mul, code_mul, h2]
      · apply code_injective
        rw [code_mul, code_mul, hc2]
  · intro c hc
    simp only [Core.cpslList, List.mem_filter, List.contains_eq_any_beq, List.any_eq_true,
      beq_iff_eq] at hc
    obtain ⟨⟨hc1, hc2⟩, c', ⟨hc'1, hc'2⟩, hcc'⟩ := hc
    have hcc : c' = c := (by simpa using hcc' : c = c').symm
    subst hcc
    obtain ⟨x, hx, rfl⟩ := exists_psl29_of_code hc1
    refine ⟨x, ⟨⟨hx, ?_⟩, ?_⟩, rfl⟩
    · show x ∈ Subgroup.centralizer ({a} : Set P10)
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply code_injective
      rw [code_mul, code_mul, hc2]
    · show x ∈ Subgroup.centralizer ({b} : Set P10)
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply code_injective
      rw [code_mul, code_mul, hc'2]

theorem model_swap_unique {a b : P10} (ha : a ∈ A6Models.autA6) (hb : b ∈ A6Models.autA6)
    (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (ha12 : 12 ∣ Nat.card ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({a} : Set P10)))
    (hb12 : 12 ∣ Nat.card ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({b} : Set P10)))
    (hab : 12 ≤ Nat.card ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({a} : Set P10) ⊓
      Subgroup.centralizer ({b} : Set P10))) : a = b := by
  by_contra hne
  have hall := swap_unique_check
  rw [List.all_eq_true] at hall
  have mem : ∀ {x : P10}, x ∈ A6Models.autA6 → x * x = 1 → x ≠ 1 →
      12 ∣ Nat.card ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({x} : Set P10)) →
        code x ∈ swapCands := by
    intro x hx hx2 hx1 hx12
    unfold swapCands
    rw [List.mem_filter]
    refine ⟨code_mem_autL hx, ?_⟩
    rw [card_psl29_centralizer] at hx12
    have e1 : (Core.cmul (code x) (code x) == Core.cid) = true := by
      rw [← code_mul, hx2, code_one]
      simp
    have e2 : (code x != Core.cid) = true := by
      simp only [bne_iff_ne, ne_eq]
      rw [← code_one]
      intro hc
      exact hx1 (code_injective hc)
    have e3 : ((Core.cpslList (code x)).length % 12 == 0) = true := by
      simp [Nat.mod_eq_zero_of_dvd hx12]
    simp [e1, e2, e3]
  have h1 := hall (code a) (mem ha ha2 ha1 ha12)
  rw [List.all_eq_true] at h1
  have h2 := h1 (code b) (mem hb hb2 hb1 hb12)
  rw [card_psl29_centralizer2] at hab
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
  rcases h2 with h2 | h2
  · exact hne (code_injective h2)
  · omega

section Abstract

variable {K : Type*} [Group K]

theorem swap_model_data (φ : K ≃* ↥A6Models.psl29) (α : MulAut K) (hα2 : ∀ k, α (α k) = k)
    (hα1 : ∃ k, α k ≠ k) (L : Subgroup K) (hL : Nat.card L = 12) (hαL : ∀ l ∈ L, α l = l) :
    ∃ a : P10, a ∈ A6Models.autA6 ∧
      (∀ k : K, ((φ (α k) : ↥A6Models.psl29) : P10) =
        a * ((φ k : ↥A6Models.psl29) : P10) * a⁻¹) ∧ a * a = 1 ∧ a ≠ 1 ∧
      12 ∣ Nat.card ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({a} : Set P10)) ∧
      ∀ l ∈ L, ((φ l : ↥A6Models.psl29) : P10) ∈ Subgroup.centralizer ({a} : Set P10) := by
  obtain ⟨a, haA, hβa⟩ := exists_aut_model φ α
  have ha2 : a * a = 1 := by
    have hc : a * a ∈ A6Models.autA6 := A6Models.autA6.mul_mem haA haA
    refine centralizer_psl29 hc fun x hx => ?_
    set k := φ.symm ⟨x, hx⟩ with hkdef
    have hk : ((φ k : ↥A6Models.psl29) : P10) = x := by simp [hkdef]
    have h1 := hβa k
    have h2 := hβa (α k)
    rw [hα2 k, h1, hk] at h2
    calc a * a * x = (a * (a * x * a⁻¹) * a⁻¹) * (a * a) := by group
      _ = x * (a * a) := by rw [← h2]
  have ha1 : a ≠ 1 := by
    intro h1
    obtain ⟨k, hk⟩ := hα1
    apply hk
    apply φ.injective
    apply Subtype.ext
    rw [hβa k, h1]
    simp
  have hLc : ∀ l ∈ L, ((φ l : ↥A6Models.psl29) : P10) ∈ Subgroup.centralizer ({a} : Set P10) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hβa l
    rw [hαL l hl] at h
    calc ((φ l : ↥A6Models.psl29) : P10) * a
        = (a * ((φ l : ↥A6Models.psl29) : P10) * a⁻¹) * a := by rw [← h]
      _ = a * ((φ l : ↥A6Models.psl29) : P10) := by group
  refine ⟨a, haA, hβa, ha2, ha1, ?_, hLc⟩
  let f : K →* P10 := A6Models.psl29.subtype.comp φ.toMonoidHom
  have hfinj : Function.Injective f := Subtype.val_injective.comp φ.injective
  have hle : L.map f ≤ A6Models.psl29 ⊓ Subgroup.centralizer ({a} : Set P10) := by
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨(φ l).2, hLc l hl⟩
  have hcard : Nat.card (L.map f) = 12 := by
    rw [Subgroup.card_map_of_injective hfinj]
    exact hL
  exact hcard ▸ Subgroup.card_dvd_of_le hle

theorem aut_swap_unique (e₀ : K ≃* alternatingGroup (Fin 6)) (L : Subgroup K)
    (hL : Nat.card L = 12) (α β : MulAut K) (hα2 : ∀ k, α (α k) = k) (hβ2 : ∀ k, β (β k) = k)
    (hα1 : ∃ k, α k ≠ k) (hβ1 : ∃ k, β k ≠ k) (hαL : ∀ l ∈ L, α l = l)
    (hβL : ∀ l ∈ L, β l = l) : α = β := by
  obtain ⟨ψ, -⟩ := exists_psl_equiv
  let φ : K ≃* ↥A6Models.psl29 := e₀.trans ψ.symm
  obtain ⟨a, haA, hαa, ha2, ha1, ha12, haL⟩ := swap_model_data φ α hα2 hα1 L hL hαL
  obtain ⟨b, hbA, hβb, hb2, hb1, hb12, hbL⟩ := swap_model_data φ β hβ2 hβ1 L hL hβL
  have hab : 12 ≤ Nat.card ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({a} : Set P10) ⊓
      Subgroup.centralizer ({b} : Set P10)) := by
    let f : K →* P10 := A6Models.psl29.subtype.comp φ.toMonoidHom
    have hfinj : Function.Injective f := Subtype.val_injective.comp φ.injective
    have hle : L.map f ≤ A6Models.psl29 ⊓ Subgroup.centralizer ({a} : Set P10) ⊓
        Subgroup.centralizer ({b} : Set P10) := by
      rintro _ ⟨l, hl, rfl⟩
      exact ⟨⟨(φ l).2, haL l hl⟩, hbL l hl⟩
    have hcard : Nat.card (L.map f) = 12 := by
      rw [Subgroup.card_map_of_injective hfinj]
      exact hL
    exact hcard ▸ Subgroup.card_le_of_le hle
  have hab' : a = b := model_swap_unique haA hbA ha2 hb2 ha1 hb1 ha12 hb12 hab
  subst hab'
  ext k
  apply φ.injective
  apply Subtype.ext
  rw [hαa k, hβb k]

end Abstract

end CFSG.Quasithin.H13.F431.U42Aut
