module

public import CFSG.OddTranspositions.TheoremTwo.PropFourSeven.Labelling

public section

namespace CFSG.OddTranspositions.PropFourSeven

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Connectivity CFSG.GroupTheory Equiv

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem mem_blockClass_of_mem_Dalpha {α θ ξ : Set G} (hθ : θ ∈ blockClass α)
    (hξ : ξ ∈ Dalpha D θ) : ξ ∈ blockClass α :=
  mem_blockClass_of_mem_blockClass (mem_blockClass_comm.mp hθ) hξ.1

omit [Finite G] in
theorem ne_of_mem_of_ne_block {α β γ : Set G} (hα : IsBlock D α) (hβ : β ∈ blockClass α)
    (hγ : γ ∈ blockClass α) (hne : β ≠ γ) {x y : G} (hx : x ∈ β) (hy : y ∈ γ) : x ≠ y := by
  rintro rfl
  exact hne (eq_of_mem_of_mem_blockClass hα hβ hγ ⟨x, hx, hy⟩)

theorem mem_Dalpha_of_commute (hN : IsNormalSet D) (hD : IsOddTransp D) {α θ ξ : Set G}
    (hα : IsBlock D α) (hθ : θ ∈ blockClass α) (hξ : ξ ∈ blockClass α) (hne : ξ ≠ θ)
    {x y : G} (hx : x ∈ ξ) (hy : y ∈ θ) (hxy : Commute x y) : ξ ∈ Dalpha D θ :=
  ⟨mem_blockClass_of_mem_blockClass hθ hξ, subset_of_mem_blockClass hN hα hξ, hne,
    blocks_commute_of_mem hN hD hα hθ hξ hne.symm hy hx hxy.symm⟩

omit [Finite G] in
theorem conj_image_mem_blockClass {α β : Set G} (hβ : β ∈ blockClass α) (g : G) :
    (fun x => g * x * g⁻¹) '' β ∈ blockClass α := by
  obtain ⟨k, rfl⟩ := mem_blockClass_iff.mp hβ
  refine mem_blockClass_iff.mpr ⟨g * k, ?_⟩
  simp only [Set.image_image]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, by group⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, by group⟩

omit [Finite G] in
theorem mem_of_mem_DalphaStar {θ : Set G} {x : G} (hx : x ∈ DalphaStar D θ) : x ∈ D := by
  obtain ⟨ξ, hξ, hxξ⟩ := hx
  exact hξ.2.1 hxξ

theorem conj_conj_eq_of_mul_self {M : Type*} [Group M] {r s : M} (h : r * r = 1) :
    r * (r * s * r⁻¹) * r⁻¹ = s := by
  rw [inv_eq_of_mul_eq_one_right h,
    show r * (r * s * r) * r = (r * r) * s * (r * r) by simp only [mul_assoc], h, one_mul, mul_one]

theorem transposition_mul_self {σ : Perm (Fin 5)} (hσ : σ ∈ transpositions) : σ * σ = 1 := by
  obtain ⟨a, b, -, rfl⟩ := hσ
  exact swap_mul_self a b

theorem conj_swap (ρ : Perm (Fin 5)) (x y : Fin 5) : ρ * swap x y * ρ⁻¹ = swap (ρ x) (ρ y) :=
  (swap_apply_apply ρ x y).symm

theorem exists_two_more_fin5 : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c → ∃ d e : Fin 5,
    a ≠ d ∧ a ≠ e ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e ∧
      ∀ x : Fin 5, x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := by decide

theorem exists_common_point_fin5 : ∀ a b p q : Fin 5, a ≠ b → p ≠ q → swap p q ≠ swap a b →
    swap p q * swap a b ≠ swap a b * swap p q →
    ∃ c : Fin 5, a ≠ c ∧ b ≠ c ∧ (swap p q = swap a c ∨ swap p q = swap b c) := by decide

theorem swap_disjoint_fin5 {a b x y : Fin 5} (hxy : x ≠ y) (hxa : x ≠ a) (hxb : x ≠ b)
    (hya : y ≠ a) (hyb : y ≠ b) :
    swap x y ∈ transpositions ∧ swap x y ≠ swap a b ∧ Commute (swap x y) (swap a b) := by
  refine ⟨⟨x, y, hxy, rfl⟩, fun h => ?_, ?_⟩
  · have := congrArg (fun σ : Perm (Fin 5) => σ x) h
    simp only [swap_apply_left, swap_apply_of_ne_of_ne hxa hxb] at this
    exact hxy this.symm
  · have h : swap x y * swap a b * (swap x y)⁻¹ = swap a b := by
      rw [conj_swap, swap_apply_of_ne_of_ne hxa.symm hya.symm,
        swap_apply_of_ne_of_ne hxb.symm hyb.symm]
    exact mul_inv_eq_iff_eq_mul.mp h

theorem swap_mem_of_closure {Λ : Set (Perm (Fin 5))} {a b c : Fin 5} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (h0 : ∀ σ ∈ transpositions, σ ≠ swap a b → Commute σ (swap a b) → σ ∈ Λ)
    (hcl : ∀ ρ : Perm (Fin 5), (ρ = swap a b ∨ ρ = swap a c ∨
      (ρ ∈ transpositions ∧ ρ ≠ swap a b ∧ Commute ρ (swap a b))) →
        ∀ σ ∈ Λ, ρ * σ * ρ⁻¹ ∈ Λ) :
    ∀ σ ∈ transpositions, σ ∈ Λ := by
  obtain ⟨d, e, had, hae, hbd, hbe, hcd, hce, hde, hall⟩ := exists_two_more_fin5 a b c hab hac hbc
  have mem : ∀ {x y : Fin 5}, x ≠ y → x ≠ a → x ≠ b → y ≠ a → y ≠ b → swap x y ∈ Λ :=
    fun hxy hxa hxb hya hyb =>
      let h := swap_disjoint_fin5 hxy hxa hxb hya hyb
      h0 _ h.1 h.2.1 h.2.2
  have hcd' : swap c d ∈ Λ := mem hcd hac.symm hbc.symm had.symm hbd.symm
  have hce' : swap c e ∈ Λ := mem hce hac.symm hbc.symm hae.symm hbe.symm
  have hde' : swap d e ∈ Λ := mem hde had.symm hbd.symm hae.symm hbe.symm
  have hρab := hcl (swap a b) (Or.inl rfl)
  have hρac := hcl (swap a c) (Or.inr (Or.inl rfl))
  have hρcd := hcl (swap c d) (Or.inr (Or.inr
    (swap_disjoint_fin5 hcd hac.symm hbc.symm had.symm hbd.symm)))
  have had' : swap a d ∈ Λ := by
    have := hρac _ hcd'
    rwa [conj_swap, swap_apply_right, swap_apply_of_ne_of_ne had.symm hcd.symm] at this
  have hae' : swap a e ∈ Λ := by
    have := hρac _ hce'
    rwa [conj_swap, swap_apply_right, swap_apply_of_ne_of_ne hae.symm hce.symm] at this
  have hbd' : swap b d ∈ Λ := by
    have := hρab _ had'
    rwa [conj_swap, swap_apply_left, swap_apply_of_ne_of_ne had.symm hbd.symm] at this
  have hbe' : swap b e ∈ Λ := by
    have := hρab _ hae'
    rwa [conj_swap, swap_apply_left, swap_apply_of_ne_of_ne hae.symm hbe.symm] at this
  have hbc' : swap b c ∈ Λ := by
    have := hρcd _ hbd'
    rwa [conj_swap, swap_apply_right, swap_apply_of_ne_of_ne hbc hbd] at this
  have hac' : swap a c ∈ Λ := by
    have := hρcd _ had'
    rwa [conj_swap, swap_apply_right, swap_apply_of_ne_of_ne hac had] at this
  have hab' : swap a b ∈ Λ := by
    have := hρac _ hbc'
    rwa [conj_swap, swap_apply_right, swap_apply_of_ne_of_ne hab.symm hbc, swap_comm] at this
  rintro σ ⟨x, y, hxy, rfl⟩
  rcases hall x with rfl | rfl | rfl | rfl | rfl <;>
    rcases hall y with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hxy
    | assumption
    | (rwa [swap_comm])

theorem transpositions_subset_of_closure {Λ : Set (Perm (Fin 5))} {τ τ' : Perm (Fin 5)}
    (hτ : τ ∈ transpositions) (hτ' : τ' ∈ transpositions) (hne : τ' ≠ τ)
    (hnc : ¬ Commute τ' τ) (h0 : ∀ σ ∈ transpositions, σ ≠ τ → Commute σ τ → σ ∈ Λ)
    (hcl : ∀ ρ : Perm (Fin 5), (ρ = τ ∨ ρ = τ' ∨ (ρ ∈ transpositions ∧ ρ ≠ τ ∧ Commute ρ τ)) →
      ∀ σ ∈ Λ, ρ * σ * ρ⁻¹ ∈ Λ) :
    ∀ σ ∈ transpositions, σ ∈ Λ := by
  obtain ⟨a, b, hab, rfl⟩ := hτ
  obtain ⟨p, q, hpq, rfl⟩ := hτ'
  obtain ⟨c, hac, hbc, hc | hc⟩ := exists_common_point_fin5 a b p q hab hpq hne hnc
  · rw [hc] at hcl
    exact swap_mem_of_closure hab hac hbc h0 hcl
  · rw [hc, swap_comm a b] at hcl
    rw [swap_comm a b] at h0
    exact swap_mem_of_closure hab.symm hbc hac h0 hcl

section CaseB

variable {α δ ε β : Set G} {ψ ψδ ψε : G → Perm (Fin 5)} {u v b : G}

theorem caseB_label_of_commute (hN : IsNormalSet D) (hD : IsOddTransp D) (hα : IsBlock D α)
    (hL : S5Labelling D α ψ) (hLδ : S5Labelling D δ ψδ) (hδ : δ ∈ Dalpha D α)
    (hu : u ∈ α) (hv : v ∈ δ) {x : G} (hx : x ∈ DalphaStar D δ) (hxu : Commute x u)
    (hne : x ≠ u) : x ∈ DalphaStar D α ∧ ψ x ≠ ψ v ∧ Commute (ψ x) (ψ v) := by
  obtain ⟨ξ, hξ, hxξ⟩ := hx
  have hξα : ξ ∈ blockClass α := mem_blockClass_of_mem_Dalpha hδ.1 hξ
  have hαδ : α ∈ Dalpha D δ := Dalpha_symm hδ hα.subset
  have hξne : ξ ≠ α := by
    rintro rfl
    exact hne (hLδ.eq_of_commute_of_mem_block hαδ hxξ hu hxu)
  have hξD : ξ ∈ Dalpha D α :=
    mem_Dalpha_of_commute hN hD hα (mem_blockClass_self α) hξα hξne hxξ hu hxu
  have hxv : x ≠ v := ne_of_mem_of_ne_block hα hξα hδ.1 (Dalpha.ne_self hξ) hxξ hv
  exact ⟨⟨ξ, hξD, hxξ⟩, hL.label_of_commute ⟨ξ, hξD, hxξ⟩ (subset_DalphaStar hδ hv) hxv
    (hξ.2.2.2 v hv x hxξ).symm⟩

omit [Finite G] in
theorem caseB_commute_block (hL : S5Labelling D α ψ) (hβ : β ∈ Dalpha D α)
    (hlab : ∀ y ∈ β, ψ y = ψ v) {x : G} (hx : x ∈ DalphaStar D α) (hne : ψ x ≠ ψ v)
    (hc : Commute (ψ x) (ψ v)) : ∀ y ∈ β, Commute x y := fun y hy =>
  hL.commute_of_label hx (subset_DalphaStar hβ hy) (by rw [hlab y hy]; exact hne)
    (by rw [hlab y hy]; exact hc)

theorem caseB_commute_block_of_commute (hN : IsNormalSet D) (hD : IsOddTransp D)
    (hα : IsBlock D α) (hL : S5Labelling D α ψ) (hLδ : S5Labelling D δ ψδ)
    (hδ : δ ∈ Dalpha D α) (hu : u ∈ α) (hv : v ∈ δ) (hβ : β ∈ Dalpha D α)
    (hlab : ∀ y ∈ β, ψ y = ψ v) {x : G} (hx : x ∈ DalphaStar D δ) (hxu : Commute x u)
    (hne : x ≠ u) : ∀ y ∈ β, Commute x y := by
  obtain ⟨hx', h1, h2⟩ := caseB_label_of_commute hN hD hα hL hLδ hδ hu hv hx hxu hne
  exact caseB_commute_block hL hβ hlab hx' h1 h2

theorem caseB_mem_and_commute (hN : IsNormalSet D) (hD : IsOddTransp D) (hα : IsBlock D α)
    (hL : S5Labelling D α ψ) (hLε : S5Labelling D ε ψε) (hδ : δ ∈ Dalpha D α)
    (hε : ε ∈ Dalpha D α) (hδε : ε ∈ Dalpha D δ) (hβ : β ∈ Dalpha D α)
    (hlab : ∀ y ∈ β, ψ y = ψ v) (hu : u ∈ α) (hv : v ∈ δ) (hb : b ∈ β)
    (hbδ : b ∉ DalphaStar D δ) {u' : G} (hu' : u' ∈ Phi D ε u) (hu'u : u' ≠ u) :
    u' ∈ DalphaStar D δ ∧ Commute u' b := by
  have huε : u ∈ DalphaStar D ε := subset_DalphaStar (Dalpha_symm hε hα.subset) hu
  have hδε' : δ ∈ Dalpha D ε := Dalpha_symm hδε hδ.2.1
  have hvε : v ∈ DalphaStar D ε := subset_DalphaStar hδε' hv
  obtain ⟨hu'ε, hlabu'⟩ := (hLε.mem_Phi_iff huε).mp hu'
  have hvu : v ≠ u :=
    ne_of_mem_of_ne_block hα hδ.1 (mem_blockClass_self α) (Dalpha.ne_self hδ) hv hu
  have hcvu : Commute v u := (hδ.2.2.2 u hu v hv).symm
  have hvu' : v ≠ u' := by
    rintro rfl
    exact (hLε.label_of_commute hvε huε hvu hcvu).1 hlabu'
  have hcvu' : Commute v u' := (hu'.2 v hvε hvu hvu').mp hcvu
  obtain ⟨ξ, hξ, hu'ξ⟩ := hu'ε
  have hξα : ξ ∈ blockClass α := mem_blockClass_of_mem_Dalpha hε.1 hξ
  have hξδ : ξ ≠ δ := by
    rintro rfl
    exact hvu' (hLε.eq_of_commute_of_mem_block hδε' hv hu'ξ hcvu')
  have hu'δ : u' ∈ DalphaStar D δ :=
    ⟨ξ, mem_Dalpha_of_commute hN hD hα hδ.1 hξα hξδ hu'ξ hv hcvu'.symm, hu'ξ⟩
  obtain ⟨e₀, he₀⟩ := blockClass_nonempty hα.nonempty hε.1
  have he₀v : e₀ ≠ v := ne_of_mem_of_ne_block hα hε.1 hδ.1 (Dalpha.ne_self hδε) he₀ hv
  obtain ⟨h1, h2⟩ := hL.label_of_commute (subset_DalphaStar hε he₀) (subset_DalphaStar hδ hv)
    he₀v (hδε.2.2.2 v hv e₀ he₀).symm
  have hbe₀ : Commute e₀ b := caseB_commute_block hL hβ hlab (subset_DalphaStar hε he₀) h1 h2 b hb
  have hβε : β ≠ ε := by
    rintro rfl
    exact hbδ (subset_DalphaStar hδε hb)
  have hbε : b ∈ DalphaStar D ε :=
    ⟨β, mem_Dalpha_of_commute hN hD hα hε.1 hβ.1 hβε hb he₀ hbe₀.symm, hb⟩
  have hbu : b ≠ u :=
    ne_of_mem_of_ne_block hα hβ.1 (mem_blockClass_self α) (Dalpha.ne_self hβ) hb hu
  have hbu' : b ≠ u' := fun h => hbδ (h ▸ hu'δ)
  exact ⟨hu'δ, ((hu'.2 b hbε hbu hbu').mp (hβ.2.2.2 u hu b hb).symm).symm⟩

omit [Finite G] in
theorem caseB_conj_mem (hN : IsNormalSet D) (hα : IsBlock D α) (hβ : β ∈ blockClass α)
    (hb : b ∈ β) {g x : G} (hg : g ∈ DalphaStar D δ) (hgb : Commute g b)
    (hx : x ∈ DalphaStar D δ) (hxβ : ∀ y ∈ β, Commute x y) :
    g * x * g⁻¹ ∈ DalphaStar D δ ∧ ∀ y ∈ β, Commute (g * x * g⁻¹) y := by
  refine ⟨conj_mem_DalphaStar hN hg hx, fun y hy => ?_⟩
  have himg : (fun z => g⁻¹ * z * g⁻¹⁻¹) '' β = β := by
    refine eq_of_mem_of_mem_blockClass hα (conj_image_mem_blockClass hβ g⁻¹) hβ
      ⟨b, ⟨b, hb, ?_⟩, hb⟩
    show g⁻¹ * b * g⁻¹⁻¹ = b
    rw [inv_inv, mul_assoc, ← hgb.eq, inv_mul_cancel_left]
  have hy' : g⁻¹ * y * g ∈ β := by
    rw [← himg]
    exact ⟨y, hy, by rw [inv_inv]⟩
  have := (commute_conj_iff g x (g⁻¹ * y * g)).mpr (hxβ _ hy')
  rwa [conj_inv_conj] at this

end CaseB

theorem Phi_subset_of_adjacent (hC : HypothesisC D) {ψ : G → Perm (Fin 5)}
    (hL : S5Labelling D hC.alpha ψ)
    (hspread : ∀ θ ∈ Dalpha D hC.alpha, ∃ θ' ∈ Dalpha D hC.alpha, θ' ≠ θ ∧
      ∀ x ∈ θ, ∀ y ∈ θ', ψ y = ψ x)
    {u : G} (hu : u ∈ hC.alpha) {δ ε : Set G} (hδ : δ ∈ Dalpha D hC.alpha)
    (hε : ε ∈ Dalpha D hC.alpha) (hδε : ε ∈ Dalpha D δ) :
    Phi D ε u ⊆ Phi D δ u := by
  have hN := hC.setup.normal
  have hD := hC.setup.oddT
  have hα := hC.isBlock_alpha
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hδ.1
  obtain ⟨h, hh⟩ := mem_blockClass_iff.mp hε.1
  obtain ⟨ψδ, hLδ⟩ : ∃ ψδ : G → Perm (Fin 5), S5Labelling D δ ψδ :=
    ⟨_, by rw [hg]; exact hL.conj hN g⟩
  obtain ⟨ψε, hLε⟩ : ∃ ψε : G → Perm (Fin 5), S5Labelling D ε ψε :=
    ⟨_, by rw [hh]; exact hL.conj hN h⟩
  intro u' hu'
  by_contra hu'δ
  have huδ : u ∈ DalphaStar D δ := subset_DalphaStar (Dalpha_symm hδ hα.subset) hu
  have huε : u ∈ DalphaStar D ε := subset_DalphaStar (Dalpha_symm hε hα.subset) hu
  obtain ⟨β, hβ, hβδ, hlab0⟩ := hspread δ hδ
  obtain ⟨v, hv⟩ := blockClass_nonempty hα.nonempty hδ.1
  obtain ⟨b, hb⟩ := blockClass_nonempty hα.nonempty hβ.1
  have hlab : ∀ y ∈ β, ψ y = ψ v := fun y hy => hlab0 v hv y hy
  have hbv : b ≠ v := ne_of_mem_of_ne_block hα hβ.1 hδ.1 hβδ hb hv
  have hbδ : b ∉ DalphaStar D δ := by
    rintro ⟨ξ, hξ, hbξ⟩
    exact hL.not_commute_of_label_eq (subset_DalphaStar hβ hb) (subset_DalphaStar hδ hv) hbv
      (hlab b hb) (hξ.2.2.2 v hv b hbξ).symm
  have hu'u : u' ≠ u := fun he => hu'δ (he.symm ▸ hLδ.mem_Phi_self huδ)
  obtain ⟨hu'D, hu'b⟩ :=
    caseB_mem_and_commute hN hD hα hL hLε hδ hε hδε hβ hlab hu hv hb hbδ hu' hu'u
  have hnc : ¬ Commute u' u := by
    obtain ⟨hu'ε, he⟩ := (hLε.mem_Phi_iff huε).mp hu'
    exact hLε.not_commute_of_label_eq hu'ε huε hu'u he
  have hne4 : ψδ u' ≠ ψδ u := fun he => hu'δ ((hLδ.mem_Phi_iff huδ).mpr ⟨hu'D, he⟩)
  have hnc4 : ¬ Commute (ψδ u') (ψδ u) := fun hc => hnc (hLδ.commute_of_label hu'D huδ hne4 hc)
  have hS2 : ∀ x ∈ DalphaStar D δ, ψδ x ≠ ψδ u → Commute (ψδ x) (ψδ u) →
      ∀ y ∈ β, Commute x y := fun x hx hne hc =>
    caseB_commute_block_of_commute hN hD hα hL hLδ hδ hu hv hβ hlab hx
      (hLδ.commute_of_label hx huδ hne hc) (fun he => hne (congrArg ψδ he))
  have hall := transpositions_subset_of_closure
    (Λ := {σ | ∀ x ∈ DalphaStar D δ, ψδ x = σ → ∀ y ∈ β, Commute x y})
    (hLδ.mem u huδ) (hLδ.mem u' hu'D) hne4 hnc4
    (fun σ _ hστ hστc x hx hxσ => hS2 x hx (hxσ ▸ hστ) (hxσ ▸ hστc)) <| by
      intro ρ hρ σ hσ x hx hxσ
      obtain ⟨g', hg', rfl, hg'b⟩ : ∃ g' ∈ DalphaStar D δ, ψδ g' = ρ ∧ Commute g' b := by
        rcases hρ with rfl | rfl | ⟨hρT, hρτ, hρc⟩
        · exact ⟨u, huδ, rfl, hβ.2.2.2 u hu b hb⟩
        · exact ⟨u', hu'D, rfl, hu'b⟩
        · obtain ⟨g', hg', rfl⟩ := hLδ.surj ρ hρT
          exact ⟨g', hg', rfl, hS2 g' hg' hρτ hρc b hb⟩
      have hgg : g' * g' = 1 := hD.mul_self_eq_one (mem_of_mem_DalphaStar hg')
      have hx' : g' * x * g'⁻¹ ∈ DalphaStar D δ := conj_mem_DalphaStar hN hg' hx
      have hlx' : ψδ (g' * x * g'⁻¹) = σ := by
        rw [hLδ.equiv g' hg' x hx, hxσ,
          conj_conj_eq_of_mul_self (transposition_mul_self (hLδ.mem g' hg'))]
      have := (caseB_conj_mem hN hα hβ.1 hb hg' hg'b hx' (hσ _ hx' hlx')).2
      rwa [conj_conj_eq_of_mul_self hgg] at this
  have hsub : Dalpha D δ ⊆ Dalpha D β := by
    intro θ hθ
    have hθα := mem_blockClass_of_mem_Dalpha hδ.1 hθ
    obtain ⟨t, ht⟩ := blockClass_nonempty hα.nonempty hθα
    have htD : t ∈ DalphaStar D δ := subset_DalphaStar hθ ht
    have htb : Commute t b := hall _ (hLδ.mem t htD) t htD rfl b hb
    have hθβ : θ ≠ β := by
      rintro rfl
      exact hbδ (subset_DalphaStar hθ hb)
    exact mem_Dalpha_of_commute hN hD hα hβ.1 hθα hθβ ht hb htb
  obtain ⟨k, hk⟩ := mem_blockClass_iff.mp hβ.1
  have hcard : (Dalpha D β).ncard = (Dalpha D δ).ncard := by
    rw [hk, hg, ncard_Dalpha_conj hN, ncard_Dalpha_conj hN]
  have heq : Dalpha D δ = Dalpha D β := Set.eq_of_subset_of_ncard_le hsub hcard.le
  have hW : β ∈ Walpha D δ := ⟨mem_blockClass_of_mem_blockClass hδ.1 hβ.1, heq.symm⟩
  have hδα : δ = (hC.conj g).alpha := by
    rw [HypothesisC.conj_alpha]
    exact hg
  rw [hδα, Walpha_alpha_eq_singleton] at hW
  exact hβδ ((Set.mem_singleton_iff.mp hW).trans hδα.symm)

end CFSG.OddTranspositions.PropFourSeven

