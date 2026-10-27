module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.Quasithin.S152W

open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def AtlasClauses (Γ : Type) [Group Γ] : Prop :=
  (∀ α : MulAut Γ, α ^ 3 = 1 → ∃ g : Γ, α = MulAut.conj g) ∧
    ∀ t : Γ, orderOf t = 2 →
      2 ^ (Nat.card Γ).factorization 2 ∣ Nat.card (Subgroup.centralizer ({t} : Set Γ)) →
        ¬ 9 ∣ Nat.card (Subgroup.centralizer ({t} : Set Γ))

theorem out_of_equiv {Γ M : Type*} [Group Γ] [Group M] (e : Γ ≃* M)
    (h : ∀ β : MulAut M, β ^ 3 = 1 → ∃ g : M, β = MulAut.conj g) :
    ∀ α : MulAut Γ, α ^ 3 = 1 → ∃ g : Γ, α = MulAut.conj g := by
  intro α hα
  obtain ⟨g, hg⟩ := h (MulAut.congr e α) (by rw [← map_pow, hα, map_one])
  refine ⟨e.symm g, (MulAut.congr e).injective ?_⟩
  rw [hg, congr_conj, e.apply_symm_apply]

theorem card_centralizer_equiv {Γ M : Type*} [Group Γ] [Group M] (e : Γ ≃* M) (t : Γ) :
    Nat.card (Subgroup.centralizer ({t} : Set Γ)) =
      Nat.card (Subgroup.centralizer ({e t} : Set M)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => ?_)
  simp only [Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
  constructor
  · intro h
    rw [← map_mul, ← map_mul, h]
  · intro h
    apply e.injective
    rw [map_mul, map_mul, h]

theorem AtlasClauses.of_equiv {Γ M : Type} [Group Γ] [Group M] (e : Γ ≃* M) (h : AtlasClauses M) :
    AtlasClauses Γ := by
  refine ⟨out_of_equiv e h.1, fun t ht h2 => ?_⟩
  have hcard : Nat.card Γ = Nat.card M := Nat.card_congr e.toEquiv
  have hC := card_centralizer_equiv e t
  rw [hC]
  refine h.2 (e t) (by rw [MulEquiv.orderOf_eq]; exact ht) ?_
  rw [← hcard, ← hC]
  exact h2

theorem finite_mulAut (G : Type*) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun α : MulAut G => (α : G → G)) DFunLike.coe_injective

theorem out_of_card_outer_le_two {M : Type*} [Group M] [Finite M] (h : Nat.card (Outer M) ≤ 2) :
    ∀ β : MulAut M, β ^ 3 = 1 → ∃ g : M, β = MulAut.conj g := by
  intro β hβ
  have := finite_mulAut M
  let x : Outer M := QuotientGroup.mk β
  have h3 : x ^ 3 = 1 := by
    show (QuotientGroup.mk β : Outer M) ^ 3 = 1
    rw [← QuotientGroup.mk_pow, hβ, QuotientGroup.mk_one]
  have hpos : 0 < Nat.card (Outer M) := Nat.card_pos
  have hN : x ^ Nat.card (Outer M) = 1 := pow_card_eq_one'
  have hx : x = 1 := by
    have h12 : Nat.card (Outer M) = 1 ∨ Nat.card (Outer M) = 2 := by omega
    rcases h12 with h1 | h2
    · rw [h1, pow_one] at hN
      exact hN
    · rw [h2] at hN
      calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
        _ = 1 := by rw [h3, hN]; group
  have hmem : β ∈ inner M := (QuotientGroup.eq_one_iff β).1 hx
  obtain ⟨g, hg⟩ := hmem
  exact ⟨g, hg.symm⟩

theorem card_inner_eq (M : Type*) [Group M] (hc : Subgroup.center M = ⊥) :
    Nat.card (inner M) = Nat.card M := by
  have hinj : Function.Injective (MulAut.conj : M →* MulAut M) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hcentral : x ∈ Subgroup.center M := by
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      have hconj := congrArg (fun f : MulAut M => f y) hx
      change x * y * x⁻¹ = y at hconj
      have heq := congrArg (fun z : M => z * x) hconj
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using heq.symm
    rw [hc] at hcentral
    exact hcentral
  change Nat.card (MulAut.conj : M →* MulAut M).range = _
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

theorem card_outer_le_two_of_card_aut {M : Type*} [Group M] [Finite M]
    (hc : Subgroup.center M = ⊥) (h : Nat.card (MulAut M) ≤ 2 * Nat.card M) :
    Nat.card (Outer M) ≤ 2 := by
  have := finite_mulAut M
  have hinn := card_inner_eq M hc
  have hq := (inner M).card_eq_card_quotient_mul_card_subgroup
  rw [hinn] at hq
  have hpos : 0 < Nat.card M := Nat.card_pos
  have hle : Nat.card (Outer M) * Nat.card M ≤ 2 * Nat.card M := by
    change Nat.card (MulAut M ⧸ inner M) * Nat.card M ≤ _
    rw [← hq]
    exact h
  exact Nat.le_of_mul_le_mul_right hle hpos

theorem card_centralizer_subtype {M : Type*} [Group M] (H : Subgroup M) (t : H) :
    Nat.card (Subgroup.centralizer ({t} : Set H)) =
      Nat.card (H ⊓ Subgroup.centralizer ({(t : M)} : Set M) : Subgroup M) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨(x.1 : M), Subgroup.mem_inf.2 ⟨x.1.2,
        Subgroup.mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 x.2))⟩⟩
      invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩,
        Subgroup.mem_centralizer_singleton_iff.2
          (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2))⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem card_inf_centralizer_conj {M : Type*} [Group M] {H : Subgroup M} {g : M} (hg : g ∈ H)
    (u : M) :
    Nat.card (H ⊓ Subgroup.centralizer ({g * u * g⁻¹} : Set M) : Subgroup M) =
      Nat.card (H ⊓ Subgroup.centralizer ({u} : Set M) : Subgroup M) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj g⁻¹).toEquiv fun x => ?_)
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe,
    MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨hx, hxu⟩
    refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩
    calc g⁻¹ * x * g * u = g⁻¹ * (x * (g * u * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * u * g⁻¹) * x) * g := by rw [hxu]
      _ = u * (g⁻¹ * x * g) := by group
  · rintro ⟨hx, hxu⟩
    have hx' : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    refine ⟨?_, ?_⟩
    · rw [hx']
      exact H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
    · calc x * (g * u * g⁻¹) = g * ((g⁻¹ * x * g) * u) * g⁻¹ := by group
        _ = g * (u * (g⁻¹ * x * g)) * g⁻¹ := by rw [hxu]
        _ = g * u * g⁻¹ * x := by group

theorem card_fixed_conj {G : Type*} [Group G] (g : G) :
    Nat.card {x : G // MulAut.conj g x = x} = Nat.card (Subgroup.centralizer ({g} : Set G)) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [MulAut.conj_apply]
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

theorem conj_involution {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥) {t : G}
    (ht : orderOf t = 2) : MulAut.conj t * MulAut.conj t = 1 ∧ MulAut.conj t ≠ 1 := by
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  refine ⟨by rw [← map_mul, ht2, map_one], fun h => ?_⟩
  have hc : t ∈ Subgroup.center G := by
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    have := congrArg (fun f : MulAut G => f y) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * t = (t * y * t⁻¹) * t := by rw [this]
      _ = t * y := by group
  rw [hZ, Subgroup.mem_bot] at hc
  have h1 : orderOf t = 1 := by rw [hc, orderOf_one]
  omega

theorem two_pow_dvd_of_sylow {Γ : Type*} [Group Γ] [Finite Γ] (t : Γ)
    (h : ∃ S : Sylow 2 Γ, ∀ x ∈ S, x * t = t * x) :
    2 ^ (Nat.card Γ).factorization 2 ∣ Nat.card (Subgroup.centralizer ({t} : Set Γ)) := by
  obtain ⟨S, hS⟩ := h
  have hle : (S : Subgroup Γ) ≤ Subgroup.centralizer ({t} : Set Γ) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hS x hx)
  have := Subgroup.card_dvd_of_le hle
  rwa [Sylow.card_eq_multiplicity] at this

theorem cent_clause_of_values {Γ : Type*} [Group Γ] (L : List ℕ)
    (hL : ∀ t : Γ, orderOf t = 2 → Nat.card (Subgroup.centralizer ({t} : Set Γ)) ∈ L)
    (hbad : ∀ c ∈ L, 9 ∣ c → ¬ 2 ^ (Nat.card Γ).factorization 2 ∣ c) :
    ∀ t : Γ, orderOf t = 2 →
      2 ^ (Nat.card Γ).factorization 2 ∣ Nat.card (Subgroup.centralizer ({t} : Set Γ)) →
        ¬ 9 ∣ Nat.card (Subgroup.centralizer ({t} : Set Γ)) :=
  fun t ht h2 h9 => hbad _ (hL t ht) h9 h2

theorem hbad_of_not_dvd {Γ : Type*} [Group Γ] (L : List ℕ) (h : ∀ c ∈ L, ¬ 9 ∣ c) :
    ∀ c ∈ L, 9 ∣ c → ¬ 2 ^ (Nat.card Γ).factorization 2 ∣ c :=
  fun c hc h9 _ => h c hc h9

theorem atlasClauses_of_data {M : Type} [Group M] [Finite M] (hout : Nat.card (Outer M) ≤ 2)
    (L : List ℕ)
    (hL : ∀ t : M, orderOf t = 2 → Nat.card (Subgroup.centralizer ({t} : Set M)) ∈ L)
    (hbad : ∀ c ∈ L, 9 ∣ c → ¬ 2 ^ (Nat.card M).factorization 2 ∣ c) : AtlasClauses M :=
  ⟨out_of_card_outer_le_two hout, cent_clause_of_values L hL hbad⟩

theorem factorization_two_of_eq {n k b : ℕ} (h : n = 2 ^ k * b) (hb : ¬ 2 ∣ b) :
    n.factorization 2 = k := by
  subst h
  have hb0 : b ≠ 0 := fun h => hb (h ▸ dvd_zero 2)
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hb0]
  simp [Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hb]

theorem center_eq_bot_of_simple_not_prime {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h1 | h1
  · exact h1
  · exfalso
    let _ : CommGroup G := Group.commGroupOfCenterEqTop h1
    exact h (IsSimpleGroup.prime_card (α := G))

theorem atlas_statement_of_clauses {Γ : Type} [Group Γ] [Finite Γ] (h : AtlasClauses Γ) :
    (∀ α : MulAut Γ, α ^ 3 = 1 → ∃ g : Γ, α = MulAut.conj g) ∧
      ∀ t : Γ, orderOf t = 2 → (∃ S : Sylow 2 Γ, ∀ x ∈ S, x * t = t * x) →
        ¬ 9 ∣ Nat.card (Subgroup.centralizer ({t} : Set Γ)) :=
  ⟨h.1, fun t ht hS => h.2 t ht (two_pow_dvd_of_sylow t hS)⟩

end CFSG.Quasithin.S152W
