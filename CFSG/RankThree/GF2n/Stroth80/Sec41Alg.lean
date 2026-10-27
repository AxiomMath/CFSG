module

public import CFSG.RankThree.GF2n.Stroth80.Sec3Action

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG
open scoped commutatorElement

theorem hom_eq_one_of_perfect_of_comm {Γ A : Type*} [Group Γ] [Group A] [Group.IsPerfect Γ]
    (hA : ∀ a b : A, a * b = b * a) (f : Γ →* A) (g : Γ) : f g = 1 := by
  have hle : commutator Γ ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hA _ _
  exact hle Group.IsPerfect.mem_commutator

theorem linear_of_perfect {K : Type} {E Γ : Type*} [Field K] [Finite K] [AddCommGroup E]
    [Module K E] [Nontrivial E] [Group Γ] [Group.IsPerfect Γ] (ρ : Γ →* Equiv.Perm E)
    (hadd : ∀ γ e f, ρ γ (e + f) = ρ γ e + ρ γ f)
    (hsemi : ∀ γ, ∃ σ : K ≃+* K, ∀ (c : K) e, ρ γ (c • e) = σ c • ρ γ e) :
    ∀ γ (c : K) e, ρ γ (c • e) = c • ρ γ e := by
  choose σ hσ using hsemi
  obtain ⟨e₀, he₀⟩ := exists_ne (0 : E)
  have hρ0 : ∀ γ, ρ γ 0 = 0 := fun γ => by
    have := hadd γ 0 0
    simpa using this
  have hmul : ∀ γ δ, σ (γ * δ) = σ γ * σ δ := by
    intro γ δ
    refine RingEquiv.ext fun c => ?_
    have hw : ρ (γ * δ) e₀ ≠ 0 := fun h => he₀ ((ρ (γ * δ)).injective (h.trans (hρ0 _).symm))
    have h1 : ρ (γ * δ) (c • e₀) = σ (γ * δ) c • ρ (γ * δ) e₀ := hσ _ c e₀
    have h2 : ρ (γ * δ) (c • e₀) = σ γ (σ δ c) • ρ (γ * δ) e₀ := by
      have e1 : ρ (γ * δ) (c • e₀) = ρ γ (ρ δ (c • e₀)) := by rw [map_mul]; rfl
      have e2 : ρ (γ * δ) e₀ = ρ γ (ρ δ e₀) := by rw [map_mul]; rfl
      rw [e1, e2, hσ δ c e₀, hσ γ (σ δ c)]
    have h3 : (σ (γ * δ) c - σ γ (σ δ c)) • ρ (γ * δ) e₀ = 0 := by
      rw [sub_smul, ← h1, ← h2, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw
  haveI := isCyclic_ringEquiv K
  have hone : ∀ γ, σ γ = 1 := fun γ =>
    hom_eq_one_of_perfect_of_comm (fun a b => mul_comm' a b) (MonoidHom.mk' σ hmul) γ
  intro γ c e
  rw [hσ γ c e, hone γ]
  rfl

theorem fixes_vector_of_perfect {K E Γ : Type*} [Field K] [AddCommGroup E] [Module K E] [Group Γ]
    [Group.IsPerfect Γ] (ρ : Γ →* Equiv.Perm E)
    (hadd : ∀ γ e f, ρ γ (e + f) = ρ γ e + ρ γ f)
    (hlin : ∀ γ (c : K) e, ρ γ (c • e) = c • ρ γ e) (b : E) (hb : b ≠ 0)
    (hline : ∀ γ, ∃ c : K, ρ γ b = c • b) : ∀ γ, ρ γ b = b := by
  choose lam hlam using hline
  have hρ0 : ∀ γ, ρ γ 0 = 0 := fun γ => by
    have := hadd γ 0 0
    simpa using this
  have hne : ∀ γ, lam γ ≠ 0 := by
    intro γ h0
    have : ρ γ b = ρ γ 0 := by rw [hlam γ, h0, zero_smul, hρ0]
    exact hb ((ρ γ).injective this)
  have hmul : ∀ γ δ, lam (γ * δ) = lam γ * lam δ := by
    intro γ δ
    have h1 : ρ (γ * δ) b = (lam γ * lam δ) • b := by
      have e1 : ρ (γ * δ) b = ρ γ (ρ δ b) := by rw [map_mul]; rfl
      rw [e1, hlam δ, hlin γ, hlam γ, smul_smul, mul_comm]
    have h3 : (lam (γ * δ) - lam γ * lam δ) • b = 0 := by
      rw [sub_smul, ← hlam (γ * δ), h1, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hb
  let u : Γ →* Kˣ :=
    MonoidHom.mk' (fun γ => Units.mk0 (lam γ) (hne γ)) (fun γ δ => Units.ext (hmul γ δ))
  intro γ
  have h : lam γ = 1 :=
    congrArg Units.val (hom_eq_one_of_perfect_of_comm (fun a b => mul_comm a b) u γ)
  rw [hlam γ, h, one_smul]

theorem exists_odd_prime_orderOf {Γ : Type*} [Group Γ] [Finite Γ] [Nontrivial Γ]
    [Group.IsPerfect Γ] : ∃ r : Γ, Nat.Prime (orderOf r) ∧ orderOf r ≠ 2 := by
  by_contra hcon
  push Not at hcon
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : ∃ k, Nat.card Γ = 2 ^ k := by
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (p := 2) (Nat.card_pos (α := Γ)).ne'
      (fun {d} hd hdvd => ?_)⟩
    haveI : Fact d.Prime := ⟨hd⟩
    obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' d hdvd
    exact hr.symm.trans (hcon r (hr ▸ hd))
  have hP : IsPGroup 2 Γ := IsPGroup.iff_card.mpr hcard
  exact Group.IsPerfect.not_isNilpotent Γ hP.isNilpotent

theorem quasisimple_le_or_comm {Y : Type*} [Group Y] {X N : Subgroup Y} [X.Normal] [N.Normal]
    (hXq : CFSG.IsQuasisimple X) : X ≤ N ∨ ∀ x ∈ X, ∀ y ∈ N, x * y = y * x := by
  obtain ⟨hperf, hsimple, -⟩ := hXq
  haveI : Group.IsPerfect ↥X := hperf
  haveI hN' : (N.subgroupOf X).Normal := Subgroup.Normal.subgroupOf inferInstance X
  by_cases hcen : N.subgroupOf X ≤ Subgroup.center ↥X
  · right
    have hcentral : ∀ n ∈ X ⊓ N, ∀ x ∈ X, n * x = x * n := by
      intro n hn x hx
      have h := Subgroup.mem_center_iff.mp
        (hcen (show (⟨n, hn.1⟩ : ↥X) ∈ N.subgroupOf X from hn.2)) ⟨x, hx⟩
      exact (congrArg Subtype.val h).symm
    have hXN : ⁅X, N⁆ ≤ X ⊓ N := Subgroup.commutator_le_inf X N
    have h1 : ⁅⁅X, N⁆, X⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro w hw x hx
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hcentral w (hXN hw) x hx
    have h2 : ⁅⁅N, X⁆, X⁆ = ⊥ := by rw [Subgroup.commutator_comm N X]; exact h1
    have h3 : ⁅⁅X, X⁆, N⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [Subgroup.commutator_eq_self] at h3
    intro x hx y hy
    have h4 : ⁅x, y⁆ ∈ (⊥ : Subgroup Y) := by
      rw [← h3]; exact Subgroup.commutator_mem_commutator hx hy
    rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h4
  · left
    let π : ↥X →* ↥X ⧸ Subgroup.center ↥X := QuotientGroup.mk' (Subgroup.center ↥X)
    have hmapN : ((N.subgroupOf X).map π).Normal :=
      Subgroup.Normal.map hN' π (QuotientGroup.mk'_surjective _)
    haveI := hmapN
    rcases hsimple.eq_bot_or_eq_top_of_normal ((N.subgroupOf X).map π) with hbot | htop
    · exact absurd (by rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot; exact hbot) hcen
    · have hsup : N.subgroupOf X ⊔ Subgroup.center ↥X = ⊤ := by
        rw [eq_top_iff]
        intro a _
        have : π a ∈ (N.subgroupOf X).map π := by rw [htop]; trivial
        obtain ⟨n, hn, hna⟩ := this
        have hc : n⁻¹ * a ∈ Subgroup.center ↥X := by
          rw [← QuotientGroup.ker_mk' (Subgroup.center ↥X), MonoidHom.mem_ker]
          change π (n⁻¹ * a) = 1
          rw [map_mul, map_inv, hna, inv_mul_cancel]
        have : a = n * (n⁻¹ * a) := by group
        rw [this]
        exact Subgroup.mul_mem_sup hn hc
      have hperf' : ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ = ⊤ := by
        rw [← commutator_def]; exact Group.IsPerfect.commutator_eq_top
      have htop' : (⊤ : Subgroup ↥X) ≤ N.subgroupOf X := by
        calc (⊤ : Subgroup ↥X) = ⁅N.subgroupOf X ⊔ Subgroup.center ↥X, (⊤ : Subgroup ↥X)⁆ := by
              rw [hsup, hperf']
          _ = ⁅N.subgroupOf X, (⊤ : Subgroup ↥X)⁆ ⊔ ⁅Subgroup.center ↥X, (⊤ : Subgroup ↥X)⁆ :=
              Subgroup.commutator_sup_right _ _ _
          _ = ⁅N.subgroupOf X, (⊤ : Subgroup ↥X)⁆ := by
              rw [Subgroup.commutator_center_left, sup_bot_eq]
          _ ≤ N.subgroupOf X := Subgroup.commutator_le_left _ _
      intro x hx
      exact htop' (Subgroup.mem_top (⟨x, hx⟩ : ↥X))

theorem false_of_perfect_action {K : Type} {E Γ : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup E] [Module K E] [Finite E] [Group Γ] [Nontrivial Γ] [Group.IsPerfect Γ]
    (ρ : Γ →* Equiv.Perm E) (hρ : Function.Injective ρ)
    (hadd : ∀ γ e f, ρ γ (e + f) = ρ γ e + ρ γ f)
    (hsemi : ∀ γ, ∃ σ : K ≃+* K, ∀ (c : K) e, ρ γ (c • e) = σ c • ρ γ e)
    (Λ : Subgroup (E ≃ₗ[K] E)) (hΛ : IsPGroup 2 Λ) (b : E) (hb : b ≠ 0)
    (hfix : ∀ v : E, (∀ T ∈ Λ, T v = v) ↔ ∃ c : K, v = c • b)
    (hcomm : ∀ γ, ∀ T ∈ Λ, ∀ e, ρ γ (T e) = T (ρ γ e)) : False := by
  haveI : Nontrivial E := ⟨⟨b, 0, hb⟩⟩
  haveI : Finite Γ := Finite.of_injective ρ hρ
  have hlin := linear_of_perfect ρ hadd hsemi
  have hTb : ∀ T ∈ Λ, T b = b := fun T hT =>
    ((hfix b).mpr ⟨1, (one_smul K b).symm⟩) T hT
  have hline : ∀ γ, ∃ c : K, ρ γ b = c • b := by
    intro γ
    obtain ⟨c, hc⟩ := (hfix (ρ γ b)).mp fun T hT => by
      rw [← hcomm γ T hT b, hTb T hT]
    exact ⟨c, hc⟩
  have hfb := fixes_vector_of_perfect ρ hadd hlin b hb hline
  obtain ⟨r, hrp, hr2⟩ := exists_odd_prime_orderOf (Γ := Γ)
  have hodd : Odd (orderOf r) := hrp.odd_of_ne_two hr2
  let Tl : E →ₗ[K] E := { toFun := ρ r, map_add' := hadd r, map_smul' := hlin r }
  have hTpow : ∀ n : ℕ, ∀ e, (Tl ^ n) e = (ρ r ^ n) e := by
    intro n
    induction n with
    | zero => intro e; rfl
    | succ n ih => intro e; rw [pow_succ, Module.End.mul_apply, ih, pow_succ]; rfl
  have hTp : Tl ^ orderOf r = 1 := by
    refine LinearMap.ext fun e => ?_
    rw [hTpow, ← map_pow, pow_orderOf_eq_one, map_one]
    rfl
  have hker : LinearMap.ker (Tl - 1) ⊓ LinearMap.range (Tl - 1) = ⊥ :=
    ker_inf_range_eq_bot_of_pow_eq_one hodd hTp
  have hRbot : LinearMap.range (Tl - 1) ≠ ⊥ := by
    intro h
    rw [LinearMap.range_eq_bot, sub_eq_zero] at h
    have h1 : ρ r = 1 := Equiv.ext fun e => by
      have := LinearMap.congr_fun h e
      simpa [Tl] using this
    have h2 : r = 1 := hρ (by rw [h1, map_one])
    rw [h2, orderOf_one] at hrp
    exact Nat.not_prime_one hrp
  have hRinv : ∀ T ∈ Λ, ∀ v ∈ LinearMap.range (Tl - 1), T v ∈ LinearMap.range (Tl - 1) := by
    intro T hT v hv
    obtain ⟨e, he⟩ := hv
    refine ⟨T e, ?_⟩
    have he' : ρ r e - e = v := by simpa [Tl] using he
    have h1 : T (ρ r e) = ρ r (T e) := (hcomm r T hT e).symm
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    rw [← he', map_sub, h1]
    rfl
  obtain ⟨v, hvR, hv0, hvfix⟩ := exists_fixed_vector_of_isPGroup Λ hΛ _ hRinv hRbot
  obtain ⟨c, hc⟩ := (hfix v).mp hvfix
  have hvker : v ∈ LinearMap.ker (Tl - 1) := by
    rw [LinearMap.mem_ker, hc]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_smul]
    change c • (ρ r b - b) = 0
    rw [hfb r, sub_self, smul_zero]
  have : v ∈ LinearMap.ker (Tl - 1) ⊓ LinearMap.range (Tl - 1) := ⟨hvker, hvR⟩
  rw [hker] at this
  exact hv0 ((Submodule.mem_bot K).mp this)

end CFSG.RankThree.GF2n.Stroth80
