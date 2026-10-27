module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPU4Tab
public import CFSG.Quasithin.Background.A4Four

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.Quasithin.F53Mod Equiv

@[expose] def pu4P (i : Fin 5) : Bool := i == 1 || i == 3 || i == 4

@[expose] def pu4Stab : Subgroup (Perm (Fin 5)) where
  carrier := {σ | ∀ i, pu4P i = pu4P (σ i)}
  one_mem' := fun _ => rfl
  mul_mem' := fun {a b} ha hb i => by
    show pu4P i = pu4P (a (b i))
    rw [hb i, ha (b i)]
  inv_mem' := fun {a} ha i => by
    show pu4P i = pu4P (a⁻¹ i)
    rw [ha (a⁻¹ i)]; simp

@[expose] def pu4Restr : pu4Stab →* Perm {i : Fin 5 // pu4P i = true} where
  toFun σ := σ.1.subtypePerm (fun i => by rw [σ.2 i])
  map_one' := by ext; rfl
  map_mul' a b := by ext; rfl

@[expose] def pu4E3 : {i : Fin 5 // pu4P i = true} ≃ Fin 3 where
  toFun i := match i.1 with
    | 1 => 0
    | 3 => 1
    | _ => 2
  invFun j := match j with
    | 0 => ⟨1, rfl⟩
    | 1 => ⟨3, rfl⟩
    | 2 => ⟨4, rfl⟩
  left_inv := by decide +kernel
  right_inv := by decide +kernel

@[expose] def pu4R : pu4Stab →* Perm (Fin 3) := pu4E3.permCongrHom.toMonoidHom.comp pu4Restr

@[expose] def pu4Rf (σ : Perm (Fin 5)) : Perm (Fin 3) :=
  if h : ∀ i, pu4P i = pu4P (σ i) then pu4R ⟨σ, h⟩ else 1

theorem pu4R_eq (σ : pu4Stab) : pu4R σ = pu4Rf σ.1 := by
  unfold pu4Rf
  split_ifs with hh
  · rfl
  · exact absurd σ.2 hh

theorem centralizer_stab : ∀ σ : Perm (Fin 5), σ * swap 0 2 = swap 0 2 * σ →
    ∀ i, pu4P i = pu4P (σ i) := by decide +kernel

theorem pu4Rf_eq_one_iff : ∀ σ : Perm (Fin 5), σ * swap 0 2 = swap 0 2 * σ →
    (pu4Rf σ = 1 ↔ σ = 1 ∨ σ = swap 0 2) := by decide +kernel

private theorem perm3_two_pow {σ : Perm (Fin 3)} {k : ℕ} (h : σ ^ 2 ^ k = 1) : σ = 1 ∨ σ * σ = 1 := by
  by_cases h3 : σ ^ 3 = 1
  · left
    have h3' : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have h2' : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
    rcases (Nat.prime_three.eq_one_or_self_of_dvd _ h3') with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      rw [h] at h2'
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2'
      omega
  · right
    exact (by decide +kernel : ∀ σ : Perm (Fin 3), ¬ σ ^ 3 = 1 → σ * σ = 1) σ h3

private theorem perm3_product : ∀ σ : Perm (Fin 3), σ * σ = 1 → σ ≠ 1 →
    ((swap 0 1 * swap 1 2) * σ * (swap 0 1 * swap 1 2)⁻¹ * σ) ^ 3 = 1 ∧
      (swap 0 1 * swap 1 2) * σ * (swap 0 1 * swap 1 2)⁻¹ * σ ≠ 1 := by decide +kernel

theorem perm3_normal_two_group (K : Subgroup (Perm (Fin 3))) [K.Normal] (hK : IsPGroup 2 K) :
    K = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := hK ⟨σ, hσ⟩
  have hk' : σ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  by_contra hne
  have hsq : σ * σ = 1 := (perm3_two_pow hk').resolve_left hne
  set c : Perm (Fin 3) := swap 0 1 * swap 1 2 with hc
  have hρ : c * σ * c⁻¹ ∈ K := Subgroup.Normal.conj_mem ‹K.Normal› σ hσ c
  have hπ : c * σ * c⁻¹ * σ ∈ K := K.mul_mem hρ hσ
  obtain ⟨k', hk'⟩ := hK ⟨_, hπ⟩
  have hk'' : (c * σ * c⁻¹ * σ) ^ 2 ^ k' = 1 := by simpa using congrArg Subtype.val hk'
  obtain ⟨h3, hne3⟩ := perm3_product σ hsq hne
  have h3' : orderOf (c * σ * c⁻¹ * σ) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h2' : orderOf (c * σ * c⁻¹ * σ) ∣ 2 ^ k' := orderOf_dvd_of_pow_eq_one hk''
  rcases (Nat.prime_three.eq_one_or_self_of_dvd _ h3') with h | h
  · exact hne3 (orderOf_eq_one_iff.mp h)
  · rw [h] at h2'
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2'
    omega

variable {G : Type} [Group G] [Finite G]

theorem oTwoQuot_equiv_perm3 {U X : Subgroup G} (hUX : U ≤ X) (θ : ↥X →* Perm (Fin 5))
    (hQ : ∀ (x : G) (hx : x ∈ X), θ ⟨x, hx⟩ = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hU : ∀ (u : G) (hu : u ∈ U),
      θ ⟨u, hUX hu⟩ * swap 0 2 = swap 0 2 * θ ⟨u, hUX hu⟩)
    (hc : ∃ (u : G) (hu : u ∈ U), θ ⟨u, hUX hu⟩ = pu4C)
    (ht : ∃ (u : G) (hu : u ∈ U), θ ⟨u, hUX hu⟩ = swap 1 3) :
    Nonempty (OTwoQuot U ≃* Perm (Fin 3)) := by
  set θU : ↥U →* Perm (Fin 5) := θ.comp (Subgroup.inclusion hUX) with hθU
  have hθUapp : ∀ u : ↥U, θU u = θ ⟨u.1, hUX u.2⟩ := fun u => rfl
  let ψ : ↥U →* Perm (Fin 3) :=
    pu4R.comp (θU.codRestrict pu4Stab fun u => by
      rw [hθUapp]
      exact centralizer_stab _ (hU u.1 u.2))
  have hψ : ∀ u : ↥U, ψ u = pu4Rf (θ ⟨u.1, hUX u.2⟩) := fun u => by
    show pu4R ⟨θU u, _⟩ = _
    rw [pu4R_eq]
    rfl
  have hψker : ∀ u : ↥U, ψ u = 1 ↔ θ ⟨u.1, hUX u.2⟩ = 1 ∨ θ ⟨u.1, hUX u.2⟩ = swap 0 2 := fun u => by
    rw [hψ]
    exact pu4Rf_eq_one_iff _ (hU u.1 u.2)
  have hψs : Function.Surjective ψ := by
    obtain ⟨uc, huc, hθc⟩ := hc
    obtain ⟨ut, hut, hθt⟩ := ht
    intro π
    have hall : ∀ π : Perm (Fin 3), π = 1 ∨ π = pu4Rf pu4C ∨ π = pu4Rf pu4C * pu4Rf pu4C ∨
        π = pu4Rf (swap 1 3) ∨ π = pu4Rf pu4C * pu4Rf (swap 1 3) ∨
        π = pu4Rf pu4C * pu4Rf pu4C * pu4Rf (swap 1 3) := by
      unfold pu4C; decide +kernel
    have h1 : ψ ⟨uc, huc⟩ = pu4Rf pu4C := by rw [hψ]; exact congrArg pu4Rf hθc
    have h2 : ψ ⟨ut, hut⟩ = pu4Rf (swap 1 3) := by rw [hψ]; exact congrArg pu4Rf hθt
    rcases hall π with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, map_one _⟩
    · exact ⟨⟨uc, huc⟩, h1⟩
    · exact ⟨⟨uc, huc⟩ * ⟨uc, huc⟩, by rw [map_mul, h1]⟩
    · exact ⟨⟨ut, hut⟩, h2⟩
    · exact ⟨⟨uc, huc⟩ * ⟨ut, hut⟩, by rw [map_mul, h1, h2]⟩
    · exact ⟨⟨uc, huc⟩ * ⟨uc, huc⟩ * ⟨ut, hut⟩, by rw [map_mul, map_mul, h1, h2]⟩
  have hN2 : IsPGroup 2 ψ.ker := by
    intro n
    have hn : ψ n.1 = 1 := n.2
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (n.1.1 ^ 2) ^ 2 ^ k = 1 := by
      have hx : n.1.1 ^ 2 ∈ X := X.pow_mem (hUX n.1.2) 2
      have hθ1 : θ ⟨n.1.1 ^ 2, hx⟩ = 1 := by
        have e : (⟨n.1.1 ^ 2, hx⟩ : ↥X) = ⟨n.1.1, hUX n.1.2⟩ ^ 2 := rfl
        rw [e, map_pow]
        rcases (hψker n.1).mp hn with h1 | h1 <;> rw [h1]
        · simp
        · exact (by decide +kernel : swap (0 : Fin 5) 2 ^ 2 = 1)
      exact hQ _ hx hθ1
    refine ⟨k + 1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show n.1.1 ^ 2 ^ (k + 1) = 1
    rw [show 2 ^ (k + 1) = 2 * 2 ^ k from pow_succ' 2 k, pow_mul]
    exact hk
  have hpc : CFSG.Open.pCore 2 ↥U = ψ.ker := by
    apply le_antisymm
    ·
      have hnorm : (CFSG.Open.pCore 2 ↥U).Normal := CFSG.LieType.BorelTits.pCore_normal 2
      have hp : IsPGroup 2 (CFSG.Open.pCore 2 ↥U) := CFSG.LieType.BorelTits.pCore_isPGroup 2
      have : ((CFSG.Open.pCore 2 ↥U).map ψ).Normal := hnorm.map ψ hψs
      have h2 : IsPGroup 2 ((CFSG.Open.pCore 2 ↥U).map ψ) := hp.map ψ
      have := perm3_normal_two_group _ h2
      intro u hu
      have hmem : ψ u ∈ (CFSG.Open.pCore 2 ↥U).map ψ := ⟨u, hu, rfl⟩
      rw [this, Subgroup.mem_bot] at hmem
      exact hmem
    · exact CFSG.LieType.BorelTits.le_pCore 2 (MonoidHom.normal_ker ψ) hN2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hpc).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)⟩

end CFSG.Quasithin.F53Push
