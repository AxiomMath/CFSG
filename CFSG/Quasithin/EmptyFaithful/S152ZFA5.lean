module

public import CFSG.Quasithin.Background.HA5Weyl

public section

namespace CFSG.Quasithin.F204

open Equiv CFSG.QuasithinUnique.A5.Delta5 CFSG.Quasithin.H.A5W

theorem klein_std_closure : ∀ x : Perm (Fin 5), Perm.sign x = 1 → x ∉ kleinSet →
    x ^ 10 ≠ 1 ∨ ∃ v ∈ kleinSet, ∃ w ∈ kleinSet, ((v * x * v⁻¹) * (w * x * w⁻¹)⁻¹) ^ 10 ≠ 1 := by
  decide +kernel

theorem perm5_pow_four : ∀ σ : Perm (Fin 5), σ ^ 8 = 1 → σ ^ 4 = 1 := by
  decide +kernel

@[expose] def NormK (n : Perm (Fin 5)) : Prop :=
  ∀ x : Perm (Fin 5), x ∈ kleinSet ↔ n * x * n⁻¹ ∈ kleinSet

instance (n : Perm (Fin 5)) : Decidable (NormK n) := by unfold NormK; infer_instance

theorem klein_std_sigma : ∀ σ : Perm (Fin 5), NormK σ →
    (∀ n : Perm (Fin 5), Perm.sign n = 1 → NormK n → σ * n * σ⁻¹ * n⁻¹ ∈ kleinSet) →
    σ ^ 4 = 1 → σ ∈ kleinSet := by
  decide +kernel

private theorem mem_klein_of_perm {v : Perm (Fin 5)} (hv : v ∈ kleinSet) :
    (⟨v, Perm.mem_alternatingGroup.mpr (kleinSet_alt v hv)⟩ : Alt5) ∈ kleinStd := hv

private theorem conj_pow_aux (g x : Alt5) (n : ℕ) : (g⁻¹ * x * g) ^ n = g⁻¹ * x ^ n * g := by
  simpa using conj_pow (a := g⁻¹) (b := x) (i := n)

private theorem conj_pow_perm (g x : Perm (Fin 5)) (n : ℕ) :
    (g⁻¹ * x * g) ^ n = g⁻¹ * x ^ n * g := by
  simpa using conj_pow (a := g⁻¹) (b := x) (i := n)

theorem closure_aux {V : Subgroup Alt5} (hV : Nat.card V = 4) {x : Alt5} (hx : x ∉ V) :
    x ^ 10 ≠ 1 ∨ ∃ v ∈ V, ∃ w ∈ V, ((v * x * v⁻¹) * (w * x * w⁻¹)⁻¹) ^ 10 ≠ 1 := by
  obtain ⟨g, hg⟩ := exists_conj_kleinStd V hV
  have hx' : g⁻¹ * x * g ∉ kleinStd := fun h => hx ((hg x).mpr h)
  have hsign : Perm.sign ((g⁻¹ * x * g : Alt5) : Perm (Fin 5)) = 1 :=
    Perm.mem_alternatingGroup.mp (g⁻¹ * x * g).2
  have key := klein_std_closure _ hsign hx'
  rcases key with h | ⟨v, hv, w, hw, h⟩
  · left
    intro h10
    apply h
    have h1 : (g⁻¹ * x * g) ^ 10 = 1 := by
      rw [conj_pow_aux, h10]
      group
    simpa using congrArg Subtype.val h1
  · right
    set va : Alt5 := ⟨v, Perm.mem_alternatingGroup.mpr (kleinSet_alt v hv)⟩ with hva
    set wa : Alt5 := ⟨w, Perm.mem_alternatingGroup.mpr (kleinSet_alt w hw)⟩ with hwa
    have hv1 : g * va * g⁻¹ ∈ V := by
      refine (hg _).mpr ?_
      have : g⁻¹ * (g * va * g⁻¹) * g = va := by group
      rw [this]
      exact mem_klein_of_perm hv
    have hw1 : g * wa * g⁻¹ ∈ V := by
      refine (hg _).mpr ?_
      have : g⁻¹ * (g * wa * g⁻¹) * g = wa := by group
      rw [this]
      exact mem_klein_of_perm hw
    refine ⟨g * va * g⁻¹, hv1, g * wa * g⁻¹, hw1, fun h10 => h ?_⟩
    have h2 : (va * (g⁻¹ * x * g) * va⁻¹ * (wa * (g⁻¹ * x * g) * wa⁻¹)⁻¹) ^ 10 = 1 := by
      have e : va * (g⁻¹ * x * g) * va⁻¹ * (wa * (g⁻¹ * x * g) * wa⁻¹)⁻¹ =
          g⁻¹ * (((g * va * g⁻¹) * x * (g * va * g⁻¹)⁻¹) *
            ((g * wa * g⁻¹) * x * (g * wa * g⁻¹)⁻¹)⁻¹) * g := by group
      rw [e, conj_pow_aux, h10]
      group
    simpa using congrArg Subtype.val h2

private theorem conj_four {G : Type*} [Group G] {τ : G} (h : τ ^ 4 = 1) (x : G) :
    τ * (τ * (τ * (τ * x * τ⁻¹) * τ⁻¹) * τ⁻¹) * τ⁻¹ = x := by
  have h1 : τ * τ * τ * τ = 1 := by simpa [pow_succ, mul_assoc] using h
  have h2 : τ⁻¹ * τ⁻¹ * τ⁻¹ * τ⁻¹ = 1 := by
    have := congrArg (·⁻¹) h1
    simpa [mul_assoc] using this
  calc τ * (τ * (τ * (τ * x * τ⁻¹) * τ⁻¹) * τ⁻¹) * τ⁻¹
      = (τ * τ * τ * τ) * x * (τ⁻¹ * τ⁻¹ * τ⁻¹ * τ⁻¹) := by simp only [mul_assoc]
    _ = x := by rw [h1, h2]; simp

private theorem perm5_pow_eight {σ : Perm (Fin 5)} {k : ℕ} (h : σ ^ 2 ^ k = 1) : σ ^ 8 = 1 := by
  have hd : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have h120 : orderOf σ ∣ 120 := by
    have : Nat.card (Perm (Fin 5)) = 120 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]; decide
    rw [← this]
    exact orderOf_dvd_natCard σ
  have hj3 : j ≤ 3 := by
    by_contra hlt
    have h16 : 2 ^ 4 ∣ 120 := by
      rw [hj'] at h120
      exact (pow_dvd_pow 2 (by omega)).trans h120
    norm_num at h16
  have : orderOf σ ∣ 8 := by
    rw [hj']
    exact (pow_dvd_pow 2 hj3 : 2 ^ j ∣ 2 ^ 3)
  exact orderOf_dvd_iff_pow_eq_one.mp this

theorem sigma_aux {V : Subgroup Alt5} (hV : Nat.card V = 4) (ψ : Alt5 ≃* Alt5) (k : ℕ)
    (hk : ∀ a : Alt5, (⇑ψ)^[2 ^ k] a = a) (h1 : ∀ v ∈ V, ψ v ∈ V)
    (h2 : ∀ n ∈ Subgroup.normalizer (V : Set Alt5), ψ n * n⁻¹ ∈ V) :
    ∃ v ∈ V, ∀ a : Alt5, ψ a = v * a * v⁻¹ := by
  obtain ⟨σ, hσ⟩ := aut_inner ψ
  have hiter : ∀ (m : ℕ) (a : Alt5), (((⇑ψ)^[m] a : Alt5) : Perm (Fin 5)) =
      σ ^ m * a * (σ ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro a; simp
    | succ m ih =>
      intro a
      rw [Function.iterate_succ_apply', hσ, ih, pow_succ]
      group
  have hcent : σ ^ 2 ^ k = 1 := by
    apply cent_alt
    intro a ha
    have := hiter (2 ^ k) ⟨a, Perm.mem_alternatingGroup.mpr ha⟩
    rw [hk] at this
    calc σ ^ 2 ^ k * a = σ ^ 2 ^ k * a * (σ ^ 2 ^ k)⁻¹ * σ ^ 2 ^ k := by group
      _ = a * σ ^ 2 ^ k := by rw [← this]
  have h4 : σ ^ 4 = 1 := perm5_pow_four σ (perm5_pow_eight hcent)
  obtain ⟨g, hg⟩ := exists_conj_kleinStd V hV
  set gp : Perm (Fin 5) := (g : Perm (Fin 5)) with hgp
  set τ : Perm (Fin 5) := gp⁻¹ * σ * gp with hτ
  have hmemV : ∀ y : Alt5, y ∈ V ↔ gp⁻¹ * (y : Perm (Fin 5)) * gp ∈ kleinSet := fun y => hg y
  have hτ4 : τ ^ 4 = 1 := by rw [hτ, conj_pow_perm, h4]; group
  have hτmap : ∀ x : Perm (Fin 5), x ∈ kleinSet → τ * x * τ⁻¹ ∈ kleinSet := by
    intro x hx
    set xa : Alt5 := ⟨x, Perm.mem_alternatingGroup.mpr (kleinSet_alt x hx)⟩ with hxa
    have hgx : g * xa * g⁻¹ ∈ V := by
      refine (hg _).mpr ?_
      have : g⁻¹ * (g * xa * g⁻¹) * g = xa := by group
      rw [this]
      exact mem_klein_of_perm hx
    have h3 := (hmemV _).mp (h1 _ hgx)
    have e : gp⁻¹ * (((ψ (g * xa * g⁻¹) : Alt5)) : Perm (Fin 5)) * gp = τ * x * τ⁻¹ := by
      rw [hσ]
      show gp⁻¹ * (σ * (gp * x * gp⁻¹) * σ⁻¹) * gp = _
      rw [hτ]
      group
    rwa [e] at h3
  have hNormτ : NormK τ := by
    intro x
    refine ⟨hτmap x, fun hx => ?_⟩
    have h3 := hτmap _ (hτmap _ (hτmap _ hx))
    have e2 : τ * (τ * (τ * (τ * x * τ⁻¹) * τ⁻¹) * τ⁻¹) * τ⁻¹ = x := conj_four hτ4 x
    rwa [e2] at h3
  have hcomm : ∀ n : Perm (Fin 5), Perm.sign n = 1 → NormK n → τ * n * τ⁻¹ * n⁻¹ ∈ kleinSet := by
    intro n hn hNn
    set na : Alt5 := ⟨n, Perm.mem_alternatingGroup.mpr hn⟩ with hna
    have hnorm : g * na * g⁻¹ ∈ Subgroup.normalizer (V : Set Alt5) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [hmemV y, hmemV (g * na * g⁻¹ * y * (g * na * g⁻¹)⁻¹)]
      have e : gp⁻¹ * ((((g * na * g⁻¹ * y * (g * na * g⁻¹)⁻¹ : Alt5)) : Perm (Fin 5))) * gp =
          n * (gp⁻¹ * (y : Perm (Fin 5)) * gp) * n⁻¹ := by
        show gp⁻¹ * (gp * n * gp⁻¹ * (y : Perm (Fin 5)) * (gp * n * gp⁻¹)⁻¹) * gp = _
        group
      rw [e]
      exact hNn _
    have h3 := (hmemV _).mp (h2 _ hnorm)
    have e : gp⁻¹ * ((((ψ (g * na * g⁻¹) : Alt5) * (g * na * g⁻¹)⁻¹ : Alt5)) : Perm (Fin 5)) * gp =
        τ * n * τ⁻¹ * n⁻¹ := by
      rw [show (((ψ (g * na * g⁻¹) : Alt5) * (g * na * g⁻¹)⁻¹ : Alt5) : Perm (Fin 5)) =
          ((ψ (g * na * g⁻¹) : Alt5) : Perm (Fin 5)) * (gp * n * gp⁻¹)⁻¹ from rfl, hσ]
      show gp⁻¹ * (σ * (gp * n * gp⁻¹) * σ⁻¹ * (gp * n * gp⁻¹)⁻¹) * gp = _
      rw [hτ]
      group
    rwa [e] at h3
  have hτK : τ ∈ kleinSet := klein_std_sigma τ hNormτ hcomm hτ4
  set ta : Alt5 := ⟨τ, Perm.mem_alternatingGroup.mpr (kleinSet_alt τ hτK)⟩ with hta
  have hv : g * ta * g⁻¹ ∈ V := by
    refine (hg _).mpr ?_
    have : g⁻¹ * (g * ta * g⁻¹) * g = ta := by group
    rw [this]
    exact mem_klein_of_perm hτK
  refine ⟨g * ta * g⁻¹, hv, fun a => ?_⟩
  apply Subtype.ext
  rw [hσ]
  show σ * (a : Perm (Fin 5)) * σ⁻¹ = gp * τ * gp⁻¹ * (a : Perm (Fin 5)) * (gp * τ * gp⁻¹)⁻¹
  rw [hτ]
  group

end CFSG.Quasithin.F204
