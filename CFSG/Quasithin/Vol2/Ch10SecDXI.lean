module

public import CFSG.Quasithin.Background.B4L3Fin

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Quasithin

set_option maxRecDepth 100000 in
theorem L3.exists_pow_mul_mem_AS : ∀ c : L3.Vec, c ≠ 0 → ∀ δ : L3.Γ, L3.act δ c = c →
    δ ^ 3 = 1 → δ ≠ 1 → ∀ γ : L3.Γ, L3.act γ c = c → γ ^ 3 = 1 →
      ∃ i : Fin 3, δ ^ (i : ℕ) * γ ∈ L3.AS {0, c} := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem L3.mul_conj_mem_AS : ∀ c : L3.Vec, c ≠ 0 → ∀ δ : L3.Γ, L3.act δ c = c → δ ^ 3 = 1 →
    δ ≠ 1 → ∀ σ : L3.Γ, L3.act σ c = c → σ ^ 8 = 1 → σ ∉ L3.AS {0, c} →
      δ * (σ * δ * σ⁻¹) ∈ L3.AS {0, c} := by
  decide +kernel

variable {G : Type*} [Group G]

theorem conj_eq_of_mem_zpowers {g v n : G} (hgv : g * v = v * g) (hn : n ∈ Subgroup.zpowers v) :
    g * n * g⁻¹ = n := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  rw [((Commute.zpow_right (show Commute g v from hgv) k)).eq, mul_inv_cancel_right]

@[expose] def kOf (W : Subgroup G) (v : G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (W : Set G) ∧ g * v = v * g ∧
    ∀ u ∈ W, g * u * g⁻¹ * u⁻¹ ∈ Subgroup.zpowers v}
  mul_mem' := by
    rintro g h ⟨hgN, hgv, hg⟩ ⟨hhN, hhv, hh⟩
    refine ⟨Subgroup.mul_mem _ hgN hhN, by rw [mul_assoc, hhv, ← mul_assoc, hgv, mul_assoc],
      fun u hu => ?_⟩
    have e : g * h * u * (g * h)⁻¹ * u⁻¹ =
        (g * (h * u * h⁻¹ * u⁻¹) * g⁻¹) * (g * u * g⁻¹ * u⁻¹) := by group
    rw [e, conj_eq_of_mem_zpowers hgv (hh u hu)]
    exact Subgroup.mul_mem _ (hh u hu) (hg u hu)
  one_mem' := ⟨Subgroup.one_mem _, by rw [one_mul, mul_one], fun u _ => by
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]; exact Subgroup.one_mem _⟩
  inv_mem' := by
    rintro g ⟨hgN, hgv, hg⟩
    refine ⟨Subgroup.inv_mem _ hgN, ?_, fun u hu => ?_⟩
    · calc g⁻¹ * v = g⁻¹ * (v * g) * g⁻¹ := by group
        _ = v * g⁻¹ := by rw [← hgv]; group
    · have hu' : g⁻¹ * u * g ∈ W := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) u).mp hu
        simpa using this
      have e : g⁻¹ * u * g⁻¹⁻¹ * u⁻¹ = (g * (g⁻¹ * u * g) * g⁻¹ * (g⁻¹ * u * g)⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ (hg _ hu')

theorem conj_mem_kOf {W : Subgroup G} {v h g : G} (hhN : h ∈ Subgroup.normalizer (W : Set G))
    (hhv : h * v = v * h) (hg : g ∈ kOf W v) : h * g * h⁻¹ ∈ kOf W v := by
  obtain ⟨hgN, hgv, hg⟩ := hg
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hhN hgN) (Subgroup.inv_mem _ hhN), ?_,
    fun u hu => ?_⟩
  · have hv' : h⁻¹ * v = v * h⁻¹ := by
      calc h⁻¹ * v = h⁻¹ * (v * h) * h⁻¹ := by group
        _ = v * h⁻¹ := by rw [← hhv]; group
    calc h * g * h⁻¹ * v = h * g * (h⁻¹ * v) := by group
      _ = h * (g * v) * h⁻¹ := by rw [hv']; group
      _ = v * (h * g * h⁻¹) := by rw [hgv, ← mul_assoc h v, hhv]; group
  · have hu' : h⁻¹ * u * h ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhN) u).mp hu
      simpa using this
    have e : h * g * h⁻¹ * u * (h * g * h⁻¹)⁻¹ * u⁻¹ =
        h * (g * (h⁻¹ * u * h) * g⁻¹ * (h⁻¹ * u * h)⁻¹) * h⁻¹ := by group
    rw [e, conj_eq_of_mem_zpowers hhv (hg _ hu')]
    exact hg _ hu'

theorem mem_kOf_of_mem_centralizer {W : Subgroup G} {v g : G} (hv : v ∈ W)
    (hg : g ∈ Subgroup.centralizer (W : Set G)) : g ∈ kOf W v := by
  refine ⟨Subgroup.centralizer_le_normalizer (W : Set G) hg,
    ((Subgroup.mem_centralizer_iff.mp hg) v hv).symm, fun u hu => ?_⟩
  rw [← (Subgroup.mem_centralizer_iff.mp hg) u hu, mul_inv_cancel_right, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem sq_mem_centralizer_of_mem_kOf {W : Subgroup G} {v g : G} (hv2 : v ^ 2 = 1)
    (hg : g ∈ kOf W v) : g ^ 2 ∈ Subgroup.centralizer (W : Set G) := by
  obtain ⟨hgN, hgv, hg⟩ := hg
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg u hu)
  have hgu : g * u * g⁻¹ = v ^ k * u := by rw [hk]; group
  have hvk : g * v ^ k * g⁻¹ = v ^ k := conj_eq_of_mem_zpowers hgv (Subgroup.zpow_mem_zpowers v k)
  have hv2k : v ^ k * v ^ k = 1 := by
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, ← pow_two, hv2, one_zpow]
  have h2 : g * g * u * (g * g)⁻¹ = u := by
    calc g * g * u * (g * g)⁻¹ = g * (g * u * g⁻¹) * g⁻¹ := by group
      _ = g * (v ^ k * u) * g⁻¹ := by rw [hgu]
      _ = (g * v ^ k * g⁻¹) * (g * u * g⁻¹) := by group
      _ = u := by rw [hvk, hgu, ← mul_assoc, hv2k, one_mul]
  rw [pow_two]
  calc u * (g * g) = g * g * u * (g * g)⁻¹ * (g * g) := by rw [h2]
    _ = g * g * u := by group

theorem conj_mem_kOf_of {W W' : Subgroup G} {v v' t g : G}
    (hW : ∀ w : G, w ∈ W' ↔ t * w * t⁻¹ ∈ W) (hv : t * v' * t⁻¹ = v) (hg : g ∈ kOf W v) :
    t⁻¹ * g * t ∈ kOf W' v' := by
  obtain ⟨hgN, hgv, hg⟩ := hg
  have hv' : v' = t⁻¹ * v * t := by rw [← hv]; group
  refine ⟨?_, ?_, fun u hu => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [hW, hW]
    have e : t * (t⁻¹ * g * t * w * (t⁻¹ * g * t)⁻¹) * t⁻¹ = g * (t * w * t⁻¹) * g⁻¹ := by group
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp hgN _
  · rw [hv']
    calc t⁻¹ * g * t * (t⁻¹ * v * t) = t⁻¹ * (g * v) * t := by group
      _ = t⁻¹ * (v * g) * t := by rw [hgv]
      _ = t⁻¹ * v * t * (t⁻¹ * g * t) := by group
  · have h1 := hg _ ((hW u).mp hu)
    have e : t⁻¹ * g * t * u * (t⁻¹ * g * t)⁻¹ * u⁻¹ =
        t⁻¹ * (g * (t * u * t⁻¹) * g⁻¹ * (t * u * t⁻¹)⁻¹) * t := by group
    rw [e]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    rw [← hk, hv']
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [show t⁻¹ * v * t = t⁻¹ * v * t⁻¹⁻¹ by rw [inv_inv], conj_zpow, inv_inv]

theorem pow_mul_mem_of {N : Subgroup G} {x s y : G} (hx : x ∈ Subgroup.normalizer (N : Set G))
    (hs : s ∈ Subgroup.normalizer (N : Set G)) (hb : x * (s * x * s⁻¹) ∈ N) {i : ℕ}
    (ha : x ^ i * y ∈ N) : x ^ (2 * i) * (y * (s * y * s⁻¹)⁻¹) ∈ N := by
  have hconj : ∀ g ∈ Subgroup.normalizer (N : Set G), ∀ n ∈ N, g * n * g⁻¹ ∈ N :=
    fun g hg n hn => (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have hpow : ∀ w : G, x * w ∈ N → ∀ n : ℕ, x ^ n * w ^ n ∈ N := by
    intro w hw n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : x ^ (n + 1) * w ^ (n + 1) = (x ^ n * (x * w) * (x ^ n)⁻¹) * (x ^ n * w ^ n) := by
        rw [pow_succ', pow_succ']
        group
      rw [e]
      exact N.mul_mem (hconj _ (Subgroup.pow_mem _ hx n) _ hw) ih
  set e := (s * x * s⁻¹) ^ i with he
  set c := s * y * s⁻¹ with hc
  have hec : e * c ∈ N := by
    have h1 := hconj s hs _ ha
    have e1 : s * (x ^ i * y) * s⁻¹ = e * c := by
      rw [he, hc, conj_pow]
      group
    rwa [e1] at h1
  have e2 : x ^ (2 * i) * (y * c⁻¹) =
      x ^ i * (x ^ i * y * (e * c)⁻¹) * (x ^ i)⁻¹ * (x ^ i * e) := by
    rw [two_mul, pow_add]
    group
  rw [e2]
  exact N.mul_mem (hconj _ (Subgroup.pow_mem _ hx i) _ (N.mul_mem ha (N.inv_mem hec)))
    (hpow _ hb i)

end CFSG.Quasithin.Vol2.Ch10.SecD
