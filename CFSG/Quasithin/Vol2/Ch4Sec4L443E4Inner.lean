module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeAxB
public import CFSG.Quasithin.Background.A3Structure38Facts
public import CFSG.Quasithin.Vol2.Ch4Sec4L443EFact

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
open scoped Pointwise commutatorElement

variable {H : Type} [Group H]

theorem mem_sup_centralizer_of_conj_eq {K : Subgroup H} {x k : H} (hk : k ∈ K)
    (h : ∀ y ∈ K, x * y * x⁻¹ = k * y * k⁻¹) : x ∈ K ⊔ Subgroup.centralizer (K : Set H) := by
  have hc : k⁻¹ * x ∈ Subgroup.centralizer (K : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := h y hy
    calc y * (k⁻¹ * x) = k⁻¹ * (k * y * k⁻¹) * x := by group
      _ = k⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
      _ = k⁻¹ * x * y := by group
  have e : x = k * (k⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hc)

theorem le_sup_centralizer_of_outSolvable {K X : Subgroup H} (hOut : OutSolvable ↥K)
    (hXK : X ≤ Subgroup.normalizer (K : Set H)) (hX : ⁅X, X⁆ = X) :
    X ≤ K ⊔ Subgroup.centralizer (K : Set H) := by
  set ψ : ↥X →* MulAut ↥K := (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hXK)
    with hψ
  have htop : ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ = (⊤ : Subgroup ↥X) := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hX]
  have hDX : ∀ n : ℕ, derivedSeries ↥X n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, htop]
  intro x hx
  obtain ⟨n, hn⟩ := hOut
  have hmem : ψ ⟨x, hx⟩ ∈ derivedSeries (MulAut ↥K) n := by
    refine map_derivedSeries_le_derivedSeries ψ n ⟨⟨x, hx⟩, ?_, rfl⟩
    rw [hDX n]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := hn hmem
  refine mem_sup_centralizer_of_conj_eq k.2 fun y hy => ?_
  have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨y, hy⟩ : ↥K) : H)) hk
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
  rw [hψ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
  exact h1.symm

theorem le_sup_centralizer_of_commutator_eq {K X V : Subgroup H}
    (hXKC : X ≤ K ⊔ Subgroup.centralizer (K : Set H))
    (hVK : V ≤ Subgroup.normalizer (K : Set H)) (hV : V = ⁅V, X⁆) :
    V ≤ K ⊔ Subgroup.centralizer (K : Set H) := by
  have hKC : K ≤ Subgroup.normalizer (Subgroup.centralizer (K : Set H) : Set H) :=
    Subgroup.le_normalizer.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer K)
  rw [hV, Subgroup.commutator_le]
  intro v hv x hx
  have hx' : x ∈ (K : Set H) * (Subgroup.centralizer (K : Set H) : Set H) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K _ hKC]
    exact hXKC hx
  obtain ⟨k, hk, c, hc, rfl⟩ := hx'
  have hvN := hVK hv
  have hvk : v * k * v⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hvN k).mp hk
  have hvc : v * c * v⁻¹ ∈ Subgroup.centralizer (K : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : v⁻¹ * y * v ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hvN) y).mp hy
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hy'
    calc y * (v * c * v⁻¹) = v * ((v⁻¹ * y * v) * c) * v⁻¹ := by group
      _ = v * (c * (v⁻¹ * y * v)) * v⁻¹ := by rw [h1]
      _ = v * c * v⁻¹ * y := by group
  have e : ⁅v, k * c⁆ = (v * k * v⁻¹) * (v * c * v⁻¹) * c⁻¹ * k⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hvk)
    (Subgroup.mem_sup_right hvc)) (Subgroup.mem_sup_right (Subgroup.inv_mem _ hc)))
    (Subgroup.mem_sup_left (Subgroup.inv_mem _ hk))

end CFSG.Quasithin.H13.Ch4.E443
