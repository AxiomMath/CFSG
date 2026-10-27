module

public import CFSG.RankThree.PartOne.N143.JACount

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartOne.KFOUT3 (SL3 Tor IsZeta diagSL tSep tNon permSL ent ent_ext tSep_mem)
open scoped commutatorElement

@[expose] def swap01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

theorem perm_cycle_two_ne : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → σ ≠ 1 → σ 2 ≠ 2 := by decide

theorem perm_comm_cycle : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → σ ≠ 1 →
    (σ * swap01⁻¹ * σ⁻¹ * swap01) ^ 3 = 1 ∧ σ * swap01⁻¹ * σ⁻¹ * swap01 ≠ 1 := by
  decide +kernel

section DLemmas

variable {G : Type} [Group G] {A J : Subgroup G}

theorem conj_mem_D {g : G} (hgJ : g ∈ Subgroup.normalizer (J : Set G))
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) {d : G}
    (hd : d ∈ J ⊓ Subgroup.centralizer (A : Set G)) :
    g * d * g⁻¹ ∈ J ⊓ Subgroup.centralizer (A : Set G) := by
  refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hgJ d).1 hd.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have ha' : g⁻¹ * a * g ∈ A := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgA) a).1 ha
    simpa using this
  have hc : (g⁻¹ * a * g) * d = d * (g⁻¹ * a * g) := Subgroup.mem_centralizer_iff.1 hd.2 _ ha'
  calc a * (g * d * g⁻¹) = g * ((g⁻¹ * a * g) * d) * g⁻¹ := by group
    _ = g * (d * (g⁻¹ * a * g)) * g⁻¹ := by rw [hc]
    _ = g * d * g⁻¹ * a := by group

end DLemmas

section Star

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A J : Subgroup G} {c : G} {K : Type} [Field K]
  {ρ : SL3 K →* G}

theorem D_comm (hp : p.Prime) (h : JGood p A c J) (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ}
    (hζ : IsZeta p ζ) {d d' : G} (hd : d ∈ J ⊓ Subgroup.centralizer (A : Set G))
    (hd' : d' ∈ J ⊓ Subgroup.centralizer (A : Set G)) : d * d' = d' * d := by
  obtain ⟨m, hm, rfl⟩ := (hρ.mem_inf_centralizer_iff hp h).1 hd
  obtain ⟨n, hn, rfl⟩ := (hρ.mem_inf_centralizer_iff hp h).1 hd'
  rw [← map_mul, ← map_mul, commute_of_mem_centralizer_Tor hζ hm hn]

theorem star_comm (hp : p.Prime) (h : JGood p A c J) (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ}
    (hζ : IsZeta p ζ) {u s : G} (huJ : u ∈ Subgroup.normalizer (J : Set G))
    (huA : u ∈ Subgroup.normalizer (A : Set G)) {k : ℕ} (huk : ∀ a ∈ A, u * a * u⁻¹ = a ^ k)
    (hsJ : s ∈ J) (hsA : s ∈ Subgroup.normalizer (A : Set G)) {d : G}
    (hd : d ∈ J ⊓ Subgroup.centralizer (A : Set G)) :
    u * (s * d * s⁻¹) * u⁻¹ = s * (u * d * u⁻¹) * s⁻¹ := by
  have hsJ' : s ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hsJ
  have hconjA : ∀ a ∈ A, (u * s * u⁻¹) * a * (u * s * u⁻¹)⁻¹ = s * a * s⁻¹ := by
    intro a ha
    have ha' : u⁻¹ * a * u ∈ A := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ huA) a).1 ha
      simpa using this
    have hsa' : s * (u⁻¹ * a * u) * s⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hsA _).1 ha'
    have e1 : (u * s * u⁻¹) * a * (u * s * u⁻¹)⁻¹ =
        u * (s * (u⁻¹ * a * u) * s⁻¹) * u⁻¹ := by group
    have e2 : (u⁻¹ * a * u) ^ k = a := by
      rw [← huk _ ha']
      group
    rw [e1, huk _ hsa', conj_pow, e2]
  obtain ⟨e, he⟩ : ∃ e : G, e = u * s * u⁻¹ * s⁻¹ := ⟨_, rfl⟩
  have heD : e ∈ J ⊓ Subgroup.centralizer (A : Set G) := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [he]
      exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 huJ s).1 hsJ)
        (Subgroup.inv_mem _ hsJ)
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hs'A : s⁻¹ * a * s ∈ A := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hsA) a).1 ha
        simpa using this
      have h1 := hconjA _ hs'A
      have h2 : e * a * e⁻¹ = a := by
        calc e * a * e⁻¹ = (u * s * u⁻¹) * (s⁻¹ * a * s) * (u * s * u⁻¹)⁻¹ := by rw [he]; group
          _ = s * (s⁻¹ * a * s) * s⁻¹ := h1
          _ = a := by group
      exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  have hx : s * (u * d * u⁻¹) * s⁻¹ ∈ J ⊓ Subgroup.centralizer (A : Set G) :=
    conj_mem_D hsJ' hsA (conj_mem_D huJ huA hd)
  have hcomm : e * (s * (u * d * u⁻¹) * s⁻¹) = (s * (u * d * u⁻¹) * s⁻¹) * e :=
    D_comm hp h hρ hζ heD hx
  calc u * (s * d * s⁻¹) * u⁻¹ = (e * (s * (u * d * u⁻¹) * s⁻¹)) * e⁻¹ := by rw [he]; group
    _ = (s * (u * d * u⁻¹) * s⁻¹) * e * e⁻¹ := by rw [hcomm]
    _ = s * (u * d * u⁻¹) * s⁻¹ := by rw [mul_inv_cancel_right]

end Star

section Moved

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A J : Subgroup G} {c : G} {K : Type} [Field K]
  [Finite K] {ρ : SL3 K →* G}

omit [Finite K] in
theorem prod_const_of_pow {r : Kˣ} (hr : r ^ 3 = 1) : ∏ _i : Fin 3, r = 1 := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact hr

omit [Finite G] [Finite K] in
theorem ratio_const (hρ : IsPSL3Cover p A J ρ) {m : SL3 K} {σ : Equiv.Perm (Fin 3)}
    (hm : ActsAll m σ) {u : Fin 3 → Kˣ} (hu : ∏ i, u i = 1)
    (h : ρ (m * diagSL u hu * m⁻¹) = ρ (diagSL u hu)) :
    ∃ (r₀ : Kˣ) (hr : r₀ ^ 3 = 1), (∀ k, u (σ⁻¹ k) = r₀ * u k) ∧
      ρ (diagSL (fun _ => r₀) (prod_const_of_pow hr)) = 1 := by
  rw [hm u hu] at h
  have hker0 : ρ (diagSL (permVec σ u) (prod_permVec σ hu) * (diagSL u hu)⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hmem : diagSL (permVec σ u) (prod_permVec σ hu) * (diagSL u hu)⁻¹ ∈
      Subgroup.center (SL3 K) :=
    hρ.ker_central (MonoidHom.mem_ker.2 hker0)
  rw [diagSL_inv, diagSL_mul] at hmem hker0
  have hconst : ∀ a b : Fin 3, permVec σ u a * (u a)⁻¹ = permVec σ u b * (u b)⁻¹ :=
    fun a b => KFOUT3.const_of_diagSL_mem_center hmem a b
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : Kˣ, ∀ k, permVec σ u k * (u k)⁻¹ = r₀ :=
    ⟨permVec σ u 0 * (u 0)⁻¹, fun k => hconst k 0⟩
  have hu_eq : ∀ k, u (σ⁻¹ k) = r₀ * u k := by
    intro k
    have e : u (σ⁻¹ k) = permVec σ u k := rfl
    rw [e]
    calc permVec σ u k = (permVec σ u k * (u k)⁻¹) * u k := by group
      _ = r₀ * u k := by rw [hr₀ k]
  have hr3 : r₀ ^ 3 = 1 := by
    have h1 : ∏ k, u (σ⁻¹ k) = ∏ k, (r₀ * u k) := Finset.prod_congr rfl fun k _ => hu_eq k
    rw [Equiv.prod_comp σ⁻¹ u, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hu] at h1
    simpa using h1.symm
  refine ⟨r₀, hr3, hu_eq, ?_⟩
  have : diagSL (fun _ => r₀) (prod_const_of_pow hr3) =
      diagSL (permVec σ u * u⁻¹) (by
        simp only [Pi.mul_apply, Pi.inv_apply, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
          prod_permVec σ hu, hu, inv_one, mul_one]) :=
    diagSL_congr (funext fun k => (hr₀ k).symm) _ _
  rw [this]
  exact hker0

end Moved

section MovedV

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A J : Subgroup G} {c : G} {K : Type} [Field K]
  [Finite K] {ρ : SL3 K →* G}

omit [Finite K] in
theorem dm_pow_three (a b : Kˣ) : (dm (a, b) : SL3 K) ^ 3 = dm (a ^ 3, b ^ 3) :=
  (map_pow dm (a, b) 3).symm.trans (congrArg dm (Prod.ext rfl rfl))

omit [Finite K] in
theorem dmVec_xx_of_ne (x : Kˣ) {k : Fin 3} (hk : k ≠ 2) : dmVec x x k = x := by
  fin_cases k <;> simp [dmVec] at hk ⊢

omit [Finite K] in
theorem dmVec_const (r : Kˣ) (hr : r ^ 3 = 1) : dmVec r r = fun _ => r := by
  have hrr : (r * r)⁻¹ = r := inv_eq_of_mul_eq_one_right (by rw [← pow_three']; exact hr)
  funext i
  fin_cases i <;> simp [dmVec, hrr]

omit [Finite K] in
theorem dm_const (r : Kˣ) (hr : r ^ 3 = 1) :
    (dm (r, r) : SL3 K) = diagSL (fun _ => r) (prod_const_of_pow hr) :=
  (dm_apply (r, r)).trans (diagSL_congr (dmVec_const r hr) _ _)

theorem exists_moved_V (hp : p.Prime) (h : JGood p A c J) (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ}
    (hζ : IsZeta p ζ) (h9 : 9 ∣ Nat.card K - 1) {m : SL3 K} {σ : Equiv.Perm (Fin 3)}
    (hm : ActsAll m σ) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) :
    ∃ v ∈ Vof A J, ρ m * v * (ρ m)⁻¹ ≠ v := by
  obtain ⟨ε, hε⟩ := exists_unit_orderOf_nine h9
  have hσ2 : σ 2 ≠ 2 := perm_cycle_two_ne σ hσ3 hσ1
  have hσ2' : σ⁻¹ 2 ≠ 2 := fun h2 => hσ2 (Equiv.Perm.inv_eq_iff_eq.1 h2).symm
  have hmem : ∀ X : Kˣ × Kˣ, ρ (dm X) ∈ J ⊓ Subgroup.centralizer (A : Set G) := fun X =>
    (mem_inf_centralizer_iff_dm hp h hρ hζ).2 ⟨X, rfl⟩
  by_cases hK : ∃ (r : Kˣ) (hr : r ^ 3 = 1), r ≠ 1 ∧
      ρ (diagSL (fun _ => r) (prod_const_of_pow hr)) = 1
  · obtain ⟨r, hr, hr1, hrk⟩ := hK
    obtain ⟨x, hx⟩ := exists_cube_of_pow_three hε hr
    have hcube : ρ (dm (x, x)) ^ 3 = 1 := by
      rw [← map_pow, dm_pow_three, hx, dm_const r hr]
      exact hrk
    refine ⟨ρ (dm (x, x)), (mem_Vof_iff hp h hρ hζ).2 ⟨hmem _, hcube⟩, ?_⟩
    intro hfix
    have h1 : ρ (m * diagSL (dmVec x x) (prod_dmVec x x) * m⁻¹) =
        ρ (diagSL (dmVec x x) (prod_dmVec x x)) := by
      rw [map_mul, map_mul, map_inv]
      exact hfix
    obtain ⟨r₀, hr₀3, hu, -⟩ := ratio_const hρ hm (prod_dmVec x x) h1
    have E1 : (x * x)⁻¹ = r₀ * x := by
      have := hu (σ 2)
      rw [show σ⁻¹ (σ 2) = 2 by simp, dmVec_xx_of_ne x hσ2] at this
      simpa [dmVec] using this
    have E2 : x = r₀ * (x * x)⁻¹ := by
      have := hu 2
      rw [dmVec_xx_of_ne x hσ2'] at this
      simpa [dmVec] using this
    have E3 : x = r₀ * (r₀ * x) := by
      rw [E1] at E2
      exact E2
    have hr0sq : r₀ * r₀ = 1 := by
      have h2 : (r₀ * r₀) * x = 1 * x := by
        calc (r₀ * r₀) * x = r₀ * (r₀ * x) := mul_assoc _ _ _
          _ = x := E3.symm
          _ = 1 * x := (one_mul x).symm
      exact mul_right_cancel h2
    have hr0 : r₀ = 1 := by
      calc r₀ = r₀ * (r₀ * r₀) := by rw [hr0sq, mul_one]
        _ = r₀ ^ 3 := (pow_three r₀).symm
        _ = 1 := hr₀3
    rw [hr0, one_mul] at E1
    have hx3 : x ^ 3 = 1 := by
      rw [pow_three']
      exact mul_eq_one_iff_inv_eq.2 E1
    exact hr1 (hx.symm.trans hx3)
  · push Not at hK
    have hε9 : ε ^ 9 = 1 := by
      have := pow_orderOf_eq_one ε
      rwa [hε] at this
    obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, ω = ε ^ 3 := ⟨_, rfl⟩
    have hω3 : ω ^ 3 = 1 := by
      rw [hω, ← pow_mul]
      exact hε9
    have hω1 : ω ≠ 1 := by
      intro h1
      rw [hω] at h1
      have := orderOf_dvd_of_pow_eq_one h1
      rw [hε] at this
      omega
    have hω2 : ω ^ 2 ≠ 1 := by
      intro h1
      rw [hω, ← pow_mul] at h1
      have := orderOf_dvd_of_pow_eq_one h1
      rw [hε] at this
      omega
    have hω12 : ω ≠ ω ^ 2 := by
      intro h1
      apply hω1
      have : ω * ω = ω * 1 := by
        rw [mul_one, ← sq]
        exact h1.symm
      exact mul_left_cancel this
    have hprod : ω * ω ^ 2 = 1 := by
      rw [← pow_succ']
      exact hω3
    have hinv : (ω * ω ^ 2)⁻¹ = 1 := by rw [hprod, inv_one]
    have hsq3 : (ω ^ 2) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
    have hcube : ρ (dm (ω, ω ^ 2)) ^ 3 = 1 := by
      rw [← map_pow, dm_pow_three, hω3, hsq3]
      have : (dm (1, 1) : SL3 K) = 1 := map_one dm
      rw [this, map_one]
    refine ⟨ρ (dm (ω, ω ^ 2)), (mem_Vof_iff hp h hρ hζ).2 ⟨hmem _, hcube⟩, ?_⟩
    intro hfix
    have h1 : ρ (m * diagSL (dmVec ω (ω ^ 2)) (prod_dmVec ω (ω ^ 2)) * m⁻¹) =
        ρ (diagSL (dmVec ω (ω ^ 2)) (prod_dmVec ω (ω ^ 2))) := by
      rw [map_mul, map_mul, map_inv]
      exact hfix
    obtain ⟨r₀, hr₀3, hu, hrk⟩ := ratio_const hρ hm (prod_dmVec ω (ω ^ 2)) h1
    have hr₀1 : r₀ = 1 := by
      by_contra hne
      exact hK r₀ hr₀3 hne hrk
    have hinj : Function.Injective (dmVec ω (ω ^ 2)) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [dmVec, hinv, hω12, hω1, hω2, hω12.symm, hω1.symm, hω2.symm] at hij ⊢
    have hfix' : ∀ k, dmVec ω (ω ^ 2) (σ⁻¹ k) = dmVec ω (ω ^ 2) k := fun k => by
      rw [hu k, hr₀1, one_mul]
    have hσinv : ∀ k, σ⁻¹ k = k := fun k => hinj (hfix' k)
    apply hσ1
    refine Equiv.ext fun k => ?_
    have h4 := Equiv.apply_symm_apply σ k
    rw [show σ.symm k = k from hσinv k] at h4
    exact h4

end MovedV

theorem jLemmaA_holds (hGA : CFSG.Open.GriessAllModelsStatement) :
    JLemmaA := by
  intro G _ _ p A c J h f hf h9 hm
  classical
  obtain ⟨K, hKf, hKfin, hK, ρ, hρ⟩ := exists_psl3Data hGA h hf hm
  have hp := h.hyp.prime
  have h5 := Sec12Three.five_le h.hyp
  have hchar : CharP K 2 := charP_two_of_card hK
  obtain ⟨ζ, hζ⟩ := exists_isZeta hp h5 (by rw [hK]; exact hf)
  have h9K : 9 ∣ Nat.card K - 1 := by rw [hK]; exact h9
  refine ⟨jLemmaA_part1 hp h hρ hζ h9K, ?_⟩
  intro w hw hw3 hwne y hy k hk
  by_contra hcon
  push Not at hcon
  have hwJ : w ∈ J := hw.1
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := hw.2
  have hyJ : y ∈ Subgroup.normalizer (J : Set G) := hy.1
  have hyA : y ∈ Subgroup.normalizer (A : Set G) := hy.2
  have hwJ' : w ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hwJ
  have huJ : w⁻¹ * y ∈ Subgroup.normalizer (J : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hwJ') hyJ
  have huA : w⁻¹ * y ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hwA) hyA
  have huk : ∀ a ∈ A, (w⁻¹ * y) * a * (w⁻¹ * y)⁻¹ = a ^ k := by
    intro a ha
    have e : (w⁻¹ * y) * a * (w⁻¹ * y)⁻¹ = w⁻¹ * (y * a * y⁻¹) * w := by group
    rw [e, hk a ha]
    group
  obtain ⟨s, hsρ⟩ : ∃ s : G, ρ (permSL swap01) = s := ⟨_, rfl⟩
  have hs : s ∈ J ⊓ torusNormalizer A := by
    rw [← hsρ]
    exact (hρ.mem_inf_normalizer_iff hp h).2 ⟨permSL swap01, permSL_mem_normalizer_Tor _, rfl⟩
  have hsJ : s ∈ J := hs.1
  have hsA : s ∈ Subgroup.normalizer (A : Set G) := hs.2
  have hsJ' : s ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer hsJ
  obtain ⟨mw, hmw, hwρ⟩ := (hρ.mem_inf_normalizer_iff hp h).1 hw
  obtain ⟨σ, hσ⟩ := exists_actsBy hζ hmw
  have hv0 : ∏ k, tSep ζ 0 1 k = 1 := KFU.prod_torusElt 0 1 ζ
  have hd₀ : diagSL (tSep ζ 0 1) hv0 ∈ Tor p K := tSep_mem hζ (by decide)
  have hd₀A : ρ (diagSL (tSep ζ 0 1) hv0) ∈ A := hρ.map_mem_A hd₀
  have hσ3 : σ ^ 3 = 1 := by
    apply ActsBy.perm_pow_eq_one hp hρ hζ hσ hv0 3
    rw [map_mul, map_mul, map_inv, map_pow, hwρ]
    exact hw3 _ hd₀A
  have hσ1 : σ ≠ 1 := by
    intro h1
    obtain ⟨a, haA, hane⟩ := hwne
    apply hane
    have := hρ.act_trivial h hσ (n := 1) (by rw [pow_one]; exact h1) a haA
    rw [pow_one, hwρ] at this
    exact this
  have hAw : ActsAll mw σ := hσ.toAll hζ
  have hAs : ActsAll (permSL swap01 : SL3 K) swap01 := ActsAll.permSL swap01
  have hAc : ActsAll (mw * (permSL swap01 : SL3 K)⁻¹ * mw⁻¹ * permSL swap01)
      (σ * swap01⁻¹ * σ⁻¹ * swap01) := ((hAw.mul hAs.inv).mul hAw.inv).mul hAs
  obtain ⟨hc3, hc1⟩ := perm_comm_cycle σ hσ3 hσ1
  obtain ⟨v, hvV, hvmoved⟩ := exists_moved_V hp h hρ hζ h9K hAc hc3 hc1
  apply hvmoved
  have hρc : ρ (mw * (permSL swap01 : SL3 K)⁻¹ * mw⁻¹ * permSL swap01) =
      w * s⁻¹ * w⁻¹ * s := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hwρ, hsρ]
  rw [hρc]
  have hvD := ((mem_Vof_iff hp h hρ hζ).1 hvV)
  have hsv : s * v * s⁻¹ ∈ Vof A J := by
    refine (mem_Vof_iff hp h hρ hζ).2 ⟨conj_mem_D hsJ' hsA hvD.1, ?_⟩
    rw [conj_pow, hvD.2]
    group
  have h1 : y * v * y⁻¹ = v := hcon v hvV
  have h2 : y * (s * v * s⁻¹) * y⁻¹ = s * v * s⁻¹ := hcon _ hsv
  have hstar := star_comm hp h hρ hζ huJ huA huk hsJ hsA hvD.1
  have e1 : (w⁻¹ * y) * (s * v * s⁻¹) * (w⁻¹ * y)⁻¹ = w⁻¹ * (s * v * s⁻¹) * w := by
    calc (w⁻¹ * y) * (s * v * s⁻¹) * (w⁻¹ * y)⁻¹ = w⁻¹ * (y * (s * v * s⁻¹) * y⁻¹) * w := by
          group
      _ = w⁻¹ * (s * v * s⁻¹) * w := by rw [h2]
  have e2 : (w⁻¹ * y) * v * (w⁻¹ * y)⁻¹ = w⁻¹ * v * w := by
    calc (w⁻¹ * y) * v * (w⁻¹ * y)⁻¹ = w⁻¹ * (y * v * y⁻¹) * w := by group
      _ = w⁻¹ * v * w := by rw [h1]
  rw [e1, e2] at hstar
  calc w * s⁻¹ * w⁻¹ * s * v * (w * s⁻¹ * w⁻¹ * s)⁻¹
      = w * (s⁻¹ * (w⁻¹ * (s * v * s⁻¹) * w) * s) * w⁻¹ := by group
    _ = w * (s⁻¹ * (s * (w⁻¹ * v * w) * s⁻¹) * s) * w⁻¹ := by rw [hstar]
    _ = v := by group

end CFSG.RankThree.PartOne.N143
