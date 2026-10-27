module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentConfig
public import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentMat
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentNT
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree.PartTwo.Sec4 Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)

local notation "pmk" => Matrix.ProjGenLinGroup.mk

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem piCard_mod_three {q₀ : ℕ} (h : ModThree π q₀) :
    piCard π q₀ % 3 = 1 ∧ piCard π q₀ ^ 2 % 3 = 1 := by
  cases π
  · change q₀ % 3 = 2 at h
    have h2 : q₀ ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
    refine ⟨h2, ?_⟩
    change (q₀ ^ 2) ^ 2 % 3 = 1
    rw [Nat.pow_mod, h2]
  · change q₀ % 3 = 1 at h
    refine ⟨h, ?_⟩
    change q₀ ^ 2 % 3 = 1
    rw [Nat.pow_mod, h]

theorem fieldAut_apply_eq (hq : ModThree π (p ^ f)) {f₀ : ℕ} (hf : f = 3 * f₀) {σ : K ≃+* K}
    (hσ : (∀ c, σ c = c ^ piCard π (p ^ f₀)) ∨ ∀ c, σ c = c ^ (piCard π (p ^ f₀) ^ 2))
    {τ : K} (hτ : τ ^ 3 = 1) : σ τ = τ := by
  have hq₀ : ModThree π (p ^ f₀) := by
    apply modThree_of_cube
    rwa [← pow_mul, mul_comm, ← hf]
  obtain ⟨h1, h2⟩ := piCard_mod_three hq₀
  rcases hσ with hσ | hσ
  · exact ringAut_apply_eq_of_pow_three hσ h1 hτ
  · exact ringAut_apply_eq_of_pow_three hσ h2 hτ

theorem pow_three_ne_one_of_orderOf {G : Type*} [Group G] {ρ : G} {n : ℕ} (hρ : orderOf ρ = n)
    (hn1 : 1 < n) (hn3 : ¬ 3 ∣ n) : ρ ^ 3 ≠ 1 := by
  intro h
  have hdvd : n ∣ 3 := hρ ▸ orderOf_dvd_of_pow_eq_one h
  have hle : n ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases n <;> simp_all

theorem exists_orderOf_eq (hK : PiField π p f K) {n : ℕ} (hn0 : n ≠ 0)
    (hn : n ∣ qSubPi π (p ^ f)) : ∃ ρ : Kˣ, ρ ∈ rootsOfUnity n K ∧ orderOf ρ = n := by
  have := hK.finite
  have : NeZero n := ⟨hn0⟩
  have hcard : Nat.card (rootsOfUnity n K) = n :=
    CFSG.LinearGroups.card_rootsOfUnity_of_dvd (dvd_trans hn (qSubPi_dvd hK))
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity n K)
  refine ⟨g, g.2, ?_⟩
  rw [orderOf_submonoid, orderOf_eq_card_of_forall_mem_zpowers hg, hcard]

theorem orderOf_dvd_of_pow_eq_self {ρ : Kˣ} {s : ℕ} (hs : 1 ≤ s) (h : (ρ : K) ^ s = ρ) :
    orderOf ρ ∣ s - 1 := by
  apply orderOf_dvd_of_pow_eq_one
  have h' : ρ ^ s = ρ := Units.ext (by rw [Units.val_pow_eq_pow_val, h])
  rw [← Nat.sub_add_cancel hs, pow_succ] at h'
  exact mul_eq_right.mp h'

@[expose] noncomputable def torusHomM (hK : PiField π p f K) {n : ℕ}
    (hn : n ∣ qSubPi π (p ^ f)) :
    rootsOfUnity n K × rootsOfUnity n K →* projImage (slPi π 3 (p ^ f) K) :=
  (projOf (slPi π 3 (p ^ f) K)).comp
    ((torusHom.comp ((rootsOfUnity n K).subtype.prodMap (rootsOfUnity n K).subtype)).codRestrict
      (slPi π 3 (p ^ f) K) fun uv => torusHom_mem_slPi hK
        (rootsOfUnity_le_of_dvd hn uv.1.2) (rootsOfUnity_le_of_dvd hn uv.2.2))

theorem coe_torusHomM (hK : PiField π p f K) {n : ℕ} (hn : n ∣ qSubPi π (p ^ f))
    (uv : rootsOfUnity n K × rootsOfUnity n K) :
    (torusHomM hK hn uv : ProjGenLinGroup (Fin 3) K) =
      pmk (diagUnits (uv.1 : Kˣ) uv.2 ((uv.1 : Kˣ) * uv.2)⁻¹) :=
  rfl

@[expose] noncomputable def torusSub (hK : PiField π p f K) {n : ℕ}
    (hn : n ∣ qSubPi π (p ^ f)) : Subgroup (projImage (slPi π 3 (p ^ f) K)) :=
  (torusHomM hK hn).range

theorem mem_torusSub (hK : PiField π p f K) {n : ℕ} (hn : n ∣ qSubPi π (p ^ f))
    {m : projImage (slPi π 3 (p ^ f) K)} {u v : Kˣ} (hu : u ∈ rootsOfUnity n K)
    (hv : v ∈ rootsOfUnity n K)
    (hm : (m : ProjGenLinGroup (Fin 3) K) = pmk (diagUnits u v (u * v)⁻¹)) :
    m ∈ torusSub hK hn :=
  ⟨(⟨u, hu⟩, ⟨v, hv⟩), Subtype.ext (by rw [coe_torusHomM]; exact hm.symm)⟩

theorem not_three_dvd_card_torusSub (hK : PiField π p f K) {n : ℕ}
    (hn : n ∣ qSubPi π (p ^ f)) (hn1 : 1 < n) (hn3 : ¬ 3 ∣ n) :
    ¬ 3 ∣ Nat.card (torusSub hK hn) := by
  have := hK.finite
  have : NeZero n := ⟨by omega⟩
  have hcard : Nat.card (rootsOfUnity n K) = n :=
    CFSG.LinearGroups.card_rootsOfUnity_of_dvd (dvd_trans hn (qSubPi_dvd hK))
  have hdvd : Nat.card (torusSub hK hn) ∣ n * n := by
    have h := Subgroup.card_range_dvd (torusHomM hK hn)
    rwa [Nat.card_prod, hcard] at h
  intro h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp (dvd_trans h3 hdvd) with h | h <;> exact hn3 h

theorem mem_torusSub_of_monomial (hK : PiField π p f K) {n : ℕ} (hn : n ∣ qSubPi π (p ^ f))
    {a b c u v : Kˣ} {k : ℕ} (hk : k < 3) (hu : u ∈ rootsOfUnity n K)
    (hv : v ∈ rootsOfUnity n K) {m : projImage (slPi π 3 (p ^ f) K)}
    (hm : (m : ProjGenLinGroup (Fin 3) K) = pmk ((diagUnits a b c * cycThree ^ k) *
      diagUnits u v (u * v)⁻¹ * (diagUnits a b c * cycThree ^ k)⁻¹)) :
    m ∈ torusSub hK hn := by
  have huv : (u * v)⁻¹ ∈ rootsOfUnity n K := inv_mem (mul_mem hu hv)
  rcases conj_monomial_diagUnits_eq a b c u v (u * v)⁻¹ hk with h | h | h <;> rw [h] at hm
  · exact mem_torusSub hK hn hu hv hm
  · refine mem_torusSub hK hn huv hu ?_
    rw [hm, show ((u * v)⁻¹ * u)⁻¹ = v by group]
  · refine mem_torusSub hK hn hv huv ?_
    rw [hm, show (v * (u * v)⁻¹)⁻¹ = u by group]

@[expose] def IsMonoAct (π : Bool) (p f : ℕ) (K : Type) [Field K]
    (β : MulAut (projImage (slPi π 3 (p ^ f) K))) : Prop :=
  (∃ (a b c : Kˣ) (k : ℕ), k < 3 ∧ ∀ m : projImage (slPi π 3 (p ^ f) K),
    (β m : ProjGenLinGroup (Fin 3) K) = pmk (diagUnits a b c * cycThree ^ k) *
      (m : ProjGenLinGroup (Fin 3) K) * (pmk (diagUnits a b c * cycThree ^ k))⁻¹) ∨
  (∃ (σ : K ≃+* K) (a b c : Kˣ) (k : ℕ), k < 3 ∧ ∀ s (hs : s ∈ slPi π 3 (p ^ f) K),
    (β (projOf _ ⟨s, hs⟩) : ProjGenLinGroup (Fin 3) K) =
      pmk ((diagUnits a b c * cycThree ^ k) * frobGL σ s * (diagUnits a b c * cycThree ^ k)⁻¹))

theorem units_map_mem_rootsOfUnity (σ : K ≃+* K) {n : ℕ} {u : Kˣ}
    (hu : u ∈ rootsOfUnity n K) : Units.map (σ : K →* K) u ∈ rootsOfUnity n K := by
  rw [mem_rootsOfUnity] at hu ⊢
  rw [← map_pow, hu, map_one]

theorem IsMonoAct.mapsTo_torusSub (hK : PiField π p f K) {n : ℕ} (hn : n ∣ qSubPi π (p ^ f))
    {β : MulAut (projImage (slPi π 3 (p ^ f) K))} (hβ : IsMonoAct π p f K β) :
    ∀ w ∈ torusSub hK hn, β w ∈ torusSub hK hn := by
  rintro _ ⟨⟨u, v⟩, rfl⟩
  rcases hβ with ⟨a, b, c, k, hk, hβ⟩ | ⟨σ, a, b, c, k, hk, hβ⟩
  · refine mem_torusSub_of_monomial (a := a) (b := b) (c := c) hK hn hk u.2 v.2 ?_
    rw [hβ, coe_torusHomM]
    simp only [map_mul, map_inv]
  · have hs := torusHom_mem_slPi hK (rootsOfUnity_le_of_dvd hn u.2)
      (rootsOfUnity_le_of_dvd hn v.2)
    have he : torusHomM hK hn (u, v) = projOf _ ⟨torusHom ((u : Kˣ), (v : Kˣ)), hs⟩ := rfl
    refine mem_torusSub_of_monomial (a := a) (b := b) (c := c) hK hn hk
      (units_map_mem_rootsOfUnity σ u.2)
      (units_map_mem_rootsOfUnity σ v.2) ?_
    have hinv : Units.map (σ : K →* K) ((u : Kˣ) * v)⁻¹ =
        (Units.map (σ : K →* K) u * Units.map (σ : K →* K) v)⁻¹ := by
      rw [map_inv, map_mul]
    rw [he, hβ _ hs, show torusHom ((u : Kˣ), (v : Kˣ)) = diagUnits (u : Kˣ) v ((u : Kˣ) * v)⁻¹
      from rfl, frobGL_diagUnits, hinv]

variable {ι : Type*} {α : ι → MulAut (projImage (slPi π 3 (p ^ f) K))}
  {e₀ : projImage (slPi π 3 (p ^ f) K)}

theorem CentConfig.isMonoAct_of_diagTau (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hc : CentConfig π p f K α e₀) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (he₀ : (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagTau hτ)) (x : ι) :
    IsMonoAct π p f K (α x) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  rcases hc.dich x with ⟨y, -, hyx⟩ | ⟨f₀, hf, σ, hσ, g, -, hgx⟩
  · obtain ⟨c, hc'⟩ := exists_conj_eq_scalar_mul hyx (hc.fix x) he₀
    obtain ⟨a, b, c', k, hk, rfl⟩ := monomial_of_conj_diagTau hτ hτ1 hc'
    exact Or.inl ⟨a, b, c', k, hk, hyx⟩
  · obtain ⟨c, hc'⟩ := exists_frob_conj_eq_scalar_mul hgx (hc.fix x)
      (diagTau_mem_slPi hπ hq' hτ) he₀
    rw [frobGL_diagTau σ hτ (fieldAut_apply_eq hq hf hσ hτ)] at hc'
    obtain ⟨a, b, c', k, hk, rfl⟩ := monomial_of_conj_diagTau hτ hτ1 hc'
    exact Or.inr ⟨σ, a, b, c', k, hk, hgx⟩

theorem CentConfig.torus_fixed (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hc : CentConfig π p f K α e₀) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (he₀ : (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagTau hτ)) {n : ℕ}
    (hn : n ∣ qSubPi π (p ^ f)) (hn1 : 1 < n) (hn3 : ¬ 3 ∣ n) :
    ∀ x, ∀ w ∈ torusSub hK hn, α x w = w :=
  hc.hV _ (not_three_dvd_card_torusSub hK hn hn1 hn3) fun x =>
    (hc.isMonoAct_of_diagTau hK hq hτ hτ1 he₀ x).mapsTo_torusSub hK hn

theorem torus_elt_mem (hK : PiField π p f K) {n : ℕ} (hn : n ∣ qSubPi π (p ^ f)) {ρ : Kˣ}
    (hρ : ρ ∈ rootsOfUnity n K) :
    ∃ w ∈ torusSub hK hn, (w : ProjGenLinGroup (Fin 3) K) = pmk (diagUnits ρ 1 ρ⁻¹) :=
  ⟨torusHomM hK hn (⟨ρ, hρ⟩, 1), ⟨_, rfl⟩, by rw [coe_torusHomM]; simp⟩

theorem CentConfig.diag_of_typeOne (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hc : CentConfig π p f K α e₀) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (he₀ : (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagTau hτ))
    (hpgl : ∀ x, IsPGLAct π p f K (α x)) {n : ℕ} (hn : n ∣ qSubPi π (p ^ f)) (hn1 : 1 < n)
    (hn3 : ¬ 3 ∣ n) (x : ι) :
    ∃ y ∈ glPi π 3 (p ^ f) K, (∃ a b c : Kˣ, y = diagUnits a b c) ∧
      ∀ m, (α x m : ProjGenLinGroup (Fin 3) K) = pmk y * m * (pmk y)⁻¹ := by
  obtain ⟨ρ, hρ, hρo⟩ := exists_orderOf_eq hK (by omega) hn
  have hρ3 := pow_three_ne_one_of_orderOf hρo hn1 hn3
  obtain ⟨y, hy, hyx⟩ := hpgl x
  obtain ⟨c, hc'⟩ := exists_conj_eq_scalar_mul hyx (hc.fix x) he₀
  obtain ⟨a, b, c', k, hk, rfl⟩ := monomial_of_conj_diagTau hτ hτ1 hc'
  obtain ⟨w, hw, hwρ⟩ := torus_elt_mem hK hn hρ
  have hfix := congrArg Subtype.val (hc.torus_fixed hK hq hτ hτ1 he₀ hn hn1 hn3 x w hw)
  rw [hyx, hwρ, ← map_inv, ← map_mul, ← map_mul] at hfix
  obtain ⟨-, hk0 | h3⟩ := mk_conj_torus_eq hk hfix
  · subst hk0
    exact ⟨_, hy, ⟨a, b, c', by rw [pow_zero, mul_one]⟩, hyx⟩
  · exact absurd h3 hρ3

theorem CentConfig.false_of_field_typeOne (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (h8 : ¬ (π = false ∧ p ^ f = 8)) (hc : CentConfig π p f K α e₀) {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) (he₀ : (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (diagTau hτ)) (x : ι)
    (hx : IsFieldAct π p f K (α x)) : False := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨f₀, hf, σ, hσ, g, -, hgx⟩ := hx
  have hp := hK.prime
  have hf₀ : 1 ≤ f₀ := by have := hK.one_le; omega
  have hq₀3 : p ^ f = (p ^ f₀) ^ 3 := by rw [← pow_mul, mul_comm, ← hf]
  have hq₀ : ModThree π (p ^ f₀) := modThree_of_cube (hq₀3 ▸ hq)
  have hq₀2 : 2 ≤ p ^ f₀ := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
  obtain ⟨n, hn1, hndvd, hn3, hns1, hns2⟩ : ∃ n, 1 < n ∧ n ∣ qSubPi π (p ^ f) ∧ ¬ 3 ∣ n ∧
      ¬ n ∣ piCard π (p ^ f₀) - 1 ∧ ¬ n ∣ piCard π (p ^ f₀) ^ 2 - 1 := by
    cases π
    · change p ^ f₀ % 3 = 2 at hq₀
      have h2 : 2 < p ^ f₀ := by
        rcases Nat.lt_or_ge 2 (p ^ f₀) with h | h
        · exact h
        · exfalso
          apply h8
          refine ⟨rfl, ?_⟩
          rw [hq₀3, show p ^ f₀ = 2 by omega]
          norm_num
      obtain ⟨n, hn1, hnd, hn3, h1, h2⟩ := exists_field_divisor_minus hq₀ h2
      refine ⟨n, hn1, ?_, hn3, h1, ?_⟩
      · change n ∣ p ^ f + 1
        rwa [hq₀3]
      · change ¬ n ∣ ((p ^ f₀) ^ 2) ^ 2 - 1
        rwa [← pow_mul]
    · change p ^ f₀ % 3 = 1 at hq₀
      obtain ⟨n, hn1, hnd, hn3, h1, h2⟩ := exists_field_divisor_plus hq₀ hq₀2
      refine ⟨n, hn1, ?_, hn3, h1, h2⟩
      change n ∣ p ^ f - 1
      rwa [hq₀3]
  obtain ⟨ρ, hρ, hρo⟩ := exists_orderOf_eq hK (by omega) hndvd
  obtain ⟨c, hc'⟩ := exists_frob_conj_eq_scalar_mul hgx (hc.fix x)
    (diagTau_mem_slPi hπ hq' hτ) he₀
  rw [frobGL_diagTau σ hτ (fieldAut_apply_eq hq hf hσ hτ)] at hc'
  obtain ⟨a, b, c', k, hk, rfl⟩ := monomial_of_conj_diagTau hτ hτ1 hc'
  have hs : diagUnits ρ 1 ρ⁻¹ ∈ slPi π 3 (p ^ f) K := by
    have := torusHom_mem_slPi hK (rootsOfUnity_le_of_dvd hndvd hρ) (one_mem _)
    rwa [show torusHom (ρ, (1 : Kˣ)) = diagUnits ρ 1 ρ⁻¹ by
      rw [show torusHom (ρ, (1 : Kˣ)) = diagUnits ρ 1 (ρ * 1)⁻¹ from rfl, mul_one]] at this
  have hw : projOf _ ⟨diagUnits ρ 1 ρ⁻¹, hs⟩ ∈ torusSub hK hndvd :=
    mem_torusSub hK hndvd hρ (one_mem _) (by rw [coe_projOf, mul_one])
  have hfix := congrArg Subtype.val (hc.torus_fixed hK hq hτ hτ1 he₀ hndvd hn1 hn3 x _ hw)
  rw [hgx, coe_projOf, frobGL_diagUnits, map_one, map_inv] at hfix
  obtain ⟨hσρ, -⟩ := mk_conj_torus_eq hk hfix
  have hσρ' : σ (ρ : K) = ρ := congrArg Units.val hσρ
  have hpos : 1 ≤ piCard π (p ^ f₀) := by
    cases π
    · exact Nat.one_le_pow _ _ (by omega)
    · change 1 ≤ p ^ f₀
      omega
  rcases hσ with hσ | hσ
  · rw [hσ] at hσρ'
    exact hns1 (hρo ▸ orderOf_dvd_of_pow_eq_self hpos hσρ')
  · rw [hσ] at hσρ'
    exact hns2 (hρo ▸ orderOf_dvd_of_pow_eq_self (Nat.one_le_pow _ _ (by omega)) hσρ')

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
