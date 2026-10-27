module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OLinesCent

public section

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Lines

variable (K : Type) [Field K] (p : ℕ)

@[expose] def invSq : Kˣ →* Kˣ where
  toFun a := (a * a)⁻¹
  map_one' := by simp
  map_mul' a b := by
    show (a * b * (a * b))⁻¹ = (a * a)⁻¹ * (b * b)⁻¹
    rw [mul_mul_mul_comm, mul_inv]

@[expose] def lineDiag : Kˣ →* Kˣ × Kˣ := (MonoidHom.id Kˣ).prod (MonoidHom.id Kˣ)

@[expose] def lineSnd : Kˣ →* Kˣ × Kˣ := (MonoidHom.id Kˣ).prod (invSq K)

@[expose] def lineFst : Kˣ →* Kˣ × Kˣ := (invSq K).prod (MonoidHom.id Kˣ)

@[expose] def lineHom (ℓ : Kˣ →* Kˣ × Kˣ) : rootsOfUnity p K →* projectiveSL 3 K :=
  ((proj 3 K).comp (diagHom.comp ℓ)).comp (rootsOfUnity p K).subtype

@[expose] def lineP (ℓ : Kˣ →* Kˣ × Kˣ) : Subgroup (projectiveSL 3 K) := (lineHom K p ℓ).range

@[expose] def lineSet : Set (Subgroup (projectiveSL 3 K)) :=
  {U | U ≤ torusP K p ∧ Nat.card U = p ∧
    Subgroup.centralizer (U : Set (projectiveSL 3 K)) ≠
      Subgroup.centralizer (torusP K p : Set (projectiveSL 3 K))}

variable {K p}

theorem mem_lineP {ℓ : Kˣ →* Kˣ × Kˣ} {y : projectiveSL 3 K} :
    y ∈ lineP K p ℓ ↔ ∃ a : Kˣ, a ^ p = 1 ∧ proj 3 K (diagHom (ℓ a)) = y := by
  rw [lineP, MonoidHom.mem_range]
  constructor
  · rintro ⟨⟨a, ha⟩, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem pow_eq_one_of_pow_eq_one (ℓ : Kˣ →* Kˣ × Kˣ) {a : Kˣ} (ha : a ^ p = 1) :
    (ℓ a).1 ^ p = 1 ∧ (ℓ a).2 ^ p = 1 := by
  have h : (ℓ a) ^ p = 1 := by rw [← map_pow, ha, map_one]
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem lineP_le_torusP (ℓ : Kˣ →* Kˣ × Kˣ) : lineP K p ℓ ≤ torusP K p := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := mem_lineP.1 hy
  obtain ⟨h1, h2⟩ := pow_eq_one_of_pow_eq_one ℓ ha
  exact mem_torusP.2 ⟨(ℓ a).1, (ℓ a).2, h1, h2, rfl⟩

theorem card_lineP [Finite K] [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1)
    {ℓ : Kˣ →* Kˣ × Kˣ} (hℓ : Function.Injective ℓ) : Nat.card (lineP K p ℓ) = p := by
  have hinj : Function.Injective (lineHom K p ℓ) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, ha⟩ h
    obtain ⟨h1, h2⟩ := pow_eq_one_of_pow_eq_one ℓ ha
    have h3 : proj 3 K (diagHom ((ℓ a).1, (ℓ a).2)) = 1 := h
    obtain ⟨h4, h5⟩ := eq_one_of_proj_diagHom_eq_one (by omega) h1 h2 h3
    exact Subtype.ext (hℓ (Prod.ext h4 h5 |>.trans (map_one ℓ).symm))
  rw [lineP, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
  exact card_rootsOfUnity_eq hpq

theorem proj_trv_mem_centralizer_lineP_iff [hp : Fact p.Prime] (hp3 : p ≠ 3)
    (ℓ : Kˣ →* Kˣ × Kˣ) (i j : Fin 3) (hij : i ≠ j) :
    proj 3 K (trv i j hij) ∈ Subgroup.centralizer (lineP K p ℓ : Set (projectiveSL 3 K)) ↔
      ∀ a : Kˣ, a ^ p = 1 → dv (ℓ a) i = dv (ℓ a) j := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h a ha
    obtain ⟨h1, h2⟩ := pow_eq_one_of_pow_eq_one ℓ ha
    exact (proj_trv_commute_iff hp3 h1 h2 i j hij).1 (h _ (mem_lineP.2 ⟨a, ha, rfl⟩)).symm
  · intro h y hy
    obtain ⟨a, ha, rfl⟩ := mem_lineP.1 hy
    obtain ⟨h1, h2⟩ := pow_eq_one_of_pow_eq_one ℓ ha
    exact ((proj_trv_commute_iff hp3 h1 h2 i j hij).2 (h a ha)).symm

theorem lineP_mem_lineSet [Finite K] [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1) {ℓ : Kˣ →* Kˣ × Kˣ} (hℓ : Function.Injective ℓ) (i j : Fin 3)
    (hij : i ≠ j) (hdv : ∀ a : Kˣ, dv (ℓ a) i = dv (ℓ a) j) : lineP K p ℓ ∈ lineSet K p := by
  refine ⟨lineP_le_torusP ℓ, card_lineP hp5 hpq hℓ, fun h => ?_⟩
  apply proj_trv_not_mem_centralizer hp5 hpq i j hij
  rw [← h]
  exact (proj_trv_mem_centralizer_lineP_iff (by omega) ℓ i j hij).2 fun a _ => hdv a

theorem lineP_ne [hp : Fact p.Prime] (hp3 : p ≠ 3) {ℓ ℓ' : Kˣ →* Kˣ × Kˣ} (i j : Fin 3)
    (hij : i ≠ j) (hdv : ∀ a : Kˣ, dv (ℓ a) i = dv (ℓ a) j) {a : Kˣ} (ha : a ^ p = 1)
    (hne : dv (ℓ' a) i ≠ dv (ℓ' a) j) : lineP K p ℓ ≠ lineP K p ℓ' := by
  intro h
  have h1 := (proj_trv_mem_centralizer_lineP_iff (K := K) (p := p) hp3 ℓ i j hij).2
    fun a _ => hdv a
  rw [h] at h1
  exact hne ((proj_trv_mem_centralizer_lineP_iff hp3 ℓ' i j hij).1 h1 a ha)

end Lines

end CFSG.Quasithin.H13.NQCore.L3Odd
