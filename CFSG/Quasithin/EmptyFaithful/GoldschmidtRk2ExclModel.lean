module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclCov
public import CFSG.Quasithin.EmptyFaithful.S151S2

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Model

variable {G : Type} [Group G] [Finite G]

@[expose] def RkModel (L : Subgroup G) : Prop :=
  ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (ρ : ↥L →* Y) (n : ℕ), 2 ≤ n ∧
    (IsPSL 3 2 n Y ∨ IsPSp4 2 n Y ∨ IsG2 2 n Y) ∧ Function.Surjective ρ ∧
    CFSG.Open.pCore 2 ↥L ≤ ρ.ker ∧ (∀ x ∈ ρ.ker, ∀ g : ↥L, ⁅x, g⁆ ∈ CFSG.Open.pCore 2 ↥L) ∧
    ∀ (U : Subgroup Y) (P : Fin 2 → Subgroup Y), Rank2Pkg Y U P → ∀ j : Fin 2,
      ∀ x ∈ lev ρ (P j), ρ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1

theorem rkModel_quot (L : Subgroup G) {n : ℕ} (hn : 2 ≤ n)
    (hY : IsPSL 3 2 n (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSp4 2 n (↥L ⧸ CFSG.pCore 2 ↥L) ∨
      IsG2 2 n (↥L ⧸ CFSG.pCore 2 ↥L)) : RkModel L := by
  have hnorm : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  have hN : (CFSG.Open.pCore 2 ↥L).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker = CFSG.Open.pCore 2 ↥L := by
    rw [QuotientGroup.ker_mk']
  refine ⟨↥L ⧸ CFSG.pCore 2 ↥L, inferInstance, inferInstance, QuotientGroup.mk' (CFSG.pCore 2 ↥L),
    n, hn, hY, QuotientGroup.mk'_surjective _, hker.ge, fun x hx g => ?_, ?_⟩
  · rw [hker] at hx
    have h1 : ⁅x, g⁆ = x * (g * x⁻¹ * g⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [h1]
    exact mul_mem hx (hN.conj_mem x⁻¹ ((CFSG.Open.pCore 2 ↥L).inv_mem hx) g)
  · intro U P _ j x hx hρx
    have hxk : x ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff x).1 hρx
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨x, hxk⟩
    exact ⟨k, congrArg Subtype.val hk⟩

theorem rkModel_cover (L : Subgroup G) {n : ℕ} (hn : 2 ≤ n)
    (hY : IsPSL 3 2 n ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) :
    RkModel L := by
  have hnorm : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  set Y₀ := ↥L ⧸ CFSG.pCore 2 ↥L with hY₀
  set π₀ : ↥L →* Y₀ := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ₀
  set π₁ : Y₀ →* Y₀ ⧸ Subgroup.center Y₀ := QuotientGroup.mk' (Subgroup.center Y₀) with hπ₁
  have hπ₀s : Function.Surjective π₀ := QuotientGroup.mk'_surjective _
  have hπ₁s : Function.Surjective π₁ := QuotientGroup.mk'_surjective _
  have hker₀ : π₀.ker = CFSG.Open.pCore 2 ↥L := by
    rw [hπ₀, QuotientGroup.ker_mk']
  let ρ : ↥L →* Y₀ ⧸ Subgroup.center Y₀ := π₁.comp π₀
  have hρs : Function.Surjective ρ := hπ₁s.comp hπ₀s
  have hq_le : CFSG.Open.pCore 2 ↥L ≤ ρ.ker := by
    intro x hx
    have h1 : π₀ x = 1 := MonoidHom.mem_ker.1 (hker₀.ge hx)
    show π₁ (π₀ x) = 1
    rw [h1, map_one]
  have hcent : ∀ x ∈ ρ.ker, ∀ g : ↥L, ⁅x, g⁆ ∈ CFSG.Open.pCore 2 ↥L := by
    intro x hx g
    have h1 : π₀ x ∈ Subgroup.center Y₀ := (QuotientGroup.eq_one_iff _).1 hx
    have h2 : π₀ ⁅x, g⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.1 h1 (π₀ g)).symm
    exact hker₀.le (MonoidHom.mem_ker.2 h2)
  refine ⟨_, inferInstance, inferInstance, ρ, n, hn, Or.inl hY, hρs, hq_le, hcent, ?_⟩
  intro U P hP j
  obtain ⟨K, hF, hFin, hCh, m, hK, hm, g, hg, hkerg⟩ := hP.levi j
  exact kerTwo_of_cover hρs hq_le hcent (cyclic_odd_sylow_of_levi hm hK g hg hkerg)

theorem rkModel (L : Subgroup G) (hB : ListB15120' L) : RkModel L := by
  rcases hB with (⟨n, hn, hY⟩ | ⟨n, hn, hY⟩ | ⟨n, hn, hY⟩) | ⟨n, hn, hY⟩
  · exact rkModel_quot L hn (Or.inl hY)
  · exact rkModel_quot L hn (Or.inr (Or.inl hY))
  · exact rkModel_quot L hn (Or.inr (Or.inr hY))
  · exact rkModel_cover L hn hY

end Model

end CFSG.Quasithin.Rk2
