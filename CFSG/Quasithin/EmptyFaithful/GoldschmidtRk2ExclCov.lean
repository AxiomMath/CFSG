module

public import CFSG.Quasithin.Background.KnownMultTypes
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclLev

public section

namespace CFSG.Quasithin.Rk2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Sylow

theorem cyclic_odd_sylow_of_levi {J : Type} [Group J] [Finite J] {K : Type} [Field K] [Finite K]
    [CharP K 2] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (g : J →* Matrix.SpecialLinearGroup (Fin 2) K) (hg : Function.Surjective g)
    (hker : IsPGroup 2 g.ker) :
    ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ [Fact r.Prime] (Q : Sylow r J), IsCyclic (Q : Subgroup J) := by
  intro r hr hr2 hfact Q
  let e : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := K)
  let h : J →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K := e.symm.toMonoidHom.comp g
  have hh : Function.Surjective h := e.symm.surjective.comp hg
  let R : Sylow r (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := Sylow.mapSurjective hh Q
  have hRc : IsCyclic (R : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) :=
    psl_two_sylow_isCyclic_even hn hK hr2 R
  have hRe : (R : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) =
      (Q : Subgroup J).map h := Sylow.coe_mapSurjective hh Q
  have hinj : Function.Injective (h.subgroupMap (Q : Subgroup J)) := by
    intro x y hxy
    have h1 : h x.1 = h y.1 := congrArg Subtype.val hxy
    have h2 : g (x.1 * y.1⁻¹) = 1 := by
      have : e.symm (g x.1) = e.symm (g y.1) := h1
      have h3 := e.symm.injective this
      rw [map_mul, map_inv, h3, mul_inv_cancel]
    have h4 : x.1 * y.1⁻¹ ∈ g.ker := h2
    have h5 : x.1 * y.1⁻¹ ∈ (Q : Subgroup J) := mul_mem x.2 (inv_mem y.2)
    obtain ⟨a, ha⟩ := Q.isPGroup' ⟨_, h5⟩
    obtain ⟨b, hb⟩ := hker ⟨_, h4⟩
    have ha' : (x.1 * y.1⁻¹) ^ r ^ a = 1 := congrArg Subtype.val ha
    have hb' : (x.1 * y.1⁻¹) ^ 2 ^ b = 1 := congrArg Subtype.val hb
    have hcop : Nat.Coprime (r ^ a) (2 ^ b) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes hr Nat.prime_two).2 hr2)
    have hd1 : orderOf (x.1 * y.1⁻¹) ∣ r ^ a := orderOf_dvd_of_pow_eq_one ha'
    have hd2 : orderOf (x.1 * y.1⁻¹) ∣ 2 ^ b := orderOf_dvd_of_pow_eq_one hb'
    have hone : orderOf (x.1 * y.1⁻¹) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    have hxy' : x.1 * y.1⁻¹ = 1 := orderOf_eq_one_iff.1 hone
    exact Subtype.ext (mul_inv_eq_one.1 hxy')
  have hRc' : IsCyclic ↥((Q : Subgroup J).map h) := by
    rw [← hRe]
    exact hRc
  exact isCyclic_of_injective (h.subgroupMap (Q : Subgroup J)) hinj

end Sylow

section Cover

variable {Γ Y : Type} [Group Γ] [Finite Γ] [Group Y] [Finite Y]

theorem kerTwo_of_cover {ρ : Γ →* Y} (hρ : Function.Surjective ρ) {B : Subgroup Y}
    (hQ : CFSG.Open.pCore 2 Γ ≤ ρ.ker)
    (hcent : ∀ x ∈ ρ.ker, ∀ g : Γ, ⁅x, g⁆ ∈ CFSG.Open.pCore 2 Γ)
    (hcyc : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ [Fact r.Prime] (Q : Sylow r ↥(perfectCore B)),
      IsCyclic (Q : Subgroup ↥(perfectCore B))) :
    ∀ x ∈ lev ρ B, ρ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx hρx
  have hQn : (CFSG.Open.pCore 2 Γ).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hQ2 : IsPGroup 2 (CFSG.Open.pCore 2 Γ) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  set A : Subgroup Γ := lev ρ B with hA
  let Q0 : Subgroup ↥A := (CFSG.Open.pCore 2 Γ).subgroupOf A
  have hQ0n : Q0.Normal := Subgroup.normal_subgroupOf
  let θ : ↥A →* ↥(perfectCore B) := levHom hρ B
  have hQ0 : Q0 ≤ θ.ker := fun q hq =>
    (mem_ker_levHom hρ B).2 (MonoidHom.mem_ker.1 (hQ hq))
  let φ : ↥A ⧸ Q0 →* ↥(perfectCore B) := QuotientGroup.lift Q0 θ hQ0
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨a, ha⟩ := levHom_surjective hρ B y
    exact ⟨QuotientGroup.mk a, ha⟩
  have hperfA : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.2 (lev_perfect ρ B)
  have : Group.IsPerfect (↥A ⧸ Q0) := inferInstance
  have hcentral : φ.ker ≤ Subgroup.center (↥A ⧸ Q0) := by
    intro z hz
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective z
    have ha : θ a = 1 := hz
    have hρa : ρ a.1 = 1 := (mem_ker_levHom hρ B).1 ha
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have h2 : (⁅a, b⁆ : ↥A) ∈ Q0 := hcent a.1 (MonoidHom.mem_ker.2 hρa) b.1
    have h3 : (QuotientGroup.mk' Q0) ⁅a, b⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h2
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3.symm
  have hker2 := isPGroup_two_ker_of_cyclic_odd_sylow φ hφ hcentral hcyc
  let x' : ↥A := ⟨x, hx⟩
  have hx' : (QuotientGroup.mk x' : ↥A ⧸ Q0) ∈ φ.ker :=
    (mem_ker_levHom hρ B).2 hρx
  obtain ⟨k, hk⟩ := hker2 ⟨_, hx'⟩
  have h1 : (QuotientGroup.mk x' : ↥A ⧸ Q0) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  have h2 : (x ^ 2 ^ k) ∈ CFSG.Open.pCore 2 Γ := h1
  obtain ⟨m, hm⟩ := hQ2 ⟨_, h2⟩
  refine ⟨k + m, ?_⟩
  rw [pow_add, pow_mul]
  exact congrArg Subtype.val hm

end Cover

end CFSG.Quasithin.Rk2
