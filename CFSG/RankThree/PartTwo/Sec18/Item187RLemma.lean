module

public import CFSG.RankThree.PartTwo.Sec18.Item187Min
import CFSG.RankThree.PartTwo.Sec18.SylowPlane

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem commutator_conj_eq_of_commute {y r z : G} (hyz : y * z = z * y) :
    ⁅y * r * y⁻¹, z⁆ = ⁅y * r, z⁆ := by
  have hconj : y⁻¹ * z * y = z := by rw [mul_assoc, ← hyz, inv_mul_cancel_left]
  rw [commutatorElement_def, commutatorElement_def]
  have e : y * r * y⁻¹ * z * (y * r * y⁻¹)⁻¹ * z⁻¹
      = y * r * (y⁻¹ * z * y) * r⁻¹ * y⁻¹ * z⁻¹ := by group
  rw [e, hconj]
  group

private theorem le_normalizer_commutator_self (A Z : Subgroup G) :
    A ≤ Subgroup.normalizer ((⁅A, Z⁆ : Subgroup G) : Set G) := by
  have key : ∀ g ∈ A, ∀ d ∈ ⁅A, Z⁆, g * d * g⁻¹ ∈ ⁅A, Z⁆ := by
    intro g hg
    have hle : ⁅A, Z⁆ ≤ (⁅A, Z⁆).comap (MulAut.conj g).toMonoidHom := by
      refine Subgroup.commutator_le.mpr fun a ha z hz => ?_
      rw [Subgroup.mem_comap]
      show g * ⁅a, z⁆ * g⁻¹ ∈ ⁅A, Z⁆
      have e : g * ⁅a, z⁆ * g⁻¹ = ⁅g * a, z⁆ * ⁅g, z⁆⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev, inv_inv]
        group
      rw [e]
      exact mul_mem (Subgroup.commutator_mem_commutator (mul_mem hg ha) hz)
        (inv_mem (Subgroup.commutator_mem_commutator hg hz))
    intro d hd
    exact hle hd
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · exact key g hg d
  · intro hd
    simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hd

private theorem exists_commute_mul_of_commutator_le {X Q : Subgroup G} {c : G}
    (hc3 : orderOf c = 3) (hX3 : ¬ 3 ∣ Nat.card X) (hQX : Q ≤ X)
    (hcQ : c ∈ Subgroup.normalizer (Q : Set G))
    (h : ⁅X, Subgroup.zpowers c⁆ ≤ Q) {x : G} (hx : x ∈ X) :
    ∃ q ∈ Q, c * (x * q) = x * q * c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : c * c * c = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hc3, pow_three'] at this
  obtain ⟨u, hu_def⟩ : ∃ u : G, u = x⁻¹ * c * x * c⁻¹ := ⟨_, rfl⟩
  have hu : u ∈ Q := by
    have hmem : ⁅x⁻¹, c⁆ ∈ Q :=
      h (Subgroup.commutator_mem_commutator (inv_mem hx) (Subgroup.mem_zpowers c))
    rwa [show ⁅x⁻¹, c⁆ = u by rw [hu_def, commutatorElement_def, inv_inv]] at hmem
  have hτ : ∀ r ∈ Q, c * r * c⁻¹ ∈ Q := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp hcQ r).mp hr
  have hτ' : ∀ r ∈ Q, c⁻¹ * r * c ∈ Q := fun r hr =>
    (Subgroup.mem_normalizer_iff''.mp hcQ r).mp hr
  let σ : Equiv.Perm Q :=
    { toFun := fun q => ⟨u * (c * (q : G) * c⁻¹), mul_mem hu (hτ _ q.2)⟩
      invFun := fun p => ⟨c⁻¹ * (u⁻¹ * (p : G)) * c, hτ' _ (mul_mem (inv_mem hu) p.2)⟩
      left_inv := fun q => Subtype.ext (by
        show c⁻¹ * (u⁻¹ * (u * (c * (q : G) * c⁻¹))) * c = q
        group)
      right_inv := fun p => Subtype.ext (by
        show u * (c * (c⁻¹ * (u⁻¹ * (p : G)) * c) * c⁻¹) = p
        group) }
  have hσ_apply : ∀ q : Q, ((σ q : Q) : G) = u * (c * (q : G) * c⁻¹) := fun q => rfl
  have hcube : ∀ q : G, u * (c * (u * (c * (u * (c * q * c⁻¹)) * c⁻¹)) * c⁻¹) = q := by
    intro q
    have e : u * (c * (u * (c * (u * (c * q * c⁻¹)) * c⁻¹)) * c⁻¹)
        = (x⁻¹ * (c * c * c) * x * (c * c * c)⁻¹) * ((c * c * c) * q * (c * c * c)⁻¹) := by
      rw [hu_def]
      group
    rw [e, hc]
    simp
  have hσ3p : ∀ p : Q, σ (σ (σ p)) = p := fun p => Subtype.ext (by
    rw [hσ_apply, hσ_apply, hσ_apply]
    exact hcube p)
  have hσ3 : σ ^ 3 = 1 := by
    ext p
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact congrArg Subtype.val (hσ3p p)
  haveI : Fintype Q := Fintype.ofFinite Q
  have hα : ¬ 3 ∣ Fintype.card Q := by
    rw [← Nat.card_eq_fintype_card]
    exact fun h3 => hX3 (h3.trans (Subgroup.card_dvd_of_le hQX))
  have hσ3' : σ ^ 3 ^ 1 = 1 := by simpa using hσ3
  obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1) hα hσ3'
  have hfix : u * (c * (a : G) * c⁻¹) = a := (hσ_apply a).symm.trans (congrArg Subtype.val ha)
  refine ⟨(a : G), a.2, ?_⟩
  calc c * (x * (a : G)) = x * (u * (c * (a : G) * c⁻¹)) * c := by rw [hu_def]; group
    _ = x * (a : G) * c := by rw [hfix]

theorem inf_centralizer_sup_eq_of_commutator_le {X Q : Subgroup G} {c : G}
    (hc3 : orderOf c = 3) (hX3 : ¬ 3 ∣ Nat.card X) (hQX : Q ≤ X)
    (hcQ : c ∈ Subgroup.normalizer (Q : Set G))
    (h : ⁅X, Subgroup.zpowers c⁆ ≤ Q) :
    (X ⊓ Subgroup.centralizer ({c} : Set G)) ⊔ Q = X := by
  apply le_antisymm (sup_le inf_le_left hQX)
  intro x hx
  obtain ⟨q, hq, hcq⟩ := exists_commute_mul_of_commutator_le hc3 hX3 hQX hcQ h hx
  have hC : x * q ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun m hm => by
      rw [Set.mem_singleton_iff.mp hm]
      exact hcq
  have hy : x * q ∈ X ⊓ Subgroup.centralizer ({c} : Set G) := ⟨mul_mem hx (hQX hq), hC⟩
  have key : x * q * q⁻¹ ∈ (X ⊓ Subgroup.centralizer ({c} : Set G)) ⊔ Q :=
    mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right (inv_mem hq))
  rwa [mul_inv_cancel_right] at key

variable {A M H : Subgroup G} {c : G}

theorem MinCex.not_commutator_le {X : Subgroup G} (hX : MinCex A M H c X)
    (hc3 : orderOf c = 3)
    (hQS : CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 (H ⊓ M))
    (hR : Subgroup.normalizer ((⁅CFSG.Open.pCoreOf 2 (H ⊓ M), Subgroup.zpowers c⁆ : Subgroup G) :
        Set G) ≤
      Subgroup.normalizer (inSubgroup perfectResidual H : Set G)) :
    ¬ ⁅X, Subgroup.zpowers c⁆ ≤ CFSG.Open.pCoreOf 2 X := by
  intro h
  have hcA : c ∈ A := (mem_and_commutator_mem_of_sec18H hX.sec18H).1
  have hcX : c ∈ Subgroup.normalizer (X : Set G) :=
    hX.le_normalizer (Subgroup.mem_sup_left hcA)
  have hcQ : c ∈ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X hcX
  have hQX : CFSG.Open.pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hXQ : X ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hX3 : ¬ 3 ∣ Nat.card X := fun h3 => by
    have hmem : (⟨3, Nat.prime_three⟩ : Nat.Primes) ∈ piCompl 3 :=
      hX.isPiSubgroup ⟨3, Nat.prime_three⟩ h3
    exact hmem rfl
  have hle1 : ⁅X, Subgroup.zpowers c⁆ ≤ ⁅CFSG.Open.pCoreOf 2 (H ⊓ M), Subgroup.zpowers c⁆ := by
    refine Subgroup.commutator_le.mpr fun x hx z hz => ?_
    obtain ⟨q, hq, hcq⟩ := exists_commute_mul_of_commutator_le hc3 hX3 hQX hcQ h hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hcommute : x * q * z = z * (x * q) := by
      rw [← hk]
      exact (Commute.zpow_right (show Commute (x * q) c from hcq.symm) k).eq
    have hkey : ⁅x * q * q⁻¹ * (x * q)⁻¹, z⁆ = ⁅x, z⁆ := by
      rw [commutator_conj_eq_of_commute hcommute, mul_inv_cancel_right]
    have hmemQ : x * q * q⁻¹ * (x * q)⁻¹ ∈ CFSG.Open.pCoreOf 2 X :=
      (Subgroup.mem_normalizer_iff.mp (hXQ (mul_mem hx (hQX hq))) q⁻¹).mp (inv_mem hq)
    rw [← hkey]
    exact Subgroup.commutator_mem_commutator (hQS hmemQ) hz
  have hle2 : ⁅CFSG.Open.pCoreOf 2 (H ⊓ M), Subgroup.zpowers c⁆ ≤ ⁅X, Subgroup.zpowers c⁆ :=
    Subgroup.commutator_mono hX.pCoreOf_le le_rfl
  have hEq : ⁅X, Subgroup.zpowers c⁆ = ⁅CFSG.Open.pCoreOf 2 (H ⊓ M), Subgroup.zpowers c⁆ :=
    le_antisymm hle1 hle2
  have hN : X ≤ Subgroup.normalizer
      ((⁅CFSG.Open.pCoreOf 2 (H ⊓ M), Subgroup.zpowers c⁆ : Subgroup G) : Set G) := by
    rw [← hEq]
    exact le_normalizer_commutator_self X (Subgroup.zpowers c)
  exact hX.not_le (hN.trans hR)

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
