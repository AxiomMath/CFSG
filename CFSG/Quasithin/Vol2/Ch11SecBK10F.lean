module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Vol2.Ch11SecBK10C

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

namespace BK10

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_inf_of_subnormal {T H L : Subgroup G} (h : IsSubnormal L H)
    (hT : IsSylowTwoOf T H) : IsSylowTwoOf (T ⊓ L) L := by
  induction h with
  | refl K => rwa [inf_eq_left.mpr hT.1]
  | @step L M K hLM hN _ ih =>
    have h1 := ih hT
    have hnorm : M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hN
    have h2 := CFSG.Quasithin.A4.isSylowTwoOf_inf_normal h1 hLM hnorm
    rwa [inf_assoc, inf_eq_right.mpr hLM] at h2

omit [Finite G] in
theorem card_xCls_dvd [Finite G] (J : Subgroup G) : Nat.card (XCls J) ∣ Nat.card J :=
  (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)

theorem exists_isCoprimePrimeAut {J A : Subgroup G}
    (hJq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J))
    (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hcop : Nat.Coprime (Nat.card A) (2 * Nat.card J))
    (hnot : ¬ ⁅J, A⁆ ≤ pCoreOf 2 J) :
    ∃ a, ∃ ha : a ∈ A, IsCoprimePrimeAut (rhoX J ⟨a, hAJ ha⟩) := by
  by_contra hno
  apply hnot
  have htriv : ∀ a (ha : a ∈ A), rhoX J ⟨a, hAJ ha⟩ = 1 := by
    intro a ha
    by_contra hne
    set β₀ := rhoX J ⟨a, hAJ ha⟩ with hβ₀
    have hfin : orderOf β₀ ≠ 0 := (isOfFinOrder_of_finite β₀).orderOf_pos.ne'
    have h1 : orderOf β₀ ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
    obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd h1
    have hord : orderOf (β₀ ^ (orderOf β₀ / r)) = r := orderOf_pow_orderOf_div hfin hrm
    apply hno
    refine ⟨a ^ (orderOf β₀ / r), A.pow_mem ha _, ?_⟩
    have heq : rhoX J ⟨a ^ (orderOf β₀ / r), hAJ (A.pow_mem ha _)⟩ = β₀ ^ (orderOf β₀ / r) := by
      rw [hβ₀, ← map_pow]
      try rfl
    rw [heq]
    refine ⟨r, hr, by
      have := pow_orderOf_eq_one (β₀ ^ (orderOf β₀ / r))
      rwa [hord] at this, fun h => ?_, fun hrX => ?_⟩
    · rw [h, orderOf_one] at hord
      exact hr.one_lt.ne' hord.symm
    · have hrA : r ∣ Nat.card A := by
        have h2 : orderOf β₀ ∣ orderOf (⟨a, hAJ ha⟩ : ↥(Subgroup.normalizer (J : Set G))) :=
          orderOf_map_dvd _ _
        rw [Subgroup.orderOf_mk] at h2
        exact hrm.trans (h2.trans (Subgroup.orderOf_dvd_natCard A ha))
      have hrJ : r ∣ Nat.card J := hrX.trans (card_xCls_dvd J)
      have h3 := Nat.Coprime.coprime_dvd_left hrA hcop
      have h4 : Nat.Coprime r (Nat.card J) := Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) h3
      exact hr.one_lt.ne' (h4.eq_one_of_dvd hrJ)
  rw [Subgroup.commutator_le]
  intro j hj a ha
  have : Group.IsPerfect (↥J ⧸ CFSG.pCore 2 ↥J) := hJq.1
  have h1 := eq_one_of_quotAut_center (htriv a ha)
  have h2 := congrArg (fun φ : MulAut (↥J ⧸ CFSG.pCore 2 ↥J) =>
    φ ((⟨j, hj⟩ : ↥J) : ↥J ⧸ CFSG.pCore 2 ↥J)) h1
  simp only [MulAut.one_apply] at h2
  change ((J.normalizerMonoidHom ⟨a, hAJ ha⟩ ⟨j, hj⟩ : ↥J) : ↥J ⧸ CFSG.pCore 2 ↥J) =
    ((⟨j, hj⟩ : ↥J) : ↥J ⧸ CFSG.pCore 2 ↥J) at h2
  have h3 := QuotientGroup.eq.mp h2
  set x := (J.normalizerMonoidHom ⟨a, hAJ ha⟩ ⟨j, hj⟩)⁻¹ * ⟨j, hj⟩ with hx
  have h4 : (⟨j, hj⟩ : ↥J) * x * (⟨j, hj⟩ : ↥J)⁻¹ ∈ CFSG.pCore 2 ↥J :=
    (CFSG.pCore_normal (p := 2) (G := ↥J)).conj_mem x h3 _
  have h5 : (((⟨j, hj⟩ : ↥J) * x * (⟨j, hj⟩ : ↥J)⁻¹ : ↥J) : G) = ⁅j, a⁆ := by
    rw [hx]
    change j * ((a * j * a⁻¹)⁻¹ * j) * j⁻¹ = ⁅j, a⁆
    rw [commutatorElement_def]
    group
  rw [← h5]
  have h6 : (⟨j, hj⟩ : ↥J) * x * (⟨j, hj⟩ : ↥J)⁻¹ ∈ CFSG.Open.pCore 2 ↥J := by
    exact h4
  exact ⟨_, h6, rfl⟩

end BK10

end CFSG.Quasithin.Vol2.Ch11.SecD
