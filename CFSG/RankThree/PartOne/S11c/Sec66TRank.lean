module

public import CFSG.RankThree.PartOne.S11c.Sec66Plane
public import CFSG.RankThree.PartOne.S11c.Sec66TDefs
public import CFSG.RankThree.PartOne.S11c.Sec66TLift

public section

namespace CFSG.RankThree.PartOne.Sec66T

open Subgroup CFSG CFSG.Assembly

variable {H : Type} [Group H] [Finite H]

theorem localRankLeTwo_of_localRank {p : ℕ}
    (he : CFSG.Assembly.RankThreeEven.localRank p H ≤ 3) (hp : p.Prime)
    {J : Subgroup H} (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) {c : H}
    (hcC : c ∈ Subgroup.centralizer (J : Set H)) (hc1 : c ≠ 1) (hcp : c ^ p = 1) :
    LocalRankLeTwo p (↥J ⧸ Subgroup.center ↥J) := by
  intro R hR hRcard U hU1 hU2 hRU
  have hcop : Nat.Coprime (Nat.card (Subgroup.center J)) (p ^ 3) :=
    Nat.Coprime.pow_right 3 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hZ).symm
  obtain ⟨R', hR'map, hR'card, hR'inj⟩ :=
    exists_lift_of_central_coprime (Subgroup.center J) hcop R hRcard
  obtain ⟨S, hS2, hS1, hSN⟩ := exists_invariant_two_subgroup (Subgroup.center J)
    (fun z hz => hz) U hU2 hU1
  let π : J →* J ⧸ Subgroup.center J := QuotientGroup.mk' (Subgroup.center J)
  have hπR : ∀ x ∈ R', π x ∈ R := by
    intro x hx
    rw [← hR'map]
    exact ⟨x, hx, rfl⟩
  let A : Subgroup H := R'.map J.subtype
  let S' : Subgroup H := S.map J.subtype
  have hAJ : ∀ x ∈ A, x ∈ J := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have h1 := hR.is_comm.comm (⟨π x, hπR x hx⟩ : R) ⟨π y, hπR y hy⟩
    have h2 : π (x * y) = π (y * x) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val h1
    have h3 := hR'inj (x * y) (R'.mul_mem hx hy) (y * x) (R'.mul_mem hy hx) h2
    exact congrArg Subtype.val h3
  have hAp : ∀ x ∈ A, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : (⟨π x, hπR x hx⟩ : R) ^ p = 1 := by
      have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p R)
        ⟨π x, hπR x hx⟩
      exact this
    have h2 : π (x ^ p) = π 1 := by
      rw [map_pow, map_one]
      exact congrArg Subtype.val h1
    have h3 := hR'inj (x ^ p) (R'.pow_mem hx p) 1 R'.one_mem h2
    change ((x ^ p : J) : H) = 1
    rw [h3]
    rfl
  have hAcard : Nat.card A = p ^ 3 := by
    rw [Subgroup.card_map_of_injective J.subtype_injective, hR'card]
  have hSJ : S' ≤ J := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hS'1 : S' ≠ ⊥ := by
    intro h
    apply hS1
    have := (Subgroup.map_eq_bot_iff _).mp h
    rw [Subgroup.ker_subtype] at this
    exact eq_bot_iff.mpr this
  have hS'2 : IsPGroup 2 S' := hS2.map J.subtype
  have hnormJ : ∀ x ∈ R', ∀ s ∈ S, x * s * x⁻¹ ∈ S := fun x hx s hs =>
    hSN x (hRU (hπR x hx)) s hs
  have hAS : A ≤ Subgroup.normalizer (S' : Set H) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨x * s * x⁻¹, hnormJ x hx s hs, rfl⟩
    · rintro ⟨s, hs, hsh⟩
      refine ⟨x⁻¹ * s * x, ?_, ?_⟩
      · have := hnormJ x⁻¹ (R'.inv_mem hx) s hs
        simpa using this
      · have h1 : J.subtype (x⁻¹ * s * x) = (x : H)⁻¹ * (s : H) * (x : H) := by simp
        have hs' : (s : H) = (x : H) * h * (x : H)⁻¹ := hsh
        rw [h1, hs']
        group
  have hcJ : c ∉ A := by
    intro hcA
    exact hc1 (PlaneInner.eq_one_of_pow_eq_one hp hZ (hAJ c hcA) hcC hcp)
  have htc : ∀ x ∈ A, x * c = c * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp hcC) x (hAJ x hx)
  have htS : c ∈ Subgroup.normalizer (S' : Set H) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hSJ) hcC)
  exact PlaneInner.false_of_commuting_extension_of_localRank he hp hAc hAp hAcard hS'1 hS'2 hAS
    hcJ hcp htc htS

theorem localRankLeTwo_of_evenRank (he : evenRank H ≤ 3) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {J : Subgroup H} (hZ : ¬ p ∣ Nat.card (Subgroup.center J)) {c : H}
    (hcC : c ∈ Subgroup.centralizer (J : Set H)) (hc1 : c ≠ 1) (hcp : c ^ p = 1) :
    LocalRankLeTwo p (↥J ⧸ Subgroup.center ↥J) :=
  localRankLeTwo_of_localRank ((CFSG.RankThree.OddKernel.localRank_le_evenRank hp hp2).trans he) hp
    hZ hcC hc1 hcp

end CFSG.RankThree.PartOne.Sec66T
