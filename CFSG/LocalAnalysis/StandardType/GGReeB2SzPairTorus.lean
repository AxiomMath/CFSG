module

public import CFSG.LocalAnalysis.StandardType.GGReeB2SzPairDefs

public section

namespace CFSG.StandardType.ReeB2Fixed

open CFSG.SectionRank.LargeRee CFSG.LieType.Ree CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Quasithin.B45Sz

private theorem suzukiDElt_bridge (a : ℕ) (K : Type) [Field K]
    (l : Kˣ) :
    CFSG.LieType.Ree.suzukiDElt a K l = CFSG.SectionRank.LargeRee.suzukiDElt a l := by
  apply Subtype.ext
  apply Units.ext
  rfl

private theorem reeNa_mul_self
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] (m : ℕ) :
    reeNa K m * reeNa K m = 1 := by
  simpa only [reeNa] using relNrepHom_blockGen_mul_self (K := K) (a := m) (i := 0)

private theorem reeNa_conj_T0
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (u : Kˣ) :
    reeNa K m * reeTorusHom m hK fi_zero_mem_longSet u * (reeNa K m)⁻¹ =
      (reeTorusHom m hK fi_zero_mem_longSet u)⁻¹ := by
  apply Subtype.ext
  change (reeNa K m : adjointGroup ReeTag.F4.tag K) *
      (reeTorusHom m hK fi_zero_mem_longSet u : adjointGroup ReeTag.F4.tag K) *
      (reeNa K m : adjointGroup ReeTag.F4.tag K)⁻¹ =
    (reeTorusHom m hK fi_zero_mem_longSet u : adjointGroup ReeTag.F4.tag K)⁻¹
  exact (torus_reflections hK u).1

private theorem reeNa_conj_T1
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (u : Kˣ) :
    reeNa K m * reeTorusHom m hK fi_one_mem_longSet u * (reeNa K m)⁻¹ =
      reeTorusHom m hK fi_one_mem_longSet u * reeTorusHom m hK fi_zero_mem_longSet u := by
  apply Subtype.ext
  change (reeNa K m : adjointGroup ReeTag.F4.tag K) *
      (reeTorusHom m hK fi_one_mem_longSet u : adjointGroup ReeTag.F4.tag K) *
      (reeNa K m : adjointGroup ReeTag.F4.tag K)⁻¹ =
    (reeTorusHom m hK fi_one_mem_longSet u : adjointGroup ReeTag.F4.tag K) *
      (reeTorusHom m hK fi_zero_mem_longSet u : adjointGroup ReeTag.F4.tag K)
  exact (torus_reflections hK u).2.1

private theorem reeNb_conj_T1
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (u : Kˣ) :
    reeNb K m * reeTorusHom m hK fi_one_mem_longSet u * (reeNb K m)⁻¹ =
      (reeTorusHom m hK fi_one_mem_longSet u)⁻¹ := by
  apply Subtype.ext
  change (reeNb K m : adjointGroup ReeTag.F4.tag K) *
      (reeTorusHom m hK fi_one_mem_longSet u : adjointGroup ReeTag.F4.tag K) *
      (reeNb K m : adjointGroup ReeTag.F4.tag K)⁻¹ =
    (reeTorusHom m hK fi_one_mem_longSet u : adjointGroup ReeTag.F4.tag K)⁻¹
  exact (torus_reflections hK u).2.2.1

private theorem reeNb_conj_T0
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (u : Kˣ) :
    reeNb K m * reeTorusHom m hK fi_zero_mem_longSet u * (reeNb K m)⁻¹ =
      reeTorusHom m hK fi_zero_mem_longSet u *
        reeTorusHom m hK fi_one_mem_longSet (u ^ (2 + 2 * (2 ^ m : ℤ))) := by
  apply Subtype.ext
  change (reeNb K m : adjointGroup ReeTag.F4.tag K) *
      (reeTorusHom m hK fi_zero_mem_longSet u : adjointGroup ReeTag.F4.tag K) *
      (reeNb K m : adjointGroup ReeTag.F4.tag K)⁻¹ =
    (reeTorusHom m hK fi_zero_mem_longSet u : adjointGroup ReeTag.F4.tag K) *
      (reeTorusHom m hK fi_one_mem_longSet (u ^ (2 + 2 * ((ReeTag.F4.prime : ℕ) ^ m : ℤ))) :
        adjointGroup ReeTag.F4.tag K)
  exact (torus_reflections hK u).2.2.2

private theorem commute_reeTorusHom
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (x y : Kˣ) :
    Commute (reeTorusHom m hK fi_zero_mem_longSet x)
      (reeTorusHom m hK fi_one_mem_longSet y) :=
  commute_of_mem_reeTorusPart
    (reeTorusSub_le_reeTorusPart hK fi_zero_mem_longSet ⟨x, rfl⟩)
    (reeTorusSub_le_reeTorusPart hK fi_one_mem_longSet ⟨y, rfl⟩)

private theorem conj_mem_reeU_of_mem_reeTorusPart
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    {h : reeFixed ReeTag.F4 K m} (hh : h ∈ reeTorusPart ReeTag.F4 K m)
    {u : reeFixed ReeTag.F4 K m} (hu : u ∈ reeU K m) :
    h * u * h⁻¹ ∈ reeU K m := by
  have hh' : (h : adjointGroup ReeTag.F4.tag K) ∈ (nativeData ReeTag.F4.tag K).H := hh
  simp only [reeU, Subgroup.mem_comap] at hu ⊢
  exact (Subgroup.mem_normalizer_iff.mp
    (RootGroupData.H_le_normalizer_U (D := nativeData ReeTag.F4.tag K) hh') _).mp hu

private theorem reeSz₁_szD_eq
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m) (l : Kˣ) :
    reeSz₁ hK hm (szD K m l) =
      reeTorusHom m hK fi_one_mem_longSet (l ^ (1 + 2 * (2 ^ m : ℤ))) := by
  have hq : (Nat.card K : ℤ) = 2 * (2 ^ m : ℤ) ^ 2 := by
    rw [hK, ← natCast_prime_pow]
    exact two_pow_eq_two_mul_sq m
  have hexp : (l ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 - 2 * (2 ^ m : ℤ)) = l⁻¹ := by
    rw [← zpow_mul, ← zpow_neg_one]
    apply units_zpow_congr l (-2)
    rw [hq]; ring
  have hWinv : (CFSG.LieType.Ree.suzukiWElt m K)⁻¹ = CFSG.LieType.Ree.suzukiWElt m K :=
    CFSG.LieType.Ree.suzukiWElt_inv
  have hWDW : CFSG.LieType.Ree.suzukiWElt m K * CFSG.LieType.Ree.suzukiDElt m K l *
      (CFSG.LieType.Ree.suzukiWElt m K)⁻¹ = CFSG.LieType.Ree.suzukiDElt m K l⁻¹ := by
    rw [hWinv]
    exact CFSG.LieType.Ree.suzukiWElt_D_W hK l
  change (r2 K m hK).subtype ((r2EquivSuzuki K m hK hm).symm
      (CFSG.LieType.Ree.suzukiWElt m K * szD K m l *
        (CFSG.LieType.Ree.suzukiWElt m K)⁻¹)) =
    reeTorusHom m hK fi_one_mem_longSet (l ^ (1 + 2 * (2 ^ m : ℤ)))
  have key : (r2EquivSuzuki K m hK hm).symm
      (CFSG.LieType.Ree.suzukiWElt m K * szD K m l *
        (CFSG.LieType.Ree.suzukiWElt m K)⁻¹) =
      (⟨reeTorusHom m hK fi_one_mem_longSet (l ^ (1 + 2 * (2 ^ m : ℤ))),
        blockT_le_r2 hK ⟨l ^ (1 + 2 * (2 ^ m : ℤ)), rfl⟩⟩ : r2 K m hK) := by
    rw [show szD K m l = CFSG.LieType.Ree.suzukiDElt m K l from rfl, hWDW]
    apply (Equiv.symm_apply_eq (r2EquivSuzuki K m hK hm).toEquiv).2
    trans CFSG.SectionRank.LargeRee.suzukiDElt m l⁻¹
    · exact suzukiDElt_bridge m K l⁻¹
    · trans CFSG.SectionRank.LargeRee.suzukiDElt m
          ((l ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 - 2 * (2 ^ m : ℤ)))
      · rw [hexp]
      · exact (r2EquivSuzuki_reeTorusHom (a := m) hK hm
          (l ^ (1 + 2 * (2 ^ m : ℤ)))).symm
  rw [key]
  rfl

private theorem reeSz₂_szD_eq
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m) (l : Kˣ) :
    reeSz₂ hK hm (szD K m l) =
      reeTorusHom m hK fi_zero_mem_longSet
          ((l ^ (1 + 2 * (2 ^ m : ℤ))) ^ (2 * (2 ^ m : ℤ))) *
        reeTorusHom m hK fi_one_mem_longSet
          ((l ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 + 2 * (2 ^ m : ℤ))) := by
  set b : Kˣ := l ^ (1 + 2 * (2 ^ m : ℤ)) with hb
  have h1 : reeSz₁ hK hm (szD K m l) = reeTorusHom m hK fi_one_mem_longSet b := by
    rw [show reeSz₁ hK hm (szD K m l) =
        reeTorusHom m hK fi_one_mem_longSet (l ^ (1 + 2 * (2 ^ m : ℤ))) from
      reeSz₁_szD_eq hK hm l, ← hb]
  change (reeNa K m * reeNb K m * reeNa K m) * reeSz₁ hK hm (szD K m l) *
      (reeNa K m * reeNb K m * reeNa K m)⁻¹ =
    reeTorusHom m hK fi_zero_mem_longSet (b ^ (2 * (2 ^ m : ℤ))) *
      reeTorusHom m hK fi_one_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ)))
  rw [h1]
  have hc1 : Commute (reeTorusHom m hK fi_zero_mem_longSet b)
      (reeTorusHom m hK fi_one_mem_longSet (b ^ (2 + 2 * (2 ^ m : ℤ)))) :=
    commute_reeTorusHom hK b (b ^ (2 + 2 * (2 ^ m : ℤ)))
  have hc2 : Commute (reeTorusHom m hK fi_zero_mem_longSet b)
      (reeTorusHom m hK fi_one_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ)))) :=
    commute_reeTorusHom hK b (b ^ (1 + 2 * (2 ^ m : ℤ)))
  have hc3 : Commute (reeTorusHom m hK fi_zero_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ))))
      (reeTorusHom m hK fi_one_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ)))) :=
    commute_reeTorusHom hK (b ^ (1 + 2 * (2 ^ m : ℤ))) (b ^ (1 + 2 * (2 ^ m : ℤ)))
  have hT1 : (reeTorusHom m hK fi_one_mem_longSet b)⁻¹ *
      reeTorusHom m hK fi_one_mem_longSet (b ^ (2 + 2 * (2 ^ m : ℤ))) =
      reeTorusHom m hK fi_one_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ))) := by
    rw [← map_inv, ← map_mul]
    congr 1
    rw [← zpow_neg_one, ← zpow_add]
    congr 1
    ring
  have hT0 : (reeTorusHom m hK fi_zero_mem_longSet b)⁻¹ *
      reeTorusHom m hK fi_zero_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ))) =
      reeTorusHom m hK fi_zero_mem_longSet (b ^ (2 * (2 ^ m : ℤ))) := by
    rw [← map_inv, ← map_mul]
    congr 1
    rw [← zpow_neg_one, ← zpow_add]
    congr 1
    ring
  have aux1 : (reeTorusHom m hK fi_one_mem_longSet b)⁻¹ *
      (reeTorusHom m hK fi_zero_mem_longSet b *
        reeTorusHom m hK fi_one_mem_longSet (b ^ (2 + 2 * (2 ^ m : ℤ)))) =
      reeTorusHom m hK fi_zero_mem_longSet b *
        reeTorusHom m hK fi_one_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ))) := by
    calc (reeTorusHom m hK fi_one_mem_longSet b)⁻¹ *
          (reeTorusHom m hK fi_zero_mem_longSet b *
            reeTorusHom m hK fi_one_mem_longSet (b ^ (2 + 2 * (2 ^ m : ℤ))))
        = (reeTorusHom m hK fi_one_mem_longSet b)⁻¹ *
            (reeTorusHom m hK fi_one_mem_longSet (b ^ (2 + 2 * (2 ^ m : ℤ))) *
              reeTorusHom m hK fi_zero_mem_longSet b) := by rw [hc1]
      _ = ((reeTorusHom m hK fi_one_mem_longSet b)⁻¹ *
            reeTorusHom m hK fi_one_mem_longSet (b ^ (2 + 2 * (2 ^ m : ℤ)))) *
              reeTorusHom m hK fi_zero_mem_longSet b := by group
      _ = reeTorusHom m hK fi_one_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ))) *
              reeTorusHom m hK fi_zero_mem_longSet b := by rw [hT1]
      _ = reeTorusHom m hK fi_zero_mem_longSet b *
              reeTorusHom m hK fi_one_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ))) := by
            rw [← hc2]
  have aux2 : (reeTorusHom m hK fi_zero_mem_longSet b)⁻¹ *
      (reeTorusHom m hK fi_one_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ))) *
        reeTorusHom m hK fi_zero_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ)))) =
      reeTorusHom m hK fi_zero_mem_longSet (b ^ (2 * (2 ^ m : ℤ))) *
        reeTorusHom m hK fi_one_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ))) := by
    calc (reeTorusHom m hK fi_zero_mem_longSet b)⁻¹ *
          (reeTorusHom m hK fi_one_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ))) *
            reeTorusHom m hK fi_zero_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ))))
        = (reeTorusHom m hK fi_zero_mem_longSet b)⁻¹ *
            (reeTorusHom m hK fi_zero_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ))) *
              reeTorusHom m hK fi_one_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ)))) := by
            rw [← hc3]
      _ = ((reeTorusHom m hK fi_zero_mem_longSet b)⁻¹ *
            reeTorusHom m hK fi_zero_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ)))) *
              reeTorusHom m hK fi_one_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ))) := by group
      _ = reeTorusHom m hK fi_zero_mem_longSet (b ^ (2 * (2 ^ m : ℤ))) *
              reeTorusHom m hK fi_one_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ))) := by
            rw [hT0]
  calc (reeNa K m * reeNb K m * reeNa K m) * reeTorusHom m hK fi_one_mem_longSet b *
        (reeNa K m * reeNb K m * reeNa K m)⁻¹
      = reeNa K m * reeNb K m *
          (reeNa K m * reeTorusHom m hK fi_one_mem_longSet b * (reeNa K m)⁻¹) *
            (reeNb K m)⁻¹ * (reeNa K m)⁻¹ := by group
    _ = reeNa K m * reeNb K m *
          (reeTorusHom m hK fi_one_mem_longSet b *
            reeTorusHom m hK fi_zero_mem_longSet b) *
            (reeNb K m)⁻¹ * (reeNa K m)⁻¹ := by rw [reeNa_conj_T1 hK b]
    _ = reeNa K m *
          ((reeNb K m * reeTorusHom m hK fi_one_mem_longSet b * (reeNb K m)⁻¹) *
            (reeNb K m * reeTorusHom m hK fi_zero_mem_longSet b * (reeNb K m)⁻¹)) *
              (reeNa K m)⁻¹ := by group
    _ = reeNa K m *
          ((reeTorusHom m hK fi_one_mem_longSet b)⁻¹ *
            (reeTorusHom m hK fi_zero_mem_longSet b *
              reeTorusHom m hK fi_one_mem_longSet (b ^ (2 + 2 * (2 ^ m : ℤ))))) *
              (reeNa K m)⁻¹ := by rw [reeNb_conj_T1 hK b, reeNb_conj_T0 hK b]
    _ = reeNa K m *
          (reeTorusHom m hK fi_zero_mem_longSet b *
            reeTorusHom m hK fi_one_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ)))) *
              (reeNa K m)⁻¹ := by rw [aux1]
    _ = (reeNa K m * reeTorusHom m hK fi_zero_mem_longSet b * (reeNa K m)⁻¹) *
          (reeNa K m * reeTorusHom m hK fi_one_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ))) *
            (reeNa K m)⁻¹) := by group
    _ = (reeTorusHom m hK fi_zero_mem_longSet b)⁻¹ *
          (reeTorusHom m hK fi_one_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ))) *
            reeTorusHom m hK fi_zero_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ)))) := by
          rw [reeNa_conj_T0 hK b, reeNa_conj_T1 hK (b ^ (1 + 2 * (2 ^ m : ℤ)))]
    _ = reeTorusHom m hK fi_zero_mem_longSet (b ^ (2 * (2 ^ m : ℤ))) *
          reeTorusHom m hK fi_one_mem_longSet (b ^ (1 + 2 * (2 ^ m : ℤ))) := aux2

private theorem reeNa_inv
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] (m : ℕ) :
    (reeNa K m)⁻¹ = reeNa K m :=
  inv_eq_of_mul_eq_one_right (reeNa_mul_self (K := K) (m := m))

private theorem reeNa_conj_T01
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (x z : Kˣ) :
    (reeNa K m)⁻¹ * (reeTorusHom m hK fi_zero_mem_longSet x *
        reeTorusHom m hK fi_one_mem_longSet z) * reeNa K m =
      reeTorusHom m hK fi_zero_mem_longSet (x⁻¹ * z) *
        reeTorusHom m hK fi_one_mem_longSet z := by
  have h0 : (reeNa K m)⁻¹ * reeTorusHom m hK fi_zero_mem_longSet x * reeNa K m =
      (reeTorusHom m hK fi_zero_mem_longSet x)⁻¹ := by
    rw [show (reeNa K m)⁻¹ * reeTorusHom m hK fi_zero_mem_longSet x * reeNa K m =
        reeNa K m * reeTorusHom m hK fi_zero_mem_longSet x * (reeNa K m)⁻¹ by
          rw [reeNa_inv]]
    exact reeNa_conj_T0 hK x
  have h1 : (reeNa K m)⁻¹ * reeTorusHom m hK fi_one_mem_longSet z * reeNa K m =
      reeTorusHom m hK fi_one_mem_longSet z * reeTorusHom m hK fi_zero_mem_longSet z := by
    rw [show (reeNa K m)⁻¹ * reeTorusHom m hK fi_one_mem_longSet z * reeNa K m =
        reeNa K m * reeTorusHom m hK fi_one_mem_longSet z * (reeNa K m)⁻¹ by
          rw [reeNa_inv]]
    exact reeNa_conj_T1 hK z
  calc (reeNa K m)⁻¹ * (reeTorusHom m hK fi_zero_mem_longSet x *
          reeTorusHom m hK fi_one_mem_longSet z) * reeNa K m
      = ((reeNa K m)⁻¹ * reeTorusHom m hK fi_zero_mem_longSet x * reeNa K m) *
          ((reeNa K m)⁻¹ * reeTorusHom m hK fi_one_mem_longSet z * reeNa K m) := by
        group
    _ = (reeTorusHom m hK fi_zero_mem_longSet x)⁻¹ *
          (reeTorusHom m hK fi_one_mem_longSet z *
            reeTorusHom m hK fi_zero_mem_longSet z) := by
        rw [h0, h1]
    _ = (reeTorusHom m hK fi_zero_mem_longSet x)⁻¹ *
          (reeTorusHom m hK fi_zero_mem_longSet z *
            reeTorusHom m hK fi_one_mem_longSet z) := by
        rw [← commute_reeTorusHom hK z z]
    _ = ((reeTorusHom m hK fi_zero_mem_longSet x)⁻¹ *
            reeTorusHom m hK fi_zero_mem_longSet z) *
          reeTorusHom m hK fi_one_mem_longSet z := by group
    _ = reeTorusHom m hK fi_zero_mem_longSet (x⁻¹ * z) *
          reeTorusHom m hK fi_one_mem_longSet z := by
        rw [← map_inv, ← map_mul]

private theorem reeT01_reorder
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (a x z : Kˣ) :
    reeTorusHom m hK fi_one_mem_longSet a *
        (reeTorusHom m hK fi_zero_mem_longSet x *
          reeTorusHom m hK fi_one_mem_longSet z) =
      reeTorusHom m hK fi_zero_mem_longSet x *
        reeTorusHom m hK fi_one_mem_longSet (a * z) := by
  calc reeTorusHom m hK fi_one_mem_longSet a *
        (reeTorusHom m hK fi_zero_mem_longSet x *
          reeTorusHom m hK fi_one_mem_longSet z)
      = (reeTorusHom m hK fi_one_mem_longSet a *
          reeTorusHom m hK fi_zero_mem_longSet x) *
          reeTorusHom m hK fi_one_mem_longSet z := by group
    _ = (reeTorusHom m hK fi_zero_mem_longSet x *
          reeTorusHom m hK fi_one_mem_longSet a) *
          reeTorusHom m hK fi_one_mem_longSet z := by
        rw [← commute_reeTorusHom hK x a]
    _ = reeTorusHom m hK fi_zero_mem_longSet x *
        (reeTorusHom m hK fi_one_mem_longSet a *
          reeTorusHom m hK fi_one_mem_longSet z) := by group
    _ = reeTorusHom m hK fi_zero_mem_longSet x *
        reeTorusHom m hK fi_one_mem_longSet (a * z) := by rw [← map_mul]

theorem reeT_norm
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m) :
    ∀ l₁ l₂ : Kˣ, ∀ u ∈ reeU K m,
      (reeSz₁ hK hm (szD K m l₁) * reeSz₂ hK hm (szD K m l₂)) * u *
        (reeSz₁ hK hm (szD K m l₁) * reeSz₂ hK hm (szD K m l₂))⁻¹ ∈ reeU K m := by
  intro l₁ l₂ u hu
  have hA : reeSz₁ hK hm (szD K m l₁) ∈ reeTorusPart ReeTag.F4 K m := by
    rw [reeSz₁_szD_eq hK hm l₁]
    exact reeTorusSub_le_reeTorusPart hK fi_one_mem_longSet ⟨_, rfl⟩
  have hB : reeSz₂ hK hm (szD K m l₂) ∈ reeTorusPart ReeTag.F4 K m := by
    rw [reeSz₂_szD_eq hK hm l₂]
    exact mul_mem
      (reeTorusSub_le_reeTorusPart hK fi_zero_mem_longSet ⟨_, rfl⟩)
      (reeTorusSub_le_reeTorusPart hK fi_one_mem_longSet ⟨_, rfl⟩)
  exact conj_mem_reeU_of_mem_reeTorusPart (mul_mem hA hB) hu

theorem reeNa_conj_tau
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m) :
    ∀ l₁ l₂ : Kˣ,
      (reeNa K m)⁻¹ * (reeSz₁ hK hm (szD K m l₁) * reeSz₂ hK hm (szD K m l₂)) * reeNa K m =
        reeSz₁ hK hm (szD K m ((l₂ / l₁) ^ 2 ^ m)) *
        reeSz₂ hK hm (szD K m ((l₁ * l₂) ^ 2 ^ m)) := by
  intro l₁ l₂
  have hq : (Nat.card K : ℤ) = 2 * (2 ^ m : ℤ) ^ 2 := by
    rw [hK, ← natCast_prime_pow]
    exact two_pow_eq_two_mul_sq m
  have hxL : ((l₂ ^ (1 + 2 * (2 ^ m : ℤ))) ^ (2 * (2 ^ m : ℤ)))⁻¹ *
      (l₁ ^ (1 + 2 * (2 ^ m : ℤ)) *
        (l₂ ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 + 2 * (2 ^ m : ℤ))) =
      (l₁ * l₂) ^ (1 + 2 * (2 ^ m : ℤ)) := by
    rw [← zpow_mul, ← zpow_mul, ← zpow_neg]
    calc l₂ ^ (-((1 + 2 * (2 ^ m : ℤ)) * (2 * (2 ^ m : ℤ)))) *
          (l₁ ^ (1 + 2 * (2 ^ m : ℤ)) *
            l₂ ^ ((1 + 2 * (2 ^ m : ℤ)) * (1 + 2 * (2 ^ m : ℤ))))
        = l₁ ^ (1 + 2 * (2 ^ m : ℤ)) *
            (l₂ ^ (-((1 + 2 * (2 ^ m : ℤ)) * (2 * (2 ^ m : ℤ)))) *
              l₂ ^ ((1 + 2 * (2 ^ m : ℤ)) * (1 + 2 * (2 ^ m : ℤ)))) := by
          rw [← mul_assoc, mul_comm
            (l₂ ^ (-((1 + 2 * (2 ^ m : ℤ)) * (2 * (2 ^ m : ℤ)))))
            (l₁ ^ (1 + 2 * (2 ^ m : ℤ))), mul_assoc]
      _ = l₁ ^ (1 + 2 * (2 ^ m : ℤ)) * l₂ ^ (1 + 2 * (2 ^ m : ℤ)) := by
            rw [← zpow_add, show
              -((1 + 2 * (2 ^ m : ℤ)) * (2 * (2 ^ m : ℤ))) +
                ((1 + 2 * (2 ^ m : ℤ)) * (1 + 2 * (2 ^ m : ℤ))) =
                (1 + 2 * (2 ^ m : ℤ)) by ring]
      _ = (l₁ * l₂) ^ (1 + 2 * (2 ^ m : ℤ)) := by rw [← mul_zpow]
  have hxR : (((l₁ * l₂) ^ 2 ^ m) ^ (1 + 2 * (2 ^ m : ℤ))) ^ (2 * (2 ^ m : ℤ)) =
      (l₁ * l₂) ^ (1 + 2 * (2 ^ m : ℤ)) := by
    rw [← zpow_natCast (l₁ * l₂) (2 ^ m), ← zpow_mul, ← zpow_mul]
    apply units_zpow_congr (l₁ * l₂) (1 + 2 * (2 ^ m : ℤ))
    rw [hq]; push_cast; ring
  have hzL : l₁ ^ (1 + 2 * (2 ^ m : ℤ)) *
        (l₂ ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 + 2 * (2 ^ m : ℤ)) =
      l₁ ^ (1 + 2 * (2 ^ m : ℤ)) *
        l₂ ^ ((1 + 2 * (2 ^ m : ℤ)) * (1 + 2 * (2 ^ m : ℤ))) := by
    rw [← zpow_mul]
  have hzR : (((l₂ / l₁) ^ 2 ^ m) ^ (1 + 2 * (2 ^ m : ℤ))) *
      ((((l₁ * l₂) ^ 2 ^ m) ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 + 2 * (2 ^ m : ℤ))) =
      l₁ ^ (1 + 2 * (2 ^ m : ℤ)) *
        l₂ ^ ((1 + 2 * (2 ^ m : ℤ)) * (1 + 2 * (2 ^ m : ℤ))) := by
    rw [← zpow_natCast (l₂ / l₁) (2 ^ m), ← zpow_natCast (l₁ * l₂) (2 ^ m),
        ← zpow_mul, ← zpow_mul, ← zpow_mul]
    rw [div_eq_inv_mul,
        show (↑(2 ^ m : ℕ) : ℤ) = (2 : ℤ) ^ m by push_cast; rfl]
    conv_lhs => rw [← zpow_neg_one l₁]
    conv_lhs => enter [2, 1]; rw [← zpow_one l₁, ← zpow_one l₂]
    conv_lhs => enter [1, 1, 2]; rw [← zpow_one l₂]
    rw [zpow_mul_zpow_zpow]
    congr 1
    · apply units_zpow_congr l₁ (1 + 2 * (2 ^ m : ℤ))
      rw [hq]; push_cast; ring
    · apply units_zpow_congr l₂ (1 + 2 * (2 ^ m : ℤ))
      rw [hq]; push_cast; ring
  have hx : ((l₂ ^ (1 + 2 * (2 ^ m : ℤ))) ^ (2 * (2 ^ m : ℤ)))⁻¹ *
      (l₁ ^ (1 + 2 * (2 ^ m : ℤ)) *
        (l₂ ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 + 2 * (2 ^ m : ℤ))) =
      (((l₁ * l₂) ^ 2 ^ m) ^ (1 + 2 * (2 ^ m : ℤ))) ^ (2 * (2 ^ m : ℤ)) :=
    hxL.trans hxR.symm
  have hz : l₁ ^ (1 + 2 * (2 ^ m : ℤ)) *
        (l₂ ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 + 2 * (2 ^ m : ℤ)) =
      (((l₂ / l₁) ^ 2 ^ m) ^ (1 + 2 * (2 ^ m : ℤ))) *
        ((((l₁ * l₂) ^ 2 ^ m) ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 + 2 * (2 ^ m : ℤ))) :=
    hzL.trans hzR.symm
  rw [reeSz₁_szD_eq hK hm l₁, reeSz₂_szD_eq hK hm l₂,
      reeSz₁_szD_eq hK hm ((l₂ / l₁) ^ 2 ^ m),
      reeSz₂_szD_eq hK hm ((l₁ * l₂) ^ 2 ^ m)]
  calc (reeNa K m)⁻¹ *
        (reeTorusHom m hK fi_one_mem_longSet (l₁ ^ (1 + 2 * (2 ^ m : ℤ))) *
          (reeTorusHom m hK fi_zero_mem_longSet
              ((l₂ ^ (1 + 2 * (2 ^ m : ℤ))) ^ (2 * (2 ^ m : ℤ))) *
            reeTorusHom m hK fi_one_mem_longSet
              ((l₂ ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 + 2 * (2 ^ m : ℤ))))) *
        reeNa K m
      = (reeNa K m)⁻¹ *
          (reeTorusHom m hK fi_zero_mem_longSet
              ((l₂ ^ (1 + 2 * (2 ^ m : ℤ))) ^ (2 * (2 ^ m : ℤ))) *
            reeTorusHom m hK fi_one_mem_longSet
              (l₁ ^ (1 + 2 * (2 ^ m : ℤ)) *
                (l₂ ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 + 2 * (2 ^ m : ℤ)))) *
          reeNa K m := by
        rw [reeT01_reorder hK (l₁ ^ (1 + 2 * (2 ^ m : ℤ)))
          ((l₂ ^ (1 + 2 * (2 ^ m : ℤ))) ^ (2 * (2 ^ m : ℤ)))
          ((l₂ ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 + 2 * (2 ^ m : ℤ)))]
    _ = reeTorusHom m hK fi_zero_mem_longSet
          (((l₂ ^ (1 + 2 * (2 ^ m : ℤ))) ^ (2 * (2 ^ m : ℤ)))⁻¹ *
            (l₁ ^ (1 + 2 * (2 ^ m : ℤ)) *
              (l₂ ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 + 2 * (2 ^ m : ℤ)))) *
        reeTorusHom m hK fi_one_mem_longSet
          (l₁ ^ (1 + 2 * (2 ^ m : ℤ)) *
            (l₂ ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 + 2 * (2 ^ m : ℤ))) :=
        reeNa_conj_T01 hK ((l₂ ^ (1 + 2 * (2 ^ m : ℤ))) ^ (2 * (2 ^ m : ℤ)))
          (l₁ ^ (1 + 2 * (2 ^ m : ℤ)) *
            (l₂ ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 + 2 * (2 ^ m : ℤ)))
    _ = reeTorusHom m hK fi_zero_mem_longSet
          ((((l₁ * l₂) ^ 2 ^ m) ^ (1 + 2 * (2 ^ m : ℤ))) ^ (2 * (2 ^ m : ℤ))) *
        reeTorusHom m hK fi_one_mem_longSet
          ((((l₂ / l₁) ^ 2 ^ m) ^ (1 + 2 * (2 ^ m : ℤ))) *
            ((((l₁ * l₂) ^ 2 ^ m) ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 + 2 * (2 ^ m : ℤ)))) := by
        rw [hx, hz]
    _ = reeTorusHom m hK fi_one_mem_longSet
          (((l₂ / l₁) ^ 2 ^ m) ^ (1 + 2 * (2 ^ m : ℤ))) *
        (reeTorusHom m hK fi_zero_mem_longSet
            ((((l₁ * l₂) ^ 2 ^ m) ^ (1 + 2 * (2 ^ m : ℤ))) ^ (2 * (2 ^ m : ℤ))) *
          reeTorusHom m hK fi_one_mem_longSet
            ((((l₁ * l₂) ^ 2 ^ m) ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 + 2 * (2 ^ m : ℤ)))) :=
        (reeT01_reorder hK (((l₂ / l₁) ^ 2 ^ m) ^ (1 + 2 * (2 ^ m : ℤ)))
          ((((l₁ * l₂) ^ 2 ^ m) ^ (1 + 2 * (2 ^ m : ℤ))) ^ (2 * (2 ^ m : ℤ)))
          ((((l₁ * l₂) ^ 2 ^ m) ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 + 2 * (2 ^ m : ℤ)))).symm

theorem reeB0_mem
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] [CharP K 2] [Fintype K] {m : ℕ}
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * m + 1)) (hm : 1 ≤ m) (w : Kˣ)
    (e : reeFixed ReeTag.F4 K m)
    (he : (e : adjointGroup ReeTag.F4.tag K) = F4Chief.reeB2Elt K m w) :
    ∃ l : Kˣ, e = reeSz₂ hK hm (szD K m l) := by
  have hq : (Nat.card K : ℤ) = 2 * (2 ^ m : ℤ) ^ 2 := by
    rw [hK, ← natCast_prime_pow]
    exact two_pow_eq_two_mul_sq m
  refine ⟨w, ?_⟩
  apply Subtype.ext
  change (e : adjointGroup ReeTag.F4.tag K) =
    (reeSz₂ hK hm (szD K m w) : adjointGroup ReeTag.F4.tag K)
  rw [he]
  change F4Rest.b2TorusElt K m w =
    (reeSz₂ hK hm (szD K m w) : adjointGroup ReeTag.F4.tag K)
  have hF2 := congrArg (fun x : reeFixed ReeTag.F4 K m =>
      (x : adjointGroup ReeTag.F4.tag K)) (reeSz₂_szD_eq hK hm w)
  rw [hF2]
  simp only [Subgroup.coe_mul, coe_reeTorusHom]
  change ReeTag.F4.reeTorus m 0 (w ^ (2 : ℤ) * (w ^ (2 ^ m)) ^ (2 : ℤ)) *
      ReeTag.F4.reeTorus m 1 (w ^ (3 : ℤ) * (w ^ (2 ^ m)) ^ (4 : ℤ)) =
    ReeTag.F4.reeTorus m 0 ((w ^ (1 + 2 * (2 ^ m : ℤ))) ^ (2 * (2 ^ m : ℤ))) *
      ReeTag.F4.reeTorus m 1 ((w ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 + 2 * (2 ^ m : ℤ)))
  have h0 : (w ^ (1 + 2 * (2 ^ m : ℤ))) ^ (2 * (2 ^ m : ℤ)) =
      w ^ (2 : ℤ) * (w ^ (2 ^ m)) ^ (2 : ℤ) := by
    rw [← zpow_natCast w (2 ^ m), ← zpow_mul, ← zpow_mul, ← zpow_add]
    apply units_zpow_congr w 2
    rw [hq]; push_cast; ring
  have h1 : (w ^ (1 + 2 * (2 ^ m : ℤ))) ^ (1 + 2 * (2 ^ m : ℤ)) =
      w ^ (3 : ℤ) * (w ^ (2 ^ m)) ^ (4 : ℤ) := by
    rw [← zpow_natCast w (2 ^ m), ← zpow_mul, ← zpow_mul, ← zpow_add]
    apply units_zpow_congr w 2
    rw [hq]; push_cast; ring
  rw [h0, h1]

end CFSG.StandardType.ReeB2Fixed
