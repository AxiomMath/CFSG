module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Residual

namespace CFSG
end CFSG
open CFSG

/-!
# Residual and Sylow data for Proposition 8.2

This file isolates the solvable-group front end of Proposition 8.2(a).  For a
nontrivial finite solvable group of odd order, it selects an odd prime `p` for
which the `p`-residual is proper and a Sylow `p`-subgroup supplementing that
residual.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open External
open scoped Pointwise

universe u

/-- The odd-prime residual and Sylow supplement selected at the start of the
proof of Proposition 8.2(a). -/
public structure Proposition82ResidualData
    (Y : Type u) [Group Y] where
  p : ℕ
  p_prime : p.Prime
  p_odd : Odd p
  residual_ne_top : hktPResidual p Y ≠ ⊤
  R : Sylow p Y
  residual_sup_sylow :
    hktPResidual p Y ⊔ (R : Subgroup Y) = ⊤

/-- A nontrivial finite solvable group of odd order has an odd prime `p` such
that `O^p(Y)` is proper, together with a Sylow `p`-subgroup `R` satisfying
`Y = O^p(Y) R` in subgroup-join form. -/
public theorem proposition82ResidualData_nonempty_of_odd
    (Y : Type u) [Group Y] [Finite Y] [Group.IsSolvable Y] [Nontrivial Y]
    (hYodd : Odd (Nat.card Y)) :
    Nonempty (Proposition82ResidualData Y) := by
  classical
  obtain ⟨H, hHnormal, hp⟩ := exist_index_p_of_solvable Y
  let p : ℕ := H.index
  have hpPrime : p.Prime := by
    simpa [p] using hp
  let : Fact p.Prime := ⟨hpPrime⟩
  have hpOdd : Odd p :=
    Odd.of_dvd_nat hYodd (by simpa [p] using H.index_dvd_card)
  let : H.Normal := hHnormal
  have hquotientP : IsPGroup p (Y ⧸ H) := by
    apply IsPGroup.of_card (p := p) (G := Y ⧸ H) (n := 1)
    simpa only [pow_one, p] using H.index_eq_card.symm
  have hResidualLe : hktPResidual p Y ≤ H :=
    hktPResidual_le H hHnormal hquotientP
  have hHneTop : H ≠ ⊤ := by
    intro hHtop
    have hpOne : p = 1 := by
      simp [p, hHtop]
    exact hpPrime.ne_one hpOne
  have hResidualNeTop : hktPResidual p Y ≠ ⊤ := by
    intro hResidualTop
    apply hHneTop
    exact top_unique (by simpa [hResidualTop] using hResidualLe)
  let R : Sylow p Y := Classical.choice (Sylow.nonempty (p := p) (G := Y))
  let W : Subgroup Y := hktPResidual p Y
  let : W.Normal := by
    simpa [W] using hktPResidual_normal (Q := Y) (q := p)
  let q : Y →* Y ⧸ W := QuotientGroup.mk' W
  have hResidualQuotientP : IsPGroup p (Y ⧸ W) := by
    simpa [W] using hktPResidual_quotient_isPGroup (Q := Y) (q := p)
  have hTopP : IsPGroup p (⊤ : Subgroup (Y ⧸ W)) :=
    hResidualQuotientP.to_subgroup ⊤
  have hRmapTop : (R : Subgroup Y).map q = ⊤ := by
    let Rbar : Sylow p (Y ⧸ W) :=
      R.mapSurjective (f := q) (QuotientGroup.mk'_surjective W)
    simpa [Rbar] using (Rbar.3 hTopP le_top).symm
  have hResidualSupSylow : W ⊔ (R : Subgroup Y) = ⊤ := by
    calc
      W ⊔ (R : Subgroup Y) = q.ker ⊔ (R : Subgroup Y) := by
        simp [q, QuotientGroup.ker_mk']
      _ = (R : Subgroup Y) ⊔ q.ker := by rw [sup_comm]
      _ = ((R : Subgroup Y).map q).comap q :=
        (Subgroup.comap_map_eq (f := q) (H := (R : Subgroup Y))).symm
      _ = ⊤ := by rw [hRmapTop, Subgroup.comap_top]
  exact ⟨{
    p := p
    p_prime := hpPrime
    p_odd := hpOdd
    residual_ne_top := hResidualNeTop
    R := R
    residual_sup_sylow := by simpa [W] using hResidualSupSylow
  }⟩

/-- If an odd-prime `p`-subgroup `R` normalizes `C`, every element of
`C ⊔ R` whose square is one already lies in `C`.

The quotient of `C ⊔ R` by `C` is a homomorphic image of `R`, hence a
`p`-group.  Since `p` is odd, that quotient has no nontrivial element whose
square is one.  This is the quotient step used in Proposition 8.2 to turn a
normalizing involution in `C_X(W)R` into an element of `C_X(W)`. -/
public theorem sq_eq_one_mem_left_of_sup_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hpOdd : Odd p) (C R : Subgroup G)
    (hRp : IsPGroup p R)
    (hRnormC : R ≤ Subgroup.normalizer (C : Set G))
    {u : G} (huF : u ∈ C ⊔ R) (huSq : u ^ 2 = 1) :
    u ∈ C := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let F : Subgroup G := C ⊔ R
  let CF : Subgroup F := C.subgroupOf F
  have hFNormC : F ≤ Subgroup.normalizer (C : Set G) := by
    exact sup_le Subgroup.le_normalizer hRnormC
  let : CF.Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      (show C ≤ F from le_sup_left)).2
    exact hFNormC
  let q : F →* F ⧸ CF := QuotientGroup.mk' CF
  let iR : R →* F :=
    { toFun := fun r => ⟨(r : G), (le_sup_right : R ≤ F) r.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let qR : R →* F ⧸ CF := q.comp iR
  have hqRsurj : Function.Surjective qR := by
    intro z
    obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective CF z
    have hf : (f : G) ∈ (C : Set G) * (R : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left C R hRnormC]
      exact f.property
    rcases hf with ⟨c, hc, r, hr, hcr⟩
    refine ⟨⟨r, hr⟩, ?_⟩
    change q ⟨r, (le_sup_right : R ≤ F) hr⟩ = q f
    have hfEq : f =
        ⟨c, (le_sup_left : C ≤ F) hc⟩ *
          ⟨r, (le_sup_right : R ≤ F) hr⟩ := by
      apply Subtype.ext
      exact hcr.symm
    rw [hfEq, map_mul]
    have hcOne : q ⟨c, (le_sup_left : C ≤ F) hc⟩ = 1 := by
      exact (QuotientGroup.eq_one_iff (N := CF) _).2 hc
    rw [hcOne, one_mul]
  have hquotP : IsPGroup p (F ⧸ CF) :=
    IsPGroup.of_surjective hRp qR hqRsurj
  let uF : F := ⟨u, huF⟩
  have huFsq : uF ^ 2 = 1 := by
    apply Subtype.ext
    exact huSq
  have hqSq : q uF ^ 2 = 1 := by
    rw [← map_pow, huFsq, map_one]
  have hpNeTwo : p ≠ 2 := by
    intro h
    subst p
    rcases hpOdd with ⟨k, hk⟩
    omega
  have hqOne : q uF = 1 := by
    have hordDvd : orderOf (q uF) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one hqSq
    rcases (IsPGroup.iff_orderOf (p := p) (G := F ⧸ CF)).1
        hquotP (q uF) with ⟨k, hk⟩
    have hkDvd : p ^ k ∣ 2 := by simpa [hk] using hordDvd
    have hkZero : k = 0 := by
      cases k with
      | zero => rfl
      | succ k =>
          exfalso
          have hpDvd : p ∣ 2 :=
            dvd_trans (dvd_pow_self p (Nat.succ_ne_zero k)) hkDvd
          exact hpNeTwo
            ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpDvd)
    apply orderOf_eq_one_iff.mp
    simpa [hkZero] using hk
  exact (QuotientGroup.eq_one_iff (N := CF) uF).1 hqOne

end CFSG.BenderSuzuki
