module

public import CFSG.LocalAnalysis.StandardType.GGF4H4Psl64Scalar
public import CFSG.Assembly.GL83LieDefs
import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType

open CFSG.Assembly
open scoped Matrix
open scoped MatrixGroups

private noncomputable def ggF4H4Psl64_glToLinearEquiv (F : Type) [Field F] :
    GL (Fin 6) F ≃* ((Fin 6 → F) ≃ₗ[F] (Fin 6 → F)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 6 → F))

private lemma ggF4H4Psl64_glToLinearEquiv_apply (F : Type) [Field F] (A : GL (Fin 6) F)
    (v : Fin 6 → F) :
    (ggF4H4Psl64_glToLinearEquiv F A) v = (A : Matrix (Fin 6) (Fin 6) F) *ᵥ v :=
  rfl

private lemma ggF4H4Psl64_glToLinearEquiv_scalar (F : Type) [Field F] (u : Fˣ)
    (v : Fin 6 → F) :
    (ggF4H4Psl64_glToLinearEquiv F (Matrix.GeneralLinearGroup.scalar (Fin 6) u)) v =
      (u : F) • v := by
  rw [ggF4H4Psl64_glToLinearEquiv_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec]

private lemma ggF4H4Psl64_card_units {F : Type} [Field F] (hF : Nat.card F = 4) :
    Nat.card Fˣ = 3 := by
  rw [Nat.card_units, hF]

private lemma ggF4H4Psl64_units_pow_three {F : Type} [Field F] (hF : Nat.card F = 4)
    (c : Fˣ) : c ^ 3 = 1 := by
  have h := pow_card_eq_one' (x := c)
  rwa [ggF4H4Psl64_card_units hF] at h

private lemma ggF4H4Psl64_mem_scalars_pow_three {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (n : ↥(LargeEvenSLGroup (Fin 6) F))
    (hn : n ∈ (LargeEvenScalars (Fin 6) F).subgroupOf (LargeEvenSLGroup (Fin 6) F)) :
    n ^ 3 = 1 := by
  have hnr : (n : GL (Fin 6) F) ∈ (Matrix.GeneralLinearGroup.scalar (Fin 6)).range := by
    have h := (Subgroup.mem_subgroupOf).1 hn
    simpa only [largeEvenScalars_def] using h
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hnr
  have hgl : (n : GL (Fin 6) F) ^ 3 = 1 := by
    rw [← hc, ← map_pow (Matrix.GeneralLinearGroup.scalar (Fin 6)) c 3,
      ggF4H4Psl64_units_pow_three hF c, map_one]
  exact Subtype.ext (by simpa only [Subgroup.coe_pow, Subgroup.coe_one] using hgl)

private lemma ggF4H4Psl64_mem_scalars_commute {F : Type} [Field F] [Finite F]
    (n g : ↥(LargeEvenSLGroup (Fin 6) F))
    (hn : n ∈ (LargeEvenScalars (Fin 6) F).subgroupOf (LargeEvenSLGroup (Fin 6) F)) :
    n * g = g * n :=
  ((Subgroup.mem_center_iff.1 (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center
    (LargeEvenSLGroup (Fin 6) F) hn)) g).symm

private lemma ggF4H4Psl64_lift {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (y : LargeEvenProj (LargeEvenSLGroup (Fin 6) F)) (k ℓ : ℕ) (hk : y ^ k = y)
    (h3k : 3 ∣ k) (hy : y ^ ℓ = 1) (hy1 : y ≠ 1) :
    ∃ A : ↥(LargeEvenSLGroup (Fin 6) F),
      (QuotientGroup.mk A : LargeEvenProj (LargeEvenSLGroup (Fin 6) F)) = y ∧
        A ^ ℓ = 1 ∧ A ≠ 1 := by
  obtain ⟨a₀, ha₀⟩ := QuotientGroup.mk_surjective (s :=
    (LargeEvenScalars (Fin 6) F).subgroupOf (LargeEvenSLGroup (Fin 6) F)) y
  have hmem : a₀ ^ ℓ ∈ (LargeEvenScalars (Fin 6) F).subgroupOf (LargeEvenSLGroup (Fin 6) F) := by
    refine (QuotientGroup.eq_one_iff (a₀ ^ ℓ)).mp ?_
    rw [QuotientGroup.mk_pow, ha₀, hy]
  have hAl : (a₀ ^ k) ^ ℓ = 1 := by
    have h3 : (a₀ ^ ℓ) ^ 3 = 1 := ggF4H4Psl64_mem_scalars_pow_three hF (a₀ ^ ℓ) hmem
    have hkeq : (a₀ ^ k) ^ ℓ = (a₀ ^ ℓ) ^ k := by
      rw [← pow_mul a₀ k ℓ, ← pow_mul a₀ ℓ k, Nat.mul_comm k ℓ]
    rw [hkeq]
    obtain ⟨m, hm⟩ := h3k
    rw [hm, pow_mul, h3, one_pow]
  have hmk : (QuotientGroup.mk (a₀ ^ k) :
      LargeEvenProj (LargeEvenSLGroup (Fin 6) F)) = y := by
    rw [QuotientGroup.mk_pow, ha₀, hk]
  exact ⟨a₀ ^ k, hmk, hAl, fun h => hy1 (by rw [← hmk, h, QuotientGroup.mk_one])⟩

private lemma ggF4H4Psl64_commute {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (A Z : ↥(LargeEvenSLGroup (Fin 6) F)) (ℓ : ℕ) (hgcd : ℓ.gcd 3 = 1) (hA : A ^ ℓ = 1)
    (hZ : Z ^ 3 ∈ (LargeEvenScalars (Fin 6) F).subgroupOf (LargeEvenSLGroup (Fin 6) F))
    (hcomm : (QuotientGroup.mk A : LargeEvenProj (LargeEvenSLGroup (Fin 6) F)) *
        (QuotientGroup.mk Z : LargeEvenProj (LargeEvenSLGroup (Fin 6) F)) =
      (QuotientGroup.mk Z : LargeEvenProj (LargeEvenSLGroup (Fin 6) F)) *
        (QuotientGroup.mk A : LargeEvenProj (LargeEvenSLGroup (Fin 6) F))) :
    Z * A = A * Z := by
  set n : ↥(LargeEvenSLGroup (Fin 6) F) := Z * A * Z⁻¹ * A⁻¹ with hn_def
  have hZA : Z * A * Z⁻¹ = n * A := by
    rw [hn_def]
    group
  have hnN : n ∈ (LargeEvenScalars (Fin 6) F).subgroupOf (LargeEvenSLGroup (Fin 6) F) := by
    refine (QuotientGroup.eq_one_iff n).mp ?_
    have hcoe : (QuotientGroup.mk n : LargeEvenProj (LargeEvenSLGroup (Fin 6) F)) =
        (QuotientGroup.mk Z : LargeEvenProj (LargeEvenSLGroup (Fin 6) F)) *
          (QuotientGroup.mk A : LargeEvenProj (LargeEvenSLGroup (Fin 6) F)) *
          (QuotientGroup.mk Z : LargeEvenProj (LargeEvenSLGroup (Fin 6) F))⁻¹ *
          (QuotientGroup.mk A : LargeEvenProj (LargeEvenSLGroup (Fin 6) F))⁻¹ := by
      simp only [hn_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hcoe, hcomm.symm]
    group
  have hnℓ : n ^ ℓ = 1 := by
    have h2 : (Z * A * Z⁻¹) ^ ℓ = n ^ ℓ * A ^ ℓ := by
      rw [hZA, Commute.mul_pow (ggF4H4Psl64_mem_scalars_commute n A hnN) ℓ]
    have h3 : (Z * A * Z⁻¹) ^ ℓ = 1 := by
      rw [conj_pow, hA, mul_one, mul_inv_cancel]
    rw [h3] at h2
    rw [hA, mul_one] at h2
    exact h2.symm
  have hn3 : n ^ 3 = 1 := ggF4H4Psl64_mem_scalars_pow_three hF n hnN
  have hn1 : n = 1 := by
    have hg : n ^ (ℓ.gcd 3) = 1 := pow_gcd_eq_one.mpr ⟨hnℓ, hn3⟩
    rwa [hgcd, pow_one] at hg
  have hZA' : Z * A * Z⁻¹ = A := by rw [hZA, hn1, one_mul]
  calc Z * A = Z * A * Z⁻¹ * Z := by group
    _ = A * Z := by rw [hZA']

theorem ggF4H4Psl64_gl_scalar {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (A B Z : GL (Fin 6) F) (hA : A ^ 13 = 1) (hA1 : A ≠ 1) (hB : B ^ 17 = 1) (hB1 : B ≠ 1)
    (hAZ : A * Z = Z * A) (hBZ : B * Z = Z * B) (hZ3 : Z ^ 3 ∈ LargeEvenScalars (Fin 6) F) :
    Z ∈ LargeEvenScalars (Fin 6) F := by
  have hZ3r : Z ^ 3 ∈ (Matrix.GeneralLinearGroup.scalar (Fin 6)).range := by
    simpa only [largeEvenScalars_def] using hZ3
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 hZ3r
  let e := ggF4H4Psl64_glToLinearEquiv F
  have ha : (e A) ^ 13 = 1 := by rw [← map_pow e A 13, hA, map_one e]
  have ha1 : e A ≠ 1 := fun h => hA1 (e.injective (h.trans (map_one e).symm))
  have hb : (e B) ^ 17 = 1 := by rw [← map_pow e B 17, hB, map_one e]
  have hb1 : e B ≠ 1 := fun h => hB1 (e.injective (h.trans (map_one e).symm))
  have haz : e A * e Z = e Z * e A := by
    have h := congrArg e hAZ
    simpa using h
  have hbz : e B * e Z = e Z * e B := by
    have h := congrArg e hBZ
    simpa using h
  have hz3 : ∃ c : F, ∀ v : Fin 6 → F, ((e Z) ^ 3) v = c • v := by
    refine ⟨(u : F), fun v => ?_⟩
    rw [← map_pow e Z 3, ← hu]
    exact ggF4H4Psl64_glToLinearEquiv_scalar F u v
  obtain ⟨c, hc⟩ := ggF4H4Psl64_scalar_of_commute hF (Module.finrank_fin_fun F)
    (e A) (e B) (e Z) ha ha1 hb hb1 haz hbz hz3
  have hne : (1 : Fin 6 → F) ≠ 0 := by
    intro h
    have h0 : (1 : F) = 0 := by simpa using congrFun h 0
    exact one_ne_zero h0
  have hc0 : c ≠ 0 := by
    intro h0
    have hv : (e Z) (1 : Fin 6 → F) = 0 := by
      rw [hc (1 : Fin 6 → F), h0, zero_smul]
    have hz0 : (e Z) (1 : Fin 6 → F) = (e Z) 0 := by rw [hv, map_zero]
    exact hne ((e Z).injective hz0)
  let u' : Fˣ := Units.mk0 c hc0
  have he_scalar : e (Matrix.GeneralLinearGroup.scalar (Fin 6) u') = e Z := by
    apply LinearEquiv.ext
    intro v
    rw [ggF4H4Psl64_glToLinearEquiv_scalar F u' v]
    exact (hc v).symm
  rw [largeEvenScalars_def, MonoidHom.mem_range]
  exact ⟨u', e.injective he_scalar⟩

theorem ggF4H4Psl64_no_commuting {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (y y' z : LargeEvenProj (LargeEvenSLGroup (Fin 6) F)) (hy : y ^ 13 = 1) (hy1 : y ≠ 1)
    (hy' : y' ^ 17 = 1) (hy1' : y' ≠ 1) (hz : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hyz : y * z = z * y) (hy'z : y' * z = z * y') : False := by
  obtain ⟨A, hmkA, hA13, hA1⟩ := ggF4H4Psl64_lift hF y 27 13 (by
    rw [show (27 : ℕ) = 13 * 2 + 1 by norm_num, pow_add, pow_mul, pow_one, hy, one_pow,
      one_mul]) (by norm_num) hy hy1
  obtain ⟨B, hmkB, hB17, hB1⟩ := ggF4H4Psl64_lift hF y' 18 17 (by
    rw [show (18 : ℕ) = 17 + 1 by norm_num, pow_add, pow_one, hy', one_mul])
    (by norm_num) hy' hy1'
  obtain ⟨Z, hmkZ⟩ := QuotientGroup.mk_surjective (s :=
    (LargeEvenScalars (Fin 6) F).subgroupOf (LargeEvenSLGroup (Fin 6) F)) z
  have hZ3 : Z ^ 3 ∈ (LargeEvenScalars (Fin 6) F).subgroupOf (LargeEvenSLGroup (Fin 6) F) := by
    refine (QuotientGroup.eq_one_iff (Z ^ 3)).mp ?_
    rw [QuotientGroup.mk_pow, hmkZ, hz]
  have hAZ : Z * A = A * Z := ggF4H4Psl64_commute hF A Z 13 (by decide) hA13 hZ3 (by
    rw [hmkA, hmkZ, hyz])
  have hBZ : Z * B = B * Z := ggF4H4Psl64_commute hF B Z 17 (by decide) hB17 hZ3 (by
    rw [hmkB, hmkZ, hy'z])
  have hA13' : (A : GL (Fin 6) F) ^ 13 = 1 := by
    have h := congrArg (Subgroup.subtype (LargeEvenSLGroup (Fin 6) F)) hA13
    rw [map_pow, map_one] at h
    exact h
  have hA1' : (A : GL (Fin 6) F) ≠ 1 := fun h => hA1 (Subtype.ext h)
  have hB17' : (B : GL (Fin 6) F) ^ 17 = 1 := by
    have h := congrArg (Subgroup.subtype (LargeEvenSLGroup (Fin 6) F)) hB17
    rw [map_pow, map_one] at h
    exact h
  have hB1' : (B : GL (Fin 6) F) ≠ 1 := fun h => hB1 (Subtype.ext h)
  have hAZ' : (A : GL (Fin 6) F) * (Z : GL (Fin 6) F) =
      (Z : GL (Fin 6) F) * (A : GL (Fin 6) F) := by
    have h := congrArg (Subgroup.subtype (LargeEvenSLGroup (Fin 6) F)) hAZ
    simp only [map_mul] at h
    exact h.symm
  have hBZ' : (B : GL (Fin 6) F) * (Z : GL (Fin 6) F) =
      (Z : GL (Fin 6) F) * (B : GL (Fin 6) F) := by
    have h := congrArg (Subgroup.subtype (LargeEvenSLGroup (Fin 6) F)) hBZ
    simp only [map_mul] at h
    exact h.symm
  have hZ3' : (Z : GL (Fin 6) F) ^ 3 ∈ LargeEvenScalars (Fin 6) F := by
    have h := (Subgroup.mem_subgroupOf).1 hZ3
    rwa [Subgroup.coe_pow] at h
  have hZscalar : (Z : GL (Fin 6) F) ∈ LargeEvenScalars (Fin 6) F :=
    ggF4H4Psl64_gl_scalar hF (A : GL (Fin 6) F) (B : GL (Fin 6) F) (Z : GL (Fin 6) F)
      hA13' hA1' hB17' hB1' hAZ' hBZ' hZ3'
  have hZN : Z ∈ (LargeEvenScalars (Fin 6) F).subgroupOf (LargeEvenSLGroup (Fin 6) F) :=
    (Subgroup.mem_subgroupOf).2 hZscalar
  have hZ1 : (QuotientGroup.mk Z : LargeEvenProj (LargeEvenSLGroup (Fin 6) F)) = 1 :=
    (QuotientGroup.eq_one_iff Z).mpr hZN
  exact hz1 (by rw [← hmkZ, hZ1])

theorem ggF4H4Psl64_no_embedding {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    {J : Type} [Group J] [Finite J] (ι : J →* LargeEvenProj (LargeEvenSLGroup (Fin 6) F))
    (hι : Function.Injective ι) (h13 : 13 ∣ Nat.card J) (h17 : 17 ∣ Nat.card J)
    (h3 : 3 ∣ Nat.card (Subgroup.center J)) : False := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 13 h13
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' 17 h17
  obtain ⟨zc, hzc⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center J) 3 h3
  have haord : orderOf (ι a) = 13 := by rw [orderOf_injective ι hι a, ha]
  have hbord : orderOf (ι b) = 17 := by rw [orderOf_injective ι hι b, hb]
  have hizord : orderOf (ι zc) = 3 := by
    rw [orderOf_injective ι hι (zc : J), Subgroup.orderOf_coe zc, hzc]
  have ha13 : (ι a) ^ 13 = 1 := by simpa [haord] using pow_orderOf_eq_one (ι a)
  have hb17 : (ι b) ^ 17 = 1 := by simpa [hbord] using pow_orderOf_eq_one (ι b)
  have hiz3 : (ι zc) ^ 3 = 1 := by simpa [hizord] using pow_orderOf_eq_one (ι zc)
  have ha1 : ι a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at haord
    omega
  have hb1 : ι b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hbord
    omega
  have hiz1 : ι zc ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hizord
    omega
  have hcz : ∀ g : J, g * (zc : J) = (zc : J) * g := Subgroup.mem_center_iff.1 zc.2
  have haz : ι a * ι zc = ι zc * ι a := by
    calc ι a * ι zc = ι (a * (zc : J)) := (map_mul ι a (zc : J)).symm
      _ = ι ((zc : J) * a) := by rw [hcz a]
      _ = ι zc * ι a := map_mul ι (zc : J) a
  have hbz : ι b * ι zc = ι zc * ι b := by
    calc ι b * ι zc = ι (b * (zc : J)) := (map_mul ι b (zc : J)).symm
      _ = ι ((zc : J) * b) := by rw [hcz b]
      _ = ι zc * ι b := map_mul ι (zc : J) b
  exact ggF4H4Psl64_no_commuting hF (ι a) (ι b) (ι zc) ha13 ha1 hb17 hb1 hiz3 hiz1 haz hbz

end CFSG.StandardType
