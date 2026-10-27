module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218BorelDiag
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Main
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankChevUni
import CFSG.RankThree.PartOne.K133.SylowKill
import CFSG.RankThree.PartOne.AUTSL.FieldExt
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvBasic
import CFSG.RankThree.CentralLiftU.UnitaryTorus
public import CFSG.LocalAnalysis.UniquenessCase.UC22P218c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup Matrix
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Quasithin.H13.Sec53F.Unit (borelAutDiag_u5 borelBase_u5 hypSU_ext' hypTorus_comm
  fieldAut fieldAut_apply mat_fieldHom fieldP fieldP_apply Eext finite_hypPSU_five)
open CFSG.RankThree.CentralLiftU (tcoord coe_tcoord_of_diag hypSU_eq_of_diag)

set_option linter.unusedSectionVars false

private theorem u5_five_not_dvd {s : ℕ} (hs : Odd s) : ¬ 5 ∣ 2 ^ s - 1 := by
  obtain ⟨k, rfl⟩ := hs
  have h4 : ∀ k : ℕ, 4 ^ k % 5 = 1 ∨ 4 ^ k % 5 = 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; omega
  have h2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [h2]
  have := h4 k
  generalize 4 ^ k = X at this ⊢
  omega

private theorem u5_pow_add_one_dvd (n : ℕ) : 2 ^ n + 1 ∣ 2 ^ (2 * n) - 1 := by
  have hfac : 2 ^ (2 * n) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have e : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [e]
    generalize 2 ^ n = x at h ⊢
    have h3 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ h
    zify [h, h3]
    ring
  exact Dvd.intro_left _ hfac.symm

private theorem u5_div_le_two {e : ℕ} (he : e ≠ 1) : 5 / e ≤ 2 := by
  rcases Nat.lt_or_ge e 2 with h | h
  · obtain rfl : e = 0 := by omega
    simp
  · calc 5 / e ≤ 5 / 2 := Nat.div_le_div_left h (by norm_num)
      _ = 2 := by norm_num

private theorem u5_orderOf_eq_two {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ q - 1)
    (hq : 1 ≤ q) : orderOf (-(q : ZMod p)) = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : (q : ZMod p) = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (q - 1) p).2 hpq
    rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at h
    exact h
  rw [hq1, orderOf_neg_one, ZMod.ringChar_zmod_n, if_neg hp2]

private theorem u5_orderOf_ne_one {p q : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q + 1) :
    orderOf (-(q : ZMod p)) ≠ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Ne, orderOf_eq_one_iff, neg_eq_iff_add_eq_zero]
  intro h
  apply hpq
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  exact h

private theorem u5_not_dvd_cofactor {r X : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hX : 1 ≤ X)
    (hrX : r ∣ X - 1) : ¬ r ∣ X ^ 10 * (X ^ 3 + 1) * (X ^ 2 + 1) * (X ^ 5 + 1) := by
  have : Fact r.Prime := ⟨hr⟩
  have hX1 : (X : ZMod r) = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (X - 1) r).2 hrX
    rw [Nat.cast_sub hX, Nat.cast_one, sub_eq_zero] at h
    exact h
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [hX1]
  norm_num
  intro h
  have h8 : ((8 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff, show (8 : ℕ) = 2 ^ 3 by norm_num] at h8
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h8))

section Model

variable {n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)

private theorem u5_mat_pow {t : ↥(hypSU h 2 1)} {v : HypIndex 2 1 → K}
    (hm : ((t : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = diagonal v)
    (k : ℕ) :
    (((t ^ k : ↥(hypSU h 2 1)) : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) = diagonal (v ^ k) := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hm, diagonal_pow]

private theorem u5_fieldAut_pow (τ : K ≃+* K) :
    ∃ j : ℕ, ∀ t ∈ hypTorus h 2 1, fieldAut h τ t = t ^ 2 ^ j := by
  have := h.finite
  have := h.charP
  obtain ⟨j, hj⟩ := CFSG.RankThree.PartOne.AUTSL.exists_ringEquiv_eq_pow_two τ
  refine ⟨j, fun t ht => ?_⟩
  obtain ⟨a, d, -, -, hm⟩ := ht
  apply hypSU_ext'
  rw [fieldAut_apply, mat_fieldHom, hm, u5_mat_pow h hm, diagonal_map (map_zero τ)]
  congr 1
  funext x
  exact hj _

private noncomputable def u5_coord : ↥(hypTorus h 2 1) →* Kˣ × Kˣ :=
  (tcoord (r := 2) (ε := 1) h 0).prod (tcoord (r := 2) (ε := 1) h 1)

private theorem u5_coord_eq {t : ↥(hypTorus h 2 1)} {a : Fin 2 → Kˣ} {d : Fin 1 → Kˣ}
    (hm : (((t : ↥(hypSU h 2 1)) : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) = diagonal (torusEntries h a d)) :
    u5_coord h t = (a 0, a 1) :=
  Prod.ext (Units.ext (coe_tcoord_of_diag h 0 hm)) (Units.ext (coe_tcoord_of_diag h 1 hm))

private theorem u5_torus_d {a : Fin 2 → Kˣ} {d : Fin 1 → Kˣ} (hp : torusRatio h a d = 1)
    (k : Fin 1) : (d k : K) = (∏ i, (a i : K) / h.bar (a i))⁻¹ := by
  rw [torusRatio] at hp
  have := eq_inv_of_mul_eq_one_right hp
  rw [Fin.prod_univ_one] at this
  rw [Fin.fin_one_eq_zero k]
  exact this

private theorem u5_coord_injective : Function.Injective (u5_coord h) := by
  intro t t' htt'
  obtain ⟨a, d, -, hp, hm⟩ := t.2
  obtain ⟨a', d', -, hp', hm'⟩ := t'.2
  rw [u5_coord_eq h hm, u5_coord_eq h hm'] at htt'
  have haa : a = a' := by
    funext i
    fin_cases i
    · exact (Prod.mk.inj htt').1
    · exact (Prod.mk.inj htt').2
  refine Subtype.ext (hypSU_eq_of_diag h hm hm' (fun x => ?_) (fun k => ?_))
  · simp only [torusEntries, haa]
  · simp only [torusEntries]
    rw [u5_torus_d h hp k, u5_torus_d h hp' k, haa]

private theorem u5_coord_surjective : Function.Surjective (u5_coord h) := by
  rintro ⟨u, v⟩
  have hbb : ∀ x : K, h.bar (h.bar x) = x := h.bar_bar
  have hu : (u : K) ≠ 0 := u.ne_zero
  have hv : (v : K) ≠ 0 := v.ne_zero
  have hu' : h.bar (u : K) ≠ 0 := by simp [hu]
  have hv' : h.bar (v : K) ≠ 0 := by simp [hv]
  let a : Fin 2 → Kˣ := ![u, v]
  let d : Fin 1 → Kˣ := fun _ => Units.map (h.bar : K →* K) (u * v) * (u * v)⁻¹
  have hd : ∀ k, h.norm (d k : K) = 1 := by
    intro k
    simp only [d, UnitaryFieldData.norm, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass,
      Units.val_inv_eq_inv_val, map_mul, map_inv₀, hbb]
    field_simp
  have hp : torusRatio h a d = 1 := by
    rw [torusRatio, Fin.prod_univ_two, Fin.prod_univ_one]
    simp only [a, d, Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_mul, Units.coe_map,
      MonoidHom.coe_ofClass, Units.val_inv_eq_inv_val, map_mul]
    field_simp
  obtain ⟨g, hg, hm⟩ := torusMat_mem_hypSU h a hd hp
  refine ⟨⟨g, hg⟩, ?_⟩
  rw [u5_coord_eq h hm]
  rfl

private noncomputable def u5_torusEquiv : ↥(hypTorus h 2 1) ≃* Kˣ × Kˣ :=
  MulEquiv.ofBijective (u5_coord h) ⟨u5_coord_injective h, u5_coord_surjective h⟩

private theorem u5_card_torus : Nat.card ↥(hypTorus h 2 1) = (2 ^ (2 * n) - 1) ^ 2 := by
  have := h.finite
  rw [Nat.card_congr (u5_torusEquiv h).toEquiv, Nat.card_prod, Nat.card_units, h.card, sq]

private theorem u5_torus_pow {t : ↥(hypSU h 2 1)} (ht : t ∈ hypTorus h 2 1) :
    t ^ (2 ^ (2 * n) - 1) = 1 := by
  have := h.finite
  have hK : Nat.card Kˣ = 2 ^ (2 * n) - 1 := by rw [Nat.card_units, h.card]
  have hc : ∀ x : Kˣ × Kˣ, x ^ (2 ^ (2 * n) - 1) = 1 := fun x => by
    refine Prod.ext ?_ ?_
    · rw [Prod.pow_fst, Prod.fst_one, ← hK]
      exact pow_card_eq_one'
    · rw [Prod.pow_snd, Prod.snd_one, ← hK]
      exact pow_card_eq_one'
  have h1 : (⟨t, ht⟩ : ↥(hypTorus h 2 1)) ^ (2 ^ (2 * n) - 1) = 1 :=
    u5_coord_injective h (by rw [map_pow, map_one]; exact hc _)
  simpa using congrArg Subtype.val h1

private theorem u5_exists_orderOf_torus {s : ℕ} (hsn : s ∣ n) :
    ∃ g : ↥(hypTorus h 2 1), orderOf g = 2 ^ s - 1 := by
  have := h.finite
  obtain ⟨u, hu⟩ := uc22p218c_exists_orderOf_units (K := K) (n := 2 * n) h.card
    (Dvd.dvd.mul_left hsn 2)
  obtain ⟨g, hg⟩ := u5_coord_surjective h (u, 1)
  refine ⟨g, ?_⟩
  rw [← orderOf_injective (u5_coord h) (u5_coord_injective h) g, hg, Prod.orderOf]
  simp [hu]

private theorem u5_orderOf_proj {y : ↥(hypSU h 2 1)}
    (hy : Nat.Coprime (orderOf y) (Nat.gcd 5 (2 ^ n + 1))) :
    orderOf (hypProj h 2 1 y) = orderOf y := by
  refine Nat.dvd_antisymm (orderOf_map_dvd _ _) ?_
  set m := orderOf (hypProj h 2 1 y) with hm
  have h1 : y ^ m ∈ hypScalars h 2 1 := by
    rw [← ker_hypProj, MonoidHom.mem_ker, map_pow]
    exact pow_orderOf_eq_one _
  have hZ : Nat.card (hypScalars h 2 1) = Nat.gcd 5 (2 ^ n + 1) :=
    card_hypScalars h (by norm_num)
  have h2 : (y ^ m) ^ Nat.gcd 5 (2 ^ n + 1) = 1 := by
    have := pow_card_eq_one' (G := ↥(hypScalars h 2 1)) (x := ⟨y ^ m, h1⟩)
    rw [hZ] at this
    simpa using congrArg Subtype.val this
  have h3 : orderOf y ∣ m * Nat.gcd 5 (2 ^ n + 1) := by
    apply orderOf_dvd_of_pow_eq_one
    rwa [pow_mul]
  exact hy.dvd_of_dvd_mul_right h3

private theorem u5_eq_one_of_mem_scalars {y : ↥(hypSU h 2 1)} {m : ℕ} (hy : y ∈ hypScalars h 2 1)
    (hym : y ^ m = 1) (hm : Nat.Coprime m (Nat.gcd 5 (2 ^ n + 1))) : y = 1 := by
  have hZ : Nat.card (hypScalars h 2 1) = Nat.gcd 5 (2 ^ n + 1) :=
    card_hypScalars h (by norm_num)
  have h1 : orderOf y ∣ Nat.card (hypScalars h 2 1) := by
    rw [← Subgroup.orderOf_mk y hy]
    exact orderOf_dvd_natCard _
  rw [hZ] at h1
  have h3 : orderOf y ∣ Nat.gcd m (Nat.gcd 5 (2 ^ n + 1)) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hym) h1
  rwa [Nat.Coprime.gcd_eq_one hm, Nat.dvd_one, orderOf_eq_one_iff] at h3

theorem uc22s218_u5_fieldBorelDiagData_model :
    FieldBorelDiagData n (2 ^ (2 * n) - 1) (hypProjUnitriangular h 2 1)
      ((hypTorus h 2 1).map (hypProj h 2 1)) (MonoidHom.range (fieldP h)) (Eext h) where
  borel := borelAutDiag_u5 h
  pow := by
    rintro _ ⟨τ, rfl⟩
    obtain ⟨j, hj⟩ := u5_fieldAut_pow h τ
    refine ⟨j, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    rw [fieldP_apply, hj t ht, map_pow]
  exp := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow, u5_torus_pow h ht, map_one]
  exists_d := fun hs hsn => by
    obtain ⟨g, hg⟩ := u5_exists_orderOf_torus h hsn
    have hc : Nat.Coprime (orderOf (g : ↥(hypSU h 2 1))) (Nat.gcd 5 (2 ^ n + 1)) := by
      rw [Subgroup.orderOf_coe, hg]
      exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 5 _)
        ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 (u5_five_not_dvd hs)).symm
    refine ⟨hypProj h 2 1 g, ⟨g, g.2, rfl⟩, ?_⟩
    rw [u5_orderOf_proj h hc, Subgroup.orderOf_coe, hg]

theorem uc22s218_u5_model_elemAbelian {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓK : ℓ ∣ 2 ^ (2 * n) - 1)
    (hcop : Nat.Coprime ℓ (Nat.gcd 5 (2 ^ n + 1))) :
    ∃ A : Subgroup (hypPSU h 2 1), A ≤ (hypTorus h 2 1).map (hypProj h 2 1) ∧
      IsElemAbelian ℓ A ∧ Nat.card A = ℓ ^ 2 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have := h.finite
  have hℓK' : ℓ ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card]
    exact hℓK
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) ℓ hℓK'
  have hz : ∀ a ∈ Subgroup.zpowers ζ, a ^ ℓ = 1 := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ← hζ,
      pow_orderOf_eq_one, _root_.one_zpow]
  obtain ⟨B, hBpow, hBcard⟩ : ∃ B : Subgroup (Kˣ × Kˣ), (∀ x ∈ B, x ^ ℓ = 1) ∧
      Nat.card B = ℓ ^ 2 := by
    refine ⟨(Subgroup.zpowers ζ).prod (Subgroup.zpowers ζ), fun x hx => ?_, ?_⟩
    · exact Prod.ext (hz _ (Subgroup.mem_prod.1 hx).1) (hz _ (Subgroup.mem_prod.1 hx).2)
    · rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Nat.card_zpowers, hζ,
        sq]
  let φ : Kˣ × Kˣ →* hypPSU h 2 1 :=
    ((hypProj h 2 1).comp (hypTorus h 2 1).subtype).comp (u5_torusEquiv h).symm.toMonoidHom
  have hφB : ∀ x ∈ B, φ x = 1 → x = 1 := by
    intro x hx hφ
    have h1 : (((u5_torusEquiv h).symm x : ↥(hypTorus h 2 1)) : ↥(hypSU h 2 1)) ∈
        hypScalars h 2 1 := by
      rw [← ker_hypProj, MonoidHom.mem_ker]
      exact hφ
    have h2 : (((u5_torusEquiv h).symm x : ↥(hypTorus h 2 1)) : ↥(hypSU h 2 1)) ^ ℓ = 1 := by
      have : (u5_torusEquiv h).symm x ^ ℓ = 1 := by rw [← map_pow, hBpow x hx, map_one]
      simpa using congrArg Subtype.val this
    have h3 := u5_eq_one_of_mem_scalars h h1 h2 hcop
    have h4 : (u5_torusEquiv h).symm x = 1 := Subtype.ext h3
    simpa using congrArg (u5_torusEquiv h) h4
  refine ⟨B.map φ, ?_, CFSG.SectionRank.isElemAbelian_map ⟨inferInstance, hBpow⟩ φ, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact ⟨_, ((u5_torusEquiv h).symm x).2, rfl⟩
  · have hinj : Function.Injective (φ.subgroupMap B) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker, Subtype.ext_iff, MonoidHom.subgroupMap_apply_coe,
        OneMemClass.coe_one] at hx
      exact (Subgroup.mem_bot).mpr (Subtype.ext (hφB _ x.2 hx))
    rw [← hBcard]
    exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, MonoidHom.subgroupMap_surjective φ B⟩)).symm

private theorem u5_card_hypSU_five (X : ℕ) (hX : X = 2 ^ n) :
    Nat.card (hypSU h 2 1) =
      (X ^ 2 - 1) ^ 2 * (X ^ 10 * (X ^ 3 + 1) * (X ^ 2 + 1) * (X ^ 5 + 1)) := by
  have h1 := (card_hypSU h (r := 2) (ε := 1) (by norm_num)).1
  subst hX
  have hX1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  generalize 2 ^ n = X at h1 hX1 ⊢
  have h2 : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ hX1
  rw [show Finset.Icc 2 (2 * 2 + 1) = {2, 3, 4, 5} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton] at h1
  zify [h2]
  rw [h1]
  norm_num
  ring

theorem uc22s218_u5_model_not_dvd_card_sylow {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr5 : r ≠ 5)
    (hrn : r ∣ 2 ^ n - 1) : ¬ r ∣ Nat.card (Sylow 2 (hypPSU h 2 1)) := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have hX1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  obtain ⟨-, -, -, -, ⟨P, hP⟩, -⟩ :=
    unitary_order_and_Sylow h (r := 2) (ε := 1) (by norm_num) (by norm_num)
  refine CFSG.RankThree.PartOne.K133.not_dvd_card_sylow_of_le_normalizer hr P
    ((hypTorus h 2 1).map (hypProj h 2 1)) ?_ ?_
  · have hH := (borelBase_u5 h).H_le
    rw [← hP] at hH
    exact hH
  · intro k hk
    have hZ : Nat.card (hypScalars h 2 1) = Nat.gcd 5 (2 ^ n + 1) :=
      card_hypScalars h (by norm_num)
    have hSk : r ^ k ∣ Nat.card (hypSU h 2 1) := hk.trans (Dvd.intro _ (card_hypPSU_mul h))
    rw [u5_card_hypSU_five h _ rfl] at hSk
    have hcop : Nat.Coprime (r ^ k) ((2 ^ n) ^ 10 * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 2 + 1) *
        ((2 ^ n) ^ 5 + 1)) :=
      Nat.Coprime.pow_left k
        ((Nat.Prime.coprime_iff_not_dvd hr).2 (u5_not_dvd_cofactor hr hr2 hX1 hrn))
    have hG : r ^ k ∣ ((2 ^ n) ^ 2 - 1) ^ 2 := hcop.dvd_of_dvd_mul_right hSk
    have hT : Nat.card ↥(hypTorus h 2 1) = ((2 ^ n) ^ 2 - 1) ^ 2 := by
      rw [u5_card_torus, ← pow_mul, mul_comm n 2]
    let g : ↥(hypTorus h 2 1) →* hypPSU h 2 1 := (hypProj h 2 1).comp (hypTorus h 2 1).subtype
    have hrange : g.range = (hypTorus h 2 1).map (hypProj h 2 1) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    let κ : g.ker →* ↥(hypScalars h 2 1) :=
      ((hypTorus h 2 1).subtype.comp g.ker.subtype).codRestrict (hypScalars h 2 1) (fun x => by
        have h1 : ((hypTorus h 2 1).subtype.comp g.ker.subtype) x ∈ (hypProj h 2 1).ker :=
          MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 x.2)
        rwa [ker_hypProj] at h1)
    have hκ : Function.Injective κ := fun x y hxy => by
      have h1 := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h1)
    have hkerdvd : Nat.card g.ker ∣ 5 := by
      have := Subgroup.card_dvd_of_injective κ hκ
      rw [hZ] at this
      exact this.trans (Nat.gcd_dvd_left 5 _)
    have hker : Nat.Coprime (r ^ k) (Nat.card g.ker) :=
      Nat.Coprime.coprime_dvd_right hkerdvd
        (Nat.Coprime.pow_left k ((Nat.coprime_primes hr (by norm_num)).2 hr5))
    have hmul := Subgroup.card_ker_mul_card_range g
    have h1 : r ^ k ∣ Nat.card g.ker * Nat.card g.range := by
      rw [hmul, hT]
      exact hG
    have h2 := hker.dvd_of_dvd_mul_left h1
    rwa [hrange] at h2

end Model

section Rank

theorem uc22s218_u5_exists_model {Y : Type} [Group Y] {n : ℕ} (hY : IsU5 Y n) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 n K), Nonempty (hypPSU h 2 1 ≃* Y) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hY (by decide)
  have h : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hadm.2.1, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
  exact ⟨K, inferInstance, h, ⟨(hypPSUEquivStatedProj h hR (by norm_num)).trans e.symm⟩⟩

theorem uc22s218_u5_fieldBorelDiag {Y : Type} [Group Y] {n : ℕ} (hY : IsU5 Y n) :
    FieldBorelDiag Y n (2 ^ (2 * n) - 1) := by
  obtain ⟨K, _, h, ⟨e⟩⟩ := uc22s218_u5_exists_model hY
  exact FieldBorelDiag.of_mulEquiv (Y := hypPSU h 2 1)
    ⟨_, _, _, _, uc22s218_u5_fieldBorelDiagData_model h⟩ e

theorem uc22s218_u5_torus {Y : Type} [Group Y] {n : ℕ} (hY : IsU5 Y n) :
    ∃ T : Subgroup Y, (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧
      ∀ ℓ : ℕ, ℓ.Prime → (ℓ ∣ 2 ^ (2 * n) - 1 ∧ ¬ (ℓ = 5 ∧ 5 ∣ 2 ^ n + 1)) →
        ∃ A : Subgroup Y, A ≤ T ∧ IsElemAbelian ℓ A ∧ Nat.card A = ℓ ^ 2 := by
  obtain ⟨K, _, h, ⟨e⟩⟩ := uc22s218_u5_exists_model hY
  refine ⟨((hypTorus h 2 1).map (hypProj h 2 1)).map e.toMonoidHom, ?_, fun ℓ hℓ hℓn => ?_⟩
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simp only [← map_mul, hypTorus_comm h hx hy]
  · have hcop : Nat.Coprime ℓ (Nat.gcd 5 (2 ^ n + 1)) := by
      by_cases hℓ5 : ℓ = 5
      · subst hℓ5
        have h5 : ¬ 5 ∣ 2 ^ n + 1 := fun hd => hℓn.2 ⟨rfl, hd⟩
        rw [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5)]
        exact Nat.coprime_one_right _
      · exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 5 _)
          ((Nat.coprime_primes hℓ (by norm_num)).2 hℓ5)
    obtain ⟨A, hAT, hAe, hAc⟩ := uc22s218_u5_model_elemAbelian h hℓ hℓn.1 hcop
    refine ⟨A.map e.toMonoidHom, Subgroup.map_mono hAT,
      CFSG.SectionRank.isElemAbelian_map hAe _, ?_⟩
    rw [Subgroup.card_map_of_injective e.injective, hAc]

theorem uc22s218_u5_pRank_eq_div {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsU5 Y n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp1 : ¬ p ∣ 2 ^ n + 1) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) = 5 / orderOf (-((2 ^ n : ℕ) : ZMod p)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hY (by decide)
  let := Fintype.ofFinite K
  have hpq : ¬ p ∣ 2 ^ n := fun hd =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  let S : Subgroup ↥(StatedSU 5 (2 ^ n) K) :=
    (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ n) K)
  have hSdvd : Nat.card S ∣ 2 ^ n + 1 :=
    (CFSG.LocalAnalysis.RankThreeUC.S15.RankChevUniProof.card_scalars_statedSU_dvd (F := K)
      (p := 2) (f := n) (m := 5) Nat.prime_two hK (by norm_num)).2
  have hSnot : ¬ p ∣ Nat.card S := fun hdiv => hp1 (hdiv.trans hSdvd)
  calc CFSG.Open.pRank p (⊤ : Subgroup Y)
      = CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ n) K))) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
    _ = CFSG.Open.pRank p (⊤ : Subgroup (↥(StatedSU 5 (2 ^ n) K) ⧸ S)) := rfl
    _ = CFSG.Open.pRank p (⊤ : Subgroup ↥(StatedSU 5 (2 ^ n) K)) :=
        CFSG.SectionRank.pRank_quotient_eq S hSnot
    _ = 5 / orderOf (-((2 ^ n : ℕ) : ZMod p)) :=
        CFSG.LocalAnalysis.RankThreeUC.S15.pRank_statedSU_of_not_dvd hp hp2
          (by rw [← Nat.card_eq_fintype_card, hK]) hpq hp1 5 (by norm_num)

theorem uc22s218_u5_pRank_le_two {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsU5 Y n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp1 : ¬ p ∣ 2 ^ n + 1) :
    CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2 := by
  rw [uc22s218_u5_pRank_eq_div hY hp hp2 hp1]
  exact u5_div_le_two (u5_orderOf_ne_one hp (by exact_mod_cast hp1))

theorem uc22s218_u5_pRank_eq_two {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsU5 Y n)
    {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) :
    CFSG.Open.pRank r (⊤ : Subgroup Y) = 2 := by
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd hs.pos hrs
  have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  have hr1 : ¬ r ∣ 2 ^ n + 1 := by
    intro hd
    have h2 : r ∣ 2 ^ n + 1 - (2 ^ n - 1) := Nat.dvd_sub hd hrn
    rw [show 2 ^ n + 1 - (2 ^ n - 1) = 2 by have := Nat.one_le_two_pow (n := n); omega] at h2
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
  have h5 := uc22s218_u5_pRank_eq_div hY hr hr2 hr1
  rw [u5_orderOf_eq_two hr hr2 hrn Nat.one_le_two_pow] at h5
  omega

theorem uc22s218_u5_not_dvd_card_sylow {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsU5 Y n)
    {s r : ℕ} (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) :
    ¬ r ∣ Nat.card (Sylow 2 Y) := by
  obtain ⟨K, _, h, ⟨e⟩⟩ := uc22s218_u5_exists_model hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  rw [← CFSG.ComponentClassification.AschbacherToolkit.Bender.card_sylow_eq_of_mulEquiv e 2]
  exact uc22s218_u5_model_not_dvd_card_sylow h hr (uc22p218c_ne_two_of_dvd hs.pos hrs)
    (fun h5 => u5_five_not_dvd hs (h5 ▸ hrs)) (hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn))

theorem torusFacts218_U5 {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hY : IsU5 Y n) :
    TorusFacts218 Y n (fun p => p ∣ 2 ^ (2 * n) - 1 ∧ ¬ (p = 5 ∧ 5 ∣ 2 ^ n + 1))
      (fun p => ¬ p ∣ 2 ^ (2 * n) - 1) :=
  torusFacts218_of_fieldBorelDiag (E := 2 ^ (2 * n) - 1) (uc22s218_u5_fieldBorelDiag hY)
    (fun hs hsn _ hrs =>
      ⟨hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (Dvd.dvd.mul_left hsn 2)),
        fun h5 => u5_five_not_dvd hs (h5.1 ▸ hrs)⟩)
    (fun _ _ hout => hout) (uc22s218_u5_torus hY)
    (fun hs hsn hr hrs => uc22s218_u5_pRank_eq_two hY hs hsn hr hrs)
    (fun hs hsn hr hrs => uc22s218_u5_not_dvd_card_sylow hY hs hsn hr hrs)
    (fun hp hp2 hout =>
      uc22s218_u5_pRank_le_two hY hp hp2 (fun hd => hout (hd.trans (u5_pow_add_one_dvd n))))

end Rank

end CFSG.LocalAnalysis.UniquenessCase.UC22
