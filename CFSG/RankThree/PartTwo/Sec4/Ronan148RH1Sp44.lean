module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1A8
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherSp44

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projSp)

namespace Sp44

open CFSG.GH74.Uniqueness.SU.SU5 (F4c)
open CFSG.GH74.Uniqueness.SU.SU5.F4c (z0 z1 w w2 equivGF)
open Matrix

abbrev S : Type := ↥(CFSG.Open.StatedSp 2 (GaloisField 2 2))

abbrev ι : Type := Fin 2 ⊕ Fin 2

@[expose] noncomputable def Φ : Matrix ι ι (GaloisField 2 2) ≃+* Matrix ι ι F4c :=
  equivGF.symm.mapMatrix

@[expose] noncomputable def toM : S →* Matrix ι ι F4c :=
  (Φ.toMonoidHom.comp (Units.coeHom (Matrix ι ι (GaloisField 2 2)))).comp
    (CFSG.Open.StatedSp 2 (GaloisField 2 2)).subtype

theorem toM_apply (a : S) :
    toM a = Φ (((a : GL ι (GaloisField 2 2))) : Matrix ι ι (GaloisField 2 2)) := rfl

theorem toM_injective : Function.Injective toM := by
  intro a b e
  rw [toM_apply, toM_apply] at e
  exact Subtype.ext (Units.ext (Φ.injective e))

theorem toM_inv_of {a : S} {A Ai : Matrix ι ι F4c} (h : toM a = A) (hA : A * Ai = 1) :
    toM a⁻¹ = Ai := by
  calc toM a⁻¹ = toM a⁻¹ * (A * Ai) := by rw [hA, mul_one]
    _ = toM (a⁻¹ * a) * Ai := by rw [map_mul, h, mul_assoc]
    _ = Ai := by rw [inv_mul_cancel, map_one, one_mul]

@[expose] def spJ : Matrix ι ι F4c := fromBlocks 0 1 (-1) 0

@[expose] def sG1 : Matrix ι ι F4c := diagonal (Sum.elim ![w, z1] ![w2, z1])

@[expose] def sG1i : Matrix ι ι F4c := diagonal (Sum.elim ![w2, z1] ![w, z1])

@[expose] def sG2 : Matrix ι ι F4c := diagonal (Sum.elim ![z1, w] ![z1, w2])

@[expose] def sG2i : Matrix ι ι F4c := diagonal (Sum.elim ![z1, w2] ![z1, w])

@[expose] def rσ : ι → ι
  | .inl i => if i = 0 then .inr 1 else .inl 0
  | .inr i => if i = 0 then .inl 1 else .inr 0

@[expose] def sR : Matrix ι ι F4c := Matrix.of fun i j => if i = rσ j then 1 else 0

@[expose] def sRi : Matrix ι ι F4c := Matrix.of fun i j => if rσ i = j then 1 else 0

theorem sG1_mul : sG1 * sG1i = 1 := by decide +kernel
theorem sG1_mul' : sG1i * sG1 = 1 := by decide +kernel
theorem sG2_mul : sG2 * sG2i = 1 := by decide +kernel
theorem sG2_mul' : sG2i * sG2 = 1 := by decide +kernel
theorem sR_mul : sR * sRi = 1 := by decide +kernel
theorem sR_mul' : sRi * sR = 1 := by decide +kernel

theorem sG1_sp : sG1ᵀ * spJ * sG1 = spJ := by decide +kernel
theorem sG2_sp : sG2ᵀ * spJ * sG2 = spJ := by decide +kernel
theorem sR_sp : sRᵀ * spJ * sR = spJ := by decide +kernel

theorem sG1_pow : sG1 ^ 3 = 1 := by decide +kernel
theorem sG2_pow : sG2 ^ 3 = 1 := by decide +kernel
theorem sG12 : sG1 * sG2 = sG2 * sG1 := by decide +kernel
theorem sG1_ne : sG1 ≠ 1 := by decide +kernel
theorem sG2_ne : sG2 ≠ 1 := by decide +kernel
theorem sG2_ne_G1 : sG2 ≠ sG1 := by decide +kernel
theorem sG2_ne_G1i : sG2 ≠ sG1i := by decide +kernel

theorem sR_G1 : sR * sG1 * sRi = sG2 ^ 2 := by decide +kernel

theorem sR_G2 : sR * sG2 * sRi = sG1 := by decide +kernel

noncomputable def mkS (M Mi : Matrix ι ι F4c) (h1 : M * Mi = 1) (h2 : Mi * M = 1)
    (hs : Mᵀ * spJ * M = spJ) : S :=
  ⟨Matrix.GeneralLinearGroup.map equivGF.toRingHom ⟨M, Mi, h1, h2⟩,
    CFSG.Open.StatedAPI.map_mem_statedSp equivGF.toRingHom
      (CFSG.Open.StatedAPI.mem_statedSp_iff.mpr hs)⟩

theorem toM_mkS (M Mi : Matrix ι ι F4c) (h1 : M * Mi = 1) (h2 : Mi * M = 1)
    (hs : Mᵀ * spJ * M = spJ) : toM (mkS M Mi h1 h2 hs) = M := by
  ext i j
  rw [toM_apply]
  show equivGF.symm (Matrix.GeneralLinearGroup.map equivGF.toRingHom ⟨M, Mi, h1, h2⟩ i j) = M i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact equivGF.symm_apply_apply (M i j)

noncomputable def g1S : S := mkS sG1 sG1i sG1_mul sG1_mul' sG1_sp

noncomputable def g2S : S := mkS sG2 sG2i sG2_mul sG2_mul' sG2_sp

noncomputable def rS : S := mkS sR sRi sR_mul sR_mul' sR_sp

theorem toM_g1 : toM g1S = sG1 := toM_mkS _ _ _ _ _
theorem toM_g2 : toM g2S = sG2 := toM_mkS _ _ _ _ _
theorem toM_r : toM rS = sR := toM_mkS _ _ _ _ _

theorem g1S_pow : g1S ^ 3 = 1 := toM_injective (by rw [map_pow, toM_g1, sG1_pow, map_one])
theorem g2S_pow : g2S ^ 3 = 1 := toM_injective (by rw [map_pow, toM_g2, sG2_pow, map_one])
theorem g12S : g1S * g2S = g2S * g1S :=
  toM_injective (by rw [map_mul, map_mul, toM_g1, toM_g2, sG12])
theorem g1S_ne : g1S ≠ 1 := fun h => sG1_ne (by rw [← toM_g1, h, map_one])
theorem g2S_ne : g2S ≠ 1 := fun h => sG2_ne (by rw [← toM_g2, h, map_one])
theorem g2S_ne_g1S : g2S ≠ g1S := fun h => sG2_ne_G1 (by rw [← toM_g1, ← toM_g2, h])
theorem g2S_ne_g1S_inv : g2S ≠ g1S⁻¹ := fun h =>
  sG2_ne_G1i (by rw [← toM_inv_of toM_g1 sG1_mul, ← toM_g2, h])

theorem rS_g1 : rS * g1S * rS⁻¹ = g2S ^ 2 :=
  toM_injective (by rw [map_mul, map_mul, toM_inv_of toM_r sR_mul, toM_r, toM_g1, map_pow, toM_g2,
    sR_G1])

theorem rS_g2 : rS * g2S * rS⁻¹ = g1S :=
  toM_injective (by rw [map_mul, map_mul, toM_inv_of toM_r sR_mul, toM_r, toM_g1, toM_g2, sR_G2])

@[expose] noncomputable def E0 : Subgroup S := Subgroup.zpowers g1S ⊔ Subgroup.zpowers g2S

theorem e9_E0 : CFSG.Assembly.IsElemAbelian 3 E0 ∧ Nat.card E0 = 9 :=
  e9_of_commute g1S_pow g1S_ne g2S_pow g12S
    (not_mem_zpowers_of_ne g1S_pow g2S_ne g2S_ne_g1S g2S_ne_g1S_inv)

theorem mem_E0 {x : S} (hx : x ∈ E0) :
    ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ x = g1S ^ i * g2S ^ j := by
  have hc : ∀ u ∈ Subgroup.zpowers g1S, ∀ v ∈ Subgroup.zpowers g2S, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((show Commute g1S g2S from g12S).zpow_zpow i j).eq
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc).2
  have hx' : x ∈ ((Subgroup.zpowers g1S ⊔ Subgroup.zpowers g2S : Subgroup _) : Set _) := hx
  rw [hset] at hx'
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hx'
  have hpow : ∀ (c : S), c ^ 3 = 1 → ∀ w ∈ Subgroup.zpowers c,
      ∃ k : ℕ, k < 3 ∧ w = c ^ k := by
    intro c hc3 w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    refine ⟨(k % 3).toNat, by omega, ?_⟩
    have h1 : c ^ k = c ^ (k % 3) := zpow_eq_zpow_emod' k hc3
    rw [h1, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
  obtain ⟨i, hi, rfl⟩ := hpow g1S g1S_pow u hu
  obtain ⟨j, hj, rfl⟩ := hpow g2S g2S_pow v hv
  exact ⟨i, j, hi, hj, rfl⟩

theorem rS_mem_normalizer : rS ∈ Subgroup.normalizer (E0 : Set S) := by
  refine mem_normalizer_of_map_le ?_
  rw [E0, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  refine sup_le ?_ ?_ <;> rw [Subgroup.zpowers_le]
  · show rS * g1S * rS⁻¹ ∈ Subgroup.zpowers g1S ⊔ Subgroup.zpowers g2S
    rw [rS_g1]
    exact Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers g2S) 2)
  · show rS * g2S * rS⁻¹ ∈ Subgroup.zpowers g1S ⊔ Subgroup.zpowers g2S
    rw [rS_g2]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers g1S)

theorem rS_not_mem (i j : ℕ) (h1 : sR * (sG1 ^ i * sG2 ^ j) * sRi ≠ 1)
    (h2 : sR * (sG1 ^ i * sG2 ^ j) * sRi ≠ sG1 ^ i * sG2 ^ j)
    (h3 : sR * (sG1 ^ i * sG2 ^ j) * sRi ≠ (sG1 ^ i * sG2 ^ j) ^ 2) :
    rS ∉ Subgroup.normalizer (Subgroup.zpowers (g1S ^ i * g2S ^ j) : Set S) := by
  have ht : toM (g1S ^ i * g2S ^ j) = sG1 ^ i * sG2 ^ j := by
    rw [map_mul, map_pow, map_pow, toM_g1, toM_g2]
  have hc : toM (rS * (g1S ^ i * g2S ^ j) * rS⁻¹) = sR * (sG1 ^ i * sG2 ^ j) * sRi := by
    rw [map_mul, map_mul, ht, toM_r, toM_inv_of toM_r sR_mul]
  have hmem : g1S ^ i * g2S ^ j ∈ E0 :=
    mul_mem (Subgroup.mem_sup_left (pow_mem (Subgroup.mem_zpowers g1S) i))
      (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers g2S) j))
  have ht3 : (g1S ^ i * g2S ^ j) ^ 3 = 1 := e9_E0.1.2 _ hmem
  have hti : (g1S ^ i * g2S ^ j)⁻¹ = (g1S ^ i * g2S ^ j) ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact ht3)
  refine not_mem_normalizer_of_conj (not_mem_zpowers_of_ne ht3 ?_ ?_ ?_)
  · intro h
    exact h1 (by rw [← hc, h, map_one])
  · intro h
    exact h2 (by rw [← hc, h, ht])
  · intro h
    exact h3 (by rw [← hc, h, hti, map_pow, ht])

theorem sp44_move (s : S) (hs : s ∈ E0) (hs1 : s ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (E0 : Set S),
      n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set S) := by
  obtain ⟨i, j, hi, hj, rfl⟩ := mem_E0 hs
  interval_cases i <;> interval_cases j
  · exact absurd (by simp) hs1
  all_goals exact ⟨rS, rS_mem_normalizer,
    rS_not_mem _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

theorem e9Move_S : E9Move S :=
  e9Move_of_sylow Item434SmallTwoOther.factorization_card_sp44 e9_E0.2 sp44_move

noncomputable def projEquiv : projSp 2 (GaloisField 2 2) ≃* S :=
  Item434SmallTwoOther.sp44Equiv

theorem card_projSp : Nat.card (projSp 2 (GaloisField 2 2)) = 979200 :=
  (Nat.card_congr projEquiv.toEquiv).trans Item434SmallTwoOther.card_sp44

theorem e9Move_projSp44 : E9Move (projSp 2 (GaloisField 2 2)) :=
  e9Move_S.of_mulEquiv projEquiv

theorem rankTwo_projSp44 : RankTwoData (projSp 2 (GaloisField 2 2)) := by
  haveI : Finite (projSp 2 (GaloisField 2 2)) :=
    Nat.finite_of_card_ne_zero (by rw [card_projSp]; norm_num)
  refine ⟨cubeInner_of_mulEquiv projEquiv fun τ hτ =>
    Item434SmallTwoOther.mem_range_conj_of_pow_three_sp44 τ hτ, fun E hE => ?_, ?_⟩
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hp : IsPGroup 3 E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 _ g.2)⟩
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    have hd : 3 ^ k ∣ Nat.card (projSp 2 (GaloisField 2 2)) :=
      hk ▸ Subgroup.card_subgroup_dvd_card E
    rw [hk]
    have : k ≤ 2 := by
      by_contra h
      push Not at h
      have h27 : 3 ^ 3 ∣ Nat.card (projSp 2 (GaloisField 2 2)) := (Nat.pow_dvd_pow 3 h).trans hd
      rw [card_projSp] at h27
      norm_num at h27
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
      _ = 9 := by norm_num
  · refine ⟨E0.map projEquiv.symm.toMonoidHom, isElemAbelian_map _ e9_E0.1, ?_⟩
    rw [Subgroup.card_map_of_injective projEquiv.symm.injective, e9_E0.2]

theorem sp44_orderChecks :
    (∀ q, 2 ≤ q → q ^ 3 ∣ 979200 →
      979200 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ∧
    (∀ q, 2 ≤ q → q ^ 3 ∣ 979200 →
      979200 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :=
  orderChecks_of_bound (B := 20) (by norm_num) (by decide +kernel)

end Sp44

open Sp44

section Row



theorem rowOf427_sp44
    : RowOf427 (projSp 2 (GaloisField 2 2)) := by
  haveI : Finite (projSp 2 (GaloisField 2 2)) :=
    Nat.finite_of_card_ne_zero (by rw [card_projSp]; norm_num)
  refine rowOf427_of_e9Move ?_ rankTwo_projSp44
    (fun S _ _ ⟨e⟩ => e9Move_projSp44.of_mulEquiv e) (by rw [card_projSp]; norm_num)
  intro L _ _ hSL hL hZ3 ⟨e'⟩
  exact center_eq_bot_of_card hSL hL hZ3 ((Nat.card_congr e'.toEquiv).trans card_projSp)
    sp44_orderChecks.1 sp44_orderChecks.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
