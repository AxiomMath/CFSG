module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusOrderThree
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin (quadMinus)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

private noncomputable def sylowTorus0_T2J9a (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (u : Fˣ) : Gom (quadMinus 3 F b c) :=
  Classical.choose (exists_isTorusEl
    (commutator_orthogonalGroup_quadMinus_of_two_le (by norm_num) hirr)
    (stdP0 F b c) (Units.ne_zero u))

private theorem sylowTorus0_spec_T2J9a (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (u : Fˣ) : IsTorusEl (stdP0 F b c) (u : F) (sylowTorus0_T2J9a hirr u) :=
  Classical.choose_spec (exists_isTorusEl
    (commutator_orthogonalGroup_quadMinus_of_two_le (by norm_num) hirr)
    (stdP0 F b c) (Units.ne_zero u))

private noncomputable def sylowTorus1_T2J9a (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (u : Fˣ) : Gom (quadMinus 3 F b c) :=
  Classical.choose (exists_isTorusEl
    (commutator_orthogonalGroup_quadMinus_of_two_le (by norm_num) hirr)
    (stdP1 F b c) (Units.ne_zero u))

private theorem sylowTorus1_spec_T2J9a (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (u : Fˣ) : IsTorusEl (stdP1 F b c) (u : F) (sylowTorus1_T2J9a hirr u) :=
  Classical.choose_spec (exists_isTorusEl
    (commutator_orthogonalGroup_quadMinus_of_two_le (by norm_num) hirr)
    (stdP1 F b c) (Units.ne_zero u))

private theorem sylowTorus1_one_T2J9a (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    sylowTorus1_T2J9a (b := b) (c := c) hirr 1 = 1 := by
  refine IsTorusEl.unique ?_ (isTorusEl_one (stdP1 F b c))
  simpa using sylowTorus1_spec_T2J9a (b := b) (c := c) hirr 1

private noncomputable def sylowTau_T2J9a (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Fˣ × Fˣ →* Gom (quadMinus 3 F b c) :=
  MonoidHom.mk'
    (fun p => sylowTorus0_T2J9a hirr p.1 * sylowTorus1_T2J9a hirr p.2)
    (by
      rintro ⟨d0, d1⟩ ⟨e0, e1⟩
      have h0 : sylowTorus0_T2J9a hirr (d0 * e0) =
          sylowTorus0_T2J9a hirr d0 * sylowTorus0_T2J9a hirr e0 := by
        refine IsTorusEl.unique ?_ (IsTorusEl.mul
          (sylowTorus0_spec_T2J9a hirr d0) (sylowTorus0_spec_T2J9a hirr e0))
        simpa [Units.val_mul] using sylowTorus0_spec_T2J9a hirr (d0 * e0)
      have h1 : sylowTorus1_T2J9a hirr (d1 * e1) =
          sylowTorus1_T2J9a hirr d1 * sylowTorus1_T2J9a hirr e1 := by
        refine IsTorusEl.unique ?_ (IsTorusEl.mul
          (sylowTorus1_spec_T2J9a hirr d1) (sylowTorus1_spec_T2J9a hirr e1))
        simpa [Units.val_mul] using sylowTorus1_spec_T2J9a hirr (d1 * e1)
      have hc : sylowTorus0_T2J9a hirr e0 * sylowTorus1_T2J9a hirr d1 =
          sylowTorus1_T2J9a hirr d1 * sylowTorus0_T2J9a hirr e0 :=
        IsTorusEl.comm_of_orth (stdP0_orth_stdP1 F b c)
          (sylowTorus0_spec_T2J9a hirr e0) (sylowTorus1_spec_T2J9a hirr d1)
      rw [Prod.mk_mul_mk, h0, h1]
      calc
        (sylowTorus0_T2J9a hirr d0 * sylowTorus0_T2J9a hirr e0) *
            (sylowTorus1_T2J9a hirr d1 * sylowTorus1_T2J9a hirr e1)
            = sylowTorus0_T2J9a hirr d0 *
                (sylowTorus0_T2J9a hirr e0 * sylowTorus1_T2J9a hirr d1) *
                  sylowTorus1_T2J9a hirr e1 := by simp only [mul_assoc]
        _ = sylowTorus0_T2J9a hirr d0 *
                (sylowTorus1_T2J9a hirr d1 * sylowTorus0_T2J9a hirr e0) *
                  sylowTorus1_T2J9a hirr e1 := by rw [hc]
        _ = (sylowTorus0_T2J9a hirr d0 * sylowTorus1_T2J9a hirr d1) *
              (sylowTorus0_T2J9a hirr e0 * sylowTorus1_T2J9a hirr e1) := by
              simp only [mul_assoc])

private theorem sylowTau_apply_T2J9a (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (p : Fˣ × Fˣ) : sylowTau_T2J9a (b := b) (c := c) hirr p =
      sylowTorus0_T2J9a hirr p.1 * sylowTorus1_T2J9a hirr p.2 := rfl

private theorem sylowTorus0_eq_tau_T2J9a (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (u : Fˣ) : sylowTorus0_T2J9a hirr u = sylowTau_T2J9a hirr (u, 1) := by
  rw [sylowTau_apply_T2J9a, sylowTorus1_one_T2J9a, mul_one]

private theorem eq_one_of_smul_eq_self_T2J9a {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {v : V} (hv : v ≠ 0) {a : K} (h : a • v = v) : a = 1 := by
  have hzero : (a - 1) • v = 0 := by rw [sub_smul, h, one_smul, sub_self]
  rcases smul_eq_zero.mp hzero with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' hv

private theorem sylowTau_injective_T2J9a (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Function.Injective (sylowTau_T2J9a (b := b) (c := c) hirr) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨u, v⟩ h
  have hP0 : (sylowTorus1_T2J9a hirr v).app (stdP0 F b c).e = (stdP0 F b c).e :=
    (IsTorusEl.app_eq_of_orth (stdP0_orth_stdP1 F b c).symm
      (sylowTorus1_spec_T2J9a hirr v)).1
  have hP1 : (sylowTorus0_T2J9a hirr u).app (stdP1 F b c).e = (stdP1 F b c).e :=
    (IsTorusEl.app_eq_of_orth (stdP0_orth_stdP1 F b c)
      (sylowTorus0_spec_T2J9a hirr u)).1
  have hu : (u : F) • (stdP0 F b c).e = (stdP0 F b c).e := by
    have h' := congrArg (fun g : Gom (quadMinus 3 F b c) => g.app (stdP0 F b c).e) h
    rw [sylowTau_apply_T2J9a hirr (u, v)] at h'
    rw [Gom.app_mul, hP0, (sylowTorus0_spec_T2J9a hirr u).1, Gom.app_one] at h'
    exact h'
  have hv : (v : F) • (stdP1 F b c).e = (stdP1 F b c).e := by
    have h' := congrArg (fun g : Gom (quadMinus 3 F b c) => g.app (stdP1 F b c).e) h
    rw [sylowTau_apply_T2J9a hirr (u, v)] at h'
    rw [Gom.app_mul, (sylowTorus1_spec_T2J9a hirr v).1, Gom.map_smul, hP1,
      Gom.app_one] at h'
    exact h'
  have hu1 : u = 1 := by
    apply Units.ext
    exact eq_one_of_smul_eq_self_T2J9a (stdP0 F b c).e_ne_zero hu
  have hv1 : v = 1 := by
    apply Units.ext
    exact eq_one_of_smul_eq_self_T2J9a (stdP1 F b c).e_ne_zero hv
  ext
  · simpa using hu1
  · simpa using hv1

private theorem sylowTau_mem_pointStabilizer_T2J9a
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (p : Fˣ × Fˣ) :
    sylowTau_T2J9a hirr p ∈ pointStabilizer (quadMinus 3 F b c) (stdP0 F b c).e := by
  rw [mem_pointStabilizer]
  refine ⟨p.1, ?_⟩
  have hfix : (sylowTorus1_T2J9a hirr p.2).app (stdP0 F b c).e = (stdP0 F b c).e :=
    (IsTorusEl.app_eq_of_orth (stdP0_orth_stdP1 F b c).symm
      (sylowTorus1_spec_T2J9a hirr p.2)).1
  rw [sylowTau_apply_T2J9a hirr p]
  rw [Gom.app_mul, hfix, (sylowTorus0_spec_T2J9a hirr p.1).1]

private theorem sylowTau_comm_T2J9a (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (p q : Fˣ × Fˣ) : sylowTau_T2J9a hirr p * sylowTau_T2J9a hirr q =
      sylowTau_T2J9a hirr q * sylowTau_T2J9a hirr p := by
  rw [← map_mul, ← map_mul, mul_comm]

private theorem three_dvd_card_sub_one_T2J9a {n : ℕ} (hcard : Nat.card F = 2 ^ n)
    (hn : Even n) : 3 ∣ Nat.card F - 1 := by
  obtain ⟨m, rfl⟩ := hn
  have hn' : m + m = 2 * m := by omega
  rw [hcard, hn', pow_mul]
  change 3 ∣ 4 ^ m - 1
  have h4 : (4 : ℕ) ≡ 1 [MOD 3] := by decide
  have hpow : 4 ^ m ≡ 1 [MOD 3] := by simpa using h4.pow m
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow m 4 (by norm_num))).mp hpow.symm

private theorem three_dvd_card_units_T2J9a {n : ℕ} (hcard : Nat.card F = 2 ^ n)
    (hn : Even n) : 3 ∣ Nat.card Fˣ := by
  rw [Nat.card_units (α := F)]
  exact three_dvd_card_sub_one_T2J9a hcard hn

private theorem orderOf_torus0_T2J9a (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {ω₀ : Fˣ} (hω₀ : orderOf ω₀ = 3) :
    orderOf (sylowTorus0_T2J9a hirr ω₀) = 3 := by
  have hω₀3 : (ω₀ : Fˣ) ^ 3 = 1 := by simpa [hω₀] using pow_orderOf_eq_one ω₀
  have hpair : ((ω₀, 1) : Fˣ × Fˣ) ^ 3 = 1 := by ext <;> simp [hω₀3]
  have ht3 : (sylowTorus0_T2J9a hirr ω₀) ^ 3 = 1 := by
    rw [sylowTorus0_eq_tau_T2J9a, ← map_pow, hpair, map_one]
  have htne : sylowTorus0_T2J9a hirr ω₀ ≠ 1 := by
    intro h
    have happ : (sylowTorus0_T2J9a hirr ω₀).app (stdP0 F b c).e = (stdP0 F b c).e := by
      rw [h, Gom.app_one]
    rw [(sylowTorus0_spec_T2J9a hirr ω₀).1] at happ
    have hsm : (ω₀ : F) • (stdP0 F b c).e = (1 : F) • (stdP0 F b c).e := by
      simpa using happ
    have hcoef : (ω₀ : F) = 1 :=
      eq_one_of_smul_eq_self_T2J9a (stdP0 F b c).e_ne_zero (by simpa using hsm)
    have hω₀1 : ω₀ = 1 := Units.ext hcoef
    rw [hω₀1] at hω₀
    simp at hω₀
  exact orderOf_eq_prime ht3 htne

private theorem unit_cube_root_T2J9a {ω₀ : Fˣ} (hω₀ : orderOf ω₀ = 3) :
    (ω₀ : F) ^ 3 = 1 ∧ (ω₀ : F) ≠ 1 := by
  constructor
  · have h : (ω₀ : Fˣ) ^ 3 = 1 := by simpa [hω₀] using pow_orderOf_eq_one ω₀
    simpa using congrArg (fun x : Fˣ => (x : F)) h
  · intro h
    have h' : (ω₀ : Fˣ) = 1 := Units.ext h
    rw [h'] at hω₀
    simp at hω₀

private theorem sylow3_card_T2J9a (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : Even n) (S₃ : Sylow 3 (Fˣ × Fˣ)) :
    Nat.card ((S₃ : Subgroup (Fˣ × Fˣ)).map (sylowTau_T2J9a hirr)) =
      3 ^ (Nat.card (Gom (quadMinus 3 F b c))).factorization 3 := by
  have hcardH : Nat.card (Fˣ × Fˣ) = (Nat.card F - 1) * (Nat.card F - 1) := by
    rw [Nat.card_prod, Nat.card_units (α := F)]
  have hfacH : (Nat.card (Fˣ × Fˣ)).factorization 3 =
      2 * (Nat.card F - 1).factorization 3 := by
    rw [hcardH, ← pow_two, Nat.factorization_pow]
    simp
  calc
    Nat.card ((S₃ : Subgroup (Fˣ × Fˣ)).map (sylowTau_T2J9a hirr))
        = Nat.card (S₃ : Subgroup (Fˣ × Fˣ)) :=
      Subgroup.card_map_of_injective (sylowTau_injective_T2J9a hirr)
    _ = 3 ^ (Nat.card (Fˣ × Fˣ)).factorization 3 := Sylow.card_eq_multiplicity S₃
    _ = 3 ^ (Nat.card (Gom (quadMinus 3 F b c))).factorization 3 := by
      rw [hfacH, factorization_three_natCard_gom_quadMinus_three hirr hcard hn]

private theorem sylow3_zpowers_le_T2J9a (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (S₃ : Sylow 3 (Fˣ × Fˣ)) {ω₀ : Fˣ} (hω₀ : orderOf ω₀ = 3) :
    Subgroup.zpowers (sylowTorus0_T2J9a hirr ω₀) ≤
      (S₃ : Subgroup (Fˣ × Fˣ)).map (sylowTau_T2J9a hirr) := by
  let x0 : Fˣ × Fˣ := (ω₀, 1)
  have hx0ord : orderOf x0 = 3 := by
    rw [Prod.orderOf_mk]
    simp [x0, hω₀]
  have hzp : IsPGroup 3 (Subgroup.zpowers x0) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx0ord, pow_one])
  have hleS : Subgroup.zpowers x0 ≤ (S₃ : Subgroup (Fˣ × Fˣ)) :=
    IsPGroup.le_sylow_of_normal hzp S₃
  have hmaple : (Subgroup.zpowers x0).map (sylowTau_T2J9a hirr) ≤
      (S₃ : Subgroup (Fˣ × Fˣ)).map (sylowTau_T2J9a hirr) :=
    Subgroup.map_mono hleS
  have hmapEq : (Subgroup.zpowers x0).map (sylowTau_T2J9a hirr) =
      Subgroup.zpowers (sylowTorus0_T2J9a hirr ω₀) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    dsimp [x0]
    rw [sylowTau_apply_T2J9a, sylowTorus1_one_T2J9a, mul_one]
  rwa [hmapEq] at hmaple

private theorem sylow3_comm_T2J9a (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (S₃ : Sylow 3 (Fˣ × Fˣ)) :
    ∀ x ∈ (S₃ : Subgroup (Fˣ × Fˣ)).map (sylowTau_T2J9a hirr),
      ∀ y ∈ (S₃ : Subgroup (Fˣ × Fˣ)).map (sylowTau_T2J9a hirr), x * y = y * x := by
  intro x hx y hy
  obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨q, -, rfl⟩ := Subgroup.mem_map.mp hy
  exact sylowTau_comm_T2J9a hirr p q

private theorem sylow3_le_pointStabilizer_T2J9a (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (S₃ : Sylow 3 (Fˣ × Fˣ)) :
    (S₃ : Subgroup (Fˣ × Fˣ)).map (sylowTau_T2J9a hirr) ≤
      pointStabilizer (quadMinus 3 F b c) (stdP0 F b c).e := by
  intro x hx
  obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp hx
  exact sylowTau_mem_pointStabilizer_T2J9a hirr p

theorem exists_sylow3_torus (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : Even n) :
    ∃ (B P₃ : Subgroup (Gom (quadMinus 3 F b c))) (t : Gom (quadMinus 3 F b c)) (ω : F),
      ω ^ 3 = 1 ∧ ω ≠ 1 ∧ IsTorusEl (stdP0 F b c) ω t ∧ B = Subgroup.zpowers t ∧
      Nat.card B = 3 ∧ B ≤ P₃ ∧ CFSG.ABGLocalTools.IsSylowOf 3 P₃ ⊤ ∧
      (∀ x ∈ P₃, ∀ y ∈ P₃, x * y = y * x) ∧
      P₃ ≤ pointStabilizer (quadMinus 3 F b c) (stdP0 F b c).e := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨ω₀, hω₀⟩ := exists_prime_orderOf_dvd_card' 3
    (three_dvd_card_units_T2J9a hcard hn)
  let t : Gom (quadMinus 3 F b c) := sylowTorus0_T2J9a hirr ω₀
  have hspec : IsTorusEl (stdP0 F b c) (ω₀ : F) t := sylowTorus0_spec_T2J9a hirr ω₀
  have htord : orderOf t = 3 := orderOf_torus0_T2J9a hirr hω₀
  let S₃ : Sylow 3 (Fˣ × Fˣ) := default
  let B : Subgroup (Gom (quadMinus 3 F b c)) := Subgroup.zpowers t
  let P₃ : Subgroup (Gom (quadMinus 3 F b c)) :=
    (S₃ : Subgroup (Fˣ × Fˣ)).map (sylowTau_T2J9a hirr)
  have hcube := unit_cube_root_T2J9a hω₀
  have htcard : Nat.card B = 3 := by
    rw [show B = Subgroup.zpowers t from rfl, Nat.card_zpowers, htord]
  have hBle : B ≤ P₃ := by
    simpa [B, P₃, t] using sylow3_zpowers_le_T2J9a hirr S₃ hω₀
  have hcardP : Nat.card P₃ =
      3 ^ (Nat.card (Gom (quadMinus 3 F b c))).factorization 3 :=
    sylow3_card_T2J9a hirr hcard hn S₃
  have hSylow : CFSG.ABGLocalTools.IsSylowOf 3 P₃ ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_of_card (K := ⊤) le_top
      (by simpa [Subgroup.card_top] using hcardP)
  exact ⟨B, P₃, t, (ω₀ : F), hcube.1, hcube.2, hspec, rfl, htcard, hBle, hSylow,
    sylow3_comm_T2J9a hirr S₃, sylow3_le_pointStabilizer_T2J9a hirr S₃⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

end
