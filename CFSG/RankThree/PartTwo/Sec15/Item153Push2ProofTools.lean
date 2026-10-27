module

public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec15.Item153PushProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15.Push153B

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.Semidihedral.Principal Equiv

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pow_mul_mem_of_mem {V Y : Subgroup G} (hYV : Y ≤ Subgroup.normalizer (V : Set G))
    {v y : G} (hv : v ∈ V) (hy : y ∈ Y) (k : ℕ) : (v * y) ^ k * (y ^ k)⁻¹ ∈ V := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : y ^ k * v * (y ^ k)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hYV (Y.pow_mem hy k)) v).mp hv
    have e : (v * y) ^ (k + 1) * (y ^ (k + 1))⁻¹ =
        ((v * y) ^ k * (y ^ k)⁻¹) * (y ^ k * v * (y ^ k)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact V.mul_mem ih hc

theorem exists_mem_inf_of_fixed {A Y : Subgroup G} (hAF : A ∈ partTwoF G)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {y : G} (hy : y ∈ Y)
    (hfix : ∀ a ∈ A, a * y * a⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y)
    (hy3 : y ^ 3 ∈ CFSG.Open.pCoreOf 2 Y) :
    ∃ a₀ ∈ A ⊓ Y, a₀ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set V := CFSG.Open.pCoreOf 2 Y with hVdef
  have hV2 : IsPGroup 2 V := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hVY : V ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hYV : Y ≤ Subgroup.normalizer (V : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hA3 : IsPGroup 3 ↥A := fun a => ⟨1, Subtype.ext (by simpa using hAF.1.2 a a.2)⟩
  let α : ↥A →* MulAut G := MulAut.conj.comp A.subtype
  have hcop : ¬ 3 ∣ Nat.card V := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV2
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  obtain ⟨c, hcV, hcfix⟩ := (coprime_invariant_coset_fixed 3 hA3 α V hcop y).1 (by
    intro a x hx
    change (a : G) * x * (a : G)⁻¹ * y⁻¹ ∈ V
    have h1 : (a : G) * (x * y⁻¹) * (a : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hAV a.2) _).mp hx
    have e : (a : G) * x * (a : G)⁻¹ * y⁻¹ =
        ((a : G) * (x * y⁻¹) * (a : G)⁻¹) * ((a : G) * y * (a : G)⁻¹ * y⁻¹) := by group
    rw [e]
    exact V.mul_mem h1 (hfix a a.2))
  have hcA : ∀ a ∈ A, a * c * a⁻¹ = c := fun a ha => hcfix ⟨a, ha⟩
  have hcY : c ∈ Y := by
    have : c = (c * y⁻¹) * y := by group
    rw [this]
    exact Y.mul_mem (hVY hcV) hy
  have hc3 : c ^ 3 ∈ V := by
    have h := pow_mul_mem_of_mem hYV hcV hy 3
    have e : c * y⁻¹ * y = c := by group
    rw [e] at h
    have e2 : c ^ 3 = (c ^ 3 * (y ^ 3)⁻¹) * y ^ 3 := by group
    rw [e2]
    exact V.mul_mem h hy3
  obtain ⟨k, hk⟩ := hV2 ⟨c ^ 3, hc3⟩
  have hk' : (c ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨m, hm⟩ : ∃ m, 4 ^ k = 3 * m + 1 := by
    have h4 : 4 ^ k % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    exact ⟨4 ^ k / 3, by omega⟩
  refine ⟨c ^ (3 * m + 1), ⟨?_, Y.pow_mem hcY _⟩, ?_⟩
  · apply mem_of_mem_partTwoF hAF
    · rw [← pow_mul, show (3 * m + 1) * 3 = 3 * (2 ^ k * 2 ^ k) by
        rw [← hm, ← mul_pow]; norm_num; ring, pow_mul, pow_mul, hk', one_pow]
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      have h := congrArg (· ^ (3 * m + 1)) (hcA a ha)
      simp only [conj_pow] at h
      calc c ^ (3 * m + 1) * a = a * (a⁻¹ * c ^ (3 * m + 1) * a) := by group
        _ = a * c ^ (3 * m + 1) := by
          congr 1
          have h' := congrArg (fun z => a⁻¹ * z * a) h
          rw [← h']
          group
  · have e : c ^ (3 * m + 1) * y⁻¹ = (c ^ 3) ^ m * (c * y⁻¹) := by
      rw [← pow_mul, pow_succ]
      group
    rw [e]
    exact V.mul_mem (V.pow_mem hc3 m) hcV

omit [Finite G] in
theorem mem_of_pow_three_of_mem_sup {Y S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSY : S ≤ Subgroup.normalizer (Y : Set G)) {x : G} (hx : x ∈ Y ⊔ S) {j : ℕ}
    (hxj : x ^ 3 ^ j = 1) : x ∈ Y := by
  obtain ⟨a, ha⟩ := Push153.exists_pow_two_mem_of_sup hS2 hSY hx
  have hcop : Nat.Coprime (2 ^ a) (orderOf x) := by
    have hd : orderOf x ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one hxj
    exact Nat.Coprime.coprime_dvd_right hd (Nat.Coprime.pow _ _ (by norm_num))
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← ht, ← pow_mul]
  rw [pow_mul]
  exact Y.pow_mem ha t

section Action

variable (Y : Subgroup G)

omit [Finite G] in
theorem pCore_mem_of_normalizer (g : ↥(Subgroup.normalizer (Y : Set G))) :
    ∀ m ∈ CFSG.pCore 2 ↥Y, Y.normalizerMonoidHom g m ∈ CFSG.pCore 2 ↥Y := by
  intro m hm
  have hfix := Subgroup.characteristic_iff_map_eq.mp (CFSG.pCore_characteristic (p := 2))
    (Y.normalizerMonoidHom g)
  rw [← hfix]
  exact Subgroup.mem_map_of_mem _ hm

omit [Finite G] in
@[expose] noncomputable def barAct : ↥(Subgroup.normalizer (Y : Set G)) →*
    MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
  CoprimeFixedPoint.quotientAction Y.normalizerMonoidHom (CFSG.pCore 2 ↥Y)
    (pCore_mem_of_normalizer Y)

omit [Finite G] in
theorem barAct_mem (y : G) (hy : y ∈ Y) :
    barAct Y ⟨y, Subgroup.le_normalizer hy⟩ = MulAut.conj (QuotientGroup.mk ⟨y, hy⟩) := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H z =>
    rw [barAct, CoprimeFixedPoint.quotientAction_mk, MulAut.conj_apply]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1

variable {n : ℕ} {Y} (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin n))
  (autE : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)))

omit [Finite G] in
@[expose] noncomputable def permAct : ↥(Subgroup.normalizer (Y : Set G)) →* Perm (Fin n) :=
  autE.symm.toMonoidHom.comp ((MulAut.congr φ).toMonoidHom.comp (barAct Y))

omit [Finite G] in
theorem permAct_mem (hautE : ∀ σ, autE σ = MulAut.conjNormal σ) (y : G) (hy : y ∈ Y) :
    permAct φ autE ⟨y, Subgroup.le_normalizer hy⟩ =
      ((φ (QuotientGroup.mk ⟨y, hy⟩) : alternatingGroup (Fin n)) : Perm (Fin n)) := by
  apply autE.injective
  rw [permAct, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, hautE, MulAut.conjNormal_val,
    barAct_mem Y y hy]
  refine MulEquiv.ext fun a => ?_
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

omit [Finite G] in
theorem permAct_eq_one_iff (hautE : ∀ σ, autE σ = MulAut.conjNormal σ) (y : G) (hy : y ∈ Y) :
    permAct φ autE ⟨y, Subgroup.le_normalizer hy⟩ = 1 ↔ y ∈ CFSG.Open.pCoreOf 2 Y := by
  rw [permAct_mem φ autE hautE y hy, OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff,
    QuotientGroup.eq_one_iff, Push153.mem_pCore_iff_mem_pCoreOf]

omit [Finite G] in
theorem exists_permAct_eq (hautE : ∀ σ, autE σ = MulAut.conjNormal σ) {z : Perm (Fin n)}
    (hz : z ∈ alternatingGroup (Fin n)) :
    ∃ (y : G) (hy : y ∈ Y), permAct φ autE ⟨y, Subgroup.le_normalizer hy⟩ = z := by
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (φ.symm ⟨z, hz⟩)
  refine ⟨w, w.2, ?_⟩
  rw [permAct_mem φ autE hautE _ w.2]
  have : (QuotientGroup.mk ⟨(w : G), w.2⟩ : ↥Y ⧸ CFSG.pCore 2 ↥Y) = φ.symm ⟨z, hz⟩ := hw
  rw [this, MulEquiv.apply_symm_apply]

end Action

end CFSG.RankThree.PartTwo.Sec15.Push153B
