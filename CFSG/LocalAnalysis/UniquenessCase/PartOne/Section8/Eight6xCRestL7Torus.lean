module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestL7Weyl
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestL7F3
public import CFSG.RankThree.PartOne.KLR.TorusGeneric

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.TrialityL7

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Lattice

open scoped Matrix


section TorusBasics

open scoped Matrix

private theorem trialityM_mulVec_l7t (x : Fin TwistTag.D4.tag.rank → ℤ) :
    trialityM *ᵥ x = permLattice TwistTag.D4.perm x :=
  (permLattice_eq_trialityM_mulVec x).symm

private theorem smul_trialityM_mulVec_l7t (eps : ℤ)
    (y : Fin TwistTag.D4.tag.rank → ℤ) :
    (eps • trialityM) *ᵥ y = eps • (trialityM *ᵥ y) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

private theorem twEps_smul_eq_l7t {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) (x : Fin TwistTag.D4.tag.rank → ℤ) :
    twEps eps • x = eps • x := by
  have h := twEps_smul_permLattice heps (permLattice TwistTag.D4.perm.symm x)
  have h1 : (eps • trialityM) *ᵥ permLattice TwistTag.D4.perm.symm x = eps • x := by
    rw [smul_trialityM_mulVec_l7t, trialityM_mulVec_l7t,
      permLattice_permLattice_symm]
  rw [h1, permLattice_permLattice_symm] at h
  exact h

private theorem twEps_inv_smul_eq_l7t {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) (x : Fin TwistTag.D4.tag.rank → ℤ) :
    (twEps eps)⁻¹ • x = eps • x := by
  have h := twEps_smul_eq_l7t heps ((twEps eps)⁻¹ • x)
  rw [smul_smul, mul_inv_cancel, one_smul] at h
  have heps2 : eps * eps = 1 := by rcases heps with rfl | rfl <;> norm_num
  have h' : eps • x = (twEps eps)⁻¹ • x := by
    calc eps • x = eps • (eps • ((twEps eps)⁻¹ • x)) := by rw [h.symm]
      _ = (twEps eps)⁻¹ • x := by rw [smul_smul, heps2, one_smul]
  exact h'.symm

private theorem weylTuple_twEps_l7t {L : Type} [Field L]
    {eps : ℤ} (heps : eps = 1 ∨ eps = -1) (c : Fin TwistTag.D4.tag.rank → Lˣ)
    (i : Fin TwistTag.D4.tag.rank) :
    weylTuple (twEps eps) c i = c i ^ eps := by
  rw [weylTuple, twEps_inv_smul_eq_l7t heps, rootChar_zsmul, CTTorus.rootChar_single]

end TorusBasics


section TorusCoords

private theorem trialityM_mulVec_single_l7t2 (j : Fin TwistTag.D4.tag.rank) :
    trialityM *ᵥ (Pi.single j (1 : ℤ)) =
      Pi.single (TwistTag.D4.perm j) (1 : ℤ) := by
  fin_cases j <;> funext i <;> fin_cases i <;> decide +kernel

private theorem three_pow_a_dvd_q_sub_eps_l7t2 {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {eps : ℤ} (heps : eps = 1 ∨ eps = -1) {a : ℕ}
    (ha : a = padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps))) :
    (3 : ℤ) ^ a ∣ (p : ℤ) ^ f - eps := by
  have hq_ne : (p : ℤ) ^ f - eps ≠ 0 := by
    have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    have hpow : (1 : ℤ) < (p : ℤ) ^ f := by
      calc (1 : ℤ) < (p : ℤ) := by linarith
        _ ≤ (p : ℤ) ^ f := le_self_pow₀ (by linarith) (by omega)
    rcases heps with rfl | rfl <;> linarith
  have hdiv : (3 : ℕ) ^ a ∣ Int.natAbs ((p : ℤ) ^ f - eps) := by
    rw [ha]
    exact pow_padicValNat_dvd
  have hdiv' : (3 : ℤ) ^ a ∣ ((Int.natAbs ((p : ℤ) ^ f - eps)) : ℤ) := by
    rw [show (3 : ℤ) ^ a = ((3 : ℕ) ^ a : ℤ) by norm_num]
    exact Int.natCast_dvd_natCast.mpr hdiv
  simpa using Int.natAbs_dvd.mpr hdiv'

private theorem three_pow_succ_dvd_q_cube_sub_eps_l7t2 {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    {eps : ℤ} (heps : eps = 1 ∨ eps = -1) (hq : (p : ZMod 3) ^ f = (eps : ZMod 3)) {a : ℕ}
    (ha : a = padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps))) :
    (3 : ℤ) ^ (a + 1) ∣ (p : ℤ) ^ (3 * f) - eps := by
  have h_dvd_sub : (3 : ℤ) ^ a ∣ (p : ℤ) ^ f - eps :=
    three_pow_a_dvd_q_sub_eps_l7t2 hp hf heps ha
  have hq_mod : (p : ZMod 3) ^ f = (eps : ZMod 3) := hq
  have h_dvd_sum : (3 : ℤ) ∣ (p : ℤ) ^ (2 * f) + eps * (p : ℤ) ^ f + 1 := by
    change ((3 : ℕ) : ℤ) ∣ (p : ℤ) ^ (2 * f) + eps * (p : ℤ) ^ f + 1
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    have h2 : (p : ZMod 3) ^ (2 * f) = (eps : ZMod 3) ^ 2 := by
      rw [show 2 * f = f * 2 by ring, pow_mul, hq_mod]
    rw [h2, hq_mod]
    rcases heps with rfl | rfl <;> decide
  have h_factor : (p : ℤ) ^ (3 * f) - eps =
      ((p : ℤ) ^ f - eps) * ((p : ℤ) ^ (2 * f) + eps * (p : ℤ) ^ f + 1) := by
    rcases heps with rfl | rfl <;> ring
  rw [h_factor, show (3 : ℤ) ^ (a + 1) = (3 : ℤ) ^ a * 3 by rw [pow_succ]]
  exact mul_dvd_mul h_dvd_sub h_dvd_sum

private theorem fixedCharTuples_iff_basis_l7t2 {L : Type} [Field L] (ε : ℤ) {Fr : L →+* L}
    {b : Fin TwistTag.D4.tag.rank → Lˣ} :
    b ∈ fixedCharTuples (ε • trialityM) Fr ↔
      ∀ j, b (TwistTag.D4.perm j) ^ ε = Units.map Fr.toMonoidHom (b j) := by
  constructor
  · intro hb j
    have h := mem_fixedCharTuples_iff.1 hb (Pi.single j (1 : ℤ))
    rw [Matrix.smul_mulVec, trialityM_mulVec_single_l7t2, rootChar_zsmul,
      CTTorus.rootChar_single, CTTorus.rootChar_single] at h
    exact h
  · intro hb u
    have h' : ∀ j, rootChar b ((ε • trialityM) *ᵥ (Pi.single j (1 : ℤ))) =
        Units.map Fr.toMonoidHom (rootChar b (Pi.single j (1 : ℤ))) := by
      intro j
      rw [Matrix.smul_mulVec, trialityM_mulVec_single_l7t2, rootChar_zsmul,
        CTTorus.rootChar_single, CTTorus.rootChar_single]
      exact hb j
    have hu : u = ∑ j, u j • (Pi.single j (1 : ℤ) : Fin TwistTag.D4.tag.rank → ℤ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    have hu' : (ε • trialityM) *ᵥ u =
        ∑ j, u j • ((ε • trialityM) *ᵥ (Pi.single j (1 : ℤ))) := by
      nth_rewrite 1 [hu]
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul]
    calc
      rootChar b ((ε • trialityM) *ᵥ u)
          = rootChar b (∑ j, u j • ((ε • trialityM) *ᵥ (Pi.single j (1 : ℤ)))) := by
              rw [hu']
      _ = ∏ j, rootChar b (u j • ((ε • trialityM) *ᵥ (Pi.single j (1 : ℤ)))) := by
              rw [rootChar_sum]
      _ = ∏ j, (rootChar b ((ε • trialityM) *ᵥ (Pi.single j (1 : ℤ)))) ^ u j := by
              apply Finset.prod_congr rfl
              intro j _
              rw [rootChar_zsmul]
      _ = ∏ j, (Units.map Fr.toMonoidHom (rootChar b (Pi.single j (1 : ℤ)))) ^ u j := by
              apply Finset.prod_congr rfl
              intro j _
              rw [h' j]
      _ = Units.map Fr.toMonoidHom (∏ j, (rootChar b (Pi.single j (1 : ℤ))) ^ u j) := by
              rw [map_prod]
              apply Finset.prod_congr rfl
              intro j _
              rw [map_zpow]
      _ = Units.map Fr.toMonoidHom (rootChar b u) := by
              congr 1
              rw [rootChar]
              apply Finset.prod_congr rfl
              intro j _
              rw [CTTorus.rootChar_single]

private noncomputable def psiTuple_l7t2 {L : Type} [Field L] {a p f : ℕ}
    (eps : ℤ) (f1 : Multiplicative (ZMod (3 ^ (a + 1))) →* Lˣ)
    (f2 : Multiplicative (ZMod (3 ^ a)) →* Lˣ) :
    (Multiplicative (ZMod (3 ^ (a + 1))) × Multiplicative (ZMod (3 ^ a))) →*
      (Fin TwistTag.D4.tag.rank → Lˣ) where
  toFun x := fun j =>
    if j = (0 : Fin TwistTag.D4.tag.rank) then f1 x.1
    else if j = (1 : Fin TwistTag.D4.tag.rank) then (f1 x.1) ^ (eps * (p : ℤ) ^ f)
    else if j = (2 : Fin TwistTag.D4.tag.rank) then f2 x.2
    else (f1 x.1) ^ (((p : ℤ) ^ f) ^ 2)
  map_one' := by
    funext j
    fin_cases j <;> simp
  map_mul' := by
    intro x y
    funext j
    fin_cases j <;> split_ifs <;> simp_all [mul_zpow]

private theorem zmod_pow_eq_one_l7t2 {L : Type} [Field L] {n : ℕ} {ζ : Lˣ} (hζ : ζ ^ n = 1)
    (f : Multiplicative (ZMod n) →* Lˣ)
    (hf : ∀ i : ZMod n, f (Multiplicative.ofAdd i) = ζ ^ i.val) :
    ∀ i, f i ^ n = 1 := by
  intro i
  rw [show i = Multiplicative.ofAdd i.toAdd from rfl, hf]
  rw [← pow_mul, mul_comm (Multiplicative.toAdd i).val n, pow_mul, hζ, one_pow]

private theorem psiTuple_mem_l7t2 {L : Type} [Field L] {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) {eps : ℤ} (heps : eps = 1 ∨ eps = -1)
    (hq : (p : ZMod 3) ^ f = (eps : ZMod 3)) {a : ℕ}
    (ha : a = padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps))) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ (p ^ f))
    (f1 : Multiplicative (ZMod (3 ^ (a + 1))) →* Lˣ)
    (f2 : Multiplicative (ZMod (3 ^ a)) →* Lˣ)
    (hf1_pow : ∀ i, f1 i ^ (3 ^ (a + 1)) = 1)
    (hf2_pow : ∀ i, f2 i ^ (3 ^ a) = 1)
    (x : Multiplicative (ZMod (3 ^ (a + 1))) × Multiplicative (ZMod (3 ^ a))) :
    psiTuple_l7t2 (p := p) (f := f) eps f1 f2 x ∈ fixedCharTuples (eps • trialityM) Fr := by
  rw [fixedCharTuples_iff_basis_l7t2]
  intro j
  fin_cases j
  · change ((f1 x.1) ^ (eps * (p : ℤ) ^ f)) ^ eps =
      Units.map Fr.toMonoidHom (f1 x.1)
    rw [CTTorus.map_units_eq_pow hFr, ← zpow_mul]
    rw [← zpow_natCast (a := f1 x.1)]
    congr 1
    rw [Nat.cast_pow]
    set q : ℤ := (p : ℤ) ^ f with hq_def
    rcases heps with rfl | rfl <;> ring
  · change ((f1 x.1) ^ (((p : ℤ) ^ f) ^ 2)) ^ eps =
      Units.map Fr.toMonoidHom ((f1 x.1) ^ (eps * (p : ℤ) ^ f))
    rw [CTTorus.map_units_eq_pow hFr]
    rw [← zpow_mul]
    rw [← zpow_natCast (a := (f1 x.1) ^ (eps * (p : ℤ) ^ f)), ← zpow_mul]
    congr 1
    rw [Nat.cast_pow]
    set q : ℤ := (p : ℤ) ^ f with hq_def
    ring
  · change (f2 x.2) ^ eps = Units.map Fr.toMonoidHom (f2 x.2)
    rw [CTTorus.map_units_eq_pow hFr]
    exact CFSG.RankThree.PartOne.KLR.zpow_eq_zpow_of_modEq (hf2_pow x.2)
      (Int.modEq_iff_dvd.mpr (three_pow_a_dvd_q_sub_eps_l7t2 hp hf heps ha))
  · change (f1 x.1) ^ eps =
      Units.map Fr.toMonoidHom ((f1 x.1) ^ (((p : ℤ) ^ f) ^ 2))
    rw [CTTorus.map_units_eq_pow hFr]
    rw [← zpow_natCast (a := (f1 x.1) ^ (((p : ℤ) ^ f) ^ 2)), ← zpow_mul]
    have hdvd := three_pow_succ_dvd_q_cube_sub_eps_l7t2 hp hf heps hq ha
    have hdvd' : ((3 ^ (a + 1) : ℕ) : ℤ) ∣
        eps - (((p : ℤ) ^ f) ^ 2 * (p : ℤ) ^ f) := by
      have hq3 : (((p : ℤ) ^ f) ^ 2 * (p : ℤ) ^ f) = (p : ℤ) ^ (3 * f) := by
        rw [show 3 * f = f * 2 + f by ring, pow_add, pow_mul]
      rw [show eps - (((p : ℤ) ^ f) ^ 2 * (p : ℤ) ^ f) =
        -((p : ℤ) ^ (3 * f) - eps) by rw [hq3]; ring]
      exact dvd_neg.mpr hdvd
    exact CFSG.RankThree.PartOne.KLR.zpow_eq_zpow_of_modEq (hf1_pow x.1)
      (Int.modEq_iff_dvd.mpr hdvd').symm

private theorem surj_of_zmodEquivZPowers_l7t2 {L : Type} [Field L] {n : ℕ} (hn : n ≠ 0) {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ n)
    (f : Multiplicative (ZMod n) →* Lˣ)
    (hf : f = (Subgroup.zpowers ζ).subtype.comp
      (AddEquiv.toMultiplicativeLeft hζ.zmodEquivZPowers).toMonoidHom) :
    ∀ y : Lˣ, y ^ n = 1 → ∃ i : Multiplicative (ZMod n), f i = y := by
  have : NeZero n := ⟨hn⟩
  intro y hy
  have hζL : IsPrimitiveRoot (ζ : L) n := IsPrimitiveRoot.coe_units_iff.2 hζ
  have hyL : (y : L) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, hy, Units.val_one]
  obtain ⟨k, hk, hk'⟩ := hζL.eq_pow_of_pow_eq_one hyL
  have hyk : y = ζ ^ k := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact hk'.symm
  refine ⟨Multiplicative.ofAdd (k : ZMod n), ?_⟩
  rw [hf]
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  change ↑(Additive.toMul (hζ.zmodEquivZPowers (k : ZMod n))) = y
  rw [hζ.zmodEquivZPowers_apply_coe_nat k]
  simp
  exact hyk.symm

private theorem inj_of_zmodEquivZPowers_l7t2 {L : Type} [Field L] {n : ℕ} {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ n)
    (f : Multiplicative (ZMod n) →* Lˣ)
    (hf : f = (Subgroup.zpowers ζ).subtype.comp
      (AddEquiv.toMultiplicativeLeft hζ.zmodEquivZPowers).toMonoidHom) :
    Function.Injective f := by
  rw [hf]
  exact Subtype.val_injective.comp
    (AddEquiv.toMultiplicativeLeft hζ.zmodEquivZPowers).injective

private theorem gcd_three_pow_l7t2 {n : ℕ} (hn : n ≠ 0) {a : ℕ}
    (ha : a = padicValNat 3 n) :
    Nat.gcd (3 ^ (a + 1)) n = 3 ^ a := by
  have hdvd : 3 ^ a ∣ n := by
    rw [ha]
    exact pow_padicValNat_dvd
  have hndvd : ¬ (3 ^ (a + 1) ∣ n) := by
    rw [ha]
    exact pow_succ_padicValNat_not_dvd hn
  obtain ⟨k, hk_le, hk_eq⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).1 (Nat.gcd_dvd_left _ _)
  have h3a_dvd_gcd : 3 ^ a ∣ Nat.gcd (3 ^ (a + 1)) n :=
    Nat.dvd_gcd (pow_dvd_pow 3 (Nat.le_succ a)) hdvd
  have hk_ge : a ≤ k := by
    rw [hk_eq] at h3a_dvd_gcd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp h3a_dvd_gcd
  have hk_le_a : k ≤ a := by
    rcases Nat.lt_or_ge k (a + 1) with h | h
    · omega
    · exfalso
      apply hndvd
      have hk_eq_a1 : k = a + 1 := le_antisymm hk_le h
      rw [← hk_eq_a1, ← hk_eq]
      exact Nat.gcd_dvd_right _ _
  rw [hk_eq, le_antisymm hk_le_a hk_ge]

private theorem torsion_second_l7t2 {L : Type} [Field L] {p f : ℕ}
    {b : Fin TwistTag.D4.tag.rank → Lˣ} {Fr : L →+* L}
    (hp : p.Prime) (hf : 1 ≤ f) {eps : ℤ} (heps : eps = 1 ∨ eps = -1)
    (hq : (p : ZMod 3) ^ f = (eps : ZMod 3)) {a : ℕ}
    (ha : a = padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps)))
    (hFr : ∀ c, Fr c = c ^ (p ^ f))
    (hrel : ∀ j, b (TwistTag.D4.perm j) ^ eps = Units.map Fr.toMonoidHom (b j))
    (hb_pow : b ^ (3 ^ (a + 1)) = 1) :
    b 2 ^ (3 ^ a) = 1 := by
  have h2 : b 2 ^ eps = Units.map Fr.toMonoidHom (b 2) := by
    have h := hrel 2
    rw [show TwistTag.D4.perm (2 : Fin TwistTag.D4.tag.rank) = 2 from rfl] at h
    exact h
  have hq_ne : (p : ℤ) ^ f - eps ≠ 0 := by
    have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
    have hpow : (1 : ℤ) < (p : ℤ) ^ f := by
      calc (1 : ℤ) < (p : ℤ) := by linarith
        _ ≤ (p : ℤ) ^ f := le_self_pow₀ (by linarith) (by omega)
    rcases heps with rfl | rfl <;> linarith
  have hmod : eps ≡ (p : ℤ) ^ f [ZMOD (orderOf (b 2) : ℤ)] := by
    apply zpow_eq_zpow_iff_modEq.mp
    rw [h2, CTTorus.map_units_eq_pow hFr, ← zpow_natCast (a := b 2)]
    congr 1
  have hdvd_int : (orderOf (b 2) : ℤ) ∣ (p : ℤ) ^ f - eps :=
    Int.modEq_iff_dvd.mp hmod
  have hb2_pow : b 2 ^ (3 ^ (a + 1)) = 1 := congrFun hb_pow 2
  have hdvd_3 : orderOf (b 2) ∣ 3 ^ (a + 1) := orderOf_dvd_of_pow_eq_one hb2_pow
  have hdvd_nat : orderOf (b 2) ∣ Int.natAbs ((p : ℤ) ^ f - eps) := by
    rw [← Int.natAbs_natCast (orderOf (b 2))]
    exact Int.natAbs_dvd_natAbs.mpr hdvd_int
  have hgcd : Nat.gcd (3 ^ (a + 1)) (Int.natAbs ((p : ℤ) ^ f - eps)) = 3 ^ a :=
    gcd_three_pow_l7t2 (Int.natAbs_ne_zero.mpr hq_ne) ha
  have hdvd_gcd : orderOf (b 2) ∣ Nat.gcd (3 ^ (a + 1)) (Int.natAbs ((p : ℤ) ^ f - eps)) :=
    Nat.dvd_gcd hdvd_3 hdvd_nat
  rw [hgcd] at hdvd_gcd
  exact (orderOf_dvd_iff_pow_eq_one).mp hdvd_gcd

private theorem coord_relations_l7t2 {L : Type} [Field L] {p f : ℕ}
    {b : Fin TwistTag.D4.tag.rank → Lˣ}
    {Fr : L →+* L} {eps : ℤ} (heps : eps = 1 ∨ eps = -1)
    (hFr : ∀ c, Fr c = c ^ (p ^ f))
    (hrel : ∀ j, b (TwistTag.D4.perm j) ^ eps = Units.map Fr.toMonoidHom (b j))
    {w : Lˣ} (hw : b 0 = w) :
    b 1 = w ^ (eps * ((p : ℤ) ^ f)) ∧ b 3 = w ^ ((((p : ℤ) ^ f)) ^ 2) := by
  set q : ℤ := (p : ℤ) ^ f with hq_def
  have hq_cast : ((p ^ f : ℕ) : ℤ) = q := by rw [hq_def, Nat.cast_pow]
  have hsq : eps * eps = 1 := by rcases heps with rfl | rfl <;> ring
  have hsq2 : eps ^ 2 = 1 := by rw [sq, hsq]
  have hinj : Function.Injective (fun x : Lˣ => x ^ eps) := by
    intro x y hxy
    calc x = (x ^ eps) ^ eps := by rw [← zpow_mul, hsq, zpow_one]
      _ = (y ^ eps) ^ eps := congrArg (fun z => z ^ eps) hxy
      _ = y := by rw [← zpow_mul, hsq, zpow_one]
  have h0 : b 1 ^ eps = Units.map Fr.toMonoidHom (b 0) := by
    have h := hrel 0
    rw [show TwistTag.D4.perm (0 : Fin TwistTag.D4.tag.rank) = 1 from rfl] at h
    exact h
  have hb1 : b 1 = w ^ (eps * q) := by
    apply hinj
    change b 1 ^ eps = (w ^ (eps * q)) ^ eps
    rw [h0, CTTorus.map_units_eq_pow hFr, hw]
    rw [← zpow_natCast (a := w), hq_cast]
    rw [← zpow_mul]
    congr 1
    rw [show (eps * q) * eps = eps ^ 2 * q by ring]
    rw [hsq2]
    ring
  have h1 : b 3 ^ eps = Units.map Fr.toMonoidHom (b 1) := by
    have h := hrel 1
    rw [show TwistTag.D4.perm (1 : Fin TwistTag.D4.tag.rank) = 3 from rfl] at h
    exact h
  have hb3 : b 3 = w ^ (q ^ 2) := by
    apply hinj
    change b 3 ^ eps = (w ^ (q ^ 2)) ^ eps
    rw [h1, CTTorus.map_units_eq_pow hFr, hb1]
    rw [← zpow_natCast (a := w ^ (eps * q)), hq_cast]
    rw [← zpow_mul, ← zpow_mul]
    congr 1
    rw [show (eps * q) * q = q ^ 2 * eps by ring]
  exact ⟨by simpa [hq_def] using hb1, by simpa [hq_def] using hb3⟩

private theorem mem_range_psiTuple_l7t2 {L : Type} [Field L]
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {eps : ℤ} (heps : eps = 1 ∨ eps = -1)
    (hq : (p : ZMod 3) ^ f = (eps : ZMod 3)) {a : ℕ}
    (ha : a = padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps))) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ (p ^ f))
    (f1 : Multiplicative (ZMod (3 ^ (a + 1))) →* Lˣ)
    (f2 : Multiplicative (ZMod (3 ^ a)) →* Lˣ)
    (hf1_surj : ∀ y : Lˣ, y ^ (3 ^ (a + 1)) = 1 → ∃ i, f1 i = y)
    (hf2_surj : ∀ y : Lˣ, y ^ (3 ^ a) = 1 → ∃ i, f2 i = y)
    {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (hb : b ∈ fixedCharTuples (eps • trialityM) Fr)
    (hb_pow : b ^ (3 ^ (a + 1)) = 1) :
    ∃ x, psiTuple_l7t2 (p := p) (f := f) eps f1 f2 x = b := by
  have hrel := (fixedCharTuples_iff_basis_l7t2 eps).1 hb
  have hb0 : b 0 ^ (3 ^ (a + 1)) = 1 := congrFun hb_pow 0
  have hb2 : b 2 ^ (3 ^ a) = 1 :=
    torsion_second_l7t2 hp hf heps hq ha hFr hrel hb_pow
  obtain ⟨x1, hx1⟩ := hf1_surj (b 0) hb0
  obtain ⟨x2, hx2⟩ := hf2_surj (b 2) hb2
  obtain ⟨hb1, hb3⟩ := coord_relations_l7t2 heps hFr hrel hx1.symm
  refine ⟨(x1, x2), ?_⟩
  funext j
  fin_cases j
  · change f1 x1 = b 0
    exact hx1
  · change f1 x1 ^ (eps * (p : ℤ) ^ f) = b 1
    exact hb1.symm
  · change f2 x2 = b 2
    exact hx2
  · change f1 x1 ^ (((p : ℤ) ^ f) ^ 2) = b 3
    exact hb3.symm

private theorem psiTuple_pow_l7t2 {L : Type} [Field L] {p f a : ℕ} {eps : ℤ}
    (f1 : Multiplicative (ZMod (3 ^ (a + 1))) →* Lˣ)
    (f2 : Multiplicative (ZMod (3 ^ a)) →* Lˣ)
    (hf1_pow : ∀ i, f1 i ^ (3 ^ (a + 1)) = 1)
    (hf2_pow : ∀ i, f2 i ^ (3 ^ a) = 1)
    (x : Multiplicative (ZMod (3 ^ (a + 1))) × Multiplicative (ZMod (3 ^ a))) :
    psiTuple_l7t2 (p := p) (f := f) eps f1 f2 x ^ (3 ^ (a + 1)) = 1 := by
  funext j
  fin_cases j
  · change f1 x.1 ^ (3 ^ (a + 1)) = 1
    exact hf1_pow x.1
  · change ((f1 x.1) ^ (eps * (p : ℤ) ^ f)) ^ (3 ^ (a + 1)) = 1
    rw [← zpow_natCast (a := (f1 x.1) ^ (eps * (p : ℤ) ^ f)), ← zpow_mul]
    have hdvd : ((3 ^ (a + 1) : ℕ) : ℤ) ∣
        (eps * (p : ℤ) ^ f) * ((3 ^ (a + 1) : ℕ) : ℤ) - 0 := by
      simp
    have h := CFSG.RankThree.PartOne.KLR.zpow_eq_zpow_of_modEq (hf1_pow x.1)
      (Int.modEq_iff_dvd.mpr hdvd).symm
    simpa using h
  · change f2 x.2 ^ (3 ^ (a + 1)) = 1
    change f2 x.2 ^ (3 ^ a * 3) = 1
    rw [pow_mul, hf2_pow, one_pow]
  · change ((f1 x.1) ^ (((p : ℤ) ^ f) ^ 2)) ^ (3 ^ (a + 1)) = 1
    rw [← zpow_natCast (a := (f1 x.1) ^ (((p : ℤ) ^ f) ^ 2)), ← zpow_mul]
    have hdvd : ((3 ^ (a + 1) : ℕ) : ℤ) ∣
        (((p : ℤ) ^ f) ^ 2) * ((3 ^ (a + 1) : ℕ) : ℤ) - 0 := by
      simp
    have h := CFSG.RankThree.PartOne.KLR.zpow_eq_zpow_of_modEq (hf1_pow x.1)
      (Int.modEq_iff_dvd.mpr hdvd).symm
    simpa using h

private theorem psi_inj_l7t2 {L : Type} [Field L] {p f a : ℕ}
    {eps : ℤ} (f1 : Multiplicative (ZMod (3 ^ (a + 1))) →* Lˣ)
    (f2 : Multiplicative (ZMod (3 ^ a)) →* Lˣ)
    (hf1_inj : Function.Injective f1) (hf2_inj : Function.Injective f2) :
    Function.Injective ((rootDiagUnitHom TwistTag.D4.tag L).comp
      (psiTuple_l7t2 (p := p) (f := f) eps f1 f2)) := by
  intro x y hxy
  have h1 : psiTuple_l7t2 (p := p) (f := f) eps f1 f2 x =
      psiTuple_l7t2 (p := p) (f := f) eps f1 f2 y :=
    rootDiagUnit_injective hxy
  have h2 : f1 x.1 = f1 y.1 := by
    have := congrFun h1 0
    simpa [psiTuple_l7t2] using this
  have h3 : f2 x.2 = f2 y.2 := by
    have := congrFun h1 2
    simpa [psiTuple_l7t2] using this
  exact Prod.ext (hf1_inj h2) (hf2_inj h3)

private theorem psi_range_sub_l7t2 {L : Type} [Field L]
    [IsAlgClosed L] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {eps : ℤ} (heps : eps = 1 ∨ eps = -1)
    (hq : (p : ZMod 3) ^ f = (eps : ZMod 3)) {a : ℕ}
    (ha : a = padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps))) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ (p ^ f))
    (f1 : Multiplicative (ZMod (3 ^ (a + 1))) →* Lˣ)
    (f2 : Multiplicative (ZMod (3 ^ a)) →* Lˣ)
    (hf1_pow : ∀ i, f1 i ^ (3 ^ (a + 1)) = 1)
    (hf2_pow : ∀ i, f2 i ^ (3 ^ a) = 1) :
    ∀ t, t ∈ ((rootDiagUnitHom TwistTag.D4.tag L).comp
        (psiTuple_l7t2 (p := p) (f := f) eps f1 f2)).range →
      t ∈ twistedTorusOf (canonicalRep (coxeterSystem TwistTag.D4.tag) L (twEps eps))
          (twistHom TwistTag.D4 L Fr) ∧ t ^ (3 ^ (a + 1)) = 1 := by
  rintro t ⟨x, rfl⟩
  have hmem : psiTuple_l7t2 (p := p) (f := f) eps f1 f2 x ∈
      fixedCharTuples (eps • trialityM) Fr :=
    psiTuple_mem_l7t2 hp hf heps hq ha hFr f1 f2 hf1_pow hf2_pow x
  refine ⟨?_, ?_⟩
  · rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedTorusOf_twistHom_eq_map
      TwistTag.D4 Fr (twEps eps) (eps • trialityM)
      (fun x => twEps_smul_permLattice heps x)]
    exact ⟨_, hmem, rfl⟩
  · change ((rootDiagUnitHom TwistTag.D4.tag L)
      ((psiTuple_l7t2 (p := p) (f := f) eps f1 f2) x)) ^ (3 ^ (a + 1)) = 1
    rw [← map_pow, psiTuple_pow_l7t2 f1 f2 hf1_pow hf2_pow x, map_one]

private theorem psi_range_sup_l7t2 {L : Type} [Field L]
    [IsAlgClosed L] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {eps : ℤ} (heps : eps = 1 ∨ eps = -1)
    (hq : (p : ZMod 3) ^ f = (eps : ZMod 3)) {a : ℕ}
    (ha : a = padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps))) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ (p ^ f))
    (f1 : Multiplicative (ZMod (3 ^ (a + 1))) →* Lˣ)
    (f2 : Multiplicative (ZMod (3 ^ a)) →* Lˣ)
    (hf1_surj : ∀ y : Lˣ, y ^ (3 ^ (a + 1)) = 1 → ∃ i, f1 i = y)
    (hf2_surj : ∀ y : Lˣ, y ^ (3 ^ a) = 1 → ∃ i, f2 i = y) :
    ∀ t, t ∈ twistedTorusOf (canonicalRep (coxeterSystem TwistTag.D4.tag) L (twEps eps))
        (twistHom TwistTag.D4 L Fr) ∧ t ^ (3 ^ (a + 1)) = 1 →
      t ∈ ((rootDiagUnitHom TwistTag.D4.tag L).comp
        (psiTuple_l7t2 (p := p) (f := f) eps f1 f2)).range := by
  rintro t ⟨htw, hpow⟩
  rw [CFSG.HardMathSupport.Timmesfeld.CrossChar.twistedTorusOf_twistHom_eq_map
    TwistTag.D4 Fr (twEps eps) (eps • trialityM)
    (fun x => twEps_smul_permLattice heps x)] at htw
  obtain ⟨b, hb, rfl⟩ := htw
  have hbpow : b ^ (3 ^ (a + 1)) = 1 := by
    apply rootDiagUnit_injective
    change (rootDiagUnitHom TwistTag.D4.tag L) (b ^ 3 ^ (a + 1)) =
      (rootDiagUnitHom TwistTag.D4.tag L) 1
    rw [map_pow, hpow, map_one]
  obtain ⟨x, hx⟩ := mem_range_psiTuple_l7t2 hp hf heps hq ha hFr f1 f2
    hf1_surj hf2_surj hb hbpow
  refine ⟨x, ?_⟩
  change (rootDiagUnitHom TwistTag.D4.tag L) ((psiTuple_l7t2 (p := p) (f := f) eps f1 f2) x) =
    (rootDiagUnitHom TwistTag.D4.tag L) b
  exact congrArg (rootDiagUnitHom TwistTag.D4.tag L) hx

private theorem zmod_hom_pow_l7t2 {L : Type} [Field L] {n : ℕ} [NeZero n] {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ n)
    (f : Multiplicative (ZMod n) →* Lˣ)
    (hf : f = (Subgroup.zpowers ζ).subtype.comp
      (AddEquiv.toMultiplicativeLeft hζ.zmodEquivZPowers).toMonoidHom) :
    ∀ i, f i ^ n = 1 := by
  apply zmod_pow_eq_one_l7t2 hζ.pow_eq_one
  intro i
  rw [hf]
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  change ↑(Additive.toMul (hζ.zmodEquivZPowers i)) = ζ ^ i.val
  rw [← ZMod.natCast_zmod_val i, hζ.zmodEquivZPowers_apply_coe_nat i.val]
  simp

end TorusCoords

theorem exists_torusCoords {L : Type} [Field L] [IsAlgClosed L]
    (h3 : (3 : L) ≠ 0)
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (p ^ f))
    {eps : ℤ} (heps : eps = 1 ∨ eps = -1) (hq : (p : ZMod 3) ^ f = (eps : ZMod 3)) {a : ℕ}
    (ha : a = padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps))) :
    ∃ ψ : Multiplicative (ZMod (3 ^ (a + 1))) × Multiplicative (ZMod (3 ^ a)) →*
        ModGL TwistTag.D4.tag L,
      Function.Injective ψ ∧ ∀ t, t ∈ ψ.range ↔
        t ∈ twistedTorusOf (canonicalRep (coxeterSystem TwistTag.D4.tag) L (twEps eps))
            (twistHom TwistTag.D4 L Fr) ∧ t ^ (3 ^ (a + 1)) = 1 := by
  classical
  have h3pow : ((3 ^ (a + 1) : ℕ) : L) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ h3
  obtain ⟨ζ1L, hζ1L⟩ := @HasEnoughRootsOfUnity.exists_primitiveRoot L _ (3 ^ (a + 1))
    (@IsSepClosed.hasEnoughRootsOfUnity L _ (3 ^ (a + 1)) ⟨h3pow⟩
      (inferInstance : IsSepClosed L))
  let ζ1 : Lˣ := Units.mk0 ζ1L (hζ1L.ne_zero (by norm_num))
  have hζ1 : IsPrimitiveRoot ζ1 (3 ^ (a + 1)) := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    simpa [ζ1] using hζ1L
  let ζ2 : Lˣ := ζ1 ^ 3
  have hζ2 : IsPrimitiveRoot ζ2 (3 ^ a) := by
    simpa [ζ2, pow_succ] using
      hζ1.pow_of_dvd (by norm_num : (3 : ℕ) ≠ 0)
        (by rw [pow_succ]; exact dvd_mul_left 3 (3 ^ a))
  let f1 : Multiplicative (ZMod (3 ^ (a + 1))) →* Lˣ :=
    (Subgroup.zpowers ζ1).subtype.comp
      (AddEquiv.toMultiplicativeLeft hζ1.zmodEquivZPowers).toMonoidHom
  let f2 : Multiplicative (ZMod (3 ^ a)) →* Lˣ :=
    (Subgroup.zpowers ζ2).subtype.comp
      (AddEquiv.toMultiplicativeLeft hζ2.zmodEquivZPowers).toMonoidHom
  have hf1_inj : Function.Injective f1 := inj_of_zmodEquivZPowers_l7t2 hζ1 f1 rfl
  have hf2_inj : Function.Injective f2 := inj_of_zmodEquivZPowers_l7t2 hζ2 f2 rfl
  have hf1_surj : ∀ y : Lˣ, y ^ (3 ^ (a + 1)) = 1 → ∃ i, f1 i = y :=
    surj_of_zmodEquivZPowers_l7t2 (by norm_num : (3 : ℕ) ^ (a + 1) ≠ 0) hζ1 f1 rfl
  have hf2_surj : ∀ y : Lˣ, y ^ (3 ^ a) = 1 → ∃ i, f2 i = y :=
    surj_of_zmodEquivZPowers_l7t2 (by norm_num : (3 : ℕ) ^ a ≠ 0) hζ2 f2 rfl
  have hf1_pow : ∀ i, f1 i ^ (3 ^ (a + 1)) = 1 := zmod_hom_pow_l7t2 hζ1 f1 rfl
  have hf2_pow : ∀ i, f2 i ^ (3 ^ a) = 1 := zmod_hom_pow_l7t2 hζ2 f2 rfl
  let ψ : Multiplicative (ZMod (3 ^ (a + 1))) × Multiplicative (ZMod (3 ^ a)) →*
      ModGL TwistTag.D4.tag L :=
    (rootDiagUnitHom TwistTag.D4.tag L).comp (psiTuple_l7t2 (p := p) (f := f) eps f1 f2)
  refine ⟨ψ, psi_inj_l7t2 f1 f2 hf1_inj hf2_inj, ?_⟩
  intro t
  exact ⟨psi_range_sub_l7t2 hp hf heps hq ha hFr f1 f2 hf1_pow hf2_pow t,
    psi_range_sup_l7t2 hp hf heps hq ha hFr f1 f2 hf1_surj hf2_surj t⟩

private theorem coord_perm_l7t {L : Type} [Field L] {p f : ℕ}
    {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (p ^ f)) {eps : ℤ} (heps : eps = 1 ∨ eps = -1)
    {b : Fin TwistTag.D4.tag.rank → Lˣ}
    (ht : rootDiagUnit TwistTag.D4.tag b ∈
      twistedTorusOf (canonicalRep (coxeterSystem TwistTag.D4.tag) L (twEps eps))
        (twistHom TwistTag.D4 L Fr)) (j : Fin TwistTag.D4.tag.rank) :
    b (TwistTag.D4.perm j) = b j ^ (eps * (p : ℤ) ^ f) := by
  have hfix := (mem_twistedTorusOf.1 ht).2
  set c : Fin TwistTag.D4.tag.rank → Lˣ :=
    fun i => b (TwistTag.D4.perm.symm i) ^ (p ^ f) with hc
  have hF : twistHom TwistTag.D4 L Fr (rootDiagUnit TwistTag.D4.tag b) =
      rootDiagUnit TwistTag.D4.tag c := by
    rw [twistHom_rootDiagUnit_eq]
    congr 1
    funext i
    exact CTTorus.map_units_eq_pow hFr (b (TwistTag.D4.perm.symm i))
  have hconj : canonicalRep (coxeterSystem TwistTag.D4.tag) L (twEps eps) *
      rootDiagUnit TwistTag.D4.tag c *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) L (twEps eps))⁻¹ =
      rootDiagUnit TwistTag.D4.tag b := by
    rw [← hF]
    exact hfix
  have htu : weylTuple (twEps eps) c = b := by
    refine rootDiagUnit_injective ?_
    rwa [canonicalRep_conj_rootDiagUnit] at hconj
  have h := congrFun htu (TwistTag.D4.perm j)
  rw [weylTuple_twEps_l7t heps, hc] at h
  simp only [] at h
  rw [Equiv.symm_apply_apply] at h
  change (b j ^ (p ^ f)) ^ eps = b (TwistTag.D4.perm j) at h
  rw [← h]
  change (b j ^ (p ^ f)) ^ eps = b j ^ (eps * (p : ℤ) ^ f)
  rw [← zpow_natCast (b j) (p ^ f), ← zpow_mul]
  congr 1
  push_cast
  ring

private theorem diagramMap_conj_rootDiagUnit_l7t {L : Type} [Field L]
    (b : Fin TwistTag.D4.tag.rank → Lˣ) :
    (diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag b * diagramMap TwistTag.D4 L =
      rootDiagUnit TwistTag.D4.tag (fun i => b (TwistTag.D4.perm i)) := by
  have h := diagramMap_mul_rootDiagUnit (t := TwistTag.D4) (K := L)
    (b := fun i => b (TwistTag.D4.perm i))
  have h' : diagramMap TwistTag.D4 L *
      rootDiagUnit TwistTag.D4.tag (fun i => b (TwistTag.D4.perm i)) =
      rootDiagUnit TwistTag.D4.tag b * diagramMap TwistTag.D4 L := by
    simpa using h
  rw [mul_assoc, ← h', ← mul_assoc, inv_mul_cancel, one_mul]

theorem diagramMap_conj_of_mem_twistedTorus {L : Type} [Field L]
    {p f : ℕ} {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (p ^ f)) {eps : ℤ} (heps : eps = 1 ∨ eps = -1)
    {t : ModGL TwistTag.D4.tag L}
    (ht : t ∈ twistedTorusOf (canonicalRep (coxeterSystem TwistTag.D4.tag) L (twEps eps))
      (twistHom TwistTag.D4 L Fr)) :
    (diagramMap TwistTag.D4 L)⁻¹ * t * diagramMap TwistTag.D4 L = t ^ (eps * (p : ℤ) ^ f) := by
  obtain ⟨b, rfl⟩ :=
    exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 ht).1
  have hpow : rootDiagUnit TwistTag.D4.tag b ^ (eps * (p : ℤ) ^ f) =
      rootDiagUnit TwistTag.D4.tag (fun i => b i ^ (eps * (p : ℤ) ^ f)) := by
    change (rootDiagUnitHom TwistTag.D4.tag L b) ^ (eps * (p : ℤ) ^ f) = _
    rw [← map_zpow]
    rfl
  rw [diagramMap_conj_rootDiagUnit_l7t, hpow]
  congr 1
  funext i
  exact coord_perm_l7t hFr heps ht i

section MovedByY

open scoped Matrix

private def triWordL_l7t : List (Fin TwistTag.D4.tag.rank) := triWord

private def yWordL_l7t : List (Fin TwistTag.D4.tag.rank) :=
  List.reverse (triWordL_l7t ++ triWordL_l7t ++ triWordL_l7t ++ triWordL_l7t)

private def yInvMatList_l7t : List (List ℤ) :=
  [[0, -1, 1, -1], [-1, 0, 1, -1], [-1, -1, 1, -1], [-1, -1, 1, 0]]

private def yInvMat_l7t : Matrix (Fin TwistTag.D4.tag.rank)
    (Fin TwistTag.D4.tag.rank) ℤ :=
  toMat TwistTag.D4.tag.rank yInvMatList_l7t

private theorem wordMat_yInv_l7t :
    wordMat TwistTag.D4.tag yWordL_l7t = yInvMat_l7t := by
  rw [wordMat_eq_toMat _ _ (L := yInvMatList_l7t) (by decide +kernel)]
  rfl

private theorem wordProd_yWordL_l7t :
    (coxeterSystem TwistTag.D4.tag).wordProd yWordL_l7t =
      ((coxeterSystem TwistTag.D4.tag).wordProd triWord ^ 4)⁻¹ := by
  have h : (coxeterSystem TwistTag.D4.tag).wordProd yWordL_l7t =
      ((coxeterSystem TwistTag.D4.tag).wordProd
        (triWordL_l7t ++ triWordL_l7t ++ triWordL_l7t ++ triWordL_l7t))⁻¹ := by
    rw [yWordL_l7t, CoxeterSystem.wordProd_reverse]
  rw [h]
  congr 1

private theorem yInvMat_smul_l7t
    (y : Fin TwistTag.D4.tag.rank → ℤ) :
    ((coxeterSystem TwistTag.D4.tag).wordProd triWord ^ 4)⁻¹ • y =
      yInvMat_l7t *ᵥ y := by
  rw [← wordProd_yWordL_l7t, wordProd_smul_eq_wordMat_mulVec, wordMat_yInv_l7t]

private theorem yInvMat_transpose_ne_l7t :
    (yInvMat_l7t.map (Int.castRingHom (ZMod 3)))ᵀ *ᵥ
        (Pi.single (2 : Fin TwistTag.D4.tag.rank) 1) ≠
      (Pi.single (2 : Fin TwistTag.D4.tag.rank) 1) := by
  decide +kernel

end MovedByY

theorem exists_moved_by_yElt {L : Type} [Field L] [IsAlgClosed L]
    (h3 : (3 : L) ≠ 0) {p f : ℕ} {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (p ^ f)) {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) (hq : (p : ZMod 3) ^ f = (eps : ZMod 3)) :
    ∃ v ∈ twistedTorusOf (canonicalRep (coxeterSystem TwistTag.D4.tag) L (twEps eps))
        (twistHom TwistTag.D4 L Fr), v ^ 3 = 1 ∧ yElt L * v * (yElt L)⁻¹ ≠ v := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Lˣ, IsPrimitiveRoot ζ 3 := by
    have : NeZero ((3 : ℕ) : L) := ⟨by simpa using h3⟩
    have : NeZero (3 : ℕ) := .of_neZero_natCast L
    obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
    exact ⟨(hz.isUnit (by norm_num)).unit, hz.isUnit_unit (by norm_num)⟩
  have hζord : orderOf ζ = 3 := (IsPrimitiveRoot.iff_orderOf).1 hζ
  let x : Fin TwistTag.D4.tag.rank → ZMod 3 := Pi.single 2 1
  let v : ModGL TwistTag.D4.tag L := f3Diag TwistTag.D4.tag ζ x
  have hq3 : ((p ^ f : ℕ) : ZMod 3) = (eps : ZMod 3) := by
    rw [← hq]
    push_cast
    rfl
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [f3Diag_mem_twistedTorusOf_iff (t := TwistTag.D4) (ζ := ζ) hζord
      (hFr := hFr) (q := p ^ f) (v := twEps eps) (M := eps • trialityM)
      (twEps_smul_permLattice heps) x]
    rcases heps with rfl | rfl <;>
      ext i <;> fin_cases i <;>
        simp [x, Matrix.mulVec, dotProduct, Matrix.transpose, Matrix.map, trialityM, hq3,
          Pi.single_apply] <;> decide +kernel
  · exact f3Diag_pow_three hζ.pow_eq_one x
  · intro heq
    have hconj := f3Diag_conj_of_twActsAs (τ := TwistTag.D4.tag) (ζ := ζ)
      (hζ := hζ.pow_eq_one) (g := yElt L)
      (u := (coxeterSystem TwistTag.D4.tag).wordProd triWord ^ 4)
      (twActsAs_yElt (L := L)) (W := yInvMat_l7t) (yInvMat_smul_l7t) x
    have h1 : f3Diag TwistTag.D4.tag ζ
        ((yInvMat_l7t.map (Int.castRingHom (ZMod 3)))ᵀ *ᵥ x) =
        f3Diag TwistTag.D4.tag ζ x := by
      rw [← hconj, heq]
    exact yInvMat_transpose_ne_l7t (f3Diag_injective hζord h1)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.TrialityL7
