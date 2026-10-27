module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillDefs
public import Certificates.Certificate830101
public import CFSG.Blueprint.ChevalleyRoots
public import CFSG.LieType.Chevalley.LongestElement
public import CFSG.LieType.Chevalley.SignCharacterCertificates
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

public section

namespace CFSG.StandardType.TwE6RootKill

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Rank

open Matrix

theorem card_ker_le_of_isUnit_minor {p : ℕ} [Fact p.Prime] {n : ℕ}
    (N : Matrix (Fin n) (Fin n) ℤ) (R C : Fin 3 → Fin n)
    (hdet : IsUnit (((N.submatrix R C).det : ℤ) : ZMod p)) :
    Nat.card {y : Fin n → ZMod p // N.map (Int.cast : ℤ → ZMod p) *ᵥ y = 0} ≤ p ^ (n - 3) := by
  classical
  set N' : Matrix (Fin n) (Fin n) (ZMod p) := N.map (Int.cast : ℤ → ZMod p) with hN'
  set M3 : Matrix (Fin 3) (Fin 3) (ZMod p) := N'.submatrix R C with hM3
  have hM3det : M3.det = (((N.submatrix R C).det : ℤ) : ZMod p) := by
    rw [← eq_intCast (Int.castRingHom (ZMod p)), RingHom.map_det]
    rfl
  have hunit : IsUnit M3 := (Matrix.isUnit_iff_isUnit_det M3).2 (hM3det ▸ hdet)
  have hsurj3 : Function.Surjective M3.mulVec := Matrix.mulVec_surjective_iff_isUnit.2 hunit
  set L : (Fin n → ZMod p) →ₗ[ZMod p] (Fin 3 → ZMod p) := Matrix.mulVecLin (N'.submatrix R id)
  have hL : ∀ y, L y = fun a => (N' *ᵥ y) (R a) := fun y => rfl
  have hsurj : Function.Surjective L := by
    intro x
    obtain ⟨z, hz⟩ := hsurj3 x
    refine ⟨fun k => ∑ b, if C b = k then z b else 0, ?_⟩
    rw [← hz, hL]
    funext a
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hM3, Matrix.submatrix_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [mul_ite]
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fin_fun,
    Module.finrank_fin_fun] at hrank
  have hker : Nat.card (LinearMap.ker L) = p ^ (n - 3) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    congr 1
    omega
  have hinj : Function.Injective (fun y : {y : Fin n → ZMod p // N' *ᵥ y = 0} =>
      (⟨y.1, LinearMap.mem_ker.2 (funext fun a => by rw [hL]; exact congrFun y.2 (R a))⟩ :
        LinearMap.ker L)) := by
    intro y y' h
    apply Subtype.ext
    simpa using congrArg Subtype.val h
  calc Nat.card {y : Fin n → ZMod p // N' *ᵥ y = 0}
      ≤ Nat.card (LinearMap.ker L) := Nat.card_le_card_of_injective _ hinj
    _ = p ^ (n - 3) := hker

theorem isUnit_intCast_of_mem_wk {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {d : ℤ}
    (hd : d ∈ ({1, -1, 2, -2} : Finset ℤ)) : IsUnit ((d : ℤ) : ZMod p) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h')
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · simp
  · simp
  · exact isUnit_iff_ne_zero.2 (by exact_mod_cast h2)
  · exact isUnit_iff_ne_zero.2 (by push_cast; exact neg_ne_zero.2 h2)

end Rank

section Zpow

theorem prod_zpow_eq_zpow_sum_wk {G ι : Type*} [CommGroup G] (ζ : G) (s : Finset ι)
    (e : ι → ℤ) : ∏ i ∈ s, ζ ^ e i = ζ ^ ∑ i ∈ s, e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add]

theorem rootChar_zpow_wk {τ : Tag} {L : Type} [Field L] (ζ : Lˣ) (m u : Fin τ.rank → ℤ) :
    rootChar (fun j => ζ ^ m j) u = ζ ^ ∑ j, m j * u j := by
  rw [rootChar, ← prod_zpow_eq_zpow_sum_wk]
  exact Finset.prod_congr rfl fun j _ => (zpow_mul _ _ _).symm

theorem zpow_eq_zpow_iff_wk {L : Type} [Field L] {p : ℕ} {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    (m m' : ℤ) : ζ ^ m = ζ ^ m' ↔ ((m : ℤ) : ZMod p) = m' := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, ← hζ.zpow_eq_one_iff_dvd, zpow_sub,
    mul_inv_eq_one, eq_comm]

theorem rootChar_val_eq_one_iff_wk {τ : Tag} {L : Type} [Field L] {p : ℕ} [NeZero p]
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) (y : Fin τ.rank → ZMod p) (u : Fin τ.rank → ℤ) :
    rootChar (fun k => ζ ^ ((y k).val : ℤ)) u = 1 ↔ ∑ k, y k * (u k : ZMod p) = 0 := by
  rw [rootChar_zpow_wk, ← zpow_zero ζ, zpow_eq_zpow_iff_wk hζ]
  push_cast
  simp only [ZMod.natCast_zmod_val]

end Zpow

section Check


theorem isLongest_of_wkMatrix_eq_zero {v : WeylGroup TwistTag.E6.tag} (h : wkMatrix v⁻¹ = 0) :
    IsLongest v := by
  have hneg : ∀ i, height (v⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) < 0 := by
    intro i
    have hk : ∀ k, (v⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) (TwistTag.E6.perm k) =
        -(if i = k then 1 else 0) := by
      intro k
      have := congrFun (congrFun h i) k
      simp only [wkMatrix, Matrix.zero_apply] at this
      linarith
    have hh : height (v⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) = -1 := by
      unfold height
      rw [← Equiv.sum_comp TwistTag.E6.perm]
      simp only [hk, Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    omega
  have hrev : ReversesSigns v⁻¹ := fun α hα hpos => height_smul_neg_of_forall_single hneg hα hpos
  have hrev' : ReversesSigns v := by simpa using hrev.inv
  obtain ⟨w₀, hmax, -⟩ := weyl_longest_element TwistTag.E6.tag
  rw [hrev'.eq (reversesSigns_of_forall_length_le hmax)]
  exact hmax

end Check

section Log


open CFSG.RankThree.PartOne.KE

theorem exists_wkLog {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (D : TwLangData K σ q A) {p : ℕ} [NeZero p]
    (hq : ((q : ℕ) : ZMod p) = -1) {ζ : (AlgebraicClosure K)ˣ} (hζ : IsPrimitiveRoot ζ p)
    {x : ModGL TwistTag.E6.tag K} (hx : x ∈ A) (hxp : x ^ p = 1) :
    ∃ y : Fin TwistTag.E6.tag.rank → ZMod p,
      rootDiagUnit TwistTag.E6.tag (fun k => ζ ^ ((y k).val : ℤ)) =
        D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) * D.g0 ∧
      ∀ i, ∑ k, ((wkMatrix D.v⁻¹ i k : ℤ) : ZMod p) * y k = 0 := by
  classical
  obtain ⟨s, hs, hsz⟩ := Subgroup.mem_map.1 (D.hc x hx)
  have hsz' : D.g0 * s * D.g0⁻¹ =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) := hsz
  have hs_eq : D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) *
      D.g0 = s := by
    rw [← hsz']
    group
  rw [mem_twistedTorusOf] at hs
  obtain ⟨hsT, hsF⟩ := hs
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hsT
  rw [twistHom_rootDiagUnit_eq, canonicalRep_conj_rootDiagUnit] at hsF
  have hwa := CFSG.LieType.Chevalley.rootDiagUnit_injective hsF
  have hz : baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) ^ p = 1 := by
    rw [← map_pow, conj_pow, hxp, mul_one, mul_inv_cancel, map_one]
  have h1 : rootDiagUnit TwistTag.E6.tag a ^ p = 1 := by
    rw [← hs_eq]
    have hc := conj_pow (a := D.g0⁻¹)
      (b := baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹)) (i := p)
    rw [inv_inv] at hc
    rw [hc, hz, mul_one, inv_mul_cancel]
  have h2 : rootDiagUnit TwistTag.E6.tag (a ^ p) = rootDiagUnit TwistTag.E6.tag 1 := by
    have hmp := map_pow (rootDiagUnitHom TwistTag.E6.tag (AlgebraicClosure K)) a p
    change rootDiagUnit TwistTag.E6.tag (a ^ p) = rootDiagUnit TwistTag.E6.tag a ^ p at hmp
    rw [hmp, h1, rootDiagUnit_one]
  have hap : ∀ k, a k ^ p = 1 := fun k =>
    congrFun (CFSG.LieType.Chevalley.rootDiagUnit_injective h2) k
  have hlog : ∀ k, ∃ e : ℕ, e < p ∧ ζ ^ e = a k := fun k =>
    hζ.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity p (a k)).2 (hap k))
  choose e he hea using hlog
  have hya : (fun k => ζ ^ ((((e k : ℕ) : ZMod p)).val : ℤ)) = a := by
    funext k
    rw [ZMod.val_cast_of_lt (he k), zpow_natCast, hea k]
  refine ⟨fun k => (e k : ZMod p), ?_, fun i => ?_⟩
  · rw [hya]
    exact hs_eq.symm
  have hFr : ∀ u : (AlgebraicClosure K)ˣ, Units.map D.Fr.toMonoidHom u = u ^ q := fun u =>
    Units.ext (by rw [Units.coe_map, Units.val_pow_eq_pow_val]; exact D.hFr u)
  have hb : (fun j => Units.map D.Fr.toMonoidHom (a (TwistTag.E6.perm.symm j))) =
      fun j => ζ ^ (((e (TwistTag.E6.perm.symm j) * q : ℕ) : ℤ)) := by
    funext j
    rw [hFr, ← hea, ← pow_mul, zpow_natCast]
  have hi : rootChar (fun j => ζ ^ (((e (TwistTag.E6.perm.symm j) * q : ℕ) : ℤ)))
      (D.v⁻¹ • (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ)) = ζ ^ ((e i : ℕ) : ℤ) := by
    rw [← hb, zpow_natCast, hea i]
    exact congrFun hwa i
  rw [rootChar_zpow_wk, zpow_eq_zpow_iff_wk hζ] at hi
  push_cast at hi
  rw [hq, ← Equiv.sum_comp TwistTag.E6.perm] at hi
  simp only [Equiv.symm_apply_apply] at hi
  simp only [wkMatrix]
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [← hi, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun k _ => by ring

end Log

section Main


open Matrix

theorem weylKill_holds : WeylKill := by
  intro K _ _ σ q hK hσ h2 p hp hpq A hA hcard D hv
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 1 := (Nat.dvd_add_right (two_dvd_of_card hK h2)).mp hpq
    omega
  have hq : ((q : ℕ) : ZMod p) = -1 := by
    have h0 : ((q + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hpq
    push_cast at h0
    exact eq_neg_of_add_eq_zero_left h0
  haveI : NeZero ((p : ℕ) : K) := ⟨fun h => by
    have h' := (ringChar.spec K p).1 h
    rw [h2] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h').symm⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) p
  obtain ⟨ζ, hζ⟩ : ∃ ζ : (AlgebraicClosure K)ˣ, IsPrimitiveRoot ζ p :=
    ⟨_, IsPrimitiveRoot.isUnit_unit hp.ne_zero hζ0⟩
  have hlog : ∀ x ∈ A, ∃ y : Fin TwistTag.E6.tag.rank → ZMod p,
      rootDiagUnit TwistTag.E6.tag (fun k => ζ ^ ((y k).val : ℤ)) =
        D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x * D.c⁻¹) * D.g0 ∧
      ∀ i, ∑ k, ((wkMatrix D.v⁻¹ i k : ℤ) : ZMod p) * y k = 0 :=
    fun x hx => exists_wkLog D hq hζ hx (hA.2 x hx)
  rcases Certificates.certificate830101 D.v⁻¹ with
    ⟨i, hi⟩ | hz | ⟨R, C, hdet⟩
  ·
    refine ⟨wkMatrix D.v⁻¹ i, hi, fun x hx => ?_⟩
    obtain ⟨y, hy1, hy2⟩ := hlog x hx
    refine ⟨_, hy1, (rootChar_val_eq_one_iff_wk hζ y _).2 ?_⟩
    rw [← hy2 i]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  ·
    exact absurd (isLongest_of_wkMatrix_eq_zero hz) hv
  ·
    exfalso
    have hker := card_ker_le_of_isUnit_minor (p := p) (wkMatrix D.v⁻¹) R C
      (isUnit_intCast_of_mem_wk hp2 hdet)
    choose y hy1 hy2 using hlog
    let f : A → {z : Fin TwistTag.E6.tag.rank → ZMod p //
        (wkMatrix D.v⁻¹).map (Int.cast : ℤ → ZMod p) *ᵥ z = 0} :=
      fun x => ⟨y x.1 x.2, funext fun i => by
        simpa [Matrix.mulVec, dotProduct] using hy2 x.1 x.2 i⟩
    have hf : Function.Injective f := by
      intro x x' hxx
      have h1 : y x.1 x.2 = y x'.1 x'.2 := congrArg Subtype.val hxx
      have h3 : D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (D.c * x.1 * D.c⁻¹) *
          D.g0 = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (D.c * x'.1 * D.c⁻¹) * D.g0 := by
        rw [← hy1 x.1 x.2, ← hy1 x'.1 x'.2, h1]
      have h4 := baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
        (mul_left_cancel (mul_right_cancel h3))
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h4))
    have hle : Nat.card A ≤ p ^ 3 := (Nat.card_le_card_of_injective f hf).trans hker
    have h4 : p ^ 4 ≤ p ^ (if p = 3 then 4 else 5) := by
      split_ifs
      · exact le_rfl
      · exact Nat.pow_le_pow_right hp.pos (by norm_num)
    have h34 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    exact absurd (h34.trans_le (h4.trans (hcard.trans hle))) (lt_irrefl _)

end Main

end CFSG.StandardType.TwE6RootKill

end
