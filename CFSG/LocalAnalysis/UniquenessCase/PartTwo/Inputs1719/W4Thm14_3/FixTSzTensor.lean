module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.FixTSzDelta
public import CFSG.Quasithin.Background.SmithB45SzIrr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.LieType.Ree CFSG.Quasithin.B45Sz CFSG.QuasithinUnique.Setup.X7b
open CFSG.QuasithinUnique.Setup.X7
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.Blueprint (suzukiS)

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]

@[expose] def eTopS (k : Type*) [Field k] (A : Finset ℕ) : (↥A → Fin 4) → k :=
  Pi.single (fun _ => 3) 1

theorem eTopS_ne_zero (k : Type*) [Field k] (A : Finset ℕ) : eTopS k A ≠ 0 := by
  intro h
  have := congrFun h (fun _ => 3)
  simp [eTopS] at this

omit [CharP K 2] [Fintype K] in
private theorem suzukiS_map {k : Type} [Field k] (f : K →+* k) (u v : K) :
    (CFSG.Blueprint.suzukiS a u v).map f = CFSG.Blueprint.suzukiS a (f u) (f v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.Blueprint.suzukiS, CFSG.Blueprint.suzukiN]

private theorem natRepS_szIncl_suzukiSElt
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (k : Type) [Field k] [Algebra K k] (i : ℕ) (u v : K) :
    natRepS k i (szIncl hK (suzukiSElt a K u v)) = CFSG.Blueprint.suzukiS a
      (algebraMap K k (u ^ 2 ^ ((a + 1) * i)))
      (algebraMap K k (v ^ 2 ^ ((a + 1) * i))) := by
  rw [natRepS_szIncl]
  change (CFSG.Blueprint.suzukiS a u v).map
    (fun x => algebraMap K k (x ^ 2 ^ ((a + 1) * i))) = _
  rw [show (fun x => algebraMap K k (x ^ 2 ^ ((a + 1) * i))) =
      ⇑((algebraMap K k).comp (iterateFrobenius K 2 ((a + 1) * i))) by
    funext x
    simp [iterateFrobenius_def]]
  rw [suzukiS_map]
  simp [iterateFrobenius_def]

private def szSlot (k : Type*) [Field k] {A : Finset ℕ} (j : ↥A) (w : Fin 4 → k) :
    (↥A → Fin 4) → k := fun x => if ∀ i, i ≠ j → x i = 3 then w (x j) else 0

private theorem szSlot_add (k : Type*) [Field k] {A : Finset ℕ} (j : ↥A) (w w' : Fin 4 → k) :
    szSlot k j (w + w') = szSlot k j w + szSlot k j w' := by
  funext x
  simp only [szSlot, Pi.add_apply]
  split_ifs <;> simp

private theorem szSlot_e4 (k : Type*) [Field k] {A : Finset ℕ} (j : ↥A) :
    szSlot k j ![0, 0, 0, 1] = eTopS k A := by
  have hvec : ∀ t : Fin 4, (![0, 0, 0, 1] : Fin 4 → k) t = if t = 3 then 1 else 0 := by
    intro t
    fin_cases t <;> simp
  funext x
  rw [szSlot, eTopS, Pi.single_apply, hvec]
  by_cases h : ∀ i, i ≠ j → x i = 3
  · rw [if_pos h]
    by_cases hj : x j = 3
    · rw [if_pos hj, if_pos (by
        funext i
        by_cases hi : i = j
        · subst hi
          exact hj
        · exact h i hi)]
    · rw [if_neg hj, if_neg (fun hx => hj (by rw [hx]))]
  · rw [if_neg h, if_neg (fun hx => h (by rw [hx]; intro i _; rfl))]

private theorem szT_mulVec_szSlot
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (k : Type) [Field k] [Algebra K k] {A : Finset ℕ}
    (g : ↥(CFSG.Blueprint.suzukiGroup a K)) (j : ↥A)
    (hcol : ∀ i : ↥A, i ≠ j → ∀ y : Fin 4,
      natRepS k (i : ℕ) (szIncl hK g) y 3 = if y = 3 then 1 else 0) (w : Fin 4 → k) :
    (szT k hK A g).mulVec (szSlot k j w) =
      szSlot k j ((natRepS k (j : ℕ) (szIncl hK g)).mulVec w) := by
  classical
  let u : Fin 4 → (↥A → Fin 4) := fun t i => if i = j then t else 3
  have hslot : szSlot k j w = ∑ t : Fin 4, w t • (Pi.single (u t) (1 : k)) := by
    funext x
    rw [szSlot]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    by_cases hx : ∀ i, i ≠ j → x i = 3
    · rw [if_pos hx]
      have hgoal : (∑ t : Fin 4, w t * (if x = u t then 1 else 0)) =
          w (x j) * (if x = u (x j) then 1 else 0) :=
        Finset.sum_eq_single (x j)
          (fun t _ ht => by
            rw [if_neg, mul_zero]
            intro h
            exact ht (by have := congrFun h j; simpa [u] using this.symm))
          (fun hmem => absurd (Finset.mem_univ (x j)) hmem)
      rw [hgoal]
      have hux : u (x j) = x := by
        funext i
        by_cases hi : i = j
        · subst hi
          simp [u]
        · simp [u, hi, hx i hi]
      rw [if_pos hux.symm, mul_one]
    · rw [if_neg hx]
      have hzero : (∑ t : Fin 4, w t * (if x = u t then 1 else 0)) = 0 :=
        Finset.sum_eq_zero fun t _ => by
          rw [if_neg, mul_zero]
          intro h
          exact hx (by rw [h]; intro i hi; simp [u, hi])
      rw [hzero]
  rw [hslot, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul, Matrix.mulVec_single_one]
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply, szSlot]
  rw [szT_apply]
  simp_rw [tensorRepS_apply]
  have hsplit : ∀ t : Fin 4,
      (∏ i : ↥A, natRepS k (i : ℕ) (szIncl hK g) (x i) (u t i)) =
        (∏ i ∈ (Finset.univ : Finset ↥A).erase j,
          natRepS k (i : ℕ) (szIncl hK g) (x i) 3) *
        natRepS k (j : ℕ) (szIncl hK g) (x j) t := by
    intro t
    rw [← Finset.prod_erase_mul (Finset.univ : Finset ↥A)
      (fun i => natRepS k (i : ℕ) (szIncl hK g) (x i) (u t i)) (Finset.mem_univ j)]
    congr 1
    · exact Finset.prod_congr rfl fun i hi => by simp [u, (Finset.mem_erase.mp hi).1]
    · simp [u]
  simp_rw [hsplit]
  have hP : (∏ i ∈ (Finset.univ : Finset ↥A).erase j,
      natRepS k (i : ℕ) (szIncl hK g) (x i) 3) =
      if (∀ i, i ≠ j → x i = 3) then 1 else 0 := by
    have h1 : ∀ i ∈ (Finset.univ : Finset ↥A).erase j,
        natRepS k (i : ℕ) (szIncl hK g) (x i) 3 = if x i = 3 then 1 else 0 :=
      fun i hi => hcol i (Finset.mem_erase.mp hi).1 (x i)
    rw [Finset.prod_congr rfl h1, Finset.prod_boole]
    congr 1
    exact propext ⟨fun h i hi => h i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩),
      fun h i hi => h i (Finset.mem_erase.mp hi).1⟩
  rw [hP]
  by_cases hx : ∀ i, i ≠ j → x i = 3
  · rw [if_pos hx, if_pos hx]
    simp only [one_mul, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  · rw [if_neg hx, if_neg hx]
    simp

theorem szT_norm_eTopS (hK : Nat.card K = 2 ^ (2 * a + 1))
    (k : Type) [Field k] [Algebra K k] {A : Finset ℕ} (hA : A.Nonempty) {u : K} (hu : u ≠ 0)
    (v : K) :
    ∃ z : (↥A → Fin 4) → k, eTopS k A =
      z + (szT k hK A (suzukiSElt a K u v)).mulVec z +
        (szT k hK A (suzukiSElt a K u v)).mulVec
          ((szT k hK A (suzukiSElt a K u v)).mulVec z) +
        (szT k hK A (suzukiSElt a K u v)).mulVec
          ((szT k hK A (suzukiSElt a K u v)).mulVec
            ((szT k hK A (suzukiSElt a K u v)).mulVec z)) := by
  classical
  obtain ⟨j, hj⟩ := hA
  let jA : ↥A := ⟨j, hj⟩
  have h2k : (2 : k) = 0 := by
    have h' := congrArg (algebraMap K k) (CharP.cast_eq_zero K 2)
    rw [map_zero, map_natCast] at h'
    exact h'
  let U : k := algebraMap K k (u ^ 2 ^ ((a + 1) * (jA : ℕ)))
  let V : k := algebraMap K k (v ^ 2 ^ ((a + 1) * (jA : ℕ)))
  let z0 : k := (U ^ (2 ^ (a + 1) + 2))⁻¹
  have hUn : u ^ 2 ^ ((a + 1) * (jA : ℕ)) ≠ 0 := pow_ne_zero _ hu
  have hU : U ≠ 0 := by
    simp only [U]
    exact fun h0 => hUn ((algebraMap K k).injective (by simpa using h0))
  have hz : z0 * U ^ (2 ^ (a + 1) + 2) = 1 := by
    simp only [z0]
    exact inv_mul_cancel₀ (pow_ne_zero _ hU)
  have hM0 : natRepS k (jA : ℕ) (szIncl hK (suzukiSElt a K u v)) = suzukiS a U V :=
    natRepS_szIncl_suzukiSElt hK k (jA : ℕ) u v
  have hfixe4 : ∀ i : ↥A, i ≠ jA → ∀ y : Fin 4,
      natRepS k (i : ℕ) (szIncl hK (suzukiSElt a K u v)) y 3 = if y = 3 then 1 else 0 := by
    intro i _ y
    rw [natRepS_szIncl_suzukiSElt hK k i u v]
    fin_cases y <;> simp [suzukiS]
  have hstep : ∀ w : Fin 4 → k,
      (szT k hK A (suzukiSElt a K u v)).mulVec (szSlot k jA w) =
        szSlot k jA ((suzukiS a U V).mulVec w) := by
    intro w
    rw [szT_mulVec_szSlot hK k (suzukiSElt a K u v) jA hfixe4 w, hM0]
  have hnorm : (![0, 0, 0, 1] : Fin 4 → k) =
      ![z0, 0, 0, 0] + (suzukiS a U V).mulVec ![z0, 0, 0, 0] +
        (suzukiS a U V).mulVec ((suzukiS a U V).mulVec ![z0, 0, 0, 0]) +
        (suzukiS a U V).mulVec ((suzukiS a U V).mulVec
          ((suzukiS a U V).mulVec ![z0, 0, 0, 0])) := by
    have h := suzukiS_norm_mulVec a h2k U V z0
    dsimp only at h
    rw [h]
    ext i
    fin_cases i <;> simp [hz]
  refine ⟨szSlot k jA ![z0, 0, 0, 0], ?_⟩
  rw [← szSlot_e4 (k := k) jA,
    hstep ![z0, 0, 0, 0],
    hstep ((suzukiS a U V).mulVec ![z0, 0, 0, 0]),
    hstep ((suzukiS a U V).mulVec ((suzukiS a U V).mulVec ![z0, 0, 0, 0]))]
  rw [← szSlot_add k jA, ← szSlot_add k jA, ← szSlot_add k jA]
  exact congrArg (szSlot k jA) hnorm

private theorem szT_suzukiWElt_hwS
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (k : Type) [Field k] [Algebra K k]
    (A : Finset ℕ) :
    (szT k hK A (suzukiWElt a K)).mulVec (hwS k A) = eTopS k A := by
  have hma : minorAut K Jsp = Jsp := minorHom_Jsp
  have hJ : ∀ i : ℕ, ((minorAut K) ^ i) Jsp = Jsp := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ', MulAut.mul_apply, ih, hma]
  have hnat : ∀ (i : ℕ) (y : Fin 4),
      natRepS k i (szIncl hK (suzukiWElt a K)) y 0 = if y = 3 then 1 else 0 := by
    intro i y
    rw [szIncl_suzukiWElt, natRepS_apply, hJ, glMat_Jsp, Matrix.map_apply, minorJ_apply]
    change (algebraMap K k) (if (y : ℕ) = 3 then 1 else 0) = if y = 3 then 1 else 0
    by_cases hy : y = 3
    · subst hy
      simp
    · have hne : ¬ ((y : ℕ) = 3) := fun h => hy (Fin.ext h)
      rw [if_neg hne, if_neg hy, map_zero]
  funext x
  rw [szT_apply, tensorRepS_mulVec_hwS]
  simp_rw [hnat]
  rw [eTopS, Pi.single_apply, Fintype.prod_boole]
  simp only [funext_iff]

private theorem szT_suzukiDElt_eTopS
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (k : Type) [Field k] [Algebra K k] {A : Finset ℕ}
    (hA : A ⊆ szOmega a) (l : Kˣ) :
    (szT k hK A (suzukiDElt a K l)).mulVec (eTopS k A) =
      (algebraMap K k ((l⁻¹ ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) ^ mIdx (2 * a + 1) A) •
        eTopS k A := by
  have hDW : suzukiDElt a K l * suzukiWElt a K =
      suzukiWElt a K * suzukiDElt a K l⁻¹ := by
    calc suzukiDElt a K l * suzukiWElt a K
        = (suzukiWElt a K * suzukiWElt a K) * suzukiDElt a K l * suzukiWElt a K := by
            rw [suzukiWElt_mul_self, one_mul]
      _ = suzukiWElt a K * (suzukiWElt a K * suzukiDElt a K l * suzukiWElt a K) := by group
      _ = suzukiWElt a K * suzukiDElt a K l⁻¹ := by rw [suzukiWElt_D_W hK l]
  calc (szT k hK A (suzukiDElt a K l)).mulVec (eTopS k A)
      = (szT k hK A (suzukiDElt a K l)).mulVec
          ((szT k hK A (suzukiWElt a K)).mulVec (hwS k A)) := by
          rw [szT_suzukiWElt_hwS]
    _ = (szT k hK A (suzukiDElt a K l) * szT k hK A (suzukiWElt a K)).mulVec
          (hwS k A) := by
          rw [Matrix.mulVec_mulVec]
    _ = (szT k hK A (suzukiDElt a K l * suzukiWElt a K)).mulVec (hwS k A) := by
          rw [map_mul]
    _ = (szT k hK A (suzukiWElt a K * suzukiDElt a K l⁻¹)).mulVec (hwS k A) := by
          rw [hDW]
    _ = (szT k hK A (suzukiWElt a K) * szT k hK A (suzukiDElt a K l⁻¹)).mulVec
          (hwS k A) := by
          rw [map_mul]
    _ = (szT k hK A (suzukiWElt a K)).mulVec
          ((szT k hK A (suzukiDElt a K l⁻¹)).mulVec (hwS k A)) := by
          rw [Matrix.mulVec_mulVec]
    _ = (szT k hK A (suzukiWElt a K)).mulVec
          ((algebraMap K k ((l⁻¹ ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) ^ mIdx (2 * a + 1) A) •
            hwS k A) := by
          rw [szT_suzukiDElt_hwS k hK hA]
    _ = (algebraMap K k ((l⁻¹ ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) ^ mIdx (2 * a + 1) A) •
          (szT k hK A (suzukiWElt a K)).mulVec (hwS k A) := by
          rw [Matrix.mulVec_smul]
    _ = (algebraMap K k ((l⁻¹ ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) ^ mIdx (2 * a + 1) A) •
          eTopS k A := by
          rw [szT_suzukiWElt_hwS]

theorem exists_szT_suzukiDElt_eTopS_ne
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (k : Type) [Field k] [Algebra K k] {A : Finset ℕ}
    (hA : A ⊆ szOmega a) (hAne : A.Nonempty) (hAΩ : A ≠ szOmega a) :
    ∃ (l : Kˣ) (c : k), c ≠ 1 ∧
      (szT k hK A (suzukiDElt a K l)).mulVec (eTopS k A) = c • eTopS k A := by
  classical
  have hF : Fintype.card K = 2 ^ (2 * a + 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have hm_lt : mIdx (2 * a + 1) A < 2 ^ (2 * a + 1) := by
    rw [mIdx_eq_mBits]
    exact CFSG.QuasithinUnique.Setup.X7a.mBits_lt _
  have hm_ne0 : mIdx (2 * a + 1) A ≠ 0 := by
    intro h0
    have hbits : CFSG.QuasithinUnique.Setup.X7a.mBits (evenBits (2 * a + 1) A) = 0 := by
      rw [← mIdx_eq_mBits]
      exact h0
    have hz := CFSG.QuasithinUnique.Setup.X7a.mBits_eq_zero hbits
    have hA0 : A = ∅ := by
      refine eq_of_evenBits hA (Finset.empty_subset _) ?_
      rw [hz]
      funext j
      simp [evenBits, CFSG.QuasithinUnique.Setup.X7a.zeros]
    exact hAne.ne_empty hA0
  have hm_ne_top : mIdx (2 * a + 1) A ≠ 2 ^ (2 * a + 1) - 1 := by
    intro htop
    have hbits : CFSG.QuasithinUnique.Setup.X7a.mBits (evenBits (2 * a + 1) A) =
        2 ^ (2 * a + 1) - 1 := by
      rw [← mIdx_eq_mBits]
      exact htop
    have hone := CFSG.QuasithinUnique.Setup.X7a.eq_ones_of_mBits hbits
    exact hAΩ (eq_szOmega_of_evenBits hA hone)
  have hAll : ∃ l : Kˣ,
      (algebraMap K k ((l⁻¹ ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K)) ^ mIdx (2 * a + 1) A ≠ 1 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hbij⟩ := suzuki_frobenius_exponents a K hK
    have hi : Function.Bijective (fun l : Kˣ => l⁻¹) :=
      Function.bijective_iff_has_inverse.mpr
        ⟨fun l => l⁻¹, fun l => inv_inv l, fun l => inv_inv l⟩
    have hcomp : Function.Bijective (fun l : Kˣ => l⁻¹ ^ (1 + (2 ^ a : ℤ))) := hbij.comp hi
    by_contra h
    push Not at h
    have hz : ∀ z : Kˣ, z ^ mIdx (2 * a + 1) A = 1 := by
      intro z
      obtain ⟨l, hl⟩ := hcomp.surjective z
      rw [← hl]
      have h1 := h l
      have h3 : ((↑(l⁻¹ ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) ^ mIdx (2 * a + 1) A) = 1 := by
        apply (algebraMap K k).injective
        rw [map_pow, map_one]
        exact h1
      change ((l⁻¹ ^ (1 + (2 ^ a : ℤ)) : Kˣ) ^ mIdx (2 * a + 1) A) = 1
      exact Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact h3)
    have hz' : ∀ z : Kˣ, z ^ mIdx (2 * a + 1) A = z ^ 0 := by
      simpa using hz
    rcases CFSG.QuasithinUnique.Setup.X7a.torus_weight_eq hF hm_lt (by positivity) hz' with
      h1 | ⟨h1, -⟩ | ⟨-, h1⟩
    · exact hm_ne0 h1
    · exact hm_ne0 h1
    · exact hm_ne_top h1
  obtain ⟨l, hl⟩ := hAll
  exact ⟨l, _, hl, szT_suzukiDElt_eTopS hK k hA l⟩

theorem szT_higman (hK : Nat.card K = 2 ^ (2 * a + 1))
    (k : Type) [Field k] [Algebra K k] [CharP k 2] :
    ∃ φ : (((↥(szOmega a) → Fin 4) → k) →ₗ[k] ((↥(szOmega a) → Fin 4) → k)),
      ∀ y, ∑ u : ↥(suzukiU a K),
        (szT k hK (szOmega a) (u : ↥(CFSG.Blueprint.suzukiGroup a K))).mulVec
          (φ ((szT k hK (szOmega a) ((u : ↥(CFSG.Blueprint.suzukiGroup a K))⁻¹)).mulVec y)) =
        y := by
  classical
  obtain ⟨b, hb⟩ := szOrbit_basis (k := k) (a := a) hK
  let ρ : ↥(suzukiU a K) →* (((↥(szOmega a) → Fin 4) → k) →ₗ[k]
      ((↥(szOmega a) → Fin 4) → k)) :=
    (matRep (szT k hK (szOmega a))).comp (suzukiU a K).subtype
  have hb_mul : ∀ g h : ↥(suzukiU a K), b (g * h) = ρ g (b h) := by
    intro g h
    rw [hb (g * h), hb h]
    simp only [ρ, MonoidHom.comp_apply, Subgroup.subtype_apply, matRep_apply,
      Subgroup.coe_mul]
    rw [map_mul, Matrix.mulVec_mulVec]
  let L : (↥(suzukiU a K) → k) →ₗ[k] (↥(suzukiU a K) → k) :=
    (LinearMap.proj (1 : ↥(suzukiU a K))).smulRight
      (Pi.single (1 : ↥(suzukiU a K)) (1 : k))
  have hsingle : ∀ u : ↥(suzukiU a K),
      regRep k u (Pi.single (1 : ↥(suzukiU a K)) (1 : k)) = Pi.single u (1 : k) := by
    intro u
    funext g
    rw [regRep_apply, Pi.single_apply, Pi.single_apply]
    have hiff : (u⁻¹ * g = 1) ↔ (g = u) := by
      constructor
      · intro h
        have h' := congrArg (fun x => u * x) h
        simpa using h'
      · intro h
        rw [h, inv_mul_cancel]
    by_cases h : g = u
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  have hreg : ∀ Y : ↥(suzukiU a K) → k,
      ∑ u : ↥(suzukiU a K), regRep k u (L (regRep k u⁻¹ Y)) = Y := by
    intro Y
    funext g
    rw [Finset.sum_apply]
    have hterm : ∀ u : ↥(suzukiU a K),
        regRep k u (L (regRep k u⁻¹ Y)) g = Y u * (if g = u then 1 else 0) := by
      intro u
      have h1 : (regRep k u⁻¹ Y) 1 = Y u := by
        rw [regRep_apply, inv_inv, mul_one]
      have h2 : L (regRep k u⁻¹ Y) = Y u • Pi.single (1 : ↥(suzukiU a K)) (1 : k) := by
        rw [show L (regRep k u⁻¹ Y) =
          (regRep k u⁻¹ Y) 1 • Pi.single (1 : ↥(suzukiU a K)) (1 : k) from rfl, h1]
      rw [h2, map_smul, hsingle u, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    simp_rw [hterm]
    have hsum : (∑ u : ↥(suzukiU a K), Y u * (if g = u then 1 else 0)) =
        Y g * (if g = g then 1 else 0) :=
      Finset.sum_eq_single g
        (f := fun u => Y u * (if g = u then 1 else 0))
        (fun u _ hu => by rw [if_neg (fun h => hu h.symm), mul_zero])
        (fun hg => absurd (Finset.mem_univ g) hg)
    rw [hsum, if_pos rfl, mul_one]
  let ψ := b.equivFun
  let φ : ((↥(szOmega a) → Fin 4) → k) →ₗ[k] ((↥(szOmega a) → Fin 4) → k) :=
    ψ.symm.toLinearMap.comp (L.comp ψ.toLinearMap)
  refine ⟨φ, fun y => ?_⟩
  have hψ : ∀ (u : ↥(suzukiU a K)) (x : (↥(szOmega a) → Fin 4) → k),
      ψ ((szT k hK (szOmega a) (u : ↥(CFSG.Blueprint.suzukiGroup a K))).mulVec x) =
        regRep k u (ψ x) := by
    intro u x
    have h := equivFun_orbit_basis k ρ b hb_mul u x
    simpa [ψ, ρ, matRep_apply] using h
  have h1 : ψ (∑ u : ↥(suzukiU a K),
      (szT k hK (szOmega a) (u : ↥(CFSG.Blueprint.suzukiGroup a K))).mulVec
        (φ ((szT k hK (szOmega a) ((u : ↥(CFSG.Blueprint.suzukiGroup a K))⁻¹)).mulVec y))) =
      ∑ u : ↥(suzukiU a K), regRep k u (L (regRep k u⁻¹ (ψ y))) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hψ u]
    congr 1
    show ψ (φ ((szT k hK (szOmega a) ((u : ↥(CFSG.Blueprint.suzukiGroup a K))⁻¹)).mulVec y)) =
      L (regRep k u⁻¹ (ψ y))
    rw [show φ _ = ψ.symm (L (ψ _)) from rfl, LinearEquiv.apply_symm_apply,
      ← Subgroup.coe_inv, hψ (u⁻¹)]
  have h2 : ψ (∑ u : ↥(suzukiU a K),
      (szT k hK (szOmega a) (u : ↥(CFSG.Blueprint.suzukiGroup a K))).mulVec
        (φ ((szT k hK (szOmega a) ((u : ↥(CFSG.Blueprint.suzukiGroup a K))⁻¹)).mulVec y))) =
      ψ y := by
    rw [h1, hreg (ψ y)]
  exact ψ.injective h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
