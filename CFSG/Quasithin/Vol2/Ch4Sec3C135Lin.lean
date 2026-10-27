module

public import CFSG.Quasithin.Vol2.Ch4Sec3C135Kern
public import CFSG.Quasithin.Vol2.Ch9H11Fix

public section

namespace CFSG.Quasithin.H13.Ch4.C135

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch4 Matrix
open scoped commutatorElement

variable {G : Type} [Group G] {F : Type} [Field F]

@[expose] def mix {k : ℕ} (c : Matrix (Fin k) (Fin k) F) (v : Fin k → Fin 3 → F) :
    Fin k → Fin 3 → F :=
  fun i => ∑ j, c i j • v j

theorem mix_apply {k : ℕ} (c : Matrix (Fin k) (Fin k) F) (v : Fin k → Fin 3 → F) (i : Fin k) :
    mix c v i = ∑ j, c i j • v j := rfl

theorem mix_add {k : ℕ} (c : Matrix (Fin k) (Fin k) F) (v w : Fin k → Fin 3 → F) :
    mix c (v + w) = mix c v + mix c w := by
  funext i
  simp [mix_apply, smul_add, Finset.sum_add_distrib]

theorem mix_mix {k : ℕ} (c c' : Matrix (Fin k) (Fin k) F) (v : Fin k → Fin 3 → F) :
    mix c (mix c' v) = mix (c * c') v := by
  funext i
  simp only [mix_apply, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem mix_one {k : ℕ} (v : Fin k → Fin 3 → F) : mix 1 v = v := by
  classical
  funext i
  rw [mix_apply, Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, one_smul]
  · intro j _ hj
    rw [Matrix.one_apply_ne (Ne.symm hj), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem mix_dact {k : ℕ} (c : Matrix (Fin k) (Fin k) F) (X : Matrix (Fin 3) (Fin 3) F)
    (v : Fin k → Fin 3 → F) : mix c (dact X v) = dact X (mix c v) := by
  funext i
  simp [mix_apply, dact, mulVec_sum, mulVec_smul]

theorem mix_single {k : ℕ} (c : Matrix (Fin k) (Fin k) F) (j : Fin k) (x : Fin 3 → F) :
    mix c (Pi.single j x) = fun i => c i j • x := by
  classical
  funext i
  rw [mix_apply, Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
  · intro l _ hl
    rw [Pi.single_eq_of_ne hl, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem eq_of_mix_eq {k : ℕ} {c c' : Matrix (Fin k) (Fin k) F}
    (h : ∀ v, mix c v = mix c' v) : c = c' := by
  ext i j
  have h1 := congrFun (congrFun (h (Pi.single j (Pi.single 0 1))) i) 0
  rw [mix_single, mix_single] at h1
  simpa using h1

theorem exists_mix_of_commute {k : ℕ} (T : (Fin k → Fin 3 → F) →+ (Fin k → Fin 3 → F))
    (h : ∀ (X : SpecialLinearGroup (Fin 3) F) (v : Fin k → Fin 3 → F),
      T (dact (X : Matrix (Fin 3) (Fin 3) F) v) = dact (X : Matrix (Fin 3) (Fin 3) F) (T v)) :
    ∃ c : Matrix (Fin k) (Fin k) F, ∀ v, T v = mix c v := by
  classical
  have hblock : ∀ i j, ∃ a : F, ∀ x, dactBlock T i j x = a • x := by
    intro i j
    refine exists_smul_of_commute (dactBlock T i j) fun i' j' hij b x => ?_
    show T (Pi.single j _) i = _ *ᵥ T (Pi.single j x) i
    rw [← dact_single, h]
    rfl
  choose a ha using hblock
  refine ⟨Matrix.of a, fun v => funext fun i => ?_⟩
  rw [apply_eq_sum_dactBlock T v i, mix_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [ha, Matrix.of_apply]

namespace Hyp135

variable {G₀ L : Subgroup G} {α : ↥L →* ↥(StatedSL 3 F)} (H : Hyp135 G₀ L α)
include H

theorem crd_cnj_eq_of_crd_eq {t : G} (ht : t ∈ Subgroup.normalizer (c134Q G₀ L : Set G))
    {q q' : ↥(c134Q G₀ L)} (h : crd H.dual q = crd H.dual q')
    (htU : t ∈ Subgroup.normalizer (centerOf (c134Q G₀ L) : Set G)) :
    crd H.dual (cnj ht q) = crd H.dual (cnj ht q') := by
  rw [crd_eq_iff] at h ⊢
  have e : ((cnj ht q)⁻¹ * cnj ht q' : ↥(c134Q G₀ L)) = cnj ht (q⁻¹ * q') :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_cnj]; group)
  rw [e, coe_cnj]
  exact (Subgroup.mem_normalizer_iff.mp htU _).mp h

theorem exists_mix [Finite G] {t : G} (ht : t ∈ pCoreOf 2 G₀) :
    ∃ c : Matrix (Fin 2) (Fin 2) F,
      ∀ q, crd H.dual (cnj (H.pCoreOf_le_normalizer_Q ht) q) = mix c (crd H.dual q) := by
  classical
  have htN := H.pCoreOf_le_normalizer_Q ht
  have htU := H.le_normalizer_U (pCoreOf_le 2 G₀ ht)
  choose sec hsec using crd_surjective H.dual
  have hwd : ∀ q, crd H.dual (cnj htN (sec (crd H.dual q))) = crd H.dual (cnj htN q) :=
    fun q => H.crd_cnj_eq_of_crd_eq htN (hsec _) htU
  let T : (Fin 2 → Fin 3 → F) →+ (Fin 2 → Fin 3 → F) :=
    { toFun := fun v => crd H.dual (cnj htN (sec v))
      map_zero' := by
        have h0 : crd H.dual (sec 0) = crd H.dual 1 := by rw [hsec, crd_one]
        rw [H.crd_cnj_eq_of_crd_eq htN h0 htU, cnj_one, crd_one]
      map_add' := fun v w => by
        have h1 : crd H.dual (sec (v + w)) = crd H.dual (sec v * sec w) := by
          rw [hsec, crd_mul, hsec, hsec]
        rw [H.crd_cnj_eq_of_crd_eq htN h1 htU, cnj_mul, crd_mul] }
  have hT : ∀ q, T (crd H.dual q) = crd H.dual (cnj htN q) := hwd
  obtain ⟨c, hc⟩ := exists_mix_of_commute T (fun X v => by
    obtain ⟨g, hg⟩ := H.ρd_surjective X
    have hgN := H.le_normalizer_Q (H.le g.2)
    obtain ⟨q, rfl⟩ := crd_surjective H.dual v
    have h1 : dact ((X : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
        (crd H.dual q) = crd H.dual (cnj hgN q) := by
      rw [crd_conj_true H.dual g q (cnj hgN q) rfl, ← hg]
      rfl
    rw [h1, hT, hT]
    have hcQ : t * g * t⁻¹ * (g : G)⁻¹ ∈ c134Q G₀ L := by
      have h2 := Subgroup.commutator_mem_commutator ht g.2
      rwa [commutatorElement_def] at h2
    have hcN := H.le_normalizer_Q (H.le (c134Q_le H.norm hcQ))
    have e : cnj htN (cnj hgN q) = cnj hcN (cnj hgN (cnj htN q)) :=
      Subtype.ext (by simp only [coe_cnj]; group)
    have h3 := H.crd_conj_Q ⟨_, hcQ⟩ (cnj hgN (cnj htN q)) (cnj hcN (cnj hgN (cnj htN q))) rfl
    rw [e, h3, crd_conj_true H.dual g (cnj htN q) (cnj hgN (cnj htN q)) rfl, ← hg]
    rfl)
  exact ⟨c, fun q => by rw [← hT, hc]⟩

@[expose] noncomputable def cMat [Finite G] {t : G} (ht : t ∈ pCoreOf 2 G₀) :
    Matrix (Fin 2) (Fin 2) F :=
  Classical.choose (H.exists_mix ht)

theorem crd_cnj_eq_mix [Finite G] {t : G} (ht : t ∈ pCoreOf 2 G₀) (q : ↥(c134Q G₀ L)) :
    crd H.dual (cnj (H.pCoreOf_le_normalizer_Q ht) q) = mix (H.cMat ht) (crd H.dual q) :=
  Classical.choose_spec (H.exists_mix ht) q

theorem cMat_eq_of_mix [Finite G] {t : G} (ht : t ∈ pCoreOf 2 G₀) {c : Matrix (Fin 2) (Fin 2) F}
    (hc : ∀ q, crd H.dual (cnj (H.pCoreOf_le_normalizer_Q ht) q) = mix c (crd H.dual q)) :
    H.cMat ht = c := by
  refine eq_of_mix_eq fun v => ?_
  obtain ⟨q, rfl⟩ := crd_surjective H.dual v
  rw [← H.crd_cnj_eq_mix ht, hc]

theorem cMat_mul [Finite G] {t t' : G} (ht : t ∈ pCoreOf 2 G₀) (ht' : t' ∈ pCoreOf 2 G₀) :
    H.cMat ((pCoreOf 2 G₀).mul_mem ht ht') = H.cMat ht * H.cMat ht' := by
  refine H.cMat_eq_of_mix _ fun q => ?_
  rw [← mix_mix, ← H.crd_cnj_eq_mix ht', ← H.crd_cnj_eq_mix ht, ← cnj_mul_left]

theorem cMat_one [Finite G] : H.cMat (pCoreOf 2 G₀).one_mem = 1 := by
  refine H.cMat_eq_of_mix _ fun q => ?_
  rw [mix_one]
  congr 1
  exact Subtype.ext (by simp [coe_cnj])

theorem cMat_congr [Finite G] {t t' : G} (ht : t ∈ pCoreOf 2 G₀) (ht' : t' ∈ pCoreOf 2 G₀)
    (h : t = t') : H.cMat ht = H.cMat ht' := by
  subst h
  rfl

theorem cMat_pow [Finite G] {t : G} (ht : t ∈ pCoreOf 2 G₀) (m : ℕ) :
    H.cMat ((pCoreOf 2 G₀).pow_mem ht m) = H.cMat ht ^ m := by
  induction m with
  | zero => exact (H.cMat_congr _ (pCoreOf 2 G₀).one_mem (pow_zero t)).trans H.cMat_one
  | succ m ih =>
    rw [H.cMat_congr _ ((pCoreOf 2 G₀).mul_mem ((pCoreOf 2 G₀).pow_mem ht m) ht) (pow_succ t m),
      H.cMat_mul ((pCoreOf 2 G₀).pow_mem ht m) ht, ih, pow_succ]

theorem det_cMat [Finite G] [CharP F 2] {t : G} (ht : t ∈ pCoreOf 2 G₀) :
    (H.cMat ht).det = 1 := by
  obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 G₀) ⟨t, ht⟩
  have htm : t ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have h1 : H.cMat ht ^ 2 ^ m = 1 := by
    rw [← H.cMat_pow, H.cMat_congr _ (pCoreOf 2 G₀).one_mem htm, H.cMat_one]
  have h2 : (H.cMat ht).det ^ 2 ^ m = 1 := by rw [← det_pow, h1, det_one]
  have h3 : ((H.cMat ht).det - 1) ^ 2 ^ m = 0 := by rw [sub_pow_char_pow, h2, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h3)

@[expose] noncomputable def cHom [Finite G] [CharP F 2] :
    ↥(pCoreOf 2 G₀) →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun t := ⟨H.cMat t.2, H.det_cMat t.2⟩
  map_one' := Subtype.ext H.cMat_one
  map_mul' t t' := Subtype.ext (H.cMat_mul t.2 t'.2)

theorem coe_cHom [Finite G] [CharP F 2] (t : ↥(pCoreOf 2 G₀)) :
    ((H.cHom t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      H.cMat t.2 := rfl

structure Adapted where
  e : ↥(c134Q G₀ L) → Fin 2 → Fin 3 → F
  mul : ∀ q q', e (q * q') = e q + e q'
  surj : Function.Surjective e
  ker : ∀ q, e q = 0 ↔ (q : G) ∈ centerOf (c134Q G₀ L)
  conjL : ∀ (a : ↥L) (q : ↥(c134Q G₀ L)), e (cnj (H.le_normalizer_Q (H.le a.2)) q) =
    dact ((H.ρd a : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) (e q)
  conjT : ∀ (t : G) (ht : t ∈ pCoreOf 2 G₀), ∃ s : F, ∀ q,
    e (cnj (H.pCoreOf_le_normalizer_Q ht) q) 0 = e q 0 + s • e q 1 ∧
      e (cnj (H.pCoreOf_le_normalizer_Q ht) q) 1 = e q 1

omit H in
theorem mix_uu (s : F) (v : Fin 2 → Fin 3 → F) :
    mix ((H11P.uu s : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) v 0 =
      v 0 + s • v 1 ∧
    mix ((H11P.uu s : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) v 1 =
      v 1 := by
  rw [H11P.coe_uu]
  simp [mix_apply, Fin.sum_univ_two]

theorem exists_adapted [Finite G] [Finite F] [CharP F 2] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) :
    Nonempty H.Adapted := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (H.cHom.range) :=
    (pCoreOf_isPGroup 2 G₀).of_surjective H.cHom.rangeRestrict H.cHom.rangeRestrict_surjective
  obtain ⟨g, hg⟩ := H11P.exists_conj_le_Uu hn hF hP
  set P : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F) with hPdef
  have hPinv : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * P =
      1 := by
    rw [hPdef, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  refine ⟨⟨fun q => mix P (crd H.dual q), fun q q' => by rw [crd_mul, mix_add],
    fun v => ?_, fun q => ?_, fun a q => ?_, fun t ht => ?_⟩⟩
  · obtain ⟨q, hq⟩ := crd_surjective H.dual
      (mix ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) v)
    refine ⟨q, ?_⟩
    show mix P (crd H.dual q) = v
    rw [hq, mix_mix, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, mix_one]
  · show mix P (crd H.dual q) = 0 ↔ _
    rw [← crd_eq_zero_iff H.dual]
    constructor
    · intro h
      have h1 := congrArg (mix ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)) h
      rw [mix_mix, hPinv, mix_one] at h1
      rw [h1]
      funext i
      simp [mix_apply]
    · intro h
      rw [h]
      funext i
      simp [mix_apply]
  · show mix P (crd H.dual (cnj _ q)) = dact _ (mix P (crd H.dual q))
    rw [crd_conj_true H.dual a q _ rfl, mix_dact]
    rfl
  · obtain ⟨s, hs⟩ : ∃ s, H11P.uu s = g * H.cHom ⟨t, ht⟩ * g⁻¹ := by
      have h1 := hg ⟨H.cHom ⟨t, ht⟩, ⟨_, rfl⟩, rfl⟩
      obtain ⟨s, hs⟩ := (H11P.mem_Uu).mp h1
      exact ⟨s, hs⟩
    refine ⟨s, fun q => ?_⟩
    have e : mix P (crd H.dual (cnj (H.pCoreOf_le_normalizer_Q ht) q)) =
        mix ((H11P.uu s : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          (mix P (crd H.dual q)) := by
      rw [hs, H.crd_cnj_eq_mix ht, mix_mix, mix_mix, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, coe_cHom, Matrix.mul_assoc, Matrix.mul_assoc, hPinv,
        Matrix.mul_one]
    show mix P (crd H.dual (cnj (H.pCoreOf_le_normalizer_Q ht) q)) 0 = mix P (crd H.dual q) 0 +
        s • mix P (crd H.dual q) 1 ∧ mix P (crd H.dual (cnj (H.pCoreOf_le_normalizer_Q ht) q)) 1 =
          mix P (crd H.dual q) 1
    rw [e]
    exact mix_uu s _

end Hyp135

end CFSG.Quasithin.H13.Ch4.C135

end
