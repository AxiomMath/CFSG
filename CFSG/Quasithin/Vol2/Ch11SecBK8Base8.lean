module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base7
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base5
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base6

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

theorem matrix_ext_mulVec {A B : Matrix (Fin 3) (Fin 3) K} (h : ∀ v, A *ᵥ v = B *ᵥ v) :
    A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using this

theorem trvMat_mul_self [CharP K 2] {w ψ : Fin 3 → K} (h : ψ ⬝ᵥ w = 0) :
    (1 + vecMulVec w ψ) * (1 + vecMulVec w ψ) = 1 := by
  refine matrix_ext_mulVec fun v => ?_
  rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, SL3Pair.one_add_vecMulVec_mulVec,
    SL3Pair.one_add_vecMulVec_mulVec, dotProduct_add, dotProduct_smul, h, smul_zero, add_zero,
    add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

@[expose] noncomputable def trv [CharP K 2] (w ψ : Fin 3 → K) (h : ψ ⬝ᵥ w = 0) :
    GL (Fin 3) K :=
  ⟨1 + vecMulVec w ψ, 1 + vecMulVec w ψ, trvMat_mul_self h, trvMat_mul_self h⟩

theorem coe_trv [CharP K 2] {w ψ : Fin 3 → K} (h : ψ ⬝ᵥ w = 0) :
    ((trv w ψ h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec w ψ := rfl

theorem trv_mul_self [CharP K 2] {w ψ : Fin 3 → K} (h : ψ ⬝ᵥ w = 0) :
    trv w ψ h * trv w ψ h = 1 :=
  Units.ext (trvMat_mul_self h)

theorem det_one_add_vecMulVec (w ψ : Fin 3 → K) :
    (1 + vecMulVec w ψ).det = 1 + ψ ⬝ᵥ w := by
  rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]

theorem trv_mem_statedSL [CharP K 2] {w ψ : Fin 3 → K} (h : ψ ⬝ᵥ w = 0) :
    trv w ψ h ∈ StatedSL 3 K := by
  rw [SL3Pair.mem_statedSL_iff, coe_trv, det_one_add_vecMulVec, h, add_zero]

theorem mem_fixSub_trv [CharP K 2] {w ψ : Fin 3 → K} (h : ψ ⬝ᵥ w = 0) (hw : w ≠ 0)
    (u : Fin 3 → K) : u ∈ fixSub (trv w ψ h) ↔ ψ ⬝ᵥ u = 0 := by
  rw [mem_fixSub, coe_trv, SL3Pair.one_add_vecMulVec_mulVec, add_eq_left, smul_eq_zero,
    or_iff_left hw]

theorem card_fix_trv [CharP K 2] [Finite K] {w ψ : Fin 3 → K} (h : ψ ⬝ᵥ w = 0) (hw : w ≠ 0)
    (hψ : ψ ≠ 0) :
    Nat.card {u : Fin 3 → K // ((trv w ψ h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ u = u} =
      Nat.card K ^ 2 := by
  rw [← SL3Pair.card_orth hψ]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun u => by
    rw [← mem_fixSub, mem_fixSub_trv h hw])

theorem exists_axis {A : GL (Fin 3) K} (h2 : Module.finrank K (fixSub A) = 2) :
    ∃ ψ : Fin 3 → K, ψ ≠ 0 ∧ (∀ u, u ∈ fixSub A ↔ ψ ⬝ᵥ u = 0) ∧
      ∃ w : Fin 3 → K, (A : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec w ψ := by
  have hlt : fixSub A < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => ?_
    have := h2
    rw [h, finrank_top, Module.finrank_fin_fun] at this
    omega
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  have hkerf : fixSub A = LinearMap.ker f := by
    refine Submodule.eq_of_le_of_finrank_le hf ?_
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    rw [Module.finrank_fin_fun] at h1
    have h3 : Module.finrank K (LinearMap.range f) ≠ 0 := fun h =>
      hf0 (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h))
    omega
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : Fin 3 → K, ∀ j, ψ j = f (Pi.single j 1) := ⟨_, fun _ => rfl⟩
  have hfψ : ∀ v, f v = ψ ⬝ᵥ v := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ f v, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul, mul_comm, hψdef]
    congr 2
    ext i
    simp [Pi.single_apply, eq_comm]
  have hψ : ψ ≠ 0 := by
    intro h
    apply hf0
    refine LinearMap.ext fun v => ?_
    rw [hfψ, h, zero_dotProduct, LinearMap.zero_apply]
  obtain ⟨j₁, hj₁⟩ : ∃ j, ψ j ≠ 0 := by
    by_contra h
    push Not at h
    exact hψ (funext h)
  set v₀ : Fin 3 → K := (ψ j₁)⁻¹ • Pi.single j₁ 1 with hv₀
  have hfv₀ : f v₀ = 1 := by
    rw [hv₀, map_smul, smul_eq_mul, ← hψdef]
    exact inv_mul_cancel₀ hj₁
  refine ⟨ψ, hψ, fun u => by rw [hkerf, LinearMap.mem_ker, hfψ],
    (A : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀ - v₀, SL3Pair.matrix_eq_one_add fun v => ?_⟩
  rw [SL3Pair.vecMulVec_mulVec', ← hfψ]
  have h1 : v - f v • v₀ ∈ fixSub A := by
    rw [hkerf, LinearMap.mem_ker, map_sub, map_smul, hfv₀, smul_eq_mul, mul_one, sub_self]
  rw [mem_fixSub, Matrix.mulVec_sub, Matrix.mulVec_smul] at h1
  rw [smul_sub]
  calc (A : Matrix (Fin 3) (Fin 3) K) *ᵥ v
      = ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ v - f v • ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀)) +
        f v • ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀) := by abel
    _ = (v - f v • v₀) + f v • ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀) := by rw [h1]
    _ = v + (f v • ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀) - f v • v₀) := by abel

theorem homology_of_odd [CharP K 2] {A : GL (Fin 3) K} (h2 : Module.finrank K (fixSub A) = 2)
    {p : ℕ} (hp2 : p ≠ 2) (hp : p.Prime) (hAp : A ^ p = 1) :
    ∃ l : K, l ≠ 1 ∧ l ^ p = 1 ∧ (A : Matrix (Fin 3) (Fin 3) K).det = l := by
  obtain ⟨ψ, -, -, w, hA⟩ := exists_axis h2
  have hAv : ∀ v, (A : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v + (ψ ⬝ᵥ v) • w := fun v => by
    rw [hA, SL3Pair.one_add_vecMulVec_mulVec]
  have hA1 : A ≠ 1 := by
    intro h
    have := finrank_fixSub_lt (A := A)
    rw [h] at h2
    have h3 : fixSub (1 : GL (Fin 3) K) = ⊤ :=
      eq_top_iff.mpr fun u _ => mem_fixSub.mpr (by rw [Units.val_one, Matrix.one_mulVec])
    rw [h3, finrank_top, Module.finrank_fin_fun] at h2
    omega
  have hw : w ≠ 0 := by
    rintro rfl
    exact hA1 (eq_one_of_fix fun v => by rw [hAv, smul_zero, add_zero])
  set l := 1 + ψ ⬝ᵥ w with hl
  have hAw : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ w = l • w := by rw [hAv, add_smul, one_smul]
  have hpow : ∀ k : ℕ, ((A ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = l ^ k • w := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, one_smul, Units.val_one, Matrix.one_mulVec]
    | succ k ih =>
      rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec, hAw, Matrix.mulVec_smul, ih, smul_smul,
        pow_succ, mul_comm]
  have hlp : l ^ p = 1 := by
    have h1 := hpow p
    rw [hAp, Units.val_one, Matrix.one_mulVec] at h1
    have h3 : (l ^ p - 1) • w = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hw)
  refine ⟨l, fun hl1 => ?_, hlp, by rw [hA, det_one_add_vecMulVec]⟩
  have hμ : ψ ⬝ᵥ w = 0 := by
    have := hl1
    rw [hl, add_eq_left] at this
    exact this
  have hsq : A * A = 1 := by
    have := trvMat_mul_self hμ
    exact Units.ext (by rw [Units.val_mul, hA, this, Units.val_one])
  obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
  apply hA1
  rw [← hAp, hk, pow_succ, pow_mul, sq, hsq, one_pow, one_mul]

theorem dvd_card_sub_one [Finite K] {l : K} (hl : l ≠ 1) {p : ℕ} (hp : p.Prime)
    (hlp : l ^ p = 1) : p ∣ Nat.card K - 1 := by
  have := Fintype.ofFinite K
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hlp
    exact zero_ne_one hlp
  have h1 := FiniteField.pow_card_sub_one_eq_one l hl0
  by_contra hd
  have hcop := (Nat.Prime.coprime_iff_not_dvd hp).mpr (by rwa [Nat.card_eq_fintype_card] at hd)
  have h2 : l ^ Nat.gcd p (Fintype.card K - 1) = 1 := pow_gcd_eq_one.mpr ⟨hlp, h1⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h2
  exact hl h2

theorem charP_two_of_card [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) : CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])

theorem mParam_eq [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {Y : Subgroup (MulAut (W6 K))} (h1 : diagSL K ≤ Y) (h2 : Y ≤ normD K) :
    E3.mParam Y = 2 * n := by
  have : Finite (MulAut (W6 K)) := MulEquiv.finite_left
  have h01 : (Pi.single 1 1 : Fin 3 → K) ⬝ᵥ Pi.single 0 1 = 0 := by simp
  have hw : (Pi.single 0 1 : Fin 3 → K) ≠ 0 := fun h => by simpa using congrFun h 0
  have hψ : (Pi.single 1 1 : Fin 3 → K) ≠ 0 := fun h => by simpa using congrFun h 1
  set t := matAut (dgHom (trv _ _ h01)) with ht
  have htY : t ∈ Y := h1 (matAut_dgHom_mem_diagSL (trv_mem_statedSL h01))
  have ht1 : t ≠ 1 := by
    intro h
    rw [ht, ← matAut_dgHom_one] at h
    have h3 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 1)
      (matAut_dgHom_injective h)
    simp [coe_trv, Matrix.vecMulVec_apply] at h3
  have ht2 : orderOf t = 2 := by
    refine orderOf_eq_prime ?_ ht1
    rw [ht, ← matAut_dgHom_pow, sq, trv_mul_self, matAut_dgHom_one]
  have hcard : Nat.card (FixW t) = 2 ^ (4 * n) := by
    rw [ht, card_fix_dg, card_fix_trv h01 hw hψ, hK, ← pow_mul, ← pow_mul]
    ring_nf
  have hrk : rkIdx (fixV (Subgroup.zpowers t)) = 2 * n := by
    obtain ⟨j, -, hj, hrk⟩ := exists_rkIdx_fix hK t
    rw [hcard] at hj
    have := Nat.pow_right_injective le_rfl hj
    omega
  have heven : Even (Nat.card Y) := by
    have h3 := orderOf_dvd_natCard (⟨t, htY⟩ : Y)
    rw [Subgroup.orderOf_mk, ht2] at h3
    exact even_iff_two_dvd.mpr h3
  unfold E3.mParam
  rw [ite_eq_left heven]
  refine le_antisymm (Nat.sInf_le ⟨t, htY, ht2, hrk.symm⟩)
    (le_csInf ⟨_, t, htY, ht2, hrk.symm⟩ ?_)
  rintro m ⟨s, hsY, hs2, rfl⟩
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs2
    exact absurd hs2 (by norm_num)
  exact two_mul_le_rkIdx hK (card_fix_le_of_ne_one (h2 hsY) hs1)

variable {G : Type} [Group G]

theorem exists_model_X {L W X : Subgroup G} {n : ℕ} (hW : IsElemAbelian 2 W)
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (h : TwoNaturalSum L W n)
    (hXN : X ⊓ Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      ∃ Φ : IntMod W hW ≃* W6 K, (autI hW L).map (congrHom Φ) = diagSL K ∧
        (autI hW X).map (congrHom Φ) ≤ normD K := by
  obtain ⟨K, hKf, hKfin, hK, Φ, hΦ⟩ := exists_model hW hLW h
  exact ⟨K, hKf, hKfin, charP_two_of_card hK, hK, Φ, hΦ,
    map_autI_le_normD Φ hΦ fun x hxX hxW => hXN ⟨hxX, hxW⟩⟩

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
