module

public import CFSG.Timmesfeld.Transvection.OddModelPairs
public import CFSG.Timmesfeld.Transvection.OddModelBlock
public import CFSG.Timmesfeld.Transvection.PresSUHalf
import CFSG.Timmesfeld.Transvection.OddPairsModel
import CFSG.Timmesfeld.Transvection.OddModelWeyl
import CFSG.Timmesfeld.Transvection.OddModelHeis
import CFSG.Timmesfeld.Transvection.OddModelBC2Struct
import CFSG.Timmesfeld.Transvection.PresSU
import CFSG.Assembly.Subnormal
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Timmesfeld.Transvection.Pres
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)

abbrev cLastIdx (r : ℕ) (hr : 2 ≤ r) : Fin (2 * r / 2) :=
  ⟨2 * r / 2 - 1, Nat.sub_lt (Nat.div_pos (Nat.le_mul_of_pos_right 2
    (Nat.lt_of_lt_of_le Nat.two_pos hr)) Nat.two_pos) Nat.one_pos⟩

abbrev cPrevIdx (r : ℕ) (hr : 2 ≤ r) : Fin (2 * r / 2) :=
  ⟨2 * r / 2 - 2, Nat.sub_lt (Nat.div_pos (Nat.le_mul_of_pos_right 2
    (Nat.lt_of_lt_of_le Nat.two_pos hr)) Nat.two_pos) Nat.two_pos⟩

theorem finCastOdd_cLastIdx {r : ℕ} (hr : 2 ≤ r) :
    finCastOdd r (cLastIdx r hr) = bcLastIdx r (Nat.one_le_of_lt hr) := by
  apply Fin.ext
  simp only [cLastIdx, bcLastIdx, val_finCastOdd, Fin.val_mk]
  omega

theorem finCastOdd_cPrevIdx {r : ℕ} (hr : 2 ≤ r) :
    finCastOdd r (cPrevIdx r hr) = bcPrevIdx r hr := by
  apply Fin.ext
  simp only [cPrevIdx, bcPrevIdx, val_finCastOdd, Fin.val_mk]
  omega

theorem finCastOdd_symm_bcLastIdx {r : ℕ} (hr : 2 ≤ r) :
    (finCastOdd r).symm (bcLastIdx r (Nat.one_le_of_lt hr)) = cLastIdx r hr := by
  rw [← finCastOdd_cLastIdx hr]
  exact (finCastOdd r).symm_apply_apply _

theorem finCastOdd_symm_bcPrevIdx {r : ℕ} (hr : 2 ≤ r) :
    (finCastOdd r).symm (bcPrevIdx r hr) = cPrevIdx r hr := by
  rw [← finCastOdd_cPrevIdx hr]
  exact (finCastOdd r).symm_apply_apply _

structure OddFrameCompatible {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hFn : Nat.card F = (2 ^ n) ^ 2) {r : ℕ} (hr : 2 ≤ r) {H : Type} [Group H]
    (Ψ₀ : SU (unitaryInvolution F 2 n) (2 * r) →* H)
    (θ : SU (unitaryInvolution F 2 n) 3 →* H) : Prop where
  long_last : ∀ c, unitaryInvolution F 2 n c = c →
    Ψ₀ (suLong (unitaryInvolution F 2 n) (Sum.inl (cLastIdx r hr)) c) =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) ∧
      Ψ₀ (suLong (unitaryInvolution F 2 n) (Sum.inr (cLastIdx r hr)) c) =
        θ (suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (3 / 2))) c)
  commute_short : ∀ i : Fin (2 * r / 2), i.val + 3 ≤ r →
    ∀ x ∈ CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Universal.Unitary.rootGroup
      (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn) (2 * r)) i,
      ∀ A, Commute (Ψ₀ x) (θ A)
  commute_prev : ∀ c, unitaryInvolution F 2 n c = c → ∀ A,
    Commute (Ψ₀ (suLong (unitaryInvolution F 2 n) (Sum.inl (cPrevIdx r hr)) c)) (θ A) ∧
      Commute (Ψ₀ (suLong (unitaryInvolution F 2 n) (Sum.inr (cPrevIdx r hr)) c)) (θ A)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2)
  {r : ℕ} (hr : 2 ≤ r) {H : Type} [Group H]
  (Ψ₀ : SU (unitaryInvolution F 2 n) (2 * r) →* H) (θ : SU (unitaryInvolution F 2 n) 3 →* H)

@[expose] noncomputable def oddPrevLift : SU (unitaryInvolution F 2 n) 3 →* H :=
  (MulAut.conj (Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
    (cPrevIdx r hr)))).toMonoidHom.comp θ

theorem oddPrevLift_apply (A : SU (unitaryInvolution F 2 n) 3) :
    oddPrevLift hFn hr Ψ₀ θ A =
      Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ (cPrevIdx r hr)) *
        θ A * (Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
          (cPrevIdx r hr)))⁻¹ := rfl

noncomputable def oddFrameMap (γ : Fin ((2 * r + 1) / 2) → ℤ)
    (x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup γ) : H :=
  if Even (γ (bcLastIdx r (Nat.one_le_of_lt hr))) then
    Ψ₀ (Function.invFun (oddEmb (unitaryInvolution F 2 n) r)
      (x : SU (unitaryInvolution F 2 n) (2 * r + 1)))
  else if γ (bcPrevIdx r hr) = 0 then
    θ (Function.invFun (su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
      (bcLastIdx r (Nat.one_le_of_lt hr))) (x : SU (unitaryInvolution F 2 n) (2 * r + 1)))
  else
    oddPrevLift hFn hr Ψ₀ θ (Function.invFun (su3Emb (unitaryInvolution F 2 n)
      (Nat.not_even_two_mul_add_one r) (bcPrevIdx r hr))
        (x : SU (unitaryInvolution F 2 n) (2 * r + 1)))

theorem oddFrameMap_eq_of_even {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (hγ : Even (γ (bcLastIdx r (Nat.one_le_of_lt hr))))
    (x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup γ)
    (y : SU (unitaryInvolution F 2 n) (2 * r)) (hy : oddEmb (unitaryInvolution F 2 n) r y = x) :
    oddFrameMap hFn hr Ψ₀ θ γ x = Ψ₀ y := by
  rw [oddFrameMap, if_pos hγ]
  rw [← hy, Function.leftInverse_invFun
    (oddEmb_injective (σ := unitaryInvolution F 2 n) (r := r)) y]

theorem oddFrameMap_eq_of_last {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (hγ : ¬Even (γ (bcLastIdx r (Nat.one_le_of_lt hr)))) (hP : γ (bcPrevIdx r hr) = 0)
    (x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup γ) (A : SU (unitaryInvolution F 2 n) 3)
    (hA : su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
      (bcLastIdx r (Nat.one_le_of_lt hr)) A = x) :
    oddFrameMap hFn hr Ψ₀ θ γ x = θ A := by
  rw [oddFrameMap, if_neg hγ, if_pos hP]
  rw [← hA, Function.leftInverse_invFun
    (su3Emb_injective (σ := unitaryInvolution F 2 n) (n := 2 * r + 1)
      (Nat.not_even_two_mul_add_one r) (bcLastIdx r (Nat.one_le_of_lt hr))) A]

theorem oddFrameMap_eq_of_prev {γ : Fin ((2 * r + 1) / 2) → ℤ}
    (hγ : ¬Even (γ (bcLastIdx r (Nat.one_le_of_lt hr)))) (hP : γ (bcPrevIdx r hr) ≠ 0)
    (x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup γ) (A : SU (unitaryInvolution F 2 n) 3)
    (hA : su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
      (bcPrevIdx r hr) A = x) :
    oddFrameMap hFn hr Ψ₀ θ γ x = oddPrevLift hFn hr Ψ₀ θ A := by
  rw [oddFrameMap, if_neg hγ, if_neg hP]
  rw [← hA, Function.leftInverse_invFun
    (su3Emb_injective (σ := unitaryInvolution F 2 n) (n := 2 * r + 1)
      (Nat.not_even_two_mul_add_one r) (bcPrevIdx r hr)) A]

theorem oddFrameMap_eq_of_toStd_last {γ : Fin ((2 * r + 1) / 2) → ℤ}
    {a : Fin ((2 * r + 1) / 2) ⊕ Fin ((2 * r + 1) / 2)}
    (ha : idx a = bcLastIdx r (Nat.one_le_of_lt hr)) (hγ : toStd (2 * r + 1) γ = wt a)
    (x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup γ) (A : SU (unitaryInvolution F 2 n) 3)
    (hA : su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
      (bcLastIdx r (Nat.one_le_of_lt hr)) A = x) :
    oddFrameMap hFn hr Ψ₀ θ γ x = θ A := by
  have hγ' : ¬Even (γ (bcLastIdx r (Nat.one_le_of_lt hr))) :=
    not_even_last_of_toStd_eq_wt hr (Or.inl ha) hγ
  have hP : γ (bcPrevIdx r hr) = 0 :=
    (prev_eq_zero_iff_of_toStd_eq_wt hr (Or.inl ha) hγ).2 ha
  exact oddFrameMap_eq_of_last hFn hr Ψ₀ θ hγ' hP x A hA

theorem oddFrameMap_eq_of_toStd_prev {γ : Fin ((2 * r + 1) / 2) → ℤ}
    {a : Fin ((2 * r + 1) / 2) ⊕ Fin ((2 * r + 1) / 2)}
    (ha : idx a = bcPrevIdx r hr) (hγ : toStd (2 * r + 1) γ = wt a)
    (x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup γ) (A : SU (unitaryInvolution F 2 n) 3)
    (hA : su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
      (bcPrevIdx r hr) A = x) :
    oddFrameMap hFn hr Ψ₀ θ γ x = oddPrevLift hFn hr Ψ₀ θ A := by
  have hγ' : ¬Even (γ (bcLastIdx r (Nat.one_le_of_lt hr))) :=
    not_even_last_of_toStd_eq_wt hr (Or.inr ha) hγ
  have hP : γ (bcPrevIdx r hr) ≠ 0 := by
    intro hzero
    exact bcPrevIdx_ne_bcLastIdx hr
      (ha.symm.trans ((prev_eq_zero_iff_of_toStd_eq_wt hr (Or.inr ha) hγ).1 hzero))
  exact oddFrameMap_eq_of_prev hFn hr Ψ₀ θ hγ' hP x A hA

namespace OddFrameCompatible

variable {hFn hr Ψ₀ θ}

theorem map_levelWeyl_last (hd : OddFrameCompatible hFn hr Ψ₀ θ) :
    Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩ (cLastIdx r hr)) =
      θ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
        (0 : Fin (3 / 2))) := by
  have hL : ¬ (cLastIdx r hr).val + 1 < (2 * r) / 2 := by
    simp only [cLastIdx, Fin.val_mk]
    omega
  have h0 : ¬ (0 : Fin (3 / 2)).val + 1 < 3 / 2 := by decide
  rw [levelWeyl_one_last_eq (m := 2 * r) (unitaryInvolution_involutive hFn) hL,
    levelWeyl_one_last_eq (m := 3) (unitaryInvolution_involutive hFn) h0]
  simp only [map_mul]
  rw [(hd.long_last 1 (map_one _)).1, (hd.long_last 1 (map_one _)).2]

theorem oddPrevLift_suLong_inl (hd : OddFrameCompatible hFn hr Ψ₀ θ) {c : F}
    (hc : unitaryInvolution F 2 n c = c) :
    oddPrevLift hFn hr Ψ₀ θ (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) =
      Ψ₀ (suLong (unitaryInvolution F 2 n) (Sum.inl (cPrevIdx r hr)) c) := by
  have hjk : (cPrevIdx r hr).val + 1 = (cLastIdx r hr).val := by
    simp only [cPrevIdx, cLastIdx, Fin.val_mk]
    omega
  rw [oddPrevLift_apply, ← (hd.long_last c hc).1]
  rw [← map_inv, ← map_mul, ← map_mul]
  rw [levelWeyl_one_conj_suLong (m := 2 * r) (unitaryInvolution_involutive hFn)
    (cPrevIdx r hr) (Sum.inl (cLastIdx r hr)) c]
  rw [levelPermS_inl_of_val_succ (m := 2 * r) hjk]

theorem oddPrevLift_suLong_inr (hd : OddFrameCompatible hFn hr Ψ₀ θ) {c : F}
    (hc : unitaryInvolution F 2 n c = c) :
    oddPrevLift hFn hr Ψ₀ θ (suLong (unitaryInvolution F 2 n) (Sum.inr (0 : Fin (3 / 2))) c) =
      Ψ₀ (suLong (unitaryInvolution F 2 n) (Sum.inr (cPrevIdx r hr)) c) := by
  have hjk : (cPrevIdx r hr).val + 1 = (cLastIdx r hr).val := by
    simp only [cPrevIdx, cLastIdx, Fin.val_mk]
    omega
  rw [oddPrevLift_apply, ← (hd.long_last c hc).2]
  rw [← map_inv, ← map_mul, ← map_mul]
  rw [levelWeyl_one_conj_suLong (m := 2 * r) (unitaryInvolution_involutive hFn)
    (cPrevIdx r hr) (Sum.inr (cLastIdx r hr)) c]
  rw [levelPermS_inr_of_val_succ (m := 2 * r) hjk]

theorem commute_levelWeyl_last_oddPrevLift (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    (A : SU (unitaryInvolution F 2 n) 3) :
    Commute (Ψ₀ (levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
      (cLastIdx r hr))) (oddPrevLift hFn hr Ψ₀ θ A) := by
  let wP := levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
    (cPrevIdx r hr)
  let wL := levelWeyl (unitaryInvolution_involutive hFn) ⟨1, one_mem_traceZero⟩
    (cLastIdx r hr)
  let x := suLong (unitaryInvolution F 2 n) (Sum.inl (cPrevIdx r hr)) 1
  let y := suLong (unitaryInvolution F 2 n) (Sum.inr (cPrevIdx r hr)) 1
  have hjk : (cPrevIdx r hr).val + 1 = (cLastIdx r hr).val := by
    simp only [cPrevIdx, cLastIdx, Fin.val_mk]
    omega
  have hL : ¬ (cLastIdx r hr).val + 1 < (2 * r) / 2 := by
    simp only [cLastIdx, Fin.val_mk]
    omega
  have hconj := levelWeyl_one_conj_levelWeyl_one_last (m := 2 * r)
    (unitaryInvolution_involutive hFn) hjk hL
  have hinv := levelWeyl_one_inv (m := 2 * r) (unitaryInvolution_involutive hFn)
    (cPrevIdx r hr)
  rw [hinv] at hconj
  have hsq : wP * wP = 1 := by
    calc wP * wP = wP * wP⁻¹ := by rw [hinv]
      _ = 1 := mul_inv_cancel wP
  change wP * wL * wP = x * y * x at hconj
  have hw : wL = wP * (x * y * x) * wP⁻¹ := by
    rw [hinv]
    calc wL = (wP * wP) * wL * (wP * wP) := by rw [hsq, one_mul, mul_one]
      _ = wP * (wP * wL * wP) * wP := by group
      _ = wP * (x * y * x) * wP := by rw [hconj]
  change Commute (Ψ₀ wL) (oddPrevLift hFn hr Ψ₀ θ A)
  rw [hw, map_mul, map_mul, oddPrevLift_apply, map_inv, map_mul, map_mul]
  refine (Commute.conj_iff (Ψ₀ wP)).2 ?_
  have hx := (hd.commute_prev 1 (map_one _) A).1
  have hy := (hd.commute_prev 1 (map_one _) A).2
  change Commute (Ψ₀ x * Ψ₀ y * Ψ₀ x) (θ A)
  exact (hx.mul_left hy).mul_left hx

theorem exists_oddFrameMap_ne_one (hd : OddFrameCompatible hFn hr Ψ₀ θ) {c : F}
    (hc : unitaryInvolution F 2 n c = c)
    (hne : Ψ₀ (suLong (unitaryInvolution F 2 n) (Sum.inl (cLastIdx r hr)) c) ≠ 1) :
    ∃ k : Fin ((2 * r + 1) / 2), ∃ x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      (Pi.single k 1), oddFrameMap hFn hr Ψ₀ θ _ x ≠ 1 := by
  have hmem : suLong (unitaryInvolution F 2 n)
      (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) c ∈
      (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
        (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) := by
    rw [← suHeis_zero_left (unitaryInvolution_involutive hFn)
      (Nat.not_even_two_mul_add_one r) (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) c]
    exact suHeis_mem (unitaryInvolution_involutive hFn) (Nat.not_even_two_mul_add_one r)
      (toStd_bc2 hr).2.1 0 c
  refine ⟨bcLastIdx r (Nat.one_le_of_lt hr),
    ⟨suLong (unitaryInvolution F 2 n) (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) c, hmem⟩,
    ?_⟩
  have hγne : ¬Even ((Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1 :
      Fin ((2 * r + 1) / 2) → ℤ) (bcLastIdx r (Nat.one_le_of_lt hr))) := by
    rw [Pi.single_eq_same]
    exact Int.not_even_one
  have hP : (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1 :
      Fin ((2 * r + 1) / 2) → ℤ) (bcPrevIdx r hr) = 0 := by
    rw [Pi.single_eq_of_ne (bcPrevIdx_ne_bcLastIdx hr)]
  have hA : su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
      (bcLastIdx r (Nat.one_le_of_lt hr))
      (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) =
      (⟨suLong (unitaryInvolution F 2 n)
        (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) c, hmem⟩ :
        (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
          (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) := by
    rw [su3Emb_suLong_inl]
  have hval := oddFrameMap_eq_of_last hFn hr Ψ₀ θ hγne hP
    ⟨suLong (unitaryInvolution F 2 n) (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) c, hmem⟩
    (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) hA
  change oddFrameMap hFn hr Ψ₀ θ
      (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)
      ⟨suLong (unitaryInvolution F 2 n) (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) c,
        hmem⟩ ≠ 1
  erw [hval, ← (hd.long_last c hc).1]
  exact hne

private theorem oddEmb_eq_of_mem_unitaryLongRoot
    (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    {Φ : SU (unitaryInvolution F 2 n) (2 * r + 1) →* H}
    (hΦ : ∀ x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1),
      Φ x = oddFrameMap hFn hr Ψ₀ θ _ x)
    (h : 2 ≤ 2 * r + 1) (h' : 2 ≤ 2 * r)
    {y : SU (unitaryInvolution F 2 n) (2 * r)}
    (hy : y ∈ (Unitary.rootDatum hFn (2 * r)).rootGroup (unitaryLongRoot (2 * r) h')) :
    Φ (oddEmb (unitaryInvolution F 2 n) r y) = Ψ₀ y := by
  obtain ⟨h1, h2⟩ := rootGroup_unitaryLongRoot_odd (unitaryInvolution_involutive hFn) hr h h'
  have hX : (Unitary.rootDatum hFn (2 * r)).rootGroup (unitaryLongRoot (2 * r) h') =
      (Unitary.rootDatum hFn (2 * r)).rootGroup (Pi.single (cLastIdx r hr) 1) := by
    rw [unitaryLongRoot_eq (even_two_mul r) h']
    congr 1
  have hk : ¬ (cLastIdx r hr).val + 1 < (2 * r) / 2 := by
    simp only [cLastIdx, Fin.val_mk]
    omega
  have hγ : toStd (2 * r) (Pi.single (cLastIdx r hr) 1) =
      rt (Sum.inl (cLastIdx r hr)) (Sum.inl (cLastIdx r hr)) :=
    toStd_single_last_even (m := 2 * r) (i := cLastIdx r hr) hk (even_two_mul r)
  have hy0 := hy
  erw [hX] at hy
  obtain ⟨c, hc0, hyc⟩ := (mem_rootGroup_iff_suLong
    (unitaryInvolution_involutive hFn) (even_two_mul r)
    (Sum.inl (cLastIdx r hr)) hγ y).mp hy
  have hc : unitaryInvolution F 2 n c = c := add_map_eq_zero_iff.1 hc0
  have hoddEmb_y : oddEmb (unitaryInvolution F 2 n) r y =
      suLong (unitaryInvolution F 2 n) (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) c := by
    rw [← hyc, oddEmb_suLong, sCast_inl, finCastOdd_cLastIdx]
  have hodd_mem : oddEmb (unitaryInvolution F 2 n) r y ∈
      Unitary.rootGroup (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (2 * r + 1) (unitaryLongRoot (2 * r + 1) h) := by
    rw [h1]
    exact Subgroup.mem_map.mpr ⟨y, hy0, rfl⟩
  have hmem : suLong (unitaryInvolution F 2 n)
      (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) c ∈
      Unitary.rootGroup (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (2 * r + 1) (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1) := by
    rw [← hoddEmb_y]
    exact h2 hodd_mem
  have hγne : ¬Even ((Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1 :
      Fin ((2 * r + 1) / 2) → ℤ) (bcLastIdx r (Nat.one_le_of_lt hr))) := by
    rw [Pi.single_eq_same]
    exact Int.not_even_one
  have hP : (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1 :
      Fin ((2 * r + 1) / 2) → ℤ) (bcPrevIdx r hr) = 0 := by
    rw [Pi.single_eq_of_ne (bcPrevIdx_ne_bcLastIdx hr)]
  have hA : su3Emb (unitaryInvolution F 2 n) (Nat.not_even_two_mul_add_one r)
      (bcLastIdx r (Nat.one_le_of_lt hr))
      (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) =
      (⟨suLong (unitaryInvolution F 2 n) (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) c,
        hmem⟩ : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
          (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1)) := by
    rw [su3Emb_suLong_inl]
  have hval := oddFrameMap_eq_of_last hFn hr Ψ₀ θ hγne hP
    ⟨suLong (unitaryInvolution F 2 n) (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) c, hmem⟩
    (suLong (unitaryInvolution F 2 n) (Sum.inl (0 : Fin (3 / 2))) c) hA
  have hΦx := hΦ ⟨suLong (unitaryInvolution F 2 n)
    (Sum.inl (bcLastIdx r (Nat.one_le_of_lt hr))) c, hmem⟩
  rw [hoddEmb_y]
  erw [hΦx, hval, ← (hd.long_last c hc).1, ← hyc]

theorem map_rootGroup_unitaryLongRoot (hd : OddFrameCompatible hFn hr Ψ₀ θ)
    {Φ : SU (unitaryInvolution F 2 n) (2 * r + 1) →* H}
    (hΦ : ∀ x : (Unitary.rootDatum hFn (2 * r + 1)).rootGroup
      (Pi.single (bcLastIdx r (Nat.one_le_of_lt hr)) 1),
      Φ x = oddFrameMap hFn hr Ψ₀ θ _ x)
    (h : 2 ≤ 2 * r + 1) (h' : 2 ≤ 2 * r) :
    ((Unitary.rootDatum hFn (2 * r + 1)).rootGroup (unitaryLongRoot (2 * r + 1) h)).map Φ =
      ((Unitary.rootDatum hFn (2 * r)).rootGroup (unitaryLongRoot (2 * r) h')).map Ψ₀ := by
  obtain ⟨h1, -⟩ := rootGroup_unitaryLongRoot_odd (unitaryInvolution_involutive hFn) hr h h'
  change Subgroup.map Φ (Unitary.rootGroup (unitaryInvolution F 2 n)
      (unitaryInvolution_involutive hFn) (2 * r + 1) (unitaryLongRoot (2 * r + 1) h)) =
    Subgroup.map Ψ₀ (Unitary.rootGroup (unitaryInvolution F 2 n)
      (unitaryInvolution_involutive hFn) (2 * r) (unitaryLongRoot (2 * r) h'))
  rw [h1]
  rw [Subgroup.map_map]
  apply le_antisymm
  · rintro z ⟨y, hy, rfl⟩
    exact ⟨y, hy, (oddEmb_eq_of_mem_unitaryLongRoot hd hΦ h h' hy).symm⟩
  · rintro z ⟨y, hy, rfl⟩
    exact ⟨y, hy, oddEmb_eq_of_mem_unitaryLongRoot hd hΦ h h' hy⟩

end OddFrameCompatible

end CFSG.Timmesfeld.Transvection
