module

public import CFSG.Quasithin.Background.HSL3S77Coord
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch7Sec77Setup
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

section Fix

variable {V : Subgroup G} (hV : IsElemAbelian 2 V)

omit [Finite G] in
theorem mem_centralizer_iff_convI {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) {v : G}
    (hv : v ∈ V) :
    v ∈ Subgroup.centralizer ({x} : Set G) ↔ convI hV ⟨x, hx⟩ (IntMod.mk hV ⟨v, hv⟩) =
      IntMod.mk hV ⟨v, hv⟩ := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply IntMod.val_injective
    rw [convI_apply_val]
    change x * v * x⁻¹ = v
    rw [← h, mul_inv_cancel_right]
  · intro h
    have h1 := congrArg IntMod.val h
    rw [convI_apply_val] at h1
    change x * v * x⁻¹ = v at h1
    calc v * x = (x * v * x⁻¹) * x := by rw [h1]
      _ = x * v := by group

end Fix

omit [Finite G] in
theorem pow_apply_eq_self {W : Type*} [Group W] {φ : MulAut W} {x : W} (h : φ x = x) (n : ℕ) :
    (φ ^ n) x = x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, h, ih]

omit [Finite G] in
theorem pow_two_pow_pow {W : Type*} [Group W] {φ : MulAut W} (h3 : φ ^ 3 = 1) (k : ℕ) :
    (φ ^ 2 ^ k) ^ 2 ^ k = φ := by
  have h : 2 ^ k * 2 ^ k = 3 * (4 ^ k / 3) + 1 := by
    have h1 : 2 ^ k * 2 ^ k = 4 ^ k := by rw [← mul_pow]; norm_num
    have h2 : 4 ^ k % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    omega
  rw [← pow_mul, h, pow_succ, pow_mul, h3, one_pow, one_mul]

theorem exists_odd_pow (x : G) : ∃ k : ℕ, Odd (orderOf (x ^ 2 ^ k)) ∧ ∃ m : ℕ, Odd m ∧
    orderOf x = 2 ^ k * m := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨k, Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one ?_), m, hm, hn⟩
  rw [← pow_mul, ← hn, pow_orderOf_eq_one]

namespace Setup

variable (S : Setup T L I)
include S

theorem exists_model_th0 {θ : G} (hθL : θ ∈ L)
    (hθ3 : θ ^ 3 ∈ Subgroup.centralizer (fsuV T I : Set G))
    (hθ1 : θ ∉ Subgroup.centralizer (fsuV T I : Set G)) :
    ∃ θ' ∈ L, Odd (orderOf θ') ∧
      (∀ v ∈ fsuV T I, v ∈ Subgroup.centralizer ({θ'} : Set G) ↔
        v ∈ Subgroup.centralizer ({θ} : Set G)) ∧
      ∃ (hθ' : θ' ∈ Subgroup.normalizer (fsuV T I : Set G))
        (e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)),
        (autI S.hV (fsuL0 T L)).map (congrHom e) = pairSL (ZMod 2) ∧
        (autI S.hV ⊤).map (congrHom e) ≤ pairNorm (ZMod 2) ∧
        (intSub S.hV I).map e.toMonoidHom = V₁ (ZMod 2) ∧
        congrHom e (convI S.hV ⟨θ', hθ'⟩) = SL3One.rho th0 := by
  have hθN : θ ∈ Subgroup.normalizer (fsuV T I : Set G) := S.L_le_normalizer_V hθL
  set θb := convI S.hV ⟨θ, hθN⟩ with hθb
  have hθb3 : θb ^ 3 = 1 := by
    rw [hθb, ← map_pow]
    exact (convI_eq_one_iff S.hV _).mpr hθ3
  have hθb1 : θb ≠ 1 := fun h => hθ1 ((convI_eq_one_iff S.hV _).mp h)
  obtain ⟨k, hodd, -⟩ := exists_odd_pow θ
  have hθ₁L : θ ^ 2 ^ k ∈ L := L.pow_mem hθL _
  have hθ₁N : θ ^ 2 ^ k ∈ Subgroup.normalizer (fsuV T I : Set G) := S.L_le_normalizer_V hθ₁L
  have hθb₁ : convI S.hV ⟨θ ^ 2 ^ k, hθ₁N⟩ = θb ^ 2 ^ k := by
    rw [hθb, ← map_pow]
    rfl
  have hθb₁3 : (θb ^ 2 ^ k) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hθb3, one_pow]
  have hθb₁1 : θb ^ 2 ^ k ≠ 1 := by
    intro h
    apply hθb1
    rw [← pow_two_pow_pow hθb3 k, h, one_pow]
  have hfix : ∀ v ∈ fsuV T I, v ∈ Subgroup.centralizer ({θ ^ 2 ^ k} : Set G) ↔
      v ∈ Subgroup.centralizer ({θ} : Set G) := by
    intro v hv
    rw [mem_centralizer_iff_convI S.hV hθ₁N hv, mem_centralizer_iff_convI S.hV hθN hv, hθb₁]
    constructor
    · intro h
      have h' := pow_apply_eq_self h (2 ^ k)
      rwa [pow_two_pow_pow hθb3 k] at h'
    · intro h
      exact pow_apply_eq_self h _
  obtain ⟨htw, hnat⟩ := S.row
  obtain ⟨t, -, φ, hφN, hinf, hsup, hniso, -⟩ := exists_twist_eq S.hV S.hN S.hNM htw
  have hL3 : BinaryNaturalSL (V := IntMod (fsuV T I) S.hV) (autI S.hV (fsuL0 T L))
      (intSub S.hV I) ⊥ 3 1 := hnat
  have hθ₁H : convI S.hV ⟨θ ^ 2 ^ k, hθ₁N⟩ ∈ autI S.hV (fsuL0 T L) :=
    convI_mem_autI S.hV (by rw [← S.hL]; exact hθ₁L) hθ₁N
  rw [hθb₁] at hθ₁H
  obtain ⟨e, he, hNe, hV₁, hθe⟩ :=
    S77.exists_model_th0 hL3 hφN hinf hsup hniso hθ₁H hθb₁3 hθb₁1
  have hMe : (autI S.hV ⊤).map (congrHom e) ≤ pairNorm (ZMod 2) :=
    (Subgroup.map_mono S.autI_top_le).trans hNe.le
  rcases hθe with hθe | hθe
  · refine ⟨θ ^ 2 ^ k, hθ₁L, hodd, hfix, hθ₁N, e, he, hMe, hV₁, ?_⟩
    rw [hθb₁]
    exact hθe
  ·
    have hsqL : (θ ^ 2 ^ k) ^ 2 ∈ L := L.pow_mem hθ₁L _
    have hsqN : (θ ^ 2 ^ k) ^ 2 ∈ Subgroup.normalizer (fsuV T I : Set G) :=
      S.L_le_normalizer_V hsqL
    have hsqb : convI S.hV ⟨(θ ^ 2 ^ k) ^ 2, hsqN⟩ = (θb ^ 2 ^ k) ^ 2 := by
      rw [← hθb₁, ← map_pow]
      rfl
    have h4 : ((θb ^ 2 ^ k) ^ 2) ^ 2 = θb ^ 2 ^ k := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hθb₁3, one_mul]
    refine ⟨(θ ^ 2 ^ k) ^ 2, hsqL, Odd.of_dvd_nat hodd (orderOf_pow_dvd 2), fun v hv => ?_,
      hsqN, e, he, hMe, hV₁, ?_⟩
    · rw [← hfix v hv, mem_centralizer_iff_convI S.hV hsqN hv,
        mem_centralizer_iff_convI S.hV hθ₁N hv, hsqb, hθb₁]
      constructor
      · intro h
        have h' := pow_apply_eq_self h 2
        rwa [h4] at h'
      · intro h
        exact pow_apply_eq_self h 2
    · rw [hsqb]
      have h2 : th0 * th0 * (th0 * th0) = th0 := by
        rw [← pow_two, ← pow_two, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ,
          th0_pow_three, one_mul]
      exact ((map_pow (congrHom e) _ 2).trans (congrArg (· ^ 2) hθe)).trans
        ((map_pow SL3One.rho _ 2).symm.trans (by rw [pow_two, h2]))

end Setup

end CFSG.Quasithin.H13.Sec77
