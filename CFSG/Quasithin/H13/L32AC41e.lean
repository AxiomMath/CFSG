module

public import CFSG.Quasithin.H13.L32AC41d
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped Pointwise

theorem exists_conj_of_card_three {X : Type*} [Group X] [Finite X] {m : ℕ}
    (hX : Nat.card X = 3 * 2 ^ m) {P Q : Subgroup X} (hP : Nat.card P = 3)
    (hQ : Nat.card Q = 3) : ∃ g : X, ∀ p ∈ P, g * p * g⁻¹ ∈ Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hidx : ∀ R : Subgroup X, Nat.card R = 3 → ¬ 3 ∣ R.index := by
    intro R hR h3
    have h := R.index_mul_card
    rw [hR, hX] at h
    have hR2 : R.index = 2 ^ m :=
      Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3) (h.trans (mul_comm 3 (2 ^ m)))
    rw [hR2] at h3
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (Nat.Coprime.pow_right m (by norm_num)) h3
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 1) (by rw [hP, pow_one])
  have hQ3 : IsPGroup 3 Q := IsPGroup.of_card (n := 1) (by rw [hQ, pow_one])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (hP3.toSylow (hidx P hP))
    (hQ3.toSylow (hidx Q hQ))
  refine ⟨g, fun p hp => ?_⟩
  have h1 : Q = MulAut.conj g • P := by
    have := congrArg (fun R : Sylow 3 X => (R : Subgroup X)) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at this
    exact this.symm
  rw [h1]
  exact Subgroup.smul_mem_pointwise_smul p (MulAut.conj g) P hp

theorem sl2_ne_br {a r b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)} (ha1 : a ≠ 1)
    (ha3 : a ^ 3 = 1) (hr1 : r ≠ 1) (hr2 : r ^ 2 = 1) (hb : b * a = a * b) :
    b * r * a * (b * r)⁻¹ ≠ a := by
  intro h
  have h1 := sl2_comm_ra a r ha1 ha3 hr1 hr2
  have e : r * a * r⁻¹ = b⁻¹ * (b * r * a * (b * r)⁻¹) * b := by group
  have h2 : b⁻¹ * a * b = a := by rw [mul_assoc, ← hb, inv_mul_cancel_left]
  rw [e, h, h2, mul_inv_cancel] at h1
  exact ha1 h1.symm

theorem mem_center_of_inv_mod {X : Type*} [Group X] [Finite X]
    (hZ : Odd (Nat.card (Subgroup.center X))) {S : Subgroup X} (hS : IsPGroup 2 S) {k a : X}
    (h3 : k ^ 3 ∈ Subgroup.center X) (h1 : a * k ∈ Subgroup.center X) (h2 : a * k⁻¹ ∈ S) :
    k ∈ Subgroup.center X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.center X with hZdef
  set s := a * k⁻¹ with hs
  have hk : k = k ^ 3 * (a * k)⁻¹ * s := by
    rw [hs]
    group
  have hz : k ^ 3 * (a * k)⁻¹ ∈ Z := mul_mem h3 (inv_mem h1)
  set z := k ^ 3 * (a * k)⁻¹ with hzdef
  have hzc : ∀ y : X, z * y = y * z := fun y => (Subgroup.mem_center_iff.mp hz y).symm
  have hks : k ^ 3 = z ^ 3 * s ^ 3 := by
    have hc : Commute z s := hzc s
    conv_lhs => rw [hk]
    rw [hc.mul_pow]
  have hs3 : s ^ 3 ∈ Z := by
    have : s ^ 3 = (z ^ 3)⁻¹ * k ^ 3 := by rw [hks, inv_mul_cancel_left]
    rw [this]
    exact mul_mem (inv_mem (pow_mem hz 3)) h3
  obtain ⟨e, he⟩ := hS ⟨s, h2⟩
  have hse : s ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  have hs31 : s ^ 3 = 1 := by
    have hodd : Odd (orderOf (⟨s ^ 3, hs3⟩ : ↥Z)) := Odd.of_dvd_nat hZ (orderOf_dvd_natCard _)
    have h2e : (⟨s ^ 3, hs3⟩ : ↥Z) ^ 2 ^ e = 1 := Subtype.ext (by
      show (s ^ 3) ^ 2 ^ e = 1
      rw [← pow_mul, mul_comm, pow_mul, hse, one_pow])
    have := map_eq_one_of_odd (MonoidHom.id ↥Z) hodd (k := e) h2e
    exact congrArg Subtype.val this
  have hs1 : s = 1 := by
    have hc : Nat.Coprime 3 (2 ^ e) := Nat.Coprime.pow_right e (by norm_num)
    have h1' : orderOf s ∣ 3 := orderOf_dvd_of_pow_eq_one hs31
    have h2' : orderOf s ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hse
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc h1' h2')
  rw [hk, hs1, mul_one]
  exact hz

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

section Inv

variable {V₂ : Subgroup G} [IsMulCommutative ↥V]

theorem psi_mem_zpowers (S14 : L32NSet14.Setting G T L V V₂)
    {ψ : ↥(L32NSet14.nX T V) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)}
    {x : G} (hxX : x ∈ L32NSet14.nX T V) (hx1 : ψ ⟨x, hxX⟩ ≠ 1) (hx3 : ψ ⟨x, hxX⟩ ^ 3 = 1)
    {g : G} (hg : g ∈ l1 T L V) (hgX : g ∈ L32NSet14.nX T V) :
    ψ ⟨g, hgX⟩ ∈ Subgroup.zpowers (ψ ⟨x, hxX⟩) := by
  have key : l1 T L V ≤
      ((Subgroup.zpowers (ψ ⟨x, hxX⟩)).comap ψ).map (L32NSet14.nX T V).subtype := by
    show Subgroup.closure _ ≤ _
    refine (Subgroup.closure_le _).mpr ?_
    rintro w ⟨⟨hwL, hwN⟩, hwo⟩
    have hwX : w ∈ L32NSet14.nX T V := ⟨S14.LV hwL, hwN⟩
    refine ⟨⟨w, hwX⟩, ?_, rfl⟩
    show ψ ⟨w, hwX⟩ ∈ Subgroup.zpowers (ψ ⟨x, hxX⟩)
    rcases sl2_trich (ψ ⟨x, hxX⟩) (ψ ⟨w, hwX⟩) hx1 hx3 with h | h | h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers _
    · rw [h]
      exact mul_mem (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
    · have hwo' : Odd (orderOf (⟨w, hwX⟩ : ↥(L32NSet14.nX T V))) := by
        rwa [Subgroup.orderOf_mk]
      rw [map_eq_one_of_odd ψ hwo' (k := 1) (by rw [pow_one]; exact h)]
      exact one_mem _
  obtain ⟨g', hg', hgg⟩ := Subgroup.mem_map.mp (key hg)
  have : g' = ⟨g, hgX⟩ := Subtype.ext hgg
  rw [← this]
  exact hg'

theorem sl2_mem_zpowers {a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)} (ha1 : a ≠ 1)
    (ha3 : a ^ 3 = 1) (hb : b ∈ Subgroup.zpowers a) : b = 1 ∨ b = a ∨ b = a * a := by
  classical
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  rw [mem_zpowers_iff_mem_range_orderOf, hoa] at hb
  simp only [Finset.mem_image, Finset.mem_range] at hb
  obtain ⟨i, hi, hib⟩ := hb
  interval_cases i
  · left
    rw [← hib, pow_zero]
  · right; left
    rw [← hib, pow_one]
  · right; right
    rw [← hib, pow_two]

theorem exists_inv_s (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (S : Setting147 G T L V H) (S14 : L32NSet14.Setting G T L V V₂)
    {ψ : ↥(L32NSet14.nX T V) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)}
    {x : G} (hxl : x ∈ l1 T L V) (hxX : x ∈ L32NSet14.nX T V) (hx1 : ψ ⟨x, hxX⟩ ≠ 1)
    (hx3 : x ^ 3 = 1)
    {t : G} (htT : t ∈ T) (htL : t ∈ L) (htX : t ∈ L32NSet14.nX T V) (ht1 : ψ ⟨t, htX⟩ ≠ 1) :
    ∃ s ∈ L, s ∈ l1 T L V ⊔ T ∧ (∃ k : ℕ, s ^ 2 ^ k = 1) ∧ s * x * s⁻¹ = x⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hψx3 : ψ ⟨x, hxX⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxX⟩ : ↥(L32NSet14.nX T V)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hψt2 : ψ ⟨t, htX⟩ ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := S.hyp.fsu.sylow.1 ⟨t, htT⟩
    refine L32NSet14.sl2_sq_of_two (k := k) ?_
    rw [← map_pow]
    have : (⟨t, htX⟩ : ↥(L32NSet14.nX T V)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hx1' : x ≠ 1 := by
    rintro rfl
    exact hx1 (by rw [show (⟨1, hxX⟩ : ↥(L32NSet14.nX T V)) = 1 from rfl, map_one])
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hl1X : l1 T L V ≤ L32NSet14.nX T V := hl1 ▸ S14.L1_le_X
  obtain ⟨m, hm⟩ := (pCoreOf_isPGroup 2 (l1 T L V)).exists_card_eq
  have hcard : Nat.card ↥(l1 T L V) = 3 * 2 ^ m := by
    have h := Subgroup.relIndex_mul_card (pCoreOf 2 (l1 T L V)) (l1 T L V)
    rw [relIndex_l1 h1222 h1332 h1334 S.hyp, inf_eq_left.mpr (pCoreOf_le 2 _), hm] at h
    exact h.symm
  have hxt : t * x * t⁻¹ ∈ l1 T L V :=
    (Subgroup.mem_normalizer_iff.mp (Setting147.T_le_N_l1 S h1332 htT) x).mp hxl
  have hord : ∀ (y : G) (hy : y ∈ l1 T L V), y ^ 3 = 1 → y ≠ 1 →
      Nat.card (Subgroup.zpowers (⟨y, hy⟩ : ↥(l1 T L V))) = 3 := by
    intro y hy hy3 hy1
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (Subtype.ext (by simpa using hy3))
      (fun h => hy1 (congrArg Subtype.val h))
  have hxt3 : (t * x * t⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hx3, mul_one, mul_inv_cancel]
  have hxt1 : t * x * t⁻¹ ≠ 1 := fun h => hx1' (by
    have := congrArg (fun z => t⁻¹ * z * t) h
    simpa [mul_assoc] using this)
  obtain ⟨g, hg⟩ := exists_conj_of_card_three hcard (hord _ hxt hxt3 hxt1) (hord x hxl hx3 hx1')
  have hgx := hg _ (Subgroup.mem_zpowers _)
  have hgl : (g : G) ∈ l1 T L V := g.2
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : G, s₁ = (g : G) * t := ⟨_, rfl⟩
  have hs₁x : s₁ * x * s₁⁻¹ ∈ Subgroup.zpowers x := by
    have h1 : ((g * ⟨t * x * t⁻¹, hxt⟩ * g⁻¹ : ↥(l1 T L V)) : G) ∈
        (Subgroup.zpowers (⟨x, hxl⟩ : ↥(l1 T L V))).map (l1 T L V).subtype := ⟨_, hgx, rfl⟩
    rw [MonoidHom.map_zpowers] at h1
    have e : s₁ * x * s₁⁻¹ = ((g * ⟨t * x * t⁻¹, hxt⟩ * g⁻¹ : ↥(l1 T L V)) : G) := by
      rw [hs₁]
      simp [mul_assoc]
    rw [e]
    exact h1
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1'
  have hcases : s₁ * x * s₁⁻¹ = 1 ∨ s₁ * x * s₁⁻¹ = x ∨ s₁ * x * s₁⁻¹ = x * x := by
    rw [mem_zpowers_iff_mem_range_orderOf, hox] at hs₁x
    simp only [Finset.mem_image, Finset.mem_range] at hs₁x
    obtain ⟨i, hi, hix⟩ := hs₁x
    interval_cases i
    · left
      rw [← hix, pow_zero]
    · right; left
      rw [← hix, pow_one]
    · right; right
      rw [← hix, pow_two]
  have hgX : (g : G) ∈ L32NSet14.nX T V := hl1X hgl
  have hs₁X : s₁ ∈ L32NSet14.nX T V := by
    rw [hs₁]
    exact mul_mem hgX htX
  have hinv : s₁ * x * s₁⁻¹ = x⁻¹ := by
    rcases hcases with h | h | h
    · exfalso
      apply hx1'
      have := congrArg (fun z => s₁⁻¹ * z * s₁) h
      simpa [mul_assoc] using this
    · exfalso
      have hψ : ψ ⟨s₁, hs₁X⟩ * ψ ⟨x, hxX⟩ * (ψ ⟨s₁, hs₁X⟩)⁻¹ = ψ ⟨x, hxX⟩ := by
        have e : (⟨s₁ * x * s₁⁻¹, mul_mem (mul_mem hs₁X hxX) (inv_mem hs₁X)⟩ :
            ↥(L32NSet14.nX T V)) = ⟨s₁, hs₁X⟩ * ⟨x, hxX⟩ * ⟨s₁, hs₁X⟩⁻¹ := rfl
        have e2 : (⟨s₁ * x * s₁⁻¹, mul_mem (mul_mem hs₁X hxX) (inv_mem hs₁X)⟩ :
            ↥(L32NSet14.nX T V)) = ⟨x, hxX⟩ := Subtype.ext h
        rw [← map_inv, ← map_mul, ← map_mul, ← e, e2]
      have hψs : ψ ⟨s₁, hs₁X⟩ = ψ ⟨g, hgX⟩ * ψ ⟨t, htX⟩ := by
        rw [← map_mul]
        exact congrArg ψ (Subtype.ext hs₁)
      rw [hψs] at hψ
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (psi_mem_zpowers S14 hxX hx1 hψx3 hgl hgX)
      have hcomm : ψ ⟨g, hgX⟩ * ψ ⟨x, hxX⟩ = ψ ⟨x, hxX⟩ * ψ ⟨g, hgX⟩ := by
        rw [← hj]
        exact (Commute.zpow_left (Commute.refl _) j)
      exact sl2_ne_br hx1 hψx3 ht1 hψt2 hcomm hψ
    · rw [h]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [mul_assoc, ← pow_three, hx3]
  have hinv' : s₁ * x⁻¹ * s₁⁻¹ = x := by
    have := congrArg (·⁻¹) hinv
    simpa [mul_assoc] using this
  have hgL : (g : G) ∈ L := (oTwoUpper_le _ hgl).1
  have hs₁L : s₁ ∈ L := by
    rw [hs₁]
    exact mul_mem hgL htL
  have hs₁LT : s₁ ∈ l1 T L V ⊔ T := by
    rw [hs₁]
    exact mul_mem (Subgroup.mem_sup_left hgl) (Subgroup.mem_sup_right htT)
  obtain ⟨b, hb⟩ := (S.hyp.fsu.sylow.1 : IsPGroup 2 ↥T).exists_card_eq
  have hLT : Nat.card ↥(l1 T L V ⊔ T) = 3 * 2 ^ b := by
    have h := Subgroup.relIndex_mul_card T (l1 T L V ⊔ T)
    rw [relIndex_T_l1T h1222 h1332 h1334 S, inf_eq_left.mpr le_sup_right, hb] at h
    exact h.symm
  refine ⟨s₁ ^ 3, pow_mem hs₁L 3, pow_mem hs₁LT 3, ⟨b, ?_⟩, ?_⟩
  · have h := pow_card_eq_one' (G := ↥(l1 T L V ⊔ T)) (x := ⟨s₁, hs₁LT⟩)
    rw [hLT] at h
    have h' := congrArg Subtype.val h
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h'
    rw [← pow_mul]
    exact h'
  · calc s₁ ^ 3 * x * (s₁ ^ 3)⁻¹ = s₁ * (s₁ * (s₁ * x * s₁⁻¹) * s₁⁻¹) * s₁⁻¹ := by
          rw [pow_three]
          simp only [mul_inv_rev, mul_assoc]
      _ = x⁻¹ := by rw [hinv, hinv', hinv]

end Inv

end CFSG.Quasithin.H13.L32A.C
