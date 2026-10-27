module

public import CFSG.RankThree.PartTwo.KFacts.KS14HJNative
public import CFSG.RankThree.PartTwo.KFacts.KS14HJSignalizer

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem le_centralizer_of_forall_commutator {V : Subgroup X} {z : X} (hV : IsPGroup 2 V)
    (hz3 : z ^ 3 = 1) (hzV : z ∈ Subgroup.normalizer (V : Set X))
    (h : ∀ v ∈ V, v * z * v⁻¹ * z⁻¹ ∈ Subgroup.centralizer ({z} : Set X)) :
    V ≤ Subgroup.centralizer ({z} : Set X) := by
  intro v hv
  set r := v * z * v⁻¹ * z⁻¹ with hr
  have hrV : r ∈ V := by
    have h1 : z * v⁻¹ * z⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hzV _).mp (V.inv_mem hv)
    have h2 := V.mul_mem hv h1
    rwa [show v * (z * v⁻¹ * z⁻¹) = r by rw [hr]; group] at h2
  have hrz : r * z = z * r := Subgroup.mem_centralizer_singleton_iff.mp (h v hv)
  have hr3 : r ^ 3 = 1 := by
    have h1 : (v * z * v⁻¹) ^ 3 = 1 := by rw [conj_pow, hz3, mul_one, mul_inv_cancel]
    rw [show v * z * v⁻¹ = r * z by rw [hr]; group, (Commute.mul_pow hrz 3), hz3,
      mul_one] at h1
    exact h1
  obtain ⟨k, hk⟩ := hV ⟨r, hrV⟩
  have hk' : r ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have h1 := pow_gcd_eq_one.mpr ⟨hk', hr3⟩
  rw [hcop, pow_one] at h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  have : v * z * v⁻¹ * z⁻¹ = 1 := h1
  calc v * z = (v * z * v⁻¹ * z⁻¹) * z * v := by group
    _ = z * v := by rw [this, one_mul]

theorem j2_exists_twoGroup_not_le_centralizer
    (hX : Nonempty (X ≃* NativeSporadic.J2)) {E : Subgroup X} (hE9 : Nat.card E = 9) {z : X}
    (hzE : z ∈ E) (hz1 : z ≠ 1) (hz27 : 27 ∣ Nat.card (Subgroup.centralizer ({z} : Set X))) :
    ∃ V : Subgroup X, IsPGroup 2 V ∧ E ≤ Subgroup.normalizer (V : Set X) ∧
      ¬ V ≤ Subgroup.centralizer ({z} : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h415 := CFSG.RankThree.PartTwo.Sec4.Sporadic.rank3II_4_15
  obtain ⟨P, hEP, -, -⟩ := KFacts.KS14.Native.j2_exists_sylow_of_card_nine hX hE9
  obtain ⟨⟨hHeis, -⟩, -, ⟨-, hext, -⟩, h4, h5⟩ := h415 X hX P _ rfl _ rfl
  obtain ⟨-, -, hexp⟩ := hHeis
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZ
  have hpow3 : ∀ y ∈ (P : Subgroup X), y ^ 3 = 1 := by
    intro y hy
    have h := Monoid.pow_exponent_eq_one (⟨y, hy⟩ : ↥(P : Subgroup X))
    rw [hexp] at h
    exact congrArg Subtype.val h
  have hEcomm : ∀ c ∈ E, ∀ d ∈ E, c * d = d * c := by
    intro c hc d hd
    have h := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := E)
      (by rw [hE9]; norm_num)).is_comm.comm ⟨c, hc⟩ ⟨d, hd⟩
    exact congrArg Subtype.val h
  have hCN : ∀ c : X, Subgroup.centralizer ({c} : Set X) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set X) := fun c => by
    rw [← KFacts.KS14.centralizer_zpowers_eq]
    exact Subgroup.centralizer_le_normalizer _
  have hzZ : z ∈ Z := by
    by_contra hzZ
    obtain ⟨-, ⟨e⟩, -⟩ := h4 E ⟨hEP, hE9⟩ z hzE hzZ
    have h72 : Nat.card (Subgroup.normalizer (Subgroup.zpowers z : Set X)) = 72 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, KFacts.KS14.card_alternatingGroup_four,
        Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have hdvd := hz27.trans (Subgroup.card_dvd_of_le (hCN z))
    rw [h72] at hdvd
    norm_num at hdvd
  have hZz : ∀ w ∈ Z, w = 1 ∨ w = z ∨ w = z * z :=
    fun w hw => KFacts.KS14.j2_mem_inf_centralizer_eq h415 hX P hzZ hz1 hw
  obtain ⟨S, hS, -, -, ⟨T, ⟨eT⟩⟩, a, b, hab, hprod⟩ := h5 E ⟨hEP, hE9⟩
  set W := S ⊓ Subgroup.centralizer (Z : Set X) with hW
  set Va := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a} : Set X)) with hVa
  set Vb := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({b} : Set X)) with hVb
  have haE : a ∈ E := hab ▸ Subgroup.subset_closure (Set.mem_insert a {b})
  have hbE : b ∈ E := hab ▸ Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp hS.prop.2.1
  have hVaS : Va ≤ S := by
    intro v hv
    have h := Set.mul_mem_mul (Set.mul_mem_mul (SetLike.mem_coe.mpr (one_mem W))
      (SetLike.mem_coe.mpr hv)) (SetLike.mem_coe.mpr (one_mem Vb))
    rw [hprod, one_mul, mul_one] at h
    exact h
  have h64 : 64 ≤ Nat.card S := KFacts.KS14.le_card_of_mulEquiv_sylow_two_projSL T eT
  have hW8 : Nat.card W ≤ 8 := by
    have hW2 : IsPGroup 2 W := hS2.to_le inf_le_left
    have hC : Nat.card (Subgroup.centralizer (Z : Set X)) = 1080 :=
      KFacts.KS14.card_eq_of_isExtOf_alternating_six hext
    obtain ⟨k, hk⟩ := hW2.exists_card_eq
    have hdvd : 2 ^ k ∣ 1080 := hk ▸ hC ▸ Subgroup.card_dvd_of_le inf_le_right
    have hk3 : k ≤ 3 := by
      by_contra h
      have : 2 ^ 4 ∣ 1080 := (pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at this
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
      _ = 8 := by norm_num
  have hb1 : b ≠ 1 := by
    intro h
    have hcl : E = Subgroup.zpowers a := by
      rw [← hab, h, Subgroup.zpowers_eq_closure]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro y (rfl | rfl)
        · exact Subgroup.subset_closure rfl
        · exact one_mem _
      · exact Subgroup.closure_mono (Set.singleton_subset_iff.mpr (Set.mem_insert a _))
    have hcard : Nat.card E ∣ 3 := by
      rw [hcl, Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one (hpow3 a (hEP haE))
    rw [hE9] at hcard
    norm_num at hcard
  have hVb4 : Nat.card Vb ≤ 4 := by
    by_cases hbZ : b ∈ Z
    · have hbot := KFacts.KS14.j2_pCore_two_centralizer_eq_bot h415 hX hb1
        ⟨P, hbZ.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
          (KFacts.KS14.commute_of_mem_inf_centralizer hbZ hy)⟩
      rw [hVb, inSubgroup, hbot, Subgroup.map_bot, Subgroup.card_bot]
      norm_num
    · exact KFacts.KS14.j2_card_pCore_two_centralizer_le_four h415 hX P hEP hE9 hbE hbZ
  have hVaZ : ¬ Va ≤ Subgroup.centralizer (Z : Set X) := by
    intro hle
    have hVaW : Va ≤ W := le_inf hVaS hle
    have hWVa : (W : Set X) * (Va : Set X) = (W : Set X) := by
      ext x
      constructor
      · rintro ⟨w, hw, v, hv, rfl⟩
        exact W.mul_mem hw (hVaW hv)
      · intro hx
        exact ⟨x, hx, 1, one_mem Va, mul_one x⟩
    rw [hWVa] at hprod
    have h1 := Set.natCard_mul_le (s := (W : Set X)) (t := (Vb : Set X))
    rw [hprod] at h1
    have h1' : Nat.card S ≤ Nat.card W * Nat.card Vb := h1
    have h2 : Nat.card W * Nat.card Vb ≤ 8 * 4 := Nat.mul_le_mul hW8 hVb4
    omega
  have hVa2 : IsPGroup 2 Va := (CFSG.pCore_isPGroup (p := 2)
    (G := ↥(Subgroup.centralizer ({a} : Set X)))).map (Subgroup.centralizer ({a} : Set X)).subtype
  have hEVa : E ≤ Subgroup.normalizer (Va : Set X) := by
    refine le_trans (fun c hc => ?_)
      ((hCN a).trans (KFacts.KS14.normalizer_zpowers_le_normalizer_pCore a))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hEcomm c hc a haE
  refine ⟨Va, hVa2, hEVa, fun hle => hVaZ fun v hv => ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hvz : z * v = v * z := (Subgroup.mem_centralizer_singleton_iff.mp (hle hv)).symm
  rcases hZz w hw with rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact hvz
  · rw [mul_assoc, hvz, ← mul_assoc, hvz, mul_assoc]

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
