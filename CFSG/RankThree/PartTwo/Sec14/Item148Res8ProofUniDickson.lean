module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofSLTwoMain
import CFSG.Dihedral.Glauberman.DicksonMaxUp

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res8

open Matrix

variable {K : Type} [Field K]

@[expose] def uRootAdd (S : AddSubgroup K) : Subgroup (SpecialLinearGroup (Fin 2) K) where
  carrier := {g | ∃ x ∈ S, g = uSL x}
  one_mem' := ⟨0, S.zero_mem, (SpecialLinearGroup.transvection_coeff_zero _).symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, S.add_mem ha hb, uSL_mul a b⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, S.neg_mem ha, SpecialLinearGroup.transvection_inv _ _⟩

theorem card_uRootAdd (S : AddSubgroup K) : Nat.card (uRootAdd S) = Nat.card S := by
  refine (Nat.card_congr (Equiv.ofBijective (fun a : S => (⟨uSL (a : K), a, a.2, rfl⟩ :
    uRootAdd S)) ⟨?_, ?_⟩)).symm
  · intro a b hab
    have h0 : uSL (a : K) = uSL (b : K) := congrArg Subtype.val hab
    exact Subtype.ext (uSL_injective h0)
  · rintro ⟨g, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem exists_odd_card_eq_add [Finite K] [CharP K 2] (S : AddSubgroup K) (hS1 : (1 : K) ∈ S)
    {m : ℕ} (hSm : Nat.card S = 2 ^ m) (G : Subgroup (SpecialLinearGroup (Fin 2) K))
    (hu : uRootAdd S ≤ G) (hU : ∀ x, uSL x ∈ G → x ∈ S) :
    ∃ r, Odd r ∧ Nat.card G = 2 ^ m * r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R' := (uRootAdd S).subgroupOf G with hR'
  have hR'card : Nat.card R' = 2 ^ m := by
    rw [hR', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hu).toEquiv, card_uRootAdd, hSm]
  obtain ⟨P, hP⟩ := (IsPGroup.of_card hR'card).exists_le_sylow
  have h1mem : uSL (1 : K) ∈ uRootAdd S := ⟨1, hS1, rfl⟩
  have h11 : uSL (1 : K) ≠ 1 := by
    intro h1
    apply one_ne_zero (α := K)
    apply uSL_injective
    rw [h1]
    exact (SpecialLinearGroup.transvection_coeff_zero _).symm
  set Q := (P : Subgroup G).map G.subtype with hQ
  have hQ2 : IsPGroup 2 Q := P.isPGroup'.map _
  have h1Q : uSL (1 : K) ∈ Q :=
    ⟨⟨uSL 1, hu h1mem⟩, hP (Subgroup.mem_subgroupOf.mpr h1mem), rfl⟩
  have hQG : Q ≤ G := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hQle : Q ≤ uRootAdd S := by
    have : Nontrivial Q := ⟨⟨⟨uSL 1, h1Q⟩, 1, fun h => h11 (congrArg Subtype.val h)⟩⟩
    have := hQ2.center_nontrivial
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center Q)
    have hzc := Subgroup.mem_center_iff.mp z.2 ⟨uSL 1, h1Q⟩
    have hzc' : ((z : Q) : SpecialLinearGroup (Fin 2) K) * uSL 1 =
        uSL 1 * ((z : Q) : SpecialLinearGroup (Fin 2) K) := (congrArg Subtype.val hzc).symm
    obtain ⟨b, hb⟩ := exists_eq_uSL_of_commute one_ne_zero hzc'
    have hb0 : b ≠ 0 := by
      rintro rfl
      apply hz
      apply Subtype.ext
      apply Subtype.ext
      rw [hb]
      exact SpecialLinearGroup.transvection_coeff_zero _
    intro x hx
    have hxc := Subgroup.mem_center_iff.mp z.2 ⟨x, hx⟩
    have hxc' : x * uSL b = uSL b * x := by
      have := congrArg Subtype.val hxc
      rw [← hb]
      exact this
    obtain ⟨b', rfl⟩ := exists_eq_uSL_of_commute hb0 hxc'
    exact ⟨b', hU b' (hQG hx), rfl⟩
  have hPR : (P : Subgroup G) = R' := by
    refine le_antisymm (fun g hg => ?_) hP
    rw [hR', Subgroup.mem_subgroupOf]
    exact hQle ⟨g, hg, rfl⟩
  refine ⟨(P : Subgroup G).index, ?_, ?_⟩
  · exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (P.not_dvd_index))
  · rw [← Subgroup.card_mul_index (P : Subgroup G), hPR, hR'card]

theorem mem_of_sq_eq_one_of_odd_index {H : Type*} [Group H] [Finite H] {E : Subgroup H}
    [E.Normal] (hE : Odd E.index) {x : H} (hx : x ^ 2 = 1) : x ∈ E := by
  have h1 : orderOf (x : H ⧸ E) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow,
    hx, QuotientGroup.mk_one])
  have h2 : orderOf (x : H ⧸ E) ∣ E.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (x : H ⧸ E) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at h2
      exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hE)
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem sylow_exp_dvd_of_dickson [Finite K] [CharP K 2] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (G : Subgroup (SpecialLinearGroup (Fin 2) K))
    {m r : ℕ} (hm : 3 ≤ m) (hr : Odd r) (hcard : Nat.card G = 2 ^ m * r)
    {x y : SpecialLinearGroup (Fin 2) K} (hxG : x ∈ G) (hyG : y ∈ G) (hx2 : x ^ 2 = 1)
    (hy2 : y ^ 2 = 1) (hxy : x * y ≠ y * x) : m ∣ f ∨ 2 * m ∣ f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) K)) with hφdef
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, hφdef, QuotientGroup.ker_mk', center_slTwo_eq_bot]
  set H := G.map φ with hH
  have hHG : Nat.card H = Nat.card G := Subgroup.card_map_of_injective hφ
  set x' : H := ⟨φ x, Subgroup.mem_map_of_mem φ hxG⟩ with hx'
  set y' : H := ⟨φ y, Subgroup.mem_map_of_mem φ hyG⟩ with hy'
  have hx'y' : x' * y' ≠ y' * x' := by
    intro h
    apply hxy
    apply hφ
    simpa using congrArg Subtype.val h
  have hx'2 : x' ^ 2 = 1 := by
    apply Subtype.ext
    simp [hx', ← map_pow, hx2]
  have hy'2 : y' ^ 2 = 1 := by
    apply Subtype.ext
    simp [hy', ← map_pow, hy2]
  have hHnc : ¬ IsMulCommutative H := fun hc => hx'y' (hc.is_comm.comm x' y')
  have hcardH : Nat.card H = 2 ^ m * r := hHG.trans hcard
  have hodd1 : Odd (2 ^ f - 1) := odd_two_pow_sub_one hf
  have hg : Nat.gcd (2 ^ f - 1) 2 = 1 := Nat.Coprime.gcd_eq_one
    (Nat.coprime_two_right.mpr hodd1)
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hK H with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hzc, -⟩ | ⟨-, ⟨e4⟩⟩ | ⟨h16, -⟩ | ⟨-, ⟨e5⟩⟩ |
      ⟨k, t, htk, -, N, C, hNn, hNel, hNc, hCcyc, hCc, hdisj, hsup⟩ | ⟨k, hk, hkf, ⟨e⟩⟩ |
      ⟨k, hk, hkf, ⟨e⟩⟩
  · exact absurd hEl.toIsMulCommutative hHnc
  · exact absurd ⟨⟨fun a b => (IsCyclic.commGroup (α := H)).mul_comm a b⟩⟩ hHnc
  ·
    exfalso
    rw [hK, hg, Nat.div_one, Nat.div_one] at hz
    have hzodd : Odd z := by
      rcases hz with hz | hz
      · exact Odd.of_dvd_nat hodd1 hz
      · exact Odd.of_dvd_nat (odd_two_pow_add_one hf) hz
    have := two_pow_mul_odd_inj hr hzodd (hcardH.symm.trans (by rw [hzc, pow_one]))
    omega
  ·
    exfalso
    have h12 : Nat.card H = 12 := by
      rw [Nat.card_congr e4.toEquiv, nat_card_alternatingGroup]
      simp
      decide
    have := two_pow_mul_odd_inj hr (by decide : Odd 3)
      (hcardH.symm.trans (by rw [h12]; norm_num : Nat.card H = 2 ^ 2 * 3))
    omega
  ·
    exfalso
    have hodd : Odd (2 ^ (2 * f) - 1) := odd_two_pow_sub_one (by omega)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 16).trans h16))
  ·
    exfalso
    have h60 : Nat.card H = 60 := by
      rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup]
      simp
      decide
    have := two_pow_mul_odd_inj hr (by decide : Odd 15)
      (hcardH.symm.trans (by rw [h60]; norm_num : Nat.card H = 2 ^ 2 * 15))
    omega
  ·
    exfalso
    have hNC : Nat.card H = 2 ^ k * t := by
      rw [← hNc, ← hCc, ← card_sup_eq_mul_of_disjoint N C hdisj, hsup, Subgroup.card_top]
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    ·
      have hN1 : N = ⊥ := by
        rw [← Subgroup.card_eq_one, hNc, pow_zero]
      rw [hN1, bot_sup_eq] at hsup
      rw [hsup] at hCcyc
      have : IsCyclic H := isCyclic_of_surjective
        (Subgroup.topEquiv : (⊤ : Subgroup H) ≃* H).toMonoidHom (MulEquiv.surjective _)
      exact hHnc ⟨⟨fun a b => (IsCyclic.commGroup (α := H)).mul_comm a b⟩⟩
    · have htodd : Odd t := Odd.of_dvd_nat (odd_two_pow_sub_one hkpos) htk
      have hidx : N.index = t := by
        have h1 := Subgroup.card_mul_index N
        rw [hNc, hNC] at h1
        exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
      have hxN : x' ∈ N := mem_of_sq_eq_one_of_odd_index (hidx ▸ htodd) hx'2
      have hyN : y' ∈ N := mem_of_sq_eq_one_of_odd_index (hidx ▸ htodd) hy'2
      apply hx'y'
      have := hNel.toIsMulCommutative.is_comm.comm ⟨x', hxN⟩ ⟨y', hyN⟩
      simpa using congrArg Subtype.val this
  ·
    left
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hcard' : Nat.card H = 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, card_psl2_charTwo, GaloisField.card 2 k hk]
    have hodd : Odd ((2 ^ k) ^ 2 - 1) := by
      rw [← pow_mul]
      exact odd_two_pow_sub_one (by omega)
    obtain ⟨rfl, -⟩ := two_pow_mul_odd_inj hr hodd (hcardH.symm.trans hcard')
    exact hkf
  ·
    right
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have hcard' : Nat.card H = 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
      rw [Nat.card_congr e.toEquiv, CFSG.Glauberman.Dickson.MaxUp.card_pgl2_galoisField hk,
        ← pow_mul, mul_comm k 2]
    have hodd : Odd ((2 ^ k) ^ 2 - 1) := by
      rw [← pow_mul]
      exact odd_two_pow_sub_one (by omega)
    obtain ⟨rfl, -⟩ := two_pow_mul_odd_inj hr hodd (hcardH.symm.trans hcard')
    exact hkf

end CFSG.RankThree.PartTwo.Sec14.Item148Res8
