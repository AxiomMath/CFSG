module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeEndCount
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeHat
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords

public section

namespace CFSG.StandardType.E6NonToralThree

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.Three TableBExc.E6Three

open E6ThreeEnd

private theorem cubic_aux (v : Fin 3 → ZMod 3)
    (hv : ∀ i, v i ≠ 0) (j : Fin Tag.E6.rank) :
    (Pi.single j 1 : Fin Tag.E6.rank → ℤ) +
      ((coxeterSystem .E6).wordProd (nfWordE6 (v 0).val (v 1).val (v 2).val)) •
        (Pi.single j 1 : Fin Tag.E6.rank → ℤ) +
      ((coxeterSystem .E6).wordProd (nfWordE6 (v 0).val (v 1).val (v 2).val)) •
        (((coxeterSystem .E6).wordProd (nfWordE6 (v 0).val (v 1).val (v 2).val)) •
          (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) = (0 : Fin Tag.E6.rank → ℤ) := by
  rw [CFSG.StandardType.TableBExc.wordProd_smul]
  revert v hv j
  decide +kernel

private theorem inv_cubic_aux (v : Multiplicative (Fin 3 → ZMod 3))
    (hv : ∀ i, v.toAdd i ≠ 0) (j : Fin Tag.E6.rank) :
    (Pi.single j 1 : Fin Tag.E6.rank → ℤ) +
      (modelHomE6 (SemidirectProduct.inl v))⁻¹ • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) +
      (modelHomE6 (SemidirectProduct.inl v))⁻¹ •
        ((modelHomE6 (SemidirectProduct.inl v))⁻¹ •
          (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) = (0 : Fin Tag.E6.rank → ℤ) := by
  have hbinv : (modelHomE6 (SemidirectProduct.inl v))⁻¹ =
      modelHomE6 (SemidirectProduct.inl v⁻¹) := by
    rw [← map_inv, ← map_inv]
    rfl
  rw [hbinv, modelHomE6_inl]
  refine cubic_aux (v⁻¹).toAdd (fun i => ?_) j
  rw [toAdd_inv, Pi.neg_apply]
  exact neg_ne_zero.mpr (hv i)

private theorem tuple_pow_three_eq_one {L : Type} [Field L]
    (a : Fin Tag.E6.rank → Lˣ) {v : Multiplicative (Fin 3 → ZMod 3)}
    (hv : ∀ i, v.toAdd i ≠ 0)
    (hwt : weylTuple (modelHomE6 (SemidirectProduct.inl v)) a = a) :
    a ^ 3 = 1 := by
  have hfix : ∀ u : Fin Tag.E6.rank → ℤ,
      rootChar a ((modelHomE6 (SemidirectProduct.inl v))⁻¹ • u) = rootChar a u := by
    intro u
    rw [← rootChar_weylTuple, hwt]
  funext i
  have hsingle : rootChar a (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = a i := by
    have h := rootChar_nsmul_single a i 1
    rwa [one_nsmul, pow_one] at h
  have h2 : rootChar a ((modelHomE6 (SemidirectProduct.inl v))⁻¹ •
      (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = a i := by
    rw [hfix, hsingle]
  have h3 : rootChar a ((modelHomE6 (SemidirectProduct.inl v))⁻¹ •
      ((modelHomE6 (SemidirectProduct.inl v))⁻¹ •
        (Pi.single i 1 : Fin Tag.E6.rank → ℤ))) = a i := by
    rw [hfix, h2]
  have hsum : rootChar a ((Pi.single i 1 : Fin Tag.E6.rank → ℤ) +
      (modelHomE6 (SemidirectProduct.inl v))⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) +
      (modelHomE6 (SemidirectProduct.inl v))⁻¹ •
        ((modelHomE6 (SemidirectProduct.inl v))⁻¹ •
          (Pi.single i 1 : Fin Tag.E6.rank → ℤ))) = 1 := by
    rw [inv_cubic_aux v hv i, rootChar_zero]
  rw [rootChar_add, rootChar_add, hsingle, h2, h3] at hsum
  show (a i) ^ 3 = 1
  simpa [pow_three, mul_assoc] using hsum

theorem pow_three_eq_one_of_commute
    {L : Type} [Field L] {n : ModGL .E6 L}
    (hn : n ∈ monomialSubgroup .E6 L) {v : Multiplicative (Fin 3 → ZMod 3)}
    (hv : ∀ i, v.toAdd i ≠ 0)
    (hnv : weylQuotientHom .E6 L ⟨n, hn⟩ = modelHomE6 (SemidirectProduct.inl v))
    {t : ModGL .E6 L} (ht : t ∈ torusGroup .E6 L) (htn : t * n = n * t) : t ^ 3 = 1 := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hpsi : psiHat .E6 L ⟨n, monomial_le_monoHat hn⟩ =
      modelHomE6 (SemidirectProduct.inl v) := by
    rw [psiHat_of_mem_monomial hn, hnv]
  have hconj : n * rootDiagUnit .E6 a * n⁻¹ =
      rootDiagUnit .E6 (weylTuple (modelHomE6 (SemidirectProduct.inl v)) a) := by
    have h := conj_rootDiagUnit_of_mem_monoHat (x := ⟨n, monomial_le_monoHat hn⟩) a
    rw [hpsi] at h
    exact h
  have h1 : n * rootDiagUnit .E6 a * n⁻¹ = rootDiagUnit .E6 a := by
    rw [← htn]
    group
  have hwt : weylTuple (modelHomE6 (SemidirectProduct.inl v)) a = a := by
    apply rootDiagUnit_injective
    rw [← hconj, h1]
  rw [rootDiagUnit_pow, tuple_pow_three_eq_one a hv hwt, rootDiagUnit_one]

private theorem eq_smul_const_of_shiftAut {w : Fin 3 → ZMod 3}
    (h : shiftAut piE7 (.ofAdd w) = .ofAdd w) :
    ∃ a : ZMod 3, w = a • (![1, 1, 1] : Fin 3 → ZMod 3) := by
  revert w
  decide +kernel

private theorem exists_nonzero_coord_sum_zero {c : Fin 3 → ZMod 3}
    (hc : ∀ i, c i ≠ 0) :
    ∃ v : Fin 3 → ZMod 3, (∀ i, v i ≠ 0) ∧ ∑ i, c i * v i = 0 := by
  revert c hc
  decide +kernel

private theorem two_smul_const_add_self :
    (2 : ZMod 3) • (![1, 1, 1] : Fin 3 → ZMod 3) + (2 : ZMod 3) • ![1, 1, 1] =
      (![1, 1, 1] : Fin 3 → ZMod 3) := by
  funext i
  fin_cases i <;> decide

private theorem zmod_ne_zero_eq_one_or_two (a : ZMod 3) (ha : a ≠ 0) :
    a = 1 ∨ a = 2 := by
  revert a
  decide +kernel

private theorem exists_ne_one_right_eq_one (A' : Subgroup (Model piE7 piE7_pow_three))
    (hA'3 : ∀ y ∈ A', y ^ 3 = 1) (h9 : 9 ≤ Nat.card A')
    {y1 : Model piE7 piE7_pow_three} (hy1 : y1 ∈ A')
    (hy1r : y1.right = .ofAdd 1) :
    ∃ b ∈ A', b ≠ 1 ∧ b.right = 1 := by
  haveI := finite_model (π := piE7) (hπ := piE7_pow_three)
  have hy1ne : y1 ≠ 1 := by
    have hright1 : y1.right ≠ 1 := by
      rw [hy1r]
      decide
    exact fun h1 => hright1 (by rw [h1, SemidirectProduct.one_right])
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have horder : orderOf y1 = 3 := orderOf_eq_prime (hA'3 y1 hy1) hy1ne
  have hnotle : ¬ A' ≤ Subgroup.zpowers y1 := by
    intro hle
    have hcle := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, horder] at hcle
    omega
  obtain ⟨z, hzA', hznot⟩ := Set.not_subset.mp hnotle
  obtain ⟨m, hm⟩ := Multiplicative.ofAdd.surjective z.right
  refine ⟨z * (y1 ^ m.val)⁻¹, mul_mem hzA' (inv_mem (Subgroup.pow_mem A' hy1 m.val)),
    ?_, ?_⟩
  · intro h1
    apply hznot
    have hz : z = y1 ^ m.val := mul_inv_eq_one.mp h1
    rw [hz]
    exact Subgroup.pow_mem (Subgroup.zpowers y1) (Subgroup.mem_zpowers y1) m.val
  · have hy1right' : SemidirectProduct.rightHom y1 = Multiplicative.ofAdd 1 := hy1r
    have hy1pow : (y1 ^ m.val).right = Multiplicative.ofAdd m := by
      change SemidirectProduct.rightHom (y1 ^ m.val) = Multiplicative.ofAdd m
      rw [map_pow, hy1right', ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    rw [SemidirectProduct.mul_right, SemidirectProduct.inv_right, ← hm, hy1pow,
      mul_inv_cancel]

private theorem exists_smul_const_of_mem (A' : Subgroup (Model piE7 piE7_pow_three))
    (hA'c : ∀ y ∈ A', ∀ z ∈ A', y * z = z * y)
    {b y1 : Model piE7 piE7_pow_three} (hb : b ∈ A') (hy1 : y1 ∈ A')
    (hb1 : b.right = 1) (hy1r : y1.right = .ofAdd 1) :
    ∃ a : ZMod 3, b.left.toAdd = a • (![1, 1, 1] : Fin 3 → ZMod 3) := by
  have hcomm : b * y1 = y1 * b := hA'c b hb y1 hy1
  have hshift : shiftAut piE7 b.left = b.left := by
    apply shiftAut_eq_of_comm (v := y1.left) (w := b.left)
    have e1 : b = (⟨b.left, 1⟩ : Model piE7 piE7_pow_three) :=
      SemidirectProduct.ext rfl hb1
    have e2 : y1 = (⟨y1.left, .ofAdd 1⟩ : Model piE7 piE7_pow_three) :=
      SemidirectProduct.ext rfl hy1r
    rw [← e1, ← e2]
    exact hcomm
  have hshift' : shiftAut piE7 (.ofAdd b.left.toAdd) = .ofAdd b.left.toAdd := by
    rw [ofAdd_toAdd]
    exact hshift
  exact eq_smul_const_of_shiftAut hshift'

private theorem diag_mem_of_smul_const (A' : Subgroup (Model piE7 piE7_pow_three))
    {b : Model piE7 piE7_pow_three} (hb : b ∈ A') (hb1 : b.right = 1)
    {a : ZMod 3} (ha : b.left.toAdd = a • (![1, 1, 1] : Fin 3 → ZMod 3)) (ha0 : a ≠ 0) :
    SemidirectProduct.inl (.ofAdd (![1, 1, 1] : Fin 3 → ZMod 3)) ∈ A' := by
  have hb_inl : b = SemidirectProduct.inl b.left := eq_inl_of_right_eq_one hb1
  have hb_eq : b = SemidirectProduct.inl
      (.ofAdd (a • (![1, 1, 1] : Fin 3 → ZMod 3))) := by
    have hleft : b.left = Multiplicative.ofAdd (a • (![1, 1, 1] : Fin 3 → ZMod 3)) := by
      rw [show b.left = Multiplicative.ofAdd b.left.toAdd from (ofAdd_toAdd _).symm]
      rw [ha]
    rw [hb_inl, hleft]
  rcases zmod_ne_zero_eq_one_or_two a ha0 with rfl | h2
  · rw [hb_eq, one_smul] at hb
    exact hb
  · rw [hb_eq, h2] at hb
    have hsq : (SemidirectProduct.inl
        (.ofAdd ((2 : ZMod 3) • (![1, 1, 1] : Fin 3 → ZMod 3))) :
        Model piE7 piE7_pow_three) ^ 2 =
        SemidirectProduct.inl (.ofAdd (![1, 1, 1] : Fin 3 → ZMod 3)) := by
      rw [pow_two, ← map_mul]
      congr 1
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd, two_smul_const_add_self]
    rw [← hsq]
    exact Subgroup.pow_mem A' hb 2

private theorem diag_mem_of_outside (A' : Subgroup (Model piE7 piE7_pow_three))
    (hA'3 : ∀ y ∈ A', y ^ 3 = 1) (hA'c : ∀ y ∈ A', ∀ z ∈ A', y * z = z * y)
    (h9 : 9 ≤ Nat.card A') (hOut : ∃ y ∈ A', y.right ≠ 1) :
    SemidirectProduct.inl (.ofAdd (![1, 1, 1] : Fin 3 → ZMod 3)) ∈ A' := by
  obtain ⟨y, hy, hyr⟩ := hOut
  obtain ⟨y1, hy1, hy1r⟩ := exists_right_eq_ofAdd_one hy hyr
  obtain ⟨b, hb, hbne, hb1⟩ := exists_ne_one_right_eq_one A' hA'3 h9 hy1 hy1r
  obtain ⟨a, ha⟩ := exists_smul_const_of_mem A' hA'c hb hy1 hb1 hy1r
  have ha0 : a ≠ 0 := by
    intro h0
    apply hbne
    have hleft : b.left = 1 := by
      apply Multiplicative.toAdd.injective
      rw [ha, h0, zero_smul]
      rfl
    rw [eq_inl_of_right_eq_one hb1, hleft]
    rfl
  exact diag_mem_of_smul_const A' hb hb1 ha ha0

private theorem exists_nonzero_coord_inl_of_inside (A' : Subgroup (Model piE7 piE7_pow_three))
    (hN : ∀ y ∈ A', y.right = 1) (h9 : 9 ≤ Nat.card A')
    (hg' : ∀ i, SemidirectProduct.inl (.ofAdd (Pi.single i 1)) ∉ A') :
    ∃ v : Fin 3 → ZMod 3, (∀ i, v i ≠ 0) ∧
      SemidirectProduct.inl (.ofAdd v) ∈ A' := by
  have hXcard : Nat.card (expSub A') = Nat.card A' := card_expSub hN
  have hX : 3 ^ (3 - 1) ≤ Nat.card (expSub A') := by
    rw [hXcard]
    simpa using h9
  obtain ⟨c, hc⟩ := exists_forall_mem_iff_dot (expSub A') hX
  have hcne : ∀ i, c i ≠ 0 := by
    intro i hi
    apply hg' i
    have hsingle : Pi.single i 1 ∈ expSub A' := by
      rw [hc]
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · intro h
        exact absurd (Finset.mem_univ i) h
    exact (mem_expSub).mp hsingle
  obtain ⟨v, hv0, hvsum⟩ := exists_nonzero_coord_sum_zero hcne
  exact ⟨v, hv0, (mem_expSub).mp ((hc v).mpr hvsum)⟩

theorem exists_inl_mem (A : Subgroup (WeylGroup .E6)) (hAS : A ≤ modelHomE6.range)
    (hA : IsElemAbelian 3 A) (hg : ∀ i, gE6 i ∉ A) (h9 : 9 ≤ Nat.card A) :
    ∃ v : Multiplicative (Fin 3 → ZMod 3), (∀ i, v.toAdd i ≠ 0) ∧
      modelHomE6 (SemidirectProduct.inl v) ∈ A := by
  classical
  haveI := finite_model (π := piE7) (hπ := piE7_pow_three)
  set A' : Subgroup (Model piE7 piE7_pow_three) := A.comap modelHomE6 with hA'
  have hmap : A'.map modelHomE6 = A := Subgroup.map_comap_eq_self hAS
  have hcard : Nat.card A' = Nat.card A := by
    conv_rhs => rw [← hmap]
    exact (Subgroup.card_map_of_injective modelHomE6_injective).symm
  have hA'3 : ∀ y ∈ A', y ^ 3 = 1 := by
    intro y hy
    apply modelHomE6_injective
    rw [map_pow, map_one]
    exact hA.2 (modelHomE6 y) hy
  have hA'c : ∀ y ∈ A', ∀ z ∈ A', y * z = z * y := by
    intro y hy z hz
    apply modelHomE6_injective
    rw [map_mul, map_mul]
    exact TableB.IsElemAbelian.comm hA hy hz
  have hg' : ∀ i, SemidirectProduct.inl (.ofAdd (Pi.single i 1)) ∉ A' := by
    intro i hi
    apply hg i
    change modelHomE6 (SemidirectProduct.inl (.ofAdd (Pi.single i 1))) ∈ A at hi
    rwa [E6ThreeEnd.modelHomE6_inl_single] at hi
  have h9' : 9 ≤ Nat.card A' := by rw [hcard]; exact h9
  by_cases hOut : ∃ y ∈ A', y.right ≠ 1
  · have hDelta : SemidirectProduct.inl
        (.ofAdd (![1, 1, 1] : Fin 3 → ZMod 3)) ∈ A' :=
      diag_mem_of_outside A' hA'3 hA'c h9' hOut
    refine ⟨.ofAdd (![1, 1, 1] : Fin 3 → ZMod 3), ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num
    · rw [← hmap]
      exact Subgroup.mem_map_of_mem modelHomE6 hDelta
  · push Not at hOut
    obtain ⟨v, hv0, hvin⟩ := exists_nonzero_coord_inl_of_inside A' hOut h9' hg'
    exact ⟨.ofAdd v, by simpa using hv0, by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem modelHomE6 hvin⟩

end CFSG.StandardType.E6NonToralThree
