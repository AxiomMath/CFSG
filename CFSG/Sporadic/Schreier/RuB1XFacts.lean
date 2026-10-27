module

public import CFSG.Sporadic.Schreier.RuB1XList
import CFSG.Sporadic.Schreier.RuSEnum

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native RuB1

namespace RuB1X

theorem check_parts (h : ruB1XCheck = true) :
    allLt 35 (fun j => allLt 35 fun j' =>
      eqA 4060 (compA 4060 xList[j]! xList[j']!) (idA 4060) ||
        Nat.any 35 fun j'' _ => eqA 4060 (compA 4060 xList[j]! xList[j']!) xList[j'']!) = true ∧
    allLt 35 (fun j => allLt 35 fun j' =>
      eqA 4060 (compA 4060 xList[j]! xList[j']!) (compA 4060 xList[j']! xList[j]!)) = true ∧
    allLt 35 (fun j => eqA 4060 (compA 4060 xList[j]! xList[j]!) (idA 4060)) = true ∧
    allLt 35 (fun j => siftA 4060 ruLevS (ruBaseArr 4060 ruS4060ChainBase) 0 xList[j]!) = true ∧
    allLt 35 (fun j => allLt 2 fun g => Nat.any 35 fun j' _ =>
      eqA 4060 (ruConjA #[ruC0A, ruC1A][g]! xList[j]!) xList[j']!) = true ∧
    allLt 35 (fun j => allLt 35 fun j' =>
      !(xKept j && xKept j' && decide (j < j')) || !eqA 4060 xList[j]! xList[j']!) = true ∧
    allLt 35 (fun j => !eqA 4060 xList[j]! (idA 4060)) = true ∧
    allLt 5 (fun k => eqA 4060 xList[7 * k]! ruZA) = true ∧
    eqA 4060 (powA 4060 ruC0A 20) (idA 4060) = true ∧ (!eqA 4060 g5A (idA 4060)) = true ∧
    allLt 35 (fun j => !eqA 4060 (compA 4060 g5A xList[j]!) (compA 4060 xList[j]! g5A) ||
      eqA 4060 xList[j]! ruZA) = true := by
  simpa only [ruB1XCheck, xCheckWith, Bool.and_eq_true, and_assoc] using h

theorem rep_g5A : Rep 4060 g5A ruG5 := rep_powA rep_ruC0 4

theorem rep_ruConjA_c {g : ℕ} (hg : g < 2) {e : Array ℕ}
    {E : Equiv.Perm (Fin 4060)} (he : Rep 4060 e E) :
    Rep 4060 (ruConjA #[ruC0A, ruC1A][g]! e)
      ([ruC0, ruC1].getD g 1 * E * ([ruC0, ruC1].getD g 1)⁻¹) := by
  have hc := rep_pair_getD rep_ruC0 rep_ruC1 g hg
  have hinv : isInvA 4060 #[ruC0A, ruC1A][g]! (invCand 4060 #[ruC0A, ruC1A][g]!) = true := by
    interval_cases g
    · simpa [ruInv] using ruBasic_check.2.2.2.2.2.2.1
    · simpa [ruInv] using ruBasic_check.2.2.2.2.2.2.2.1
  exact rep_compA (rep_compA hc he) (rep_inv_of_isInvA hc hinv)

abbrev xSet : Set (Equiv.Perm (Fin 4060)) := {x | x = 1 ∨ ∃ j < 35, ruXElt j = x}

theorem xSet_finite : xSet.Finite := by
  have e : xSet = ((insert 1 (Finset.image ruXElt (Finset.range 35)) : Finset _) : Set _) := by
    ext g
    simp [xSet, eq_comm]
  rw [e]
  exact Finset.finite_toSet _

theorem xSet_mul
    (h : ruB1XCheck = true) {a b : Equiv.Perm (Fin 4060)} (ha : a ∈ xSet) (hb : b ∈ xSet) :
    a * b ∈ xSet := by
  obtain ⟨h1, -⟩ := check_parts h
  rcases ha with rfl | ⟨j, hj, rfl⟩
  · rwa [one_mul]
  · rcases hb with rfl | ⟨j', hj', rfl⟩
    · rw [mul_one]
      exact Or.inr ⟨j, hj, rfl⟩
    · have hp := allLt_spec (allLt_spec h1 hj) hj'
      rw [Bool.or_eq_true, nat_any_iff'] at hp
      rcases hp with hp | ⟨j'', hj'', hp⟩
      · exact Or.inl (eq_of_eqA (rep_compA (rep_xList hj) (rep_xList hj')) rep_idA hp)
      · exact Or.inr ⟨j'', hj'', (eq_of_eqA (rep_compA (rep_xList hj) (rep_xList hj'))
          (rep_xList hj'') hp).symm⟩

theorem xSet_mul_self
    (h : ruB1XCheck = true) {a : Equiv.Perm (Fin 4060)} (ha : a ∈ xSet) : a * a = 1 := by
  obtain ⟨-, -, h3, -⟩ := check_parts h
  rcases ha with rfl | ⟨j, hj, rfl⟩
  · exact mul_one 1
  · exact eq_of_eqA (rep_compA (rep_xList hj) (rep_xList hj)) rep_idA (allLt_spec h3 hj)

theorem xSet_conj
    (h : ruB1XCheck = true) {c a : Equiv.Perm (Fin 4060)} (hc : c ∈ ruC) (ha : a ∈ xSet) :
    c * a * c⁻¹ ∈ xSet := by
  obtain ⟨-, -, -, -, h5, -⟩ := check_parts h
  have hgen : ∀ g ∈ ({ruC0, ruC1} : Set (Equiv.Perm (Fin 4060))), ∀ x ∈ xSet,
      g * x * g⁻¹ ∈ xSet := by
    rintro g hg x (rfl | ⟨j, hj, rfl⟩)
    · exact Or.inl (by group)
    · obtain ⟨k, hk, rfl⟩ : ∃ k < 2, [ruC0, ruC1].getD k 1 = g := by
        rcases hg with rfl | rfl
        · exact ⟨0, by norm_num, rfl⟩
        · exact ⟨1, by norm_num, rfl⟩
      obtain ⟨j', hj', he⟩ := nat_any_iff'.1 (allLt_spec (allLt_spec h5 hj) hk)
      exact Or.inr ⟨j', hj', (eq_of_eqA (rep_ruConjA_c hk (rep_xList hj)) (rep_xList hj')
        he).symm⟩
  exact conj_closed xSet_finite hgen c hc a ha

theorem xSet_of_mem_ruESub
    {a : Equiv.Perm (Fin 4060)} (ha : a ∈ ruESub) : a ∈ xSet := by
  rcases mem_ruESub.1 ha with rfl | ⟨i, hi, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨i, by omega, ruXElt_of_lt hi⟩

theorem conj_mem_ruXN
    {c x : Equiv.Perm (Fin 4060)} (hc : c ∈ ruC) (hx : x ∈ ruXN) : c * x * c⁻¹ ∈ ruXN := by
  have hle : ruXN ≤ ruXN.comap (MulAut.conj c).toMonoidHom := by
    rw [ruXN, Subgroup.closure_le]
    rintro _ ⟨c', hc', a, ha, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Subgroup.subset_closure ⟨c * c', ruC.mul_mem hc hc', a, ha, by group⟩
  have hc' := Subgroup.mem_comap.1 (hle hx)
  rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc'

theorem ruZ_mem_ruXN :
    ruZ ∈ ruXN :=
  Subgroup.subset_closure ⟨1, ruC.one_mem, ruZ,
    mem_ruESub.2 (Or.inr ⟨0, by norm_num, ruEElt_zero⟩), by group⟩

theorem ruZ_ne_one_of_E :
    ruZ ≠ 1 := by
  rw [← ruEElt_zero]
  exact ruEElt_ne_one (by norm_num)

theorem ruG5_pow_five (h : ruB1XCheck = true) : ruG5 ^ 5 = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := check_parts h
  rw [ruG5, ← pow_mul]
  exact eq_of_eqA (rep_powA rep_ruC0 20) rep_idA h9

theorem ruG5_ne_one (h : ruB1XCheck = true) : ruG5 ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -⟩ := check_parts h
  intro e
  rw [(eqA_iff rep_g5A rep_idA).2 e] at h10
  simp at h10

theorem ruG5_mul_ruZ : ruG5 * ruZ = ruZ * ruG5 := (Commute.pow_pow_self ruC0 4 10).eq

end RuB1X

open RuB1X

theorem mem_ruXN_of_check
    (h : ruB1XCheck = true) {x : Equiv.Perm (Fin 4060)} :
    x ∈ ruXN ↔ x = 1 ∨ ∃ j < 35, ruXElt j = x := by
  constructor
  · intro hx
    rw [ruXN] at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨c, hc, a, ha, rfl⟩ := hy
      exact xSet_conj h hc (xSet_of_mem_ruESub ha)
    | one => exact Or.inl rfl
    | mul y y' _ _ ihy ihy' => exact xSet_mul h ihy ihy'
    | inv y _ ihy =>
      rw [inv_eq_of_mul_eq_one_right (xSet_mul_self h ihy)]
      exact ihy
  · rintro (rfl | ⟨j, -, rfl⟩)
    · exact ruXN.one_mem
    · exact ruXElt_mem j

theorem ruXN_comm_of_check
    (h : ruB1XCheck = true) : ∀ x ∈ ruXN, ∀ x' ∈ ruXN, x * x' = x' * x := by
  obtain ⟨-, h2, -⟩ := check_parts h
  intro x hx x' hx'
  rcases (mem_ruXN_of_check h).1 hx with rfl | ⟨j, hj, rfl⟩
  · rw [one_mul, mul_one]
  · rcases (mem_ruXN_of_check h).1 hx' with rfl | ⟨j', hj', rfl⟩
    · rw [one_mul, mul_one]
    · exact eq_of_eqA (rep_compA (rep_xList hj) (rep_xList hj'))
        (rep_compA (rep_xList hj') (rep_xList hj)) (allLt_spec (allLt_spec h2 hj) hj')

theorem ruXN_sq_of_check
    (h : ruB1XCheck = true) : ∀ x ∈ ruXN, x * x = 1 := fun _ hx =>
  xSet_mul_self h ((mem_ruXN_of_check h).1 hx)

theorem card_ruXN_of_check
    (h : ruB1XCheck = true) : Nat.card ruXN = 32 := by
  classical
  obtain ⟨-, -, -, -, -, h6, h7, h8, -⟩ := check_parts h
  set K := (Finset.range 35).filter fun j => xKept j = true with hK
  have hK31 : K.card = 31 := by
    rw [hK]
    decide
  have hz : ∀ j < 35, xKept j = false → ruXElt j = ruXElt 0 := by
    intro j hj hk
    have hk' : 7 ≤ j ∧ j % 7 = 0 := by simpa [xKept] using hk
    have h7j : 7 * (j / 7) = j := by omega
    have e := eq_of_eqA (rep_xList (by omega : 7 * (j / 7) < 35)) rep_ruZ
      (allLt_spec h8 (by omega : j / 7 < 5))
    rw [h7j] at e
    rw [e, ruXElt_of_lt (by norm_num : 0 < 7), ruEElt_zero]
  have hset : (ruXN : Set (Equiv.Perm (Fin 4060))) =
      ((insert 1 (K.image ruXElt) : Finset _) : Set _) := by
    ext g
    rw [SetLike.mem_coe, mem_ruXN_of_check h, Finset.coe_insert, Finset.coe_image,
      Set.mem_insert_iff, Set.mem_image]
    constructor
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact Or.inl rfl
      · by_cases hk : xKept j = true
        · exact Or.inr ⟨j, by simp [hK, hj, hk], rfl⟩
        · exact Or.inr ⟨0, by simp [hK, xKept], (hz j hj (by simpa using hk)).symm⟩
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨j, Finset.mem_range.1 (Finset.mem_filter.1 hj).1, rfl⟩
  have hinj : Set.InjOn ruXElt (K : Set ℕ) := by
    have key : ∀ j ∈ K, ∀ j' ∈ K, j < j' → ruXElt j ≠ ruXElt j' := by
      intro j hj j' hj' hlt he
      obtain ⟨hj35, hjk⟩ := Finset.mem_filter.1 hj
      obtain ⟨hj'35, hj'k⟩ := Finset.mem_filter.1 hj'
      rw [Finset.mem_range] at hj35 hj'35
      have hp := allLt_spec (allLt_spec h6 hj35) hj'35
      rw [(eqA_iff (rep_xList hj35) (rep_xList hj'35)).2 he, hjk, hj'k,
        decide_eq_true hlt] at hp
      simp at hp
    intro j hj j' hj' he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact key j hj j' hj' hlt he
    · exact key j' hj' j hj hlt he.symm
  have hnot : (1 : Equiv.Perm (Fin 4060)) ∉ K.image ruXElt := by
    intro hmem
    obtain ⟨j, hj, he⟩ := Finset.mem_image.1 hmem
    have hj35 := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
    have hp := allLt_spec h7 hj35
    rw [(eqA_iff (rep_xList hj35) rep_idA).2 he] at hp
    simp at hp
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj, hK31]

theorem ruXN_le_of_check
    (h : ruB1XCheck = true) : ruXN ≤ ruS := by
  obtain ⟨-, -, -, h4, -⟩ := check_parts h
  intro x hx
  rcases (mem_ruXN_of_check h).1 hx with rfl | ⟨j, hj, rfl⟩
  · exact ruS.one_mem
  · have hs : ruSift 4060 (ruField4060 4) ruS4060ChainBase xList[j]! = true := allLt_spec h4 hj
    rw [← ruChainS4060_sub]
    exact ((ruChain_sift ruInv_check.1 (rep_xList hj)).1 hs :
      ruXElt j ∈ ruChainS4060.originalSubgroup)

theorem ruG5_mem : ruG5 ∈ ruC := ruC.pow_mem ruC0_memC 4

theorem orderOf_ruG5_of_check (h : ruB1XCheck = true) :
    orderOf ruG5 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime (ruG5_pow_five h) (ruG5_ne_one h)

theorem ruG5_cent_of_check
    (h : ruB1XCheck = true) : ∀ x ∈ ruXN, ruG5 * x = x * ruG5 → x = 1 ∨ x = ruZ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11⟩ := check_parts h
  intro x hx hc
  rcases (mem_ruXN_of_check h).1 hx with rfl | ⟨j, hj, rfl⟩
  · exact Or.inl rfl
  · right
    have hp := allLt_spec h11 hj
    rw [(eqA_iff (rep_compA rep_g5A (rep_xList hj)) (rep_compA (rep_xList hj) rep_g5A)).2 hc,
      Bool.not_true, Bool.false_or] at hp
    exact eq_of_eqA (rep_xList hj) rep_ruZ hp

theorem ruG5_gen_of_check
    (h : ruB1XCheck = true) :
    ∀ u ∈ ruXN, u ≠ 1 → u ≠ ruZ → ruXN ≤ Subgroup.closure (insert ruZ
      (Set.range fun i : Fin 5 => ruG5 ^ (i : ℕ) * u * (ruG5 ^ (i : ℕ))⁻¹)) := by
  classical
  intro u hu hu1 huz
  set T : Set (Equiv.Perm (Fin 4060)) :=
    insert ruZ (Set.range fun i : Fin 5 => ruG5 ^ (i : ℕ) * u * (ruG5 ^ (i : ℕ))⁻¹) with hT
  set U := Subgroup.closure T with hU
  have hg5 := ruG5_pow_five h
  have hUX : U ≤ ruXN := by
    rw [hU, Subgroup.closure_le]
    rintro _ (rfl | ⟨i, rfl⟩)
    · exact ruZ_mem_ruXN
    · exact conj_mem_ruXN (ruC.pow_mem ruG5_mem _) hu
  have hTT : ∀ t ∈ T, ruG5 * t * ruG5⁻¹ ∈ T := by
    rintro t (rfl | ⟨i, rfl⟩)
    · left
      rw [ruG5_mul_ruZ, mul_inv_cancel_right]
    · right
      refine ⟨i + 1, ?_⟩
      have hv : ((i + 1 : Fin 5) : ℕ) = ((i : ℕ) + 1) % 5 := by
        rw [Fin.val_add, Fin.val_one]
      simp only
      rw [hv, ← pow_eq_pow_mod _ hg5, pow_succ']
      group
  have hUU : ∀ x ∈ U, ruG5 * x * ruG5⁻¹ ∈ U := by
    have hle : U ≤ U.comap (MulAut.conj ruG5).toMonoidHom := by
      rw [hU, Subgroup.closure_le]
      intro t ht
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact Subgroup.subset_closure (hTT t ht)
    intro x hx
    have hx' := Subgroup.mem_comap.1 (hle hx)
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hx'
  have : Fintype U := Fintype.ofFinite U
  let f : U → U := fun x => ⟨ruG5 * x * ruG5⁻¹, hUU x x.2⟩
  have hf : Function.Injective f := fun x y hxy => by
    have e : ruG5 * (x : Equiv.Perm (Fin 4060)) * ruG5⁻¹ = ruG5 * y * ruG5⁻¹ :=
      congrArg Subtype.val hxy
    exact Subtype.ext (by simpa using e)
  let σ : Equiv.Perm U := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
  have hσ : ∀ n : ℕ, ∀ x : U,
      ((σ ^ n) x : Equiv.Perm (Fin 4060)) = ruG5 ^ n * x * (ruG5 ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply]
      change ruG5 * ((σ ^ n) x : Equiv.Perm (Fin 4060)) * ruG5⁻¹ = _
      rw [ih x, pow_succ']
      group
  have hσ5 : σ ^ 5 ^ 1 = 1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    rw [pow_one, hσ 5 x, hg5, one_mul, inv_one, mul_one]
    rfl
  have hzU : ruZ ∈ U := Subgroup.subset_closure (Set.mem_insert _ _)
  have huU : u ∈ U := Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨0, by simp⟩)
  have hfix : ∀ x : U, σ x = x ↔
      ((x : Equiv.Perm (Fin 4060)) = 1 ∨ (x : Equiv.Perm (Fin 4060)) = ruZ) := by
    intro x
    constructor
    · intro hx
      have e : ruG5 * (x : Equiv.Perm (Fin 4060)) * ruG5⁻¹ = x := congrArg Subtype.val hx
      exact ruG5_cent_of_check h x (hUX x.2) (mul_inv_eq_iff_eq_mul.1 e)
    · intro hx
      apply Subtype.ext
      change ruG5 * (x : Equiv.Perm (Fin 4060)) * ruG5⁻¹ = x
      rcases hx with hx | hx
      · rw [hx, mul_one, mul_inv_cancel]
      · rw [hx, ruG5_mul_ruZ, mul_inv_cancel_right]
  have hsupp : σ.supportᶜ = {⟨1, U.one_mem⟩, ⟨ruZ, hzU⟩} := by
    ext x
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not, hfix, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro (hx | hx)
      · exact Or.inl (Subtype.ext hx)
      · exact Or.inr (Subtype.ext hx)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hcard2 : σ.supportᶜ.card = 2 := by
    rw [hsupp, Finset.card_insert_of_notMem, Finset.card_singleton]
    rw [Finset.mem_singleton]
    intro e
    exact RuB1X.ruZ_ne_one_of_E (congrArg Subtype.val e).symm
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 5) (n := 1) hσ5
  rw [hcard2] at hmod
  have hu_supp : (⟨u, huU⟩ : U) ∈ σ.support := by
    rw [Equiv.Perm.mem_support]
    intro e
    rcases (hfix _).1 e with e1 | e1
    · exact hu1 e1
    · exact huz e1
  have hcompl := Finset.card_compl σ.support
  rw [hcard2] at hcompl
  have hle_univ := Finset.card_le_univ σ.support
  have hpos : 0 < σ.support.card := Finset.card_pos.2 ⟨_, hu_supp⟩
  have hdvd : Nat.card U ∣ 2 ^ 5 := by
    have hd := Subgroup.card_dvd_of_le hUX
    rw [card_ruXN_of_check h] at hd
    exact hd
  obtain ⟨k, hk, hkU⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [Nat.card_eq_fintype_card] at hkU
  rw [hkU] at hmod hcompl hle_univ
  have h2k : 2 ^ k % 5 = 2 := by
    unfold Nat.ModEq at hmod
    omega
  have h3 : 3 ≤ 2 ^ k := by omega
  have hk5 : k = 5 := by
    revert h2k h3
    interval_cases k <;> norm_num
  have hcardU : Nat.card ruXN ≤ Nat.card U := by
    rw [card_ruXN_of_check h, Nat.card_eq_fintype_card, hkU, hk5]
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge hUX hcardU).ge

end CFSG.Sporadic.RuSchreier
