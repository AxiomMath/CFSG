module

public import CFSG.Sporadic.Schreier.RuCheckCenters
public import CFSG.Sporadic.Schreier.RuLocalRes
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem nat_any_iff' {n : ℕ} {p : ℕ → Bool} :
    (Nat.any n fun i _ => p i) = true ↔ ∃ i < n, p i = true := by
  rw [Nat.any_eq_finRange_any, List.any_eq_true]
  constructor
  · rintro ⟨⟨i, hi⟩, -, h⟩
    exact ⟨i, hi, h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, hi⟩, List.mem_finRange _, h⟩

theorem conj_closed {G : Type*} [Group G] {X : Set G} (hX : X.Finite) {Y : Set G}
    (h : ∀ g ∈ Y, ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    ∀ g ∈ Subgroup.closure Y, ∀ x ∈ X, g * x * g⁻¹ ∈ X := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact h g hg
  | one => intro x hx; simpa using hx
  | mul g g' _ _ ihg ihg' =>
    intro x hx
    have := ihg _ (ihg' x hx)
    simpa [mul_assoc] using this
  | inv g _ ihg =>
    intro x hx
    have hmaps : Set.MapsTo (fun y => g * y * g⁻¹) X X := fun y hy => ihg y hy
    have hinj : Set.InjOn (fun y => g * y * g⁻¹) X := fun y _ y' _ e => by
      simpa using e
    obtain ⟨y, hy, rfl⟩ := ((hX.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj).surjOn hx
    simpa [mul_assoc] using hy

@[expose] def ruEElt (i : ℕ) : Equiv.Perm (Fin 4060) := permOfArr 4060 ruEArr[i]!

theorem rep_ruEElt
    {i : ℕ} (hi : i < 7) : Rep 4060 ruEArr[i]! (ruEElt i) :=
  (rep_permOfArr (ruE_check.2.2.2.2.1 i hi)).1

theorem ruEElt_zero :
    ruEElt 0 = ruZ := by
  have h := rep_ruEElt (i := 0) (by norm_num)
  rw [ruE_check.2.2.2.1] at h
  exact h.unique rep_ruZ

theorem rep_ruNGensA :
    ∀ g < 2, Rep 4060 ruNGensA[g]! ([ruNs0, ruNs1].getD g 1) := rep_ruNsPair

theorem ruNGensA_zero : ruNGensA[0]! = ruNs0A := by simp [ruNGensA]

theorem ruNGensA_one : ruNGensA[1]! = ruNs1A := by simp [ruNGensA]

theorem ruNGensA_inv :
    ∀ g < 2, isInvA 4060 ruNGensA[g]! (invCand 4060 ruNGensA[g]!) = true := by
  intro g hg
  interval_cases g
  · rw [ruNGensA_zero]
    exact ruBasic_check.2.2.2.2.2.2.2.2.2.2.1
  · rw [ruNGensA_one]
    exact ruBasic_check.2.2.2.2.2.2.2.2.2.2.2.1

theorem rep_ruConjA
    {g : ℕ} (hg : g < 2) {e : Array ℕ} {E : Equiv.Perm (Fin 4060)}
    (he : Rep 4060 e E) :
    Rep 4060 (ruConjA ruNGensA[g]! e) ([ruNs0, ruNs1].getD g 1 * E * ([ruNs0, ruNs1].getD g 1)⁻¹) :=
  rep_compA (rep_compA (rep_ruNGensA g hg) he)
    (rep_inv_of_isInvA (rep_ruNGensA g hg) (ruNGensA_inv g hg))

theorem ruNGen_mem {g : ℕ} (hg : g < 2) : [ruNs0, ruNs1].getD g 1 ∈ ruN := by
  interval_cases g
  · exact ruNs0_memN
  · exact ruNs1_memN

theorem ruEElt_conj :
    ∀ i < 7, ∃ m ∈ ruN, ruEElt i = m * ruZ * m⁻¹ := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact ⟨1, ruN.one_mem, by rw [ruEElt_zero]; group⟩
    · obtain ⟨hp, hg, he⟩ := ruE_check.2.2.2.2.2.1 i hpos hi
      obtain ⟨m, hm, hme⟩ := ih _ hp (by omega)
      have := eq_of_eqA (rep_ruEElt hi) (rep_ruConjA hg (rep_ruEElt (by omega))) he
      refine ⟨[ruNs0, ruNs1].getD ruEGen[i]! 1 * m, ruN.mul_mem (ruNGen_mem hg) hm, ?_⟩
      rw [this, hme]
      group

abbrev ruEList : Set (Equiv.Perm (Fin 4060)) := {g | ∃ i < 7, ruEElt i = g}

theorem ruEList_finite : ruEList.Finite := by
  have : ruEList = (Finset.image ruEElt (Finset.range 7) : Set _) := by
    ext g
    simp
  rw [this]
  exact Finset.finite_toSet _

theorem ruN_conj_ruZ
    {m : Equiv.Perm (Fin 4060)} (hm : m ∈ ruN) : m * ruZ * m⁻¹ ∈ ruEList := by
  have hcl : ∀ g ∈ ({ruNs0, ruNs1} : Set _), ∀ x ∈ ruEList, g * x * g⁻¹ ∈ ruEList := by
    rintro g hg _ ⟨i, hi, rfl⟩
    have hg' : ∃ k < 2, [ruNs0, ruNs1].getD k 1 = g := by
      rcases hg with rfl | rfl
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, rfl⟩
    obtain ⟨k, hk, rfl⟩ := hg'
    obtain ⟨j, hj, hje⟩ := ruE_check.2.2.2.2.2.2.1 i hi k hk
    exact ⟨j, hj, (eq_of_eqA (rep_ruConjA hk (rep_ruEElt hi)) (rep_ruEElt hj) hje).symm⟩
  exact conj_closed ruEList_finite hcl m hm ruZ ⟨0, by norm_num, ruEElt_zero⟩

theorem ruE_eq :
    ruE = {1} ∪ ruEList := by
  ext g
  simp only [ruE, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  constructor
  · rintro (h | ⟨m, hm, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (ruN_conj_ruZ hm)
  · rintro (h | ⟨i, hi, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (ruEElt_conj i hi)

theorem ruEElt_sq {i : ℕ} (hi : i < 7) : ruEElt i * ruEElt i = 1 :=
  eq_of_eqA (rep_compA (rep_ruEElt hi) (rep_ruEElt hi)) rep_idA (ruE_check.2.2.2.2.2.2.2.2.2.1 i hi)

theorem ruEElt_ne_one
    {i : ℕ} (hi : i < 7) : ruEElt i ≠ 1 := fun h => by
  have := ruE_check.2.2.2.2.2.2.2.2.1 i hi
  rw [(eqA_iff (rep_ruEElt hi) rep_idA).2 h] at this
  exact Bool.noConfusion this

theorem ruEElt_inj
    {i j : ℕ} (hi : i < 7) (hj : j < 7) (h : ruEElt i = ruEElt j) : i = j := by
  by_contra hne
  have := ruE_check.2.2.2.2.2.2.2.1 i hi j hj hne
  rw [(eqA_iff (rep_ruEElt hi) (rep_ruEElt hj)).2 h] at this
  exact Bool.noConfusion this

theorem ruEElt_mul_mem {i j : ℕ} (hi : i < 7) (hj : j < 7) :
    ruEElt i * ruEElt j ∈ ({1} ∪ ruEList : Set _) := by
  by_cases hij : i = j
  · subst hij
    exact Or.inl (ruEElt_sq hi)
  · obtain ⟨k, hk, he⟩ := ruE_check.2.2.2.2.2.2.2.2.2.2.1 i hi j hj hij
    exact Or.inr ⟨k, hk, (eq_of_eqA (rep_compA (rep_ruEElt hi) (rep_ruEElt hj))
      (rep_ruEElt hk) he).symm⟩

theorem ruEElt_comm {i j : ℕ} (hi : i < 7) (hj : j < 7) :
    ruEElt i * ruEElt j = ruEElt j * ruEElt i :=
  eq_of_eqA (rep_compA (rep_ruEElt hi) (rep_ruEElt hj)) (rep_compA (rep_ruEElt hj) (rep_ruEElt hi))
    (ruE_check.2.2.2.2.2.2.2.2.2.2.2.1 i hi j hj)

theorem ruE_mul_mem
    {a b : Equiv.Perm (Fin 4060)} (ha : a ∈ ({1} ∪ ruEList : Set _))
    (hb : b ∈ ({1} ∪ ruEList : Set _)) : a * b ∈ ({1} ∪ ruEList : Set _) := by
  rcases ha with ha | ⟨i, hi, rfl⟩
  · rw [Set.mem_singleton_iff.1 ha, one_mul]
    exact hb
  · rcases hb with hb | ⟨j, hj, rfl⟩
    · rw [Set.mem_singleton_iff.1 hb, mul_one]
      exact Or.inr ⟨i, hi, rfl⟩
    · exact ruEElt_mul_mem hi hj

theorem ruE_inv_eq
    {a : Equiv.Perm (Fin 4060)} (ha : a ∈ ({1} ∪ ruEList : Set _)) : a⁻¹ = a := by
  rcases ha with ha | ⟨i, hi, rfl⟩
  · rw [Set.mem_singleton_iff.1 ha, inv_one]
  · exact inv_eq_of_mul_eq_one_right (ruEElt_sq hi)

@[expose] def ruESub :
    Subgroup (Equiv.Perm (Fin 4060)) where
  carrier := ruE
  mul_mem' ha hb := by
    rw [ruE_eq] at *
    exact ruE_mul_mem ha hb
  one_mem' := by
    rw [ruE_eq]
    exact Or.inl rfl
  inv_mem' ha := by
    rw [ruE_eq] at *
    rw [ruE_inv_eq ha]
    exact ha

theorem mem_ruESub
    {g : Equiv.Perm (Fin 4060)} : g ∈ ruESub ↔ g = 1 ∨ ∃ i < 7, ruEElt i = g := by
  change g ∈ ruE ↔ _
  rw [ruE_eq]
  rfl

theorem ruESub_comm
    (a b : ruESub) : a * b = b * a := by
  apply Subtype.ext
  rcases mem_ruESub.1 a.2 with ha | ⟨i, hi, hia⟩
  · show (a : Equiv.Perm (Fin 4060)) * b = b * a
    rw [ha, one_mul, mul_one]
  · rcases mem_ruESub.1 b.2 with hb | ⟨j, hj, hjb⟩
    · show (a : Equiv.Perm (Fin 4060)) * b = b * a
      rw [hb, one_mul, mul_one]
    · show (a : Equiv.Perm (Fin 4060)) * b = b * a
      rw [← hia, ← hjb]
      exact ruEElt_comm hi hj

theorem ruESub_sq
    (a : ruESub) : a ^ 2 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, pow_two, Subgroup.coe_one]
  rcases mem_ruESub.1 a.2 with ha | ⟨i, hi, hia⟩
  · rw [ha, one_mul]
  · rw [← hia]
    exact ruEElt_sq hi

instance ruESub_elem :
    CFSG.IsElementaryAbelian 2 ruESub :=
  { toIsMulCommutative := ⟨⟨ruESub_comm⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one ruESub_sq }

theorem card_ruESub :
    Nat.card ruESub = 8 := by
  classical
  have hset : (ruESub : Set (Equiv.Perm (Fin 4060))) =
      ((insert 1 (Finset.image ruEElt (Finset.range 7)) : Finset _) : Set _) := by
    ext g
    rw [SetLike.mem_coe, mem_ruESub]
    simp [eq_comm]
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Finset.card_insert_of_notMem, Finset.card_image_of_injOn, Finset.card_range]
  · intro i hi j hj h
    exact ruEElt_inj (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h
  · simp only [Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro i hi h
    exact ruEElt_ne_one hi h

theorem ruZ_memE : ruZ ∈ ruE := by
  rw [ruE_eq]
  exact Or.inr ⟨0, by norm_num, ruEElt_zero⟩

end CFSG.Sporadic.RuSchreier
