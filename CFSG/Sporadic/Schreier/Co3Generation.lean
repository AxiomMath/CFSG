module

public import CFSG.Sporadic.Schreier.Co3Second
public import CFSG.Sporadic.Schreier.Co3GenerationCheck

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3.Native CFSG.Sporadic.Mathieu CFSG.Blueprint
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier

theorem co3JointArrs_size : co3JointArrs.size = 25 := co3Field276_size' 10 rfl

theorem co3JointArrs_inv : ∀ j < co3JointArrs.size,
    isInvA 276 co3JointArrs[j]! (rawInvs 276 co3JointArrs)[j]! = true := by
  intro j hj
  rw [rawInvs, co3_getElem!_map hj]
  exact isInvA_co3Field276 (f := 10) (by norm_num) hj

theorem co3JointArrays :
    ChainArrays co3JointChain (co3JointArrs.extract 0 co3JointGenCount)
    co3JointArrs co3JointBaseArr
    (wordsArr co3JointGenCount co3JointStrongCount co3JointDerivations) :=
  chainArrays_ofArrays co3JointArrs_inv

theorem card_co3JointG :
    Nat.card co3JointG = 495766656000 := by
  rw [co3JointG, card_originalSubgroup_of_chainOK co3JointArrays (by norm_num)
    co3JointChain_check.1, co3JointChain_check.2]
  rfl

theorem extract_get {S : Array (Array ℕ)} {k j : ℕ} (hj : j < k) (hk : k ≤ S.size) :
    (S.extract 0 k)[j]! = S[j]! := by
  rw [getElem!_pos _ j (by simp; omega), getElem!_pos _ j (by omega), Array.getElem_extract]
  simp

theorem co3JointG_eq : co3JointG = Subgroup.closure
    {g | ∃ j < (co3JointArrs.extract 0 13).size,
      permOfArr 276 (co3JointArrs.extract 0 13)[j]! = g} := by
  rw [co3JointG, co3JointChain, ofArrays_originalSubgroup]
  congr 1
  ext g
  have hsz : (co3JointArrs.extract 0 13).size = 13 := by simp [co3JointArrs_size]
  rw [Set.mem_range, Set.mem_ofPred_eq, hsz]
  constructor
  · rintro ⟨i, rfl⟩
    have hi' : (i : ℕ) < 13 := i.2
    exact ⟨i, hi', by rw [extract_get hi' (by rw [co3JointArrs_size]; omega)]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, by rw [extract_get hi (by rw [co3JointArrs_size]; omega)]⟩

theorem co3MM1Gens_size : co3MM1Gens.size = 13 := by
  simp [co3MM1Gens, co3MArrs_size, co3M1Arrs_size]

theorem co3MM1Gens_get {i : ℕ} (hi : i < 13) :
    co3MM1Gens[i]! = if i < 7 then co3MArrs[i]! else co3M1Arrs[i - 7]! := by
  rw [co3MM1Gens, getElem!_pos _ i (by simp [co3MArrs_size, co3M1Arrs_size]; omega)]
  split_ifs with h
  · rw [Array.getElem_append_left (by simp [co3MArrs_size]; omega),
      ← getElem!_pos _ _ (by simp [co3MArrs_size]; omega),
      extract_get h (by rw [co3MArrs_size]; omega)]
  · rw [Array.getElem_append_right (by simp [co3MArrs_size]; omega),
      ← getElem!_pos _ _ (by simp [co3MArrs_size, co3M1Arrs_size]; omega)]
    have e : (co3MArrs.extract 0 7).size = 7 := by simp [co3MArrs_size]
    rw [e, extract_get (by omega : i - 7 < 6) (by rw [co3M1Arrs_size]; omega)]

theorem co3MM1Gens_mem {i : ℕ} (hi : i < 13) :
    permOfArr 276 co3MM1Gens[i]! ∈ co3M ⊔ co3M1 := by
  rw [co3MM1Gens_get hi]
  split_ifs with h
  · apply Subgroup.mem_sup_left
    rw [co3M_eq]
    exact Subgroup.subset_closure ⟨⟨i, h⟩, rfl⟩
  · apply Subgroup.mem_sup_right
    rw [co3M1_eq]
    exact Subgroup.subset_closure ⟨⟨i - 7, by omega⟩, rfl⟩

theorem rep_co3MM1Gens : ∀ i < co3MM1Gens.size,
    Rep 276 co3MM1Gens[i]! (permOfArr 276 co3MM1Gens[i]!) := by
  intro i hi
  rw [co3MM1Gens_size] at hi
  rw [co3MM1Gens_get hi]
  split_ifs with h
  · exact rep_co3MArr (by omega)
  · exact rep_co3M1Arr (by omega)

theorem rep_co3JointGens : ∀ j < (co3JointArrs.extract 0 13).size,
    Rep 276 (co3JointArrs.extract 0 13)[j]! (permOfArr 276 (co3JointArrs.extract 0 13)[j]!) := by
  intro j hj
  have hj' : j < 13 := by simpa [co3JointArrs_size] using hj
  rw [extract_get hj' (by rw [co3JointArrs_size]; omega)]
  exact (rep_permOfArr (co3JointArrs_inv j (by rw [co3JointArrs_size]; omega))).1

theorem co3M_sup_M1 :
    co3M ⊔ co3M1 = co3P := by
  have hJ : co3JointG ≤ co3M ⊔ co3M1 := by
    rw [co3JointG_eq, ← closure_eq_of_coversOK rep_co3MM1Gens rep_co3JointGens
      co3Generation_check.1, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    rw [co3MM1Gens_size] at hi
    exact co3MM1Gens_mem hi
  have hle : co3M ⊔ co3M1 ≤ co3P := sup_le co3M_le_P co3M1_le_P
  have hJP : co3JointG = co3P :=
    Subgroup.eq_of_le_of_card_ge (hJ.trans hle) (by rw [card_co3JointG, card_co3P])
  exact le_antisymm hle (hJP ▸ hJ)

theorem co3D0Arrs_size : co3D0Arrs.size = 5 := co3Field276_size' 4 rfl

theorem rep_co3D0Gen
    {k : ℕ} (hk : k < 5) : Rep 276 co3D0Arrs[k]! (co3D0Gen k) :=
  (rep_permOfArr (isInvA_co3Field276 (f := 4) (by norm_num)
    (by rw [show (co3Field276 4).size = 5 from co3D0Arrs_size]; omega))).1

theorem mem_co3M1_of_sift
    {g : Array ℕ} {G : Equiv.Perm (Fin 276)} (hG : Rep 276 g G)
    (h : siftA 276 co3M1Levels co3M1BaseArr 0 g = true) : G ∈ co3M1 :=
  (siftA_iff_mem_originalSubgroup co3M1Arrays (by norm_num) co3M1Chain_check.1 hG).1 h

theorem co3D0Gen_mem
    {k : ℕ} (hk : k < 5) : co3D0Gen k ∈ co3M ⊓ co3M1 :=
  Subgroup.mem_inf.2 ⟨mem_co3M_of_sift (rep_co3D0Gen hk) (co3Generation_check.2 k hk).1,
    mem_co3M1_of_sift (rep_co3D0Gen hk) (co3Generation_check.2 k hk).2⟩

theorem co3D0_le :
    co3D0 ≤ co3M ⊓ co3M1 := by
  rw [co3D0, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact co3D0Gen_mem hk

@[expose] def co3D0M1
    (k : ℕ) (hk : k < 5) : co3M1 :=
  ⟨co3D0Gen k, (Subgroup.mem_inf.1 (co3D0Gen_mem hk)).2⟩

@[expose] def co3D0K
    (k : ℕ) : Equiv.Perm (Fin 12) :=
  if hk : k < 5 then co3Kappa1 (co3D0M1 k hk) else 1

theorem rep_co3D0Kappa1
    {k : ℕ} (hk : k < 5) :
    CFSG.Monster.B.Co2.Rep 12 co3D0Kappa1[k]! (co3D0K k) := by
  rw [co3D0K, dite_eq_left hk, co3D0Kappa1, co3_getElem!_ofFn _ hk]
  exact rep_kappa1 (rep_co3D0Gen hk)

theorem toNat_map_ofNat_getElem! (a : Array ℕ) (i : ℕ) :
    ((a.map UInt32.ofNat)[i]!).toNat = a[i]! % 2 ^ 32 := by
  by_cases h : i < a.size
  · rw [getElem!_pos _ i (by simpa using h), Array.getElem_map, getElem!_pos a i h,
      UInt32.toNat_ofNat']
  · rw [getElem!_neg _ i (by simpa using h), getElem!_neg a i h]
    rfl

theorem rep_co3ToT {n : ℕ} (hn : n < 2 ^ 32) {a : Array ℕ} {g : Equiv.Perm (Fin n)}
    (ha : CFSG.Monster.B.Co2.Rep n a g) : CFSG.Sporadic.Th.Rep n (co3ToT a) g := by
  intro i hi
  rw [idx_of_lt _ hi, co3ToT, ap, toNat_map_ofNat_getElem!, ha ⟨i, hi⟩,
    Nat.mod_eq_of_lt ((Fin.isLt _).trans hn)]
  rfl

theorem co3D0Test_iff
    {T : Table} {g : Equiv.Perm (Fin 12)} (hT : CFSG.Sporadic.Th.Rep 12 T g) :
    co3D0Test T = true ↔ ∀ k < 5, g * co3D0K k = co3D0K k * g := by
  unfold co3D0Test
  rw [allLt_iff]
  constructor
  · intro h k hk
    have hD := rep_co3ToT (by norm_num) (rep_co3D0Kappa1 hk)
    have h1 := Rep.compT hT hD
    have h2 := Rep.compT hD hT
    refine Equiv.ext fun x => Fin.ext ?_
    have := allLt_iff.1 (h k hk) x x.2
    rw [beq_iff_eq, h1 x x.2, h2 x x.2, idx_of_lt _ x.2, idx_of_lt _ x.2] at this
    exact this
  · intro h k hk
    have hD := rep_co3ToT (by norm_num) (rep_co3D0Kappa1 hk)
    have h1 := Rep.compT hT hD
    have h2 := Rep.compT hD hT
    rw [allLt_iff]
    intro i hi
    rw [beq_iff_eq, h1 i hi, h2 i hi, h k hk]

theorem card_co3D0Cent :
    Nat.card {x : NativeSporadic.M12 //
    ∀ k < 5, (x : Equiv.Perm (Fin 12)) * co3D0K k = co3D0K k * x} = 2 := by
  have hQ : ValidSchreier m12Certificate := m12Certificate_check
  have h := countProducts_spec (n := 12) (G := Equiv.Perm (Fin 12)) (f := co3D0Test)
    (P := fun g => ∀ k < 5, g * co3D0K k = co3D0K k * g) (fun T g hT => co3D0Test_iff hT)
    (forall₂_levelTables (by norm_num) m12Certificate) (Rep.idT (by norm_num))
  rw [co3D0Count_check] at h
  simp only [one_mul, List.map_id'] at h
  have h2 := @card_subtype_eq_countP _ _ m12Certificate.originalSubgroup
    (enumeration m12Certificate) (enumeration_nodup m12Certificate hQ)
    (mem_enumeration_iff m12Certificate hQ)
    (fun g : Equiv.Perm (Fin 12) => ∀ k < 5, g * co3D0K k = co3D0K k * g) (Classical.decPred _)
  rw [m12Certificate_originalSubgroup] at h2
  rw [h2, enumeration, h]
  exact List.countP_congr fun x _ => by simp only [decide_eq_true_eq]

@[expose] def co3CD0 :
    Subgroup co3M1 :=
  Subgroup.centralizer (Set.range fun k : Fin 5 => co3D0M1 k k.2)

theorem mem_co3CD0
    (m : co3M1) :
    m ∈ co3CD0 ↔ ∀ k (hk : k < 5), m * co3D0M1 k hk = co3D0M1 k hk * m := by
  rw [co3CD0, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    exact (h _ ⟨⟨k, hk⟩, rfl⟩).symm
  · rintro h _ ⟨k, rfl⟩
    exact (h k k.2).symm

theorem card_co3CD0_le :
    Nat.card co3CD0 ≤ 4 := by
  set f := co3Kappa1.comp co3CD0.subtype
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
  have hker : Nat.card f.ker ≤ 2 := by
    rw [← card_ker_co3Kappa1]
    refine Nat.card_le_card_of_injective (fun x => ⟨(x : co3CD0), ?_⟩) ?_
    · exact x.2
    · intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : co3Kappa1.ker => ((z : co3M1))) h))
  have hrange : Nat.card f.range ≤ 2 := by
    rw [← card_co3D0Cent]
    refine Nat.card_le_card_of_injective (fun y => ⟨⟨y, ?_⟩, ?_⟩) ?_
    · obtain ⟨m, hm⟩ := y.2
      rw [← co3Kappa1_range, ← hm]
      exact ⟨(m : co3M1), rfl⟩
    · intro k hk
      obtain ⟨m, hm⟩ := y.2
      show (y : Equiv.Perm (Fin 12)) * co3D0K k = co3D0K k * y
      rw [← hm, co3D0K, dite_eq_left hk]
      change co3Kappa1 m * co3Kappa1 (co3D0M1 k hk) = co3Kappa1 (co3D0M1 k hk) * co3Kappa1 m
      rw [← map_mul, ← map_mul, (mem_co3CD0 (m : co3M1)).1 m.2 k hk]
    · intro x y h
      exact Subtype.ext (congrArg (fun z => ((z.1 : NativeSporadic.M12) : Equiv.Perm (Fin 12))) h)
  rw [h1]
  calc Nat.card f.range * Nat.card f.ker ≤ 2 * 2 := Nat.mul_le_mul hrange hker
    _ = 4 := rfl

@[expose] def co3CM1 : Subgroup (Equiv.Perm (Fin 276)) :=
  co3M1 ⊓ Subgroup.centralizer ((co3M ⊓ co3M1 : Subgroup (Equiv.Perm (Fin 276))) :
    Set (Equiv.Perm (Fin 276)))

theorem card_co3CM1_le :
    Nat.card co3CM1 ≤ 4 := by
  refine le_trans (Nat.card_le_card_of_injective
    (fun x : co3CM1 => (⟨⟨x, (Subgroup.mem_inf.1 x.2).1⟩, ?_⟩ : co3CD0)) ?_) card_co3CD0_le
  · rw [mem_co3CD0]
    intro k hk
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 x.2).2 _ (co3D0Gen_mem hk)).symm
  · intro x y h
    exact Subtype.ext (congrArg (fun z : co3CD0 => ((z : co3M1) : Equiv.Perm (Fin 276))) h)

theorem co3CM1_solvable :
    Group.IsSolvable co3CM1 :=
  CFSG.ComponentClassification.CatalogueSchreierAlternating.solvable_of_card_le_four
    card_co3CM1_le

theorem AT_Co3_two_centralizer_generation :
    co3M ⊔ co3M1 = co3P ∧ co3D0 ≤ co3M ⊓ co3M1 ∧ Nat.card co3CM1 ≤ 4 ∧
      Group.IsSolvable co3CM1 :=
  ⟨co3M_sup_M1, co3D0_le, card_co3CM1_le, co3CM1_solvable⟩

end CFSG.Sporadic.Schreier.Co3
