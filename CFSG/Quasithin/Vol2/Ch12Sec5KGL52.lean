module

public import CFSG.Quasithin.Vol2.Ch12Sec5Pm
public import CFSG.Quasithin.Vol2.Ch12Sec5KGM24
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherBorelOvergroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Q1
public import CFSG.Sporadic.Schreier.J4SSylow

public section

namespace CFSG.Quasithin.H13.S125KG.L52

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open scoped commutatorElement

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

@[expose] noncomputable def tv (a b : Fin 5) (h : a ≠ b) : SL5 :=
  SpecialLinearGroup.transvection h (1 : ZMod 2)

theorem transvection_mul_comm : ∀ a b c : Fin 5, a ≠ b → b ≠ c → a ≠ c →
    Matrix.transvection a c (1 : ZMod 2) * Matrix.transvection c b 1 =
      Matrix.transvection a b 1 * (Matrix.transvection c b 1 * Matrix.transvection a c 1) := by
  decide +kernel

theorem commutator_tv {a b c : Fin 5} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ⁅tv a c hac, tv c b hbc.symm⁆ = tv a b hab := by
  have h : tv a c hac * tv c b hbc.symm = tv a b hab * (tv c b hbc.symm * tv a c hac) :=
    Subtype.ext (transvection_mul_comm a b c hab hbc hac)
  rw [commutatorElement_def, h]
  group

theorem tv_mem_stab {a b : Fin 5} (h : a ≠ b) {k : ℕ} (hk : ¬ (b.val < k ∧ k ≤ a.val)) :
    tv a b h ∈ flagStabilizer 5 (ZMod 2) {k} := by
  rw [← S125Pm.stabK_eq, S125Tr.mem_stabK]
  intro i j hj hi
  rw [tv, SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.one_apply_ne
    (fun hij => by rw [hij] at hi; omega), Matrix.single_apply, zero_add]
  split_ifs with hc
  · obtain ⟨rfl, rfl⟩ := hc
    exact absurd ⟨hj, hi⟩ hk
  · rfl

theorem tv_mem_flagStabilizer {a b : Fin 5} (h : a ≠ b) {I : Set ℕ}
    (hI : ∀ k ∈ I, ¬ (b.val < k ∧ k ≤ a.val)) : tv a b h ∈ flagStabilizer 5 (ZMod 2) I := by
  rw [mem_flagStabilizer]
  intro k hk
  have := tv_mem_stab h (hI k hk)
  rw [mem_flagStabilizer] at this
  exact this k (Set.mem_singleton k)

@[expose] def blk3 (p : ℕ) : Set (Fin 5) := {a | p ≤ a.val ∧ a.val ≤ p + 2}

@[expose] noncomputable def H3 (p : ℕ) : Subgroup SL5 :=
  Subgroup.closure {g | ∃ (a b : Fin 5) (h : a ≠ b), a ∈ blk3 p ∧ b ∈ blk3 p ∧ g = tv a b h}

theorem H3_le_commutator {p : ℕ} (hp : p + 2 < 5) : H3 p ≤ ⁅H3 p, H3 p⁆ := by
  rw [H3, Subgroup.closure_le]
  rintro _ ⟨a, b, hab, ha, hb, rfl⟩
  obtain ⟨c, hc, hca, hcb⟩ : ∃ c : Fin 5, c ∈ blk3 p ∧ c ≠ a ∧ c ≠ b := by
    simp only [blk3, Set.mem_ofPred_eq] at ha hb
    have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    refine ⟨⟨3 * p + 3 - a.val - b.val, by omega⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · show p ≤ 3 * p + 3 - a.val - b.val
      omega
    · show 3 * p + 3 - a.val - b.val ≤ p + 2
      omega
    · intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    · intro h
      have := congrArg Fin.val h
      simp only at this
      omega
  rw [← commutator_tv hab hcb.symm hca.symm]
  exact Subgroup.commutator_mem_commutator
    (Subgroup.subset_closure ⟨a, c, hca.symm, ha, hc, rfl⟩)
    (Subgroup.subset_closure ⟨c, b, hcb, hc, hb, rfl⟩)

theorem H3_le_flagStabilizer {p : ℕ} {I : Set ℕ} (h1 : p + 1 ∉ I) (h2 : p + 2 ∉ I) :
    H3 p ≤ flagStabilizer 5 (ZMod 2) I := by
  rw [H3, Subgroup.closure_le]
  rintro _ ⟨a, b, hab, ha, hb, rfl⟩
  simp only [blk3, Set.mem_ofPred_eq] at ha hb
  refine tv_mem_flagStabilizer hab fun k hk hba => ?_
  have : k = p + 1 ∨ k = p + 2 := by omega
  rcases this with rfl | rfl
  · exact h1 hk
  · exact h2 hk

theorem tv_mem_H3 {p : ℕ} {a b : Fin 5} (h : a ≠ b) (ha : p ≤ a.val ∧ a.val ≤ p + 2)
    (hb : p ≤ b.val ∧ b.val ≤ p + 2) : tv a b h ∈ H3 p :=
  Subgroup.subset_closure ⟨a, b, h, ha, hb, rfl⟩

theorem refl_one : reflection 5 (ZMod 2) 1 (by norm_num) (by norm_num) =
    tv 0 1 (by decide) * tv 1 0 (by decide) * tv 0 1 (by decide) := by
  apply Subtype.ext
  rw [BinaryParabolic.reflection_eq_permMatrix]
  decide +kernel

theorem refl_two : reflection 5 (ZMod 2) 2 (by norm_num) (by norm_num) =
    tv 1 2 (by decide) * tv 2 1 (by decide) * tv 1 2 (by decide) := by
  apply Subtype.ext
  rw [BinaryParabolic.reflection_eq_permMatrix]
  decide +kernel

theorem refl_three : reflection 5 (ZMod 2) 3 (by norm_num) (by norm_num) =
    tv 2 3 (by decide) * tv 3 2 (by decide) * tv 2 3 (by decide) := by
  apply Subtype.ext
  rw [BinaryParabolic.reflection_eq_permMatrix]
  decide +kernel

theorem refl_four : reflection 5 (ZMod 2) 4 (by norm_num) (by norm_num) =
    tv 3 4 (by decide) * tv 4 3 (by decide) * tv 3 4 (by decide) := by
  apply Subtype.ext
  rw [BinaryParabolic.reflection_eq_permMatrix]
  decide +kernel

theorem reflection_mem_perfectResidual {j : ℕ} (hj : 1 ≤ j) (hj5 : j < 5) {I : Set ℕ}
    (hjI : j ∉ I) (h : (j + 1 < 5 ∧ j + 1 ∉ I) ∨ (2 ≤ j ∧ j - 1 ∉ I)) :
    reflection 5 (ZMod 2) j hj hj5 ∈
      CFSG.inSubgroup CFSG.perfectResidual (flagStabilizer 5 (ZMod 2) I) := by
  obtain ⟨p, hp, hp1, hp2, hjp⟩ : ∃ p : ℕ, p + 2 < 5 ∧ p + 1 ∉ I ∧ p + 2 ∉ I ∧
      (p + 1 = j ∨ p + 2 = j) := by
    rcases h with ⟨h5, h1⟩ | ⟨h2, h1⟩
    · exact ⟨j - 1, by omega, by rwa [show j - 1 + 1 = j by omega],
        by rwa [show j - 1 + 2 = j + 1 by omega], Or.inl (by omega)⟩
    · exact ⟨j - 2, by omega, by rwa [show j - 2 + 1 = j - 1 by omega],
        by rwa [show j - 2 + 2 = j by omega], Or.inr (by omega)⟩
  have hH := S125KG.le_inSubgroup_perfectResidual_of_le (H3_le_flagStabilizer hp1 hp2)
    (H3_le_commutator hp)
  refine hH ?_
  have hj4 : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases hj4 with rfl | rfl | rfl | rfl
  · rw [refl_one]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_ <;>
      exact tv_mem_H3 _ (by simp; omega) (by simp; omega)
  · rw [refl_two]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_ <;>
      exact tv_mem_H3 _ (by simp; omega) (by simp; omega)
  · rw [refl_three]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_ <;>
      exact tv_mem_H3 _ (by simp; omega) (by simp; omega)
  · rw [refl_four]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_ <;>
      exact tv_mem_H3 _ (by simp; omega) (by simp; omega)

theorem card_U : Nat.card (unitriangular 5 (ZMod 2)) = 1024 := by
  rw [card_unitriangular, Nat.card_zmod]
  norm_num

theorem refl_mem_iff {I : Set ℕ} {j : ℕ} (hj : 1 ≤ j) (hjn : j < 5) :
    reflection 5 (ZMod 2) j hj hjn ∈ flagStabilizer 5 (ZMod 2) I ↔ j ∉ I :=
  (subflag_stabilizer_generation I).2.2 j hj hjn

theorem eq_flag {A : Subgroup SL5} (hA : unitriangular 5 (ZMod 2) ≤ A) :
    A = flagStabilizer 5 (ZMod 2) (borelOvergroupCuts A) :=
  (borel_overgroups A (BinaryParabolic.upperTriangular_eq_unitriangular ▸ hA)).1

theorem mem_cuts_iff {A : Subgroup SL5} {i : ℕ} (hi : 1 ≤ i) (hin : i < 5) :
    i ∈ borelOvergroupCuts A ↔ reflection 5 (ZMod 2) i hi hin ∉ A :=
  ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hi, hin, h⟩⟩

theorem cuts_bound {A : Subgroup SL5} {i : ℕ} (h : i ∈ borelOvergroupCuts A) : 1 ≤ i ∧ i < 5 := by
  obtain ⟨h1, h5, -⟩ := h
  exact ⟨h1, h5⟩

theorem relIndex_Q2 : (unitriangular 5 (ZMod 2)).relIndex (flagStabilizer 5 (ZMod 2) {2}) = 63 := by
  rw [← S125Pm.stabK_eq]
  exact S125Pm.relIndex_stab2

theorem map_graph_Q3 :
    (flagStabilizer 5 (ZMod 2) {3}).map (BinaryParabolic.graphAut 5).toMonoidHom =
      flagStabilizer 5 (ZMod 2) {2} := by
  set A := (flagStabilizer 5 (ZMod 2) {3}).map (BinaryParabolic.graphAut 5).toMonoidHom with hA
  have hUA : unitriangular 5 (ZMod 2) ≤ A := by
    rw [← BinaryParabolic.map_graphAut_unitriangular, hA]
    exact Subgroup.map_mono (BinaryParabolic.unitriangular_le_flagStabilizer _)
  have hmem : ∀ (i : ℕ) (hi : 1 ≤ i) (hin : i < 5),
      reflection 5 (ZMod 2) i hi hin ∈ A ↔ 5 - i ∉ ({3} : Set ℕ) := by
    intro i hi hin
    rw [hA, Subgroup.mem_map_equiv]
    change BinaryParabolic.graphFun _ ∈ _ ↔ _
    rw [BinaryParabolic.graphFun_reflection hi hin, refl_mem_iff]
  rw [eq_flag hUA]
  congr 1
  ext i
  constructor
  · intro h
    obtain ⟨hi, hin⟩ := cuts_bound h
    rw [mem_cuts_iff hi hin, hmem, not_not, Set.mem_singleton_iff] at h
    rw [Set.mem_singleton_iff]
    omega
  · intro h
    rw [Set.mem_singleton_iff] at h
    subst h
    rw [mem_cuts_iff (by norm_num) (by norm_num), hmem, not_not]
    rfl

theorem relIndex_Q3 : (unitriangular 5 (ZMod 2)).relIndex (flagStabilizer 5 (ZMod 2) {3}) = 63 := by
  have h := Subgroup.relIndex_map_map_of_injective (unitriangular 5 (ZMod 2))
    (flagStabilizer 5 (ZMod 2) {3}) (f := (BinaryParabolic.graphAut 5).toMonoidHom)
    (BinaryParabolic.graphAut 5).injective
  rw [BinaryParabolic.map_graphAut_unitriangular, map_graph_Q3, relIndex_Q2] at h
  exact h.symm

theorem card_of_relIndex {A : Subgroup SL5} (hUA : unitriangular 5 (ZMod 2) ≤ A)
    (h63 : (unitriangular 5 (ZMod 2)).relIndex A = 63) : Nat.card A = 63 * 1024 := by
  have h := Subgroup.relIndex_mul_card (H := unitriangular 5 (ZMod 2)) (K := A)
  rw [inf_eq_left.2 hUA, h63, card_U] at h
  exact h.symm

@[expose] def g5a : SL5 :=
  ⟨!![1, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 1, 0, 0, 1; 0, 0, 1, 0, 1; 0, 0, 0, 1, 1], by decide +kernel⟩

@[expose] def g5b : SL5 :=
  ⟨!![0, 0, 0, 1, 0; 1, 0, 0, 1, 0; 0, 1, 0, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1], by decide +kernel⟩

theorem orderOf_g5a : orderOf g5a = 5 :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  orderOf_eq_prime (Subtype.ext (by decide +kernel)) (fun h => by
    have := congrArg (fun g : SL5 => (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) 1 1) h
    revert this
    decide +kernel)

theorem orderOf_g5b : orderOf g5b = 5 :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  orderOf_eq_prime (Subtype.ext (by decide +kernel)) (fun h => by
    have := congrArg (fun g : SL5 => (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 0) h
    revert this
    decide +kernel)

theorem g5a_mem : g5a ∈ flagStabilizer 5 (ZMod 2) {1} := by
  rw [← S125Pm.stabK_eq, S125Tr.mem_stabK]
  intro i j hj hi
  fin_cases i <;> fin_cases j <;> simp_all <;> rfl

theorem g5b_mem : g5b ∈ flagStabilizer 5 (ZMod 2) {4} := by
  rw [← S125Pm.stabK_eq, S125Tr.mem_stabK]
  intro i j hj hi
  fin_cases i <;> fin_cases j <;> simp_all <;> rfl

theorem not_mem_of_orderOf_five {A : Subgroup SL5} (hUA : unitriangular 5 (ZMod 2) ≤ A)
    (h63 : (unitriangular 5 (ZMod 2)).relIndex A = 63) {g : SL5} (hg : g ∈ A)
    (h5 : orderOf g = 5) : False := by
  have h := Subgroup.orderOf_dvd_natCard A hg
  rw [h5, card_of_relIndex hUA h63] at h
  norm_num at h

theorem relIndex_Q14_ne :
    (unitriangular 5 (ZMod 2)).relIndex (flagStabilizer 5 (ZMod 2) {1, 4}) ≠ 63 := by
  intro h63
  have hc := card_of_relIndex (BinaryParabolic.unitriangular_le_flagStabilizer _) h63
  have hK : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hker := CFSG.QuasithinUnique.Vol2Native.L239.L52.q1_ker_isPGroup (K := ZMod 2) hK
  have h1 := Subgroup.card_ker_mul_card_range (CFSG.QuasithinUnique.Vol2Native.L239.L52.q1
    (ZMod 2) hK)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hker
  have h2 : Nat.card (CFSG.QuasithinUnique.Vol2Native.L239.L52.q1 (ZMod 2) hK).range ∣ 168 :=
    card_sl_three_zmod_two ▸ Subgroup.card_subgroup_dvd_card _
  rw [hk, hc] at h1
  have h9 : 9 ∣ Nat.card (CFSG.QuasithinUnique.Vol2Native.L239.L52.q1 (ZMod 2) hK).range := by
    have : 9 ∣ 2 ^ k *
        Nat.card (CFSG.QuasithinUnique.Vol2Native.L239.L52.q1 (ZMod 2) hK).range := by
      rw [h1]
      norm_num
    exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right k (by norm_num)) this
  have := h9.trans h2
  norm_num at this

theorem index63 {N : Subgroup SL5} (hUN : unitriangular 5 (ZMod 2) ≤ N)
    (h63 : (unitriangular 5 (ZMod 2)).relIndex N = 63) :
    N = flagStabilizer 5 (ZMod 2) {2} ∨ N = flagStabilizer 5 (ZMod 2) {3} := by
  set I := borelOvergroupCuts N with hI
  have hN : N = flagStabilizer 5 (ZMod 2) I := eq_flag hUN
  have hsq : ∀ {k : ℕ}, k ∈ I → (unitriangular 5 (ZMod 2)).relIndex
      (flagStabilizer 5 (ZMod 2) {k}) = 63 → N = flagStabilizer 5 (ZMod 2) {k} := by
    intro k hk hk63
    have hle : N ≤ flagStabilizer 5 (ZMod 2) {k} := by
      rw [hN]
      exact BinaryParabolic.flagStabilizer_anti (Set.singleton_subset_iff.2 hk)
    have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hUN hle
    rw [h63, hk63] at hmul
    have h1 : N.relIndex (flagStabilizer 5 (ZMod 2) {k}) = 1 := by omega
    exact le_antisymm hle (Subgroup.relIndex_eq_one.1 h1)
  by_cases h2 : 2 ∈ I
  · exact Or.inl (hsq h2 relIndex_Q2)
  by_cases h3 : 3 ∈ I
  · exact Or.inr (hsq h3 relIndex_Q3)
  exfalso
  have hsub : ∀ i ∈ I, i = 1 ∨ i = 4 := by
    intro i hi
    obtain ⟨h1, h5⟩ := cuts_bound hi
    have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd hi h2
    · exact absurd hi h3
    · exact Or.inr rfl
  by_cases h1 : 1 ∈ I <;> by_cases h4 : 4 ∈ I
  ·
    have hIe : I = {1, 4} := by
      ext i
      constructor
      · intro hi
        rcases hsub i hi with rfl | rfl <;> simp
      · intro hi
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
        rcases hi with rfl | rfl
        · exact h1
        · exact h4
    rw [hN, hIe] at h63
    exact relIndex_Q14_ne h63
  ·
    have hIe : I = {1} := by
      ext i
      constructor
      · intro hi
        rcases hsub i hi with rfl | rfl
        · rfl
        · exact absurd hi h4
      · intro hi
        rw [Set.mem_singleton_iff] at hi
        rw [hi]
        exact h1
    exact not_mem_of_orderOf_five hUN h63 (hN ▸ hIe ▸ g5a_mem) orderOf_g5a
  ·
    have hIe : I = {4} := by
      ext i
      constructor
      · intro hi
        rcases hsub i hi with rfl | rfl
        · exact absurd hi h1
        · rfl
      · intro hi
        rw [Set.mem_singleton_iff] at hi
        rw [hi]
        exact h4
    exact not_mem_of_orderOf_five hUN h63 (hN ▸ hIe ▸ g5b_mem) orderOf_g5b
  ·
    have hIe : I = ∅ := by
      ext i
      constructor
      · intro hi
        rcases hsub i hi with rfl | rfl
        · exact absurd hi h1
        · exact absurd hi h4
      · intro hi
        exact absurd hi (Set.notMem_empty i)
    have htop : N = ⊤ := by rw [hN, hIe, flagStabilizer_empty]
    have hc := card_of_relIndex hUN h63
    rw [htop, Subgroup.card_top, card_sl_five_zmod_two] at hc
    norm_num at hc

theorem q234_eq : S125Pm.q234 = flagStabilizer 5 (ZMod 2) (Set.Icc 1 4 \ {1}) := rfl

theorem normalizer_M1_le :
    Subgroup.normalizer (oTwoUpper S125Pm.q234 : Set SL5) ≤ flagStabilizer 5 (ZMod 2) {2} := by
  set A := Subgroup.normalizer (oTwoUpper S125Pm.q234 : Set SL5) with hA
  have hQA : flagStabilizer 5 (ZMod 2) {2} ≤ A := by
    rw [← S125Pm.stabK_eq]
    exact S125Pm.stabK2_le_normalizer
  have hUA : unitriangular 5 (ZMod 2) ≤ A :=
    (BinaryParabolic.unitriangular_le_flagStabilizer _).trans hQA
  have hAe := eq_flag hUA
  set K := borelOvergroupCuts A with hK
  have hKsub : ∀ i ∈ K, i = 2 := by
    intro i hi
    obtain ⟨h1, h5⟩ := cuts_bound hi
    rw [mem_cuts_iff h1 h5] at hi
    by_contra hne
    exact hi (hQA ((refl_mem_iff h1 h5).2 hne))
  by_cases h2 : 2 ∈ K
  · rw [hAe]
    exact BinaryParabolic.flagStabilizer_anti (Set.singleton_subset_iff.2 h2)
  · exfalso
    have hKe : K = ∅ := by
      ext i
      constructor
      · intro hi
        rw [hKsub i hi] at hi
        exact absurd hi h2
      · intro hi
        exact absurd hi (Set.notMem_empty i)
    have htop : A = ⊤ := by rw [hAe, hKe, flagStabilizer_empty]
    have hn : (oTwoUpper S125Pm.q234).Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hg : g ∈ A := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    have hs := (isSimpleGroup_sl_zmod_two (m := 5) (by norm_num)).1
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hn with hb | ht
    ·
      have hc : Nat.card S125Pm.q234 = 3 * 1024 := by
        have h := Subgroup.relIndex_mul_card (H := unitriangular 5 (ZMod 2)) (K := S125Pm.q234)
        have hU : unitriangular 5 (ZMod 2) ≤ S125Pm.q234 :=
          BinaryParabolic.unitriangular_le_flagStabilizer _
        rw [inf_eq_left.2 hU, S125Pm.relIndex_q234, card_U] at h
        exact h.symm
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥S125Pm.q234) 3
        (by rw [hc]; norm_num)
      have hxO : (x : SL5) ∈ oTwoUpper S125Pm.q234 :=
        mem_oTwoUpper_of_odd x.2 (by rw [Subgroup.orderOf_coe, hx]; decide)
      rw [hb, Subgroup.mem_bot] at hxO
      have : x = 1 := Subtype.ext hxO
      rw [this, orderOf_one] at hx
      omega
    · have hr : reflection 5 (ZMod 2) 2 (by norm_num) (by norm_num) ∈ S125Pm.q234 :=
        oTwoUpper_le _ (ht ▸ Subgroup.mem_top _)
      rw [q234_eq, refl_mem_iff] at hr
      exact hr (by simp)

theorem config63_U {N D : Subgroup SL5} (hc : Config63 (unitriangular 5 (ZMod 2)) N D) :
    (N = flagStabilizer 5 (ZMod 2) {2} ∧ D = flagStabilizer 5 (ZMod 2) (Set.Icc 1 4 \ {1})) ∨
      (N = flagStabilizer 5 (ZMod 2) {3} ∧ D = flagStabilizer 5 (ZMod 2) (Set.Icc 1 4 \ {4})) := by
  obtain ⟨hUD, hDN, hNc, hDc, hnot⟩ := hc
  have hUN := hUD.trans hDN
  have h63 : (unitriangular 5 (ZMod 2)).relIndex N = 63 := by
    have h := Subgroup.relIndex_mul_card (H := unitriangular 5 (ZMod 2)) (K := N)
    rw [inf_eq_left.2 hUN, hNc, card_U] at h
    omega
  have h3 : (unitriangular 5 (ZMod 2)).relIndex D = 3 := by
    have h := Subgroup.relIndex_mul_card (H := unitriangular 5 (ZMod 2)) (K := D)
    rw [inf_eq_left.2 hUD, hDc, card_U] at h
    omega
  obtain ⟨j, ⟨hj1, hj5, hDj⟩, -⟩ := (BinaryParabolic.eq_or_eq_parabolic hUD h3.le).resolve_left
    (fun h => by rw [h, Subgroup.relIndex_self] at h3; omega)
  have hrD : reflection 5 (ZMod 2) j hj1 hj5 ∈ D := by
    rw [hDj, refl_mem_iff]
    simp
  have hrN : reflection 5 (ZMod 2) j hj1 hj5 ∉ CFSG.inSubgroup CFSG.perfectResidual N := by
    intro h
    apply hnot
    rw [hDj, BinaryParabolic.parabolic_eq_closure hj1 hj5, Subgroup.closure_le]
    rintro g (hg | hg)
    · exact Subgroup.mem_sup_right hg
    · rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact Subgroup.mem_sup_left h
  rcases index63 hUN h63 with hN | hN
  · left
    refine ⟨hN, ?_⟩
    rw [hDj]
    have hj2 : j ≠ 2 := by
      intro h
      subst h
      have := hDN hrD
      rw [hN, refl_mem_iff] at this
      exact this rfl
    have hj : j = 1 := by
      by_contra hj
      apply hrN
      rw [hN]
      refine reflection_mem_perfectResidual hj1 hj5 (by simpa using hj2) ?_
      have : j = 3 ∨ j = 4 := by omega
      rcases this with rfl | rfl
      · exact Or.inl ⟨by norm_num, by simp⟩
      · exact Or.inr ⟨by norm_num, by simp⟩
    subst hj
    rfl
  · right
    refine ⟨hN, ?_⟩
    rw [hDj]
    have hj3 : j ≠ 3 := by
      intro h
      subst h
      have := hDN hrD
      rw [hN, refl_mem_iff] at this
      exact this rfl
    have hj : j = 4 := by
      by_contra hj
      apply hrN
      rw [hN]
      refine reflection_mem_perfectResidual hj1 hj5 (by simpa using hj3) ?_
      have : j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl
      · exact Or.inl ⟨by norm_num, by simp⟩
      · exact Or.inr ⟨by norm_num, by simp⟩
    subst hj
    rfl

theorem transvection_sq : ∀ a b : Fin 5, a ≠ b →
    Matrix.transvection a b (1 : ZMod 2) * Matrix.transvection a b 1 = 1 := by
  decide +kernel

theorem tv_mul_self {a b : Fin 5} (h : a ≠ b) : tv a b h * tv a b h = 1 :=
  Subtype.ext (transvection_sq a b h)

theorem tv_inv {a b : Fin 5} (h : a ≠ b) : (tv a b h)⁻¹ = tv a b h :=
  inv_eq_of_mul_eq_one_right (tv_mul_self h)

theorem conj_entry {e : SL5} (he : e ∈ unitriangular 5 (ZMod 2)) {a b : Fin 5} (hab : a < b) :
    ((tv b a hab.ne' * e * (tv b a hab.ne')⁻¹ : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) b a =
      (e : Matrix (Fin 5) (Fin 5) (ZMod 2)) a b := by
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.1 he
  rw [tv_inv]
  show ((Matrix.transvection b a (1 : ZMod 2) * (e : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
    Matrix.transvection b a 1 : Matrix (Fin 5) (Fin 5) (ZMod 2))) b a = _
  rw [Matrix.mul_transvection_apply_same, Matrix.transvection_mul_apply_same,
    Matrix.transvection_mul_apply_same, hlow b a hab, hdiag a, hdiag b]
  have : ∀ x : ZMod 2, 0 + 1 * 1 + 1 * (1 + 1 * x) = x := by decide
  exact this _

theorem tv_mem_Q2 {a b : Fin 5} (hab : a < b) (h : ¬ (a.val < 2 ∧ 2 ≤ b.val)) :
    tv b a hab.ne' ∈ flagStabilizer 5 (ZMod 2) {2} :=
  tv_mem_flagStabilizer _ fun k hk h' => by
    rw [Set.mem_singleton_iff] at hk
    subst hk
    exact h ⟨h'.1, h'.2⟩

@[expose] def cornerMat (A : Fin 2 → Fin 3 → ZMod 2) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of fun i j => if i = j then 1 else
    if h : i.val < 2 ∧ 2 ≤ j.val then A ⟨i.val, h.1⟩ ⟨j.val - 2, by omega⟩ else 0

@[expose] noncomputable def cornerSL (A : Fin 2 → Fin 3 → ZMod 2) : SL5 :=
  (if A 0 0 = 1 then tv 0 2 (by decide) else 1) * (if A 0 1 = 1 then tv 0 3 (by decide) else 1) *
    (if A 0 2 = 1 then tv 0 4 (by decide) else 1) *
    (if A 1 0 = 1 then tv 1 2 (by decide) else 1) * (if A 1 1 = 1 then tv 1 3 (by decide) else 1) *
    (if A 1 2 = 1 then tv 1 4 (by decide) else 1)

theorem cornerSL_coe : ∀ A : Fin 2 → Fin 3 → ZMod 2,
    ((cornerSL A : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = cornerMat A := by
  decide +kernel

theorem corner_center : ∀ A : Fin 2 → Fin 3 → ZMod 2,
    cornerMat A * Matrix.transvection 0 1 1 = Matrix.transvection 0 1 1 * cornerMat A →
    cornerMat A * Matrix.transvection 2 3 1 = Matrix.transvection 2 3 1 * cornerMat A →
    cornerMat A * Matrix.transvection 3 4 1 = Matrix.transvection 3 4 1 * cornerMat A →
    A = 0 ∨ A = fun i j => if i = 0 ∧ j = 2 then 1 else 0 := by
  decide +kernel

theorem cornerMat_E04 : cornerMat (fun i j => if i = 0 ∧ j = 2 then 1 else 0) =
    Matrix.transvection 0 4 (1 : ZMod 2) := by
  decide +kernel

theorem cornerMat_zero : cornerMat 0 = 1 := by
  decide +kernel

theorem conj_identities :
    Matrix.transvection (4 : Fin 5) (3 : Fin 5) (1 : ZMod 2) *
        Matrix.transvection (0 : Fin 5) (4 : Fin 5) 1 =
      Matrix.transvection (0 : Fin 5) (4 : Fin 5) 1 *
        Matrix.transvection (0 : Fin 5) (3 : Fin 5) 1 *
        Matrix.transvection (4 : Fin 5) (3 : Fin 5) 1 ∧
    Matrix.transvection (3 : Fin 5) (2 : Fin 5) (1 : ZMod 2) *
        Matrix.transvection (0 : Fin 5) (3 : Fin 5) 1 =
      Matrix.transvection (0 : Fin 5) (3 : Fin 5) 1 *
        Matrix.transvection (0 : Fin 5) (2 : Fin 5) 1 *
        Matrix.transvection (3 : Fin 5) (2 : Fin 5) 1 ∧
    Matrix.transvection (1 : Fin 5) (0 : Fin 5) (1 : ZMod 2) *
        Matrix.transvection (0 : Fin 5) (2 : Fin 5) 1 =
      Matrix.transvection (0 : Fin 5) (2 : Fin 5) 1 *
        Matrix.transvection (1 : Fin 5) (2 : Fin 5) 1 *
        Matrix.transvection (1 : Fin 5) (0 : Fin 5) 1 ∧
    Matrix.transvection (1 : Fin 5) (0 : Fin 5) (1 : ZMod 2) *
        Matrix.transvection (0 : Fin 5) (3 : Fin 5) 1 =
      Matrix.transvection (0 : Fin 5) (3 : Fin 5) 1 *
        Matrix.transvection (1 : Fin 5) (3 : Fin 5) 1 *
        Matrix.transvection (1 : Fin 5) (0 : Fin 5) 1 ∧
    Matrix.transvection (1 : Fin 5) (0 : Fin 5) (1 : ZMod 2) *
        Matrix.transvection (0 : Fin 5) (4 : Fin 5) 1 =
      Matrix.transvection (0 : Fin 5) (4 : Fin 5) 1 *
        Matrix.transvection (1 : Fin 5) (4 : Fin 5) 1 *
        Matrix.transvection (1 : Fin 5) (0 : Fin 5) 1 := by
  decide +kernel

theorem cornerMat_entry : ∀ (A : Fin 2 → Fin 3 → ZMod 2) (i : Fin 2) (j : Fin 3),
    cornerMat A ⟨i.val, by omega⟩ ⟨j.val + 2, by omega⟩ = A i j := by
  decide +kernel

theorem normal_two_Q2 {E : Subgroup SL5} (hE2 : IsPGroup 2 E)
    (hEQ : E ≤ flagStabilizer 5 (ZMod 2) {2})
    (hQE : flagStabilizer 5 (ZMod 2) {2} ≤ Subgroup.normalizer (E : Set SL5)) :
    E = ⊥ ∨ Nat.card E = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := flagStabilizer 5 (ZMod 2) {2} with hQ
  have hUQ : unitriangular 5 (ZMod 2) ≤ Q := BinaryParabolic.unitriangular_le_flagStabilizer _
  have hEU : E ≤ unitriangular 5 (ZMod 2) := by
    have hS : QuasithinUnique.IsSylowTwoOf (unitriangular 5 (ZMod 2)) Q := by
      refine ⟨hUQ, S125Pm.isPGroup_unitriangular5, ?_⟩
      show ¬ 2 ∣ (unitriangular 5 (ZMod 2)).relIndex Q
      rw [hQ, relIndex_Q2]
      decide
    have hEO : E ≤ pCoreOf 2 Q := LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hEQ hQE hE2
    exact hEO.trans (pCoreOf_two_le_of_isSylowTwoOf hS)
  have hzero : ∀ e ∈ E, ∀ a b : Fin 5, a < b → ¬ (a.val < 2 ∧ 2 ≤ b.val) →
      (e : Matrix (Fin 5) (Fin 5) (ZMod 2)) a b = 0 := by
    intro e he a b hab hcut
    have hc : tv b a hab.ne' * e * (tv b a hab.ne')⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hQE (tv_mem_Q2 hab hcut)) e).mp he
    rw [← conj_entry (hEU he) hab]
    exact (mem_unitriangular.1 (hEU hc)).1 b a hab
  have hcorner : ∀ e ∈ E, (e : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      cornerMat (fun i j => (e : Matrix (Fin 5) (Fin 5) (ZMod 2)) ⟨i.val, by omega⟩
        ⟨j.val + 2, by omega⟩) := by
    intro e he
    obtain ⟨hlow, hdiag⟩ := mem_unitriangular.1 (hEU he)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cornerMat] <;>
      first
      | exact hdiag _
      | exact hlow _ _ (by decide)
      | exact hzero e he _ _ (by decide) (by decide)
  by_cases hb : E = ⊥
  · exact Or.inl hb
  right
  have hUn : (E.subgroupOf (unitriangular 5 (ZMod 2))).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hUQ.trans hQE)
  have : Group.IsNilpotent ↥(unitriangular 5 (ZMod 2)) := S125Pm.isPGroup_unitriangular5.isNilpotent
  have hne : E.subgroupOf (unitriangular 5 (ZMod 2)) ≠ ⊥ := by
    intro h
    apply hb
    rw [← Subgroup.map_subgroupOf_eq_of_le hEU, h, Subgroup.map_bot]
  obtain ⟨⟨z, hzU⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hzE, hzc⟩ := Subgroup.mem_inf.1 ‹_ ∈ _›
  have hzE' : (z : SL5) ∈ E := hzE
  have hcomm : ∀ (a b : Fin 5) (hab : a < b), ((z : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
      Matrix.transvection a b (1 : ZMod 2) =
        Matrix.transvection a b (1 : ZMod 2) * ((z : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
    intro a b hab
    have h := Subgroup.mem_center_iff.1 hzc ⟨tv a b hab.ne, transvection_mem_unitriangular hab 1⟩
    have h' := congrArg (fun x : ↥(unitriangular 5 (ZMod 2)) =>
      ((x : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2))) h
    exact h'.symm
  have hz := hcorner (z : SL5) hzE'
  set Az := fun (i : Fin 2) (j : Fin 3) => ((z : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2))
    ⟨i.val, by omega⟩ ⟨j.val + 2, by omega⟩ with hAz
  have hc1 := hcomm 0 1 (by decide)
  have hc2 := hcomm 2 3 (by decide)
  have hc3 := hcomm 3 4 (by decide)
  rw [hz] at hc1 hc2 hc3
  rcases corner_center Az hc1 hc2 hc3 with h0 | h04
  · exfalso
    apply hz1
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    show ((z : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1
    rw [hz, h0, cornerMat_zero]
  have h04E : tv 0 4 (by decide) ∈ E := by
    have : (z : SL5) = tv 0 4 (by decide) := Subtype.ext (by
      show ((z : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = Matrix.transvection 0 4 1
      rw [hz, h04, cornerMat_E04])
    rw [← this]
    exact hzE'
  have hstep : ∀ {x y c : SL5}, x ∈ E → c ∈ Q → c * x = x * y * c → y ∈ E := by
    intro x y c hx hc h
    have h1 : c * x * c⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hQE hc) x).mp hx
    have h2 : y = x⁻¹ * (c * x * c⁻¹) := by
      rw [h]
      group
    rw [h2]
    exact E.mul_mem (E.inv_mem hx) h1
  obtain ⟨c1, c2, c3, c4, c5⟩ := conj_identities
  have hQ43 := tv_mem_Q2 (show (3 : Fin 5) < 4 by decide) (by decide)
  have hQ32 := tv_mem_Q2 (show (2 : Fin 5) < 3 by decide) (by decide)
  have hQ10 := tv_mem_Q2 (show (0 : Fin 5) < 1 by decide) (by decide)
  have h03 : tv 0 3 (by decide) ∈ E := hstep h04E hQ43 (Subtype.ext c1)
  have h02 : tv 0 2 (by decide) ∈ E := hstep h03 hQ32 (Subtype.ext c2)
  have h12 : tv 1 2 (by decide) ∈ E := hstep h02 hQ10 (Subtype.ext c3)
  have h13 : tv 1 3 (by decide) ∈ E := hstep h03 hQ10 (Subtype.ext c4)
  have h14 : tv 1 4 (by decide) ∈ E := hstep h04E hQ10 (Subtype.ext c5)
  have hcE : ∀ A, cornerSL A ∈ E := by
    intro A
    simp only [cornerSL]
    refine E.mul_mem (E.mul_mem (E.mul_mem (E.mul_mem (E.mul_mem ?_ ?_) ?_) ?_) ?_) ?_ <;>
      split_ifs <;> first | exact E.one_mem | assumption
  let φ : ↥E → (Fin 2 → Fin 3 → ZMod 2) := fun e i j =>
    ((e : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) ⟨i.val, by omega⟩ ⟨j.val + 2, by omega⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun e₁ e₂ h => ?_, fun A => ⟨⟨cornerSL A, hcE A⟩, ?_⟩⟩
    · apply Subtype.ext
      apply Subtype.ext
      rw [hcorner _ e₁.2, hcorner _ e₂.2]
      exact congrArg cornerMat h
    · funext i j
      show ((cornerSL A : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) _ _ = _
      rw [cornerSL_coe]
      exact cornerMat_entry A i j
  rw [Nat.card_eq_of_bijective φ hφ]
  simp [Nat.card_eq_fintype_card]

theorem map_graph_M4 :
    (flagStabilizer 5 (ZMod 2) (Set.Icc 1 4 \ {4})).map (BinaryParabolic.graphAut 5).toMonoidHom =
      S125Pm.q234 := by
  have h := BinaryParabolic.map_graphAut_parabolic (n := 5) (j := 4) (by norm_num) (by norm_num)
  have e1 : (5 - 1 : ℕ) = 4 := rfl
  have e2 : (5 - 4 : ℕ) = 1 := rfl
  rw [e1, e2] at h
  rw [h, q234_eq]

theorem alphaU {N D : Subgroup SL5} (hc : Config63 (unitriangular 5 (ZMod 2)) N D) :
    Subgroup.normalizer (oTwoUpper D : Set SL5) ≤ N := by
  rcases config63_U hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact normalizer_M1_le
  · set γ := BinaryParabolic.graphAut 5 with hγ
    rw [← Subgroup.map_le_map_iff_of_injective (f := γ.toMonoidHom) γ.injective,
      Subgroup.map_equiv_normalizer_eq, ← CFSG.Quasithin.oTwoUpper_map, map_graph_M4, map_graph_Q3]
    exact normalizer_M1_le

theorem betaU {N D E : Subgroup SL5} (hc : Config63 (unitriangular 5 (ZMod 2)) N D)
    (hE2 : IsPGroup 2 E) (hEN : E ≤ N) (hNE : N ≤ Subgroup.normalizer (E : Set SL5)) :
    E = ⊥ ∨ Nat.card E = 64 := by
  rcases config63_U hc with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact normal_two_Q2 hE2 hEN hNE
  · set γ := BinaryParabolic.graphAut 5 with hγ
    have h := normal_two_Q2 (E := E.map γ.toMonoidHom) (hE2.map _)
      (map_graph_Q3 ▸ Subgroup.map_mono hEN)
      (by rw [← map_graph_Q3, ← Subgroup.map_equiv_normalizer_eq]; exact Subgroup.map_mono hNE)
    rcases h with hb | h64
    · left
      rwa [Subgroup.map_eq_bot_iff_of_injective (f := γ.toMonoidHom) _ γ.injective] at hb
    · right
      rwa [Subgroup.card_map_of_injective (f := γ.toMonoidHom) γ.injective] at h64

theorem isSylowTwoOf_U : QuasithinUnique.IsSylowTwoOf (unitriangular 5 (ZMod 2)) ⊤ := by
  refine ⟨le_top, S125Pm.isPGroup_unitriangular5, ?_⟩
  show ¬ 2 ∣ (unitriangular 5 (ZMod 2)).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  have h := Subgroup.card_mul_index (unitriangular 5 (ZMod 2))
  rw [card_U, card_sl_five_zmod_two] at h
  have h9765 : (unitriangular 5 (ZMod 2)).index = 9765 := by omega
  rw [h9765]
  decide

theorem config63_map {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (f : X ≃* Y)
    {S N D : Subgroup X} (hc : Config63 S N D) :
    Config63 (S.map f.toMonoidHom) (N.map f.toMonoidHom) (D.map f.toMonoidHom) := by
  obtain ⟨hSD, hDN, hN, hD, hnot⟩ := hc
  refine ⟨Subgroup.map_mono hSD, Subgroup.map_mono hDN, ?_, ?_, fun h => hnot ?_⟩
  · rw [Subgroup.card_map_of_injective f.injective, Subgroup.card_map_of_injective f.injective, hN]
  · rw [Subgroup.card_map_of_injective f.injective, Subgroup.card_map_of_injective f.injective, hD]
  · rw [← CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective _
      f.injective, ← Subgroup.map_sup] at h
    exact (Subgroup.map_le_map_iff_of_injective f.injective).1 h

theorem exists_equiv_U {X : Type} [Group X] [Finite X] (e : X ≃* SL5) {S : Subgroup X}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ f : X ≃* SL5, S.map f.toMonoidHom = unitriangular 5 (ZMod 2) := by
  have hS' := isSylowTwoOf_top_map_of_surjective hS e.toMonoidHom e.surjective
  obtain ⟨g, hg⟩ :=
    CFSG.QuasithinUnique.Vol2Native.A312L.exists_conj_of_isSylowTwoOf hS' isSylowTwoOf_U
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  rw [← hg, Subgroup.map_map]
  rfl

theorem kg125AlphaL52 :
    ∀ (X : Type) [Group X] [Finite X],
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
      ∀ S N D : Subgroup X, QuasithinUnique.IsSylowTwoOf S ⊤ → Config63 S N D →
        Subgroup.normalizer (oTwoUpper D : Set X) ≤ N := by
  intro X _ _ ⟨e⟩ S N D hS hc
  obtain ⟨f, hf⟩ := exists_equiv_U e hS
  have hcf := config63_map f hc
  rw [hf] at hcf
  have h := alphaU hcf
  rw [CFSG.Quasithin.oTwoUpper_map, ← Subgroup.map_equiv_normalizer_eq] at h
  exact (Subgroup.map_le_map_iff_of_injective f.injective).1 h

theorem kg125BetaL52 :
    ∀ (X : Type) [Group X] [Finite X],
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
      ∀ S N D E : Subgroup X, QuasithinUnique.IsSylowTwoOf S ⊤ → Config63 S N D →
        E ≤ pCoreOf 2 N → N ≤ Subgroup.normalizer (E : Set X) → E = ⊥ ∨ Nat.card E = 64 := by
  intro X _ _ ⟨e⟩ S N D E hS hc hEO hNE
  obtain ⟨f, hf⟩ := exists_equiv_U e hS
  have hcf := config63_map f hc
  rw [hf] at hcf
  have hE2 : IsPGroup 2 E :=
    (LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le hEO
  have hEN : E ≤ N := hEO.trans (LieType.BorelTits.pCoreOf_le 2 N)
  rcases betaU hcf (hE2.map _) (Subgroup.map_mono hEN)
      (by rw [← Subgroup.map_equiv_normalizer_eq]; exact Subgroup.map_mono hNE) with hb | h64
  · left
    rwa [Subgroup.map_eq_bot_iff_of_injective _ f.injective] at hb
  · right
    rwa [Subgroup.card_map_of_injective f.injective] at h64

end CFSG.Quasithin.H13.S125KG.L52
