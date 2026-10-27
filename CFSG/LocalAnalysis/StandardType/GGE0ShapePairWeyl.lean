module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeCheckSound
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc
public import CFSG.RankThree.Chevalley.SteinbergBID4A2CharStab

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private noncomputable def rootDiagUnitHom (τ : Tag) (K : Type) [Field K] :
    (Fin τ.rank → Kˣ) →* ModGL τ K where
  toFun := rootDiagUnit τ
  map_one' := rootDiagUnit_one
  map_mul' a b := rootDiagUnit_mul a b

private theorem rootChar_single {τ : Tag} {K : Type} [Field K]
    (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) : rootChar a (Pi.single i 1) = a i := by
  have h := rootChar_nsmul_single a i 1
  rwa [one_smul, pow_one] at h

private theorem rootChar_zsmul_single {τ : Tag} {K : Type} [Field K]
    (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) (k : ℤ) :
    rootChar a (k • (Pi.single i 1 : Fin τ.rank → ℤ)) = a i ^ k := by
  simp only [rootChar, Pi.smul_apply, smul_eq_mul]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    have hz : ((Pi.single i (1 : ℤ) : Fin τ.rank → ℤ)) j = 0 :=
      Pi.single_eq_of_ne (M := fun _ : Fin τ.rank => ℤ) hji (1 : ℤ)
    rw [hz, mul_zero, zpow_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

private theorem cube_roots_eq {K : Type} [Field K] (ω : Kˣ)
    (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (y : Kˣ) (hy : y ^ 3 = 1) :
    y = 1 ∨ y = ω ∨ y = ω ^ 2 := by
  have h1 : (ω : K) ^ 3 = 1 := by simpa using congrArg Units.val hω
  have h2 : (ω : K) ≠ 1 := fun h => hω1 (Units.ext h)
  have hsum : ((1 : K) + ω + ω ^ 2) = 0 := by
    have : ((ω : K) - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination h1
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h2)
  have hy' : (y : K) ^ 3 = 1 := by simpa using congrArg Units.val hy
  have h3 : ((y : K) - 1) * ((y : K) - ω) * ((y : K) - ω ^ 2) = 0 := by
    linear_combination hy' + ((y : K) - (y : K) ^ 2) * hsum + ((y : K) - 1) * h1
  rcases mul_eq_zero.1 h3 with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (Units.ext (sub_eq_zero.1 h))
    · exact Or.inr (Or.inl (Units.ext (sub_eq_zero.1 h)))
  · exact Or.inr (Or.inr (Units.ext (by simpa using sub_eq_zero.1 h)))

private theorem rootChar_eq_pow_of_ker_eq {τ : Tag} {K : Type} [Field K]
    (a b : Fin τ.rank → Kˣ) (ha : ∀ i, a i ^ 3 = 1) (hb : ∀ i, b i ^ 3 = 1)
    (hker : ∀ v : Fin τ.rank → ℤ, rootChar a v = 1 ↔ rootChar b v = 1) :
    ∃ c : ℤ, ∀ i, b i = (a i) ^ c := by
  by_cases hall : ∀ i, a i = 1
  · refine ⟨0, fun i => ?_⟩
    have h1 : rootChar a (Pi.single i 1) = 1 := by rw [rootChar_single, hall i]
    have h2 : rootChar b (Pi.single i 1) = 1 := (hker _).1 h1
    rw [rootChar_single] at h2
    rw [hall i, h2, zpow_zero]
  · push Not at hall
    obtain ⟨i0, hi0⟩ := hall
    have hω : (a i0) ^ 3 = 1 := ha i0
    obtain ⟨c, hc⟩ : ∃ c : ℤ, b i0 = (a i0) ^ c := by
      rcases cube_roots_eq (a i0) hω hi0 (b i0) (hb i0) with h | h | h
      · exact ⟨0, by rw [h, zpow_zero]⟩
      · exact ⟨1, by rw [h, zpow_one]⟩
      · exact ⟨2, by rw [h, zpow_ofNat]⟩
    refine ⟨c, fun i => ?_⟩
    obtain ⟨m, hm⟩ : ∃ m : ℤ, a i = (a i0) ^ m := by
      rcases cube_roots_eq (a i0) hω hi0 (a i) (ha i) with h | h | h
      · exact ⟨0, by rw [h, zpow_zero]⟩
      · exact ⟨1, by rw [h, zpow_one]⟩
      · exact ⟨2, by rw [h, zpow_ofNat]⟩
    have hv : rootChar a (Pi.single i 1 - m • (Pi.single i0 1 : Fin τ.rank → ℤ)) = 1 := by
      rw [rootChar_sub, rootChar_single, rootChar_zsmul_single, hm, mul_inv_cancel]
    have hv' : rootChar b (Pi.single i 1 - m • (Pi.single i0 1 : Fin τ.rank → ℤ)) = 1 :=
      (hker _).1 hv
    rw [rootChar_sub, rootChar_single, rootChar_zsmul_single, hc] at hv'
    have hbi : b i = ((a i0) ^ c) ^ m := by rwa [mul_inv_eq_one] at hv'
    rw [hbi, hm, ← zpow_mul, ← zpow_mul, mul_comm c m]

private theorem triPairing_add_left {τ : Tag} (b b' : Fin τ.rank → ZMod 3)
    (v : Fin τ.rank → ℤ) :
    triPairing (b + b') v = triPairing b v + triPairing b' v := by
  simp only [triPairing, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem triPairing_smul {τ : Tag} (c : ZMod 3) (b : Fin τ.rank → ZMod 3)
    (v : Fin τ.rank → ℤ) : triPairing (c • b) v = c * triPairing b v := by
  simp only [triPairing, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem triPairing_zero_left {τ : Tag} (v : Fin τ.rank → ℤ) :
    triPairing (0 : Fin τ.rank → ZMod 3) v = 0 := by
  simp [triPairing]

private theorem triChar_zero_apply {τ : Tag} (v : Fin τ.rank → ℤ) :
    triChar (0 : Fin τ.rank → ZMod 3) (Multiplicative.ofAdd v) = 1 := by
  rw [triChar_apply, triPairing_zero_left]
  rfl

private theorem triPairing_eq_zero_of_rootCharHom3 {τ : Tag} {K : Type} [Field K]
    {a : Fin τ.rank → Kˣ} {b : Fin τ.rank → ZMod 3}
    (hb : ∀ x, rootCharHom3 a x = 1 ↔ triChar b x = 1) (v : Fin τ.rank → ℤ) :
    rootChar a v = 1 ↔ triPairing b v = 0 := by
  have h := hb (Multiplicative.ofAdd v)
  change rootChar a v = 1 ↔ triChar b (Multiplicative.ofAdd v) = 1 at h
  rwa [triChar_apply, Z3.ofAdd_eq_one] at h

private theorem eq_one_of_triChar_zero {τ : Tag} {K : Type} [Field K]
    {a : Fin τ.rank → Kˣ} {b : Fin τ.rank → ZMod 3}
    (hb : ∀ x, rootCharHom3 a x = 1 ↔ triChar b x = 1) (hbz : b = 0) : a = 1 := by
  funext j
  have h : rootChar a (Pi.single j 1) = 1 := by
    have h' : triChar b (Multiplicative.ofAdd (Pi.single j 1)) = 1 := by
      rw [hbz]
      exact triChar_zero_apply (Pi.single j 1)
    have h'' := (hb (Multiplicative.ofAdd (Pi.single j 1))).2 h'
    change rootChar a (Pi.single j 1) = 1 at h''
    exact h''
  rw [← rootChar_single a j]
  simpa using h

private theorem familyKernel_eq_pair {L : Type} [Field L]
    (a : Fin 2 → Fin Tag.E6.rank → Lˣ) (b : Fin 2 → Fin Tag.E6.rank → ZMod 3)
    (hb : ∀ i x, rootCharHom3 (a i) x = 1 ↔ triChar (b i) x = 1) :
    familyKernel a =
      {γ | IsRoot .E6 γ ∧ triPairing (b 0) γ = 0 ∧ triPairing (b 1) γ = 0} := by
  ext γ
  simp only [familyKernel, Set.mem_setOf_eq]
  rw [Fin.forall_fin_two]
  refine and_congr_right fun _ => and_congr ?_ ?_
  · exact triPairing_eq_zero_of_rootCharHom3 (hb 0) γ
  · exact triPairing_eq_zero_of_rootCharHom3 (hb 1) γ

private theorem familyKernel_unit_eq_rootCharKernel {L : Type} [Field L]
    (a : Fin Tag.E6.rank → Lˣ) :
    familyKernel (fun _ : Unit => a) = rootCharKernel a := by
  ext γ
  simp only [familyKernel, rootCharKernel, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hroot, hf⟩; exact ⟨hroot, hf ()⟩
  · rintro ⟨hroot, hf⟩; exact ⟨hroot, fun _ => hf⟩

private theorem closure_rootReflection_familyKernel_unit {L : Type} [Field L]
    (a : Fin Tag.E6.rank → Lˣ) :
    Subgroup.closure {s | ∃ α ∈ familyKernel (fun _ : Unit => a), s = rootReflection α} =
      Subgroup.closure ((fun α => rootReflection α) '' rootCharKernel a) := by
  rw [familyKernel_unit_eq_rootCharKernel a]
  congr 1
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_image]
  exact ⟨fun ⟨α, hα, hs⟩ => ⟨α, hα, hs.symm⟩, fun ⟨α, hα, hs⟩ => ⟨α, hα, hs.symm⟩⟩

private theorem range_fin_two' {α : Type} (f : Fin 2 → α) : Set.range f = {f 0, f 1} := by
  ext z
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

private theorem not_card_nine_of_le_zpowers {G : Type} [Group G] {f : Fin 2 → G} {x : G}
    (hx : x ∈ Subgroup.closure (Set.range f))
    (hle : Subgroup.closure (Set.range f) ≤ Subgroup.zpowers x) (hx3 : x ^ 3 = 1) :
    Nat.card (Subgroup.closure (Set.range f)) ≠ 9 := by
  intro h9
  have hEq : Subgroup.closure (Set.range f) = Subgroup.zpowers x :=
    le_antisymm hle (Subgroup.zpowers_le.2 hx)
  rw [hEq, Nat.card_zpowers] at h9
  have hdvd : orderOf x ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 hx3
  have hle3 : orderOf x ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem pairWeylGood_of_large_kernel
    {L : Type} [Field L] (a : Fin 2 → Fin Tag.E6.rank → Lˣ)
    (h3 : ∀ i j, a i j ^ 3 = 1)
    (hcard : Nat.card (Subgroup.closure (Set.range fun i => rootDiagUnit .E6 (a i))) = 9)
    (hlarge : 6 < (familyKernel a).ncard) : PairWeylGood a := by
  choose χ hχ using fun i =>
    exists_triChar_ker_eq (rootCharHom3 (a i)) (rootCharHom3_pow_three (a i) (h3 i))
  let b : Fin 2 → Fin Tag.E6.rank → ZMod 3 := fun i j =>
    Z3.toAdd (χ i (Multiplicative.ofAdd (Pi.single j 1)))
  have hb : ∀ i x, rootCharHom3 (a i) x = 1 ↔ triChar (b i) x = 1 := by
    intro i x
    rw [show triChar (b i) = χ i from (eq_triChar (χ i)).symm]
    exact hχ i x
  set f : Fin 2 → ModGL .E6 L := fun i => rootDiagUnit .E6 (a i) with hf
  have hcardf : Nat.card (Subgroup.closure (Set.range f)) = 9 := by rw [hf]; exact hcard
  have hf3 : ∀ i, f i ^ 3 = 1 := by
    intro i
    rw [hf]
    change (rootDiagUnitHom .E6 L (a i)) ^ 3 = 1
    have ha3 : a i ^ 3 = 1 := by
      funext j
      rw [Pi.pow_apply]
      exact h3 i j
    rw [← map_pow (rootDiagUnitHom .E6 L) (a i) 3, ha3, map_one]
  have hind : ∀ c0 c1 : ZMod 3, c0 • b 0 + c1 • b 1 = 0 → c0 = 0 ∧ c1 = 0 := by
    intro c0 c1 hrel
    by_contra hne
    by_cases hc0 : c0 = 0
    · have hc1 : c1 ≠ 0 := fun hc => hne ⟨hc0, hc⟩
      have hb1z : b 1 = 0 := by
        funext j
        have h := congrFun hrel j
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc0, zero_mul, zero_add] at h
        exact (mul_eq_zero.mp h).resolve_left hc1
      have ha1 : a 1 = 1 := eq_one_of_triChar_zero (hb 1) hb1z
      have hf1 : f 1 = 1 := by
        rw [hf]
        change rootDiagUnit .E6 (a 1) = 1
        rw [ha1, rootDiagUnit_one]
      have hle : Subgroup.closure (Set.range f) ≤ Subgroup.zpowers (f 0) := by
        rw [range_fin_two']
        refine (Subgroup.closure_le _).2 ?_
        rintro z (rfl | rfl)
        · exact Subgroup.mem_zpowers (f 0)
        · rw [hf1]; exact Subgroup.mem_zpowers_iff.2 ⟨0, by simp⟩
      have hx : f 0 ∈ Subgroup.closure (Set.range f) := Subgroup.subset_closure ⟨0, rfl⟩
      exact (not_card_nine_of_le_zpowers hx hle (hf3 0)) hcardf
    · by_cases hc1 : c1 = 0
      · have hc0' : c0 ≠ 0 := fun hc => hne ⟨hc, hc1⟩
        have hb0z : b 0 = 0 := by
          funext j
          have h := congrFun hrel j
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc1, zero_mul, add_zero] at h
          exact (mul_eq_zero.mp h).resolve_left hc0'
        have ha0 : a 0 = 1 := eq_one_of_triChar_zero (hb 0) hb0z
        have hf0 : f 0 = 1 := by
          rw [hf]
          change rootDiagUnit .E6 (a 0) = 1
          rw [ha0, rootDiagUnit_one]
        have hle : Subgroup.closure (Set.range f) ≤ Subgroup.zpowers (f 1) := by
          rw [range_fin_two']
          refine (Subgroup.closure_le _).2 ?_
          rintro z (rfl | rfl)
          · rw [hf0]; exact Subgroup.mem_zpowers_iff.2 ⟨0, by simp⟩
          · exact Subgroup.mem_zpowers (f 1)
        have hx : f 1 ∈ Subgroup.closure (Set.range f) := Subgroup.subset_closure ⟨1, rfl⟩
        exact (not_card_nine_of_le_zpowers hx hle (hf3 1)) hcardf
      · have hker01 : ∀ v : Fin Tag.E6.rank → ℤ,
            rootChar (a 0) v = 1 ↔ rootChar (a 1) v = 1 := by
          intro v
          have hzero : c0 * triPairing (b 0) v + c1 * triPairing (b 1) v = 0 := by
            have h := congrArg (fun w => triPairing w v) hrel
            simpa only [triPairing_add_left, triPairing_smul, triPairing_zero_left] using h
          have ht : triPairing (b 0) v = 0 ↔ triPairing (b 1) v = 0 := by
            constructor
            · intro h
              have h' := hzero
              rw [h, mul_zero, zero_add] at h'
              exact (mul_eq_zero.mp h').resolve_left hc1
            · intro h
              have h' := hzero
              rw [h, mul_zero, add_zero] at h'
              exact (mul_eq_zero.mp h').resolve_left hc0
          rw [triPairing_eq_zero_of_rootCharHom3 (hb 0) v,
            triPairing_eq_zero_of_rootCharHom3 (hb 1) v]
          exact ht
        obtain ⟨c, hc⟩ := rootChar_eq_pow_of_ker_eq (a 0) (a 1) (h3 0) (h3 1) hker01
        have ha1 : a 1 = (a 0) ^ c := by
          funext j
          exact hc j
        have hf1 : f 1 = (f 0) ^ c := by
          rw [hf]
          change rootDiagUnitHom .E6 L (a 1) = (rootDiagUnitHom .E6 L (a 0)) ^ c
          rw [ha1, ← map_zpow (rootDiagUnitHom .E6 L)]
        have hle : Subgroup.closure (Set.range f) ≤ Subgroup.zpowers (f 0) := by
          rw [range_fin_two']
          refine (Subgroup.closure_le _).2 ?_
          rintro z (rfl | rfl)
          · exact Subgroup.mem_zpowers (f 0)
          · rw [hf1]; exact Subgroup.mem_zpowers_iff.2 ⟨c, rfl⟩
        have hx : f 0 ∈ Subgroup.closure (Set.range f) := Subgroup.subset_closure ⟨0, rfl⟩
        exact (not_card_nine_of_le_zpowers hx hle (hf3 0)) hcardf
  have hlarge' : 6 < {γ | IsRoot .E6 γ ∧ triPairing (b 0) γ = 0 ∧
      triPairing (b 1) γ = 0}.ncard := by
    rw [← familyKernel_eq_pair a b hb]
    exact hlarge
  intro w hw i
  have hstab : ∀ j : Fin 2, w ∈ charStabilizer (triChar (b j)) := by
    intro j
    have h1 : w ∈ rootCharStabilizerSubgroup (a j) :=
      mem_rootCharStabilizerSubgroup.2 (hw j)
    have hS : rootCharStabilizerSubgroup (a j) = charStabilizer (rootCharHom3 (a j)) :=
      Subgroup.ext fun u => Iff.rfl
    rw [hS] at h1
    rwa [charStabilizer_congr_ker (hb j)] at h1
  have hshift := shapeCheck_sound (b 0) (b 1) hind hlarge' (hstab 0) (hstab 1)
  have htri : triPairing (b i) (e6Shift w) = 0 := by
    fin_cases i
    · exact hshift.1
    · exact hshift.2
  have h1 : rootChar (a i) (e6Shift w) = 1 :=
    (triPairing_eq_zero_of_rootCharHom3 (hb i) (e6Shift w)).2 htri
  have hkr := mem_kernelReflectionGroup_of_e6Shift (a i) (h3 i)
    (mem_rootCharStabilizerSubgroup.2 (hw i)) h1
  rw [CFSG.RankThree.Chevalley.kernelReflectionGroup_eq_closure_rootReflection (a i)] at hkr
  rw [closure_rootReflection_familyKernel_unit (a i)]
  exact hkr

end CFSG.StandardType
