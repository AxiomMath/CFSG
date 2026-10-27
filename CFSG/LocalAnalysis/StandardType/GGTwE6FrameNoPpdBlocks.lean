module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusActPow
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeSc
public import CFSG.LieType.Chevalley.C2E6RootOperators
public import CFSG.LieType.Chevalley.SignKernelPositiveRepresentatives
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages

public section

namespace CFSG.StandardType.TwE6FrameNoPpd

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b
  CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Steinberg.Adjoint

private abbrev V := Fin Tag.E6.rank → ℤ

private def f12 : V := ![-4, -3, -5, -6, -4, -2]

private def B10 : List V :=
  [![0,-1,-1,-2,-2,-2], ![0,-1,-1,-2,-2,0], ![0,-1,-1,-2,0,0], ![0,-1,-1,0,0,0],
   ![0,-1,1,0,0,0], ![0,1,-1,0,0,0], ![0,1,1,0,0,0], ![0,1,1,2,0,0],
   ![0,1,1,2,2,0], ![0,1,1,2,2,2]]

private def B12 : List V := f12 :: B10

private def B3 : List V :=
  [![-4,-3,-5,-6,-4,-2], ![-1,-3,-5,-6,-4,-2], ![-1,-3,-2,-6,-4,-2],
   ![-1,-3,-2,-3,-4,-2], ![-1,-3,-2,-3,-1,-2], ![-1,-3,-2,-3,-1,1]]

private def B4a : List V := [![-1,-2,-2,-3,-2,-1], ![1,2,2,3,2,1]]

private def B4b : List V :=
  [![-1,0,-1,-1,-1,-1], ![-1,0,-1,-1,-1,0], ![-1,0,-1,-1,0,0],
   ![-1,0,-1,0,0,0], ![-1,0,0,0,0,0]]

private def B45 : List V := B4a ++ B4b

private def f6 : V := ![-2,0,-4,-3,-2,-1]

private def B6a : List V := [f6]

private def B6b : List V :=
  [![-1,-1,-2,-3,-2,-1], ![-1,-1,-2,-2,-2,-1], ![-1,-1,-2,-2,-1,-1],
   ![-1,-1,-2,-2,-1,0], ![0,0,-1,-1,-1,-1], ![0,0,-1,-1,-1,0],
   ![0,0,-1,-1,0,0], ![0,0,-1,0,0,0]]

private def B6 : List V := B6a ++ B6b

private def B7a : List V :=
  [![-1,-2,-2,-3,-2,-1], ![-1,-1,-2,-3,-2,-1], ![0,-1,0,0,0,0],
   ![0,1,0,0,0,0], ![1,1,2,3,2,1], ![1,2,2,3,2,1]]

private def B7b : List V :=
  [![-1,0,-1,0,0,0], ![-1,0,0,0,0,0], ![0,0,-1,0,0,0],
   ![0,0,1,0,0,0], ![1,0,0,0,0,0], ![1,0,1,0,0,0]]

private def B7c : List V :=
  [![0,0,0,0,-1,-1], ![0,0,0,0,-1,0], ![0,0,0,0,0,-1],
   ![0,0,0,0,0,1], ![0,0,0,0,1,0], ![0,0,0,0,1,1]]

private def B7 : List V := B7a ++ B7b ++ B7c

private def cf12 : Fin Tag.E6.rank → List ℤ :=
  ![[-16,16,16,16,16,-16,0,0,0,0,0], [0,0,0,0,-32,-32,0,0,0,0,0],
    [0,0,0,0,-32,32,0,0,0,0,0], [0,0,0,-32,32,0,0,0,0,0,0],
    [0,0,-32,32,0,0,0,0,0,0,0], [0,-32,32,0,0,0,0,0,0,0,0]]

private def cf3 : Fin Tag.E6.rank → List ℤ :=
  ![[-243,243,0,0,0,0], [81,81,81,-162,-162,-162], [0,-243,243,0,0,0],
    [0,0,-243,243,0,0], [0,0,0,-243,243,0], [0,0,0,0,-243,243]]

private def cf45 : Fin Tag.E6.rank → List ℤ :=
  ![[0,0,0,0,0,0,-2], [-1,0,1,1,1,-1,-1], [0,0,0,0,0,-2,2],
    [0,0,0,0,-2,2,0], [0,0,0,-2,2,0,0], [0,0,-2,2,0,0,0]]

private def cf6 : Fin Tag.E6.rank → List ℤ :=
  ![[-1,-1,-1,-1,3,4,0,0,0], [1,1,-1,-1,-1,0,0,0,0], [0,2,0,0,-2,-2,0,0,0],
    [0,-2,2,0,0,0,0,0,0], [0,0,-2,2,0,0,0,0,0], [0,0,0,-2,2,0,0,0,0]]

private def cf7 : Fin Tag.E6.rank → List ℤ :=
  ![[0,0,0,0,0,0,0,-3,0,0,0,0,0,0,0,0,0,0],
    [-3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    [0,0,0,0,0,0,-3,3,0,0,0,0,0,0,0,0,0,0],
    [1,-2,0,0,0,0,2,-1,0,0,0,0,1,1,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,0,-3,0,0,0,0],
    [0,0,0,0,0,0,0,0,0,0,0,0,-3,3,0,0,0,0]]

private theorem stable12f (ρ : ℕ) (hρ : ρ = 1 ∨ ρ = 2) :
    ∀ (k : Fin 72), triPairing (vec3 (τ := .E6) (e6ThreeReps.getD ρ [])) (e6Root k) = 0 →
      ∀ v ∈ [f12], v - corootPair (e6Root k) v • e6Root k ∈ [f12] := by
  rcases hρ with rfl | rfl <;> decide +kernel

private theorem stable12b (ρ : ℕ) (hρ : ρ = 1 ∨ ρ = 2) :
    ∀ (k : Fin 72), triPairing (vec3 (τ := .E6) (e6ThreeReps.getD ρ [])) (e6Root k) = 0 →
      ∀ v ∈ B10, v - corootPair (e6Root k) v • e6Root k ∈ B10 := by
  rcases hρ with rfl | rfl <;> decide +kernel

private theorem stable3 :
    ∀ (k : Fin 72), triPairing (vec3 (τ := .E6) (e6ThreeReps.getD 3 [])) (e6Root k) = 0 →
      ∀ v ∈ B3, v - corootPair (e6Root k) v • e6Root k ∈ B3 := by
  decide +kernel

private theorem stable45a (ρ : ℕ) (hρ : ρ = 4 ∨ ρ = 5) :
    ∀ (k : Fin 72), triPairing (vec3 (τ := .E6) (e6ThreeReps.getD ρ [])) (e6Root k) = 0 →
      ∀ v ∈ B4a, v - corootPair (e6Root k) v • e6Root k ∈ B4a := by
  rcases hρ with rfl | rfl <;> decide +kernel

private theorem stable45b (ρ : ℕ) (hρ : ρ = 4 ∨ ρ = 5) :
    ∀ (k : Fin 72), triPairing (vec3 (τ := .E6) (e6ThreeReps.getD ρ [])) (e6Root k) = 0 →
      ∀ v ∈ B4b, v - corootPair (e6Root k) v • e6Root k ∈ B4b := by
  rcases hρ with rfl | rfl <;> decide +kernel

private theorem stable6a :
    ∀ (k : Fin 72), triPairing (vec3 (τ := .E6) (e6ThreeReps.getD 6 [])) (e6Root k) = 0 →
      ∀ v ∈ B6a, v - corootPair (e6Root k) v • e6Root k ∈ B6a := by
  decide +kernel

private theorem stable6b :
    ∀ (k : Fin 72), triPairing (vec3 (τ := .E6) (e6ThreeReps.getD 6 [])) (e6Root k) = 0 →
      ∀ v ∈ B6b, v - corootPair (e6Root k) v • e6Root k ∈ B6b := by
  decide +kernel

private theorem stable7a :
    ∀ (k : Fin 72), triPairing (vec3 (τ := .E6) (e6ThreeReps.getD 7 [])) (e6Root k) = 0 →
      ∀ v ∈ B7a, v - corootPair (e6Root k) v • e6Root k ∈ B7a := by
  decide +kernel

private theorem stable7b :
    ∀ (k : Fin 72), triPairing (vec3 (τ := .E6) (e6ThreeReps.getD 7 [])) (e6Root k) = 0 →
      ∀ v ∈ B7b, v - corootPair (e6Root k) v • e6Root k ∈ B7b := by
  decide +kernel

private theorem stable7c :
    ∀ (k : Fin 72), triPairing (vec3 (τ := .E6) (e6ThreeReps.getD 7 [])) (e6Root k) = 0 →
      ∀ v ∈ B7c, v - corootPair (e6Root k) v • e6Root k ∈ B7c := by
  decide +kernel

private theorem len12 (j : Fin Tag.E6.rank) : (cf12 j).length = B12.length := by
  fin_cases j <;> decide

private theorem len3 (j : Fin Tag.E6.rank) : (cf3 j).length = B3.length := by
  fin_cases j <;> decide

private theorem len45 (j : Fin Tag.E6.rank) : (cf45 j).length = B45.length := by
  fin_cases j <;> decide

private theorem len6 (j : Fin Tag.E6.rank) : (cf6 j).length = B6.length := by
  fin_cases j <;> decide

private theorem len7 (j : Fin Tag.E6.rank) : (cf7 j).length = B7.length := by
  fin_cases j <;> decide

private theorem comb12 (j : Fin Tag.E6.rank) :
    (64 : ℤ) • (Pi.single j 1) = (B12.zipWith (fun v k => k • v) (cf12 j)).sum := by
  fin_cases j <;> decide +kernel

private theorem comb3 (j : Fin Tag.E6.rank) :
    (729 : ℤ) • (Pi.single j 1) = (B3.zipWith (fun v k => k • v) (cf3 j)).sum := by
  fin_cases j <;> decide +kernel

private theorem comb45 (j : Fin Tag.E6.rank) :
    (2 : ℤ) • (Pi.single j 1) = (B45.zipWith (fun v k => k • v) (cf45 j)).sum := by
  fin_cases j <;> decide +kernel

private theorem comb6 (j : Fin Tag.E6.rank) :
    (2 : ℤ) • (Pi.single j 1) = (B6.zipWith (fun v k => k • v) (cf6 j)).sum := by
  fin_cases j <;> decide +kernel

private theorem comb7 (j : Fin Tag.E6.rank) :
    (3 : ℤ) • (Pi.single j 1) = (B7.zipWith (fun v k => k • v) (cf7 j)).sum := by
  fin_cases j <;> decide +kernel

private theorem mapsTo_of_check
    {b : Fin Tag.E6.rank → ZMod 3} {B : List V}
    (hcheck : ∀ (k : Fin 72), triPairing b (e6Root k) = 0 →
      ∀ v ∈ B, v - corootPair (e6Root k) v • e6Root k ∈ B)
    {u : WeylGroup Tag.E6} (hu : u ∈ kernelWeylGroup (triChar b)) :
    ∀ v ∈ B, u • v ∈ B := by
  have key : ∀ u : WeylGroup Tag.E6, u ∈ kernelWeylGroup (triChar b) →
      (∀ v ∈ B, u • v ∈ B) ∧ (∀ v ∈ B, u⁻¹ • v ∈ B) := by
    intro u hu
    rw [kernelWeylGroup_eq_closure] at hu
    refine Subgroup.closure_induction (p := fun u _ =>
      (∀ v ∈ B, u • v ∈ B) ∧ (∀ v ∈ B, u⁻¹ • v ∈ B)) ?_ ?_ ?_ ?_ hu
    · rintro x ⟨α, hα, rfl⟩
      obtain ⟨hroot, hpair⟩ := mem_kernelRoots_triChar.1 hα
      obtain ⟨k, hk⟩ := exists_e6Root_eq hroot
      subst hk
      have hb : triPairing b (e6Root k) = 0 := hpair
      have hmem : ∀ v ∈ B, v - corootPair (e6Root k) v • e6Root k ∈ B := hcheck k hb
      exact ⟨fun v hv => by
          show rootReflection (e6Root k) • v ∈ B
          rw [rootReflection_smul (isRoot_e6Root k)]
          exact hmem v hv,
        fun v hv => by
          show (rootReflection (e6Root k))⁻¹ • v ∈ B
          rw [rootReflection_inv (isRoot_e6Root k), rootReflection_smul (isRoot_e6Root k)]
          exact hmem v hv⟩
    · exact ⟨fun v hv => by simpa using hv, fun v hv => by simpa using hv⟩
    · intro x y _ _ hx hy
      exact ⟨fun v hv => by rw [mul_smul]; exact hx.1 _ (hy.1 v hv),
        fun v hv => by rw [mul_inv_rev, mul_smul]; exact hy.2 _ (hx.2 v hv)⟩
    · intro x _ hx
      exact ⟨fun v hv => by simpa using hx.2 v hv, fun v hv => by simpa using hx.1 v hv⟩
  exact (key u hu).1

private theorem rootChar_zipWith_sum {K : Type} [Field K] {c : Fin Tag.E6.rank → Kˣ} :
    ∀ (B : List V) (cs : List ℤ), cs.length = B.length →
      (∀ v ∈ B, rootChar c v = 1) →
      rootChar c ((B.zipWith (fun v k => k • v) cs).sum) = 1
  | [], [], _, _ => by simp [rootChar_zero]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | v :: B, k :: cs, h, hB => by
      rw [List.zipWith_cons_cons, List.sum_cons, rootChar_add, rootChar_zsmul,
        hB v (by simp), one_zpow, one_mul]
      exact rootChar_zipWith_sum B cs (by simpa using h) (fun w hw => hB w (by simp [hw]))

private theorem pow_eq_one_of_comb {K : Type} [Field K] {c : Fin Tag.E6.rank → Kˣ}
    {B : List V} {N : ℕ} {j : Fin Tag.E6.rank} {cs : List ℤ}
    (hlen : cs.length = B.length)
    (hcomb : (N : ℤ) • (Pi.single j 1) = (B.zipWith (fun v k => k • v) cs).sum)
    (hB : ∀ v ∈ B, rootChar c v = 1) : c j ^ N = 1 := by
  have h1 : rootChar c ((N : ℤ) • (Pi.single j 1)) = 1 := by
    rw [hcomb]
    exact rootChar_zipWith_sum B cs hlen hB
  rwa [rootChar_zsmul, rootChar_single, zpow_natCast] at h1

private theorem exists_pow_smul_eq_self_of_mapsTo
    {G X : Type*} [Group G] [MulAction G X]
    {u : G} {B : Finset X} {lam : X} (hB : ∀ v ∈ B, u • v ∈ B) (hlam : lam ∈ B) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ B.card ∧ (u ^ l) • lam = lam := by
  classical
  have hiter : ∀ k : ℕ, (u ^ k) • lam ∈ B := by
    intro k
    induction k with
    | zero => simpa using hlam
    | succ k ih => rw [pow_succ', mul_smul]; exact hB _ ih
  have hmaps : Set.MapsTo (fun k : ℕ => (u ^ k) • lam) ↑(Finset.range (B.card + 1)) ↑B :=
    fun k _ => hiter k
  have hcard : B.card < (Finset.range (B.card + 1)).card := by
    rw [Finset.card_range]; omega
  obtain ⟨i, hi, j, hj, hij, hEq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [Finset.mem_range] at hi hj
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨j - i, by omega, by omega, ?_⟩
    have hji : u ^ j = u ^ i * u ^ (j - i) := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [hji, mul_smul] at hEq
    have := congrArg (fun x => (u ^ i)⁻¹ • x) hEq
    simpa using this.symm
  · refine ⟨i - j, by omega, by omega, ?_⟩
    have hij' : u ^ i = u ^ j * u ^ (i - j) := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [hij', mul_smul] at hEq
    have := congrArg (fun x => (u ^ j)⁻¹ • x) hEq
    simpa using this

private theorem dvd_of_pow_smul_eq_self
    {G X : Type*} [Group G] [MulAction G X]
    {u : G} {lam : X} {l : ℕ} (hl1 : 1 ≤ l) (hfix : (u ^ l) • lam = lam)
    (hmin : ∀ k : ℕ, 0 < k → k < l → (u ^ k) • lam ≠ lam) {d : ℕ}
    (hd : (u ^ d) • lam = lam) : l ∣ d := by
  have hdq : d = l * (d / l) + d % l := (Nat.div_add_mod d l).symm
  have hfixq : (u ^ (l * (d / l))) • lam = lam := by
    rw [pow_mul]
    induction d / l with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, hfix, ih]
  have hmod : (u ^ (d % l)) • lam = lam := by
    have h1 : (u ^ (l * (d / l))) • ((u ^ (d % l)) • lam) = lam := by
      rw [← mul_smul, ← pow_add, ← hdq, hd]
    have h2 : (u ^ (l * (d / l))) • ((u ^ (d % l)) • lam)
        = (u ^ (l * (d / l))) • lam := by rw [h1, hfixq]
    exact smul_left_cancel (u ^ (l * (d / l))) h2
  have hlt : d % l < l := Nat.mod_lt _ (by omega)
  rcases Nat.eq_zero_or_pos (d % l) with h0 | hpos
  · exact Nat.dvd_of_mod_eq_zero h0
  · exact absurd hmod (hmin _ hpos hlt)

private theorem exists_pow_smul_eq_self_of_negClosed
    {u : WeylGroup Tag.E6} {B : Finset V} {lam : V} (hB : ∀ v ∈ B, u • v ∈ B)
    (hlam : lam ∈ B) (hneg : ∀ v, v ∈ B ↔ -v ∈ B) (h0 : (0 : V) ∉ B)
    (hcard : B.card = 10) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ 10 ∧ l ≠ 9 ∧ (u ^ l) • lam = lam := by
  classical
  obtain ⟨l₀, hl₀1, hl₀card, hl₀fix⟩ := exists_pow_smul_eq_self_of_mapsTo hB hlam
  have hex : ∃ k, 1 ≤ k ∧ (u ^ k) • lam = lam := ⟨l₀, hl₀1, hl₀fix⟩
  obtain ⟨hl1, hlfix⟩ := Nat.find_spec hex
  set l := Nat.find hex with hldef
  have hlcard : l ≤ B.card := by
    rw [hldef]
    exact (Nat.find_le ⟨hl₀1, hl₀fix⟩).trans hl₀card
  have hmin : ∀ k : ℕ, 0 < k → k < l → (u ^ k) • lam ≠ lam := by
    intro k hk1 hkl hk
    exact Nat.find_min hex hkl ⟨hk1, hk⟩
  refine ⟨l, hl1, by omega, ?_, hlfix⟩
  intro hl9
  set O : Finset V := (Finset.range 9).image (fun k => (u ^ k) • lam) with hOdef
  have hinj : Set.InjOn (fun k : ℕ => (u ^ k) • lam) ↑(Finset.range 9) := by
    intro i hi j hj hEq
    rw [Finset.mem_coe, Finset.mem_range] at hi hj
    change (u ^ i) • lam = (u ^ j) • lam at hEq
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · exfalso
      have hd : (u ^ (j - i)) • lam = lam := by
        have hji : u ^ j = u ^ i * u ^ (j - i) := by
          rw [← pow_add, Nat.add_sub_cancel' hlt.le]
        rw [hji, mul_smul] at hEq
        have := congrArg (fun x => (u ^ i)⁻¹ • x) hEq
        simpa using this.symm
      exact hmin (j - i) (by omega) (by omega) hd
    · exact heq
    · exfalso
      have hd : (u ^ (i - j)) • lam = lam := by
        have hij : u ^ i = u ^ j * u ^ (i - j) := by
          rw [← pow_add, Nat.add_sub_cancel' hgt.le]
        rw [hij, mul_smul] at hEq
        have := congrArg (fun x => (u ^ j)⁻¹ • x) hEq
        simpa using this
      exact hmin (i - j) (by omega) (by omega) hd
  have hOcard : O.card = 9 := by
    rw [hOdef, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hOsub : O ⊆ B := by
    intro x hx
    rw [hOdef, Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [Finset.mem_range] at hk
    induction k with
    | zero => simpa using hlam
    | succ k ih => rw [pow_succ', mul_smul]; exact hB _ (ih (by omega))
  have hfix9 : (u ^ 9) • lam = lam := by simpa [hl9] using hlfix
  have hOinv : ∀ y ∈ O, u • y ∈ O := by
    intro y hy
    rw [hOdef, Finset.mem_image] at hy ⊢
    obtain ⟨k, hk, rfl⟩ := hy
    rw [Finset.mem_range] at hk
    by_cases hk9 : k + 1 < 9
    · exact ⟨k + 1, by simpa using hk9, by rw [pow_succ', mul_smul]⟩
    · have hk8 : k = 8 := by omega
      subst hk8
      refine ⟨0, by simp, ?_⟩
      rw [pow_zero, one_smul, ← mul_smul, ← pow_succ', hfix9]
  have hOimage : O.image (fun y => u • y) = O := by
    refine Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hOinv) ?_
    rw [Finset.card_image_of_injOn (fun y _ z _ h => smul_left_cancel u h)]
  set C : Finset V := B \ O with hCdef
  have hCcard : C.card = 1 := by
    have := Finset.card_sdiff_add_card_eq_card hOsub
    rw [hOcard, hcard] at this
    rw [hCdef]
    omega
  obtain ⟨x, hx⟩ : C.Nonempty := Finset.card_pos.mp (by rw [hCcard]; norm_num)
  have hxC : x ∈ C := hx
  rw [hCdef, Finset.mem_sdiff] at hx
  obtain ⟨hxB, hxO⟩ := hx
  have huxC : u • x ∈ C := by
    rw [hCdef, Finset.mem_sdiff]
    refine ⟨hB x hxB, ?_⟩
    intro huxO
    have hmem : u • x ∈ O.image (fun y => u • y) := by rw [hOimage]; exact huxO
    rw [Finset.mem_image] at hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hyx' : y = x := smul_left_cancel u hyx
    exact hxO (hyx' ▸ hy)
  have hsingle : ∀ y ∈ C, y = x := by
    have hle : C.card ≤ 1 := by omega
    have h2 : ∀ a ∈ C, ∀ b ∈ C, a = b := Finset.card_le_one.mp hle
    exact fun y hy => h2 y hy x hxC
  have hux : u • x = x := (hsingle (u • x) huxC).trans (hsingle x hxC).symm
  have hnegO : -lam ∉ O := by
    intro hmem
    rw [hOdef, Finset.mem_image] at hmem
    obtain ⟨k, hk, hEq⟩ := hmem
    rw [Finset.mem_range] at hk
    have h2 : (u ^ (2 * k)) • lam = lam := by
      have h1 : (u ^ k) • (-lam) = (u ^ k) • ((u ^ k) • lam) := by rw [← hEq]
      rw [smul_neg, ← mul_smul, ← pow_add] at h1
      rw [hEq, neg_neg] at h1
      have h1' : u ^ (k + k) • lam = lam := h1.symm
      rwa [show k + k = 2 * k by omega] at h1'
    have hdvd : 9 ∣ 2 * k :=
      dvd_of_pow_smul_eq_self (l := 9) (by omega) (by simpa [hl9] using hlfix)
        (fun m hm1 hm9 => hmin m hm1 (by omega)) h2
    obtain ⟨t, ht⟩ := hdvd
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · have hz : lam = 0 := by
        have h : lam = -lam := by simpa [hk0] using hEq
        funext i
        have hi := congrFun h i
        simp only [Pi.neg_apply] at hi
        change lam i = 0
        omega
      exact h0 (hz ▸ hlam)
    · omega
  have hnegB : -lam ∈ B := (hneg lam).mp hlam
  have hnegC : -lam ∈ C := by
    rw [hCdef, Finset.mem_sdiff]
    exact ⟨hnegB, hnegO⟩
  have hnegx : -lam = x := hsingle (-lam) hnegC
  have hufix : u • (-lam) = -lam := by rw [hnegx, hux]
  have : u • lam = lam := by
    have h1 : -(u • lam) = -lam := by rw [← smul_neg]; exact hufix
    exact neg_injective h1
  exact hmin 1 (by omega) (by omega) (by simpa using this)

private theorem neg_mem_iff_of_image_neg {B : Finset V} (h : B.image Neg.neg = B) (v : V) :
    v ∈ B ↔ -v ∈ B := by
  constructor
  · intro hv
    rw [← h, Finset.mem_image]
    exact ⟨v, hv, rfl⟩
  · intro hv
    rw [← h, Finset.mem_image]
    exact ⟨-v, hv, neg_neg v⟩

private theorem pow_eq_one_of_dvd_six_six {K : Type} [Field K] {c : Fin Tag.E6.rank → Kˣ}
    {r N : ℕ} (hN : N ∣ 6 ^ 6) (hr : r.Prime) (hr3 : 3 < r)
    (hcr : ∀ i, c i ^ r = 1) (hpow : ∀ j, c j ^ N = 1) : c = 1 := by
  have hcop : Nat.Coprime N r := by
    rw [Nat.coprime_comm, hr.coprime_iff_not_dvd]
    intro hd
    have hd6 : r ∣ 6 := hr.dvd_of_dvd_pow (hd.trans hN)
    have hle : r ≤ 6 := Nat.le_of_dvd (by norm_num) hd6
    have h4 : r = 4 ∨ r = 5 ∨ r = 6 := by omega
    rcases h4 with rfl | rfl | rfl
    · norm_num at hr
    · norm_num at hd6
    · norm_num at hr
  funext j
  have hdvd : orderOf (c j) ∣ N := orderOf_dvd_of_pow_eq_one (hpow j)
  have hdvd' : orderOf (c j) ∣ r := orderOf_dvd_of_pow_eq_one (hcr j)
  have hgcd : orderOf (c j) ∣ Nat.gcd N r := Nat.dvd_gcd hdvd hdvd'
  rw [Nat.Coprime.gcd_eq_one hcop] at hgcd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)

private theorem c_eq_one_12 {K : Type} [Field K] {c : Fin Tag.E6.rank → Kˣ} {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) (hcr : ∀ i, c i ^ r = 1)
    (hB : ∀ v ∈ B12, rootChar c v = 1) : c = 1 :=
  pow_eq_one_of_dvd_six_six (by norm_num) hr hr3 hcr fun j =>
    pow_eq_one_of_comb (len12 j) (comb12 j) hB

private theorem c_eq_one_3 {K : Type} [Field K] {c : Fin Tag.E6.rank → Kˣ} {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) (hcr : ∀ i, c i ^ r = 1)
    (hB : ∀ v ∈ B3, rootChar c v = 1) : c = 1 :=
  pow_eq_one_of_dvd_six_six (by norm_num) hr hr3 hcr fun j =>
    pow_eq_one_of_comb (len3 j) (comb3 j) hB

private theorem c_eq_one_45 {K : Type} [Field K] {c : Fin Tag.E6.rank → Kˣ} {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) (hcr : ∀ i, c i ^ r = 1)
    (hB : ∀ v ∈ B45, rootChar c v = 1) : c = 1 :=
  pow_eq_one_of_dvd_six_six (by norm_num) hr hr3 hcr fun j =>
    pow_eq_one_of_comb (len45 j) (comb45 j) hB

private theorem c_eq_one_6 {K : Type} [Field K] {c : Fin Tag.E6.rank → Kˣ} {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) (hcr : ∀ i, c i ^ r = 1)
    (hB : ∀ v ∈ B6, rootChar c v = 1) : c = 1 :=
  pow_eq_one_of_dvd_six_six (by norm_num) hr hr3 hcr fun j =>
    pow_eq_one_of_comb (len6 j) (comb6 j) hB

private theorem c_eq_one_7 {K : Type} [Field K] {c : Fin Tag.E6.rank → Kˣ} {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) (hcr : ∀ i, c i ^ r = 1)
    (hB : ∀ v ∈ B7, rootChar c v = 1) : c = 1 :=
  pow_eq_one_of_dvd_six_six (by norm_num) hr hr3 hcr fun j =>
    pow_eq_one_of_comb (len7 j) (comb7 j) hB

private theorem dvd_of_orbit {K : Type} [Field K] {c : Fin Tag.E6.rank → Kˣ} {r : ℕ}
    (hr : r.Prime) (hcr : ∀ i, c i ^ r = 1)
    {u : WeylGroup Tag.E6} {m : ℤ} (hcu : weylAct u (c ^ m) = c)
    {lam : V} {l : ℕ} (hv : (u ^ l) • lam = lam) (hne : rootChar c lam ≠ 1) :
    (r : ℤ) ∣ m ^ l - 1 := by
  have hpow : rootChar c lam ^ r = 1 := by
    rw [rootChar, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcr i, one_zpow]
  have hord : orderOf (rootChar c lam) = r := by
    haveI : Fact r.Prime := ⟨hr⟩
    exact orderOf_eq_prime hpow hne
  rw [← hord]
  exact orderOf_dvd_iff_zpow_eq_one.mpr
    (rootChar_pow_sub_one_eq_one_of_weylAct_zpow_eq hcu hv)

private theorem toFinset_mapsTo
    {b : Fin Tag.E6.rank → ZMod 3} {B : List V}
    (hcheck : ∀ (k : Fin 72), triPairing b (e6Root k) = 0 →
      ∀ v ∈ B, v - corootPair (e6Root k) v • e6Root k ∈ B)
    {u : WeylGroup Tag.E6} (hu : u ∈ kernelWeylGroup (triChar b)) :
    ∀ v ∈ B.toFinset, u • v ∈ B.toFinset := by
  intro v hv
  rw [List.mem_toFinset] at hv ⊢
  exact mapsTo_of_check hcheck hu v hv

private theorem exists_pow_smul_eq_self_of_card
    {u : WeylGroup Tag.E6} {B : Finset V} {lam : V} {n : ℕ}
    (hB : ∀ v ∈ B, u • v ∈ B) (hlam : lam ∈ B) (hcard : B.card = n) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ n ∧ (u ^ l) • lam = lam := by
  obtain ⟨l, hl1, hlcard, hv⟩ := exists_pow_smul_eq_self_of_mapsTo hB hlam
  exact ⟨l, hl1, by omega, hv⟩

private theorem case1
    {K : Type} [Field K] {c : Fin Tag.E6.rank → Kˣ} {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) (hcr : ∀ i, c i ^ r = 1) (hc : c ≠ 1)
    {u : WeylGroup Tag.E6}
    (hu : u ∈ kernelWeylGroup (triChar (vec3 (τ := .E6) (e6ThreeReps.getD 1 []))))
    {m : ℤ} (hcu : weylAct u (c ^ m) = c) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ 10 ∧ l ≠ 9 ∧ (r : ℤ) ∣ m ^ l - 1 := by
  have hdetect : ∃ lam ∈ B12, rootChar c lam ≠ 1 := by
    by_contra h
    push Not at h
    exact hc (c_eq_one_12 hr hr3 hcr h)
  obtain ⟨lam, hlam, hne⟩ := hdetect
  rcases List.mem_cons.mp hlam with rfl | hlam10
  · have hfix : u • f12 = f12 := by
      have := toFinset_mapsTo (stable12f 1 (Or.inl rfl)) hu f12 (by simp)
      simpa using this
    exact ⟨1, le_rfl, by norm_num, by norm_num,
      dvd_of_orbit hr hcr hcu (l := 1) (by simpa using hfix) hne⟩
  · have hstable : ∀ v ∈ B10.toFinset, u • v ∈ B10.toFinset :=
      toFinset_mapsTo (stable12b 1 (Or.inl rfl)) hu
    have hneg : ∀ v : V, v ∈ B10.toFinset ↔ -v ∈ B10.toFinset :=
      neg_mem_iff_of_image_neg (by decide)
    have h0 : (0 : V) ∉ B10.toFinset := by decide
    have hcard : B10.toFinset.card = 10 := by decide
    obtain ⟨l, hl1, hl10, hl9, hv⟩ :=
      exists_pow_smul_eq_self_of_negClosed hstable (by rwa [List.mem_toFinset]) hneg h0 hcard
    exact ⟨l, hl1, hl10, hl9, dvd_of_orbit hr hcr hcu hv hne⟩

private theorem case2
    {K : Type} [Field K] {c : Fin Tag.E6.rank → Kˣ} {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) (hcr : ∀ i, c i ^ r = 1) (hc : c ≠ 1)
    {u : WeylGroup Tag.E6}
    (hu : u ∈ kernelWeylGroup (triChar (vec3 (τ := .E6) (e6ThreeReps.getD 2 []))))
    {m : ℤ} (hcu : weylAct u (c ^ m) = c) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ 10 ∧ l ≠ 9 ∧ (r : ℤ) ∣ m ^ l - 1 := by
  have hdetect : ∃ lam ∈ B12, rootChar c lam ≠ 1 := by
    by_contra h
    push Not at h
    exact hc (c_eq_one_12 hr hr3 hcr h)
  obtain ⟨lam, hlam, hne⟩ := hdetect
  rcases List.mem_cons.mp hlam with rfl | hlam10
  · have hfix : u • f12 = f12 := by
      have := toFinset_mapsTo (stable12f 2 (Or.inr rfl)) hu f12 (by simp)
      simpa using this
    exact ⟨1, le_rfl, by norm_num, by norm_num,
      dvd_of_orbit hr hcr hcu (l := 1) (by simpa using hfix) hne⟩
  · have hstable : ∀ v ∈ B10.toFinset, u • v ∈ B10.toFinset :=
      toFinset_mapsTo (stable12b 2 (Or.inr rfl)) hu
    have hneg : ∀ v : V, v ∈ B10.toFinset ↔ -v ∈ B10.toFinset :=
      neg_mem_iff_of_image_neg (by decide)
    have h0 : (0 : V) ∉ B10.toFinset := by decide
    have hcard : B10.toFinset.card = 10 := by decide
    obtain ⟨l, hl1, hl10, hl9, hv⟩ :=
      exists_pow_smul_eq_self_of_negClosed hstable (by rwa [List.mem_toFinset]) hneg h0 hcard
    exact ⟨l, hl1, hl10, hl9, dvd_of_orbit hr hcr hcu hv hne⟩

private theorem case3
    {K : Type} [Field K] {c : Fin Tag.E6.rank → Kˣ} {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) (hcr : ∀ i, c i ^ r = 1) (hc : c ≠ 1)
    {u : WeylGroup Tag.E6}
    (hu : u ∈ kernelWeylGroup (triChar (vec3 (τ := .E6) (e6ThreeReps.getD 3 []))))
    {m : ℤ} (hcu : weylAct u (c ^ m) = c) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ 10 ∧ l ≠ 9 ∧ (r : ℤ) ∣ m ^ l - 1 := by
  have hdetect : ∃ lam ∈ B3, rootChar c lam ≠ 1 := by
    by_contra h
    push Not at h
    exact hc (c_eq_one_3 hr hr3 hcr h)
  obtain ⟨lam, hlam, hne⟩ := hdetect
  have hstable : ∀ v ∈ B3.toFinset, u • v ∈ B3.toFinset := toFinset_mapsTo stable3 hu
  have hcard : B3.toFinset.card = 6 := by decide
  obtain ⟨l, hl1, hl6, hv⟩ :=
    exists_pow_smul_eq_self_of_card hstable (by rwa [List.mem_toFinset]) hcard
  exact ⟨l, hl1, by omega, by omega, dvd_of_orbit hr hcr hcu hv hne⟩

private theorem case4
    {K : Type} [Field K] {c : Fin Tag.E6.rank → Kˣ} {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) (hcr : ∀ i, c i ^ r = 1) (hc : c ≠ 1)
    {u : WeylGroup Tag.E6}
    (hu : u ∈ kernelWeylGroup (triChar (vec3 (τ := .E6) (e6ThreeReps.getD 4 []))))
    {m : ℤ} (hcu : weylAct u (c ^ m) = c) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ 10 ∧ l ≠ 9 ∧ (r : ℤ) ∣ m ^ l - 1 := by
  have hdetect : ∃ lam ∈ B45, rootChar c lam ≠ 1 := by
    by_contra h
    push Not at h
    exact hc (c_eq_one_45 hr hr3 hcr h)
  obtain ⟨lam, hlam, hne⟩ := hdetect
  rcases List.mem_append.mp hlam with hlam4a | hlam4b
  · have hstable : ∀ v ∈ B4a.toFinset, u • v ∈ B4a.toFinset :=
      toFinset_mapsTo (stable45a 4 (Or.inl rfl)) hu
    have hcard : B4a.toFinset.card = 2 := by decide
    obtain ⟨l, hl1, hl2, hv⟩ :=
      exists_pow_smul_eq_self_of_card hstable (by rwa [List.mem_toFinset]) hcard
    exact ⟨l, hl1, by omega, by omega, dvd_of_orbit hr hcr hcu hv hne⟩
  · have hstable : ∀ v ∈ B4b.toFinset, u • v ∈ B4b.toFinset :=
      toFinset_mapsTo (stable45b 4 (Or.inl rfl)) hu
    have hcard : B4b.toFinset.card = 5 := by decide
    obtain ⟨l, hl1, hl5, hv⟩ :=
      exists_pow_smul_eq_self_of_card hstable (by rwa [List.mem_toFinset]) hcard
    exact ⟨l, hl1, by omega, by omega, dvd_of_orbit hr hcr hcu hv hne⟩

private theorem case5
    {K : Type} [Field K] {c : Fin Tag.E6.rank → Kˣ} {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) (hcr : ∀ i, c i ^ r = 1) (hc : c ≠ 1)
    {u : WeylGroup Tag.E6}
    (hu : u ∈ kernelWeylGroup (triChar (vec3 (τ := .E6) (e6ThreeReps.getD 5 []))))
    {m : ℤ} (hcu : weylAct u (c ^ m) = c) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ 10 ∧ l ≠ 9 ∧ (r : ℤ) ∣ m ^ l - 1 := by
  have hdetect : ∃ lam ∈ B45, rootChar c lam ≠ 1 := by
    by_contra h
    push Not at h
    exact hc (c_eq_one_45 hr hr3 hcr h)
  obtain ⟨lam, hlam, hne⟩ := hdetect
  rcases List.mem_append.mp hlam with hlam4a | hlam4b
  · have hstable : ∀ v ∈ B4a.toFinset, u • v ∈ B4a.toFinset :=
      toFinset_mapsTo (stable45a 5 (Or.inr rfl)) hu
    have hcard : B4a.toFinset.card = 2 := by decide
    obtain ⟨l, hl1, hl2, hv⟩ :=
      exists_pow_smul_eq_self_of_card hstable (by rwa [List.mem_toFinset]) hcard
    exact ⟨l, hl1, by omega, by omega, dvd_of_orbit hr hcr hcu hv hne⟩
  · have hstable : ∀ v ∈ B4b.toFinset, u • v ∈ B4b.toFinset :=
      toFinset_mapsTo (stable45b 5 (Or.inr rfl)) hu
    have hcard : B4b.toFinset.card = 5 := by decide
    obtain ⟨l, hl1, hl5, hv⟩ :=
      exists_pow_smul_eq_self_of_card hstable (by rwa [List.mem_toFinset]) hcard
    exact ⟨l, hl1, by omega, by omega, dvd_of_orbit hr hcr hcu hv hne⟩

private theorem case6
    {K : Type} [Field K] {c : Fin Tag.E6.rank → Kˣ} {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) (hcr : ∀ i, c i ^ r = 1) (hc : c ≠ 1)
    {u : WeylGroup Tag.E6}
    (hu : u ∈ kernelWeylGroup (triChar (vec3 (τ := .E6) (e6ThreeReps.getD 6 []))))
    {m : ℤ} (hcu : weylAct u (c ^ m) = c) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ 10 ∧ l ≠ 9 ∧ (r : ℤ) ∣ m ^ l - 1 := by
  have hdetect : ∃ lam ∈ B6, rootChar c lam ≠ 1 := by
    by_contra h
    push Not at h
    exact hc (c_eq_one_6 hr hr3 hcr h)
  obtain ⟨lam, hlam, hne⟩ := hdetect
  rcases List.mem_append.mp hlam with hlam6a | hlam6b
  · have hlamf : lam = f6 := List.mem_singleton.mp hlam6a
    subst hlamf
    have hfix : u • f6 = f6 := by
      have := toFinset_mapsTo stable6a hu f6 (by simp [B6a])
      simpa [B6a] using this
    exact ⟨1, le_rfl, by norm_num, by norm_num,
      dvd_of_orbit hr hcr hcu (l := 1) (by simpa using hfix) hne⟩
  · have hstable : ∀ v ∈ B6b.toFinset, u • v ∈ B6b.toFinset := toFinset_mapsTo stable6b hu
    have hcard : B6b.toFinset.card = 8 := by decide
    obtain ⟨l, hl1, hl8, hv⟩ :=
      exists_pow_smul_eq_self_of_card hstable (by rwa [List.mem_toFinset]) hcard
    exact ⟨l, hl1, by omega, by omega, dvd_of_orbit hr hcr hcu hv hne⟩

private theorem case7
    {K : Type} [Field K] {c : Fin Tag.E6.rank → Kˣ} {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) (hcr : ∀ i, c i ^ r = 1) (hc : c ≠ 1)
    {u : WeylGroup Tag.E6}
    (hu : u ∈ kernelWeylGroup (triChar (vec3 (τ := .E6) (e6ThreeReps.getD 7 []))))
    {m : ℤ} (hcu : weylAct u (c ^ m) = c) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ 10 ∧ l ≠ 9 ∧ (r : ℤ) ∣ m ^ l - 1 := by
  have hdetect : ∃ lam ∈ B7, rootChar c lam ≠ 1 := by
    by_contra h
    push Not at h
    exact hc (c_eq_one_7 hr hr3 hcr h)
  obtain ⟨lam, hlam, hne⟩ := hdetect
  rcases List.mem_append.mp hlam with hlam7ab | hlam7c
  · rcases List.mem_append.mp hlam7ab with hlam7a | hlam7b
    · have hstable : ∀ v ∈ B7a.toFinset, u • v ∈ B7a.toFinset := toFinset_mapsTo stable7a hu
      have hcard : B7a.toFinset.card = 6 := by decide
      obtain ⟨l, hl1, hl6, hv⟩ :=
        exists_pow_smul_eq_self_of_card hstable (by rwa [List.mem_toFinset]) hcard
      exact ⟨l, hl1, by omega, by omega, dvd_of_orbit hr hcr hcu hv hne⟩
    · have hstable : ∀ v ∈ B7b.toFinset, u • v ∈ B7b.toFinset := toFinset_mapsTo stable7b hu
      have hcard : B7b.toFinset.card = 6 := by decide
      obtain ⟨l, hl1, hl6, hv⟩ :=
        exists_pow_smul_eq_self_of_card hstable (by rwa [List.mem_toFinset]) hcard
      exact ⟨l, hl1, by omega, by omega, dvd_of_orbit hr hcr hcu hv hne⟩
  · have hstable : ∀ v ∈ B7c.toFinset, u • v ∈ B7c.toFinset := toFinset_mapsTo stable7c hu
    have hcard : B7c.toFinset.card = 6 := by decide
    obtain ⟨l, hl1, hl6, hv⟩ :=
      exists_pow_smul_eq_self_of_card hstable (by rwa [List.mem_toFinset]) hcard
    exact ⟨l, hl1, by omega, by omega, dvd_of_orbit hr hcr hcu hv hne⟩

private theorem weylAct_one_tuple {K : Type} [Field K] (w : WeylGroup Tag.E6) :
    weylAct w (1 : Fin Tag.E6.rank → Kˣ) = 1 := by
  funext i
  change rootChar (1 : Fin Tag.E6.rank → Kˣ) (w⁻¹ • (Pi.single i 1)) = 1
  rw [rootChar]
  simp

theorem exists_dvd_pow_sub_one_of_mem_kernelReflectionGroup
    {K : Type} [Field K] {a : Fin Tag.E6.rank → Kˣ} (ha3 : ∀ i, a i ^ 3 = 1) (ha : a ≠ 1)
    {u : WeylGroup Tag.E6} (hu : u ∈ kernelReflectionGroup a) {c : Fin Tag.E6.rank → Kˣ} {r : ℕ}
    (hr : r.Prime) (hr3 : 3 < r) (hcr : ∀ i, c i ^ r = 1) (hc : c ≠ 1) {m : ℤ}
    (hcu : weylAct u (c ^ m) = c) :
    ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ 10 ∧ ℓ ≠ 9 ∧ (r : ℤ) ∣ m ^ ℓ - 1 := by
  obtain ⟨χ', hker⟩ := exists_triChar_ker_eq (rootCharHom3 a) (rootCharHom3_pow_three a ha3)
  set b : Fin Tag.E6.rank → ZMod 3 :=
    fun j => Z3.toAdd (χ' (Multiplicative.ofAdd (Pi.single j 1))) with hbdef
  have hχ' : χ' = triChar b := eq_triChar χ'
  have huW : u ∈ kernelWeylGroup (triChar b) := by
    have h1 : kernelReflectionGroup a = kernelWeylGroup (rootCharHom3 a) := rfl
    rw [h1] at hu
    rw [kernelWeylGroup_congr_ker hker] at hu
    rwa [hχ'] at hu
  obtain ⟨horbit, -⟩ := e6ThreeScCheck_spec
  obtain ⟨ρ, hρ, t, ht⟩ := exists_isCharConj_of_orbitCheck3 horbit (triChar b)
  rw [kernelWeylGroup_eq_map ht, Subgroup.mem_map] at huW
  obtain ⟨u₀, hu₀, hu_eq⟩ := huW
  have hu_eq' : u = t * u₀ * t⁻¹ := by
    rw [← hu_eq]
    exact MulAut.conj_apply t u₀
  let c' : Fin Tag.E6.rank → Kˣ := weylAct t⁻¹ c
  have hc' : c' ≠ 1 := by
    intro h
    apply hc
    have h1 : weylAct t c' = c := by
      show weylAct t (weylAct t⁻¹ c) = c
      rw [← weylAct_mul, mul_inv_cancel, weylAct_one]
    rw [h, weylAct_one_tuple] at h1
    exact h1.symm
  have hcr' : ∀ i, c' i ^ r = 1 := by
    have h2 : (weylAct t⁻¹ c) ^ ((r : ℤ)) = 1 := by
      rw [← weylAct_zpow]
      have hcrpow : c ^ r = 1 := funext hcr
      rw [zpow_natCast, hcrpow, weylAct_one_tuple]
    have h3 : c' ^ r = 1 := by simpa using h2
    intro i
    exact congrFun h3 i
  have hcu₀' : weylAct u₀ ((weylAct t⁻¹ c) ^ m) = weylAct t⁻¹ c := by
    have h1 : weylAct t (weylAct u₀ ((weylAct t⁻¹ c) ^ m)) = c := by
      rw [show weylAct t (weylAct u₀ ((weylAct t⁻¹ c) ^ m))
          = weylAct t (weylAct u₀ (weylAct t⁻¹ (c ^ m))) from
            congrArg (fun x => weylAct t (weylAct u₀ x)) (weylAct_zpow t⁻¹ c m).symm]
      rw [← weylAct_mul, ← weylAct_mul]
      rw [← hu_eq']
      exact hcu
    have h2 := congrArg (weylAct t⁻¹) h1
    rw [← weylAct_mul, inv_mul_cancel, weylAct_one] at h2
    exact h2
  have hcu₀ : weylAct u₀ (c' ^ m) = c' := hcu₀'
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    have htri : ∀ x : Multiplicative (Fin Tag.E6.rank → ℤ), triChar b x = 1 := by
      intro x
      rw [show x = Multiplicative.ofAdd (Multiplicative.toAdd x) from rfl,
        ht (Multiplicative.toAdd x)]
      have hb0 : (vec3 (τ := .E6) (e6ThreeReps.getD 0 []) : Fin Tag.E6.rank → ZMod 3) = 0 := by
        decide
      rw [hb0]
      simp [triChar, triPairing]
      rfl
    have hroot : rootCharHom3 a = 1 := by
      refine MonoidHom.ext fun x => ?_
      exact (hker x).mpr (by rw [hχ']; exact htri x)
    apply ha
    funext i
    have := congrArg (fun f : Multiplicative (Fin Tag.E6.rank → ℤ) →* Kˣ =>
      f (Multiplicative.ofAdd (Pi.single i 1))) hroot
    simpa [rootCharHom3, rootChar_single] using this
  have hρ8 : ρ < 8 := by simpa [e6ThreeReps] using hρ
  have hρ1 : 1 ≤ ρ := Nat.one_le_iff_ne_zero.mpr hρ0
  have hcases : ρ = 1 ∨ ρ = 2 ∨ ρ = 3 ∨ ρ = 4 ∨ ρ = 5 ∨ ρ = 6 ∨ ρ = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact case1 hr hr3 hcr' hc' hu₀ hcu₀
  · exact case2 hr hr3 hcr' hc' hu₀ hcu₀
  · exact case3 hr hr3 hcr' hc' hu₀ hcu₀
  · exact case4 hr hr3 hcr' hc' hu₀ hcu₀
  · exact case5 hr hr3 hcr' hc' hu₀ hcu₀
  · exact case6 hr hr3 hcr' hc' hu₀ hcu₀
  · exact case7 hr hr3 hcr' hc' hu₀ hcu₀

end CFSG.StandardType.TwE6FrameNoPpd
