module

public import CFSG.Quasithin.Background.RonanE114Good
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Q1
public import CFSG.Quasithin.Background.RonanE114A7
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.RonanE114.L52Flag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.L239
  CFSG.Open CFSG.Quasithin

section Flags

variable {K : Type} [Field K] {n : ℕ}

theorem flagStabilizer_le_iff {I J : Set ℕ} (hJ : ∀ j ∈ J, 1 ≤ j ∧ j < n) :
    flagStabilizer n K I ≤ flagStabilizer n K J ↔ J ⊆ I := by
  constructor
  · intro h j hj
    by_contra hjI
    obtain ⟨hj1, hjn⟩ := hJ j hj
    have hrI : reflection n K j hj1 hjn ∈ flagStabilizer n K I :=
      ((subflag_stabilizer_generation (K := K) (n := n) I).2.2 j hj1 hjn).mpr hjI
    have hrJ := h hrI
    exact (((subflag_stabilizer_generation (K := K) (n := n) J).2.2 j hj1 hjn).mp hrJ) hj
  · intro h g hg
    exact mem_flagStabilizer.mpr fun j hj => mem_flagStabilizer.mp hg j (h hj)

theorem flagStabilizer_inj {I J : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ j < n) (h : flagStabilizer n K I = flagStabilizer n K J) : I = J :=
  Set.Subset.antisymm ((flagStabilizer_le_iff (K := K) hI).mp h.ge)
    ((flagStabilizer_le_iff (K := K) hJ).mp h.le)

theorem flagStabilizer_sup {I J : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < n)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ j < n) :
    flagStabilizer n K I ⊔ flagStabilizer n K J = flagStabilizer n K (I ∩ J) := by
  set A := flagStabilizer n K I ⊔ flagStabilizer n K J with hA
  have hBA : upperTriangular n K ≤ A :=
    (upperTriangular_le_flagStabilizer (K := K) (n := n) I).trans le_sup_left
  obtain ⟨hAeq, -⟩ := borel_overgroups A hBA
  have hcuts : ∀ c ∈ borelOvergroupCuts A, 1 ≤ c ∧ c < n := fun c hc => ⟨hc.1, hc.2.1⟩
  have h1 : borelOvergroupCuts A ⊆ I :=
    (flagStabilizer_le_iff (K := K) (I := I) hcuts).mp (hAeq ▸ le_sup_left)
  have h2 : borelOvergroupCuts A ⊆ J :=
    (flagStabilizer_le_iff (K := K) (I := J) hcuts).mp (hAeq ▸ le_sup_right)
  refine le_antisymm ?_ ?_
  · exact sup_le ((flagStabilizer_le_iff (K := K) (I := I) fun k hk => hI k hk.1).mpr
      Set.inter_subset_left) ((flagStabilizer_le_iff (K := K) (I := J) fun k hk => hI k hk.1).mpr
      Set.inter_subset_right)
  · rw [hAeq]
    exact (flagStabilizer_le_iff (K := K) (I := I ∩ J) hcuts).mpr (Set.subset_inter h1 h2)

end Flags

section Five

open CFSG.QuasithinUnique.Setup.Family

theorem solvable_flagStabilizer_five {I : Set ℕ}
    (hsmall : ∀ a m : ℕ, a + m ≤ 5 → (a = 0 ∨ a ∈ I) → (a + m = 5 ∨ a + m ∈ I) →
      (∀ c ∈ I, ¬ (a < c ∧ c < a + m)) → m ≤ 2) :
    Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) I) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  exact (isSolvable_iff_perfectCore_eq_bot _).mpr
    (perfectCore_eq_bot_of_small (n := 5) hK2 (by norm_num) hsmall)

theorem solvable_Q23 : Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) {2, 3}) := by
  refine solvable_flagStabilizer_five fun a m h ha hb hno => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hno
  have h2 := hno 2 (Or.inl rfl)
  have h3 := hno 3 (Or.inr rfl)
  omega

theorem solvable_Q124 : Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) {1, 2, 4}) := by
  refine solvable_flagStabilizer_five fun a m h ha hb hno => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hno
  have h1 := hno 1 (Or.inl rfl)
  have h2 := hno 2 (Or.inr (Or.inl rfl))
  have h4 := hno 4 (Or.inr (Or.inr rfl))
  omega

theorem solvable_Q134 : Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) {1, 3, 4}) := by
  refine solvable_flagStabilizer_five fun a m h ha hb hno => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hno
  have h1 := hno 1 (Or.inl rfl)
  have h3 := hno 3 (Or.inr (Or.inl rfl))
  have h4 := hno 4 (Or.inr (Or.inr rfl))
  omega

@[expose] def FlagFix (α : MulAut (SpecialLinearGroup (Fin 5) (ZMod 2))) : Prop :=
  ∀ d ≤ 5, (stabilizer (flagSpace 5 (ZMod 2) d)).map α.toMonoidHom =
    stabilizer (flagSpace 5 (ZMod 2) d)

@[expose] def FlagSwap (α : MulAut (SpecialLinearGroup (Fin 5) (ZMod 2))) : Prop :=
  ∀ d ≤ 5, (stabilizer (flagSpace 5 (ZMod 2) d)).map α.toMonoidHom =
    stabilizer (flagSpace 5 (ZMod 2) (5 - d))

theorem flag_dichotomy (α : MulAut (SpecialLinearGroup (Fin 5) (ZMod 2)))
    (hα : (unitriangular 5 (ZMod 2)).map α.toMonoidHom = unitriangular 5 (ZMod 2)) :
    FlagFix α ∨ FlagSwap α := by
  set β : MulAut (projectiveSL 5 (ZMod 2)) :=
    (projEquiv 5).symm.trans (α.trans (projEquiv 5)) with hβ
  have hβp : ∀ x : SpecialLinearGroup (Fin 5) (ZMod 2),
      β (proj 5 (ZMod 2) x) = proj 5 (ZMod 2) (α x) := by
    intro x
    have h1 : proj 5 (ZMod 2) x = projEquiv 5 x := rfl
    have h2 : proj 5 (ZMod 2) (α x) = projEquiv 5 (α x) := rfl
    rw [h1, h2, hβ]
    simp
  have hmap : ∀ Q : Subgroup (SpecialLinearGroup (Fin 5) (ZMod 2)),
      (Q.map (proj 5 (ZMod 2))).map β.toMonoidHom = (Q.map α.toMonoidHom).map (proj 5 (ZMod 2)) := by
    intro Q
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    exact hβp x
  have hU : (projUnitriangular 5 (ZMod 2)).map β.toMonoidHom = projUnitriangular 5 (ZMod 2) := by
    rw [projUnitriangular, hmap, hα]
  have hinj := Subgroup.map_injective (proj_injective_zmod_two 5)
  rcases automorphism_flag_dichotomy (by norm_num) β hU with h | h
  · left
    intro d hd
    have := h d hd
    apply hinj
    rw [← hmap]
    exact this
  · right
    intro d hd
    have := h d hd
    apply hinj
    rw [← hmap]
    exact this

theorem map_flagStabilizer_of_fix {α : MulAut (SpecialLinearGroup (Fin 5) (ZMod 2))}
    (h : FlagFix α) {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 5) :
    (flagStabilizer 5 (ZMod 2) I).map α.toMonoidHom = flagStabilizer 5 (ZMod 2) I := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_flagStabilizer, mem_flagStabilizer]
  refine forall₂_congr fun i hi => ?_
  have h1 := h i (hI i hi)
  have h2 : g ∈ (stabilizer (flagSpace 5 (ZMod 2) i)).map α.toMonoidHom ↔
      α.symm g ∈ stabilizer (flagSpace 5 (ZMod 2) i) := Subgroup.mem_map_equiv
  rw [h1] at h2
  exact h2.symm

theorem map_flagStabilizer_of_swap {α : MulAut (SpecialLinearGroup (Fin 5) (ZMod 2))}
    (h : FlagSwap α) {I : Set ℕ} (hI : ∀ i ∈ I, i ≤ 5) :
    (flagStabilizer 5 (ZMod 2) I).map α.toMonoidHom =
      flagStabilizer 5 (ZMod 2) ((fun i => 5 - i) '' I) := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_flagStabilizer, mem_flagStabilizer]
  simp only [Set.forall_mem_image]
  refine forall₂_congr fun i hi => ?_
  have := h i (hI i hi)
  rw [← this, Subgroup.mem_map_equiv]

theorem flagStabilizer_full_eq_unitriangular :
    flagStabilizer 5 (ZMod 2) {1, 2, 3, 4} = unitriangular 5 (ZMod 2) := by
  have hK2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hset : ({1, 2, 3, 4} : Set ℕ) = {i | 1 ≤ i ∧ i < 5} := by
    ext i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    omega
  have h : upperTriangular 5 (ZMod 2) = flagStabilizer 5 (ZMod 2) {1, 2, 3, 4} := by
    rw [hset]
    exact upperTriangular_eq_flagStabilizer_full 5
  rw [← h]
  exact le_antisymm (upperTriangular_le_unitriangular hK2) (unitriangular_le_upperTriangular 5 _)

theorem l52_goodPair (𝒜 : Set (MulAut (SpecialLinearGroup (Fin 5) (ZMod 2))))
    (h𝒜 : ∀ α ∈ 𝒜, (unitriangular 5 (ZMod 2)).map α.toMonoidHom = unitriangular 5 (ZMod 2)) :
    Good.GoodPair (SpecialLinearGroup (Fin 5) (ZMod 2)) (unitriangular 5 (ZMod 2)) 𝒜 := by
  have hK2 : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have hUle : ∀ I : Set ℕ, unitriangular 5 (ZMod 2) ≤ flagStabilizer 5 (ZMod 2) I := fun I =>
    (unitriangular_le_upperTriangular 5 (ZMod 2)).trans (upperTriangular_le_flagStabilizer I)
  refine ⟨flagStabilizer 5 (ZMod 2) {2, 3}, flagStabilizer 5 (ZMod 2) {1, 4}, hUle _, hUle _,
    solvable_Q23, ?_, fun α hα => ?_, ?_⟩
  · rw [sup_comm, flagStabilizer_sup (K := ZMod 2) (n := 5) (I := {1, 4}) (J := {2, 3})
      (by intro i hi; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi; omega)
      (by intro i hi; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi; omega)]
    have : ({1, 4} : Set ℕ) ∩ {2, 3} = ∅ := by
      ext i
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false]
      omega
    rw [this, flagStabilizer_empty]
  · have h := L52.flagStabilizer_pair_invariant α (h𝒜 α hα)
    exact ⟨h.2, h.1⟩
  have hc14 : ∀ i ∈ ({1, 4} : Set ℕ), 1 ≤ i ∧ i < 5 := by
    intro i hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    omega
  have hc124 : ∀ i ∈ ({1, 2, 4} : Set ℕ), 1 ≤ i ∧ i < 5 := by
    intro i hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    omega
  have hc134 : ∀ i ∈ ({1, 3, 4} : Set ℕ), 1 ≤ i ∧ i < 5 := by
    intro i hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    omega
  by_cases hfix : ∀ α ∈ 𝒜, FlagFix α
  · left
    refine ⟨flagStabilizer 5 (ZMod 2) {1, 2, 4}, flagStabilizer 5 (ZMod 2) {1, 3, 4},
      (flagStabilizer_le_iff (K := ZMod 2) (I := {1, 2, 4}) hc14).mpr ?_,
      (flagStabilizer_le_iff (K := ZMod 2) (I := {1, 3, 4}) hc14).mpr ?_,
      solvable_Q124, solvable_Q134, ?_, fun α hα => ⟨?_, ?_⟩⟩
    · intro i hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
      omega
    · intro i hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
      omega
    · rw [flagStabilizer_sup (K := ZMod 2) (n := 5) hc124 hc134]
      congr 1
      ext i
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    · exact map_flagStabilizer_of_fix (hfix α hα) (fun i hi => (hc124 i hi).2.le)
    · exact map_flagStabilizer_of_fix (hfix α hα) (fun i hi => (hc134 i hi).2.le)
  · right
    push Not at hfix
    obtain ⟨α₀, hα₀, hne⟩ := hfix
    have hswap : FlagSwap α₀ := (flag_dichotomy α₀ (h𝒜 α₀ hα₀)).resolve_left hne
    refine ⟨fun X hUX hXP hXinv => ?_, L52.q1 (ZMod 2) hK2, L52.q1_surjective hK2,
      L52.q1_ker_isPGroup hK2⟩
    obtain ⟨hXeq, -⟩ := borel_overgroups X ((upperTriangular_le_unitriangular hK2).trans hUX)
    have hIc : ∀ i ∈ borelOvergroupCuts X, 1 ≤ i ∧ i < 5 := fun i hi => ⟨hi.1, hi.2.1⟩
    set I := borelOvergroupCuts X with hI
    have h14 : ({1, 4} : Set ℕ) ⊆ I :=
      (flagStabilizer_le_iff (K := ZMod 2) (I := I) hc14).mp (hXeq ▸ hXP)
    have hdual : flagStabilizer 5 (ZMod 2) I =
        flagStabilizer 5 (ZMod 2) ((fun i => 5 - i) '' I) := by
      have h := hXinv α₀ hα₀
      rw [hXeq] at h
      rw [map_flagStabilizer_of_swap hswap (fun i hi => (hIc i hi).2.le)] at h
      exact h.symm
    have hdualcuts : ∀ j ∈ (fun i => 5 - i) '' I, 1 ≤ j ∧ j < 5 := by
      rintro _ ⟨i, hi, rfl⟩
      have := hIc i hi
      show 1 ≤ 5 - i ∧ 5 - i < 5
      omega
    have hII : I = (fun i => 5 - i) '' I :=
      flagStabilizer_inj (K := ZMod 2) hIc hdualcuts hdual
    have h23 : 2 ∈ I ↔ 3 ∈ I := by
      constructor
      · intro h
        have : 5 - 2 ∈ (fun i => 5 - i) '' I := ⟨2, h, rfl⟩
        rw [← hII] at this
        exact this
      · intro h
        have : 5 - 3 ∈ (fun i => 5 - i) '' I := ⟨3, h, rfl⟩
        rw [← hII] at this
        exact this
    by_cases h2I : 2 ∈ I
    · left
      have h3I := h23.mp h2I
      have hIeq : I = {1, 2, 3, 4} := by
        ext i
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · intro hi
          have := hIc i hi
          omega
        · rintro (rfl | rfl | rfl | rfl)
          · exact h14 (Or.inl rfl)
          · exact h2I
          · exact h3I
          · exact h14 (Or.inr rfl)
      rw [hXeq, hIeq]
      exact flagStabilizer_full_eq_unitriangular
    · right
      have h3I : 3 ∉ I := fun h => h2I (h23.mpr h)
      have hIeq : I = {1, 4} := by
        ext i
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · intro hi
          have := hIc i hi
          by_contra hcon
          have : i = 2 ∨ i = 3 := by omega
          rcases this with rfl | rfl
          · exact h2I hi
          · exact h3I hi
        · rintro (rfl | rfl)
          · exact h14 (Or.inl rfl)
          · exact h14 (Or.inr rfl)
      rw [hXeq, hIeq]

end Five

end CFSG.Quasithin.RonanE114.L52Flag

namespace CFSG.Quasithin.RonanE114

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.L239
  CFSG.Open CFSG.Quasithin CFSG.Quasithin.RonanE114.L52Flag

section Main

variable {G : Type} [Group G] [Finite G]

theorem nParam_eq_one_of_isPSL52
    {T : Subgroup G} (hL : IsPSL 5 2 1 (ASInputs.FStar G))
    (hT : quasithinIsSylowTwo T) (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    E1.nParam (⊤ : Subgroup G) = 1 := by
  have hTs : IsSylowTwoOf T ⊤ := ⟨le_top, hT.1, by
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hT.2⟩
  have hLn : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hL
  have hK : Nat.card K = 2 := by simpa using hcard
  have := Fintype.ofFinite K
  have hKc : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card]
  let σ : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hKc
  let φ : ↥(CFSG.generalizedFitting G) ≃* SpecialLinearGroup (Fin 5) (ZMod 2) :=
    e.trans ((slEquivStatedProj hK 5).symm.trans (L52.slEquivOfRingEquiv σ 5))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := ZMod 2) 2 (n := 5) (by norm_num)
  have hU : IsSylowTwoOf (unitriangular 5 (ZMod 2)) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  refine le_antisymm
    (Good.nParam_le_one_of_goodPair hU (fun 𝒜 h => l52_goodPair 𝒜 h) hLn φ hTs hFT) ?_
  refine Vol2.Ch11.SecE3.one_le_nParam_of_not_odd
    (not_odd_of_two_dvd_card (H := CFSG.generalizedFitting G) ?_)
  rw [Nat.card_congr φ.toEquiv]
  have hU' : Nat.card (unitriangular 5 (ZMod 2)) = 2 ^ 10 := by
    rw [card_unitriangular, Nat.card_zmod]
  have hdvd := Subgroup.card_subgroup_dvd_card (unitriangular 5 (ZMod 2))
  rw [hU'] at hdvd
  exact dvd_trans (dvd_pow_self 2 (by norm_num)) hdvd

end Main

end CFSG.Quasithin.RonanE114
