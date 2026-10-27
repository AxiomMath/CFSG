module

public import CFSG.Monster.B.TwoA.Amalgam.EightOrbitsQuot
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Planes
public import CFSG.Monster.B.E6.StdF4Fiber

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.E6.StdF4
open CFSG.Fischer CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.TwoA.Unitary
open CFSG.Monster.B.Co2 (v0)

theorem fibOrbit_subset_rootClass
    (d : Fin 5) :
    fibOrbit d ⊆ SemidirectProduct.inl '' rootClass := by
  rw [fibOrbit_eq]
  rintro _ ⟨_, ⟨g, -, rfl⟩, rfl⟩
  exact ⟨_, (mem_rootClass_iff _).2 ⟨g, rfl⟩, rfl⟩

theorem fibOrbit_disjoint
    {d d' : Fin 5} (h : d ≠ d') : Disjoint (fibOrbit d) (fibOrbit d') := by
  rw [Set.disjoint_left]
  intro y hy hy'
  have e1 := conjOrbit_eq_of_mem hy
  have e2 := conjOrbit_eq_of_mem hy'
  have e3 : fibOrbit d = fibOrbit d' := e1.symm.trans e2
  have e4 := congrArg Set.ncard e3
  rw [ncard_fibOrbit, ncard_fibOrbit] at e4
  exact h (repSize_injective e4)

theorem existsUnique_mem_fibOrbit
    {y : GStar} (hy : y ∈ SemidirectProduct.inl '' rootClass) :
    ∃! d : Fin 5, y ∈ fibOrbit d := by
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨d, hd⟩ := exists_mem_fibOrbit hx
  refine ⟨d, hd, fun d' hd' => ?_⟩
  by_contra hne
  exact Set.disjoint_left.1 (fibOrbit_disjoint hne) hd' hd

theorem fibOrbit_zero :
    fibOrbit 0 = {rootStar} := by
  obtain ⟨d, hd⟩ := exists_mem_fibOrbit (show rootInv ∈ rootClass from IsConj.refl _)
  have hc : conjOrbit (parStar firstJ) rootStar = {rootStar} := by
    ext y
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      rw [← centralizer_rootStar] at hγ
      refine Set.mem_singleton_iff.2 ?_
      rw [Subgroup.mem_centralizer_singleton_iff.1 hγ, mul_inv_cancel_right]
    · rintro rfl
      exact mem_conjOrbit_self _ _
  have e : fibOrbit d = {rootStar} := (conjOrbit_eq_of_mem hd).symm.trans hc
  have hd0 : d = 0 := by
    have h := ncard_fibOrbit d
    rw [e, Set.ncard_singleton] at h
    exact repSize_injective (show repSize d = repSize 0 from h.symm.trans rfl)
  subst hd0
  exact e

@[expose] def quotOrb (d : Fin 5) (c : ℕ) : Set (Submodule F4 V6) :=
  if d = 2 then ptOrbit c else plOrbit c

@[expose] def quotOrbSize (d : Fin 5) (c : ℕ) : ℕ :=
  if d = 2 then (if c = 0 then 126 else 567) else (if c = 0 then 324 else 567)

theorem quotOrb_facts
    {d : Fin 5} :
    {S | UIso (quotDim d) S} = quotOrb d 0 ∪ quotOrb d 1 ∧ Disjoint (quotOrb d 0) (quotOrb d 1) ∧
      (∀ c < 2, ∀ P ∈ quotOrb d c, orbitA P = quotOrb d c) ∧
      (∀ c < 2, (quotOrb d c).ncard = quotOrbSize d c) := by
  obtain ⟨-, -, hpt, hptU, hptD, hpt0, hpt1, hpl, hplU, hplD, hpl0, hpl1, -, -, -⟩ :=
    native_unitary_1408_stabilizer_point_plane_orbits
  unfold quotOrb quotDim quotOrbSize
  split_ifs
  · refine ⟨hptU, hptD, hpt, fun c hc => ?_⟩
    interval_cases c
    · exact hpt0
    · exact hpt1
  · refine ⟨hplU, hplD, hpl, fun c hc => ?_⟩
    interval_cases c
    · exact hpl0
    · exact hpl1

@[expose] def midSet
    (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar) (d : Fin 5) (c : ℕ) : Set GStar :=
  {y | y ∈ fibOrbit d ∧ nquot θ d y ∈ quotOrb d c}

@[expose] def eightLevel : Fin 8 → Fin 5 := ![1, 2, 3, 0, 1, 2, 3, 4]

@[expose] def eightIdx : Fin 8 → ℕ := ![0, 0, 0, 0, 1, 1, 1, 0]

@[expose] def eightSet
    (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar) (i : Fin 8) : Set GStar :=
  if eightLevel i = 0 ∨ eightLevel i = 4 then fibOrbit (eightLevel i)
  else midSet θ (eightLevel i) (eightIdx i)

@[expose] def eightSize : Fin 8 → ℕ := ![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152]

theorem eightIdx_lt (i : Fin 8) : eightIdx i < 2 := by
  revert i
  decide

theorem isMid_of_not_JJ {d : Fin 5} (h : ¬ (d = 0 ∨ d = 4)) : IsMid d := by
  unfold IsMid
  revert h
  revert d
  decide

theorem isMid_eightLevel {i : Fin 8} (h : ¬ (eightLevel i = 0 ∨ eightLevel i = 4)) :
    IsMid (eightLevel i) :=
  isMid_of_not_JJ h

theorem eightSet_eq_of_JJ
    {i : Fin 8} (h : eightLevel i = 0 ∨ eightLevel i = 4) (θ) :
    eightSet θ i = fibOrbit (eightLevel i) := ite_eq_left h

theorem eightSet_eq_of_mid
    {i : Fin 8} (h : ¬ (eightLevel i = 0 ∨ eightLevel i = 4)) (θ) :
    eightSet θ i = midSet θ (eightLevel i) (eightIdx i) := ite_eq_right h

theorem eightSet_subset_fibOrbit
    (θ) (i : Fin 8) : eightSet θ i ⊆ fibOrbit (eightLevel i) := by
  unfold eightSet
  split_ifs
  · exact le_rfl
  · exact fun _ hy => hy.1

theorem eightSet_subset_rootClass
    (θ) (i : Fin 8) :
    eightSet θ i ⊆ SemidirectProduct.inl '' rootClass :=
  (eightSet_subset_fibOrbit θ i).trans (fibOrbit_subset_rootClass _)

theorem eq_of_eightLevel {i j : Fin 8} (h : eightLevel i = eightLevel j)
    (h' : eightLevel i = 0 ∨ eightLevel i = 4 ∨ eightIdx i = eightIdx j) : i = j := by
  revert h h'
  revert i j
  decide

section Count

variable {θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar} {f : Chamber ≃ C2E6Std.stdChamber}
  (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
    stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
  (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
  (hfB : f baseChamber = c₀)

include hadj hfeq hfB in
theorem fibOrbit_eq_union_midSet
    {d : Fin 5} (hd : IsMid d) :
    fibOrbit d = midSet θ d 0 ∪ midSet θ d 1 := by
  ext y
  constructor
  · intro hy
    have h := uIso_nquot hadj hfeq hfB hd hy
    have h' : nquot θ d y ∈ {S | UIso (quotDim d) S} := h
    rw [quotOrb_facts.1] at h'
    rcases h' with h0 | h1
    · exact Or.inl ⟨hy, h0⟩
    · exact Or.inr ⟨hy, h1⟩
  · rintro (⟨hy, -⟩ | ⟨hy, -⟩) <;> exact hy

theorem disjoint_midSet
    {d : Fin 5} : Disjoint (midSet θ d 0) (midSet θ d 1) :=
  Set.disjoint_left.2 fun _ h0 h1 => Set.disjoint_left.1 quotOrb_facts.2.1 h0.2 h1.2

include hadj hfeq hfB in
theorem midSet_nonempty
    {d : Fin 5} (hd : IsMid d) {c : ℕ} (hc : c < 2) :
    (midSet θ d c).Nonempty := by
  have hpos : 0 < (quotOrb d c).ncard := by
    rw [quotOrb_facts.2.2.2 c hc]
    unfold quotOrbSize
    split_ifs <;> decide
  obtain ⟨S, hS⟩ := Set.nonempty_of_ncard_ne_zero hpos.ne'
  have hS' : S ∈ nquot θ d '' fibOrbit d := by
    rw [image_nquot hadj hfeq hfB hd, quotOrb_facts.1]
    interval_cases c
    · exact Or.inl hS
    · exact Or.inr hS
  obtain ⟨y, hy, hyS⟩ := hS'
  exact ⟨y, hy, by rw [hyS]; exact hS⟩

variable {k : Jhat} (hk0 : cvOf (jhatS k) ≠ cv0) (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k)))
  (hτ : psiW (labE k) = tauW)

include hk0 hk hτ in
theorem setOf_sigmaAct_q4P
    (P : Submodule F4 V6) :
    {S | ∃ q ∈ q4P k, sigmaAct P (rhoP1 q) = S} = orbitA P := by
  have hmap := map_Q4 hk0 hk
  rw [hτ] at hmap
  ext S
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨p1Proj ⟨q, q.2⟩, ?_, by rw [rhoP1_apply]⟩
    have h : jhatToKv0 ⟨q, P1_le_Jhat q.2⟩ ∈ Usig ⊓ wStab tauW := by
      rw [← hmap]
      exact ⟨⟨q, P1_le_Jhat q.2⟩, hq, rfl⟩
    exact h.2
  · rintro ⟨a, ha, rfl⟩
    have h : (a : Kstab v0) ∈ ((Q4 k).subgroupOf Jhat).map jhatToKv0 := by
      rw [hmap]
      exact ⟨a.2, ha⟩
    obtain ⟨g, hg, hga⟩ := h
    have hgP : (g : Dfull) ∈ Pc 0 := Q4_le_P1 hg
    refine ⟨⟨g, hgP⟩, hg, ?_⟩
    rw [rhoP1_apply]
    congr 2
    exact Subtype.ext hga

include hadj hfeq hfB hk0 hk hτ in
theorem conjOrbit_eq_midSet
    {d : Fin 5} (hd : IsMid d) {c : ℕ} (hc : c < 2) {x : GStar}
    (hx : x ∈ midSet θ d c) : conjOrbit ((q4P k).map (rho1 θ)) x = midSet θ d c := by
  rw [conjOrbit_eq_of_mid hadj hfeq hfB (radStar_le_map_q4P hk0 hk hadj hfeq hfB) hd hx.1]
  have e := setOf_sigmaAct_q4P hk0 hk hτ (nquot θ d x)
  rw [quotOrb_facts.2.2.1 c hc _ hx.2] at e
  ext y
  constructor
  · rintro ⟨hy, q, hq, hqy⟩
    refine ⟨hy, ?_⟩
    rw [← e]
    exact ⟨q, hq, hqy⟩
  · rintro ⟨hy, hyc⟩
    rw [← e] at hyc
    obtain ⟨q, hq, hqy⟩ := hyc
    exact ⟨hy, q, hq, hqy⟩

include hadj hfeq hfB hk0 hk hτ in
theorem ncard_midSet
    {d : Fin 5} (hd : IsMid d) {c : ℕ} (hc : c < 2) :
    (midSet θ d c).ncard = fibUSize d * quotOrbSize d c := by
  obtain ⟨x, hx⟩ := midSet_nonempty hadj hfeq hfB hd hc
  rw [← conjOrbit_eq_midSet hadj hfeq hfB hk0 hk hτ hd hc hx,
    ncard_conjOrbit_of_mid hadj hfeq hfB (radStar_le_map_q4P hk0 hk hadj hfeq hfB) hd hx.1,
    setOf_sigmaAct_q4P hk0 hk hτ, quotOrb_facts.2.2.1 c hc _ hx.2, quotOrb_facts.2.2.2 c hc]

include hadj hfeq hfB hk0 hk hτ in
theorem eightSet_eq_conjOrbit
    (i : Fin 8) :
    ∃ x ∈ eightSet θ i, eightSet θ i = conjOrbit ((q4P k).map (rho1 θ)) x := by
  by_cases h : eightLevel i = 0 ∨ eightLevel i = 4
  · rw [eightSet_eq_of_JJ h]
    refine ⟨_, mem_conjOrbit_self _ _, (conjOrbit_eq_of_JJ hadj hfeq hfB
      (radStar_le_map_q4P hk0 hk hadj hfeq hfB) h (mem_conjOrbit_self _ _)).symm⟩
  · rw [eightSet_eq_of_mid h]
    obtain ⟨x, hx⟩ := midSet_nonempty hadj hfeq hfB (isMid_eightLevel h) (eightIdx_lt i)
    exact ⟨x, hx, (conjOrbit_eq_midSet hadj hfeq hfB hk0 hk hτ (isMid_eightLevel h)
      (eightIdx_lt i) hx).symm⟩

include hadj hfeq hfB hk0 hk hτ in
theorem ncard_eightSet
    (i : Fin 8) : (eightSet θ i).ncard = eightSize i := by
  by_cases h : eightLevel i = 0 ∨ eightLevel i = 4
  · rw [eightSet_eq_of_JJ h, ncard_fibOrbit]
    revert h
    fin_cases i <;> decide
  · rw [eightSet_eq_of_mid h, ncard_midSet hadj hfeq hfB hk0 hk hτ (isMid_eightLevel h)
      (eightIdx_lt i)]
    revert h
    fin_cases i <;> decide

include hadj hfeq hfB in
theorem existsUnique_mem_eightSet
    {y : GStar} (hy : y ∈ SemidirectProduct.inl '' rootClass) :
    ∃! i, y ∈ eightSet θ i := by
  obtain ⟨d, hd, hdu⟩ := existsUnique_mem_fibOrbit hy
  have hex : ∃ i, y ∈ eightSet θ i := by
    by_cases hJJ : d = 0 ∨ d = 4
    · rcases hJJ with rfl | rfl
      · exact ⟨3, by rw [eightSet_eq_of_JJ (i := 3) (by decide)]; exact hd⟩
      · exact ⟨7, by rw [eightSet_eq_of_JJ (i := 7) (by decide)]; exact hd⟩
    · have hmid : IsMid d := isMid_of_not_JJ hJJ
      rw [fibOrbit_eq_union_midSet hadj hfeq hfB hmid] at hd
      rcases hmid with rfl | rfl | rfl
      · rcases hd with h0 | h1
        · exact ⟨0, by rw [eightSet_eq_of_mid (i := 0) (by decide)]; exact h0⟩
        · exact ⟨4, by rw [eightSet_eq_of_mid (i := 4) (by decide)]; exact h1⟩
      · rcases hd with h0 | h1
        · exact ⟨1, by rw [eightSet_eq_of_mid (i := 1) (by decide)]; exact h0⟩
        · exact ⟨5, by rw [eightSet_eq_of_mid (i := 5) (by decide)]; exact h1⟩
      · rcases hd with h0 | h1
        · exact ⟨2, by rw [eightSet_eq_of_mid (i := 2) (by decide)]; exact h0⟩
        · exact ⟨6, by rw [eightSet_eq_of_mid (i := 6) (by decide)]; exact h1⟩
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, hi, fun j hj => ?_⟩
  change y ∈ eightSet θ j at hj
  have hli : eightLevel i = d := hdu _ (eightSet_subset_fibOrbit θ i hi)
  have hlj : eightLevel j = d := hdu _ (eightSet_subset_fibOrbit θ j hj)
  refine eq_of_eightLevel (hlj.trans hli.symm) ?_
  by_cases hJJ : eightLevel j = 0 ∨ eightLevel j = 4
  · rcases hJJ with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · right; right
    have hJJ' : ¬ (eightLevel i = 0 ∨ eightLevel i = 4) := by rwa [hli, ← hlj]
    rw [eightSet_eq_of_mid hJJ] at hj
    rw [eightSet_eq_of_mid hJJ'] at hi
    have hd' : eightLevel j = eightLevel i := hlj.trans hli.symm
    rw [hd'] at hj
    have hji := eightIdx_lt j
    have hii := eightIdx_lt i
    by_contra hne
    have h01 : (eightIdx j = 0 ∧ eightIdx i = 1) ∨ (eightIdx j = 1 ∧ eightIdx i = 0) := by omega
    rcases h01 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at hj
      rw [h2] at hi
      exact Set.disjoint_left.1 disjoint_midSet hj hi
    · rw [h1] at hj
      rw [h2] at hi
      exact Set.disjoint_left.1 disjoint_midSet hi hj

include hadj hfeq hfB in
theorem fibOrbit_eq_eightSet :
    fibOrbit 0 = eightSet θ 3 ∧ fibOrbit 1 = eightSet θ 0 ∪ eightSet θ 4 ∧
      fibOrbit 2 = eightSet θ 1 ∪ eightSet θ 5 ∧ fibOrbit 3 = eightSet θ 2 ∪ eightSet θ 6 ∧
      fibOrbit 4 = eightSet θ 7 := by
  refine ⟨(eightSet_eq_of_JJ (i := 3) (by decide) θ).symm, ?_, ?_, ?_,
    (eightSet_eq_of_JJ (i := 7) (by decide) θ).symm⟩
  · rw [eightSet_eq_of_mid (i := 0) (by decide), eightSet_eq_of_mid (i := 4) (by decide)]
    exact fibOrbit_eq_union_midSet hadj hfeq hfB (Or.inl rfl)
  · rw [eightSet_eq_of_mid (i := 1) (by decide), eightSet_eq_of_mid (i := 5) (by decide)]
    exact fibOrbit_eq_union_midSet hadj hfeq hfB (Or.inr (Or.inl rfl))
  · rw [eightSet_eq_of_mid (i := 2) (by decide), eightSet_eq_of_mid (i := 6) (by decide)]
    exact fibOrbit_eq_union_midSet hadj hfeq hfB (Or.inr (Or.inr rfl))

end Count

end CFSG.Monster.B.TwoA.Amalgam
