module

public import CFSG.Quasithin.Recognition.Stroth.MoufangLittleGen

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair CFSG.Geometry.GeneralizedPolygons

open scoped Pointwise

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]

@[simp] theorem mem_moufangB {t : ZMod (2 * n) → V} {x : ↥(littleGroup D Γ n)} :
    x ∈ moufangB D Γ n t ↔ (x : D) • t n = t n ∧ (x : D) • t (n + 1) = t (n + 1) := by
  rw [moufangB, Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff]

@[simp] theorem mem_moufangN {t : ZMod (2 * n) → V} {x : ↥(littleGroup D Γ n)} :
    x ∈ moufangN D Γ n t ↔ (x : D) • (Set.range t) = Set.range t := by
  rw [moufangN, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]

theorem smul_mem_range_of_mem_stabilizer {t : ZMod (2 * n) → V} {g : D}
    (hg : g ∈ MulAction.stabilizer D (Set.range t)) {y : V} (hy : y ∈ Set.range t) :
    g • y ∈ Set.range t := by
  have hs : g • Set.range t = Set.range t := hg
  have h := Set.smul_mem_smul_set (a := g) hy
  rwa [hs] at h

theorem moufangB_inf_moufangN_fix {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    {x : ↥(littleGroup D Γ n)} (hx : x ∈ moufangB D Γ n t ⊓ moufangN D Γ n t) :
    (x : D) ∈ fixingSubgroup D (Set.range t) := by
  have hB := mem_moufangB.mp hx.1
  have hN := mem_moufangN.mp hx.2
  rw [mem_fixingSubgroup_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := hy
  exact apt_fix_of_fix_two ht hn hP hT hN hB.1 hB.2 k

theorem conj_mem_fixingSubgroup {s : Set V} {g x : D}
    (hg : g ∈ MulAction.stabilizer D s) (hx : x ∈ fixingSubgroup D s) :
    g * x * g⁻¹ ∈ fixingSubgroup D s := by
  rw [mem_fixingSubgroup_iff] at hx ⊢
  intro y hy
  have hgy : g⁻¹ • y ∈ s := by
    have h : g • s = s := hg
    have h1 : y ∈ g • s := by rw [h]; exact hy
    rwa [Set.mem_smul_set_iff_inv_smul_mem] at h1
  calc (g * x * g⁻¹) • y = g • (x • (g⁻¹ • y)) := by rw [mul_smul, mul_smul]
    _ = g • (g⁻¹ • y) := by rw [hx _ hgy]
    _ = y := by rw [smul_inv_smul]

theorem moufangCartan_normal {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) :
    (cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal := by
  rw [cartan, Subgroup.normal_subgroupOf_iff inf_le_right]
  intro h k hh hk
  have hfix := moufangB_inf_moufangN_fix ht hn hP hT hh
  have hkfix : ((k : ↥(littleGroup D Γ n)) : D) ∈ MulAction.stabilizer D (Set.range t) :=
    mem_moufangN.mp hk
  have hconj : ((k * h * k⁻¹ : ↥(littleGroup D Γ n)) : D) ∈ fixingSubgroup D (Set.range t) := by
    have := conj_mem_fixingSubgroup (s := Set.range t) hkfix hfix
    simpa using this
  have hconj' : ∀ y ∈ Set.range t, ((k * h * k⁻¹ : ↥(littleGroup D Γ n)) : D) • y = y :=
    (mem_fixingSubgroup_iff D).mp hconj
  have hN : ((k * h * k⁻¹ : ↥(littleGroup D Γ n)) : D) ∈
      MulAction.stabilizer D (Set.range t) := by
    have h1 : ((k : ↥(littleGroup D Γ n)) : D) * ((h : ↥(littleGroup D Γ n)) : D) *
        (((k⁻¹ : ↥(littleGroup D Γ n)) : D)) ∈
        MulAction.stabilizer D (Set.range t) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hkfix (mem_moufangN.mp hh.2))
        (by simpa using Subgroup.inv_mem _ hkfix)
    simpa using h1
  refine ⟨?_, ?_⟩
  · change k * h * k⁻¹ ∈ moufangB D Γ n t
    rw [mem_moufangB]
    exact ⟨hconj' _ (Set.mem_range_self (f := t) (i := (n : ZMod (2 * n)))),
      hconj' _ (Set.mem_range_self (f := t) (i := (n : ZMod (2 * n)) + 1))⟩
  · change k * h * k⁻¹ ∈ moufangN D Γ n t
    rw [mem_moufangN]
    exact hN

theorem exists_reflection {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) {i : ℤ}
    {u : D} (hu : u ∈ aptRoot D Γ n t i) (hu1 : u ≠ 1) :
    ∃ m ∈ littleGroup D Γ n, m ∈ MulAction.stabilizer D (Set.range t) ∧
      ∀ k : ℤ, m • apt t k = apt t (2 * i - k) := by
  obtain ⟨v, hv, w, hw, hact, -⟩ :=
    exists_reflectionData (t := t) ht hn hP hT hM (i := i) (u := u) hu hu1
  have hmL : v * u * w ∈ littleGroup D Γ n :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _
      (aptRoot_le_littleGroup ht (by omega) (i + (n : ℤ)) hv)
      (aptRoot_le_littleGroup ht (by omega) i hu))
      (aptRoot_le_littleGroup ht (by omega) (i + (n : ℤ)) hw)
  have hN : (⟨v * u * w, hmL⟩ : ↥(littleGroup D Γ n)) ∈ moufangN D Γ n t :=
    reflection_mem_normalizer (t := t) hn hmL hact
  exact ⟨v * u * w, hmL,
    MulAction.mem_stabilizer_iff.mpr (mem_moufangN.mp hN), hact⟩

theorem mem_moufangB_inf_moufangN_of_fix {t : ZMod (2 * n) → V}
    {x : ↥(littleGroup D Γ n)} (hx : (x : D) ∈ fixingSubgroup D (Set.range t)) :
    x ∈ moufangB D Γ n t ⊓ moufangN D Γ n t := by
  have hfix : ∀ y ∈ Set.range t, (x : D) • y = y := (mem_fixingSubgroup_iff D).mp hx
  refine ⟨?_, ?_⟩
  · change x ∈ moufangB D Γ n t
    rw [mem_moufangB]
    exact ⟨hfix _ (Set.mem_range_self (f := t) (i := (n : ZMod (2 * n)))),
      hfix _ (Set.mem_range_self (f := t) (i := (n : ZMod (2 * n)) + 1))⟩
  · change x ∈ moufangN D Γ n t
    rw [mem_moufangN]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change (x : D) • z ∈ Set.range t
      rw [hfix z hz]
      exact hz
    · intro hy
      exact ⟨y, hy, hfix y hy⟩

theorem exists_reflection_one {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    ∃ m ∈ littleGroup D Γ n, m ∈ MulAction.stabilizer D (Set.range t) ∧
      ∀ k : ℤ, m • apt t k = apt t (2 * ((n : ℤ) + 1) - k) := by
  have hne : aptRoot D Γ n t ((n : ℤ) + 1) ≠ ⊥ :=
    aptRoot_ne_bot ht hn hP hT hM ((n : ℤ) + 1)
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hu : (u : D) ∈ aptRoot D Γ n t ((n : ℤ) + 1) := u.2
  have hu1' : (u : D) ≠ 1 := fun h => hu1 (Subtype.ext h)
  simpa using exists_reflection ht hn hP hT hM hu hu1'

theorem exists_reflection_two {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    ∃ m ∈ littleGroup D Γ n, m ∈ MulAction.stabilizer D (Set.range t) ∧
      ∀ k : ℤ, m • apt t k = apt t (2 * (n : ℤ) - k) := by
  have hne : aptRoot D Γ n t (n : ℤ) ≠ ⊥ := aptRoot_ne_bot ht hn hP hT hM (n : ℤ)
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hu : (u : D) ∈ aptRoot D Γ n t (n : ℤ) := u.2
  have hu1' : (u : D) ≠ 1 := fun h => hu1 (Subtype.ext h)
  exact exists_reflection ht hn hP hT hM hu hu1'

noncomputable def reflOne {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) : D :=
  Classical.choose (exists_reflection_one ht hn hP hT hM)

noncomputable def reflTwo {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) : D :=
  Classical.choose (exists_reflection_two ht hn hP hT hM)

theorem reflOne_mem {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    reflOne ht hn hP hT hM ∈ littleGroup D Γ n :=
  (Classical.choose_spec (exists_reflection_one ht hn hP hT hM)).1

theorem reflTwo_mem {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    reflTwo ht hn hP hT hM ∈ littleGroup D Γ n :=
  (Classical.choose_spec (exists_reflection_two ht hn hP hT hM)).1

theorem reflOne_mem_stabilizer {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    reflOne ht hn hP hT hM ∈ MulAction.stabilizer D (Set.range t) :=
  (Classical.choose_spec (exists_reflection_one ht hn hP hT hM)).2.1

theorem reflTwo_mem_stabilizer {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    reflTwo ht hn hP hT hM ∈ MulAction.stabilizer D (Set.range t) :=
  (Classical.choose_spec (exists_reflection_two ht hn hP hT hM)).2.1

theorem reflOne_smul {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) (k : ℤ) :
    reflOne ht hn hP hT hM • apt t k = apt t (2 * ((n : ℤ) + 1) - k) :=
  (Classical.choose_spec (exists_reflection_one ht hn hP hT hM)).2.2 k

theorem reflTwo_smul {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) (k : ℤ) :
    reflTwo ht hn hP hT hM • apt t k = apt t (2 * (n : ℤ) - k) :=
  (Classical.choose_spec (exists_reflection_two ht hn hP hT hM)).2.2 k

theorem reflect_sq_smul {t : ZMod (2 * n) → V} {m : D} {i : ℤ}
    (hm : ∀ k : ℤ, m • apt t k = apt t (2 * i - k)) (k : ℤ) :
    (m * m) • apt t k = apt t k := by
  rw [mul_smul, hm, hm, show 2 * i - (2 * i - k) = k by ring]

theorem reflOne_sq_fix {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    reflOne ht hn hP hT hM * reflOne ht hn hP hT hM ∈ fixingSubgroup D (Set.range t) := by
  rw [mem_fixingSubgroup_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := hy
  have hk : apt t ((k.val : ℤ)) = t k := by
    haveI : NeZero (2 * n) := ⟨by omega⟩
    show t (((k.val : ℤ) : ZMod (2 * n))) = t k
    congr 1
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [← hk]
  exact reflect_sq_smul (reflOne_smul ht hn hP hT hM) _

theorem reflTwo_sq_fix {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    reflTwo ht hn hP hT hM * reflTwo ht hn hP hT hM ∈ fixingSubgroup D (Set.range t) := by
  rw [mem_fixingSubgroup_iff]
  intro y hy
  obtain ⟨k, rfl⟩ := hy
  have hk : apt t ((k.val : ℤ)) = t k := by
    haveI : NeZero (2 * n) := ⟨by omega⟩
    show t (((k.val : ℤ) : ZMod (2 * n))) = t k
    congr 1
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [← hk]
  exact reflect_sq_smul (reflTwo_smul ht hn hP hT hM) _

theorem reflOne_mul_reflTwo_smul {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    (k : ℤ) :
    (reflOne ht hn hP hT hM * reflTwo ht hn hP hT hM) • apt t k = apt t (k + 2) := by
  rw [mul_smul, reflTwo_smul, reflOne_smul]
  congr 1
  ring

theorem reflOne_not_fix {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    reflOne ht hn hP hT hM ∉ fixingSubgroup D (Set.range t) := by
  intro h
  have hfix := (mem_fixingSubgroup_iff D).mp h
  have h2 : reflOne ht hn hP hT hM • apt t (n : ℤ) = apt t (n : ℤ) :=
    hfix (apt t (n : ℤ)) ⟨((n : ℤ) : ZMod (2 * n)), rfl⟩
  rw [reflOne_smul ht hn hP hT hM] at h2
  have hne : apt t (2 * ((n : ℤ) + 1) - (n : ℤ)) ≠ apt t (n : ℤ) := by
    have h3 := apt_ne_two (by omega : 2 ≤ n) ht (n : ℤ)
    have e : 2 * ((n : ℤ) + 1) - (n : ℤ) = (n : ℤ) + 2 := by ring
    rw [e]
    exact fun hc => h3 hc.symm
  exact hne h2

theorem reflTwo_not_fix {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    reflTwo ht hn hP hT hM ∉ fixingSubgroup D (Set.range t) := by
  intro h
  have hfix := (mem_fixingSubgroup_iff D).mp h
  have h2 : reflTwo ht hn hP hT hM • apt t ((n : ℤ) + 1) = apt t ((n : ℤ) + 1) :=
    hfix (apt t ((n : ℤ) + 1)) ⟨(((n : ℤ) + 1 : ℤ) : ZMod (2 * n)), rfl⟩
  rw [reflTwo_smul ht hn hP hT hM] at h2
  have hne : apt t (2 * (n : ℤ) - ((n : ℤ) + 1)) ≠ apt t ((n : ℤ) + 1) := by
    have e : 2 * (n : ℤ) - ((n : ℤ) + 1) = (n : ℤ) - 1 := by ring
    rw [e]
    have h3 := apt_ne_two (by omega : 2 ≤ n) ht ((n : ℤ) - 1)
    rw [show (n : ℤ) - 1 + 2 = (n : ℤ) + 1 by ring] at h3
    exact fun hc => h3 hc
  exact hne h2

end CFSG.Quasithin.Stroth
