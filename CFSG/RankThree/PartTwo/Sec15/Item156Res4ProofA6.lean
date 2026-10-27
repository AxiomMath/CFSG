module

public import CFSG.RankThree.PartTwo.KFacts.K412AlternatingSix
public import CFSG.RankThree.Native.ONTripleA6

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof156Res4

attribute [local irreducible] dotProduct

open Equiv Subgroup CFSG.RankThree.Native.ONTriple

@[expose] def IsA6Signal (t : Perm (Fin 6)) (V : Subgroup (Perm (Fin 6))) : Prop :=
  V ≤ alternatingGroup (Fin 6) ∧ (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ (∀ v ∈ V, v ^ 2 = 1) ∧
    t ∈ normalizer (V : Set (Perm (Fin 6)))

@[expose] def a6SignalSet (t : Perm (Fin 6)) : Set (Perm (Fin 6)) :=
  {x | ∃ V : Subgroup (Perm (Fin 6)), IsA6Signal t V ∧ x ∈ V}

theorem mem_normalizer_of_conj_le {X : Type*} [Group X] {t : X} (ht3 : t ^ 3 = 1)
    {V : Subgroup X} (hV : ∀ v ∈ V, t * v * t⁻¹ ∈ V) : t ∈ normalizer (V : Set X) := by
  refine mem_normalizer_iff.mpr fun h => ⟨hV h, fun hh => ?_⟩
  have h1 := hV _ (hV _ hh)
  have h3 : t * t * t = 1 := by rw [← pow_three', ht3]
  have e : t * (t * (t * h * t⁻¹) * t⁻¹) * t⁻¹ = h := by
    calc t * (t * (t * h * t⁻¹) * t⁻¹) * t⁻¹ = (t * t * t) * h * (t * t * t)⁻¹ := by group
      _ = h := by rw [h3]; group
  rwa [e] at h1

theorem closure_pair_props {X : Type*} [Group X] {t x : X} (ht3 : t ^ 3 = 1) (hx2 : x ^ 2 = 1)
    (hc : x * (t * x * t⁻¹) = t * x * t⁻¹ * x)
    (hcl : x * (t * x * t⁻¹) = t * (t * x * t⁻¹) * t⁻¹) :
    (∀ v ∈ closure ({x, t * x * t⁻¹} : Set X), ∀ w ∈ closure ({x, t * x * t⁻¹} : Set X),
      v * w = w * v) ∧ (∀ v ∈ closure ({x, t * x * t⁻¹} : Set X), v ^ 2 = 1) ∧
      t ∈ normalizer (closure ({x, t * x * t⁻¹} : Set X) : Set X) := by
  set y := t * x * t⁻¹ with hy
  have hpair : ({x, y} : Set X).Pairwise Commute := by
    intro a ha b hb _
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hc
    · exact hc.symm
    · exact Commute.refl _
  have hcomm : IsMulCommutative (closure ({x, y} : Set X)) :=
    Subgroup.isMulCommutative_closure hpair
  have hcomm' : ∀ v ∈ closure ({x, y} : Set X), ∀ w ∈ closure ({x, y} : Set X),
      v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨v, hv⟩ ⟨w, hw⟩)
  have hy2 : y ^ 2 = 1 := by
    rw [hy, sq, show t * x * t⁻¹ * (t * x * t⁻¹) = t * (x * x) * t⁻¹ by group, ← sq, hx2]
    group
  refine ⟨hcomm', fun v hv => ?_, mem_normalizer_of_conj_le ht3 fun v hv => ?_⟩
  · induction hv using Subgroup.closure_induction with
    | mem a ha =>
      rcases ha with rfl | rfl
      · exact hx2
      · exact hy2
    | one => exact one_pow 2
    | mul a b ha hb iha ihb =>
      have hab : Commute a b := hcomm' a ha b hb
      rw [hab.mul_pow, iha, ihb, one_mul]
    | inv a _ iha => rw [inv_pow, iha, inv_one]
  ·
    have hle : closure ({x, y} : Set X) ≤
        (closure ({x, y} : Set X)).comap (MulAut.conj t).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rcases ha with rfl | rfl
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      · rw [← hcl]
        exact mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
    have := hle hv
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem mem_a6SignalSet_of {t x : Perm (Fin 6)} (htA : t ∈ alternatingGroup (Fin 6))
    (ht3 : t ^ 3 = 1) (hxA : x ∈ alternatingGroup (Fin 6)) (hx2 : x ^ 2 = 1)
    (hc : x * (t * x * t⁻¹) = t * x * t⁻¹ * x)
    (hcl : x * (t * x * t⁻¹) = t * (t * x * t⁻¹) * t⁻¹) : x ∈ a6SignalSet t := by
  obtain ⟨h1, h2, h3⟩ := closure_pair_props ht3 hx2 hc hcl
  refine ⟨closure ({x, t * x * t⁻¹} : Set (Perm (Fin 6))), ⟨?_, h1, h2, h3⟩,
    Subgroup.subset_closure (Set.mem_insert _ _)⟩
  rw [Subgroup.closure_le]
  rintro a (rfl | rfl)
  · exact hxA
  · exact mul_mem (mul_mem htA hxA) (inv_mem htA)

theorem conj_mem_a6SignalSet {t x : Perm (Fin 6)} (hx : x ∈ a6SignalSet t) (g : Perm (Fin 6)) :
    g * x * g⁻¹ ∈ a6SignalSet (g * t * g⁻¹) := by
  obtain ⟨V, ⟨hVA, hVc, hV2, htV⟩, hxV⟩ := hx
  refine ⟨V.map (MulAut.conj g).toMonoidHom, ⟨?_, ?_, ?_, ?_⟩, ⟨x, hxV, rfl⟩⟩
  · rintro _ ⟨v, hv, rfl⟩
    have hn : (alternatingGroup (Fin 6)).Normal := inferInstance
    exact hn.conj_mem v (hVA hv) g
  · rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g * v * g⁻¹ * (g * w * g⁻¹) = g * (v * w) * g⁻¹ by group, hVc v hv w hw]
    group
  · rintro _ ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [sq, show g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ by group, ← sq, hV2 v hv]
    group
  · rw [Subgroup.mem_normalizer_iff] at htV ⊢
    intro h
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨t * v * t⁻¹, (htV v).mp hv, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro ⟨v, hv, hvh⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hvh
      refine ⟨t⁻¹ * v * t, (htV _).mpr ?_, ?_⟩
      · rwa [show t * (t⁻¹ * v * t) * t⁻¹ = v by group]
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have e : h = (g * t * g⁻¹)⁻¹ * (g * v * g⁻¹) * (g * t * g⁻¹) := by
          rw [hvh]
          group
        rw [e]
        group

theorem le_closure_of_conj {t : Perm (Fin 6)} (g : Perm (Fin 6))
    (h : alternatingGroup (Fin 6) ≤ closure (a6SignalSet (g * t * g⁻¹))) :
    alternatingGroup (Fin 6) ≤ closure (a6SignalSet t) := by
  intro x hx
  have hn : (alternatingGroup (Fin 6)).Normal := inferInstance
  have h1 : g * x * g⁻¹ ∈ closure (a6SignalSet (g * t * g⁻¹)) := h (hn.conj_mem x hx g)
  have hle : closure (a6SignalSet (g * t * g⁻¹)) ≤
      (closure (a6SignalSet t)).comap (MulAut.conj g⁻¹).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro y hy
    have := conj_mem_a6SignalSet hy g⁻¹
    rw [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
    exact Subgroup.subset_closure this
  have h2 := hle h1
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h2

theorem sK_mem_closure_zero :
    sK1 ∈ closure (a6SignalSet (sY 0)) ∧ sK2 ∈ closure (a6SignalSet (sY 0)) := by
  have htA : sY 0 ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  have ht3 : sY 0 ^ 3 = 1 := by decide +kernel
  have hmem : ∀ x : Perm (Fin 6), Perm.sign x = 1 → x ^ 2 = 1 →
      x * (sY 0 * x * (sY 0)⁻¹) = sY 0 * x * (sY 0)⁻¹ * x →
      x * (sY 0 * x * (sY 0)⁻¹) = sY 0 * (sY 0 * x * (sY 0)⁻¹) * (sY 0)⁻¹ →
      x ∈ closure (a6SignalSet (sY 0)) := fun x hs hx2 hc hcl =>
    Subgroup.subset_closure
      (mem_a6SignalSet_of htA ht3 (Equiv.Perm.mem_alternatingGroup.mpr hs) hx2 hc hcl)
  have m1 := hmem (swap 0 4 * swap 1 2) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have m2 := hmem (swap 0 1 * swap 2 3) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have m3 := hmem (swap 0 2 * swap 1 4) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have m4 := hmem (swap 0 3 * swap 1 2) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have m5 := hmem (swap 0 5 * swap 1 2) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  refine ⟨?_, ?_⟩
  · have e : sK1 = (swap 0 4 * swap 1 2) * (swap 0 1 * swap 2 3) * (swap 0 2 * swap 1 4) := by
      decide +kernel
    rw [e]
    exact mul_mem (mul_mem m1 m2) m3
  · have e : sK2 = (swap 0 1 * swap 2 3) * (swap 0 4 * swap 1 2) * (swap 0 3 * swap 1 2) *
        (swap 0 5 * swap 1 2) := by
      decide +kernel
    rw [e]
    exact mul_mem (mul_mem (mul_mem m2 m1) m4) m5

theorem sK_mem_closure_one :
    sK1 ∈ closure (a6SignalSet (sY 1)) ∧ sK2 ∈ closure (a6SignalSet (sY 1)) := by
  have htA : sY 1 ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  have ht3 : sY 1 ^ 3 = 1 := by decide +kernel
  have hmem : ∀ x : Perm (Fin 6), Perm.sign x = 1 → x ^ 2 = 1 →
      x * (sY 1 * x * (sY 1)⁻¹) = sY 1 * x * (sY 1)⁻¹ * x →
      x * (sY 1 * x * (sY 1)⁻¹) = sY 1 * (sY 1 * x * (sY 1)⁻¹) * (sY 1)⁻¹ →
      x ∈ closure (a6SignalSet (sY 1)) := fun x hs hx2 hc hcl =>
    Subgroup.subset_closure
      (mem_a6SignalSet_of htA ht3 (Equiv.Perm.mem_alternatingGroup.mpr hs) hx2 hc hcl)
  have m1 := hmem (swap 1 3 * swap 2 5) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have m2 := hmem (swap 1 5 * swap 2 4) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  have m3 := hmem (swap 0 5 * swap 1 4) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  refine ⟨?_, ?_⟩
  · have e : sK1 = (swap 1 3 * swap 2 5) * (swap 1 5 * swap 2 4) * (swap 0 5 * swap 1 4) *
        (swap 1 5 * swap 2 4) := by
      decide +kernel
    rw [e]
    exact mul_mem (mul_mem (mul_mem m1 m2) m3) m2
  · have e : sK2 = (swap 0 5 * swap 1 4) * (swap 1 3 * swap 2 5) := by
      decide +kernel
    rw [e]
    exact mul_mem m3 m1

theorem le_closure_sY {j : ℕ} (hj : j = 0 ∨ j = 1) :
    alternatingGroup (Fin 6) ≤ closure (a6SignalSet (sY j)) := by
  rw [← closure_sK_eq_alt, Subgroup.closure_le]
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
  rcases hj with rfl | rfl
  · rcases hg with rfl | rfl
    · exact sK_mem_closure_zero.1
    · exact sK_mem_closure_zero.2
  · rcases hg with rfl | rfl
    · exact sK_mem_closure_one.1
    · exact sK_mem_closure_one.2

theorem exists_conj_sY_of_sixF : ∀ i j : Fin 3, (i, j) ≠ (0, 0) →
    ∃ h : Perm (Fin 6), h * KFacts.K412.sixF i j * h⁻¹ = sY 0 ∨
      h * KFacts.K412.sixF i j * h⁻¹ = sY 1 := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact ⟨swap 0 3 * swap 1 5 * swap 2 4, Or.inl (by decide +kernel)⟩
  · exact ⟨swap 0 3 * swap 1 4 * swap 2 5, Or.inl (by decide +kernel)⟩
  · exact ⟨swap 1 2, Or.inl (by decide +kernel)⟩
  · exact ⟨swap 1 2, Or.inr (by decide +kernel)⟩
  · exact ⟨swap 1 2 * swap 4 5, Or.inr (by decide +kernel)⟩
  · exact ⟨1, Or.inl (by decide +kernel)⟩
  · exact ⟨1, Or.inr (by decide +kernel)⟩
  · exact ⟨swap 4 5, Or.inr (by decide +kernel)⟩

theorem alternatingGroup_le_closure_signal {t : Perm (Fin 6)}
    (htA : t ∈ alternatingGroup (Fin 6)) (ht3 : t ^ 3 = 1) :
    alternatingGroup (Fin 6) ≤ closure (a6SignalSet t) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases ht1 : t = 1
  · subst ht1
    refine (le_closure_sY (Or.inl rfl)).trans (closure_mono fun x hx => ?_)
    obtain ⟨V, ⟨h1, h2, h3, -⟩, hxV⟩ := hx
    exact ⟨V, ⟨h1, h2, h3, Subgroup.one_mem _⟩, hxV⟩
  have htp : IsPGroup 3 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime ht3 ht1)
  have hE0 : IsPGroup 3 KFacts.K412.eSix :=
    IsPGroup.of_card (n := 2) (by rw [KFacts.K412.card_eSix]; norm_num)
  obtain ⟨g, hg⟩ := KFacts.K412.exists_conj_le_sylow htp
    (hE0.toSylow (KFacts.K412.not_three_dvd_index_six KFacts.K412.card_eSix))
  have hgt : g * t * g⁻¹ ∈ KFacts.K412.eSix := by
    have : (MulAut.conj g).toMonoidHom t ∈ (zpowers t).map (MulAut.conj g).toMonoidHom :=
      mem_map_of_mem _ (mem_zpowers t)
    have h := hg this
    simpa using h
  obtain ⟨i, j, hij⟩ := hgt
  have hij0 : (i, j) ≠ (0, 0) := by
    rintro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    apply ht1
    have e : g * t * g⁻¹ = 1 := by rw [hij]; decide +kernel
    have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [this, e]
    group
  obtain ⟨h, hh⟩ := exists_conj_sY_of_sixF i j hij0
  refine le_closure_of_conj (h * g) ?_
  have e : h * g * t * (h * g)⁻¹ = h * (g * t * g⁻¹) * h⁻¹ := by group
  rw [e, hij]
  rcases hh with hh | hh
  · rw [hh]
    exact le_closure_sY (Or.inl rfl)
  · rw [hh]
    exact le_closure_sY (Or.inr rfl)

end CFSG.RankThree.PartTwo.Sec15.Proof156Res4
