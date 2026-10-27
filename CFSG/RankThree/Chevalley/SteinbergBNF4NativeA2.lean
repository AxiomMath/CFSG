module

public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeA2Rep

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix SteinbergBN

inductive F4A2Kind
  | long
  | short

namespace F4A2Kind

@[expose] def i : F4A2Kind → Fin Tag.F4.rank
  | long => 0
  | short => 2

@[expose] def j : F4A2Kind → Fin Tag.F4.rank
  | long => 1
  | short => 3

end F4A2Kind

variable (K : Type) [Field K]

@[expose] def f4A2Rep :
    (κ : F4A2Kind) → subsystemGroup Tag.F4 K {κ.i, κ.j} →* Matrix.SpecialLinearGroup (Fin 3) K
  | .long => f4LongRep K
  | .short => f4ShortRep K

theorem isElemRep_f4A2Rep
    (κ : F4A2Kind) : IsElemRep K κ.i κ.j (f4A2Rep K κ) := by
  cases κ
  · exact isElemRep_f4LongRep
  · exact isElemRep_f4ShortRep

theorem not_mem_pair_of_ne {s i j : Fin Tag.F4.rank} (hi : s ≠ i) (hj : s ≠ j) :
    s ∉ ({i, j} : Set (Fin Tag.F4.rank)) := by
  rintro (h | h)
  · exact hi h
  · exact hj h

theorem range_f4LongPos
    : Set.range f4LongPos = parabolicPosRoots Tag.F4 {0, 1} := by
  obtain ⟨hroot, hout, hall, -⟩ := f4LongPos_checks
  ext α
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := hroot a
    have hα : IsRoot Tag.F4 (f4LongPos a) := isRoot_F4_iff.2 ⟨k, hk⟩
    refine ⟨⟨hα, fun s hs => ?_⟩, hα, (hout a).2.2⟩
    have h23 : s = 2 ∨ s = 3 := by
      have hs' : ¬(s = 0 ∨ s = 1) := hs
      revert s
      decide
    rcases h23 with rfl | rfl
    · exact (hout a).1
    · exact (hout a).2.1
  · rintro ⟨⟨hα, hz⟩, -, hpos⟩
    obtain ⟨k, rfl⟩ := isRoot_F4_iff.1 hα
    exact hall k (hz 2 (not_mem_pair_of_ne (by decide) (by decide)))
      (hz 3 (not_mem_pair_of_ne (by decide) (by decide))) hpos

theorem range_f4ShortPos
    : Set.range f4ShortPos = parabolicPosRoots Tag.F4 {2, 3} := by
  obtain ⟨hroot, hout, hall, -⟩ := f4ShortPos_checks
  ext α
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := hroot a
    have hα : IsRoot Tag.F4 (f4ShortPos a) := isRoot_F4_iff.2 ⟨k, hk⟩
    refine ⟨⟨hα, fun s hs => ?_⟩, hα, (hout a).2.2⟩
    have h01 : s = 0 ∨ s = 1 := by
      have hs' : ¬(s = 2 ∨ s = 3) := hs
      revert s
      decide
    rcases h01 with rfl | rfl
    · exact (hout a).1
    · exact (hout a).2.1
  · rintro ⟨⟨hα, hz⟩, -, hpos⟩
    obtain ⟨k, rfl⟩ := isRoot_F4_iff.1 hα
    exact hall k (hz 0 (not_mem_pair_of_ne (by decide) (by decide)))
      (hz 1 (not_mem_pair_of_ne (by decide) (by decide))) hpos

theorem f4A2Rep_bijective
    (κ : F4A2Kind) : Function.Bijective (f4A2Rep K κ) := by
  refine ⟨?_, (isElemRep_f4A2Rep K κ).surjective⟩
  cases κ
  · obtain ⟨-, -, -, hinj, h0, h1, h2⟩ := f4LongPos_checks
    exact isElemRep_f4LongRep.injective hinj range_f4LongPos h0 h1 h2
      fun g hg => f4LongRep_mem_subsystemBorel hg
  · obtain ⟨-, -, -, hinj, h0, h1, h2⟩ := f4ShortPos_checks
    exact isElemRep_f4ShortRep.injective hinj range_f4ShortPos h0 h1 h2
      fun g hg => f4ShortRep_mem_subsystemBorel hg

@[expose] def f4A2Equiv
    (κ : F4A2Kind) :
    subsystemGroup Tag.F4 K {κ.i, κ.j} ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
  MulEquiv.ofBijective (f4A2Rep K κ) (f4A2Rep_bijective K κ)

theorem f4A2Equiv_apply
    (κ : F4A2Kind) (g : subsystemGroup Tag.F4 K {κ.i, κ.j}) :
    f4A2Equiv K κ g = f4A2Rep K κ g :=
  rfl

theorem isElemRep_of_matrix
    {i j : Fin Tag.F4.rank}
    {φ : subsystemGroup Tag.F4 K {i, j} →* Matrix.SpecialLinearGroup (Fin 3) K}
    (h : ∀ c : K,
      ((φ (qx (left_mem_pair i j) c) : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 + single 0 1 c ∧
      ((φ (qy (left_mem_pair i j) c) : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 + single 1 0 c ∧
      ((φ (qx (right_mem_pair i j) c) : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 + single 1 2 c ∧
      ((φ (qy (right_mem_pair i j) c) : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 + single 2 1 c) : IsElemRep K i j φ := fun c =>
  ⟨Subtype.ext (h c).1, Subtype.ext (h c).2.1, Subtype.ext (h c).2.2.1, Subtype.ext (h c).2.2.2⟩

theorem F4_native_long_and_short_A2_faithful_SL3_all_characteristics
    (κ : F4A2Kind) :
    (∀ c : K,
      ((f4A2Equiv K κ (qx (left_mem_pair κ.i κ.j) c) : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 + single 0 1 c ∧
      ((f4A2Equiv K κ (qy (left_mem_pair κ.i κ.j) c) : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 + single 1 0 c ∧
      ((f4A2Equiv K κ (qx (right_mem_pair κ.i κ.j) c) : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 + single 1 2 c ∧
      ((f4A2Equiv K κ (qy (right_mem_pair κ.i κ.j) c) : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = 1 + single 2 1 c) ∧
    (∀ φ : subsystemGroup Tag.F4 K {κ.i, κ.j} →* Matrix.SpecialLinearGroup (Fin 3) K,
      (∀ c : K,
        ((φ (qx (left_mem_pair κ.i κ.j) c) : Matrix.SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = 1 + single 0 1 c ∧
        ((φ (qy (left_mem_pair κ.i κ.j) c) : Matrix.SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = 1 + single 1 0 c ∧
        ((φ (qx (right_mem_pair κ.i κ.j) c) : Matrix.SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = 1 + single 1 2 c ∧
        ((φ (qy (right_mem_pair κ.i κ.j) c) : Matrix.SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) = 1 + single 2 1 c) →
      ∀ g, φ g = f4A2Equiv K κ g) ∧
    (∀ t u : Kˣ,
      ((f4A2Equiv K κ ⟨torusElt Tag.F4 K κ.i t * torusElt Tag.F4 K κ.j u,
          torusElt_pair_mem κ.i κ.j t u⟩ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = diagonal ![(t : K), (t : K)⁻¹ * u, (u : K)⁻¹]) ∧
    subsystemGroup Tag.F4 K {κ.i, κ.j} = rootSpan Tag.F4 K (parabolicRoots Tag.F4 {κ.i, κ.j}) ∧
    (∀ g : ModGL Tag.F4 K, g ∈ subsystemGroup Tag.F4 K {κ.i, κ.j} ⊓ torusGroup Tag.F4 K ↔
      ∃ t u : Kˣ, g = torusElt Tag.F4 K κ.i t * torusElt Tag.F4 K κ.j u) ∧
    (∀ (L : Type) [Field L] (σ : K →+* L) (g : subsystemGroup Tag.F4 K {κ.i, κ.j}),
      ∃ hσ : baseChangeGL σ (g : ModGL Tag.F4 K) ∈ subsystemGroup Tag.F4 L {κ.i, κ.j},
        ((f4A2Equiv L κ ⟨_, hσ⟩ : Matrix.SpecialLinearGroup (Fin 3) L) :
          Matrix (Fin 3) (Fin 3) L) =
        ((f4A2Equiv K κ g : Matrix.SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K).map σ) ∧
    ∀ h ∈ torusGroup Tag.F4 K, ∀ a b : K,
      (h : Module.End K (RootModule Tag.F4 K)) (rootVec Tag.F4 K (Pi.single κ.i 1)) =
        a • rootVec Tag.F4 K (Pi.single κ.i 1) →
      (h : Module.End K (RootModule Tag.F4 K)) (rootVec Tag.F4 K (Pi.single κ.j 1)) =
        b • rootVec Tag.F4 K (Pi.single κ.j 1) →
      ∃ hN : ∀ z ∈ subsystemGroup Tag.F4 K {κ.i, κ.j},
          h * z * h⁻¹ ∈ subsystemGroup Tag.F4 K {κ.i, κ.j},
        ∀ z : subsystemGroup Tag.F4 K {κ.i, κ.j},
          ((f4A2Equiv K κ ⟨h * z * h⁻¹, hN z z.2⟩ : Matrix.SpecialLinearGroup (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) =
          diagonal ![a * b, b, 1] *
            ((f4A2Equiv K κ z : Matrix.SpecialLinearGroup (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K) * (diagonal ![a * b, b, 1])⁻¹ := by
  have hr := isElemRep_f4A2Rep K κ
  refine ⟨fun c => ?_, fun φ hφ g => ?_, fun t u => hr.torus t u, subsystemGroup_eq_rootSpan _,
    fun g => ?_, fun L _ σ g => ⟨baseChangeGL_mem_subsystemGroup σ g.2, ?_⟩,
    fun h hh a b ha hb => ?_⟩
  · simp only [f4A2Equiv_apply, (hr c).1, (hr c).2.1, (hr c).2.2.1, (hr c).2.2.2,
      CFSG.LinearGroups.coe_transvection, and_self]
  · rw [f4A2Equiv_apply, (isElemRep_of_matrix K hφ).ext hr]
  · rw [subsystemGroup_inf_torusGroup, mem_subsystemTorus_pair]
  · have e := hr.map σ (isElemRep_f4A2Rep L κ) g
    rw [f4A2Equiv_apply, f4A2Equiv_apply]
    have e' : (⟨baseChangeGL σ (g : ModGL Tag.F4 K), baseChangeGL_mem_subsystemGroup σ g.2⟩ :
        subsystemGroup Tag.F4 L {κ.i, κ.j}) = baseChangeQ σ {κ.i, κ.j} g := rfl
    rw [e', e, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  · have hconj := hr.conj hh ha hb
    obtain ⟨ha0, -, -⟩ := conj_xUnit_of_apply_single hh ha
    obtain ⟨hb0, -, -⟩ := conj_xUnit_of_apply_single hh hb
    refine ⟨fun z hz => (hconj z hz).1, fun z => ?_⟩
    obtain ⟨hm, hD⟩ := hconj z z.2
    have hdet : IsUnit (diagonal ![a * b, b, 1]).det := by
      rw [Matrix.det_diagonal, Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, mul_one]
      exact (mul_ne_zero (mul_ne_zero ha0 hb0) hb0).isUnit
    rw [f4A2Equiv_apply, f4A2Equiv_apply]
    have hz : (⟨(z : ModGL Tag.F4 K), z.2⟩ : subsystemGroup Tag.F4 K {κ.i, κ.j}) = z := rfl
    rw [hz] at hD
    rw [hD, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]

end CFSG.RankThree.Chevalley
