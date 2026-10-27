module

public import CFSG.LocalAnalysis.WeakClosure81.SixTwo
public import CFSG.LocalAnalysis.WeakClosure81.SixOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mQuot_inf_right (V U : Subgroup G) : E3.mQuot V (U ⊓ V) = E3.mQuot V U := by
  unfold E3.mQuot
  rw [Subgroup.inf_relIndex_right]

theorem mQuot_inf_left (V U : Subgroup G) : E3.mQuot V (V ⊓ U) = E3.mQuot V U := by
  rw [inf_comm, mQuot_inf_right]

theorem six_ten {M V₀ V : Subgroup G} (h : Hyp62 M V₀ V) {g : G} {k j : ℕ}
    (hj : 1 ≤ j) (hO : InCalO k M V₀ V g)
    (hmin : ((k + j : ℕ) : ℕ∞) ≤
      min (betaN k M V) (rMV M V - (mSub V₀ : ℕ∞))) :
    (∀ D : Subgroup G, D ≤ conjSubgroup V g ⊓ M →
        E3.mQuot (conjSubgroup V g ⊓ M) D < j →
      V ⊓ Subgroup.centralizer (D : Set G) =
        V ⊓ Subgroup.centralizer ((conjSubgroup V g ⊓ M : Subgroup G) : Set G)) ∧
    (∀ D : Subgroup G, D ≤ conjSubgroup V g ⊓ M →
        E3.mQuot (conjSubgroup V g ⊓ M) D < j →
      V₀ ≤ V ⊓ Subgroup.centralizer (D : Set G)) ∧
    (∀ D : Subgroup G, D ≤ conjSubgroup V g ⊓ M →
        E3.mQuot (conjSubgroup V g ⊓ M) D < j →
      ∀ v ∈ V, (∀ d ∈ D, ⁅v, d⁆ ∈ V₀) →
        v ∈ Subgroup.centralizer (D : Set G)) := by
  have hkjβ : ((k + j : ℕ) : ℕ∞) ≤ betaN k M V := hmin.trans (min_le_left _ _)
  have hkjr : ((k + j : ℕ) : ℕ∞) ≤ rMV M V - (mSub V₀ : ℕ∞) := hmin.trans (min_le_right _ _)
  have hkj1 : (1 : ℕ∞) ≤ ((k + j : ℕ) : ℕ∞) := by
    exact_mod_cast (by omega : 1 ≤ k + j)
  have hle : (mSub V₀ : ℕ∞) ≤ rMV M V := by
    by_contra hlt
    rw [not_le] at hlt
    have h0 : rMV M V - (mSub V₀ : ℕ∞) = 0 := tsub_eq_zero_of_le hlt.le
    have h1 : ((k + j : ℕ) : ℕ∞) ≤ 0 := by simpa [h0] using hkjr
    have h2 : ((k + j : ℕ) : ℕ∞) = 0 :=
      le_antisymm h1 (by exact_mod_cast Nat.zero_le (k + j))
    rw [h2] at hkj1
    exact (not_le_of_gt (by norm_num : (0 : ℕ∞) < 1)) hkj1
  have hkjm : ((k + j : ℕ) : ℕ∞) + (mSub V₀ : ℕ∞) ≤ rMV M V :=
    add_le_of_le_tsub_right_of_le hle hkjr
  have key : ∀ D : Subgroup G, D ≤ conjSubgroup V g ⊓ M →
      E3.mQuot (conjSubgroup V g ⊓ M) D < j →
      ((V ⊓ Subgroup.centralizer (D : Set G) =
          V ⊓ Subgroup.centralizer ((conjSubgroup V g ⊓ M : Subgroup G) : Set G)) ∧
        V₀ ≤ V ⊓ Subgroup.centralizer (D : Set G) ∧
        (∀ v ∈ V, (∀ d ∈ D, ⁅v, d⁆ ∈ V₀) → v ∈ Subgroup.centralizer (D : Set G))) := by
    intro D hDB hDlt
    have hBle : (conjSubgroup V g ⊓ M : Subgroup G) ≤ conjSubgroup V g := inf_le_left
    have hmB : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ M) ≤ k := by
      rw [mQuot_inf_left]
      exact hO.2.2.1
    have hmQuotD : E3.mQuot (conjSubgroup V g) D < k + j := by
      rw [E3.mQuot_add hDB hBle]
      omega
    have hr : ((E3.mQuot (conjSubgroup V g) D + mSub V₀ : ℕ) : ℕ∞) < rMV M V := by
      have hcast : ((E3.mQuot (conjSubgroup V g) D + mSub V₀ : ℕ) : ℕ∞) =
          (E3.mQuot (conjSubgroup V g) D : ℕ∞) + (mSub V₀ : ℕ∞) := by
        rw [Nat.cast_add]
      rw [hcast]
      exact lt_of_lt_of_le
        ((ENat.add_lt_add_iff_right (ENat.natCast_ne_top (mSub V₀))).mpr
          (by exact_mod_cast hmQuotD)) hkjm
    have hcomm : ⁅preCTilde V₀ V D h.isElemAbelian, D⁆ = ⊥ :=
      six_two_two h hDB hr (Or.inl hO.1.1)
    have hpreC : preCTilde V₀ V D h.isElemAbelian ≤ Subgroup.centralizer (D : Set G) := by
      have hcomm' := Subgroup.commutator_le.mp (le_of_eq hcomm)
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h1 : ⁅u, d⁆ = 1 := by simpa using hcomm' u hu d hd
      exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
    have hV0_le : V₀ ≤ V ⊓ Subgroup.centralizer (D : Set G) :=
      le_inf h.le ((le_preCTilde h.isElemAbelian h.le).trans hpreC)
    have helem : ∀ v ∈ V, (∀ d ∈ D, ⁅v, d⁆ ∈ V₀) → v ∈ Subgroup.centralizer (D : Set G) := by
      intro v hv hvD
      exact hpreC ((mem_preCTilde_iff h.isElemAbelian (h.le_stabTil hDB) hv).2 hvD)
    have hβ : (E3.mQuot (conjSubgroup V g) D : ℕ∞) <
        betaN (E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ M)) M V :=
      lt_of_lt_of_le (by exact_mod_cast hmQuotD) (hkjβ.trans (betaN_anti hmB))
    have hcommB : ⁅V ⊓ Subgroup.centralizer (D : Set G), conjSubgroup V g ⊓ M⁆ = ⊥ :=
      six_two_three h hDB hr hO.2.1 hβ
    have hCVD_le : V ⊓ Subgroup.centralizer (D : Set G) ≤
        V ⊓ Subgroup.centralizer ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) := by
      have hcommB' := Subgroup.commutator_le.mp (le_of_eq hcommB)
      intro x hx
      exact Subgroup.mem_inf.mpr ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun b hb => by
        have h1 : ⁅x, b⁆ = 1 := by simpa using hcommB' x hx b hb
        exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm⟩
    have hCVB_le : V ⊓ Subgroup.centralizer ((conjSubgroup V g ⊓ M : Subgroup G) : Set G) ≤
        V ⊓ Subgroup.centralizer (D : Set G) :=
      inf_le_inf_left V (Subgroup.centralizer_le hDB)
    exact ⟨le_antisymm hCVD_le hCVB_le, hV0_le, helem⟩
  exact ⟨fun D hDB hDlt => (key D hDB hDlt).1,
    fun D hDB hDlt => (key D hDB hDlt).2.1,
    fun D hDB hDlt => (key D hDB hDlt).2.2⟩

theorem preTil_injective (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    Function.Injective (preTil V₀ V hV) := by
  intro S T h
  rw [← imgTil_preTil V₀ V hV S, h, imgTil_preTil V₀ V hV T]

theorem preCTilde_bot_eq {V D : Subgroup G} (hV : IsElemAbelian 2 V)
    (hD : D ≤ stabTil ⊥ V) :
    preCTilde ⊥ V D hV = V ⊓ Subgroup.centralizer (D : Set G) := by
  apply le_antisymm
  · intro u hu
    refine ⟨preCTilde_le ⊥ V D hV hu, ?_⟩
    exact Subgroup.mem_centralizer_iff.2 fun d hd => by
      have h1 : ⁅u, d⁆ = 1 := by
        have := (mem_preCTilde_iff hV hD (preCTilde_le ⊥ V D hV hu)).1 hu d hd
        simpa using this
      exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  · intro u hu
    exact (mem_preCTilde_iff hV hD hu.1).2 fun d hd => by
      have h1 : ⁅u, d⁆ = 1 := by
        exact commutatorElement_eq_one_iff_mul_comm.2
          (Subgroup.mem_centralizer_iff.1 hu.2 d hd).symm
      simpa using h1

end CFSG.LocalAnalysis.WeakClosure81
