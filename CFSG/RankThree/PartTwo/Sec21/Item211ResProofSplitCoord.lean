module

public import CFSG.RankThree.PartTwo.Sec21.Item211ResProofSplitBase
public import CFSG.RankThree.SubgroupLists.SchurCommutant

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2130SplitProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] {k : ℕ}

@[expose] noncomputable def glEquivK (k : ℕ) :
    GL (Fin k) (ZMod 3) ≃* ((Fin k → ZMod 3) ≃ₗ[ZMod 3] (Fin k → ZMod 3)) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

theorem glEquivK_apply (g : GL (Fin k) (ZMod 3)) (v : Fin k → ZMod 3) :
    glEquivK k g v = (g : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ v := by
  simp [glEquivK, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv]

@[expose] noncomputable def matB {B : Subgroup G} (f : Multiplicative (Fin k → ZMod 3) ≃* B) :
    Subgroup.normalizer (B : Set G) →* GL (Fin k) (ZMod 3) :=
  (glEquivK k).symm.toMonoidHom.comp ((Sec12.coordHom f).comp B.normalizerMonoidHom)

@[expose] def coordB {B : Subgroup G} (f : Multiplicative (Fin k → ZMod 3) ≃* B) (b : B) :
    Fin k → ZMod 3 :=
  Multiplicative.toAdd (f.symm b)

@[expose] def eltB {B : Subgroup G} (f : Multiplicative (Fin k → ZMod 3) ≃* B)
    (v : Fin k → ZMod 3) : G :=
  ((f (Multiplicative.ofAdd v) : B) : G)

theorem eltB_mem {B : Subgroup G} (f : Multiplicative (Fin k → ZMod 3) ≃* B)
    (v : Fin k → ZMod 3) : eltB f v ∈ B :=
  (f (Multiplicative.ofAdd v)).2

theorem eltB_coordB {B : Subgroup G} (f : Multiplicative (Fin k → ZMod 3) ≃* B) (b : B) :
    eltB f (coordB f b) = b := by
  simp [eltB, coordB]

theorem eltB_injective {B : Subgroup G} (f : Multiplicative (Fin k → ZMod 3) ≃* B) :
    Function.Injective (eltB f) := fun _ _ e =>
  Multiplicative.ofAdd.injective (f.injective (Subtype.ext e))

theorem eltB_zero {B : Subgroup G} (f : Multiplicative (Fin k → ZMod 3) ≃* B) :
    eltB f 0 = 1 := by
  simp [eltB]

theorem eltB_eq_one_iff {B : Subgroup G} (f : Multiplicative (Fin k → ZMod 3) ≃* B)
    (v : Fin k → ZMod 3) : eltB f v = 1 ↔ v = 0 := by
  rw [← eltB_zero f]
  exact (eltB_injective f).eq_iff

theorem exists_eltB {B : Subgroup G} (f : Multiplicative (Fin k → ZMod 3) ≃* B) {b : G}
    (hb : b ∈ B) : ∃ v, eltB f v = b :=
  ⟨coordB f ⟨b, hb⟩, by rw [eltB_coordB]⟩

theorem eltB_matB {B : Subgroup G} (f : Multiplicative (Fin k → ZMod 3) ≃* B)
    (n : Subgroup.normalizer (B : Set G)) (v : Fin k → ZMod 3) :
    eltB f (((matB f n : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ v) =
      (n : G) * eltB f v * (n : G)⁻¹ := by
  have h1 : ((matB f n : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ v =
      Sec12.coordHom f (B.normalizerMonoidHom n) v := by
    rw [← glEquivK_apply]
    simp [matB]
  rw [h1, Sec12.coordHom_apply]
  simp only [eltB, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  rfl

@[expose] noncomputable def M1 {B : Subgroup G} (N : Subgroup G)
    (f : Multiplicative (Fin k → ZMod 3) ≃* B) : Subgroup (GL (Fin k) (ZMod 3)) :=
  (N.subgroupOf (Subgroup.normalizer (B : Set G))).map (matB f)

namespace SplitHyp

variable {A B N : Subgroup G} (h : SplitHyp A B N)
include h

abbrev nb {n : G} (hn : n ∈ N) : Subgroup.normalizer (B : Set G) := ⟨n, h.normB hn⟩

theorem matB_mem_M1 (f : Multiplicative (Fin k → ZMod 3) ≃* B) {n : G} (hn : n ∈ N) :
    matB f (h.nb hn) ∈ M1 N f :=
  ⟨h.nb hn, hn, rfl⟩

theorem exists_of_mem_M1 (f : Multiplicative (Fin k → ZMod 3) ≃* B)
    {g : GL (Fin k) (ZMod 3)} (hg : g ∈ M1 N f) : ∃ n, ∃ hn : n ∈ N, matB f (h.nb hn) = g := by
  obtain ⟨⟨n, hnB⟩, hn, rfl⟩ := hg
  exact ⟨n, hn, rfl⟩

theorem conj_eltB_eq_iff (f : Multiplicative (Fin k → ZMod 3) ≃* B) {n : G} (hn : n ∈ N)
    (v : Fin k → ZMod 3) :
    n * eltB f v * n⁻¹ = eltB f v ↔
      ((matB f (h.nb hn) : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ v = v := by
  rw [← eltB_matB f (h.nb hn) v]
  exact (eltB_injective f).eq_iff

theorem trivial_on_B_iff (f : Multiplicative (Fin k → ZMod 3) ≃* B) {n : G} (hn : n ∈ N) :
    (∀ b ∈ B, n * b * n⁻¹ = b) ↔ matB f (h.nb hn) = 1 := by
  constructor
  · intro hB
    apply Units.ext
    ext i j
    have h1 := (h.conj_eltB_eq_iff f hn (Pi.single j 1)).mp (hB _ (eltB_mem f _))
    have h2 := congrFun h1 i
    rw [Matrix.mulVec_single_one] at h2
    rw [Units.val_one]
    simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h2
  · intro h1 b hb
    obtain ⟨v, rfl⟩ := exists_eltB f hb
    rw [h.conj_eltB_eq_iff f hn, h1, Units.val_one, Matrix.one_mulVec]

theorem conj_eq_on_B_of_matB_eq (f : Multiplicative (Fin k → ZMod 3) ≃* B) {n m : G}
    (hn : n ∈ N) (hm : m ∈ N) (e : matB f (h.nb hn) = matB f (h.nb hm)) :
    ∀ b ∈ B, n * b * n⁻¹ = m * b * m⁻¹ := by
  intro b hb
  obtain ⟨v, rfl⟩ := exists_eltB f hb
  have h1 := eltB_matB f (h.nb hn) v
  have h2 := eltB_matB f (h.nb hm) v
  rw [e] at h1
  exact h1.symm.trans h2

theorem conj_eq_of_matB_eq (f : Multiplicative (Fin k → ZMod 3) ≃* B)
    (hfB : ∀ w ∈ N, (∀ b ∈ B, w * b * w⁻¹ = b) → ∀ a ∈ A, w * a * w⁻¹ = a) {n m : G}
    (hn : n ∈ N) (hm : m ∈ N) (e : matB f (h.nb hn) = matB f (h.nb hm)) :
    ∀ a ∈ A, n * a * n⁻¹ = m * a * m⁻¹ :=
  SplitHyp.conj_eq_of_conj_eq hn hm hfB (h.conj_eq_on_B_of_matB_eq f hn hm e)

theorem trivQ_of_matB_pow [Finite G] (f : Multiplicative (Fin k → ZMod 3) ≃* B)
    (hfB : ∀ w ∈ N, (∀ b ∈ B, w * b * w⁻¹ = b) → ∀ a ∈ A, w * a * w⁻¹ = a) {n : G}
    (hn : n ∈ N) {j : ℕ} (hj : matB f (h.nb hn) ^ (2 * j + 1) = 1) : TrivQ A B n := by
  have hp : n ^ (2 * j + 1) ∈ N := N.pow_mem hn _
  have he : matB f (h.nb hp) = matB f (h.nb hn) ^ (2 * j + 1) := by
    rw [← map_pow]
    rfl
  refine h.trivQ_of_pow_odd hn (j := j) (hfB _ hp ((h.trivial_on_B_iff f hp).mpr ?_))
  rw [he, hj]

theorem isIrreducibleOn_M1 (f : Multiplicative (Fin k → ZMod 3) ≃* B) :
    CFSG.RankThree.SubgroupLists.IsIrreducibleOn (M1 N f) := by
  intro W hW
  set Y : Subgroup G :=
    ((AddSubgroup.toSubgroup W.toAddSubgroup).map f.toMonoidHom).map B.subtype with hY
  have hmem : ∀ v, eltB f v ∈ Y ↔ v ∈ W := by
    intro v
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, hxv⟩
      have : x = Multiplicative.ofAdd v :=
        f.injective (Subtype.ext hxv)
      rw [this] at hx
      exact hx
    · intro hv
      exact ⟨f (Multiplicative.ofAdd v), ⟨Multiplicative.ofAdd v, hv, rfl⟩, rfl⟩
  have hYB : Y ≤ B := Subgroup.map_subtype_le _
  have hYN : N ≤ Subgroup.normalizer (Y : Set G) := by
    refine le_normalizer_of_forall fun n hn y hy => ?_
    obtain ⟨v, rfl⟩ := exists_eltB f (hYB hy)
    rw [← eltB_matB f (h.nb hn) v, hmem]
    exact hW _ (h.matB_mem_M1 f hn) v ((hmem v).mp hy)
  rcases h.irr Y hYB hYN with h0 | h1
  · left
    rw [eq_bot_iff]
    intro v hv
    have := (hmem v).mpr hv
    rw [h0, Subgroup.mem_bot, eltB_eq_one_iff] at this
    rw [Submodule.mem_bot]
    exact this
  · right
    rw [eq_top_iff]
    intro v _
    rw [← hmem, h1]
    exact eltB_mem f v

theorem concl_of_matSet [Finite G] (f : Multiplicative (Fin k → ZMod 3) ≃* B)
    (Y : Set (GL (Fin k) (ZMod 3)))
    (hYN : ∀ m (hm : m ∈ N), ∀ y ∈ Y, matB f (h.nb hm) * y * (matB f (h.nb hm))⁻¹ ∈ Y)
    (hY1 : ∀ v : Fin k → ZMod 3, (∀ r (hr : r ∈ N), matB f (h.nb hr) ∈ Y →
      ((matB f (h.nb hr) : GL (Fin k) (ZMod 3)) : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ v = v) →
        v = 0)
    {c : G} (hcA : c ∈ A) (hcB : c ∉ B)
    (hRc : ∀ r (hr : r ∈ N), matB f (h.nb hr) ∈ Y → r * c * r⁻¹ = c) : SplitConcl A B N := by
  refine h.exists_of_fixSet {r | ∃ hr : r ∈ N, matB f (h.nb hr) ∈ Y} ?_ hcA hcB ?_ ?_
  · intro b hb hR
    obtain ⟨v, rfl⟩ := exists_eltB f hb
    rw [hY1 v fun r hr hrY => (h.conj_eltB_eq_iff f hr v).mp (hR r ⟨hr, hrY⟩), eltB_zero]
  · rintro r ⟨hr, hrY⟩
    exact hRc r hr hrY
  · rintro m hm r ⟨hr, hrY⟩
    have hmr : m * r * m⁻¹ ∈ N := N.mul_mem (N.mul_mem hm hr) (N.inv_mem hm)
    refine ⟨m * r * m⁻¹, ⟨hmr, ?_⟩, fun a _ => rfl⟩
    rw [show h.nb hmr = h.nb hm * h.nb hr * (h.nb hm)⁻¹ from rfl, map_mul, map_mul, map_inv]
    exact hYN m hm _ hrY

end SplitHyp

end CFSG.RankThree.PartTwo.Sec21.Item2130SplitProof
