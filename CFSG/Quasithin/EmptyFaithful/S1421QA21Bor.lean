module

public import CFSG.Quasithin.EmptyFaithful.S1421QA21Lie

public section

namespace CFSG.Quasithin.QA21

open CFSG.Assembly.LowTwoRank CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6
  CFSG.Quasithin CFSG.Quasithin.Rk2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def SolvableOvergroupsNormalize (X : Type) [Group X] (U : Subgroup X) : Prop :=
  ∀ A : Subgroup X, U ≤ A → Group.IsSolvable ↥A → A ≤ Subgroup.normalizer (U : Set X)

theorem SolvableOvergroupsNormalize.map {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {U : Subgroup X} (h : SolvableOvergroupsNormalize X U) :
    SolvableOvergroupsNormalize Y (U.map e.toMonoidHom) := by
  intro A hUA hA
  have hsymm : ∀ B : Subgroup Y, (B.map e.symm.toMonoidHom).map e.toMonoidHom = B := fun B => by
    rw [Subgroup.map_map]
    have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by ext; simp
    rw [this, Subgroup.map_id]
  have hsymm' : ∀ B : Subgroup X, (B.map e.toMonoidHom).map e.symm.toMonoidHom = B := fun B => by
    rw [Subgroup.map_map]
    have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X := by ext; simp
    rw [this, Subgroup.map_id]
  have h1 : U ≤ A.map e.symm.toMonoidHom := by
    have := Subgroup.map_mono (f := e.symm.toMonoidHom) hUA
    rwa [hsymm'] at this
  have hs : Group.IsSolvable ↥(A.map e.symm.toMonoidHom) :=
    map_isSolvable_equiv e.symm A hA
  have h2 := h _ h1 hs
  rw [← hsymm A, ← Subgroup.map_equiv_normalizer_eq U e]
  exact Subgroup.map_mono h2

theorem SolvableOvergroupsNormalize.of_isSylow {X : Type} [Group X] [Finite X] {U₀ U : Subgroup X}
    (h : SolvableOvergroupsNormalize X U₀) (hU₀ : IsSylowTwoOf U₀ ⊤) (hU : IsSylowTwoOf U ⊤) :
    SolvableOvergroupsNormalize X U := by
  obtain ⟨k, -, hk⟩ := (isSylowTwoOf_iff_isSylowOf.1 hU₀).exists_mem_conj
    (isSylowTwoOf_iff_isSylowOf.1 hU)
  have hconj : U₀.map (MulAut.conj k).toMonoidHom = U := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  have := h.map (MulAut.conj k)
  rwa [hconj] at this

theorem SolvableOvergroupsNormalize.of_equiv {X C : Type} [Group X] [Group C] [Finite X] [Finite C]
    (e : X ≃* C) {U₀ : Subgroup C} (h : SolvableOvergroupsNormalize C U₀)
    (hU₀ : IsSylowTwoOf U₀ ⊤) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    SolvableOvergroupsNormalize X U := by
  have h1 := h.map e.symm
  have h2 : IsSylowTwoOf (U₀.map e.symm.toMonoidHom) ⊤ :=
    CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_map_top e.symm hU₀
  exact h1.of_isSylow h2 hU

theorem solvableOvergroupsNormalize_sl3 {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    SolvableOvergroupsNormalize (Matrix.SpecialLinearGroup (Fin 3) K) (unitriangular 3 K) := by
  intro A hUA hA a ha
  have h1 := SzN2.sl3_le_upperTriangular_of_solvable (exists_finset_card_four_of_pow hK hn)
    hUA hA ha
  rwa [← normalizer_unitriangular] at h1

theorem solvableOvergroupsNormalize_of_isSL3 {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    (hX : IsSL3 (2 ^ n) X) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    SolvableOvergroupsNormalize X U := by
  obtain ⟨K, hF, hFin, hcard, ⟨e⟩⟩ := hX
  have hcard' : Nat.card K = 2 ^ n := hcard
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard'
  exact SolvableOvergroupsNormalize.of_equiv (e.trans (specialLinearGroupEquivStatedSL 3 K).symm)
    (solvableOvergroupsNormalize_sl3 hcard' hn) (SzN2.isSylowTwoOf_unitriangular (by norm_num)) hU

theorem solvableOvergroupsNormalize_of_isPSL3 {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 2 ≤ n) (hX : IsPSL 3 2 n X) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    SolvableOvergroupsNormalize X U := by
  obtain ⟨P, -, hE⟩ := rank2PkgExt_exists_psl3 hn hX hU
  exact fun A hUA hA => hE.solvable_le_normalizer A hUA hA

theorem solvableOvergroupsNormalize_of_isPSp4 {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 2 ≤ n) (hX : IsPSp4 2 n X) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    SolvableOvergroupsNormalize X U := by
  obtain ⟨P, hP⟩ := borelPkg_sp4 hn hX hU
  exact hP.solv

theorem solvableOvergroupsNormalize_of_big3
    {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 2 ≤ n)
    (hX : IsSL3 (2 ^ n) X ∨ IsPSp4 2 n X ∨ IsG2 2 n X) {U : Subgroup X} (hU : IsSylowTwoOf U ⊤) :
    SolvableOvergroupsNormalize X U := by
  rcases hX with h | h | h
  · exact solvableOvergroupsNormalize_of_isSL3 hn h hU
  · exact solvableOvergroupsNormalize_of_isPSp4 hn h hU
  · obtain ⟨P, hP⟩ := borelPkg_g2 h hU
    exact hP.solv

end CFSG.Quasithin.QA21
