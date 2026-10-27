module

public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitLinearGeometry
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup Matrix Module CFSG.Open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Phan (Su blockEmb)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Steinberg (fixedSubfield)
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary (coordBlockSU mem_coordBlockSU_iff)
open scoped MatrixGroups
open CFSG.ComponentClassification.AS81.Sec2

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

@[expose] noncomputable def unitaryFrameBlock (F : Type) [Field F] [Finite F]
    (p f m : ℕ) [Fact p.Prime] [CharP F p] (k : Fin (m + 1)) (tail : ℕ := 0) :
    Subgroup (Su F p f (2 * m + 1 + 1 + tail)) :=
  (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by omega)).range

@[expose] noncomputable def unitaryFrameInvolution (F : Type) [Field F] [Finite F]
    (p f m : ℕ) [Fact p.Prime] [CharP F p] (k : Fin (m + 1)) (tail : ℕ := 0) :
    Su F p f (2 * m + 1 + 1 + tail) :=
  blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by omega) (negOneSU F p f)

theorem isLongRootSU2_unitaryFrameBlock {m : ℕ}
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (k : Fin (m + 1)) (tail : ℕ := 0) :
    IsLongRootSU2 F p f (by omega) (unitaryFrameBlock F p f m k tail)
      (unitaryFrameInvolution F p f m k tail) :=
  isLongRootSU2_range_blockEmb hF hp2 (by omega)

theorem suMat_unitaryFrameInvolution {m tail : ℕ} (k : Fin (m + 1)) :
    suMat (unitaryFrameInvolution F p f m k tail) = negBlock F (2 * m + 1 + 1 + tail) (2 * k.val) := by
  rw [unitaryFrameInvolution, suMat_blockEmb, suMat_negOneSU]
  rfl

theorem mem_minusSpace_unitaryFrameInvolution {m tail : ℕ}
    (h2 : (2 : F) ≠ 0) (k : Fin (m + 1)) {v : Fin (2 * m + 1 + 1 + tail) → F} :
    v ∈ minusSpaceSU (unitaryFrameInvolution F p f m k tail) ↔
      ∀ a : Fin (2 * m + 1 + 1 + tail),
        ¬ (2 * k.val ≤ a.val ∧ a.val < 2 * k.val + 2) → v a = 0 := by
  change v ∈ eigSpace (suMat (unitaryFrameInvolution F p f m k tail)) (-1) ↔ _
  rw [suMat_unitaryFrameInvolution]
  exact mem_eigSpace_negBlock_neg_one_iff h2 _

theorem mem_fixSpace_unitaryFrameInvolution {m tail : ℕ}
    (h2 : (2 : F) ≠ 0) (k : Fin (m + 1)) {v : Fin (2 * m + 1 + 1 + tail) → F} :
    v ∈ fixSpaceSU (unitaryFrameInvolution F p f m k tail) ↔
      ∀ a : Fin (2 * m + 1 + 1 + tail), 2 * k.val ≤ a.val →
        a.val < 2 * k.val + 2 → v a = 0 := by
  change v ∈ eigSpace (suMat (unitaryFrameInvolution F p f m k tail)) 1 ↔ _
  rw [suMat_unitaryFrameInvolution]
  exact (mem_eigSpace_negBlock_one_iff h2 _).trans (by aesop)

theorem commutes_unitaryFrameBlock {m tail : ℕ} {k j : Fin (m + 1)} (hkj : k ≠ j) :
    Commutes (unitaryFrameBlock F p f m k tail) (unitaryFrameBlock F p f m j tail) := by
  rintro a ⟨A, rfl⟩ b ⟨B, rfl⟩
  exact CFSG.ClassicalInvolution.Phan.blockEmb_comm (by omega) (by omega) (by
    have hval : k.val ≠ j.val := fun h => hkj (Fin.ext h)
    omega) A B

theorem nonempty_equiv_sl2_unitaryFrameBlock {m tail : ℕ}
    (hF : Nat.card F = (p ^ f) ^ 2) (k : Fin (m + 1)) :
    Nonempty (unitaryFrameBlock F p f m k tail ≃* SL(2, fixedSubfield F p f)) := by
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_su_two hF
  exact ⟨((MonoidHom.ofInjective (CFSG.ClassicalInvolution.Phan.blockEmb_injective
    (by omega : 2 * k.val + 2 ≤ 2 * m + 1 + 1 + tail))).symm).trans e.symm⟩

theorem eigenspaces_of_commutes_unitaryFrameBlock {m tail : ℕ}
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hn3 : 3 ≤ 2 * m + 1 + 1 + tail)
    {L : Subgroup (Su F p f (2 * m + 1 + 1 + tail))}
    {z : Su F p f (2 * m + 1 + 1 + tail)}
    (hL : IsLongRootSU2 F p f (by omega) L z) (j : Fin (m + 1))
    (hc : Commutes L (unitaryFrameBlock F p f m j tail)) :
    minusSpaceSU z ≤ fixSpaceSU (unitaryFrameInvolution F p f m j tail) ∧
      minusSpaceSU (unitaryFrameInvolution F p f m j tail) ≤ fixSpaceSU z := by
  have hne : L ≠ unitaryFrameBlock F p f m j tail := by
    intro heq
    rw [heq] at hc
    obtain ⟨e⟩ := nonempty_equiv_sl2_unitaryFrameBlock (m := m) (tail := tail) hF j
    obtain ⟨a, ha, b, hb, hab⟩ := F14.exists_noncommuting_map_of_equiv_sl2
      (MonoidHom.id _) (by simp) e
    exact hab (hc a ha b hb)
  have h := CFSG.ClassicalInvolution.RouteD.Exotic.le_of_commutes_su hF hp2 hn3 hL
    (isLongRootSU2_unitaryFrameBlock hF hp2 j tail) hne hc
  exact ⟨h.1, h.2.1⟩

theorem mem_coordBlockSU_of_smul_single {n : ℕ} {I : Finset (Fin n)}
    (x : Su F p f n)
    (hx : ∀ j : Fin n, j ∉ I → x • (Pi.single j 1 : Fin n → F) = Pi.single j 1) :
    x ∈ coordBlockSU F p f I := by
  have hcol : ∀ j : Fin n, j ∉ I → ∀ i, suMat x i j =
      (1 : Matrix (Fin n) (Fin n) F) i j := by
    intro j hj i
    have h := congrFun (hx j hj) i
    simpa [suMat_smul, Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using h
  rw [mem_coordBlockSU_iff]
  intro i j hij
  change suMat x i j = if i = j then 1 else 0
  rcases hij with hi | hj
  · have hM : CFSG.LieType.Universal.Unitary.conjTr (unitaryInvolution F p f) (suMat x) *
        suMat x = 1 := x.2.2
    have h := congrArg (fun v => CFSG.LieType.Universal.Unitary.conjTr
      (unitaryInvolution F p f) (suMat x) *ᵥ v) (hx i hi)
    rw [suMat_smul, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec] at h
    have hrow : unitaryInvolution F p f (suMat x i j) = (Pi.single i 1 : Fin n → F) j := by
      simpa [Matrix.mulVec_single_one, CFSG.LieType.Universal.Unitary.conjTr] using (congrFun h j).symm
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      apply (unitaryInvolution F p f).injective
      simpa using hrow
    · rw [if_neg hij]
      apply (map_eq_zero_iff _ (unitaryInvolution F p f).injective).mp
      simpa [Pi.single_apply, Ne.symm hij] using hrow
  · simpa [Matrix.one_apply] using hcol j hj i

theorem mem_coordBlockSU_iff_smul_single {n : ℕ} {I : Finset (Fin n)} (x : Su F p f n) :
    x ∈ coordBlockSU F p f I ↔
      ∀ j : Fin n, j ∉ I → x • (Pi.single j 1 : Fin n → F) = Pi.single j 1 := by
  constructor
  · intro hx j hj
    have h := (mem_coordBlockSU_iff.mp hx)
    ext i
    change (suMat x *ᵥ Pi.single j 1) i = _
    rw [Matrix.mulVec_single_one]
    exact (h i j (Or.inr hj)).trans (by simp [Pi.single_apply, eq_comm])
  · exact mem_coordBlockSU_of_smul_single x

theorem mem_coordBlockSU_iff_suToSL {n : ℕ} {I : Finset (Fin n)} (x : Su F p f n) :
    x ∈ coordBlockSU F p f I ↔ suToSL (unitaryInvolution F p f) n x ∈
      CFSG.SeitzReduction.LinearPilot.blockSpecialLinear I := by
  rw [mem_coordBlockSU_iff, CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear]
  rfl

theorem commutes_coordBlockSU_of_disjoint {n : ℕ} {I J : Finset (Fin n)}
    (hIJ : Disjoint I J) : Commutes (coordBlockSU F p f I) (coordBlockSU F p f J) := by
  intro a ha b hb
  apply suToSL_injective (σ := unitaryInvolution F p f)
  simpa only [map_mul] using (CFSG.SeitzReduction.LinearPilot.commute_blockSpecialLinear_of_disjoint
    hIJ ((mem_coordBlockSU_iff_suToSL a).mp ha) ((mem_coordBlockSU_iff_suToSL b).mp hb)).eq

theorem LcU_eq_coordBlockSU {n : ℕ} (h2 : (2 : F) ≠ 0) (T : Pair n) :
    LcU F p f T = coordBlockSU F p f T.1 := by
  ext x
  change suToSL (unitaryInvolution F p f) n x ∈ Lc F T ↔ _
  rw [Lc_eq_blockSpecialLinear h2]
  exact (mem_coordBlockSU_iff_suToSL x).symm

theorem unitaryFrameBlock_eq_coordBlockSU {m tail : ℕ} (h2 : (2 : F) ≠ 0)
    (k : Fin (m + 1)) : unitaryFrameBlock F p f m k tail =
    coordBlockSU F p f {⟨2 * k.val, by omega⟩, ⟨2 * k.val + 1, by omega⟩} := by
  have hab : (⟨2 * k.val, by omega⟩ : Fin (2 * m + 1 + 1 + tail)) ≠
      ⟨2 * k.val + 1, by omega⟩ := by
    intro h
    have hh : 2 * k.val = 2 * k.val + 1 := congrArg Fin.val h
    omega
  let T : Pair (2 * m + 1 + 1 + tail) :=
    ⟨{⟨2 * k.val, by omega⟩, ⟨2 * k.val + 1, by omega⟩}, Finset.card_pair hab⟩
  rw [unitaryFrameBlock, range_blockEmb_eq_longRootGroupSU h2,
    negBlock_eq_zMat (by omega : 2 * k.val + 2 ≤ 2 * m + 1 + 1 + tail)]
  exact LcU_eq_coordBlockSU h2 T

theorem commutes_unitaryTripleBlock_unitaryFrameBlock {m : ℕ} (hp2 : p ≠ 2)
    {k j : Fin (m + 1)} (hjk : j ≠ k) :
    Commutes (coordBlockSU F p f (linearFrameTriple m k)) (unitaryFrameBlock F p f m j 1) := by
  rw [unitaryFrameBlock_eq_coordBlockSU (two_ne_zero_of_charP_ne_two hp2)]
  exact commutes_coordBlockSU_of_disjoint (disjoint_linearFrameTriple_pair hjk)

theorem map_coordBlockSU_of_monomial {n : ℕ} {g : Su F p f n} {τ : Equiv.Perm (Fin n)}
    (hg : IsMonomialFor (suMat g) τ) (I : Finset (Fin n)) :
    (coordBlockSU F p f I).map (MulAut.conj g).toMonoidHom =
      coordBlockSU F p f (I.map τ.toEmbedding) := by
  have hstep : ∀ {u : Su F p f n} {σ : Equiv.Perm (Fin n)},
      IsMonomialFor (suMat u) σ → ∀ J : Finset (Fin n), ∀ x ∈ coordBlockSU F p f J,
        u * x * u⁻¹ ∈ coordBlockSU F p f (J.map σ.toEmbedding) := by
    intro u σ hu J x hx
    rw [mem_coordBlockSU_iff_smul_single]
    intro b hb
    have hb' : σ.symm b ∉ J := by
      intro h
      exact hb (Finset.mem_map.mpr ⟨σ.symm b, h, σ.apply_symm_apply b⟩)
    obtain ⟨c, hc, huc⟩ := hu (σ.symm b)
    rw [σ.apply_symm_apply] at huc
    change u • (Pi.single (σ.symm b) 1 : Fin n → F) = c • Pi.single b 1 at huc
    have hfix := (mem_coordBlockSU_iff_smul_single x).mp hx (σ.symm b) hb'
    have hconj : (u * x * u⁻¹) • (u • (Pi.single (σ.symm b) 1 : Fin n → F)) =
        u • (Pi.single (σ.symm b) 1 : Fin n → F) := by
      simp only [mul_smul, inv_smul_smul, hfix]
    rw [huc, smul_comm (u * x * u⁻¹) c] at hconj
    exact smul_right_injective _ hc hconj
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hstep hg I x hx
  · intro x hx
    have hgInv : IsMonomialFor (suMat g⁻¹) τ⁻¹ := hg.of_mul_eq_one (suMat_inv_mul_suMat g)
    have hxx := hstep hgInv (I.map τ.toEmbedding) x hx
    have hI : (I.map τ.toEmbedding).map τ.symm.toEmbedding = I := by
      ext a
      simp
    change g⁻¹ * x * g ∈ coordBlockSU F p f ((I.map τ.toEmbedding).map τ.symm.toEmbedding) at hxx
    rw [hI] at hxx
    refine ⟨g⁻¹ * x * g, hxx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem exists_monomial_unitaryTriple {m : ℕ} (k : Fin (m + 1)) :
    ∃ (g : Su F p f (2 * m + 1 + 1 + 1)) (τ : Equiv.Perm (Fin (2 * m + 1 + 1 + 1))),
      IsMonomialFor (suMat g) τ ∧
      ({⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} :
        Finset (Fin (2 * m + 1 + 1 + 1))).map τ.toEmbedding = linearFrameTriple m k := by
  let a : Fin (2 * m + 1 + 1 + 1) := ⟨0, by omega⟩
  let b : Fin (2 * m + 1 + 1 + 1) := ⟨1, by omega⟩
  let c : Fin (2 * m + 1 + 1 + 1) := ⟨2, by omega⟩
  have hab : a ≠ b := by intro h; have hh : 0 = 1 := congrArg Fin.val h; omega
  have hac : a ≠ c := by intro h; have hh : 0 = 2 := congrArg Fin.val h; omega
  have hbc : b ≠ c := by intro h; have hh : 1 = 2 := congrArg Fin.val h; omega
  have hcard : ({a, b, c} : Finset (Fin (2 * m + 1 + 1 + 1))).card =
      (linearFrameTriple m k).card := by simp [hab, hac, hbc, card_linearFrameTriple]
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq {a, b, c} (linearFrameTriple m k) hcard
  exact ⟨monoSU F p f (by omega) τ, τ, isMonomialFor_monoMat τ, hτ⟩

theorem range_blockEmb_three_eq_coordBlockSU {n : ℕ} (hn : 3 ≤ n) :
    (blockEmb F p f n 3 0 (by omega)).range =
      coordBlockSU F p f {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} := by
  ext x
  rw [CFSG.ClassicalInvolution.Phan.mem_range_blockEmb_iff,
    mem_coordBlockSU_iff_smul_single]
  have hmem : ∀ j : Fin n,
      j ∈ ({⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin n)) ↔ j.val < 3 := by
    intro j
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega
  simp only [hmem, Nat.zero_le, zero_add, true_and]

theorem map_B12_blockEmb_three {n : ℕ} (hn : 3 ≤ n) :
    (CFSG.ClassicalInvolution.Phan.B12 F p f).map (blockEmb F p f n 3 0 (by omega)) =
      (blockEmb F p f n 2 0 (by omega)).range := by
  rw [CFSG.ClassicalInvolution.Phan.B12, CFSG.ClassicalInvolution.Phan.embSUid_two_eq_blockEmb,
    ← MonoidHom.range_comp, CFSG.ClassicalInvolution.Phan.blockEmb_comp]

theorem map_B23_blockEmb_three {n : ℕ} (hn : 3 ≤ n) :
    (CFSG.ClassicalInvolution.Phan.B23 F p f).map (blockEmb F p f n 3 0 (by omega)) =
      (blockEmb F p f n 2 1 (by omega)).range := by
  rw [CFSG.ClassicalInvolution.Phan.B23, CFSG.ClassicalInvolution.Phan.embSUid_zero_eq_blockEmb,
    ← MonoidHom.range_comp, CFSG.ClassicalInvolution.Phan.blockEmb_comp]

theorem unitaryTripleBlock_le_iSup_supported_pairs {m : ℕ}
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (k : Fin (m + 1)) :
    coordBlockSU F p f (linearFrameTriple m k) ≤
      ⨆ (T : Pair (2 * m + 1 + 1 + 1)) (_ : T.1 ⊆ linearFrameTriple m k), LcU F p f T := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  obtain ⟨g, τ, hg, hτ⟩ := exists_monomial_unitaryTriple (F := F) (p := p) (f := f) k
  let I₀ : Finset (Fin (2 * m + 1 + 1 + 1)) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩}
  have hrange : coordBlockSU F p f (linearFrameTriple m k) =
      ((blockEmb F p f (2 * m + 1 + 1 + 1) 3 0 (by omega)).range).map
        (MulAut.conj g).toMonoidHom := by
    rw [range_blockEmb_three_eq_coordBlockSU, map_coordBlockSU_of_monomial hg, hτ]
  have hgen : (blockEmb F p f (2 * m + 1 + 1 + 1) 3 0 (by omega)).range =
      (blockEmb F p f (2 * m + 1 + 1 + 1) 2 0 (by omega)).range ⊔
        (blockEmb F p f (2 * m + 1 + 1 + 1) 2 1 (by omega)).range := by
    rw [MonoidHom.range_eq_map, ← CFSG.ClassicalInvolution.Phan.B12_sup_B23 hF
      (prime_pow_ne_two_of_ne_two hp2 f), Subgroup.map_sup,
      map_B12_blockEmb_three, map_B23_blockEmb_three]
  rw [hrange, hgen, Subgroup.map_sup]
  apply sup_le
  · let T : Pair (2 * m + 1 + 1 + 1) :=
      ⟨{τ ⟨0, by omega⟩, τ ⟨1, by omega⟩}, Finset.card_pair (by
        intro h
        have h' := τ.injective h
        have hh : 0 = 1 := congrArg Fin.val h'
        omega)⟩
    rw [← LcU_eq_map_conj h2 hg (by omega : 0 + 2 ≤ 2 * m + 1 + 1 + 1) (T := T) rfl]
    refine le_iSup_of_le T (le_iSup_of_le ?_ le_rfl)
    intro i hi
    rw [← hτ]
    rcases Finset.mem_insert.mp hi with h | h
    · exact Finset.mem_map.mpr ⟨⟨0, by omega⟩, by simp, h.symm⟩
    · rw [Finset.mem_singleton] at h
      exact Finset.mem_map.mpr ⟨⟨1, by omega⟩, by simp, h.symm⟩
  · let T : Pair (2 * m + 1 + 1 + 1) :=
      ⟨{τ ⟨1, by omega⟩, τ ⟨2, by omega⟩}, Finset.card_pair (by
        intro h
        have h' := τ.injective h
        have hh : 1 = 2 := congrArg Fin.val h'
        omega)⟩
    rw [← LcU_eq_map_conj h2 hg (by omega : 1 + 2 ≤ 2 * m + 1 + 1 + 1) (T := T) rfl]
    refine le_iSup_of_le T (le_iSup_of_le ?_ le_rfl)
    intro i hi
    rw [← hτ]
    rcases Finset.mem_insert.mp hi with h | h
    · exact Finset.mem_map.mpr ⟨⟨1, by omega⟩, by simp, h.symm⟩
    · rw [Finset.mem_singleton] at h
      exact Finset.mem_map.mpr ⟨⟨2, by omega⟩, by simp, h.symm⟩

theorem not_commutes_all_unitaryFrameBlocks_odd {m : ℕ}
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    {L : Subgroup (Su F p f (2 * m + 1 + 1 + 1))}
    {z : Su F p f (2 * m + 1 + 1 + 1)}
    (hL : IsLongRootSU2 F p f (by omega) L z)
    (hc : ∀ j : Fin (m + 1), Commutes L (unitaryFrameBlock F p f m j 1)) : False := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have hspaces := fun j => eigenspaces_of_commutes_unitaryFrameBlock hF hp2 (by omega) hL j (hc j)
  let v₀ : Fin (2 * m + 1 + 1 + 1) → F := Pi.single (Fin.last (2 * m + 1 + 1)) 1
  have hline : minusSpaceSU z ≤ Submodule.span F ({v₀} : Set (Fin (2 * m + 1 + 1 + 1) → F)) := by
    intro v hv
    rw [Submodule.mem_span_singleton]
    refine ⟨v (Fin.last (2 * m + 1 + 1)), ?_⟩
    ext a
    by_cases ha : a = Fin.last (2 * m + 1 + 1)
    · subst a
      simp [v₀]
    · have halast : a.val ≠ 2 * m + 1 + 1 := fun h => ha (Fin.ext h)
      let j : Fin (m + 1) := ⟨a.val / 2, by omega⟩
      have hv0 := (mem_fixSpace_unitaryFrameInvolution h2 j).mp ((hspaces j).1 hv) a
        (by dsimp [j]; omega) (by dsimp [j]; omega)
      simp [v₀, ha, hv0]
  have hv₀ : v₀ ≠ 0 := by
    intro h
    have := congrFun h (Fin.last (2 * m + 1 + 1))
    simp [v₀] at this
  have hdim := Submodule.finrank_mono hline
  rw [hL.finrank_minusSpaceSU h2, finrank_span_singleton hv₀] at hdim
  omega

theorem le_tripleBlock_of_commutes_other_unitaryFrameBlocks {m : ℕ}
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    {L : Subgroup (Su F p f (2 * m + 1 + 1 + 1))}
    {z : Su F p f (2 * m + 1 + 1 + 1)}
    (hL : IsLongRootSU2 F p f (by omega) L z) (k : Fin (m + 1))
    (hc : ∀ j : Fin (m + 1), j ≠ k → Commutes L (unitaryFrameBlock F p f m j 1)) :
    L ≤ coordBlockSU F p f (linearFrameTriple m k) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have hspaces := fun j hj => eigenspaces_of_commutes_unitaryFrameBlock hF hp2 (by omega) hL j (hc j hj)
  intro x hx
  apply mem_coordBlockSU_of_smul_single x
  intro a ha
  have ha' := (mem_linearFrameTriple k a).not.mp ha
  let j : Fin (m + 1) := ⟨a.val / 2, by omega⟩
  have hj : j ≠ k := by intro h; have := congrArg Fin.val h; dsimp [j] at this; omega
  apply (hL.mem_iff_fix hF hp2).mp hx
  apply (hspaces j hj).2
  rw [mem_minusSpace_unitaryFrameInvolution h2]
  intro b hb
  have hba : b ≠ a := by intro h; subst b; dsimp [j] at hb; omega
  simp [hba]

theorem eq_unitaryFrameBlock_of_commutes_other_blocks {m : ℕ}
    (hm : 1 ≤ m) (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    {L : Subgroup (Su F p f (2 * m + 1 + 1))} {z : Su F p f (2 * m + 1 + 1)}
    (hL : IsLongRootSU2 F p f (by omega) L z) (k : Fin (m + 1))
    (hc : ∀ j : Fin (m + 1), j ≠ k → Commutes L (unitaryFrameBlock F p f m j)) :
    L = unitaryFrameBlock F p f m k := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  have hspaces := fun j hj => eigenspaces_of_commutes_unitaryFrameBlock (tail := 0)
    hF hp2 (by omega) hL j (hc j hj)
  have hminus : minusSpaceSU z ≤ minusSpaceSU (unitaryFrameInvolution F p f m k) := by
    intro v hv
    rw [mem_minusSpace_unitaryFrameInvolution h2]
    intro a ha
    let j : Fin (m + 1) := ⟨a.val / 2, by omega⟩
    have hj : j ≠ k := by intro h; have := congrArg Fin.val h; dsimp [j] at this; omega
    exact (mem_fixSpace_unitaryFrameInvolution h2 j).mp ((hspaces j hj).1 hv) a
      (by dsimp [j]; omega) (by dsimp [j]; omega)
  have hminusEq := Submodule.eq_of_le_of_finrank_eq hminus
    ((hL.finrank_minusSpaceSU h2).trans
      ((isLongRootSU2_unitaryFrameBlock hF hp2 k).finrank_minusSpaceSU h2).symm)
  have hfixEq : fixSpaceSU z = fixSpaceSU (unitaryFrameInvolution F p f m k) := by
    rw [← hL.perp_minusSpaceSU hF hp2,
      ← (isLongRootSU2_unitaryFrameBlock hF hp2 k).perp_minusSpaceSU hF hp2, hminusEq]
  ext x
  rw [hL.mem_iff_fix hF hp2,
    (isLongRootSU2_unitaryFrameBlock hF hp2 k).mem_iff_fix hF hp2, hfixEq]

theorem exists_conj_unitaryFrameBlock_permutation {m : ℕ} (hp2 : p ≠ 2)
    (σ : Equiv.Perm (Fin (m + 1))) :
    ∃ g : Su F p f (2 * m + 1 + 1), ∀ k : Fin (m + 1),
      (unitaryFrameBlock F p f m k).map (MulAut.conj g).toMonoidHom =
        unitaryFrameBlock F p f m (σ k) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  let τ : Equiv.Perm (Fin (2 * m + 1 + 1)) := linearFramePerm σ
  let g := monoSU F p f (by omega : 0 < 2 * m + 1 + 1) τ
  have hg : IsMonomialFor (suMat g) τ := isMonomialFor_monoMat τ
  refine ⟨g, fun k => ?_⟩
  let a : Fin (2 * m + 1 + 1) := ⟨2 * (σ k).val, by omega⟩
  let b : Fin (2 * m + 1 + 1) := ⟨2 * (σ k).val + 1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have hh : 2 * (σ k).val = 2 * (σ k).val + 1 := congrArg Fin.val h
    omega
  let T : Pair (2 * m + 1 + 1) := ⟨{a, b}, Finset.card_pair hab⟩
  have hT : T.1 = {τ ⟨2 * k.val, by omega⟩, τ ⟨2 * k.val + 1, by omega⟩} := by
    rw [show τ ⟨2 * k.val, by omega⟩ = ⟨2 * (σ k).val, by omega⟩ from
      linearFramePerm_pair_first σ k]
    rw [show τ ⟨2 * k.val + 1, by omega⟩ = ⟨2 * (σ k).val + 1, by omega⟩ from
      linearFramePerm_pair_second σ k]
  have hLc : LcU F p f T = unitaryFrameBlock F p f m (σ k) := by
    rw [unitaryFrameBlock, range_blockEmb_eq_longRootGroupSU h2]
    have hneg := negBlock_eq_zMat (K := F) (by omega : 2 * (σ k).val + 2 ≤ 2 * m + 1 + 1)
    change longRootGroupSU F p f (zMat F (2 * m + 1 + 1) T.1) = _
    rw [hneg]
  exact (LcU_eq_map_conj h2 hg (by omega) hT).symm.trans hLc

theorem exists_conj_oddUnitaryFrameBlock_permutation {m : ℕ} (hp2 : p ≠ 2)
    (σ : Equiv.Perm (Fin (m + 1))) :
    ∃ g : Su F p f (2 * m + 1 + 1 + 1), ∀ k : Fin (m + 1),
      (unitaryFrameBlock F p f m k 1).map (MulAut.conj g).toMonoidHom =
        unitaryFrameBlock F p f m (σ k) 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  let τ : Equiv.Perm (Fin (2 * m + 1 + 1 + 1)) := oddLinearFramePerm σ
  let g := monoSU F p f (by omega : 0 < 2 * m + 1 + 1 + 1) τ
  have hg : IsMonomialFor (suMat g) τ := isMonomialFor_monoMat τ
  refine ⟨g, fun k => ?_⟩
  let a : Fin (2 * m + 1 + 1 + 1) := ⟨2 * (σ k).val, by omega⟩
  let b : Fin (2 * m + 1 + 1 + 1) := ⟨2 * (σ k).val + 1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have hh : 2 * (σ k).val = 2 * (σ k).val + 1 := congrArg Fin.val h
    omega
  let T : Pair (2 * m + 1 + 1 + 1) := ⟨{a, b}, Finset.card_pair hab⟩
  have hT : T.1 = {τ ⟨2 * k.val, by omega⟩, τ ⟨2 * k.val + 1, by omega⟩} := by
    rw [show τ ⟨2 * k.val, by omega⟩ = ⟨2 * (σ k).val, by omega⟩ from
      oddLinearFramePerm_pair_first σ k]
    rw [show τ ⟨2 * k.val + 1, by omega⟩ = ⟨2 * (σ k).val + 1, by omega⟩ from
      oddLinearFramePerm_pair_second σ k]
  have hLc : LcU F p f T = unitaryFrameBlock F p f m (σ k) 1 := by
    rw [unitaryFrameBlock, range_blockEmb_eq_longRootGroupSU h2]
    have hneg := negBlock_eq_zMat (K := F) (by omega : 2 * (σ k).val + 2 ≤ 2 * m + 1 + 1 + 1)
    change longRootGroupSU F p f (zMat F (2 * m + 1 + 1 + 1) T.1) = _
    rw [hneg]
  exact (LcU_eq_map_conj h2 hg (by omega) hT).symm.trans hLc

theorem lieModel_unitaryTripleBlock_map_quotient
    {X : Type} [Group X] {p f m : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (ψ : Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1 + 1) →* X) (k : Fin (m + 1))
    (hne : (coordBlockSU (GaloisField p (2 * f)) p f (linearFrameTriple m k)).map ψ ≠ ⊥) :
    CFSG.Blueprint.LieModel
      (((coordBlockSU (GaloisField p (2 * f)) p f (linearFrameTriple m k)).map ψ) ⧸
        center ((coordBlockSU (GaloisField p (2 * f)) p f (linearFrameTriple m k)).map ψ))
      .PSU 3 p f := by
  let F := GaloisField p (2 * f)
  have hF : Nat.card F = (p ^ f) ^ 2 := CFSG.LieType.Universal.card_galoisField_two_mul p f hf
  have hq2 : p ^ f ≠ 2 := prime_pow_ne_two_of_ne_two hp2 f
  have hpair : (3, p ^ f) ≠ (3, 2) := fun h => hq2 (congrArg Prod.snd h)
  have hadm : StatedLieAdmissible .PSU 3 p f := ⟨hp.out, hf, le_rfl, hpair⟩
  have hQ : CFSG.IsQuasisimple (Su F p f 3) :=
    CFSG.GH74.L5U5.isQuasisimple_su hF le_rfl hpair
  have hmodel : CFSG.Blueprint.LieModel (Su F p f 3 ⧸ center (Su F p f 3)) .PSU 3 p f :=
    Or.inl ⟨by decide, hadm, F, inferInstance, inferInstance, hF,
      ⟨CFSG.GH74.L5U5.centerQuotientEquivStatedProjSu hF le_rfl hpair⟩⟩
  let I := linearFrameTriple m k
  have hcard : I.card = 3 := card_linearFrameTriple k
  have heI : Nonempty (Su F p f 3 ≃* Su F p f I.card) := by
    rw [hcard]
    exact ⟨MulEquiv.refl _⟩
  obtain ⟨eI⟩ := heI
  let φ := (CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary.blockSUOn F p f I).comp
    eI.toMonoidHom
  let η := ψ.comp φ
  have hφ : φ.range = coordBlockSU F p f I := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eI.surjective,
      ← MonoidHom.range_eq_map]
    rfl
  have hη : η.range = (coordBlockSU F p f I).map ψ := by rw [MonoidHom.range_comp, hφ]
  have hηne : η.range ≠ ⊥ := by rwa [hη]
  have hnt : ∃ x, η.rangeRestrict x ≠ 1 := by
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hηne
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, fun h => hy1 h⟩
  have hmodel' := CFSG.Timmesfeld.lieModel_quotient_of_surjective hQ hmodel
    η.rangeRestrict_surjective hnt
  exact CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv (MulEquiv.subgroupCongr hη) hmodel'


theorem commutes_unitaryFund_of_commutes_map
    {X : Type} [Group X] {p f n : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .PSU n p f)
    (e : (modelUniv .PSU n p f hp.out).K ≃* Su (GaloisField p (2 * f)) p f n)
    (he : ∀ R : Subgroup (modelUniv .PSU n p f hp.out).K,
      R ∈ fundamentalSubgroups .PSU (modelUniv .PSU n p f hp.out).D ↔
        R.map e.toMonoidHom ∈ longRootSetU (K := GaloisField p (2 * f))
          (p := p) (f := f) (by have := hadm.2.2.1; omega : 2 ≤ n))
    (ψ : Su (GaloisField p (2 * f)) p f n →* X)
    (hker : ψ.ker ≤ center (Su (GaloisField p (2 * f)) p f n))
    {R S : Subgroup (Su (GaloisField p (2 * f)) p f n)}
    (hR : R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f)
      (by have := hadm.2.2.1; omega : 2 ≤ n))
    (hc : Commutes (R.map ψ) (S.map ψ)) : Commutes R S := by
  let R₀ := R.map e.symm.toMonoidHom
  let S₀ := S.map e.symm.toMonoidHom
  let ψ₀ := ψ.comp e.toMonoidHom
  have hRmap : R₀.map e.toMonoidHom = R := by simp [R₀, Subgroup.map_map]
  have hSmap : S₀.map e.toMonoidHom = S := by simp [S₀, Subgroup.map_map]
  have hR₀ : R₀ ∈ fundamentalSubgroups .PSU (modelUniv .PSU n p f hp.out).D :=
    (he R₀).mpr (hRmap.symm ▸ hR)
  have hker₀ : ψ₀.ker ≤ center (modelUniv .PSU n p f hp.out).K := by
    intro x hx
    have hx' : e x ∈ center (Su (GaloisField p (2 * f)) p f n) := hker hx
    rw [Subgroup.mem_center_iff] at hx' ⊢
    intro y
    apply e.injective
    simpa only [map_mul] using hx' (e y)
  have hc₀ : Commutes (R₀.map ψ₀) (S₀.map ψ₀) := by
    have h1 : R₀.map ψ₀ = R.map ψ := by dsimp only [ψ₀]; rw [← Subgroup.map_map, hRmap]
    have h2 : S₀.map ψ₀ = S.map ψ := by dsimp only [ψ₀]; rw [← Subgroup.map_map, hSmap]
    rwa [h1, h2]
  have hcomm := commutes_modelFund_of_commutes_map hp2 (by trivial) hadm ψ₀ hker₀ hR₀ hc₀
  intro a ha b hb
  have ha₀ : e.symm a ∈ R₀ := Subgroup.mem_map_of_mem _ ha
  have hb₀ : e.symm b ∈ S₀ := Subgroup.mem_map_of_mem _ hb
  simpa only [map_mul, e.apply_symm_apply] using congrArg e (hcomm _ ha₀ _ hb₀)

theorem isFundamentalOver_unitary_root_map
    {X : Type} [Group X] {p f n : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .PSU n p f)
    (e : (modelUniv .PSU n p f hp.out).K ≃* Su (GaloisField p (2 * f)) p f n)
    (he : ∀ R : Subgroup (modelUniv .PSU n p f hp.out).K,
      R ∈ fundamentalSubgroups .PSU (modelUniv .PSU n p f hp.out).D ↔
        R.map e.toMonoidHom ∈ longRootSetU (K := GaloisField p (2 * f))
          (p := p) (f := f) (by have := hadm.2.2.1; omega : 2 ≤ n))
    (ψ : Su (GaloisField p (2 * f)) p f n →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center (Su (GaloisField p (2 * f)) p f n))
    {R : Subgroup (Su (GaloisField p (2 * f)) p f n)}
    (hR : R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f)
      (by have := hadm.2.2.1; omega : 2 ≤ n)) : IsFundamentalOver (p ^ f) (R.map ψ) := by
  let R₀ := R.map e.symm.toMonoidHom
  let ψ₀ := ψ.comp e.toMonoidHom
  have hRmap : R₀.map e.toMonoidHom = R := by simp [R₀, Subgroup.map_map]
  have hR₀ : R₀ ∈ fundamentalSubgroups .PSU (modelUniv .PSU n p f hp.out).D :=
    (he R₀).mpr (hRmap.symm ▸ hR)
  have hker₀ : ψ₀.ker ≤ center (modelUniv .PSU n p f hp.out).K := by
    intro x hx
    have hx' : e x ∈ center (Su (GaloisField p (2 * f)) p f n) := hker hx
    rw [Subgroup.mem_center_iff] at hx' ⊢
    intro y
    apply e.injective
    simpa only [map_mul] using hx' (e y)
  refine ⟨.PSU, n, p, f, hp.out, hp2, rfl, trivial, hadm, ψ₀,
    hψ.comp e.surjective, hker₀, R₀, hR₀, ?_⟩
  dsimp only [ψ₀]
  rw [← Subgroup.map_map, hRmap]


theorem exists_unitary_root_of_isFundamentalOver
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p f n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSU n p f) (hX : CFSG.Blueprint.LieModel X .PSU n p f)
    (hL2 : ¬ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.IsL2Over17 (X ⧸ center X) (p ^ f))
    (e : (modelUniv .PSU n p f hp.out).K ≃* Su (GaloisField p (2 * f)) p f n)
    (he : ∀ R : Subgroup (modelUniv .PSU n p f hp.out).K,
      R ∈ fundamentalSubgroups .PSU (modelUniv .PSU n p f hp.out).D ↔
        R.map e.toMonoidHom ∈ longRootSetU (K := GaloisField p (2 * f))
          (p := p) (f := f) (by have := hadm.2.2.1; omega : 2 ≤ n))
    (ψ : Su (GaloisField p (2 * f)) p f n →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center (Su (GaloisField p (2 * f)) p f n))
    {K : Subgroup X} (hK : IsFundamentalOver (p ^ f) K) :
    ∃ R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f)
      (by have := hadm.2.2.1; omega : 2 ≤ n), K = R.map ψ := by
  let ψ₀ := ψ.comp e.toMonoidHom
  have hker₀ : ψ₀.ker ≤ center (modelUniv .PSU n p f hp.out).K := by
    intro x hx
    have hx' : e x ∈ center (Su (GaloisField p (2 * f)) p f n) := hker hx
    rw [Subgroup.mem_center_iff] at hx' ⊢
    intro y
    apply e.injective
    simpa only [map_mul] using hx' (e y)
  obtain ⟨R₀, hR₀, heq, _⟩ := exists_mem_fundamentalSubgroups_of_isFundamentalOver_general
    hp.out hp2 hadm hX (by trivial) (by simp) hL2 ψ₀ (hψ.comp e.surjective) hker₀ hK
  refine ⟨R₀.map e.toMonoidHom, (he R₀).mp hR₀, ?_⟩
  rw [Subgroup.map_map]
  exact heq

theorem exists_full_coordinate_frame_funSet_psu_even
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hadm : StatedLieAdmissible .PSU (2 * m + 1 + 1) p f) (hX : CFSG.Blueprint.LieModel X .PSU (2 * m + 1 + 1) p f)
    (e : (modelUniv .PSU (2 * m + 1 + 1) p f hp.out).K ≃*
      Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1))
    (he : ∀ R : Subgroup (modelUniv .PSU (2 * m + 1 + 1) p f hp.out).K,
      R ∈ fundamentalSubgroups .PSU (modelUniv .PSU (2 * m + 1 + 1) p f hp.out).D ↔
        R.map e.toMonoidHom ∈ longRootSetU (K := GaloisField p (2 * f))
          (p := p) (f := f) (by omega : 2 ≤ 2 * m + 1 + 1))
    (ψ : Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1) →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center (Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1))) (P : Sylow 2 X) :
    ∃ c : X,
      F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
        Set.range (fun k : Fin (m + 1) =>
          ((unitaryFrameBlock (GaloisField p (2 * f)) p f m k).map ψ).map (MulAut.conj c).toMonoidHom) := by
  let F := GaloisField p (2 * f)
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.RouteD.two_ne_zero_galoisField hp2
  have hF : Nat.card F = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hadm.2.1
  let A : Fin (m + 1) → Subgroup X := fun k => (unitaryFrameBlock F p f m k).map ψ
  have hroots : ∀ k : Fin (m + 1), unitaryFrameBlock F p f m k ∈
      longRootSetU (K := F) (p := p) (f := f) (by omega : 2 ≤ 2 * m + 1 + 1) := fun k =>
    ⟨unitaryFrameInvolution F p f m k, isLongRootSU2_unitaryFrameBlock hF hp2 k⟩
  have hA : ∀ k, IsFundamentalOver (p ^ f) (A k) := fun k =>
    isFundamentalOver_unitary_root_map hp2 hadm e he ψ hψ hker (hroots k)
  have hblockcomm : ∀ {k j : Fin (m + 1)}, k ≠ j →
      Commutes (unitaryFrameBlock F p f m k) (unitaryFrameBlock F p f m j) := fun h => commutes_unitaryFrameBlock h
  have hcomm : ∀ k j, k ≠ j → Commutes (A k) (A j) := by
    intro k j hkj a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    simpa only [map_mul] using congrArg ψ (hblockcomm hkj a₀ ha₀ b₀ hb₀)
  have hnorm : ∀ k j, A j ≤ normalizer (A k : Set X) := by
    intro k j
    by_cases hkj : k = j
    · rw [hkj]
      exact Subgroup.le_normalizer
    · have hc : A j ≤ centralizer (A k : Set X) := by
        intro a ha
        exact Subgroup.mem_centralizer_iff.mpr fun b hb => hcomm k j hkj b hb a ha
      exact hc.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨c, hc⟩ := F14.exists_conj_family_mem_funSet (𝔉 := fundPred (p ^ f))
    (fun g _ h => isFundamentalOver_map_mulEquiv (MulAut.conj g) h) A hA hnorm P
  let ψc : Su F p f (2 * m + 1 + 1) →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center (Su F p f (2 * m + 1 + 1)) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  have hc' : ∀ k, (unitaryFrameBlock F p f m k).map ψc ∈
      F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) := by
    intro k
    simpa [A, ψc, Subgroup.map_map] using hc k
  let k0 : Fin (m + 1) := 0
  obtain ⟨hZ, _, hL2, hΩ⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX
    (by simp) (hc' k0).1
  have hdesc : ∃ (t : StatedLieTag) (n e : ℕ), StatedLieAdmissible t n p e ∧
      p ^ f = p ^ e ∧ CFSG.Blueprint.LieModel (X ⧸ center X) t n p e :=
    ⟨.PSU, 2 * m + 1 + 1, f, hadm, rfl, hX.quotient_center hZ⟩
  refine ⟨c, ?_⟩
  ext L
  constructor
  · intro hL
    by_contra hnot
    have hne : ∀ k, L ≠ (unitaryFrameBlock F p f m k).map ψc := by
      intro k heq
      apply hnot
      exact ⟨k, by simpa [A, ψc, Subgroup.map_map] using heq.symm⟩
    obtain ⟨R, hR, hLR⟩ := exists_unitary_root_of_isFundamentalOver hp2 hadm hX hL2
      e he ψc hψc hkerC hL.1
    have hcR : ∀ k, Commutes (R.map ψc) ((unitaryFrameBlock F p f m k).map ψc) := by
      intro k
      rw [← hLR]
      have h := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.funSet_commute_of_lieModel
        hp.out hp2 hdesc hL2 P hL (hc' k) (hne k)
      exact fun a ha b hb => (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha) b hb).symm
    obtain ⟨z, hz⟩ := hR
    have hcR' : ∀ j : Fin (m + 1), j ≠ k0 → Commutes R (unitaryFrameBlock F p f m j) :=
      fun j _ => commutes_unitaryFund_of_commutes_map hp2 hadm e he ψc hkerC ⟨z, hz⟩ (hcR j)
    have heq := eq_unitaryFrameBlock_of_commutes_other_blocks hm hF hp2 hz k0 hcR'
    exact hne k0 (hLR.trans (congrArg (fun T : Subgroup _ => T.map ψc) heq))
  · rintro ⟨k, rfl⟩
    exact hc k



theorem nonempty_equiv_perm_funSet_psu_even
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hadm : StatedLieAdmissible .PSU (2 * m + 1 + 1) p f) (hX : CFSG.Blueprint.LieModel X .PSU (2 * m + 1 + 1) p f)
    (P : Sylow 2 X) :
    let Δ := F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)
    Nonempty ((conjPermHom (le_refl (conjSetStab Δ))).range ≃* Equiv.Perm (Fin (m + 1))) := by
  obtain ⟨ψ0, hψ0, hker0⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSU (2 * m + 1 + 1) p f hp.out hp2 (by trivial) hadm X hX
  obtain ⟨eU, heU⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  let ψ : Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1) →* X := ψ0.comp eU.symm.toMonoidHom
  have hψ : Function.Surjective ψ := hψ0.comp eU.symm.surjective
  have hker : ψ.ker ≤ center (Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1)) := by
    intro x hx
    have hx' : eU.symm x ∈ center (modelUniv .PSU (2 * m + 1 + 1) p f hp.out).K := hker0 hx
    rw [Subgroup.mem_center_iff] at hx' ⊢
    intro y
    apply eU.symm.injective
    simpa only [map_mul] using hx' (eU.symm y)
  have hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hadm.2.1
  obtain ⟨c, hfull⟩ := exists_full_coordinate_frame_funSet_psu_even hp2 hm hadm hX
    eU heU ψ hψ hker P
  let ψc : Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1) →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hkerC : ψc.ker ≤ center (Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1)) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  have hfull' : F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      Set.range (fun k : Fin (m + 1) => (unitaryFrameBlock (GaloisField p (2 * f)) p f m k).map ψc) := by
    simpa [ψc, Subgroup.map_map] using hfull
  rw [hfull']
  classical
  let Δ := Set.range (fun k : Fin (m + 1) => (unitaryFrameBlock (GaloisField p (2 * f)) p f m k).map ψc)
  let d : Fin (m + 1) → Δ := fun k => ⟨(unitaryFrameBlock (GaloisField p (2 * f)) p f m k).map ψc, ⟨k, rfl⟩⟩
  have hd : Function.Bijective d := by
    constructor
    · intro i j heq
      by_contra hij
      exact F14.map_ne_of_commuting_of_equiv_sl2 ψc hkerC
        (Classical.choice (nonempty_equiv_sl2_unitaryFrameBlock (F := GaloisField p (2 * f)) (p := p) (f := f) (m := m) (tail := 0) hF i))
        (fun a ha b hb => commutes_unitaryFrameBlock (tail := 0) hij a ha b hb) (congrArg Subtype.val heq)
    · rintro ⟨L, k, rfl⟩
      exact ⟨k, rfl⟩
  let e : Fin (m + 1) ≃ Δ := Equiv.ofBijective d hd
  have hρ : Function.Surjective (conjPermHom (le_refl (conjSetStab Δ))) :=
    surjective_conjPermHom_of_indexed_conjugations e fun σ => by
      obtain ⟨g, hg⟩ := exists_conj_unitaryFrameBlock_permutation (F := GaloisField p (2 * f)) (f := f)
        hp2 σ
      refine ⟨ψc g, fun k => ?_⟩
      change ((unitaryFrameBlock (GaloisField p (2 * f)) p f m k).map ψc).map
        (MulAut.conj (ψc g)).toMonoidHom =
          (unitaryFrameBlock (GaloisField p (2 * f)) p f m (σ k)).map ψc
      have hhom : (MulAut.conj (ψc g)).toMonoidHom.comp ψc =
          ψc.comp (MulAut.conj g).toMonoidHom := by
        ext x
        simp [MulAut.conj_apply]
      rw [Subgroup.map_map, hhom, ← Subgroup.map_map, hg]
  have htop := MonoidHom.range_eq_top.mpr hρ
  exact ⟨(MulEquiv.subgroupCongr htop).trans
    (Subgroup.topEquiv.trans e.symm.permCongrHom)⟩

theorem centralizingLayer_funSet_eq_of_psu_even
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hadm : StatedLieAdmissible .PSU (2 * m + 1 + 1) p f) (hX : CFSG.Blueprint.LieModel X .PSU (2 * m + 1 + 1) p f)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)) :
    centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ f) L}
      {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X),
        L ≠ K ∧ x ∈ L} = K := by
  obtain ⟨ψ0, hψ0, hker0⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSU (2 * m + 1 + 1) p f hp.out hp2 (by trivial) hadm X hX
  obtain ⟨eU, heU⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  let ψ : Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1) →* X := ψ0.comp eU.symm.toMonoidHom
  have hψ : Function.Surjective ψ := hψ0.comp eU.symm.surjective
  have hker : ψ.ker ≤ center (Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1)) := by
    intro x hx
    have hx' : eU.symm x ∈ center (modelUniv .PSU (2 * m + 1 + 1) p f hp.out).K := hker0 hx
    rw [Subgroup.mem_center_iff] at hx' ⊢
    intro y
    apply eU.symm.injective
    simpa only [map_mul] using hx' (eU.symm y)
  have hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hadm.2.1
  obtain ⟨c, hfull⟩ := exists_full_coordinate_frame_funSet_psu_even hp2 hm hadm hX
    eU heU ψ hψ hker P
  let F := GaloisField p (2 * f)
  let ψc : Su F p f (2 * m + 1 + 1) →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center (Su F p f (2 * m + 1 + 1)) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  have hfull' : F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      Set.range (fun k : Fin (m + 1) => (unitaryFrameBlock F p f m k).map ψc) := by
    simpa [ψc, Subgroup.map_map] using hfull
  have hKrange : K ∈ Set.range (fun k : Fin (m + 1) => (unitaryFrameBlock F p f m k).map ψc) := hfull' ▸ hK
  obtain ⟨k, rfl⟩ := hKrange
  have hinj : Function.Injective (fun j : Fin (m + 1) => (unitaryFrameBlock F p f m j).map ψc) := by
    intro i j heq
    by_contra hij
    exact F14.map_ne_of_commuting_of_equiv_sl2 ψc hkerC
      (Classical.choice (nonempty_equiv_sl2_unitaryFrameBlock (F := GaloisField p (2 * f)) (p := p) (f := f) (m := m) (tail := 0) hF i))
      (fun a ha b hb => commutes_unitaryFrameBlock (tail := 0) hij a ha b hb) heq
  have hΓ : {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X),
      L ≠ (unitaryFrameBlock F p f m k).map ψc ∧ x ∈ L} =
      {x : X | ∃ j : Fin (m + 1), j ≠ k ∧ x ∈ (unitaryFrameBlock F p f m j).map ψc} := by
    ext x
    constructor
    · rintro ⟨L, hL, hne, hx⟩
      rw [hfull'] at hL
      obtain ⟨j, rfl⟩ := hL
      exact ⟨j, fun h => hne (h ▸ rfl), hx⟩
    · rintro ⟨j, hne, hx⟩
      exact ⟨(unitaryFrameBlock F p f m j).map ψc, hfull'.symm ▸ ⟨j, rfl⟩,
        fun h => hne (hinj h), hx⟩
  obtain ⟨_, _, hL2, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX
    (by simp) hK.1
  have hreal : ∀ L ∈ {L : Subgroup X | IsFundamentalOver (p ^ f) L},
      ∃ R ∈ longRootSetU (K := F) (p := p) (f := f) (by omega : 2 ≤ 2 * m + 1 + 1),
        L = R.map ψc := by
    intro L hL
    exact exists_unitary_root_of_isFundamentalOver hp2 hadm hX hL2 eU heU ψc hψc hkerC hL
  have hΩ : ∀ j : Fin (m + 1), (unitaryFrameBlock F p f m j).map ψc ∈
      {L : Subgroup X | IsFundamentalOver (p ^ f) L} := fun j =>
    (show (unitaryFrameBlock F p f m j).map ψc ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) from
      hfull'.symm ▸ ⟨j, rfl⟩).1
  rw [hΓ]
  let Γ := {x : X | ∃ j : Fin (m + 1), j ≠ k ∧ x ∈ (unitaryFrameBlock F p f m j).map ψc}
  apply le_antisymm
  · refine iSup₂_le fun L hL => ?_
    obtain ⟨R, hR, rfl⟩ := hreal L hL.1
    have hcR : ∀ j : Fin (m + 1), j ≠ k → Commutes R (unitaryFrameBlock F p f m j) := by
      intro j hj
      apply commutes_unitaryFund_of_commutes_map hp2 hadm eU heU ψc hkerC hR
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp (hL.2 ha) b ⟨j, hj, hb⟩).symm
    obtain ⟨z, hz⟩ := hR
    have heq := eq_unitaryFrameBlock_of_commutes_other_blocks hm hF hp2 hz k hcR
    exact Subgroup.map_mono heq.le
  · have hcentral : (unitaryFrameBlock F p f m k).map ψc ≤ centralizer Γ := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      rintro b ⟨j, hj, hb⟩
      obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
      simpa only [map_mul] using (congrArg ψc (commutes_unitaryFrameBlock (tail := 0) hj.symm a₀ ha₀ b₀ hb₀)).symm
    exact le_centralizingLayer ⟨hΩ k, hcentral⟩

theorem exists_full_coordinate_frame_funSet_psu_odd
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hadm : StatedLieAdmissible .PSU (2 * m + 1 + 1 + 1) p f) (hX : CFSG.Blueprint.LieModel X .PSU (2 * m + 1 + 1 + 1) p f)
    (e : (modelUniv .PSU (2 * m + 1 + 1 + 1) p f hp.out).K ≃*
      Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1 + 1))
    (he : ∀ R : Subgroup (modelUniv .PSU (2 * m + 1 + 1 + 1) p f hp.out).K,
      R ∈ fundamentalSubgroups .PSU (modelUniv .PSU (2 * m + 1 + 1 + 1) p f hp.out).D ↔
        R.map e.toMonoidHom ∈ longRootSetU (K := GaloisField p (2 * f))
          (p := p) (f := f) (by omega : 2 ≤ 2 * m + 1 + 1 + 1))
    (ψ : Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1 + 1) →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ center (Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1 + 1))) (P : Sylow 2 X) :
    ∃ c : X,
      F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
        Set.range (fun k : Fin (m + 1) =>
          ((unitaryFrameBlock (GaloisField p (2 * f)) p f m k 1).map ψ).map (MulAut.conj c).toMonoidHom) := by
  let F := GaloisField p (2 * f)
  have h2 : (2 : F) ≠ 0 := CFSG.ClassicalInvolution.RouteD.two_ne_zero_galoisField hp2
  have hF : Nat.card F = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hadm.2.1
  let A : Fin (m + 1) → Subgroup X := fun k => (unitaryFrameBlock F p f m k 1).map ψ
  have hroots : ∀ k : Fin (m + 1), unitaryFrameBlock F p f m k 1 ∈
      longRootSetU (K := F) (p := p) (f := f) (by omega : 2 ≤ 2 * m + 1 + 1 + 1) := fun k =>
    ⟨unitaryFrameInvolution F p f m k 1, isLongRootSU2_unitaryFrameBlock hF hp2 k 1⟩
  have hA : ∀ k, IsFundamentalOver (p ^ f) (A k) := fun k =>
    isFundamentalOver_unitary_root_map hp2 hadm e he ψ hψ hker (hroots k)
  have hblockcomm : ∀ {k j : Fin (m + 1)}, k ≠ j →
      Commutes (unitaryFrameBlock F p f m k 1) (unitaryFrameBlock F p f m j 1) := fun h => commutes_unitaryFrameBlock (tail := 1) h
  have hcomm : ∀ k j, k ≠ j → Commutes (A k) (A j) := by
    intro k j hkj a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    simpa only [map_mul] using congrArg ψ (hblockcomm hkj a₀ ha₀ b₀ hb₀)
  have hnorm : ∀ k j, A j ≤ normalizer (A k : Set X) := by
    intro k j
    by_cases hkj : k = j
    · rw [hkj]
      exact Subgroup.le_normalizer
    · have hc : A j ≤ centralizer (A k : Set X) := by
        intro a ha
        exact Subgroup.mem_centralizer_iff.mpr fun b hb => hcomm k j hkj b hb a ha
      exact hc.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨c, hc⟩ := F14.exists_conj_family_mem_funSet (𝔉 := fundPred (p ^ f))
    (fun g _ h => isFundamentalOver_map_mulEquiv (MulAut.conj g) h) A hA hnorm P
  let ψc : Su F p f (2 * m + 1 + 1 + 1) →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center (Su F p f (2 * m + 1 + 1 + 1)) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  have hc' : ∀ k, (unitaryFrameBlock F p f m k 1).map ψc ∈
      F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) := by
    intro k
    simpa [A, ψc, Subgroup.map_map] using hc k
  let k0 : Fin (m + 1) := 0
  obtain ⟨hZ, _, hL2, hΩ⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX
    (by simp) (hc' k0).1
  have hdesc : ∃ (t : StatedLieTag) (n e : ℕ), StatedLieAdmissible t n p e ∧
      p ^ f = p ^ e ∧ CFSG.Blueprint.LieModel (X ⧸ center X) t n p e :=
    ⟨.PSU, 2 * m + 1 + 1 + 1, f, hadm, rfl, hX.quotient_center hZ⟩
  refine ⟨c, ?_⟩
  ext L
  constructor
  · intro hL
    by_contra hnot
    have hne : ∀ k, L ≠ (unitaryFrameBlock F p f m k 1).map ψc := by
      intro k heq
      apply hnot
      exact ⟨k, by simpa [A, ψc, Subgroup.map_map] using heq.symm⟩
    obtain ⟨R, hR, hLR⟩ := exists_unitary_root_of_isFundamentalOver hp2 hadm hX hL2
      e he ψc hψc hkerC hL.1
    have hcR : ∀ k, Commutes (R.map ψc) ((unitaryFrameBlock F p f m k 1).map ψc) := by
      intro k
      rw [← hLR]
      have h := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.funSet_commute_of_lieModel
        hp.out hp2 hdesc hL2 P hL (hc' k) (hne k)
      exact fun a ha b hb => (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha) b hb).symm
    obtain ⟨z, hz⟩ := hR
    have hcR' : ∀ j : Fin (m + 1), Commutes R (unitaryFrameBlock F p f m j 1) :=
      fun j => commutes_unitaryFund_of_commutes_map hp2 hadm e he ψc hkerC ⟨z, hz⟩ (hcR j)
    exact not_commutes_all_unitaryFrameBlocks_odd hF hp2 hz hcR'
  · rintro ⟨k, rfl⟩
    exact hc k



theorem nonempty_equiv_perm_funSet_psu_odd
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hadm : StatedLieAdmissible .PSU (2 * m + 1 + 1 + 1) p f) (hX : CFSG.Blueprint.LieModel X .PSU (2 * m + 1 + 1 + 1) p f)
    (P : Sylow 2 X) :
    let Δ := F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)
    Nonempty ((conjPermHom (le_refl (conjSetStab Δ))).range ≃* Equiv.Perm (Fin (m + 1))) := by
  obtain ⟨ψ0, hψ0, hker0⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSU (2 * m + 1 + 1 + 1) p f hp.out hp2 (by trivial) hadm X hX
  obtain ⟨eU, heU⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  let ψ : Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1 + 1) →* X := ψ0.comp eU.symm.toMonoidHom
  have hψ : Function.Surjective ψ := hψ0.comp eU.symm.surjective
  have hker : ψ.ker ≤ center (Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1 + 1)) := by
    intro x hx
    have hx' : eU.symm x ∈ center (modelUniv .PSU (2 * m + 1 + 1 + 1) p f hp.out).K := hker0 hx
    rw [Subgroup.mem_center_iff] at hx' ⊢
    intro y
    apply eU.symm.injective
    simpa only [map_mul] using hx' (eU.symm y)
  have hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hadm.2.1
  obtain ⟨c, hfull⟩ := exists_full_coordinate_frame_funSet_psu_odd hp2 hm hadm hX
    eU heU ψ hψ hker P
  let ψc : Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1 + 1) →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hkerC : ψc.ker ≤ center (Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1 + 1)) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  have hfull' : F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      Set.range (fun k : Fin (m + 1) => (unitaryFrameBlock (GaloisField p (2 * f)) p f m k 1).map ψc) := by
    simpa [ψc, Subgroup.map_map] using hfull
  rw [hfull']
  classical
  let Δ := Set.range (fun k : Fin (m + 1) => (unitaryFrameBlock (GaloisField p (2 * f)) p f m k 1).map ψc)
  let d : Fin (m + 1) → Δ := fun k => ⟨(unitaryFrameBlock (GaloisField p (2 * f)) p f m k 1).map ψc, ⟨k, rfl⟩⟩
  have hd : Function.Bijective d := by
    constructor
    · intro i j heq
      by_contra hij
      exact F14.map_ne_of_commuting_of_equiv_sl2 ψc hkerC
        (Classical.choice (nonempty_equiv_sl2_unitaryFrameBlock (F := GaloisField p (2 * f)) (p := p) (f := f) (m := m) (tail := 1) hF i))
        (fun a ha b hb => commutes_unitaryFrameBlock (tail := 1) hij a ha b hb) (congrArg Subtype.val heq)
    · rintro ⟨L, k, rfl⟩
      exact ⟨k, rfl⟩
  let e : Fin (m + 1) ≃ Δ := Equiv.ofBijective d hd
  have hρ : Function.Surjective (conjPermHom (le_refl (conjSetStab Δ))) :=
    surjective_conjPermHom_of_indexed_conjugations e fun σ => by
      obtain ⟨g, hg⟩ := exists_conj_oddUnitaryFrameBlock_permutation (F := GaloisField p (2 * f)) (f := f)
        hp2 σ
      refine ⟨ψc g, fun k => ?_⟩
      change ((unitaryFrameBlock (GaloisField p (2 * f)) p f m k 1).map ψc).map
        (MulAut.conj (ψc g)).toMonoidHom =
          (unitaryFrameBlock (GaloisField p (2 * f)) p f m (σ k) 1).map ψc
      have hhom : (MulAut.conj (ψc g)).toMonoidHom.comp ψc =
          ψc.comp (MulAut.conj g).toMonoidHom := by
        ext x
        simp [MulAut.conj_apply]
      rw [Subgroup.map_map, hhom, ← Subgroup.map_map, hg]
  have htop := MonoidHom.range_eq_top.mpr hρ
  exact ⟨(MulEquiv.subgroupCongr htop).trans
    (Subgroup.topEquiv.trans e.symm.permCongrHom)⟩

theorem centralizingLayer_funSet_eq_triple_map_of_psu_odd
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hadm : StatedLieAdmissible .PSU (2 * m + 1 + 1 + 1) p f) (hX : CFSG.Blueprint.LieModel X .PSU (2 * m + 1 + 1 + 1) p f)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)) :
    ∃ (ψ : Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1 + 1) →* X)
      (k : Fin (m + 1)),
      ψ.ker ≤ center (Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1 + 1)) ∧
      centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ f) L}
        {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X), L ≠ K ∧ x ∈ L} =
          (coordBlockSU (GaloisField p (2 * f)) p f (linearFrameTriple m k)).map ψ := by
  obtain ⟨ψ0, hψ0, hker0⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    .PSU (2 * m + 1 + 1 + 1) p f hp.out hp2 (by trivial) hadm X hX
  obtain ⟨eU, heU⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  let ψ : Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1 + 1) →* X := ψ0.comp eU.symm.toMonoidHom
  have hψ : Function.Surjective ψ := hψ0.comp eU.symm.surjective
  have hker : ψ.ker ≤ center (Su (GaloisField p (2 * f)) p f (2 * m + 1 + 1 + 1)) := by
    intro x hx
    have hx' : eU.symm x ∈ center (modelUniv .PSU (2 * m + 1 + 1 + 1) p f hp.out).K := hker0 hx
    rw [Subgroup.mem_center_iff] at hx' ⊢
    intro y
    apply eU.symm.injective
    simpa only [map_mul] using hx' (eU.symm y)
  have hF : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p f hadm.2.1
  obtain ⟨c, hfull⟩ := exists_full_coordinate_frame_funSet_psu_odd hp2 hm hadm hX
    eU heU ψ hψ hker P
  let F := GaloisField p (2 * f)
  let ψc : Su F p f (2 * m + 1 + 1 + 1) →* X := (MulAut.conj c).toMonoidHom.comp ψ
  have hψc : Function.Surjective ψc := (MulAut.conj c).surjective.comp hψ
  have hkerC : ψc.ker ≤ center (Su F p f (2 * m + 1 + 1 + 1)) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  have hfull' : F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) =
      Set.range (fun k : Fin (m + 1) => (unitaryFrameBlock F p f m k 1).map ψc) := by
    simpa [ψc, Subgroup.map_map] using hfull
  have hKrange : K ∈ Set.range (fun k : Fin (m + 1) => (unitaryFrameBlock F p f m k 1).map ψc) := hfull' ▸ hK
  obtain ⟨k, rfl⟩ := hKrange
  have hinj : Function.Injective (fun j : Fin (m + 1) => (unitaryFrameBlock F p f m j 1).map ψc) := by
    intro i j heq
    by_contra hij
    exact F14.map_ne_of_commuting_of_equiv_sl2 ψc hkerC
      (Classical.choice (nonempty_equiv_sl2_unitaryFrameBlock (F := GaloisField p (2 * f)) (p := p) (f := f) (m := m) (tail := 1) hF i))
      (fun a ha b hb => commutes_unitaryFrameBlock (tail := 1) hij a ha b hb) heq
  have hΓ : {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X),
      L ≠ (unitaryFrameBlock F p f m k 1).map ψc ∧ x ∈ L} =
      {x : X | ∃ j : Fin (m + 1), j ≠ k ∧ x ∈ (unitaryFrameBlock F p f m j 1).map ψc} := by
    ext x
    constructor
    · rintro ⟨L, hL, hne, hx⟩
      rw [hfull'] at hL
      obtain ⟨j, rfl⟩ := hL
      exact ⟨j, fun h => hne (h ▸ rfl), hx⟩
    · rintro ⟨j, hne, hx⟩
      exact ⟨(unitaryFrameBlock F p f m j 1).map ψc, hfull'.symm ▸ ⟨j, rfl⟩,
        fun h => hne (hinj h), hx⟩
  obtain ⟨_, _, hL2, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX
    (by simp) hK.1
  have hreal : ∀ L ∈ {L : Subgroup X | IsFundamentalOver (p ^ f) L},
      ∃ R ∈ longRootSetU (K := F) (p := p) (f := f) (by omega : 2 ≤ 2 * m + 1 + 1 + 1),
        L = R.map ψc := by
    intro L hL
    exact exists_unitary_root_of_isFundamentalOver hp2 hadm hX hL2 eU heU ψc hψc hkerC hL
  refine ⟨ψc, k, hkerC, ?_⟩
  rw [hΓ]
  let Γ := {x : X | ∃ j : Fin (m + 1), j ≠ k ∧ x ∈ (unitaryFrameBlock F p f m j 1).map ψc}
  apply le_antisymm
  · refine iSup₂_le fun L hL => ?_
    obtain ⟨R, hR, rfl⟩ := hreal L hL.1
    have hcR : ∀ j : Fin (m + 1), j ≠ k → Commutes R (unitaryFrameBlock F p f m j 1) := by
      intro j hj
      apply commutes_unitaryFund_of_commutes_map hp2 hadm eU heU ψc hkerC hR
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp (hL.2 ha) b ⟨j, hj, hb⟩).symm
    obtain ⟨z, hz⟩ := hR
    exact Subgroup.map_mono (le_tripleBlock_of_commutes_other_unitaryFrameBlocks hF hp2 hz k hcR)
  · apply (Subgroup.map_mono (unitaryTripleBlock_le_iSup_supported_pairs hF hp2 k)).trans
    rw [Subgroup.map_iSup]
    refine iSup_le fun T => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hT => ?_
    have hroot : LcU F p f T ∈ longRootSetU (K := F) (p := p) (f := f)
        (by omega : 2 ≤ 2 * m + 1 + 1 + 1) :=
      ⟨zEltU F p f T, isLongRootSU2_LcU (two_ne_zero_of_charP_ne_two hp2) _ T⟩
    have hΩ : IsFundamentalOver (p ^ f) ((LcU F p f T).map ψc) :=
      isFundamentalOver_unitary_root_map hp2 hadm eU heU ψc hψc hkerC hroot
    have hle : LcU F p f T ≤ coordBlockSU F p f (linearFrameTriple m k) := by
      rw [LcU_eq_coordBlockSU (two_ne_zero_of_charP_ne_two hp2)]
      intro g hg
      rw [mem_coordBlockSU_iff] at hg ⊢
      intro a b hab
      exact hg a b (hab.imp (fun ha ht => ha (hT ht)) (fun hb ht => hb (hT ht)))
    have hcent : (LcU F p f T).map ψc ≤ centralizer Γ := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      rintro y ⟨j, hj, hy⟩
      obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
      simpa only [map_mul] using (congrArg ψc
        (commutes_unitaryTripleBlock_unitaryFrameBlock hp2 hj x₀ (hle hx₀) y₀ hy₀)).symm
    exact le_centralizingLayer ⟨hΩ, hcent⟩


theorem lieModel_centralizingLayer_quotient_of_psu_odd
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {p m f : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (hadm : StatedLieAdmissible .PSU (2 * m + 1 + 1 + 1) p f)
    (hX : CFSG.Blueprint.LieModel X .PSU (2 * m + 1 + 1 + 1) p f)
    (P : Sylow 2 X) {K : Subgroup X}
    (hK : K ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X)) :
    let A := centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ f) L}
      {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X), L ≠ K ∧ x ∈ L}
    CFSG.Blueprint.LieModel (A ⧸ center A) .PSU 3 p f := by
  let A := centralizingLayer {L : Subgroup X | IsFundamentalOver (p ^ f) L}
    {x : X | ∃ L ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X), L ≠ K ∧ x ∈ L}
  obtain ⟨hZ, _, hL2, _⟩ := fundamental_ambient_of_lieModel hp.out hp2 hadm hX (by simp) hK.1
  have hdesc : ∃ (t : StatedLieTag) (n e : ℕ), StatedLieAdmissible t n p e ∧
      p ^ f = p ^ e ∧ CFSG.Blueprint.LieModel (X ⧸ center X) t n p e :=
    ⟨.PSU, 2 * m + 1 + 1 + 1, f, hadm, rfl, hX.quotient_center hZ⟩
  have hKle : K ≤ A := by
    apply le_centralizingLayer
    refine ⟨hK.1, ?_⟩
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨L, hL, hne, hy⟩
    have hc := CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.funSet_commute_of_lieModel
      hp.out hp2 hdesc hL2 P hK hL hne.symm
    exact Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc hx) y hy
  have hAne : A ≠ ⊥ := fun h => hK.1.ne_bot (le_bot_iff.mp (h ▸ hKle))
  obtain ⟨ψ, k, _, heq⟩ := centralizingLayer_funSet_eq_triple_map_of_psu_odd hp2 hm hadm hX P hK
  have hne : (coordBlockSU (GaloisField p (2 * f)) p f (linearFrameTriple m k)).map ψ ≠ ⊥ := by
    simpa only [← heq] using hAne
  have hmodel := lieModel_unitaryTripleBlock_map_quotient hp2 hadm.2.1 ψ k hne
  exact CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv
    (MulEquiv.subgroupCongr heq.symm) hmodel

end CFSG.LocalAnalysis.UniquenessCase.UC22
