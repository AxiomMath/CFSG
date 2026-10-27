module

import CFSG.LieType.Universal.SymplecticExtras.RankOne
import all CFSG.LieType.Universal.SymplecticExtras.Matrices
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Iso
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Smith

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Open
open CFSG.Quasithin.SmithCurtis CFSG.QuasithinUnique.Setup.X7 TauCeti.GLSymplecticFin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open scoped Matrix

variable {k : Type} [Field k] [CharP k 2]

private theorem spXEquiv_bijective {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (i : Fin n) : Function.Bijective (fun c : K =>
      (⟨elt (simpleIdx i) c, (mem_X_iff i).mpr ⟨c, rfl⟩⟩ : (spCurtisDatum n K).X i)) := by
  refine ⟨fun a b h => elt_injective (simpleIdx i) (congrArg Subtype.val h), fun x => ?_⟩
  obtain ⟨c, hc⟩ := (mem_X_iff i).mp x.2
  exact ⟨c, Subtype.ext hc.symm⟩

private noncomputable def spXEquiv {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (i : Fin n) : K ≃ (spCurtisDatum n K).X i :=
  Equiv.ofBijective _ (spXEquiv_bijective i)

private theorem sp_two_card_X (n : ℕ) (i : Fin n) :
    Nat.card ((spCurtisDatum n (ZMod 2)).X i) = 2 := by
  rw [← Nat.card_congr (spXEquiv i), Nat.card_zmod]

theorem spCurtisDatum_two_H (n : ℕ) : (spCurtisDatum n (ZMod 2)).H = ⊥ := by
  apply le_antisymm _ bot_le
  intro h hh
  rw [Subgroup.mem_bot]
  have hpow := spCurtisDatum_H_pow (n := n) (K := ZMod 2) hh
  rw [show Nat.card (ZMod 2) - 1 = 1 by rw [Nat.card_zmod]] at hpow
  simpa using hpow

private theorem curtisDatum_dScalar_eq_one {G : Type*} [Group G] {B : Type*} {M : CoxeterMatrix B}
    {W : Type*} [Group W] {cs : CoxeterSystem M W} {p : ℕ} (D : CurtisDatum G cs p) [Finite G]
    {k : Type*} [Field k] [CharP k 2] {χ : G → k} (hχ : χ 1 = 1) (s : B)
    (hX : Nat.card (D.X s) = 2) (hH : D.H = ⊥) : D.dScalar χ s = 1 := by
  classical
  let : Fintype (D.X s) := Fintype.ofFinite (D.X s)
  rw [CurtisDatum.dScalar.eq_1]
  have hcard : (Finset.univ.erase (1 : D.X s)).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
      show Fintype.card (D.X s) = 2 by rw [← Nat.card_eq_fintype_card, hX]]
  have hterm : ∀ x ∈ (Finset.univ : Finset (D.X s)).erase 1, χ (D.phi s x) = 1 := by
    intro x hx
    have hxne : x ≠ 1 := Finset.ne_of_mem_erase hx
    have hmem : D.phi s x ∈ D.H := D.phi_mem s x x.2 (fun h => hxne (OneMemClass.coe_eq_one.mp h))
    rw [hH] at hmem
    rw [show D.phi s x = 1 from by simpa using hmem, hχ]
  rw [Finset.sum_congr rfl (fun x hx => hterm x hx), Finset.sum_const, hcard, one_smul]

private theorem curtisDatum_d'Scalar_eq_one {G : Type*} [Group G] {B : Type*} {M : CoxeterMatrix B}
    {W : Type*} [Group W] {cs : CoxeterSystem M W} {p : ℕ} (D : CurtisDatum G cs p) [Finite G]
    {k : Type*} [Field k] [CharP k 2] {χ : G → k} (hχ : χ 1 = 1) (s : B)
    (hX : Nat.card (D.X s) = 2) (hH : D.H = ⊥) : D.d'Scalar χ s = 1 := by
  classical
  let : Fintype (D.X s) := Fintype.ofFinite (D.X s)
  rw [CurtisDatum.d'Scalar.eq_1]
  have hcard : (Finset.univ.erase (1 : D.X s)).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
      show Fintype.card (D.X s) = 2 by rw [← Nat.card_eq_fintype_card, hX]]
  have hterm : ∀ x ∈ (Finset.univ : Finset (D.X s)).erase 1, χ (D.psi s x) = 1 := by
    intro x hx
    have hxne : x ≠ 1 := Finset.ne_of_mem_erase hx
    have hmem : D.psi s x ∈ D.H := D.psi_mem s x x.2 (fun h => hxne (OneMemClass.coe_eq_one.mp h))
    rw [hH] at hmem
    rw [show D.psi s x = 1 from by simpa using hmem, hχ]
  rw [Finset.sum_congr rfl (fun x hx => hterm x hx), Finset.sum_const, hcard, one_smul]

theorem spCurtisDatum_two_dScalar {n : ℕ} {χ : StatedSp n (ZMod 2) → k} (hχ : χ 1 = 1)
    (s : Fin n) : (spCurtisDatum n (ZMod 2)).dScalar χ s = 1 := by
  exact curtisDatum_dScalar_eq_one (spCurtisDatum n (ZMod 2)) hχ s (sp_two_card_X n s)
    (spCurtisDatum_two_H n)

theorem spCurtisDatum_two_d'Scalar {n : ℕ} {χ : StatedSp n (ZMod 2) → k} (hχ : χ 1 = 1)
    (s : Fin n) : (spCurtisDatum n (ZMod 2)).d'Scalar χ s = 1 := by
  exact curtisDatum_d'Scalar_eq_one (spCurtisDatum n (ZMod 2)) hχ s (sp_two_card_X n s)
    (spCurtisDatum_two_H n)

omit [CharP k 2] in
theorem isSimpleRep_representation_trivial (G : Type) [Group G] :
    IsSimpleRep (Representation.trivial k G k) := by
  refine ⟨inferInstance, fun W _ => Ideal.eq_bot_or_top W⟩

theorem isCurtisType_sp_two_trivial {n : ℕ} {χ : StatedSp n (ZMod 2) → k} (hχ : χ 1 = 1) :
    (spCurtisDatum n (ZMod 2)).IsCurtisType
      (Representation.trivial k (StatedSp n (ZMod 2)) k) 1 χ 0 := by
  refine ⟨?_, one_ne_zero, ?_, ?_⟩
  · intro u _
    rw [Representation.trivial_apply]
  · intro h hh
    have h1 : h = 1 := by
      have hmem : h ∈ (spCurtisDatum n (ZMod 2)).H := hh
      rw [spCurtisDatum_two_H n] at hmem
      simpa using hmem
    subst h1
    simp [hχ]
  · intro s
    let D := spCurtisDatum n (ZMod 2)
    have : Fintype (D.X s) := Fintype.ofFinite _
    rw [CurtisDatum.heckeT_apply D]
    simp only [Representation.trivial_apply]
    rw [Finset.sum_const, Finset.card_univ,
      show Fintype.card (D.X s) = 2 by rw [← Nat.card_eq_fintype_card, sp_two_card_X n s]]
    simp only [Pi.zero_apply, zero_smul, nsmul_eq_mul, mul_one]
    exact CharTwo.two_eq_zero

private theorem sp_map_E_of_ringHomClass {n : ℕ} (φ : ZMod 2 →+* k) (r : RootSubgroupIndex n) :
    (E (ZMod 2) r).map φ = E k r := by
  ext a b
  cases r <;> simp only [E, Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.single_apply] <;> split_ifs <;> simp [CharTwo.neg_eq]

private theorem sp_matMap_elt {n : ℕ} (φ : ZMod 2 →+* k) (r : RootSubgroupIndex n)
    (c : ZMod 2) : matMap φ (mat n (ZMod 2)) (elt r c) = 1 + φ c • E k r := by
  rw [matMap_apply, mat_elt, Matrix.map_add φ φ.map_add,
    Matrix.map_one φ (map_zero φ) (map_one φ),
    Matrix.map_smul' φ c (E (ZMod 2) r) φ.map_mul,
    sp_map_E_of_ringHomClass φ r]

private theorem sp_natMap_elt {n : ℕ} (φ : ZMod 2 →+* k) (r : RootSubgroupIndex n)
    (c : ZMod 2) (v : Fin n ⊕ Fin n → k) :
    matRep (matMap φ (mat n (ZMod 2))) (elt r c) v = v + φ c • (E k r *ᵥ v) := by
  rw [matRep_apply, sp_matMap_elt, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]

omit [CharP k 2] in
private theorem sp_E_difference_mulVec {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (v : Fin n ⊕ Fin n → k) :
    E k (.difference i j hij) *ᵥ v =
      v (Sum.inl j) • Pi.single (Sum.inl i) (1 : k) -
        v (Sum.inr i) • Pi.single (Sum.inr j) (1 : k) := by
  simp only [E, Matrix.sub_mulVec, Matrix.single_mulVec_eq, one_mul]

omit [CharP k 2] in
private theorem sp_E_positiveLong_mulVec {n : ℕ} (i : Fin n) (v : Fin n ⊕ Fin n → k) :
    E k (.positiveLong i) *ᵥ v = v (Sum.inr i) • Pi.single (Sum.inl i) (1 : k) := by
  simp only [E, Matrix.single_mulVec_eq, one_mul]

omit [CharP k 2] in
private theorem sp_E_negativeLong_mulVec {n : ℕ} (i : Fin n) (v : Fin n ⊕ Fin n → k) :
    E k (.negativeLong i) *ᵥ v = v (Sum.inl i) • Pi.single (Sum.inr i) (1 : k) := by
  simp only [E, Matrix.single_mulVec_eq, one_mul]

omit [CharP k 2] in
theorem sp_E_simpleIdx_mulVec_e0 {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    E k (simpleIdx i) *ᵥ (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : k)) = 0 := by
  unfold simpleIdx
  split_ifs with h
  · rw [sp_E_difference_mulVec]
    have h1 : (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : k) : Fin n ⊕ Fin n → k)
        (Sum.inl (⟨i.val + 1, h⟩ : Fin n)) = 0 := by
      rw [Pi.single_apply]
      exact if_neg (fun hh => Nat.succ_ne_zero i.val (by
        simpa using congrArg Fin.val (Sum.inl.inj hh)))
    have h2 : (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : k) : Fin n ⊕ Fin n → k)
        (Sum.inr i) = 0 := by
      rw [Pi.single_apply]
      exact if_neg (fun hh => Sum.inr_ne_inl hh)
    rw [h1, h2, zero_smul, zero_smul, sub_zero]
  · rw [sp_E_positiveLong_mulVec]
    have h2 : (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : k) : Fin n ⊕ Fin n → k)
        (Sum.inr i) = 0 := by
      rw [Pi.single_apply]
      exact if_neg (fun hh => Sum.inr_ne_inl hh)
    rw [h2, zero_smul]

omit [CharP k 2] in
theorem sp_E_simpleIdx_zero_mulVec_e1 {n : ℕ} (hn : 2 ≤ n) :
    E k (simpleIdx (⟨0, by omega⟩ : Fin n)) *ᵥ
      (Pi.single (Sum.inl ⟨1, by omega⟩) (1 : k) : Fin n ⊕ Fin n → k) =
      Pi.single (Sum.inl ⟨0, by omega⟩) (1 : k) := by
  have h0 : (⟨0, by omega⟩ : Fin n).val + 1 < n := by
    show 0 + 1 < n
    omega
  unfold simpleIdx
  rw [dif_pos h0]
  rw [sp_E_difference_mulVec]
  have h1 : (Pi.single (Sum.inl ⟨1, by omega⟩) (1 : k) : Fin n ⊕ Fin n → k)
      (Sum.inl (⟨0 + 1, h0⟩ : Fin n)) = 1 := by
    rw [Pi.single_apply]
    exact if_pos (by simp)
  have h2 : (Pi.single (Sum.inl ⟨1, by omega⟩) (1 : k) : Fin n ⊕ Fin n → k)
      (Sum.inr (⟨0, by omega⟩ : Fin n)) = 0 := by
    rw [Pi.single_apply]
    exact if_neg (fun hh => Sum.inr_ne_inl hh)
  rw [h1, h2, one_smul, zero_smul, sub_zero]

omit [CharP k 2] in
theorem sp_E_difference_mulVec_e0 {n : ℕ} (hn : 2 ≤ n) {a b : Fin n} (hab : a ≠ b)
    (hb : b.val ≠ 0) :
    E k (.difference a b hab) *ᵥ (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : k)) = 0 := by
  rw [sp_E_difference_mulVec]
  have h1 : (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : k) : Fin n ⊕ Fin n → k)
      (Sum.inl b) = 0 := by
    rw [Pi.single_apply]
    exact if_neg (fun hh => hb (by simpa using congrArg Fin.val (Sum.inl.inj hh)))
  have h2 : (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : k) : Fin n ⊕ Fin n → k)
      (Sum.inr a) = 0 := by
    rw [Pi.single_apply]
    exact if_neg (fun hh => Sum.inr_ne_inl hh)
  rw [h1, h2, zero_smul, zero_smul, sub_zero]

omit [CharP k 2] in
theorem sp_E_positiveLong_mulVec_e0 {n : ℕ} (hn : 2 ≤ n) (a : Fin n) :
    E k (.positiveLong a) *ᵥ (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : k)) = 0 := by
  rw [sp_E_positiveLong_mulVec]
  have h2 : (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : k) : Fin n ⊕ Fin n → k)
      (Sum.inr a) = 0 := by
    rw [Pi.single_apply]
    exact if_neg (fun hh => Sum.inr_ne_inl hh)
  rw [h2, zero_smul]

omit [CharP k 2] in
theorem sp_E_negativeLong_mulVec_e0 {n : ℕ} (hn : 2 ≤ n) {a : Fin n}
    (ha : a.val ≠ 0) :
    E k (.negativeLong a) *ᵥ (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : k)) = 0 := by
  rw [sp_E_negativeLong_mulVec]
  have h1 : (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : k) : Fin n ⊕ Fin n → k)
      (Sum.inl a) = 0 := by
    rw [Pi.single_apply]
    exact if_neg (fun hh => ha (by simpa using congrArg Fin.val (Sum.inl.inj hh)))
  rw [h1, zero_smul]

omit [CharP k 2] in
theorem sp_E_difference_mulVec_e1 {n : ℕ} (hn : 2 ≤ n) {a b : Fin n} (hab : a ≠ b)
    (ha : a.val = 0) (hb : b.val = 1) :
    E k (.difference a b hab) *ᵥ (Pi.single (Sum.inl ⟨1, by omega⟩) (1 : k)) =
      Pi.single (Sum.inl ⟨0, by omega⟩) (1 : k) := by
  rw [sp_E_difference_mulVec]
  have h1 : (Pi.single (Sum.inl ⟨1, by omega⟩) (1 : k) : Fin n ⊕ Fin n → k)
      (Sum.inl b) = 1 := by
    rw [Pi.single_apply]
    exact if_pos (by simp [Fin.ext_iff, hb])
  have h2 : (Pi.single (Sum.inl ⟨1, by omega⟩) (1 : k) : Fin n ⊕ Fin n → k)
      (Sum.inr a) = 0 := by
    rw [Pi.single_apply]
    exact if_neg (fun hh => Sum.inr_ne_inl hh)
  rw [h1, h2, one_smul, zero_smul, sub_zero]
  congr 1
  exact congrArg Sum.inl (Fin.ext ha)

omit [CharP k 2] in
theorem sp_E_difference_mulVec_e0_of {n : ℕ} (hn : 2 ≤ n) {a b : Fin n} (hab : a ≠ b)
    (ha : a.val = 1) (hb : b.val = 0) :
    E k (.difference a b hab) *ᵥ (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : k)) =
      Pi.single (Sum.inl ⟨1, by omega⟩) (1 : k) := by
  rw [sp_E_difference_mulVec]
  have h1 : (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : k) : Fin n ⊕ Fin n → k)
      (Sum.inl b) = 1 := by
    rw [Pi.single_apply]
    exact if_pos (by simp [Fin.ext_iff, hb])
  have h2 : (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : k) : Fin n ⊕ Fin n → k)
      (Sum.inr a) = 0 := by
    rw [Pi.single_apply]
    exact if_neg (fun hh => Sum.inr_ne_inl hh)
  rw [h1, h2, one_smul, zero_smul, sub_zero]
  congr 1
  exact congrArg Sum.inl (Fin.ext ha)

private theorem sp_natMap_weyl {n : ℕ} (hn : 2 ≤ n) (φ : ZMod 2 →+* k) (i : Fin n) :
    matRep (matMap φ (mat n (ZMod 2))) (weylRep n (ZMod 2) i)
      (Pi.single (Sum.inl ⟨0, by omega⟩) (1 : k)) =
      if i.val = 0 then Pi.single (Sum.inl ⟨1, by omega⟩) (1 : k)
      else Pi.single (Sum.inl ⟨0, by omega⟩) (1 : k) := by
  by_cases hi : i.val = 0
  · rw [if_pos hi]
    have hi0 : i = ⟨0, by omega⟩ := Fin.ext hi
    rw [hi0]
    have h0 : (⟨0, by omega⟩ : Fin n).val + 1 < n := by show 0 + 1 < n; omega
    rw [CFSG.LieType.Universal.Symplectic.SpExtras.weylRep_eq_short h0]
    simp only [map_mul, Module.End.mul_apply, sp_natMap_elt,
      sp_E_difference_mulVec_e0 (n := n) hn (a := (⟨0, by omega⟩ : Fin n))
        (b := (⟨1, h0⟩ : Fin n)) (ne_succ' h0) (by simp),
      sp_E_difference_mulVec_e0_of (n := n) hn (a := (⟨1, h0⟩ : Fin n))
        (b := (⟨0, by omega⟩ : Fin n)) (ne_succ' h0).symm rfl rfl,
      sp_E_difference_mulVec_e1 (n := n) hn (a := (⟨0, by omega⟩ : Fin n))
        (b := (⟨1, h0⟩ : Fin n)) (ne_succ' h0) rfl rfl,
      Matrix.mulVec_add, map_one, CharTwo.neg_eq, one_smul, add_zero, zero_add]
    abel_nf
    ext a
    simp [CharTwo.two_eq_zero]
  · rw [if_neg hi]
    by_cases hshort : i.val + 1 < n
    · rw [CFSG.LieType.Universal.Symplectic.SpExtras.weylRep_eq_short hshort]
      simp only [map_mul, Module.End.mul_apply, sp_natMap_elt,
        sp_E_difference_mulVec_e0 (n := n) hn (a := i) (b := (⟨i.val + 1, hshort⟩ : Fin n))
          (ne_succ' hshort) (by simp),
        sp_E_difference_mulVec_e0 (n := n) hn (a := (⟨i.val + 1, hshort⟩ : Fin n)) (b := i)
          (ne_succ' hshort).symm hi,
        map_one, CharTwo.neg_eq, one_smul, add_zero]
    · rw [CFSG.LieType.Universal.Symplectic.SpExtras.weylRep_eq_long hshort]
      simp only [map_mul, Module.End.mul_apply, sp_natMap_elt,
        sp_E_positiveLong_mulVec_e0 (n := n) hn i,
        sp_E_negativeLong_mulVec_e0 (n := n) hn hi,
        map_one, CharTwo.neg_eq, one_smul, add_zero]

omit [CharP k 2] in
private theorem sp_natMap_fixU {n : ℕ} (hn : 2 ≤ n) (φ : ZMod 2 →+* k) :
    (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) ∈
      (spCurtisDatum n (ZMod 2)).fixU (matRep (matMap φ (mat n (ZMod 2)))) := by
  intro g hg
  change g ∈ ⨆ γ ∈ {γ | γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanC n) ∅ ∧
    0 < CFSG.LieType.Steinberg.ht γ}, rootGroup n (ZMod 2) γ at hg
  have hbelow := idBelow_of_mem_iSup 1 _ (fun γ hγ =>
    ⟨hγ.1, by
      have hpos : 0 < CFSG.LieType.Steinberg.ht γ := hγ.2
      simpa only [one_mul] using (show 1 ≤ CFSG.LieType.Steinberg.ht γ by omega)⟩) hg
  change ((mat n (ZMod 2) g).map φ) *ᵥ
    Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) = _
  ext a
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.map_apply]
  have hlev : (1 : ℤ) * lvl (Sum.inl (⟨0, by omega⟩ : Fin n)) - (1 : ℤ) * lvl a < 1 := by
    rcases a with i | i <;> simp only [lvl] <;> omega
  rw [hbelow _ _ hlev]
  simp [Matrix.one_apply, Pi.single_apply]

omit [CharP k 2] in
private theorem sp_sum_phi (φ : ZMod 2 →+* k) : (∑ c : ZMod 2, φ c) = 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide,
    Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
  simp

private theorem sp_natMap_hecke {n : ℕ} (hn : 2 ≤ n) (φ : ZMod 2 →+* k) (i : Fin n) :
    (spCurtisDatum n (ZMod 2)).heckeT (matRep (matMap φ (mat n (ZMod 2)))) i
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) =
      (if i.val = 0 then (1 : k) else 0) •
        Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
  classical
  have : Fintype ((spCurtisDatum n (ZMod 2)).X i) := Fintype.ofFinite _
  erw [CurtisDatum.heckeT_apply (spCurtisDatum n (ZMod 2))]
  have hbij := spXEquiv_bijective (K := ZMod 2) i
  rw [← hbij.sum_comp]
  simp only [map_mul, Module.End.mul_apply]
  erw [spCurtisDatum_n n (ZMod 2) i]
  rw [sp_natMap_weyl hn φ i]
  by_cases hi : i.val = 0
  · rw [if_pos hi, if_pos hi]
    have hterm : ∀ c : ZMod 2,
        matRep (matMap φ (mat n (ZMod 2))) (elt (simpleIdx i) c)
          (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin n)) (1 : k)) =
        Pi.single (Sum.inl (⟨1, by omega⟩ : Fin n)) (1 : k) +
          φ c • Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
      intro c
      have hi0 : i = ⟨0, by omega⟩ := Fin.ext hi
      rw [hi0, sp_natMap_elt, sp_E_simpleIdx_zero_mulVec_e1 hn]
    rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, ZMod.card, ← Finset.sum_smul, sp_sum_phi, one_smul]
    ext a
    simp [CharTwo.two_eq_zero]
  · rw [if_neg hi, if_neg hi]
    have hterm : ∀ c : ZMod 2,
        matRep (matMap φ (mat n (ZMod 2))) (elt (simpleIdx i) c)
          (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k)) =
        Pi.single (Sum.inl (⟨0, by omega⟩ : Fin n)) (1 : k) := by
      intro c
      rw [sp_natMap_elt, sp_E_simpleIdx_mulVec_e0 hn i, smul_zero, add_zero]
    rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_const, Finset.card_univ,
      ZMod.card, zero_smul]
    ext a
    simp [CharTwo.two_eq_zero]

theorem isCurtisType_sp_two_natural {n : ℕ} (hn : 2 ≤ n) (φ : ZMod 2 →+* k)
    {χ : StatedSp n (ZMod 2) → k} (hχ : χ 1 = 1) :
    (spCurtisDatum n (ZMod 2)).IsCurtisType (matRep (matMap φ (mat n (ZMod 2))))
      (Pi.single (Sum.inl ⟨0, by omega⟩) 1) χ (fun s => if s.val = 0 then 1 else 0) := by
  refine ⟨sp_natMap_fixU hn φ, Pi.single_ne_zero_iff.mpr one_ne_zero, ?_, sp_natMap_hecke hn φ⟩
  intro h hh
  have h1 : h = 1 := by
    have hmem : h ∈ (spCurtisDatum n (ZMod 2)).H := hh
    rw [spCurtisDatum_two_H n] at hmem
    simpa using hmem
  subst h1
  rw [map_one, Module.End.one_apply, hχ, one_smul]

end CFSG.LocalAnalysis.WeakClosure81
