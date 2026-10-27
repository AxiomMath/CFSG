module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDelete

import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitUnitaryGeometry
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitWeylGen
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitWeylXA
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosPermAux4
import CFSG.ClassicalInvolution.Asc77.AscIHSectG
import CFSG.ClassicalInvolution.AschTight.S1911P3a
import CFSG.ClassicalInvolution.AschTight.S1911P3b
import CFSG.ClassicalInvolution.AschTight.S1911SecG
import CFSG.ClassicalInvolution.AschTight.S1916FusStmt
import CFSG.ClassicalInvolution.Q3.Q3T6FaField
import CFSG.GH74.GLS.IVK.Lifted.GroupAux
import CFSG.GH74.GLS.IVK.Lifted.SolvAut
import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Prop46d
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.After
import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_7
import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements129b
import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQO
import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step25
import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FunHypOmegaHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunHolds
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitLinearInner
import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitPermutationAction
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aF
import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

open scoped Matrix

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}

private theorem qtwoDB14_ggPermSU_coe {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {m : ℕ}
    (σ : Equiv.Perm (Fin m)) :
    (((ggPermSU (K := F0) (f := 1) σ : Su F0 2 1 m) : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) = σ.permMatrix F0 := rfl

private theorem qtwoDB14_mem_coordBlockSU_erase {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {m : ℕ} {c : Fin m} {x : Su F0 2 1 m}
    (hx : x • (Pi.single c 1 : Fin m → F0) = Pi.single c 1) :
    x ∈ coordBlockSU F0 2 1 (Finset.univ.erase c) :=
  CFSG.LocalAnalysis.UniquenessCase.UC22.mem_coordBlockSU_of_smul_single (p := 2) (f := 1) x
    (fun j hj => by
      have hj' : j = c := by
        by_contra h
        exact hj (Finset.mem_erase.mpr ⟨h, Finset.mem_univ j⟩)
      subst hj'
      exact hx)

private theorem qtwoDB14_diag_inv {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {m : ℕ}
    (c : Fin m → F0ˣ) :
    (qTwoChartTwoThree_diag c)⁻¹ = qTwoChartTwoThree_diag (fun j => (c j)⁻¹) := rfl

private theorem qtwoDB14_diag_mulVec_single {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {m : ℕ}
    (c : Fin m → F0ˣ) (i : Fin m) :
    ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *ᵥ
      Pi.single i 1 = (c i : F0) • Pi.single i 1 := by
  change Matrix.diagonal (fun j => ((c j : F0ˣ) : F0)) *ᵥ Pi.single i 1 =
    (c i : F0) • Pi.single i 1
  rw [Matrix.diagonal_mulVec_single, mul_one]
  simpa using Pi.single_smul' i (c i : F0) (1 : F0)

private theorem qtwoDB14_perm_mulVec_single {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {m : ℕ}
    {c : Fin m} (σ : Equiv.Perm (Fin m)) (hσ : σ c = c) :
    (((ggPermSU (K := F0) (f := 1) σ⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) *ᵥ Pi.single c 1 = Pi.single c 1 := by
  rw [qtwoDB14_ggPermSU_coe, Matrix.permMatrix_mulVec]
  funext i
  have hσinv : σ⁻¹ c = c := by
    have h := Equiv.symm_apply_apply σ c
    rw [hσ] at h
    exact h
  by_cases hi : i = c
  · subst hi
    rw [Function.comp_apply, hσinv, Pi.single_eq_same]
  · have hne : σ⁻¹ i ≠ c := fun h => hi (by
      have h' := congrArg (fun x => σ x) h
      simpa [hσ] using h')
    rw [Function.comp_apply, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hi]

private theorem qtwoDB14_diag_conj_perm_mem {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {m : ℕ} {c : Fin m} {c₀ : Fin m → F0ˣ} {u' : Su F0 2 1 m} (σ : Equiv.Perm (Fin m))
    (hσ : σ c = c)
    (hu' : (u' : GL (Fin m) F0) =
      qTwoChartTwoThree_diag c₀ * ggPermSU (K := F0) (f := 1) σ⁻¹ *
        (qTwoChartTwoThree_diag c₀)⁻¹) :
    u' ∈ coordBlockSU F0 2 1 (Finset.univ.erase c) := by
  refine qtwoDB14_mem_coordBlockSU_erase ?_
  show (((u' : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) *ᵥ Pi.single c 1 = Pi.single c 1
  rw [hu', Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    qtwoDB14_diag_inv]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [qtwoDB14_diag_mulVec_single (fun j => (c₀ j)⁻¹) c, Matrix.mulVec_smul,
    qtwoDB14_perm_mulVec_single σ hσ, Matrix.mulVec_smul,
    qtwoDB14_diag_mulVec_single c₀ c, smul_smul]
  rw [show (((c₀ c)⁻¹ : F0ˣ) : F0) * (c₀ c : F0) = 1 by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one], one_smul]

theorem qtwoDB14_perm_mem_coordBlockSU {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]
    {m : ℕ} {c : Fin m} (σ : Equiv.Perm (Fin m)) (hσ : σ c = c) :
    ggPermSU (K := F0) (f := 1) σ⁻¹ ∈ coordBlockSU F0 2 1 (Finset.univ.erase c) :=
  qtwoDB14_mem_coordBlockSU_erase (qtwoDB14_perm_mulVec_single σ hσ)


private theorem qtwoDB14_comm_mem_J1 (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) {c : Fin m}
    (σ : Equiv.Perm (Fin m)) (hσ : σ c = c) (t : ↥Bs) :
    ((t * (((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) t)⁻¹ : ↥Bs) : G) ∈
        (coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ ∧
      βL (Additive.ofMul (t * (((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) t)⁻¹)) =
        βL (Additive.ofMul t) - dPerm m σ (βL (Additive.ofMul t)) := by
  obtain ⟨u', hu'mat, hu'ψ⟩ := hcoords.induces t (ggPermSU (K := F0) (f := 1) σ⁻¹)
  have hσinv : σ⁻¹ c = c := by
    have h := Equiv.symm_apply_apply σ c
    rw [hσ] at h
    exact h
  have hpermJ : ψ (ggPermSU (K := F0) (f := 1) σ⁻¹) ∈
      (coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ :=
    Subgroup.mem_map_of_mem _ (qtwoDB14_perm_mem_coordBlockSU σ hσ)
  have hconjJ : (t : G) * ψ (ggPermSU (K := F0) (f := 1) σ⁻¹) * (t : G)⁻¹ ∈
      (coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ := by
    rw [← hu'ψ]
    exact Subgroup.mem_map_of_mem _ (qtwoDB14_diag_conj_perm_mem σ hσ hu'mat)
  constructor
  · have hb := hbase.perm σ t
    have heq : ((t * (((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) t)⁻¹ : ↥Bs) : G) =
        ((t : G) * ψ (ggPermSU (K := F0) (f := 1) σ⁻¹) * (t : G)⁻¹) *
          (ψ (ggPermSU (K := F0) (f := 1) σ⁻¹))⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hb]
      group
    rw [heq]
    exact mul_mem hconjJ (Subgroup.inv_mem _ hpermJ)
  · have hcoord : βL (Additive.ofMul (t * (((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) t)⁻¹)) =
        βL (Additive.ofMul t) -
          βL (Additive.ofMul (((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) t)) := by
      simp [map_add, sub_eq_add_neg]
    rw [hcoord, hcoords.perm σ t]

private theorem qtwoDB14_dPerm_single {m : ℕ} (i j : Fin m) :
    dPerm m (Equiv.swap i j) (Pi.single i 1) = Pi.single j 1 := by
  rw [show (Pi.single i 1 : DVec m) = dBasis m i by rw [dBasis, Pi.basisFun_apply],
    dPerm_apply, Equiv.swap_apply_left,
    show dBasis m j = (Pi.single j 1 : DVec m) by rw [dBasis, Pi.basisFun_apply]]

private theorem qtwoDB14_dSign_single_self {m : ℕ} (a b : Fin m) :
    dSign m a b (Pi.single a 1) = -Pi.single a 1 := by
  rw [show (Pi.single a 1 : DVec m) = dBasis m a by rw [dBasis, Pi.basisFun_apply],
    dSign_apply, if_pos (Or.inl rfl), neg_one_smul,
    show dBasis m a = (Pi.single a 1 : DVec m) by rw [dBasis, Pi.basisFun_apply]]

private theorem qtwoDB14_dSign_single_of_ne {m : ℕ} {a b k : Fin m} (hka : k ≠ a)
    (hkb : k ≠ b) :
    dSign m a b (Pi.single k 1) = Pi.single k 1 := by
  rw [show (Pi.single k 1 : DVec m) = dBasis m k by rw [dBasis, Pi.basisFun_apply],
    dSign_apply, if_neg (fun h => h.elim hka hkb), one_smul,
    show dBasis m k = (Pi.single k 1 : DVec m) by rw [dBasis, Pi.basisFun_apply]]

private theorem qtwoDB14_sum_smul_single {F0 : Type} [Field F0] {m : ℕ} (v : Fin m → F0) :
    v = ∑ i, v i • (Pi.single i 1 : Fin m → F0) := by
  funext j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hij), smul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

private theorem qtwoDB14_span_erase {m : ℕ} {a b c : Fin m} (hab : a ≠ b) (hca : c ≠ a)
    (hcb : c ≠ b) (hm : 5 ≤ m) (A : Set (DVec m))
    (hA1 : ∀ i j : Fin m, i ≠ c → j ≠ c → i ≠ j →
      (Pi.single i 1 - Pi.single j 1 : DVec m) ∈ A)
    (hA2 : ∀ k : Fin m, k ≠ c → k ≠ a → k ≠ b →
      (Pi.single a 1 + Pi.single k 1 : DVec m) ∈ A) :
    ∀ v : DVec m, v c = 0 → v ∈ Submodule.span (ZMod 3) A := by
  classical
  have hcard : ({c, a, b} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have h3 : ({c, a, b} : Finset (Fin m)).card ≤ 3 := by
      have h1 : ({c, a, b} : Finset (Fin m)).card ≤ ({a, b} : Finset (Fin m)).card + 1 :=
        Finset.card_insert_le c ({a, b} : Finset (Fin m))
      have h2 : ({a, b} : Finset (Fin m)).card ≤ ({b} : Finset (Fin m)).card + 1 :=
        Finset.card_insert_le a ({b} : Finset (Fin m))
      have hb : ({b} : Finset (Fin m)).card ≤ 1 := by simp
      omega
    omega
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  obtain ⟨hkc, hka, hkb⟩ := hk
  intro v hvc
  let w : DVec m := v - (2 * (∑ j, v j)) • (Pi.single a 1 + Pi.single k 1)
  have hAc : (Pi.single a 1 + Pi.single k 1 : DVec m) ∈ A := hA2 k hkc hka hkb
  have hwc : w c = 0 := by
    simp [w, hvc, Ne.symm hca, hkc]
  have hwsum : ∑ i, w i = 0 := by
    have hf : ∑ i, ((Pi.single a 1 + Pi.single k 1 : DVec m) i) = 2 := by
      simp_rw [Pi.add_apply]
      rw [Finset.sum_add_distrib]
      have ha : (∑ i, (Pi.single a 1 : DVec m) i) = 1 := by
        rw [Finset.sum_eq_single a]
        · simp
        · intro i _ hi; simp [Pi.single_eq_of_ne hi]
        · intro h; exact absurd (Finset.mem_univ a) h
      have hksum : (∑ i, (Pi.single k 1 : DVec m) i) = 1 := by
        rw [Finset.sum_eq_single k]
        · simp
        · intro i _ hi; simp [Pi.single_eq_of_ne hi]
        · intro h; exact absurd (Finset.mem_univ k) h
      rw [ha, hksum]
      norm_num
    simp only [w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hf]
    have h2 : (2 : ZMod 3) * 2 = 1 := by decide
    calc (∑ j, v j) - 2 * (∑ j, v j) * 2 = (∑ j, v j) - (∑ j, v j) * (2 * 2) := by ring
      _ = (∑ j, v j) - (∑ j, v j) * 1 := by rw [h2]
      _ = 0 := by ring
  have hwexp : w = ∑ i, w i • (Pi.single i 1 - Pi.single b 1) := by
    conv_lhs => rw [qtwoDB14_sum_smul_single w]
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hwsum, zero_smul, sub_zero]
  have hVw : w ∈ Submodule.span (ZMod 3) A := by
    rw [hwexp]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    by_cases hic : i = c
    · subst hic; rw [hwc, zero_smul]; exact Submodule.zero_mem _
    · by_cases hib : i = b
      · subst hib; rw [sub_self, smul_zero]; exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (hA1 i b hic hcb.symm hib))
  have hv : v = w + (2 * (∑ j, v j)) • (Pi.single a 1 + Pi.single k 1) := by
    simp only [w]; abel
  rw [hv]
  exact Submodule.add_mem _ hVw (Submodule.smul_mem _ _ (Submodule.subset_span hAc))

theorem ggQTwoDUnit_torus (hm : 5 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) {a b c : Fin m} (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign m a b (βL (Additive.ofMul s))) {g : G}
    (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) (s : ↥Bs)
    (hs : βL (Additive.ofMul s) c = 0) :
    (s : G) ∈ (coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ ⊔
      ((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ).map (MulAut.conj g).toMonoidHom := by
  classical
  let J₁ : Subgroup G := (coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ
  let J₂ : Subgroup G := J₁.map (MulAut.conj g).toMonoidHom
  let A : Set (DVec m) := {v | (∃ i j : Fin m, i ≠ c ∧ j ≠ c ∧ i ≠ j ∧
      v = Pi.single i 1 - Pi.single j 1) ∨
      (∃ k : Fin m, k ≠ c ∧ k ≠ a ∧ k ≠ b ∧ v = Pi.single a 1 + Pi.single k 1)}
  let t : Fin m → ↥Bs := fun i => Additive.toMul (βL.symm (Pi.single i 1))
  have ht : ∀ i, βL (Additive.ofMul (t i)) = Pi.single i 1 := fun i => by simp [t]
  let u1 : Fin m → Fin m → ↥Bs := fun i j =>
    t i * (((ε (Equiv.swap i j) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) (t i))⁻¹
  let u2 : Fin m → ↥Bs := fun k =>
    (α (t a * (((ε (Equiv.swap a k) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) (t a))⁻¹))⁻¹
  have hu1 : ∀ i j (hij : i ≠ j) (hic : i ≠ c) (hjc : j ≠ c),
      (u1 i j : G) ∈ J₁ ∧ βL (Additive.ofMul (u1 i j)) = Pi.single i 1 - Pi.single j 1 := by
    intro i j hij hic hjc
    have hσ : Equiv.swap i j c = c := Equiv.swap_apply_of_ne_of_ne (Ne.symm hic) (Ne.symm hjc)
    obtain ⟨hmem, hcoord⟩ := qtwoDB14_comm_mem_J1 hbase hcoords (Equiv.swap i j) hσ (t i)
    exact ⟨hmem, by rw [hcoord, ht i, qtwoDB14_dPerm_single i j]⟩
  have hu2 : ∀ k (hkc : k ≠ c) (hka : k ≠ a) (hkb : k ≠ b),
      (u2 k : G) ∈ J₂ ∧ βL (Additive.ofMul (u2 k)) = Pi.single a 1 + Pi.single k 1 := by
    intro k hkc hka hkb
    have hσ : Equiv.swap a k c = c :=
      Equiv.swap_apply_of_ne_of_ne hca (Ne.symm hkc)
    obtain ⟨hmem, hcoord⟩ := qtwoDB14_comm_mem_J1 hbase hcoords (Equiv.swap a k) hσ (t a)
    let inner : ↥Bs :=
      t a * (((ε (Equiv.swap a k) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) (t a))⁻¹
    have hinner : inner =
        t a * (((ε (Equiv.swap a k) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) (t a))⁻¹ := rfl
    have hcoord' : βL (Additive.ofMul inner) = Pi.single a 1 - Pi.single k 1 := by
      rw [hinner, hcoord, ht a, qtwoDB14_dPerm_single a k]
    have hgin : g * (inner : G) * g⁻¹ ∈ J₂ :=
      Subgroup.mem_map.mpr ⟨(inner : G), hmem, rfl⟩
    have hαinner : ((α inner : ↥Bs) : G) = g * (inner : G) * g⁻¹ := hg inner
    have hu2eq : u2 k = (α inner)⁻¹ := rfl
    rw [hu2eq]
    constructor
    · rw [Subgroup.coe_inv, hαinner]
      exact Subgroup.inv_mem _ hgin
    · simp only [ofMul_inv, map_neg]
      rw [hα, hcoord', map_sub, qtwoDB14_dSign_single_self,
        qtwoDB14_dSign_single_of_ne hka hkb]
      abel
  let Gen : Set ↥Bs := {u | (∃ i j : Fin m, i ≠ c ∧ j ≠ c ∧ i ≠ j ∧ u = u1 i j) ∨
    (∃ k : Fin m, k ≠ c ∧ k ≠ a ∧ k ≠ b ∧ u = u2 k)}
  have hspan : ∀ v : DVec m, v c = 0 → v ∈ Submodule.span (ZMod 3) A :=
    qtwoDB14_span_erase hab hca hcb hm A
      (fun i j hic hjc hij => Or.inl ⟨i, j, hic, hjc, hij, rfl⟩)
      (fun k hkc hka hkb => Or.inr ⟨k, hkc, hka, hkb, rfl⟩)
  have hmem : ∀ v ∈ Submodule.span (ZMod 3) A,
      Additive.toMul (βL.symm v) ∈ Subgroup.closure Gen := by
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro v' (⟨i, j, hic, hjc, hij, rfl⟩ | ⟨k, hkc, hka, hkb, rfl⟩)
      · have h1 : βL (Additive.ofMul
            (Additive.toMul (βL.symm (Pi.single i 1 - Pi.single j 1)))) =
            Pi.single i 1 - Pi.single j 1 := by
          rw [ofMul_toMul, AddEquiv.apply_symm_apply]
        have heq : Additive.toMul (βL.symm (Pi.single i 1 - Pi.single j 1)) = u1 i j :=
          Additive.ofMul.injective (βL.injective (h1.trans (hu1 i j hij hic hjc).2.symm))
        rw [heq]
        exact Subgroup.subset_closure (Or.inl ⟨i, j, hic, hjc, hij, rfl⟩)
      · have h1 : βL (Additive.ofMul
            (Additive.toMul (βL.symm (Pi.single a 1 + Pi.single k 1)))) =
            Pi.single a 1 + Pi.single k 1 := by
          rw [ofMul_toMul, AddEquiv.apply_symm_apply]
        have heq : Additive.toMul (βL.symm (Pi.single a 1 + Pi.single k 1)) = u2 k :=
          Additive.ofMul.injective (βL.injective (h1.trans (hu2 k hkc hka hkb).2.symm))
        rw [heq]
        exact Subgroup.subset_closure (Or.inr ⟨k, hkc, hka, hkb, rfl⟩)
    · simp
    · intro x y hx hy hpx hpy
      rw [map_add, toMul_add]
      exact Subgroup.mul_mem _ hpx hpy
    · intro c' x hx hpx
      have hc : c' = 0 ∨ c' = 1 ∨ c' = 2 := by
        have hv : c'.val = 0 ∨ c'.val = 1 ∨ c'.val = 2 := by
          have hlt : c'.val < 3 := ZMod.val_lt c'
          omega
        rcases hv with hv | hv | hv
        · left; rw [← ZMod.natCast_zmod_val c', hv]; norm_num
        · right; left; rw [← ZMod.natCast_zmod_val c', hv]; norm_num
        · right; right; rw [← ZMod.natCast_zmod_val c', hv]; norm_num
      rcases hc with h | h | h
      · rw [h, zero_smul]; simp
      · rw [h, one_smul]; exact hpx
      · rw [h, two_smul, map_add, toMul_add]
        exact Subgroup.mul_mem _ hpx hpx
  have hs_closure : s ∈ Subgroup.closure Gen := by
    have h := hmem (βL (Additive.ofMul s)) (hspan _ hs)
    simpa using h
  have hle : Subgroup.closure Gen ≤ (J₁ ⊔ J₂).subgroupOf Bs := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro u (⟨i, j, hic, hjc, hij, rfl⟩ | ⟨k, hkc, hka, hkb, rfl⟩)
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (hu1 i j hij hic hjc).1)
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (hu2 k hkc hka hkb).1)
  exact Subgroup.mem_subgroupOf.mp (hle hs_closure)

theorem ggQTwoDUnit_weyl_X (hm : 5 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) {a b c : Fin m} (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign m a b (βL (Additive.ofMul s))) {g : G}
    (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) {a' : MulAut ↥Bs}
    (ha' : a' ∈ ggAutomizerJoin L Bs 𝒦) {w : DVec m ≃ₗ[ZMod 3] DVec m} (hw : w ∈ dEven m)
    (hwc : w (Pi.single c 1) = Pi.single c 1)
    (ha'w : ∀ s : ↥Bs, βL (Additive.ofMul (a' s)) = w (βL (Additive.ofMul s))) :
    a' ∈ ggAutomizer ((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ ⊔
      ((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ).map (MulAut.conj g).toMonoidHom) Bs := by
  classical
  let J₁ : Subgroup G := (coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ
  let J₂ : Subgroup G := J₁.map (MulAut.conj g).toMonoidHom
  let H : Subgroup (DVec m ≃ₗ[ZMod 3] DVec m) :=
    (ggAutomizer (J₁ ⊔ J₂) Bs).map (ggLin (p := 3) βL)
  change a' ∈ ggAutomizer (J₁ ⊔ J₂) Bs
  have hperm : ∀ σ : Equiv.Perm (Fin m), σ c = c → dPerm m σ ∈ H := by
    intro σ hσ
    refine Subgroup.mem_map.mpr ⟨(ε σ : ↥(ggAutomizer L Bs)), ?_, ?_⟩
    · refine mem_ggAutomizer_iff.mpr
        ⟨ψ (ggPermSU (K := F0) (f := 1) σ⁻¹), ?_, ?_, hbase.perm σ⟩
      · exact Subgroup.mem_sup_left
          (Subgroup.mem_map_of_mem _ (qtwoDB14_perm_mem_coordBlockSU σ hσ))
      · exact ggNSPosPA_permSU_mem_normalizer hbase.hyp hbase.diag σ⁻¹
    · refine LinearEquiv.ext fun v => ?_
      obtain ⟨s, rfl⟩ := βL.surjective v
      obtain ⟨t, rfl⟩ : ∃ t : ↥Bs, Additive.ofMul t = s := ⟨Additive.toMul s, ofMul_toMul s⟩
      rw [ggLin_apply_ofMul, hcoords.perm σ t]
  have hαinv : ∀ s : ↥Bs, βL (Additive.ofMul (α⁻¹ s)) =
      dSign m a b (βL (Additive.ofMul s)) := by
    intro s
    have h' := congrArg (dSign m a b) (hα (α⁻¹ s))
    rw [show α (α⁻¹ s) = s by rw [MulAut.apply_inv_self], ← LinearEquiv.mul_apply,
      qtwoDB37_dSign_double] at h'
    simpa [LinearEquiv.coe_one] using h'.symm
  have hconj : ∀ σ : Equiv.Perm (Fin m), σ c = c →
      α * (ε σ : ↥(ggAutomizer L Bs)) * α⁻¹ ∈ ggAutomizer (J₁ ⊔ J₂) Bs ∧
      ggLin (p := 3) βL (α * (ε σ : ↥(ggAutomizer L Bs)) * α⁻¹) =
        dSign m a b * dPerm m σ * dSign m a b := by
    intro σ hσ
    have hπJ : ψ (ggPermSU (K := F0) (f := 1) σ⁻¹) ∈ J₁ :=
      Subgroup.mem_map_of_mem _ (qtwoDB14_perm_mem_coordBlockSU σ hσ)
    constructor
    · refine mem_ggAutomizer_iff.mpr
        ⟨g * ψ (ggPermSU (K := F0) (f := 1) σ⁻¹) * g⁻¹, ?_, ?_, ?_⟩
      · exact Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨_, hπJ, rfl⟩)
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN
          (ggNSPosPA_permSU_mem_normalizer hbase.hyp hbase.diag σ⁻¹))
          (Subgroup.inv_mem _ hgN)
      · intro b
        change ((α (((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) (α⁻¹ b)) : ↥Bs) : G) =
          (g * ψ (ggPermSU (K := F0) (f := 1) σ⁻¹) * g⁻¹) * b *
            (g * ψ (ggPermSU (K := F0) (f := 1) σ⁻¹) * g⁻¹)⁻¹
        rw [hg (((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) (α⁻¹ b)),
          hbase.perm σ (α⁻¹ b)]
        have h3 : ((α⁻¹ b : ↥Bs) : G) = g⁻¹ * (b : G) * g := by
          have h := hg (α⁻¹ b)
          rw [show α (α⁻¹ b) = b by rw [MulAut.apply_inv_self]] at h
          rw [h]; group
        rw [h3]; group
    · refine LinearEquiv.ext fun v => ?_
      obtain ⟨s, rfl⟩ := βL.surjective v
      obtain ⟨t, rfl⟩ : ∃ t : ↥Bs, Additive.ofMul t = s := ⟨Additive.toMul s, ofMul_toMul s⟩
      rw [ggLin_apply_ofMul]
      change βL (Additive.ofMul (α (((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) (α⁻¹ t)))) =
        (dSign m a b * dPerm m σ * dSign m a b) (βL (Additive.ofMul t))
      rw [hα (((ε σ : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) (α⁻¹ t)),
        hcoords.perm σ (α⁻¹ t), hαinv t]
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have hsa : ∀ k : Fin m, k ≠ a → k ≠ b → k ≠ c → dSign m a k ∈ H := by
    intro k hka hkb hkc
    have hσ : Equiv.swap a k c = c := Equiv.swap_apply_of_ne_of_ne hca (Ne.symm hkc)
    rw [ggQTwoDUnit_dSign_eq_comm hab hka hkb]
    exact H.mul_mem (hperm (Equiv.swap a k) hσ)
      (Subgroup.mem_map.mpr ⟨α * (ε (Equiv.swap a k) : ↥(ggAutomizer L Bs)) * α⁻¹,
        (hconj (Equiv.swap a k) hσ).1, (hconj (Equiv.swap a k) hσ).2⟩)
  have hsb : ∀ k : Fin m, k ≠ a → k ≠ b → k ≠ c → dSign m b k ∈ H := by
    intro k hka hkb hkc
    have hσ : Equiv.swap b k c = c := Equiv.swap_apply_of_ne_of_ne hcb (Ne.symm hkc)
    rw [ggQTwoDUnit_dSign_eq_comm (a := b) (b := a) (k := k) hab.symm hkb hka,
      qtwoDB37_dSign_comm b a]
    exact H.mul_mem (hperm (Equiv.swap b k) hσ)
      (Subgroup.mem_map.mpr ⟨α * (ε (Equiv.swap b k) : ↥(ggAutomizer L Bs)) * α⁻¹,
        (hconj (Equiv.swap b k) hσ).1, (hconj (Equiv.swap b k) hσ).2⟩)
  have hwH : w ∈ H :=
    ggQTwoDUnit_dEven_fix_mem (m := m) (by omega) hab hca hcb H hperm hsa hsb hw hwc
  obtain ⟨φ, hφX, hφw⟩ := Subgroup.mem_map.mp hwH
  have hgg : ggLin (p := 3) βL a' = w := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨s, rfl⟩ := βL.surjective v
    obtain ⟨t, rfl⟩ : ∃ t : ↥Bs, Additive.ofMul t = s := ⟨Additive.toMul s, ofMul_toMul s⟩
    rw [ggLin_apply_ofMul, ha'w t]
  have hφa : φ = a' := ggLin_injective (p := 3) βL (hφw.trans hgg.symm)
  rw [← hφa]
  exact hφX

end CFSG.StandardType.QTwo

end
