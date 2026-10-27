module

public import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalCoord
public import CFSG.Quasithin.Background.F1Hyp

import CFSG.Quasithin.Recognition.St84.Gen.Sp4qAmalLocal
import CFSG.Quasithin.Recognition.St84.Gen.SL2Semilinear

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

private lemma sp4RadMat_mulVec_first_of_upper {F : Type*} [Field F] {M : SL(2, F)}
    (h10 : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (v : Fin 3 → F) (h2 : v 2 = 0) :
    ((sp4RadMat M).mulVec v) 0 = v 0 := by
  rw [sp4RadMat_mulVec]
  simp [h10, h2]

private lemma sp4RadMat_mulVec_second_of_upper {F : Type*} [Field F] {M : SL(2, F)}
    {μ : F} (h10 : (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (h00 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 = μ) (v : Fin 3 → F) (h2 : v 2 = 0) :
    ((sp4RadMat M).mulVec v) 1 = μ ^ 2 * v 1 := by
  rw [sp4RadMat_mulVec]
  simp [h10, h00, h2]

private lemma exists_unit_ne_one (hf : 2 ≤ f) :
    ∃ lam : (GaloisField 2 f)ˣ, lam ≠ 1 := by
  classical
  let F := GaloisField 2 f
  letI : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = 2 ^ f := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 f (by omega : f ≠ 0)]
  have hf1 : 1 < f := Nat.lt_of_lt_of_le (by norm_num) hf
  have hgt : 2 < Fintype.card F := by
    rw [hcardF]
    calc 2 = 2 ^ 1 := by norm_num
      _ < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) hf1
  have hnot : ∃ x : F, x ∉ ({0, 1} : Finset F) := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset F) ⊆ ({0, 1} : Finset F) := by
      intro x _
      exact h x
    have hle := Finset.card_le_card hsub
    have hpair : ({0, 1} : Finset F).card ≤ 2 := by simp
    have hle' : Fintype.card F ≤ 2 := by simpa using hle
    omega
  obtain ⟨x, hx⟩ := hnot
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  refine ⟨Units.mk0 x hx.1, ?_⟩
  intro h
  apply hx.2
  have hval := congrArg Units.val h
  simpa using hval

private lemma second_coord_eq_zero_of_mem_inf (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c : Sp4VertexCoord L1 S (GaloisField 2 f))
    {z : ↥(pCoreOf 2 L1)}
    (hz : (z : G) ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2) :
    Multiplicative.toAdd (c.γ z) 2 = 0 := by
  have hcent : (z : G) ∈ Subgroup.centralizer (S : Set G) := hD.inf_le_centralizer hH hz
  exact (c.mem_centralizer_iff (hD.le_left hH) z).mp
    (fun s hs => (Subgroup.mem_centralizer_iff.mp hcent) s hs)

private lemma conj_mem_blockZ_of_mem_normalizer (hD : Sp4qLocalData L1 L2 S f)
    {d : G} (hd : d ∈ Subgroup.normalizer (L2 : Set G)) {w : G} (hw : w ∈ blockZ L2) :
    d * w * d⁻¹ ∈ blockZ L2 := by
  have hdQ : d ∈ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 L2 hd
  rw [blockZ, Subgroup.mem_inf]
  refine ⟨?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
  · have hwU : w ∈ pCoreOf 2 L2 := by
      have h := hw.1
      rwa [hD.blockU_right] at h
    simpa [hD.blockU_right] using (Subgroup.mem_normalizer_iff.mp hdQ w).mp hwU
  · intro l hl
    have hdl : d⁻¹ * l * d ∈ L2 := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hd) l).mp hl
    have hcomm : w * (d⁻¹ * l * d) = (d⁻¹ * l * d) * w :=
      (Subgroup.mem_centralizer_iff.mp hw.2 (d⁻¹ * l * d) hdl).symm
    calc l * (d * w * d⁻¹) = d * ((d⁻¹ * l * d) * w) * d⁻¹ := by group
      _ = d * (w * (d⁻¹ * l * d)) * d⁻¹ := by rw [← hcomm]
      _ = (d * w * d⁻¹) * l := by group

private lemma exists_blockZ_right_datum (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f)) :
    ∃ (b : ↥L1) (lam r : GaloisField 2 f),
      lam ≠ 1 ∧ lam ^ 2 + 1 ≠ 0 ∧
      (b : G) ∈ Subgroup.normalizer (L2 : Set G) ∧
      (c₁.α b : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) =
        !![lam, r; 0, lam⁻¹] ∧
      (∀ w : ↥(blockZ L2), (b : G) * (w : G) * (b : G)⁻¹ ∈ pCoreOf 2 L1) := by
  classical
  obtain ⟨nu, hnu1⟩ := exists_unit_ne_one (f := f) hf
  obtain ⟨b, hbN, r, hbα⟩ := c₁.exists_mem_normalizer (hD.le_left hH) nu
  let lam : GaloisField 2 f := (nu : GaloisField 2 f)
  have hlam1 : lam ≠ 1 := by
    intro h
    exact hnu1 (Units.ext h)
  have hbα' : (c₁.α b : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) =
      !![lam, r; 0, lam⁻¹] := by
    simpa [lam] using hbα
  have hc : lam ^ 2 + 1 ≠ 0 := by
    intro h
    have hneg : lam ^ 2 = -(1 : GaloisField 2 f) := eq_neg_of_add_eq_zero_left h
    rw [CharTwo.neg_eq] at hneg
    have hpos : lam = 1 := by
      rcases (sq_eq_one_iff.mp hneg) with h1 | h1
      · exact h1
      · rw [h1, CharTwo.neg_eq]
    exact hlam1 hpos
  have hbB : (b : G) ∈ borelOf L1 S := by
    rw [borelOf]
    refine ⟨b.2, ?_⟩
    have hSL : S ⊓ L1 = S := inf_eq_left.mpr (hD.le_left hH)
    rw [hSL]
    exact hbN
  have hdL2 : (b : G) ∈ Subgroup.normalizer (L2 : Set G) := hH.h2.borel_le hbB
  have hconj : ∀ w : ↥(blockZ L2),
      (b : G) * (w : G) * (b : G)⁻¹ ∈ pCoreOf 2 L1 := by
    intro w
    have hbQ1 : (b : G) ∈ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
      le_normalizer_pCoreOf 2 L1 b.2
    exact (Subgroup.mem_normalizer_iff.mp hbQ1 (w : G)).mp (hD.blockZ_right_le hH w.2).1
  exact ⟨b, lam, r, hlam1, hc, hdL2, hbα', hconj⟩

private noncomputable def blockZRightKappa (hD : Sp4qLocalData L1 L2 S f)
    {b : ↥L1} (hdL2 : (b : G) ∈ Subgroup.normalizer (L2 : Set G))
    (hconj : ∀ w : ↥(blockZ L2), (b : G) * (w : G) * (b : G)⁻¹ ∈ pCoreOf 2 L1)
    (w : ↥(blockZ L2)) : ↥(blockZ L2) :=
  ⟨(b : G) * (w : G) * (b : G)⁻¹ * (w : G)⁻¹,
    (blockZ L2).mul_mem (conj_mem_blockZ_of_mem_normalizer hD hdL2 w.2)
      ((blockZ L2).inv_mem w.2)⟩

private noncomputable def blockZToQ1 (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (w : ↥(blockZ L2)) : ↥(pCoreOf 2 L1) :=
  ⟨(w : G), (hD.blockZ_right_le hH w.2).1⟩

private lemma blockZRightKappa_coord (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    {b : ↥L1} {lam r : GaloisField 2 f}
    (hdL2 : (b : G) ∈ Subgroup.normalizer (L2 : Set G))
    (hconj : ∀ w : ↥(blockZ L2), (b : G) * (w : G) * (b : G)⁻¹ ∈ pCoreOf 2 L1)
    (hbα : (c₁.α b : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) =
      !![lam, r; 0, lam⁻¹]) (w : ↥(blockZ L2)) :
    Multiplicative.toAdd
        (c₁.γ (blockZToQ1 hH hD (blockZRightKappa hD hdL2 hconj w))) =
      ![0, (lam ^ 2 + 1) * Multiplicative.toAdd (c₁.γ (blockZToQ1 hH hD w)) 1, 0] := by
  classical
  let u : ↥(pCoreOf 2 L1) := blockZToQ1 hH hD w
  let v : ↥(pCoreOf 2 L1) := ⟨(b : G) * (w : G) * (b : G)⁻¹, hconj w⟩
  let k : ↥(pCoreOf 2 L1) := blockZToQ1 hH hD (blockZRightKappa hD hdL2 hconj w)
  have hk : k = v * u⁻¹ :=
    Subtype.ext (by simp [k, v, u, blockZToQ1, blockZRightKappa])
  have hu2 : Multiplicative.toAdd (c₁.γ u) 2 = 0 :=
    second_coord_eq_zero_of_mem_inf hH hD c₁ (hD.blockZ_right_le hH w.2)
  have hv2 : Multiplicative.toAdd (c₁.γ v) 2 = 0 :=
    second_coord_eq_zero_of_mem_inf hH hD c₁
      (hD.blockZ_right_le hH (conj_mem_blockZ_of_mem_normalizer hD hdL2 w.2))
  have heq := c₁.equivariant b u v (by rfl)
  have h10 : (c₁.α b : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 1 0 = 0 := by
    rw [hbα]
    simp
  have h00 : (c₁.α b : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) 0 0 = lam := by
    rw [hbα]
    simp
  have hv0 : Multiplicative.toAdd (c₁.γ v) 0 = Multiplicative.toAdd (c₁.γ u) 0 := by
    have h0 := congrFun heq 0
    rw [sp4RadMat_mulVec_first_of_upper h10 _ hu2] at h0
    exact h0
  have hv1 : Multiplicative.toAdd (c₁.γ v) 1 = lam ^ 2 * Multiplicative.toAdd (c₁.γ u) 1 := by
    have h1 := congrFun heq 1
    rw [sp4RadMat_mulVec_second_of_upper h10 h00 _ hu2] at h1
    exact h1
  have hκ : Multiplicative.toAdd (c₁.γ k) =
      Multiplicative.toAdd (c₁.γ v) - Multiplicative.toAdd (c₁.γ u) := by
    rw [hk, map_mul, map_inv, toAdd_mul, toAdd_inv]
    simp [sub_eq_add_neg]
  rw [hκ]
  funext i
  fin_cases i
  · simp [hv0]
  · simp [hv1]
    rw [sub_eq_add_neg, CharTwo.neg_eq]
    ring
  · simp [hv2, hu2]

private lemma blockZRightKappa_injective (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    {b : ↥L1} {lam r : GaloisField 2 f}
    (hdL2 : (b : G) ∈ Subgroup.normalizer (L2 : Set G))
    (hconj : ∀ w : ↥(blockZ L2), (b : G) * (w : G) * (b : G)⁻¹ ∈ pCoreOf 2 L1)
    (hbα : (c₁.α b : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) =
      !![lam, r; 0, lam⁻¹]) (hc : lam ^ 2 + 1 ≠ 0) :
    Function.Injective (blockZRightKappa hD hdL2 hconj) := by
  classical
  have hinj : Function.Injective (blockZRightKappa hD hdL2 hconj) := by
    intro w1 w2 hκ
    have hκγ : Multiplicative.toAdd
        (c₁.γ (blockZToQ1 hH hD (blockZRightKappa hD hdL2 hconj w1))) =
        Multiplicative.toAdd
        (c₁.γ (blockZToQ1 hH hD (blockZRightKappa hD hdL2 hconj w2))) := by
      rw [hκ]
    have hv : Multiplicative.toAdd (c₁.γ (blockZToQ1 hH hD w1)) 1 =
        Multiplicative.toAdd (c₁.γ (blockZToQ1 hH hD w2)) 1 := by
      have h1 := congrFun (blockZRightKappa_coord hH hD c₁ hdL2 hconj hbα w1) 1
      have h2 := congrFun (blockZRightKappa_coord hH hD c₁ hdL2 hconj hbα w2) 1
      have h := congrFun hκγ 1
      rw [h1, h2] at h
      exact mul_left_cancel₀ hc h
    let k : ↥(blockZ L2) := w1 * w2⁻¹
    have hk1 : Multiplicative.toAdd (c₁.γ (blockZToQ1 hH hD k)) 1 = 0 := by
      have hγ : Multiplicative.toAdd (c₁.γ (blockZToQ1 hH hD k)) =
          Multiplicative.toAdd (c₁.γ (blockZToQ1 hH hD w1)) -
            Multiplicative.toAdd (c₁.γ (blockZToQ1 hH hD w2)) := by
        rw [show blockZToQ1 hH hD k =
            blockZToQ1 hH hD w1 * (blockZToQ1 hH hD w2)⁻¹ by
          apply Subtype.ext
          simp [blockZToQ1, k]]
        rw [map_mul, map_inv, toAdd_mul, toAdd_inv]
        simp [sub_eq_add_neg]
      have h0 := congrFun hγ 1
      simp only [Pi.sub_apply] at h0
      rw [hv] at h0
      simpa using h0
    have hk2 : Multiplicative.toAdd (c₁.γ (blockZToQ1 hH hD k)) 2 = 0 :=
      second_coord_eq_zero_of_mem_inf hH hD c₁ (hD.blockZ_right_le hH k.2)
    have hkZ1 : (k : G) ∈ blockZ L1 :=
      (c₁.mem_blockZ_iff hD.blockU_left _).mpr ⟨hk1, hk2⟩
    have hkBot : k = 1 := by
      apply Subtype.ext
      have hmem : (k : G) ∈ blockZ L1 ⊓ blockZ L2 := ⟨hkZ1, k.2⟩
      have hle : (k : G) ∈ (⊥ : Subgroup G) := by
        rw [← hD.blockZ_inf_blockZ hf hH]
        exact hmem
      simpa using hle
    have hww : w1 = w2 := by
      have h := congrArg (fun x : ↥(blockZ L2) => x * w2) hkBot
      simpa [k] using h
    exact hww
  exact hinj

private lemma mem_blockZ_right_forward (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    {z : ↥(pCoreOf 2 L1)} (hz : (z : G) ∈ blockZ L2) :
    Multiplicative.toAdd (c₁.γ z) 0 = 0 ∧ Multiplicative.toAdd (c₁.γ z) 2 = 0 := by
  classical
  have hzℓ : (z : G) ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2 := hD.blockZ_right_le hH hz
  have hz2 : Multiplicative.toAdd (c₁.γ z) 2 = 0 :=
    second_coord_eq_zero_of_mem_inf hH hD c₁ hzℓ
  obtain ⟨b, lam, r, -, hc, hdL2, hbα, hconj⟩ :=
    exists_blockZ_right_datum hf hH hD c₁
  have hcoord : ∀ w : ↥(blockZ L2),
      Multiplicative.toAdd
          (c₁.γ (blockZToQ1 hH hD (blockZRightKappa hD hdL2 hconj w))) =
        ![0, (lam ^ 2 + 1) * Multiplicative.toAdd (c₁.γ (blockZToQ1 hH hD w)) 1, 0] :=
    fun w => blockZRightKappa_coord hH hD c₁ hdL2 hconj hbα w
  have hinj := blockZRightKappa_injective hf hH hD c₁ hdL2 hconj hbα hc
  have hsurj := Finite.injective_iff_surjective.mp hinj
  let zZ : ↥(blockZ L2) := ⟨z, hz⟩
  obtain ⟨w, hwz⟩ := hsurj zZ
  have hzval : (z : G) = (blockZRightKappa hD hdL2 hconj w : G) := by
    have h := congrArg (fun y : ↥(blockZ L2) => (y : G)) hwz
    exact h.symm
  have h0 : Multiplicative.toAdd
      (c₁.γ (blockZToQ1 hH hD (blockZRightKappa hD hdL2 hconj w))) 0 = 0 := by
    have h := congrFun (hcoord w) 0
    simpa using h
  have hzeq : z = blockZToQ1 hH hD (blockZRightKappa hD hdL2 hconj w) :=
    Subtype.ext hzval
  refine ⟨?_, hz2⟩
  rw [hzeq]
  exact h0

private lemma mem_blockZ_right_backward (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    {z : ↥(pCoreOf 2 L1)}
    (h0 : Multiplicative.toAdd (c₁.γ z) 0 = 0)
    (h2 : Multiplicative.toAdd (c₁.γ z) 2 = 0) :
    (z : G) ∈ blockZ L2 := by
  classical
  let F := GaloisField 2 f
  let u : ↥(blockZ L2) → ↥(pCoreOf 2 L1) :=
    fun w => ⟨(w : G), (hD.blockZ_right_le hH w.2).1⟩
  let ψ : ↥(blockZ L2) → F := fun w => Multiplicative.toAdd (c₁.γ (u w)) 1
  have hψinj : Function.Injective ψ := by
    intro w1 w2 hψ
    let w : ↥(blockZ L2) := w1 * w2⁻¹
    have huw : u w = u w1 * (u w2)⁻¹ := by
      apply Subtype.ext
      simp [u, w]
    have h1coord : Multiplicative.toAdd (c₁.γ (u w)) 1 = 0 := by
      rw [huw, map_mul, map_inv, toAdd_mul, toAdd_inv]
      simp only [Pi.add_apply, Pi.neg_apply]
      rw [show Multiplicative.toAdd (c₁.γ (u w1)) 1 =
        Multiplicative.toAdd (c₁.γ (u w2)) 1 from hψ]
      simp
    have hfw := mem_blockZ_right_forward hf hH hD c₁ (z := u w) w.2
    have hZ1 : (u w : G) ∈ blockZ L1 :=
      (c₁.mem_blockZ_iff hD.blockU_left (u w)).mpr ⟨h1coord, hfw.2⟩
    have hZ1' : (w : G) ∈ blockZ L1 := by simpa [u] using hZ1
    have hmem : (w : G) ∈ blockZ L1 ⊓ blockZ L2 := ⟨hZ1', w.2⟩
    have hbot : w = 1 := by
      apply Subtype.ext
      have hle : (w : G) ∈ (⊥ : Subgroup G) := by
        rw [← hD.blockZ_inf_blockZ hf hH]
        exact hmem
      simpa using hle
    have hww : w1 = w2 := by
      have h := congrArg (fun x : ↥(blockZ L2) => x * w2) hbot
      simpa [w] using h
    exact hww
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype ↥(blockZ L2) := Fintype.ofFinite ↥(blockZ L2)
  have hcardZ : Fintype.card ↥(blockZ L2) = Fintype.card F := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hD.card_blockZ_right,
      GaloisField.card 2 f (by omega : f ≠ 0)]
  let e : ↥(blockZ L2) ≃ F := Fintype.equivOfCardEq hcardZ
  have hψsurj : Function.Surjective ψ :=
    (Finite.injective_iff_surjective_of_equiv e).mp hψinj
  obtain ⟨w, hw⟩ := hψsurj (Multiplicative.toAdd (c₁.γ z) 1)
  have hfw := mem_blockZ_right_forward hf hH hD c₁ (z := u w) w.2
  have hγeq : Multiplicative.toAdd (c₁.γ (u w)) = Multiplicative.toAdd (c₁.γ z) := by
    funext i
    fin_cases i
    · simp [hfw.1, h0]
    · simpa using hw
    · simp [hfw.2, h2]
  have huz : u w = z := c₁.γ.injective (Multiplicative.toAdd.injective hγeq)
  have hzw : (z : G) = (w : G) := by
    simpa [u] using congrArg (fun x : ↥(pCoreOf 2 L1) => (x : G)) huz.symm
  rw [hzw]
  exact w.2

theorem Sp4qLocalData.mem_blockZ_right_iff (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (z : ↥(pCoreOf 2 L1)) :
    (z : G) ∈ blockZ L2 ↔
      Multiplicative.toAdd (c₁.γ z) 0 = 0 ∧ Multiplicative.toAdd (c₁.γ z) 2 = 0 := by
  constructor
  · exact mem_blockZ_right_forward hf hH hD c₁
  · rintro ⟨h0, h2⟩
    exact mem_blockZ_right_backward hf hH hD c₁ h0 h2

theorem Sp4qLocalData.mem_blockZ_left_iff (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f))
    (z : ↥(pCoreOf 2 L2)) :
    (z : G) ∈ blockZ L1 ↔
      Multiplicative.toAdd (c₂.γ z) 0 = 0 ∧ Multiplicative.toAdd (c₂.γ z) 2 = 0 :=
  Sp4qLocalData.mem_blockZ_right_iff (f := f) hf hH.symm hD.symm c₂ z

private def uMat {F : Type*} [Field F] (t : F) : Matrix (Fin 2) (Fin 2) F := !![1, t; 0, 1]

private lemma uMat_det {F : Type*} [Field F] (t : F) : (uMat t).det = 1 := by
  simp [uMat, Matrix.det_fin_two]

private def uSL {F : Type*} [Field F] (t : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨uMat t, uMat_det t⟩

private lemma coe_uSL {F : Type*} [Field F] (t : F) :
    (uSL t : Matrix (Fin 2) (Fin 2) F) = uMat t := rfl

private lemma uSL_injective {F : Type*} [Field F] : Function.Injective (uSL (F := F)) := by
  intro s t h
  have h' : uMat s = uMat t := congrArg Subtype.val h
  have := congrFun (congrFun h' 0) 1
  simpa [uMat] using this

private lemma uSL_mul {F : Type*} [Field F] (s t : F) : uSL s * uSL t = uSL (s + t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_uSL, coe_uSL, coe_uSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private lemma uSL_zero {F : Type*} [Field F] : uSL (0 : F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL, uMat]

private lemma inclQ1L2 (hH : Hyp111 L1 L2 S) (hD : Sp4qLocalData L1 L2 S f) :
    pCoreOf 2 L1 ≤ L2 :=
  hH.pCoreOf_le_left.trans (hD.le_right hH)

theorem Sp4qLocalData.pCoreOf_right_le_left (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) : pCoreOf 2 L2 ≤ L1 :=
  hH.pCoreOf_le_right.trans (hD.le_left hH)

theorem Sp4VertexCoord.coord_two_eq_zero_of_mem_inf (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c : Sp4VertexCoord L2 S (GaloisField 2 f))
    {z : ↥(pCoreOf 2 L2)}
    (hz : (z : G) ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2) :
    Multiplicative.toAdd (c.γ z) 2 = 0 := by
  have hcent : (z : G) ∈ Subgroup.centralizer (S : Set G) := hD.inf_le_centralizer hH hz
  exact (c.mem_centralizer_iff (hD.le_right hH) z).mp
    (fun s hs => (Subgroup.mem_centralizer_iff.mp hcent) s hs)

private lemma alpha_second_eq_of_alpha_eq (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f)) {y1 y2 : ↥(pCoreOf 2 L2)}
    (hy : c₁.α (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) y1) =
      c₁.α (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) y2)) :
    Multiplicative.toAdd (c₂.γ y1) 2 = Multiplicative.toAdd (c₂.γ y2) 2 := by
  let k : ↥(pCoreOf 2 L2) := y1 * y2⁻¹
  have hkα : c₁.α (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) k) = 1 := by
    have h : Subgroup.inclusion (hD.pCoreOf_right_le_left hH) k =
        Subgroup.inclusion (hD.pCoreOf_right_le_left hH) y1 *
          (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) y2)⁻¹ := by
      rw [show k = y1 * y2⁻¹ from rfl, map_mul, map_inv]
    rw [h, map_mul, map_inv, hy, mul_inv_cancel]
  have hkQ1 : (k : G) ∈ pCoreOf 2 L1 := by
    have h := (c₁.eq_one_iff (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) k)).mp hkα
    simpa using h
  have hkℓ : (k : G) ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2 := ⟨hkQ1, k.2⟩
  have hk2 : Multiplicative.toAdd (c₂.γ k) 2 = 0 :=
    Sp4VertexCoord.coord_two_eq_zero_of_mem_inf hH hD c₂ hkℓ
  have hyk : y1 = k * y2 := by
    apply Subtype.ext
    simp [k]
  have hγ : Multiplicative.toAdd (c₂.γ y1) =
      Multiplicative.toAdd (c₂.γ k) + Multiplicative.toAdd (c₂.γ y2) := by
    rw [hyk, map_mul, toAdd_mul]
  have h := congrFun hγ 2
  simp only [Pi.add_apply] at h
  rw [hk2, zero_add] at h
  exact h

theorem Sp4qLocalData.exists_pCoreOf_right_alpha (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (t : GaloisField 2 f) :
    ∃ y : ↥(pCoreOf 2 L2),
      (c₁.α (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) y) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, t; 0, 1] := by
  classical
  obtain ⟨x, hx⟩ := c₁.surjective (uSL t)
  have hxS : (x : G) ∈ S :=
    (c₁.mem_iff x).mpr ⟨t, by simpa [uSL, uMat] using congrArg Subtype.val hx⟩
  have hQ2N : pCoreOf 2 L2 ≤
      Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    (hH.pCoreOf_le_right.trans (hD.le_left hH)).trans (le_normalizer_pCoreOf 2 L1)
  have hsup : pCoreOf 2 L1 ⊔ pCoreOf 2 L2 = S := hD.sup_pCoreOf hH
  rw [← hsup] at hxS
  obtain ⟨q1, hq1, q2, hq2, hxmul⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hQ2N).mp hxS
  have hxsplit : x = Subgroup.inclusion (pCoreOf_le 2 L1) ⟨q1, hq1⟩ *
      Subgroup.inclusion (hD.pCoreOf_right_le_left hH) ⟨q2, hq2⟩ :=
    Subtype.ext (by simpa using hxmul)
  have hq1α : c₁.α (Subgroup.inclusion (pCoreOf_le 2 L1) ⟨q1, hq1⟩) = 1 :=
    (c₁.eq_one_iff _).mpr (by simpa using hq1)
  refine ⟨⟨q2, hq2⟩, ?_⟩
  have hmul : c₁.α (Subgroup.inclusion (pCoreOf_le 2 L1) ⟨q1, hq1⟩ *
      Subgroup.inclusion (hD.pCoreOf_right_le_left hH) ⟨q2, hq2⟩) = uSL t := by
    rw [← hxsplit]
    exact hx
  rw [map_mul, hq1α, one_mul] at hmul
  simpa [uSL, uMat] using congrArg Subtype.val hmul

private noncomputable def pairingY (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (t : GaloisField 2 f) : ↥(pCoreOf 2 L2) :=
  Classical.choose (Sp4qLocalData.exists_pCoreOf_right_alpha hH hD c₁ t)

private lemma pairingY_spec (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (t : GaloisField 2 f) :
    c₁.α (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) (pairingY hH hD c₁ t)) = uSL t := by
  apply Subtype.ext
  rw [coe_uSL]
  simpa [pairingY, uMat] using
    Classical.choose_spec (Sp4qLocalData.exists_pCoreOf_right_alpha hH hD c₁ t)

private noncomputable def pairingC (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f)) :
    GaloisField 2 f →+ GaloisField 2 f where
  toFun t := Multiplicative.toAdd (c₂.γ (pairingY hH hD c₁ t)) 2
  map_zero' := by
    have hα : c₁.α (Subgroup.inclusion (hD.pCoreOf_right_le_left hH)
        (pairingY hH hD c₁ 0)) = 1 := by
      rw [pairingY_spec, uSL_zero]
    have hQ1 : (pairingY hH hD c₁ 0 : G) ∈ pCoreOf 2 L1 := by
      have h := (c₁.eq_one_iff
        (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) (pairingY hH hD c₁ 0))).mp hα
      simpa using h
    exact Sp4VertexCoord.coord_two_eq_zero_of_mem_inf hH hD c₂ ⟨hQ1, (pairingY hH hD c₁ 0).2⟩
  map_add' s t := by
    have hs := pairingY_spec hH hD c₁ s
    have ht := pairingY_spec hH hD c₁ t
    have hst := pairingY_spec hH hD c₁ (s + t)
    have hprod : c₁.α (Subgroup.inclusion (hD.pCoreOf_right_le_left hH)
        (pairingY hH hD c₁ s * pairingY hH hD c₁ t)) = uSL (s + t) := by
      rw [map_mul, map_mul, hs, ht, uSL_mul]
    have heq := alpha_second_eq_of_alpha_eq hH hD c₁ c₂
      (y1 := pairingY hH hD c₁ s * pairingY hH hD c₁ t)
      (y2 := pairingY hH hD c₁ (s + t)) (by rw [hprod, hst])
    change Multiplicative.toAdd (c₂.γ (pairingY hH hD c₁ (s + t))) 2 =
      Multiplicative.toAdd (c₂.γ (pairingY hH hD c₁ s)) 2 +
        Multiplicative.toAdd (c₂.γ (pairingY hH hD c₁ t)) 2
    rw [← heq]
    rw [map_mul, toAdd_mul]
    rfl

private lemma pairingC_bijective (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f)) :
    Function.Bijective (pairingC hH hD c₁ c₂) := by
  have hinj : Function.Injective (pairingC hH hD c₁ c₂) := by
    intro s t hst
    change Multiplicative.toAdd (c₂.γ (pairingY hH hD c₁ s)) 2 =
      Multiplicative.toAdd (c₂.γ (pairingY hH hD c₁ t)) 2 at hst
    let k : ↥(pCoreOf 2 L2) := pairingY hH hD c₁ s * (pairingY hH hD c₁ t)⁻¹
    have hlast : Multiplicative.toAdd (c₂.γ k) 2 = 0 := by
      have hγ : Multiplicative.toAdd (c₂.γ k) =
          Multiplicative.toAdd (c₂.γ (pairingY hH hD c₁ s)) -
            Multiplicative.toAdd (c₂.γ (pairingY hH hD c₁ t)) := by
        rw [show k = pairingY hH hD c₁ s * (pairingY hH hD c₁ t)⁻¹ from rfl,
          map_mul, map_inv, toAdd_mul, toAdd_inv]
        simp [sub_eq_add_neg]
      have h0 := congrFun hγ 2
      simp only [Pi.sub_apply] at h0
      rw [hst] at h0
      simpa using h0
    have hcent : (k : G) ∈ Subgroup.centralizer (S : Set G) :=
      (c₂.mem_centralizer_iff (hD.le_right hH) k).mpr hlast
    have hkℓ : (k : G) ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2 := by
      rw [← hD.inf_centralizer_right hH]
      exact ⟨k.2, hcent⟩
    have hkα : c₁.α (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) k) = 1 :=
      (c₁.eq_one_iff _).mpr (by simpa using hkℓ.1)
    have hkform : c₁.α (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) k) =
        uSL s * (uSL t)⁻¹ := by
      have h : Subgroup.inclusion (hD.pCoreOf_right_le_left hH) k =
          Subgroup.inclusion (hD.pCoreOf_right_le_left hH) (pairingY hH hD c₁ s) *
            (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) (pairingY hH hD c₁ t))⁻¹ := by
        rw [show k = pairingY hH hD c₁ s * (pairingY hH hD c₁ t)⁻¹ from rfl,
          map_mul, map_inv]
      rw [h, map_mul, map_inv, pairingY_spec, pairingY_spec]
    have hstUL : uSL s = uSL t := by
      have h : uSL s * (uSL t)⁻¹ = 1 := by
        rw [← hkform]
        exact hkα
      calc uSL s = uSL s * (uSL t)⁻¹ * uSL t := by group
        _ = 1 * uSL t := by rw [h]
        _ = uSL t := one_mul _
    exact uSL_injective hstUL
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

private noncomputable def pairingX (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f))
    (s : GaloisField 2 f) : ↥(pCoreOf 2 L1) :=
  Classical.choose (Sp4qLocalData.exists_pCoreOf_right_alpha hH.symm hD.symm c₂ s)

private lemma pairingX_spec (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f))
    (s : GaloisField 2 f) :
    c₂.α (Subgroup.inclusion (inclQ1L2 hH hD) (pairingX hH hD c₂ s)) = uSL s := by
  have hcoe : Subgroup.inclusion (hD.symm.pCoreOf_right_le_left hH.symm)
        (pairingX hH hD c₂ s) =
      Subgroup.inclusion (inclQ1L2 hH hD) (pairingX hH hD c₂ s) := Subtype.ext rfl
  rw [← hcoe]
  apply Subtype.ext
  rw [coe_uSL]
  simpa [pairingX, uMat] using
    Classical.choose_spec (Sp4qLocalData.exists_pCoreOf_right_alpha hH.symm hD.symm c₂ s)

private noncomputable def pairingA (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f)) :
    GaloisField 2 f →+ GaloisField 2 f where
  toFun s := Multiplicative.toAdd (c₁.γ (pairingX hH hD c₂ s)) 2
  map_zero' := by
    have hα : c₂.α (Subgroup.inclusion (inclQ1L2 hH hD) (pairingX hH hD c₂ 0)) = 1 := by
      rw [pairingX_spec, uSL_zero]
    have hQ2 : (pairingX hH hD c₂ 0 : G) ∈ pCoreOf 2 L2 := by
      have h := (c₂.eq_one_iff
        (Subgroup.inclusion (inclQ1L2 hH hD) (pairingX hH hD c₂ 0))).mp hα
      simpa using h
    exact second_coord_eq_zero_of_mem_inf hH hD c₁ ⟨(pairingX hH hD c₂ 0).2, hQ2⟩
  map_add' s t := by
    have hs := pairingX_spec hH hD c₂ s
    have ht := pairingX_spec hH hD c₂ t
    have hst := pairingX_spec hH hD c₂ (s + t)
    have hprod : c₂.α (Subgroup.inclusion (inclQ1L2 hH hD)
        (pairingX hH hD c₂ s * pairingX hH hD c₂ t)) = uSL (s + t) := by
      rw [map_mul, map_mul, hs, ht, uSL_mul]
    have heq := alpha_second_eq_of_alpha_eq hH.symm hD.symm c₂ c₁
      (y1 := pairingX hH hD c₂ s * pairingX hH hD c₂ t)
      (y2 := pairingX hH hD c₂ (s + t)) (by rw [hprod, hst])
    change Multiplicative.toAdd (c₁.γ (pairingX hH hD c₂ (s + t))) 2 =
      Multiplicative.toAdd (c₁.γ (pairingX hH hD c₂ s)) 2 +
        Multiplicative.toAdd (c₁.γ (pairingX hH hD c₂ t)) 2
    rw [← heq]
    rw [map_mul, toAdd_mul]
    rfl

private lemma pairingA_bijective (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f)) :
    Function.Bijective (pairingA hH hD c₁ c₂) := by
  have hinj : Function.Injective (pairingA hH hD c₁ c₂) := by
    intro s t hst
    change Multiplicative.toAdd (c₁.γ (pairingX hH hD c₂ s)) 2 =
      Multiplicative.toAdd (c₁.γ (pairingX hH hD c₂ t)) 2 at hst
    let k : ↥(pCoreOf 2 L1) := pairingX hH hD c₂ s * (pairingX hH hD c₂ t)⁻¹
    have hlast : Multiplicative.toAdd (c₁.γ k) 2 = 0 := by
      have hγ : Multiplicative.toAdd (c₁.γ k) =
          Multiplicative.toAdd (c₁.γ (pairingX hH hD c₂ s)) -
            Multiplicative.toAdd (c₁.γ (pairingX hH hD c₂ t)) := by
        rw [show k = pairingX hH hD c₂ s * (pairingX hH hD c₂ t)⁻¹ from rfl,
          map_mul, map_inv, toAdd_mul, toAdd_inv]
        simp [sub_eq_add_neg]
      have h0 := congrFun hγ 2
      simp only [Pi.sub_apply] at h0
      rw [hst] at h0
      simpa using h0
    have hcent : (k : G) ∈ Subgroup.centralizer (S : Set G) :=
      (c₁.mem_centralizer_iff (hD.le_left hH) k).mpr hlast
    have hkℓ : (k : G) ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2 := by
      rw [← hD.inf_centralizer_left hH]
      exact ⟨k.2, hcent⟩
    have hkα : c₂.α (Subgroup.inclusion (inclQ1L2 hH hD) k) = 1 :=
      (c₂.eq_one_iff _).mpr (by simpa using hkℓ.2)
    have hkform : c₂.α (Subgroup.inclusion (inclQ1L2 hH hD) k) =
        uSL s * (uSL t)⁻¹ := by
      have h : Subgroup.inclusion (inclQ1L2 hH hD) k =
          Subgroup.inclusion (inclQ1L2 hH hD) (pairingX hH hD c₂ s) *
            (Subgroup.inclusion (inclQ1L2 hH hD) (pairingX hH hD c₂ t))⁻¹ := by
        rw [show k = pairingX hH hD c₂ s * (pairingX hH hD c₂ t)⁻¹ from rfl,
          map_mul, map_inv]
      rw [h, map_mul, map_inv, pairingX_spec, pairingX_spec]
    have hstUL : uSL s = uSL t := by
      have h : uSL s * (uSL t)⁻¹ = 1 := by
        rw [← hkform]
        exact hkα
      calc uSL s = uSL s * (uSL t)⁻¹ * uSL t := by group
        _ = 1 * uSL t := by rw [h]
        _ = uSL t := one_mul _
    exact uSL_injective hstUL
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

private noncomputable def pairingLineElem (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (u : GaloisField 2 f) : ↥(pCoreOf 2 L1) :=
  c₁.γ.symm (Multiplicative.ofAdd ![u, 0, 0])

private lemma pairingLineElem_coord (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (u : GaloisField 2 f) :
    Multiplicative.toAdd (c₁.γ (pairingLineElem hH hD c₁ u)) = ![u, 0, 0] := by
  simp [pairingLineElem]

private lemma pairingLineElem_add (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (u v : GaloisField 2 f) :
    pairingLineElem hH hD c₁ (u + v) =
      pairingLineElem hH hD c₁ u * pairingLineElem hH hD c₁ v := by
  apply c₁.γ.injective
  apply Multiplicative.toAdd.injective
  rw [map_mul, toAdd_mul, pairingLineElem_coord, pairingLineElem_coord, pairingLineElem_coord]
  ext i
  fin_cases i <;> simp

private lemma pairingLineElem_mem_blockZ (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (u : GaloisField 2 f) :
    (pairingLineElem hH hD c₁ u : G) ∈ blockZ L1 :=
  (c₁.mem_blockZ_iff hD.blockU_left (pairingLineElem hH hD c₁ u)).mpr (by
    rw [pairingLineElem_coord]
    exact ⟨rfl, rfl⟩)

private noncomputable def pairingLineElemRight (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (u : GaloisField 2 f) : ↥(pCoreOf 2 L2) :=
  ⟨pairingLineElem hH hD c₁ u, (hD.blockZ_left_le hH (pairingLineElem_mem_blockZ hH hD c₁ u)).2⟩

private lemma pairingLineElemRight_coe (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (u : GaloisField 2 f) :
    (pairingLineElemRight hH hD c₁ u : G) = (pairingLineElem hH hD c₁ u : G) := rfl

private lemma pairingLineElemRight_add (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (u v : GaloisField 2 f) :
    pairingLineElemRight hH hD c₁ (u + v) =
      pairingLineElemRight hH hD c₁ u * pairingLineElemRight hH hD c₁ v := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, pairingLineElemRight_coe, pairingLineElem_add]

private noncomputable def pairingL (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f)) :
    GaloisField 2 f →+ GaloisField 2 f where
  toFun u := Multiplicative.toAdd (c₂.γ (pairingLineElemRight hH hD c₁ u)) 1
  map_zero' := by
    have h : pairingLineElem hH hD c₁ 0 = 1 := by
      apply c₁.γ.injective
      apply Multiplicative.toAdd.injective
      rw [pairingLineElem_coord]
      funext i
      fin_cases i <;> simp
    have hR : pairingLineElemRight hH hD c₁ 0 = 1 := by
      apply Subtype.ext
      rw [pairingLineElemRight_coe]
      simpa using congrArg (fun x : ↥(pCoreOf 2 L1) => (x : G)) h
    rw [hR, map_one]
    simp
  map_add' u v := by
    rw [pairingLineElemRight_add, map_mul, toAdd_mul]
    rfl

private lemma pairingL_bijective (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f)) :
    Function.Bijective (pairingL hH hD c₁ c₂) := by
  have hinj : Function.Injective (pairingL hH hD c₁ c₂) := by
    intro u v huv
    change Multiplicative.toAdd (c₂.γ (pairingLineElemRight hH hD c₁ u)) 1 =
      Multiplicative.toAdd (c₂.γ (pairingLineElemRight hH hD c₁ v)) 1 at huv
    let z : ↥(pCoreOf 2 L1) :=
      pairingLineElem hH hD c₁ u * (pairingLineElem hH hD c₁ v)⁻¹
    have hZ1z : (z : G) ∈ blockZ L1 :=
      (blockZ L1).mul_mem (pairingLineElem_mem_blockZ hH hD c₁ u)
        ((blockZ L1).inv_mem (pairingLineElem_mem_blockZ hH hD c₁ v))
    have hzQ2 : (z : G) ∈ pCoreOf 2 L2 := (hD.blockZ_left_le hH hZ1z).2
    have hcoord := (Sp4qLocalData.mem_blockZ_left_iff (f := f) hf hH hD c₂
      ⟨z, hzQ2⟩).mp (by simpa [z] using hZ1z)
    have hγ₂ : Multiplicative.toAdd (c₂.γ (⟨z, hzQ2⟩ : ↥(pCoreOf 2 L2))) =
        Multiplicative.toAdd (c₂.γ (pairingLineElemRight hH hD c₁ u)) -
          Multiplicative.toAdd (c₂.γ (pairingLineElemRight hH hD c₁ v)) := by
      have hz_eq : (⟨z, hzQ2⟩ : ↥(pCoreOf 2 L2)) =
          pairingLineElemRight hH hD c₁ u * (pairingLineElemRight hH hD c₁ v)⁻¹ :=
        Subtype.ext (by simp [z, pairingLineElemRight_coe])
      rw [hz_eq, map_mul, map_inv, toAdd_mul, toAdd_inv]
      simp [sub_eq_add_neg]
    have hcoord1 : Multiplicative.toAdd (c₂.γ (⟨z, hzQ2⟩ : ↥(pCoreOf 2 L2))) 1 = 0 := by
      have h0 := congrFun hγ₂ 1
      simp only [Pi.sub_apply] at h0
      rw [huv] at h0
      simpa using h0
    have hvec : Multiplicative.toAdd (c₂.γ (⟨z, hzQ2⟩ : ↥(pCoreOf 2 L2))) = 0 := by
      funext i
      fin_cases i
      · exact hcoord.1
      · exact hcoord1
      · exact hcoord.2
    have hzQ2eq : (⟨z, hzQ2⟩ : ↥(pCoreOf 2 L2)) = 1 := by
      apply c₂.γ.injective
      apply Multiplicative.toAdd.injective
      rw [hvec]
      simp
    have hz1 : z = 1 :=
      Subtype.ext (by simpa using congrArg (fun x : ↥(pCoreOf 2 L2) => (x : G)) hzQ2eq)
    have hγ₁ : Multiplicative.toAdd (c₁.γ z) =
        ![u, 0, 0] - ![v, 0, 0] := by
      rw [show z = pairingLineElem hH hD c₁ u * (pairingLineElem hH hD c₁ v)⁻¹ from rfl,
        map_mul, map_inv, toAdd_mul, toAdd_inv, pairingLineElem_coord, pairingLineElem_coord]
      funext i
      fin_cases i <;> simp [Pi.sub_apply, sub_eq_add_neg]
    have hzero : Multiplicative.toAdd (c₁.γ z) 0 = 0 := by
      rw [hz1, map_one]
      simp
    have h0 := congrFun hγ₁ 0
    simp only [Pi.sub_apply] at h0
    rw [hzero] at h0
    exact sub_eq_zero.mp h0.symm
  exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩

private lemma pairingL_eq_coord (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f)) {z : ↥(pCoreOf 2 L1)}
    (hz : (z : G) ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2) :
    Multiplicative.toAdd (c₂.γ (⟨z, hz.2⟩ : ↥(pCoreOf 2 L2))) 1 =
      pairingL hH hD c₁ c₂ (Multiplicative.toAdd (c₁.γ z) 0) := by
  let u : GaloisField 2 f := Multiplicative.toAdd (c₁.γ z) 0
  let v : GaloisField 2 f := Multiplicative.toAdd (c₁.γ z) 1
  have h2z : Multiplicative.toAdd (c₁.γ z) 2 = 0 :=
    second_coord_eq_zero_of_mem_inf hH hD c₁ hz
  let z₁ : ↥(pCoreOf 2 L1) := pairingLineElem hH hD c₁ u
  let z₂ : ↥(pCoreOf 2 L1) := z₁⁻¹ * z
  have hzvec : Multiplicative.toAdd (c₁.γ z) = ![u, v, 0] := by
    funext i
    fin_cases i <;> simp [u, v, h2z]
  have hz₁vec : Multiplicative.toAdd (c₁.γ z₁) = ![u, 0, 0] :=
    pairingLineElem_coord hH hD c₁ u
  have hz₂vec : Multiplicative.toAdd (c₁.γ z₂) = ![0, v, 0] := by
    have hγ : Multiplicative.toAdd (c₁.γ z₂) =
        -Multiplicative.toAdd (c₁.γ z₁) + Multiplicative.toAdd (c₁.γ z) := by
      rw [show z₂ = z₁⁻¹ * z from rfl, map_mul, toAdd_mul, map_inv, toAdd_inv]
    rw [hγ, hz₁vec, hzvec]
    funext i
    fin_cases i <;> simp [Pi.add_apply, Pi.neg_apply]
  have hz₂Z2 : (z₂ : G) ∈ blockZ L2 :=
    (Sp4qLocalData.mem_blockZ_right_iff (f := f) hf hH hD c₁ z₂).mpr (by
      rw [hz₂vec]
      exact ⟨rfl, rfl⟩)
  have hz₂Q2 : (z₂ : G) ∈ pCoreOf 2 L2 := (hD.blockZ_right_le hH hz₂Z2).2
  let z₂₂ : ↥(pCoreOf 2 L2) := ⟨z₂, hz₂Q2⟩
  have hz₂Z2' : (z₂₂ : G) ∈ blockZ L2 := by simpa [z₂₂] using hz₂Z2
  have hz₂coord : Multiplicative.toAdd (c₂.γ z₂₂) 1 = 0 :=
    ((c₂.mem_blockZ_iff hD.blockU_right z₂₂).mp hz₂Z2').1
  have hzdecomp : (⟨z, hz.2⟩ : ↥(pCoreOf 2 L2)) =
      pairingLineElemRight hH hD c₁ u * z₂₂ := by
    apply Subtype.ext
    simp [z₂₂, z₁, z₂, pairingLineElemRight_coe]
  have hγ : Multiplicative.toAdd (c₂.γ (⟨z, hz.2⟩ : ↥(pCoreOf 2 L2))) =
      Multiplicative.toAdd (c₂.γ (pairingLineElemRight hH hD c₁ u)) +
        Multiplicative.toAdd (c₂.γ z₂₂) := by
    rw [hzdecomp, map_mul, toAdd_mul]
  have h1 := congrFun hγ 1
  simp only [Pi.add_apply] at h1
  rw [hz₂coord, add_zero] at h1
  exact h1

private lemma commutator_mem_inf (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (x : ↥(pCoreOf 2 L1)) (y : ↥(pCoreOf 2 L2)) :
    (y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹ ∈
        pCoreOf 2 L1 ⊓ pCoreOf 2 L2 ∧
      (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈
        pCoreOf 2 L1 ⊓ pCoreOf 2 L2 ∧
      (y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹ =
        (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ := by
  have hQ1L2 : pCoreOf 2 L1 ≤ L2 := inclQ1L2 hH hD
  have hQ2L1 : pCoreOf 2 L2 ≤ L1 := hD.pCoreOf_right_le_left hH
  have hzQ1 : (y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 L1 := by
    have h1 : (y : G) * (x : G) * (y : G)⁻¹ ∈ pCoreOf 2 L1 :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L1 (hQ2L1 y.2))
        (x : G)).mp x.2
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ x.2)
  have hzQ2 : (y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 L2 := by
    have h1 : (x : G) * (y : G)⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 L2 :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L2 (hQ1L2 x.2))
        (y : G)⁻¹).mp (Subgroup.inv_mem _ y.2)
    have heq : (y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹ =
        (y : G) * ((x : G) * (y : G)⁻¹ * (x : G)⁻¹) := by group
    rw [heq]
    exact Subgroup.mul_mem _ y.2 h1
  have hz'Q1 : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 L1 := by
    have h1 : (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 L1 :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L1 (hQ2L1 y.2))
        (x : G)⁻¹).mp (Subgroup.inv_mem _ x.2)
    have heq : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ =
        (x : G) * ((y : G) * (x : G)⁻¹ * (y : G)⁻¹) := by group
    rw [heq]
    exact Subgroup.mul_mem _ x.2 h1
  have hz'Q2 : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 L2 := by
    have h1 : (x : G) * (y : G) * (x : G)⁻¹ ∈ pCoreOf 2 L2 :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L2 (hQ1L2 x.2))
        (y : G)).mp y.2
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ y.2)
  have hinv : (y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹ =
      ((x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹)⁻¹ := by group
  refine ⟨⟨hzQ1, hzQ2⟩, ⟨hz'Q1, hz'Q2⟩, ?_⟩
  rw [hinv]
  exact inv_eq_of_mul_eq_one_right
    (by simpa [pow_two] using hD.elem_left.2 _ hz'Q1)

private lemma commutator_coord (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f))
    {x : ↥(pCoreOf 2 L1)} {y : ↥(pCoreOf 2 L2)}
    {σ τ : GaloisField 2 f}
    (hx : c₂.α (Subgroup.inclusion (inclQ1L2 hH hD) x) = uSL σ)
    (hy : c₁.α (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) y) = uSL τ)
    (z₁ : ↥(pCoreOf 2 L1)) (z₂ : ↥(pCoreOf 2 L2))
    (hz₁ : (z₁ : G) = (y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹)
    (hz₂ : (z₂ : G) = (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹) :
    Multiplicative.toAdd (c₁.γ z₁) =
        ![τ * Multiplicative.toAdd (c₁.γ x) 2,
          τ ^ 2 * Multiplicative.toAdd (c₁.γ x) 2, 0] ∧
      Multiplicative.toAdd (c₂.γ z₂) =
        ![σ * Multiplicative.toAdd (c₂.γ y) 2,
          σ ^ 2 * Multiplicative.toAdd (c₂.γ y) 2, 0] ∧
      (z₁ : G) = (z₂ : G) := by
  have hx' : (c₂.α (Subgroup.inclusion (inclQ1L2 hH hD) x) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, σ; 0, 1] := by
    simpa [uSL, uMat] using congrArg Subtype.val hx
  have hy' : (c₁.α (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) y) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, τ; 0, 1] := by
    simpa [uSL, uMat] using congrArg Subtype.val hy
  refine ⟨?_, ?_, ?_⟩
  · exact c₁.commutator (s := Subgroup.inclusion (hD.pCoreOf_right_le_left hH) y) (x := x)
      (v := z₁) hy' (by simpa using hz₁)
  · exact c₂.commutator (s := Subgroup.inclusion (inclQ1L2 hH hD) x) (x := y)
      (v := z₂) hx' (by simpa using hz₂)
  · have hmem := commutator_mem_inf hH hD x y
    rw [hz₁, hz₂]
    exact hmem.2.2

private noncomputable def pairingAE (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f)) :
    GaloisField 2 f ≃+ GaloisField 2 f :=
  AddEquiv.ofBijective (pairingA hH hD c₁ c₂) (pairingA_bijective hH hD c₁ c₂)

private noncomputable def pairingAMap (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f)) :
    GaloisField 2 f →+ GaloisField 2 f where
  toFun y := (pairingAE hH hD c₁ c₂).symm y ^ 2
  map_zero' := by simp
  map_add' y z := by
    rw [map_add, add_sq]
    have h2 : (2 : GaloisField 2 f) = 0 := CharTwo.two_eq_zero
    simp [h2, add_assoc, add_left_comm, add_comm]

private lemma pairingL_pairingA (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f)) (s t : GaloisField 2 f) :
    pairingL hH hD c₁ c₂ (t * pairingA hH hD c₁ c₂ s) =
      s ^ 2 * pairingC hH hD c₁ c₂ t := by
  let x : ↥(pCoreOf 2 L1) := pairingX hH hD c₂ s
  let y : ↥(pCoreOf 2 L2) := pairingY hH hD c₁ t
  have hxα : c₂.α (Subgroup.inclusion (inclQ1L2 hH hD) x) = uSL s :=
    pairingX_spec hH hD c₂ s
  have hyα : c₁.α (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) y) = uSL t :=
    pairingY_spec hH hD c₁ t
  have hmem := commutator_mem_inf hH hD x y
  let z₁ : ↥(pCoreOf 2 L1) :=
    ⟨(y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹, hmem.1.1⟩
  let z₂ : ↥(pCoreOf 2 L2) :=
    ⟨(x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹, hmem.2.1.2⟩
  have hz₁ : (z₁ : G) = (y : G) * (x : G) * (y : G)⁻¹ * (x : G)⁻¹ := rfl
  have hz₂ : (z₂ : G) = (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ := rfl
  have hcomm := commutator_coord hH hD c₁ c₂ hxα hyα z₁ z₂ hz₁ hz₂
  have hz_eq : (⟨z₁, hmem.1.2⟩ : ↥(pCoreOf 2 L2)) = z₂ := Subtype.ext hcomm.2.2
  have hL := pairingL_eq_coord hf hH hD c₁ c₂ (z := z₁) (by simpa [z₁] using hmem.1)
  rw [hz_eq] at hL
  rw [hcomm.2.1] at hL
  rw [hcomm.1] at hL
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply] at hL
  change s ^ 2 * Multiplicative.toAdd (c₂.γ y) 2 =
    pairingL hH hD c₁ c₂ (t * (pairingA hH hD c₁ c₂ s)) at hL
  exact hL.symm

private lemma pairingL_mul_eq (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f) (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f))
    (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f)) :
    ∀ y t : GaloisField 2 f,
      pairingL hH hD c₁ c₂ (y * t) =
        pairingAMap hH hD c₁ c₂ y * pairingC hH hD c₁ c₂ t := by
  intro y t
  let s : GaloisField 2 f := (pairingAE hH hD c₁ c₂).symm y
  have hs : pairingA hH hD c₁ c₂ s = y := (pairingAE hH hD c₁ c₂).apply_symm_apply y
  have h := pairingL_pairingA hf hH hD c₁ c₂ s t
  rw [hs] at h
  rw [mul_comm t y] at h
  change pairingL hH hD c₁ c₂ (y * t) =
    (pairingAE hH hD c₁ c₂).symm y ^ 2 * pairingC hH hD c₁ c₂ t
  rw [show (pairingAE hH hD c₁ c₂).symm y = s from rfl]
  exact h

theorem Sp4qLocalData.exists_ringEquiv_pairing (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : Sp4qLocalData L1 L2 S f)
    (c₁ : Sp4VertexCoord L1 S (GaloisField 2 f)) (c₂ : Sp4VertexCoord L2 S (GaloisField 2 f)) :
    ∃ (ρ : GaloisField 2 f ≃+* GaloisField 2 f) (e₁ e₂ : (GaloisField 2 f)ˣ),
      (∀ (z₁ : ↥(pCoreOf 2 L1)) (z₂ : ↥(pCoreOf 2 L2)), (z₁ : G) = z₂ →
        (z₁ : G) ∈ blockZ L1 →
          Multiplicative.toAdd (c₂.γ z₂) 1 =
            e₁ * ρ (Multiplicative.toAdd (c₁.γ z₁) 0)) ∧
      (∀ (y : ↥(pCoreOf 2 L2)) (y' : ↥L1) (t : GaloisField 2 f), (y : G) = y' →
        (c₁.α y' : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) = !![1, t; 0, 1] →
          Multiplicative.toAdd (c₂.γ y) 2 = e₂ * ρ t) := by
  classical
  let F := GaloisField 2 f
  have hLbij := pairingL_bijective hf hH hD c₁ c₂
  have hCbij := pairingC_bijective hH hD c₁ c₂
  obtain ⟨ρ, hρl, -, hρc⟩ :=
    exists_ringEquiv_of_map_mul (pairingL hH hD c₁ c₂) (pairingAMap hH hD c₁ c₂)
      (pairingC hH hD c₁ c₂) hLbij (pairingL_mul_eq hf hH hD c₁ c₂)
  have hl1 : pairingL hH hD c₁ c₂ 1 ≠ 0 := by
    intro h0
    have h10 : (1 : F) = 0 := hLbij.1 (by rw [h0, map_zero])
    exact one_ne_zero h10
  have hc1 : pairingC hH hD c₁ c₂ 1 ≠ 0 := by
    intro h0
    have h10 : (1 : F) = 0 := hCbij.1 (by rw [h0, map_zero])
    exact one_ne_zero h10
  let e₁ : Fˣ := Units.mk0 (pairingL hH hD c₁ c₂ 1) hl1
  let e₂ : Fˣ := Units.mk0 (pairingC hH hD c₁ c₂ 1) hc1
  refine ⟨ρ, e₁, e₂, ?_, ?_⟩
  · intro z₁ z₂ hz hzZ1
    have hzℓ : (z₁ : G) ∈ pCoreOf 2 L1 ⊓ pCoreOf 2 L2 := hD.blockZ_left_le hH hzZ1
    have hcoord := pairingL_eq_coord hf hH hD c₁ c₂ (z := z₁) hzℓ
    have hz₂ : z₂ = (⟨z₁, hzℓ.2⟩ : ↥(pCoreOf 2 L2)) := Subtype.ext hz.symm
    rw [hz₂, hcoord, hρl]
    rfl
  · intro y y' t hy hyα
    have hincl : (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) y : ↥L1) = y' := Subtype.ext hy
    have hyα' : c₁.α (Subgroup.inclusion (hD.pCoreOf_right_le_left hH) y) = uSL t := by
      rw [hincl]
      apply Subtype.ext
      rw [coe_uSL, uMat]
      exact hyα
    have hspec := pairingY_spec hH hD c₁ t
    have heq := alpha_second_eq_of_alpha_eq hH hD c₁ c₂
      (y1 := y) (y2 := pairingY hH hD c₁ t) (by rw [hyα', hspec])
    rw [heq]
    change pairingC hH hD c₁ c₂ t = e₂ * ρ t
    rw [hρc]
    rfl

end CFSG.Quasithin.F112R.St84
