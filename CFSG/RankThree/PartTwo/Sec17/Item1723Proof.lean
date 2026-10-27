module

public import CFSG.RankThree.PartTwo.Sec17.Item1722Proof
public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProof

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

@[expose] def Claim1723Orbit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (w : G) (Q : Subgroup G), Sec17W G A c L Y₀ Y₁ S p P w Q →
      (∀ g ∈ Subgroup.normalizer (A : Set G), ∃ i : ℕ,
        (S ⊓ L).map (MulAut.conj g).toMonoidHom = (S ⊓ L).map (MulAut.conj (w ^ i)).toMonoidHom) ∧
      (S ⊓ L).map (MulAut.conj w).toMonoidHom ≠ S ⊓ L

section Steps

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ Y₁ S : Subgroup G}
  {p : ℕ} {P : Subgroup G} {w : G} {Q : Subgroup G}

theorem Sec17Y1.exists_conj_of_mem (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h168 : Item168 A (lB A) c L)
    (h1411 : Item1411_1 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY1Star A (lB A))
    (hYM : ¬ Y ≤ Subgroup.normalizer (Y₀ : Set G)) :
    ∃ g ∈ Subgroup.normalizer (A : Set G), Y = Y₁.map (MulAut.conj g).toMonoidHom := by
  have hs := h.toSec17Std
  have hY3 : Y ∈ scriptY3 A (lB A) := hY.prop.1
  obtain ⟨V, hV, hVY⟩ := HeadProof.exists_omega168_le hs h166 hbot hY3 hYM
  obtain ⟨N, hN, hYN, hNS⟩ := h168 (HeadProof.item168_premise hs) V hV Y hY3 hVY
  have hYN' : Y ≤ N := hYN Y hY3 le_rfl
  have hNY : N = Y := le_antisymm (hY.2 hN.prop hYN') hYN'
  rw [hNY] at hNS
  obtain ⟨SY, hSY⟩ := exists_mem_scriptQPiStar (A := A) (LB := lB A) Y (piOf 2)
  obtain ⟨hSYG, hSYY, -, -⟩ := hNS SY hSY
  obtain ⟨hSG, -, -, -⟩ := h.item168_at h166 hbot h168
  obtain ⟨g, hg, hgS⟩ := h1411 S hSG SY hSYG
  have hgA : g ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp hg).1
  have hY₁g := HeadProof.map_conj_mem_scriptY1Star hgA h.mem_y1Star
  have hle : Y₁.map (MulAut.conj g).toMonoidHom ≤ Y :=
    hSYY _ hY₁g.prop (hgS ▸ Subgroup.map_mono h.mem_qStar_two.prop.1.2)
  exact ⟨g, hgA, le_antisymm (hY₁g.2 hY.prop hle) hle⟩

theorem Sec17W.conj_eq_pow (h : Sec17W G A c L Y₀ Y₁ S p P w Q) (h166 : Item166 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h168 : Item168 A (lB A) c L)
    (horb : ∀ g ∈ Subgroup.normalizer (A : Set G), ∃ i : ℕ,
      (S ⊓ L).map (MulAut.conj g).toMonoidHom = (S ⊓ L).map (MulAut.conj (w ^ i)).toMonoidHom)
    (h1720 : Sec4.autIn (Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)) A ≤
      Sec4.autIn (Subgroup.normalizer (S : Set G)) A)
    (h1722 : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (Y₁ : Set G))
    {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    ∃ i : ℕ, i < 3 ∧
      Y₁.map (MulAut.conj g).toMonoidHom = Y₁.map (MulAut.conj (w ^ i)).toMonoidHom := by
  obtain ⟨-, -, -, hWS⟩ := h.toSec17Y1.item168_at h166 hbot h168
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp h.w_mem).1
  obtain ⟨i, hi⟩ := horb g hg
  set k := (w ^ i)⁻¹ * g with hk
  have hkSL : k ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    inv_mul_mem_normalizer_of_map_conj_eq hi.symm
  have hkA : k ∈ Subgroup.normalizer (A : Set G) := mul_mem (inv_mem (pow_mem hwA i)) hg
  have hσ : A.normalizerMonoidHom ⟨k, hkA⟩ ∈
      Sec4.autIn (Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)) A :=
    Sec4.mem_autIn_iff.mpr ⟨k, hkA, hkSL, rfl⟩
  obtain ⟨n, hnA, hnS, hn⟩ := Sec4.mem_autIn_iff.mp (h1720 hσ)
  have hxA : k * n⁻¹ ∈ Subgroup.normalizer (A : Set G) := mul_mem hkA (inv_mem hnA)
  have hker : A.normalizerMonoidHom ⟨k * n⁻¹, hxA⟩ = 1 := by
    have e : (⟨k * n⁻¹, hxA⟩ : Subgroup.normalizer (A : Set G)) =
        ⟨k, hkA⟩ * (⟨n, hnA⟩ : Subgroup.normalizer (A : Set G))⁻¹ := rfl
    rw [e, map_mul, map_inv, hn, mul_inv_cancel]
  have hxC : k * n⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
    exact hker
  have hxY : k * n⁻¹ ∈ Subgroup.normalizer (Y₁ : Set G) := h1722 hxC
  have hnY : n ∈ Subgroup.normalizer (Y₁ : Set G) := hWS (Subgroup.mem_inf.mpr ⟨hnA, hnS⟩)
  have hkY : k ∈ Subgroup.normalizer (Y₁ : Set G) := by
    have e : k = (k * n⁻¹) * n := by group
    rw [e]
    exact mul_mem hxY hnY
  have hgk : g = w ^ i * k := by rw [hk]; group
  refine ⟨i % 3, Nat.mod_lt _ (by norm_num), ?_⟩
  rw [hgk, map_conj_mul, Late.map_conj_eq_of_mem_normalizer hkY, ← h.orderOf_w, pow_mod_orderOf]

theorem Sec17W.map_conj_ne (h : Sec17W G A c L Y₀ Y₁ S p P w Q) (h1718 : Item1718)
    (hne : (S ⊓ L).map (MulAut.conj w).toMonoidHom ≠ S ⊓ L) :
    Y₁.map (MulAut.conj w).toMonoidHom ≠ Y₁ := by
  have hwL : w ∈ L := (Subgroup.mem_inf.mp h.w_mem).2
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := (Subgroup.mem_inf.mp h.w_mem).1
  refine h1718 G A c L Y₀ Y₁ S p P h.toSec17Y1 w
    (Subgroup.mem_inf.mpr ⟨hwA, h.le_y0 hwL⟩) fun hwS => hne ?_
  have hSL : S ⊓ L = (S ⊓ Y₀) ⊓ L := by
    rw [inf_assoc, inf_eq_right.mpr h.le_y0]
  rw [hSL, Subgroup.map_inf_eq _ _ _ (MulAut.conj w).injective,
    Late.map_conj_eq_of_mem_normalizer hwS,
    Late.map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hwL)]

omit [Finite G] in
theorem map_conj_pow_ne {Y₁ : Subgroup G} {w : G} (hw3 : w ^ 3 = 1)
    (hne : Y₁.map (MulAut.conj w).toMonoidHom ≠ Y₁) :
    Y₁ ≠ Y₁.map (MulAut.conj w).toMonoidHom ∧ Y₁ ≠ Y₁.map (MulAut.conj (w ^ 2)).toMonoidHom ∧
      Y₁.map (MulAut.conj w).toMonoidHom ≠ Y₁.map (MulAut.conj (w ^ 2)).toMonoidHom := by
  refine ⟨Ne.symm hne, fun h2 => hne ?_, fun h12 => hne ?_⟩
  ·
    calc Y₁.map (MulAut.conj w).toMonoidHom =
          (Y₁.map (MulAut.conj (w ^ 2)).toMonoidHom).map (MulAut.conj w).toMonoidHom := by
            rw [← h2]
      _ = Y₁ := by rw [map_conj_map_conj, ← pow_succ', hw3, map_conj_one]
  ·
    have := congrArg (Subgroup.map (MulAut.conj w⁻¹).toMonoidHom) h12
    rw [map_conj_map_conj, map_conj_map_conj, inv_mul_cancel, map_conj_one,
      show w⁻¹ * w ^ 2 = w by group] at this
    exact this.symm

end Steps

end CFSG.RankThree.PartTwo.Sec17
