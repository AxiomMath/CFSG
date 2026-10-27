module

public import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

section Statement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def x1720 (A Y₀ S L : Subgroup G) : Subgroup G :=
  delta A (lB A) (cQuot Y₀) ⊔ (S ⊓ L)

end Statement

@[expose] def Claim1720 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      S ∈ scriptQPiStar A (lB A) (x1720 A Y₀ S L) (piOf 2) ∧
        TransOn A (lB A) (xA A) (x1720 A Y₀ S L)

namespace HeadProof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_cQuot {Y₀ : Subgroup G} {g x : G} (hg : g ∈ Subgroup.normalizer (Y₀ : Set G))
    (hx : x ∈ cQuot Y₀) : g * x * g⁻¹ ∈ cQuot Y₀ := by
  set N := Subgroup.normalizer (Y₀ : Set G) with hN
  rw [← SetLike.mem_coe, coe_cQuot] at hx ⊢
  obtain ⟨hxN, hxC⟩ := hx
  refine ⟨N.mul_mem (N.mul_mem hg hxN) (N.inv_mem hg), fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ Y₀ := by
    have := (Subgroup.mem_normalizer_iff.mp (N.inv_mem hg) y).mp hy
    rwa [inv_inv] at this
  have hgO : g ∈ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y₀ : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀ hg
  have h2 := (Subgroup.mem_normalizer_iff.mp hgO _).mp (hxC _ hy')
  have e : g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹ * y⁻¹ =
      g * (x * (g⁻¹ * y * g) * x⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
  rw [e]
  exact h2

omit [Finite G] in
theorem normalizer_le_normalizer_cQuot (Y₀ : Subgroup G) :
    Subgroup.normalizer (Y₀ : Set G) ≤ Subgroup.normalizer (cQuot Y₀ : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_cQuot hg, fun hx => ?_⟩
  have := conj_mem_cQuot (Subgroup.inv_mem _ hg) hx
  simpa [mul_assoc] using this

theorem map_conj_x1720 {A : Subgroup G} {c : G} {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    {S : Subgroup G} {n : G} (hnA : n ∈ Subgroup.normalizer (A : Set G))
    (hnSL : n ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)) :
    (x1720 A Y₀ S L).map (MulAut.conj n).toMonoidHom = x1720 A Y₀ S L := by
  have hnM : n ∈ Subgroup.normalizer (Y₀ : Set G) := h.normalizer_le hnA
  rw [x1720, Subgroup.map_sup, map_conj_delta hnA,
    Late.map_conj_eq_of_mem_normalizer (normalizer_le_normalizer_cQuot Y₀ hnM),
    Late.map_conj_eq_of_mem_normalizer hnSL]

end HeadProof

section Item1720

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
  {L Y₀ Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}

theorem rank3II_17_20_le_of (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (hC : Claim1720) :
    Sec4.autIn (Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)) A ≤
      Sec4.autIn (Subgroup.normalizer (S : Set G)) A := by
  intro σ hσ
  obtain ⟨n, hnA, hnSL, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
  obtain ⟨hSX, htr⟩ := hC G A c L Y₀ Y₁ S p P h
  have hSn : S.map (MulAut.conj n).toMonoidHom ∈
      scriptQPiStar A (lB A) (x1720 A Y₀ S L) (piOf 2) := by
    have := HeadProof.map_conj_mem_scriptQPiStar hnA hSX
    rwa [HeadProof.map_conj_x1720 h.toSec17Std hnA hnSL] at this
  obtain ⟨x, hx, hxS⟩ := htr S hSX _ hSn
  have hxC : x ∈ Subgroup.centralizer (A : Set G) :=
    CFSG.RankThree.PartTwo.Sec14.pPrimeCoreOf_le 3 _ hx.1
  have hxN : x⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.centralizer_le_normalizer _ (inv_mem hxC)
  have hmA : x⁻¹ * n ∈ Subgroup.normalizer (A : Set G) := mul_mem hxN hnA
  have hmS : x⁻¹ * n ∈ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show S.map (MulAut.conj (x⁻¹ * n)).toMonoidHom = S
    rw [← map_conj_map_conj, hxS, map_conj_map_conj, inv_mul_cancel, map_conj_one]
  have hker : A.normalizerMonoidHom ⟨x⁻¹, hxN⟩ = 1 := by
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    exact inv_mem hxC
  refine Sec4.mem_autIn_iff.mpr ⟨x⁻¹ * n, hmA, hmS, ?_⟩
  have e : (⟨x⁻¹ * n, hmA⟩ : Subgroup.normalizer (A : Set G)) = ⟨x⁻¹, hxN⟩ * ⟨n, hnA⟩ := rfl
  rw [e, map_mul, hker, one_mul]

end Item1720

end CFSG.RankThree.PartTwo.Sec17
