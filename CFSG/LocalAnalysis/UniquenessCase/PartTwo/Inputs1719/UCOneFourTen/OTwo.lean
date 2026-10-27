module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTenNormIOf
import CFSG.GroupTheory.PGroup.LtInfNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centOverO2_le (M L : Subgroup G) : F08.CentOverO2 M L ≤ M := by
  rw [F08.CentOverO2]
  exact (Subgroup.closure_le M).2 (by rintro x ⟨hxM, _⟩; exact hxM)

theorem centOverO2_le_normalizer (M L : Subgroup G) :
    F08.CentOverO2 M L ≤ normalizer (L : Set G) := by
  rw [F08.CentOverO2]
  apply (Subgroup.closure_le _).2
  rintro x ⟨hxM, hx⟩
  change x ∈ normalizer (L : Set G)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hmaple : L.map (MulAut.conj x).toMonoidHom ≤ L := by
    rintro y ⟨l, hl, rfl⟩
    have hmem : (MulAut.conj x).toMonoidHom l = (x * l * x⁻¹ * l⁻¹) * l := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [hmem]
    exact L.mul_mem (CFSG.LieType.BorelTits.pCoreOf_le 2 L (hx l hl)) hl
  exact Subgroup.eq_of_le_of_card_ge hmaple
    (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective])

theorem pCoreOf_le_centOverO2 {M L : Subgroup G} (hL : L ∈ calC M) :
    CFSG.Open.pCoreOf 2 M ≤ F08.CentOverO2 M L := by
  have hLM : L ≤ M := CFSG.Open.IsSubnormal.le hL.1
  have hsub : CFSG.Open.IsSubnormal L M := hL.1
  have hperf : ⁅L, L⁆ = L := hL.2.1
  have hN : CFSG.Open.pCoreOf 2 M ≤ normalizer (L : Set G) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TenTenNormI.pCoreOf_le_normalizer hLM hsub hperf
  intro x hx
  rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff]
  constructor
  · exact CFSG.LieType.BorelTits.pCoreOf_le 2 M hx
  · intro l hl
    have hxl : x * l * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hN hx) l).mp hl
    have hcommL : x * l * x⁻¹ * l⁻¹ ∈ L := L.mul_mem hxl (L.inv_mem hl)
    have hMnorm : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
    have hlx : l * x⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
      (Subgroup.mem_normalizer_iff.mp (hMnorm (hLM hl)) x⁻¹).mp
        ((CFSG.Open.pCoreOf 2 M).inv_mem hx)
    have hcommM : x * l * x⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
      have := (CFSG.Open.pCoreOf 2 M).mul_mem hx hlx
      simpa [mul_assoc] using this
    have hcommN : x * l * x⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 M ⊓ L :=
      Subgroup.mem_inf.mpr ⟨hcommM, hcommL⟩
    have hNL : CFSG.Open.pCoreOf 2 M ⊓ L ≤ CFSG.Open.pCoreOf 2 L := by
      apply CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      · intro l hl
        rw [Subgroup.mem_normalizer_iff]
        intro y
        rw [Subgroup.mem_inf, Subgroup.mem_inf]
        constructor
        · intro hy
          exact ⟨(Subgroup.mem_normalizer_iff.mp (hMnorm (hLM hl)) y).mp hy.1,
            L.mul_mem (L.mul_mem hl hy.2) (L.inv_mem hl)⟩
        · intro hy
          exact ⟨(Subgroup.mem_normalizer_iff.mp (hMnorm (hLM hl)) y).mpr hy.1,
            by simpa [mul_assoc] using L.mul_mem (L.mul_mem (L.inv_mem hl) hy.2) hl⟩
      · exact IsPGroup.to_le (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) inf_le_left
    exact hNL hcommN

theorem pCoreOf_le_of_isSylowOf {H M L R : Subgroup G} (hMH : M ≤ H) (hL : L ∈ calC M)
    (hR : IsSylowOf 2 R (F08.CentOverO2 M L)) (hNR : H ⊓ normalizer (R : Set G) ≤ M) :
    CFSG.Open.pCoreOf 2 H ≤ R := by
  have hOM_le_R : CFSG.Open.pCoreOf 2 M ≤ R := by
    have hC : CFSG.Open.pCoreOf 2 M ≤ F08.CentOverO2 M L := pCoreOf_le_centOverO2 hL
    have hOM_sup_p : IsPGroup 2 (CFSG.Open.pCoreOf 2 M ⊔ R : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hR.isPGroup
        ((hR.le.trans (centOverO2_le M L)).trans
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
    have hOM_sup_le_C : CFSG.Open.pCoreOf 2 M ⊔ R ≤ F08.CentOverO2 M L :=
      sup_le hC hR.le
    have heq := CFSG.ABGLocalTools.IsSylowOf.eq_of_le hR le_sup_right hOM_sup_le_C hOM_sup_p
    exact le_sup_left.trans (le_of_eq heq)
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 H
  have hQH : Q ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hQnormH : H ≤ normalizer (Q : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hRH : R ≤ H := hR.le.trans (le_trans (centOverO2_le M L) hMH)
  have hMnorm : M ≤ normalizer (Q ⊓ M : Subgroup G) :=
    (le_inf (hMH.trans hQnormH) Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hpq : IsPGroup 2 (Q ⊓ M : Subgroup G) := hQp.to_inf_left
  have hQM_le_OM : Q ⊓ M ≤ CFSG.Open.pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hMnorm hpq
  have hNQ_le_R : Q ⊓ normalizer (R : Set G) ≤ R := by
    have h1 : Q ⊓ normalizer (R : Set G) ≤ H ⊓ normalizer (R : Set G) :=
      inf_le_inf hQH le_rfl
    have h2 : Q ⊓ normalizer (R : Set G) ≤ M := h1.trans hNR
    exact (le_inf inf_le_left h2).trans (hQM_le_OM.trans hOM_le_R)
  have hNQ_eq : Q ⊓ normalizer (R : Set G) = Q ⊓ R := by
    apply le_antisymm
    · exact le_inf inf_le_left hNQ_le_R
    · exact inf_le_inf le_rfl Subgroup.le_normalizer
  have hQR : Q ≤ R := by
    have hPp : IsPGroup 2 (Q ⊔ R : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' hQp hR.isPGroup (hRH.trans hQnormH)
    by_contra hle
    have hne : R ≠ Q ⊔ R := by
      intro heq
      apply hle
      rw [heq]
      exact le_sup_left
    have hlt : R < Q ⊔ R := lt_of_le_of_ne le_sup_right hne
    have hltN : R < (Q ⊔ R) ⊓ normalizer (R : Set G) :=
      CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hPp hlt
    have hmod : (Q ⊔ R) ⊓ normalizer (R : Set G) = R := by
      apply le_antisymm
      · intro x hx
        obtain ⟨hxP, hxN⟩ := Subgroup.mem_inf.mp hx
        have hxProd : x ∈ ((Q ⊔ R : Subgroup G) : Set G) := hxP
        rw [Subgroup.coe_mul_of_right_le_normalizer_left Q R (hRH.trans hQnormH)] at hxProd
        obtain ⟨q, hqQ, r, hrR, rfl⟩ := hxProd
        have hqN : q ∈ normalizer (R : Set G) := by
          have hrN : r ∈ normalizer (R : Set G) := Subgroup.le_normalizer hrR
          have hxN' : q * r ∈ normalizer (R : Set G) := hxN
          have : (q * r) * r⁻¹ ∈ normalizer (R : Set G) :=
            (normalizer (R : Set G)).mul_mem hxN' ((normalizer (R : Set G)).inv_mem hrN)
          simpa [mul_assoc] using this
        have hqR : q ∈ R := by
          have : q ∈ Q ⊓ normalizer (R : Set G) := Subgroup.mem_inf.mpr ⟨hqQ, hqN⟩
          rw [hNQ_eq] at this
          exact (Subgroup.mem_inf.mp this).2
        exact R.mul_mem hqR hrR
      · exact le_inf le_sup_right Subgroup.le_normalizer
    rw [hmod] at hltN
    exact (lt_irrefl R) hltN
  exact hQR

private theorem centOverO2_inf_eq {X Y L : Subgroup G} :
    F08.CentOverO2 (X ⊓ Y) L = F08.CentOverO2 X L ⊓ Y := by
  ext x
  rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff,
    Subgroup.mem_inf, Subgroup.mem_inf,
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff]
  constructor
  · rintro ⟨⟨hxX, hxY⟩, hxL⟩
    exact ⟨⟨hxX, hxL⟩, hxY⟩
  · rintro ⟨⟨hxX, hxL⟩, hxY⟩
    exact ⟨⟨hxX, hxY⟩, hxL⟩

theorem isSylowOf_centOverO2_inf {M L R H₁ : Subgroup G}
    (hR : IsSylowOf 2 R (F08.CentOverO2 M L)) (hRH : R ≤ H₁) :
    IsSylowOf 2 R (F08.CentOverO2 (M ⊓ H₁) L) := by
  rw [centOverO2_inf_eq (X := M) (Y := H₁) (L := L)]
  exact CFSG.ABGLocalTools.IsSylowOf.of_le hR (le_inf hR.le hRH) inf_le_left

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
