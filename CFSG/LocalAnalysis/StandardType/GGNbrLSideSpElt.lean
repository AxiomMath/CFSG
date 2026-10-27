module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitExcl
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitElt
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitGL3
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitQuot
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitCard
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpBlocks
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpComps
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpTypeSp
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpTypeGL
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideSpTypeGU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154Symp2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Open.StatedAPI CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private lemma induces_of_agree {R : Type} [Group R] {ψ ψ' : MulAut R} {J : Subgroup R}
    {α : MulAut (↥J ⧸ Subgroup.center ↥J)} (h : GGNbrLSideInduces ψ J α)
    (hag : ∀ j ∈ J, ψ' j = ψ j) : GGNbrLSideInduces ψ' J α := by
  intro j
  obtain ⟨j', hj', hα⟩ := h j
  exact ⟨j', by rw [hag _ j.2]; exact hj', hα⟩

theorem ggNbrLSideSp_elt {ℓ n : ℕ} {K : Type} [Field K] [Finite K] (hDet : GGNbrLSideClsDet)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ) (lab : LargeEvenLabel) :
    GGNbrLSideDichElt lab (LargeEvenProj (LargeEvenSpGroup K ℓ)) := by
  haveI : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  have hinj : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K ℓ)) :=
    CFSG.LocalAnalysis.GLTheoremA.K155XSp.l154s_proj_injective (CharP.cast_eq_zero K 2)
  intro a b ha1 ha3 _ hab J hJ Q hQ4 _ hF α hα
  obtain ⟨x, rfl⟩ : ∃ x, LargeEvenProjMk (LargeEvenSpGroup K ℓ) x = a :=
    QuotientGroup.mk'_surjective _ a
  obtain ⟨y, rfl⟩ : ∃ y, LargeEvenProjMk (LargeEvenSpGroup K ℓ) y = b :=
    QuotientGroup.mk'_surjective _ b
  have hx1 : x ≠ 1 := fun h => ha1 (by rw [h, map_one])
  have hx3 : x ^ 3 = 1 := hinj (by rw [map_pow, ha3, map_one])
  have hxy : x * y = y * x := hinj (by rw [map_mul, map_mul, hab])
  obtain ⟨A₁, A₂, y₁, y₂, hc, hjoin, hy₁, hy₂, hy, h₁, h₂, ⟨s, ⟨φ₁⟩⟩, hA₂⟩ :=
    ggNbrLSideSp_blocks hK hn hℓ x y hx3 hx1 hxy
  obtain ⟨F, _, _, hFQ, ⟨e⟩⟩ := hF
  have hF4 : 4 ≤ Nat.card F := by omega
  have hcard : 720 < Nat.card (projectiveSL 3 F) := ggNbrLSidePSL3_card_gt hF4
  rcases ggNbrLSideSp_components x A₁ A₂ hc hjoin h₁ h₂ J hJ with ⟨hq₁, hJeq⟩ | ⟨hq₂, hJeq⟩
  ·
    exfalso
    subst hJeq
    obtain ⟨e₂⟩ := ggNbrLSideQuot_map_equiv (LargeEvenProjMk (LargeEvenSpGroup K ℓ)) hinj ⁅A₁, A₁⁆
    have e' := e₂.symm.trans e
    rcases ggNbrLSideSp_typeSp hK hn φ₁ hq₁ with ⟨t, m, f, ht, hmodel⟩ | hle
    · obtain ⟨ht', hm', _⟩ := ggNbrLSideExcl hDet hO hF4 e' hmodel
      rcases ht with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [h1] at ht'
        exact absurd ht' (by decide)
      · omega
    · rw [Nat.card_congr e'.toEquiv] at hle
      omega
  · subst hJeq
    obtain ⟨e₂⟩ := ggNbrLSideQuot_map_equiv (LargeEvenProjMk (LargeEvenSpGroup K ℓ)) hinj ⁅A₂, A₂⁆
    have e' := e₂.symm.trans e
    rcases hA₂ with ⟨r, _, ⟨φ₂⟩⟩ | ⟨r, E, _, _, τ, hτ, _, hEc, hτQ, ⟨φ₂⟩⟩
    ·
      obtain ⟨_, hr3, hFn⟩ :=
        ggNbrLSideExcl hDet hO hF4 e' (ggNbrLSideSp_typeGL hK hn φ₂ hq₂)
      subst hr3
      have hQK : Q = Nat.card K := by rw [← hFQ, hFn, hK]
      subst hy
      have hag : ∀ j ∈ ⁅A₂, A₂⁆.map (LargeEvenProjMk (LargeEvenSpGroup K ℓ)),
          (MulAut.conj (LargeEvenProjMk (LargeEvenSpGroup K ℓ) y₂)) j =
            (MulAut.conj (LargeEvenProjMk (LargeEvenSpGroup K ℓ) (y₁ * y₂))) j := by
        rintro _ ⟨z, hz, rfl⟩
        have hzA : z ∈ A₂ := Subgroup.commutator_le_self _ hz
        have hw : y₂ * z * y₂⁻¹ ∈ A₂ := A₂.mul_mem (A₂.mul_mem hy₂ hzA) (A₂.inv_mem hy₂)
        have h1 : y₁ * (y₂ * z * y₂⁻¹) * y₁⁻¹ = y₂ * z * y₂⁻¹ :=
          mul_inv_eq_iff_eq_mul.2 (hc y₁ hy₁ _ hw)
        simp only [MulAut.conj_apply, ← map_inv, ← map_mul]
        congr 1
        rw [← h1]
        group
      left
      rw [hQK]
      exact ggNbrLSideGL3Witness (LargeEvenProjMk (LargeEvenSpGroup K ℓ)) hinj A₂ φ₂ ⟨y₂, hy₂⟩ α
        (induces_of_agree hα hag)
    ·
      exfalso
      obtain ⟨t, m, ht, hmodel⟩ := ggNbrLSideSp_typeGU hK hn hEc hτQ φ₂ hq₂
      obtain ⟨ht', hm', _⟩ := ggNbrLSideExcl hDet hO hF4 e' hmodel
      rcases ht with ⟨h1, _⟩ | ⟨_, h2⟩
      · rw [h1] at ht'
        exact absurd ht' (by decide)
      · omega

end CFSG.StandardType
