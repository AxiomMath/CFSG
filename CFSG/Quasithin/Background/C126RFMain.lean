module

public import CFSG.Quasithin.Background.C126RFCases
public import CFSG.Quasithin.Background.GoldschmidtE23Glue
public import CFSG.Quasithin.Background.GoldschmidtE23Blocks

public section

namespace CFSG.Quasithin.C126

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin B2F E2

variable {G : Type} [Group G]

section Rho

variable {V K₁ : Subgroup G} (hV : IsElemAbelian 2 V)

@[expose] noncomputable def barRho (hKN : K₁ ≤ Subgroup.normalizer (V : Set G))
    (hQ : pCoreOf 2 K₁ ≤ Subgroup.centralizer (V : Set G)) :
    (↥K₁ ⧸ CFSG.Open.pCore 2 ↥K₁) →* MulAut (IntMod V hV) :=
  QuotientGroup.lift (CFSG.Open.pCore 2 ↥K₁) (convHom hV K₁ hKN) (fun x hx => by
    rw [ker_convHom hV K₁ hKN, Subgroup.mem_subgroupOf]
    exact ⟨x.2, hQ (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)⟩)

theorem range_barRho (hKN : K₁ ≤ Subgroup.normalizer (V : Set G))
    (hQ : pCoreOf 2 K₁ ≤ Subgroup.centralizer (V : Set G)) :
    (barRho hV hKN hQ).range = autI hV K₁ := by
  rw [← range_convHom hV K₁ hKN]
  ext φ
  constructor
  · rintro ⟨q, rfl⟩
    induction q using QuotientGroup.induction_on with
    | _ x => exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨QuotientGroup.mk x, rfl⟩

end Rho

variable [Finite G]

theorem a134_of_cases {H T V K₁ : Subgroup G}
    {hV : IsElemAbelian 2 V} (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hK₁H : K₁ ≤ H)
    (hHK₁ : H ≤ Subgroup.normalizer (K₁ : Set G)) (hres : twoResidual H = K₁)
    (hQV : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G))
    (hY : CFSG.Open.IsQuasisimple (↥K₁ ⧸ CFSG.Open.pCore 2 ↥K₁))
    (hcase : NatCase H T V hV ∨ A5Case H T V hV) :
    A134TypesCentral (↥K₁ ⧸ CFSG.Open.pCore 2 ↥K₁) := by
  have hKN : K₁ ≤ Subgroup.normalizer (V : Set G) := hK₁H.trans hHN
  have hQK : pCoreOf 2 K₁ ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₁).trans hK₁H)
      (hHK₁.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
  obtain ⟨P, hP, hPperf, hPJ, hPN⟩ := exists_perfect_normalized hcase
  have hJH : K₁ ≤ thompsonJ H := by
    rw [← hres]
    exact hcase.elim (fun h => h.1) (fun h => h.1)
  have hPH : P ≤ autI hV H := hPJ.trans (autI_mono hV (thompsonJ_le_self H))
  have hPK : P ≤ autI hV K₁ := by
    have h1 := GE23.le_twoResidual_of_perfect hPH hPperf
    rw [← GE23.autI_twoResidual_eq hV hHN, hres] at h1
    exact h1
  have hKP : autI hV K₁ ≤ Subgroup.normalizer (P : Set _) := (autI_mono hV hJH).trans hPN
  have hrange := range_barRho hV hKN (hQK.trans hQV)
  have hnc : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
    have := hP.nontrivial
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_perfect hPperf
    exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩
  obtain ⟨f, hf⟩ := exists_surjective_to_normal hY (barRho hV hKN (hQK.trans hQV))
    (L := P) (hrange ▸ hPK) (hrange ▸ hKP) hnc
  exact a134_of_surjective hY hP f hf

omit [Finite G] in
theorem not_isSolvable_of_cases {H T V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hHN : H ≤ Subgroup.normalizer (V : Set G)) (hcase : NatCase H T V hV ∨ A5Case H T V hV) :
    ¬ Group.IsSolvable ↥H := by
  intro hsolv
  obtain ⟨P, hP, hPperf, hPJ, -⟩ := exists_perfect_normalized hcase
  have hPH : P ≤ autI hV H := hPJ.trans (autI_mono hV (thompsonJ_le_self H))
  have hsolvA : Group.IsSolvable ↥(autI hV H) := by
    rw [← range_convHom hV H hHN]
    exact Group.isSolvable_of_surjective (f := (convHom hV H hHN).rangeRestrict)
      (MonoidHom.rangeRestrict_surjective _)
  have hsolvP : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hPH)
      (Subgroup.inclusion_injective hPH)
  have := hP.nontrivial
  have := hPperf
  exact Group.IsPerfect.not_isSolvable (G := ↥P) hsolvP

end CFSG.Quasithin.C126
