module

public import CFSG.Quasithin.Background.RonanH163Main
public import CFSG.Quasithin.Background.RonanH164Std
public import CFSG.Quasithin.Background.RonanH164Tconj

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

theorem main164 {a b : Fin 24}
    (hab : a ≠ b) {O : Finset (Fin 24)} {S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ Γ : Subgroup P24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
    {β : ↥(⊤ : Subgroup V) →* ↥(golayC ⊓ pairKer a b) ⧸
      (Subgroup.zpowers (G6.allOnes 24)).subgroupOf (golayC ⊓ pairKer a b)}
    (hO : O.card = 8) (haO : a ∈ O) (hbO : b ∈ O) (hS : IsSextR S) (hBS : B ∈ S) (haB : a ∈ B)
    (hbB : b ∈ B) (hTO : ∀ g ∈ T₀, g • O = O) (hTS : ∀ g ∈ T₀, g • S = S)
    (hL : M22g a b ≤ Γ) (hSyl : IsSylowIn 2 (T₀ ⊓ Γ) Γ)
    (hreal : RealizesBy (FFModel.golaySec Γ (golayC ⊓ pairKer a b)
      (Subgroup.zpowers (G6.allOnes 24))) ρ.range ⊤ ⊥ ρ.rangeRestrict β) : Γ = M2ab a b → Concl164 ρ ((O.erase a).erase b) (S.erase B) := by
  intro hΓ
  obtain ⟨c, hca, hcb, hcO, hcS, hcB, hcΓ, φ, hφ, e, he'⟩ :=
    exists_std_iso hab hO haO hbO hS hBS haB hbB hTO hTS hL hSyl hΓ hreal
  have hH : c • (O.erase a).erase b = Hstd := by
    rw [smul_erase_finset c (O.erase a) b, smul_erase_finset c O a, hcO, hca, hcb, ← Hstd_eq]
  have hQ : c • S.erase B = Qstd := by
    rw [smul_erase_finset_finset, hcS, hcB, Sstd_erase]
  refine Concl164_of_transport c hcΓ ρ R φ hφ e he' _ _ ?_
  rw [hH, hQ]
  exact std164

end CFSG.Quasithin.RonanH163
