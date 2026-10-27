module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CoprimePSU
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourLocalMaps
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourSpinLifts
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHyperbolic

public noncomputable section

namespace CFSG.StandardType.F4KGPosition

open CFSG.LieType.Universal CFSG.Assembly CFSG.Open CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.TableCRes

theorem exists_unitary_lifts_of_f4_member
    (hMp : GGInnerDiagMpInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) (hX : X = L ∨ X = K) {f : ℕ}
    (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f - 1) (hmark : GGCentralImage .PSU 6 f X) :
    ∃ ψ : (ggU .PSU 6 f).K →* G,
      ψ.ker ≤ Subgroup.center (ggU .PSU 6 f).K ∧ ψ.range = X ∧
      ∃ ℓ : ↥Bs →* (ggU .PSU 6 f).K,
        (∀ (b : ↥Bs) (u : (ggU .PSU 6 f).K),
          (b : G)⁻¹ * ψ u * (b : G) = ψ (ℓ b * u * (ℓ b)⁻¹)) ∧
        ℓ.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (X : Set G) ∧
        (∀ b : ↥Bs, ℓ b ^ p = 1) ∧ p ^ 3 ≤ Nat.card ℓ.range := by
  cases f with
  | zero => omega
  | succ g =>
    obtain ⟨hp, hp2, _, h4⟩ := hcfg.1.1.1.2.2.2.2.2.1
    have hBs : IsElemAbelian p Bs := hcfg.1.1.2.1.2.1
    have hBBs : B ≤ Bs := hcfg.1.1.2.1.1
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G :=
      hcfg.1.1.1.2.2.2.2.2.2.1.1.2.1
    have h4Bs : p ^ 4 ≤ Nat.card Bs := calc
      p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos h4
      _ = Nat.card B := hBcard.symm
      _ ≤ Nat.card Bs := Subgroup.card_le_of_le hBBs
    obtain ⟨ψ, hadm, hker, hrange⟩ := hmark
    have hrk : 2 ≤ (ggU .PSU 6 (g + 1)).D.rank :=
      two_le_lieUniversal_rank .PSU 6 2 (g + 1) Nat.prime_two hadm (by decide)
    obtain ⟨hN, hdiag, hcard⟩ := ggF4QGeFour_localMap_of_mp hMp hcfg hX ψ hadm hrk hker hrange
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let ψn : ↥(Unitary.SU (PSUσ g) 6) →* G := ψ
    have hdiag' : ∀ b ∈ Bs, GGPsiInnerDiag (Unitary.rootDatum (card_PSUF g) 6) ψn b := hdiag
    have hN' : Bs ≤ Subgroup.normalizer (ψn.range : Set G) := by
      rw [show ψn.range = X from hrange]
      exact hN
    have hcard' : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψn.range : Set G)) ≤ Nat.card Bs := by
      rw [show ψn.range = X from hrange]
      exact hcard
    have hpq' : ¬ p ∣ 2 ^ (g + 1) + 1 :=
      not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
    obtain ⟨ℓ, hℓ, hkerℓ, hpowℓ, hrankℓ⟩ := exists_unitary_lift_kernel_rank
      ψn hker hadm hp hp2 Bs hBs hN' hdiag' h4Bs hpq' hcard'
    refine ⟨ψ, hker, hrange, ℓ, hℓ, ?_, hpowℓ, hrankℓ⟩
    rw [show ψn.range = X from hrange] at hkerℓ
    exact hkerℓ

theorem exists_unitary_lifts_of_f4_member_holds
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) (hX : X = L ∨ X = K) {f : ℕ}
    (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f - 1) (hmark : GGCentralImage .PSU 6 f X) :
    ∃ ψ : (ggU .PSU 6 f).K →* G,
      ψ.ker ≤ Subgroup.center (ggU .PSU 6 f).K ∧ ψ.range = X ∧
      ∃ ℓ : ↥Bs →* (ggU .PSU 6 f).K,
        (∀ (b : ↥Bs) (u : (ggU .PSU 6 f).K),
          (b : G)⁻¹ * ψ u * (b : G) = ψ (ℓ b * u * (ℓ b)⁻¹)) ∧
        ℓ.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (X : Set G) ∧
        (∀ b : ↥Bs, ℓ b ^ p = 1) ∧ p ^ 3 ≤ Nat.card ℓ.range := by
  exact exists_unitary_lifts_of_f4_member ggInnerDiagMpInput_holds hcfg hX hf hpq hmark

end CFSG.StandardType.F4KGPosition
