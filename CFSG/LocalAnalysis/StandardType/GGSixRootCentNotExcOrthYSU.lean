module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcOrthYDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcOrthYSULevi
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcOrthYSUFrame
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcOrthYSUConj

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Inputs

theorem ggRootCentOrthYSUInput_holds :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (ψ : (ggU .PSU 6 1).K →* G),
      GGSixCtxV2 p B Bs x L D J (ggU .PSU 6 1).D .PSU 6 1 ψ → GGSixStepOne p B Bs x L D J →
        GGSixStepTwo p B Bs x L D J → p = 3 → ∀ (E : Subgroup G) (r : G),
        GGStepThreeChoice p Bs (ggM p B x L D J) (ggU .PSU 6 1).D .PSU ψ E r →
          GGRootCentOrthYData p B x L D J r := by
  intro G _ _ p B Bs x L D J
  have e : ggU .PSU 6 1 = ⟨SU (unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) 6,
      Unitary.rootDatum (card_galoisField_two_mul 2 1 le_rfl) 6⟩ := by
    simp only [ggU, lieUniversal, le_refl, ↓reduceDIte]
  rw [e]
  intro ψ hctx s1 s2 hp E r hch
  subst hp
  obtain ⟨-, -, -, ⟨-, hker⟩, -⟩ := hctx.2
  have hF : Nat.card (GaloisField 2 (2 * 1)) = (2 ^ 1) ^ 2 :=
    card_galoisField_two_mul 2 1 le_rfl
  obtain ⟨h, hrh, hcov⟩ := ggRootInvol_exists_levi_PSU (k := 4) le_rfl (by norm_num) hker
    hch.rootInvolution
  obtain ⟨d, Q, e', j₁, j₂, hdD, hd1, hQ, hdX, hj, he12, he⟩ := ggSUSix_exists_d_frame hctx s1 rfl
  obtain ⟨g, hgr, hgι⟩ := OrthYSU.exists_conj_comm_root_levi (k := 4) hF ψ hQ hj he12 he hdX h
  have hgM : ψ g ∈ ggM 3 B x L D J :=
    Subgroup.le_normalizer (hctx.range_eq ▸ (⟨g, rfl⟩ : ψ g ∈ ψ.range))
  have hdC : Subgroup.centralizer {d} ≤ ggM 3 B x L D J := by
    intro z hz
    refine s1.2.1.mem_of_conj_mem hdD hd1 ?_
    have hzd : z * d = d * z := Subgroup.mem_centralizer_singleton_iff.mp hz
    have : z⁻¹ * d * z = d := by
      rw [mul_assoc, ← hzd, inv_mul_cancel_left]
    rw [this]
    exact s1.2.1.1 hdD
  have hd3 : orderOf d = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (hctx.d_elem.2 d hdD) hd1
  refine ⟨ψ g * d * (ψ g)⁻¹, ?_, ?_, centralizer_conj_le hdC hgM,
    (ψ.comp ((MulAut.conj h).toMonoidHom.comp
      (CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaHom (m := 4)))).range, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff, hrh]
    exact hgr
  · exact (SemiconjBy.orderOf_eq (ψ g) (inv_mul_cancel_right (ψ g * d) (ψ g)).symm).symm.trans hd3
  · rintro _ ⟨u, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hgι u).symm
  · rw [hctx.range_eq] at hcov
    exact hcov

end Inputs

end CFSG.StandardType
