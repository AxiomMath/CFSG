module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMPrimeCTorus
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMPrimeCAssemble

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

theorem qTwoLMSkel_prime_thetaT {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    {m : ℕ} (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 5 ≤ m) (h3 : ¬ 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) (hMul : PSUTrivialMultiplier m) :
    ∃ ΘT : ↥(sumZero m 3) ≃* ↥(Bs ⊓ L),
      (∀ n : ↥L, (n : G) ∈ Subgroup.normalizer (Bs : Set G) →
        ∃ π : Equiv.Perm (Fin m), ∀ v : ↥(sumZero m 3),
          (n : G) * ((ΘT v : ↥(Bs ⊓ L)) : G) * (n : G)⁻¹ =
            ((ΘT (permAutVHom m 3 π v) : ↥(Bs ⊓ L)) : G)) ∧
      (∀ σ : Equiv.Perm (Fin m), ∃ n : ↥L,
        (n : G) ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ v : ↥(sumZero m 3),
          (n : G) * ((ΘT v : ↥(Bs ⊓ L)) : G) * (n : G)⁻¹ =
            ((ΘT (permAutVHom m 3 σ v) : ↥(Bs ⊓ L)) : G)) := by
  have hxBs : x ∈ Bs := hBs.1 hG.2.2.2.2.2.2.1.2.1
  obtain ⟨R, _, eL, hTSC⟩ := qTwoLMPrimeC_model hG h3 hL hMul
  obtain ⟨hE1, hE2, hE3⟩ := qTwoLMPrimeC_imgT_props eL (qTwoLMPrimeC_elemAbelian_T hBs)
    (qTwoLMPrimeC_card_T_ge hG hBs hN h3 hL hMul) (qTwoLMPrimeC_selfcent hG hBs hN h3 hL hMul)
  obtain ⟨τ, hτinj, hτrange, hperm, hnorm⟩ := hTSC _ hE1 hE2 hE3
  exact qTwoLMPrimeC_assemble eL hxBs (qTwoLMFrameC_le_centralizer hG)
    (qTwoLMPrimeC_split hG hBs hN h3 hL hMul) τ hτinj hτrange hperm hnorm

end CFSG.StandardType.QTwo

end
