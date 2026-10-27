module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructND
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoPSL
import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLRank
import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueRootPlaneA
import CFSG.LocalAnalysis.StandardType.GGRootPlaneOm
import CFSG.Open.StatedAPI
import CFSG.GroupTheory.ElemAbelianRank
import CFSG.LieType.SteinbergBRSemidirectSLEven
import CFSG.LieType.SteinbergBRSemidirectSL2

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

section Tags

theorem ggRootCentKGStructTag_PSL_of
    (hpieces : ∀ (m : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] (hm : 3 ≤ m),
      4 ≤ m ∨ 4 ≤ Nat.card K →
        KGND.KGPiecesD (AutPSL.inndiag : Subgroup (MulAut (projectiveSL (m + 1) K)))
          (KGPSL.rootInvPSL m K (by omega))) :
    GGRootCentKGStructTag .PSL := by
  intro G _ _ p n f ψ hp hp2 hadm hrank hker _ _ hC _ hBs r hr _ E hEN hEC hEip hEinn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hf : 1 ≤ f := hadm.2.1
  have hm2 : 2 ≤ m := hrank
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ (ψ : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G),
      ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) →
      Subgroup.centralizer (ψ.range : Set G) = ⊥ →
      (∃ Bs : Subgroup G, IsElemAbelian p Bs ∧ p ^ 4 ≤ Nat.card Bs ∧
        Bs ≤ Subgroup.normalizer (ψ.range : Set G) ∧
        ∀ b ∈ Bs, GGPsiInnerDiag (SpecialLinear.rootDatum m (GaloisField 2 f)) ψ b) →
      ∀ r : G, GGRootInvolution (SpecialLinear.rootDatum m (GaloisField 2 f)) .PSL ψ r →
      ∀ E : Subgroup G, E ≤ Subgroup.normalizer (ψ.range : Set G) →
        E ≤ Subgroup.centralizer {r} → IsPGroup p E →
        (∀ e ∈ E, GGPsiInnerDiag (SpecialLinear.rootDatum m (GaloisField 2 f)) ψ e) →
        ∃ 𝒥 : Set (Subgroup G),
          (∀ P : Subgroup G, P ≤ ψ.range ⊓ Subgroup.centralizer ({r} : Set G) → ⁅P, P⁆ = P →
            P ≤ sSup 𝒥) ∧
          ∀ J ∈ 𝒥, GGRCSKGPiece (ψ.range ⊓ Subgroup.centralizer ({r} : Set G)) E J := by
    intro ψ hker hC hBs r hr E _ hEC _ hEinn
    rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
    ·
      exfalso
      obtain ⟨Bs, hBsE, hcard, hBsN, hBsI⟩ := hBs
      exact AutPSL.pslThreeRankInput_holds G f ψ hf hker hC p Bs hp hp2 hBsE hcard hBsN hBsI
    ·
      have hmain : 4 ≤ m ∨ 4 ≤ Nat.card (GaloisField 2 f) → ∃ 𝒥 : Set (Subgroup G),
          (∀ P : Subgroup G, P ≤ ψ.range ⊓ Subgroup.centralizer ({r} : Set G) → ⁅P, P⁆ = P →
            P ≤ sSup 𝒥) ∧
          ∀ J ∈ 𝒥, GGRCSKGPiece (ψ.range ⊓ Subgroup.centralizer ({r} : Set G)) E J := by
        intro hbig
        obtain ⟨w, hw⟩ := AutPSL.exists_conj_rootInv_of_rootInvolution (K := GaloisField 2 f)
          (m := m) (G := G) (ψ := ψ) (r := r) (by omega) hr
        set Θ : projectiveSL (m + 1) (GaloisField 2 f) ≃* ψ.range :=
          AutPSL.projEquiv (K := GaloisField 2 f) (m := m) hker hC with hΘ
        set ψ' : projectiveSL (m + 1) (GaloisField 2 f) →* G :=
          ψ.range.subtype.comp Θ.toMonoidHom with hψ'
        set w' : projectiveSL (m + 1) (GaloisField 2 f) := proj (m + 1) (GaloisField 2 f) w
          with hw'
        set z : projectiveSL (m + 1) (GaloisField 2 f) :=
          KGPSL.rootInvPSL m (GaloisField 2 f) (by omega) with hz
        have hψ'range : ψ'.range = ψ.range := by
          rw [hψ', MonoidHom.range_comp]
          have h : Θ.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr Θ.surjective
          rw [h, Subgroup.map_top, Subgroup.range_subtype]
        have hψ'inj : Function.Injective ψ' := by
          intro x y h
          exact Θ.injective (Subtype.ext h)
        have hψ'proj : ∀ v : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f),
            ψ' (proj (m + 1) (GaloisField 2 f) v) = ψ v := by
          intro v
          rw [hψ', hΘ]
          exact AutPSL.projEquiv_proj hker hC v
        have hΘw : (Θ w' : G) = ψ w := by
          rw [hw', hΘ]
          exact AutPSL.projEquiv_proj hker hC w
        have hΘr : (Θ z : G) = ψ (AutPSL.rootInv (by omega)) := by
          rw [hz, hΘ]
          exact AutPSL.projEquiv_proj hker hC (AutPSL.rootInv (by omega))
        have hβz : ψ' ((MulAut.conj w') z) = r := by
          show ψ' (w' * z * w'⁻¹) = r
          have e1 : ψ' (w' * z * w'⁻¹) =
              (Θ w' : G) * (Θ z : G) * (Θ w' : G)⁻¹ := by
            simp only [hψ', MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, map_inv]
            rfl
          rw [e1, hΘw, hΘr, ← hw]
        have hβ : (MulAut.conj w') ∈ (AutPSL.inndiag :
            Subgroup (MulAut (projectiveSL (m + 1) (GaloisField 2 f)))) :=
          AutPSL.inn_le_inndiag ⟨w', rfl⟩
        have hDz : KGND.KGPiecesD (AutPSL.inndiag :
            Subgroup (MulAut (projectiveSL (m + 1) (GaloisField 2 f))))
            ((MulAut.conj w') z) :=
          KGND.KGPiecesD.map_of_mem (hpieces m (GaloisField 2 f) hm3 hbig) hβ
        have hact : ∀ ε ∈ E, ∃ δ ∈ (AutPSL.inndiag :
            Subgroup (MulAut (projectiveSL (m + 1) (GaloisField 2 f)))),
            ∀ u : projectiveSL (m + 1) (GaloisField 2 f), ε⁻¹ * ψ' u * ε = ψ' (δ u) := by
          intro ε hε
          obtain ⟨A, hA⟩ :=
            RootPlaneA.exists_gl_of_psiInnerDiag (m := m) (by omega) hker (hEinn ε hε)
          refine ⟨conjAut (m + 1) (GaloisField 2 f) A, ⟨A, rfl⟩, fun u => ?_⟩
          obtain ⟨u₀, rfl⟩ := proj_surjective (m + 1) (GaloisField 2 f) u
          have hconj : conjAut (m + 1) (GaloisField 2 f) A
              (proj (m + 1) (GaloisField 2 f) u₀) =
              proj (m + 1) (GaloisField 2 f) (InnerDiagA.conjSL A u₀) := by
            rw [conjAut_proj]
            congr 1
            apply SpecialLinearGroup.toGL_injective
            rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
              RootPlaneA.toGL_conjSL]
          rw [hψ'proj u₀, hconj, hψ'proj (InnerDiagA.conjSL A u₀), hA u₀]
        have hEsub : E ≤ Subgroup.centralizer ({ψ' ((MulAut.conj w') z)} : Set G) := by
          rw [hβz]
          exact hEC
        obtain ⟨𝒥, hcover, hpiece⟩ := hDz G ψ' hψ'inj E hEsub hact
        have hC₀ : ψ.range ⊓ Subgroup.centralizer ({r} : Set G) =
            ψ'.range ⊓ Subgroup.centralizer ({ψ' ((MulAut.conj w') z)} : Set G) := by
          rw [hψ'range, hβz]
        refine ⟨𝒥, ?_, ?_⟩
        · intro P hP hPperf
          rw [hC₀] at hP
          exact hcover P hP hPperf
        · intro J hJ
          rw [hC₀]
          exact hpiece J hJ
      rcases (show m = 3 ∨ 4 ≤ m by omega) with hm3' | hm4
      · rcases (show f = 1 ∨ 2 ≤ f by omega) with hf1 | hf2
        ·
          subst hf1
          subst hm3'
          exfalso
          obtain ⟨Bs, hBsE, hcard, hBsN, hBsI⟩ := hBs
          have hcenter : Subgroup.center (SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 1)) =
              ⊥ :=
            CFSG.LieType.SteinbergBR.center_SL_eq_bot_of_charTwo (m := 3 + 1) (by norm_num)
              (Or.inr (by rw [GaloisField.card 2 1 (by norm_num)]; norm_num))
          have hψinj : Function.Injective ψ := by
            rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
            exact hker.trans hcenter.le
          have hBsψ : Bs ≤ ψ.range := by
            refine bstar_le_range_of_inner hC fun b hb => ?_
            obtain ⟨A, hA⟩ :=
              RootPlaneA.exists_gl_of_psiInnerDiag (m := 3) (by norm_num) hker (hBsI b hb)
            have hdet1 : (A : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (GaloisField 2 1)).det = 1 := by
              have hcardu : Nat.card (Units (GaloisField 2 1)) = 1 := by
                rw [Nat.card_units, GaloisField.card 2 1 (by norm_num)]
                norm_num
              haveI : Subsingleton (Units (GaloisField 2 1)) :=
                (Nat.card_eq_one_iff_unique.mp hcardu).1
              have hdet : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
              rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet]
              rfl
            set s : SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 1) :=
              ⟨(A : Matrix (Fin (3 + 1)) (Fin (3 + 1)) (GaloisField 2 1)), hdet1⟩ with hs
            have htoGL : SpecialLinearGroup.toGL s = A := by
              rw [hs]
              exact Units.ext rfl
            have hconj : ∀ u : SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 1),
                ψ (InnerDiagA.conjSL A u) = ψ s * ψ u * (ψ s)⁻¹ := by
              intro u
              rw [show ψ s * ψ u * (ψ s)⁻¹ = ψ (s * u * s⁻¹) by
                simp only [map_mul, map_inv]]
              congr 1
              apply SpecialLinearGroup.toGL_injective
              simp only [RootPlaneA.toGL_conjSL, map_mul, map_inv, htoGL]
            refine ⟨ψ s, ⟨s, rfl⟩, ?_⟩
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            obtain ⟨u, rfl⟩ := hy
            have h1 : ψ u = (b * ψ s) * ψ u * (b * ψ s)⁻¹ := by
              calc ψ u = b * (b⁻¹ * ψ u * b) * b⁻¹ := by group
                _ = b * ψ (InnerDiagA.conjSL A u) * b⁻¹ := by rw [hA u]
                _ = b * (ψ s * ψ u * (ψ s)⁻¹) * b⁻¹ := by rw [hconj u]
                _ = (b * ψ s) * ψ u * (b * ψ s)⁻¹ := by group
            calc ψ u * (b * ψ s) = ((b * ψ s) * ψ u * (b * ψ s)⁻¹) * (b * ψ s) := by
                  conv_lhs => rw [h1]
              _ = (b * ψ s) * ψ u := by group
          have hpow : p ^ 4 ∣ Nat.card Bs := by
            have hcardBs :=
              CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian (G := G) hp hBsE
            rw [hcardBs]
            refine Nat.pow_dvd_pow p ?_
            have hle : p ^ 4 ≤ p ^ CFSG.Open.pRank p Bs := by rw [← hcardBs]; exact hcard
            exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
          have hBdvd : Nat.card Bs ∣ Nat.card ψ.range := Subgroup.card_dvd_of_le hBsψ
          have hUeq : Nat.card ψ.range =
              Nat.card (SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 1)) :=
            (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
          have h20160 : Nat.card (SpecialLinearGroup (Fin (3 + 1)) (GaloisField 2 1)) =
              20160 := by
            rw [← CFSG.Open.StatedAPI.card_statedSL (3 + 1) (GaloisField 2 1)]
            exact CFSG.Open.StatedAPI.card_statedSL_four_of_card_eq_two
              (by rw [GaloisField.card 2 1 (by norm_num)]; norm_num)
          have hdvd : p ^ 4 ∣ 20160 := by
            rw [← h20160, ← hUeq]
            exact hpow.trans hBdvd
          have hp3 : 3 ≤ p := by have := hp.two_le; omega
          have hle : p ^ 4 ≤ 20160 := Nat.le_of_dvd (by norm_num) hdvd
          have hp11 : p ≤ 11 := by
            by_contra h
            have h12 : 12 ≤ p := by omega
            have hgt : 12 ^ 4 ≤ p ^ 4 := Nat.pow_le_pow_left h12 4
            norm_num at hgt
            omega
          interval_cases p <;> norm_num at hdvd
        · subst hm3'
          exact hmain (Or.inr (by
            have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
            rw [hK]
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2))
      · exact hmain (Or.inl hm4)
  exact key ψ hker hC hBs r hr E hEN hEC hEip hEinn

end Tags

end CFSG.StandardType

end
