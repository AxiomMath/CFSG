module

public import CFSG.Quasithin.Vol2.Ch11SecB36Fin2
public import CFSG.Quasithin.Background.C1PackC127Act
public import CFSG.Quasithin.Vol2.Ch10SecEL0

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem false_of_VH (hFV : FactsVM) (hFL : FactsL2) (hG16 : ASInputs.AS_G_1_6)
    (h331 : Stmt3_3_1) (hyp : Hyp11 G T L I n) {V₁ V₂ H K : Subgroup G}
    (h31 : Hyp11_3_1 T L I n V₁ H) (hfl : Flag36 L (fsuV T I) (VM T L I) ⊤ T V₁ V₂ n)
    (hs : E3.sParam hfl.elemW = 2 * n)
    (hrlt : ((2 * n : ℕ) : ℕ∞) < E3.rParam (VM T L I))
    (hW0 : ¬ E3.wClos (VM T L I) 0 T ≤ pCoreOf 2 H) (hKO : K = oTwoUpper H)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ (2 * n))
    (eK : ↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := hfl.two_le
  have hW := hfl.elemW
  have hTH : QuasithinUnique.IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow h31.hstar.1.1
  have hVR := conjClosure_isTwoReducedIn_of_charTwo hTH
    (charTwo_of_inH hyp.fsu.qtke.2.1 (hyp.fsu.sylow.1.toSylow hyp.fsu.sylow.2) h31.hstar.1)
    (le_rfl : quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter T)
  have hVHel : IsElemAbelian 2 (VZ T H) := hVR.2.1
  have hR : IsTwoReducedIn H (VZ T H) := hVR.2.2
  have hHVH : H ≤ Subgroup.normalizer (VZ T H : Set G) := hR.2.1
  have hKdef : K = twoResidual H := by rw [hKO, Ch10.SecE.twoResidual_eq_oTwoUpper]
  have hKH : K ≤ H := hKO ▸ oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := hKO ▸ le_normalizer_oTwoUpper H
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := h31.hstar.1.1.trans hHK
  have hHKT : K ⊔ T = H := by
    rw [hKdef, sup_comm]
    exact sup_twoResidual_eq hTH
  have hKN : K ≤ Subgroup.normalizer (VZ T H : Set G) := hKH.trans hHVH
  have hKC : ¬ K ≤ Subgroup.centralizer (VZ T H : Set G) := fun h =>
    twoResidual_not_le_centralizer hyp h31 (hKdef ▸ h)
  obtain ⟨g, hBT, hBO⟩ : ∃ g : G, conjSubgroup (VM T L I) g ≤ T ∧
      ¬ conjSubgroup (VM T L I) g ≤ pCoreOf 2 H := by
    by_contra hall
    push Not at hall
    apply hW0
    refine iSup₂_le fun A hA => ?_
    obtain ⟨hAT, g, hAg, hA0⟩ := hA
    have hAeq : A = conjSubgroup (VM T L I) g := (E3.mQuot_eq_zero_iff
      (E3.isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hW) g) hAg).mp hA0
    subst hAeq
    exact hall g hAT
  have hBN : conjSubgroup (VM T L I) g ≤ Subgroup.normalizer (VZ T H : Set G) :=
    (hBT.trans h31.hstar.1.1).trans hHVH
  have hBC : ¬ conjSubgroup (VM T L I) g ≤ Subgroup.centralizer (VZ T H : Set G) := fun h =>
    hBO ((le_inf hBT h).trans (inf_centralizer_VZ_le h331 hyp h31))
  have haS := autI_mem_aSet hW hVHel (hBT.trans h31.hstar.1.1) hHVH hBC
  rw [hs] at haS
  obtain ⟨eG⟩ := autI_equiv_SL2 hVHel hR hKH hHK (by omega : 2 ≤ 2 * n) hF eK hKC
  have hGm : ∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = 2 ^ (2 * n) ∧
      Nonempty (↥(autI hVHel K) ≃* Matrix.SpecialLinearGroup (Fin 2) F') :=
    ⟨F, inferInstance, inferInstance, hF, ⟨eG⟩⟩
  obtain ⟨-, hBS, hBcard⟩ := hFL.offender (IntMod (VZ T H) hVHel) IntMod.sq_eq_one
    (autI hVHel H) (autI hVHel K) (autI hVHel T) (2 * n) (by omega) hGm
    (B6.isPGroup_autOn hyp.fsu.sylow.1 (VZ T H)) (autI_le_normalizer_autI hVHel hTK)
    (by rw [← autI_sup hVHel hKN (h31.hstar.1.1.trans hHVH), hHKT])
    (C1Pack.pCoreOf_autI_eq_bot hVHel hR) _ haS
  have hBm : E3.mQuot (conjSubgroup (VM T L I) g)
      (conjSubgroup (VM T L I) g ⊓ Subgroup.centralizer (VZ T H : Set G)) = 2 * n := by
    unfold E3.mQuot
    rw [← card_autI_eq hVHel hBN, hBcard, padicValNat.prime_pow]
  have hVHB : VZ T H ≤ Subgroup.normalizer (conjSubgroup (VM T L I) g : Set G) := by
    have hC := centralizer_le_normalizer_of_lt (V := VM T L I)
      (B := conjSubgroup (VM T L I) g ⊓ Subgroup.centralizer (VZ T H : Set G)) (g := g)
      inf_le_left (by rw [hBm]; exact hrlt)
    refine le_trans (fun v hv => ?_) hC
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp hx.2 v hv).symm
  exact false_of_VH_two hFV hFL hG16 hfl hVHel hKN hKC hHKT hTK hBT hBN haS hBS hBcard hBm
    hVHB hGm

end CFSG.Quasithin.Vol2.Ch11.SecB
