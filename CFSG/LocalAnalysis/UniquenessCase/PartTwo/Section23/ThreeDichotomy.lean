module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeWeakClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ThreeTI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEighteenGen
public import CFSG.LocalAnalysis.WeakClosure81.NineStep3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11RouteFX
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.W3Lem45Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin
  CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.WeakClosure81 Subgroup
open CFSG.CGT.Timmesfeld75 (conjSubgroup)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {Ch : Choice2011 G}

private theorem one_lt_rk_U (c : Ctx23L D Ch)
    (hU0 : c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z) (hlt : c.U0 < D.U) :
    1 < rk ↥D.U := by
  have h4 : 4 ≤ Nat.card D.U := four_le_card_U c hU0 hlt
  have hV : IsElemAbelian 2 D.U := (uc22p22e_inCalV_U D).2.2.2
  have hcard : Nat.card D.U = 2 ^ rk ↥D.U :=
    card_eq_two_pow_of_isPGroup (uc22p22e_isPGroup_of_elem hV)
  have hge : 4 ≤ 2 ^ rk ↥D.U := by rw [← hcard]; exact h4
  by_contra hle
  have hle' : rk ↥D.U ≤ 1 := by omega
  have htop : 2 ^ rk ↥D.U ≤ 2 := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hle'
  omega

private theorem not_le_sup_centralizer_of_commutator_ne_bot {X : Subgroup G}
    (hTX : D.T ≤ X) (hC : ⁅E3.cClos D.U 1 D.T, twoResidual X⁆ ≠ ⊥) :
    ¬ X ≤ (X ⊓ Subgroup.centralizer (E3.cClos D.U 1 D.T : Set G)) ⊔ D.T := by
  intro hX
  have hSJ : D.T ≤ Subgroup.normalizer
      ((X ⊓ Subgroup.centralizer (E3.cClos D.U 1 D.T : Set G) : Subgroup G) : Set G) := by
    refine CFSG.Quasithin.A1a.le_normalizer_inf (hTX.trans Subgroup.le_normalizer) ?_
    exact CFSG.Quasithin.A1a.le_normalizer_centralizer
      (Subgroup.le_normalizer.trans
        (E3.normalizer_le_normalizer_cClos (V := D.U) (i := 1) D.T))
  have hO2X : twoResidual X ≤ X ⊓ Subgroup.centralizer (E3.cClos D.U 1 D.T : Set G) :=
    CFSG.Quasithin.RonanE111.twoResidual_le_of_le_sup_two hSJ D.sylowM.isPGroup hX
  apply hC
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hO2X.trans inf_le_right)

private theorem cClos_le_cClos_inf_of_isE' {X K A : Subgroup G}
    (hV : IsElemAbelian 2 D.U) (h1 : 1 < rk ↥D.U) (hTX : D.T ≤ X)
    (hA : A ∈ E3.gammaSet D.U 0 D.T) (hK : E1.IsE 1 X D.T A K) :
    E3.cClos D.U 1 D.T ≤ E3.cClos D.U 1 (D.T ⊓ K) := by
  obtain ⟨hAT, g, hAg, hmg⟩ := hA
  have hVg : IsPGroup 2 (conjSubgroup D.U g) := (uc22p22e_isPGroup_of_elem hV).map _
  have hAeq : A = conjSubgroup D.U g := (E3.mQuot_eq_zero_iff hVg hAg).mp hmg
  subst hAeq
  have hA_le_W : conjSubgroup D.U g ≤ E3.wClos D.U 1 D.T := by
    refine E3.le_wClos_of_mQuot_le hV g hAT le_rfl ?_ h1
    rw [E3.mQuot_self]
    norm_num
  have hcS : E3.cClos D.U 1 D.T ≤
      D.T ⊓ Subgroup.centralizer (conjSubgroup D.U g : Set G) := by
    rw [E3.cClos]
    exact inf_le_inf_left D.T (Subgroup.centralizer_le (fun x hx => hA_le_W hx))
  have hCtau : D.T ⊓ Subgroup.centralizer (conjSubgroup D.U g : Set G) ≤
      E1.tauOf X D.T (conjSubgroup D.U g) := by
    intro t ht
    obtain ⟨htT, htC⟩ := ht
    refine (E1.mem_tauOf_of_le hTX).mpr ⟨htT, fun a ha => ?_⟩
    have hcomm : a * t = t * a := Subgroup.mem_centralizer_iff.mp htC a ha
    rw [commutatorElement_def, ← hcomm]
    simp
  have hle1 : E3.cClos D.U 1 D.T ≤ D.T ⊓ K := (hcS.trans hCtau).trans hK.2.1
  have hWmono : E3.wClos D.U 1 (D.T ⊓ K) ≤ E3.wClos D.U 1 D.T :=
    E3.wClos_mono inf_le_left
  have hle2 : E3.cClos D.U 1 D.T ≤
      Subgroup.centralizer (E3.wClos D.U 1 (D.T ⊓ K) : Set G) := by
    rw [E3.cClos]
    exact inf_le_right.trans (Subgroup.centralizer_le (fun x hx => hWmono hx))
  rw [E3.cClos]
  exact le_inf hle1 hle2

private theorem twoResidual_commutator_cClos_inf_ne_bot {X K A : Subgroup G}
    (hV : IsElemAbelian 2 D.U) (h1 : 1 < rk ↥D.U) (hTX : D.T ≤ X)
    (hA : A ∈ E3.gammaSet D.U 0 D.T) (hK : E1.IsE 1 X D.T A K)
    (hne : ⁅twoResidual K, E3.cClos D.U 1 D.T⁆ ≠ ⊥) :
    ⁅twoResidual K, E3.cClos D.U 1 (D.T ⊓ K)⁆ ≠ ⊥ := by
  have hle : E3.cClos D.U 1 D.T ≤ E3.cClos D.U 1 (D.T ⊓ K) :=
    cClos_le_cClos_inf_of_isE' hV h1 hTX hA hK
  intro h0
  have hle' : ⁅twoResidual K, E3.cClos D.U 1 D.T⁆ ≤
      ⁅twoResidual K, E3.cClos D.U 1 (D.T ⊓ K)⁆ := Subgroup.commutator_mono le_rfl hle
  rw [h0] at hle'
  exact hne (le_bot_iff.mp hle')

private theorem twoResidual_commutator_cClos_ne_bot_of_not_le_sup {X K A : Subgroup G}
    (hK : E1.IsE 1 X D.T A K)
    (hKM : ¬ K ≤ (X ⊓ Subgroup.centralizer (E3.cClos D.U 1 D.T : Set G)) ⊔ D.T) :
    ⁅twoResidual K, E3.cClos D.U 1 D.T⁆ ≠ ⊥ := by
  intro h0
  apply hKM
  have hO2K : twoResidual K ≤
      X ⊓ Subgroup.centralizer (E3.cClos D.U 1 D.T : Set G) := by
    refine le_inf ((CFSG.Quasithin.twoResidual_le K).trans hK.1) ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h0
  rw [← CFSG.Quasithin.sup_twoResidual_eq hK.2.2.1]
  exact sup_le (inf_le_left.trans le_sup_right) (hO2K.trans le_sup_left)

private theorem exists_inCalO2_of_isE_not_le (c : Ctx23L D Ch)
    (hU0 : c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z) (hlt : c.U0 < D.U)
    {X K A : Subgroup G} (hTX : D.T ≤ X) (hA : A ∈ E3.gammaSet D.U 0 D.T)
    (hK : E1.IsE 1 X D.T A K)
    (hKM : ¬ K ≤ (X ⊓ Subgroup.centralizer (E3.cClos D.U 1 D.T : Set G)) ⊔ D.T) :
    ∃ g : G, InCalO2 1 D.M ⊥ D.U g := by
  have hV : IsElemAbelian 2 D.U := (uc22p22e_inCalV_U D).2.2.2
  have h1 : 1 < rk ↥D.U := one_lt_rk_U c hU0 hlt
  have hS : IsSylowIn 2 D.T X := TwelveShort.isSylowIn_of_le D hTX
  have hne0 := twoResidual_commutator_cClos_ne_bot_of_not_le_sup hK hKM
  have hAab : IsElemAbelian 2 A := (E3.isInvColl_gammaSet hV 0 D.T).isElemAbelian A hA
  have hAK : A ≤ K :=
    (le_sup_left.trans (CFSG.Quasithin.E1.le_tauOf hS hA.1 hAab)).trans
      (hK.2.1.trans inf_le_right)
  have hAgamma : A ∈ E3.gammaSet D.U 0 (D.T ⊓ K) :=
    ⟨le_inf hA.1 hAK, hA.2⟩
  have hKself : E1.IsE 1 K (D.T ⊓ K) A K := CFSG.LocalAnalysis.WeakClosure81.isE_self hK
  have hneK := twoResidual_commutator_cClos_inf_ne_bot hV h1 hTX hA hK hne0
  obtain ⟨H', S', A', hS', hK', hAg', hAV', hAne', hne'⟩ :=
    conj_reduction (n := 1) hK.2.2.1 hAgamma hKself hneK
  have hparam : E3.rParam D.U = (rk ↥D.U : ℕ∞) := by
    rw [← rMV_eq_rParam_of_inCalV D (uc22p22e_inCalV_U D), Ctx23.rMV_eq_rk_of_TI c.toCtx23]
  have hr : (1 : ℕ∞) < E3.rParam D.U := hparam ▸ ENat.natCast_lt_natCast.mpr h1
  have hbeta : (1 : ℕ∞) < betaN 0 D.M D.U := by
    rw [Ctx23.betaN_eq_top_of_TI c.toCtx23]
    exact ENat.natCast_lt_top 1
  have hMV := uc22p22e_inCalV_U D
  obtain ⟨g, -, hg⟩ := six_nine_two_core (M := D.M) (V := D.U) (H := H') (S := S') (A := A')
    hV hMV.2.2.1 (normalizer_eq_of_inCalV D hMV) hS' (by norm_num : 1 = 1 + 0)
    hAg' hAV' hAne' hK' h1 hr hne' hbeta
  exact ⟨g, hg⟩

private theorem exists_inCalO2_of_not_le_normalizer (c : Ctx23L D Ch)
    (hU0 : c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z) (hlt : c.U0 < D.U)
    {X : Subgroup G} (hTX : D.T ≤ X) (_hXM : X ≤ D.M) (hF : InFSq 1 X)
    (hN : ¬ X ≤ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G))
    (hC : ⁅E3.cClos D.U 1 D.T, twoResidual X⁆ ≠ ⊥) :
    ∃ g : G, InCalO2 1 D.M ⊥ D.U g := by
  have hV : IsElemAbelian 2 D.U := (uc22p22e_inCalV_U D).2.2.2
  have hS : IsSylowIn 2 D.T X := TwelveShort.isSylowIn_of_le D hTX
  obtain ⟨A, hA, hAne⟩ := TwelveEighteen.exists_gammaSet_not_le_pCoreOf hS hN
  have hHM : ¬ X ≤ (X ⊓ Subgroup.centralizer (E3.cClos D.U 1 D.T : Set G)) ⊔ D.T :=
    not_le_sup_centralizer_of_commutator_ne_bot hTX hC
  obtain ⟨A, hA, hAne, K, hK, hKM⟩ :=
    exists_isE_not_le_of_inF2 (V := D.U) hV hS hF le_sup_right hHM ⟨A, hA, hAne⟩
  exact exists_inCalO2_of_isE_not_le c hU0 hlt hTX hA hK hKM

theorem dich_U (c : Ctx23L D Ch)
    (hU0 : c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z) (hlt : c.U0 < D.U)
    {X : Subgroup G} (hTX : D.T ≤ X) (hXM : X ≤ D.M) (hF : InFSq 1 X) :
    X ≤ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G) ∨
      ⁅E3.cClos D.U 1 D.T, twoResidual X⁆ = ⊥ ∨
        ∃ g : G, InCalO2 1 D.M ⊥ D.U g := by
  by_cases hN : X ≤ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G)
  · exact Or.inl hN
  by_cases hC : ⁅E3.cClos D.U 1 D.T, twoResidual X⁆ = ⊥
  · exact Or.inr (Or.inl hC)
  exact Or.inr (Or.inr
    (exists_inCalO2_of_not_le_normalizer c hU0 hlt hTX hXM hF hN hC))

theorem eq_mul_U (c : Ctx23L D Ch)
    (hU0 : c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z) (hlt : c.U0 < D.U)
    {X : Subgroup G} (hTX : D.T ≤ X) (hXM : X ≤ D.M) (hF : InFSq 1 X) :
    (X : Set G) = ((X ⊓ Subgroup.centralizer (E3.cClos D.U 1 D.T : Set G) : Subgroup G) : Set G) *
      ((X ⊓ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G) : Subgroup G) : Set G) ∨
      ∃ g : G, InCalO2 1 D.M ⊥ D.U g := by
  rcases dich_U c hU0 hlt hTX hXM hF with hN | hC | hO
  · left
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      exact ⟨1, ⟨one_mem _, one_mem _⟩, x, ⟨hx, hN hx⟩, one_mul x⟩
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact X.mul_mem ha.1 hb.1
  · left
    rw [Subgroup.commutator_comm] at hC
    have hRC := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hC
    have hS : IsSylowIn 2 D.T X := TwelveShort.isSylowIn_of_le D hTX
    have hSN : D.T ≤ Subgroup.normalizer (twoResidual X : Set G) :=
      hTX.trans (CFSG.Quasithin.le_normalizer_twoResidual X)
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      have hx' : x ∈ ((twoResidual X ⊔ D.T : Subgroup G) : Set G) := by
        rw [sup_comm, CFSG.Quasithin.sup_twoResidual_eq hS]
        exact hx
      rw [Subgroup.coe_mul_of_right_le_normalizer_left (twoResidual X) D.T hSN] at hx'
      obtain ⟨r, hr, s, hs, rfl⟩ := hx'
      exact ⟨r, ⟨CFSG.Quasithin.twoResidual_le X hr, hRC hr⟩, s,
        ⟨hTX hs, E3.normalizer_le_normalizer_wClos (V := D.U) (i := 0) D.T
          (Subgroup.le_normalizer hs)⟩, rfl⟩
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact X.mul_mem ha.1 hb.1
  · exact Or.inr hO

theorem eq_mul_U_of_isSolvable (c : Ctx23L D Ch)
    (hU0 : c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z) (hlt : c.U0 < D.U)
    {X : Subgroup G} (hTX : D.T ≤ X) (hX : Group.IsSolvable ↥X) :
    (X : Set G) = ((X ⊓ Subgroup.centralizer (E3.cClos D.U 1 D.T : Set G) : Subgroup G) : Set G) *
      ((X ⊓ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G) : Subgroup G) : Set G) ∨
      ∃ g : G, InCalO2 1 D.M ⊥ D.U g := by
  have hS : IsSylowIn 2 D.T X := TwelveShort.isSylowIn_of_le D hTX
  have hV : IsElemAbelian 2 D.U := (uc22p22e_inCalV_U D).2.2.2
  have h45 := w3Lem45_2_holds G X D.T 1 (E3.gammaSet D.U 0 X) le_rfl hS
    (E3.isInvColl_gammaSet hV 0 X)
    (s16c11_compFactorAutInF_of_isSolvable 1 (H := X) (S := D.T) hX)
  rw [E3.weakClosure_gammaSet hS.le] at h45
  by_cases h : ∀ A ∈ E3.gammaSet D.U 0 D.T, ∀ K, E1.IsE 1 X D.T A K →
      K ≤ (X ⊓ Subgroup.centralizer (E3.cClos D.U 1 D.T : Set G)) ⊔ D.T
  · left
    have hE : E1.eGen 1 X D.T (E3.gammaSet D.U 0 X) ≤
        (X ⊓ Subgroup.centralizer (E3.cClos D.U 1 D.T : Set G)) ⊔ D.T := by
      refine iSup₂_le fun A hA => iSup_le fun hAS => iSup₂_le fun K hK => ?_
      exact h A ⟨hAS, hA.2⟩ K hK
    have hSN : D.T ≤ X ⊓ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G) :=
      fun s hs => ⟨hTX hs, (Subgroup.le_normalizer.trans
        (E3.normalizer_le_normalizer_wClos (V := D.U) (i := 0) D.T)) hs⟩
    have hSC : D.T ≤ Subgroup.normalizer
        ((X ⊓ Subgroup.centralizer (E3.cClos D.U 1 D.T : Set G) : Subgroup G) : Set G) :=
      CFSG.Quasithin.A1a.le_normalizer_inf (hTX.trans Subgroup.le_normalizer)
        (CFSG.Quasithin.A1a.le_normalizer_centralizer
          (Subgroup.le_normalizer.trans
            (E3.normalizer_le_normalizer_cClos (V := D.U) (i := 1) D.T)))
    exact TwelveShort.eq_mul_of_le_sup (H := X) (S := D.T)
      (C := X ⊓ Subgroup.centralizer (E3.cClos D.U 1 D.T : Set G))
      (N := X ⊓ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G))
      (E := E1.eGen 1 X D.T (E3.gammaSet D.U 0 X)) inf_le_left inf_le_left hSN hSC hE h45
  · right
    push Not at h
    obtain ⟨A, hA, K, hK, hKM⟩ := h
    exact exists_inCalO2_of_isE_not_le c hU0 hlt hTX hA hK hKM

theorem eq_mul_U_of_or (c : Ctx23L D Ch)
    (hU0 : c.U0 = conjClosure (c.L0 ⊓ D.M) D.Z) (hlt : c.U0 < D.U)
    {X : Subgroup G} (hTX : D.T ≤ X) (hXM : X ≤ D.M)
    (hF : InFSq 1 X ∨ Group.IsSolvable ↥X) :
    (X : Set G) = ((X ⊓ Subgroup.centralizer (E3.cClos D.U 1 D.T : Set G) : Subgroup G) : Set G) *
      ((X ⊓ Subgroup.normalizer (E3.wClos D.U 0 D.T : Set G) : Subgroup G) : Set G) ∨
      ∃ g : G, InCalO2 1 D.M ⊥ D.U g := by
  rcases hF with hF | hF
  · exact eq_mul_U c hU0 hlt hTX hXM hF
  · exact eq_mul_U_of_isSolvable c hU0 hlt hTX hF

end CFSG.LocalAnalysis.UniquenessCase.UC22
