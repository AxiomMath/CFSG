module

public import CFSG.RankThree.PartTwo.Sec4.Item424ProofKFacts
import CFSG.RankThree.PartTwo.Sec4.Item424Res6ProofTools
import CFSG.RankThree.PartTwo.Sec4.Item424Res6ProofCross
import CFSG.RankThree.PartTwo.Sec4.Item424Res6ProofSolv
import CFSG.RankThree.PartTwo.Sec4.Item424Res6ProofFrame
import CFSG.RankThree.PartTwo.Sec4.Item424Res6ProofSL
import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofLTypeThree
public import CFSG.RankThree.PartTwo.Sec13.Item131Transport

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Res423Four Sec21.Item211Proof Res424Six

section Main


theorem k424SLThree_of (h45 : Item4_5) : K424SLThree := by
  intro G _ _ A L a c K h hany hkind
  have hAL := h.le_normalizer h45
  have hA : IsPGroup 3 A := h.isPGroup
  have hCA := h.inf_thetaQuotCentralizer hAL
  have hLsn : L.IsSubnormal := h.mem_thetaComponents.2.1
  obtain ⟨Φ₀, hΦ₀⟩ := exists_lEquiv hAL
  have hL₁n : (lOne L A).Normal := normal_lOne hAL
  have hLq : IsQuasisimple (lOne L A) :=
    LocalCores.isQuasisimple_of_mulEquiv Φ₀ h.isQuasisimple_L
  have : Group.IsPerfect (lOne L A) := hLq.1
  have hmax : Maximal (fun B : Subgroup (QuotX L A) => CFSG.Assembly.IsElemAbelian 3 B)
      (aOne L A) :=
    maximal_aOne h.isElemAbelian (fun B hB hAB => h.maximal.eq_of_ge hB hAB)
  have hA27 : Nat.card (aOne L A) = 27 := by
    rw [← Nat.card_congr (aEquiv (L := L) hA).toEquiv, h.card_eq]
  have hA3₁ : ∀ x ∈ aOne L A, x ^ 3 = 1 := hmax.prop.2
  have hAcomm₁ : ∀ x ∈ aOne L A, ∀ y ∈ aOne L A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hmax.prop.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨d, hdK, -, hdac, hAeq⟩ := h.exists_d h45
  have hdAK : d ∈ A ⊓ K := by
    rw [hdK]
    exact Subgroup.mem_zpowers d
  have hdA : d ∈ A := hdAK.1
  have hdL : d ∈ L := h.K_le_L hdAK.2
  set a₁ : QuotX L A := piX L A ⟨a, Subgroup.mem_sup_right h.a_mem⟩ with ha₁def
  set c₁ : QuotX L A := piX L A ⟨c, Subgroup.mem_sup_right h.c_mem⟩ with hc₁def
  set d₁ : QuotX L A := piX L A ⟨d, Subgroup.mem_sup_right hdA⟩ with hd₁def
  have ha₁ : orderOf a₁ = 3 := by
    have h1 : a₁ = ((aEquiv (L := L) hA ⟨a, h.a_mem⟩ : aOne L A) : QuotX L A) := rfl
    rw [h1, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact h.orderOf_a
  have hAa₁ : aOne L A ⊓ Subgroup.centralizer (lOne L A : Set (QuotX L A)) =
      Subgroup.zpowers a₁ := aOne_inf_centralizer hA hAL h.a_mem hCA
  have ha₁A : a₁ ∈ aOne L A := piX_mem_aOne h.a_mem
  have hc₁A : c₁ ∈ aOne L A := piX_mem_aOne h.c_mem
  have hd₁A : d₁ ∈ aOne L A := piX_mem_aOne hdA
  have hd₁L : d₁ ∈ lOne L A :=
    ⟨⟨d, Subgroup.mem_sup_right hdA⟩, Subgroup.mem_subgroupOf.mpr hdL, rfl⟩
  have hc₁3 : c₁ ^ 3 = 1 := hA3₁ c₁ hc₁A
  have ha₁C : a₁ ∈ Subgroup.centralizer (lOne L A : Set (QuotX L A)) := by
    have h1 : a₁ ∈ Subgroup.zpowers a₁ := Subgroup.mem_zpowers a₁
    rw [← hAa₁] at h1
    exact h1.2
  have hc₁a : c₁ ∉ Subgroup.zpowers a₁ := fun hmem =>
    h.c_not_mem (mem_zpowers_of_piX hA h.a_mem h.c_mem hmem)
  have hd₁a : d₁ ∉ Subgroup.zpowers a₁ := by
    intro hmem
    have h1 := mem_zpowers_of_piX hA h.a_mem hdA hmem
    apply hdac
    refine Subgroup.zpowers_le.mpr ?_ h1
    exact Subgroup.subset_closure (by simp)
  have hc₁C : c₁ ∉ Subgroup.centralizer (lOne L A : Set (QuotX L A)) := fun hC =>
    hc₁a (hAa₁ ▸ Subgroup.mem_inf.mpr ⟨hc₁A, hC⟩)
  obtain ⟨eT⟩ := nonempty_sup_equiv_thetaImage hLsn hA hAL
  obtain ⟨eAut⟩ := nonempty_autIn_lOne_equiv' hA hAL
  have hcube : ∀ x ∈ aOne L A,
      (⟨x, mem_normalizer_of_normal x⟩ : Subgroup.normalizer (lOne L A : Set (QuotX L A))) ^ 3
        = 1 := fun x hx => Subtype.ext (by rw [Subgroup.coe_pow]; exact hA3₁ x hx)
  rcases hany with hSL | ⟨p, e, hp, he, hiso⟩
  ·
    exfalso
    obtain ⟨π, p, f, Kf, _, hK, hq, hq2, ⟨e₁⟩⟩ :=
      exists_slPi_model (Sec13.isSLThreePi_of_mulEquiv Φ₀ hSL) hLq
    have hθ₁ := aschbacherSolvableCore_eq_bot_of_slPi hK hq hLq e₁
    have hπ : π = false → UnitaryFieldData p f Kf := fun h => by subst h; exact hK.unitary
    have hcy : ∃ y, IsPGLAt e₁ c₁ y := by
      rcases hkind with hin | hdiag
      · rcases slAct_pgl_or_field hK hq2 hθ₁ e₁ _ (hcube c₁ hc₁A) with ⟨y, hy, hys⟩ | ⟨hk, -⟩
        · exact ⟨y, hy, hys⟩
        · exact absurd (inducesStdKind_of_lOne hAL hΦ₀ h.c_mem hk)
            (not_inducesStdKind_of_not_inducesOuterTheta L hin (by decide))
      · exact exists_isPGLAt_of_diagonal hK hq hq2 hθ₁ e₁ hc₁3
          (inducesStdKind_lOne_of hAL hΦ₀ h.c_mem hdiag)
    let T : Subgroup (QuotX L A) :=
      { carrier := {x | ∃ y, IsPGLAt e₁ x y}
        mul_mem' := fun ⟨y, hy⟩ ⟨z, hz⟩ => ⟨y * z, isPGLAt_mul e₁ hy hz⟩
        one_mem' := ⟨1, isPGLAt_of_mem_centralizer e₁ (Subgroup.one_mem _)⟩
        inv_mem' := fun ⟨y, hy⟩ => ⟨y⁻¹, isPGLAt_inv hπ hy⟩ }
    have hAT : aOne L A ≤ T := aOne_le_of_closure hAeq h.a_mem h.c_mem hdA
      ⟨1, isPGLAt_of_mem_centralizer e₁ ha₁C⟩ hcy ⟨_, isPGLAt_of_mem e₁ hπ hd₁L⟩
    have hpgl : ∀ x ∈ aOne L A, ∃ y, IsPGLAt e₁ x y := fun x hx => hAT hx
    obtain ⟨n, hnL, hnN, hnd⟩ :=
      exists_not_normalizes_of_slPi hK hq e₁ hmax ha₁ hAa₁ hpgl hd₁A hd₁L hd₁a
    obtain ⟨l, hl, -, hlN, rfl⟩ := exists_lift_normalizer hA hAL hnL hnN
    apply hnd
    have hlK := h.normalizer_le hlN
    have h1 : l * d * l⁻¹ ∈ A ⊓ K := (Subgroup.mem_normalizer_iff.mp hlK d).mp hdAK
    rw [hdK] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [hd₁def, ← map_zpow, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hk
  ·
    obtain ⟨π, Kf, _, hK, hq, hq2, ⟨e₁⟩⟩ :=
      exists_pslPi_model he (Sec21.Item211Proof.isoLThreePi_of_mulEquiv Φ₀ hiso) hLq
    have hθ₁ := aschbacherSolvableCore_eq_bot_proj hK hq hLq e₁
    have := isPerfect_projImage_of_equiv e₁
    have hπ : π = false → UnitaryFieldData p e Kf := fun h => by subst h; exact hK.unitary
    have hcy : ∃ y, IsPGLAtP e₁ c₁ y := by
      rcases hkind with hin | hdiag
      · rcases pslAct_pgl_or_field hK hq2 hθ₁ e₁ _ (hcube c₁ hc₁A) with ⟨y, hy, hys⟩ | ⟨hk, -⟩
        · exact ⟨y, hy, hys⟩
        · exact absurd (inducesStdKind_of_lOne hAL hΦ₀ h.c_mem hk)
            (not_inducesStdKind_of_not_inducesOuterTheta L hin (by decide))
      · exact exists_isPGLAtP_of_diagonal hK hq hθ₁ e₁ hc₁3
          (inducesStdKind_lOne_of hAL hΦ₀ h.c_mem hdiag)
    let T : Subgroup (QuotX L A) :=
      { carrier := {x | ∃ y, IsPGLAtP e₁ x y}
        mul_mem' := fun ⟨y, hy⟩ ⟨z, hz⟩ => ⟨y * z, isPGLAtP_mul e₁ hy hz⟩
        one_mem' := ⟨1, isPGLAtP_of_mem_centralizer e₁ (Subgroup.one_mem _)⟩
        inv_mem' := fun ⟨y, hy⟩ => ⟨y⁻¹, isPGLAtP_inv_of hy⟩ }
    have hd₁y : ∃ y, IsPGLAtP e₁ d₁ y := by
      obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e₁ ⟨d₁, hd₁L⟩).2
      exact ⟨s, isPGLAtP_of_mem e₁ hπ hd₁L hs hse.symm⟩
    have hAT : aOne L A ≤ T := aOne_le_of_closure hAeq h.a_mem h.c_mem hdA
      ⟨1, isPGLAtP_of_mem_centralizer e₁ ha₁C⟩ hcy hd₁y
    have hpgl : ∀ x ∈ aOne L A, ∃ y, IsPGLAtP e₁ x y := fun x hx => hAT hx
    have hcardA := card_eq_card_inf_mul_card_rangeP (hK := hK) (hq := hq) (hA' := hpgl)
    rw [hAa₁, Nat.card_zpowers, ha₁, hA27] at hcardA
    have hR9 : Nat.card (pglHomP hK hq (aOne L A) hpgl).range = 9 := by omega
    have hRcomm := range_pglHomP_comm (hK := hK) (hq := hq) (hA' := hpgl) hAcomm₁
    have hRexp := range_pglHomP_pow (hK := hK) (hq := hq) (hA' := hpgl) hA3₁
    obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
    rcases frame_or_heis (hK.three_ne_zero hq) hτ hτ1 _ hRcomm hRexp (by rw [hR9]; norm_num) with
      ⟨bb, hbb, hd, -⟩ | ⟨y₁, y₂, hy₁, hy₂, ζ, hζ1, hζ⟩
    ·
      obtain ⟨φ⟩ := nonempty_autIn_equiv_perm_of_frameP hK hq e₁ hmax hA27 ha₁ hAa₁ hpgl hbb hd
      refine ⟨⟨eAut.symm.trans φ⟩, ?_⟩
      have hLC := inf_centralizer_eq_bot_proj hK hq e₁
      by_cases hcLC : c₁ ∈ lOne L A ⊔ Subgroup.centralizer (lOne L A : Set (QuotX L A))
      ·
        left
        have hc₁' : c₁ ∈ Subgroup.zpowers a₁ ⊔ lOne L A := by
          have h1 : c₁ ∈ aOne L A ⊓
              (lOne L A ⊔ Subgroup.centralizer (lOne L A : Set (QuotX L A))) :=
            Subgroup.mem_inf.mpr ⟨hc₁A, hcLC⟩
          rw [inf_sup_centralizer_eq hmax hLC hAa₁] at h1
          have hle : (aOne L A ⊓ lOne L A) ⊔ Subgroup.zpowers a₁ ≤
              Subgroup.zpowers a₁ ⊔ lOne L A :=
            sup_le (inf_le_right.trans le_sup_right) le_sup_left
          exact hle h1
        have hsup : aOne L A ⊔ lOne L A = Subgroup.zpowers a₁ ⊔ lOne L A := by
          apply le_antisymm
          · exact sup_le (aOne_le_of_closure hAeq h.a_mem h.c_mem hdA
              (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) hc₁'
              (Subgroup.mem_sup_right hd₁L)) le_sup_right
          · exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left ha₁A)) le_sup_right
        have hZ₁ : Subgroup.center (lOne L A) = ⊥ := center_eq_bot_proj hK hq e₁
        obtain ⟨eP⟩ := nonempty_zpowers_sup_equiv_prod hZ₁ ha₁C ha₁
        rcases hiso with ⟨hq3, ⟨ψ⟩⟩ | ⟨hq3, ⟨ψ⟩⟩
        · exact ⟨p, e, hp, he, Or.inl ⟨hq3, ⟨eT.symm.trans ((MulEquiv.subgroupCongr hsup).trans
            (eP.trans (MulEquiv.prodCongr (MulEquiv.refl _) (Φ₀.symm.trans ψ))))⟩⟩⟩
        · exact ⟨p, e, hp, he, Or.inr ⟨hq3, ⟨eT.symm.trans ((MulEquiv.subgroupCongr hsup).trans
            (eP.trans (MulEquiv.prodCongr (MulEquiv.refl _) (Φ₀.symm.trans ψ))))⟩⟩⟩
      ·
        right
        obtain ⟨yc, hyc⟩ := hcy
        have hsup : aOne L A ⊔ lOne L A =
            Subgroup.zpowers a₁ ⊔ (lOne L A ⊔ Subgroup.zpowers c₁) := by
          apply le_antisymm
          · refine sup_le (aOne_le_of_closure hAeq h.a_mem h.c_mem hdA
              (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
              (Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
              (Subgroup.mem_sup_right (Subgroup.mem_sup_left hd₁L))) ?_
            exact le_sup_left.trans le_sup_right
          · refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left ha₁A))
              (sup_le le_sup_right (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hc₁A)))
        have hca : a₁ * c₁ = c₁ * a₁ := hAcomm₁ a₁ ha₁A c₁ hc₁A
        have hP := isZ3PGLThreePi_sup hK hq hLC ha₁ ha₁C hca hc₁3 hcLC hyc hsup
        exact Sec13.isZ3PGLThreePi_of_mulEquiv eT hP
    ·
      exfalso
      obtain ⟨yc, hyc⟩ := hcy
      have hycZ := not_mem_zPi_of_isPGLAtP hK hq hc₁C hyc
      have hyc3 := pow_three_mem_zPiP hK hq hc₁3 hyc
      have h13 := type13_of_heisP hK hq hRcomm hy₁ hy₂ hζ1 hζ hyc.1 hycZ hyc3
        (mk_mem_range_pglHomP hc₁A hyc)
      exact false_of_isSolvable h (isSolvable_inf_centralizer_of_isPGLAtP hyc
        (isSolvable_centMod_of_type13 hK hq hyc.1 hycZ hyc3 h13))

end Main

end CFSG.RankThree.PartTwo.Sec4
