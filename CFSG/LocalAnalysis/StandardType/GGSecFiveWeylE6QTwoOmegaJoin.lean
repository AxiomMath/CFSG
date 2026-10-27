module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaLocal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaSpan
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoNbrConj
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoJoinPreimage
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoUnitaryAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoLabel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoPairing
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem GGSecFiveRouteCfg.exists_sup_eq_of_omegaPlus
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) (hNS : ¬ GGSplitLie 3 L) {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hM : ∃ e' : Fin 6 ≃ ι, M = CoxeterMatrix.E₆.reindex e')
    (hr : ∃ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e ∧ Nat.card (ggRankOneIn L Bs r) = 6)
    (h𝒦 : 𝒦.card = 2)
    (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1)) :
    ∃ K ∈ 𝒦, ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizerJoin L Bs 𝒦 := by
  classical
  have hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J := ⟨𝒦, hR, hNS, ι, M, e, hP, hM, hr⟩
  obtain ⟨hRest, -, -, hBs, hxB, hx1, horderx, hLx, hstar, hcyc, hNT⟩ :=
    e6QTwo_config_facts hC
  have hcfg : GGConfig 3 B Bs x L D J := hRest.1
  have hIDall : GGInnerDiagAll 3 B Bs x L D J := hRest.2.2.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hcfg.2.2
  have hNbrSet : GGNbrSet 3 B x D J 𝒦 := hR.2.2.2.1
  have hSclosed : ∀ lab lab' : LargeEvenLabel, GGLabelIso lab lab' →
      (lab'.tag = .D ∧ lab'.rank = 4 ∧ lab'.n = 1) →
      (lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = 1) := by
    intro lab lab' hiso h'
    rw [E6QTwo.eq_of_ggLabelIso_end hiso ⟨Or.inr (Or.inl ⟨h'.1, h'.2.1⟩), h'.2.2⟩]
    exact h'
  obtain ⟨hperf, Kf, hfieldK, hfiniteK, θ, hKf, hBsN, hI⟩ :=
    exists_omegaPlusDatum_of_innerDiagOnLabel_D4
      (E6QTwo.innerDiagOnLabel_of_marking (p := 3) hRig hSclosed hIDall.1 hlab)
  have hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian Nat.prime_three hBs hxB hx1 hLx
      (fun S hSL hSp => hcyc S hSp hSL)
  have hZ2 : IsPGroup 2 (Subgroup.center L) :=
    E6QTwo.isPGroup_two_center_of_omegaPlus hKf θ hperf
  obtain ⟨K₀, hWeyl₀⟩ := GGSecFiveE6QTwoCfg.exists_weylOfType_E6_sup hC
  have hAind₀ : ∀ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K₀ Bs, φ ∈ ggInduced ⊤ Bs := by
    intro φ hφ
    exact mem_ggInduced_top_of_mem_ggAutomizer
      (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ)
  have hcard : Nat.card Bs = 3 ^ 5 :=
    le_antisymm (E6QTwo.card_le_three_pow_five_of_omegaPlus hKf θ hperf hBs hBL hBsN hI)
      (E6QTwo.three_pow_five_le_card hBs hNT hAind₀ hWeyl₀)
  have hcardE : Nat.card ↥(Bs ⊓ L) = 3 ^ 4 :=
    E6QTwo.card_inf_eq_of_omegaPlus hKf θ hperf hZ2 hBs hcard hx1 hBL hstar hBsN hI
  obtain ⟨hAL192, hALr⟩ := E6QTwo.card_ggAutomizer_eq_of_omegaPlus hKf θ hZ2 hBs
    hcard hcardE hx1 hLx hBL hstar
  obtain ⟨hDB, -, hDcard, hxD, -, hJcomp, -⟩ := hDJ.1
  obtain ⟨hlabJ, hJaut, h6⟩ := E6QTwo.hasLabel_and_ggAutomizer_of_omegaPlus hKf θ hperf
    hZ2 hBs hcard hcardE hx1 hLx hBL hstar hBsN hI (hDB.trans hcfg.2.1.1) hDcard hxD hJcomp
  obtain ⟨K₁, K₂, hK₁₂, rfl⟩ := Finset.card_eq_two.mp h𝒦
  obtain ⟨y₁, hNbr₁⟩ := hNbrSet.2 K₁ (by simp)
  obtain ⟨y₂, hNbr₂⟩ := hNbrSet.2 K₂ (by simp)
  have hy₁B : y₁ ∈ Bs := hcfg.2.1.1 hNbr₁.1.2.1
  have hy₂B : y₂ ∈ Bs := hcfg.2.1.1 hNbr₂.1.2.1
  have hy₁D : y₁ ∈ D := by
    rw [hNbr₁.2.1]
    exact Subgroup.subset_closure (by simp)
  have hy₂D : y₂ ∈ D := by
    rw [hNbr₂.2.1]
    exact Subgroup.subset_closure (by simp)
  have hJK₁ : J ≤ K₁ :=
    le_of_ggNbr hLB hcfg.1 hDJ (E6QTwo.three_dvd_card_of_hasLabel_twA3 hlabJ) hNbr₁
  have hJK₂ : J ≤ K₂ :=
    le_of_ggNbr hLB hcfg.1 hDJ (E6QTwo.three_dvd_card_of_hasLabel_twA3 hlabJ) hNbr₂
  have hcomp₁ : CFSG.Assembly.IsComponentOf K₁ (Subgroup.centralizer ({y₁} : Set G)) :=
    (isComponentOf_of_isNeighborOf hcfg.1.2.2.2.2.2.2.2
      (isNeighborOf_of_ggNbr hDJ hNbr₁)).1
  have hcomp₂ : CFSG.Assembly.IsComponentOf K₂ (Subgroup.centralizer ({y₂} : Set G)) :=
    (isComponentOf_of_isNeighborOf hcfg.1.2.2.2.2.2.2.2
      (isNeighborOf_of_ggNbr hDJ hNbr₂)).1
  have hxy₁ : (⟨y₁, hy₁B⟩ : ↥Bs) ∉ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hyx : y₁ ∈ Subgroup.zpowers x :=
      Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hDle : D ≤ Subgroup.zpowers x := by
      rw [hNbr₁.2.1, Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact Subgroup.mem_zpowers z
      · exact hyx
    have h9 := Subgroup.card_le_of_le hDle
    rw [hDcard, Nat.card_zpowers, horderx] at h9
    norm_num at h9
  have hxy₂ : (⟨y₂, hy₂B⟩ : ↥Bs) ∉ Subgroup.zpowers (⟨x, hxB⟩ : ↥Bs) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hyx : y₂ ∈ Subgroup.zpowers x :=
      Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hDle : D ≤ Subgroup.zpowers x := by
      rw [hNbr₂.2.1, Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact Subgroup.mem_zpowers z
      · exact hyx
    have h9 := Subgroup.card_le_of_le hDle
    rw [hDcard, Nat.card_zpowers, horderx] at h9
    norm_num at h9
  have hy₁₂ : (⟨y₂, hy₂B⟩ : ↥Bs) ∉ Subgroup.zpowers (⟨y₁, hy₁B⟩ : ↥Bs) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hzy : y₂ ∈ Subgroup.zpowers y₁ :=
      Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
    exact hK₁₂ (GGNbr.eq_of_mem_zpowers hLB hcfg.1 hDJ
      (E6QTwo.three_dvd_card_of_hasLabel_twA3 hlabJ) hNbr₁ hNbr₂ hzy)
  have hW : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizerJoin L Bs {K₁, K₂}) := by
    obtain ⟨e', rfl⟩ := hM
    exact GGWeylOfType.of_reindex (M := CoxeterMatrix.E₆) (e := e') ⟨e, hP.2⟩
  have hAJle : ggAutomizerJoin L Bs {K₁, K₂} ≤ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (iSup₂_le fun K _ => ggAutomizer_mono Bs le_top)
  have hAind : ∀ ψ ∈ ggAutomizerJoin L Bs {K₁, K₂}, ψ ∈ ggInduced ⊤ Bs :=
    fun ψ hψ => mem_ggInduced_top_of_mem_ggAutomizer (hAJle hψ)
  have hALA : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs {K₁, K₂} := by
    rw [ggAutomizerJoin]
    exact le_sup_left
  have hA₁A : ggAutomizer K₁ Bs ≤ ggAutomizerJoin L Bs {K₁, K₂} := by
    rw [ggAutomizerJoin]
    exact le_sup_of_le_right (le_iSup₂_of_le K₁ (by simp) le_rfl)
  have hA₂A : ggAutomizer K₂ Bs ≤ ggAutomizerJoin L Bs {K₁, K₂} := by
    rw [ggAutomizerJoin]
    exact le_sup_of_le_right (le_iSup₂_of_le K₂ (by simp) le_rfl)
  have hb : (⟨x, hxB⟩ : ↥Bs) ≠ 1 := by
    intro h
    exact hx1 (Subtype.ext_iff.mp h)
  have hfixAL : ∀ ψ ∈ ggAutomizer L Bs, ψ ⟨x, hxB⟩ = ⟨x, hxB⟩ :=
    fun ψ hψ => ggAutomizer_apply_eq_of_le_centralizer hLx hψ
  have hR₁ : ∀ r ∈ ggAutomizer L Bs, GGIsReflection 3 r →
      (∀ d : ↥Bs, (d : G) ∈ D → r d = d) → r ∈ ggAutomizer K₁ Bs :=
    fun r hr _ hrD => ggAutomizer_mono Bs hJK₁ (hJaut r hr hrD)
  have hR₂ : ∀ r ∈ ggAutomizer L Bs, GGIsReflection 3 r →
      (∀ d : ↥Bs, (d : G) ∈ D → r d = d) → r ∈ ggAutomizer K₂ Bs :=
    fun r hr _ hrD => ggAutomizer_mono Bs hJK₂ (hJaut r hr hrD)
  have hN₁ : ∀ ψ ∈ ggAutomizerJoin L Bs {K₁, K₂}, ψ ⟨y₁, hy₁B⟩ = ⟨y₁, hy₁B⟩ →
      (∀ a ∈ ggAutomizer K₁ Bs, ψ * a * ψ⁻¹ ∈ ggAutomizer K₁ Bs) ∨
        ∀ a ∈ ggAutomizer K₁ Bs, ∀ b ∈ ggAutomizer K₁ Bs,
          a * (ψ * b * ψ⁻¹) = ψ * b * ψ⁻¹ * a :=
    fun ψ hψ hψy => ggAutomizer_conj_mem_or_commute hy₁B hcomp₁ (hAJle hψ) hψy
  have hN₂ : ∀ ψ ∈ ggAutomizerJoin L Bs {K₁, K₂}, ψ ⟨y₂, hy₂B⟩ = ⟨y₂, hy₂B⟩ →
      (∀ a ∈ ggAutomizer K₂ Bs, ψ * a * ψ⁻¹ ∈ ggAutomizer K₂ Bs) ∨
        ∀ a ∈ ggAutomizer K₂ Bs, ∀ b ∈ ggAutomizer K₂ Bs,
          a * (ψ * b * ψ⁻¹) = ψ * b * ψ⁻¹ * a :=
    fun ψ hψ hψy => ggAutomizer_conj_mem_or_commute hy₂B hcomp₂ (hAJle hψ) hψy
  have hres := E6QTwo.sup_eq_or_sup_eq_of_card_192 (Bs := Bs)
    hBs hNT hcard card_coxeterE6_group
    (A := ggAutomizerJoin L Bs {K₁, K₂}) hW hAind
    (AL := ggAutomizer L Bs) hALA hAL192 hALr
    (x := (⟨x, hxB⟩ : ↥Bs)) hb hfixAL
    (D := D) (hDBs := hDB.trans hcfg.2.1.1) (hD := by rw [hDcard]; norm_num) hxD h6
    (y₁ := (⟨y₁, hy₁B⟩ : ↥Bs)) (y₂ := (⟨y₂, hy₂B⟩ : ↥Bs)) hy₁D hy₂D hxy₁ hxy₂ hy₁₂
    (A₁ := ggAutomizer K₁ Bs) (A₂ := ggAutomizer K₂ Bs) hA₁A hA₂A hR₁ hR₂ hN₁ hN₂
  rcases hres with h | h
  · exact ⟨K₁, by simp, h⟩
  · exact ⟨K₂, by simp, h⟩

end CFSG.StandardType

end
