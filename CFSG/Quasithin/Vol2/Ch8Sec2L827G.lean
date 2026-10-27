module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827D
public import CFSG.Quasithin.Vol2.Ch8Sec2L827E
public import CFSG.Quasithin.Vol2.Ch8Sec2L827F
public import CFSG.Quasithin.Vol2.Ch9Sec4Xi
public import CFSG.Quasithin.H13.NQCatSuzukiCComponent
public import CFSG.Quasithin.H13.A5S132
public import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
public import CFSG.Quasithin.Vol2.Ch8Sec2D3Inputs
public import CFSG.Quasithin.Vol2.Ch8Sec2HLU
public import CFSG.Quasithin.Vol2.Ch8Sec2L828E

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

section L827G

theorem step827_of
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal)
    (hcard : Mathieu.StmtH13Card) (h734 : Stmt7_3_4) (h822 : Stmt8_2_2) (h825 : Stmt8_2_5)
    (hxi : Step827Xi) : Step827 := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC K hK hLUK
  by_contra hKq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC5 := h825 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  obtain ⟨hV, hL0, hTL, hLN, -, hAN, hAL, hAp, hAe, hTU, -, hU1, hLUT⟩ :=
    setup_828 hmod h711n hyp hrow hC hC5
  obtain ⟨hfam, hLUC, -⟩ :=
    lu_facts_828 hLU82_holds hcard hyp hrow hC5 hV hL0 hTL hLN hAN hAL hAp hAe hLUT
  have hLU := hlu82_82 hLU82_holds hcard hrow hL0 hV hLN hC5 hAN hAL hAp hAe
  have hUV : ch82U (fsuV T I) h ≤ fsuV T I := inf_le_left
  have hU2 : IsPGroup 2 ↥(ch82U (fsuV T I) h) := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hV.2 _ x.2.1)⟩
  have hS : QuasithinUnique.IsSylowTwoOf T
      (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) :=
    ⟨hTU, hyp.fsu.sylow.1, fun h2 =>
      hyp.fsu.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTU))⟩
  have hH2 : pCoreOf 2 (Subgroup.normalizer (ch82U (fsuV T I) h : Set G)) ≠ ⊥ := by
    intro hbot
    apply hU1
    rw [eq_bot_iff, ← hbot]
    exact CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 _ hU2
  have hKn := lemma_1_2_4_normal hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37 h38 hH2 hS
    hfam hLUK hK hLUT
  have hKN : K ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G) := le_of_mem_cComp hK
  have hNK : Subgroup.normalizer (ch82U (fsuV T I) h : Set G) ≤
      Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).mp hKn
  have hSQ := stronglyQuasithin_of_pCoreOf_ne_bot hyp.fsu.qtke hH2
  obtain ⟨X, hXi, hXK, hNKX, hXs, hXK'⟩ := exists_isXi_of_cComp hSQ hS hK hNK hH2 hKq
  obtain ⟨-, hTX, hO2XT, p, hp, hp2, hXp, -, -⟩ := id hXi
  have hKX : K ≤ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer.trans hNKX
  have hLUL : ch82LU L (ch82U (fsuV T I) h) ≤ L := (perfectCore_le _).trans inf_le_left
  have hLUp : ⁅ch82LU L (ch82U (fsuV T I) h), ch82LU L (ch82U (fsuV T I) h)⁆ =
      ch82LU L (ch82U (fsuV T I) h) := perfectCore_perfect _
  have hLUns : ¬ Group.IsSolvable ↥(ch82LU L (ch82U (fsuV T I) h)) := by
    intro hs
    apply hLUC
    have hp' : Group.IsPerfect ↥(ch82LU L (ch82U (fsuV T I) h)) :=
      Subgroup.isPerfect_iff.mpr hLUp
    have hsub : Subsingleton ↥(ch82LU L (ch82U (fsuV T I) h)) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isSolvable _ hs
    intro x hx
    have hx1 : x = 1 := congrArg Subtype.val
      (Subsingleton.elim (⟨x, hx⟩ : ↥(ch82LU L (ch82U (fsuV T I) h))) 1)
    rw [hx1]
    exact Subgroup.one_mem _
  have hLUX : ¬ ⁅ch82LU L (ch82U (fsuV T I) h), X⁆ ≤ pCoreOf 2 X := fun h' =>
    hLUns (hXK' _ hLUK h')
  have hXM : ¬ X ≤ fsuM T L := by
    intro hXM
    apply hLUX
    have hML : fsuM T L = Subgroup.normalizer (L : Set G) := by
      rw [show fsuM T L = Subgroup.normalizer (fsuL0 T L : Set G) from rfl, hL0]
    have hXLU : X ≤ Subgroup.normalizer (ch82LU L (ch82U (fsuV T I) h) : Set G) := by
      intro x hx
      apply normalizer_le_normalizer_perfectCore
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨(hML ▸ hXM) hx, Subgroup.le_normalizer (hKN (hXK hx))⟩
    have hLUXn : ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.normalizer (X : Set G) :=
      hLUK.trans hKX
    have hLUV : ch82LU L (ch82U (fsuV T I) h) ≤ Subgroup.normalizer (fsuV T I : Set G) :=
      hLUL.trans hLN
    have hperfL : ⁅L, L⁆ = L := hyp.fsu.maximal.1.2.1.2.1
    have hNC : Subgroup.normalizer (fsuV T I : Set G) ≤
        Subgroup.normalizer (Subgroup.centralizer (fsuV T I : Set G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _)
    have hLD : L ≤ Subgroup.normalizer
        ((L ⊓ Subgroup.centralizer (fsuV T I : Set G) : Subgroup G) : Set G) :=
      (le_inf Subgroup.le_normalizer (hLN.trans hNC)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hLCV : ⁅L, L ⊓ Subgroup.centralizer (fsuV T I : Set G)⁆ ≤ pCoreOf 2 L := by
      refine commutator_le_pCoreOf_828 (D := L ⊓ Subgroup.centralizer (fsuV T I : Set G))
        hyp.fsu.quasisimple hperfL (inf_le_left.trans Subgroup.le_normalizer) inf_le_left
        ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hLD) ?_
        (Subgroup.le_normalizer_iff_commutator_le_right.mp hLD)
      intro e
      apply not_le_centralizer_fsuV hyp hTL
      rw [← e]
      exact inf_le_right
    have hCB : ⁅ch82LU L (ch82U (fsuV T I) h) ⊓ Subgroup.centralizer (fsuV T I : Set G),
        ch82LU L (ch82U (fsuV T I) h)⁆ ≤ pCoreOf 2 L := by
      refine (Subgroup.commutator_mono (inf_le_inf_right _ hLUL) hLUL).trans ?_
      rw [Subgroup.commutator_comm]
      exact hLCV
    exact commutator_le_pCoreOf_827 hLUp hLUXn hXLU hLUV hLU.1
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hCB hp hp2 hXp hXs
  have hInH : InH T (X ⊔ T) := ⟨le_sup_right, hO2XT⟩
  obtain ⟨H', hH', hH'XT⟩ := A5.exists_isHStar_le' hInH (fun h' => hXM (le_sup_left.trans h'))
  have hTs : Group.IsSolvable ↥T := by
    have := (hyp.fsu.sylow.1 : IsPGroup 2 ↥T).isNilpotent
    infer_instance
  have hXTs : Group.IsSolvable ↥(X ⊔ T) :=
    CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer hTX hXs hTs
  have hH's : Group.IsSolvable ↥H' :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hH'XT)
      (Subgroup.inclusion_injective hH'XT)
  have hfix : fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)) =
      (ch82U (fsuV T I) h).subgroupOf (fsuV T I) := fixV_autOn_82 hAN
  let eW : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) ≃* ↥(ch82U (fsuV T I) h) :=
    (MulEquiv.subgroupCongr hfix).trans (Subgroup.subgroupOfEquivOfLe hUV)
  have heW : ∀ w, ((eW w : ↥(ch82U (fsuV T I) h)) : G) = ((w : ↥(fsuV T I)) : G) :=
    fun w => rfl
  have heWs : ∀ u : ↥(ch82U (fsuV T I) h),
      (((eW.symm u : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) : ↥(fsuV T I)) : G) =
        (u : G) := fun u => rfl
  let ψ : ↥K →* MulAut ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) :=
    (MulAut.congr eW.symm).toMonoidHom.comp
      ((conjAct (ch82U (fsuV T I) h)).comp (Subgroup.inclusion hKN))
  have hψ : ∀ (x : ↥K) (w : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))),
      (((ψ x w : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) : ↥(fsuV T I)) : G) =
        (x : G) * ((w : ↥(fsuV T I)) : G) * (x : G)⁻¹ := by
    intro x w
    show (((eW.symm (conjAct (ch82U (fsuV T I) h) (Subgroup.inclusion hKN x) (eW w)) :
      ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) : ↥(fsuV T I)) : G) = _
    rw [heWs, CFSG.QuasithinUnique.Setup.coe_conjAct_apply, heW]
    rfl
  have hXY : autSub (autOn (ch82LU L (ch82U (fsuV T I) h)) (fsuV T I))
      (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) ≤ ψ.range := by
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨b, hb, hgb⟩ := Subgroup.mem_map.mp hg
    have hbLU : (b : G) ∈ ch82LU L (ch82U (fsuV T I) h) := Subgroup.mem_subgroupOf.mp hb
    refine ⟨⟨b, hLUK hbLU⟩, ?_⟩
    ext w
    rw [hψ, resHom_apply, ← hgb, CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
  have hW2 : ∀ w : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))), w ^ 2 = 1 := by
    intro w
    apply Subtype.ext
    apply Subtype.ext
    show ((w : ↥(fsuV T I)) : G) ^ 2 = 1
    exact hV.2 _ (w : ↥(fsuV T I)).2
  have hW16 : rk ↥(ch82U (fsuV T I) h) = 4 →
      Nat.card ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 16 := by
    intro hrk
    rw [Nat.card_congr eW.toEquiv]
    obtain ⟨n, hn⟩ := hU2.exists_card_eq
    have hn4 : n = 4 := by
      rw [← hrk]
      unfold rk
      rw [hn, padicValNat.prime_pow]
    rw [hn, hn4]
    norm_num
  have hXCU : ((∃ n : ℕ, Row711L3Nine T L I n) ∨ Row711M22Code T L I) →
      X ≤ Subgroup.centralizer (ch82U (fsuV T I) h : Set G) := by
    intro hr
    have hrk : rk ↥(ch82U (fsuV T I) h) = 4 := by
      rcases hr with hr | hr
      · exact (hC5.2.2.2.1 hr).2.2.2
      · exact (hC5.2.2.2.2.1 hr).2.2.2
    have hN : (X.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mpr hKX
    have hO : ((pCoreOf 2 X).subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXK)).mpr
        (hKX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
    have hO2 : IsPGroup 2 ↥((pCoreOf 2 X).subgroupOf K) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).comap_of_injective K.subtype
        K.subtype_injective
    have hNp : ∀ n ∈ X.subgroupOf K, n ^ p ∈ (pCoreOf 2 X).subgroupOf K := by
      intro n hn
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      rw [Subgroup.coe_pow]
      exact hXp _ hn
    have hmap := map_eq_bot_827 hW2 (hW16 hrk) ψ (hLU.2.1 hr) hXY hN hO hO2 hp hp2 hNp
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hψx : ψ ⟨x, hXK hx⟩ = 1 := by
      have hmem : ψ ⟨x, hXK hx⟩ ∈ (X.subgroupOf K).map ψ :=
        ⟨_, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      rw [hmap, Subgroup.mem_bot] at hmem
      exact hmem
    have h1 := congrArg (fun φ : MulAut ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) =>
      (((φ (eW.symm ⟨u, hu⟩) : ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)))) :
        ↥(fsuV T I)) : G)) hψx
    rw [hψ, heWs, MulAut.one_apply, heWs] at h1
    calc u * x = x * u * x⁻¹ * x := by rw [h1]
      _ = x * u := by group
  obtain ⟨-, hall⟩ := h822 G T L I hyp h731 h821 hc hrow
  obtain ⟨⟨h', hh', hIC, hhI⟩, hall'⟩ := hall H' hH'
  obtain ⟨k', hC'⟩ := hall' h' hh' hIC hhI
  rcases id hrow with hr | hr | hr | hr
  · exact hxi G T L I hyp h731 h821 hc hrow H h k hH hh hC (Or.inl hr) K hK hLUK hKq X hXi hXK
      (hXCU (Or.inl hr)) hXM hNKX hXK' H' h' k' hH' hH'XT hh' hC'
  · exact hxi G T L I hyp h731 h821 hc hrow H h k hH hh hC (Or.inr hr) K hK hLUK hKq X hXi hXK
      (hXCU (Or.inr hr)) hXM hNKX hXK' H' h' k' hH' hH'XT hh' hC'
  ·
    have hrk : rk ↥(ch82U (fsuV T I) h) = 4 := (hC5.2.2.2.2.2.1 hr).2.2.2
    have hSQT : CFSG.IsStronglyQuasithin ↥K := by
      rw [CFSG.SectionRank.isStronglyQuasithin_iff]
      intro q hq hq2
      exact (CFSG.SectionRank.pRank_top_le_of_injective hq.one_lt (Subgroup.inclusion hKN)
        (Subgroup.inclusion_injective hKN)).trans (hSQ q hq hq2)
    have hKself : K ∈ cComp K := cComp_mem_of_le hK le_rfl hKN
    have hKtop : CFSG.IsCComponent (⊤ : Subgroup ↥K) := by
      have h3 := mem_cComp_top_iff_isCComponent.mp (subgroupOf_mem_cComp hKself)
      rwa [Subgroup.subgroupOf_self] at h3
    obtain ⟨s, hs, hs5, π, hπ, hker, -⟩ :=
      (NQCat.sqt_nonquasisimple_Ccomponent_prime_linear_radical_quotient_and_no_Suzuki_section
        hSQT hKtop).1 hKq
    have hkers : Group.IsSolvable ↥π.ker := by
      rw [hker]
      exact CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
    exact false_of_code24_827 hW2 (hW16 hrk) ψ (hLU.2.2.1 hr) hXY hs hs5 π hπ hkers
  ·
    have hw2 := (hC5.2.2.2.2.2.2.1 hr).1
    have h1 := ((h734 G T L I hyp h731 hV).1 H' hH').1
    have h2 := E1.solvable_nParam_le_one hH's
    rw [hw2] at h1
    exact absurd (h1.trans h2) (by decide)

end L827G

end CFSG.Quasithin.H13
