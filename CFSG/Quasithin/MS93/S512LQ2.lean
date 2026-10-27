module

public import CFSG.Quasithin.MS93.S512LHat
public import CFSG.Quasithin.MS93.S512LRed

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512L

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem offender_facts (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hb : 2 < critDist (puAmalgam h.le))
    (hv : ⁅Vv _ (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆ ≤
      S5.dSub h.le L (baseA _))
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hTl : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.qLine l))
    (hsec : S512N.SecHyp h (S5.voSub h.le L (baseA _)))
    {S : Type} [CommGroup S] {p : ↥(S5.voSub h.le L (baseA (puAmalgam h.le))) →* S}
    {ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S}
    (hs : S36E.SecData (stab _ (baseA (puAmalgam h.le))) (S5.voSub h.le L (baseA _))
      (S5.voSub h.le L (baseA _) ⊓ S5.bSub h.le L (baseA _)) S p ρ)
    (hirr : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → S512N.IsInv ρ S₁ → S₁ = ⊤)
    {W E : Subgroup (puAmalgam h.le).Universal} {δ : Vtx (puAmalgam h.le)}
    (hWst : W ≤ stab _ (baseA (puAmalgam h.le)))
    (hVW : S5.voSub h.le L (baseA _) ≤ W ⊔ S5.bSub h.le L (baseA _))
    (hEβ : E ≤ Qv _ (baseB (puAmalgam h.le)))
    (hpair : ⁅W ⊓ Qv _ δ, E⁆ ≤ ZM _ (baseA (puAmalgam h.le)))
    (hidx : (Qv _ δ).relIndex W ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex E)
    (hlt : 1 < (Qv _ (baseA (puAmalgam h.le))).relIndex E) :
    S38E.IsIrrRep L (ρ.comp (S512N.eM h.le)) ∧
      (E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ ≤ ρ.range ∧
      IsElemAbelian2 ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ) ∧
      (E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ ≠ ⊥ ∧
      Nat.card S ≤ Nat.card ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ) *
        Nat.card (fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ)) := by
  have := hsec.finite_S hs
  have hQ := rho_eq_one_of_mem_qv h hv (voSub_le_vv h) hs
  have hρM := isIrrRep_of_irr h hsec hs hQ hirr
  have hβα := (adj_baseA_baseB (puAmalgam h.le)).symm
  have hEst : E ≤ stab _ (baseA (puAmalgam h.le)) := hEβ.trans (qv_le_stab_of_adj _ hβα)
  have hE2 : IsPGroup 2 E := (isPGroup_qv _ h.hyp20 (not_isMVtx_baseB _)).to_le hEβ
  have hAcard := card_map_eq h hv (voSub_le_vv h) hsec hs hirr hEst hE2
  have hAidx := index_fixV_le h hb (voSub_le_vv h) hs hWst hVW hEst hpair
  have hAel : IsElemAbelian2 ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
      obtain ⟨hc, -⟩ := commutator_mem_qv_of_le_qLine h hd hl hTl
        (hEβ (Subgroup.mem_subgroupOf.1 hg)) (hEβ (Subgroup.mem_subgroupOf.1 hg'))
      have hcq : ρ ⁅g, g'⁆ = 1 := hQ ⁅g, g'⁆ (by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at hc ⊢
        exact hc)
      rw [← map_mul, ← map_mul]
      have e : g * g' = ⁅g, g'⁆ * (g' * g) := by
        rw [commutatorElement_def]
        group
      rw [e, map_mul, hcq, one_mul]
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨-, hsq⟩ := commutator_mem_qv_of_le_qLine h hd hl hTl
        (hEβ (Subgroup.mem_subgroupOf.1 hg)) (hEβ (Subgroup.mem_subgroupOf.1 hg))
      rw [← map_pow]
      exact hQ (g ^ 2) (by simpa using hsq)
  have hA1 : (E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hAcard
    omega
  refine ⟨hρM, Subgroup.map_le_range _ _, hAel, hA1, ?_⟩
  have h1 := (fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ)).card_mul_index
  rw [← h1, mul_comm, hAcard]
  exact Nat.mul_le_mul_right _ (hAidx.trans hidx)

theorem ff_cases_q2 (h14 : MS14AS) (hSQ : SQTKQuot) (hT : S32.TypeFacts) (h : PUHyp M T L)
    (hd : S5.IsSp4Data M T L k F a) (hk1 : k = 1) {S₀ : Type} [CommGroup S₀] [Finite S₀]
    {ρ : ↥M →* MulAut S₀} (hρ : S38E.IsIrrRep L ρ) (hFF : IsFFModule ρ.range) :
    FFCaseHatA6 (S38E.IsIrrRep.imL L ρ) ∨ AlternatingNatural (S38E.IsIrrRep.imL L ρ) ⊤ ⊥ 6 := by
  have hH := hρ.ffHyp h hSQ hFF
  obtain ⟨-, -, hcases, -⟩ := h14 S₀ hρ.sq _ _ hH
  have h360 : Nat.card (S32.Lstar L) = 360 := by
    rcases S512N.card_lstar_of_data h hd with ⟨-, h360⟩ | ⟨hk2, -⟩
    · exact h360
    · omega
  rcases hcases with hSL | hhat | hsp | hG2
  · exfalso
    obtain ⟨n, hn, hc⟩ := S38E.card_lstar_of_ffCaseSL3 hρ h hSL
    exact S32.ordA_two_ne_360 hn (hc.symm.trans h360)
  · exact Or.inl hhat
  · rcases hsp with ⟨n, hn2, F', iF, fF, hcard, π, hπ⟩ | hA6
    · exfalso
      have hc := S38E.card_lstar_of_sp4Nat hρ h hn2 ⟨F', iF, fF, hcard, π, hπ⟩
      exact (S32.ordBC_two_ne (by omega)).2.1 (hc.symm.trans h360)
    · exact Or.inr hA6
  · exfalso
    rcases S38E.card_lstar_of_ffCaseG2 hρ h hT hG2 with ⟨n, hn2, hc⟩ | hc
    · exact (S32.ordG2_ne (by omega)).2.1 (hc.symm.trans h360)
    · rw [hc] at h360
      norm_num at h360

theorem exists_setup_of (h : PUHyp M T L)
    {S : Type} [CommGroup S] {p : ↥(S5.voSub h.le L (baseA (puAmalgam h.le))) →* S}
    {ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S}
    (hs : S36E.SecData (stab _ (baseA (puAmalgam h.le))) (S5.voSub h.le L (baseA _))
      (S5.voSub h.le L (baseA _) ⊓ S5.bSub h.le L (baseA _)) S p ρ)
    (hirr : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → S512N.IsInv ρ S₁ → S₁ = ⊤)
    {F' : Type} [Field F'] {a' : ↥(stab (puAmalgam h.le) (baseA _)) →* MSP.Sp4 F'}
    {θ : S ≃* Multiplicative (MSP.V4 F')}
    (hθ : ∀ (g : ↥(stab (puAmalgam h.le) (baseA _))) (s : S),
      Multiplicative.toAdd (θ (ρ g s)) = MSP.mat (a' g) *ᵥ Multiplicative.toAdd (θ s))
    (hord3 : ∀ g : MSP.Sp4 F', g ^ 3 = 1 → ∃ l : ↥(stab (puAmalgam h.le) (baseA _)),
      (l : (puAmalgam h.le).Universal) ∈ puTrans h.le L (baseA _) ∧ a' l = g)
    {V₀ : Subgroup (puAmalgam h.le).Universal} (hV₀ : V₀ ≤ S5.voSub h.le L (baseA _))
    (hV₀n : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (V₀ : Set _))
    (hV₀B : ¬ V₀ ≤ S5.bSub h.le L (baseA _)) :
    ∃ βv : (puAmalgam h.le).Universal → MSP.V4 F',
      S310.Setup (stab _ (baseA (puAmalgam h.le))) (puTrans h.le L (baseA _)) V₀
        (V₀ ⊓ S5.bSub h.le L (baseA _)) a' βv := by
  classical
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  let βv : (puAmalgam h.le).Universal → MSP.V4 F' := fun x =>
    if hx : x ∈ S5.voSub h.le L (baseA (puAmalgam h.le)) then
      Multiplicative.toAdd (θ (p ⟨x, hx⟩)) else 0
  have hβv : ∀ x (hx : x ∈ S5.voSub h.le L (baseA (puAmalgam h.le))),
      βv x = Multiplicative.toAdd (θ (p ⟨x, hx⟩)) := fun x hx => by simp [βv, hx]
  have hsurj := exists_mem_of_irr hs hirr hV₀ hV₀n hV₀B
  refine ⟨βv, puTrans_le_stab h.le L _, stab_le_normalizer_puTrans h.le hLn _, hV₀n, inf_le_left,
    fun x hx y hy => ?_, fun w => ?_, fun x hx => ?_, fun g x hx => ?_, hord3⟩
  · rw [hβv x (hV₀ hx), hβv y (hV₀ hy), hβv _ (mul_mem (hV₀ hx) (hV₀ hy))]
    rw [show (⟨x * y, mul_mem (hV₀ hx) (hV₀ hy)⟩ : ↥(S5.voSub h.le L (baseA _))) =
      ⟨x, hV₀ hx⟩ * ⟨y, hV₀ hy⟩ from rfl, map_mul, map_mul, toAdd_mul]
  · obtain ⟨v, hv, hpv⟩ := hsurj (θ.symm (Multiplicative.ofAdd w))
    refine ⟨v, hv, ?_⟩
    rw [hβv _ v.2, Subtype.coe_eta, hpv, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  · rw [hβv x (hV₀ hx)]
    constructor
    · intro h0
      have h1 : θ (p ⟨x, hV₀ hx⟩) = 1 := by
        apply Multiplicative.toAdd.injective
        rw [h0]
        rfl
      have h2 : p ⟨x, hV₀ hx⟩ = 1 := by
        rw [← map_one θ] at h1
        exact θ.injective h1
      exact ⟨hx, ((hs.ker _).1 h2).2⟩
    · intro h1
      have h2 : p ⟨x, hV₀ hx⟩ = 1 := (hs.ker _).2 ⟨hV₀ hx, h1.2⟩
      rw [h2, map_one]
      rfl
  · have hgx : (g : (puAmalgam h.le).Universal) * x * (g : (puAmalgam h.le).Universal)⁻¹ ∈
        S5.voSub h.le L (baseA (puAmalgam h.le)) := S36E.conj_mem hs.hMA g.2 (hV₀ hx)
    rw [hβv x (hV₀ hx), hβv _ hgx, ← hθ g, hs.conj g ⟨x, hV₀ hx⟩ hgx]

theorem exists_setup_alt (h : PUHyp M T L)
    {S : Type} [CommGroup S] [Finite S] {p : ↥(S5.voSub h.le L (baseA (puAmalgam h.le))) →* S}
    {ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S}
    (hs : S36E.SecData (stab _ (baseA (puAmalgam h.le))) (S5.voSub h.le L (baseA _))
      (S5.voSub h.le L (baseA _) ⊓ S5.bSub h.le L (baseA _)) S p ρ)
    (hirr : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → S512N.IsInv ρ S₁ → S₁ = ⊤)
    (hK : AlternatingNatural (S38E.IsIrrRep.imL L (ρ.comp (S512N.eM h.le))) ⊤ ⊥ 6)
    {V₀ : Subgroup (puAmalgam h.le).Universal} (hV₀ : V₀ ≤ S5.voSub h.le L (baseA _))
    (hV₀n : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (V₀ : Set _))
    (hV₀B : ¬ V₀ ≤ S5.bSub h.le L (baseA _)) :
    ∃ (a' : ↥(stab (puAmalgam h.le) (baseA _)) →* MSP.Sp4 (ZMod 2))
      (βv : (puAmalgam h.le).Universal → MSP.V4 (ZMod 2)),
      S310.Setup (stab _ (baseA (puAmalgam h.le))) (puTrans h.le L (baseA _)) V₀
        (V₀ ⊓ S5.bSub h.le L (baseA _)) a' βv := by
  obtain ⟨π, hπ⟩ := hK
  obtain ⟨φ, θ, hθ⟩ := S36E.coord_of_altDn hπ (S38E.IsIrrRep.range_le_normalizer h)
  have hmemR : ∀ g : ↥(stab (puAmalgam h.le) (baseA _)),
      ρ g ∈ (ρ.comp (S512N.eM h.le)).range := fun g => by
    obtain ⟨m, rfl⟩ := S512N.eM_surjective h.le g
    exact ⟨m, rfl⟩
  set a' := φ.comp (ρ.codRestrict _ hmemR) with ha'
  have hθ' : ∀ (g : ↥(stab (puAmalgam h.le) (baseA _))) (s : S),
      Multiplicative.toAdd (θ (ρ g s)) = MSP.mat (a' g) *ᵥ Multiplicative.toAdd (θ s) :=
    fun g s => hθ (ρ.codRestrict _ hmemR g) s
  set K := S38E.IsIrrRep.imL L (ρ.comp (S512N.eM h.le)) with hKdef
  have hKX : K ≤ (ρ.comp (S512N.eM h.le)).range := S38E.IsIrrRep.imL_le
  have hφi : Function.Injective φ := S512N.injective_of_coord hθ
  have hcK : Nat.card K = 360 := by
    rw [← Nat.card_congr (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ).toEquiv]
    show Nat.card ↥(alternatingGroup (Fin 6)) = 360
    rw [H13.card_alternatingGroup_fin 6 (by norm_num)]
    decide
  have hcSp : Nat.card (MSP.Sp4 (ZMod 2)) = 720 := by
    rw [← Nat.card_congr (B5FinSp.theta (RingEquiv.refl (ZMod 2))).toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hcKφ : Nat.card ((K.subgroupOf (ρ.comp (S512N.eM h.le)).range).map φ) = 360 := by
    rw [Subgroup.card_map_of_injective hφi, ← hcK]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv
  have hidx : ((K.subgroupOf (ρ.comp (S512N.eM h.le)).range).map φ).index = 2 := by
    have h1 := ((K.subgroupOf (ρ.comp (S512N.eM h.le)).range).map φ).card_mul_index
    rw [hcKφ, hcSp] at h1
    omega
  have hord3 : ∀ g : MSP.Sp4 (ZMod 2), g ^ 3 = 1 → ∃ l : ↥(stab (puAmalgam h.le) (baseA _)),
      (l : (puAmalgam h.le).Universal) ∈ puTrans h.le L (baseA _) ∧ a' l = g := by
    intro g hg
    have hgK : g ∈ (K.subgroupOf (ρ.comp (S512N.eM h.le)).range).map φ := by
      have e : g = (g ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hg, one_mul]
      rw [e]
      exact Subgroup.sq_mem_of_index_two hidx _
    obtain ⟨y, hy, rfl⟩ := hgK
    obtain ⟨m, hm, hmy⟩ := Subgroup.mem_subgroupOf.1 hy
    refine ⟨S512N.eM h.le m, ?_, ?_⟩
    · rw [S5B.puTrans_L_baseA h, S512N.coe_eM]
      exact (S512N.ofA_mem_imM_iff h.le m).2 (Subgroup.mem_subgroupOf.1 hm)
    · show φ (ρ.codRestrict _ hmemR (S512N.eM h.le m)) = φ y
      congr 1
      exact Subtype.ext hmy
  obtain ⟨βv, hβv⟩ := exists_setup_of h hs hirr hθ' hord3 hV₀ hV₀n hV₀B
  exact ⟨a', βv, hβv⟩

theorem false_of_coreQ2 (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) (h32 : S32) (h52 : S52) (h53 : S53) (h54 : S54) (h55 : S55)
    (h56 : S56) (h : PUHyp M T L) (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a) (hk1 : k = 1)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    {μ : Vtx (puAmalgam h.le)} {y : (puAmalgam h.le).Universal}
    (hy : y ∈ stab _ (baseA (puAmalgam h.le))) (hμy : μ = y • geo _ (baseA (puAmalgam h.le)) α' 2)
    (hcμ : IsCritical _ μ (geo _ (baseA (puAmalgam h.le)) α' 2))
    (hbad : 2 ^ k < (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ))
    (hRc : ⁅ZM (puAmalgam h.le) μ, ZM (puAmalgam h.le) (geo _ (baseA (puAmalgam h.le)) α' 2)⁆ ≤
      stabCenter _ (baseA (puAmalgam h.le))) : False := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hk : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
  have hfin := S310.finite_stab_of_isMVtx h hα
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  set γ := geo _ (baseA (puAmalgam h.le)) α' 2 with hγdef
  have hγM : IsMVtx _ γ := isMVtx_geo_two _ hyp hb0 hc
  have hdαγ : (puAmalgam h.le).treeGraph.dist (baseA _) γ = 2 :=
    dist_geo _ (by have := hc.2.1; omega)
  have hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ := by
    rw [← hαβ]
    exact adj_geo _ (by have := hc.2.1; omega)
  have hβα := (adj_baseA_baseB (puAmalgam h.le)).symm
  have hv := S512R.fullVQD56_holds h52 h54 h55 h56 G M T L h hmin hb4 k F _ _ a hd α' hc hαβ l
    hl μ ⟨y, hy, hμy⟩ hcμ hbad hRc
  obtain ⟨l', hl', hTl⟩ := S512R.qv_le_vPre_qLine_core h54 h hmin hb4 hd hc hy hμy hcμ hbad hRc
  obtain ⟨hμM, -, -, -, -, -, -, -, -, -, -, -⟩ := S512T.pair_facts h hb4 hcμ
  obtain ⟨hrel, -⟩ := S512T.bad_indices h hb4 hd hcμ hbad
  have hΛ : (2 ^ k) ^ 2 ≤ (Qv _ γ).relIndex (ZM _ μ) := by
    rw [S512T.relIndex_qv_zm_eq h hb4 hcμ, hrel]
  obtain ⟨g₀, hg₀⟩ := exists_eq_smul_baseA _ hμM
  have hc₀ : IsCritical _ (baseA (puAmalgam h.le)) (g₀⁻¹ • γ) := by
    have := (isCritical_smul _ g₀⁻¹ _ _).2 hcμ
    rwa [hg₀, inv_smul_smul] at this
  have hΛ₀ : (2 ^ k) ^ 2 ≤ (Qv _ (g₀⁻¹ • γ)).relIndex (ZM _ (baseA (puAmalgam h.le))) := by
    have e := S5B.relIndex_qv_zm_smul g₀⁻¹ γ μ
    rw [hg₀, inv_smul_smul] at e
    rw [e, ← hg₀]
    exact hΛ
  have hone := (h52 G M T L h hmin hb k F _ _ a hd (g₀⁻¹ • γ) hc₀).1 hΛ₀
  have hpair := S512R.commutator_nclStab_qv_le h32 h53 h hmin hd hb hl' hTl hv hβα hβγ
  have hV₁Q : S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ) ≤ Qv _ (baseA (puAmalgam h.le)) :=
    S310.nclStab_le_qv h hγM hdαγ hb
  have hV₁c : ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ),
      S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ)⁆ ≤ stabCenter _ (baseA (puAmalgam h.le)) :=
    ((Subgroup.commutator_mono le_rfl hV₁Q).trans hpair).trans inf_le_right
  obtain ⟨hV₁', hcomm, hV₀L⟩ := core_v₁ h hb hc hV₁c
  obtain ⟨-, hst, -, -⟩ := S512T.zm_facts h hb4 hcμ
  have hlow := S512R.relIndex_le_card_commutator h hd hcμ.1 hst
  rw [hrel] at hlow
  have hRV : ⁅S5.uSub h.le L μ, ZM _ γ⁆ ≤ ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ),
      S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ)⁆ := by
    refine Subgroup.commutator_mono ((S5B.uSub_le_zm h.le μ).trans ?_) (S512R.zm_le_nclStab h γ)
    rw [hμy]
    exact S512R.zm_smul_le_nclStab h hy _
  have hAV₁ : stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ) : Set _) :=
    S310.stab_le_normalizer_nclStab _ _ _
  have hAV₀ : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer
      ((⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆ :
        Subgroup _) : Set _) :=
    le_normalizer_commutator hAV₁ (stab_le_normalizer_puTrans h.le hLn _)
  have hV₀V₁ : ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆ ≤
      S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ) :=
    commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L _).trans hAV₁)
  have hV₀o : ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆ ≤
      S5.voSub h.le L (baseA _) :=
    Subgroup.commutator_mono (S512N.nclStab_le_vv h hγM hdαγ.le) le_rfl
  have hV₀st : ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆ ≤
      stab _ (baseA (puAmalgam h.le)) :=
    hV₀o.trans ((voSub_le_vv h).trans ((S310.vv_le_qv_baseA h hb).trans (qv_le_stab _ _)))
  have hV₀'st : ⁅⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆,
      ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆⁆ ≤
      stab _ (baseA (puAmalgam h.le)) := commutator_le_of_le hV₀st hV₀st
  have : Finite ↥⁅⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆,
      ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆⁆ :=
    Finite.of_injective _ (Subgroup.inclusion_injective hV₀'st)
  have hcard := (Subgroup.card_le_of_le (hRV.trans hV₁')).trans' hlow
  have hV₀B : ¬ ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆ ≤
      S5.bSub h.le L (baseA _) := by
    intro hle
    have hZ : ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆ ≤
        ZM _ (baseA (puAmalgam h.le)) := by
      have h1 : ⁅⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆,
          puTrans h.le L (baseA (puAmalgam h.le))⁆ ≤ ZM _ (baseA (puAmalgam h.le)) :=
        Subgroup.commutator_le.2 fun x hx l hl =>
          S310.commutator_mem_zm_of_mem_bSub h hb (hle hx) hl
      rwa [hV₀L] at h1
    have hab : ⁅⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆,
        ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆⁆ = ⊥ := by
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hZ.trans ?_)
      exact (zm_le_centralizer_qv _ hyp hα).trans (Subgroup.centralizer_le (hV₀o.trans
        ((voSub_le_vv h).trans (S310.vv_le_qv_baseA h hb))))
    rw [hab, Subgroup.card_bot] at hcard
    have : 1 < (2 ^ k) ^ 2 := by nlinarith
    omega
  have hsec := secHyp_voSub h hb hv hone.1
  obtain ⟨S, _, p, ρ, hs⟩ := hsec.exists_secMod
  have hirr : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → S512N.IsInv ρ S₁ → S₁ = ⊤ :=
    fun S₁ hne hS₁ => eq_top_of_isInv h hb hone le_rfl hs hne hS₁
  obtain ⟨W, E, δ, hWst, hVW, hEβ, hpairWE, hidx, hlt⟩ :=
    exists_offender h32 h53 h hmin hb4 hd hl' hTl hv hone hc hαβ hy hμy hcμ hbad
  obtain ⟨hρM, hAX, hAel, hA1, hoff⟩ := offender_facts h hd hb hv hl' hTl hsec hs hirr hWst hVW
    hEβ hpairWE hidx (hk.trans hlt)
  have := hsec.finite_S hs
  have hXX : ρ.range ≤ (ρ.comp (S512N.eM h.le)).range := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨m, rfl⟩ := S512N.eM_surjective h.le g
    exact ⟨m, rfl⟩
  have hFF : IsFFModule (ρ.comp (S512N.eM h.le)).range := ⟨_, hAX.trans hXX, hA1, hAel, hoff⟩
  rcases ff_cases_q2 h14 hSQ hT h hd hk1 hρM hFF with hhat | halt
  ·
    have hcen : ∀ v ∈ ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆,
        ∀ w ∈ ⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆,
        ∀ g ∈ stab _ (baseA (puAmalgam h.le)), g * ⁅v, w⁆ = ⁅v, w⁆ * g := fun v hv w hw g hg =>
      S510.commute_of_mem_stabCenter
        (hV₁c (Subgroup.commutator_mem_commutator (hV₀V₁ hv) (hV₀V₁ hw))) hg
    have hbot := commutator_eq_bot_of_hat hs hirr hV₀o hV₀st hAV₀ hV₀B hcomm hcen
      (S38H.HatMod.of_tripleA6Six hρM.sq hhat.1)
      (hXX.trans (S38E.IsIrrRep.range_le_normalizer h)) hAX hAel hA1 hoff
    rw [hbot, Subgroup.card_bot] at hcard
    have : 1 < (2 ^ k) ^ 2 := by nlinarith
    omega
  ·
    obtain ⟨a', βv, hSetup⟩ := exists_setup_alt h hs hirr halt hV₀o hAV₀ hV₀B
    have hD : ⁅⁅⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆,
          puTrans h.le L (baseA (puAmalgam h.le))⁆,
        ⁅⁅S5.nclStab _ (baseA (puAmalgam h.le)) (ZM _ γ), puTrans h.le L (baseA _)⁆,
          puTrans h.le L (baseA (puAmalgam h.le))⁆⁆ ≤
        Subgroup.centralizer (puTrans h.le L (baseA (puAmalgam h.le)) : Set _) := by
      rw [hV₀L]
      intro x hx
      have hx' : x ∈ stabCenter _ (baseA (puAmalgam h.le)) :=
        hV₁c ((Subgroup.commutator_mono hV₀V₁ hV₀V₁) hx)
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact S510.commute_of_mem_stabCenter hx' (puTrans_le_stab h.le L _ hl)
    have hbound := hSetup.card_comm_le (by rw [hV₀L]; exact hcomm) hD (by rw [hV₀L, hV₀L])
    rw [hV₀L, ZMod.card] at hbound
    subst hk1
    norm_num at hcard
    omega

theorem coreQ2_of (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) (h32 : S32) (h52 : S52) (h53 : S53) (h54 : S54) (h55 : S55)
    (h56 : S56) : CoreQ2 :=
  fun _ _ _ _ _ _ h hmin hb4 _ _ _ _ _ hd hk1 _ hc hαβ _ hl _ ⟨_, hy, hμy⟩ hcμ hbad hRc =>
    false_of_coreQ2 h14 hSQ hT h32 h52 h53 h54 h55 h56 h hmin hb4 hd hk1 hc hαβ hl hy hμy hcμ
      hbad hRc

section Holds

open S32

theorem coreQ2_holds
    (h32 : S32) (h52 : S52) (h53 : S53) (h54 : S54) (h55 : S55) (h56 : S56) : CoreQ2 := by
  have halt8 : ∀ (P : Type) [Group P], IsRankTwoLie2Derived (P ⧸ Subgroup.center P) →
      (↥(alternatingGroup (Fin 8)) ≃* P) → False := by
    intro P _ hR e
    have h8 : 4 ≤ Nat.card (Fin 8) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    have hZ : Subgroup.center P = ⊥ :=
      center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot h8)
    have h20 : Nat.card (P ⧸ Subgroup.center P) = 20160 := by
      rw [card_quot_center_eq hZ, ← Nat.card_congr e.toEquiv,
        H13.card_alternatingGroup_fin 8 (by norm_num)]
      decide
    have hE := (CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated
      (P ⧸ Subgroup.center P) (isPSL_three_two_two_of_card hR h20)).2.2 (Fin 8) (by simp)
    exact hE.false ((SmithC27.quotCenterEquivSelf hZ).trans e.symm)
  have hT : TypeFacts :=
    { g2 := fun _ _ _ _ _ _ hF hn e => card_quot_of_equiv_quasithinG2 hF hn e
      g2two := fun _ _ _ _ _ hF e => R3c2.not_isQuasisimple_quasithinG2_two hF e
      g2d := fun _ _ _ _ _ hF e => (card_quot_of_equiv_g2Derived hF e).2
      alt8 := halt8
      sl2 := fun _ _ hq hR _ _ _ _ hF e => false_of_equiv_statedSL_two hq hR hF e
      alt57 := fun _ _ hR _ hm e => false_of_equiv_alt hR hm e
      u33 := fun _ _ _ _ _ hF e => SmithC27.b42TypeU33_of_equiv hF e
      u33aut := fun _ _ _ _ _ hKX hXN hC hP => card_le_of_b42TypeU33 hKX hXN hC hP }
  have hSQ : SQTKQuot := fun _ _ _ _ _ _ hS f hf hQ =>
    H13.A5.sqtkGroup_of_surjective_quasisimple hS f hf hQ
  exact coreQ2_of ms14AS_holds hSQ hT h32 h52 h53 h54 h55 h56

theorem core_holds
    (h32 : S32) (h52 : S52) (h53 : S53) (h54 : S54) (h55 : S55) (h56 : S56) : S512T.Core :=
  core_of_coreQ2 h32 h52 h53 h54 h55 h56 (coreQ2_holds h32 h52 h53 h54 h55 h56)

end Holds

end S512L

end CFSG.Quasithin.MS93
