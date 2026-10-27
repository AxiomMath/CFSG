module

public import CFSG.Quasithin.Vol2.Ch3Sec3Comp
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.Vol2.Ch3Sec3Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative Pointwise commutatorElement

@[expose] def RankTwoA38Types : Prop :=
  ∀ (X : Type) [Group X] [Finite X], A38Types X → IsRankTwoLie2Derived (X ⧸ Subgroup.center X) →
    IsPSL 3 2 1 X

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

namespace Setup331

theorem isLocal (h : Setup331 G T M L) : quasithinIsLocal T L := h.Lmax.1

theorem mem_cComp (h : Setup331 G T M L) : L ∈ cComp (L ⊔ T) := cComp_of_isLocal h.Lmax.1

theorem isSylowTwoOf (h : Setup331 G T M L) : IsSylowTwoOf T (L ⊔ T) :=
  ⟨le_sup_right, h.Lmax.1.1, h.Lmax.1.2.2.1⟩

theorem pCoreOf_ne_bot (h : Setup331 G T M L) : pCoreOf 2 (L ⊔ T) ≠ ⊥ := h.Lmax.1.2.2.2

theorem T_ne_bot (h : Setup331 G T M L) : T ≠ ⊥ := by
  intro hT
  apply h.pCoreOf_ne_bot
  exact le_bot_iff.mp (hT ▸ pCoreOf_le_of_isSylowTwoOf h.isSylowTwoOf)

theorem perfect (h : Setup331 G T M L) : ⁅L, L⁆ = L := perfect_of_mem_cComp h.mem_cComp

theorem quasisimple_open (h : Setup331 G T M L) :
    CFSG.Open.IsQuasisimple (↥L ⧸ CFSG.Open.pCore 2 ↥L) :=
  B1Red.isQuasisimple_to_open (CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (BlueprintB2.pCore_eq_open_pCore 2 ↥L)) h.Lq)

theorem charTwo (h : Setup331 G T M L) : CharTwo (L ⊔ T) := by
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
  have hH : InH (S : Subgroup G) (L ⊔ T) := ⟨hS ▸ le_sup_right, h.pCoreOf_ne_bot⟩
  exact charTwo_of_inH h.qtke.2.1 S hH

theorem isUniqueM_normalizer
    (h : Setup331 G T M L) (h38 : A38ForSQTKCat)
    (h39 : A39ForSQTKCat) : IsUniqueM (L ⊔ T) (Subgroup.normalizer (mPlus L T : Set G)) :=
  lemma_1_2_7_three h.qtke h.simple h.nonabelian
    (a37ForSQTK_of_cat CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved)
    (a38ForSQTK_of_cat h38) (a39ForSQTK_of_cat h39) h.sylow h.Lmax

theorem eq_normalizer
    (h : Setup331 G T M L) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    M = Subgroup.normalizer (mPlus L T : Set G) :=
  (h.isUniqueM_normalizer h38 h39).2 M ⟨h.maxM, sup_le h.LM h.TM⟩

theorem isUniqueM
    (h : Setup331 G T M L) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    IsUniqueM (L ⊔ T) M := by
  rw [h.eq_normalizer h38 h39]
  exact h.isUniqueM_normalizer h38 h39

theorem le_of_pCoreOf_ne_bot
    (h : Setup331 G T M L) (h38 : A38ForSQTKCat)
    (h39 : A39ForSQTKCat) {X : Subgroup G} (hX : L ⊔ T ≤ X) (hO : pCoreOf 2 X ≠ ⊥) : X ≤ M := by
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hO
  have := (h.isUniqueM h38 h39).2 M' ⟨hM'.1, hX.trans hM'.2⟩
  exact this ▸ hM'.2

theorem normalizer_le
    (h : Setup331 G T M L) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    {P : Subgroup G} (hP : P ≠ ⊥) (hP2 : IsPGroup 2 P)
    (hLT : L ⊔ T ≤ Subgroup.normalizer (P : Set G)) : Subgroup.normalizer (P : Set G) ≤ M := by
  have hloc : IsTwoLocal (Subgroup.normalizer (P : Set G)) := ⟨P, hP, hP2, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have := (h.isUniqueM h38 h39).2 M' ⟨hM', hLT.trans hle⟩
  exact this ▸ hle

theorem pCoreOf_ne_bot_of_normal (h : Setup331 G T M L) {X : Subgroup G} (hX : X ≠ ⊥)
    (hXH : X ≤ L ⊔ T) (hN : L ⊔ T ≤ Subgroup.normalizer (X : Set G)) : pCoreOf 2 X ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (L ⊔ T) with hR
  have hRN : L ⊔ T ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have hY : X ⊓ R ≠ ⊥ := by
    intro hbot
    apply hX
    rw [eq_bot_iff]
    intro x hx
    have hxC : x ∈ (L ⊔ T) ⊓ Subgroup.centralizer (R : Set G) := by
      refine ⟨hXH hx, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
      have hc : ⁅x, r⁆ ∈ X ⊓ R := by
        refine ⟨?_, ?_⟩
        · rw [commutatorElement_def]
          have := (Subgroup.mem_normalizer_iff.mp
            (hN (CFSG.LieType.BorelTits.pCoreOf_le 2 (L ⊔ T) hr)) x⁻¹).mp (X.inv_mem hx)
          simpa [mul_assoc] using X.mul_mem hx this
        · rw [commutatorElement_def]
          have := (Subgroup.mem_normalizer_iff.mp (hRN (hXH hx)) r).mp hr
          exact R.mul_mem this (R.inv_mem hr)
      rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc.symm
    have hxR := h.charTwo hxC
    have : x ∈ X ⊓ R := ⟨hx, hxR⟩
    rwa [hbot] at this
  have hYX : X ⊓ R ≤ pCoreOf 2 X := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)).to_inf_right)
    intro x hx
    exact mem_normalizer_inf (Subgroup.le_normalizer hx) (hRN (hXH hx))
  intro hbot
  exact hY (le_bot_iff.mp (hbot ▸ hYX))

end Setup331

theorem stmt3_3_5_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : Stmt3_3_5 := by
  intro G _ _ T M L h
  rw [conjClosure_sup_eq]
  refine ⟨h.eq_normalizer h38 h39, h.isUniqueM h38 h39, ?_⟩
  exact (quasithinGenFitting_eq_pCoreOf_iff (L ⊔ T) 2).mpr h.charTwo

namespace Hyp331

theorem not_D_le (h : Hyp331 G T M L D) : ¬ D ≤ M := fun hD =>
  h.counter (h.ND ▸ sup_le h.TM hD)

theorem not_le_normalizer
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    {X : Subgroup G} (hX : X ≠ ⊥) (hXH : X ≤ L ⊔ T)
    (hN : L ⊔ T ≤ Subgroup.normalizer (X : Set G)) : ¬ D ≤ Subgroup.normalizer (X : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hD
  have hO := h.toSetup331.pCoreOf_ne_bot_of_normal hX hXH hN
  have hle : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
  have hM := h.toSetup331.normalizer_le h38 h39 hO (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
    (hN.trans hle)
  exact h.not_D_le (hD.trans (hle.trans hM))

theorem pCoreOf_sup_eq_bot
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    pCoreOf 2 (L ⊔ T ⊔ D) = ⊥ := by
  by_contra hne
  exact h.not_D_le (le_sup_right.trans (h.toSetup331.le_of_pCoreOf_ne_bot h38 h39 le_sup_left hne))

omit [Finite G] in
theorem normalizer_le_normalizer_of_characteristic {C : Subgroup G} (hCT : C ≤ T)
    (hchar : (C.subgroupOf T).Characteristic) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  have := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (C.subgroupOf T)
  rwa [Subgroup.map_subgroupOf_eq_of_le hCT] at this

theorem not_le_normalizer_of_characteristic
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat)
    (h39 : A39ForSQTKCat) {C : Subgroup G} (hCT : C ≤ T) (hC : C ≠ ⊥)
    (hchar : (C.subgroupOf T).Characteristic) :
    ¬ L ⊔ T ≤ Subgroup.normalizer (C : Set G) := fun hN =>
  h.not_le_normalizer h38 h39 hC (hCT.trans le_sup_right) hN
    (h.DN.trans (normalizer_le_normalizer_of_characteristic hCT hchar))

theorem le_normalizer_of_rankTwo
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat)
    (hR : RankTwoA38Types)
    (hr : IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)))
    (hn : ¬ IsPSL 3 2 1 (↥L ⧸ CFSG.pCore 2 ↥L)) : T ≤ Subgroup.normalizer (L : Set G) := by
  rcases lemma_1_2_1_three h.qtke h.simple h.nonabelian
      (a37ForSQTK_of_cat CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved)
      (a38ForSQTK_of_cat h38) h.toSetup331.pCoreOf_ne_bot h.toSetup331.mem_cComp with
    hL | ⟨-, hA⟩
  · exact le_sup_right.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hL)
  · exact absurd (hR _ hA hr) hn

theorem isMSPair
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hr : IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)))
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) : IsMSPair (L ⊔ T) T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := h.toSetup331.isSylowTwoOf
  refine ⟨⟨sqtkGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian h.toSetup331.pCoreOf_ne_bot,
    h.toSetup331.charTwo, L, h.toSetup331.mem_cComp,
    Subgroup.coe_mul_of_right_le_normalizer_left L T hTL, hr⟩, Or.inl ⟨T, ?_, hS.2.2, ?_⟩,
    fun C hCT hC hchar => h.not_le_normalizer_of_characteristic h38 h39 hCT hC hchar⟩
  · refine lt_of_le_of_ne le_sup_right fun hT => ?_
    have hLT : L ≤ T := hT ▸ le_sup_left
    have hsol : Group.IsSolvable ↥T := by
      have := hS.2.1.isNilpotent
      infer_instance
    exact not_isSolvable_of_mem_cComp h.toSetup331.mem_cComp
      (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLT)
        (Subgroup.inclusion_injective hLT))
  · exact (F6.pCoreOf_eq_self_of_isPGroup hS.2.1).symm

end Hyp331

theorem stmt3_3_6_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (hR : RankTwoA38Types) :
    Stmt3_3_6 := by
  intro G _ _ T M L D h
  rw [conjClosure_sup_eq]
  refine ⟨h.not_D_le, ⟨h.pCoreOf_sup_eq_bot h38 h39, fun X hX hXH hN =>
    h.not_le_normalizer h38 h39 hX hXH hN⟩, fun C hCT hC hchar =>
    h.not_le_normalizer_of_characteristic h38 h39 hCT hC hchar, fun hr =>
    ⟨h.le_normalizer_of_rankTwo h38 hR hr, h.isMSPair h38 h39 hr⟩⟩

namespace Hyp331

omit [Finite G] in
theorem le_normalizer_vPlus (L T : Subgroup G) :
    T ≤ Subgroup.normalizer (vPlus L T : Set G) := by
  have hTM := le_normalizer_conjClosure_right L T
  have hTZ : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T
  have key : ∀ t ∈ T, ∀ x ∈ vPlus L T, t * x * t⁻¹ ∈ vPlus L T := by
    intro t ht x hx
    have hle : (vPlus L T).map (MulAut.conj t).toMonoidHom ≤ vPlus L T := by
      unfold vPlus conjClosure
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨m, hm, z, hz, rfl⟩, rfl⟩
      have hm' : t * m * t⁻¹ ∈ conjClosure L T :=
        (Subgroup.mem_normalizer_iff.mp (hTM ht) m).mp hm
      have hz' : t * z * t⁻¹ = z := by
        have := Subgroup.mem_centralizer_iff.mp (hTZ ht) z hz
        rw [← this]; group
      have htz' : t⁻¹ * z * t = z := by
        calc t⁻¹ * z * t = t⁻¹ * (t * z * t⁻¹) * t := by rw [hz']
          _ = z := by group
      refine Subgroup.subset_closure ⟨t * m * t⁻¹, hm', z, hz, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc t * m * t⁻¹ * z * (t * m * t⁻¹)⁻¹ = t * m * (t⁻¹ * z * t) * m⁻¹ * t⁻¹ := by group
        _ = t * m * z * m⁻¹ * t⁻¹ := by rw [htz']
        _ = t * (m * z * m⁻¹) * t⁻¹ := by group
    exact hle ⟨x, hx, rfl⟩
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key t ht x
  · intro hx
    have := key t⁻¹ (T.inv_mem ht) _ hx
    simpa [mul_assoc] using this

omit [Finite G] in
theorem vPlus_eq (L T : Subgroup G) :
    vPlus L T = conjClosure (quasithinOmegaOneCenter T) (L ⊔ T) := by
  refine le_antisymm (conjClosure_mono le_rfl ?_) (conjClosure_le fun x hx z hz => ?_)
  · rw [← conjClosure_sup_eq]
    exact le_sup_left
  · have hN : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := by
      rw [← conjClosure_sup_eq]
      exact sup_le (le_normalizer_conjClosure _ _) (le_normalizer_vPlus L T)
    exact (Subgroup.mem_normalizer_iff.mp (hN hx) z).mp (le_conjClosure _ _ hz)

theorem vPlus_reduced (h : Setup331 G T M L) :
    vPlus L T ≤ pCoreOf 2 (L ⊔ T) ⊓ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) ∧
      IsElemAbelian 2 (vPlus L T) ∧ IsTwoReducedIn (L ⊔ T) (vPlus L T) := by
  rw [vPlus_eq]
  exact conjClosure_isTwoReducedIn_of_charTwo h.isSylowTwoOf h.charTwo le_rfl

theorem not_L_le_centralizer
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    ¬ L ≤ Subgroup.centralizer (vPlus L T : Set G) := by
  intro hL
  set Z := quasithinOmegaOneCenter T with hZ
  have hTV := le_normalizer_vPlus L T
  have hM : conjClosure L T ≤ Subgroup.centralizer (vPlus L T : Set G) := by
    refine conjClosure_le fun t ht l hl => ?_
    exact (Subgroup.mem_normalizer_iff.mp
      (B2F.normalizer_le_normalizer_centralizer (vPlus L T) (hTV ht)) l).mp (hL hl)
  have hZV : Z ≤ vPlus L T := le_conjClosure _ _
  have hMZ : conjClosure L T ≤ Subgroup.centralizer (Z : Set G) :=
    hM.trans (Subgroup.centralizer_le hZV)
  have hZT : Z ≤ T := (B2F.omegaOneCenter_le_inf_centralizer T).trans inf_le_left
  have hZ1 : Z ≠ ⊥ := quasithinOmegaOneCenter_ne_bot h.sylow.1 h.toSetup331.T_ne_bot
  apply h.not_le_normalizer_of_characteristic h38 h39 hZT hZ1
    (CFSG.QuasithinUnique.L246C127.characteristic_omegaOneCenter T)
  rw [← conjClosure_sup_eq]
  refine sup_le (hMZ.trans (Subgroup.centralizer_le_normalizer _)) ?_
  exact (CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T).trans
    (Subgroup.centralizer_le_normalizer _)

theorem centralizer_vPlus
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    ⁅conjClosure L T, (L ⊔ T) ⊓ Subgroup.centralizer (vPlus L T : Set G)⁆ ≤
        pCoreOf 2 (L ⊔ T) ∧
      T ⊓ Subgroup.centralizer (vPlus L T : Set G) = pCoreOf 2 (L ⊔ T) ∧
      (L ⊔ T) ⊓ Subgroup.centralizer (vPlus L T : Set G) ≤ oTwoPhi (L ⊔ T) :=
  centralizer_reduced_of_cComp h.toSetup331.mem_cComp h.toSetup331.quasisimple_open
    h.toSetup331.isSylowTwoOf (vPlus_reduced h.toSetup331).2.2 (h.not_L_le_centralizer h38 h39)

theorem not_thompsonJ_le
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (vPlus L T : Set G) := by
  intro hJ
  have hCT := (h.centralizer_vPlus h38 h39).2.1
  have hJR : thompsonJ T ≤ pCoreOf 2 (L ⊔ T) := by
    rw [← hCT]
    exact le_inf (C1GN.thompsonJ_le T) hJ
  have hRT : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have heq : thompsonJ (pCoreOf 2 (L ⊔ T)) = thompsonJ T := B6.thompsonJ_eq_of_le hJR hRT
  have hN : L ⊔ T ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    rw [← heq]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)).trans
      (normalizer_le_normalizer_thompsonJ _)
  exact h.not_le_normalizer_of_characteristic h38 h39 (C1GN.thompsonJ_le T)
    (CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot h.sylow.1 h.toSetup331.T_ne_bot)
    (CFSG.QuasithinUnique.Setup.characteristic_thompsonJ T) hN

theorem isFFModule
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    ∃ _ : IsMulCommutative ↥(vPlus L T),
      IsFFModule (V := ↥(vPlus L T)) (autOn (L ⊔ T) (vPlus L T)) := by
  have hJ := h.not_thompsonJ_le h38 h39
  rw [vPlus_eq] at hJ ⊢
  obtain ⟨hU, hcase⟩ := B2_15 h.toSetup331.charTwo h.toSetup331.isSylowTwoOf
  rcases hcase with ⟨-, hFF, -⟩ | ⟨hJ', -⟩
  · exact ⟨⟨⟨fun a b => Subtype.ext (by
      have := hU.1
      exact setLike_mul_comm a.2 b.2)⟩⟩, hFF⟩
  · exact absurd hJ' hJ

theorem vPlus_decomp (h : Hyp331 G T M L D) :
    ⁅vPlus L T, mPlus L T⁆ = ⁅quasithinOmegaOneCenter T, mPlus L T⁆ ∧
      vPlus L T = ⁅vPlus L T, mPlus L T⁆ ⊔
        quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (mPlus L T : Set G) := by
  set Z := quasithinOmegaOneCenter T with hZ
  set Mp := mPlus L T with hMp
  set V := vPlus L T with hV
  set W₀ := ⁅Z, Mp⁆ with hW₀
  have hred := vPlus_reduced h.toSetup331
  have hVe : IsElemAbelian 2 V := hred.2.1
  have hZV : Z ≤ V := le_conjClosure _ _
  have hZW₀ : Z ≤ Subgroup.normalizer (W₀ : Set G) := Subgroup.normalizer_commutator_ge_left _ _
  have hMW₀ : Mp ≤ Subgroup.normalizer (W₀ : Set G) := Subgroup.normalizer_commutator_ge_right _ _
  have hVZW : V ≤ Z ⊔ W₀ := by
    refine conjClosure_le fun m hm z hz => ?_
    have e : m * z * m⁻¹ = ⁅z, m⁆⁻¹ * z := by simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right
      (W₀.inv_mem (Subgroup.commutator_mem_commutator hz hm))) (Subgroup.mem_sup_left hz)
  have h1 : ⁅V, Mp⁆ = W₀ := by
    refine le_antisymm ?_ (Subgroup.commutator_mono hZV le_rfl)
    calc ⁅V, Mp⁆ ≤ ⁅Z ⊔ W₀, Mp⁆ := Subgroup.commutator_mono hVZW le_rfl
      _ ≤ ⁅Z, Mp⁆ ⊔ W₀ := commutator_sup_le_of_le_normalizer hZW₀ hMW₀
      _ = W₀ := sup_idem _
  refine ⟨h1, ?_⟩
  set W := ⁅V, Mp⁆ with hW
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_normalizer_vPlus L T
  have hMV : Mp ≤ Subgroup.normalizer (V : Set G) := le_normalizer_conjClosure _ _
  have hWV : W ≤ V := commutator_le_left_of_le_normalizer hMV
  have hTW : T ≤ Subgroup.normalizer (W : Set G) := fun t ht =>
    mem_normalizer_commutator (hTV ht) (le_normalizer_conjClosure_right L T ht)
  have hMW : Mp ≤ Subgroup.normalizer (W : Set G) := Subgroup.normalizer_commutator_ge_right _ _
  have hTZ : ∀ t ∈ T, ∀ z ∈ Z, t * z = z * t := fun t ht z hz =>
    (Subgroup.mem_centralizer_iff.mp
      (CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T ht) z hz).symm
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
    have := hVe.1
    exact setLike_mul_comm ha hb
  have hVZW' : ∀ v ∈ V, ∃ z ∈ Z, ∃ w ∈ W, v = z * w := by
    intro v hv
    have hv' : v ∈ (Z : Set G) * (W : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Z W
        (fun z hz => (hZV hz) |> fun hzV => by
          rw [Subgroup.mem_normalizer_iff]
          intro w
          constructor
          · intro hw
            have := hVcomm z hzV w (hWV hw)
            rw [this]; simpa using hw
          · intro hw
            have hw' : z * w * z⁻¹ ∈ V := hWV hw
            have hwV : w ∈ V := by
              have := V.mul_mem (V.mul_mem (V.inv_mem hzV) hw') hzV
              simpa [mul_assoc] using this
            have := hVcomm z hzV w hwV
            rw [this] at hw; simpa using hw)]
      rw [← h1] at hVZW
      exact hVZW hv
    obtain ⟨z, hz, w, hw, rfl⟩ := hv'
    exact ⟨z, hz, w, hw, rfl⟩
  have hHW : ∀ x ∈ L ⊔ T, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ W := by
    intro x hx v hv
    rw [← conjClosure_sup_eq] at hx
    have hx' : x ∈ (Mp : Set G) * (T : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Mp T
        (le_normalizer_conjClosure_right L T)]
      exact hx
    obtain ⟨m, hm, t, ht, rfl⟩ := hx'
    have htv : t * v * t⁻¹ * v⁻¹ ∈ W := by
      obtain ⟨z, hz, w, hw, rfl⟩ := hVZW' v hv
      have htw : t * w * t⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hTW ht) w).mp hw
      have htz : t * z * t⁻¹ = z := by rw [hTZ t ht z hz]; group
      have hzV := hZV hz
      have hwV := hWV hw
      have htwV := hWV htw
      have e : t * (z * w) * t⁻¹ * (z * w)⁻¹ = (t * w * t⁻¹) * w⁻¹ := by
        calc t * (z * w) * t⁻¹ * (z * w)⁻¹
            = (t * z * t⁻¹) * ((t * w * t⁻¹) * w⁻¹) * z⁻¹ := by group
          _ = z * ((t * w * t⁻¹) * w⁻¹) * z⁻¹ := by rw [htz]
          _ = ((t * w * t⁻¹) * w⁻¹) * z * z⁻¹ := by
            rw [hVcomm z hzV _ (V.mul_mem htwV (V.inv_mem hwV))]
          _ = (t * w * t⁻¹) * w⁻¹ := by group
      rw [e]
      exact W.mul_mem htw (W.inv_mem hw)
    have hmv : m * v * m⁻¹ * v⁻¹ ∈ W := by
      have e : m * v * m⁻¹ * v⁻¹ = ⁅v, m⁆⁻¹ := by simp only [commutatorElement_def]; group
      rw [e]
      exact W.inv_mem (Subgroup.commutator_mem_commutator hv hm)
    have e : m * t * v * (m * t)⁻¹ * v⁻¹ =
        (m * (t * v * t⁻¹ * v⁻¹) * m⁻¹) * (m * v * m⁻¹ * v⁻¹) := by group
    rw [e]
    exact W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hMW hm) _).mp htv) hmv
  refine le_antisymm (fun v hv => ?_) (sup_le hWV (inf_le_left.trans hZV))
  obtain ⟨z, hz, w, hw, rfl⟩ := hVZW' v hv
  obtain ⟨c, hcV, hcH, hcz⟩ := exists_centralizer_mem_coset h.toSetup331.isSylowTwoOf.2.2 hVe
    hred.2.2.2.1 hHW (hZV hz) (fun t ht => hTZ t ht z hz)
  have hcZ : c ∈ Z ⊓ Subgroup.centralizer (Mp : Set G) := by
    refine ⟨Subgroup.subset_closure ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · have hVT : V ≤ T := hred.1.trans (inf_le_left.trans
        (pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf))
      exact hVT hcV
    · show c ∈ Subgroup.centralizer (T : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have := hcH t (Subgroup.mem_sup_right ht)
      calc t * c = t * c * t⁻¹ * t := by group
        _ = c * t := by rw [this]
    · exact hVe.2 c hcV
    · show c ∈ Subgroup.centralizer (Mp : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have hmH : m ∈ L ⊔ T := by
        rw [← conjClosure_sup_eq]
        exact Subgroup.mem_sup_left hm
      have := hcH m hmH
      calc m * c = m * c * m⁻¹ * m := by group
        _ = c * m := by rw [this]
  have hw' : c⁻¹ * z * w ∈ W := by
    have h2 : c⁻¹ * z = (c * z⁻¹)⁻¹ := by
      rw [hVcomm c⁻¹ (V.inv_mem hcV) z (hZV hz)]
      group
    rw [h2]
    exact W.mul_mem (W.inv_mem hcz) hw
  have e : z * w = (c⁻¹ * z * w) * c := by
    rw [hVcomm (c⁻¹ * z * w) (V.mul_mem (V.mul_mem (V.inv_mem hcV) (hZV hz)) (hWV hw)) c hcV]
    group
  rw [e]
  exact Subgroup.mul_mem_sup hw' hcZ

end Hyp331

theorem stmt3_3_7_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : Stmt3_3_7 := by
  intro G _ _ T M L D h
  have hred := (Hyp331.vPlus_reduced h.toSetup331).2.2
  have hC := h.centralizer_vPlus h38 h39
  refine ⟨?_, ?_, ?_, h.vPlus_decomp⟩
  · rw [conjClosure_sup_eq]
    exact ⟨hC.2.2, hC.2.1⟩
  · rw [conjClosure_sup_eq]
    exact ⟨h.not_thompsonJ_le h38 h39, h.isFFModule h38 h39⟩
  · rw [conjClosure_sup_eq]
    obtain ⟨hVH, hR⟩ := isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mp hred
    exact ⟨hVH, hR, CFSG.QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred⟩

theorem stmt3_3_9_of : Stmt3_3_9 := by
  intro G _ _ T M L D h
  obtain ⟨-, hdec⟩ := h.vPlus_decomp
  refine le_antisymm (inf_le_inf_left _ (Subgroup.centralizer_le inf_le_left)) ?_
  rintro x ⟨hxM, hxC⟩
  refine ⟨hxM, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  have hzV : z ∈ vPlus L T := le_conjClosure _ _ hz
  rw [hdec] at hzV
  have hzV' : z ∈ ((⁅vPlus L T, mPlus L T⁆ : Subgroup G) : Set G) *
      ((quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (mPlus L T : Set G) : Subgroup G) :
        Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left]
    · exact hzV
    · intro c hc
      exact mem_normalizer_commutator
        (Hyp331.le_normalizer_vPlus L T ((B2F.omegaOneCenter_le_inf_centralizer T hc.1).1))
        (Subgroup.centralizer_le_normalizer _ hc.2)
  obtain ⟨w, hw, c, hc, rfl⟩ := hzV'
  have hwZ : w ∈ quasithinOmegaOneCenter T := by
    have := (quasithinOmegaOneCenter T).mul_mem hz ((quasithinOmegaOneCenter T).inv_mem hc.1)
    simpa using this
  have hxw : x * w = w * x := (Subgroup.mem_centralizer_iff.mp hxC w ⟨hwZ, hw⟩).symm
  have hxc : x * c = c * x := Subgroup.mem_centralizer_iff.mp hc.2 x hxM
  calc (w * c) * x = w * (c * x) := by group
    _ = w * (x * c) := by rw [hxc]
    _ = (w * x) * c := by group
    _ = x * (w * c) := by rw [← hxw]; group

end CFSG.Quasithin.H13
