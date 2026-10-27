module

public import CFSG.Quasithin.Vol2.Ch11SecSI3
public import CFSG.Quasithin.Vol2.Ch11SecSObl
public import CFSG.Quasithin.Vol2.Ch11SecSSym3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

@[expose] def Obl11_1_2StarZK : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I V₁ V₂ X K : Subgroup G),
    StarHyp G T L I V₁ V₂ X K → ⁅quasithinOmegaOneCenter T, K⁆ = ⊥

@[expose] def Obl11_1_2StarSymRole : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I V₁ V₂ X K K₀ I' U₁ U₂ : Subgroup G),
    StarHyp G T L I V₁ V₂ X K → IsK0 T L V₁ K K₀ → ¬ KindSL3 L (fsuV T I) 2 →
    pCoreOf 2 (K₀ ⊔ LOf L V₂ ⊔ X ⊔ T) ≠ ⊥ →
    quasithinIsCComponent (K₀ ⊔ LOf L V₂) (K₀ ⊔ LOf L V₂ ⊔ X ⊔ T) →
    T ≤ Subgroup.normalizer ((K₀ ⊔ LOf L V₂ : Subgroup G) : Set G) →
    X ≤ K₀ ⊔ LOf L V₂ → Shape11 (K₀ ⊔ LOf L V₂) 2 →
    ¬ IsPSL 3 2 2 (↥(K₀ ⊔ LOf L V₂) ⧸ CFSG.pCore 2 ↥(K₀ ⊔ LOf L V₂)) →
    Hyp11 G T (K₀ ⊔ LOf L V₂) I' 2 →
    IsVi T (K₀ ⊔ LOf L V₂) I' 2 1 U₁ → IsVi T (K₀ ⊔ LOf L V₂) I' 2 2 U₂ →
    ⁅quasithinOmegaOneCenter T, K⁆ = ⊥ →
    fsuV T I' ⊓ Subgroup.centralizer ((K₀ ⊔ LOf L V₂ : Subgroup G) : Set G) = ⊥ →
      LOf (K₀ ⊔ LOf L V₂) U₁ = K₀ ∧ LOf (K₀ ⊔ LOf L V₂) U₂ = LOf L V₂ ∧
      IsCartanX T (K₀ ⊔ LOf L V₂) X ∧ K ≤ Subgroup.centralizer (U₁ : Set G) ∧
      quasithinIsCComponent K (Subgroup.normalizer (U₁ : Set G))

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_omegaOneCenter_ne_bot' [Finite G] {T V : Subgroup G} (hT : IsPGroup 2 T)
    (hV : IsElemAbelian 2 V) (hVT : V ≤ T) (hN : T ≤ Subgroup.normalizer (V : Set G))
    (hV1 : V ≠ ⊥) : V ⊓ quasithinOmegaOneCenter T ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥T := hT.isNilpotent
  have hnorm : (V.subgroupOf T).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hVT]
    exact hN
  have hne : V.subgroupOf T ≠ ⊥ := by
    intro h0
    apply hV1
    rw [eq_bot_iff]
    intro v hv
    have : (⟨v, hVT hv⟩ : ↥T) ∈ V.subgroupOf T := hv
    rw [h0, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  intro h0
  apply hx1
  have hxV : ((x : ↥T) : G) ∈ V := (Subgroup.mem_inf.mp x.2).1
  have hxZ : (x : ↥T) ∈ Subgroup.center ↥T := (Subgroup.mem_inf.mp x.2).2
  have hmem : ((x : ↥T) : G) ∈ quasithinOmegaOneCenter T := by
    refine Subgroup.subset_closure ⟨⟨(x : ↥T).2, ?_⟩, hV.2 _ hxV⟩
    show ((x : ↥T) : G) ∈ Subgroup.centralizer (T : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have := Subgroup.mem_center_iff.mp hxZ ⟨t, ht⟩
    exact congrArg Subtype.val this
  have : ((x : ↥T) : G) ∈ (⊥ : Subgroup G) := h0 ▸ ⟨hxV, hmem⟩
  rw [Subgroup.mem_bot] at this
  exact Subtype.ext (Subtype.ext this)

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G}

theorem fsuV_inf_centralizer_eq_bot (hPG : FactParabGen) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) (cL : CartanL L V₁ V₂ X) {J I' : Subgroup G}
    (hJ : Hyp11 G T J I' 2) (hJloc : quasithinIsLocal T J) (hL₂J : LOf L V₂ ≤ J)
    (hZK : ⁅quasithinOmegaOneCenter T, K⁆ = ⊥) :
    fsuV T I' ⊓ Subgroup.centralizer (J : Set G) = ⊥ := by
  by_contra hne
  have hTJ := hJ.normal
  set Z := quasithinOmegaOneCenter T with hZdef
  have hZT : Z ≤ T := (Subgroup.closure_le _).mpr fun z hz => hz.1.1
  have hZC : Z ≤ Subgroup.centralizer (T : Set G) := (Subgroup.closure_le _).mpr fun z hz => hz.1.2
  have hVab := isElemAbelian_fsuV hJ
  have hV'ab : IsElemAbelian 2 (fsuV T I' ⊓ Subgroup.centralizer (J : Set G)) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hVab.2 x hx.1⟩
    have := congrArg Subtype.val (hVab.1.is_comm.comm ⟨a, a.2.1⟩ ⟨b, b.2.1⟩)
    simpa using this
  have hV'T : fsuV T I' ⊓ Subgroup.centralizer (J : Set G) ≤ T := inf_le_left.trans (fsuV_le_T hJ)
  have hNC : Subgroup.normalizer (J : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (J : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have hTV' : T ≤ Subgroup.normalizer
      ((fsuV T I' ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨T_le_normalizer_fsuV T I' ht, hNC (hTJ ht)⟩
  have h1 := inf_omegaOneCenter_ne_bot' h.sylow.1 hV'ab hV'T hTV' hne
  set P := Z ⊓ Subgroup.centralizer (J : Set G) with hPdef
  have hP1 : P ≠ ⊥ := fun hb => h1 (eq_bot_iff.mpr fun x hx => hb ▸ ⟨hx.2, hx.1.2⟩)
  have hloc : IsTwoLocal (Subgroup.normalizer (P : Set G)) :=
    ⟨P, hP1, h.sylow.1.to_le (inf_le_left.trans hZT), rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hCN : Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hJN : J ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.le_centralizer_iff.mp inf_le_right).trans hCN
  have hTN : T ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.le_centralizer_iff.mp (inf_le_left.trans hZC)).trans hCN
  have hKN : K ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.le_centralizer_iff.mp (inf_le_left.trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZK))).trans hCN
  have hmax : quasithinIsMaximalLocal T J := hJ.fsu.maximal
  have hU := lemma_1_2_7_three h.hyp.fsu.qtke h.hyp.fsu.simple h.hyp.fsu.nonabelian h37 h38 h39
    h.sylow hmax
  have hcc : conjClosure J T = J :=
    le_antisymm
      (conjClosure_le fun _ ht l hl => (Subgroup.mem_normalizer_iff.1 (hTJ ht) l).1 hl)
      (le_conjClosure J T)
  rw [hcc] at hU
  have hM := hU.2 M' ⟨hM', (sup_le hJN hTN).trans hle⟩
  refine h.not_le_normalizer_of_isLocal hPG h37 h38 h39 hN h1102 cL hJloc hTJ hL₂J ?_
  rw [← hM]
  exact hKN.trans hle

theorem normalizer_le_of_cComp (h : StarHyp G T L I V₁ V₂ X K) {U K₀ : Subgroup G}
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hTU : T ≤ Subgroup.normalizer (U : Set G)) (hK₀ : quasithinIsLocal T K₀) (hK₀K : K₀ ≤ K)
    (hTK₀ : T ≤ Subgroup.normalizer (K₀ : Set G))
    (hKc : quasithinIsCComponent K (Subgroup.normalizer (U : Set G))) :
    Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : pCoreOf 2 (Subgroup.normalizer (U : Set G)) ≠ ⊥ := by
    intro hb
    apply hU
    refine eq_bot_iff.mpr ?_
    rw [← hb]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hU2
  have hS := isSylowTwoOf_of_quasithinIsSylowTwo h.sylow hTU
  have hnorm := CFSG.Quasithin.lemma_1_2_4_normal h.hyp.fsu.qtke h.hyp.fsu.simple
    h.hyp.fsu.nonabelian h37 h38 hH hS (mem_lFamily_iff'.mpr hK₀.2.1) hK₀K hKc hTK₀
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hKc)).mp hnorm

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
