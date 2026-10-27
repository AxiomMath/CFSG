module

public import CFSG.Quasithin.Vol2.Ch12Sec5Pm
public import CFSG.Quasithin.Vol2.Ch12Sec5KG
public import CFSG.RankThree.PartTwo.Sec18.Components
public import CFSG.LieType.SteinbergBRParabolicResidualImage
public import CFSG.Quasithin.EmptyFaithful.R3c5Gen
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.Quasithin.EmptyFaithful.R3c2List
public import CFSG.Quasithin.EmptyFaithful.S153D25
public import CFSG.Quasithin.EmptyFaithful.S153D43
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec13.Statements
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125
open scoped Pointwise

local notation "SL5" => Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)

namespace S125Cfg

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem relIndex_inf_eq {N T M : Subgroup G} (hTM : T ≤ M)
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) (hM : M ≤ N ⊔ T) :
    (T ⊓ N).relIndex (M ⊓ N) = T.relIndex M := by
  set N' : Subgroup ↥M := (N ⊓ M).subgroupOf M with hN'
  set T' : Subgroup ↥M := T.subgroupOf M with hT'
  have hN'n : N'.Normal := by
    rw [hN', Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro m hm
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hMN hm, Subgroup.le_normalizer hm⟩
  have hsup : T' ⊔ N' = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨m, hm⟩ -
    have hmNT : m ∈ ((N ⊔ T : Subgroup G) : Set G) := hM hm
    rw [Subgroup.coe_mul_of_right_le_normalizer_left N T (hTM.trans hMN)] at hmNT
    obtain ⟨n, hn, t, ht, rfl⟩ := hmNT
    have hnM : n ∈ M := by
      have := M.mul_mem hm (M.inv_mem (hTM ht))
      simpa using this
    have he : (⟨n * t, hm⟩ : ↥M) = ⟨n, hnM⟩ * ⟨t, hTM ht⟩ := rfl
    rw [he]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (show (⟨n, hnM⟩ : ↥M) ∈ N' from ⟨hn, hnM⟩))
      (Subgroup.mem_sup_left (show (⟨t, hTM ht⟩ : ↥M) ∈ T' from ht))
  have h1 := Subgroup.relIndex_sup_right T' N'
  rw [hsup, Subgroup.relIndex_top_right] at h1
  have hc1 := Subgroup.card_mul_index N'
  have hc2 := Subgroup.card_mul_index T'
  have hc3 := Subgroup.relIndex_mul_card (H := N') (K := T')
  have hc4 := Subgroup.relIndex_mul_card (H := T') (K := N')
  rw [inf_comm] at hc4
  have hpos : 0 < Nat.card ↥(N' ⊓ T') := Nat.card_pos
  have hpos' : 0 < N'.relIndex T' := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_mul] at hc3
    exact absurd hc3.symm (Nat.card_pos (α := ↥T')).ne'
  have key : T'.index = T'.relIndex N' := by
    have e1 : Nat.card ↥T' * T'.index = Nat.card ↥N' * N'.relIndex T' := by
      rw [hc2, ← hc1, h1]
    rw [← hc3, ← hc4] at e1
    have e2 : (N'.relIndex T' * Nat.card ↥(N' ⊓ T')) * T'.index =
        (N'.relIndex T' * Nat.card ↥(N' ⊓ T')) * T'.relIndex N' := by
      rw [e1]; ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hpos' hpos) e2
  have hTN : T ⊓ N = T ⊓ (M ⊓ N) := by
    rw [← inf_assoc, inf_eq_left.mpr hTM]
  rw [hTN, Subgroup.inf_relIndex_right, show M ⊓ N = N ⊓ M from inf_comm M N,
    ← Subgroup.relIndex_subgroupOf (inf_le_right : N ⊓ M ≤ M)]
  exact key.symm

theorem mi_perfectResidual_le (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    CFSG.inSubgroup CFSG.perfectResidual (mi T L F.V1) ≤ li L F.V1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.inSubgroup CFSG.perfectResidual (mi T L F.V1) with hR
  have hRp : ⁅R, R⁆ = R := CFSG.RankThree.PartTwo.Sec18.commutator_inSubgroup_perfectResidual _
  have hRM : R ≤ mi T L F.V1 := Subgroup.map_subtype_le _
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hH.hyp.normalizes
  have hLn : (L.subgroupOf (L ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hTL)
  have hsolv : Group.IsSolvable (↥(L ⊔ T) ⧸ L.subgroupOf (L ⊔ T)) := by
    have hp : IsPGroup 2 (↥(L ⊔ T) ⧸ L.subgroupOf (L ⊔ T)) := by
      intro q
      obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective q
      have hx' : x ∈ ((L ⊔ T : Subgroup G) : Set G) := hx
      rw [Subgroup.coe_mul_of_right_le_normalizer_left L T hTL] at hx'
      obtain ⟨l, hl, t, ht, rfl⟩ := hx'
      obtain ⟨k, hk⟩ := hH.hyp.sylow.1 ⟨t, ht⟩
      have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hlt : (⟨l * t, hx⟩ : ↥(L ⊔ T)) =
          ⟨l, (le_sup_left : L ≤ L ⊔ T) hl⟩ * ⟨t, (le_sup_right : T ≤ L ⊔ T) ht⟩ := rfl
      have hl1 : (QuotientGroup.mk (⟨l, (le_sup_left : L ≤ L ⊔ T) hl⟩ : ↥(L ⊔ T)) :
          ↥(L ⊔ T) ⧸ L.subgroupOf (L ⊔ T)) = 1 := by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hl
      refine ⟨k, ?_⟩
      rw [hlt, QuotientGroup.mk_mul, hl1, one_mul, ← QuotientGroup.mk_pow,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have : (((⟨t, (le_sup_right : T ≤ L ⊔ T) ht⟩ : ↥(L ⊔ T)) ^ 2 ^ k : ↥(L ⊔ T)) : G) = 1 := by
        rw [SubgroupClass.coe_pow]
        exact hk'
      rw [this]
      exact L.one_mem
    have := hp.isNilpotent
    infer_instance
  have hRL : R ≤ L := (CFSG.RankThree.PartTwo.Sec18.inSubgroup_perfectResidual_mono
    (inf_le_left : mi T L F.V1 ≤ L ⊔ T)).trans
    (CFSG.RankThree.PartTwo.Sec18.inSubgroup_perfectResidual_le_of_isSolvable le_sup_left hsolv)
  exact CFSG.RankThree.PartTwo.Sec18.le_inSubgroup_perfectResidual hRp
    (le_inf hRL (hRM.trans inf_le_right))

theorem T_le_P (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) : T ≤ F.P := by
  have hf := S125Ex.Facts125.of h1222 hH
  obtain ⟨h1, h3, -, h6⟩ := S125L2G.T_le_V F hf.T_le
  exact le_inf (le_inf (le_inf le_sup_right h1) h3) h6

section Bad

variable {K₁ : Subgroup G}

theorem P_le_sup (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hPK : oTwoUpper F.P ≤ K₁) : F.P ≤ K₁ ⊔ T := by
  have hS : QuasithinUnique.IsSylowTwoOf T F.P :=
    isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow (T_le_P h1222 F hH)
  rw [CFSG.Quasithin.eq_oTwoUpper_sup_of_isSylowTwoOf hS]
  exact sup_le_sup_right hPK T

theorem mi_le_sup' (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hLK : li L F.V1 ≤ K₁) (hPK : oTwoUpper F.P ≤ K₁) :
    mi T L F.V1 ≤ K₁ ⊔ T :=
  (S125Pm.mi_le_sup h1222 F hH).trans (sup_le (P_le_sup h1222 F hH hPK)
    (sup_le (hLK.trans le_sup_left) le_sup_right))

theorem relIndex_mi_inf (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤
      Subgroup.normalizer (K₁ : Set G)) (hLK : li L F.V1 ≤ K₁) (hPK : oTwoUpper F.P ≤ K₁) :
    (T ⊓ K₁).relIndex (mi T L F.V1 ⊓ K₁) = 63 := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hTM : T ≤ mi T L F.V1 := le_inf le_sup_right (S125L2G.T_le_V F hf.T_le).1
  rw [relIndex_inf_eq hTM (inf_le_right.trans hK₁n) (mi_le_sup' h1222 F hH hLK hPK)]
  exact S125Pm.relIndex_mi h1222 F hH

theorem relIndex_P_inf (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤
      Subgroup.normalizer (K₁ : Set G)) (hPK : oTwoUpper F.P ≤ K₁) :
    (T ⊓ K₁).relIndex (F.P ⊓ K₁) = 3 := by
  have hPN : F.P ≤ Subgroup.normalizer (K₁ : Set G) :=
    (inf_le_left.trans (inf_le_left.trans inf_le_right)).trans hK₁n
  rw [relIndex_inf_eq (T_le_P h1222 F hH) hPN (P_le_sup h1222 F hH hPK)]
  exact S125Pm.relIndex_P h1222 F hH

end Bad

section Quot

variable {K₁ : Subgroup G}

@[expose] noncomputable def img (K₁ A : Subgroup G) : Subgroup (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) :=
  (A.subgroupOf K₁).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁))

omit [Finite G] in
theorem img_mono {A B : Subgroup G} (h : A ≤ B) : img K₁ A ≤ img K₁ B :=
  Subgroup.map_mono fun _ hx => h hx

omit [Finite G] in
theorem pCore_le_subgroupOf {A : Subgroup G} (hA : pCoreOf 2 K₁ ≤ A) :
    CFSG.pCore 2 ↥K₁ ≤ A.subgroupOf K₁ := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  apply hA
  exact ⟨x, hx, rfl⟩

omit [Finite G] in
theorem relIndex_img {A B : Subgroup G} (hA : pCoreOf 2 K₁ ≤ A) (hB : pCoreOf 2 K₁ ≤ B) :
    (img K₁ A).relIndex (img K₁ B) = (A ⊓ K₁).relIndex (B ⊓ K₁) := by
  rw [img, img, Subgroup.relIndex_map_map, QuotientGroup.ker_mk',
    sup_eq_left.2 (pCore_le_subgroupOf hA), sup_eq_left.2 (pCore_le_subgroupOf hB),
    ← Subgroup.inf_subgroupOf_right A K₁, ← Subgroup.inf_subgroupOf_right B K₁,
    Subgroup.relIndex_subgroupOf inf_le_right]

omit [Finite G] in
theorem card_img {A B : Subgroup G} (hA : pCoreOf 2 K₁ ≤ A) (hAB : A ≤ B) :
    Nat.card ↥(img K₁ B) = (A ⊓ K₁).relIndex (B ⊓ K₁) * Nat.card ↥(img K₁ A) := by
  have h := Subgroup.relIndex_mul_card (H := img K₁ A) (K := img K₁ B)
  rw [inf_eq_left.2 (img_mono hAB), relIndex_img hA (hA.trans hAB)] at h
  exact h.symm

omit [Finite G] in
theorem mem_of_mk_mem {A : Subgroup G} (hA : pCoreOf 2 K₁ ≤ A) (x : ↥K₁)
    (hx : QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) x ∈ img K₁ A) : (x : G) ∈ A := by
  obtain ⟨y, hy, hyx⟩ := hx
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
  have h1 := pCore_le_subgroupOf hA hyx
  rw [Subgroup.mem_subgroupOf] at h1
  have hy' : (y : G) ∈ A := hy
  have := A.mul_mem hy' h1
  simpa using this

end Quot

section Config

variable {K₁ : Subgroup G}

theorem pCoreOf_le_T (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hKG : K₁ ≤ Subgroup.normalizer (F.V1 : Set G)) : pCoreOf 2 K₁ ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  have hTG₁ : T ≤ Subgroup.normalizer (F.V1 : Set G) := (S125L2G.T_le_V F hf.T_le).1
  have hS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (F.V1 : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow hTG₁
  have h1 : pCoreOf 2 K₁ ≤ pCoreOf 2 (Subgroup.normalizer (F.V1 : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₁).trans hKG)
      (hK₁n.trans (S125Fin.normalizer_le_normalizer_pCoreOf K₁))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
  exact h1.trans (pCoreOf_two_le_of_isSylowTwoOf hS)

theorem isSylow_img (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hKG : K₁ ≤ Subgroup.normalizer (F.V1 : Set G)) :
    QuasithinUnique.IsSylowTwoOf (img K₁ T) ⊤ := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hTG₁ : T ≤ Subgroup.normalizer (F.V1 : Set G) := (S125L2G.T_le_V F hf.T_le).1
  have hS : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (F.V1 : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow hTG₁
  have hSK := CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hS hKG hK₁n
  have h := isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hSK)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁)) (QuotientGroup.mk'_surjective _)
  rwa [Subgroup.inf_subgroupOf_right] at h

theorem config63 (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hKG : K₁ ≤ Subgroup.normalizer (F.V1 : Set G)) (hLK : li L F.V1 ≤ K₁)
    (hPK : oTwoUpper F.P ≤ K₁) :
    S125KG.Config63 (img K₁ T) (img K₁ (mi T L F.V1)) (img K₁ F.P) := by
  have hO := pCoreOf_le_T h1222 F hH hK₁n hKG
  have hTP := T_le_P h1222 F hH
  have hPM : F.P ≤ mi T L F.V1 := inf_le_left.trans inf_le_left
  have hTM := hTP.trans hPM
  refine ⟨img_mono hTP, img_mono hPM, ?_, ?_, ?_⟩
  · rw [card_img hO hTM, relIndex_mi_inf h1222 F hH hK₁n hLK hPK]
  · rw [card_img hO hTP, relIndex_P_inf h1222 F hH hK₁n hPK]
  · intro hD
    have hres : CFSG.inSubgroup CFSG.perfectResidual (img K₁ (mi T L F.V1)) ≤
        img K₁ (li L F.V1) := by
      have e := CFSG.LieType.SteinbergBR.BlockPar.map_perfectResidual_subgroup
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁)) ((mi T L F.V1).subgroupOf K₁)
      change (CFSG.perfectResidual ↥(img K₁ (mi T L F.V1))).map
        (img K₁ (mi T L F.V1)).subtype ≤ _
      rw [show img K₁ (mi T L F.V1) = ((mi T L F.V1).subgroupOf K₁).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K₁)) from rfl, ← e]
      apply Subgroup.map_mono
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      have h1 : (x : G) ∈ (CFSG.inSubgroup CFSG.perfectResidual
          ((mi T L F.V1).subgroupOf K₁)).map K₁.subtype := ⟨x, hx, rfl⟩
      rw [CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective
        K₁.subtype K₁.subtype_injective, Subgroup.subgroupOf_map_subtype] at h1
      exact mi_perfectResidual_le F hH
        (CFSG.RankThree.PartTwo.Sec18.inSubgroup_perfectResidual_mono inf_le_left h1)
    have hD' : img K₁ F.P ≤ img K₁ (li L F.V1 ⊔ T) :=
      hD.trans (sup_le (hres.trans (img_mono le_sup_left)) (img_mono le_sup_right))
    have hPKT : F.P ⊓ K₁ ≤ li L F.V1 ⊔ T := fun x hx =>
      mem_of_mk_mem (hO.trans le_sup_right) ⟨x, hx.2⟩ (hD' ⟨⟨x, hx.2⟩, hx.1, rfl⟩)
    have hSP : QuasithinUnique.IsSylowTwoOf T F.P :=
      isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow hTP
    refine S125Pm.P_not_le h1222 F hH ?_
    rw [CFSG.Quasithin.eq_oTwoUpper_sup_of_isSylowTwoOf hSP]
    exact sup_le ((le_inf (oTwoUpper_le _) hPK).trans hPKT) le_sup_right

end Config

section Alpha

variable {K₁ : Subgroup G}

omit [Finite G] in
theorem oTwoUpper_inf (F : Frame125 T L V) (hPK : oTwoUpper F.P ≤ K₁) :
    oTwoUpper (F.P ⊓ K₁) = oTwoUpper F.P := by
  refine le_antisymm (oTwoUpper_mono inf_le_left) ?_
  rw [oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hx, ho⟩
  exact mem_oTwoUpper_of_odd ⟨hx, hPK (mem_oTwoUpper_of_odd hx ho)⟩ ho

theorem oTwoUpper_img (F : Frame125 T L V) (hPK : oTwoUpper F.P ≤ K₁) :
    oTwoUpper (img K₁ F.P) = img K₁ (oTwoUpper F.P) := by
  rw [img, img, CFSG.Quasithin.oTwoUpper_map]
  congr 1
  have h2 := CFSG.Quasithin.R3c5.map_oTwoUpper_subgroupOf (inf_le_right : F.P ⊓ K₁ ≤ K₁)
  rw [Subgroup.inf_subgroupOf_right, oTwoUpper_inf F hPK] at h2
  rw [← h2, CFSG.Quasithin.map_subtype_subgroupOf']

theorem normalizer_l1_of_alpha (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hKG : K₁ ≤ Subgroup.normalizer (F.V1 : Set G)) (hLK : li L F.V1 ≤ K₁)
    (hPK : oTwoUpper F.P ≤ K₁)
    (hα : Subgroup.normalizer (oTwoUpper (img K₁ F.P) : Set (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) ≤
      img K₁ (mi T L F.V1))
    {g : G} (hg : g ∈ Subgroup.normalizer (F.V1 : Set G))
    (hgP : g ∈ Subgroup.normalizer (oTwoUpper F.P : Set G)) :
    g ∈ Subgroup.normalizer (li L F.V1 : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  have mem_normalizer_sup : ∀ {A B : Subgroup G} {x : G}, x ∈ Subgroup.normalizer (A : Set G) →
      x ∈ Subgroup.normalizer (B : Set G) →
        x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := fun hA hB =>
    S125Fin.mem_normalizer_sup
      (fun a ha => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hA a).mp ha))
      (fun b hb => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hB b).mp hb))
  set O := pCoreOf 2 K₁ with hOdef
  have hOT := pCoreOf_le_T h1222 F hH hK₁n hKG
  have hOK : O ≤ K₁ := CFSG.LieType.BorelTits.pCoreOf_le 2 K₁
  have hG₁O : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    hK₁n.trans (S125Fin.normalizer_le_normalizer_pCoreOf K₁)
  have hTM : T ≤ mi T L F.V1 := le_inf le_sup_right (S125L2G.T_le_V F hf.T_le).1
  have hMG : mi T L F.V1 ≤ Subgroup.normalizer (F.V1 : Set G) := inf_le_right
  have hPG : oTwoUpper F.P ≤ Subgroup.normalizer (F.V1 : Set G) :=
    (oTwoUpper_le _).trans ((inf_le_left.trans inf_le_left).trans hMG)
  set B := oTwoUpper F.P ⊔ O with hB
  set R := K₁ ⊓ Subgroup.normalizer (B : Set G) with hR
  have hR1 : R ≤ (mi T L F.V1 ⊓ K₁) ⊔ O := by
    rintro x ⟨hxK, hxB⟩
    set x' : ↥K₁ := ⟨x, hxK⟩
    have hxn : QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) x' ∈
        Subgroup.normalizer (oTwoUpper (img K₁ F.P) : Set (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) := by
      rw [oTwoUpper_img F hPK]
      apply S125St.mem_normalizer_of_conj_le
      rintro _ ⟨y, hy, rfl⟩
      have hy' : (y : G) ∈ oTwoUpper F.P := hy
      have h1 : x * y * x⁻¹ ∈ B :=
        (Subgroup.mem_normalizer_iff.mp hxB _).mp (Subgroup.mem_sup_left hy')
      have h2 : x * y * x⁻¹ ∈ ((oTwoUpper F.P : Set G) * (O : Set G)) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right (oTwoUpper F.P) O (hPG.trans hG₁O)]
        exact h1
      obtain ⟨w, hw, o, ho, hwo⟩ := h2
      have hwK : w ∈ K₁ := hPK hw
      have hoK : o ∈ K₁ := hOK ho
      have he : x' * y * x'⁻¹ = ⟨w, hwK⟩ * ⟨o, hoK⟩ := Subtype.ext (by simp [x', hwo])
      have ho1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K₁) (⟨o, hoK⟩ : ↥K₁) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        obtain ⟨o', ho', ho'e⟩ := ho
        have : (⟨o, hoK⟩ : ↥K₁) = o' := Subtype.ext ho'e.symm
        rw [this]
        exact ho'
      rw [← map_mul, ← map_inv, ← map_mul, he, map_mul, ho1, mul_one]
      exact ⟨⟨w, hwK⟩, hw, rfl⟩
    have hxM := hα hxn
    have himg : img K₁ (mi T L F.V1) ≤ img K₁ ((mi T L F.V1 ⊓ K₁) ⊔ O) := by
      rw [show img K₁ (mi T L F.V1) = img K₁ (mi T L F.V1 ⊓ K₁) by
        rw [img, img, Subgroup.inf_subgroupOf_right]]
      exact img_mono le_sup_left
    exact mem_of_mk_mem le_sup_right x' (himg hxM)
  have hR2 : (mi T L F.V1 ⊓ K₁) ⊔ O ≤ R := by
    refine sup_le (le_inf inf_le_right fun m hm => ?_) (le_inf hOK fun o ho => ?_)
    · exact mem_normalizer_sup (S125Pm.mi_le_normalizer h1222 F hH hm.1) (hG₁O (hMG hm.1))
    · exact Subgroup.le_normalizer (Subgroup.mem_sup_right ho)
  have hgB : g ∈ Subgroup.normalizer (B : Set G) := mem_normalizer_sup hgP (hG₁O hg)
  have hgR : g ∈ Subgroup.normalizer (R : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hK₁n hg, Subgroup.le_normalizer hgB⟩
  have hReq : R = (mi T L F.V1 ⊓ K₁) ⊔ O := le_antisymm hR1 hR2
  have hRM : R ≤ mi T L F.V1 := hReq ▸ sup_le inf_le_left (hOT.trans hTM)
  have hL₁M : li L F.V1 ≤ mi T L F.V1 :=
    (Subgroup.map_subtype_le _).trans (inf_le_inf_right _ le_sup_left)
  have hL₁R : li L F.V1 ≤ R := hR2.trans' (le_sup_left.trans' (le_inf hL₁M hLK))
  have hres : CFSG.inSubgroup CFSG.perfectResidual R = li L F.V1 :=
    le_antisymm ((CFSG.RankThree.PartTwo.Sec18.inSubgroup_perfectResidual_mono hRM).trans
      (mi_perfectResidual_le F hH))
      (CFSG.RankThree.PartTwo.Sec18.le_inSubgroup_perfectResidual (S125K6.commutator_li L _)
        hL₁R)
  have := CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
    R hgR
  rwa [hres] at this

end Alpha

section C6

theorem l6_not_le_centralizer (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    ¬ li L F.V6 ≤ Subgroup.centralizer (F.V6 : Set G) := by
  intro hle
  obtain ⟨hne, -, hw⟩ := S125Gen.src_props 1
  have hm : (S125Gen.src 1).1 = 7 := rfl
  have hi : (S125Gen.src 1).2.1 = 0 := rfl
  have hj : (S125Gen.src 1).2.2 = 3 := rfl
  set t : SL5 := S125Gen.tv (S125Gen.src 1).2.1 (S125Gen.src 1).2.2 hne with ht
  have htL : t ∈ S125Gen.pL 4 1 rfl := S125Gen.tv_mem_pL41 hne (by rw [hi]; decide)
  have hψ : S125Tr2.psi F t ∈ autOn (li L F.V6) V := by
    rw [S125L4.autOn_l6 h1222 F hH]
    exact ⟨t, htL, rfl⟩
  obtain ⟨l, hlN, hlL, hl⟩ := mem_autOn_iff_exists.mp hψ
  set v : ↥V := F.e.symm (Multiplicative.ofAdd (Pi.single (S125Gen.src 1).1 1)) with hv
  have hvV₆ : (v : G) ∈ F.V6 := by
    rw [show F.V6 = F.sub {0, 1, 2, 4, 5, 7} from rfl, S125St.mem_sub_iff, hv,
      MulEquiv.apply_symm_apply, toAdd_ofAdd, hm]
    intro k hk
    exact Pi.single_eq_of_ne (by intro h; subst h; simp at hk) _
  have hcomm := Subgroup.mem_centralizer_iff.mp (hle hlL) _ hvV₆
  have hfix : conjAct V ⟨l, hlN⟩ v = v := by
    apply Subtype.ext
    rw [S125ZV.coe_conjAct_apply]
    change l * (v : G) * l⁻¹ = v
    rw [← hcomm, mul_inv_cancel_right]
  rw [hl] at hfix
  have he := congrArg (fun w => Multiplicative.toAdd (F.e w)) hfix
  change Multiplicative.toAdd (F.e (((F.γ.symm t : ↥(autOn L V)) : MulAut ↥V) v)) = _ at he
  rw [F.wedge, MulEquiv.apply_symm_apply, S125ZV.wedgeRep_apply, hv, MulEquiv.apply_symm_apply,
    toAdd_ofAdd, toAdd_ofAdd] at he
  change (JonesParshall.wedgeMat (Matrix.transvection (S125Gen.src 1).2.1 (S125Gen.src 1).2.2
    (1 : ZMod 2))).mulVec (Pi.single (S125Gen.src 1).1 1) = _ at he
  rw [hw] at he
  have := congrFun he 1
  simp [hm] at this

theorem pCoreOf_l6_le (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    pCoreOf 2 (li L F.V6) ≤ Subgroup.centralizer (F.V6 : Set G) := by
  obtain ⟨-, -, -, hR6, -⟩ := (lemma12_5_2_of h1222 G T L V F hH).2.2.2
  exact (E1.ThinA5.pCoreOf_le_pCoreOf le_sup_left
    (sup_le Subgroup.le_normalizer (S125K6.T_le_normalizer_l6 h1222 F hH))).trans hR6

theorem inf_centralizer_V6_le (h1222 : Stmt12_2_2) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    li L F.V6 ⊓ Subgroup.centralizer (F.V6 : Set G) ≤ pCoreOf 2 (li L F.V6) := by
  set L₆ := li L F.V6 with hL₆
  obtain ⟨e₆⟩ := S125K6.l6_quot_equiv h1222 F hH
  have hs : IsSimpleGroup (↥L₆ ⧸ CFSG.pCore 2 ↥L₆) := by
    have := (isSimpleGroup_sl_zmod_two (m := 4) (by norm_num)).1
    exact e₆.isSimpleGroup
  set N : Subgroup ↥L₆ := (L₆ ⊓ Subgroup.centralizer (F.V6 : Set G)).subgroupOf L₆ with hN
  have hL₆V : L₆ ≤ Subgroup.normalizer (F.V6 : Set G) := S125K6.li_le_normalizer L _
  have hNn : N.Normal := by
    rw [hN, Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro l hl
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl,
      CFSG.Quasithin.normalizer_le_normalizer_centralizer F.V6 (hL₆V hl)⟩
  have hNb : (N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L₆))).Normal :=
    hNn.map _ (QuotientGroup.mk'_surjective _)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs
    (N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L₆))) hNb with h | h
  · intro x hx
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥L₆) (⟨x, hx.1⟩ : ↥L₆) ∈
        N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L₆)) := ⟨⟨x, hx.1⟩, hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h1, rfl⟩
  · exfalso
    apply l6_not_le_centralizer h1222 F hH
    intro l hl
    obtain ⟨n, hn, hnl⟩ : QuotientGroup.mk' (CFSG.pCore 2 ↥L₆) (⟨l, hl⟩ : ↥L₆) ∈
        N.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L₆)) := h ▸ Subgroup.mem_top _
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnl
    have h2 : ((n⁻¹ * ⟨l, hl⟩ : ↥L₆) : G) ∈ Subgroup.centralizer (F.V6 : Set G) :=
      pCoreOf_l6_le h1222 F hH ⟨_, hnl, rfl⟩
    have h3 : (n : G) ∈ Subgroup.centralizer (F.V6 : Set G) := (Subgroup.mem_subgroupOf.mp hn).2
    have e : l = (n : G) * ((n⁻¹ * ⟨l, hl⟩ : ↥L₆) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem _ h3 h2

theorem centralizer_V6_le_normalizer
    (h1222 : Stmt12_2_2) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h312 : A312ForSQTK) (F : Frame125 T L V) (hH : Hyp125 G T L V) :
    Subgroup.centralizer (F.V6 : Set G) ≤ Subgroup.normalizer (oTwoUpper F.P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf := S125Ex.Facts125.of h1222 hH
  set L₆ := li L F.V6 with hL₆
  set O₆ := pCoreOf 2 L₆ with hO₆
  obtain ⟨-, hG₆N⟩ := S125K6.l6_cComp h1222 h36 h37 h38 h39 h312 F hH
  have hTL₆ := S125K6.T_le_normalizer_l6 h1222 F hH
  have hO₆T : O₆ ≤ T := by
    have hS : QuasithinUnique.IsSylowTwoOf T (L₆ ⊔ T) :=
      isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow le_sup_right
    exact (E1.ThinA5.pCoreOf_le_pCoreOf le_sup_left (sup_le Subgroup.le_normalizer hTL₆)).trans
      (pCoreOf_two_le_of_isSylowTwoOf hS)
  have hO₆P : O₆ ≤ F.P := hO₆T.trans (T_le_P h1222 F hH)
  have hPL₆ : oTwoUpper F.P ≤ L₆ := S125Pm.oTwoUpper_P_le h1222 F hH
  have hO₆N : O₆ ≤ Subgroup.normalizer (oTwoUpper F.P : Set G) :=
    hO₆P.trans (le_normalizer_oTwoUpper F.P)
  set Y := oTwoUpper F.P ⊔ O₆ with hY
  have hYP : oTwoUpper Y = oTwoUpper F.P := by
    apply le_antisymm
    · exact L1295.oTwoUpper_le_of_normal_sup le_sup_left
        ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
          (sup_le Subgroup.le_normalizer hO₆N))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) le_sup_right le_rfl
    · rw [oTwoUpper, Subgroup.closure_le]
      rintro x ⟨hx, ho⟩
      exact mem_oTwoUpper_of_odd (Subgroup.mem_sup_left (mem_oTwoUpper_of_odd hx ho)) ho
  intro c hc
  have hcG₆ : c ∈ Subgroup.normalizer (F.V6 : Set G) := Subgroup.centralizer_le_normalizer _ hc
  have hcL₆ := hG₆N hcG₆
  have hcO₆ : c ∈ Subgroup.normalizer (O₆ : Set G) :=
    S125Fin.normalizer_le_normalizer_pCoreOf L₆ hcL₆
  have hcY : c ∈ Subgroup.normalizer (Y : Set G) := by
    refine S125Fin.mem_normalizer_sup (fun x hx => ?_) (fun o ho => ?_)
    · have hxL := hPL₆ hx
      have hcomm : c * x * c⁻¹ * x⁻¹ ∈ O₆ := by
        refine inf_centralizer_V6_le h1222 F hH ⟨?_, ?_⟩
        · exact L₆.mul_mem ((Subgroup.mem_normalizer_iff.mp hcL₆ x).mp hxL) (L₆.inv_mem hxL)
        · have hxN := S125K6.li_le_normalizer L F.V6 hxL
          have hci : x * c⁻¹ * x⁻¹ ∈ Subgroup.centralizer (F.V6 : Set G) :=
            (Subgroup.mem_normalizer_iff.mp
              (CFSG.Quasithin.normalizer_le_normalizer_centralizer F.V6 hxN) c⁻¹).mp
              (Subgroup.inv_mem _ hc)
          have e : c * x * c⁻¹ * x⁻¹ = c * (x * c⁻¹ * x⁻¹) := by group
          rw [e]
          exact Subgroup.mul_mem _ hc hci
      have e : c * x * c⁻¹ = (c * x * c⁻¹ * x⁻¹) * x := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left hx)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hcO₆ o).mp ho)
  have := normalizer_le_normalizer_oTwoUpper Y hcY
  rwa [hYP] at this

theorem centralizer_V6_le_of_alpha
    (h1222 : Stmt12_2_2) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h312 : A312ForSQTK) (F : Frame125 T L V) (hH : Hyp125 G T L V)
    {K₁ : Subgroup G}
    (hK₁n : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (K₁ : Set G))
    (hKG : K₁ ≤ Subgroup.normalizer (F.V1 : Set G)) (hLK : li L F.V1 ≤ K₁)
    (hPK : oTwoUpper F.P ≤ K₁)
    (hα : ∀ S N D : Subgroup (↥K₁ ⧸ CFSG.pCore 2 ↥K₁), QuasithinUnique.IsSylowTwoOf S ⊤ →
      S125KG.Config63 S N D →
        Subgroup.normalizer (oTwoUpper D : Set (↥K₁ ⧸ CFSG.pCore 2 ↥K₁)) ≤ N) :
    Subgroup.centralizer (F.V6 : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hα' := hα _ _ _ (isSylow_img h1222 F hH hK₁n hKG) (config63 h1222 F hH hK₁n hKG hLK hPK)
  have hV₁V₆ : F.V1 ≤ F.V6 := S125L5a.sub_mono_le F (by decide)
  have hCG₁ : Subgroup.centralizer (F.V6 : Set G) ≤ Subgroup.normalizer (F.V1 : Set G) :=
    (Subgroup.centralizer_le hV₁V₆).trans (Subgroup.centralizer_le_normalizer _)
  refine S125L4.le_normalizer_L h1222 F hH (S125K6.li_le L F.V6)
    (S125K6.T_le_normalizer_l6 h1222 F hH) (S125L4.autOn_sup_l6 h1222 F hH)
    (fun c hc b hb => ?_) (fun c hc => normalizer_l1_of_alpha h1222 F hH hK₁n hKG hLK hPK hα'
      (hCG₁ hc) (centralizer_V6_le_normalizer h1222 h36 h37 h38 h39 h312 F hH hc))
  have hbW := S125K6.li_le_normalizer L F.V6 hb
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro w hw
  have hw' : b * w * b⁻¹ ∈ F.V6 := (Subgroup.mem_normalizer_iff.mp hbW w).mp hw
  have h1 := hc _ hw'
  calc w * (b⁻¹ * c * b) = b⁻¹ * ((b * w * b⁻¹) * c) * b := by group
    _ = b⁻¹ * (c * (b * w * b⁻¹)) * b := by rw [h1]
    _ = b⁻¹ * c * b * w := by group

end C6

end S125Cfg

end CFSG.Quasithin.H13
