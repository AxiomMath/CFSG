module

public import CFSG.Quasithin.Vol2.Ch12Sec6T2J
public import CFSG.Quasithin.Vol2.Ch12Sec6L11b
public import CFSG.Quasithin.H13.A7Nat1238NQBase
public import CFSG.Quasithin.MS93.S4A442FFD
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses
public import CFSG.Quasithin.Vol2.Ch11SecABasicV
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.LieType.SteinbergBRBlockParabolicDInf
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.SzN8Decomp
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1Five
public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma5
public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma7
public import CFSG.Quasithin.Vol2.Ch12Sec6L16b
public import CFSG.Quasithin.Vol2.Ch1Chief
public import CFSG.Sporadic.J4.QT2LocUniq
public import CFSG.Sporadic.Schreier.J4SNoCompCover

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique S126 S126T2
open scoped IsMulCommutative commutatorElement

namespace S126VK

variable {G : Type} [Group G]

omit [Group G] in
theorem normalizer_le_normalizer_omega {G : Type} [Group G] (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (quasithinOmegaOneCenter X : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ y ∈ quasithinOmegaOneCenter X,
      g * y * g⁻¹ ∈ quasithinOmegaOneCenter X := by
    intro g hg y hy
    obtain ⟨hyX, hyC, hy2⟩ := mem_quasithinOmegaOneCenter_iff.1 hy
    refine mem_quasithinOmegaOneCenter_iff.2 ⟨(Subgroup.mem_normalizer_iff.1 hg y).1 hyX, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have ht' : g⁻¹ * t * g ∈ X := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) t).1 ht
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.1 hyC _ ht'
      calc t * (g * y * g⁻¹) = g * ((g⁻¹ * t * g) * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * t * g)) * g⁻¹ := by rw [h1]
        _ = g * y * g⁻¹ * t := by group
    · have e : (g * y * g⁻¹) ^ 2 = g * y ^ 2 * g⁻¹ := by simp only [pow_two]; group
      rw [e, hy2]
      group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hy
  simpa [mul_assoc] using this

omit [Group G] in
theorem isElemAbelian_omega {G : Type} [Group G] (X : Subgroup G) :
    IsElemAbelian 2 (quasithinOmegaOneCenter X) := by
  have hcomm : ∀ a ∈ quasithinOmegaOneCenter X, ∀ b ∈ quasithinOmegaOneCenter X,
      a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.1 hb).2.1 a
      (mem_quasithinOmegaOneCenter_iff.1 ha).1
  exact ⟨isMulCommutative_subgroup_iff.mpr hcomm,
    fun x hx => (mem_quasithinOmegaOneCenter_iff.mp hx).2.2⟩

omit [Group G] in
theorem commutator_omega_eq_bot {G : Type} [Group G] (X : Subgroup G) :
    ⁅quasithinOmegaOneCenter X, quasithinOmegaOneCenter X⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.1 ha).2.1 b
    (mem_quasithinOmegaOneCenter_iff.1 hb).1

variable [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem isTwoReducedIn_V (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) :
    IsTwoReducedIn (L ⊔ T) V := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, -⟩ := hall V hyp.irrPlus
  exact isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVT.trans le_sup_right, hred⟩

omit [IsMulCommutative ↥V] in
theorem V_le_Z1 (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) :
    V ≤ quasithinOmegaOneCenter (Qv T V) := by
  obtain ⟨hVT, hVe⟩ := V_facts h1222 hH
  intro x hx
  refine mem_quasithinOmegaOneCenter_iff.2 ⟨⟨hVT hx, ?_⟩, ?_, hVe.2 x hx⟩
  · show x ∈ Subgroup.centralizer (V : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hVe.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  · rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (Subgroup.mem_centralizer_iff.1 hq.2 x hx).symm

omit [IsMulCommutative ↥V] in
theorem isTwoReducedIn_Z1 (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) :
    IsTwoReducedIn (L ⊔ T) (quasithinOmegaOneCenter (Qv T V)) := by
  have hred := isTwoReducedIn_V h1222 hH
  have hVZ := V_le_Z1 h1222 hH
  have hQLT : Qv T V ≤ L ⊔ T := inf_le_left.trans le_sup_right
  refine ⟨fun x hx => hQLT (mem_quasithinOmegaOneCenter_iff.1 hx).1,
    (LT_le_normalizer_Qv h1222 hH).trans (normalizer_le_normalizer_omega _),
    isElemAbelian_omega _, fun D hD hDn hDp => ?_⟩
  have hDV := hred.2.2.2 D hD hDn fun d hd =>
    (hDp d hd).imp fun k hk => Subgroup.centralizer_le hVZ hk
  intro d hd
  have hdQ : d ∈ Qv T V := by
    rw [Qv_eq h1222 hH]
    exact ⟨hD hd, hDV hd⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.1 (mem_quasithinOmegaOneCenter_iff.1 hz).2.1 d hdQ).symm

omit [IsMulCommutative ↥V] in
theorem Z1_le_R2 (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) :
    quasithinOmegaOneCenter (Qv T V) ≤ reducedAggregate (L ⊔ T) :=
  A7.le_reducedAggregate_of_isTwoReducedIn (isTwoReducedIn_Z1 h1222 hH)

omit [IsMulCommutative ↥V] in
theorem le_normalizer_of_comm_le (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V) (v : G)
    {R : Subgroup G} (hQR : Qv T V ≤ R)
    (hRL : ∀ r ∈ R, ∀ l ∈ Lv L v, r * l * r⁻¹ * l⁻¹ ∈ Qv T V) :
    Lv L v ≤ Subgroup.normalizer (R : Set G) := by
  have hQN : Lv L v ≤ Subgroup.normalizer (Qv T V : Set G) :=
    ((Lv_le_L L v).trans le_sup_left).trans (LT_le_normalizer_Qv h1222 hH)
  have key : ∀ l ∈ Lv L v, ∀ r ∈ R, l * r * l⁻¹ ∈ R := by
    intro l hl r hr
    have h1 := hRL r hr l⁻¹ ((Lv L v).inv_mem hl)
    have h2 := (Subgroup.mem_normalizer_iff.1 (hQN hl) _).1 h1
    have e : l * r * l⁻¹ = l * (r * l⁻¹ * r⁻¹ * l⁻¹⁻¹) * l⁻¹ * r := by group
    rw [e]
    exact R.mul_mem (hQR h2) hr
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨key l hl r, fun h => ?_⟩
  have := key l⁻¹ ((Lv L v).inv_mem hl) _ h
  simpa [mul_assoc] using this

omit [IsMulCommutative ↥V] in
theorem L_perfect (hH : Hyp126 G T L V) : ⁅L, L⁆ = L := hH.hyp.maximal.1.2.1.2.1

theorem comm_le_V (h1261 : Lemma12_6_1) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hJ : ¬ thompsonJ T ≤ Qv T V) : ⁅reducedAggregate (L ⊔ T), L⁆ ≤ V := by
  set R₂ := reducedAggregate (L ⊔ T) with hR₂
  set C : Subgroup G := R₂ ⊓ Subgroup.centralizer (L : Set G) with hC
  set W : Subgroup G := V ⊔ C with hW
  have hyp := hH.hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hVR : V ≤ R₂ := hyp.irrPlus.1
  obtain ⟨-, hRc, hRp, hRN⟩ := Vol2.Ch11.SecA.reducedAggregate_props (L ⊔ T)
  have hLR : L ≤ Subgroup.normalizer (R₂ : Set G) := le_sup_left.trans hRN
  have hLC : L ≤ Subgroup.normalizer (C : Set G) :=
    B2F.le_normalizer_inf hLR (B2F.le_normalizer_centralizer Subgroup.le_normalizer)
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := fun l hl =>
    Subgroup.inf_normalizer_le_normalizer_sup V C ⟨hLV hl, hLC hl⟩
  have hWR : W ≤ R₂ := sup_le hVR inf_le_left
  have hidx : W.relIndex R₂ ≤ 2 := by
    refine (h1261 G T L V F hH).2.2.1.resolve_left fun h => hJ ?_
    rw [h]
    exact thompsonJ_le_self _
  have hRW : ⁅R₂, L⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro x hx l hl
    have hlx : l * x * l⁻¹ ∈ R₂ := (Subgroup.mem_normalizer_iff.1 (hLR hl) x).1 hx
    have hlxi : l * x⁻¹ * l⁻¹ ∈ R₂ := by
      have := R₂.inv_mem hlx
      simpa [mul_assoc] using this
    have e : ⁅x, l⁆ = x * (l * x⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    have hpos : (W.subgroupOf R₂).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    change (W.subgroupOf R₂).index ≤ 2 at hidx
    rcases (show (W.subgroupOf R₂).index = 1 ∨ (W.subgroupOf R₂).index = 2 by omega) with h1 | h2
    · have hRle : R₂ ≤ W := Subgroup.relIndex_eq_one.1 h1
      exact hRle (R₂.mul_mem hx hlxi)
    · have key := Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨x, hx⟩) (b := ⟨_, hlxi⟩)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at key
      refine key.2 ?_
      change x ∈ W ↔ l * x⁻¹ * l⁻¹ ∈ W
      constructor
      · intro hxW
        exact (Subgroup.mem_normalizer_iff.1 (hLW hl) _).1 (W.inv_mem hxW)
      · intro h
        have := (Subgroup.mem_normalizer_iff.1 (hLW (L.inv_mem hl)) _).1 h
        have e2 : l⁻¹ * (l * x⁻¹ * l⁻¹) * l⁻¹⁻¹ = x⁻¹ := by group
        rw [e2] at this
        simpa using W.inv_mem this
  have hWV : ⁅W, L⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro w hw l hl
    have hVLT : V ≤ L ⊔ T := hVR.trans (hRp.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 _))
    have hLTL : L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
      sup_le Subgroup.le_normalizer hyp.normalizes
    have hVC : V ≤ Subgroup.normalizer (C : Set G) :=
      B2F.le_normalizer_inf (hVLT.trans hRN) (B2F.le_normalizer_centralizer (hVLT.trans hLTL))
    rw [← SetLike.mem_coe, hW, Subgroup.coe_mul_of_left_le_normalizer_right V C hVC] at hw
    obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_mul.1 hw
    have hcl : c * l = l * c := (Subgroup.mem_centralizer_iff.1 hc.2 l hl).symm
    have e : ⁅a * c, l⁆ = a * (l * a⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      calc a * c * l * (a * c)⁻¹ * l⁻¹ = a * (c * l) * c⁻¹ * a⁻¹ * l⁻¹ := by group
        _ = a * (l * c) * c⁻¹ * a⁻¹ * l⁻¹ := by rw [hcl]
        _ = a * (l * a⁻¹ * l⁻¹) := by group
    rw [e]
    exact V.mul_mem ha ((Subgroup.mem_normalizer_iff.1 (hLV hl) _).1 (V.inv_mem ha))
  have hRab : ⁅R₂, R₂⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hRc b hb a ha
  rw [MS93.S4A.P442.commutator_eq_commutator_commutator (L_perfect hH) hLR hRab]
  exact (Subgroup.commutator_mono hRW le_rfl).trans hWV

theorem comm_Z1_le_Vv (h1222 : Stmt12_2_2) (h1261 : Lemma12_6_1) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hJ : ¬ thompsonJ T ≤ Qv T V) (v : G) :
    ⁅quasithinOmegaOneCenter (Qv T V), Lv L v⁆ ≤ Vv L V v := by
  have hle : ⁅quasithinOmegaOneCenter (Qv T V), Lv L v⁆ ≤ V :=
    (Subgroup.commutator_mono (Z1_le_R2 h1222 hH) (Lv_le_L L v)).trans
      (comm_le_V h1261 F hH hJ)
  have hLZ : Lv L v ≤ Subgroup.normalizer (quasithinOmegaOneCenter (Qv T V) : Set G) :=
    ((Lv_le_L L v).trans le_sup_left).trans (isTwoReducedIn_Z1 h1222 hH).2.1
  have hLp : ⁅Lv L v, Lv L v⁆ = Lv L v := perfectCore_perfect _
  rw [MS93.S4A.P442.commutator_eq_commutator_commutator hLp hLZ (commutator_omega_eq_bot _)]
  exact Subgroup.commutator_mono hle le_rfl

theorem comm_omega_le_Vv (h1222 : Stmt12_2_2) (h1261 : Lemma12_6_1) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hJ : ¬ thompsonJ T ≤ Qv T V) (v : G) {R : Subgroup G}
    (hQR : Qv T V ≤ R) (hRL : ∀ r ∈ R, ∀ l ∈ Lv L v, r * l * r⁻¹ * l⁻¹ ∈ Qv T V) :
    ⁅quasithinOmegaOneCenter R, Lv L v⁆ ≤ Vv L V v := by
  have hQN : Lv L v ≤ Subgroup.normalizer (Qv T V : Set G) :=
    ((Lv_le_L L v).trans le_sup_left).trans (LT_le_normalizer_Qv h1222 hH)
  have hLR := le_normalizer_of_comm_le h1222 hH v hQR hRL
  have hZ : ⁅quasithinOmegaOneCenter R, Lv L v⁆ ≤ quasithinOmegaOneCenter (Qv T V) := by
    rw [Subgroup.commutator_le]
    intro z hz l hl
    obtain ⟨hzR, hzC, hz2⟩ := mem_quasithinOmegaOneCenter_iff.1 hz
    have hcQ : ⁅z, l⁆ ∈ Qv T V := by
      rw [commutatorElement_def]
      exact hRL z hzR l hl
    have hw : l * z⁻¹ * l⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 (hLR hl) _).1 (R.inv_mem hzR)
    have hzw : z * (l * z⁻¹ * l⁻¹) = (l * z⁻¹ * l⁻¹) * z :=
      (Subgroup.mem_centralizer_iff.1 hzC _ hw).symm
    have e : ⁅z, l⁆ = z * (l * z⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
    refine mem_quasithinOmegaOneCenter_iff.2 ⟨hcQ, ?_, ?_⟩
    · rw [e, Subgroup.mem_centralizer_iff]
      intro q hq
      have h1 : Commute q z := Subgroup.mem_centralizer_iff.1 hzC q (hQR hq)
      have hq' : l⁻¹ * q * l ∈ Qv T V := by
        have := (Subgroup.mem_normalizer_iff.1 (hQN ((Lv L v).inv_mem hl)) q).1 hq
        simpa using this
      have h2 : Commute (l⁻¹ * q * l) z := Subgroup.mem_centralizer_iff.1 hzC _ (hQR hq')
      have h3 : Commute q (l * z⁻¹ * l⁻¹) := by
        have h4 : (l⁻¹ * q * l) * z⁻¹ = z⁻¹ * (l⁻¹ * q * l) := h2.inv_right.eq
        show q * (l * z⁻¹ * l⁻¹) = (l * z⁻¹ * l⁻¹) * q
        calc q * (l * z⁻¹ * l⁻¹) = l * ((l⁻¹ * q * l) * z⁻¹) * l⁻¹ := by group
          _ = l * (z⁻¹ * (l⁻¹ * q * l)) * l⁻¹ := by rw [h4]
          _ = (l * z⁻¹ * l⁻¹) * q := by group
      exact (h1.mul_right h3).eq
    · rw [e, (show Commute z (l * z⁻¹ * l⁻¹) from hzw).mul_pow, hz2, conj_pow, inv_pow, hz2]
      group
  have hLZ : Lv L v ≤ Subgroup.normalizer (quasithinOmegaOneCenter R : Set G) :=
    hLR.trans (normalizer_le_normalizer_omega R)
  have hLp : ⁅Lv L v, Lv L v⁆ = Lv L v := perfectCore_perfect _
  rw [MS93.S4A.P442.commutator_eq_commutator_commutator hLp hLZ (commutator_omega_eq_bot _)]
  exact (Subgroup.commutator_mono hZ le_rfl).trans (comm_Z1_le_Vv h1222 h1261 F hH hJ v)

end S126VK

end CFSG.Quasithin.H13
