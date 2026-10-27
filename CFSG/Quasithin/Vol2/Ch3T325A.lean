module

public import CFSG.Quasithin.H13.StatementsL1
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch1Prop121
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.Quasithin.Background.F9Eighteen
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore

public section

namespace CFSG.Quasithin.H13.T325

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

structure Ctx [Finite G] (T L V₀ : Subgroup G) : Prop where
  fsu : FSU G T L V₀
  eqL : conjClosure L T = L
  maxM : quasithinIsMaxTwoLocal (Subgroup.normalizer (L : Set G))
  uniq : IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G))
  hstar : ∃ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H
  redVM : IsTwoReducedIn (Subgroup.normalizer (L : Set G))
    (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)))
  redV : IsTwoReducedIn (L ⊔ T) (conjClosure V₀ T)
  o2 : pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (conjClosure V₀ T : Set G)

theorem Ctx.of [Finite G] (h331 : Stmt3_3_1) (h3222 : Vol2.Ch10.TmpL6_3_2_2_two)
    (h3228 : Vol2.Ch10.TmpL6_3_2_2_eight) {T L V₀ : Subgroup G} (hfsu : FSU G T L V₀)
    (hL : L = conjClosure L T) : Ctx T L V₀ := by
  have hL' : conjClosure L T = L := hL.symm
  obtain ⟨⟨hmax, hLT, huniq⟩, -, hH, -⟩ :=
    (h331 G T hfsu.simple hfsu.nonabelian hfsu.qtke hfsu.sylow).2 L hfsu.maximal hfsu.quasisimple
  have h1 : IsTwoReducedIn (fsuM T L) (fsuVM T L V₀) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 (h3222 G T L V₀ hfsu)
  obtain ⟨hVLT, hredV, hO⟩ := h3228 G T L V₀ hfsu
  have h2 : IsTwoReducedIn (fsuL0 T L ⊔ T) (fsuV T V₀) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVLT, hredV⟩
  dsimp only [fsuVM, fsuV, fsuM, fsuL0] at h1 h2 hO
  rw [hL'] at hmax hLT huniq hH h1 h2 hO
  exact ⟨hfsu, hL', hmax, ⟨⟨hmax, hLT⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩, hH, h1, h2, hO⟩

theorem isSylowTwoOf_of_le {T H : Subgroup G} (hT : quasithinIsSylowTwo T) (hTH : T ≤ H) :
    IsSylowTwoOf T H :=
  ⟨hTH, hT.1, fun h => hT.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩

theorem V₀_le_V (T V₀ : Subgroup G) : V₀ ≤ conjClosure V₀ T := le_conjClosure V₀ T

theorem V_le_VM (T L V₀ : Subgroup G) : conjClosure V₀ T ≤
    conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) :=
  le_conjClosure _ _

theorem T_le_NV (T V₀ : Subgroup G) : T ≤ Subgroup.normalizer (conjClosure V₀ T : Set G) :=
  le_normalizer_conjClosure V₀ T

theorem M_le_NVM (T L V₀ : Subgroup G) : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer
    (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) : Set G) :=
  le_normalizer_conjClosure _ _

namespace Ctx

variable [Finite G] {T L V₀ : Subgroup G} (c : Ctx T L V₀)
include c

theorem T_le_M : T ≤ Subgroup.normalizer (L : Set G) := by
  have h := le_normalizer_conjClosure L T
  rwa [c.eqL] at h

theorem inM : InM T (Subgroup.normalizer (L : Set G)) := ⟨c.maxM, c.T_le_M⟩

theorem irr : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V₀ := by
  have h := c.fsu.irrPlus
  rwa [c.eqL] at h

theorem L_le_NV₀ : L ≤ Subgroup.normalizer (V₀ : Set G) := c.irr.2.2.1

theorem comm_V₀ : ⁅V₀, L⁆ = V₀ := c.irr.2.2.2.1

theorem V₀_ne_bot : V₀ ≠ ⊥ := c.irr.2.1

theorem L_le_NV : L ≤ Subgroup.normalizer (conjClosure V₀ T : Set G) :=
  le_normalizer_conjClosure_of_le c.L_le_NV₀ c.T_le_M

theorem elemVM : IsElemAbelian 2
    (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))) :=
  c.redVM.2.2.1

theorem elemV : IsElemAbelian 2 (conjClosure V₀ T) := c.redV.2.2.1

theorem VM_eq : conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) =
    conjClosure V₀ (Subgroup.normalizer (L : Set G)) := by
  refine le_antisymm (conjClosure_le fun m hm v hv => ?_) (conjClosure_mono (V₀_le_V T V₀) le_rfl)
  have hmem := le_normalizer_conjClosure V₀ (Subgroup.normalizer (L : Set G)) hm
  exact (Subgroup.mem_normalizer_iff.mp hmem v).mp (conjClosure_mono le_rfl c.T_le_M hv)

theorem sylowM : IsSylowTwoOf T (Subgroup.normalizer (L : Set G)) :=
  isSylowTwoOf_of_le c.fsu.sylow c.T_le_M

theorem VM_le_M : conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) ≤
    Subgroup.normalizer (L : Set G) :=
  c.redVM.1

theorem V_le_T : conjClosure V₀ T ≤ T :=
  (A4.le_pCoreOf_of_isTwoReducedIn c.redV).trans (c.o2 ▸ inf_le_left)

theorem V₀_le_T : V₀ ≤ T := (V₀_le_V T V₀).trans c.V_le_T

theorem VM_ne_bot : conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) ≠ ⊥ :=
  fun h => c.V₀_ne_bot (le_bot_iff.mp (h ▸ (V₀_le_V T V₀).trans (V_le_VM T L V₀)))

theorem pCoreOf_M_ne_bot : pCoreOf 2 (Subgroup.normalizer (L : Set G)) ≠ ⊥ :=
  fun h => c.VM_ne_bot (le_bot_iff.mp (h ▸ A4.le_pCoreOf_of_isTwoReducedIn c.redVM))

theorem sqtkM : SQTKGroup ↥(Subgroup.normalizer (L : Set G)) :=
  sqtkGroup_of_pCoreOf_ne_bot c.fsu.qtke c.fsu.simple c.fsu.nonabelian c.pCoreOf_M_ne_bot

theorem pCoreOf_L_le : pCoreOf 2 L ≤ Subgroup.centralizer
    (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) : Set G) :=
  (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L _
    Subgroup.le_normalizer (Subgroup.normal_in_normalizer)).trans
    (A4.pCoreOf_le_centralizer_of_isTwoReducedIn c.redVM)

theorem comm_VM : ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)), L⁆ =
    conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) := by
  set M := Subgroup.normalizer (L : Set G) with hM
  set VM := conjClosure (conjClosure V₀ T) M with hVM
  have hLVM : L ≤ Subgroup.normalizer (VM : Set G) := Subgroup.le_normalizer.trans (M_le_NVM T L V₀)
  refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hLVM) ?_
  rw [hVM, c.VM_eq]
  refine conjClosure_le fun m hm v hv => ?_
  rw [← c.comm_V₀] at hv
  have hmem : m * v * m⁻¹ ∈ (⁅V₀, L⁆ : Subgroup G).map (MulAut.conj m).toMonoidHom :=
    ⟨v, hv, rfl⟩
  rw [Subgroup.map_commutator] at hmem
  refine Subgroup.commutator_mono ?_ ?_ hmem
  · rintro _ ⟨w, hw, rfl⟩
    rw [← c.VM_eq]
    exact mem_conjClosure hm (V₀_le_V T V₀ hw)
  · rintro _ ⟨l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hm l).mp hl

end Ctx

end CFSG.Quasithin.H13.T325
