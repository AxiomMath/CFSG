module

public import CFSG.Quasithin.Vol2.Ch3T325A

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open T325 (V₀_le_V V_le_VM T_le_NV M_le_NVM isSylowTwoOf_of_le)

variable {G : Type} [Group G]

structure Ctx [Finite G] (T L V₀ : Subgroup G) : Prop where
  fsu : FSU G T L V₀
  ne : L ≠ conjClosure L T
  maxM : quasithinIsMaxTwoLocal (Subgroup.normalizer (conjClosure L T : Set G))
  uniq : IsUniqueM (L ⊔ T) (Subgroup.normalizer (conjClosure L T : Set G))
  hstar : ∃ H : Subgroup G, IsHStar T (Subgroup.normalizer (conjClosure L T : Set G)) H
  redVM : IsTwoReducedIn (Subgroup.normalizer (conjClosure L T : Set G))
    (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)))
  redV : IsTwoReducedIn (conjClosure L T ⊔ T) (conjClosure V₀ T)
  o2 : pCoreOf 2 (conjClosure L T ⊔ T) = T ⊓ Subgroup.centralizer (conjClosure V₀ T : Set G)

theorem Ctx.of [Finite G] (h331 : Stmt3_3_1) (h3222 : Vol2.Ch10.TmpL6_3_2_2_two)
    (h3228 : Vol2.Ch10.TmpL6_3_2_2_eight) {T L V₀ : Subgroup G} (hfsu : FSU G T L V₀)
    (hne : L ≠ conjClosure L T) : Ctx T L V₀ := by
  obtain ⟨⟨hmax, hLT, huniq⟩, -, hH, -⟩ :=
    (h331 G T hfsu.simple hfsu.nonabelian hfsu.qtke hfsu.sylow).2 L hfsu.maximal hfsu.quasisimple
  have h1 : IsTwoReducedIn (fsuM T L) (fsuVM T L V₀) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 (h3222 G T L V₀ hfsu)
  obtain ⟨hVLT, hredV, hO⟩ := h3228 G T L V₀ hfsu
  have h2 : IsTwoReducedIn (fsuL0 T L ⊔ T) (fsuV T V₀) :=
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVLT, hredV⟩
  exact ⟨hfsu, hne, hmax, ⟨⟨hmax, hLT⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩, hH, h1, h2, hO⟩

theorem conjClosure_le_sup (T L : Subgroup G) : conjClosure L T ≤ L ⊔ T :=
  conjClosure_le fun _ ht _ hl => (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (Subgroup.mem_sup_right ht)
    (Subgroup.mem_sup_left hl)) ((L ⊔ T).inv_mem (Subgroup.mem_sup_right ht))

theorem sup_eq (T L : Subgroup G) : conjClosure L T ⊔ T = L ⊔ T :=
  le_antisymm (sup_le (conjClosure_le_sup T L) le_sup_right)
    (sup_le_sup_right (le_conjClosure L T) T)

namespace Ctx

variable [Finite G] {T L V₀ : Subgroup G}

theorem T_le_M (_c : Ctx T L V₀) : T ≤ Subgroup.normalizer (conjClosure L T : Set G) :=
  le_normalizer_conjClosure L T

theorem L_le_L₀ (_c : Ctx T L V₀) : L ≤ conjClosure L T := le_conjClosure L T

variable (c : Ctx T L V₀)
include c

theorem sup_le_M : conjClosure L T ⊔ T ≤ Subgroup.normalizer (conjClosure L T : Set G) :=
  sup_le Subgroup.le_normalizer c.T_le_M

theorem inM : InM T (Subgroup.normalizer (conjClosure L T : Set G)) := ⟨c.maxM, c.T_le_M⟩

theorem uniq₀ :
    IsUniqueM (conjClosure L T ⊔ T) (Subgroup.normalizer (conjClosure L T : Set G)) := by
  rw [sup_eq T L]
  exact c.uniq

theorem irr : IsIrrPlusIn (conjClosure L T) (reducedAggregate (L ⊔ T)) T V₀ := c.fsu.irrPlus

theorem L₀_le_NV₀ : conjClosure L T ≤ Subgroup.normalizer (V₀ : Set G) := c.irr.2.2.1

theorem comm_V₀ : ⁅V₀, conjClosure L T⁆ = V₀ := c.irr.2.2.2.1

theorem V₀_ne_bot : V₀ ≠ ⊥ := c.irr.2.1

theorem L₀_le_NV : conjClosure L T ≤ Subgroup.normalizer (conjClosure V₀ T : Set G) :=
  le_normalizer_conjClosure_of_le c.L₀_le_NV₀ c.T_le_M

theorem elemVM : IsElemAbelian 2
    (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G))) :=
  c.redVM.2.2.1

theorem elemV : IsElemAbelian 2 (conjClosure V₀ T) := c.redV.2.2.1

theorem VM_eq : conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) =
    conjClosure V₀ (Subgroup.normalizer (conjClosure L T : Set G)) := by
  refine le_antisymm (conjClosure_le fun m hm v hv => ?_) (conjClosure_mono (V₀_le_V T V₀) le_rfl)
  have hmem := le_normalizer_conjClosure V₀ (Subgroup.normalizer (conjClosure L T : Set G)) hm
  exact (Subgroup.mem_normalizer_iff.mp hmem v).mp (conjClosure_mono le_rfl c.T_le_M hv)

theorem sylowM : IsSylowTwoOf T (Subgroup.normalizer (conjClosure L T : Set G)) :=
  isSylowTwoOf_of_le c.fsu.sylow c.T_le_M

theorem VM_le_M : conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ≤
    Subgroup.normalizer (conjClosure L T : Set G) :=
  c.redVM.1

theorem VM_ne_bot :
    conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) ≠ ⊥ :=
  fun h => c.V₀_ne_bot (le_bot_iff.mp (h ▸ (V₀_le_V T V₀).trans (V_le_VM T (conjClosure L T) V₀)))

theorem pCoreOf_M_ne_bot : pCoreOf 2 (Subgroup.normalizer (conjClosure L T : Set G)) ≠ ⊥ :=
  fun h => c.VM_ne_bot (le_bot_iff.mp (h ▸ A4.le_pCoreOf_of_isTwoReducedIn c.redVM))

theorem sqtkM : SQTKGroup ↥(Subgroup.normalizer (conjClosure L T : Set G)) :=
  sqtkGroup_of_pCoreOf_ne_bot c.fsu.qtke c.fsu.simple c.fsu.nonabelian c.pCoreOf_M_ne_bot

theorem pCoreOf_L₀_le : pCoreOf 2 (conjClosure L T) ≤ Subgroup.centralizer
    (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) : Set G) :=
  (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 (conjClosure L T) _
    Subgroup.le_normalizer (Subgroup.normal_in_normalizer)).trans
    (A4.pCoreOf_le_centralizer_of_isTwoReducedIn c.redVM)

theorem comm_VM :
    ⁅conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)),
        conjClosure L T⁆ =
      conjClosure (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) := by
  set L₀ := conjClosure L T with hL₀
  set M := Subgroup.normalizer (L₀ : Set G) with hM
  set VM := conjClosure (conjClosure V₀ T) M with hVM
  have hLVM : L₀ ≤ Subgroup.normalizer (VM : Set G) :=
    Subgroup.le_normalizer.trans (M_le_NVM T L₀ V₀)
  refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hLVM) ?_
  rw [hVM, c.VM_eq]
  refine conjClosure_le fun m hm v hv => ?_
  rw [← c.comm_V₀] at hv
  have hmem : m * v * m⁻¹ ∈ (⁅V₀, L₀⁆ : Subgroup G).map (MulAut.conj m).toMonoidHom :=
    ⟨v, hv, rfl⟩
  rw [Subgroup.map_commutator] at hmem
  refine Subgroup.commutator_mono ?_ ?_ hmem
  · rintro _ ⟨w, hw, rfl⟩
    rw [← c.VM_eq]
    exact mem_conjClosure hm (V₀_le_V T V₀ hw)
  · rintro _ ⟨l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hm l).mp hl

end Ctx

end CFSG.Quasithin.H13.T326
