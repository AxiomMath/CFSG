module

public import CFSG.Quasithin.Vol2.Ch11SecEFacts8
public import CFSG.Quasithin.Vol2.Ch11SecE42Rad
public import CFSG.Quasithin.Vol2.Ch11SecE42S1d
public import CFSG.Quasithin.Vol2.Ch11SecE42Setup
public import CFSG.Quasithin.Vol2.Ch11SecEFacts6

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G} {z : G}

theorem conf_spec (hF43 : Facts43) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0)
    (h1111 : Stmt11_1_1) (h1141 : Stmt11_4_1) (hc : Conf11_4_2 T L I n V₁ z) :
    T ≤ Subgroup.normalizer (kz L V₁ z : Set G) ∧ LOf L V₁ ≤ kz L V₁ z ∧
      kz L V₁ z ≤ Subgroup.centralizer ({z} : Set G) ∧
      ¬ kz L V₁ z ≤ Subgroup.centralizer (V₁ : Set G) ∧ quasithinIsLocal T (kz L V₁ z) ∧
      z ∈ V₁ := by
  have h := hc.hyp
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  have hcV := (h1141 G T L I n V₁ X h hc.vi hX).1.1
  have hzV₁ := mem_V₁_of_mem_centralizer hF43 h1102 h hcV hc.vi hc.mem.1 hc.mem.2
  have hV₁1 : V₁ ≠ ⊥ := fun h0 => hc.ne_one (Subgroup.mem_bot.mp (h0 ▸ hzV₁))
  obtain ⟨hK, hNK, -⟩ := kz_spec hF43 h1102 h1110 h1111 h hcV hc.vi hc.mem hc.ne_one
  have hTz := le_centralizer_of_mem hc.mem.2
  refine ⟨hTz.trans hNK, le_conjClosure _ _, le_of_mem_cComp hK,
    not_le_centralizer_of_ne h1110 h1111 h hc.vi hV₁1 hK hc.lt.le hc.lt.ne, ?_, hzV₁⟩
  exact isLocal_of_mem_cComp_of_sylow (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTz)
    (pCoreOf_centralizer_ne_bot h hc.mem hc.ne_one) hK

theorem isQuasisimple_kz (hF : Facts42) (hS : Facts42S3) (hc : Conf11_4_2 T L I n V₁ z) :
    CFSG.IsQuasisimple (↥(kz L V₁ z) ⧸ CFSG.pCore 2 ↥(kz L V₁ z)) := by
  rcases hc.list with h2 | ⟨-, h3⟩
  · exact hF.twoQS _ n hc.hyp.one_lt h2
  · exact hS.threeQS _ h3 hc.not_a36 hc.not_sl2pE

theorem isFaithfulLocal_kz (hF43 : Facts43) (hP : SecB.PointFacts) (h1102 : Stmt11_0_2)
    (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1) (h1141 : Stmt11_4_1)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (hc : Conf11_4_2 T L I n V₁ z)
    (hmax : quasithinIsMaximalLocal T (kz L V₁ z)) : quasithinIsFaithfulLocal T (kz L V₁ z) := by
  have h := hc.hyp
  obtain ⟨hTK, hLK, -, hnC, hloc, -⟩ := conf_spec hF43 h1102 h1110 h1111 h1141 hc
  have hV := le_omegaOneCenterOf hP h1102 h hc.vi hLK hloc.2.2.2
  have hne : ⁅omegaOneCenterOf (pCoreOf 2 (kz L V₁ z ⊔ T)), kz L V₁ z⁆ ≠ ⊥ := by
    intro h0
    apply hnC
    exact Subgroup.le_centralizer_iff.mp
      (hV.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0))
  exact isFaithfulLocal_of h.fsu.qtke h.fsu.simple h.fsu.nonabelian h37 h39 h.fsu.sylow hmax hTK
    hne

theorem exists_fsu_kz (hF : Facts42) (hS : Facts42S3) (hF43 : Facts43) (hP : SecB.PointFacts)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1) (h1141 : Stmt11_4_1)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (hFSU : Ch10.StmtFSUChoice)
    (hc : Conf11_4_2 T L I n V₁ z) (hmax : quasithinIsMaximalLocal T (kz L V₁ z)) :
    ∃ I' : Subgroup G, FSU G T (kz L V₁ z) I' := by
  have h := hc.hyp
  exact hFSU G T (kz L V₁ z) h.fsu.simple h.fsu.nonabelian h.fsu.qtke h.fsu.sylow hmax
    (isFaithfulLocal_kz hF43 hP h1102 h1110 h1111 h1141 h37 h39 hc hmax)
    (isQuasisimple_kz hF hS hc)

end CFSG.Quasithin.Vol2.Ch11.SecE
