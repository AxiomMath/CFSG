module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenSixA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenSixC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenSixE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenSixF
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ComponentCoverSimple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubConjClosure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_1.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s1715six_w141 (hW141 : Inputs1719.W4Thm14_1Used) (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) {V L : Subgroup G}
    (h : Hyp125 D ⊥ V) (hL : L ∈ calC D.M) (hLb : barSub ⊥ V h.isElemAbelian L ≠ ⊥)
    (h7 : IsL2Over17 (Bar2 L) 7)
    (hfix : fixV (barSub ⊥ V h.isElemAbelian (UC22.conjClosure D.M L)) = ⊥)
    (hnormIn : normIn (Mbar D.M ⊥ V h.isElemAbelian) (barSub ⊥ V h.isElemAbelian L) =
      barSub ⊥ V h.isElemAbelian L ⊔
        centGroupIn (Mbar D.M ⊥ V h.isElemAbelian) (barSub ⊥ V h.isElemAbelian L))
    (hm4 : mBar D.M ⊥ V h.isElemAbelian = 4) :
    (∀ g ∈ Mbar D.M ⊥ V h.isElemAbelian,
      g ∉ normIn (Mbar D.M ⊥ V h.isElemAbelian) (barSub ⊥ V h.isElemAbelian L) →
        commSub (commSub ⊤ (barSub ⊥ V h.isElemAbelian L))
          ((barSub ⊥ V h.isElemAbelian L).map (MulAut.conj g).toMonoidHom) = ⊥) ∧
    (commSub ⊤ (barSub ⊥ V h.isElemAbelian L) = ⊤ →
      IsSubgroupOfAlt ↥(centGroupIn (Mbar D.M ⊥ V h.isElemAbelian)
        (barSub ⊥ V h.isElemAbelian L)) 8 ∧
      (7 ∣ Nat.card ↥(centGroupIn (Mbar D.M ⊥ V h.isElemAbelian)
          (barSub ⊥ V h.isElemAbelian L)) →
        IsAlt ↥(centGroupIn (Mbar D.M ⊥ V h.isElemAbelian)
            (barSub ⊥ V h.isElemAbelian L)) 7 ∨
        IsAlt ↥(centGroupIn (Mbar D.M ⊥ V h.isElemAbelian)
            (barSub ⊥ V h.isElemAbelian L)) 8 ∨
        IsL3 ↥(centGroupIn (Mbar D.M ⊥ V h.isElemAbelian)
            (barSub ⊥ V h.isElemAbelian L)) 1) ∧
      (IsL3 ↥(centGroupIn (Mbar D.M ⊥ V h.isElemAbelian)
          (barSub ⊥ V h.isElemAbelian L)) 1 →
        fixV (centGroupIn (Mbar D.M ⊥ V h.isElemAbelian)
          (barSub ⊥ V h.isElemAbelian L)) ≠ ⊥)) := by
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hcomp : IsComponentOf (barSub ⊥ V hV L) (Mbar D.M ⊥ V hV) :=
    barSub_mem_compBar_of_ne_bot h hL hLb
  have hYne : Mbar D.M ⊥ V hV ≠ ⊥ := by
    intro hbot
    exact hLb (le_bot_iff.1 (hbot ▸ hcomp.1))
  have hKgroup : CFSG.Open.IsKGroup ↥(Mbar D.M ⊥ V hV) :=
    isKGroup_mbar D hV hMs
  have hK : CFSG.IsKGroup ↥(Mbar D.M ⊥ V hV) :=
    CFSG.Assembly.kGroupAllSimple_of_kGroupNonab_of_catalogImp
      (fun X _ _ _ _ hh => hh) CFSG.Assembly.inCatalog_isoInvariant
      CFSG.Assembly.inCatalog_containsAbelianSimple hKgroup
  have hO2 : O2Trivial (Mbar D.M ⊥ V hV) :=
    fun P hP hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D h hP hN h2
  have hbasic : IsBasicModule (Mbar D.M ⊥ V hV) :=
    TwelveSeventeen.isBasicModule D hx h61 h127 h1214 h hYne
  have hL3 : IsL3 (Bar2 L) 1 := isL3_one_of_isL2Over17_seven h7
  have hsimple : IsSimpleGroup (Bar2 L) := isSimpleGroup_of_isL3 hL3
  obtain ⟨e⟩ := barSubBar2Equiv_of_isSimpleGroup h hL hLb hsimple
  have hL3b : IsL3 ↥(barSub ⊥ V hV L) 1 := CFSG.Blueprint.LieModel.of_mulEquiv e hL3
  have hXg : barSub ⊥ V hV (UC22.conjClosure D.M L) =
      ⨆ g ∈ Mbar D.M ⊥ V hV,
        (barSub ⊥ V hV L).map (MulAut.conj g).toMonoidHom := by
    rw [barSub_conjClosure_eq_iSup_of_hyp125 h hLM, iSup_subtype']
  have hm' : E3.mParam (Mbar D.M ⊥ V hV) = 4 := by simpa [mBar] using hm4
  exact hW141 (Vtil ⊥ V hV) (s15_Infra_vtil_sq_eq_one ⊥ V hV)
    (Mbar D.M ⊥ V hV) (barSub ⊥ V hV L)
    (barSub ⊥ V hV (UC22.conjClosure D.M L))
    (centGroupIn (Mbar D.M ⊥ V hV) (barSub ⊥ V hV L))
    hK hO2 hbasic hcomp hL3b hXg hfix hnormIn rfl hm'

theorem gap17_15_paraSixBranches_of_inputs (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q)
    (h1771 : R17_7_1At D V₀ V L r q hC) (h127 : R127 D) (h117 : C117 D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h111 : W3Thm111 G)
    (h1214 : F12.R1214 D) (h1217 : R1217 D)
    (h82 : F08.R82 D) (h880 : F08.R880 D) (h847 : UC22.R847ThinNe3 D) (h8107 : F08.R8107 D)
    (h920 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920odd D)
    (h119 : F11.R119 D) (hSg : UC6S846.SigmaStd D)
    (hW141 : Inputs1719.W4Thm14_1Used)
    (hB : B17_15BoundK2 D V₀ V L r q hC)
    (hpair : Gap17_15_pair D V₀ V L r q hC) :
    Gap17_15_paraSixBranches D V₀ V L r q hC := by
  intro h7 hV0 hk2 hm4
  subst hV0
  obtain ⟨H₁, H₂, hT₁, hH₁M, hT₂, hH₂M, hLH, hF₁, hF₂, hO₁, hO₂, hU⟩ := hpair h7
  set h := hC.hyp125 with hh
  have hV : IsElemAbelian 2 V := h.isElemAbelian
  have hUL : UniqueMax D.M L := h1771
  have hLb : barSub ⊥ V h.isElemAbelian L ≠ ⊥ :=
    barSub_ne_bot_of_uniqueMax h127 h h117 hC.memL hUL
  have hcompK : ∀ (K : Subgroup G), K ∈ calC D.M →
      barSub ⊥ V h.isElemAbelian K ≠ ⊥ →
      ∀ (m : G), m ∈ D.M →
        barSub ⊥ V h.isElemAbelian (conjSubgroup K m) = barSub ⊥ V h.isElemAbelian K →
          conjSubgroup K m = K :=
    fun K hK hKb m hm heq => s1715six_conj_eq_of_barSub_eq h hK hKb hm heq
  have hcompL : ∀ m ∈ D.M, barSub ⊥ V h.isElemAbelian (conjSubgroup L m) =
      barSub ⊥ V h.isElemAbelian L → conjSubgroup L m = L :=
    fun m hm heq => hcompK L hC.memL hLb m hm heq
  have hfix : fixV (barSub ⊥ V h.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ :=
    s1715six_fixV_eq_bot D hx h61 h126 h111 h hC.memL hUL hk2 hm4
      hT₁ hT₂ hF₁ hF₂ hO₁ hO₂ hU
  have hcent : V ⊓ centralizer ((UC22.conjClosure D.M L : Subgroup G) : Set G) = ⊥ :=
    s1715six_inf_centralizer_eq_bot D hx h61 h126 h111 h hC.memL hUL hk2 hm4
      hT₁ hT₂ hF₁ hF₂ hO₁ hO₂ hU
  have hfalse : ∀ t ∈ V, t ≠ 1 → (∀ k ∈ D.T, k * t = t * k) →
      centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) ≤ D.M → False :=
    fun t htV ht1 htT hCt =>
      s1715six_false_of_central D hx h61 h126 h111 h hk2 hm4
        hT₁ hT₂ hF₁ hF₂ hO₁ hO₂ hU htV ht1 htT hCt
  have hnorm : ((D.M ⊓ normalizer (L : Set G)).subgroupOf D.M).Normal :=
    s1715six_normalizer_normal D h82 hC.memL h7 hk2
  have hnot : ¬ CFSG.Quasithin.F6.IsPGL2 7 (Bar2 (L ⊔ NTL17 D L)) :=
    s1715six_not_pgl D hx h61 h126 h111 h127 hC h117 h1771 hB h7 rfl hk2 hm4 hfix
  have hnormIn : normIn (Mbar D.M ⊥ V h.isElemAbelian) (barSub ⊥ V h.isElemAbelian L) =
      barSub ⊥ V h.isElemAbelian L ⊔
        centGroupIn (Mbar D.M ⊥ V h.isElemAbelian) (barSub ⊥ V h.isElemAbelian L) :=
    s1715six_normIn_eq D h hC.memL hLb
      (fun n hn => s1715six_exists_inner D hC.memL h7 hnot hnorm hn)
  obtain ⟨h2, h3⟩ :=
    s1715six_w141 hW141 D hx h61 h127 h1214 h hC.memL hLb h7 hfix hnormIn hm4
  have hYne : Mbar D.M ⊥ V h.isElemAbelian ≠ ⊥ := by
    intro hbot
    exact hLb (le_bot_iff.1 (hbot ▸ (barSub_mem_compBar_of_ne_bot h hC.memL hLb).1))
  have hbasic : IsBasicModule (Mbar D.M ⊥ V h.isElemAbelian) :=
    TwelveSeventeen.isBasicModule D hx h61 h127 h1214 h hYne
  have hL3 : IsL3 (Bar2 L) 1 := isL3_one_of_isL2Over17_seven h7
  have hsimple : IsSimpleGroup (Bar2 L) := isSimpleGroup_of_isL3 hL3
  obtain ⟨ebar⟩ := barSubBar2Equiv_of_isSimpleGroup h hC.memL hLb hsimple
  have hL3b : IsL3 ↥(barSub ⊥ V h.isElemAbelian L) 1 :=
    CFSG.Blueprint.LieModel.of_mulEquiv ebar hL3
  have hsimpleb : IsSimpleGroup ↥(barSub ⊥ V h.isElemAbelian L) :=
    isSimpleGroup_of_isL3 hL3b
  by_cases hW : wTil ⊥ V h.isElemAbelian L = ⊤
  · refine Or.inr (s1715six_sig_eq_three D h hC.memL hLb hk2 hx h61 h127 hSg h880 h847 h8107
      h920 hL3 hL3b hcompK hnormIn h2 h3 hW
      (fun C hCle hCn hCs hCna =>
        exists_calC_cover_of_simple_normal D h127 h119 h hCle hCn hCs hCna)
      (fun H hHM hTH hf => s1715six_exists_central D h hHM hTH hf) hfalse)
  · exact Or.inl (s1715six_hyp154 h1217 h hC.memL hUL hLb hcompL h2 hfix hcent
      (fun x₀ hx₀ hx₀N m hm =>
        s1715six_conj_eq_or_eq D h82 hC.memL h7 hk2 (x₀ := x₀) (m := m) hx₀ hx₀N hm)
      hbasic hsimpleb hW)

theorem gap17_15_paraSix_of_inputs (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q)
    (h1217 : R1217 D) (hR127 : R127 D)
    (h117 : C117 D V₀ V) (h1771 : R17_7_1At D V₀ V L r q hC)
    (hSg : UC6S846.SigmaStd D) (hR1513 : R15_13Small D)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h111 : W3Thm111 G)
    (h1214 : F12.R1214 D) (h82 : F08.R82 D) (h880 : F08.R880 D) (h847 : UC22.R847ThinNe3 D)
    (h8107 : F08.R8107 D)
    (h920 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920odd D)
    (h119 : F11.R119 D)
    (hW141 : Inputs1719.W4Thm14_1Used) (hB : B17_15BoundK2 D V₀ V L r q hC)
    (hpair : Gap17_15_pair D V₀ V L r q hC) :
    Gap17_15_paraSix D V₀ V L r q hC :=
  gap17_15_paraSix_of D V₀ V L r q hC h1217 hR127 h117 h1771 hSg hR1513
    (gap17_15_paraSixBranches_of_inputs D V₀ V L r q hC h1771 hR127 h117 hx h61 h126 h111
      h1214 h1217 h82 h880 h847 h8107 h920 h119 hSg hW141 hB hpair)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
