module

public import CFSG.Quasithin.Vol2.Ch1Unique4
public import CFSG.Quasithin.Vol2.Ch12Sec4Lemma5

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

structure Ctx (T L V E : Subgroup G) (z v : G) [IsMulCommutative ↥V] : Prop where
  cx : Cx1242 G T L V
  q3 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
  f : CxFacts G T L V z
  card16 : Nat.card V = 2 ^ 4
  simple : IsSimpleGroup (autOn L V)
  card168 : Nat.card (autOn L V) = 168
  nat : BinaryNaturalSL (autOn L V) ⊤ (fixV (autOn L V)) 3 1
  Q : pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (V : Set G)
  Tbar : autOn T V = autOn (T ⊓ L) V
  Tsyl : QuasithinUnique.IsSylowTwoOf (autOn (T ⊓ L) V) (autOn L V)
  EV : E ≤ V
  E4 : Nat.card E = 4
  TE : T ≤ Subgroup.normalizer (E : Set G)
  vE : v ∈ E
  vL : v ∉ Subgroup.centralizer (L : Set G)
  ZL : ⁅quasithinOmegaOneCenter T, L⁆ = ⊥
  ZQ : omegaOneCenterOf (pCoreOf 2 (L ⊔ T)) = quasithinOmegaOneCenter T ⊔ V
  off : ∀ A : Subgroup G, IsMaxElemAbelian (T ⊓ Subgroup.centralizer (E : Set G)) A →
    ¬ A ≤ pCoreOf 2 (L ⊔ T) → autOn A V = autOn (T ⊓ Subgroup.centralizer (E : Set G)) V
  uniq : IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G))
  disj : ∀ g : G, g ∉ Subgroup.normalizer (L : Set G) →
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) ⊓
      conjSubgroup (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G)) g = ⊥
  char : QuasithinUnique.CharTwo (L ⊔ T)
  perf : ∀ N : Subgroup G, N ≤ L → (N.subgroupOf L).Normal →
    (∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = L
  comp : L ∈ cComp (L ⊔ T)
  sqtk : SQTKGroup ↥(L ⊔ T)
  sqtkM : SQTKGroup ↥(Subgroup.normalizer (L : Set G))
  even : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G
  sylow : quasithinIsSylowTwo T

theorem exists_ctx (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (hpre : Pre1242)
    (h3228 : Stmt3_2_2_eight) (h1229 : Stmt12_2_9) (h51 : AsB51) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) {T L V : Subgroup G} (hcx : Cx1242 G T L V)
    (h3 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    {E : Subgroup G} (hEV : E ≤ V) (hE4 : Nat.card E = 4)
    (hTE : T ≤ Subgroup.normalizer (E : Set G)) :
    ∃ (z v : G) (_ : IsMulCommutative ↥V), Ctx T L V E z v := by
  have hyp := hcx.hyp
  obtain ⟨z, hf⟩ := CxFacts.of h331 h1222 hpre hcx (Or.inl h3)
  have := hf.comm
  obtain ⟨hV16, hGrs, hGr, hnat⟩ := cx_l3_module h1222 hcx hf h3
  have hQ := pCoreOf_sup_eq_of_hyp1223 h1222 h3228 hyp
  obtain ⟨hTsyl, hTeq⟩ := cx_autOn_T_eq hcx hf hnat
  obtain ⟨hZL, hZQ, hoff⟩ := lemma12_4_5_of h331 h1222 hpre h3228 h1229 h51 G T L V hcx h3 E hEV
    hE4 hTE
  obtain ⟨v, hvE, hvL⟩ : ∃ v ∈ E, v ∉ Subgroup.centralizer (L : Set G) := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (le_inf hEV (fun x hx => h x hx) :
      E ≤ V ⊓ Subgroup.centralizer (L : Set G))
    rw [hE4, hf.card_zV] at this
    omega
  have hcc := hyp.conjClosure_eq
  have huniq := lemma_1_2_7_three hyp.qtke hyp.simple hyp.nonabelian h37 h38 h39 hyp.sylow
    hyp.maximal
  rw [hcc] at huniq
  have hO2 : pCoreOf 2 (L ⊔ T) ≠ ⊥ := hyp.maximal.1.2.2.2
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.sylow
  have hchar : QuasithinUnique.CharTwo (L ⊔ T) := by
    have hH : InH (S : Subgroup G) (L ⊔ (S : Subgroup G)) := ⟨le_sup_right, hS ▸ hO2⟩
    have := charTwo_of_inH hyp.qtke.2.1 S hH
    rwa [hS] at this
  have hMloc := huniq.1.1
  refine ⟨z, v, this, ⟨hcx, h3, hf, hV16, hGrs, hGr, hnat, hQ, hTeq, hTsyl, hEV, hE4, hTE, hvE,
    hvL, hZL, hZQ, hoff, huniq, fun g hg => ?_, hchar, hyp.faithful.2.1,
    cComp_of_isLocal hyp.maximal.1,
    sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian hO2,
    sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian
      (pCoreOf_ne_bot_of_isTwoLocal hMloc.1), hyp.qtke.2.1, hyp.sylow⟩⟩
  have h := lemma_1_2_7_four hyp.qtke hyp.simple hyp.nonabelian h37 h38 h39 hyp.sylow hyp.maximal
    (g := g) (by rwa [hcc])
  rwa [hcc] at h

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V] (c : Ctx T L V E z v)
include c

abbrev R1 (_ : Ctx T L V E z v) : Subgroup G := T ⊓ Subgroup.centralizer (E : Set G)

theorem V_le_Q : V ≤ pCoreOf 2 (L ⊔ T) := by
  rw [c.Q]
  exact le_inf c.f.le_T c.f.le_centralizer

theorem Q_le_R1 : pCoreOf 2 (L ⊔ T) ≤ c.R1 := by
  rw [c.Q]
  exact inf_le_inf_left T (Subgroup.centralizer_le c.EV)

theorem E_le_R1 : E ≤ c.R1 :=
  (c.EV.trans c.V_le_Q).trans c.Q_le_R1

theorem R1_le_T : c.R1 ≤ T := inf_le_left

theorem Z_le_omega_R1 : quasithinOmegaOneCenter T ≤ omegaOneCenterOf c.R1 := by
  rw [quasithinOmegaOneCenter, Subgroup.closure_le]
  rintro x ⟨⟨hxT, hxC⟩, hx2⟩
  refine Subgroup.subset_closure ⟨⟨⟨hxT, ?_⟩, ?_⟩, hx2⟩
  · exact Subgroup.centralizer_le (c.EV.trans c.f.le_T) hxC
  · exact Subgroup.centralizer_le (inf_le_left : (c.R1 : Set G) ⊆ T) hxC

end Ctx

end N1246

end CFSG.Quasithin.H13
