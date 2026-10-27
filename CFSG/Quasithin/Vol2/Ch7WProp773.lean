module

public import CFSG.Quasithin.Vol2.Ch7Sec77LSide
public import CFSG.Quasithin.Vol2.Ch7Sec77L45Mod
public import CFSG.Quasithin.Vol2.Ch7Sec77Fac
public import CFSG.Quasithin.Vol2.Ch7Sec77WL3D

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H.BlkW
  CFSG.Quasithin.SBc17 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

namespace Setup

variable {S : Setup T L I} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem false_of_c27L3W
    (hMS : C134L32CorrM)
    (hC27 : ASC27Statement G) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h443 : Stmt4_4_3Orbit') (hC24a : ASC24One G)
    (hC24b : ASC24TwoChar G) (hF : CharTwo H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ fsuM T L)
    (h : C27SL3 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ∧
        Nonempty (↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
          (fsuV T I : Set G))))) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) :
    False := by
  obtain ⟨⟨eK⟩, hCK, ⟨eX⟩, hL₀K, hTpK, hH⟩ :=
    C.basic_of_c27L3 hC27 h37c h38c h443 hC24a hC24b hF hK hKq hKM h
  have hc := C.conf.hc
  have hQN : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    (le_inf inf_le_left (inf_le_right.trans C.centralizer_V_le)).trans hTpK
  have h32 := C.le_relIndex_Q_of_sl3 hF hK hQN eK hCK eX h.1.2.1 hL₀K
  have hi := C.c134Two_of_sl3W hMS hF hK hQN h.1.2.2 eX hL₀K hTpK hH
  have h128 := C.relIndex_Q_le_of_sl3 hF hK hQN eX hL₀K hi
  have h16 := relIndex_centralizer_V hc
  rcases relIndex_centralizer_th_or hc S.fsuV_le_Q le_rfl
      (le_sup_left.trans S.LT_le_normalizer_Q) (le_sup_right.trans S.LT_le_normalizer_Q)
    with h1 | h1
  · omega
  · omega

theorem false_of_minConfW
    (h3108 : Stmt3_2_10_eight) (h443 : Stmt4_4_3Orbit') (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h36c : Vol2Native.A36CoreForSQTKCat) (h36 : A36ForSQTK) (h755 : Input7_5_5)
    (kf1 : OutTwoNilpotentFact) (h23 : A23SQTKListFact) (hA23 : A23FourCentralFact)
    (hmult : LieMultiplierFact) (hcart : LieCartanFact) (hthom : LieThompsonFact) (h56 : AsB56)
    (hC27 : ASC27Statement G) (hC24a : ASC24One G) (hC24b : ASC24TwoChar G) (hA : A318Facts)
    (hE : CFSG.Quasithin.Vol2.Ch11.SecA.FactA318Excl) (hSp4 : Sp4PlaneFixFact) (h51 : AsB51)
    (hI16 : AsI16Cover) (hA8 : AsI16CoverA8) (hMS : C134L32CorrM) : False := by
  have hF : CharTwo H :=
    C.conf.charTwo h3108 h443 h37 h38 h37c h38c h755 kf1 h23 hA23 hmult hcart hthom
  obtain ⟨K, hKJ, hKM, hq, hl⟩ := C.exists_cComp_quasisimple h3108 h56 h39 hF
  have hKq := C.isQuasisimple_K h443 h36c hF hKJ hKM hq hl
  have hK : K ∈ cComp H := S153D.mem_cComp_of_mem_cComp_thompsonJ hKJ
  rcases C.c27Cases_rest4 hC27 h443 hC24a hC24b h36 h38 hA hE hSp4 hF hK hKq hKM with hg | hh
  · exact C.false_of_c27L3W hMS hC27 h37c h38c h443 hC24a hC24b hF hK hKq hKM hg
  · exact C.false_of_c27L45 hC27 h443 hC24a hC24b hA h36 h38 h51 hI16 hA8 hF hK hKq hKM hh

end MinConf

theorem centralizer_V0_leW
    (S : Setup T L I)
    (h3104 : Stmt3_2_10_four) (h3108 : Stmt3_2_10_eight) (h443 : Stmt4_4_3Orbit')
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h36c : Vol2Native.A36CoreForSQTKCat) (h36 : A36ForSQTK)
    (h755 : Input7_5_5) (kf1 : OutTwoNilpotentFact) (h23 : A23SQTKListFact)
    (hA23 : A23FourCentralFact) (hmult : LieMultiplierFact) (hcart : LieCartanFact)
    (hthom : LieThompsonFact) (h56 : AsB56) (hC27 : ASC27Statement G) (hC24a : ASC24One G)
    (hC24b : ASC24TwoChar G) (hA : A318Facts) (hE : CFSG.Quasithin.Vol2.Ch11.SecA.FactA318Excl)
    (hSp4 : Sp4PlaneFixFact) (h51 : AsB51) (hI16 : AsI16Cover) (hA8 : AsI16CoverA8)
    (hMS : C134L32CorrM) {θ : G} (hθL : θ ∈ L)
    (hθ3 : θ ^ 3 ∈ Subgroup.centralizer (fsuV T I : Set G))
    (hθ1 : θ ∉ Subgroup.centralizer (fsuV T I : Set G)) :
    Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) : Subgroup G) :
      Set G) ≤ fsuM T L := by
  refine Setup.centralizer_V0_le_of_sylow (S := S) h3104 (fun θ' e' hc hG hM => ?_) hθL hθ3 hθ1
  by_contra hnot
  obtain ⟨H, C⟩ := exists_minConf hc rfl hG hM hnot
  exact C.false_of_minConfW h3108 h443 h37 h38 h39 h37c h38c h36c h36 h755 kf1 h23 hA23 hmult
    hcart hthom h56 hC27 hC24a hC24b hA hE hSp4 h51 hI16 hA8 hMS

end Setup

theorem stmt7_7_3_ofW
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight)
    (h711n : Stmt7_1_1_normal) (h325 : Stmt3_2_5) (h3104 : Stmt3_2_10_four)
    (h3108 : Stmt3_2_10_eight) (h443 : Stmt4_4_3Orbit') (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (h36c : Vol2Native.A36CoreForSQTKCat) (h36 : A36ForSQTK)
    (h755 : Input7_5_5) (kf1 : OutTwoNilpotentFact) (h23 : A23SQTKListFact)
    (hA23 : A23FourCentralFact) (hmult : LieMultiplierFact) (hcart : LieCartanFact)
    (hthom : LieThompsonFact) (h56 : AsB56)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (hC24a : ∀ (G : Type) [Group G] [Finite G], ASC24One G)
    (hC24b : ∀ (G : Type) [Group G] [Finite G], ASC24TwoChar G) (hA : A318Facts)
    (hE : CFSG.Quasithin.Vol2.Ch11.SecA.FactA318Excl) (hSp4 : Sp4PlaneFixFact) (h51 : AsB51)
    (hI16 : AsI16Cover) (hA8 : AsI16CoverA8) (hMS : C134L32CorrM) : Stmt7_7_3 := by
  intro G _ _ T L I hyp h731 hcomm hrow θ hθL hθ3 hθ1
  have S : Setup T L I := Setup.of h37 h38 h39 h3228 h711n h325 hyp h731 hrow
  exact Setup.centralizer_V0_leW S h3104 h3108 h443 h37 h38 h39 h37c h38c h36c h36 h755 kf1 h23
    hA23 hmult hcart hthom h56 (hC27 G) (hC24a G) (hC24b G) hA hE hSp4 h51 hI16 hA8 hMS hθL hθ3
    hθ1

end CFSG.Quasithin.H13.Sec77
