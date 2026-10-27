module

public import CFSG.Quasithin.Vol2.Ch7Sec77Mod
public import CFSG.Quasithin.Vol2.Ch7Sec77Cases2
public import CFSG.Quasithin.EmptyFaithful.T1515eC

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H.BlkW
  CFSG.Quasithin.SBc17 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem threePart_mem (hA : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) {K : Subgroup G}
    (hK : K ∈ cComp H) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) {X : Type} [Group X]
    [Finite X] (eX : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* X) (hX : A318Exclusion X) {r b : ℕ}
    (hyb : orderOf (θ ^ r) = 3 ^ b) : θ ^ r ∈ K := by
  rw [eq_oPrimeResidualOf_three_of_exclusion hA h36 h38 C.hypC23.sqtk hK hKq eX hX]
  exact Subgroup.subset_closure ⟨H.pow_mem C.conf.th_mem_H r, b, hyb⟩

theorem false_of_c27A7 (hA : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) (hF : CharTwo H)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (h7 : CFSG.QuasithinUnique.IsAltType K 7) : False := by
  obtain ⟨r, b, hr, hyb⟩ := exists_threePart θ
  obtain ⟨α, hαs, hαk, -⟩ := id h7
  have eX : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  exact C.false_of_altType7 hF hK h7 hr
    (C.threePart_mem hA h36 h38 hK hKq eX a318Exclusion_alt7 hyb) hyb

theorem false_of_c27ExcA7 (hA : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hF : CharTwo H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (h : CFSG.Quasithin.IsExcA7Block K) :
    False := by
  obtain ⟨r, b, hr, hyb⟩ := exists_threePart θ
  obtain ⟨-, ⟨α, hαs, hαk⟩, -⟩ := id h
  have eX : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  exact C.false_of_excA7 hF hK h hr
    (C.threePart_mem hA h36 h38 hK hKq eX a318Exclusion_alt7 hyb) hyb

theorem false_of_c27A6 (hA : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) (hF : CharTwo H)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (h6 : CFSG.Quasithin.IsAltBlockType K 6) : False := by
  obtain ⟨r, b, hr, hyb⟩ := exists_threePart θ
  obtain ⟨-, α, hαs, hαk, -⟩ := id h6
  have eX : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  exact C.false_of_altBlock6 hF hK h6 hr
    (C.threePart_mem hA h36 h38 hK hKq eX a318Exclusion_alt6 hyb) hyb

theorem c27Cases_rest3 (hC27 : ASC27Statement G) (h443 : Stmt4_4_3Orbit')
    (hC24a : ASC24One G) (hC24b : ASC24TwoChar G) (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (hA : A318Facts) (hF : CharTwo H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ fsuM T L) :
    (CFSG.Quasithin.IsSp4Block K ∧
        IsMaxParabolic2 (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
          (fsuV T I : Set G))))) (autOn (fsuM T L ⊓ H ⊓ K) (omegaOneCenterOf (pCoreOf 2
          (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))))) ∨
      C27G2 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) ∨
      (C27SL3 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
          (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) ∧
        ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ∧
          Nonempty (↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer
            (fsuV T I : Set G))))) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) ∨
      C27L45 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) := by
  rcases C.c27Cases_rest2 hC27 h443 hC24a hC24b h36 hF hK hKq hKM with h | h | h | h | h | h | h
  · exact (C.false_of_c27A7 hA h36 h38 hF hK hKq h.2.1).elim
  · exact (C.false_of_c27A7 hA h36 h38 hF hK hKq h.2.1).elim
  · exact (C.false_of_c27ExcA7 hA h36 h38 hF hK hKq h.1).elim
  · rcases h.1 with h6 | h4
    · exact (C.false_of_c27A6 hA h36 h38 hF hK hKq h6).elim
    · exact Or.inl ⟨h4, h.2⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
