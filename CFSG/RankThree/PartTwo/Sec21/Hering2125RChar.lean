module

public import CFSG.RankThree.PartTwo.Sec21.Hering2125Reduce
public import CFSG.LieType.BorelTits.HeringCharTwoGeneral
public import CFSG.HardMathSupport.Dickson.KD.CharPAux.RadCent
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67ExcPar
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Par
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4Inner

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2125

open CFSG CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.HardMathSupport.Dickson.KD

theorem radCent_adjointGroup (τ : Tag) (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] : RadCent (adjointGroup τ K) p :=
  radCent_of_pCharData (conj_mem_diagonalFieldActors τ K) center_adjointGroup_eq_bot
    (pCharData_adjoint τ K p)

theorem isCharTwoType_of_g2Model {X : Type} [Group X] {n : ℕ}
    (h : Blueprint.ChevalleyExceptionalModel X .G2 2 n) : IsCharTwoType X := by
  have hBT : Holds X 2 := holds_of_chevalleyExceptionalModel h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_natCard_eq hK
  let eC : X ≃* adjointGroup .G2 K :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  haveI : Finite (adjointGroup .G2 K) := inferInstance
  haveI : Finite X := Finite.of_equiv _ eC.symm.toEquiv
  exact isCharTwoType_of_holds hBT (RadCent.of_mulEquiv eC (radCent_adjointGroup .G2 K 2))

theorem radCent_graphFixedRootGroup (t : TwistTag) (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hσ : σ ^ t.order = 1) (p : ℕ) [Fact p.Prime] [CharP K p]
    (hcen : Subgroup.center (graphFixedRootGroup t K σ.toRingHom) = ⊥) :
    RadCent (graphFixedRootGroup t K σ.toRingHom) p := by
  haveI : Finite (graphFixedRootGroup t K σ.toRingHom) :=
    Finite.of_injective (fun g => (g : ModGL t.tag K)) Subtype.val_injective
  exact radCent_of_pCharData (par_conj_mem_fixedDiagonalFieldActors t K σ) hcen
    (pCharData_fixed t K σ hσ p)

theorem isCharTwoType_of_d4Model {X : Type} [Group X] {n : ℕ}
    (h : Blueprint.ChevalleyExceptionalModel X .trialityD4 2 n) : IsCharTwoType X := by
  have hBT : Holds X 2 := holds_of_chevalleyExceptionalModel h
  obtain ⟨hadm, K, _, _, hK, σ, hσ, ⟨e⟩⟩ := h
  have hn : 1 ≤ n := hadm.2.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK3 : Nat.card K = (2 ^ n) ^ 3 := hK
  haveI : CharP K 2 := charP_of_natCard_eq (f := n * 3) (by rw [hK3, pow_mul])
  let σ' : K ≃+* K :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσ' : ∀ c, σ' c = c ^ (2 ^ n) := hσ
  obtain ⟨-, -, -, -, -, -, hcen, ⟨eQ⟩⟩ :=
    even_triality_exact_automorphism_normal_form hn K hK3 σ' hσ'
  have hσ3 : σ' ^ TwistTag.D4.order = 1 := d4_sigma_pow_order K hK3 σ' hσ'
  let eC : X ≃* graphFixedRootGroup TwistTag.D4 K σ'.toRingHom := e.trans eQ
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K σ'.toRingHom) :=
    Finite.of_injective (fun g => (g : ModGL TwistTag.D4.tag K)) Subtype.val_injective
  haveI : Finite X := Finite.of_equiv _ eC.symm.toEquiv
  exact isCharTwoType_of_holds hBT
    (RadCent.of_mulEquiv eC (radCent_graphFixedRootGroup TwistTag.D4 K σ' hσ3 2 hcen))

theorem item2125CharTwo : Item2125CharTwo :=
  ⟨fun _ _ _ h => isCharTwoType_of_g2Model h, fun _ _ _ h => isCharTwoType_of_d4Model h⟩

end CFSG.RankThree.PartTwo.Sec21.Hering2125
