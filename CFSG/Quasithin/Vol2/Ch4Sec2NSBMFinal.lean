module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBMCoord
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKFinal
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBMAlt

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

theorem nsbModuleStructure_of (hN31 : NotC31)
    (h22 : ∀ (G : Type) [Group G] [Finite G], ASC22Three G)
    (h27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h51 : AsB51) (hI16 : AsI16Cover) (hA8 : AsI16CoverA8) : NSBModuleStructure := by
  intro G _ _ T M L Mm I H K m k hd n hnm hpsl
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  obtain ⟨hU, n', j, hn', hj1, hjn, hds⟩ := exists_directSum_of_nsb hN31 h22 h27 h51 hI16 hA8 hd
  rcases hc.described with ⟨hcomp, h31'⟩ | ⟨hKc, hCT, hqs, hKM, h41'⟩
  · exact (hN31 G T M L Mm I H K m k hd hcomp h31').elim
  · have h4 := c41Case4_of_conclusion hd h41'
    have hred := C48Pf.isTwoReducedIn_U (h27 G) hc.hypC28 hKc hCT hqs hKM h41'
    have hKU : K ≤ Subgroup.normalizer ((uBig I K : Subgroup G) : Set G) :=
      le_sup_left.trans hred.2.1
    have hker := C48Pf.ker_autOnHom_eq (h27 G) hc.hypC28 hKc hCT hqs hKM h41' h4 hKU
    obtain ⟨α, β, hαs, hαk, hβb, hβe, hcard⟩ := exists_coords_of_directSum hU hKU hj1 hds
    let e : ModO2 K ≃* ↥(autOn K (uBig I K)) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ (InternalSec.autOnHom_surjective hKU))
    have hcardK : Nat.card (ModO2 K) = Nat.card ↥(autOn K (uBig I K)) := Nat.card_congr e.toEquiv
    have hnn : n' = n := by
      rcases hn' with rfl | rfl
      · rw [card_statedSL_four_zmod1527d] at hcard
        rcases hnm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
        · rfl
        · exfalso
          have h := card_of_isPSL_two1522 5 hpsl
          rw [hcardK, hcard] at h
          revert h
          decide
        · exfalso
          have h := card_of_isPSL_two1522 5 hpsl
          rw [hcardK, hcard] at h
          revert h
          decide
      · rw [card_statedSL_five_zmod1527d] at hcard
        rcases hnm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exfalso
          have h := card_of_isPSL_two1522 4 hpsl
          rw [hcardK, hcard] at h
          revert h
          decide
        · rfl
        · rfl
    subst hnn
    exact ⟨j, α, β, by omega, hαs, hαk.trans hker, hβb, hβe⟩

theorem conf4212NoSumBig_of_flip53
    (h22 : ∀ (G : Type) [Group G] [Finite G], ASC22Three G)
    (h27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h425 : Thm4_2_5) (h48 : ∀ (G : Type) [Group G] [Finite G], ASC48Statement G)
    (h51 : AsB51) (hI16 : AsI16Cover) (hA8 : AsI16CoverA8)
    (hF53 : NSBLocalFlipFiveThree) : Conf4212NoSumBig :=
  conf4212NoSumBig_of_nsb_inputs h22 h27 h36 h37 h38 h39 h425 h48
    (nsbModuleStructure_of notC31_holds h22 h27 h51 hI16 hA8) hF53

end CFSG.Quasithin.H13.Ch4.NSB
