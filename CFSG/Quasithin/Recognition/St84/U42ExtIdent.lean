module

public import CFSG.Quasithin.Recognition.St84.U42ExtCoords
public import CFSG.GH74.QTGen4.DSGen4.MainAmal
public import CFSG.GH74.QTGen4.DSGen4.Leaf.SylowS
public import CFSG.Quasithin.EmptyFaithful.S1421L2Two
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import Certificates.Certificate113
public import Certificates.Certificate4161
public import Certificates.Certificate2012
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.ClassicalGroups
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsDS
public import CFSG.GH74.QTGen4.DSGen4.LeafWrappersAmal
public import CFSG.GH74.QTGen4.U42.AmalgamPlain
public import CFSG.GH74.QTGen4.U42.ModelExtCore
public import CFSG.GH74.QTGen4.U42.ModelExtLatticeC
public import CFSG.GH74.QTGen4.U42.ModelP1
public import CFSG.GH74.QTGen4.U42.StubA4b
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP3
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP4Mod
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Psi
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixC
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.GH74.QTGen4.U42
  CFSG.Quasithin.Background.Harris.F112S3Big
  CFSG.Quasithin.H13.F431.U42 CFSG.Quasithin.H13.F431.U42Aut CFSG.Quasithin.A5Model
  CFSG.Quasithin.H13.A5
open scoped commutatorElement

variable {G : Type} [Group G]

structure U42ExtData (L1 L2 S : Subgroup G) : Prop where
  b6 : F112B6Loc L1 L2
  not_le_right : ¬ S ≤ L2
  oTwo_right : pCoreOf 2 L2 = dsQ L2 L1 S
  dsQ_right : dsQ L2 L1 S = dsZi L2 S
  card_right : Nat.card (pCoreOf 2 L2) = 2 ^ 4
  oTwo_left : pCoreOf 2 L1 = dsQ L1 L2 S
  card_left : Nat.card (pCoreOf 2 L1) = 2 ^ 5
  sup_eq : dsQ L2 L1 S ⊔ dsQ L1 L2 S = S ⊓ L2
  not_le : ¬ dsZi L2 S ≤ dsQ L1 L2 S
  perm5 : Nonempty (oTwoQuot ↥(L2 ⊔ bigB L2 L1 S) ≃* Equiv.Perm (Fin 5))
  s3s3 : Nonempty (oTwoQuot ↥(L1 ⊔ bigB L1 L2 S) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))

theorem isU4ExtTwo_of_u42ExtData [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hD : U42ExtData L1 L2 S) :
    IsU4ExtTwo 1 (f112Amalgam L1 L2 S) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hs3 : Nonempty (oTwoQuot ↥L1 ≃* Equiv.Perm (Fin 3)) :=
    isL2Quot_one_iff_perm3.mp hD.b6.1
  have hfr : U42ExtFrame L2 L1 S :=
    u42ExtFrame_of_local hR.symm hD.not_le_right hD.b6 hD.oTwo_right
      (by rw [hD.card_right]; norm_num) hD.perm5 (leafSylowS hR.symm).2.1
  obtain ⟨e, hB, hT, hU, hH, hUB⟩ :=
    dsuce_main hR.symm hD.not_le_right hs3 hD.b6 hD.oTwo_right hD.dsQ_right
      (by rw [hD.card_right]; norm_num) hD.oTwo_left
      (by rw [hD.card_left]; norm_num) hD.sup_eq hD.not_le
      hD.perm5 hD.s3s3 (leafSylowS hR.symm).2.1 (leafSylowS hR).2.1
  obtain ⟨eY, hY1, hY2⟩ := exists_model_coords_aligned
  have hφ : Function.Injective
      ((Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))).subtype.comp eY.toMonoidHom) :=
    Subtype.val_injective.comp eY.injective
  have hBY : ∀ g : ↥P2h, (g : Ah) ∈ P1h ↔
      ((eY g : Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))) : Mc) ∈ Bhc := by
    intro g
    have h1 : (g : Ah) ∈ P1h ↔ (g : Ah) ∈ Bh := ⟨fun h => ⟨h, g.2⟩, fun h => h.1⟩
    rw [h1, model_Bh_aligned_iff g]
    change _ ↔ ((eY g : Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))) : Mc).right 4 = 4
    rw [hY2 g]
  have hTY : ∀ g : ↥P2h, (g : Ah) ∈ That ↔
      ((eY g : Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))) : Mc) ∈ Thc := by
    intro g
    rw [model_That_aligned_iff g]
    change _ ↔ InD ((eY g : Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))) : Mc).right
    rw [hY2 g]
  have hUY : ∀ g : ↥P2h, (g : Ah) ∈ pCoreOf 2 P1h ↔
      ((eY g : Mof (⊤ : Subgroup (Equiv.Perm (Fin 5)))) : Mc) ∈ U0 := by
    intro g
    rw [← map_pCoreOf_P1h_aligned eY hY2]
    constructor
    · intro hg
      exact ⟨g, hg, rfl⟩
    · rintro ⟨a, ha, hab⟩
      have hag : a = g := hφ hab
      exact hag ▸ ha
  have hU0R : U0 ≤ Mof (⊤ : Subgroup (Equiv.Perm (Fin 5))) :=
    fun _ _ => mem_Mof.2 (Subgroup.mem_top _)
  have iso := amalgam_iso_of_coords (R := (⊤ : Subgroup (Equiv.Perm (Fin 5)))) (Bsub := Bhc)
    (Tsub := Thc) hU0R e eY hB hBY hT hTY hU hUY hH model_pairCore_extension hUB
  have iso' : Nonempty ((f112Amalgam L1 L2 S).Iso
      (RankTwoAmalgam.ofSubgroups P1h P2h)) := by
    simpa only [f112Amalgam, bigB_comm L1 L2 S] using iso
  refine ⟨Y, inferInstance, Ah, inferInstance, incl, lieModel_Y, incl_injective, ?_, That, P1h, P2h,
    CFSG.GH74.QTGen4.U42.ModelExtLatticeC.isYAmalgamPair_Ah, iso'⟩
  rw [← Yh_eq_range]
  exact index_Yh

end CFSG.Quasithin.F112R.St84
