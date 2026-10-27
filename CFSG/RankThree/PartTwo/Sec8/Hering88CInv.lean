module

public import CFSG.RankThree.PartTwo.Sec8.Hering88Swap
public import CFSG.RankThree.PartTwo.Sec8.Hering88CKey
public import CFSG.RankThree.PartTwo.Sec8.Hering88CType
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Late.Transitivity
import CFSG.Goldschmidt.Steps.G55Basic
import CFSG.RankThree.PartTwo.Sec4.HeringK419Sp4
import CFSG.RankThree.PartTwo.Sec4.HeringK419Sp4Out
import CFSG.RankThree.PartTwo.Sec4.HeringK419G2
import CFSG.RankThree.PartTwo.Sec4.HeringK419F4Holds
import CFSG.RankThree.PartTwo.Sec4.HeringK419Tits
import CFSG.RankThree.PartTwo.Sec4.HeringK419U33
import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofOrders

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo


theorem kF88SwapInv_of
    (h45 : Sec4.Item4_5) (h84 : Pair84A)
    (hAut : Sec4.K419AutThree) (hT : Hering88C.KF89JCentType419) : KF88SwapInv := by
  intro G _ _ A c L a b X n h Y hY hIJ x hx hxY
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hG := h.toTheoremFourHyp
  have hAel := h.mem_partTwoF.1
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have haA : a ∈ A := h.a_mem
  have ha3 : a ^ 3 = 1 := hAel.2 a haA
  obtain ⟨hbA, hb1, hm, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have hb3 : b ^ 3 = 1 := hAel.2 b hbA
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAel.2 g g.2)⟩
  have hAC : ∀ {e : G}, e ∈ A → A ≤ Subgroup.centralizer ({e} : Set G) := fun he u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu _ he)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 hG hb3 hb1 hAp (hAC hbA) X
      h.pairRel.2.2.1
  have hAH : A ≤ Subgroup.centralizer ({a} : Set G) := hAC haA
  have hAHn : A ≤ Subgroup.normalizer (Subgroup.centralizer ({a} : Set G) : Set G) :=
    hAH.trans Subgroup.le_normalizer
  have hAJ : A ≤ Subgroup.normalizer (sec8J X a : Set G) := fun u hu =>
    Item812Res2.mem_normalizer_inSubgroup_perfectResidual (Late.le_normalizer_inf hAX hAHn hu)
  have hk := h84 G A c L a b X n h
  have haN : a ∈ Subgroup.normalizer (X : Set G) := by
    rcases hk with h' | h'
    · exact h'.mem_normalizer
    · exact h'.mem_normalizer
  have hout : Sec4.InducesOuterTheta a X := by
    rcases hk with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X h' (by decide)
  have hXb : X ≤ Subgroup.centralizer ({b} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.pairRel.2.2.1).1
  have habs : a ∉ Subgroup.zpowers b := Item87Proof.not_mem_zpowers_of_inducesOuterTheta hXb hout
  obtain ⟨-, -, -, -, -, e', m, hem⟩ := h.mem_pairOmega
  have hm1 : 1 ≤ m := hem.2.2.1
  have htype := hT G X a m hm1 (Item87Proof.isGammaType_of_isGammaIndex hem) h.not_unitary ha3 hk
    h.gTwoPartner
  have hJX : sec8J X a ≤ X := (Item87Proof.residual_le _).trans inf_le_left
  have hJa : sec8J X a ≤ Subgroup.centralizer ({a} : Set G) :=
    (Item87Proof.residual_le _).trans inf_le_right
  have himg : imageModTheta X (sec8J X a) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) X) :=
    KFacts.imageModTheta_perfectResidual_centralizer_eq haN ⟨1, by rwa [pow_one]⟩
  have eR : imageModTheta X (sec8J X a) ≃*
      perfectResidual (barCentralizer (Subgroup.zpowers a) X) :=
    (MulEquiv.subgroupCongr himg).trans
      ((perfectResidual (barCentralizer (Subgroup.zpowers a) X)).equivMapOfInjective
        (barCentralizer (Subgroup.zpowers a) X).subtype
        (barCentralizer (Subgroup.zpowers a) X).subtype_injective).symm
  have htype' : Sec4.IsType419 (imageModTheta X (sec8J X a)) :=
    Sec4.Item419Res3.isType419_of_mulEquiv eR htype
  have h2 : 2 ∣ Nat.card (imageModTheta X (sec8J X a)) :=
    (show 2 ∣ 4 by norm_num).trans (Sec4.Res419Two.four_dvd_card htype')
  have hba : Commute b a := hAc b hbA a haA
  have hC₀ := Sec5.isElemAbelian_sup_zpowers (p := 3)
    (CFSG.Goldschmidt.G55.isElemAbelian_zpowers hb3) habs
    ha3 (fun s hs => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      exact (hba.zpow_left k).eq)
  set C₀ : Subgroup G := Subgroup.zpowers b ⊔ Subgroup.zpowers a with hC₀def
  have hC₀card : Nat.card C₀ = 9 := by
    rw [hC₀.2, Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have hC₀A : C₀ ≤ A := sup_le (Subgroup.zpowers_le.mpr hbA) (Subgroup.zpowers_le.mpr haA)
  have hC₀lt : C₀ < A := lt_of_le_of_ne hC₀A fun heq => by
    rw [heq, h.card_eq] at hC₀card
    norm_num at hC₀card
  obtain ⟨e, heA, heC⟩ := SetLike.exists_of_lt hC₀lt
  have hE := Sec5.isElemAbelian_sup_zpowers (p := 3) hC₀.1 heC (hAel.2 e heA)
    (fun s hs => hAc s (hC₀A hs) e heA)
  set E : Subgroup G := C₀ ⊔ Subgroup.zpowers e with hEdef
  have hEcard : Nat.card E = 27 := by rw [hE.2, hC₀card]
  have hEA : E ≤ A := sup_le hC₀A (Subgroup.zpowers_le.mpr heA)
  have heE : e ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  have hC₀cent : C₀ ≤ Subgroup.centralizer ((sec8J X a : Subgroup G) : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact Subgroup.mem_centralizer_singleton_iff.mp (hXb (hJX hj))
    · rw [Subgroup.mem_centralizer_iff]
      intro j hj
      exact Subgroup.mem_centralizer_singleton_iff.mp (hJa hj)
  have hC : ∀ g ∈ C₀, ∀ j ∈ sec8J X a,
      g * j * g⁻¹ * j⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) X := by
    intro g hg j hj
    have : g * j = j * g := (Subgroup.mem_centralizer_iff.mp (hC₀cent hg) j hj).symm
    rw [this, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  obtain ⟨S, hSJ, hS1, hS2, hES⟩ := Hering88C.exists_invariant_two_of_isType419 hAut hJX htype' h2
    (hAp.to_le hEA) (hEA.trans hAX) (hEA.trans hAJ) (le_sup_left : C₀ ≤ E) heE
    (hAel.2 e heA) le_rfl hC
  exact ⟨E, ⟨hE.1, hEcard, S, hS1, hS2, hES⟩, hEA, S,
    ⟨hSJ.trans (le_sup_right.trans hIJ), (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS2, hES⟩,
    hS1⟩

theorem kF88SwapInv_holds
    (h45 : Sec4.Item4_5) (h84 : Pair84A) : KF88SwapInv :=
  kF88SwapInv_of h45 h84 (Sec4.k419AutThree_of Sec4.k419AutThreeInnerSp4_holds
      Sec4.k419AutThreeOuterSp4_holds Sec4.k419AutThreeInnerG2_holds Sec4.k419AutThreeOuterG2_holds
      Sec4.k419AutThreeInnerF4_holds Sec4.k419AutThreeOuterF4_holds Sec4.k419AutThreeInnerTits_holds
      Sec4.k419AutThreeInnerU33_holds) Hering88C.kF89JCentType419_holds

end CFSG.RankThree.PartTwo.Sec8
