module

public import CFSG.Quasithin.Vol2.Ch3Sec3Close
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3328

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

@[expose] def Stmt3_3_28G2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsG2Block L → tC L T = ⊥ ∧ qL L T = vPlus L T

@[expose] def Stmt3_3_28G2TC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsG2Block L → tC L T = ⊥

@[expose] def Insp3_3_30 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G), Setup331 G T M L →
    IsG2Block L → T ≤ Subgroup.normalizer (L : Set G) → tC L T = ⊥ → qL L T = vPlus L T →
    (∀ B : Subgroup G, B ≤ T → IsElemAbelian 2 B → Nat.card ↥B ≤ Nat.card ↥(vPlus L T)) ∧
    (∀ B : Subgroup G, IsMaxElemAbelian T B → T ≤ Subgroup.normalizer (B : Set G) →
      ¬ B ≤ vPlus L T → ∃ b ∈ B, vPlus L T ⊓ Subgroup.centralizer (B : Set G) =
        vPlus L T ⊓ Subgroup.centralizer ({b} : Set G)) ∧
    ∀ B B' : Subgroup G, IsMaxElemAbelian T B → IsMaxElemAbelian T B' →
      T ≤ Subgroup.normalizer (B : Set G) → T ≤ Subgroup.normalizer (B' : Set G) →
      ¬ B ≤ vPlus L T → ¬ B' ≤ vPlus L T → B ⊔ vPlus L T = B' ⊔ vPlus L T

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

namespace Hyp331

theorem card_autOn_dvd (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥(autOn L (vPlus L T)) ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hred := vPlus_reduced h.toSetup331
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  have hQC : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hle : CFSG.pCore 2 ↥L ≤ (InternalSec.autOnHom hLV).ker := by
    intro l hl
    rw [InternalSec.mem_ker_autOnHom]
    exact hQC (hOQ ((mem_pCore_iff l).mp hl))
  refine Subgroup.card_dvd_of_surjective
    (f := QuotientGroup.lift _ (InternalSec.autOnHom hLV) hle) ?_
  intro y
  obtain ⟨l, rfl⟩ := InternalSec.autOnHom_surjective hLV y
  exact ⟨QuotientGroup.mk l, rfl⟩

theorem isPSL_of_isLnBlock
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hLn : IsLnBlock L 3) :
    IsPSL 3 2 1 ↥(autOn L (vPlus L T)) := by
  have hred := vPlus_reduced h.toSetup331
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  have hQC : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hCLV := inf_centralizer_le_of_isLnBlock hLn hLV (hOQ.trans hQC)
    (h.not_L_le_centralizer h38 h39)
  obtain ⟨-, α, hαs, hαk, -⟩ := hLn
  have hker : (InternalSec.autOnHom hLV).ker = α.ker := by
    rw [hαk]
    ext l
    rw [InternalSec.mem_ker_autOnHom, mem_pCore_iff]
    exact ⟨fun hl => hCLV (Subgroup.mem_inf.mpr ⟨l.2, hl⟩), fun hl => hQC (hOQ hl)⟩
  let e₁ : ↥(autOn L (vPlus L T)) ≃* ↥L ⧸ α.ker :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (InternalSec.autOnHom_surjective hLV))).symm
  let e₂ : ↥L ⧸ α.ker ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    QuotientGroup.quotientKerEquivOfSurjective α hαs
  exact CFSG.QuasithinUnique.Vol2Native.A312L.Seven.isPSL_three_two
    ((e₁.trans e₂).trans (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm)

end Hyp331

theorem card_statedSL_three_two :
    Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_zmod_two

theorem stmt3_3_28G2_of (h25 : Stmt3_3_25) (hTC : Stmt3_3_28G2TC) : Stmt3_3_28G2 := by
  intro G _ _ T M L D h hG2
  have hTC' := hTC G T M L D h hG2
  refine ⟨hTC', ?_⟩
  rcases (h25 G T M L D h).2.2 hTC' with hV | hA6
  · exact hV.symm
  · exfalso
    obtain ⟨-, α, hαs, hαk, -⟩ := hA6
    have h1 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 := F420.card_of_u33 hG2.2.1
    have h2 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 := by
      rw [← hαk, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv,
        nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    omega

theorem stmt3_3_28U33_of (h14 : Stmt3_3_14) (h25 : Stmt3_3_25) (hG2 : Stmt3_3_28G2) :
    Stmt3_3_28U33 := by
  intro G _ _ T M L D h hU
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  have hcard : Nat.card ↥(autOn L (vPlus L T)) = 6048 := F420.card_of_u33 hU
  have hdvd := h.card_autOn_dvd hTL
  rw [hcard] at hdvd
  rcases (h25 G T M L D h).1 with hA6 | hb | hLn
  · exfalso
    obtain ⟨-, α, hαs, hαk, -⟩ := hA6
    rw [← hαk, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv,
      nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at hdvd
    exact absurd hdvd (by decide)
  · exact hG2 G T M L D h hb
  · exfalso
    obtain ⟨-, α, hαs, hαk, -⟩ := hLn
    rw [← hαk, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv,
      card_statedSL_three_two] at hdvd
    exact absurd hdvd (by decide)

theorem stmt3_3_30_of
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14)
    (h25 : Stmt3_3_25) (h28 : Stmt3_3_28G2) (h29 : Stmt3_3_29) (hI : Insp3_3_30) :
    Stmt3_3_30 := by
  intro G _ _ T M L D h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  rcases (h25 G T M L D h).1 with hA6 | hG2 | hLn
  · exact hA6
  · exfalso
    obtain ⟨hTC, hQV⟩ := h28 G T M L D h hG2
    obtain ⟨ha, hb, hc⟩ := hI G T M L h.toSetup331 hG2 hTL hTC hQV
    have hred := Hyp331.vPlus_reduced h.toSetup331
    have hCQ : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
      (h.centralizer_vPlus h38 h39).2.1
    rw [hQV] at hCQ
    have hVe := hred.2.1
    have hVab : ∀ a ∈ vPlus L T, ∀ b ∈ vPlus L T, a * b = b * a := fun a ha b hb => by
      have := hVe.1
      exact setLike_mul_comm ha hb
    have hVT : vPlus L T ≤ T :=
      (hred.1.trans inf_le_left).trans (pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf)
    have hHV : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := hred.2.2.2.1
    have hTV : T ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_right.trans hHV
    have hVmax : IsMaxElemAbelian T (vPlus L T) := ⟨hVT, hVe, ha⟩
    have hperm : ∀ g ∈ D, ∀ B, IsMaxElemAbelian T B → T ≤ Subgroup.normalizer (B : Set G) →
        IsMaxElemAbelian T (B.map (MulAut.conj g).toMonoidHom) ∧
          T ≤ Subgroup.normalizer ((B.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
      intro g hg B hB hTB
      have hgT : g ∈ Subgroup.normalizer (T : Set G) := h.DN hg
      have hTg : T.map (MulAut.conj g).toMonoidHom = T := A38.map_conj_eq_iff.mpr hgT
      refine ⟨?_, le_normalizer_map_conj hgT hTB⟩
      have := (isMaxElemAbelian_map_mulEquiv (MulAut.conj g)).mpr hB
      rwa [hTg] at this
    have hVne : vPlus L T ≠ ⊥ := by
      intro hb'
      apply h.not_L_le_centralizer h38 h39
      rw [hb']
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
      rw [hy, one_mul, mul_one]
    have hDV : ¬ D ≤ Subgroup.normalizer (vPlus L T : Set G) :=
      h.not_le_normalizer h38 h39 hVne (hVT.trans le_sup_right) hHV
    obtain ⟨d, hdD, hdV⟩ := IsConcreteLE.not_le_iff_exists.mp hDV
    have hnot : ∀ g : G, g ∉ Subgroup.normalizer (vPlus L T : Set G) →
        ¬ (vPlus L T).map (MulAut.conj g).toMonoidHom ≤ vPlus L T := by
      intro g hg hle
      apply hg
      refine A38.map_conj_eq_iff.mp (Subgroup.eq_of_le_of_card_ge hle ?_)
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    obtain ⟨hV₁, hTV₁⟩ := hperm d hdD _ hVmax hTV
    obtain ⟨hV₂, hTV₂⟩ := hperm d hdD _ hV₁ hTV₁
    have hodd : Odd (orderOf d) := by
      have h1 : orderOf (⟨d, hdD⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat h.Dodd h1
    have hd2 : d ^ 2 ∈ Subgroup.normalizer (vPlus L T : Set G) := by
      by_contra hd2
      have h2 : ¬ ((vPlus L T).map (MulAut.conj d).toMonoidHom).map (MulAut.conj d).toMonoidHom ≤
          vPlus L T := by
        rw [map_conj_map_conj, ← pow_two]
        exact hnot _ hd2
      have hsup := hc _ _ hV₁ hV₂ hTV₁ hTV₂ (hnot d hdV) h2
      obtain ⟨b, hbV₁, hbC⟩ := hb _ hV₁ hTV₁ (hnot d hdV)
      have hauto : autI hVe ((vPlus L T).map (MulAut.conj d).toMonoidHom) =
          autI hVe (((vPlus L T).map (MulAut.conj d).toMonoidHom).map
            (MulAut.conj d).toMonoidHom) := by
        rw [autI_eq_autOn, autI_eq_autOn, ← autOn_sup_eq_of_comm hVab (hV₁.1.trans hTV), hsup,
          autOn_sup_eq_of_comm hVab (hV₂.1.trans hTV)]
      have heq := B2_21 hVe hVT hTV hCQ hV₁ hbV₁ hbC hV₂ hauto
      apply hdV
      refine A38.map_conj_eq_iff.mp ?_
      have h1 := congrArg (fun X : Subgroup G => X.map (MulAut.conj d⁻¹).toMonoidHom) heq
      simp only [map_conj_map_conj, inv_mul_cancel, map_conj_one, inv_mul_cancel_left] at h1
      exact h1
    exact hdV ((Subgroup.zpowers_le.mpr hd2) (mem_zpowers_sq_of_odd hodd))
  · exact absurd (h.isPSL_of_isLnBlock h38 h39 hTL hLn) (h29 G T M L D h)

end CFSG.Quasithin.H13
