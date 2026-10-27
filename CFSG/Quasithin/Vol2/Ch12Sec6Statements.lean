module

public import CFSG.Quasithin.H13.LinearOrders
public import CFSG.Quasithin.Vol2.Ch12Sec8OneExist
public import CFSG.Quasithin.H13.L1332Inputs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

structure Hyp126 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) : Prop where
  hyp : Hyp1223 G T L V
  alt8 : ∃ φ : ↥L →* ↥(alternatingGroup (Fin 8)), Function.Surjective φ ∧
    φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf L
  module : ∃ _ : IsMulCommutative ↥V, AlternatingNatural (V := ↥V) (autOn L V) ⊤
    ((Subgroup.centralizer (L : Set G)).subgroupOf V) 8

@[expose] def Elim126 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp126 G T L V → False

theorem pCoreOf_le_centralizer_of_reduced {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hVT : V ≤ T)
    (hred : IsPrimeReduced 2 (V.subgroupOf (L ⊔ T))) :
    pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) := by
  have hVLT : V ≤ L ⊔ T := hVT.trans le_sup_right
  have hE : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    (sup_le Subgroup.le_normalizer hTL).trans
      (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hle : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((Subgroup.map_subtype_le _).trans le_sup_left) hE (LieType.BorelTits.pCoreOf_isPGroup 2 L)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hle hx
  have hy' : y ∈ CFSG.pCore 2 ↥(L ⊔ T) := by assumption
  have hyc := pCore_le_centralizer_of_isPrimeReduced hred hy'
  rw [Subgroup.mem_centralizer_iff] at hyc ⊢
  intro v hv
  exact congrArg Subtype.val (hyc ⟨v, hVLT hv⟩ hv)

theorem stmt12_6_34_of_elim126 (h1222 : Stmt12_2_2) (helim : Elim126) : Stmt12_6_34 := by
  rw [stmt12_6_34_iff]
  intro G _ _ T L V hH hφL
  obtain ⟨φ, hφ, hker⟩ := hφL
  rcases h1222 G T hH.simple hH.nonabelian hH.qtke hH.sylow with hA | h3
  · exact absurd hA hH.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hH.maximal hH.faithful hH.quasisimple
  obtain ⟨⟨hVT, -, hred, -⟩, -, -, hc, hmod⟩ := hall V hH.irrPlus
  have hO2 : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro x hx
    rw [hker, Subgroup.mem_subgroupOf]
    apply pCoreOf_le_centralizer_of_reduced hH.normalizes hVT hred
    exact ⟨x, hx, rfl⟩
  have hψ : Function.Surjective (QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hO2) :=
    QuotientGroup.lift_surjective_of_surjective _ φ hφ hO2
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :=
    isSimpleGroup_sl_four_zmod_two
  obtain ⟨hψker, eZ, -⟩ := SteinbergBM.five_quasisimple_centerless_image hH.quasisimple
    sl_four_zmod_two_nonabelian (QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hO2) hψ
  have hQZ : Nat.card ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) =
      20160 := (Nat.card_congr eZ.toEquiv).trans card_sl_four_zmod_two
  have hdvd : 20160 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) :=
    hQZ ▸ Subgroup.card_quotient_dvd_card _
  have hLC : Nat.card (↥L ⧸ φ.ker) = 20160 :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv).trans
      card_sl_four_zmod_two
  have hinj : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ →
      Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 20160 := fun hZ => by
    rw [hZ] at hψker
    exact (Nat.card_congr (Equiv.ofBijective _ ⟨(MonoidHom.ker_eq_bot_iff _).1 hψker, hψ⟩)).trans
      card_sl_four_zmod_two
  rcases hmod with ⟨n, hn, ⟨e⟩, hnat⟩ | ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩ |
      ⟨m, hm5, hm8, ⟨φ', hφ', hker'⟩, halt⟩ | ⟨-, φ', hφ', hker'⟩ | ⟨hU, -⟩ | ⟨-, -, ⟨eA⟩, -, -, -⟩
  · have hZ := center_eq_bot_of_mulEquiv_sl (by omega) e
    have hQ4 := hinj hZ
    have hn4 : n = 4 := by
      have h := (Nat.card_congr e.toEquiv).symm.trans hQ4
      rcases hn with rfl | rfl | rfl
      · rw [card_sl_three_zmod_two] at h
        omega
      · rfl
      · rw [card_sl_five_zmod_two] at h
        omega
    subst hn4
    rw [hZ] at hψker
    have hkerφ : φ.ker = CFSG.pCore 2 ↥L := by
      refine le_antisymm (fun x hx => ?_) hO2
      have h1 : QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hO2 (x : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
        rw [QuotientGroup.lift_mk]
        exact hx
      have h2 := (MonoidHom.ker_eq_bot_iff _).1 hψker (h1.trans (map_one _).symm)
      exact (QuotientGroup.eq_one_iff x).1 h2
    have hsub : (Subgroup.centralizer (V : Set G)).subgroupOf L = CFSG.pCore 2 ↥L :=
      hker.symm.trans hkerφ
    refine ⟨(card_and_sq_of_binaryNaturalSL hnat).1, ?_, ⟨e⟩, hc, hnat⟩
    calc L ⊓ Subgroup.centralizer (V : Set G) = Subgroup.centralizer (V : Set G) ⊓ L :=
          inf_comm _ _
      _ = ((Subgroup.centralizer (V : Set G)).subgroupOf L).map L.subtype :=
          (Subgroup.subgroupOf_map_subtype _ _).symm
      _ = pCoreOf 2 L := by
          rw [hsub]
          rfl
  · exfalso
    rw [Nat.card_congr e.toEquiv, card_sl_three_zmod_two] at hdvd
    omega
  · exfalso
    have h := (Nat.card_congr e.toEquiv).symm.trans (hinj (center_eq_bot_of_mulEquiv_sl
      (by norm_num) e))
    rw [card_sl_five_zmod_two] at h
    omega
  · have hcard : Nat.card (alternatingGroup (Fin m)) = 20160 := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ' hφ').toEquiv,
        hker', ← hker, hLC]
    have hm : m = 8 := eq_eight_of_card_alternating hm5 hm8 hcard
    subst hm
    exact (helim G T L V ⟨hH, ⟨φ', hφ', hker'⟩, ⟨hc, halt⟩⟩).elim
  · exfalso
    have hcard : Nat.card (alternatingGroup (Fin 7)) = 20160 := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ' hφ').toEquiv,
        hker', ← hker, hLC]
    rw [nat_card_alternatingGroup] at hcard
    norm_num [Nat.factorial] at hcard
  · exfalso
    rw [card_of_lieModel_psu_three_three hU] at hdvd
    omega
  · exfalso
    have h := (Nat.card_congr eA.toEquiv).symm.trans hQZ
    rw [nat_card_alternatingGroup] at h
    norm_num [Nat.factorial] at h

end CFSG.Quasithin.H13
