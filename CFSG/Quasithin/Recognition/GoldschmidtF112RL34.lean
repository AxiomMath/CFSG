module

public import CFSG.Quasithin.Recognition.GoldschmidtF112RU42
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieModel
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34ParabE
public import CFSG.GH74.QTGen4.DSGen4.Leaf.Lin2OfNatural
public import CFSG.Quasithin.Background.C1GNBlockLemmas

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.QuasithinUnique CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement

section Transport

variable {G H : Type} [Group G] [Group H] {A : Subgroup G} {B : Subgroup H}

theorem natSec_of_mulEquiv (e : ↥A ≃* ↥B) (h : NatSec B ⊥ (pCoreOf 2 B)) :
    NatSec A ⊥ (pCoreOf 2 A) := by
  intro x hx ho v hv hvx
  rw [Subgroup.mem_bot] at hvx ⊢
  have hvA : v ∈ A := CFSG.LieType.BorelTits.pCoreOf_le 2 A hv
  have h1 := h ((e ⟨x, hx⟩ : ↥B) : H) (e ⟨x, hx⟩).2 (by
      have ho' : orderOf (e ⟨x, hx⟩) = 3 := by
        rw [show orderOf (e ⟨x, hx⟩) = orderOf (⟨x, hx⟩ : ↥A) from
          orderOf_injective e.toMonoidHom e.injective _, ← orderOf_submonoid]
        exact ho
      rw [orderOf_submonoid]
      exact ho')
    ((e ⟨v, hvA⟩ : ↥B) : H) ((mem_pCoreOf_iff_of_mulEquiv e 2 ⟨v, hvA⟩).mp hv) (by
      rw [Subgroup.mem_bot]
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      have hc : (⟨v, hvA⟩ : ↥A) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨v, hvA⟩ :=
        Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp hvx)
      have h2 := congrArg (fun a => ((e a : ↥B) : H)) hc
      simpa only [map_mul, Subgroup.coe_mul] using h2)
  rw [Subgroup.mem_bot] at h1
  have h3 : e ⟨v, hvA⟩ = 1 := Subtype.ext h1
  have := e.injective (h3.trans (map_one e).symm)
  exact congrArg Subtype.val this

end Transport

@[expose] def L34Par {H : Type} [Group H] (N : Subgroup H) : Prop :=
  Nat.card N = 960 ∧ Nat.card (pCoreOf 2 N) = 16 ∧ IsElemAbelian 2 (pCoreOf 2 N) ∧
    NatSec N ⊥ (pCoreOf 2 N)

section Model

open CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

variable {F : Type} [Field F] [Finite F] [CharP F 2]

open CFSG.QuasithinUnique.Fin257.L3 in
theorem l34Par_normalizer_V1 (hq : Nat.card F = 4) :
    L34Par (Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))) := by
  refine ⟨L34.card_normalizer_V1 hq, ?_, ?_, L34.natSec_normalizer_V1 hq⟩
  · rw [L34.pCoreOf_normalizer_V1, L34.card_V1, hq]
    norm_num
  · rw [L34.pCoreOf_normalizer_V1]
    exact isElemAbelian_V1

open CFSG.QuasithinUnique.Fin257.L3 in
theorem l34Par_normalizer_V2 (hq : Nat.card F = 4) :
    L34Par (Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))) := by
  refine ⟨L34.card_normalizer_V2 hq, ?_, ?_, L34.natSec_normalizer_V2 hq⟩
  · rw [L34.pCoreOf_normalizer_V2, L34.card_V2, hq]
    norm_num
  · rw [L34.pCoreOf_normalizer_V2]
    exact isElemAbelian_V2

end Model


variable {G : Type} [Group G] [Finite G]

theorem parabolic_le_normalizer_left {L1 L2 S : Subgroup G} (h : Hyp111 L1 L2 S) :
    L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) := by
  refine sup_le Subgroup.le_normalizer (sup_le (sup_le ?_ h.h1.borel_le) h.h1.normalizes)
  exact (inf_le_left : borelOf L1 S ≤ L1).trans Subgroup.le_normalizer

theorem l34_vertex {H : Type} [Group H] {N : Subgroup H} {L P : Subgroup G} (hL : VA5 L)
    (hLP : L ≤ P) (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hct : CharTwo P) (ψ : ↥P ≃* ↥N)
    (hN : L34Par N) :
    L = P ∧ IsBlock2 L L ∧ IsLin2Type L 2 ∧ ⁅L, L⁆ = L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hN960, hN16, hNE, hNnat⟩ := hN
  have hP960 : Nat.card P = 960 := (Nat.card_congr ψ.toEquiv).trans hN960
  have hP16 : Nat.card (pCoreOf 2 P) = 16 := (card_pCoreOf_of_mulEquiv ψ 2).trans hN16
  have hPnat : NatSec P ⊥ (pCoreOf 2 P) := natSec_of_mulEquiv ψ hNnat
  have hc := card_eq_of_VA5 hL
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3
    (by rw [hc]; exact Dvd.dvd.mul_right (by norm_num) _)
  set x : G := (y : G) with hx
  have hxL : x ∈ L := y.2
  have hxo : orderOf x = 3 := by rw [hx, Subgroup.orderOf_coe, hy]
  set Q := pCoreOf 2 P with hQ
  have hQP : Q ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hmem : ∀ e ∈ Q, ⁅e, x⁆ ∈ L ⊓ Q := by
    intro e he
    have heP := hQP he
    refine ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPL heP) x).mp hxL) (L.inv_mem hxL)
    · rw [commutatorElement_def, show e * x * e⁻¹ * x⁻¹ = e * (x * e⁻¹ * x⁻¹) by group]
      exact Q.mul_mem he ((Subgroup.mem_normalizer_iff.mp (hPQ (hLP hxL)) _).mp
        (Q.inv_mem he))
  let f : ↥Q → ↥(L ⊓ Q) := fun e => ⟨⁅(e : G), x⁆, hmem e e.2⟩
  have hf : Function.Injective f := by
    rintro ⟨e, he⟩ ⟨e', he'⟩ h
    have h1 : ⁅e, x⁆ = ⁅e', x⁆ := congrArg Subtype.val h
    rw [commutatorElement_def, commutatorElement_def] at h1
    have h2 : ⁅e'⁻¹ * e, x⁆ = 1 := by
      rw [commutatorElement_def]
      calc e'⁻¹ * e * x * (e'⁻¹ * e)⁻¹ * x⁻¹
          = e'⁻¹ * (e * x * e⁻¹ * x⁻¹) * x * e' * x⁻¹ := by group
        _ = e'⁻¹ * (e' * x * e'⁻¹ * x⁻¹) * x * e' * x⁻¹ := by rw [h1]
        _ = 1 := by group
    have h3 := hPnat x (hLP hxL) hxo (e'⁻¹ * e) (Q.mul_mem (Q.inv_mem he') he)
      (by rw [h2]; exact Subgroup.one_mem _)
    rw [Subgroup.mem_bot, inv_mul_eq_one] at h3
    exact Subtype.ext h3.symm
  have hcardQ : Nat.card Q ≤ Nat.card ↥(L ⊓ Q) := Nat.card_le_card_of_injective f hf
  have hQL : Q ≤ L := by
    have := Subgroup.eq_of_le_of_card_ge (inf_le_right : L ⊓ Q ≤ Q) hcardQ
    rw [← this]
    exact inf_le_left
  have hO2L : pCoreOf 2 L = Q := by
    rw [pCoreOf_eq_inf_pCoreOf hLP hPL, ← hQ]
    exact inf_eq_right.mpr hQL
  have hLeq : L = P :=
    Subgroup.eq_of_le_of_card_ge hLP (by rw [hP960, hc, hO2L, hQ, hP16])
  subst hLeq
  have hE : IsElemAbelian 2 (pCoreOf 2 L) := isElemAbelian_pCoreOf_of_mulEquiv ψ hNE
  haveI : DSLeaf LeafFaithfulA5 := ⟨leafFaithfulA5⟩
  haveI : DSLeaf LeafShort2OfA5 := ⟨leafShort2OfA5⟩
  have hshort := leafShort2OfA5 hL hct hE hP16
  refine ⟨rfl, Gold14610.isBlock2_of_short hshort le_rfl Subgroup.le_normalizer,
    leafLin2OfNatural hL hct hE hP16 hPnat, ?_⟩
  apply C1GN.isShort2_perfect_of_perfect_quotient hshort
  have h60 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 60 := by
    have e : OTwoQuot L ≃* (↥L ⧸ CFSG.pCore 2 ↥L) :=
      QuotientGroup.quotientMulEquivOfEq (A3.pCore_eq_openCore 2 ↥L).symm
    rw [← Nat.card_congr e.toEquiv]
    have : Nat.card (oTwoQuot ↥L) = 60 := by
      rw [IsL2Quot.card (by norm_num) hL]
      norm_num
    exact this
  rcases hshort.2.2.2.1 with hqs | h3
  · exact hqs.1.commutator_eq_top
  · rw [h60] at h3
    norm_num at h3

open CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour in
theorem y9L34 : Y9L34 := by
  intro G _ _ L1 L2 S hF h1 h2 hA
  obtain ⟨Y, _, hY, T, N₁, N₂, hp, ⟨iso0⟩⟩ := hA
  obtain ⟨-, F, _, _, _, hF4, ⟨e1⟩⟩ := CFSG.Quasithin.H13.F431.L3.exists_equiv_projSL3 hY
  have hq : Nat.card F = 4 := by rw [hF4]; norm_num
  have hy1 := hp.map e1
  obtain ⟨h, -, hh⟩ := IsSylowTwoOf.exists_conj hy1.1
    (CFSG.QuasithinUnique.Fin257.L3.isSylowTwoOf_U (F := F))
  let E : Y ≃* projectiveSL 3 F := e1.trans (MulAut.conj h)
  have hy2 : IsYAmalgamPair (projUnitriangular 3 F) (N₁.map E.toMonoidHom)
      (N₂.map E.toMonoidHom) := by
    have := hp.map E
    have hTD : T.map E.toMonoidHom = projUnitriangular 3 F := by
      rw [hh, Subgroup.map_map]
      rfl
    rwa [hTD] at this
  have hpar : L34Par (N₁.map E.toMonoidHom) ∧ L34Par (N₂.map E.toMonoidHom) := by
    rcases Borel252.BorelData.yam_cases Borel252.L3.borelData_L3
      CFSG.Quasithin.H13.F431.L3.no_normal_two_subgroup hy2 with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩
    · rw [e₁, e₂]
      exact ⟨l34Par_normalizer_V1 hq, l34Par_normalizer_V2 hq⟩
    · rw [e₁, e₂]
      exact ⟨l34Par_normalizer_V2 hq, l34Par_normalizer_V1 hq⟩
  have ψ1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(N₁.map E.toMonoidHom) :=
    iso0.φ1.trans (N₁.equivMapOfInjective E.toMonoidHom E.injective)
  have ψ2 : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(N₂.map E.toMonoidHom) :=
    iso0.φ2.trans (N₂.equivMapOfInjective E.toMonoidHom E.injective)
  have hH := hF.1
  have hct1 : CharTwo (L1 ⊔ bigB L1 L2 S) := by
    rw [F1.parabolic_eq]
    exact hH.h1.charTwo
  have hct2 : CharTwo (L2 ⊔ bigB L1 L2 S) := by
    rw [← bigB_comm L1 L2 S, F1.parabolic_eq]
    exact hH.h2.charTwo
  obtain ⟨hL1, hb1, hl1, hp1⟩ :=
    l34_vertex h1 le_sup_left (parabolic_le_normalizer_left hH) hct1 ψ1 hpar.1
  obtain ⟨hL2, hb2, hl2, hp2⟩ :=
    l34_vertex h2 le_sup_left (parabolic_le_normalizer_right hH) hct2 ψ2 hpar.2
  refine ⟨⟨hb1, hl1⟩, ⟨hb2, hl2⟩, perfectCore_eq_self_of_perfect hp1,
    perfectCore_eq_self_of_perfect hp2, ?_, ?_⟩
  · rw [hL1]
    exact le_sup_right.trans le_sup_right
  · rw [hL2]
    exact le_sup_right.trans le_sup_right

end CFSG.Quasithin.F112R
