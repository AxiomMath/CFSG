module

public import CFSG.Quasithin.EmptyFaithful.S153XLoc
import CFSG.Quasithin.EmptyFaithful.S153WJ
public import CFSG.Quasithin.EmptyFaithful.S153WRes

public section

namespace CFSG.Quasithin.X1469

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.ModF
open scoped commutatorElement

namespace ExE

open CFSG.QuasithinUnique.AppCS2W CFSG.QuasithinUnique.AppCS2 CFSG.QuasithinUnique.AppC

theorem esub_le_blockU {G : Type} [Group G] {K Iz : Subgroup G}
    (hKN : K ≤ Subgroup.normalizer (blockU K : Set G)) : Esub K Iz ≤ blockU K := by
  refine Subgroup.commutator_le.2 fun u hu k hk => ?_
  have h1 : k * u⁻¹ * k⁻¹ ∈ blockU K :=
    (Subgroup.mem_normalizer_iff.1 (hKN hk.1) u⁻¹).1 (inv_mem hu)
  have e : ⁅u, k⁆ = u * (k * u⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact mul_mem hu h1

theorem card_cent_V₁ {G : Type} [Group G] [Finite G] {H S L : Subgroup G} {t x : G}
    (X : WTwo H S L t x) :
    Nat.card ↥(blockU L ⊓ Subgroup.centralizer (conjR (blockU L) x : Set G)) = 4 := by
  rw [X.C.P.card_fix (X.C.V_le_N X.hx), X.hVE, card_fix_Estd]

theorem mem_cent_of_conj_mem {G : Type} [Group G] [Finite G] {H S L : Subgroup G} {t x : G}
    (X : WTwo H S L t x) {e : G} (he : e ∈ blockU L) (hQ : x * e * x⁻¹ ∈ pCoreOf 2 H) :
    e ∈ blockU L ⊓ Subgroup.centralizer (conjR (blockU L) x : Set G) := by
  have h1 : e ∈ conjR (pCoreOf 2 H) x := mem_conjSubgroup_iff.2 hQ
  rw [X.conjR_pCoreOf] at h1
  refine ⟨he, Subgroup.mem_centralizer_iff.2 fun v hv => ?_⟩
  have hv' : v ∈ conjR (U0 L t) x := by
    rw [conjR_U0_eq L t x]
    exact Subgroup.mem_sup_left hv
  exact Subgroup.mem_centralizer_iff.1 h1.2 v hv'

theorem exists_not_conj_mem {G : Type} [Group G] [Finite G] {H S L : Subgroup G} {t x : G}
    (X : WTwo H S L t x) {E : Subgroup G} (hEU : E ≤ blockU L) (hE : 4 < Nat.card E) :
    ∃ e ∈ E, x * e * x⁻¹ ∉ pCoreOf 2 H := by
  by_contra hcon
  have hle : E ≤ blockU L ⊓ Subgroup.centralizer (conjR (blockU L) x : Set G) := fun e he =>
    mem_cent_of_conj_mem X (hEU he) (not_not.1 fun h => hcon ⟨e, he, h⟩)
  have h4 := Subgroup.card_le_of_le hle
  rw [card_cent_V₁ X] at h4
  omega

theorem exists_good_conj {G : Type} [Group G] [Finite G] {I S Iz K₁ K₂ T : Subgroup G} {r z : G}
    (C : LocalCfg I S Iz K₁ K₂ T r z) {E : Subgroup G} (hEU : E ≤ blockU K₁) (hE : 4 < Nat.card E) :
    ∃ x ∈ T, x ∉ S ∧ ∃ e ∈ E, x * e * x⁻¹ ∉ pCoreOf 2 I := by
  have c := C.cfg
  have hJ := c.commutator_thompsonJ_eq C.hTN C.hb C.ht
  obtain ⟨t', ⟨D⟩⟩ := c.exists_wdbl C.ht hJ
  have hC52 : C5.NoCommonNormal S I T := fun X hXS hXne hIX hTX =>
    C.hb X hXS hXne (sup_le hTX hIX)
  obtain ⟨x, hxT, hxS, hgood⟩ := D.exists_good hC52 C.hST C.hrel
  obtain ⟨W⟩ := D.nonempty_cfg
  obtain ⟨W'⟩ := D.swap.nonempty_cfg
  let X : WTwo I S K₁ t' x := ⟨W, W', C.hTN hxT, hgood, T, C.hST, hC52, C.hrel, hxT, hxS⟩
  exact ⟨x, hxT, hxS, exists_not_conj_mem X hEU hE⟩

theorem exists_conj_eq_of_mem_diff {G : Type} [Group G] {S T E : Subgroup G} {r y e : G}
    (h2 : S.relIndex T = 2) (hrT : r ∈ T) (hrS : r ∉ S) (hyT : y ∈ T) (hyS : y ∉ S)
    (hSE : S ≤ Subgroup.normalizer (E : Set G)) (he : e ∈ E) :
    ∃ e' ∈ E, r * e' * r⁻¹ = y * e * y⁻¹ := by
  have hs : r⁻¹ * y ∈ S := CFSG.QuasithinUnique.inv_mul_mem_of_relIndex_two h2 hrT hrS hyT hyS
  exact ⟨(r⁻¹ * y) * e * (r⁻¹ * y)⁻¹, (Subgroup.mem_normalizer_iff.1 (hSE hs) e).1 he, by group⟩

end ExE

theorem exists_e_of {G : Type} [Group G] [Finite G] {I S Iz K₁ K₂ T : Subgroup G} {r z t : G}
    (C : LocalCfg I S Iz K₁ K₂ T r z) (PG : PairGen I S Iz K₁ K₂ t z)
    (hE : 4 < Nat.card ↥(Esub K₁ Iz)) :
    ∃ e ∈ E0 K₁ K₂ Iz, r * e * r⁻¹ ∉ pCoreOf 2 I := by
  obtain ⟨x, hxT, hxS, e, he, hne⟩ := ExE.exists_good_conj C (ExE.esub_le_blockU PG.K₁_N_U) hE
  obtain ⟨e', he', heq⟩ := ExE.exists_conj_eq_of_mem_diff C.hrel C.hrT C.hrS hxT hxS
    (PG.S_le_Iz.trans PG.Iz_normalizes_E) (Subgroup.mem_sup_left he)
  refine ⟨e', he', ?_⟩
  rw [heq]
  exact hne

end CFSG.Quasithin.X1469
