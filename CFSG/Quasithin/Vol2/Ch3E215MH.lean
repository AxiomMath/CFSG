module

public import CFSG.Quasithin.Vol2.Ch3E213MTr
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.Ch3E215M

open CFSG.Open

theorem card_map_eq_relIndex_ker {A L : Type*} [Group A] [Group L] (f : A →* L)
    (K : Subgroup A) : f.ker.relIndex K = Nat.card (K.map f) := by
  rw [Subgroup.relIndex, ← MonoidHom.ker_domRestrict, Subgroup.index_ker,
    MonoidHom.domRestrict_range]

theorem isElemAbelian_map {A L : Type*} [Group A] [Group L] (f : A →* L) {p : ℕ}
    {K : Subgroup A} (hK : IsElemAbelian p K) : IsElemAbelian p (K.map f) :=
  CFSG.SectionRank.isElemAbelian_map hK _

theorem isElemAbelian_comap {A L : Type*} [Group A] [Group L] (f : A →* L)
    (hf : Function.Injective f) {p : ℕ} {K : Subgroup L} (hK : IsElemAbelian p K) :
    IsElemAbelian p (K.comap f) := CFSG.Open.IsElemAbelian.comap hK hf

theorem card_le_of_isElemAbelian_suzuki {L : Type*} [Group L]
    [Finite L] {b : ℕ} {k : Type} [Field k] (hk : Nat.card k = 2 ^ (2 * b + 1))
    (e : L ≃* CFSG.Blueprint.suzukiGroup b k) {W : Subgroup L} (hW : IsElemAbelian 2 W) :
    Nat.card W ≤ 2 ^ (2 * b + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (B6.isPGroup_of_isElemAbelian hW)
  have hle : j ≤ twoRank L := by
    refine le_csSup ⟨Nat.card L, ?_⟩ ⟨W, le_top, hW, hj⟩
    rintro r ⟨E, -, -, hE⟩
    calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card E := hE.symm
      _ ≤ Nat.card L := Subgroup.card_le_card_group E
  rw [CFSG.ShultStronglyClosedTI.SuzukiModel.twoRank_eq_of_mulEquiv hk e] at hle
  rw [hj]
  exact Nat.pow_le_pow_right two_pos hle

theorem relIndex_eq_card_map {G : Type} [Group G] {H V : Subgroup G} (hVH : V ≤ H)
    {I : Subgroup H} (hVI : V.subgroupOf H ≤ I) {L : Type*} [Group L] (ψ : ↥I →* L)
    (hψk : ψ.ker = (inSubgroup (CFSG.pCore 2) I).subgroupOf I) :
    (pCoreOf 2 (I.map H.subtype) ⊓ V).relIndex V =
      Nat.card (((V.subgroupOf H).subgroupOf I).map ψ) := by
  have hV : (V.subgroupOf H).map H.subtype = V := Subgroup.map_subgroupOf_eq_of_le hVH
  conv_lhs => rw [← hV]
  rw [← Ch3E213M.map_subtype_inSubgroup_pCore, ← Subgroup.map_inf _ _ _ H.subtype_injective,
    Subgroup.relIndex_map_map_of_injective _ _ H.subtype_injective, Subgroup.inf_relIndex_right,
    ← Subgroup.relIndex_subgroupOf hVI, ← hψk, card_map_eq_relIndex_ker]

end CFSG.Quasithin.Ch3E215M
