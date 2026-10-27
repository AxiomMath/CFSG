module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Generic
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven (fixedBy)

namespace OneComp

variable {K : Type} [Group K] [Finite K] {J M X P : Subgroup K}

private theorem k330c_isSylowOf_subgroupOf_top {G : Type*} [Group G] {p : ℕ} {A B : Subgroup G}
    (h : IsSylowOf p A B) : IsSylowOf p (A.subgroupOf B) ⊤ := by
  obtain ⟨Q, hQ⟩ := h.exists_sylow_eq_subgroupOf
  exact ⟨Q.subtype le_top,
    by rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_top_eq, hQ]⟩

private theorem k330c_subgroupOf_map_conj {G : Type*} [Group G] {J Z Z' : Subgroup G}
    (hZ : Z ≤ J) (hZ' : Z' ≤ J) (n : J) :
    (Z.subgroupOf J).map (MulAut.conj n).toMonoidHom = Z'.subgroupOf J ↔
      Z.map (MulAut.conj (n : G)).toMonoidHom = Z' := by
  have hcomp : J.subtype.comp (MulAut.conj n).toMonoidHom =
      (MulAut.conj (n : G)).toMonoidHom.comp J.subtype := by
    ext x
    rfl
  have key : ((Z.subgroupOf J).map (MulAut.conj n).toMonoidHom).map J.subtype =
      Z.map (MulAut.conj (n : G)).toMonoidHom := by
    rw [Subgroup.map_map (g := J.subtype) (f := (MulAut.conj n).toMonoidHom), hcomp,
      ← Subgroup.map_map (g := (MulAut.conj (n : G)).toMonoidHom) (f := J.subtype),
      Subgroup.map_subgroupOf_eq_of_le hZ]
  constructor
  · intro h
    have h' := congrArg (Subgroup.map J.subtype) h
    rwa [key, Subgroup.map_subgroupOf_eq_of_le hZ'] at h'
  · intro h
    apply Subgroup.map_injective J.subtype_injective
    rw [key, Subgroup.map_subgroupOf_eq_of_le hZ', h]

theorem sylow_subgroupOf (h : OneComp J M X P) :
    IsSylowOf 3 (X.subgroupOf J) ⊤ ∧ IsElemAbelian 3 (X.subgroupOf J) ∧
      Nat.card (X.subgroupOf J) = 9 := by
  refine ⟨k330c_isSylowOf_subgroupOf_top h.sylow,
    CFSG.Open.IsElemAbelian.subgroupOf h.elemAbelian J, ?_⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.sylow.le).toEquiv, h.card_eq]

theorem mem_of_mem_normalizer_subgroupOf (h : OneComp J M X P) :
    ∀ n ∈ normalizer ((X.subgroupOf J : Subgroup ↥J) : Set ↥J), (n : K) ∈ M := by
  intro n hn
  apply h.normalizer_le
  have hmem : n ∈ (normalizer (X : Set K)).subgroupOf J := by
    rw [Subgroup.subgroupOf_normalizer_eq h.sylow.le]
    exact hn
  exact hmem

theorem pair_subgroupOf (h : OneComp J M X P) :
    ∃ Z₁ Z₂ : Subgroup ↥J, Z₁ ≤ X.subgroupOf J ∧ Z₂ ≤ X.subgroupOf J ∧ Nat.card Z₁ = 3 ∧
      Nat.card Z₂ = 3 ∧ Z₁ ≠ Z₂ ∧
      ∀ n ∈ normalizer ((X.subgroupOf J : Subgroup ↥J) : Set ↥J),
        (Z₁.map (MulAut.conj n).toMonoidHom = Z₁ ∧ Z₂.map (MulAut.conj n).toMonoidHom = Z₂) ∨
        (Z₁.map (MulAut.conj n).toMonoidHom = Z₂ ∧ Z₂.map (MulAut.conj n).toMonoidHom = Z₁) := by
  obtain ⟨Z₁, Z₂, hZ₁X, hZ₂X, hcard₁, hcard₂, hne, hperm⟩ := h.pair
  have hZ₁J : Z₁ ≤ J := hZ₁X.trans h.sylow.le
  have hZ₂J : Z₂ ≤ J := hZ₂X.trans h.sylow.le
  refine ⟨Z₁.subgroupOf J, Z₂.subgroupOf J, Subgroup.subgroupOf_mono J hZ₁X,
    Subgroup.subgroupOf_mono J hZ₂X, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ₁J).toEquiv, hcard₁]
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ₂J).toEquiv, hcard₂]
  · intro heq
    apply hne
    have h' := congrArg (Subgroup.map J.subtype) heq
    rwa [Subgroup.map_subgroupOf_eq_of_le hZ₁J,
      Subgroup.map_subgroupOf_eq_of_le hZ₂J] at h'
  · intro n hn
    have hnX : (n : K) ∈ normalizer (X : Set K) := by
      have hmem : n ∈ (normalizer (X : Set K)).subgroupOf J := by
        rw [Subgroup.subgroupOf_normalizer_eq h.sylow.le]
        exact hn
      exact hmem
    rcases hperm (n : K) hnX with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨(k330c_subgroupOf_map_conj hZ₁J hZ₁J n).mpr h1,
        (k330c_subgroupOf_map_conj hZ₂J hZ₂J n).mpr h2⟩
    · right
      exact ⟨(k330c_subgroupOf_map_conj hZ₁J hZ₂J n).mpr h1,
        (k330c_subgroupOf_map_conj hZ₂J hZ₁J n).mpr h2⟩

theorem exists_cyclic_sylow_seven (h : OneComp J M X P) (h7 : 7 ∣ Nat.card J) :
    ∃ R : Subgroup ↥J, IsSylowOf 7 R ⊤ ∧ R ≠ ⊥ ∧ IsCyclic ↥R ∧
      R ≤ centralizer ((X.subgroupOf J : Subgroup ↥J) : Set ↥J) := by
  have hJne : Nat.card J ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨⟨1, J.one_mem⟩⟩, inferInstance⟩
  have hPJ : IsSylowOf 7 (P ⊓ J) J :=
    h.isSylowOf_seven_top.inf_of_le_normalizer le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr h.normal])
  refine ⟨P.subgroupOf J, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.inf_subgroupOf_right P J]
    exact k330c_isSylowOf_subgroupOf_top hPJ
  · refine (Subgroup.one_lt_card_iff_ne_bot (P.subgroupOf J)).mp ?_
    rw [← Subgroup.inf_subgroupOf_right P J,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hPJ.card_eq]
    have hpos : 0 < (Nat.card J).factorization 7 :=
      Nat.Prime.factorization_pos_of_dvd (by norm_num) hJne h7
    calc 1 < 7 ^ 1 := by norm_num
      _ ≤ 7 ^ (Nat.card J).factorization 7 := Nat.pow_le_pow_right (by norm_num) hpos
  · haveI : IsCyclic ↥P := h.isCyclic
    have hf0 : Function.Injective (J.subtype.comp (P.subgroupOf J).subtype) :=
      J.subtype_injective.comp (P.subgroupOf J).subtype_injective
    exact isCyclic_of_injective
      ((J.subtype.comp (P.subgroupOf J).subtype).codRestrict P (fun x => x.2))
      ((MonoidHom.injective_codRestrict _ _ _).mpr hf0)
  · intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (h.le_centralizer hr) _ hx)

end OneComp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
