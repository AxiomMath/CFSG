module

public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin.C1Pack

variable {G : Type} [Group G]

theorem isSubnormal_of_isNilpotent' {Γ : Type*} [Group Γ] [Finite Γ] [Group.IsNilpotent Γ]
    (H : Subgroup Γ) : H.IsSubnormal := by
  suffices h : ∀ n : ℕ, ∀ K : Subgroup Γ, K.index = n → K.IsSubnormal from h _ H rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K hn
    by_cases hK : K = ⊤
    · rw [hK]
      exact Subgroup.IsSubnormal.top
    · have hlt : K < ⊤ := lt_top_iff_ne_top.2 hK
      have hN : K < Subgroup.normalizer (K : Set Γ) :=
        Group.normalizerCondition_of_isNilpotent K hlt
      have hidx : (Subgroup.normalizer (K : Set Γ)).index < K.index :=
        Subgroup.index_strictAnti hN
      exact Subgroup.IsSubnormal.step K _ hN.le (ih _ (hn ▸ hidx) _ rfl) inferInstance

theorem isSubnormal_subgroupOf_subgroupOf_iff' {B L K : Subgroup G} (hLK : L ≤ K) :
    ((B.subgroupOf K).subgroupOf (L.subgroupOf K)).IsSubnormal ↔
      (B.subgroupOf L).IsSubnormal := by
  let e : L.subgroupOf K ≃* L := Subgroup.subgroupOfEquivOfLe hLK
  constructor
  · intro h
    have h' := h.comap e.symm.toMonoidHom
    convert h' using 1
    ext z
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    rfl
  · intro h
    have h' := h.comap e.toMonoidHom
    convert h' using 1
    ext z
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    rfl

theorem isSubnormal_subgroupOf_trans' {B L K : Subgroup G} (hBL : B ≤ L) (hLK : L ≤ K)
    (hB : (B.subgroupOf L).IsSubnormal) (hL : (L.subgroupOf K).IsSubnormal) :
    (B.subgroupOf K).IsSubnormal :=
  Subgroup.IsSubnormal.trans (fun _ hz => hBL hz)
    ((isSubnormal_subgroupOf_subgroupOf_iff' (B := B) hLK).mpr hB) hL

theorem isSubnormal_subgroupOf_of_pGroup_quotient [Finite G] {KU Q A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hQn : (Q.subgroupOf KU).Normal) (hQA : Q ≤ A) (hp : ∀ g ∈ KU, ∃ a : ℕ, g ^ p ^ a ∈ Q) :
    (A.subgroupOf KU).IsSubnormal := by
  have hP : IsPGroup p (↥KU ⧸ Q.subgroupOf KU) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨a, ha⟩ := hp g g.2
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 (by simpa using ha))
  have hnil : Group.IsNilpotent (↥KU ⧸ Q.subgroupOf KU) := hP.isNilpotent
  have hsub := isSubnormal_of_isNilpotent'
    ((A.subgroupOf KU).map (QuotientGroup.mk' (Q.subgroupOf KU)))
  have h1 := hsub.comap (QuotientGroup.mk' (Q.subgroupOf KU))
  have hker : (QuotientGroup.mk' (Q.subgroupOf KU)).ker ≤ A.subgroupOf KU := by
    rw [QuotientGroup.ker_mk']
    exact fun x hx => hQA hx
  rwa [Subgroup.comap_map_eq_self hker] at h1


end CFSG.Quasithin.C1Pack
