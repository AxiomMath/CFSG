module

public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG
open scoped commutatorElement

private theorem isExtraspecial_quotient_aux {R : Type*} [Group R] [Finite R] {N B : Subgroup R}
    (hR2 : IsPGroup 2 R) (hcomm : commutator R = B) (hBc : B ≤ Subgroup.center R)
    (hsq : ∀ a : R, a ^ 2 ∈ B) (hNB : N ≤ B) (hN2 : Nat.card N * 2 = Nat.card B)
    (hker : ∀ x : R, (∀ p : R, ⁅x, p⁆ ∈ N) → x ∈ B) :
    ∃ _ : N.Normal, IsExtraspecialPGroup 2 (R ⧸ N) := by
  have hNn : N.Normal := Subgroup.normal_of_le_center (hNB.trans hBc)
  haveI := hNn
  refine ⟨hNn, ?_⟩
  set π : R →* R ⧸ N := QuotientGroup.mk' N with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hrange : π.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
  have hZ : Subgroup.center (R ⧸ N) = B.map π := by
    ext x
    obtain ⟨y, rfl⟩ := hsurj x
    constructor
    · intro hx
      rw [Subgroup.mem_center_iff] at hx
      refine Subgroup.mem_map.mpr ⟨y, hker y (fun p => ?_), rfl⟩
      have h1 : ⁅π y, π p⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (hx (π p)).symm
      rw [← map_commutatorElement] at h1
      have h2 : ⁅y, p⁆ ∈ π.ker := h1
      rwa [hπ, QuotientGroup.ker_mk'] at h2
    · rintro ⟨b, hb, hby⟩
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := hsurj g
      rw [← hby, ← map_mul, ← map_mul]
      exact congrArg π (Subgroup.mem_center_iff.mp (hBc hb) g)
  have hC : commutator (R ⧸ N) = B.map π := by
    have h := map_commutator_eq R π
    rw [hrange] at h
    rw [commutator_def, ← h, hcomm]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 (R ⧸ N)) := ⟨hR2.to_quotient N⟩
  have hF : frattini (R ⧸ N) = B.map π := by
    rw [frattini_eq_closure_commutator_union_powers (p := 2), hC]
    apply Subgroup.closure_eq_of_le
    · refine Set.union_subset subset_rfl ?_
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := hsurj x
      show π y ^ 2 ∈ B.map π
      rw [← map_pow]
      exact Subgroup.mem_map_of_mem π (hsq y)
    · exact fun z hz => Subgroup.subset_closure (Or.inl hz)
  have hcard : Nat.card (B.map π) = 2 := by
    let f : B →* R ⧸ N := π.comp B.subtype
    have hrangef : f.range = B.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hkerf : f.ker = N.subgroupOf B := by
      rw [← MonoidHom.comap_ker, hπ, QuotientGroup.ker_mk']
      rfl
    have h := Subgroup.card_ker_mul_card_range f
    rw [hrangef, hkerf, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNB).toEquiv] at h
    have hpos : 0 < Nat.card N := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h.trans hN2.symm)
  refine ⟨hR2.to_quotient N, hC.trans hZ.symm, hF.trans hZ.symm, ?_⟩
  rw [hZ]
  exact hcard

variable {G : Type} [Group G] [Finite G]

theorem isExtraspecial_quotient_of_hyperplane {P B Hh : Subgroup G} (hP2 : IsPGroup 2 P)
    (hBP : B ≤ P) (hcomm : ⁅P, P⁆ = B) (hBc : ∀ b ∈ B, ∀ x ∈ P, b * x = x * b)
    (hsq : ∀ a ∈ P, a ^ 2 ∈ B) (hHB : Hh ≤ B) (hH2 : Nat.card Hh * 2 = Nat.card B)
    (hker : ∀ x ∈ P, (∀ p ∈ P, ⁅x, p⁆ ∈ Hh) → x ∈ B) :
    ∃ _ : (Hh.subgroupOf P).Normal, IsExtraspecialPGroup 2 (↥P ⧸ Hh.subgroupOf P) := by
  have hHP : Hh ≤ P := hHB.trans hBP
  refine isExtraspecial_quotient_aux (B := B.subgroupOf P) hP2 ?_ ?_ ?_ ?_ ?_ ?_
  · apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subtype_commutator, hcomm, Subgroup.map_subgroupOf_eq_of_le hBP]
  · intro b hb
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hBc _ hb g g.2).symm
  · intro a
    exact hsq a a.2
  · exact fun x hx => hHB hx
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHP).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv]
    exact hH2
  · intro x hx
    exact hker x x.2 (fun p hp => hx ⟨p, hp⟩)

end CFSG.RankThree.GF2n.Tim78
