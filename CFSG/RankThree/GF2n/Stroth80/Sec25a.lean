module

import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.RankThree.GF2n.Stroth80.Conj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem inf_centralizer_Z_eq_Q (hc : Ctx M Q Z B) :
    Q ⊓ Subgroup.centralizer (Z : Set G) = Q := by
  refine inf_eq_left.mpr ?_
  intro y hy
  exact Subgroup.mem_centralizer_iff.mpr fun z hz => hc.hyp.toHyp79.V_central hz hy

theorem Ctx.card_QB_eq (hc : Ctx M Q Z B) :
    Nat.card (QB B) = Nat.card ↥(QB B ⊓ Subgroup.centralizer (Z : Set G)) * Nat.card Z := by
  obtain ⟨g, hg⟩ := hc.conj
  have hgV : conjSubgroup g Z ≠ Z := by
    rw [← hg]
    exact hc.ne
  have hgQ : conjSubgroup g Z ≤ Q := by
    rw [← hg]
    exact hc.le
  rw [(Ctx.QB_eq hc hg).2]
  have h := hc.hyp.toHyp79.toHyp218 hgV hgQ
  obtain ⟨y, hy⟩ := h.exists_isOpp
  obtain ⟨x₁, hxW, hxV⟩ := h.exists_conj_eq_V1 hy
  have hPQ := inf_centralizer_Z_eq_Q hc
  have hH : Q ⊔ conjSubgroup g Q = (Q ⊓ Subgroup.centralizer (Z : Set G)) ⊔
      conjSubgroup g (Q ⊓ Subgroup.centralizer (Z : Set G)) := by
    rw [hPQ]
  obtain ⟨n, hn2, hZn, φ, -, -, hφker, -, -, hφPg, -, -⟩ :=
    h.exists_natural hxW hxV hy hc.hyp.q4 hH
  rw [hPQ] at hφPg
  have hn0 : n ≠ 0 := by omega
  have hsub : conjSubgroup g Q ≤ Q ⊔ conjSubgroup g Q := le_sup_right
  obtain ⟨f, hf⟩ : ∃ f : ↥(conjSubgroup g Q) →* Matrix.SpecialLinearGroup (Fin 2)
      (GaloisField 2 n), ∀ u : ↥(conjSubgroup g Q), f u = φ (Subgroup.inclusion hsub u) :=
    ⟨φ.comp (Subgroup.inclusion hsub), fun u => rfl⟩
  have hrange : f.range = CFSG.Timmesfeld.lowerUnipotent (GaloisField 2 n) := by
    rw [← hφPg]
    ext y
    constructor
    · intro hy'
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hy'
      exact Subgroup.mem_map.mpr
        ⟨Subgroup.inclusion hsub u, Subgroup.mem_subgroupOf.mpr u.2, (hf u).symm⟩
    · intro hy'
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy'
      exact MonoidHom.mem_range.mpr ⟨⟨v, Subgroup.mem_subgroupOf.mp hv⟩, (hf _).trans rfl⟩
  have hkermem : ∀ u : ↥(conjSubgroup g Q), u ∈ f.ker ↔
      (u : G) ∈ Subgroup.centralizer ((Z ⊔ conjSubgroup g Z : Subgroup G) : Set G) := by
    intro u
    rw [MonoidHom.mem_ker, hf, ← MonoidHom.mem_ker, hφker]
    exact Subgroup.mem_subgroupOf
  have hkerW : conjSubgroup g Q ⊓ Subgroup.centralizer ((Z ⊔ conjSubgroup g Z : Subgroup G) : Set G)
      = conjSubgroup g Q ⊓ Subgroup.centralizer (Z : Set G) := by
    refine le_antisymm ?_ ?_
    · rintro u ⟨huQ, huW⟩
      exact ⟨huQ, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) huW⟩
    · rintro u ⟨huQ, huZ⟩
      refine ⟨huQ, ?_⟩
      have hT : Z ⊔ conjSubgroup g Z ≤ Subgroup.centralizer ({u} : Set G) := by
        refine sup_le (fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr ?_) ?_
        · exact Subgroup.mem_centralizer_iff.mp huZ z hz
        · intro b hb
          exact Subgroup.mem_centralizer_singleton_iff.mpr
            (hc.hyp.toHyp79.conj_central g hb huQ)
      exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
        Subgroup.mem_centralizer_singleton_iff.mp (hT hw)
  have hkerCard : Nat.card ↥f.ker =
      Nat.card ↥(conjSubgroup g Q ⊓ Subgroup.centralizer (Z : Set G)) := by
    have hmap : f.ker.map (conjSubgroup g Q).subtype = conjSubgroup g Q ⊓
        Subgroup.centralizer ((Z ⊔ conjSubgroup g Z : Subgroup G) : Set G) := by
      ext y
      constructor
      · intro hy'
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy'
        exact ⟨u.2, (hkermem u).mp hu⟩
      · intro hy'
        exact Subgroup.mem_map.mpr ⟨⟨y, hy'.1⟩, (hkermem ⟨y, hy'.1⟩).mpr hy'.2, rfl⟩
    rw [← hkerW, ← hmap, Subgroup.card_map_of_injective (conjSubgroup g Q).subtype_injective]
  have hKcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  have hLcard : Nat.card (CFSG.Timmesfeld.lowerUnipotent (GaloisField 2 n)) = Nat.card ↥Z := by
    rw [CFSG.Timmesfeld.RankOne.card_lowerUnipotent, hKcard, hZn]
  have hcard1 : Nat.card ↥(conjSubgroup g Q) = Nat.card ↥f.ker * Nat.card ↥f.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [hcard1, hkerCard, hrange, hLcard]

end CFSG.RankThree.GF2n.Stroth80
