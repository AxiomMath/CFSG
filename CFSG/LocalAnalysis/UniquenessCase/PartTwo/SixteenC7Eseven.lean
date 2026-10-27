module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c7_card_mul_card_preBarSub {V₀ V E : Subgroup G} (hV : IsElemAbelian 2 V)
    (hE : E ≤ stabTil V₀ V) {Q : Subgroup (MulAut (Vtil V₀ V hV))}
    (hQ : Q ≤ barSub V₀ V hV E) :
    Nat.card E * Nat.card Q =
      Nat.card (preBarSub E V₀ V hV Q) * Nat.card (barSub V₀ V hV E) := by
  classical
  let f : ↥E →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion hE)
  have hrange : f.range = barSub V₀ V hV E := by
    ext φ
    rw [MonoidHom.mem_range, mem_barSub]
    constructor
    · rintro ⟨e, rfl⟩
      exact ⟨⟨(e : G), hE e.2⟩, e.2, rfl⟩
    · rintro ⟨g, hg, hφ⟩
      refine ⟨⟨(g : G), hg⟩, ?_⟩
      show actTil V₀ V hV ⟨(g : G), hE hg⟩ = φ
      rw [show (⟨(g : G), hE hg⟩ : ↥(stabTil V₀ V)) = g from Subtype.ext rfl, hφ]
  have hpre : preBarSub E V₀ V hV Q = (Q.comap f).map E.subtype := by
    ext g
    rw [mem_preBarSub, Subgroup.mem_map]
    constructor
    · rintro ⟨hgE, h, hq⟩
      refine ⟨⟨g, hgE⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      show actTil V₀ V hV ⟨g, hE hgE⟩ ∈ Q
      rwa [show (⟨g, hE hgE⟩ : ↥(stabTil V₀ V)) = ⟨g, h⟩ from Subtype.ext rfl]
    · rintro ⟨e, he, rfl⟩
      refine ⟨e.2, hE e.2, ?_⟩
      rw [Subgroup.mem_comap] at he
      exact he
  have hQ' : Q ≤ f.range := by rw [hrange]; exact hQ
  have hker : Q.relIndex f.range * Nat.card Q = Nat.card f.range := by
    have h := Subgroup.relIndex_mul_card (H := Q) (K := f.range)
    rwa [inf_eq_left.2 hQ'] at h
  have hcardE : Nat.card E = Nat.card (Q.comap f) * (Q.comap f).index :=
    (Subgroup.card_mul_index (H := Q.comap f)).symm
  calc Nat.card E * Nat.card Q
      = Nat.card (Q.comap f) * (Q.comap f).index * Nat.card Q := by rw [hcardE]
    _ = Nat.card (Q.comap f) * ((Q.comap f).index * Nat.card Q) := by
          rw [Nat.mul_assoc]
    _ = Nat.card (Q.comap f) * (Q.relIndex f.range * Nat.card Q) := by
          rw [Subgroup.index_comap]
    _ = Nat.card (Q.comap f) * Nat.card f.range := by rw [hker]
    _ = Nat.card (preBarSub E V₀ V hV Q) * Nat.card (barSub V₀ V hV E) := by
          rw [hpre, hrange, Subgroup.card_map_of_injective E.subtype_injective]

theorem s16c7_not_isCyclic_of_elemAbelian {p : ℕ} (hp : p.Prime) {C : Subgroup G}
    (hC : IsElemAbelian p C) (hcard : p ^ 2 ≤ Nat.card C) : ¬ IsCyclic ↥C := by
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hC.2 g g.2)
  have hle : orderOf g ≤ p := Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hgp)
  have h2 := hp.two_le
  rw [hord] at hle
  nlinarith

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
