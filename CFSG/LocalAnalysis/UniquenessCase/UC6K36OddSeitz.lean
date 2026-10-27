module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36OddAct
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieCross

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

namespace Odd

theorem characteristic_eq_two_of_isD2SeitzException {p : ℕ} {d : TauCeti.LieTypeIndex}
    (h : AGLEmbeddingD2.IsD2SeitzException p d) : d.characteristic = 2 := by
  unfold AGLEmbeddingD2.IsD2SeitzException at h
  rcases h with ⟨-, h | h | h | h | h⟩ | ⟨-, h | h⟩
  · obtain ⟨q, hq, -, rfl⟩ := h
    simpa using hq
  · obtain ⟨q, hq, -, rfl⟩ := h
    simpa using hq
  · obtain ⟨q, hq, -, rfl⟩ := h
    simpa using hq
  · obtain ⟨q, hq, -, h | h⟩ := h <;> subst h <;> simpa using hq
  · subst h
    simp
  · subst h
    simp
  · subst h
    simp

end Odd

namespace Hyp36

open Odd

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ}

theorem le_of_seitz (hS : AGLEmbeddingD2.KFactSeitzRankTwo) (h : Hyp36 G M p E) {L : Subgroup G} [L.Normal]
    (hL : Group.IsPerfect ↥L) (d : TauCeti.ValidLieTypeIndex)
    (φ : ↥L ⧸ Subgroup.center ↥L ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hp : p ≠ d.1.characteristic) (hex : ¬ AGLEmbeddingD2.IsD2SeitzException p d.1) : L ≤ M := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hLc : commutator ↥L = ⊤ := hL.commutator_eq_top
  by_cases hfaith : ∀ e ∈ E, e ≠ 1 → ∃ y ∈ L, e * y * e⁻¹ * y⁻¹ ∉ centerOf L
  swap
  ·
    push_neg at hfaith
    obtain ⟨e, he, he1, hall⟩ := hfaith
    have hcent := centralizes_of_forall_comm_mem L hLc hall
    intro y hy
    exact h.centralizer_le_of_ne_one he he1
      (Subgroup.mem_centralizer_singleton_iff.2 (hcent y hy).symm)
  let Ψ : G →* MulAut (TauCeti.CFSGIndex.lie d).Group := (MulAut.congr φ).toMonoidHom.comp (actHom L)
  have hΨ : ∀ (g : G) (y : G) (hy : y ∈ L),
      Ψ g (φ (QuotientGroup.mk ⟨y, hy⟩)) = φ (QuotientGroup.mk ⟨y, hy⟩) ↔
        g * y * g⁻¹ * y⁻¹ ∈ centerOf L := by
    intro g y hy
    have h1 : Ψ g (φ (QuotientGroup.mk ⟨y, hy⟩)) = φ (actHom L g (QuotientGroup.mk ⟨y, hy⟩)) := by
      change (MulAut.congr φ) (actHom L g) (φ _) = _
      simp [MulAut.congr_apply]
    rw [h1, φ.injective.eq_iff, actHom_mk_eq_iff]
  have hΨ1 : ∀ e ∈ E, Ψ e = 1 → e = 1 := by
    intro e he hΨe
    by_contra he1
    obtain ⟨y, hy, hy'⟩ := hfaith e he he1
    apply hy'
    rw [← hΨ e y hy, hΨe]
    rfl
  have hinj : Function.Injective (Ψ.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro e he
    exact Subtype.ext (hΨ1 e e.2 he)
  have hcard : Nat.card (E.map Ψ) = p ^ 2 := by
    have hr : (Ψ.comp E.subtype).range = E.map Ψ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr, ← h.card]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hgen := hS d p h.prime h.odd hp hex (E.map Ψ) (CFSG.Open.IsElemAbelian.map h.elem Ψ) hcard
  let H₀ : Subgroup (TauCeti.CFSGIndex.lie d).Group :=
    ((M.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))).map φ.toMonoidHom
  have hfix : {k : (TauCeti.CFSGIndex.lie d).Group | ∃ ε ∈ E.map Ψ, ε ≠ 1 ∧ ε k = k} ⊆ H₀ := by
    rintro k ⟨ε, hε, hε1, hεk⟩
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hε
    have he1 : e ≠ 1 := fun h1 => hε1 (by rw [h1, map_one])
    obtain ⟨c, rfl⟩ := φ.surjective k
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨m, hm, z, hz, hyz⟩ :=
      h.mem_mul_centerOf_of_fixed L he he1 hy ((hΨ e y hy).1 hεk)
    refine ⟨QuotientGroup.mk ⟨m, hm.2⟩, ⟨⟨m, hm.2⟩, hm.1, rfl⟩, ?_⟩
    change φ (QuotientGroup.mk ⟨m, hm.2⟩) = φ (QuotientGroup.mk ⟨y, hy⟩)
    rw [φ.injective.eq_iff, QuotientGroup.eq, mem_center_iff_mem_centerOf]
    have : (((⟨m, hm.2⟩ : ↥L)⁻¹ * ⟨y, hy⟩ : ↥L) : G) = m⁻¹ * y := rfl
    rw [this, hyz, inv_mul_cancel_left]
    exact hz
  have htop : H₀ = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact (Subgroup.closure_le H₀).2 hfix
  refine le_of_mul_centerOf L hLc fun y hy => ?_
  have hy0 : φ (QuotientGroup.mk ⟨y, hy⟩) ∈ H₀ := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨c', ⟨m', hm', rfl⟩, hφ⟩ := Subgroup.mem_map.1 hy0
  have hc' : QuotientGroup.mk' (Subgroup.center ↥L) m' = QuotientGroup.mk ⟨y, hy⟩ := φ.injective hφ
  have hz : (m'⁻¹ * ⟨y, hy⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [← QuotientGroup.eq]
    exact hc'
  refine ⟨m', ⟨hm', m'.2⟩, ((m'⁻¹ * ⟨y, hy⟩ : ↥L) : G), (mem_center_iff_mem_centerOf L _).1 hz, ?_⟩
  change y = (m' : G) * ((m'⁻¹ : ↥L) * ⟨y, hy⟩ : ↥L)
  simp

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK
