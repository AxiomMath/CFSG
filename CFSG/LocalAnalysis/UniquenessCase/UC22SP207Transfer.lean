module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22P20l

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.ASVolI.ChIJK

private theorem uc22sp207_conj_comp {G X : Type} [Group G] [Group X] (q : G →* X) (n : G) :
    (MulAut.conj (q n)).toMonoidHom.comp q = q.comp (MulAut.conj n).toMonoidHom := by
  ext x
  simp [MulAut.conj_apply]

theorem HasCentralLongest.map {G X : Type} [Group G] [Group X] (h : HasCentralLongest G)
    (q : G →* X) (hq : Function.Surjective q) (hker : q.ker ≤ center G) :
    HasCentralLongest X := by
  obtain ⟨B, N, hBN, n₀, hn₀, hsup, hcen⟩ := h
  refine ⟨B.map q, N.map q, burnsideI2BN_map hBN q hq hker, q n₀, mem_map_of_mem q hn₀, ?_, ?_⟩
  · rw [map_map, uc22sp207_conj_comp, ← map_map, ← Subgroup.map_sup, hsup,
      map_top_of_surjective q hq]
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨n₀ * x * n₀⁻¹ * x⁻¹, hcen x hx, by simp⟩

theorem HasCentralLongest.of_mulEquiv {G X : Type} [Group G] [Group X] (e : G ≃* X)
    (h : HasCentralLongest G) : HasCentralLongest X :=
  h.map e.toMonoidHom e.surjective (by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
    exact bot_le)

theorem HasCentralLongest.comap {G X : Type} [Group G] [Group X] [Finite G]
    (h : HasCentralLongest X) (q : G →* X) (hq : Function.Surjective q)
    (hker : q.ker ≤ center G) (hodd : ¬ 2 ∣ Nat.card q.ker) : HasCentralLongest G := by
  obtain ⟨B, N, hBN, n₀, hn₀, hsup, hcen⟩ := h
  obtain ⟨n, rfl⟩ := hq n₀
  refine ⟨B.comap q, N.comap q, burnsideI2BN_comap Nat.prime_two hBN q hq hker hodd, n, hn₀, ?_,
    fun x hx => by simpa [mem_comap] using hcen (q x) hx⟩
  have hK : q.ker ≤ B.comap q ⊔ (B.comap q).map (MulAut.conj n).toMonoidHom :=
    (ker_le_comap q B).trans le_sup_left
  rw [← comap_map_eq_self hK, Subgroup.map_sup, map_comap_eq_self_of_surjective hq, map_map,
    ← uc22sp207_conj_comp, ← map_map, map_comap_eq_self_of_surjective hq, hsup, comap_top]

theorem HasCentralLongest.prod {A C : Type} [Group A] [Group C] (hA : HasCentralLongest A)
    (hC : HasCentralLongest C) : HasCentralLongest (A × C) := by
  obtain ⟨B₁, N₁, h₁, n₁, hn₁, hsup₁, hcen₁⟩ := hA
  obtain ⟨B₂, N₂, h₂, n₂, hn₂, hsup₂, hcen₂⟩ := hC
  refine ⟨B₁.prod B₂, N₁.prod N₂, uc22p20l_prod_splitBN h₁ h₂, (n₁, n₂), mem_prod.2 ⟨hn₁, hn₂⟩,
    ?_, fun x hx => mem_prod.2 ⟨hcen₁ x.1 (mem_prod.1 hx).1, hcen₂ x.2 (mem_prod.1 hx).2⟩⟩
  have hconj : (B₁.prod B₂).map (MulAut.conj (n₁, n₂)).toMonoidHom =
      (B₁.map (MulAut.conj n₁).toMonoidHom).prod (B₂.map (MulAut.conj n₂).toMonoidHom) := by
    ext ⟨a, c⟩
    simp only [mem_map_equiv, mem_prod, MulAut.conj_symm_apply, Prod.inv_mk, Prod.mk_mul_mk]
  rw [hconj, uc22p20l_prod_sup_prod, hsup₁, hsup₂, top_prod_top]

theorem HasCentralLongest.quotient_center {G : Type} [Group G] (h : HasCentralLongest G) :
    HasCentralLongest (G ⧸ center G) :=
  h.map (QuotientGroup.mk' (center G)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk'])

theorem HasCentralLongest.statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {H : Subgroup (GL ι K)} (h : HasCentralLongest ↥H) :
    HasCentralLongest (CFSG.Open.StatedProj H) := by
  refine h.map (QuotientGroup.mk' ((CFSG.Open.StatedScalars ι K).subgroupOf H))
    (QuotientGroup.mk'_surjective _) ?_
  rw [QuotientGroup.ker_mk']
  intro x hx
  have hx' : (x : GL ι K) ∈ CFSG.Open.StatedScalars ι K := hx
  rw [CFSG.Open.StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx'
  rw [mem_center_iff]
  intro y
  exact Subtype.ext (mem_center_iff.1 hx' (y : GL ι K))

end CFSG.LocalAnalysis.UniquenessCase.UC22
