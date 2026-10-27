module

public import CFSG.LocalAnalysis.SteinbergCCRegularDisjointCosetCount

public section

namespace CFSG.LocalAnalysis

namespace TransitiveSpread

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem le_or_le_of_subset_union {U R W : Submodule (ZMod 2) V}
    (h : ∀ w ∈ W, w ∈ U ∨ w ∈ R) : W ≤ U ∨ W ≤ R := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hxW, hxU⟩ := IsConcreteLE.not_le_iff_exists.mp hcon.1
  obtain ⟨y, hyW, hyR⟩ := IsConcreteLE.not_le_iff_exists.mp hcon.2
  have hxR : x ∈ R := (h x hxW).resolve_left hxU
  have hyU : y ∈ U := (h y hyW).resolve_right hyR
  rcases h (x + y) (W.add_mem hxW hyW) with hU | hR
  · exact hxU (by simpa using U.sub_mem hU hyU)
  · exact hyR (by simpa using R.sub_mem hR hxR)

end TransitiveSpread

open TransitiveSpread in
theorem binary_transitive_disjoint_subspace_spread_alternative {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (U R : Submodule (ZMod 2) V)
    (hUR : IsCompl U R) (hn : 3 ≤ Module.finrank (ZMod 2) U)
    (hm : 1 ≤ Module.finrank (ZMod 2) R) (Δ : Set (Submodule (ZMod 2) V)) (hRΔ : R ∈ Δ)
    (hdimΔ : ∀ Q ∈ Δ, Module.finrank (ZMod 2) Q = Module.finrank (ZMod 2) R)
    (hdisj : ∀ Q ∈ Δ, ∀ Z ∈ Δ, Q ≠ Z → Q ⊓ Z = ⊥) (h3 : 3 ≤ Δ.ncard)
    (M : Subgroup (V ≃ₗ[ZMod 2] V))
    (hMΔ : ∀ g ∈ M, ∀ Q ∈ Δ, Q.map (g : V →ₗ[ZMod 2] V) ∈ Δ)
    (hMtr : ∀ Q ∈ Δ, ∀ Z ∈ Δ, ∃ g ∈ M, Q.map (g : V →ₗ[ZMod 2] V) = Z)
    (H : Subgroup (V ≃ₗ[ZMod 2] V)) (hHM : H ≤ M)
    (hHU : ∀ h ∈ H, U.map (h : V →ₗ[ZMod 2] V) = U) (hHR : ∀ h ∈ H, ∀ r ∈ R, h r = r)
    (hreg : ∀ u ∈ U, ∀ v ∈ U, u ≠ 0 → v ≠ 0 → ∃! h, h ∈ H ∧ h u = v) :
    let A := {Q ∈ Δ | Q ⊓ U = ⊥}
    let B := {Q ∈ Δ | Q ≤ U}
    (A.ncard = 2 ^ Module.finrank (ZMod 2) U ∧
      (∀ h ∈ H, ∀ Q ∈ A \ {R}, Q.map (h : V →ₗ[ZMod 2] V) ∈ A \ {R}) ∧
      (∀ Q ∈ A \ {R}, ∀ Z ∈ A \ {R}, ∃! h, h ∈ H ∧ Q.map (h : V →ₗ[ZMod 2] V) = Z) ∧
      (∀ Q ∈ A, (∃ v ∈ Q, v ≠ 0) ∧ ∀ v ∈ Q, v ≠ 0 → v ∉ U) ∧
      (∀ v : V, v ∉ U → ∃! Q, Q ∈ A ∧ v ∈ Q)) ∧
    ((B = ∅ ∧ Δ = A) ∨
      (B.Nonempty ∧
        (∀ Q ∈ B, ∀ Z ∈ B, ∃ h ∈ H, Q.map (h : V →ₗ[ZMod 2] V) = Z) ∧
        B.ncard = (2 ^ Module.finrank (ZMod 2) U - 1) / (2 ^ Module.finrank (ZMod 2) R - 1) ∧
        Odd B.ncard ∧ 0 < B.ncard ∧
        (∀ v : V, v ≠ 0 → ∃! Q, Q ∈ Δ ∧ v ∈ Q) ∧
        Δ.ncard = 2 ^ Module.finrank (ZMod 2) U + B.ncard ∧ Odd Δ.ncard)) := by
  intro A B
  have hVfin : Finite V := Module.finite_of_finite (ZMod 2)
  have hSfin : Finite (Submodule (ZMod 2) V) :=
    Finite.of_injective (fun Q : Submodule (ZMod 2) V => (Q : Set V)) SetLike.coe_injective
  obtain ⟨-, ⟨hΔAB, hAB⟩, -, hAalt, hBpart⟩ :=
    binary_regular_disjoint_subspace_coset_count U R hUR hn hm Δ hRΔ hdimΔ hdisj H
      (fun h hh Q hQ => hMΔ h (hHM hh) Q hQ) hHU hHR hreg
  change Δ = A ∪ B at hΔAB
  change Disjoint A B at hAB
  change A = {R} ∨ _ at hAalt
  change B.Nonempty → _ at hBpart
  have hmem : ∀ Q ∈ Δ, Q ∈ A ∨ Q ∈ B := fun Q hQ => by
    rw [hΔAB] at hQ
    exact hQ
  have hAq : A ≠ {R} := by
    intro hA
    by_cases hB : B.Nonempty
    · obtain ⟨-, -, -, hBpartU, hBcard, -, -, -⟩ := hBpart hB
      have hRU : ∀ Q ∈ Δ, Q = R ∨ Q ≤ U := fun Q hQ => by
        rcases hmem Q hQ with hQA | hQB
        · left
          rw [hA] at hQA
          exact hQA
        · right
          exact hQB.2
      by_cases hnm : Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) R
      · have hpos : 0 < 2 ^ Module.finrank (ZMod 2) R - 1 := by
          have : 2 ≤ 2 ^ Module.finrank (ZMod 2) R :=
            le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hm)
          omega
        have hB1 : B.ncard = 1 := by
          rw [hnm] at hBcard
          exact Nat.eq_of_mul_eq_mul_right hpos (hBcard.trans (one_mul _).symm)
        have hΔ2 : Δ.ncard = 2 := by
          rw [hΔAB, Set.ncard_union_eq hAB, hA, Set.ncard_singleton, hB1]
        omega
      · obtain ⟨Z, hZΔ, hZR⟩ : ∃ Z ∈ Δ, Z ≠ R := by
          by_contra hcon
          push Not at hcon
          have hsub : Δ ⊆ {R} := fun Q hQ => hcon Q hQ
          have := Set.ncard_le_ncard hsub (Set.toFinite _)
          rw [Set.ncard_singleton] at this
          omega
        obtain ⟨g, hgM, hgR⟩ := hMtr R hRΔ Z hZΔ
        have hgU : U.map (g : V →ₗ[ZMod 2] V) ≤ U ∨ U.map (g : V →ₗ[ZMod 2] V) ≤ R := by
          apply le_or_le_of_subset_union
          rintro _ ⟨u, hu, rfl⟩
          by_cases hu0 : u = 0
          · left
            simp [hu0]
          · obtain ⟨Q, ⟨hQB, huQ⟩, -⟩ := hBpartU u hu hu0
            rcases hRU _ (hMΔ g hgM Q hQB.1) with h | h
            · right
              rw [← h]
              exact ⟨u, huQ, rfl⟩
            · left
              exact h ⟨u, huQ, rfl⟩
        have hgRU : R.map (g : V →ₗ[ZMod 2] V) ≤ U := by
          rw [hgR]
          exact (hRU Z hZΔ).resolve_left hZR
        rcases hgU with h | h
        · have hUeq : U.map (g : V →ₗ[ZMod 2] V) = U :=
            Submodule.eq_of_le_of_finrank_eq h (LinearEquiv.finrank_map_eq g U)
          have hRU' : R ≤ U := by
            rw [← Submodule.map_le_map_iff_of_injective (g : V ≃ₗ[ZMod 2] V).injective, hUeq]
            exact hgRU
          have hR0 : R = ⊥ := by
            rw [eq_bot_iff, ← hUR.inf_eq_bot]
            exact le_inf hRU' le_rfl
          rw [hR0, finrank_bot] at hm
          omega
        · have h1 : Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) R := by
            rw [← LinearEquiv.finrank_map_eq g U]
            exact Submodule.finrank_mono h
          have h2 : Module.finrank (ZMod 2) R ≤ Module.finrank (ZMod 2) U := by
            rw [← LinearEquiv.finrank_map_eq g R]
            exact Submodule.finrank_mono hgRU
          exact hnm (le_antisymm h1 h2)
    · have hBe : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
      have hΔ1 : Δ.ncard = 1 := by
        rw [hΔAB, hBe, Set.union_empty, hA, Set.ncard_singleton]
      omega
  obtain ⟨hAcard, hAH, hAreg, hAnz, hApart⟩ := hAalt.resolve_left hAq
  refine ⟨⟨hAcard, hAH, hAreg, hAnz, hApart⟩, ?_⟩
  by_cases hB : B.Nonempty
  · right
    obtain ⟨-, hBtr, -, hBpartU, -, hBeq, hBodd, hBpos⟩ := hBpart hB
    refine ⟨hB, hBtr, hBeq, hBodd, hBpos, fun v hv => ?_, ?_, ?_⟩
    · by_cases hvU : v ∈ U
      · obtain ⟨Q, ⟨hQB, hvQ⟩, hQu⟩ := hBpartU v hvU hv
        refine ⟨Q, ⟨hQB.1, hvQ⟩, fun Z hZ => ?_⟩
        rcases hmem Z hZ.1 with hZA | hZB
        · exact absurd hvU ((hAnz Z hZA).2 v hZ.2 hv)
        · exact hQu Z ⟨hZB, hZ.2⟩
      · obtain ⟨Q, ⟨hQA, hvQ⟩, hQu⟩ := hApart v hvU
        refine ⟨Q, ⟨hQA.1, hvQ⟩, fun Z hZ => ?_⟩
        rcases hmem Z hZ.1 with hZA | hZB
        · exact hQu Z ⟨hZA, hZ.2⟩
        · exact absurd (hZB.2 hZ.2) hvU
    · rw [hΔAB, Set.ncard_union_eq hAB, hAcard]
    · rw [hΔAB, Set.ncard_union_eq hAB, hAcard]
      have heven : Even (2 ^ Module.finrank (ZMod 2) U) :=
        Nat.even_pow.mpr ⟨even_two, by omega⟩
      exact heven.add_odd hBodd
  · left
    have hBe : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
    refine ⟨hBe, ?_⟩
    rw [hΔAB, hBe, Set.union_empty]

end CFSG.LocalAnalysis
