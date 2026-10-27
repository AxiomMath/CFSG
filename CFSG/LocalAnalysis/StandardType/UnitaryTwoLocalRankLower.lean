module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.SpTwoLocalRankLower
public import CFSG.LocalAnalysis.StandardType.UnitaryEvenTorus
public import CFSG.LocalAnalysis.StandardType.UnitaryCenterOrders
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.StandardType

namespace UnitaryRank

open CFSG.Assembly CFSG.Open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

theorem le_largeEvenTwoLocalRank_of_normalizes_of_inf_ker {G : Type} [Group G] [Finite G]
    {H : Type} [Group H] (χ : H →* G) {q r : ℕ} (hq : q.Prime) {E U : Subgroup H}
    (hE : IsElemAbelian q E) (hc : Nat.card E = q ^ r) (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hEU : E ≤ Subgroup.normalizer (U : Set H)) (hEker : E ⊓ χ.ker = ⊥) (hUker : U ⊓ χ.ker = ⊥) :
    r ≤ LargeEvenTwoLocalRank q G := by
  have hUne : U.map χ ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff U]
    intro hle
    exact hU (by rw [← inf_eq_left.mpr hle, hUker])
  have hinj : Function.Injective (χ.domRestrict E) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    have hxmem : (x : H) ∈ (E ⊓ χ.ker : Subgroup H) :=
      ⟨x.2, MonoidHom.mem_ker.mpr (by
        simpa only [MonoidHom.domRestrict_apply] using hx)⟩
    rwa [hEker, Subgroup.mem_bot] at hxmem
  have hcard : Nat.card (E.map χ) = q ^ r := by
    rw [← MonoidHom.domRestrict_range E χ, ← hc]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hTL : IsTwoLocal (Subgroup.normalizer ((U.map χ : Subgroup G) : Set G)) :=
    ⟨_, hUne, hU2.map _, rfl⟩
  have hle : E.map χ ≤ Subgroup.normalizer ((U.map χ : Subgroup G) : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hn := Subgroup.mem_normalizer_iff.mp (hEU he)
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨e * u * e⁻¹, (hn u).mp hu, by simp only [map_mul, map_inv]⟩
    · rintro ⟨u', hu', hyu⟩
      have hy : y = χ (e⁻¹ * u' * e) := by
        simp only [map_mul, map_inv, hyu]
        group
      refine ⟨_, ?_, hy.symm⟩
      exact (hn (e⁻¹ * u' * e)).mpr (by
        rw [show e * (e⁻¹ * u' * e) * e⁻¹ = u' by group]
        exact hu')
  refine TableB.le_twoLocalRank hq.one_lt hTL (TableB.le_pRank_of_le hq.one_lt hle
    (TableB.isElemAbelian_map hE χ) hcard)

section Projection

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}

@[expose] noncomputable def projSU (hF : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) :
    SU (unitaryInvolution F 2 f) n →* LargeEvenProj (LargeEvenSUGroup (Fin n) F (2 ^ f)) :=
  (QuotientGroup.mk' _).comp (equivStatedSU hF n).toMonoidHom

theorem projSU_surjective (hF : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) :
    Function.Surjective (projSU hF n) :=
  (QuotientGroup.mk'_surjective _).comp (equivStatedSU hF n).surjective

theorem ker_projSU_eq_center (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 4 ≤ n) :
    (projSU hF n).ker = Subgroup.center (SU (unitaryInvolution F 2 f) n) := by
  have hnq : (n, 2 ^ f) ≠ (3, 2) := by
    intro h
    have : n = 3 := congrArg Prod.fst h
    omega
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx' : ((equivStatedSU hF n x : LargeEvenSUGroup (Fin n) F (2 ^ f))) ∈
        (LargeEvenScalars (Fin n) F).subgroupOf (LargeEvenSUGroup (Fin n) F (2 ^ f)) := by
      have hmem : ((equivStatedSU hF n x : LargeEvenSUGroup (Fin n) F (2 ^ f))) ∈
          (QuotientGroup.mk' ((LargeEvenScalars (Fin n) F).subgroupOf
            (LargeEvenSUGroup (Fin n) F (2 ^ f)))).ker :=
        MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx)
      simpa only [QuotientGroup.ker_mk'] using hmem
    have hc : ((equivStatedSU hF n x : LargeEvenSUGroup (Fin n) F (2 ^ f)) : GL (Fin n) F) ∈
        Subgroup.center (GL (Fin n) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact Subgroup.mem_subgroupOf.mp hx'
    rw [Subgroup.mem_center_iff]
    intro g
    apply (equivStatedSU hF n).injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.mp hc _
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hxcenter : equivStatedSU hF n x ∈ Subgroup.center (StatedSU n (2 ^ f) F) := by
      rw [← map_center_mulEquiv (equivStatedSU hF n)]
      exact ⟨x, hx, rfl⟩
    rw [(isQuasisimple_statedSU_of_card hF (by omega) hnq).2] at hxcenter
    have hxq : (QuotientGroup.mk' ((LargeEvenScalars (Fin n) F).subgroupOf
        (LargeEvenSUGroup (Fin n) F (2 ^ f))))
        ((equivStatedSU hF n x : LargeEvenSUGroup (Fin n) F (2 ^ f))) = 1 := by
      have h : ((equivStatedSU hF n x : LargeEvenSUGroup (Fin n) F (2 ^ f))) ∈
          (QuotientGroup.mk' ((LargeEvenScalars (Fin n) F).subgroupOf
            (LargeEvenSUGroup (Fin n) F (2 ^ f)))).ker := by
        rw [QuotientGroup.ker_mk']
        exact hxcenter
      exact MonoidHom.mem_ker.mp h
    exact hxq

end Projection

section Bounds

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ} {G : Type} [Group G] [Finite G]

theorem ggUnitaryTorusRank_le_largeEvenTwoLocalRank
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn : 4 ≤ n) (hdvd : 3 ∣ 2 ^ f + 1)
    (ψ : SU (unitaryInvolution F 2 f) n →* G)
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n)) :
    ggUnitaryTorusRank 3 n ≤ LargeEvenTwoLocalRank 3 G := by
  have hnq : (n, 2 ^ f) ≠ (3, 2) := by
    intro h
    have : n = 3 := congrArg Prod.fst h
    omega
  have hkerproj : (projSU hF n).ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n) :=
    le_of_eq (ker_projSU_eq_center hF hn)
  have hkerproj' : ψ.ker ≤ (projSU hF n).ker := by
    rw [ker_projSU_eq_center hF hn]
    exact hker
  have hlift := ggTorusLift_unitary (K := F) (n := f) (d := n) (p := 3) hF hf (by omega) hnq
    Nat.prime_three hdvd
  obtain ⟨U, E, hU, hU2, hEU, hE, hc, hEk⟩ :=
    hlift (SU (unitaryInvolution F 2 f) n) (projSU hF n) (projSU_surjective hF n)
      hkerproj (isQuasisimple_SU hF (by omega) hnq).1.commutator_eq_top
  have hEψ : E ⊓ ψ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : z ∈ E ⊓ (projSU hF n).ker := ⟨hz.1, hkerproj' hz.2⟩
    rwa [hEk] at hz'
  have hUψ : U ⊓ ψ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact UnitaryCenter.eq_one_of_mem_center_of_mem_isPGroup_two hF hf (by omega) hU2
      (hker hz.2) hz.1
  exact le_largeEvenTwoLocalRank_of_normalizes_of_inf_ker ψ Nat.prime_three hE hc hU hU2
    hEU hEψ hUψ

theorem half_le_largeEvenTwoLocalRank_of_even (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (hfe : Even f) (hn : 4 ≤ n) (ψ : SU (unitaryInvolution F 2 f) n →* G)
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n)) :
    n / 2 ≤ LargeEvenTwoLocalRank 3 G := by
  obtain ⟨U, E, hU, hU2, hEU, hE, hc⟩ :=
    UnitaryEvenTorus.exists_elemAbelian_three_normalizing_longRoot hF hf hfe (by omega : 2 ≤ n)
  have hEψ : E ⊓ ψ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact UnitaryCenter.eq_one_of_mem_center_of_pow_three hF hf (by omega) hfe
      (hker hz.2) (hE.2 z hz.1)
  have hUψ : U ⊓ ψ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact UnitaryCenter.eq_one_of_mem_center_of_mem_isPGroup_two hF hf (by omega) hU2
      (hker hz.2) hz.1
  exact le_largeEvenTwoLocalRank_of_normalizes_of_inf_ker ψ Nat.prime_three hE hc hU hU2
    hEU hEψ hUψ

theorem n_le_of_largeEvenTwoLocalRank_eq_four
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn : 4 ≤ n)
    (ψ : SU (unitaryInvolution F 2 f) n →* G)
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n))
    (hm : LargeEvenTwoLocalRank 3 G = 4) : n ≤ 5 ∨ (Odd f ∧ n = 6) ∨ (Even f ∧ n ≤ 9) := by
  rcases Nat.even_or_odd f with hfe | hfo
  · right; right
    have h := half_le_largeEvenTwoLocalRank_of_even hF hf hfe hn ψ hker
    rw [hm] at h
    exact ⟨hfe, by omega⟩
  · have hdvd : 3 ∣ 2 ^ f + 1 := UnitaryCenter.three_dvd_two_pow_add_one_of_odd hfo
    have h := ggUnitaryTorusRank_le_largeEvenTwoLocalRank hF hf hn hdvd ψ hker
    rw [hm] at h
    have hn6 : n ≤ 6 := by
      by_cases h3 : 3 ∣ n
      · simp only [ggUnitaryTorusRank, h3, ite_true] at h
        obtain ⟨k, rfl⟩ := h3
        omega
      · simp only [ggUnitaryTorusRank, h3, ite_false] at h
        omega
    by_cases h5 : n ≤ 5
    · exact Or.inl h5
    · exact Or.inr (Or.inl ⟨hfo, by omega⟩)

end Bounds

end UnitaryRank

end CFSG.StandardType
