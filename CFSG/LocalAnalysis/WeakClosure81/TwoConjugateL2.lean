module

public import CFSG.LocalAnalysis.WeakClosure81.TwoConjugateL2Close
public import CFSG.LocalAnalysis.WeakClosure81.TwoConjugateL2Conj
public import CFSG.Milestones.ASVolI.C121.P4Gbar

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TwoConjL2

open Matrix CFSG.RankThree.PartOne.CTP

theorem exists_ne_zero_forall_subfield (F : Type) [Field F] [Finite F] :
    ∃ ν : F, ν ≠ 0 ∧ ∀ k : Subfield F, ν ∈ k → k = ⊤ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  refine ⟨(g : F), g.ne_zero, fun k hk => ?_⟩
  refine eq_top_iff.2 fun z _ => ?_
  by_cases hz : z = 0
  · rw [hz]
    exact k.zero_mem
  · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg (Units.mk0 z hz))
    have hzn : z = (g : F) ^ n := by
      have := congrArg (fun u : Fˣ => (u : F)) hn
      simpa using this.symm
    rw [hzn]
    exact k.zpow_mem hk n

theorem exists_sup_conj_eq_top {F : Type} [Field F] [Finite F]
    [CharP F 2] {B : Subgroup (SpecialLinearGroup (Fin 2) F)} (hB : IsPGroup 2 B)
    (hcard : 2 < Nat.card B) :
    ∃ γ : SpecialLinearGroup (Fin 2) F, B ⊔ CFSG.Quasithin.conjSubgroup B γ = ⊤ := by
  classical
  obtain ⟨h, hh⟩ := exists_conj_le_u2 hB
  haveI : Fintype B := Fintype.ofFinite B
  have hcard' : 2 < (Finset.univ : Finset B).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨b₁, b₂, hb : b₁ ≠ 1 ∧ b₂ ≠ 1 ∧ b₁ ≠ b₂⟩ : ∃ b₁ b₂ : B, b₁ ≠ 1 ∧ b₂ ≠ 1 ∧ b₁ ≠ b₂ := by
    obtain ⟨a, -, b, -, c, -, hab, hac, hbc⟩ := Finset.two_lt_card.mp hcard'
    by_cases ha : a = 1
    · exact ⟨b, c, fun hb => hab (ha.trans hb.symm), fun hc => hac (ha.trans hc.symm), hbc⟩
    · by_cases hb : b = 1
      · exact ⟨a, c, ha, fun hc => hbc (hb.trans hc.symm), hac⟩
      · exact ⟨a, b, ha, hb, hab⟩
  obtain ⟨a₁, ha₁⟩ := hh b₁ b₁.2
  obtain ⟨a₂, ha₂⟩ := hh b₂ b₂.2
  have hb₁ : (b₁ : SpecialLinearGroup (Fin 2) F) = h * u2 a₁ * h⁻¹ := by rw [← ha₁]; group
  have hb₂ : (b₂ : SpecialLinearGroup (Fin 2) F) = h * u2 a₂ * h⁻¹ := by rw [← ha₂]; group
  have ha₁0 : a₁ ≠ 0 := by
    rintro rfl
    apply hb.1
    apply Subtype.ext
    rw [hb₁, u2_zero]
    simp
  have ha₂0 : a₂ ≠ 0 := by
    rintro rfl
    apply hb.2.1
    apply Subtype.ext
    rw [hb₂, u2_zero]
    simp
  have ha₁₂ : a₁ ≠ a₂ := by
    rintro rfl
    apply hb.2.2
    apply Subtype.ext
    rw [hb₁, hb₂]
  obtain ⟨ν, hν0, hν⟩ := exists_ne_zero_forall_subfield F
  set μ : F := ν / a₁ ^ 2 with hμdef
  have hμ0 : μ ≠ 0 := div_ne_zero hν0 (pow_ne_zero 2 ha₁0)
  have hμν : μ * a₁ ^ 2 = ν := by rw [hμdef]; field_simp
  obtain ⟨γ₀, hγ₀⟩ := exists_conj_u2_eq_l2 hμ0
  refine ⟨h * γ₀ * h⁻¹, ?_⟩
  set M := B ⊔ CFSG.Quasithin.conjSubgroup B (h * γ₀ * h⁻¹) with hM
  have hl : ∀ (a : F) (b : SpecialLinearGroup (Fin 2) F), b ∈ B → b = h * u2 a * h⁻¹ →
      h * l2 (μ * a) * h⁻¹ ∈ CFSG.Quasithin.conjSubgroup B (h * γ₀ * h⁻¹) := by
    intro a b hbB hba
    rw [CFSG.Quasithin.mem_conjSubgroup_iff]
    have hc : γ₀ * l2 (μ * a) * γ₀⁻¹ = u2 a := by
      rw [← hγ₀ a]
      group
    have : h * γ₀ * h⁻¹ * (h * l2 (μ * a) * h⁻¹) * (h * γ₀ * h⁻¹)⁻¹ = h * u2 a * h⁻¹ := by
      rw [← hc]
      group
    rw [this, ← hba]
    exact hbB
  have htop : Subgroup.comap (MulAut.conj h).toMonoidHom M = ⊤ := by
    refine sl2_eq_top_of_two_root_pairs (x := a₁) (y := a₂) (μ := μ) ha₁0 ha₂0 ha₁₂
      (fun k hk => hν k (by rwa [hμν] at hk)) ?_ ?_ ?_ ?_
    · rw [Subgroup.mem_comap]
      change h * u2 a₁ * h⁻¹ ∈ M
      rw [← hb₁]
      exact Subgroup.mem_sup_left b₁.2
    · rw [Subgroup.mem_comap]
      change h * u2 a₂ * h⁻¹ ∈ M
      rw [← hb₂]
      exact Subgroup.mem_sup_left b₂.2
    · rw [Subgroup.mem_comap]
      exact Subgroup.mem_sup_right (hl a₁ b₁ b₁.2 hb₁)
    · rw [Subgroup.mem_comap]
      exact Subgroup.mem_sup_right (hl a₂ b₂ b₂.2 hb₂)
  refine eq_top_iff.2 fun z _ => ?_
  have hz : h⁻¹ * z * h ∈ Subgroup.comap (MulAut.conj h).toMonoidHom M := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_comap] at hz
  have : (MulAut.conj h).toMonoidHom (h⁻¹ * z * h) = z := by
    change h * (h⁻¹ * z * h) * h⁻¹ = z
    group
  rwa [this] at hz

theorem twoConjugateGeneration_of_isPSL {S : Type} [Group S]
    [Finite S] {n : ℕ} (hS : CFSG.Quasithin.IsPSL 2 2 n S) {A : Subgroup S}
    (hA : CFSG.Open.IsElemAbelian 2 A) (hcard : 2 < Nat.card A) :
    ∃ g : S, A ⊔ CFSG.Quasithin.conjSubgroup A g = ⊤ := by
  classical
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := CFSG.Quasithin.burnsideC121_p4_psl_equiv hS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow hKcard
  haveI : Finite K := Finite.of_fintype K
  let B : Subgroup (SpecialLinearGroup (Fin 2) K) := A.map e.toMonoidHom
  have hBp : IsPGroup 2 B := by
    intro b
    obtain ⟨a, ha, hab⟩ := Subgroup.mem_map.mp b.2
    refine ⟨1, Subtype.ext ?_⟩
    have := hA.2 a ha
    rw [Subgroup.coe_pow, ← hab]
    simp only [pow_one, MonoidHom.coe_coe, ← map_pow, this, map_one]
    rfl
  have hBcard : Nat.card B = Nat.card A := Subgroup.card_map_of_injective e.injective
  obtain ⟨γ, hγ⟩ := exists_sup_conj_eq_top hBp (hBcard ▸ hcard)
  refine ⟨e.symm γ, ?_⟩
  refine eq_top_iff.2 fun s _ => ?_
  have hs : e s ∈ B ⊔ CFSG.Quasithin.conjSubgroup B γ := by rw [hγ]; exact Subgroup.mem_top _
  have hle : B ⊔ CFSG.Quasithin.conjSubgroup B γ ≤
      (A ⊔ CFSG.Quasithin.conjSubgroup A (e.symm γ)).map e.toMonoidHom := by
    refine sup_le (Subgroup.map_mono le_sup_left) ?_
    intro z hz
    rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hz
    obtain ⟨a, ha, hab⟩ := Subgroup.mem_map.mp hz
    refine Subgroup.mem_map.mpr ⟨e.symm z, Subgroup.mem_sup_right ?_, by simp⟩
    rw [CFSG.Quasithin.mem_conjSubgroup_iff]
    have : e.symm γ * e.symm z * (e.symm γ)⁻¹ = a := by
      apply e.injective
      simpa using hab.symm
    rw [this]
    exact ha
  obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.mp (hle hs)
  have : t = s := e.injective hts
  rwa [← this]

end CFSG.LocalAnalysis.WeakClosure81.TwoConjL2
