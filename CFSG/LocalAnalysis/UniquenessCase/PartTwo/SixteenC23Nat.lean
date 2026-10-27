module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitSLNatural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H13.Orbit CFSG.Assembly.LowTwoRank

theorem c23_binaryNatural_stable {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} {d a : ℕ} (h : BinaryNaturalSL H U Z d a) :
    ∀ φ ∈ H, ∀ u ∈ U, (φ : MulAut V) u ∈ U := by
  obtain ⟨K, _, _, _, π, hπ⟩ := h
  obtain ⟨-, -, -, hstable, -, -, -, -⟩ := hπ
  intro φ hφ u hu
  exact hstable ⟨φ, hφ⟩ u hu

theorem c23_binaryNatural_transitive {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)}
    {U : Subgroup V} (h : BinaryNaturalSL H U ⊥ 3 1) :
    ∀ u ∈ U, u ≠ 1 → ∀ u' ∈ U, u' ≠ 1 → ∃ φ ∈ H, (φ : MulAut V) u = u' := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  obtain ⟨-, -, -, hstable, -, -, -, β, hβs, hβk, hβact⟩ := hπ
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have hinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥U) : V) = 1 :=
      Subgroup.mem_bot.mp ((hβk (a * b⁻¹)).mp h1)
    rw [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  intro u hu hu1 u' hu' hu'1
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨u, hu⟩)
  obtain ⟨m', hm'⟩ := QuotientGroup.mk_surjective (β ⟨u', hu'⟩)
  have hβu : β ⟨u, hu⟩ = QuotientGroup.mk m := hm.symm
  have hβu' : β ⟨u', hu'⟩ = QuotientGroup.mk m' := hm'.symm
  have hmne : m ≠ 1 := by
    intro hm1
    have hb1 : β ⟨u, hu⟩ = 1 := by rw [hβu, hm1]; simp
    exact hu1 (Subgroup.mem_bot.mp ((hβk ⟨u, hu⟩).mp hb1))
  have hm'ne : m' ≠ 1 := by
    intro hm'1
    have hb1 : β ⟨u', hu'⟩ = 1 := by rw [hβu', hm'1]; simp
    exact hu'1 (Subgroup.mem_bot.mp ((hβk ⟨u', hu'⟩).mp hb1))
  have hx : Multiplicative.toAdd (α := Fin 3 → K)
      (m : (FFModel.nat (StatedSL 3 K)).Amb) ≠ 0 :=
    fun h0 => hmne (Subtype.ext ((toAdd_eq_zero (α := Fin 3 → K)).mp h0))
  have hy : Multiplicative.toAdd (α := Fin 3 → K)
      (m' : (FFModel.nat (StatedSL 3 K)).Amb) ≠ 0 :=
    fun h0 => hm'ne (Subtype.ext ((toAdd_eq_zero (α := Fin 3 → K)).mp h0))
  obtain ⟨g, hg⟩ := exists_SL_mulVec_eq hK2 hx hy
  have hgS : Matrix.SpecialLinearGroup.toGL g ∈ StatedSL 3 K :=
    Subgroup.subset_closure (by simp)
  let γ : ↥(StatedSL 3 K) := ⟨Matrix.SpecialLinearGroup.toGL g, hgS⟩
  have hdeq : (FFModel.nat (StatedSL 3 K)).act γ (m : (FFModel.nat (StatedSL 3 K)).Amb) =
      (m' : (FFModel.nat (StatedSL 3 K)).Amb) := by
    rw [show (FFModel.nat (StatedSL 3 K)).act γ (m : (FFModel.nat (StatedSL 3 K)).Amb) =
        Multiplicative.ofAdd (((g : Matrix (Fin 3) (Fin 3) K)).mulVec
          (Multiplicative.toAdd (α := Fin 3 → K)
            (m : (FFModel.nat (StatedSL 3 K)).Amb))) from rfl]
    rw [hg]
    rfl
  have hu'' : ((π γ : ↥H) : MulAut V) u ∈ U := hstable (π γ) u hu
  refine ⟨π γ, (π γ).2, ?_⟩
  have hbu : β ⟨((π γ : ↥H) : MulAut V) u, hu''⟩ = β ⟨u', hu'⟩ := by
    rw [hβact γ ⟨u, hu⟩ m hu'' (Subgroup.mem_top _) hβu, hβu']
    rw [show (⟨(FFModel.nat (StatedSL 3 K)).act γ
          (m : (FFModel.nat (StatedSL 3 K)).Amb), Subgroup.mem_top _⟩ :
        ↥(FFModel.nat (StatedSL 3 K)).sec) = m' from Subtype.ext hdeq]
  exact Subtype.ext_iff.mp (hinj hbu)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
