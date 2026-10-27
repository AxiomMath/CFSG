module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivFactors

public section

namespace CFSG.StandardType

namespace LayerPDiv

open Matrix LayerCores CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

theorem card_sub_one_dvd_of_algebra {K D : Type*} [Field K] [Field D] [Algebra K D] [Finite D] :
    Nat.card K - 1 ∣ Nat.card D - 1 := by
  have : Finite K := Finite.of_injective _ (algebraMap K D).injective
  have : Module.Finite K D := inferInstance
  rw [Module.natCard_eq_pow_finrank (K := K) (V := D)]
  simpa using Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 (Module.finrank K D)

theorem sub_one_dvd_sq_sub_one (x : ℕ) : x - 1 ∣ x ^ 2 - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow x 1 2

variable {K : Type} [Field K] {f n : ℕ}

theorem exists_coreFamily_su_pDiv (h : UnitaryFieldData 2 f K) {A : Subgroup (GL (Fin n) K)}
    (hA : (Nat.card A : K) ≠ 0)
    (hAN : A ≤ Subgroup.normalizer (unitarySU 2 f K n : Set (GL (Fin n) K))) {p : ℕ}
    (hpK : p ∣ Nat.card K - 1) :
    ∃ (β : Type) (S : β → Subgroup ↥(unitarySU 2 f K n)),
      IsCoreFamily ((Subgroup.centralizer (A : Set (GL (Fin n) K))).comap
        (unitarySU 2 f K n).subtype) S ∧ ∀ c, p ∣ Nat.card (S c) := by
  classical
  have := h.finite
  have : CharP K 2 := h.charP
  have hsymd : ∃ Y : Matrix (Fin n) (Fin n) K, (∀ g ∈ A, Y * (g : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * Y) ∧ Y + suAdj h Y = 1 := by
    obtain ⟨c, hc⟩ := exists_add_bar_eq_one h
    refine ⟨c • 1, fun g _ => by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one], ?_⟩
    rw [suAdj_smul_one, ← add_smul, hc, one_smul]
  obtain ⟨r, D, d, _, _, _, _, Φ, hΦ, hR⟩ := exists_algHom_pi_matrix_commutant A hA
  have : ∀ i, CharP (D i) 2 := fun i =>
    charP_of_injective_algebraMap (algebraMap K (D i)).injective 2
  obtain ⟨τ, hτ, hτΦ, himg⟩ := exists_tau_of_adj Φ hΦ hR (isInvol_suAdj (n := n) h)
    fun X hX => (hR _).mpr fun g hg => suAdj_mul_comm h hAN X ((hR X).mp hX) hg
  have hy : ∃ y, y + τ y = 1 := by
    obtain ⟨Y, hYc, hY⟩ := hsymd
    obtain ⟨y, rfl⟩ := (hR Y).mpr hYc
    exact ⟨y, hΦ (by rw [map_add, hτΦ, hY, map_one])⟩
  obtain ⟨π, hπ⟩ := hτ.exists_perm
  have hfix : ∀ b (hb : π b = b), HasCore (matUnitary (isInvol_tauFix hτ hπ hb)) := by
    intro b hb
    by_cases hk : ∀ c : D b, tauFix τ b (Matrix.scalar (Fin (d b)) c) =
        Matrix.scalar (Fin (d b)) c
    · obtain ⟨Y, hY⟩ := hy
      refine altCoreInput_holds (D b) (d b) _ (isInvol_tauFix hτ hπ hb) hk ⟨Y b, ?_⟩
      have h1 := congrFun hY b
      rwa [Pi.add_apply, apply_tau_eq_tauFix hτ hπ hb, Pi.one_apply] at h1
    · push Not at hk
      exact hermCoreInput_holds (D b) (d b) _ (isInvol_tauFix hτ hπ hb) hk
  have hpair : ∀ b, π b ≠ b → HasCore (⊤ : Subgroup (GL (Fin (d b)) (D b))) :=
    fun b _ => hasCore_top_GL (d b)
  have hcore := hasCore_factorGroup hτ hπ hfix hpair
  have hX : ∀ b, b ≤ π b → Group.IsSolvable (factorGroup π hτ hπ b) ∨
      ∃ X : Subgroup (GL (Fin (d b)) (D b)), X ≤ factorGroup π hτ hπ b ∧ ⁅X, X⁆ = X ∧
        p ∣ Nat.card X := by
    intro b _
    have hpD1 : p ∣ Nat.card (D b) - 1 := hpK.trans card_sub_one_dvd_of_algebra
    have hpD2 : p ∣ Nat.card (D b) ^ 2 - 1 := hpD1.trans (sub_one_dvd_sq_sub_one _)
    by_cases hb : π b = b
    · have hfg : factorGroup π hτ hπ b = matUnitary (isInvol_tauFix hτ hπ hb) := by
        unfold factorGroup
        split_ifs
        rfl
      rw [hfg]
      by_cases hk : ∀ c : D b, tauFix τ b (Matrix.scalar (Fin (d b)) c) =
          Matrix.scalar (Fin (d b)) c
      · obtain ⟨Y, hY⟩ := hy
        have hYb : Y b + tauFix τ b (Y b) = 1 := by
          have h1 := congrFun hY b
          rwa [Pi.add_apply, apply_tau_eq_tauFix hτ hπ hb, Pi.one_apply] at h1
        rcases altFactorPDivInput_holds (D b) (d b) _ (isInvol_tauFix hτ hπ hb) hk ⟨Y b, hYb⟩ with
          h | ⟨X, hX1, hX2, hX3⟩
        · exact Or.inl h
        · exact Or.inr ⟨X, hX1, hX2, hpD2.trans hX3⟩
      · push Not at hk
        rcases hermFactorPDivInput_holds (D b) (d b) _ (isInvol_tauFix hτ hπ hb) hk with
          h | ⟨X, hX1, hX2, hX3⟩
        · exact Or.inl h
        · exact Or.inr ⟨X, hX1, hX2, hpD1.trans hX3⟩
    · have hfg : factorGroup π hτ hπ b = ⊤ := by
        unfold factorGroup
        split_ifs
        rfl
      rw [hfg]
      rcases glFactor_pDiv (E := D b) (d b) with h | ⟨X, hX1, hX2, hX3⟩
      · exact Or.inl h
      · exact Or.inr ⟨X, hX1, hX2, hpD2.trans hX3⟩
  obtain ⟨β, S, h1, h2, h3, h4, h5⟩ := exists_core_of_factors hτ hπ hfix hpair
  have hS : IsCoreFamily (unitaryOf hτ) S := ⟨h1, h2, h3, h4, h5⟩
  have hSadj := hS.map _ (Units.map_injective (f := Φ.toMonoidHom) hΦ)
  rw [himg] at hSadj
  set H₀ : Subgroup (GL (Fin n) K) :=
    adjCent A (isInvol_suAdj (n := n) h) ⊓ (Matrix.GeneralLinearGroup.det).ker with hH₀
  have hSdet : ∀ c, (S c).map (Units.map Φ.toMonoidHom) ≤ H₀ := by
    intro c
    refine le_inf (hSadj.1 c) ?_
    have hq : CFSG.IsQuasisimple ((S c).map (Units.map Φ.toMonoidHom)) := hSadj.2.2.1 c
    rw [← LayerFacts.ggCommutator_eq_of_isQuasisimple hq]
    exact (Subgroup.commutator_mono le_top le_top).trans (Abelianization.commutator_subset_ker _)
  have hS0 := hSadj.mono inf_le_left hSdet
  have hdet : ∀ g : GL (Fin n) K, g ∈ (Matrix.GeneralLinearGroup.det).ker ↔
      (g : Matrix (Fin n) (Fin n) K).det = 1 := fun g => by
    rw [MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  have hle : H₀ ≤ (unitarySU 2 f K n).subtype.range := by
    intro g hg
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
    exact ⟨⟨g, (mem_unitarySU_iff_suAdj h).mpr ⟨(Subgroup.mem_inf.mp hg1).2, (hdet g).mp hg2⟩⟩,
      rfl⟩
  have hC : H₀.comap (unitarySU 2 f K n).subtype =
      (Subgroup.centralizer (A : Set (GL (Fin n) K))).comap (unitarySU 2 f K n).subtype := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, hH₀, adjCent, Subgroup.mem_inf, Subgroup.mem_inf]
    have hx := (mem_unitarySU_iff_suAdj h).mp x.2
    exact ⟨fun hx' => hx'.1.1, fun hx' => ⟨⟨hx', hx.1⟩, (hdet _).mpr hx.2⟩⟩
  have h2' := hS0.comap (unitarySU 2 f K n).subtype (Subgroup.subtype_injective _) hle
  rw [hC] at h2'
  refine ⟨β, fun c => ((S c).map (Units.map Φ.toMonoidHom)).comap (unitarySU 2 f K n).subtype,
    h2', fun c => ?_⟩
  have hcardc : Nat.card (((S c).map (Units.map Φ.toMonoidHom)).comap
      (unitarySU 2 f K n).subtype) = Nat.card (S c) := by
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective (unitarySU 2 f K n)),
      Subgroup.map_comap_eq_self ((hSdet c).trans hle),
      Subgroup.card_map_of_injective (Units.map_injective (f := Φ.toMonoidHom) hΦ)]
  rw [hcardc]
  exact dvd_card_of_conj_mem_unitaryOf hτ hπ hcore hX (h1 c) (h2 c) (h3 c)

end LayerPDiv

end CFSG.StandardType
