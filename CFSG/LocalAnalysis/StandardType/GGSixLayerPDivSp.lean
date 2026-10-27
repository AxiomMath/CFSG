module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivUnitary
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresFinal
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDiv

public section

namespace CFSG.StandardType

namespace LayerPDiv

open Matrix LayerCores CFSG.Assembly.LowTwoRank

@[expose] def AltFactorPDivInput : Prop :=
  ∀ (D : Type) [Field D] [Finite D] [CharP D 2] (d : ℕ)
    (T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D) (hT : IsInvol T),
    (∀ c : D, T (Matrix.scalar (Fin d) c) = Matrix.scalar (Fin d) c) → (∃ y, y + T y = 1) →
      Group.IsSolvable (matUnitary hT) ∨
        ∃ X : Subgroup (GL (Fin d) D), X ≤ matUnitary hT ∧ ⁅X, X⁆ = X ∧
          Nat.card D ^ 2 - 1 ∣ Nat.card X

@[expose] def HermFactorPDivInput : Prop :=
  ∀ (D : Type) [Field D] [Finite D] [CharP D 2] (d : ℕ)
    (T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D) (hT : IsInvol T),
    (∃ c : D, T (Matrix.scalar (Fin d) c) ≠ Matrix.scalar (Fin d) c) →
      Group.IsSolvable (matUnitary hT) ∨
        ∃ X : Subgroup (GL (Fin d) D), X ≤ matUnitary hT ∧ ⁅X, X⁆ = X ∧
          Nat.card D - 1 ∣ Nat.card X

section Scalars

variable {F : Type} [Field F] {r : ℕ} {D : Fin r → Type} [∀ i, Field (D i)]
  [∀ i, Algebra F (D i)] {d : Fin r → ℕ} {τ : PiMat D d → PiMat D d} {π : Fin r → Fin r}

theorem algebraMap_piMat_apply (a : F) (b : Fin r) :
    (algebraMap F (PiMat D d) a) b = Matrix.scalar (Fin (d b)) (algebraMap F (D b) a) := by
  ext i j
  simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

theorem tauFix_scalar_algebraMap (hτ : IsInvol τ) (hπ : ∀ i, τ (piE D d i) = piE D d (π i))
    {b : Fin r} (hb : π b = b)
    (hτF : ∀ a : F, τ (algebraMap F (PiMat D d) a) = algebraMap F (PiMat D d) a) (a : F) :
    tauFix τ b (Matrix.scalar (Fin (d b)) (algebraMap F (D b) a)) =
      Matrix.scalar (Fin (d b)) (algebraMap F (D b) a) := by
  have h1 : (Pi.single b (Matrix.scalar (Fin (d b)) (algebraMap F (D b) a)) : PiMat D d) =
      algebraMap F (PiMat D d) a * piE D d b := by
    rw [mul_piE, algebraMap_piMat_apply]
  show τ (Pi.single b _) b = _
  rw [h1, hτ.map_mul, hπ, hb, hτF, piE_mul, Pi.single_eq_same, algebraMap_piMat_apply]

end Scalars

section Sp

variable {n : ℕ} {F : Type} [Field F]

theorem exists_coreFamily_sp_pDiv (hAltP : AltFactorPDivInput) (hHermP : HermFactorPDivInput)
    [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : p ∣ Nat.card F ^ 2 - 1) {A : Subgroup (StatedSp n F)} (hA : IsPGroup p A) :
    ∃ (β : Type) (S : β → Subgroup (StatedSp n F)),
      IsCoreFamily (Subgroup.centralizer (A : Set (StatedSp n F))) S ∧
        ∀ c, p ∣ Nat.card (S c) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set A' : Subgroup (GL (Fin n ⊕ Fin n) F) := A.map (StatedSp n F).subtype with hA'
  have hA'sp : ∀ g ∈ A', g ∈ StatedSp n F := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hcard : (Nat.card A' : F) ≠ 0 := by
    rw [hA', Nat.card_congr (A.equivMapOfInjective _ (Subgroup.subtype_injective _)).toEquiv.symm]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
    rw [hk, Nat.cast_pow]
    refine pow_ne_zero _ fun h => hp2 ?_
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp h
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  obtain ⟨r, D, d, _, _, _, _, Φ, hΦ, hR⟩ := exists_algHom_pi_matrix_commutant A' hcard
  have : ∀ i, CharP (D i) 2 := fun i =>
    charP_of_injective_algebraMap (algebraMap F (D i)).injective 2
  obtain ⟨τ, hτ, hτΦ, himg⟩ := exists_tau_of_adj Φ hΦ hR (isInvol_spAdj (n := n) (F := F))
    fun X hX => (hR _).mpr fun g hg => spAdj_mul_comm hA'sp X ((hR X).mp hX) hg
  obtain ⟨π, hπ⟩ := hτ.exists_perm
  have hy : ∃ y, y + τ y = 1 := by
    obtain ⟨Y, hYc, hY⟩ := exists_symd_spAdj hA'sp hcard
    obtain ⟨y, rfl⟩ := (hR Y).mpr hYc
    exact ⟨y, hΦ (by rw [map_add, hτΦ, hY, map_one])⟩
  have hτF : ∀ a : F, τ (algebraMap F (PiMat D d) a) = algebraMap F (PiMat D d) a := by
    intro a
    apply hΦ
    rw [hτΦ, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, spAdj_smul,
      isInvol_spAdj.map_one]
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
    have hpD2 : p ∣ Nat.card (D b) ^ 2 - 1 := hpF.trans sq_sub_one_dvd_of_algebra
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
        rcases hAltP (D b) (d b) _ (isInvol_tauFix hτ hπ hb) hk ⟨Y b, hYb⟩ with
          h | ⟨X, hX1, hX2, hX3⟩
        · exact Or.inl h
        · exact Or.inr ⟨X, hX1, hX2, hpD2.trans hX3⟩
      · push Not at hk
        rcases hHermP (D b) (d b) _ (isInvol_tauFix hτ hπ hb) hk with h | ⟨X, hX1, hX2, hX3⟩
        · exact Or.inl h
        · refine Or.inr ⟨X, hX1, hX2, (hpF.trans ?_).trans hX3⟩
          obtain ⟨ρ, hρ, hρ2⟩ := (isInvol_tauFix hτ hπ hb).exists_rho
          refine sq_sub_one_dvd_card_sub_one_of_invol ρ hρ2 ?_ fun a => ?_
          · obtain ⟨c, hc⟩ := hk
            exact ⟨c, fun h => hc (by rw [hρ, h])⟩
          · apply scalar_injective (d := d b)
            rw [← hρ, tauFix_scalar_algebraMap hτ hπ hb hτF]
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
  have hle : adjCent A' (isInvol_spAdj (n := n) (F := F)) ≤ (StatedSp n F).subtype.range := by
    intro g hg
    exact ⟨⟨g, mem_unitaryOf_spAdj_iff.mp (Subgroup.mem_inf.mp hg).2⟩, rfl⟩
  have hC : (adjCent A' (isInvol_spAdj (n := n) (F := F))).comap (StatedSp n F).subtype =
      Subgroup.centralizer (A : Set (StatedSp n F)) := by
    ext x
    rw [Subgroup.mem_comap, adjCent, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hx1, -⟩ a ha
      exact Subtype.ext (hx1 _ ⟨a, ha, rfl⟩)
    · intro hx
      refine ⟨fun g hg => ?_, mem_unitaryOf_spAdj_iff.mpr x.2⟩
      obtain ⟨a, ha, rfl⟩ := hg
      exact congrArg Subtype.val (hx a ha)
  have h := hSadj.comap (StatedSp n F).subtype (Subgroup.subtype_injective _) hle
  rw [hC] at h
  refine ⟨β, fun c => ((S c).map (Units.map Φ.toMonoidHom)).comap (StatedSp n F).subtype, h,
    fun c => ?_⟩
  have hcardc : Nat.card (((S c).map (Units.map Φ.toMonoidHom)).comap (StatedSp n F).subtype) =
      Nat.card (S c) := by
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective (StatedSp n F)),
      Subgroup.map_comap_eq_self ((hSadj.1 c).trans hle),
      Subgroup.card_map_of_injective (Units.map_injective (f := Φ.toMonoidHom) hΦ)]
  rw [hcardc]
  exact dvd_card_of_conj_mem_unitaryOf hτ hπ hcore hX (h1 c) (h2 c) (h3 c)

end Sp

end LayerPDiv

end CFSG.StandardType
