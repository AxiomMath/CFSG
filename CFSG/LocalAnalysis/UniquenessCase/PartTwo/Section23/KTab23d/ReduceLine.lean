module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.Transfer
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Bar2Map

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

open CFSG.Quasithin Matrix

variable {W : Type} [CommGroup W] {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

private theorem fixed_iff_coord_D13 {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
    (π : ↥Γ ≃* ↥H) (e : W ≃* Multiplicative (ι → K))
    (he : ∀ (γ : ↥Γ) (w : W), Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
      ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w))
    (S : Sylow 2 ↥H) {w₀ : ι → K}
    (hS : ∀ v : ι → K,
      (∀ s ∈ (S : Subgroup ↥H), (((π.symm s : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ v = v) ↔
        ∃ c : K, v = c • w₀) (y : W) :
    (∀ s ∈ (S : Subgroup ↥H), ((s : ↥H) : MulAut W) y = y) ↔
      ∃ c : K, Multiplicative.toAdd (e y) = c • w₀ := by
  constructor
  · intro hy
    refine (hS _).1 fun s hs => ?_
    have h3 := he (π.symm s) y
    rw [MulEquiv.apply_symm_apply, hy s hs] at h3
    exact h3.symm
  · rintro ⟨c, hc⟩ s hs
    apply e.injective
    apply Multiplicative.toAdd.injective
    have h3 := he (π.symm s) y
    rw [MulEquiv.apply_symm_apply] at h3
    rw [h3, hc]
    exact (hS (c • w₀)).2 ⟨c, rfl⟩ s hs

private theorem mem_lineStab_iff_D13 {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
    (π : ↥Γ ≃* ↥H) (e : W ≃* Multiplicative (ι → K))
    (he : ∀ (γ : ↥Γ) (w : W), Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
      ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w))
    (S : Sylow 2 ↥H) {w₀ : ι → K}
    (hS : ∀ v : ι → K,
      (∀ s ∈ (S : Subgroup ↥H), (((π.symm s : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ v = v) ↔
        ∃ c : K, v = c • w₀)
    (γ : ↥Γ) :
    γ ∈ lineStab Γ w₀ ↔ π γ ∈ pointStab H S := by
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  letI : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
  have hmem : ∀ y : W, y ∈ (CFSG.fixedPointSubgroup ↥S W : Subgroup W) ↔
      ∃ c : K, Multiplicative.toAdd (e y) = c • w₀ := fun y => by
    rw [FixedPoints.mem_subgroup]
    refine Iff.trans ?_ (fixed_iff_coord_D13 π e he S hS y)
    exact ⟨fun hy s hs => hy ⟨s, hs⟩, fun hy s => hy s s.2⟩
  have hinv : ∀ (a : ↥Γ) (v : ι → K),
      (((a⁻¹ : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ
        ((((a : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ v) = v := by
    intro a v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
  show γ ∈ lineStab Γ w₀ ↔ π γ ∈ MulAction.stabilizer ↥H
    ((CFSG.fixedPointSubgroup ↥S W : Subgroup W) : Set W)
  rw [MulAction.mem_stabilizer_set]
  have hact : ∀ b : W, Multiplicative.toAdd (e ((π γ : ↥H) • b)) =
      (((γ : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e b) := fun b => he γ b
  constructor
  · intro hγ b
    obtain ⟨d, hd⟩ := (inv_mem hγ : γ⁻¹ ∈ lineStab Γ w₀)
    obtain ⟨c, hc⟩ := hγ
    simp only [SetLike.mem_coe, hmem, hact]
    constructor
    · rintro ⟨c', hc'⟩
      exact ⟨c' * d, by rw [← hinv γ (Multiplicative.toAdd (e b)), hc', Matrix.mulVec_smul, hd,
        smul_smul]⟩
    · rintro ⟨c', hc'⟩
      exact ⟨c' * c, by rw [hc', Matrix.mulVec_smul, hc, smul_smul]⟩
  · intro hstab
    have hb₀ : e.symm (Multiplicative.ofAdd w₀) ∈ (CFSG.fixedPointSubgroup ↥S W : Subgroup W) :=
      (hmem _).2 ⟨1, by simp⟩
    have h1 := (hstab (e.symm (Multiplicative.ofAdd w₀))).2 hb₀
    rw [SetLike.mem_coe, hmem, hact] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by simpa using hc⟩

theorem pointStab_eq_map_lineStab {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
    (π : ↥Γ ≃* ↥H) (e : W ≃* Multiplicative (ι → K))
    (he : ∀ (γ : ↥Γ) (w : W), Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
      ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w))
    (S : Sylow 2 ↥H) {w₀ : ι → K}
    (hS : ∀ v : ι → K,
      (∀ s ∈ (S : Subgroup ↥H), (((π.symm s : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ v = v) ↔
        ∃ c : K, v = c • w₀) :
    pointStab H S = (lineStab Γ w₀).map π.toMonoidHom := by
  ext h
  rw [Subgroup.mem_map]
  constructor
  · intro hh
    refine ⟨π.symm h, ?_, MulEquiv.apply_symm_apply π h⟩
    exact (mem_lineStab_iff_D13 π e he S hS _).2 (by rwa [MulEquiv.apply_symm_apply])
  · rintro ⟨γ, hγ, rfl⟩
    exact (mem_lineStab_iff_D13 π e he S hS γ).1 hγ

theorem exists_mulEquiv_pointStab_eq_map [Finite W] {Γ : Subgroup (GL ι K)}
    {H : Subgroup (MulAut W)} (hreal : (FFModel.nat Γ).Realizes H ⊤ ⊥) {e₀ : ι → K}
    (hline : KTabC.SylowFixedLine Γ e₀) (S : Sylow 2 ↥H) :
    ∃ φ : ↥Γ ≃* ↥H, pointStab H S = (lineStab Γ e₀).map φ.toMonoidHom := by
  obtain ⟨π, e, he⟩ := KTabC.exists_natEquiv hreal
  obtain ⟨x, hx⟩ := hline (S.mapSurjective (f := π.symm.toMonoidHom) π.symm.surjective)
  have hS : ∀ v : ι → K, (∀ s ∈ (S : Subgroup ↥H),
      (((π.symm s : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ v = v) ↔
        ∃ c : K, v = c • (((x : GL ι K) : Matrix ι ι K) *ᵥ e₀) :=
    fun v => (KTabC.fixed_iff_fixed_sylowMap π S v).trans (hx v)
  have h1 := pointStab_eq_map_lineStab π e he S hS
  refine ⟨(MulAut.conj x).trans π, ?_⟩
  rw [h1, lineStab_mulVec Γ x e₀, Subgroup.map_map]
  rfl

theorem bar2_hinf_pointStab_equiv [Finite W] [Finite K] {Γ : Subgroup (GL ι K)}
    {H : Subgroup (MulAut W)} (hreal : (FFModel.nat Γ).Realizes H ⊤ ⊥) {e₀ : ι → K}
    (hline : KTabC.SylowFixedLine Γ e₀) (S : Sylow 2 ↥H) :
    Nonempty (Bar2 (Hinf (pointStab H S)) ≃* Bar2 (Hinf (lineStab Γ e₀))) ∧
      (Hinf (pointStab H S) = ⊥ ↔ Hinf (lineStab Γ e₀) = ⊥) ∧
      (pointStab H S = ⊤ ↔ lineStab Γ e₀ = ⊤) := by
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_pointStab_eq_map hreal hline S
  rw [hφ]
  refine ⟨?_, hinf_map_mulEquiv_eq_bot_iff φ _, map_mulEquiv_eq_top_iff φ _⟩
  obtain ⟨f⟩ := nonempty_bar2_hinf_map φ (lineStab Γ e₀)
  exact ⟨f.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
