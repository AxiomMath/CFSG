module

public import CFSG.Quasithin.Background.B4Models
import CFSG.Quasithin.Background.B69Mod
import CFSG.Quasithin.H13.KGLiePair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.LineChar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC

open CFSG.Quasithin Matrix

variable {W : Type} [CommGroup W] {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def SylowFixedLine (Γ : Subgroup (GL ι K)) (e₀ : ι → K) : Prop :=
  ∀ S : Sylow 2 ↥Γ, ∃ x : ↥Γ, ∀ v : ι → K,
    (∀ s ∈ (S : Subgroup ↥Γ), ((s : GL ι K) : Matrix ι ι K) *ᵥ v = v) ↔
      ∃ c : K, v = c • (((x : GL ι K) : Matrix ι ι K) *ᵥ e₀)

theorem exists_natEquiv {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
    (h : (FFModel.nat Γ).Realizes H ⊤ ⊥) :
    ∃ (π : ↥Γ ≃* ↥H) (e : W ≃* Multiplicative (ι → K)),
      ∀ (γ : ↥Γ) (w : W), Multiplicative.toAdd (e (((π γ : ↥H) : MulAut W) w)) =
        ((γ : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w) := by
  obtain ⟨π, hπ⟩ := h
  have hinj : Function.Injective π := CFSG.Quasithin.B69.natRealizes_injective hπ
  let π' : ↥Γ ≃* ↥H := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  obtain ⟨e₀, he₀⟩ : ∃ e : W ≃* ↥(⊤ : Subgroup (Multiplicative (ι → K))),
      ∀ (γ : ↥Γ) (w : W), (e (((π γ : ↥H) : MulAut W) w) : Multiplicative (ι → K)) =
        natAct Γ γ (e w : Multiplicative (ι → K)) := by
    obtain ⟨e₀, he₀⟩ := CFSG.Quasithin.H13.KGLie.exists_coordEquiv
      (D := FFModel.nat Γ) rfl hπ
    exact ⟨e₀, fun γ w => he₀ γ w⟩
  refine ⟨π', e₀.trans Subgroup.topEquiv, ?_⟩
  intro γ w
  have hπ' : ((π' γ : ↥H) : MulAut W) = ((π γ : ↥H) : MulAut W) := rfl
  have h1 : Multiplicative.toAdd
        ((e₀.trans Subgroup.topEquiv) (((π' γ : ↥H) : MulAut W) w)) =
      Multiplicative.toAdd (natAct Γ γ ((e₀.trans Subgroup.topEquiv) w)) := by
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, Subgroup.topEquiv_apply,
      Subgroup.topEquiv_apply]
    simpa [hπ'] using congrArg Multiplicative.toAdd (he₀ γ w)
  exact h1.trans rfl

theorem fixed_iff_fixed_sylowMap [Finite W] {Γ : Subgroup (GL ι K)}
    {H : Subgroup (MulAut W)} (π : ↥Γ ≃* ↥H) (S : Sylow 2 ↥H) (v : ι → K) :
    (∀ s ∈ (S : Subgroup ↥H), (((π.symm s : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ v = v) ↔
      ∀ s ∈ ((S.mapSurjective (f := π.symm.toMonoidHom) π.symm.surjective : Sylow 2 ↥Γ) :
          Subgroup ↥Γ), ((s : GL ι K) : Matrix ι ι K) *ᵥ v = v := by
  have hcoe : ((S.mapSurjective (f := π.symm.toMonoidHom) π.symm.surjective : Sylow 2 ↥Γ) :
      Subgroup ↥Γ) = (S : Subgroup ↥H).map π.symm.toMonoidHom :=
    Sylow.coe_mapSurjective (f := π.symm.toMonoidHom) π.symm.surjective S
  rw [hcoe]
  constructor
  · intro h s hs
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hs
    exact h t ht
  · intro h s hs
    exact h (π.symm s) (Subgroup.mem_map_of_mem π.symm.toMonoidHom hs)

section Generic

variable {H : Subgroup (MulAut W)} {ρ : ↥H →* GL ι K} {e : W ≃* Multiplicative (ι → K)}

theorem fixingSubgroupOf_fixedPointSubgroup_eq_vecStab
    (he : ∀ (h : ↥H) (w : W), Multiplicative.toAdd (e ((h : MulAut W) w)) =
      ((ρ h : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e w))
    (S : Sylow 2 ↥H) {w₀ : ι → K}
    (hS : ∀ v : ι → K, (∀ s ∈ (S : Subgroup ↥H), ((ρ s : GL ι K) : Matrix ι ι K) *ᵥ v = v) ↔
      ∃ c : K, v = c • w₀) :
    letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
    letI : MulAction ↥H W := MulAction.compHom W H.subtype
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    fixingSubgroupOf ↥H W (fixedPointSubgroup ↥S W : Set W) = vecStab ρ w₀ := by
  classical
  have smul_S : ∀ (s : ↥S) (w : W), s • w = ((s : ↥H) : MulAut W) w := fun _ _ => rfl
  have hmem : ∀ y : W,
      y ∈ fixedPointSubgroup ↥S W ↔ ∃ c : K, Multiplicative.toAdd (e y) = c • w₀ := by
    intro y
    rw [FixedPoints.mem_subgroup]
    constructor
    · intro hy
      have hy' : ∀ s ∈ (S : Subgroup ↥H),
          ((ρ s : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e y) =
            Multiplicative.toAdd (e y) := by
        intro s hs
        have h1 : (⟨s, hs⟩ : ↥S) • y = y := hy ⟨s, hs⟩
        have h2 : ((s : ↥H) : MulAut W) y = y := h1
        have h3 := he s y
        rw [h2] at h3
        exact h3.symm
      exact (hS _).1 hy'
    · rintro ⟨c, hc⟩ s
      have h1 : ((s : ↥H) : MulAut W) y = y := by
        apply e.injective
        apply Multiplicative.toAdd.injective
        rw [he (s : ↥H) y, hc]
        exact (hS (c • w₀)).2 ⟨c, rfl⟩ (s : ↥H) s.2
      exact h1
  ext h
  rw [mem_fixingSubgroup_iff, mem_vecStab]
  constructor
  · intro hfix
    have hy : e.symm (Multiplicative.ofAdd w₀) ∈ fixedPointSubgroup ↥S W := by
      rw [hmem]
      exact ⟨1, by simp⟩
    have h1 : (h : MulAut W) (e.symm (Multiplicative.ofAdd w₀)) =
        e.symm (Multiplicative.ofAdd w₀) := hfix _ hy
    have h2 := he h (e.symm (Multiplicative.ofAdd w₀))
    rw [h1] at h2
    simpa using h2.symm
  · intro hw₀ y hy
    have hy' : y ∈ fixedPointSubgroup ↥S W := hy
    rw [hmem] at hy'
    obtain ⟨c, hc⟩ := hy'
    have h1 : (h : MulAut W) y = y := by
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [he h y, hc, Matrix.mulVec_smul, hw₀]
    exact h1

theorem exists_mulVec_eq_smul_of_mem_normalizer (S : Sylow 2 ↥H) {w₀ : ι → K}
    (hS : ∀ v : ι → K, (∀ s ∈ (S : Subgroup ↥H), ((ρ s : GL ι K) : Matrix ι ι K) *ᵥ v = v) ↔
      ∃ c : K, v = c • w₀)
    {g : ↥H} (hg : g ∈ Subgroup.normalizer ((S : Subgroup ↥H) : Set ↥H)) :
    ∃ c : K, ((ρ g : GL ι K) : Matrix ι ι K) *ᵥ w₀ = c • w₀ := by
  have hw₀ : ∀ s ∈ (S : Subgroup ↥H),
      ((ρ s : GL ι K) : Matrix ι ι K) *ᵥ w₀ = w₀ :=
    (hS w₀).2 ⟨1, by simp⟩
  have hconj : ∀ s ∈ (S : Subgroup ↥H),
      ((ρ (g⁻¹ * s * g) : GL ι K) : Matrix ι ι K) *ᵥ w₀ = w₀ := by
    intro s hs
    have hg' : g⁻¹ ∈ Subgroup.normalizer ((S : Subgroup ↥H) : Set ↥H) :=
      Subgroup.inv_mem _ hg
    have hmem : g⁻¹ * s * (g⁻¹)⁻¹ ∈ (S : Subgroup ↥H) :=
      (Subgroup.mem_normalizer_iff.1 hg' s).1 hs
    simpa [inv_inv] using hw₀ _ hmem
  have hfix : ∀ s ∈ (S : Subgroup ↥H),
      ((ρ s : GL ι K) : Matrix ι ι K) *ᵥ
        (((ρ g : GL ι K) : Matrix ι ι K) *ᵥ w₀) =
      ((ρ g : GL ι K) : Matrix ι ι K) *ᵥ w₀ := by
    intro s hs
    have hMsg : ((ρ s : GL ι K) : Matrix ι ι K) *
        ((ρ g : GL ι K) : Matrix ι ι K) = ((ρ (s * g) : GL ι K) : Matrix ι ι K) := by
      rw [← Units.val_mul, ← map_mul]
    have h1 : s * g = g * (g⁻¹ * s * g) := by group
    rw [Matrix.mulVec_mulVec, hMsg, h1, map_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, hconj s hs]
  exact (hS _).1 hfix

end Generic

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC

end
