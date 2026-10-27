module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.ReduceLine
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KGenProof

open CFSG.Quasithin Matrix
open scoped commutatorElement

theorem exists_A_of_perfect_prime_order {G : Type} [Group G] [Finite G] {P V : Subgroup G}
    {p : ℕ} (hp : p.Prime) (hVP : V ≤ P) (hV : ⁅V, V⁆ = V) {x : G} (hxV : x ∈ V)
    (hxp : x ^ p = 1) (hx1 : x ≠ 1) {w : G} (hwP : w ∉ P)
    (hwx : w * x * w⁻¹ ∈ Subgroup.zpowers x) :
    ∃ A : Subgroup G, A ≤ Hinf P ∧ Nat.card ↥A = p ∧
      ∃ w : G, w ∉ P ∧ ∀ a ∈ A, w * a * w⁻¹ ∈ A := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨Subgroup.zpowers x, ?_, ?_, w, hwP, ?_⟩
  · exact (Subgroup.zpowers_le.2 hxV).trans (uc22p21c_le_Hinf hVP hV)
  · rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
  · intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hwx k

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

@[expose] def GenLine (p : ℕ) (Γ : Subgroup (GL ι K)) (e₀ : ι → K) : Prop :=
  ∃ (V : Subgroup (GL ι K)) (x w : GL ι K),
    V ≤ Γ ∧ (∀ v ∈ V, ((v : GL ι K) : Matrix ι ι K) *ᵥ e₀ = e₀) ∧ ⁅V, V⁆ = V ∧
    x ∈ V ∧ x ^ p = 1 ∧ x ≠ 1 ∧ w ∈ Γ ∧
    (¬ ∃ c : K, ((w : GL ι K) : Matrix ι ι K) *ᵥ e₀ = c • e₀) ∧
    w * x * w⁻¹ ∈ Subgroup.zpowers x

theorem GenLine.exists_A {p : ℕ} (hp : p.Prime) {W : Type} [CommGroup W] [Finite W] [Finite K]
    {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)} (hreal : (FFModel.nat Γ).Realizes H ⊤ ⊥)
    {e₀ : ι → K} (hline : KTabC.SylowFixedLine Γ e₀) (hgen : GenLine p Γ e₀) (S : Sylow 2 ↥H) :
    ∃ A : Subgroup ↥H, A ≤ Hinf (KTabD.pointStab H S) ∧ Nat.card ↥A = p ∧
      ∃ w : ↥H, w ∉ KTabD.pointStab H S ∧ ∀ a ∈ A, w * a * w⁻¹ ∈ A := by
  obtain ⟨V, x, w, hVΓ, hVfix, hVperf, hxV, hxp, hx1, hwΓ, hwmove, hwx⟩ := hgen
  obtain ⟨φ, hφ⟩ := KTabD.exists_mulEquiv_pointStab_eq_map hreal hline S
  let x' : ↥Γ := ⟨x, hVΓ hxV⟩
  let w' : ↥Γ := ⟨w, hwΓ⟩
  let V' : Subgroup ↥Γ := V.subgroupOf Γ
  have hx'val : ((x' : ↥Γ) : GL ι K) = x := rfl
  have hw'val : ((w' : ↥Γ) : GL ι K) = w := rfl
  have hVP' : V' ≤ KTabD.lineStab Γ e₀ := by
    intro v hv
    exact ⟨1, by
      rw [hVfix ((v : ↥Γ) : GL ι K) (Subgroup.mem_subgroupOf.mp hv), one_smul]⟩
  have hV'map : V'.map Γ.subtype = V := by
    change (V.subgroupOf Γ).map Γ.subtype = V
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hVΓ]
  have hV' : ⁅V', V'⁆ = V' := by
    apply Subgroup.map_injective Γ.subtype_injective
    rw [Subgroup.map_commutator, hV'map, hVperf]
  have hxV' : x' ∈ V' := Subgroup.mem_subgroupOf.mpr hxV
  have hx'p : x' ^ p = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow, hx'val] using hxp
  have hx'1 : x' ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hw'P : w' ∉ KTabD.lineStab Γ e₀ := fun h => hwmove h
  have hwx' : w' * x' * w'⁻¹ ∈ Subgroup.zpowers x' := by
    rw [Subgroup.mem_zpowers_iff] at hwx ⊢
    obtain ⟨k, hk⟩ := hwx
    exact ⟨k, by
      apply Subtype.ext
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, hx'val, hw'val] using hk⟩
  obtain ⟨AΓ, hAΓ_le, hAΓ_card, w₂, hw₂_notin, hw₂_conj⟩ :=
    exists_A_of_perfect_prime_order hp hVP' hV' hxV' hx'p hx'1 hw'P hwx'
  let A : Subgroup ↥H := AΓ.map φ.toMonoidHom
  have hA_le : A ≤ Hinf (KTabD.pointStab H S) := by
    rw [hφ, ← Hinf_map φ.toMonoidHom (KTabD.lineStab Γ e₀)]
    exact Subgroup.map_mono hAΓ_le
  have hA_card : Nat.card ↥A = p := by
    change Nat.card ↥(AΓ.map φ.toMonoidHom) = p
    rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective, hAΓ_card]
  have hw_notin : φ w₂ ∉ KTabD.pointStab H S := by
    rw [hφ]
    intro h
    exact hw₂_notin ((Subgroup.mem_map_iff_mem (f := φ.toMonoidHom) φ.injective).mp h)
  refine ⟨A, hA_le, hA_card, φ w₂, hw_notin, ?_⟩
  intro a ha
  obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
  have hmem : φ (w₂ * a₀ * w₂⁻¹) ∈ A :=
    Subgroup.mem_map_of_mem φ.toMonoidHom (hw₂_conj a₀ ha₀)
  simpa [map_mul, map_inv] using hmem

end CFSG.LocalAnalysis.UniquenessCase.UC22.KGenProof

end
