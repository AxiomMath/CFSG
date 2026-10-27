module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpTorusAutBasic
import CFSG.LocalAnalysis.StandardType.GGQ2PlaneChainGroups
import CFSG.LocalAnalysis.StandardType.GGQ2SignedPermPair
import CFSG.LocalAnalysis.StandardType.GGQ2SpPairSign
import CFSG.LocalAnalysis.StandardType.GGQ2SpTorusAutAmb
import CFSG.LocalAnalysis.StandardType.GGQ2SpTorusAutZeroFacts

public section

namespace CFSG.StandardType.GGQ2Frame.SpBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K]

theorem mem_signedPermGroupOn_of_mem_torusAut [CharP K 2]
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {S : Finset (Fin m)} {X : Subgroup ↥(StatedSp m K)} (hX : X ≤ levi m S)
    {φ : PlaneRaw.V m ≃ₗ[ZMod 3] PlaneRaw.V m} (hφ : φ ∈ torusAut ζ m X) :
    φ ∈ PlaneRaw.signedPermGroupOn m S := by
  obtain ⟨π, ε, hε, hφπ⟩ := exists_signedPerm_of_mem_torusAut hζ hφ
  obtain ⟨y, hy, hyφ⟩ := hφ
  have hfix : ∀ k ∉ S, φ (Pi.single k 1) = Pi.single k 1 := by
    intro k hk
    have hu : ∀ i ∈ S, (Pi.single k 1 : PlaneRaw.V m) i = 0 := by
      intro i hi
      have hik : i ≠ k := fun h => hk (h ▸ hi)
      simp [hik]
    refine tau_injective hζ m ?_
    rw [← hyφ, ← commute_tau_of_mem_levi (ζ := ζ) hu (hX hy), mul_inv_cancel_right]
  have hkey : ∀ k ∉ S, π k = k ∧ ε k = 1 := by
    intro k hk
    have h := hφπ (Pi.single k 1) k
    rw [hfix k hk, Pi.single_eq_same, mul_one, Pi.single_apply] at h
    by_cases hπk : π k = k
    · rw [if_pos hπk] at h
      exact ⟨hπk, h.symm⟩
    · rw [if_neg hπk] at h
      rcases hε k with h1 | h1 <;> rw [h1] at h <;> exact absurd h (by decide)
  exact PlaneRaw.mem_signedPermGroupOn_of_apply S φ π ε hε (fun k hk => (hkey k hk).1)
    (fun k hk => (hkey k hk).2) hφπ

theorem torusAut_ycode_zero_of_three_le [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {S : Finset (Fin m)} (hS : 3 ≤ S.card) :
    torusAut ζ m (Ycode ζ m (.zero S)) = (PlaneRaw.signedPermGroupOn m S : Set _) := by
  rw [ycode_zero_eq_levi hK hζ hS]
  refine Set.Subset.antisymm ?_ ?_
  · intro φ hφ
    exact mem_signedPermGroupOn_of_mem_torusAut hζ le_rfl hφ
  · intro φ hφ
    refine closure_subset_torusAut ζ m (X := levi m S) ?_ hφ
    intro ψ hψ
    rcases hψ with ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩
    · by_cases hab : a = b
      · subst b
        rw [PlaneRaw.swapEquiv_self]
        exact one_mem_torusAut ζ m (levi m S)
      · exact swapEquiv_mem_torusAut hK hζ hab (rho_mem_levi ha hb hab sl2W)
    · exact negEquiv_mem_torusAut hK hζ (lam_mem_levi ha sl2W)

theorem torusAut_ycode_zero_pair [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    torusAut ζ m (Ycode ζ m (.zero {i, j})) =
      (Subgroup.zpowers (PlaneRaw.rotEquiv m i j) : Set _) := by
  have hYle : Ycode ζ m (.zero {i, j}) ≤ levi m {i, j} :=
    Subgroup.commutator_le_self (levi m {i, j})
  have hr : PlaneRaw.rotEquiv m i j ∈ torusAut ζ m (Ycode ζ m (.zero {i, j})) := by
    refine ⟨rho i j hij sl2W * lam j sl2W, rho_mul_lam_mem_ycode_pair hK ζ hij, fun u => ?_⟩
    rw [PlaneRaw.rotEquiv, LinearEquiv.mul_apply]
    calc rho i j hij sl2W * lam j sl2W * tau ζ m u * (rho i j hij sl2W * lam j sl2W)⁻¹
        = rho i j hij sl2W * (lam j sl2W * tau ζ m u * (lam j sl2W)⁻¹) *
            (rho i j hij sl2W)⁻¹ := by group
      _ = rho i j hij sl2W * tau ζ m (PlaneRaw.negEquiv m j u) *
            (rho i j hij sl2W)⁻¹ := by rw [lam_sl2W_conj_tau hK hζ j u]
      _ = tau ζ m (PlaneRaw.swapEquiv m i j (PlaneRaw.negEquiv m j u)) :=
          rho_sl2W_conj_tau hK hζ hij _
  have hzp : ((Subgroup.zpowers (PlaneRaw.rotEquiv m i j) : Subgroup _) : Set _) ⊆
      torusAut ζ m (Ycode ζ m (.zero {i, j})) := by
    have h := closure_subset_torusAut ζ m (X := Ycode ζ m (.zero {i, j}))
      (T := {PlaneRaw.rotEquiv m i j}) (by
        intro ψ hψ
        rw [Set.mem_singleton_iff] at hψ
        rwa [hψ])
    simpa [Subgroup.zpowers_eq_closure] using h
  refine Set.Subset.antisymm ?_ hzp
  intro φ hφ
  obtain ⟨y, hy, hyφ⟩ := hφ
  have hφsigned : φ ∈ PlaneRaw.signedPermGroupOn m {i, j} :=
    mem_signedPermGroupOn_of_mem_torusAut hζ hYle ⟨y, hy, hyφ⟩
  rcases PlaneRaw.mem_zpowers_rotEquiv_or_of_mem (t := m) (i := i) (j := j) hφsigned with
    hφr | hψr
  · exact hφr
  · exfalso
    set ψ : PlaneRaw.V m ≃ₗ[ZMod 3] PlaneRaw.V m := φ * PlaneRaw.negEquiv m j with hψdef
    have hψr' : ψ ∈ Subgroup.zpowers (PlaneRaw.rotEquiv m i j) := by
      rw [hψdef]
      exact hψr
    have hψaut : ψ ∈ torusAut ζ m (Ycode ζ m (.zero {i, j})) := hzp hψr'
    obtain ⟨z, hz, hzψ⟩ := hψaut
    have hylevi : y ∈ levi m {i, j} := hYle hy
    have hlamlevi : (lam (k := K) j sl2W : ↥(StatedSp m K)) ∈ levi m {i, j} :=
      lam_mem_levi (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))
        (sl2W : SpecialLinearGroup (Fin 2) K)
    set y' : ↥(StatedSp m K) := y * lam j sl2W with hy'def
    have hy'ψ : ∀ u, y' * tau ζ m u * y'⁻¹ = tau ζ m (ψ u) := by
      intro u
      rw [hy'def, hψdef, LinearEquiv.mul_apply]
      calc y * lam j sl2W * tau ζ m u * (y * lam j sl2W)⁻¹
          = y * (lam j sl2W * tau ζ m u * (lam j sl2W)⁻¹) * y⁻¹ := by group
        _ = y * tau ζ m (PlaneRaw.negEquiv m j u) * y⁻¹ := by
            rw [lam_sl2W_conj_tau hK hζ j u]
        _ = tau ζ m (φ (PlaneRaw.negEquiv m j u)) := hyφ _
    have hy'levi : y' ∈ levi m {i, j} := by
      rw [hy'def]
      exact Subgroup.mul_mem _ hylevi hlamlevi
    set c : ↥(StatedSp m K) := z⁻¹ * y' with hcdef
    have hc_mem : c ∈ levi m {i, j} := by
      rw [hcdef]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hYle hz)) hy'levi
    have hc_comm : ∀ u, c * tau ζ m u = tau ζ m u * c := by
      intro u
      rw [hcdef]
      have h1 : y' * tau ζ m u = tau ζ m (ψ u) * y' := by
        rw [← hy'ψ u]
        group
      have h2 : z⁻¹ * tau ζ m (ψ u) = tau ζ m u * z⁻¹ := by
        calc z⁻¹ * tau ζ m (ψ u) = z⁻¹ * (z * tau ζ m u * z⁻¹) := by rw [hzψ u]
          _ = tau ζ m u * z⁻¹ := by group
      calc z⁻¹ * y' * tau ζ m u = z⁻¹ * (y' * tau ζ m u) := by group
        _ = z⁻¹ * (tau ζ m (ψ u) * y') := by rw [h1]
        _ = (z⁻¹ * tau ζ m (ψ u)) * y' := by group
        _ = (tau ζ m u * z⁻¹) * y' := by rw [h2]
        _ = tau ζ m u * (z⁻¹ * y') := by group
    obtain ⟨u₀, hu₀⟩ := exists_tau_eq_of_commute hK hζ hc_comm
    have hu₀levi : tau ζ m u₀ ∈ levi m {i, j} := hu₀ ▸ hc_mem
    have hu₀zero : ∀ k, k ∉ ({i, j} : Finset (Fin m)) → u₀ k = 0 :=
      eq_zero_of_tau_mem_levi hK hζ hu₀levi
    have hcY : c ∈ Ycode ζ m (.zero {i, j}) := by
      rw [hu₀]
      exact tau_mem_ycode_zero hK hζ hu₀zero
    have hy'Y : y' ∈ Ycode ζ m (.zero {i, j}) := by
      have hy'eq : y' = z * c := by
        rw [hcdef, hy'def]
        group
      rw [hy'eq]
      exact Subgroup.mul_mem _ hz hcY
    have hlamY : lam j sl2W ∈ Ycode ζ m (.zero {i, j}) := by
      have hyinv : y⁻¹ * y' = lam j sl2W := by
        rw [hy'def]
        group
      rw [← hyinv]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hy) hy'Y
    exact lam_not_mem_ycode_pair hK ζ hij hlamY

theorem spZeroTorusAut_holds : SpZeroTorusAut := by
  intro K _ _ _ ζ m hK hζ S hS
  rcases Nat.eq_or_lt_of_le hS with hcard | hgt
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard.symm
    rw [PlaneRaw.normalizerOf_symplectic_pair m hab]
    exact torusAut_ycode_zero_pair hK hζ hab
  · have h3 : 3 ≤ S.card := hgt
    rw [torusAut_ycode_zero_of_three_le hK hζ h3]
    dsimp only [PlaneRaw.normalizerOf]
    rw [if_neg (by omega : S.card ≠ 2)]

end CFSG.StandardType.GGQ2Frame.SpBlocks
