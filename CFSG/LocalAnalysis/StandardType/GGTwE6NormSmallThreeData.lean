module

public import CFSG.LocalAnalysis.StandardType.GGTwE6NormSmallThreeTorus
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.TwE6NormThree

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups

section Plain

variable {G : Type*} [Group G]

private theorem conj_mul_mul_conj_inv (φ : MulAut G) (g : G) :
    MulAut.conj g * φ * (MulAut.conj g)⁻¹ = MulAut.conj (g * (φ g)⁻¹) * φ := by
  refine MulEquiv.ext fun x => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul, map_inv,
    mul_inv_rev, inv_inv, mul_assoc]

private theorem mul_conj_eq_of_apply_eq {φ : MulAut G} {g : G} (h : φ g = g) :
    φ * MulAut.conj g = MulAut.conj g * φ := by
  refine MulEquiv.ext fun x => ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, h]

private theorem exists_conj_eq_pow_mul {S : Set G} (hS : IsElemAbelian 3 (Subgroup.closure S))
    {c g : G} (hc : c ∈ Subgroup.closure S) (hgen : ∀ y ∈ S, ∃ k : ℕ, g * y * g⁻¹ = c ^ k * y)
    {y : G} (hy : y ∈ Subgroup.closure S) : ∃ k : ℕ, g * y * g⁻¹ = c ^ k * y := by
  induction hy using Subgroup.closure_induction with
  | mem y hy => exact hgen y hy
  | one => exact ⟨0, by simp⟩
  | mul y₁ y₂ hy₁ _ ih₁ ih₂ =>
    obtain ⟨k₁, h₁⟩ := ih₁
    obtain ⟨k₂, h₂⟩ := ih₂
    refine ⟨k₁ + k₂, ?_⟩
    have hc₂ : y₁ * c ^ k₂ = c ^ k₂ * y₁ := hS.comm hy₁ (pow_mem hc k₂)
    calc g * (y₁ * y₂) * g⁻¹ = g * y₁ * g⁻¹ * (g * y₂ * g⁻¹) := by group
      _ = c ^ k₁ * (y₁ * c ^ k₂ * y₂) := by rw [h₁, h₂]; simp only [mul_assoc]
      _ = c ^ (k₁ + k₂) * (y₁ * y₂) := by rw [hc₂, pow_add]; simp only [mul_assoc]
  | inv y hy ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨2 * k, ?_⟩
    have hinv : (c ^ k)⁻¹ = c ^ (2 * k) := inv_eq_of_mul_eq_one_right (by
      rw [← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, hS.2 c hc, one_pow])
    calc g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
      _ = c ^ (2 * k) * y⁻¹ := by
        rw [hk, mul_inv_rev, hinv]
        exact hS.comm (inv_mem hy) (pow_mem hc _)

end Plain


theorem exists_endNode_data_of_frame {R : Type} [Group R] {L : Type} [Field L] [CharP L 2]
    {X : Subgroup (MulAut R)} (hX : IsElemAbelian 3 X) {J : Subgroup R}
    {emb : R →* ModGL TwistTag.E6.tag L} (hemb : Function.Injective emb) {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ 3) {α : Fin TwistTag.E6.tag.rank → ℤ} (hα : IsRoot TwistTag.E6.tag α)
    {Ψ : Set (Fin TwistTag.E6.tag.rank → ℤ)} (hΨ : ∀ γ ∈ Ψ, IsRoot TwistTag.E6.tag γ)
    (hr : ∀ γ, IsRoot TwistTag.E6.tag γ → ∃ r, emb r = rootSL2 TwistTag.E6.tag L γ WSL)
    (hs : ∀ γ ∈ Ψ, ∃ s ∈ J, emb s = rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ))
    (hXd : ∀ φ ∈ X, ∃ c : Fin TwistTag.E6.tag.rank → Lˣ, (∀ k, c k ^ 3 = 1) ∧ rootChar c α = 1 ∧
      ∀ r, emb (φ r) = rootDiagUnit TwistTag.E6.tag c * emb r * (rootDiagUnit TwistTag.E6.tag c)⁻¹)
    (hcount : ∀ (H : Subgroup R) (u : R),
      (∀ γ ∈ Ψ, ∃ h ∈ H, rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple γ ζ) = emb h) →
      (∀ h ∈ H, ∀ c, rootDiagUnit TwistTag.E6.tag c = emb h → rootChar c α = 1 →
        u * h = h * u) →
      3 ^ 3 ≤ Nat.card ↥(H ⊓ Subgroup.centralizer {u})) :
    ∃ (Y : Subgroup (MulAut R)) (ι : Type) (r s : ι → R) (u : R) (F : Subgroup R),
      IsElemAbelian 3 Y ∧ X ≤ Y ∧ (∀ i, MulAut.conj (s i) ∈ Y) ∧
      (∀ i, ∀ y ∈ Y, ∃ k : ℕ,
        MulAut.conj (r i) * y * (MulAut.conj (r i))⁻¹ = MulAut.conj (s i) ^ k * y) ∧
      (∀ i, r i * s i * (r i)⁻¹ = (s i)⁻¹) ∧
      u * u = 1 ∧ u ≠ 1 ∧ (∀ φ ∈ X, φ u = u) ∧
      F ≤ Subgroup.closure (Set.range s) ∧ F ≤ J ∧
      (∀ f ∈ F, f * u = u * f) ∧ 3 ^ 3 ≤ Nat.card F := by
  have hd : ∀ a b : Fin TwistTag.E6.tag.rank → Lˣ,
      Commute (rootDiagUnit TwistTag.E6.tag a) (rootDiagUnit TwistTag.E6.tag b) := fun a b => by
    rw [Commute, SemiconjBy, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  have hd3 : ∀ c : Fin TwistTag.E6.tag.rank → Lˣ, (∀ k, c k ^ 3 = 1) →
      rootDiagUnit TwistTag.E6.tag c ^ 3 = 1 := fun c hc => by
    rw [rootDiagUnit_pow, show c ^ 3 = 1 from funext hc, rootDiagUnit_one]
  have hχ3 : ∀ c : Fin TwistTag.E6.tag.rank → Lˣ, (∀ k, c k ^ 3 = 1) →
      ∀ γ, rootChar c γ ^ 3 = 1 := fun c hc γ => by
    rw [← rootChar_pow, show c ^ 3 = 1 from funext hc]
    simp [rootChar]
  have hζ3 : ∀ γ k, TwE6RootAs.corootTuple γ ζ k ^ 3 = 1 := fun γ k => by
    rw [show TwE6RootAs.corootTuple γ ζ k = ζ ^ (∑ l, TwistTag.E6.tag.cartan k l * γ l) from rfl,
      ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
  have hnα : ∀ c, rootChar c α = 1 → rootSL2 TwistTag.E6.tag L α WSL *
      rootDiagUnit TwistTag.E6.tag c =
        rootDiagUnit TwistTag.E6.tag c * rootSL2 TwistTag.E6.tag L α WSL := fun c hc => by
    have h := rootSL2_WSL_conj_rootDiagUnit hα c
    rw [hc, show TwE6RootAs.corootTuple α (1 : Lˣ) = 1 from funext fun k => one_zpow _,
      rootDiagUnit_one, inv_one, mul_one] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  choose s hsJ hse using hs
  choose r hre using hr
  have hss : ∀ γ δ : ↥Ψ, s γ.1 γ.2 * s δ.1 δ.2 = s δ.1 δ.2 * s γ.1 γ.2 := fun γ δ =>
    hemb (by rw [map_mul, map_mul, hse γ.1 γ.2, hse δ.1 δ.2]; exact (hd _ _).eq)
  have hs3 : ∀ γ : ↥Ψ, s γ.1 γ.2 ^ 3 = 1 := fun γ =>
    hemb (by rw [map_pow, hse, hd3 _ (hζ3 γ.1), map_one])
  have hXs : ∀ φ ∈ X, ∀ γ : ↥Ψ, φ (s γ.1 γ.2) = s γ.1 γ.2 := fun φ hφ γ => by
    obtain ⟨c, -, -, hc⟩ := hXd φ hφ
    exact hemb (by rw [hc, hse, (hd c _).eq, mul_inv_cancel_right])
  have hrs : ∀ γ : ↥Ψ, r γ.1 (hΨ γ.1 γ.2) * s γ.1 γ.2 * (r γ.1 (hΨ γ.1 γ.2))⁻¹ =
      (s γ.1 γ.2)⁻¹ := fun γ => hemb (by
    rw [map_mul, map_mul, map_inv, map_inv, hre, hse, rootSL2_WSL_conj_corootTuple (hΨ γ.1 γ.2)])
  have hrX : ∀ γ : ↥Ψ, ∀ φ ∈ X, ∃ k : ℕ,
      r γ.1 (hΨ γ.1 γ.2) * (φ (r γ.1 (hΨ γ.1 γ.2)))⁻¹ = s γ.1 γ.2 ^ k := fun γ φ hφ => by
    obtain ⟨c, hc3, -, hc⟩ := hXd φ hφ
    obtain ⟨k, hk⟩ := exists_corootTuple_inv_eq_pow hζ γ.1 (hχ3 c hc3 γ.1)
    refine ⟨k, hemb ?_⟩
    rw [map_pow, hse, ← hk, map_mul, map_inv, hc, hre,
      show ∀ n d : ModGL TwistTag.E6.tag L, n * (d * n * d⁻¹)⁻¹ = n * d * n⁻¹ * d⁻¹ from
        fun n d => by group, rootSL2_WSL_conj_rootDiagUnit (hΨ γ.1 γ.2) c,
      (hd c _).inv_right.eq, mul_inv_cancel_right]
  have hrΨ : ∀ γ δ : ↥Ψ, ∃ k : ℕ, r γ.1 (hΨ γ.1 γ.2) * s δ.1 δ.2 * (r γ.1 (hΨ γ.1 γ.2))⁻¹ =
      s γ.1 γ.2 ^ k * s δ.1 δ.2 := fun γ δ => by
    obtain ⟨k, hk⟩ := exists_corootTuple_inv_eq_pow hζ γ.1 (hχ3 _ (hζ3 δ.1) γ.1)
    refine ⟨k, hemb ?_⟩
    rw [map_mul, map_mul, map_inv, map_mul, map_pow, hre, hse δ.1 δ.2, hse γ.1 γ.2,
      rootSL2_WSL_conj_rootDiagUnit (hΨ γ.1 γ.2), hk, ((hd _ _).pow_right k).eq]
  have hu2 : r α hα * r α hα = 1 :=
    hemb (by rw [map_mul, hre, LangRat.rootSL2_WSL_mul_self, map_one])
  have huX : ∀ φ ∈ X, φ (r α hα) = r α hα := fun φ hφ => by
    obtain ⟨c, -, hcα, hc⟩ := hXd φ hφ
    exact hemb (by rw [hc, hre, ← hnα c hcα, mul_inv_cancel_right])
  have hu1 : r α hα ≠ 1 := fun h1 => by
    have h := rootSL2_WSL_conj_corootTuple hα ζ
    rw [← hre α hα, h1, map_one, one_mul, inv_one, mul_one] at h
    have hh : rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple α ζ) = 1 := by
      calc _ = rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple α ζ) *
            (rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple α ζ) *
              rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple α ζ)) := by
            rw [mul_eq_one_iff_eq_inv.2 h, mul_one]
        _ = 1 := by rw [← pow_three]; exact hd3 _ (hζ3 α)
    have h2 := TwE6RootKill.rootChar_corootTuple α α ζ
    rw [CFSG.LieType.Chevalley.rootDiagUnit_injective (hh.trans rootDiagUnit_one.symm),
      SimplyLacedCover.iform_self_eq_two (τ := TwistTag.E6.tag) (fun i => Matrix.one_apply_eq i)
        hα] at h2
    have h3 := (hζ.zpow_eq_one_iff_dvd 2).1 (h2.symm.trans (by simp [rootChar]))
    norm_num at h3
  set S : Set (MulAut R) := (X : Set (MulAut R)) ∪ Set.range fun γ : ↥Ψ => MulAut.conj (s γ.1 γ.2)
  have hY : IsElemAbelian 3 (Subgroup.closure S) := by
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · rintro a (ha | ⟨γ, rfl⟩) b (hb | ⟨δ, rfl⟩)
      · exact hX.comm ha hb
      · exact mul_conj_eq_of_apply_eq (hXs a ha δ)
      · exact (mul_conj_eq_of_apply_eq (hXs b hb γ)).symm
      · rw [← map_mul, ← map_mul, hss γ δ]
    · rintro a (ha | ⟨γ, rfl⟩)
      · exact hX.2 a ha
      · rw [← map_pow, hs3, map_one]
  have hrY : ∀ γ : ↥Ψ, ∀ y ∈ Subgroup.closure S, ∃ k : ℕ, MulAut.conj (r γ.1 (hΨ γ.1 γ.2)) * y *
      (MulAut.conj (r γ.1 (hΨ γ.1 γ.2)))⁻¹ = MulAut.conj (s γ.1 γ.2) ^ k * y := fun γ y hy => by
    refine exists_conj_eq_pow_mul hY (Subgroup.subset_closure (Or.inr ⟨γ, rfl⟩)) ?_ hy
    rintro _ (hφ | ⟨δ, rfl⟩)
    · obtain ⟨k, hk⟩ := hrX γ _ hφ
      exact ⟨k, by rw [conj_mul_mul_conj_inv, hk, map_pow]⟩
    · obtain ⟨k, hk⟩ := hrΨ γ δ
      exact ⟨k, by rw [← map_inv, ← map_mul, ← map_mul, hk, map_mul, map_pow]⟩
  have hFJ : Subgroup.closure (Set.range fun γ : ↥Ψ => s γ.1 γ.2) ≤ J :=
    (Subgroup.closure_le J).2 (Set.range_subset_iff.2 fun γ => hsJ γ.1 γ.2)
  refine ⟨Subgroup.closure S, ↥Ψ, fun γ => r γ.1 (hΨ γ.1 γ.2), fun γ => s γ.1 γ.2, r α hα,
    Subgroup.closure (Set.range fun γ : ↥Ψ => s γ.1 γ.2) ⊓ Subgroup.centralizer {r α hα}, hY,
    fun φ hφ => Subgroup.subset_closure (Or.inl hφ),
    fun γ => Subgroup.subset_closure (Or.inr ⟨γ, rfl⟩), hrY, hrs, hu2, hu1, huX, inf_le_left,
    inf_le_left.trans hFJ, fun f hf => Subgroup.mem_centralizer_singleton_iff.1 hf.2,
    hcount _ _ (fun γ hγ => ⟨s γ hγ, Subgroup.subset_closure ⟨⟨γ, hγ⟩, rfl⟩, (hse γ hγ).symm⟩)
      fun h _ c hc hcα => hemb ?_⟩
  rw [map_mul, map_mul, hre, ← hc]
  exact hnα c hcα

end CFSG.StandardType.TwE6NormThree

end
