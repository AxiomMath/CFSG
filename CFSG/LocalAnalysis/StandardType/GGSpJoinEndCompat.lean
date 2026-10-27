module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSpProofAut
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneConj
public import CFSG.LocalAnalysis.StandardType.GGSpJoinLeviPlane

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.Symplectic CFSG.Open CFSG.StandardType.SpJoin
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras

variable {F : Type} [Field F] [Finite F] [CharP F 2] {G : Type} [Group G]

private theorem isElemAbelian_zpowers_map {p : ℕ} (hp : p.Prime) {H N : Type} [Group H] [Group N]
    {g : H} (hg : g ^ p = 1) (hg1 : g ≠ 1) (f : H →* N) :
    IsElemAbelian p ((Subgroup.zpowers g).map f) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hmem : ∀ x ∈ (Subgroup.zpowers g).map f, x ^ p = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyord : orderOf y ∣ orderOf g := orderOf_dvd_of_mem_zpowers hy
    rw [orderOf_eq_prime hg hg1] at hyord
    rw [← map_pow, (orderOf_dvd_iff_pow_eq_one.mp hyord), map_one]
  refine ⟨?_, hmem⟩
  haveI : IsMulCommutative (Subgroup.zpowers g) := Subgroup.zpowers_isMulCommutative g
  exact Subgroup.map_isMulCommutative (Subgroup.zpowers g) f

theorem spEnd_exists_conj_mem_zpowers {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {g g₂ : SpecialLinearGroup (Fin 2) F} (hg : g ^ p = 1) (hg1 : g ≠ 1) (hg₂ : g₂ ^ p = 1)
    (hg₂1 : g₂ ≠ 1) : ∃ s : SpecialLinearGroup (Fin 2) F, s * g₂ * s⁻¹ ∈ Subgroup.zpowers g := by
  have h2 : (2 : F) = 0 := by simpa using CharP.cast_eq_zero F 2
  obtain ⟨ζ, _, hPlaneConj⟩ := exists_spPlaneConj (F := F) h2 hp hp2
  haveI : Fact p.Prime := ⟨hp⟩
  set E₁ : Subgroup (StatedSp 1 F) := (Subgroup.zpowers g).map (lam (0 : Fin 1)) with hE₁
  set E₂ : Subgroup (StatedSp 1 F) := (Subgroup.zpowers g₂).map (lam (0 : Fin 1)) with hE₂
  have hcard₁ : p ^ 1 ≤ Nat.card E₁ := by
    have h : Nat.card E₁ = p := by
      rw [hE₁, Subgroup.card_map_of_injective (lam_injective (0 : Fin 1)), Nat.card_zpowers,
        orderOf_eq_prime hg hg1]
    rw [h, pow_one]
  have hcard₂ : p ^ 1 ≤ Nat.card E₂ := by
    have h : Nat.card E₂ = p := by
      rw [hE₂, Subgroup.card_map_of_injective (lam_injective (0 : Fin 1)), Nat.card_zpowers,
        orderOf_eq_prime hg₂ hg₂1]
    rw [h, pow_one]
  obtain ⟨c₁, hc₁⟩ := hPlaneConj 1 E₁
    (isElemAbelian_zpowers_map hp hg hg1 (lam (0 : Fin 1))) hcard₁
  obtain ⟨c₂, hc₂⟩ := hPlaneConj 1 E₂
    (isElemAbelian_zpowers_map hp hg₂ hg₂1 (lam (0 : Fin 1))) hcard₂
  have hg₂mem : lam (0 : Fin 1) g₂ ∈ E₂ := by
    rw [hE₂, Subgroup.mem_map]
    exact ⟨g₂, Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩, rfl⟩
  have hz : c₂ * lam (0 : Fin 1) g₂ * c₂⁻¹ ∈ E₁.map (MulAut.conj c₁).toMonoidHom := by
    rw [hc₁, ← hc₂]
    exact ⟨lam (0 : Fin 1) g₂, hg₂mem, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
  obtain ⟨y, hyE₁, hy⟩ := Subgroup.mem_map.mp hz
  have hy' : c₁ * y * c₁⁻¹ = c₂ * lam (0 : Fin 1) g₂ * c₂⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hy
    exact hy
  have hconj_eq : c₁⁻¹ * c₂ * lam (0 : Fin 1) g₂ * (c₁⁻¹ * c₂)⁻¹ = y := by
    calc c₁⁻¹ * c₂ * lam (0 : Fin 1) g₂ * (c₁⁻¹ * c₂)⁻¹
        = c₁⁻¹ * (c₂ * lam (0 : Fin 1) g₂ * c₂⁻¹) * c₁ := by group
      _ = c₁⁻¹ * (c₁ * y * c₁⁻¹) * c₁ := by rw [hy']
      _ = y := by group
  obtain ⟨s, hs⟩ := lam_zero_surjective (F := F) (c₁⁻¹ * c₂)
  refine ⟨s, ?_⟩
  have hmemE₁ : lam (0 : Fin 1) (s * g₂ * s⁻¹) ∈ E₁ := by
    have heq : lam (0 : Fin 1) (s * g₂ * s⁻¹) = y := by
      rw [map_mul, map_mul, map_inv, hs]
      exact hconj_eq
    rw [heq]
    exact hyE₁
  rw [hE₁] at hmemE₁
  obtain ⟨y', hy'zp, hy'eq⟩ := Subgroup.mem_map.mp hmemE₁
  exact (lam_injective (0 : Fin 1)) hy'eq ▸ hy'zp

private theorem spIncl_map_ringEquiv {m n : ℕ} {K : Type} [Field K] (σ : Fin m → Fin n)
    (φ : K ≃+* K) : (spIncl (K := K) σ).map φ = spIncl (K := K) σ := by
  ext a b
  rw [Matrix.map_apply, spIncl_apply]
  by_cases h : a = Sum.map σ σ b <;> simp [h, map_one, map_zero]

private theorem spEmbedMat_map_ringEquiv {m n : ℕ} {K : Type} [Field K] (σ : Fin m → Fin n)
    (φ : K ≃+* K) (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :
    (spEmbedMat σ g).map φ = spEmbedMat σ (g.map φ) := by
  simp only [spEmbedMat, Matrix.map_add φ (map_add φ), Matrix.map_mul,
    Matrix.map_sub φ (map_sub φ), Matrix.map_one φ (map_zero φ) (map_one φ),
    Matrix.transpose_map, spIncl_map_ringEquiv]

private theorem fieldSp_spLeviBlock {m : ℕ} (σ : F ≃+* F) (h : StatedSp m F) :
    fieldSp (m + 1) F σ (spLeviBlock m F h) = spLeviBlock m F (fieldSp m F σ h) := by
  apply mat_injective
  have hL : mat (m + 1) F (fieldSp (m + 1) F σ (spLeviBlock m F h))
      = (spEmbedMat (Fin.succ : Fin m → Fin (m + 1)) (mat m F h)).map σ := by
    rw [show mat (m + 1) F (fieldSp (m + 1) F σ (spLeviBlock m F h)) =
        (mat (m + 1) F (spLeviBlock m F h)).map σ from rfl]
    rw [spLeviBlock, mat_spEmbed]
  rw [hL, spEmbedMat_map_ringEquiv]
  rw [spLeviBlock, mat_spEmbed]
  exact congrArg (spEmbedMat (Fin.succ : Fin m → Fin (m + 1))) (coe_fieldSp σ h).symm

theorem spEnd_exists_compat_lift {m : ℕ} (hm : 3 ≤ m) (φ₁ φ₂ : StatedSp (m + 1) F →* G)
    (hφ₁ : Function.Injective φ₁) (hφ₂ : Function.Injective φ₂)
    (hJ : (φ₁.comp (spLeviBlock m F)).range = (φ₂.comp (spLeviBlock m F)).range) :
    ∃ φ : StatedSp (m + 1) F →* G, Function.Injective φ ∧ φ.range = φ₂.range ∧
      ∀ h : StatedSp m F, φ (spLeviBlock m F h) = φ₁ (spLeviBlock m F h) := by
  let β := CFSG.StandardType.spLeviBlock m F
  have hβ : Function.Injective β := CFSG.StandardType.spLeviBlock_injective
  have hφ₁β : Function.Injective (φ₁.comp β) := hφ₁.comp hβ
  have hφ₂β : Function.Injective (φ₂.comp β) := hφ₂.comp hβ
  let e₁ : StatedSp m F ≃* (φ₁.comp β).range := MonoidHom.ofInjective hφ₁β
  let e₂ : StatedSp m F ≃* (φ₂.comp β).range := MonoidHom.ofInjective hφ₂β
  let γ : MulAut (StatedSp m F) := (e₁.trans (MulEquiv.subgroupCongr hJ)).trans e₂.symm
  have hγ : ∀ h, φ₂ (β (γ h)) = φ₁ (β h) := fun h => by
    have h1 : (e₂ (γ h) : G) = φ₂ (β (γ h)) := MonoidHom.ofInjective_apply hφ₂β
    have h2 : e₂ (γ h) = MulEquiv.subgroupCongr hJ (e₁ h) := MulEquiv.apply_symm_apply e₂ _
    have h3 : (e₁ h : G) = φ₁ (β h) := MonoidHom.ofInjective_apply hφ₁β
    rw [← h1, h2, ← h3]
    rfl
  obtain ⟨B, σ, hBγ⟩ := exists_spConj_fieldSp_of_mulAut hm γ
  let B' : StatedSp (m + 1) F := β B
  let ρAut : MulAut (StatedSp (m + 1) F) := MulAut.conj B' * fieldSp (m + 1) F σ
  refine ⟨φ₂.comp ρAut.toMonoidHom, hφ₂.comp ρAut.injective, ?_, ?_⟩
  · have htop : ρAut.toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top.mpr ρAut.surjective
    rw [MonoidHom.range_comp, htop, Subgroup.map_top]
  · intro h
    change φ₂ (ρAut (β h)) = φ₁ (β h)
    have hρ : ρAut (β h) = β (γ h) := by
      have happ : ρAut (β h) = B' * fieldSp (m + 1) F σ (β h) * B'⁻¹ := by
        change (MulAut.conj B') (fieldSp (m + 1) F σ (β h)) = _
        rw [MulAut.conj_apply]
      rw [happ, fieldSp_spLeviBlock σ h]
      show B' * β (fieldSp m F σ h) * B'⁻¹ = β (γ h)
      rw [hBγ h, map_mul, map_mul, map_inv]
    rw [hρ, hγ h]

theorem spEnd_exists_plane_zero_correction {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (φ : StatedSp (m + 1) F →* G) (hφ : Function.Injective φ) {g g₂ : SpecialLinearGroup (Fin 2) F}
    (hg : g ^ p = 1) (hg1 : g ≠ 1) (hg₂ : g₂ ^ p = 1) (hg₂1 : g₂ ≠ 1) :
    ∃ φ' : StatedSp (m + 1) F →* G, Function.Injective φ' ∧ φ'.range = φ.range ∧
      (∀ h : StatedSp m F, φ' (spLeviBlock m F h) = φ (spLeviBlock m F h)) ∧
      ∃ k : ℕ, φ (lam (0 : Fin (m + 1)) g₂) = φ' (lam (0 : Fin (m + 1)) (g ^ k)) := by
  obtain ⟨s, hs⟩ := spEnd_exists_conj_mem_zpowers hp hp2 hg hg1 hg₂ hg₂1
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hs
  have hpZne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hgZ : g ^ (p : ℤ) = 1 := by rw [zpow_natCast]; exact hg
  have hmod : g ^ j = g ^ (j % (p : ℤ)) := zpow_eq_zpow_emod j hgZ
  have hem : g ^ (j % (p : ℤ)) = s * g₂ * s⁻¹ := by rw [← hmod]; exact hj
  let k : ℕ := (j % (p : ℤ)).toNat
  have hkg : g ^ k = s * g₂ * s⁻¹ := by
    have hcast : (k : ℤ) = j % (p : ℤ) := by
      dsimp [k]
      exact Int.toNat_of_nonneg (Int.emod_nonneg j hpZne)
    rw [← zpow_natCast g k, hcast]
    exact hem
  have hgk : s⁻¹ * g ^ k * s = g₂ := by
    rw [hkg]; group
  let ρAut : MulAut (StatedSp (m + 1) F) := MulAut.conj (lam (0 : Fin (m + 1)) s⁻¹)
  have hρ_apply : ∀ w, ρAut w =
      lam (0 : Fin (m + 1)) s⁻¹ * w * (lam (0 : Fin (m + 1)) s⁻¹)⁻¹ := by
    intro w
    change (MulAut.conj (lam (0 : Fin (m + 1)) s⁻¹)) w = _
    rw [MulAut.conj_apply]
  refine ⟨φ.comp ρAut.toMonoidHom, hφ.comp ρAut.injective, ?_, ?_, k, ?_⟩
  · have htop : ρAut.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr ρAut.surjective
    rw [MonoidHom.range_comp, htop, Subgroup.map_top]
  · intro h
    change φ (ρAut (spLeviBlock m F h)) = φ (spLeviBlock m F h)
    have hfix : ρAut (spLeviBlock m F h) = spLeviBlock m F h := by
      rw [hρ_apply, map_inv, inv_inv]
      have hcomm : Commute (lam (0 : Fin (m + 1)) s) (spLeviBlock m F h) :=
        lam_zero_commute_spLeviBlock s h
      rw [hcomm.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
    exact congrArg φ hfix
  · have hρval : ρAut (lam (0 : Fin (m + 1)) (g ^ k)) = lam (0 : Fin (m + 1)) g₂ := by
      rw [hρ_apply, map_inv, inv_inv, ← map_inv, ← map_mul, ← map_mul, hgk]
    change φ (lam (0 : Fin (m + 1)) g₂) =
      φ (ρAut (lam (0 : Fin (m + 1)) (g ^ k)))
    exact (congrArg φ hρval).symm

end CFSG.StandardType
