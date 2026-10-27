module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigAB
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigAD

public section

namespace CFSG.StandardType.QTwo

open CFSG.LinearAlgebra
open CFSG.LinearAlgebra.SteinbergBQ
open Module QuadraticMap
open TauCeti.QuadraticMap (orthogonalGroup)

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

private noncomputable def qtwoDB41E_phi {m : ℕ}
    (σ : Multiplicative (DVec m) →* (W ≃ₗ[ZMod 2] W)) :
    DVec m →+ Additive (W ≃ₗ[ZMod 2] W) where
  toFun u := Additive.ofMul (σ (Multiplicative.ofAdd u))
  map_zero' := by simp
  map_add' u v := by
    change Additive.ofMul (σ (Multiplicative.ofAdd u * Multiplicative.ofAdd v))
      = Additive.ofMul (σ (Multiplicative.ofAdd u))
        + Additive.ofMul (σ (Multiplicative.ofAdd v))
    rw [map_mul]
    rfl

private noncomputable def qtwoDB41E_H {m : ℕ}
    (σ : Multiplicative (DVec m) →* (W ≃ₗ[ZMod 2] W))
    (N : Subgroup (W ≃ₗ[ZMod 2] W)) : Submodule (ZMod 3) (DVec m) :=
  AddSubgroup.toZModSubmodule 3 (N.toAddSubgroup.comap (qtwoDB41E_phi σ))

@[simp] private lemma qtwoDB41E_mem_H {m : ℕ}
    (σ : Multiplicative (DVec m) →* (W ≃ₗ[ZMod 2] W))
    (N : Subgroup (W ≃ₗ[ZMod 2] W)) (u : DVec m) :
    u ∈ qtwoDB41E_H σ N ↔ σ (Multiplicative.ofAdd u) ∈ N := by
  rw [qtwoDB41E_H, AddSubgroup.mem_toZModSubmodule, AddSubgroup.mem_comap,
    Additive.mem_toAddSubgroup]
  rfl

private lemma qtwoDB41E_phi_range {m : ℕ}
    (σ : Multiplicative (DVec m) →* (W ≃ₗ[ZMod 2] W)) :
    (qtwoDB41E_phi σ).range = σ.range.toAddSubgroup := by
  ext x
  constructor
  · intro hx
    rw [AddMonoidHom.mem_range] at hx
    obtain ⟨u, rfl⟩ := hx
    rw [Additive.mem_toAddSubgroup]
    exact ⟨Multiplicative.ofAdd u, rfl⟩
  · intro hx
    rw [Additive.mem_toAddSubgroup] at hx
    obtain ⟨u, hu⟩ := hx
    rw [AddMonoidHom.mem_range]
    exact ⟨Multiplicative.toAdd u, by simp [qtwoDB41E_phi, hu]⟩

private lemma qtwoDB41E_relIndex_toAddSubgroup {G : Type*} [Group G]
    (H K : Subgroup G) :
    H.toAddSubgroup.relIndex K.toAddSubgroup = H.relIndex K := rfl

private lemma qtwoDB41E_finrank_H {m : ℕ} (hm : 1 ≤ m)
    (σ : Multiplicative (DVec m) →* (W ≃ₗ[ZMod 2] W))
    (N : Subgroup (W ≃ₗ[ZMod 2] W)) (hN : N ≤ σ.range)
    (hrel : N.relIndex σ.range = 3) (hcard : Nat.card σ.range = 3 ^ (m - 1)) :
    Module.finrank (ZMod 3) (qtwoDB41E_H σ N) = m - 1 := by
  haveI : Module.Finite (ZMod 3) (qtwoDB41E_H σ N) :=
    FiniteDimensional.finiteDimensional_submodule (qtwoDB41E_H σ N)
  have hindex : (N.toAddSubgroup.comap (qtwoDB41E_phi σ)).index = 3 := by
    rw [AddSubgroup.index_comap, qtwoDB41E_phi_range,
      qtwoDB41E_relIndex_toAddSubgroup, hrel]
  have hcardEq : Nat.card (qtwoDB41E_H σ N)
      = Nat.card (N.toAddSubgroup.comap (qtwoDB41E_phi σ)) := rfl
  have hcardH : Nat.card (qtwoDB41E_H σ N) = 3 ^ (m - 1) := by
    have h1 := AddSubgroup.card_mul_index (N.toAddSubgroup.comap (qtwoDB41E_phi σ))
    have hDVec : Nat.card (DVec m) = 3 ^ m := by
      simp [DVec, Nat.card_fun, Nat.card_zmod]
    have hp : 3 ^ m = 3 ^ (m - 1) * 3 := by
      conv_lhs => rw [show m = (m - 1) + 1 from by omega]
      rw [pow_succ]
    rw [← hcardEq, hindex, hDVec, hp] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have hpow : 3 ^ Module.finrank (ZMod 3) (qtwoDB41E_H σ N) = 3 ^ (m - 1) := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := qtwoDB41E_H σ N)
    rw [Nat.card_zmod, hcardH] at this
    exact this.symm
  exact Nat.pow_right_injective (by norm_num) hpow

private lemma qtwoDB41E_H_injOn {m : ℕ}
    (σ : Multiplicative (DVec m) →* (W ≃ₗ[ZMod 2] W)) :
    Set.InjOn (qtwoDB41E_H σ) {N | N ≤ σ.range} := by
  intro N hN N' hN' hEq
  have hEqAdd : N.toAddSubgroup.comap (qtwoDB41E_phi σ)
      = N'.toAddSubgroup.comap (qtwoDB41E_phi σ) := by
    have := congrArg Submodule.toAddSubgroup hEq
    simpa only [qtwoDB41E_H, AddSubgroup.toZModSubmodule_toAddSubgroup] using this
  have hmap : (N.toAddSubgroup.comap (qtwoDB41E_phi σ)).map (qtwoDB41E_phi σ)
      = N.toAddSubgroup :=
    AddSubgroup.map_comap_eq_self (f := qtwoDB41E_phi σ) (H := N.toAddSubgroup)
      (by rw [qtwoDB41E_phi_range]; exact hN)
  have hmap' : (N'.toAddSubgroup.comap (qtwoDB41E_phi σ)).map (qtwoDB41E_phi σ)
      = N'.toAddSubgroup :=
    AddSubgroup.map_comap_eq_self (f := qtwoDB41E_phi σ) (H := N'.toAddSubgroup)
      (by rw [qtwoDB41E_phi_range]; exact hN')
  apply Subgroup.toAddSubgroup.injective
  rw [← hmap, hEqAdd, hmap']

theorem qtwoDB41_generic_fixed_W {m : ℕ} (hm : 6 ≤ m) {c : Fin m}
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {q : QuadraticForm (ZMod 2) W} (hq : (QuadraticMap.polarBilin q).Nondegenerate)
    (hdim : Module.finrank (ZMod 2) W = 2 * (m - 1))
    (σ : Multiplicative (DVec m) →* (W ≃ₗ[ZMod 2] W))
    (hσO : σ.range ≤ TauCeti.QuadraticMap.orthogonalGroup q)
    (hσker : ∀ v : DVec m, σ (Multiplicative.ofAdd v) = 1 ↔ ∀ i, i ≠ c → v i = 0)
    (hfix : fixedSub σ.range = ⊥)
    (hW : ∀ w ∈ dEvenStab m (Pi.single c 1), ∃ n ∈ TauCeti.QuadraticMap.orthogonalGroup q,
      ∀ v : DVec m, n * σ (Multiplicative.ofAdd v) * n⁻¹ = σ (Multiplicative.ofAdd (w v))) :
    ∀ v : DVec m, (∀ i, i ≠ c → v i ≠ 0) →
      ∀ x : W, σ (Multiplicative.ofAdd v) x = x → x = 0 := by
  classical
  have hBcard : Nat.card σ.range = 3 ^ (m - 1) := by
    have hker : Nat.card σ.ker = 3 := by
      have hbij : Function.Bijective (fun x : ↥σ.ker => (x.1.toAdd) c) := by
        constructor
        · intro x y hxy
          apply Subtype.ext
          apply Multiplicative.toAdd.injective
          funext i
          by_cases hic : i = c
          · subst hic; exact hxy
          · have hx0 : (x.1.toAdd) i = 0 :=
              (hσker x.1.toAdd).1 (MonoidHom.mem_ker.mpr x.2) i hic
            have hy0 : (y.1.toAdd) i = 0 :=
              (hσker y.1.toAdd).1 (MonoidHom.mem_ker.mpr y.2) i hic
            rw [hx0, hy0]
        · intro a
          refine ⟨⟨Multiplicative.ofAdd (a • Pi.single c 1), ?_⟩, ?_⟩
          · rw [MonoidHom.mem_ker]
            exact (hσker (a • Pi.single c 1)).2 (fun i hi => by
              rw [Pi.smul_apply, Pi.single_eq_of_ne hi, smul_zero])
          · change (a • Pi.single c 1) c = a
            rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      have h1 := Nat.card_congr (Equiv.ofBijective _ hbij)
      simpa [Nat.card_zmod] using h1
    have hG : Nat.card (Multiplicative (DVec m)) = 3 ^ m := by
      have : Nat.card (Multiplicative (DVec m)) = Nat.card (DVec m) := rfl
      rw [this]
      simp [DVec, Nat.card_fun, Nat.card_zmod]
    have hp : 3 ^ m = 3 * 3 ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 from by omega]
      rw [pow_succ']
    have h2 := Subgroup.card_ker_mul_card_range σ
    rw [hker, hG, hp] at h2
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  letI : IsElementaryAbelian 3 σ.range := qtwoDB41_isElementaryAbelian_range σ
  obtain ⟨I, d, hI, ⟨hindep, hsup, horth⟩, hblocks, hsum, hinf, hrI, hIm, hI3, hm0, hr0,
    hplanes, hnorm, hAll, hmr⟩ :=
    binary_quadratic_three_action_canonical_kernel_blocks (m := m - 1) (r := m - 1)
      q hq hdim σ.range hσO hBcard hfix
  obtain ⟨hIcard, hd1, -, -⟩ := hmr rfl
  let I' : Finset (Submodule (ZMod 3) (DVec m)) := I.image (qtwoDB41E_H σ)
  have hHsingle : ∀ N, Pi.single c 1 ∈ qtwoDB41E_H σ N := by
    intro N
    rw [qtwoDB41E_mem_H]
    rw [(hσker (Pi.single c 1)).2 (fun i hi => by rw [Pi.single_eq_of_ne hi])]
    exact N.one_mem
  have hHfinrank : ∀ N ∈ I, Module.finrank (ZMod 3) (qtwoDB41E_H σ N) = m - 1 := by
    intro N hN
    obtain ⟨hNB, hrel, -⟩ := (hI N).1 hN
    exact qtwoDB41E_finrank_H (by omega : 1 ≤ m) σ N hNB hrel hBcard
  have hI' : ∀ J ∈ I', Pi.single c 1 ∈ J ∧ Module.finrank (ZMod 3) J = m - 1 := by
    intro J hJ
    rw [Finset.mem_image] at hJ
    obtain ⟨N, hN, rfl⟩ := hJ
    exact ⟨hHsingle N, hHfinrank N hN⟩
  have hI'card : I'.card = m - 1 := by
    have hinj : Set.InjOn (qtwoDB41E_H σ) (↑I : Set (Subgroup (W ≃ₗ[ZMod 2] W))) :=
      Set.InjOn.mono (fun N hN => ((hI N).1 hN).1) (qtwoDB41E_H_injOn σ)
    rw [Finset.card_image_of_injOn hinj, hIcard]
  have hI'inf : ∀ v : DVec m, (∀ J ∈ I', v ∈ J) → ∀ i, i ≠ c → v i = 0 := by
    intro v hvJ i hi
    have hmem : σ (Multiplicative.ofAdd v) ∈ ⨅ N ∈ I, N := by
      rw [Subgroup.mem_iInf]
      intro N
      rw [Subgroup.mem_iInf]
      intro hN
      exact (qtwoDB41E_mem_H σ N v).mp
        (hvJ (qtwoDB41E_H σ N) (Finset.mem_image.mpr ⟨N, hN, rfl⟩))
    have hbot : σ (Multiplicative.ofAdd v) ∈ (⊥ : Subgroup (W ≃ₗ[ZMod 2] W)) := by
      rw [← hinf]
      exact ⟨⟨Multiplicative.ofAdd v, rfl⟩, hmem⟩
    exact (hσker v).mp (Subgroup.mem_bot.mp hbot) i hi
  have hI'inv : ∀ w ∈ dEvenStab m (Pi.single c 1), ∀ J ∈ I',
      J.map (w : DVec m ≃ₗ[ZMod 3] DVec m).toLinearMap ∈ I' := by
    intro w hw J hJ
    rw [Finset.mem_image] at hJ ⊢
    obtain ⟨N, hN, rfl⟩ := hJ
    obtain ⟨n, hnO, hn⟩ := hW w hw
    have hconj_inv : ∀ u : DVec m,
        n⁻¹ * σ (Multiplicative.ofAdd u) * n = σ (Multiplicative.ofAdd (w.symm u)) := by
      intro u
      have h := hn (w.symm u)
      rw [LinearEquiv.apply_symm_apply] at h
      calc n⁻¹ * σ (Multiplicative.ofAdd u) * n
          = n⁻¹ * (n * σ (Multiplicative.ofAdd (w.symm u)) * n⁻¹) * n := by rw [h]
        _ = σ (Multiplicative.ofAdd (w.symm u)) := by group
    have hnN : n ∈ Subgroup.normalizer (σ.range : Set (W ≃ₗ[ZMod 2] W)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        obtain ⟨u, rfl⟩ := hg
        change n * σ (Multiplicative.ofAdd u.toAdd) * n⁻¹ ∈ σ.range
        rw [hn u.toAdd]
        exact ⟨Multiplicative.ofAdd (w u.toAdd), rfl⟩
      · intro hg
        obtain ⟨u, hu⟩ := hg
        refine ⟨Multiplicative.ofAdd (w.symm u.toAdd), ?_⟩
        have h1 : σ (Multiplicative.ofAdd u.toAdd) = n * g * n⁻¹ := by
          rw [show Multiplicative.ofAdd u.toAdd = u from rfl]
          exact hu
        rw [← hconj_inv u.toAdd, h1]
        group
    refine ⟨N.map (MulAut.conj n).toMonoidHom, (hnorm n hnO hnN).1.mapsTo hN, ?_⟩
    ext u
    simp only [Submodule.mem_map_equiv, qtwoDB41E_mem_H, KernelBlockHyp.mem_map_conj_iff,
      hconj_inv u]
  have hcoord := qtwoDB41_coord_hyperplanes hm I' hI' hI'card hI'inf hI'inv
  intro v hv x hx
  let A : Subgroup (W ≃ₗ[ZMod 2] W) := Subgroup.zpowers (σ (Multiplicative.ofAdd v))
  have hAB : A ≤ σ.range :=
    Subgroup.zpowers_le.mpr ⟨Multiplicative.ofAdd v, rfl⟩
  have hnotA : ∀ N ∈ I, ¬ A ≤ N := by
    intro N hN hle
    have hgN : σ (Multiplicative.ofAdd v) ∈ N := hle (Subgroup.mem_zpowers _)
    obtain ⟨i, hi, hiff⟩ := hcoord (qtwoDB41E_H σ N) (Finset.mem_image.mpr ⟨N, hN, rfl⟩)
    exact hv i hi ((hiff v).mp ((qtwoDB41E_mem_H σ N v).mpr hgN))
  have hfilter : I.filter (fun N => A ≤ N) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro N hN
    rw [Finset.mem_filter] at hN
    exact hnotA N hN.1 hN.2
  have hfixA : fixedSub A = ⊥ := by
    rw [(hAll A hAB).1, hfilter]
    simp
  have hxA : x ∈ fixedSub A := by
    rw [mem_fixedSub]
    intro μ hμ
    have hstab : A ≤ MulAction.stabilizer (W ≃ₗ[ZMod 2] W) x :=
      Subgroup.zpowers_le.mpr (by
        rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def]
        exact hx)
    have := hstab hμ
    rwa [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def] at this
  rw [hfixA] at hxA
  simpa using hxA

end CFSG.StandardType.QTwo

end
