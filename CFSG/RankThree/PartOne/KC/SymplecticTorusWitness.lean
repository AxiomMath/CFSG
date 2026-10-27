module

public import CFSG.RankThree.PartOne.KC.SymplecticTorusBlock
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks

public section

namespace CFSG.RankThree.PartOne.KCSymplectic

open Polynomial Module CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.CentralCover CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven CFSG.ClassicalGroups.Alternating
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

section Scalars

variable {r : ℕ} {K : Type} [Field K]

theorem exists_smul_of_proj_eq_one {g : StatedSp r K} (hg : proj r K g = 1) :
    ∃ c : K, ∀ v, spEnd g v = c • v := by
  have h1 : g ∈ SymplecticHigher.spScalars r K := by
    rw [← SymplecticHigher.ker_proj]
    exact hg
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h1
  obtain ⟨c, hc⟩ := h1
  refine ⟨c, fun v => ?_⟩
  rw [spEnd_apply, ← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext i
  simp [Matrix.mulVec_diagonal]

theorem eq_one_of_proj_eq_one_of_pow_eq_one {p : ℕ} [Finite K] (hr : 1 ≤ r) (hp2 : p ≠ 2)
    (hp : p.Prime) {g : StatedSp r K} (hg1 : proj r K g = 1) (hgp : g ^ p = 1) : g = 1 := by
  have hZc : (proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  have hZp : Nat.Coprime (Nat.card (proj r K).ker) p := by
    rw [SymplecticHigher.ker_proj, card_spScalars_eq_gcd K hr]
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left 2 _)
      ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  exact eq_of_map_eq_of_pow_eq_one_of_coprime (proj r K) hZc hZp (a := 1) (b := 0)
    (by simpa using hgp) (by simp) (by rw [hg1, map_one])

end Scalars

section Subtorus

variable {p : ℕ} [NeZero p]

@[expose] def coordHom {m : ℕ} (i : Fin m) :
    Multiplicative (Fin m → ZMod p) →* Multiplicative (ZMod p) :=
  AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ => ZMod p) i)

omit [NeZero p] in
theorem mem_ker_coordHom {m : ℕ} {i : Fin m} {a : Multiplicative (Fin m → ZMod p)} :
    a ∈ (coordHom (p := p) i).ker ↔ Multiplicative.toAdd a i = 0 := by
  rw [MonoidHom.mem_ker]
  change Multiplicative.ofAdd (Multiplicative.toAdd a i) = 1 ↔ _
  exact ⟨fun h => by simpa using congrArg Multiplicative.toAdd h, fun h => by rw [h]; rfl⟩

theorem card_ker_coordHom {m : ℕ} (i : Fin m) :
    Nat.card (coordHom (p := p) i).ker = p ^ (m - 1) := by
  classical
  have hsurj : Function.Surjective (coordHom (p := p) i) := by
    intro t
    refine ⟨Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd t)), ?_⟩
    apply Multiplicative.toAdd.injective
    change (Pi.single i (Multiplicative.toAdd t) : Fin m → ZMod p) i = Multiplicative.toAdd t
    rw [Pi.single_eq_same]
  have h1 := Subgroup.card_mul_index (coordHom (p := p) i).ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top,
    card_multiplicative_fin_zmod] at h1
  have h2 : Nat.card (Multiplicative (ZMod p)) = p := Nat.card_zmod p
  rw [h2] at h1
  have hm : 1 ≤ m := by
    rcases m with _ | m
    · exact i.elim0
    · omega
  have h3 : p ^ m = p ^ (m - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel hm]
  rw [h3] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (NeZero.ne p)) h1

end Subtorus

section Block

variable {r : ℕ} {K : Type} [Field K]

structure TorusBlock (x : StatedSp r K) (h : primaryFactors (spEnd x)) (p m : ℕ) where
  F : Subgroup (StatedSp r K)
  ψ : F →* (primaryComponent (spEnd x) (h : K[X]) ≃ₗ[AdjoinRoot (h : K[X])]
    primaryComponent (spEnd x) (h : K[X]))
  injective : Function.Injective ψ
  act : ∀ (g : F) (w : primaryComponent (spEnd x) (h : K[X])),
    ((ψ g w : primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K) =
      spEnd (g : StatedSp r K) (w : Fin r ⊕ Fin r → K)
  basis : Basis (Fin m) (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X]))
  lam : (AdjoinRoot (h : K[X]))ˣ
  lam_pow : lam ^ p = 1
  lam_order : orderOf lam = p
  diag : ∀ c : Fin m → (AdjoinRoot (h : K[X]))ˣ, (∀ j, c j ∈ Subgroup.zpowers lam) →
    diagEquiv basis c ∈ ψ.range
  perm : ∀ τ : Equiv.Perm (Fin m), permEquiv basis τ ∈ ψ.range
  sign : ∀ i : Fin m, signEquiv basis i ∈ ψ.range

variable {x : StatedSp r K} {h : primaryFactors (spEnd x)} {p m : ℕ}

theorem TorusBlock.spEnd_torusS_basis [NeZero p] (T : TorusBlock x h p m)
    (a : Multiplicative (Fin m → ZMod p)) (i : Fin m) (ha : Multiplicative.toAdd a i = 0) :
    spEnd (torusS T.basis T.lam T.lam_pow T.ψ T.injective T.diag a)
      ((T.basis i : primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K) =
      ((T.basis i : primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K) := by
  have h1 := T.act (torusF T.basis T.lam T.lam_pow T.ψ T.injective T.diag a) (T.basis i)
  rw [psi_torusF, diagEquiv_apply_basis, torusExps_apply, ha, ZMod.val_zero, pow_zero,
    Units.val_one, one_smul] at h1
  exact h1.symm

theorem TorusBlock.witness_odd (T : TorusBlock x h p m) [Finite K] {G : Type*} [Group G]
    [Finite G] (Y : Subgroup G) (φ : Y →* StatedProj (StatedSp r K))
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) (hp : p.Prime)
    (hp2 : p ≠ 2) (hr : 1 ≤ r) (h2 : (2 : K) ≠ 0) (hm : 2 ≤ m) :
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p A ∧ Nat.card A = p ^ m ∧ m ≤ localRank p G := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  set i₀ : Fin m := ⟨0, by omega⟩
  set i₁ : Fin m := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h2E : (2 : AdjoinRoot (h : K[X])) ≠ 0 := by
    intro h0
    apply h2
    apply (algebraMap K (AdjoinRoot (h : K[X]))).injective
    rw [map_ofNat, map_zero]
    exact h0
  obtain ⟨g, hψg, hg2, hgc⟩ := exists_sign_lift T.basis T.lam T.lam_pow T.ψ T.injective T.diag i₀
    (T.sign i₀)
  refine block_torus_central_cover_witness T.basis Y (proj r K) φ hφ hker hp hp2 T.lam_pow
    T.lam_order T.ψ T.injective T.diag T.perm
    (fun g _ hg1 hgp => eq_one_of_proj_eq_one_of_pow_eq_one hr hp2 hp hg1 hgp)
    ⊤ (k := m) (le_of_eq (by rw [Subgroup.card_top, card_multiplicative_fin_zmod]))
    (z := (g : StatedSp r K)) hg2 ?_ (fun a _ => hgc a)
  intro hz1
  obtain ⟨c, hc⟩ := exists_smul_of_proj_eq_one hz1
  refine sign_not_scalar T.basis h2E hi (algebraMap K _ c) (fun w => ?_)
  apply Subtype.ext
  rw [← hψg, T.act g w, hc, coe_algebraMap_smul_primaryComponent]

theorem TorusBlock.witness_even (T : TorusBlock x h p m) [Finite K] {G : Type*} [Group G]
    [Finite G] (Y : Subgroup G) (φ : Y →* StatedProj (StatedSp r K))
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) (hp : p.Prime)
    (hp2 : p ≠ 2) (hr : 1 ≤ r) (h2 : (2 : K) = 0) (hm : 1 ≤ m) :
    ∃ u : G, u ∈ Y ∧ orderOf u = 2 ∧ ∃ A : Subgroup G, A ≤ Y ⊓ Subgroup.centralizer {u} ∧
      IsElemAbelian p A ∧ Nat.card A = p ^ (m - 1) ∧ m - 1 ≤ localRank p G := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  set i₀ : Fin m := ⟨0, by omega⟩
  obtain ⟨w, hw⟩ : ∃ w : Fin r ⊕ Fin r → K,
      w = ((T.basis i₀ : primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K) :=
    ⟨_, rfl⟩
  have hw0 : w ≠ 0 := fun h0 => T.basis.ne_zero i₀ (Subtype.ext (hw.symm.trans h0))
  set B : LinearMap.BilinForm K (Fin r ⊕ Fin r → K) := spForm r K
  have hBalt : B.IsAlt := spForm_isAlt
  set Tr := symplecticTransvection B hBalt w 1 with hTr
  have hTmem : Tr ∈ sesqUnitaryGroup B := fun u v =>
    symplecticTransvection_mem_bilinIsometryGroup hBalt w 1 u v
  obtain ⟨t, ht⟩ : Tr ∈ (spLin r K).range := by
    rw [range_spLin]
    exact hTmem
  have htu : ∀ u, spEnd t u = u + B u w • w := fun u => by
    have h1 := symplecticTransvection_apply hBalt w 1 u
    rw [one_mul] at h1
    exact (congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K) =>
      (g : Module.End K (Fin r ⊕ Fin r → K)) u) ht).trans h1
  have ht2 : t ^ 2 = 1 := by
    apply spLin_injective
    rw [map_pow, map_one, ht, hTr, pow_two, symplecticTransvection_mul,
      show (1 : K) + 1 = 0 by rw [one_add_one_eq_two, h2], symplecticTransvection_zero]
  have htρ : proj r K t ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := exists_smul_of_proj_eq_one h1
    have hBw : B w w = 0 := hBalt.self_eq_zero w
    have hc1 : c = 1 := by
      have e := (htu w).symm.trans (hc w)
      rw [hBw, zero_smul, add_zero] at e
      have : (1 - c) • w = 0 := by rw [sub_smul, one_smul, ← e, sub_self]
      exact (sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hw0)).symm
    obtain ⟨u, hu⟩ : ∃ u, B u w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hw0 (spForm_nondegenerate.2 w hcon)
    have e := (htu u).symm.trans (hc u)
    rw [hc1, one_smul] at e
    have : B u w • w = 0 := by
      have := congrArg (fun y => y - u) e
      simpa using this
    exact (smul_ne_zero hu hw0) this
  refine block_torus_central_cover_witness T.basis Y (proj r K) φ hφ hker hp hp2 T.lam_pow
    T.lam_order T.ψ T.injective T.diag T.perm
    (fun g _ hg1 hgp => eq_one_of_proj_eq_one_of_pow_eq_one hr hp2 hp hg1 hgp)
    (coordHom i₀).ker (k := m - 1) (le_of_eq (by rw [card_ker_coordHom])) (z := t) ht2 htρ ?_
  intro a ha
  have haw := T.spEnd_torusS_basis a i₀ (mem_ker_coordHom.mp ha)
  rw [← hw] at haw
  set H := torusS T.basis T.lam T.lam_pow T.ψ T.injective T.diag a
  have hHiso : ∀ u v, B (spEnd H u) (spEnd H v) = B u v := fun u v =>
    mem_sesqUnitaryGroup.mp (spLin_mem H) u v
  have hBw : ∀ u, B (spEnd H u) w = B u w := fun u => by
    have := hHiso u w
    rwa [haw] at this
  have hc : t * H = H * t := by
    apply spLin_injective
    rw [map_mul, map_mul]
    refine Units.ext (LinearMap.ext fun u => ?_)
    rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
    change spEnd t (spEnd H u) = spEnd H (spEnd t u)
    rw [htu, htu, map_add, map_smul, haw, hBw]
  exact hc

end Block

end CFSG.RankThree.PartOne.KCSymplectic
