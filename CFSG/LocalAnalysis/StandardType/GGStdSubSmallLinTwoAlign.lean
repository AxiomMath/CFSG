module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallLinTwoFrame

public section

namespace CFSG.StandardType.SmallL2

open Polynomial Module Matrix CFSG.RankThree.CALinearPlane CoordSL Multiplicative
open scoped commutatorElement

section Align

variable {G : Type} [Group G] {K : Type} [Field K] [Finite K] {g : K[X]}
  [Fact (Irreducible g)] {n s r p : ℕ} [Fact p.Prime]
  {ψ : Matrix.SpecialLinearGroup (Fin n) K →* G} {A₀ : Matrix.SpecialLinearGroup (Fin n) K}
  {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} {hC : (rootMat g).det = 1}
  {hCp : rootMat g ^ p = 1}

theorem exists_aligned_frame (hζ : AdjoinRoot.root g ^ p = 1) (β : Fin s → ZMod p) :
    ∃ (A₁ : Matrix.SpecialLinearGroup (Fin n) K) (β₁ : Fin s → ZMod p), Aligned hζ β₁ ∧
      (frameHom ψ A₁ ε hC hCp).range = (frameHom ψ A₀ ε hC hCp).range ∧
      frameHom ψ A₁ ε hC hCp (ofAdd β₁) = frameHom ψ A₀ ε hC hCp (ofAdd β) := by
  obtain ⟨η, hηO, hal⟩ := exists_aligned hζ β
  obtain ⟨M, hM⟩ := exists_conj_frameHom g ψ A₀ ε hC hCp hζ (Equiv.refl _) η hηO
  set w := SLRep.ggFrame ψ A₀ M with hwdef
  have hw : ∀ u : Fin s → ZMod p, frameHom ψ (A₀ * M) ε hC hCp (ofAdd u) =
      w * frameHom ψ A₀ ε hC hCp (ofAdd u) * w⁻¹ := by
    intro u
    simp only [hwdef, frameHom_apply, SLRep.ggFrame_apply, ← map_inv, ← map_mul]
    congr 1
    group
  have hι' : ∀ t : Fin s → ZMod p,
      frameHom ψ (A₀ * M) ε hC hCp (ofAdd fun i => (η i : ZMod p) * t i) =
        frameHom ψ A₀ ε hC hCp (ofAdd t) := by
    intro t
    have h := hM t
    simp only [Equiv.refl_apply] at h
    rw [hw, ← h]
    group
  have hrange : (frameHom ψ (A₀ * M) ε hC hCp).range = (frameHom ψ A₀ ε hC hCp).range := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨ofAdd fun i => ((η i)⁻¹ : (ZMod p)ˣ) * toAdd u i, ?_⟩
      rw [← hι']
      congr 1
      apply toAdd.injective
      funext i
      simp only [toAdd_ofAdd]
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    · rintro ⟨u, rfl⟩
      exact ⟨_, hι' (toAdd u)⟩
  exact ⟨A₀ * M, fun i => (η i : ZMod p) * β i, hal, hrange, hι' β⟩

end Align

section Aligned

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ} [Fact p.Prime]
  {ψ : Matrix.SpecialLinearGroup (Fin n) K →* G} {A₀ : Matrix.SpecialLinearGroup (Fin n) K}
  {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} {hC : (rootMat g).det = 1}
  {hCp : rootMat g ^ p = 1}

theorem comp_of_aligned_eq (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K - 1)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hgd : g ∣ cyclotomic p K) {hζ : AdjoinRoot.root g ^ p = 1} {β : Fin s → ZMod p}
    (hal : Aligned hζ β) {L₁ : Subgroup G} (hb1 : frameHom ψ A₀ ε hC hCp (ofAdd β) ≠ 1)
    (hcomp : CFSG.Assembly.IsComponentOf L₁
      (ψ.range ⊓ Subgroup.centralizer {frameHom ψ A₀ ε hC hCp (ofAdd β)})) :
    L₁ = (coordBlockSL K (zeroCoords ε β)).map (SLRep.ggFrame ψ A₀) ∨
      ∃ c : ZMod p, c ≠ 0 ∧ (classSet β c).Nonempty ∧
        L₁ = ((coordBlockSL (AdjoinRoot g) (classSet β c)).map (theta g ε)).map
          (SLRep.ggFrame ψ A₀) := by
  classical
  have hp : p.Prime := Fact.out
  have hpK' : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hprim := root_isPrimitiveRoot hp hpK' hgd
  have hnsplit : ∀ c : K, c ^ p = 1 → c = 1 := fun c hc => OrdPNS.eq_one_of_pow_eq_one hp hpK hc
  set φ := SLRep.ggFrame ψ A₀ with hφdef
  have hkerφ : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) :=
    SLRep.ker_ggFrame_le hker A₀
  set Y := SLNS.nsSL ε hC (fun i => (β i).val) with hY
  set C₀ := Subgroup.centralizer ({Y} : Set (Matrix.SpecialLinearGroup (Fin n) K)) with hC₀
  rw [centralizer_eq_map hker hnsplit β] at hcomp
  have hmemC₀ : ∀ u, u ∈ C₀ ↔ u * Y = Y * u := fun u => Subgroup.mem_centralizer_singleton_iff
  set J := zeroCoords ε β with hJ
  set KC : ZMod p → Subgroup (Matrix.SpecialLinearGroup (Fin n) K) := fun c =>
    (coordBlockSL (AdjoinRoot g) (classSet β c)).map (theta g ε) with hKC
  have hKZC : coordBlockSL K J ≤ C₀ := fun M hM => (hmemC₀ M).mpr
    (comm_zeroBlock_of_torus (k := fun i => (β i).val)
      (fun i hi => by rw [hi, ZMod.val_zero]) hM).symm
  have hKCC : ∀ c, KC c ≤ C₀ := by
    rintro c _ ⟨M, hM, rfl⟩
    exact (hmemC₀ _).mpr (comm_classBlock_of_torus (fun i j hi hj => by rw [hi, hj]) hM)
  have hKZn : (((coordBlockSL K J).map φ).subgroupOf (C₀.map φ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hKZC)]
    rintro _ _ ⟨M, hM, rfl⟩ ⟨u, hu, rfl⟩
    exact ⟨u * M * u⁻¹, conj_mem_zeroBlock hprim hal ((hmemC₀ u).mp hu) hM,
      by rw [map_mul, map_mul, map_inv]⟩
  have hKCn : ∀ c, c ≠ 0 → (((KC c).map φ).subgroupOf (C₀.map φ)).Normal := by
    intro c hc
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono (hKCC c))]
    rintro _ _ ⟨_, ⟨M, hM, rfl⟩, rfl⟩ ⟨u, hu, rfl⟩
    obtain ⟨M', hM', hM'eq⟩ := conj_mem_classBlock hprim hal hc ((hmemC₀ u).mp hu) hM
    exact ⟨theta g ε M', ⟨M', hM', rfl⟩, by rw [hM'eq, map_mul, map_mul, map_inv]⟩
  have hq := hcomp.2.2
  have hdZ := le_or_commutator_eq_bot_of_normal hcomp (Subgroup.map_mono hKZC) hKZn
  by_cases hZ : L₁ ≤ (coordBlockSL K J).map φ
  ·
    left
    have hQ := quasisimple_of_le_map_coordBlockSL φ hq hZ
    have hrange : (coordBlockSL K J).map φ = (φ.comp (blockSLOn K J)).range := by
      rw [MonoidHom.range_comp, range_blockSLOn]
    have hc' :=
      CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hcomp hZ (Subgroup.map_mono hKZC)
    rw [hrange] at hc' ⊢
    exact eq_of_isComponentOf_range hQ _ hc'
  · by_cases hCex : ∃ c, c ≠ 0 ∧ L₁ ≤ (KC c).map φ
    ·
      right
      obtain ⟨c, hc, hLc⟩ := hCex
      have : CharP (AdjoinRoot g) 2 :=
        charP_of_injective_algebraMap (algebraMap K (AdjoinRoot g)).injective 2
      have : Finite (AdjoinRoot g) := finite_adjoinRoot
      have hmap : (KC c).map φ =
          (coordBlockSL (AdjoinRoot g) (classSet β c)).map (φ.comp (theta g ε)) :=
        Subgroup.map_map _ _ _
      rw [hmap] at hLc
      have hQ := quasisimple_of_le_map_coordBlockSL (φ.comp (theta g ε)) hq hLc
      have hS2 := two_le_card_of_le_map_coordBlockSL (φ.comp (theta g ε)) hq hLc
      have hS : (classSet β c).Nonempty := Finset.card_pos.mp (by omega)
      have hrange : (coordBlockSL (AdjoinRoot g) (classSet β c)).map (φ.comp (theta g ε)) =
          ((φ.comp (theta g ε)).comp (blockSLOn (AdjoinRoot g) (classSet β c))).range := by
        rw [MonoidHom.range_comp, range_blockSLOn]
      have hL₁ : L₁ = (KC c).map φ := by
        have hc' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hcomp hLc
          (hmap ▸ Subgroup.map_mono (hKCC c))
        rw [hmap, hrange]
        rw [hrange] at hc'
        exact eq_of_isComponentOf_range hQ _ hc'
      exact ⟨c, hc, hS, hL₁⟩
    ·
      exfalso
      push Not at hCex
      have hZb : ⁅L₁, (coordBlockSL K J).map φ⁆ = ⊥ := hdZ.resolve_left hZ
      have hCb : ∀ c, c ≠ 0 → ⁅L₁, (KC c).map φ⁆ = ⊥ := fun c hc =>
        (le_or_commutator_eq_bot_of_normal hcomp (Subgroup.map_mono (hKCC c))
          (hKCn c hc)).resolve_left (hCex c hc)
      have hcommN : ∀ {N : Subgroup G}, ⁅L₁, N⁆ = ⊥ → ∀ x ∈ L₁, ∀ y ∈ N, x * y = y * x := by
        intro N hN x hx y hy
        have h1 := Subgroup.commutator_mem_commutator hx hy
        rw [hN, Subgroup.mem_bot] at h1
        exact commutatorElement_eq_one_iff_mul_comm.mp h1
      have hZw : ∀ w, φ w ∈ L₁ → ∀ x y (hxy : x ≠ y), x ∈ J → y ∈ J →
          w * Matrix.SpecialLinearGroup.transvection hxy (1 : K) =
            Matrix.SpecialLinearGroup.transvection hxy 1 * w := by
        intro w hw x y hxy hx hy
        have ht := SLRep.transvection_mem_coordBlockSL hx hy hxy (1 : K)
        exact commute_of_map_commute_of_mul_self hkerφ (LinSemisimple.transvection_one_mul_self hxy)
          (hcommN hZb _ hw _ (Subgroup.mem_map_of_mem φ ht))
      have hcw : ∀ w, φ w ∈ L₁ → ∀ i j (hij : i ≠ j), β i = β j → β i ≠ 0 →
          ∀ c' : AdjoinRoot g, w * theta g ε (Matrix.SpecialLinearGroup.transvection hij c') =
            theta g ε (Matrix.SpecialLinearGroup.transvection hij c') * w := by
        intro w hw i j hij hβij hβi c'
        have hT := SLRep.transvection_mem_coordBlockSL (mem_classSet.mpr rfl)
          (mem_classSet.mpr hβij.symm) hij c'
        have hθT : theta g ε (Matrix.SpecialLinearGroup.transvection hij c') ∈ KC (β i) :=
          ⟨_, hT, rfl⟩
        exact commute_of_map_commute_of_mul_self hkerφ (theta_transvection_mul_self ε hij c')
          (hcommN (hCb (β i) hβi) _ hw _ (Subgroup.mem_map_of_mem φ hθT))
      refine LinSemisimple.false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
      obtain ⟨u, hu, rfl⟩ := hcomp.1 hx
      obtain ⟨v, hv, rfl⟩ := hcomp.1 hy
      rw [← map_mul, ← map_mul, commute_of_comm_blocks hprim hal ((hmemC₀ u).mp hu)
        ((hmemC₀ v).mp hv) (hZw u hx) (hZw v hy) (hcw u hx) (hcw v hy)]

end Aligned

end CFSG.StandardType.SmallL2

end
