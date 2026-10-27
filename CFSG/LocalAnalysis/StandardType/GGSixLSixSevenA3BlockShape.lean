module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordShapeSL

public section

open Polynomial Module Matrix CFSG.RankThree.CALinearPlane

namespace CFSG.StandardType

namespace CoordSL

open Multiplicative CoordShape

section Aligned

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] [CharP K 2]
  {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ} [Fact p.Prime]
  {ψ : Matrix.SpecialLinearGroup (Fin n) K →* G} {A₀ : Matrix.SpecialLinearGroup (Fin n) K}
  {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} {hC : (rootMat g).det = 1}
  {hCp : rootMat g ^ p = 1}

theorem eq_zeroBlock_or_classBlock_of_isComponentOf (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K - 1)
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (hgd : g ∣ cyclotomic p K) {hζ : AdjoinRoot.root g ^ p = 1} {E J : Subgroup G}
    (hE : E ≤ (frameHom ψ A₀ ε hC hCp).range) {T : Set (Fin s → ZMod p)}
    (hT : T = {t | frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ E})
    (hal : JointAligned (galExp g hζ) T)
    (hcomp : CFSG.Assembly.IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (E : Set G))) :
    J = (coordBlockSL K (zeroCoords ε (jointSupp T))).map (SLRep.ggFrame ψ A₀) ∨
      ∃ j₀, (∃ t ∈ T, t j₀ ≠ 0) ∧
        J = ((coordBlockSL (AdjoinRoot g) (classSet (jointClass T j₀) 1)).map (theta g ε)).map
          (SLRep.ggFrame ψ A₀) := by
  classical
  subst hT
  have hp : p.Prime := Fact.out
  have hpK' : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hprim := root_isPrimitiveRoot hp hpK' hgd
  have hnsplit : ∀ c : K, c ^ p = 1 → c = 1 := fun c hc => OrdPNS.eq_one_of_pow_eq_one hp hpK hc
  rw [centralizer_eq_map_joint hker hnsplit hE] at hcomp
  set ι := frameHom ψ A₀ ε hC hCp with hιdef
  set T : Set (Fin s → ZMod p) := {t | ι (ofAdd t) ∈ E} with hTdef
  have hT : ∀ t ∈ T, ∀ t₀ ∈ T, ∀ a : ZMod p, t - a • t₀ ∈ T :=
    fun t ht t₀ ht₀ a => sub_smul_mem ht ht₀ a
  set φ := SLRep.ggFrame ψ A₀ with hφdef
  have hkerφ : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) :=
    SLRep.ker_ggFrame_le hker A₀
  set C₀ := Subgroup.centralizer {Y | ∃ t : Fin s → ZMod p, ι (ofAdd t) ∈ E ∧
    Y = SLNS.nsSL ε hC (fun i => (t i).val)} with hC₀
  have hmemC₀ : ∀ u, u ∈ C₀ ↔ ∀ t ∈ T, u * SLNS.nsSL ε hC (fun i => (t i).val) =
      SLNS.nsSL ε hC (fun i => (t i).val) * u := by
    intro u
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h t ht
      exact (h _ ⟨t, ht, rfl⟩).symm
    · rintro h _ ⟨t, ht, rfl⟩
      exact (h t ht).symm
  set KZ := coordBlockSL K (zeroCoords ε (jointSupp T)) with hKZ
  set KC : Fin s → Subgroup (Matrix.SpecialLinearGroup (Fin n) K) := fun j =>
    (coordBlockSL (AdjoinRoot g) (classSet (jointClass T j) 1)).map (theta g ε) with hKC
  have halZ : Aligned hζ (jointSupp T) := aligned_of_zero_one jointSupp_zero_or_one
  have hKZC : KZ ≤ C₀ := fun M hM => (hmemC₀ M).mpr fun t ht =>
    (comm_zeroBlock_of_torus (k := fun i => (t i).val) (fun i hi => by
      rw [jointSupp_eq_zero_iff.mp hi t ht, ZMod.val_zero]) hM).symm
  have hKCC : ∀ j, KC j ≤ C₀ := by
    rintro j _ ⟨M, hM, rfl⟩
    refine (hmemC₀ _).mpr fun t ht => comm_classBlock_of_torus (fun i i' hi hi' => ?_) hM
    rw [jointClass_eq_one_iff.mp hi t ht, jointClass_eq_one_iff.mp hi' t ht]
  have hKZn : ((KZ.map φ).subgroupOf (C₀.map φ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hKZC)]
    rintro _ _ ⟨M, hM, rfl⟩ ⟨u, hu, rfl⟩
    have huZ := comm_nsSL_of_joint hprim hT hal ((hmemC₀ u).mp hu)
      (fun i hi => jointSupp_eq_zero_iff.mpr hi) (fun i j hij => jointSupp_eq_of hij)
    exact ⟨u * M * u⁻¹, conj_mem_zeroBlock hprim halZ huZ hM,
      by rw [map_mul, map_mul, map_inv]⟩
  have hKCn : ∀ j, (∃ t ∈ T, t j ≠ 0) → (((KC j).map φ).subgroupOf (C₀.map φ)).Normal := by
    rintro j ⟨t₀, ht₀, hj⟩
    have halX : Aligned hζ (jointClass T j) := aligned_of_zero_one (jointClass_zero_or_one j)
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono (hKCC j))]
    rintro _ _ ⟨_, ⟨M, hM, rfl⟩, rfl⟩ ⟨u, hu, rfl⟩
    have huX := comm_nsSL_of_joint hprim hT hal ((hmemC₀ u).mp hu) (β := jointClass T j)
      (fun k hk => jointClass_eq_zero_of_zero ht₀ hj hk) (fun k l hkl => jointClass_eq_of hkl)
    obtain ⟨M', hM', hM'eq⟩ := conj_mem_classBlock hprim halX one_ne_zero huX hM
    exact ⟨theta g ε M', ⟨M', hM', rfl⟩, by rw [hM'eq, map_mul, map_mul, map_inv]⟩
  have hq := hcomp.2.2
  by_cases hZ : J ≤ KZ.map φ
  ·
    left
    have hQ := quasisimple_of_le_map_coordBlockSL φ hq hZ
    have hrange : KZ.map φ = (φ.comp (blockSLOn K (zeroCoords ε (jointSupp T)))).range := by
      rw [hKZ, MonoidHom.range_comp, range_blockSLOn]
    have hc' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hcomp hZ
      (Subgroup.map_mono hKZC)
    rw [hrange] at hc' ⊢
    exact eq_of_isComponentOf_range hQ _ hc'
  · by_cases hCex : ∃ j₀, (∃ t ∈ T, t j₀ ≠ 0) ∧ J ≤ (KC j₀).map φ
    ·
      right
      obtain ⟨j₀, hj₀, hJC⟩ := hCex
      refine ⟨j₀, hj₀, ?_⟩
      haveI : CharP (AdjoinRoot g) 2 :=
        charP_of_injective_algebraMap (algebraMap K (AdjoinRoot g)).injective 2
      haveI : Finite (AdjoinRoot g) := finite_adjoinRoot
      have hmap : (KC j₀).map φ =
          (coordBlockSL (AdjoinRoot g) (classSet (jointClass T j₀) 1)).map
            (φ.comp (theta g ε)) :=
        Subgroup.map_map _ _ _
      rw [hmap] at hJC
      have hQ := quasisimple_of_le_map_coordBlockSL (φ.comp (theta g ε)) hq hJC
      have hrange : (coordBlockSL (AdjoinRoot g) (classSet (jointClass T j₀) 1)).map
            (φ.comp (theta g ε)) =
          ((φ.comp (theta g ε)).comp (blockSLOn (AdjoinRoot g)
            (classSet (jointClass T j₀) 1))).range := by
        rw [MonoidHom.range_comp, range_blockSLOn]
      have hL₁ : J = (KC j₀).map φ := by
        have hc' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hcomp hJC
          (hmap ▸ Subgroup.map_mono (hKCC j₀))
        rw [hmap, hrange]
        rw [hrange] at hc'
        exact eq_of_isComponentOf_range hQ _ hc'
      exact hL₁
    ·
      exfalso
      push Not at hCex
      have hZb : ⁅J, KZ.map φ⁆ = ⊥ :=
        (le_or_commutator_eq_bot_of_normal hcomp (Subgroup.map_mono hKZC) hKZn).resolve_left hZ
      have hCb : ∀ j₀, (∃ t ∈ T, t j₀ ≠ 0) → ⁅J, (KC j₀).map φ⁆ = ⊥ := fun j₀ hj₀ =>
        (le_or_commutator_eq_bot_of_normal hcomp (Subgroup.map_mono (hKCC j₀))
          (hKCn j₀ hj₀)).resolve_left (hCex j₀ hj₀)
      have hcommN : ∀ {N : Subgroup G}, ⁅J, N⁆ = ⊥ → ∀ x ∈ J, ∀ y ∈ N, x * y = y * x := by
        intro N hN x hx y hy
        have h1 := Subgroup.commutator_mem_commutator hx hy
        rw [hN, Subgroup.mem_bot] at h1
        exact commutatorElement_eq_one_iff_mul_comm.mp h1
      have hZw : ∀ w, φ w ∈ J → ∀ x y (hxy : x ≠ y), x ∈ zeroCoords ε (jointSupp T) →
          y ∈ zeroCoords ε (jointSupp T) →
          w * Matrix.SpecialLinearGroup.transvection hxy (1 : K) =
            Matrix.SpecialLinearGroup.transvection hxy 1 * w := by
        intro w hw x y hxy hx hy
        have ht := SLRep.transvection_mem_coordBlockSL hx hy hxy (1 : K)
        exact commute_of_map_commute_of_mul_self hkerφ
          (LinSemisimple.transvection_one_mul_self hxy)
          (hcommN hZb _ hw _ (Subgroup.mem_map_of_mem φ ht))
      have hcw : ∀ w, φ w ∈ J → ∀ i j (hij : i ≠ j), (∀ t ∈ T, t i = t j) →
          (∃ t ∈ T, t i ≠ 0) → ∀ c' : AdjoinRoot g,
          w * theta g ε (Matrix.SpecialLinearGroup.transvection hij c') =
            theta g ε (Matrix.SpecialLinearGroup.transvection hij c') * w := by
        intro w hw i j hij hrel hi c'
        have hiX : i ∈ classSet (jointClass T i) 1 :=
          mem_classSet.mpr (jointClass_eq_one_iff.mpr fun _ _ => rfl)
        have hjX : j ∈ classSet (jointClass T i) 1 :=
          mem_classSet.mpr (jointClass_eq_one_iff.mpr fun t ht => (hrel t ht).symm)
        have hT' := SLRep.transvection_mem_coordBlockSL hiX hjX hij c'
        have hθT : theta g ε (Matrix.SpecialLinearGroup.transvection hij c') ∈ KC i :=
          ⟨_, hT', rfl⟩
        exact commute_of_map_commute_of_mul_self hkerφ (theta_transvection_mul_self ε hij c')
          (hcommN (hCb i hi) _ hw _ (Subgroup.mem_map_of_mem φ hθT))
      refine LinSemisimple.false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
      obtain ⟨u, hu, rfl⟩ := hcomp.1 hx
      obtain ⟨v, hv, rfl⟩ := hcomp.1 hy
      rw [← map_mul, ← map_mul, commute_of_comm_blocks_joint hprim hT hal ((hmemC₀ u).mp hu)
        ((hmemC₀ v).mp hv) (hZw u hx) (hZw v hy) (hcw u hx) (hcw v hy)]

theorem exists_jointAligned_frame (hζ : AdjoinRoot.root g ^ p = 1) (E : Subgroup G) :
    ∃ A₀' : Matrix.SpecialLinearGroup (Fin n) K,
      (frameHom ψ A₀' ε hC hCp).range = (frameHom ψ A₀ ε hC hCp).range ∧
        JointAligned (galExp g hζ) {t | frameHom ψ A₀' ε hC hCp (ofAdd t) ∈ E} := by
  obtain ⟨η, hηO, hal⟩ := exists_jointAligned (galExp g hζ)
    {t | frameHom ψ A₀ ε hC hCp (ofAdd t) ∈ E}
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
  refine ⟨A₀ * M, hrange, ?_⟩
  rw [setOf_mem_eq_image hι' E]
  exact hal

end Aligned

end CoordSL

end CFSG.StandardType
