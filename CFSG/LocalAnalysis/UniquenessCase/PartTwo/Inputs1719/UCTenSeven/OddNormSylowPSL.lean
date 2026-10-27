module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAutFrames
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddLinearFrameMatrix
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitPermutationAction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open Matrix
open scoped MatrixGroups
open CFSG.ComponentClassification.AS81.Sec2 (conjSetStab conjPermHom)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (linearFrameBlock linearFrameInvolution)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (exists_full_coordinate_frame_funSet_psl_even
  exists_full_coordinate_frame_funSet_psl_odd nonempty_equiv_perm_funSet_psl_even
  nonempty_equiv_perm_funSet_psl_odd)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.ClassicalInvolution.WeakCT (blockSL)

private abbrev linearProjFrame (F : Type) [Field F] (m tail : ℕ) : Type :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL (2 * m + 1 + 1 + tail) F

private lemma exists_odd_orderOf_lift_local {H G' : Type*} [Group H] [Finite H] [Group G']
    (ψ : H →* G') (b : H) (hodd : Odd (orderOf (ψ b))) :
    ∃ k : ℕ, Odd (orderOf (b ^ k)) ∧ ψ (b ^ k) = ψ b := by
  have hN : orderOf b ≠ 0 := (orderOf_pos b).ne'
  obtain ⟨e, m, hm, hNm⟩ := Nat.exists_eq_two_pow_mul_odd hN
  have hcop : Nat.Coprime (2 ^ e) (orderOf (ψ b)) := Nat.Coprime.pow_left e
    (Nat.coprime_two_left.mpr hodd)
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 0 1
  refine ⟨k, ?_, ?_⟩
  · have hdvd : 2 ^ e ∣ k := (Nat.modEq_zero_iff_dvd.mp hk1)
    obtain ⟨l, rfl⟩ := hdvd
    have h1 : (b ^ (2 ^ e * l)) ^ m = 1 := by
      rw [← pow_mul, show 2 ^ e * l * m = 2 ^ e * m * l by ring, pow_mul, ← hNm,
        pow_orderOf_eq_one, one_pow]
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h1)
  · rw [map_pow]
    have h1 : (ψ b) ^ k = (ψ b) ^ 1 := (pow_eq_pow_iff_modEq).mpr hk2
    rw [h1, pow_one]

private lemma linearFrameBlock_map_mulEquiv_sl2 {F : Type} [Field F] [Finite F] {X : Type}
    [Group X] {m tail : ℕ} (hm : 1 ≤ m) (ψ : SL(2 * m + 1 + 1 + tail, F) →* X)
    (hker : ψ.ker ≤ Subgroup.center SL(2 * m + 1 + 1 + tail, F)) (k : Fin (m + 1)) :
    ∃ e : ↥((linearFrameBlock F m k tail).map ψ) ≃* SL(2, F),
      ∀ z, ψ (blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by have := k.isLt; omega)
          (e.toMonoidHom z)) = (z : X) := by
  have hι : Function.Injective
      (ψ.comp (blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by have := k.isLt; omega))) :=
    CFSG.ClassicalInvolution.WeakCT.comp_blockSL_injective hker
      (by have := k.isLt; omega) (by omega)
  have hrange : (ψ.comp (blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val)
        (by have := k.isLt; omega))).range = (linearFrameBlock F m k tail).map ψ := by
    rw [MonoidHom.range_comp]
    rfl
  refine ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hι).symm, ?_⟩
  intro z
  have h := MonoidHom.ofInjective_apply (f := ψ.comp (blockSL F (2 * m + 1 + 1 + tail) 2
      (2 * k.val) (by have := k.isLt; omega))) hι
    (x := (MonoidHom.ofInjective hι).symm ((MulEquiv.subgroupCongr hrange.symm) z))
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm.trans (MulEquiv.subgroupCongr_apply hrange.symm z)

private lemma exists_sylow_sl2_of_isSylowOf_frame {F : Type} [Field F] {X : Type} [Group X]
    [Finite X] {J Q : Subgroup X} (e : ↥J ≃* SL(2, F))
    (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q J) :
    ∃ Q' : Sylow 2 SL(2, F), ∀ A ∈ (Q' : Subgroup SL(2, F)),
      ∃ z : ↥J, (z : X) ∈ Q ∧ e.toMonoidHom z = A := by
  obtain ⟨T, hT⟩ := hQ
  let Q' : Sylow 2 SL(2, F) := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ'coe : (Q' : Subgroup SL(2, F)) = (T : Subgroup ↥J).map e.toMonoidHom :=
    Sylow.coe_mapSurjective e.surjective T
  refine ⟨Q', fun A hA => ?_⟩
  rw [hQ'coe] at hA
  obtain ⟨z, hzT, hzA⟩ := Subgroup.mem_map.mp hA
  exact ⟨z, hT ▸ Subgroup.mem_map_of_mem J.subtype hzT, hzA⟩

private lemma mem_normalizer_conj_of_map_eq {G : Type*} [Group G] {H K : Subgroup G} {c w : G}
    (hw : K.map (MulAut.conj w).toMonoidHom = K)
    (hK : H = K.map (MulAut.conj c⁻¹).toMonoidHom) :
    c⁻¹ * w * c ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, hK, Subgroup.map_map]
  have hcomp : (MulAut.conj (c⁻¹ * w * c)).toMonoidHom.comp
      (MulAut.conj c⁻¹).toMonoidHom =
      (MulAut.conj c⁻¹).toMonoidHom.comp (MulAut.conj w).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    group
  change K.map ((MulAut.conj (c⁻¹ * w * c)).toMonoidHom.comp
    (MulAut.conj c⁻¹).toMonoidHom) = K.map ((MulAut.conj c⁻¹).toMonoidHom)
  rw [hcomp, ← Subgroup.map_map]
  rw [hw]

private lemma toGL_slConjugation_frame {F : Type} [Field F] {n : ℕ} (A : GL (Fin n) F)
    (g : SL(n, F)) :
    SpecialLinearGroup.toGL (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
        n F A g) = A * SpecialLinearGroup.toGL g * A⁻¹ := by
  apply Units.ext
  show ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A g :
      SL(n, F)) : Matrix (Fin n) (Fin n) F) =
    ((A * SpecialLinearGroup.toGL g * A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_slConjugation]
  simp


private lemma funSet_map_mulEquiv_local {q : ℕ} {X : Type} [Group X] [Finite X] (α : X ≃* X)
    {S Kb : Subgroup X} (h : Kb ∈ FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q) X S) :
    Kb.map α.toMonoidHom ∈
      FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q) X (S.map α.toMonoidHom) := by
  rw [FunSet] at h ⊢
  obtain ⟨hfund, hSyl⟩ := h
  refine ⟨CFSG.LocalAnalysis.UniquenessCase.isFundamentalOver_map_mulEquiv α hfund, ?_⟩
  rw [← Subgroup.map_inf S Kb α.toMonoidHom α.injective]
  obtain ⟨Q, hQ⟩ := hSyl
  rw [← hQ]
  refine ⟨Q.mapSurjective (α.toMonoidHom.subgroupMap_surjective Kb), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem normSylowIn_projectiveSL_frame {F : Type} [Field F] [Finite F] {q m tail : ℕ}
    (hF : Odd (Nat.card F)) (hm : 1 ≤ m) (htail : tail ≤ 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hframe : ∀ P : Sylow 2 (linearProjFrame F m tail),
      ∃ c : linearProjFrame F m tail,
        FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q) (linearProjFrame F m tail)
            (P : Subgroup (linearProjFrame F m tail)) =
          Set.range (fun k : Fin (m + 1) =>
            ((linearFrameBlock F m k tail).map
              (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (2 * m + 1 + 1 + tail) F)).map
              (MulAut.conj c).toMonoidHom))
    (hperm : ∀ P : Sylow 2 (linearProjFrame F m tail),
      Nonempty ((conjPermHom (le_refl (conjSetStab
        (FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q) (linearProjFrame F m tail)
          (P : Subgroup (linearProjFrame F m tail)))))).range ≃* Equiv.Perm (Fin (m + 1)))) :
    NormSylowIn (linearProjFrame F m tail)
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup
        (2 * m + 1 + 1 + tail) F) p := by
  refine normSylowIn_of_odd hp (by omega) ?_
  intro S hS θ hθD hθodd hθS hθp
  have hSiff := (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := S) (K := ⊤)).mp hS
  let P : Sylow 2 (linearProjFrame F m tail) :=
    hSiff.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hSiff.2.2)
  have hPcoe : (P : Subgroup (linearProjFrame F m tail)) = S := IsPGroup.toSylow_coe _ _
  have hS2 : IsPGroup 2 ↥S := hSiff.2.1
  obtain ⟨c, hfull⟩ := hframe P
  let ψc : SL(2 * m + 1 + 1 + tail, F) →* linearProjFrame F m tail :=
    (MulAut.conj c).toMonoidHom.comp
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (2 * m + 1 + 1 + tail) F)
  let Δ : Set (Subgroup (linearProjFrame F m tail)) :=
    FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q) (linearProjFrame F m tail)
      (P : Subgroup (linearProjFrame F m tail))
  have hfull' : Δ = Set.range (fun k : Fin (m + 1) =>
      (linearFrameBlock F m k tail).map ψc) := by
    simpa [Δ, ψc, Subgroup.map_map] using hfull
  have hconj : ∀ (g : linearProjFrame F m tail) {K : Subgroup (linearProjFrame F m tail)},
      CFSG.LocalAnalysis.UniquenessCase.fundPred q ⊤ K →
        CFSG.LocalAnalysis.UniquenessCase.fundPred q ⊤
          (K.map (MulAut.conj g).toMonoidHom) :=
    fun g K h => CFSG.LocalAnalysis.UniquenessCase.isFundamentalOver_map_mulEquiv
      (MulAut.conj g) h
  have hSΔ : (P : Subgroup (linearProjFrame F m tail)) ≤ conjSetStab Δ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.F14.sylow_le_conjSetStab_funSet hconj P
  obtain ⟨e⟩ := hperm P
  have hkerC : ψc.ker ≤ Subgroup.center SL(2 * m + 1 + 1 + tail, F) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    apply CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_le_center
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.ker_proj, MonoidHom.mem_ker]
    exact (MulAut.conj c).injective (by simpa [ψc] using hx)
  let Jf : Fin (m + 1) → Subgroup (linearProjFrame F m tail) := fun k =>
    (linearFrameBlock F m k tail).map ψc
  have hinj : Function.Injective Jf := by
    intro i j heq
    by_contra hij
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.F14.map_ne_of_commuting_of_equiv_sl2
      ψc hkerC
      ((MonoidHom.ofInjective (CFSG.ClassicalInvolution.WeakCT.blockSL_injective
        (by have := i.isLt; omega : 2 * i.val + 2 ≤ 2 * m + 1 + 1 + tail))).symm)
      (fun a ha b hb =>
        CFSG.LocalAnalysis.UniquenessCase.UC22.commutes_linearFrameBlock
          (tail := tail) hij a ha b hb) heq
  have hJΔ : ∀ k, Jf k ∈ Δ := fun k => hfull' ▸ ⟨k, rfl⟩
  have hθΔ : ∀ J ∈ Δ, J.map θ.toMonoidHom ∈ Δ := by
    intro J hJ
    have h := funSet_map_mulEquiv_local (α := θ) hJ
    rwa [show (P : Subgroup (linearProjFrame F m tail)).map θ.toMonoidHom = P from by
      rw [hPcoe, hθS]] at h
  have hcard : Nat.card ↥Δ = Nat.card (Fin (m + 1)) := by
    let d : Fin (m + 1) → ↥Δ := fun k => ⟨Jf k, hJΔ k⟩
    have hd : Function.Bijective d := by
      constructor
      · intro i j heq
        exact hinj (congrArg Subtype.val heq)
      · rintro ⟨J, hJ⟩
        rw [hfull'] at hJ
        obtain ⟨k, rfl⟩ := hJ
        exact ⟨k, rfl⟩
    exact (Nat.card_eq_of_bijective d hd).symm
  have hfixΔ : ∀ J ∈ Δ, J.map θ.toMonoidHom = J :=
    map_eq_of_odd_of_conjSetStab_perm P hSΔ e hcard θ hθΔ
      (by rw [hPcoe]; exact hθS) hθodd
  let eJ : ∀ k : Fin (m + 1), ↥(Jf k) ≃* SL(2, F) := fun k =>
    Classical.choose (linearFrameBlock_map_mulEquiv_sl2 hm ψc hkerC k)
  have heJ : ∀ (k : Fin (m + 1)) (z : ↥(Jf k)),
      ψc (blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by have := k.isLt; omega)
        ((eJ k).toMonoidHom z)) = (z : linearProjFrame F m tail) := fun k =>
    Classical.choose_spec (linearFrameBlock_map_mulEquiv_sl2 hm ψc hkerC k)
  have hQex : ∀ k : Fin (m + 1), ∃ Q' : Sylow 2 SL(2, F),
      ∀ A ∈ (Q' : Subgroup SL(2, F)),
        ∃ z : ↥(Jf k), (z : linearProjFrame F m tail) ∈
          (P : Subgroup (linearProjFrame F m tail)) ⊓ Jf k ∧ (eJ k).toMonoidHom z = A :=
    fun k => exists_sylow_sl2_of_isSylowOf_frame (eJ k) ((hJΔ k).2)
  choose Q hQ using hQex
  have hQmem : ∀ (k : Fin (m + 1)) (A : SL(2, F)), A ∈ (Q k : Subgroup SL(2, F)) →
      ψc (blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by have := k.isLt; omega) A) ∈
        (P : Subgroup (linearProjFrame F m tail)) ⊓ Jf k := by
    intro k A hA
    obtain ⟨z, hz, hzA⟩ := hQ k A hA
    rw [← hzA, heJ k z]
    exact hz
  have hfixQ : ∀ k : Fin (m + 1),
      ∀ x ∈ (P : Subgroup (linearProjFrame F m tail)) ⊓ Jf k, θ x = x := by
    intro k
    refine fixes_of_isSylowOf_sl2 hF (eJ k) ((hJΔ k).2) θ ?_ hp hp5 ?_
    · rw [Subgroup.map_inf_eq _ _ _ θ.injective]
      rw [show (P : Subgroup (linearProjFrame F m tail)) = S from hPcoe, hθS,
        hfixΔ (Jf k) (hJΔ k)]
    · intro x hx
      exact hθp x (hPcoe ▸ hx.1)
  obtain ⟨A, hA⟩ := (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_linearAutGroup_iff
    (n := 2 * m + 1 + 1 + tail) (K := F)).mp hθD
  obtain ⟨l, hAodd, hAeq⟩ := exists_odd_orderOf_lift_local
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut (2 * m + 1 + 1 + tail) F) A
    (by rwa [hA])
  let A₁ : GL (Fin (2 * m + 1 + 1 + tail)) F := A ^ l
  have hA₁odd : Odd (orderOf A₁) := hAodd
  have hA₁conj : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut
      (2 * m + 1 + 1 + tail) F A₁ = θ := by
    change CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut
      (2 * m + 1 + 1 + tail) F (A ^ l) = θ
    rw [hAeq, hA]
  obtain ⟨C, hC⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective
    (2 * m + 1 + 1 + tail) F c
  let C' : GL (Fin (2 * m + 1 + 1 + tail)) F := SpecialLinearGroup.toGL C
  let A' : GL (Fin (2 * m + 1 + 1 + tail)) F := C'⁻¹ * A₁ * C'
  have hA'conj : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut
      (2 * m + 1 + 1 + tail) F A' =
      (MulAut.conj c)⁻¹ * θ * MulAut.conj c := by
    change CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut
      (2 * m + 1 + 1 + tail) F (C'⁻¹ * A₁ * C') = _
    rw [map_mul, map_mul, map_inv, hA₁conj,
      show CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut
        (2 * m + 1 + 1 + tail) F C' = MulAut.conj c from by
        rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_toGL, hC]]
  have hA'odd : Odd (orderOf A') := by
    have h := orderOf_injective (MulAut.conj C'⁻¹).toMonoidHom
      (MulAut.conj C'⁻¹).injective A₁
    rw [show A' = (MulAut.conj C'⁻¹).toMonoidHom A₁ by
      simp [A']]
    rw [h]
    exact hA₁odd
  have hcommGL : ∀ (k : Fin (m + 1)) (B : SL(2, F)),
      B ∈ (Q k : Subgroup SL(2, F)) →
      Commute A' (SpecialLinearGroup.toGL
        (blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by have := k.isLt; omega) B)) := by
    intro k B hB
    let g : SL(2 * m + 1 + 1 + tail, F) :=
      blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by have := k.isLt; omega) B
    let b : GL (Fin (2 * m + 1 + 1 + tail)) F := SpecialLinearGroup.toGL g
    obtain ⟨n, hn⟩ := (Q k).isPGroup' ⟨B, hB⟩
    have hBpow : B ^ 2 ^ n = 1 := by
      have h := congrArg (fun x : ↥(Q k) => (x : SL(2, F))) hn
      simpa using h
    have hgpow : g ^ 2 ^ n = 1 := by
      change (blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val)
        (by have := k.isLt; omega) B) ^ 2 ^ n = 1
      rw [← map_pow, hBpow, map_one]
    have hbpow : b ^ 2 ^ n = 1 := by
      change SpecialLinearGroup.toGL g ^ 2 ^ n = 1
      rw [← map_pow, hgpow, map_one]
    have hz : ψc g ∈ (P : Subgroup (linearProjFrame F m tail)) ⊓ Jf k := by
      change ψc (blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val)
        (by have := k.isLt; omega) B) ∈ _
      exact hQmem k B hB
    have hθz : θ (ψc g) = ψc g := hfixQ k _ hz
    have hconj : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut
        (2 * m + 1 + 1 + tail) F A'
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj
            (2 * m + 1 + 1 + tail) F g) =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (2 * m + 1 + 1 + tail) F g := by
      rw [hA'conj]
      change (MulAut.conj c)⁻¹ (θ ((MulAut.conj c)
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj
          (2 * m + 1 + 1 + tail) F g))) =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (2 * m + 1 + 1 + tail) F g
      rw [show (MulAut.conj c) (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj
          (2 * m + 1 + 1 + tail) F g) = ψc g from rfl, hθz]
      exact (MulEquiv.symm_apply_apply (MulAut.conj c) _)
    have hproj : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj
        (2 * m + 1 + 1 + tail) F
          (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
            (2 * m + 1 + 1 + tail) F A' g) =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (2 * m + 1 + 1 + tail) F g := by
      rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj]
      exact hconj
    have hscl : (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
        (2 * m + 1 + 1 + tail) F A' g)⁻¹ * g ∈
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars
          (2 * m + 1 + 1 + tail) F :=
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_proj_iff).mp hproj
    have hcenter : SpecialLinearGroup.toGL
        ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
          (2 * m + 1 + 1 + tail) F A' g)⁻¹ * g) ∈
        Subgroup.center (GL (Fin (2 * m + 1 + 1 + tail)) F) :=
      (SpecialLinearGroup.toGL_mem_center_iff _).mpr
        ((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_le_center
          (2 * m + 1 + 1 + tail) F) hscl)
    have hGL : SpecialLinearGroup.toGL
        ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
          (2 * m + 1 + 1 + tail) F A' g)⁻¹ * g) = (A' * b * A'⁻¹)⁻¹ * b := by
      rw [map_mul, map_inv, toGL_slConjugation_frame]
    have hc : (A' * b * A'⁻¹)⁻¹ * b ∈ Subgroup.center
        (GL (Fin (2 * m + 1 + 1 + tail)) F) := by
      rw [← hGL]
      exact hcenter
    have hd : A' * b * A'⁻¹ * b⁻¹ ∈ Subgroup.center
        (GL (Fin (2 * m + 1 + 1 + tail)) F) := by
      have hinv : ((A' * b * A'⁻¹)⁻¹ * b)⁻¹ ∈ Subgroup.center
          (GL (Fin (2 * m + 1 + 1 + tail)) F) := Subgroup.inv_mem _ hc
      have hconj := (inferInstance : (Subgroup.center
        (GL (Fin (2 * m + 1 + 1 + tail)) F)).Normal).conj_mem
        ((A' * b * A'⁻¹)⁻¹ * b)⁻¹ hinv b
      convert hconj using 1
      group
    exact commute_of_odd_of_pow_two_pow_of_mem_center hA'odd hbpow hd
  have hAmat : ∀ (k : Fin (m + 1)) (B : SL(2, F)),
      B ∈ (Q k : Subgroup SL(2, F)) →
      ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F) : Matrix (Fin (2 * m + 1 + 1 + tail))
          (Fin (2 * m + 1 + 1 + tail)) F) *
        ((blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val)
          (by have := k.isLt; omega) B : SL(2 * m + 1 + 1 + tail, F)) :
            Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) =
      ((blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val)
          (by have := k.isLt; omega) B : SL(2 * m + 1 + 1 + tail, F)) :
            Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) *
        ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F) : Matrix (Fin (2 * m + 1 + 1 + tail))
          (Fin (2 * m + 1 + 1 + tail)) F) := by
    intro k B hB
    have h : ((A' * SpecialLinearGroup.toGL
        (blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by have := k.isLt; omega) B) :
          GL (Fin (2 * m + 1 + 1 + tail)) F) :
        Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) =
        ((SpecialLinearGroup.toGL
          (blockSL F (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by have := k.isLt; omega) B) *
            A' : GL (Fin (2 * m + 1 + 1 + tail)) F) :
          Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) := by
      rw [(hcommGL k B hB).eq]
    simpa using h
  obtain ⟨c', hdiag, hconst⟩ := exists_blockScalar_of_commute_frame_sylow hF htail Q hAmat
  have hθw : ∀ s ∈ S, θ (θ s * s⁻¹) = θ s * s⁻¹ := by
    intro s hs
    let w : linearProjFrame F m tail := θ s * s⁻¹
    have hwJ : ∀ k : Fin (m + 1),
        w ∈ Subgroup.normalizer ((Jf k : Subgroup (linearProjFrame F m tail)) :
          Set (linearProjFrame F m tail)) := by
      intro k
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      change (Jf k).map (MulAut.conj w).toMonoidHom = Jf k
      let K : Subgroup (linearProjFrame F m tail) := (Jf k).map (MulAut.conj s⁻¹).toMonoidHom
      have hKΔ : K ∈ Δ :=
        (CFSG.ComponentClassification.AS81.Sec2.mem_conjSetStab.mp (hSΔ hs) (Jf k)).mp (hJΔ k)
      have hθK : K.map θ.toMonoidHom = K := hfixΔ K hKΔ
      have hθK' : K.map θ.symm.toMonoidHom = K := by
        calc K.map θ.symm.toMonoidHom
            = (K.map θ.toMonoidHom).map θ.symm.toMonoidHom := by rw [hθK]
          _ = K.map (θ.symm.toMonoidHom.comp θ.toMonoidHom) := by rw [Subgroup.map_map]
          _ = K.map (MonoidHom.id _) := by
                congr 1
                ext x
                simp
          _ = K := Subgroup.map_id K
      have hKs : K.map (MulAut.conj s).toMonoidHom = Jf k := by
        change ((Jf k).map (MulAut.conj s⁻¹).toMonoidHom).map
            (MulAut.conj s).toMonoidHom = Jf k
        rw [Subgroup.map_map]
        have hcomp : (MulAut.conj s).toMonoidHom.comp (MulAut.conj s⁻¹).toMonoidHom =
            MonoidHom.id _ := by
          ext x
          simp
        rw [hcomp, Subgroup.map_id]
      have hstep : (Jf k).map (MulAut.conj w).toMonoidHom =
          K.map (MulAut.conj (θ s)).toMonoidHom := by
        change (Jf k).map (MulAut.conj (θ s * s⁻¹)).toMonoidHom =
          K.map (MulAut.conj (θ s)).toMonoidHom
        rw [map_mul]
        rw [show (MulAut.conj (θ s) * MulAut.conj s⁻¹).toMonoidHom =
            (MulAut.conj (θ s)).toMonoidHom.comp (MulAut.conj s⁻¹).toMonoidHom from rfl,
          ← Subgroup.map_map]
      rw [hstep]
      have hcompθs : (MulAut.conj (θ s)).toMonoidHom =
          θ.toMonoidHom.comp ((MulAut.conj s).toMonoidHom.comp θ.symm.toMonoidHom) := by
        ext x
        change (MulAut.conj (θ s)) x = θ ((MulAut.conj s) (θ.symm x))
        rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
          MulEquiv.apply_symm_apply]
      rw [hcompθs, ← Subgroup.map_map, ← Subgroup.map_map, hθK', hKs]
      exact hfixΔ (Jf k) (hJΔ k)
    have hPK : ∀ k : Fin (m + 1),
        (linearFrameBlock F m k tail).map
            (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (2 * m + 1 + 1 + tail) F) =
          (Jf k).map (MulAut.conj c⁻¹).toMonoidHom := by
      intro k
      show (linearFrameBlock F m k tail).map
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (2 * m + 1 + 1 + tail) F) =
        ((linearFrameBlock F m k tail).map
          ((MulAut.conj c).toMonoidHom.comp
            (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj
              (2 * m + 1 + 1 + tail) F))).map (↑(MulAut.conj c⁻¹))
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply]
      group
    let U : SL(2 * m + 1 + 1 + tail, F) :=
      Classical.choose (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective
        (2 * m + 1 + 1 + tail) F (c⁻¹ * w * c))
    have hU : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj
        (2 * m + 1 + 1 + tail) F U = c⁻¹ * w * c :=
      Classical.choose_spec (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective
        (2 * m + 1 + 1 + tail) F (c⁻¹ * w * c))
    have hPN : ∀ k : Fin (m + 1),
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (2 * m + 1 + 1 + tail) F U ∈
          Subgroup.normalizer ((linearFrameBlock F m k tail).map
            (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj
              (2 * m + 1 + 1 + tail) F) : Set (linearProjFrame F m tail)) := by
      intro k
      rw [hU]
      exact mem_normalizer_conj_of_map_eq
        (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hwJ k)) (hPK k)
    have hUdiag : ((U : SL(2 * m + 1 + 1 + tail, F)) :
        Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) *
          Matrix.diagonal c' =
        Matrix.diagonal c' *
          ((U : SL(2 * m + 1 + 1 + tail, F)) :
            Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) := by
      refine commute_diagonal_of_commute_frameInvolution
        (CFSG.ABGLocalTools.two_ne_zero_of_odd_card hF) htail ?_ hconst
      intro k
      have hPNk := hPN k
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hPNk
      exact congrArg (fun x : SL(2 * m + 1 + 1 + tail, F) =>
        (x : Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F))
        (commute_frameInvolution_of_map_eq hF k U hPNk)
    have hAU : ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F) :
        Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) *
          ((U : SL(2 * m + 1 + 1 + tail, F)) :
            Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) =
        ((U : SL(2 * m + 1 + 1 + tail, F)) :
            Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) *
          ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F) :
            Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) := by
      rw [hdiag]
      exact hUdiag.symm
    have hfixU : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut
        (2 * m + 1 + 1 + tail) F A'
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj
            (2 * m + 1 + 1 + tail) F U) =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (2 * m + 1 + 1 + tail) F U := by
      have hAUG : A' * SpecialLinearGroup.toGL U = SpecialLinearGroup.toGL U * A' := by
        apply Units.ext
        simpa using hAU
      have hsl : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
          (2 * m + 1 + 1 + tail) F A' U = U := by
        apply SpecialLinearGroup.toGL_injective
        rw [toGL_slConjugation_frame, hAUG]
        group
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj, hsl]
    have h1 : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut
        (2 * m + 1 + 1 + tail) F A'
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj
            (2 * m + 1 + 1 + tail) F U) = c⁻¹ * θ w * c := by
      rw [hA'conj, hU]
      change (MulAut.conj c)⁻¹ (θ ((MulAut.conj c) (c⁻¹ * w * c))) = c⁻¹ * θ w * c
      rw [show (MulAut.conj c) (c⁻¹ * w * c) = w from by rw [MulAut.conj_apply]; group,
        show (MulAut.conj c)⁻¹ = MulAut.conj c⁻¹ from (map_inv (MulAut.conj) c).symm,
        MulAut.conj_apply, inv_inv]
    have hinner : c⁻¹ * θ w * c = c⁻¹ * w * c := by
      rw [← h1, hfixU, hU]
    have h2 : c * (c⁻¹ * θ w * c) * c⁻¹ = c * (c⁻¹ * w * c) * c⁻¹ :=
      congrArg (fun x => c * x * c⁻¹) hinner
    have h3 : c * (c⁻¹ * θ w * c) * c⁻¹ = θ w := by
      generalize hx : θ w = x
      show c * (c⁻¹ * x * c) * c⁻¹ = x
      group
    have h4 : c * (c⁻¹ * w * c) * c⁻¹ = w := by
      generalize hx : w = x
      show c * (c⁻¹ * x * c) * c⁻¹ = x
      group
    rw [h3, h4] at h2
    exact h2
  refine fixes_of_odd_of_mul_inv_mem (P := S)
    (N := S ⊓ CFSG.Open.signalizerFixedSubgroup θ) hS2 inf_le_left θ hθodd ?_ ?_
  · intro x hx
    exact hx.2
  · intro s hs
    refine ⟨?_, hθw s hs⟩
    have hθsS : θ s ∈ S := by
      rw [← hθS]
      exact Subgroup.mem_map_of_mem θ.toMonoidHom hs
    exact Subgroup.mul_mem S hθsS (Subgroup.inv_mem S hs)

theorem normSylowIn_projectiveSL_galois {r f : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hf : 1 ≤ f) {n : ℕ} (hn : 4 ≤ n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    NormSylowIn (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n (GaloisField r f))
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linearAutGroup n (GaloisField r f)) p := by
  have hpr : r.Prime := Fact.out
  have hFcard : Nat.card (GaloisField r f) = r ^ f := GaloisField.card r f (by omega)
  have hFodd : Odd (Nat.card (GaloisField r f)) := by
    rw [hFcard]
    exact (hpr.odd_of_ne_two hr2).pow
  obtain ⟨m, hm, hnm⟩ : ∃ m, 1 ≤ m ∧ (n = 2 * m + 1 + 1 ∨ n = 2 * m + 1 + 1 + 1) := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hk2 : 2 ≤ k := by omega
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      exact ⟨m, by omega, Or.inl (by omega)⟩
    · have hk2 : 2 ≤ k := by omega
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      exact ⟨m, by omega, Or.inr (by omega)⟩
  rcases hnm with hnm | hnm
  · subst hnm
    have hm : 1 ≤ m := by omega
    have hadm : CFSG.Open.StatedLieAdmissible .PSL (2 * m + 1 + 1) r f := by
      refine ⟨hpr, hf, by omega, ?_, ?_⟩
      · rintro h
        exact absurd (congrArg Prod.fst h) (by omega)
      · rintro h
        exact absurd (congrArg Prod.fst h) (by omega)
    have : Finite (linearProjFrame (GaloisField r f) m 0) := inferInstance
    have : IsSimpleGroup (linearProjFrame (GaloisField r f) m 0) :=
      CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by omega)
    have hmodel : CFSG.Blueprint.LieModel (linearProjFrame (GaloisField r f) m 0) .PSL
        (2 * m + 1 + 1) r f :=
      Or.inl ⟨by decide, hadm, GaloisField r f, inferInstance, inferInstance, hFcard,
        ⟨(CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
            (2 * m + 1 + 1) (GaloisField r f)).symm.trans
          (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
            (2 * m + 1 + 1) (GaloisField r f))⟩⟩
    have hframe : ∀ P : Sylow 2 (linearProjFrame (GaloisField r f) m 0),
        ∃ c : linearProjFrame (GaloisField r f) m 0,
          FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred (r ^ f))
              (linearProjFrame (GaloisField r f) m 0)
              (P : Subgroup (linearProjFrame (GaloisField r f) m 0)) =
            Set.range (fun k : Fin (m + 1) =>
              ((linearFrameBlock (GaloisField r f) m k 0).map
                (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj
                  (2 * m + 1 + 1 + 0) (GaloisField r f))).map
                (MulAut.conj c).toMonoidHom) := by
      intro P
      simpa using exists_full_coordinate_frame_funSet_psl_even (p := r) hr2 hm hadm hmodel
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj
          (2 * m + 1 + 1) (GaloisField r f))
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective _ _)
        (by
          rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.ker_proj]
          exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_le_center _ _) P
    have hperm : ∀ P : Sylow 2 (linearProjFrame (GaloisField r f) m 0),
        Nonempty ((conjPermHom (le_refl (conjSetStab
          (FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred (r ^ f))
            (linearProjFrame (GaloisField r f) m 0)
            (P : Subgroup (linearProjFrame (GaloisField r f) m 0)))))).range ≃*
          Equiv.Perm (Fin (m + 1))) := by
      intro P
      exact nonempty_equiv_perm_funSet_psl_even (p := r) hr2 hm hadm hmodel P
    simpa using normSylowIn_projectiveSL_frame (F := GaloisField r f) (q := r ^ f)
      (m := m) (tail := 0) hFodd hm (by omega) hp hp5 hframe hperm
  · subst hnm
    have hm : 1 ≤ m := by omega
    have hadm : CFSG.Open.StatedLieAdmissible .PSL (2 * m + 1 + 1 + 1) r f := by
      refine ⟨hpr, hf, by omega, ?_, ?_⟩
      · rintro h
        exact absurd (congrArg Prod.fst h) (by omega)
      · rintro h
        exact absurd (congrArg Prod.fst h) (by omega)
    have : Finite (linearProjFrame (GaloisField r f) m 1) := inferInstance
    have : IsSimpleGroup (linearProjFrame (GaloisField r f) m 1) :=
      CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (by omega)
    have hmodel : CFSG.Blueprint.LieModel (linearProjFrame (GaloisField r f) m 1) .PSL
        (2 * m + 1 + 1 + 1) r f :=
      Or.inl ⟨by decide, hadm, GaloisField r f, inferInstance, inferInstance, hFcard,
        ⟨(CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
            (2 * m + 1 + 1 + 1) (GaloisField r f)).symm.trans
          (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
            (2 * m + 1 + 1 + 1) (GaloisField r f))⟩⟩
    have hframe : ∀ P : Sylow 2 (linearProjFrame (GaloisField r f) m 1),
        ∃ c : linearProjFrame (GaloisField r f) m 1,
          FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred (r ^ f))
              (linearProjFrame (GaloisField r f) m 1)
              (P : Subgroup (linearProjFrame (GaloisField r f) m 1)) =
            Set.range (fun k : Fin (m + 1) =>
              ((linearFrameBlock (GaloisField r f) m k 1).map
                (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj
                  (2 * m + 1 + 1 + 1) (GaloisField r f))).map
                (MulAut.conj c).toMonoidHom) := by
      intro P
      exact exists_full_coordinate_frame_funSet_psl_odd (p := r) hr2 hm hadm hmodel
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj
          (2 * m + 1 + 1 + 1) (GaloisField r f))
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective _ _)
        (by
          rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.ker_proj]
          exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_le_center _ _) P
    have hperm : ∀ P : Sylow 2 (linearProjFrame (GaloisField r f) m 1),
        Nonempty ((conjPermHom (le_refl (conjSetStab
          (FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred (r ^ f))
            (linearProjFrame (GaloisField r f) m 1)
            (P : Subgroup (linearProjFrame (GaloisField r f) m 1)))))).range ≃*
          Equiv.Perm (Fin (m + 1))) := by
      intro P
      exact nonempty_equiv_perm_funSet_psl_odd (p := r) hr2 hm hadm hmodel P
    simpa using normSylowIn_projectiveSL_frame (F := GaloisField r f) (q := r ^ f)
      (m := m) (tail := 1) hFodd hm (by omega) hp hp5 hframe hperm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
