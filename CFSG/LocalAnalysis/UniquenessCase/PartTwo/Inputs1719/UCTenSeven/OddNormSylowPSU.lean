module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAutFrames
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddUnitaryCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddUnitaryFrameMatrix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddLinearFrameMatrix
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitPermutationAction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup Matrix
open scoped MatrixGroups
open CFSG.ComponentClassification.AS81.Sec2 (conjSetStab conjPermHom)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (unitaryFrameBlock unitaryFrameInvolution)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (exists_full_coordinate_frame_funSet_psu_even
  exists_full_coordinate_frame_funSet_psu_odd nonempty_equiv_perm_funSet_psu_even
  nonempty_equiv_perm_funSet_psu_odd)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.ClassicalInvolution.Phan (Su blockEmb)
open CFSG.ClassicalInvolution.Models (suMat suMat_mul)

private lemma exists_odd_orderOf_lift_unitary {H G' : Type*} [Group H] [Finite H] [Group G']
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

private lemma exists_sylow_map_of_isSylowOf_unitary {X H : Type} [Group X] [Group H] [Finite X]
    [Finite H] {J Q : Subgroup X} (e : ↥J ≃* H)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 2 Q J) :
    ∃ Q' : Sylow 2 H, ∀ A ∈ (Q' : Subgroup H),
      ∃ z : ↥J, (z : X) ∈ Q ∧ e.toMonoidHom z = A := by
  obtain ⟨T, hT⟩ := hQ
  let Q' : Sylow 2 H := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ'coe : (Q' : Subgroup H) = (T : Subgroup ↥J).map e.toMonoidHom :=
    Sylow.coe_mapSurjective e.surjective T
  refine ⟨Q', fun A hA => ?_⟩
  rw [hQ'coe] at hA
  obtain ⟨z, hzT, hzA⟩ := Subgroup.mem_map.mp hA
  exact ⟨z, hT ▸ Subgroup.mem_map_of_mem J.subtype hzT, hzA⟩

private lemma mem_normalizer_conj_of_map_eq_unitary {G : Type*} [Group G] {H K : Subgroup G}
    {c w : G} (hw : K.map (MulAut.conj w).toMonoidHom = K)
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

private lemma unitaryFrameBlock_map_mulEquiv_su_two {F : Type} [Field F] [Finite F]
    {p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2)
    {X : Type} [Group X] {m tail : ℕ} (hm : 1 ≤ m)
    (ψ : Su F p f (2 * m + 1 + 1 + tail) →* X)
    (hker : ψ.ker ≤ Subgroup.center (Su F p f (2 * m + 1 + 1 + tail)))
    (k : Fin (m + 1)) :
    ∃ e : ↥((unitaryFrameBlock F p f m k tail).map ψ) ≃* Su F p f 2,
      ∀ z, ψ (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
          (by have := k.isLt; omega) (e.toMonoidHom z)) = (z : X) := by
  have hι : Function.Injective
      (ψ.comp (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
        (by have := k.isLt; omega))) :=
    CFSG.ClassicalInvolution.Phan.comp_blockEmb_injective hF hker
      (by have := k.isLt; omega) (by omega) (by omega)
  have hrange : (ψ.comp (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
        (by have := k.isLt; omega))).range = (unitaryFrameBlock F p f m k tail).map ψ := by
    rw [MonoidHom.range_comp]
    rfl
  refine ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hι).symm, ?_⟩
  intro z
  have h := MonoidHom.ofInjective_apply (f := ψ.comp (blockEmb F p f (2 * m + 1 + 1 + tail) 2
      (2 * k.val) (by have := k.isLt; omega))) hι
    (x := (MonoidHom.ofInjective hι).symm ((MulEquiv.subgroupCongr hrange.symm) z))
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm.trans (MulEquiv.subgroupCongr_apply hrange.symm z)



private lemma funSet_map_mulEquiv_unitary {q : ℕ} {X : Type} [Group X] [Finite X]
    (α : X ≃* X) {S Kb : Subgroup X}
    (h : Kb ∈ FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q) X S) :
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

private lemma exists_unitaryFrameData
    {F : Type} [Field F] [Finite F] {p f m tail : ℕ} [Fact p.Prime] [CharP F p]
    (h : UnitaryFieldData p f F) (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hm : 1 ≤ m) (htail : tail ≤ 1) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ) {q : ℕ}
    (hframe : ∀ P : Sylow 2 (primeFormP h (idGram F (2 * m + 1 + 1 + tail))),
      ∃ c : primeFormP h (idGram F (2 * m + 1 + 1 + tail)),
        FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q)
            (primeFormP h (idGram F (2 * m + 1 + 1 + tail))) (P : Subgroup _) =
          Set.range (fun k : Fin (m + 1) =>
            ((unitaryFrameBlock F p f m k tail).map
              (unitaryCover h (2 * m + 1 + 1 + tail))).map (MulAut.conj c).toMonoidHom))
    (hperm : ∀ P : Sylow 2 (primeFormP h (idGram F (2 * m + 1 + 1 + tail))),
      Nonempty ((conjPermHom (le_refl (conjSetStab
        (FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q)
          (primeFormP h (idGram F (2 * m + 1 + 1 + tail))) (P : Subgroup _))))).range ≃*
        Equiv.Perm (Fin (m + 1))))
    (S : Subgroup (primeFormP h (idGram F (2 * m + 1 + 1 + tail))))
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤)
    (θ : MulAut (primeFormP h (idGram F (2 * m + 1 + 1 + tail))))
    (hθodd : Odd (orderOf θ)) (hθS : S.map θ.toMonoidHom = S)
    (hθp : ∀ x ∈ S, (θ ^ ℓ) x = x) :
    ∃ (c : primeFormP h (idGram F (2 * m + 1 + 1 + tail)))
      (Jf : Fin (m + 1) → Subgroup (primeFormP h (idGram F (2 * m + 1 + 1 + tail))))
      (Q : Fin (m + 1) → Sylow 2 (Su F p f 2)),
      (∀ k, Jf k = (unitaryFrameBlock F p f m k tail).map
        ((MulAut.conj c).toMonoidHom.comp (unitaryCover h (2 * m + 1 + 1 + tail)))) ∧
      (∀ k, Jf k ∈ FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q)
        (primeFormP h (idGram F (2 * m + 1 + 1 + tail))) S) ∧
      (S ≤ conjSetStab (FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q)
        (primeFormP h (idGram F (2 * m + 1 + 1 + tail))) S)) ∧
      (∀ J ∈ FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q)
        (primeFormP h (idGram F (2 * m + 1 + 1 + tail))) S, J.map θ.toMonoidHom = J) ∧
      (∀ (k : Fin (m + 1)) (A : Su F p f 2), A ∈ (Q k : Subgroup (Su F p f 2)) →
        ((MulAut.conj c).toMonoidHom.comp (unitaryCover h (2 * m + 1 + 1 + tail)))
            (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
              (by have := k.isLt; omega) A) ∈ S ⊓ Jf k) ∧
      (∀ k, ∀ x ∈ S ⊓ Jf k, θ x = x) ∧
      (∀ k, (unitaryFrameBlock F p f m k tail).map
          (unitaryCover h (2 * m + 1 + 1 + tail)) =
        (Jf k).map (MulAut.conj c⁻¹).toMonoidHom) := by
  have hSiff := (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := S) (K := ⊤)).mp hS
  let P : Sylow 2 (primeFormP h (idGram F (2 * m + 1 + 1 + tail))) :=
    hSiff.2.1.toSylow (by simpa [Subgroup.relIndex_top_right] using hSiff.2.2)
  have hPcoe : (P : Subgroup (primeFormP h (idGram F (2 * m + 1 + 1 + tail)))) = S :=
    IsPGroup.toSylow_coe _ _
  obtain ⟨c, hfull0⟩ := hframe P
  let ψc : Su F p f (2 * m + 1 + 1 + tail) →*
      primeFormP h (idGram F (2 * m + 1 + 1 + tail)) :=
    (MulAut.conj c).toMonoidHom.comp (unitaryCover h (2 * m + 1 + 1 + tail))
  let Δ : Set (Subgroup (primeFormP h (idGram F (2 * m + 1 + 1 + tail)))) :=
    FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q)
      (primeFormP h (idGram F (2 * m + 1 + 1 + tail))) S
  have hfull' : Δ = Set.range (fun k : Fin (m + 1) =>
      (unitaryFrameBlock F p f m k tail).map ψc) := by
    rw [show Δ = FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q)
        (primeFormP h (idGram F (2 * m + 1 + 1 + tail)))
        (P : Subgroup _) from by rw [hPcoe]]
    simpa [ψc, Subgroup.map_map] using hfull0
  have hconj : ∀ (g : primeFormP h (idGram F (2 * m + 1 + 1 + tail)))
      {K : Subgroup (primeFormP h (idGram F (2 * m + 1 + 1 + tail)))},
      CFSG.LocalAnalysis.UniquenessCase.fundPred q ⊤ K →
        CFSG.LocalAnalysis.UniquenessCase.fundPred q ⊤
          (K.map (MulAut.conj g).toMonoidHom) :=
    fun g K hK => CFSG.LocalAnalysis.UniquenessCase.isFundamentalOver_map_mulEquiv
      (MulAut.conj g) hK
  have hSΔ : S ≤ conjSetStab Δ := by
    have h := CFSG.LocalAnalysis.UniquenessCase.UC22.F14.sylow_le_conjSetStab_funSet hconj P
    rwa [hPcoe] at h
  obtain ⟨e⟩ := hperm P
  have hkerC : ψc.ker ≤ Subgroup.center (Su F p f (2 * m + 1 + 1 + tail)) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    apply ker_unitaryCover_le_center h (2 * m + 1 + 1 + tail)
    rw [MonoidHom.mem_ker]
    have hx' : (MulAut.conj c) (unitaryCover h (2 * m + 1 + 1 + tail) x) =
        (MulAut.conj c) 1 := by simpa [ψc] using hx
    exact (MulAut.conj c).injective hx'
  let Jf : Fin (m + 1) → Subgroup (primeFormP h (idGram F (2 * m + 1 + 1 + tail))) :=
    fun k => (unitaryFrameBlock F p f m k tail).map ψc
  have hinj : Function.Injective Jf := by
    intro i j heq
    by_contra hij
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.F14.map_ne_of_commuting_of_equiv_sl2
      ψc hkerC
      (Classical.choice (CFSG.LocalAnalysis.UniquenessCase.UC22.nonempty_equiv_sl2_unitaryFrameBlock
        (F := F) (p := p) (f := f) (m := m) (tail := tail) hF i))
      (fun a ha b hb => CFSG.LocalAnalysis.UniquenessCase.UC22.commutes_unitaryFrameBlock
        (tail := tail) hij a ha b hb) heq
  have hJΔ : ∀ k, Jf k ∈ Δ := fun k => hfull' ▸ ⟨k, rfl⟩
  have hθΔ : ∀ J ∈ Δ, J.map θ.toMonoidHom ∈ Δ := by
    intro J hJ
    have h := funSet_map_mulEquiv_unitary (α := θ) hJ
    rwa [show S.map θ.toMonoidHom = S from hθS] at h
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
  let bEquiv : ∀ k : Fin (m + 1), ↥(Jf k) ≃* Su F p f 2 := fun k =>
    Classical.choose (unitaryFrameBlock_map_mulEquiv_su_two hF hm ψc hkerC k)
  have hbEquiv : ∀ (k : Fin (m + 1)) (z : ↥(Jf k)),
      ψc (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
        (by have := k.isLt; omega) ((bEquiv k).toMonoidHom z)) =
        (z : primeFormP h (idGram F (2 * m + 1 + 1 + tail))) := fun k =>
    Classical.choose_spec (unitaryFrameBlock_map_mulEquiv_su_two hF hm ψc hkerC k)
  have hQex : ∀ k : Fin (m + 1), ∃ Q' : Sylow 2 (Su F p f 2),
      ∀ A ∈ (Q' : Subgroup (Su F p f 2)),
        ∃ z : ↥(Jf k),
          (z : primeFormP h (idGram F (2 * m + 1 + 1 + tail))) ∈ S ⊓ Jf k ∧
            (bEquiv k).toMonoidHom z = A :=
    fun k => exists_sylow_map_of_isSylowOf_unitary (bEquiv k) ((hJΔ k).2)
  choose Q hQ using hQex
  have hQmem : ∀ (k : Fin (m + 1)) (A : Su F p f 2),
      A ∈ (Q k : Subgroup (Su F p f 2)) →
        ψc (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
          (by have := k.isLt; omega) A) ∈ S ⊓ Jf k := by
    intro k A hA
    obtain ⟨z, hz, hzA⟩ := hQ k A hA
    rw [← hzA, hbEquiv k z]
    exact hz
  have hfixQ : ∀ k : Fin (m + 1), ∀ x ∈ S ⊓ Jf k, θ x = x := by
    intro k
    let e₂ : SL(2, CFSG.LieType.Steinberg.fixedSubfield F p f) ≃* Su F p f 2 :=
      Classical.choice (CFSG.ClassicalInvolution.Models.nonempty_sl2_mulEquiv_su_two hF)
    let eJ : ↥(Jf k) ≃* SL(2, CFSG.LieType.Steinberg.fixedSubfield F p f) :=
      (bEquiv k).trans e₂.symm
    refine fixes_of_isSylowOf_sl2
      (CFSG.ClassicalInvolution.Models.odd_natCard_fixedSubfield hF hp2)
      eJ ((hJΔ k).2) θ ?_ hℓ hℓ5 ?_
    · rw [Subgroup.map_inf_eq _ _ _ θ.injective, hθS, hfixΔ (Jf k) (hJΔ k)]
    · intro x hx
      exact hθp x hx.1
  have hPK : ∀ k : Fin (m + 1), (unitaryFrameBlock F p f m k tail).map
      (unitaryCover h (2 * m + 1 + 1 + tail)) =
      (Jf k).map (MulAut.conj c⁻¹).toMonoidHom := by
    intro k
    show (unitaryFrameBlock F p f m k tail).map
        (unitaryCover h (2 * m + 1 + 1 + tail)) =
      ((unitaryFrameBlock F p f m k tail).map ψc).map (MulAut.conj c⁻¹).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [ψc, MulAut.conj_apply]
    group
  exact ⟨c, Jf, Q, fun k => rfl, fun k => hPcoe ▸ hJΔ k, hSΔ, hfixΔ,
    hQmem, hfixQ, hPK⟩


private lemma exists_unitaryLift_blockScalar
    {F : Type} [Field F] [Finite F] {p f m tail : ℕ} [Fact p.Prime] [CharP F p]
    (h : UnitaryFieldData p f F) (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (htail : tail ≤ 1)
    {c : primeFormP h (idGram F (2 * m + 1 + 1 + tail))}
    {Jf : Fin (m + 1) → Subgroup (primeFormP h (idGram F (2 * m + 1 + 1 + tail)))}
    (S : Subgroup (primeFormP h (idGram F (2 * m + 1 + 1 + tail))))
    {Q : Fin (m + 1) → Sylow 2 (Su F p f 2)}
    (hQmem : ∀ (k : Fin (m + 1)) (A : Su F p f 2), A ∈ (Q k : Subgroup (Su F p f 2)) →
      ((MulAut.conj c).toMonoidHom.comp (unitaryCover h (2 * m + 1 + 1 + tail)))
        (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
          (by have := k.isLt; omega) A) ∈ S ⊓ Jf k)
    {θ : MulAut (primeFormP h (idGram F (2 * m + 1 + 1 + tail)))}
    (hfixQ : ∀ k, ∀ x ∈ S ⊓ Jf k, θ x = x)
    (hθD : θ ∈ primeFormD h (idGram F (2 * m + 1 + 1 + tail)))
    (hθodd : Odd (orderOf θ)) :
    ∃ (A' : primeFormUnitary h (idGram F (2 * m + 1 + 1 + tail)))
      (c' : Fin (2 * m + 1 + 1 + tail) → F),
      primeFormConjHom h (idGram F (2 * m + 1 + 1 + tail)) A' =
        (MulAut.conj c)⁻¹ * θ * MulAut.conj c ∧
      Odd (orderOf ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F))) ∧
      ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F) :
        Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) =
        Matrix.diagonal c' ∧
      (∀ a b : Fin (2 * m + 1 + 1 + tail), a.val / 2 = b.val / 2 → c' a = c' b) := by
  let ψc : Su F p f (2 * m + 1 + 1 + tail) →*
      primeFormP h (idGram F (2 * m + 1 + 1 + tail)) :=
    (MulAut.conj c).toMonoidHom.comp (unitaryCover h (2 * m + 1 + 1 + tail))
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp hθD
  obtain ⟨l, hAodd, hAeq⟩ := exists_odd_orderOf_lift_unitary
    (primeFormConjHom h (idGram F (2 * m + 1 + 1 + tail))) A (by rwa [hA])
  let A₁ : primeFormUnitary h (idGram F (2 * m + 1 + 1 + tail)) := A ^ l
  have hA₁odd : Odd (orderOf A₁) := hAodd
  have hA₁conj : primeFormConjHom h (idGram F (2 * m + 1 + 1 + tail)) A₁ = θ := by
    change primeFormConjHom h (idGram F (2 * m + 1 + 1 + tail)) (A ^ l) = θ
    rw [hAeq, hA]
  obtain ⟨C, hC⟩ := unitaryCover_surjective h (2 * m + 1 + 1 + tail) c
  let C' : primeFormUnitary h (idGram F (2 * m + 1 + 1 + tail)) :=
    ⟨(C : GL (Fin (2 * m + 1 + 1 + tail)) F), coe_mem_primeFormUnitary h C⟩
  have hC' : primeFormConjHom h (idGram F (2 * m + 1 + 1 + tail)) C' = MulAut.conj c := by
    change primeFormConjHom h (idGram F (2 * m + 1 + 1 + tail))
      ⟨(C : GL (Fin (2 * m + 1 + 1 + tail)) F), coe_mem_primeFormUnitary h C⟩ =
      MulAut.conj c
    rw [primeFormConjHom_coe h C, hC]
  let A' : primeFormUnitary h (idGram F (2 * m + 1 + 1 + tail)) := C'⁻¹ * A₁ * C'
  have hA'conj : primeFormConjHom h (idGram F (2 * m + 1 + 1 + tail)) A' =
      (MulAut.conj c)⁻¹ * θ * MulAut.conj c := by
    change primeFormConjHom h (idGram F (2 * m + 1 + 1 + tail)) (C'⁻¹ * A₁ * C') = _
    rw [map_mul, map_mul, map_inv, hA₁conj, hC']
  have hA'odd : Odd (orderOf ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F))) := by
    have hA'eq : ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F)) =
        MulAut.conj ((C' : GL (Fin (2 * m + 1 + 1 + tail)) F))⁻¹
          ((A₁ : GL (Fin (2 * m + 1 + 1 + tail)) F)) := rfl
    change Odd (orderOf ((MulAut.conj
      ((C' : GL (Fin (2 * m + 1 + 1 + tail)) F))⁻¹).toMonoidHom
        ((A₁ : GL (Fin (2 * m + 1 + 1 + tail)) F))))
    rw [orderOf_injective
      (MulAut.conj ((C' : GL (Fin (2 * m + 1 + 1 + tail)) F))⁻¹).toMonoidHom
      (MulAut.conj _).injective ((A₁ : GL (Fin (2 * m + 1 + 1 + tail)) F)),
      Subgroup.orderOf_coe]
    exact hA₁odd
  have hcommGL : ∀ (k : Fin (m + 1)) (B : Su F p f 2),
      B ∈ (Q k : Subgroup (Su F p f 2)) →
      Commute ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F))
        (((blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
          (by have := k.isLt; omega) B : Su F p f (2 * m + 1 + 1 + tail)) :
            GL (Fin (2 * m + 1 + 1 + tail)) F)) := by
    intro k B hB
    let g : Su F p f (2 * m + 1 + 1 + tail) :=
      blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val) (by have := k.isLt; omega) B
    let b : GL (Fin (2 * m + 1 + 1 + tail)) F := (g : GL (Fin (2 * m + 1 + 1 + tail)) F)
    obtain ⟨n, hn⟩ := (Q k).isPGroup' ⟨B, hB⟩
    have hBpow : B ^ 2 ^ n = 1 := by
      have h := congrArg (fun x : ↥(Q k) => (x : Su F p f 2)) hn
      simpa using h
    have hgpow : g ^ 2 ^ n = 1 := by
      change (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
        (by have := k.isLt; omega) B) ^ 2 ^ n = 1
      rw [← map_pow, hBpow, map_one]
    have hbpow : b ^ 2 ^ n = 1 := by
      have h := congrArg (fun x : Su F p f (2 * m + 1 + 1 + tail) =>
        (x : GL (Fin (2 * m + 1 + 1 + tail)) F)) hgpow
      simpa [b] using h
    have hz : ψc g ∈ S ⊓ Jf k := hQmem k B hB
    have hθz : θ (ψc g) = ψc g := hfixQ k _ hz
    have hconj : primeFormConjHom h (idGram F (2 * m + 1 + 1 + tail)) A'
        (unitaryCover h (2 * m + 1 + 1 + tail) g) =
        unitaryCover h (2 * m + 1 + 1 + tail) g := by
      rw [hA'conj]
      change (MulAut.conj c)⁻¹ (θ ((MulAut.conj c)
        (unitaryCover h (2 * m + 1 + 1 + tail) g))) =
        unitaryCover h (2 * m + 1 + 1 + tail) g
      rw [show (MulAut.conj c) (unitaryCover h (2 * m + 1 + 1 + tail) g) = ψc g from rfl,
        hθz]
      exact (MulEquiv.symm_apply_apply (MulAut.conj c) _)
    let gA : Su F p f (2 * m + 1 + 1 + tail) :=
      ⟨(A' : GL (Fin (2 * m + 1 + 1 + tail)) F) * (g : GL (Fin (2 * m + 1 + 1 + tail)) F) *
          ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F))⁻¹, conj_mem_SUid h A' g⟩
    have hU : unitaryCover h (2 * m + 1 + 1 + tail) gA =
        unitaryCover h (2 * m + 1 + 1 + tail) g := by
      rw [← primeFormConjHom_unitaryCover h A' g, hconj]
    have hc : (((A' : GL (Fin (2 * m + 1 + 1 + tail)) F) * b *
        ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F))⁻¹)⁻¹ * b) ∈
        Subgroup.center (GL (Fin (2 * m + 1 + 1 + tail)) F) := by
      have h := coe_mem_center_of_unitaryCover_eq h hU
      simpa [gA, b] using h
    have hd : (A' : GL (Fin (2 * m + 1 + 1 + tail)) F) * b *
        ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F))⁻¹ * b⁻¹ ∈
        Subgroup.center (GL (Fin (2 * m + 1 + 1 + tail)) F) := by
      have hinv : ((((A' : GL (Fin (2 * m + 1 + 1 + tail)) F) * b *
          ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F))⁻¹)⁻¹ * b))⁻¹ ∈
          Subgroup.center (GL (Fin (2 * m + 1 + 1 + tail)) F) := Subgroup.inv_mem _ hc
      have hconj := (inferInstance : (Subgroup.center
        (GL (Fin (2 * m + 1 + 1 + tail)) F)).Normal).conj_mem
        ((((A' : GL (Fin (2 * m + 1 + 1 + tail)) F) * b *
          ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F))⁻¹)⁻¹ * b))⁻¹ hinv b
      convert hconj using 1
      group
    exact commute_of_odd_of_pow_two_pow_of_mem_center hA'odd hbpow hd
  have hAmat : ∀ (k : Fin (m + 1)) (B : Su F p f 2),
      B ∈ (Q k : Subgroup (Su F p f 2)) →
      ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F) :
        Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) *
        suMat (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
          (by have := k.isLt; omega) B) =
      suMat (blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
          (by have := k.isLt; omega) B) *
        ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F) :
          Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) := by
    intro k B hB
    have h : (((A' : GL (Fin (2 * m + 1 + 1 + tail)) F) *
        ((blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
          (by have := k.isLt; omega) B : Su F p f (2 * m + 1 + 1 + tail)) :
            GL (Fin (2 * m + 1 + 1 + tail)) F) : GL (Fin (2 * m + 1 + 1 + tail)) F) :
        Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) =
        ((((blockEmb F p f (2 * m + 1 + 1 + tail) 2 (2 * k.val)
          (by have := k.isLt; omega) B : Su F p f (2 * m + 1 + 1 + tail)) :
            GL (Fin (2 * m + 1 + 1 + tail)) F) * A' : GL (Fin (2 * m + 1 + 1 + tail)) F) :
        Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) := by
      rw [(hcommGL k B hB).eq]
    simpa [suMat] using h
  obtain ⟨c', hdiag, hconst⟩ :=
    exists_blockScalar_of_commute_unitaryFrame_sylow (F := F) (p := p) (f := f)
      (m := m) (tail := tail) hF hp2 htail Q hAmat
  exact ⟨A', c', hA'conj, hA'odd, hdiag, hconst⟩


private lemma theta_fixes_mul_inv_unitary
    {F : Type} [Field F] [Finite F] {p f m tail : ℕ} [Fact p.Prime] [CharP F p]
    (h : UnitaryFieldData p f F) (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (htail : tail ≤ 1) {q : ℕ}
    {c : primeFormP h (idGram F (2 * m + 1 + 1 + tail))}
    (S : Subgroup (primeFormP h (idGram F (2 * m + 1 + 1 + tail))))
    {Jf : Fin (m + 1) → Subgroup (primeFormP h (idGram F (2 * m + 1 + 1 + tail)))}
    (hSΔ : S ≤ conjSetStab (FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q)
      (primeFormP h (idGram F (2 * m + 1 + 1 + tail))) S))
    (hJΔ : ∀ k, Jf k ∈ FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q)
      (primeFormP h (idGram F (2 * m + 1 + 1 + tail))) S)
    {θ : MulAut (primeFormP h (idGram F (2 * m + 1 + 1 + tail)))}
    (hfixΔ : ∀ J ∈ FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q)
      (primeFormP h (idGram F (2 * m + 1 + 1 + tail))) S, J.map θ.toMonoidHom = J)
    (hPK : ∀ k, (unitaryFrameBlock F p f m k tail).map
        (unitaryCover h (2 * m + 1 + 1 + tail)) =
      (Jf k).map (MulAut.conj c⁻¹).toMonoidHom)
    {A' : primeFormUnitary h (idGram F (2 * m + 1 + 1 + tail))}
    (hA'conj : primeFormConjHom h (idGram F (2 * m + 1 + 1 + tail)) A' =
      (MulAut.conj c)⁻¹ * θ * MulAut.conj c)
    {c' : Fin (2 * m + 1 + 1 + tail) → F}
    (hdiag : ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F) :
      Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) =
      Matrix.diagonal c')
    (hconst : ∀ a b : Fin (2 * m + 1 + 1 + tail), a.val / 2 = b.val / 2 → c' a = c' b) :
    ∀ s ∈ S, θ (θ s * s⁻¹) = θ s * s⁻¹ := by
  let X := primeFormP h (idGram F (2 * m + 1 + 1 + tail))
  let Δ : Set (Subgroup X) := FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q) X S
  intro s hs
  let w : X := θ s * s⁻¹
  have hwJ : ∀ k : Fin (m + 1),
      w ∈ Subgroup.normalizer ((Jf k : Subgroup X) : Set X) := by
    intro k
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change (Jf k).map (MulAut.conj w).toMonoidHom = Jf k
    let K : Subgroup X := (Jf k).map (MulAut.conj s⁻¹).toMonoidHom
    have hKΔ : K ∈ Δ :=
      ((CFSG.ComponentClassification.AS81.Sec2.mem_conjSetStab.mp (hSΔ hs) (Jf k)).mp (hJΔ k))
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
  obtain ⟨U, hU⟩ : ∃ U : Su F p f (2 * m + 1 + 1 + tail),
      unitaryCover h (2 * m + 1 + 1 + tail) U = c⁻¹ * w * c :=
    unitaryCover_surjective h (2 * m + 1 + 1 + tail) (c⁻¹ * w * c)
  have hPN : ∀ k : Fin (m + 1),
      unitaryCover h (2 * m + 1 + 1 + tail) U ∈
        Subgroup.normalizer (((unitaryFrameBlock F p f m k tail).map
          (unitaryCover h (2 * m + 1 + 1 + tail))) : Set X) := by
    intro k
    rw [hU]
    exact mem_normalizer_conj_of_map_eq_unitary
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hwJ k)) (hPK k)
  have hUdiag : suMat U * Matrix.diagonal c' = Matrix.diagonal c' * suMat U := by
    refine commute_diagonal_of_commute_frameInvolution
      (CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2) htail ?_ hconst
    intro k
    have hcomm := commute_unitaryFrameInvolution_of_map_eq hF hp2
      (unitaryCover h (2 * m + 1 + 1 + tail))
      (ker_unitaryCover_le_center h (2 * m + 1 + 1 + tail)) k U
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPN k))
    have hm := congrArg suMat hcomm
    simpa [suMat_mul, ← coe_linearFrameInvolution_eq_suMat] using hm
  have hAU : ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F) :
      Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) *
        suMat U = suMat U *
      ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F) :
        Matrix (Fin (2 * m + 1 + 1 + tail)) (Fin (2 * m + 1 + 1 + tail)) F) := by
    rw [hdiag]
    exact hUdiag.symm
  have hAUG : (A' : GL (Fin (2 * m + 1 + 1 + tail)) F) *
      (U : GL (Fin (2 * m + 1 + 1 + tail)) F) =
      (U : GL (Fin (2 * m + 1 + 1 + tail)) F) *
        (A' : GL (Fin (2 * m + 1 + 1 + tail)) F) := by
    apply Units.ext
    simpa [suMat] using hAU
  have hsl : (⟨(A' : GL (Fin (2 * m + 1 + 1 + tail)) F) *
      (U : GL (Fin (2 * m + 1 + 1 + tail)) F) *
      ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F))⁻¹, conj_mem_SUid h A' U⟩ :
        Su F p f (2 * m + 1 + 1 + tail)) = U := by
    apply Subtype.ext
    show (A' : GL (Fin (2 * m + 1 + 1 + tail)) F) *
      (U : GL (Fin (2 * m + 1 + 1 + tail)) F) *
      ((A' : GL (Fin (2 * m + 1 + 1 + tail)) F))⁻¹ =
      (U : GL (Fin (2 * m + 1 + 1 + tail)) F)
    rw [hAUG]
    group
  have hfixU : primeFormConjHom h (idGram F (2 * m + 1 + 1 + tail)) A'
      (unitaryCover h (2 * m + 1 + 1 + tail) U) =
      unitaryCover h (2 * m + 1 + 1 + tail) U := by
    rw [primeFormConjHom_unitaryCover h A' U, hsl]
  have h1 : primeFormConjHom h (idGram F (2 * m + 1 + 1 + tail)) A'
      (unitaryCover h (2 * m + 1 + 1 + tail) U) = c⁻¹ * θ w * c := by
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


private theorem normSylowIn_primeFormP_frame
    {F : Type} [Field F] [Finite F] {p f m tail : ℕ} [Fact p.Prime] [CharP F p]
    (h : UnitaryFieldData p f F) (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hm : 1 ≤ m) (htail : tail ≤ 1) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ) {q : ℕ}
    (hframe : ∀ P : Sylow 2 (primeFormP h (idGram F (2 * m + 1 + 1 + tail))),
      ∃ c : primeFormP h (idGram F (2 * m + 1 + 1 + tail)),
        FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q)
            (primeFormP h (idGram F (2 * m + 1 + 1 + tail))) (P : Subgroup _) =
          Set.range (fun k : Fin (m + 1) =>
            ((unitaryFrameBlock F p f m k tail).map
              (unitaryCover h (2 * m + 1 + 1 + tail))).map (MulAut.conj c).toMonoidHom))
    (hperm : ∀ P : Sylow 2 (primeFormP h (idGram F (2 * m + 1 + 1 + tail))),
      Nonempty ((conjPermHom (le_refl (conjSetStab
        (FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred q)
          (primeFormP h (idGram F (2 * m + 1 + 1 + tail))) (P : Subgroup _))))).range ≃*
        Equiv.Perm (Fin (m + 1)))) :
    NormSylowIn (primeFormP h (idGram F (2 * m + 1 + 1 + tail)))
      (primeFormD h (idGram F (2 * m + 1 + 1 + tail))) ℓ := by
  refine normSylowIn_of_odd hℓ (by omega) ?_
  intro S hS θ hθD hθodd hθS hθp
  obtain ⟨c, Jf, Q, -, hJΔ, hSΔ, hfixΔ, hQmem, hfixQ, hPK⟩ :=
    exists_unitaryFrameData h hF hp2 hm htail hℓ hℓ5 hframe hperm S hS θ hθodd hθS hθp
  obtain ⟨A', c', hA'conj, -, hdiag, hconst⟩ :=
    exists_unitaryLift_blockScalar h hF hp2 htail S hQmem hfixQ hθD hθodd
  have hθw := theta_fixes_mul_inv_unitary h hF hp2 htail S hSΔ hJΔ hfixΔ hPK
    hA'conj hdiag hconst
  have hSiff := (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := S) (K := ⊤)).mp hS
  refine fixes_of_odd_of_mul_inv_mem (P := S)
    (N := S ⊓ CFSG.Open.signalizerFixedSubgroup θ) hSiff.2.1 inf_le_left θ hθodd ?_ ?_
  · intro x hx
    exact hx.2
  · intro s hs
    refine ⟨?_, hθw s hs⟩
    have hθsS : θ s ∈ S := by
      rw [← hθS]
      exact Subgroup.mem_map_of_mem θ.toMonoidHom hs
    exact Subgroup.mul_mem S hθsS (Subgroup.inv_mem S hs)

theorem normSylowIn_primeFormP_galois {r f : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (hf : 1 ≤ f)
    (h : UnitaryFieldData r f (GaloisField r (2 * f))) {n : ℕ} (hn : 4 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    NormSylowIn (primeFormP h (idGram (GaloisField r (2 * f)) n))
      (primeFormD h (idGram (GaloisField r (2 * f)) n)) p := by
  have hpr : r.Prime := Fact.out
  have hF : Nat.card (GaloisField r (2 * f)) = (r ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul r f hf
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
    have hadm : CFSG.Open.StatedLieAdmissible .PSU (2 * m + 1 + 1) r f := by
      refine ⟨hpr, hf, by omega, ?_⟩
      rintro h
      exact absurd (congrArg Prod.fst h) (by omega)
    have : Finite (primeFormP h (idGram (GaloisField r (2 * f)) (2 * m + 1 + 1))) :=
      inferInstance
    have : IsSimpleGroup (primeFormP h (idGram (GaloisField r (2 * f)) (2 * m + 1 + 1))) :=
      isSimpleGroup_primeFormP_idGram h (by omega) (by rintro ⟨h3, -⟩; omega)
    have hmodel : CFSG.Blueprint.LieModel
        (primeFormP h (idGram (GaloisField r (2 * f)) (2 * m + 1 + 1)))
        .PSU (2 * m + 1 + 1) r f :=
      lieModel_primeFormP_idGram h (by omega) (by rintro ⟨h3, -⟩; omega)
    have hframe : ∀ P : Sylow 2
        (primeFormP h (idGram (GaloisField r (2 * f)) (2 * m + 1 + 1))),
        ∃ c : primeFormP h (idGram (GaloisField r (2 * f)) (2 * m + 1 + 1)),
          FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred (r ^ f))
              (primeFormP h (idGram (GaloisField r (2 * f)) (2 * m + 1 + 1))) (P : Subgroup _) =
            Set.range (fun k : Fin (m + 1) =>
              ((unitaryFrameBlock (GaloisField r (2 * f)) r f m k 0).map
                (unitaryCover h (2 * m + 1 + 1))).map (MulAut.conj c).toMonoidHom) := by
      intro P
      obtain ⟨eU, heU⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hr2 hadm
      exact exists_full_coordinate_frame_funSet_psu_even (p := r) hr2 hm hadm hmodel eU heU
        (unitaryCover h (2 * m + 1 + 1)) (unitaryCover_surjective h _)
        (ker_unitaryCover_le_center h _) P
    have hperm : ∀ P : Sylow 2
        (primeFormP h (idGram (GaloisField r (2 * f)) (2 * m + 1 + 1))),
        Nonempty ((conjPermHom (le_refl (conjSetStab
          (FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred (r ^ f))
            (primeFormP h (idGram (GaloisField r (2 * f)) (2 * m + 1 + 1)))
            (P : Subgroup _))))).range ≃* Equiv.Perm (Fin (m + 1))) := by
      intro P
      exact nonempty_equiv_perm_funSet_psu_even (p := r) hr2 hm hadm hmodel P
    simpa using normSylowIn_primeFormP_frame (F := GaloisField r (2 * f)) (p := r)
      (f := f) (m := m) (tail := 0) h hF hr2 hm (by omega) hp hp5 (q := r ^ f) hframe hperm
  · subst hnm
    have hm : 1 ≤ m := by omega
    have hadm : CFSG.Open.StatedLieAdmissible .PSU (2 * m + 1 + 1 + 1) r f := by
      refine ⟨hpr, hf, by omega, ?_⟩
      rintro h
      exact absurd (congrArg Prod.fst h) (by omega)
    have : Finite (primeFormP h (idGram (GaloisField r (2 * f)) (2 * m + 1 + 1 + 1))) :=
      inferInstance
    have : IsSimpleGroup
        (primeFormP h (idGram (GaloisField r (2 * f)) (2 * m + 1 + 1 + 1))) :=
      isSimpleGroup_primeFormP_idGram h (by omega) (by rintro ⟨h3, -⟩; omega)
    have hmodel : CFSG.Blueprint.LieModel
        (primeFormP h (idGram (GaloisField r (2 * f)) (2 * m + 1 + 1 + 1)))
        .PSU (2 * m + 1 + 1 + 1) r f :=
      lieModel_primeFormP_idGram h (by omega) (by rintro ⟨h3, -⟩; omega)
    have hframe : ∀ P : Sylow 2
        (primeFormP h (idGram (GaloisField r (2 * f)) (2 * m + 1 + 1 + 1))),
        ∃ c : primeFormP h (idGram (GaloisField r (2 * f)) (2 * m + 1 + 1 + 1)),
          FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred (r ^ f))
              (primeFormP h (idGram (GaloisField r (2 * f)) (2 * m + 1 + 1 + 1)))
              (P : Subgroup _) =
            Set.range (fun k : Fin (m + 1) =>
              ((unitaryFrameBlock (GaloisField r (2 * f)) r f m k 1).map
                (unitaryCover h (2 * m + 1 + 1 + 1))).map (MulAut.conj c).toMonoidHom) := by
      intro P
      obtain ⟨eU, heU⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hr2 hadm
      exact exists_full_coordinate_frame_funSet_psu_odd (p := r) hr2 hm hadm hmodel eU heU
        (unitaryCover h (2 * m + 1 + 1 + 1)) (unitaryCover_surjective h _)
        (ker_unitaryCover_le_center h _) P
    have hperm : ∀ P : Sylow 2
        (primeFormP h (idGram (GaloisField r (2 * f)) (2 * m + 1 + 1 + 1))),
        Nonempty ((conjPermHom (le_refl (conjSetStab
          (FunSet (CFSG.LocalAnalysis.UniquenessCase.fundPred (r ^ f))
            (primeFormP h (idGram (GaloisField r (2 * f)) (2 * m + 1 + 1 + 1)))
            (P : Subgroup _))))).range ≃* Equiv.Perm (Fin (m + 1))) := by
      intro P
      exact nonempty_equiv_perm_funSet_psu_odd (p := r) hr2 hm hadm hmodel P
    simpa using normSylowIn_primeFormP_frame (F := GaloisField r (2 * f)) (p := r)
      (f := f) (m := m) (tail := 1) h hF hr2 hm (by omega) hp hp5 (q := r ^ f) hframe hperm


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
