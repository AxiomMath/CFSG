module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derDefs
import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndSmall
import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeOrthSpOne
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofLift
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuasisimpleOfCentralExtension

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l48gQ_map_Q {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    {A : Subgroup L'} {C S : Subgroup R} {Q : Subgroup L'}
    (hQ : Q = A ⊓ S.comap ψ) (hmapA : A.map ψ = C) (hSC : S ≤ C) :
    Q.map ψ = S := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [hQ] at hx
    rw [Subgroup.mem_comap]
    exact hx.2
  · intro s hs
    have hsC : s ∈ C := hSC hs
    rw [← hmapA, Subgroup.mem_map] at hsC
    obtain ⟨a, ha, haeq⟩ := hsC
    refine Subgroup.mem_map.mpr ⟨a, ?_, haeq⟩
    rw [hQ]
    exact ⟨ha, Subgroup.mem_comap.mpr (by rw [haeq]; exact hs)⟩

private lemma l48gQ_split {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    {A : Subgroup L'} {S : Subgroup R} {Q : Subgroup L'}
    (hQ : Q = A ⊓ S.comap ψ) (hmapQ : Q.map ψ = S) (hperf : ⁅S, S⁆ = S) :
    Q = ⁅Q, Q⁆ ⊔ (Q ⊓ ψ.ker) := by
  apply le_antisymm
  · intro q hq
    have hqS : ψ q ∈ S := by
      have h := hq
      rw [hQ] at h
      exact h.2
    have hq_image : ψ q ∈ (⁅Q, Q⁆).map ψ := by
      rw [Subgroup.map_commutator, hmapQ, hperf]
      exact hqS
    rw [Subgroup.mem_map] at hq_image
    obtain ⟨k, hk, hkeq⟩ := hq_image
    have hz : k⁻¹ * q ∈ Q ⊓ ψ.ker := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact mul_mem (inv_mem ((Subgroup.commutator_le_self Q) hk)) hq
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hkeq, inv_mul_cancel]
    simpa only [mul_inv_cancel_left] using Subgroup.mul_mem_sup hk hz
  · exact sup_le (Subgroup.commutator_le_self Q) inf_le_left

private lemma l48gQ_perfect {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hker : ψ.ker ≤ Subgroup.center L') {Q : Subgroup L'}
    (hQle : Q ≤ ⁅Q, Q⁆ ⊔ ψ.ker) :
    ⁅⁅Q, Q⁆, ⁅Q, Q⁆⁆ = ⁅Q, Q⁆ := by
  have hcomm_eq : ⁅⁅Q, Q⁆ ⊔ ψ.ker, ⁅Q, Q⁆ ⊔ ψ.ker⁆ = ⁅⁅Q, Q⁆, ⁅Q, Q⁆⁆ := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_sup_of_normal_right] at ha hb
      obtain ⟨k₁, hk₁, z₁, hz₁, rfl⟩ := ha
      obtain ⟨k₂, hk₂, z₂, hz₂, rfl⟩ := hb
      rw [CFSG.StandardType.Line63.H5.commutatorElement_mul_mul_central
        (hker hz₁) (hker hz₂)]
      exact Subgroup.commutator_mem_commutator hk₁ hk₂
    · exact Subgroup.commutator_mono le_sup_left le_sup_left
  have hJle : ⁅Q, Q⁆ ≤ ⁅⁅Q, Q⁆, ⁅Q, Q⁆⁆ :=
    calc ⁅Q, Q⁆ ≤ ⁅⁅Q, Q⁆ ⊔ ψ.ker, ⁅Q, Q⁆ ⊔ ψ.ker⁆ :=
          Subgroup.commutator_mono hQle hQle
      _ = ⁅⁅Q, Q⁆, ⁅Q, Q⁆⁆ := hcomm_eq
  exact le_antisymm (Subgroup.commutator_le_self ⁅Q, Q⁆) hJle

private lemma l48gQ_normal {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    {A : Subgroup L'} {C S : Subgroup R} {Q : Subgroup L'}
    (hQ : Q = A ⊓ S.comap ψ) (hmapA : A.map ψ = C)
    (hnorm : ∀ c ∈ C, ∀ s ∈ S, c * s * c⁻¹ ∈ S) :
    ∀ h ∈ A, ∀ d ∈ ⁅Q, Q⁆, h * d * h⁻¹ ∈ ⁅Q, Q⁆ := by
  intro h hh d hd
  have hconjQ : ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := by
    intro q hq
    rw [hQ] at hq ⊢
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact mul_mem (mul_mem hh hq.1) (inv_mem hh)
    · rw [Subgroup.mem_comap]
      have hqS : ψ q ∈ S := hq.2
      have hhC : ψ h ∈ C := by
        rw [← hmapA]
        exact Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
      have hkey := hnorm (ψ h) hhC (ψ q) hqS
      have hval : ψ (h * q * h⁻¹) = ψ h * ψ q * (ψ h)⁻¹ := by
        simp only [map_mul, map_inv]
      rwa [hval]
  have hmapQle : Q.map (MulAut.conj h).toMonoidHom ≤ Q := by
    rintro x ⟨y, hy, rfl⟩
    change (MulAut.conj h) y ∈ Q
    rw [MulAut.conj_apply]
    exact hconjQ y hy
  have hmapJ : (⁅Q, Q⁆).map (MulAut.conj h).toMonoidHom ≤ ⁅Q, Q⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hmapQle hmapQle
  have hd' : (MulAut.conj h) d ∈ ⁅Q, Q⁆ := hmapJ ⟨d, hd, rfl⟩
  rwa [MulAut.conj_apply] at hd'

private lemma l48gQ_quasisimple {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hker : ψ.ker ≤ Subgroup.center L') {Q : Subgroup L'} {S : Subgroup R}
    (hJmap : (⁅Q, Q⁆).map ψ = S) (hJperf : ⁅⁅Q, Q⁆, ⁅Q, Q⁆⁆ = ⁅Q, Q⁆)
    (hsimple : IsSimpleGroup ↥S) :
    CFSG.IsQuasisimple ↥(⁅Q, Q⁆) := by
  let f0 : ↥(⁅Q, Q⁆) →* ↥S := (ψ.comp (⁅Q, Q⁆).subtype).codRestrict S (fun x => by
    have hx : ψ (x : L') ∈ (⁅Q, Q⁆).map ψ := ⟨x, x.2, rfl⟩
    rwa [hJmap] at hx)
  have hf0_apply : ∀ x : ↥(⁅Q, Q⁆), ((f0 x : ↥S) : R) = ψ (x : L') := fun x => rfl
  have hf0 : Function.Surjective f0 := fun y => by
    have hy : (y : R) ∈ (⁅Q, Q⁆).map ψ := by rw [hJmap]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  haveI : Nontrivial ↥S := hsimple.toNontrivial
  have hJnontrivial : Nontrivial ↥(⁅Q, Q⁆) := Function.Surjective.nontrivial hf0
  have hJperfect : Group.IsPerfect ↥(⁅Q, Q⁆) := Subgroup.isPerfect_iff.mpr hJperf
  have hker0 : f0.ker ≤ Subgroup.center ↥(⁅Q, Q⁆) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx1 : ψ (x : L') = 1 := by
      have hx' := hx
      rw [MonoidHom.mem_ker] at hx'
      have hval := congrArg Subtype.val hx'
      rwa [hf0_apply x] at hval
    have hxcenter : (x : L') ∈ Subgroup.center L' := hker (MonoidHom.mem_ker.mpr hx1)
    exact Subgroup.mem_center_iff.mp hxcenter (y : L')
  have hgw := CFSG.GorensteinWalter.isQuasisimple_of_perfect_of_ker_le_center_of_surjective_simple
    f0 hf0 hJnontrivial hJperfect hsimple hker0
  have hquotSimple : IsSimpleGroup (↥(⁅Q, Q⁆) ⧸ Subgroup.center ↥(⁅Q, Q⁆)) := hgw.2.2
  haveI : Nontrivial (↥(⁅Q, Q⁆) ⧸ Subgroup.center ↥(⁅Q, Q⁆)) := hquotSimple.toNontrivial
  haveI : Group.IsPerfect (↥(⁅Q, Q⁆) ⧸ Subgroup.center ↥(⁅Q, Q⁆)) := by
    haveI : Group.IsPerfect ↥(⁅Q, Q⁆) := hJperfect
    exact Group.IsPerfect.ofSurjective
      (QuotientGroup.mk'_surjective (Subgroup.center ↥(⁅Q, Q⁆)))
  refine ⟨hJperfect, hquotSimple, ?_⟩
  by_contra h
  push Not at h
  exact Group.IsPerfect.not_isMulCommutative _ (isMulCommutative_iff.mpr h)

private lemma l48gQ_deriv_le {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    {A : Subgroup L'} {C S : Subgroup R} {Q : Subgroup L'}
    (hQ : Q = A ⊓ S.comap ψ) (hmapA : A.map ψ = C) (hder : ⁅C, C⁆ ≤ S) :
    ⁅A, A⁆ ≤ Q := by
  rw [hQ]
  refine le_inf (Subgroup.commutator_le_self A) ?_
  rw [← Subgroup.map_le_iff_le_comap]
  calc (⁅A, A⁆).map ψ = ⁅A.map ψ, A.map ψ⁆ := Subgroup.map_commutator A A ψ
    _ = ⁅C, C⁆ := by rw [hmapA]
    _ ≤ S := hder

theorem ggB2der_layer_of_normal_image {L' R : Type} [Group L'] [Group R] (ψ : L' →* R)
    (hker : ψ.ker ≤ Subgroup.center L') {A : Subgroup L'} {C S : Subgroup R}
    (hmapA : A.map ψ = C) (hSC : S ≤ C) (hnorm : ∀ c ∈ C, ∀ s ∈ S, c * s * c⁻¹ ∈ S)
    (hder : ⁅C, C⁆ ≤ S) (hsimple : IsSimpleGroup ↥S) (hperf : ⁅S, S⁆ = S)
    (h7 : 7 ∣ Nat.card ↥S) :
    IsComponentOf (LargeEvenLayer A) A ∧ (LargeEvenLayer A).map ψ = ⁅S, S⁆ ∧
      ¬ LargeEvenSmall (LargeEvenLayer A) := by
  set Q : Subgroup L' := A ⊓ S.comap ψ with hQdef
  have hQmap : Q.map ψ = S := l48gQ_map_Q ψ hQdef hmapA hSC
  have hQeq : Q = ⁅Q, Q⁆ ⊔ (Q ⊓ ψ.ker) := l48gQ_split ψ hQdef hQmap hperf
  have hQle : Q ≤ ⁅Q, Q⁆ ⊔ ψ.ker := by
    calc Q = ⁅Q, Q⁆ ⊔ (Q ⊓ ψ.ker) := hQeq
      _ ≤ ⁅Q, Q⁆ ⊔ ψ.ker :=
        sup_le (le_sup_left : ⁅Q, Q⁆ ≤ ⁅Q, Q⁆ ⊔ ψ.ker)
          (le_trans (inf_le_right : Q ⊓ ψ.ker ≤ ψ.ker)
            (le_sup_right : ψ.ker ≤ ⁅Q, Q⁆ ⊔ ψ.ker))
  have hJperf : ⁅⁅Q, Q⁆, ⁅Q, Q⁆⁆ = ⁅Q, Q⁆ := l48gQ_perfect ψ hker hQle
  have hJmap : (⁅Q, Q⁆).map ψ = S := by
    rw [Subgroup.map_commutator, hQmap, hperf]
  have hQleA : Q ≤ A := hQdef.le.trans inf_le_left
  have hJA : ⁅Q, Q⁆ ≤ A := (Subgroup.commutator_le_self Q).trans hQleA
  have hJnormal : ∀ h ∈ A, ∀ d ∈ ⁅Q, Q⁆, h * d * h⁻¹ ∈ ⁅Q, Q⁆ :=
    l48gQ_normal ψ hQdef hmapA hnorm
  have hJq : CFSG.IsQuasisimple ↥(⁅Q, Q⁆) :=
    l48gQ_quasisimple ψ hker hJmap hJperf hsimple
  have hderiv_le : ⁅A, A⁆ ≤ Q := l48gQ_deriv_le ψ hQdef hmapA hder
  have hlayer := CFSG.StandardType.TwoThreeOrth.largeEvenLayer_eq_of_commutator_commutator_mem
    hJA hJnormal
    (fun x hx y hy => Subgroup.commutator_mem_commutator (hderiv_le hx) (hderiv_le hy))
    hJq
  refine ⟨?_, ?_, ?_⟩
  · rw [hlayer.1]
    exact hlayer.2
  · rw [hlayer.1]
    exact hJmap.trans hperf.symm
  · rw [hlayer.1]
    exact IOneOrthEnd.not_largeEvenSmall_of_map ψ (⁅Q, Q⁆) (by rw [hJmap]; exact h7)

end CFSG.StandardType
