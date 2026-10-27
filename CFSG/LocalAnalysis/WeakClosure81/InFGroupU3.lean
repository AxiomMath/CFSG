module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupU3Top
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupU3Cent
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupU3Gen
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5EF

public section

namespace CFSG.LocalAnalysis.WeakClosure81.InFGroupU3

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase
open scoped Pointwise

variable {Q : Type} [Group Q] [Finite Q] {C : Subgroup Q} {n : ℕ}

private lemma map_perfectCore_conj_centralizer (h : Setting C n) (s t : Q) :
    (perfectCore (C ⊓ centralizer ({s} : Set Q))).map (MulAut.conj t).toMonoidHom =
      perfectCore (C ⊓ centralizer ({t * s * t⁻¹} : Set Q)) := by
  haveI : C.Normal := h.normal
  have hC : C.map (MulAut.conj t).toMonoidHom = C := by
    simpa using Subgroup.Normal.map_conj_eq C t
  rw [CFSG.Quasithin.map_perfectCore (MulAut.conj t).toMonoidHom,
    Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hC,
    CFSG.ClassicalInvolution.map_conj_centralizer_singleton t s]

private lemma le_genEi_of_card_gt
    (h : Setting C n)
    {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤) {Ω : Set (Subgroup Q)} {A : Subgroup Q}
    (hΩ : IsOmegaColl Ω) (hAΩ : A ∈ Ω) (hAT : A ≤ T) (hAel : IsElemAbelian 2 A)
    (hcard : 2 ^ n < Nat.card A) {s : Q} (hsA : s ∈ A) (hsC : s ∉ C) (t : ↥T) :
    perfectCore (C ⊓ centralizer ({(t : Q) * s * (t : Q)⁻¹} : Set Q)) ≤
      genEi n T Ω := by
  have htT : (t : Q) ∈ T := t.2
  have hA'Ω : conjSubgroup A (t : Q)⁻¹ ∈ Ω := hΩ.conj A hAΩ (t : Q)⁻¹
  have hA'T : conjSubgroup A (t : Q)⁻¹ ≤ T := by
    intro x hx
    rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hx
    have hx' : (t : Q)⁻¹ * x * (t : Q) ∈ A := by simpa using hx
    have hxT : (t : Q) * ((t : Q)⁻¹ * x * (t : Q)) * (t : Q)⁻¹ ∈ T :=
      T.mul_mem (T.mul_mem htT (hAT hx')) (T.inv_mem htT)
    have hxeq : (t : Q) * ((t : Q)⁻¹ * x * (t : Q)) * (t : Q)⁻¹ = x := by group
    rwa [hxeq] at hxT
  have hA'el : IsElemAbelian 2 (conjSubgroup A (t : Q)⁻¹) :=
    CFSG.Quasithin.E3.isElemAbelian_conjSubgroup hAel (t : Q)⁻¹
  have hcardA' : 2 ^ n < Nat.card (conjSubgroup A (t : Q)⁻¹) := by
    have hc : Nat.card (conjSubgroup A (t : Q)⁻¹) = Nat.card A := by
      rw [CFSG.Quasithin.conjSubgroup, inv_inv]
      exact Subgroup.card_map_of_injective (MulAut.conj (t : Q)).injective
    rwa [hc]
  have hs'A' : (t : Q) * s * (t : Q)⁻¹ ∈ conjSubgroup A (t : Q)⁻¹ := by
    rw [CFSG.Quasithin.mem_conjSubgroup_iff]
    have hseq : (t : Q)⁻¹ * ((t : Q) * s * (t : Q)⁻¹) * (t : Q) = s := by group
    simpa [hseq] using hsA
  have hs'C : (t : Q) * s * (t : Q)⁻¹ ∉ C := by
    intro hc
    apply hsC
    have h1 : (t : Q)⁻¹ * ((t : Q) * s * (t : Q)⁻¹) * (t : Q) ∈ C := by
      simpa using h.normal.conj_mem _ hc (t : Q)⁻¹
    have hseq : (t : Q)⁻¹ * ((t : Q) * s * (t : Q)⁻¹) * (t : Q) = s := by group
    rwa [hseq] at h1
  have hIn : InCalEi n T (conjSubgroup A (t : Q)⁻¹)
      (perfectCore (C ⊓ centralizer ({(t : Q) * s * (t : Q)⁻¹} : Set Q)) ⊔
        tA T (conjSubgroup A (t : Q)⁻¹)) :=
    h.inCalEi_perfectCore_sup hT hA'el hA'T hcardA' hs'A' hs'C
  exact (le_sup_left : perfectCore _ ≤
    perfectCore _ ⊔ tA T (conjSubgroup A (t : Q)⁻¹)).trans
    (le_iSup₂_of_le (conjSubgroup A (t : Q)⁻¹) hA'Ω
      (le_iSup_of_le hA'T (le_iSup₂_of_le _ hIn le_rfl)))

private lemma map_perfectCore_conj_le_genEi
    (h : Setting C n)
    {T : Subgroup Q} (hT : IsSylowIn 2 T ⊤) {Ω : Set (Subgroup Q)} {A : Subgroup Q}
    (hΩ : IsOmegaColl Ω) (hAΩ : A ∈ Ω) (hAT : A ≤ T) (hAel : IsElemAbelian 2 A)
    (hcard : 2 ^ n < Nat.card A) {s : Q} (hsA : s ∈ A) (hsC : s ∉ C) (t : ↥T) :
    (perfectCore (C ⊓ centralizer ({s} : Set Q))).map
        (MulAut.conj (t : Q)).toMonoidHom ≤ genEi n T Ω := by
  rw [map_perfectCore_conj_centralizer h s (t : Q)]
  exact le_genEi_of_card_gt h hT hΩ hAΩ hAT hAel hcard hsA hsC t

private lemma le_normalizer_iSup_map_conj (J T : Subgroup Q) :
    T ≤ normalizer ((⨆ t : ↥T, J.map (MulAut.conj (t : Q)).toMonoidHom :
      Subgroup Q) : Set Q) := by
  intro u hu
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rw [Subgroup.map_iSup]
    refine iSup_le fun t => ?_
    change (J.map (MulAut.conj (t : Q)).toMonoidHom).map (MulAut.conj u).toMonoidHom ≤
      ⨆ s : ↥T, J.map (MulAut.conj (s : Q)).toMonoidHom
    have hcomp : (J.map (MulAut.conj (t : Q)).toMonoidHom).map
          (MulAut.conj u).toMonoidHom =
        J.map (MulAut.conj (u * (t : Q))).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp]
    exact le_iSup (fun s : ↥T => J.map (MulAut.conj (s : Q)).toMonoidHom)
      ⟨u * (t : Q), T.mul_mem hu t.2⟩
  · refine iSup_le fun t => ?_
    have hu' : u⁻¹ ∈ T := T.inv_mem hu
    have ht' : u⁻¹ * (t : Q) ∈ T := T.mul_mem hu' t.2
    have hgen : J.map (MulAut.conj (u⁻¹ * (t : Q))).toMonoidHom ≤
        ⨆ s : ↥T, J.map (MulAut.conj (s : Q)).toMonoidHom :=
      le_iSup (fun s : ↥T => J.map (MulAut.conj (s : Q)).toMonoidHom)
        ⟨u⁻¹ * (t : Q), ht'⟩
    have hmap := Subgroup.map_mono (f := (MulAut.conj u).toMonoidHom) hgen
    have heq : (J.map (MulAut.conj (u⁻¹ * (t : Q))).toMonoidHom).map
          (MulAut.conj u).toMonoidHom =
        J.map (MulAut.conj (t : Q)).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rwa [heq] at hmap

private lemma sup_eq_top_of_setting (h : Setting C n) {T : Subgroup Q}
    (hT : IsSylowIn 2 T ⊤) : C ⊔ T = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : C.Normal := h.normal
  have hquot : IsPGroup 2 (Q ⧸ C) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective C x
    obtain ⟨k, hk⟩ := h.two_quot y
    refine ⟨k, ?_⟩
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := C) (x := y ^ 2 ^ k)).2 hk
  have hcardT : Nat.card T = 2 ^ (Nat.card Q).factorization 2 := by
    rw [IsSylowIn.card_eq hT, Subgroup.card_top]
  let S : Sylow 2 Q := Sylow.ofCard T hcardT
  have hSC : (S : Subgroup Q) ⊔ C = ⊤ :=
    CFSG.section10_sylow_sup_normal_of_p_quotient_eq_top (N := C) hquot S
  rw [Sylow.coe_ofCard T hcardT] at hSC
  rwa [sup_comm] at hSC

private lemma le_sup_iSup_map_conj_of_sylow
    (h : Setting C n) {T : Subgroup Q} (hS₀ : IsSylowIn 2 (T ⊓ C) C)
    {s : Q} (hsC : s ∉ C) (hs2 : s ^ 2 = 1) {J : Subgroup Q}
    (hJ : J = perfectCore (C ⊓ centralizer ({s} : Set Q))) :
    C ≤ (⨆ t : ↥T, J.map (MulAut.conj (t : Q)).toMonoidHom) ⊔ T := by
  have hJnorm : ¬ J ≤ normalizer (T ⊓ C : Set Q) := by
    rw [hJ]
    exact h.not_perfectCore_le_normalizer hS₀ hsC hs2
  have hXeq : J ⊔ (T ⊓ C) = C := by
    refine h.eq_of_sylow_le (X := J ⊔ (T ⊓ C)) hS₀ le_sup_right ?_ ?_
    · exact sup_le (by rw [hJ]; exact (perfectCore_le _).trans inf_le_left) inf_le_right
    · intro hle
      exact hJnorm (le_sup_left.trans hle)
  rw [← hXeq]
  refine sup_le ?_ ?_
  · have hJM : J ≤ ⨆ t : ↥T, J.map (MulAut.conj (t : Q)).toMonoidHom := by
      have hle : J.map (MulAut.conj (1 : Q)).toMonoidHom ≤ _ :=
        le_iSup (fun t : ↥T => J.map (MulAut.conj (t : Q)).toMonoidHom)
          ⟨1, T.one_mem⟩
      have hmap : J.map (MulAut.conj (1 : Q)).toMonoidHom = J := by
        have hone : (MulAut.conj (1 : Q)).toMonoidHom = MonoidHom.id Q := by
          ext x
          simp [MulAut.conj_apply]
        rw [hone, Subgroup.map_id]
      rwa [hmap] at hle
    exact hJM.trans le_sup_left
  · exact (inf_le_left : T ⊓ C ≤ T).trans le_sup_right

private lemma inFOmega_of_card_le (h : Setting C n) {T A : Subgroup Q}
    (hT : IsSylowIn 2 T ⊤) {Ω : Set (Subgroup Q)} (hAΩ : A ∈ Ω) (hAT : A ≤ T)
    (hAel : IsElemAbelian 2 A) (hAne : A ≠ ⊥) (hcard : Nat.card A ≤ 2 ^ n) :
    InFOmega n T Ω := by
  change ((genEi n T Ω : Subgroup Q) : Set Q) * (T : Set Q) = Set.univ
  have hIn : InCalEi n T A ⊤ := h.inCalEi_top hT hAel hAne hcard
  have htop : genEi n T Ω = ⊤ :=
    le_antisymm le_top
      (le_iSup₂_of_le A hAΩ (le_iSup_of_le hAT (le_iSup₂_of_le ⊤ hIn le_rfl)))
  rw [htop, Subgroup.coe_top]
  exact Set.univ_mul ⟨1, T.one_mem⟩

private lemma inFOmega_of_card_gt
    (h : Setting C n)
    {T A : Subgroup Q} (hT : IsSylowIn 2 T ⊤) {Ω : Set (Subgroup Q)}
    (hΩ : IsOmegaColl Ω) (hAΩ : A ∈ Ω) (hAT : A ≤ T) (hAel : IsElemAbelian 2 A)
    (hcard : 2 ^ n < Nat.card A) : InFOmega n T Ω := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : C.Normal := h.normal
  have hAC : ¬ A ≤ C := fun hle => (not_le_of_gt hcard) (h.card_le_of_le hle hAel)
  obtain ⟨s, hsA, hsC⟩ := SetLike.not_le_iff_exists.mp hAC
  have hs2 : s ^ 2 = 1 := hAel.2 s hsA
  set J : Subgroup Q := perfectCore (C ⊓ centralizer ({s} : Set Q)) with hJdef
  set M : Subgroup Q := ⨆ t : ↥T, J.map (MulAut.conj (t : Q)).toMonoidHom with hMdef
  have hMle : M ≤ genEi n T Ω := by
    rw [hMdef]
    exact iSup_le fun t => by
      rw [hJdef]
      exact map_perfectCore_conj_le_genEi h hT hΩ hAΩ hAT hAel hcard hsA hsC t
  have hMT : T ≤ normalizer (M : Set Q) := by
    rw [hMdef]
    exact le_normalizer_iSup_map_conj J T
  have hS₀syl : IsSylowIn 2 (T ⊓ C) C :=
    hT.inf_normal le_top (h.normal.subgroupOf ⊤)
  have hCM : C ≤ M ⊔ T := by
    rw [hMdef]
    exact le_sup_iSup_map_conj_of_sylow h hS₀syl hsC hs2 hJdef
  have hCT : C ⊔ T = ⊤ := sup_eq_top_of_setting h hT
  have hMTtop : M ⊔ T = ⊤ := by
    apply le_antisymm le_top
    rw [← hCT]
    exact sup_le hCM le_sup_right
  have hMTprod : ((M : Set Q) * (T : Set Q)) = Set.univ := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left M T hMT, hMTtop,
      Subgroup.coe_top]
  have hsub : ((M : Set Q) * (T : Set Q)) ⊆
      ((genEi n T Ω : Subgroup Q) : Set Q) * (T : Set Q) := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hMle hx, y, hy, rfl⟩
  change ((genEi n T Ω : Subgroup Q) : Set Q) * (T : Set Q) = Set.univ
  rw [hMTprod] at hsub
  exact Set.eq_univ_of_univ_subset hsub

theorem Setting.inFGroup
    (h : Setting C n) :
    InFGroup n Q := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro T hT Ω hΩ
  have hT' : IsSylowIn 2 T ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  have hΩ' : E1.IsInvColl (⊤ : Subgroup Q) Ω :=
    { le := fun _ _ => le_top
      isElemAbelian := hΩ.elemAbelian
      conj := fun A hA g _ => by
        have h1 := hΩ.conj A hA g⁻¹
        rwa [CFSG.Quasithin.conjSubgroup_eq_conjSub A g⁻¹, inv_inv] at h1 }
  obtain ⟨A, hAΩ, hAT⟩ :=
    exists_mem_le_of_isSylowOf hT hΩ' hΩ.nonempty
  have hAel : IsElemAbelian 2 A := hΩ.elemAbelian A hAΩ
  by_cases hcard : Nat.card A ≤ 2 ^ n
  · exact inFOmega_of_card_le h hT' hAΩ hAT hAel (hΩ.ne_bot A hAΩ) hcard
  · exact inFOmega_of_card_gt h hT' hΩ hAΩ hAT hAel (Nat.lt_of_not_le hcard)

end CFSG.LocalAnalysis.WeakClosure81.InFGroupU3
