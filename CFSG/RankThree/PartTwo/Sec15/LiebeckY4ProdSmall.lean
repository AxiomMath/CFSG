module

public import CFSG.RankThree.PartTwo.Sec15.LiebeckY4ProdDefs
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.AltSixCentralizer
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiagK
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Ronan148JStruct
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofPGL
import CFSG.RankThree.PartTwo.KFacts.ONanKS17J2CentralizerNine
import Certificates.Data.A5

public section

namespace CFSG.RankThree.PartTwo.Sec15.LiebeckY4

open CFSG Equiv CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

private theorem key5 : ∀ t : Perm (Fin 5), t ^ 3 = 1 → t ≠ 1 → ∀ a : alternatingGroup (Fin 5),
    t * (a : Perm (Fin 5)) = a * t → (a : Perm (Fin 5)) ^ 3 = 1 := by
  decide +kernel

theorem fixA5_holds : FixA5 := by
  intro X _ hX σ hσ3 hσ1 y hy
  obtain ⟨e⟩ := hX
  set τ : MulAut (alternatingGroup (Fin 5)) := MulAut.congr e σ with hτ
  have hτ3 : τ ^ 3 = 1 := by rw [hτ, ← map_pow, hσ3, map_one]
  have hτ1 : τ ≠ 1 := fun h => hσ1 ((MulAut.congr e).injective (by rw [← hτ, h, map_one]))
  obtain ⟨t, ht⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by norm_num) (by norm_num)).2 τ
  have hinj := GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 5 (by norm_num)
  have ht3 : t ^ 3 = 1 := hinj (by rw [map_pow, ht, hτ3, map_one])
  have ht1 : t ≠ 1 := fun h => hτ1 (by rw [← ht, h, map_one])
  have hτy : τ (e y) = e y := by simp [hτ, MulAut.congr_apply, hy]
  have hc : t * ((e y : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
      (e y : alternatingGroup (Fin 5)) * t := by
    have h1 := congrArg Subtype.val (show (MulAut.conjNormal t) (e y) = e y by rw [ht]; exact hτy)
    rw [MulAut.conjNormal_apply] at h1
    calc t * ((e y : alternatingGroup (Fin 5)) : Perm (Fin 5))
        = t * (e y : alternatingGroup (Fin 5)) * t⁻¹ * t := by group
      _ = (e y : alternatingGroup (Fin 5)) * t := by rw [h1]
  have h3 := key5 t ht3 ht1 (e y) hc
  refine ⟨1, ?_⟩
  apply e.injective
  rw [pow_one, map_pow, map_one]
  exact Subtype.ext (by simpa using h3)

private theorem a6_cent {a b : alternatingGroup (Fin 6)} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hab : a * b = b * a) : b ^ 3 = 1 := by
  have h := Sec4.Census.Karpilovsky.UniversalCoverMonster.ThreeGroup.alt_six_centralizer_cube
    (a : Perm (Fin 6)) (by simpa using congrArg Subtype.val ha3) (fun h => ha1 (Subtype.ext h))
    (Equiv.Perm.mem_alternatingGroup.mp a.2) (b : Perm (Fin 6))
    (Equiv.Perm.mem_alternatingGroup.mp b.2) (by simpa using (congrArg Subtype.val hab).symm)
  exact Subtype.ext (by simpa using h)

private theorem fixA6Cover_core {X : Type} [Group X] (hperf : Group.IsPerfect X)
    (φ : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6))
    (σ : MulAut X) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (y : X)
    (hy : y⁻¹ * σ y ∈ Subgroup.center X) : y ^ 3 ∈ Subgroup.center X := by
  haveI := hperf
  let Φ : MulAut X →* MulAut (alternatingGroup (Fin 6)) :=
    (MulAut.congr φ).toMonoidHom.comp
      (ComponentClassification.PerfectAutomorphisms.centerQuotientHom X)
  have hΦinj : Function.Injective Φ :=
    (MulAut.congr φ).injective.comp
      (ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective X)
  have hΦ : ∀ (ρ : MulAut X) (x : X),
      Φ ρ (φ (x : X ⧸ Subgroup.center X)) = φ ((ρ x : X) : X ⧸ Subgroup.center X) := by
    intro ρ x
    have h := ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk ρ x
    show φ (ComponentClassification.PerfectAutomorphisms.onCenterQuotient ρ
      (φ.symm (φ (x : X ⧸ Subgroup.center X)))) = _
    rw [MulEquiv.symm_apply_apply]
    exact congrArg φ h
  have hφπ : Function.Surjective (fun x : X => φ (x : X ⧸ Subgroup.center X)) :=
    φ.surjective.comp QuotientGroup.mk_surjective
  have hτ3 : Φ σ ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
  have hτ1 : Φ σ ≠ 1 := fun h => hσ1 (hΦinj (by rw [h, map_one]))
  obtain ⟨a, ha⟩ := (Proof15Res8Diag.mem_inner_of_pow_eq_one_six
    (MulEquiv.refl (alternatingGroup (Fin 6))) (σ := Φ σ) (k := 1) (by rw [pow_one]; exact hτ3) :
      Φ σ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner _)
  obtain ⟨x₀, hx₀⟩ := hφπ a
  have hx₀' : φ (x₀ : X ⧸ Subgroup.center X) = a := hx₀
  have hσx : σ = MulAut.conj x₀ := by
    apply hΦinj
    rw [← ha]
    ext b
    obtain ⟨x, hxb⟩ := hφπ b
    have hxb' : φ (x : X ⧸ Subgroup.center X) = b := hxb
    rw [← hxb', hΦ, MulAut.conj_apply, MulAut.conj_apply, ← hx₀']
    simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hcomm : a * φ (y : X ⧸ Subgroup.center X) = φ (y : X ⧸ Subgroup.center X) * a := by
    have h1 : ((σ y : X) : X ⧸ Subgroup.center X) = (y : X ⧸ Subgroup.center X) := by
      have h2 := (QuotientGroup.eq_one_iff (N := Subgroup.center X) (y⁻¹ * σ y)).mpr hy
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h2
      exact (inv_mul_eq_one.mp h2).symm
    have h3 := hΦ σ y
    rw [← ha, h1, MulAut.conj_apply] at h3
    calc a * φ (y : X ⧸ Subgroup.center X)
        = a * φ (y : X ⧸ Subgroup.center X) * a⁻¹ * a := by group
      _ = φ (y : X ⧸ Subgroup.center X) * a := by rw [h3]
  have ha3 : a ^ 3 = 1 := by
    have h1 : (MulAut.conj (a ^ 3) : MulAut _) = 1 := by rw [map_pow, ha, hτ3]
    have hmem : a ^ 3 ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 := congrArg (fun f : MulAut _ => f g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc g * a ^ 3 = (a ^ 3 * g * (a ^ 3)⁻¹) * a ^ 3 := by rw [h2]
        _ = a ^ 3 * g := by group
    rw [Proof15Res8Diag.center_eq_bot_six (MulEquiv.refl _), Subgroup.mem_bot] at hmem
    exact hmem
  have ha1 : a ≠ 1 := fun h => hτ1 (by rw [← ha, h, map_one])
  have hy3 : (φ (y : X ⧸ Subgroup.center X)) ^ 3 = 1 := a6_cent ha3 ha1 hcomm
  rw [← QuotientGroup.eq_one_iff]
  apply φ.injective
  rw [map_one, QuotientGroup.mk_pow, map_pow]
  exact hy3

theorem fixA6Cover_holds : FixA6Cover := by
  rintro X _ _ ⟨hperf, -, ⟨φ⟩⟩ σ hσ3 hσ1 y hy
  exact ⟨1, by simpa using fixA6Cover_core hperf φ σ hσ3 hσ1 y hy⟩

section Bridge

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G} [(ker148 A M).Normal]

theorem img148_inf_centralizer_le (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hAM : A ≤ Subgroup.normalizer (M : Set G)) {B : Subgroup G} (hB : B ≤ A) :
    img148 A M M ⊓ Subgroup.centralizer (img148 A M B : Set (↥(M ⊔ A) ⧸ ker148 A M)) ≤
      img148 A M (M ⊓ Subgroup.centralizer (B : Set G)) := by
  set N := pPrimeCoreOf 3 M with hN
  have hAN : A ≤ Subgroup.normalizer (N : Set G) :=
    hAM.trans (normalizer_le_normalizer_pPrimeCoreOf 3 M)
  rintro x ⟨hxM, hxc⟩
  obtain ⟨j, hjM, hjJ, rfl⟩ := mem_img148_iff.mp hxM
  have hk : ∀ b ∈ B, j⁻¹ * (b * j * b⁻¹) ∈ N ⊓ M := by
    intro b hb
    have hbA : b ∈ A := hB hb
    have hbjJ : b * j * b⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hAM hbA) j).mp hjJ
    refine ⟨?_, M.mul_mem (M.inv_mem hjJ) hbjJ⟩
    have hbjM : b * j * b⁻¹ ∈ M ⊔ A := Subgroup.mem_sup_left hbjJ
    have hcomm : alpha148 A M b hbA * QuotientGroup.mk' (ker148 A M) ⟨j, hjM⟩ *
        (alpha148 A M b hbA)⁻¹ = QuotientGroup.mk' (ker148 A M) ⟨j, hjM⟩ := by
      have hc := Subgroup.mem_centralizer_iff.mp hxc (alpha148 A M b hbA)
        (mem_img148_iff.mpr ⟨b, Subgroup.mem_sup_right hbA, hb, (alpha148_eq_mk' hbA).symm⟩)
      rw [hc, mul_inv_cancel_right]
    have hmk : QuotientGroup.mk' (ker148 A M) ⟨j, hjM⟩ =
        QuotientGroup.mk' (ker148 A M) ⟨b * j * b⁻¹, hbjM⟩ := by
      rw [← hcomm, alpha148_eq_mk', ← map_inv, ← map_mul, ← map_mul]
      rfl
    exact mk'_ker148_eq_iff.mp hmk
  have hB3 : IsPGroup 3 B := isPGroup_three_of_pow148 fun b hb => hA3 b (hB hb)
  have hN3 : Nat.Coprime 3 (Nat.card ↥(N ⊓ M)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_pPrimeCoreOf 3 M)
  have hBN : B ≤ Subgroup.normalizer ((N ⊓ M : Subgroup G) : Set G) := fun b hb =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hAN (hB hb), hAM (hB hb)⟩
  obtain ⟨y, hy, hyc⟩ := exists_commute_mem_coset148 hB3 hN3 hBN hk
  have hyM : y ∈ M := by
    have := M.mul_mem hjJ hy.2
    rwa [mul_inv_cancel_left] at this
  refine mem_img148_iff.mpr ⟨y, Subgroup.mem_sup_left hyM, ⟨hyM, ?_⟩, ?_⟩
  · exact Subgroup.mem_centralizer_iff.mpr fun b hb => hyc b hb
  · exact (mk'_ker148_eq_iff.mpr hy.1).symm

end Bridge

theorem step148ProdBridge_holds : Step148ProdBridge := by
  intro G _ _ A c L h M hM B hB
  letI := ker148_normal hM.2
  intro hY
  have hA := h.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  set N := pPrimeCoreOf 3 (M ⊓ Subgroup.centralizer (B : Set G)) with hN
  set T := img148 A M (deltaZero A (lB A) M) ⊓
    Subgroup.centralizer (img148 A M B : Set (↥(M ⊔ A) ⧸ ker148 A M)) with hT
  have hTle : T ≤ img148 A M (M ⊓ Subgroup.centralizer (B : Set G)) :=
    (inf_le_inf_right _ (img148_mono (deltaZero_le M))).trans
      (img148_inf_centralizer_le hA3 hM.2 hB.1)
  have hTN : T ≤ Subgroup.normalizer ((img148 A M N : Subgroup _) : Set _) :=
    hTle.trans (img148_le_normalizer (le_normalizer_pPrimeCoreOf 3 _))
  have hN3 : ¬ 3 ∣ Nat.card N := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _) h3
  have hN3' : ¬ 3 ∣ Nat.card (img148 A M N) := Item148PtRes.not_three_dvd_card_img148 hN3
  have hcop : Nat.Coprime 3 (Nat.card ↥(img148 A M N ⊓ T)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
      hN3' (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have h1 : img148 A M N ⊓ T ≤ pPrimeCoreOf 3 T :=
    le_pPrimeCoreOf inf_le_right (fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hTN ht, Subgroup.le_normalizer ht⟩) hcop
  refine le_trans (le_inf (img148_mono hY) ?_) h1
  exact le_inf (img148_mono (deltaZero_mono inf_le_left))
    (Ronan148J.img148_le_centralizer ((deltaZero_le _).trans inf_le_right))

theorem centJ2E9_holds :
    CentJ2E9 := by
  intro X _ _ hX F hF hF9 y hy
  have hyF : y ∈ F := KFacts.ks17J2CentralizerNine X hX F hF9
    (Subgroup.mem_centralizer_iff.mpr fun f hf => (hy f hf).symm)
  exact ⟨1, by simpa using hF.2 y hyF⟩

end CFSG.RankThree.PartTwo.Sec15.LiebeckY4
