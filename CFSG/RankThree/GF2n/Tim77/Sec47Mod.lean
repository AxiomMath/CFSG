module

public import CFSG.RankThree.GF2n.Tim77.Defs
public import CFSG.CGT.Timmesfeld75.Lemma27
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
public import CFSG.SignalizerFunctorTheorem.NearModels.Main
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.Open

theorem sec47_dichotomy {K : Type} [Group K] (N : Subgroup K) [N.Normal]
    (hs : IsSimpleGroup (K ⧸ Subgroup.center K)) :
    N ≤ Subgroup.center K ∨ N ⊔ Subgroup.center K = ⊤ := by
  have hNm : (N.map (QuotientGroup.mk' (Subgroup.center K))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (N.map (QuotientGroup.mk' (Subgroup.center K))) with h | h
  · left
    have h1 : N ≤ (QuotientGroup.mk' (Subgroup.center K)).ker := (Subgroup.map_eq_bot_iff _).mp h
    rwa [QuotientGroup.ker_mk'] at h1
  · right
    have h1 := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center K)) N
    rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
    exact h1.symm

theorem sec47_quotient_data {K V : Type} [Group K] [Finite K] [Group V] [Finite V]
    (ρ : K →* MulAut V) (hnt : ∃ y ∈ commutator K, ρ y ≠ 1)
    (hs : IsSimpleGroup (K ⧸ Subgroup.center K))
    (hp : Group.IsPerfect (K ⧸ Subgroup.center K)) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (ψ : X →* MulAut V)
      (θ : X →* K ⧸ Subgroup.center K), Function.Injective ψ ∧ Function.Surjective θ := by
  haveI : (commutator K).Normal := by
    unfold commutator
    infer_instance
  rcases sec47_dichotomy (ρ.ker ⊓ commutator K) hs with hNZ | hsup
  · let ψ₀ : commutator K →* MulAut V := ρ.comp (commutator K).subtype
    have hker : ψ₀.ker ≤ ((QuotientGroup.mk' (Subgroup.center K)).comp
        (commutator K).subtype).ker := by
      intro w hw
      have h1 : ρ (w : K) = 1 := MonoidHom.mem_ker.mp hw
      have h2 : (w : K) ∈ ρ.ker ⊓ commutator K :=
        Subgroup.mem_inf.mpr ⟨MonoidHom.mem_ker.mpr h1, w.2⟩
      exact MonoidHom.mem_ker.mpr ((QuotientGroup.eq_one_iff (w : K)).mpr (hNZ h2))
    have hmap : (commutator K).map (QuotientGroup.mk' (Subgroup.center K)) = ⊤ := by
      have hT := Subgroup.map_top_of_surjective (QuotientGroup.mk' (Subgroup.center K))
        (QuotientGroup.mk'_surjective _)
      have h := Subgroup.map_commutator (H₁ := ⊤) (H₂ := ⊤)
        (f := QuotientGroup.mk' (Subgroup.center K))
      rw [hT] at h
      exact h.trans hp.commutator_eq_top
    refine ⟨commutator K ⧸ ψ₀.ker, inferInstance, inferInstance, QuotientGroup.kerLift ψ₀,
      QuotientGroup.lift ψ₀.ker _ hker, QuotientGroup.kerLift_injective ψ₀, ?_⟩
    intro l
    have hl : l ∈ (commutator K).map (QuotientGroup.mk' (Subgroup.center K)) := by
      rw [hmap]
      exact Subgroup.mem_top l
    obtain ⟨k, hk, hkl⟩ := Subgroup.mem_map.mp hl
    exact ⟨QuotientGroup.mk ⟨k, hk⟩, by rw [QuotientGroup.lift_mk]; exact hkl⟩
  · exfalso
    have hcomm : commutator K ≤ ρ.ker ⊓ commutator K :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    obtain ⟨y, hy, hne⟩ := hnt
    exact hne (MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp (hcomm hy)).1)

theorem sec47_module_bound {K V : Type} [Group K] [Finite K] [Group V] [Finite V]
    (hV : IsElemAbelian 2 (⊤ : Subgroup V)) (ρ : K →* MulAut V)
    (hrad : CFSG.solvableRadical K = Subgroup.center K) {f : ℕ} (hf : 2 ≤ f)
    (hL : IsPSL2Model (K ⧸ Subgroup.center K) f) (hnt : ∃ y ∈ commutator K, ρ y ≠ 1)
    {d : ℕ} (hd : Nat.card V = 2 ^ d) : 2 * f ≤ d := by
  obtain ⟨e⟩ := hL
  have hf0 : f ≠ 0 := by omega
  have hq4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f hf0]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hq4
  haveI : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three _ (by omega)
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := e.isSimpleGroup
  haveI : Group.IsPerfect (K ⧸ Subgroup.center K) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨X, hX, hXf, ψ, θ, hψ, hθ⟩ := sec47_quotient_data ρ hnt inferInstance inferInstance
  have hLcard : Nat.card (K ⧸ Subgroup.center K) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psl2_even hf0
  have hdvd : 2 ^ f * ((2 ^ f) ^ 2 - 1) ∣ Nat.card X := by
    rw [← hLcard]
    exact Subgroup.card_dvd_of_surjective hθ
  by_cases h3 : f = 3
  · subst h3
    have h6 := CFSG.CGT.Timmesfeld75.lemma27_psl2_eight (e.toMonoidHom.comp θ)
      (e.surjective.comp hθ) ψ hψ hd
    omega
  · exact CFSG.CGT.Timmesfeld75.lemma27_psl2 hf h3 hdvd ψ hψ hd

theorem sec47_module_bound_sz {K V : Type} [Group K] [Finite K]
    [Group V] [Finite V] (hV : IsElemAbelian 2 (⊤ : Subgroup V)) (ρ : K →* MulAut V)
    (hrad : CFSG.solvableRadical K = Subgroup.center K) {k : ℕ}
    (hL : IsSzModel (K ⧸ Subgroup.center K) k) (hnt : ∃ y ∈ commutator K, ρ y ≠ 1)
    {d : ℕ} (hd : Nat.card V = 2 ^ d) : 4 * (2 * k + 1) ≤ d := by
  obtain ⟨e⟩ := hL
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    exfalso
    haveI : Group.IsSolvable (Sz 0) := CFSG.SignalizerFunctorTheorem.NearModels.isSolvable_sz_zero
    have hsolvL : Group.IsSolvable (K ⧸ Subgroup.center K) :=
      Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    haveI : Group.IsSolvable (Subgroup.center K) := by
      apply Group.isSolvable_of_comm
      intro a b
      exact Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
    have hsolvK : Group.IsSolvable K := Group.isSolvable_of_subgroup_quotient (Subgroup.center K)
    have htop : (⊤ : Subgroup K) ≤ CFSG.solvableRadical K :=
      le_sSup (show (⊤ : Subgroup K).Normal ∧ Group.IsSolvable (⊤ : Subgroup K) from
        ⟨inferInstance, inferInstance⟩)
    rw [hrad] at htop
    have hbot : commutator K ≤ ⊥ := by
      refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp (htop (Subgroup.mem_top g₁)) g₂).symm
    obtain ⟨y, hy, hne⟩ := hnt
    apply hne
    rw [Subgroup.mem_bot.mp (hbot hy), map_one]
  · haveI : IsSimpleGroup (Sz k) :=
      CFSG.SignalizerFunctorTheorem.McBride.SzModel.sz_isSimpleGroup (n := k) (by omega)
    haveI hpS := CFSG.SectionRank.suzukiMatrixGroup_isPerfect k (by omega)
    haveI : Group.IsPerfect (Sz k) :=
      Group.IsPerfect.ofSurjective
        (f := (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv k).symm.toMonoidHom)
        (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv k).symm.surjective
    haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := e.isSimpleGroup
    haveI : Group.IsPerfect (K ⧸ Subgroup.center K) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    obtain ⟨X, hX, hXf, ψ, θ, hψ, hθ⟩ := sec47_quotient_data ρ hnt inferInstance inferInstance
    have hcard : Nat.card (Sz k) = Nat.card (K ⧸ Subgroup.center K) :=
      Nat.card_congr e.symm.toEquiv
    have hdvd : Nat.card (Sz k) ∣ Nat.card X := by
      rw [hcard]
      exact Subgroup.card_dvd_of_surjective hθ
    exact CFSG.CGT.Timmesfeld75.lemma27_sz (by omega) hdvd ψ hψ hd

end CFSG.RankThree.GF2n.Tim77
