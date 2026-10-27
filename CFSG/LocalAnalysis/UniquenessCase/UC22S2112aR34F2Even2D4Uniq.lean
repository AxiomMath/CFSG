module

public import CFSG.LocalAnalysis.UniquenessCase.UC22D4FunCentralizer
import CFSG.LocalAnalysis.UniquenessCase.UC22D4PrimeCent
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2G2Fun
import CFSG.LieType.Steinberg.CentralExt.TrialityCoprime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.TwistedD4 CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups


theorem uc22d4_nonempty_mulEquiv_graphFixedRootGroup {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] {n p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .trialityD4 n p f) (hX : LieModel X .trialityD4 n p f) :
    ∃ σ : GaloisField p (3 * f) ≃+* GaloisField p (3 * f), (∀ c, σ c = c ^ (p ^ f)) ∧
      Nonempty (X ≃* graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * f)) σ.toRingHom) := by
  have hp : p.Prime := Fact.out
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨P⟩ : Nonempty (Sylow 2 X) := inferInstance
  obtain ⟨hσ, ψ, -⟩ := d4_funSet_eq_pair hp2 hadm hX P
  set σ := iterateFrobenius (GaloisField p (3 * f)) p f with hσdef
  have hKcard : Nat.card (GaloisField p (3 * f)) = (p ^ f) ^ 3 := by
    rw [GaloisField.card p (3 * f) (by omega), pow_mul']
  have hK2 : ringChar (GaloisField p (3 * f)) ≠ 2 := by
    rw [ringChar.eq (GaloisField p (3 * f)) p]
    exact hp2
  have hq2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have hσq : ∀ c, σ c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have heq : (twistedGroup σ).map (adjointGroup d4 (GaloisField p (3 * f))).subtype =
      graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * f)) σ :=
    CFSG.LieType.Steinberg.CentralExt.TrialityClosed.map_twistedGroup_eq_graphFixedRootGroup
      hK2 hq2 hKcard hσq
  let σK : GaloisField p (3 * f) ≃+* GaloisField p (3 * f) :=
    RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσK : σK.toRingHom = σ := RingHom.ext fun _ => rfl
  have heq' : (twistedGroup σ).map (adjointGroup d4 (GaloisField p (3 * f))).subtype =
      graphFixedRootGroup TwistTag.D4 (GaloisField p (3 * f)) σK.toRingHom := by
    rw [hσK]
    exact heq
  refine ⟨σK, ?_, ⟨ψ.symm.trans ?_⟩⟩
  · intro c
    change σK.toRingHom c = c ^ (p ^ f)
    rw [hσK]
    exact iterateFrobenius_def p f c
  · exact (Subgroup.equivMapOfInjective (twistedGroup σ)
      (adjointGroup d4 (GaloisField p (3 * f))).subtype
      Subtype.val_injective).trans (MulEquiv.subgroupCongr heq')

theorem uc22d4_short_partner {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {n p f : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .trialityD4 n p f)
    (hX : LieModel X .trialityD4 n p f) {K : Subgroup X} (hK : IsFundamentalOver (p ^ f) K)
    (eK : K ≃* SL(2, GaloisField p (3 * f))) :
    ∃ L : Subgroup X, centralizer (K : Set X) = L ∧ centralizer (L : Set X) = K ∧
      Nonempty (L ≃* SL(2, GaloisField p f)) := by
  have hp : p.Prime := Fact.out
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨P, hP⟩ := uc22s2112r34_exists_sylow_mem_funSet
    (𝔉 := fundPred (p ^ f)) (K := K) hK
  obtain ⟨hσ, ψ, hFun⟩ := d4_funSet_eq_pair hp2 hadm hX P
  set Lm : Subgroup X :=
    (slLong (iterateFrobenius (GaloisField p (3 * f)) p f) hσ).range.map ψ.toMonoidHom
    with hLm
  set Sm : Subgroup X :=
    (slB (iterateFrobenius (GaloisField p (3 * f)) p f) hσ).range.map ψ.toMonoidHom
    with hSm
  have hFun' : F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) = {Lm, Sm} := by
    rw [hFun]
  have hL : Nonempty (Lm ≃* SL(2, GaloisField p f)) := by
    obtain ⟨eF⟩ := CFSG.ClassicalInvolution.ModelFacts.nonempty_ringEquiv_of_natCard_eq
      (F := CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField
        (iterateFrobenius (GaloisField p (3 * f)) p f)) (F' := GaloisField p f) (by
        rw [CFSG.ClassicalInvolution.ModelFacts.card_fixedField_iterateFrobenius hf,
          GaloisField.card p f (by omega)])
    exact ⟨(Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).symm.trans
      ((MonoidHom.ofInjective (slLong_injective hσ)).symm.trans
        (CFSG.ClassicalInvolution.ModelFacts.slMapEquiv eF))⟩
  have hKcard : Nat.card K = p ^ (3 * f) * ((p ^ (3 * f)) ^ 2 - 1) := by
    rw [Nat.card_congr eK.toEquiv, CFSG.GorensteinWalter.sl2_card_formula,
      GaloisField.card p (3 * f) (by omega)]
  have hLcard : Nat.card Lm = p ^ f * ((p ^ f) ^ 2 - 1) := by
    obtain ⟨eL⟩ := hL
    rw [Nat.card_congr eL.toEquiv, CFSG.GorensteinWalter.sl2_card_formula,
      GaloisField.card p f (by omega)]
  have hqQ : p ^ f < p ^ (3 * f) :=
    Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hsq : (p ^ f) ^ 2 < (p ^ (3 * f)) ^ 2 := Nat.pow_lt_pow_left hqQ (by norm_num)
  have hp1 : 1 ≤ p := le_of_lt hp.one_lt
  have hsub : (p ^ f) ^ 2 - 1 < (p ^ (3 * f)) ^ 2 - 1 :=
    Nat.sub_lt_sub_right (Nat.one_le_pow 2 (p ^ f) (Nat.one_le_pow f p hp1)) hsq
  have hlt : p ^ f * ((p ^ f) ^ 2 - 1) <
      p ^ (3 * f) * ((p ^ (3 * f)) ^ 2 - 1) := Nat.mul_lt_mul'' hqQ hsub
  have hKne : K ≠ Lm := by
    intro h
    have hc : p ^ f * ((p ^ f) ^ 2 - 1) =
        p ^ (3 * f) * ((p ^ (3 * f)) ^ 2 - 1) := by
      rw [← hLcard, ← hKcard, h]
    exact absurd hc (ne_of_lt hlt)
  have hLmem : Lm ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) := by
    rw [hFun']
    simp
  have hKS : K = Sm := by
    have hmem : K ∈ F14.FunSet (fundPred (p ^ f)) X (P : Subgroup X) := hP
    rw [hFun'] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact absurd h hKne
    · exact h
  have hCK : centralizer (K : Set X) ≤ Lm :=
    d4_centralizer_funSet_le hp hp2 hadm hX P hP hLmem hKne
  have hCL : centralizer (Lm : Set X) ≤ K :=
    d4_centralizer_funSet_le hp hp2 hadm hX P hLmem hP (Ne.symm hKne)
  have hmodel : (slLong (iterateFrobenius (GaloisField p (3 * f)) p f) hσ).range ≤
      centralizer ((slB (iterateFrobenius (GaloisField p (3 * f)) p f) hσ).range :
        Set (twistedGroup (iterateFrobenius (GaloisField p (3 * f)) p f))) := by
    rintro _ ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨B, rfl⟩
    exact (slLong_comm_slB hσ A B).symm
  have hLmC : Lm ≤ centralizer (Sm : Set X) := by
    rw [hLm, hSm, Subgroup.coe_map]
    exact (Subgroup.map_mono hmodel (f := ψ.toMonoidHom)).trans
      (Subgroup.map_centralizer_le_centralizer_image _ ψ.toMonoidHom)
  have hLCK : Lm ≤ centralizer (K : Set X) := by
    rw [hKS]
    exact hLmC
  have hKC : K ≤ centralizer (Lm : Set X) := Subgroup.le_centralizer_iff.mp hLCK
  exact ⟨Lm, le_antisymm hCK hLCK, le_antisymm hCL hKC, hL⟩

theorem uc22d4_fund_eq_or_rank_of_short {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {n p f : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hadm : StatedLieAdmissible .trialityD4 n p f)
    (hX : LieModel X .trialityD4 n p f) {K K' : Subgroup X} (hK : IsFundamentalOver (p ^ f) K)
    (hK' : IsFundamentalOver (p ^ f) K') (eK : K ≃* SL(2, GaloisField p (3 * f)))
    (eK' : K' ≃* SL(2, GaloisField p (3 * f))) {x : X} (hx : x ∈ K ⊓ K')
    (hxr : (orderOf x).Prime) (hx5 : 5 ≤ orderOf x) (hxp : orderOf x ≠ p) :
    K = K' ∨ 2 ≤ Open.pRank p (centralizer ({x} : Set X)) := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨L, hCK, hCL, hL⟩ := uc22d4_short_partner hp2 hadm hX hK eK
  obtain ⟨L', hCK', hCL', hL'⟩ := uc22d4_short_partner hp2 hadm hX hK' eK'
  obtain ⟨eL⟩ := hL
  obtain ⟨eL'⟩ := hL'
  have hxK : x ∈ K := (Subgroup.mem_inf.mp hx).1
  have hxK' : x ∈ K' := (Subgroup.mem_inf.mp hx).2
  set r := orderOf x with hrdef
  have hr : r.Prime := by rw [hrdef]; exact hxr
  have hr5 : 5 ≤ r := by rw [hrdef]; exact hx5
  have hr3 : 3 < r := by omega
  have hrne : r ≠ p := by rw [hrdef]; exact hxp
  have hKcard : Nat.card K = p ^ (3 * f) * ((p ^ (3 * f)) ^ 2 - 1) := by
    rw [Nat.card_congr eK.toEquiv, CFSG.GorensteinWalter.sl2_card_formula,
      GaloisField.card p (3 * f) (by omega)]
  have hrK : r ∣ Nat.card K := by
    rw [hrdef]
    exact Subgroup.orderOf_dvd_natCard K hxK
  have hr_dvd : r ∣ p ^ (3 * f) * ((p ^ (3 * f)) ^ 2 - 1) := by
    rwa [hKcard] at hrK
  have hr_notQ : ¬ r ∣ p ^ (3 * f) := by
    intro hdiv
    have hrp : r ∣ p := hr.dvd_of_dvd_pow hdiv
    exact hrne ((Nat.prime_dvd_prime_iff_eq hr hp).mp hrp)
  have hrQ : r ∣ (p ^ (3 * f)) ^ 2 - 1 :=
    (hr.coprime_iff_not_dvd.mpr hr_notQ).dvd_of_dvd_mul_left hr_dvd
  have hpow : (p ^ (3 * f)) ^ 2 - 1 = (p ^ f) ^ 6 - 1 := by
    have h1 : p ^ (3 * f) = (p ^ f) ^ 3 := by rw [pow_mul']
    rw [h1, ← pow_mul]
  have hrq : r ∣ (p ^ f) ^ 6 - 1 := by
    rwa [hpow] at hrQ
  obtain ⟨σK, hσK, ⟨Θ⟩⟩ := uc22d4_nonempty_mulEquiv_graphFixedRootGroup hp2 hadm hX
  have hx₀ : orderOf (Θ x) = r := by
    rw [hrdef]
    exact Θ.orderOf_eq x
  have hKcardC : Nat.card (GaloisField p (3 * f)) = (p ^ f) ^ 3 := by
    rw [GaloisField.card p (3 * f) (by omega), pow_mul']
  have hmain := uc22d4_unique_sl2_or_rank (ℓ := p) hp hp5 hf
    (GaloisField p (3 * f)) hKcardC σK hσK hr hr3 hrq (Θ x) hx₀
  have hLle : L ≤ centralizer ({x} : Set X) := by
    rw [← hCK]
    exact Subgroup.centralizer_le fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hxK
  have hL'le : L' ≤ centralizer ({x} : Set X) := by
    rw [← hCK']
    exact Subgroup.centralizer_le fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hxK'
  have hLmap : L.map Θ.toMonoidHom ≤ centralizer ({Θ x} : Set _) := by
    refine (Subgroup.map_mono hLle).trans ?_
    simpa only [MulEquiv.coe_toMonoidHom, Set.image_singleton] using
      (Subgroup.map_centralizer_le_centralizer_image ({x} : Set X) Θ.toMonoidHom)
  have hL'map : L'.map Θ.toMonoidHom ≤ centralizer ({Θ x} : Set _) := by
    refine (Subgroup.map_mono hL'le).trans ?_
    simpa only [MulEquiv.coe_toMonoidHom, Set.image_singleton] using
      (Subgroup.map_centralizer_le_centralizer_image ({x} : Set X) Θ.toMonoidHom)
  rcases hmain with huniq | hrank
  · left
    have hLeq : Nonempty (L.map Θ.toMonoidHom ≃* SL(2, GaloisField p f)) :=
      ⟨(Subgroup.equivMapOfInjective L Θ.toMonoidHom Θ.injective).symm.trans eL⟩
    have hL'eq : Nonempty (L'.map Θ.toMonoidHom ≃* SL(2, GaloisField p f)) :=
      ⟨(Subgroup.equivMapOfInjective L' Θ.toMonoidHom Θ.injective).symm.trans eL'⟩
    have hmap := huniq (L.map Θ.toMonoidHom) (L'.map Θ.toMonoidHom) hLmap hL'map
      (GaloisField p f) (GaloisField p f) (GaloisField.card p f (by omega))
      (GaloisField.card p f (by omega)) hLeq hL'eq
    have hLL' : L = L' := Subgroup.map_injective Θ.injective hmap
    rw [← hCL, ← hCL', hLL']
  · right
    have hCent : (centralizer ({Θ x} : Set _)).map Θ.symm.toMonoidHom =
        centralizer ({x} : Set X) := by
      ext y
      constructor
      · intro hy
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
        rw [Subgroup.mem_centralizer_singleton_iff] at ha ⊢
        have h := congrArg (fun z => Θ.symm z) ha
        rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h
        simpa only [MulEquiv.coe_toMonoidHom] using h
      · intro hy
        rw [Subgroup.mem_map]
        refine ⟨Θ y, ?_, ?_⟩
        · rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
          have h := congrArg (fun z => Θ z) hy
          rw [map_mul, map_mul] at h
          simpa only [MulEquiv.coe_toMonoidHom] using h
        · rw [MulEquiv.coe_toMonoidHom]
          exact Θ.symm_apply_apply y
    have hle := CFSG.SectionRank.pRank_le_map (p := p) hp.one_lt Θ.symm.toMonoidHom
      Θ.symm.injective (centralizer ({Θ x} : Set _))
    rw [hCent] at hle
    exact le_trans hrank hle

end CFSG.LocalAnalysis.UniquenessCase.UC22
