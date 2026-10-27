module

public import CFSG.Quasithin.Background.A1bBasic
import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup
open CFSG.Quasithin.A1b
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem wc819sa_exists_conj_of_isSylowIn {p : ℕ} [Fact p.Prime]
    {V P P' : Subgroup G} (hP : IsSylowIn p P V) (hP' : IsSylowIn p P' V) :
    ∃ v ∈ V, ∀ x : G, x ∈ P' ↔ v⁻¹ * x * v ∈ P := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥V hP.toSylow hP'.toSylow
  have hg' : MulAut.conj g • (hP.toSylow : Subgroup ↥V) = (hP'.toSylow : Subgroup ↥V) := by
    rw [← Sylow.coe_subgroup_smul (g := g) (P := hP.toSylow), hg]
  refine ⟨(g : G), g.2, fun x => ?_⟩
  constructor
  · intro hx
    have hxV : x ∈ V := hP'.le hx
    have hmem : (⟨x, hxV⟩ : ↥V) ∈ (hP'.toSylow : Subgroup ↥V) := hx
    rw [← hg', Subgroup.mem_smul_pointwise_iff_exists] at hmem
    obtain ⟨s, hs, hsx⟩ := hmem
    have hval : (g : G)⁻¹ * x * g = (s : G) := by
      have h2 : ((MulAut.conj g • s : ↥V) : G) = x := congrArg Subtype.val hsx
      simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
      rw [← h2]; group
    rw [hval]
    exact hs
  · intro hx
    have hxV : (g : G)⁻¹ * x * g ∈ V := hP.le hx
    have hxV' : x ∈ V := by
      have := V.mul_mem (V.mul_mem g.2 hxV) (V.inv_mem g.2)
      simpa [mul_assoc] using this
    have hmem : (⟨x, hxV'⟩ : ↥V) ∈ (hP'.toSylow : Subgroup ↥V) := by
      rw [← hg', Subgroup.mem_smul_pointwise_iff_exists]
      refine ⟨⟨(g : G)⁻¹ * x * g, hxV⟩, hx, ?_⟩
      apply Subtype.ext
      simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    exact hmem

private theorem wc819sa_isSylowIn_conj_iff {p : ℕ} (g : G) {P H : Subgroup G} :
    IsSylowIn p (conjSub g P) (conjSub g H) ↔ IsSylowIn p P H := by
  unfold conjSub
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective).mp h.1
    · exact h.2.1.of_equiv (Subgroup.equivMapOfInjective P _ (MulAut.conj g).injective).symm
    · rw [← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) P H
        (MulAut.conj g).injective]
      exact h.2.2
  · intro h
    refine ⟨Subgroup.map_mono h.le, h.isPGroup.map _, ?_⟩
    rw [Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) P H
      (MulAut.conj g).injective]
    exact h.not_dvd_relIndex

private theorem wc819sa_isSylowIn_two_of_sup_inf {N S : Subgroup G}
    (hSN : S ≤ Subgroup.normalizer (N : Set G)) (hS2 : IsPGroup 2 S)
    (h : IsSylowIn 2 (S ⊓ N) N) : IsSylowIn 2 S (N ⊔ S) := by
  refine ⟨le_sup_right, hS2, ?_⟩
  have hri := B6.relIndex_inf_eq_relIndex_sup hSN
  have e : S ⊔ N = N ⊔ S := sup_comm S N
  rw [e] at hri
  rw [← hri]
  exact h.not_dvd_relIndex

private theorem wc819sa_isSylowIn_two_of_le {P₁ P₂ K : Subgroup G} (h : IsSylowIn 2 P₁ K)
    (h12 : P₁ ≤ P₂) (h2K : P₂ ≤ K) (hP₂ : IsPGroup 2 P₂) : IsSylowIn 2 P₂ K :=
  ⟨h2K, hP₂, fun hd => h.not_dvd_relIndex (hd.trans (Subgroup.relIndex_dvd_of_le_left K h12))⟩

theorem exists_isSylowIn_three_good {J T : Subgroup G} (hTJ : T ≤ normalizer (J : Set G))
    (hT : IsPGroup 2 ↥T) (hS : IsSylowIn 2 (T ⊓ J) J) :
    ∃ Y : Subgroup G, IsSylowIn 3 Y J ∧
      IsSylowIn 2 (T ⊓ normalizer (Y : Set G)) ((J ⊔ T) ⊓ normalizer (Y : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDJ : J ⊔ T ≤ Subgroup.normalizer (J : Set G) :=
    sup_le Subgroup.le_normalizer hTJ
  have hTD : IsSylowIn 2 T (J ⊔ T) := wc819sa_isSylowIn_two_of_sup_inf hTJ hT hS
  obtain ⟨Y₀, hY₀syl, -⟩ :=
    exists_isSylowIn_ge 3 (H := J) (P := ⊥) bot_le IsPGroup.of_bot
  obtain ⟨R, hRsyl, -⟩ :=
    exists_isSylowIn_ge 2 (H := (J ⊔ T) ⊓ Subgroup.normalizer (Y₀ : Set G)) (P := ⊥)
      bot_le IsPGroup.of_bot
  have hRD : R ≤ J ⊔ T := hRsyl.le.trans inf_le_left
  obtain ⟨R', hR'syl, hRR'⟩ := exists_isSylowIn_ge 2 hRD hRsyl.isPGroup
  obtain ⟨d, hdD, hdconj⟩ := wc819sa_exists_conj_of_isSylowIn hR'syl hTD
  have hdconj' : conjSub d R' = T := by
    ext x
    rw [mem_conjSub_iff, ← hdconj x]
  have hdJ : d ∈ Subgroup.normalizer (J : Set G) := hDJ hdD
  have hconjJ : conjSub d J = J := Subgroup.mem_normalizer_iff_map_conj_eq.mp hdJ
  have hconjD : conjSub d (J ⊔ T) = J ⊔ T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hdD)
  let Y : Subgroup G := conjSub d Y₀
  have hYsyl : IsSylowIn 3 Y J := by
    have h := (wc819sa_isSylowIn_conj_iff (p := 3) d).mpr hY₀syl
    rwa [hconjJ] at h
  refine ⟨Y, hYsyl, ?_⟩
  have hnorm : (Subgroup.normalizer (Y₀ : Set G)).map (MulAut.conj d).toMonoidHom =
      Subgroup.normalizer (Y : Set G) := by
    change conjSub d (Subgroup.normalizer (Y₀ : Set G)) = Subgroup.normalizer (Y : Set G)
    rw [conjSub_normalizer]
  have hconjN : conjSub d ((J ⊔ T) ⊓ Subgroup.normalizer (Y₀ : Set G)) =
      (J ⊔ T) ⊓ Subgroup.normalizer (Y : Set G) := by
    rw [conjSub,
      Subgroup.map_inf (J ⊔ T) (Subgroup.normalizer (Y₀ : Set G))
        (MulAut.conj d).toMonoidHom (MulAut.conj d).injective,
      show (J ⊔ T).map (MulAut.conj d).toMonoidHom = J ⊔ T from hconjD, hnorm]
  have hconjRsyl : IsSylowIn 2 (conjSub d R)
      ((J ⊔ T) ⊓ Subgroup.normalizer (Y : Set G)) := by
    have h := (wc819sa_isSylowIn_conj_iff (p := 2) d).mpr hRsyl
    rwa [hconjN] at h
  have hconjR_le_T : conjSub d R ≤ T := by
    have hle : conjSub d R ≤ conjSub d R' := conjSub_mono d hRR'
    rwa [hdconj'] at hle
  have hle : conjSub d R ≤ T ⊓ Subgroup.normalizer (Y : Set G) :=
    le_inf hconjR_le_T (hconjRsyl.le.trans inf_le_right)
  have h2K : T ⊓ Subgroup.normalizer (Y : Set G) ≤
      (J ⊔ T) ⊓ Subgroup.normalizer (Y : Set G) :=
    le_inf (inf_le_left.trans le_sup_right) inf_le_right
  have hP₂ : IsPGroup 2 (T ⊓ Subgroup.normalizer (Y : Set G) : Subgroup G) :=
    IsPGroup.to_inf_left (H := T) (K := Subgroup.normalizer (Y : Set G)) hT
  exact wc819sa_isSylowIn_two_of_le hconjRsyl hle h2K hP₂

end CFSG.LocalAnalysis.WeakClosure81

end
