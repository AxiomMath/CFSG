module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148NCent
import CFSG.RankThree.PartTwo.Sec14.Ronan148NKFModel
import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofPGLFacts

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148N

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

theorem kf148PGLCentAct : KF148PGLCentAct := by
  intro Γ _ _ J E p f _ hX hJp hEJ a haJ ha1 ha3 t ht hta
  classical
  have hJnt : Nontrivial ↥J := ⟨⟨⟨a, haJ⟩, 1, fun h => ha1 (congrArg Subtype.val h)⟩⟩
  obtain ⟨π, K, _, hK, hq, φ, h1, hsurj, hmem⟩ :=
    Item148Res6.exists_tau_of_isZ3PGLThreeAt hX hJp hJnt hEJ
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hJX : J ≤ J ⊔ E := le_sup_left
  have hXN : J ⊔ E ≤ Subgroup.normalizer (J : Set Γ) := sup_le Subgroup.le_normalizer hEJ
  set τ : ↥J →* ProjGenLinGroup (Fin 3) K :=
    (projImage (glPi π 3 (p ^ f) K)).subtype.comp
      ((MonoidHom.snd _ _).comp (φ.toMonoidHom.comp (Subgroup.inclusion hJX))) with hτ
  have hτapp : ∀ j : ↥J, τ j =
      ((φ (Subgroup.inclusion hJX j)).2 : ProjGenLinGroup (Fin 3) K) := fun j => rfl
  have hτinj : Function.Injective τ := by
    rw [injective_iff_map_eq_one]
    intro j hj
    have h2 : (φ (Subgroup.inclusion hJX j)).2 = 1 := Subtype.ext (by rw [← hτapp]; exact hj)
    have h12 : φ (Subgroup.inclusion hJX j) = 1 := Prod.ext (h1 j) h2
    have h3 : Subgroup.inclusion hJX j = 1 := φ.injective (h12.trans (map_one φ).symm)
    exact Subgroup.inclusion_injective hJX (h3.trans (map_one _).symm)
  have hconj : ∀ (x : ↥(J ⊔ E)) (j : ↥J) (hj : (x : Γ) * (j : Γ) * (x : Γ)⁻¹ ∈ J),
      τ ⟨_, hj⟩ = ((φ x).2 : ProjGenLinGroup (Fin 3) K) * τ j *
        ((φ x).2 : ProjGenLinGroup (Fin 3) K)⁻¹ := by
    intro x j hj
    have e1 : Subgroup.inclusion hJX ⟨_, hj⟩ = x * Subgroup.inclusion hJX j * x⁻¹ :=
      Subtype.ext rfl
    rw [hτapp, hτapp, e1]
    simp only [map_mul, Prod.snd_mul, Subgroup.coe_mul]
    rw [map_inv φ x]
    rfl
  obtain ⟨xm, hxmL, hxm⟩ := hmem ⟨a, haJ⟩
  set xt : ↥(J ⊔ E) := ⟨t, ht⟩ with hxt
  obtain ⟨g, hg, hgm⟩ := (φ xt).2.2
  have htJ : t ∈ Subgroup.normalizer (J : Set Γ) := hXN ht
  have hconjt : ∀ (j : ↥J), t * (j : Γ) * t⁻¹ ∈ J := fun j =>
    (Subgroup.mem_normalizer_iff.mp htJ j).mp j.2
  have hτt : ∀ (j : ↥J), τ ⟨_, hconjt j⟩ = ProjGenLinGroup.mk g * τ j *
      (ProjGenLinGroup.mk g)⁻¹ := by
    intro j
    rw [hconj xt j (hconjt j)]
    congr 2 <;> simp [hgm]
  have hτa : τ ⟨a, haJ⟩ = ProjGenLinGroup.mk xm := by rw [hτapp, ← hxm]
  have hgx : ProjGenLinGroup.mk g * ProjGenLinGroup.mk xm =
      ProjGenLinGroup.mk xm * ProjGenLinGroup.mk g := by
    have hta' : t * a * t⁻¹ = a := by rw [hta, mul_inv_cancel_right]
    have e1 := hτt ⟨a, haJ⟩
    have e2 : (⟨t * a * t⁻¹, hconjt ⟨a, haJ⟩⟩ : ↥J) = ⟨a, haJ⟩ := Subtype.ext hta'
    rw [e2, hτa] at e1
    calc ProjGenLinGroup.mk g * ProjGenLinGroup.mk xm =
        ProjGenLinGroup.mk g * ProjGenLinGroup.mk xm * (ProjGenLinGroup.mk g)⁻¹ *
          ProjGenLinGroup.mk g := by group
      _ = ProjGenLinGroup.mk xm * ProjGenLinGroup.mk g := by rw [← e1]
  have hx1 : ProjGenLinGroup.mk xm ≠ 1 := by
    intro h
    apply ha1
    have h2 : τ ⟨a, haJ⟩ = τ 1 := by rw [hτa, h, map_one]
    exact congrArg Subtype.val (hτinj h2)
  have hx3 : ProjGenLinGroup.mk xm ^ 3 = 1 := by
    rw [← hτa, ← map_pow]
    have h2 : (⟨a, haJ⟩ : ↥J) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
    rw [h2, map_one]
  obtain ⟨c, hc, hcx, hcg, hcm⟩ := model_kf148 hK hq hxmL hx1 hx3 hg hgx
  have hgc : g * c⁻¹ ∈ slPi π 3 (p ^ f) K := by
    have := conj_mem_slPi hπ hc hcg
    rwa [show c * (c⁻¹ * g) * c⁻¹ = g * c⁻¹ by group] at this
  obtain ⟨s, hs⟩ := hsurj (ProjGenLinGroup.mk (g * c⁻¹)) ⟨g * c⁻¹, hgc, rfl⟩
  have hτs : τ s = ProjGenLinGroup.mk (g * c⁻¹) := by rw [hτapp]; exact hs
  have hscomm : τ s * ProjGenLinGroup.mk xm = ProjGenLinGroup.mk xm * τ s := by
    rw [hτs, map_mul, map_inv]
    have hcx' : (ProjGenLinGroup.mk c)⁻¹ * ProjGenLinGroup.mk xm =
        ProjGenLinGroup.mk xm * (ProjGenLinGroup.mk c)⁻¹ := by
      calc (ProjGenLinGroup.mk c)⁻¹ * ProjGenLinGroup.mk xm =
          (ProjGenLinGroup.mk c)⁻¹ * (ProjGenLinGroup.mk xm * ProjGenLinGroup.mk c) *
            (ProjGenLinGroup.mk c)⁻¹ := by group
        _ = (ProjGenLinGroup.mk c)⁻¹ * (ProjGenLinGroup.mk c * ProjGenLinGroup.mk xm) *
            (ProjGenLinGroup.mk c)⁻¹ := by rw [hcx]
        _ = ProjGenLinGroup.mk xm * (ProjGenLinGroup.mk c)⁻¹ := by group
    calc ProjGenLinGroup.mk g * (ProjGenLinGroup.mk c)⁻¹ * ProjGenLinGroup.mk xm =
        ProjGenLinGroup.mk g * ((ProjGenLinGroup.mk c)⁻¹ * ProjGenLinGroup.mk xm) := by group
      _ = ProjGenLinGroup.mk g * (ProjGenLinGroup.mk xm * (ProjGenLinGroup.mk c)⁻¹) := by
          rw [hcx']
      _ = (ProjGenLinGroup.mk g * ProjGenLinGroup.mk xm) * (ProjGenLinGroup.mk c)⁻¹ := by group
      _ = (ProjGenLinGroup.mk xm * ProjGenLinGroup.mk g) * (ProjGenLinGroup.mk c)⁻¹ := by
          rw [hgx]
      _ = ProjGenLinGroup.mk xm * (ProjGenLinGroup.mk g * (ProjGenLinGroup.mk c)⁻¹) := by group
  refine ⟨s, Subgroup.mem_inf.mpr ⟨s.2, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : τ (s * ⟨a, haJ⟩) = τ (⟨a, haJ⟩ * s) := by
      rw [map_mul, map_mul, hτa, hscomm]
    exact congrArg Subtype.val (hτinj h2)
  · intro y hy
    have hyC : y ∈ J ⊓ Subgroup.centralizer ({a} : Set Γ) := pPrimeCoreOf_le 3 _ hy
    have hyJ : y ∈ J := hyC.1
    have hya : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp hyC.2
    have hy3 : Nat.Coprime 3 (orderOf y) := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ hy)
        (coprime_card_pPrimeCoreOf 3 _)
    obtain ⟨m, hmL, hmy⟩ := hmem ⟨y, hyJ⟩
    have hτy : τ ⟨y, hyJ⟩ = ProjGenLinGroup.mk m := by rw [hτapp, ← hmy]
    have hmx : ProjGenLinGroup.mk m * ProjGenLinGroup.mk xm =
        ProjGenLinGroup.mk xm * ProjGenLinGroup.mk m := by
      rw [← hτy, ← hτa, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hya
    have hmord : Nat.Coprime 3 (orderOf (ProjGenLinGroup.mk m)) := by
      rw [← hτy, orderOf_injective τ hτinj, Subgroup.orderOf_mk]
      exact hy3
    have hcmc := hcm m hmL hmx hmord
    have hsy : (s : Γ) * y * (s : Γ)⁻¹ ∈ J := J.mul_mem (J.mul_mem s.2 hyJ) (J.inv_mem s.2)
    have e1 : τ ⟨_, hconjt ⟨y, hyJ⟩⟩ = τ ⟨_, hsy⟩ := by
      rw [hτt, hτy]
      have e2 : (⟨(s : Γ) * y * (s : Γ)⁻¹, hsy⟩ : ↥J) = s * ⟨y, hyJ⟩ * s⁻¹ := Subtype.ext rfl
      rw [e2, map_mul, map_mul, map_inv, hτs, hτy, map_mul, map_inv]
      calc ProjGenLinGroup.mk g * ProjGenLinGroup.mk m * (ProjGenLinGroup.mk g)⁻¹ =
          ProjGenLinGroup.mk g * (ProjGenLinGroup.mk c)⁻¹ *
            (ProjGenLinGroup.mk c * ProjGenLinGroup.mk m) * (ProjGenLinGroup.mk g)⁻¹ := by group
        _ = ProjGenLinGroup.mk g * (ProjGenLinGroup.mk c)⁻¹ *
            (ProjGenLinGroup.mk m * ProjGenLinGroup.mk c) * (ProjGenLinGroup.mk g)⁻¹ := by
          rw [hcmc]
        _ = ProjGenLinGroup.mk g * (ProjGenLinGroup.mk c)⁻¹ * ProjGenLinGroup.mk m *
            (ProjGenLinGroup.mk g * (ProjGenLinGroup.mk c)⁻¹)⁻¹ := by group
    exact congrArg Subtype.val (hτinj e1)

theorem step148PGLCent_of_ind'
    (h134 : Item134)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (hInd : Step148PGLCentInd) : Step148PGLCent :=
  step148PGLCent_of_ind h134 h48 h415 kf148PGLCentAct hInd

end CFSG.RankThree.PartTwo.Sec14.Ronan148N
