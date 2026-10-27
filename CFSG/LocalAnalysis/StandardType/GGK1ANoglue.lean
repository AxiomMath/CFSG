module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs
public import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.StandardType.GGSporKLieZSU
public import CFSG.LocalAnalysis.StandardType.GGSporKLieZQuot

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LieType.SemisimpleCentralizers.HeldLang

private theorem ggK1An_card_subgroup_units_dvd {K : Type} [Field K] [Finite K]
    (C : Subgroup Kˣ) (n : ℕ) (h : ∀ c ∈ C, c ^ n = 1) : Nat.card C ∣ n := by
  haveI : Finite Kˣ := Finite.of_injective (fun u : Kˣ => (u : K)) Units.val_injective
  haveI : Finite ↥C := Finite.of_injective (fun c : ↥C => (c : Kˣ)) Subtype.val_injective
  haveI : IsCyclic ↥C := subgroup_units_cyclic C
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥C)
  have hgn : g ^ n = 1 := by
    apply Subtype.ext
    simpa using h (g : Kˣ) g.2
  have hdiv : orderOf g ∣ n := orderOf_dvd_of_pow_eq_one hgn
  simpa [hg] using hdiv

private theorem ggK1An_card_scalars_subgroupOf_dvd_dim {N : ℕ} {K : Type} [Field K] [Finite K]
    (H : Subgroup (GL (Fin N) K))
    (hH : H ≤ (Matrix.GeneralLinearGroup.det : GL (Fin N) K →* Kˣ).ker) :
    Nat.card ↥((LargeEvenScalars (Fin N) K).subgroupOf H) ∣ N := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    exact dvd_zero _
  · haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
    set f : Kˣ →* GL (Fin N) K := Matrix.GeneralLinearGroup.scalar (Fin N) with hf
    have hfinj : Function.Injective f := by
      intro c c' hcc
      apply Units.ext
      have h := congrArg (fun g : GL (Fin N) K => (g : Matrix (Fin N) (Fin N) K)) hcc
      simpa [f, Matrix.GeneralLinearGroup.coe_scalar] using h
    have hC : Nat.card ↥(H.comap f) ∣ N := by
      refine ggK1An_card_subgroup_units_dvd (H.comap f) N ?_
      intro c hc
      have hmem : f c ∈ H := hc
      have hdet := hH hmem
      rw [MonoidHom.mem_ker] at hdet
      rw [show (f c : GL (Fin N) K) = Matrix.GeneralLinearGroup.scalar (Fin N) c from rfl,
        Matrix.GeneralLinearGroup.det_scalar] at hdet
      simpa [f] using hdet
    have hcardC : Nat.card ↥(H.comap f) = Nat.card ↥(f.range ⊓ H) := by
      rw [← Subgroup.map_comap_eq (f := f) H]
      exact Nat.card_congr (Subgroup.equivMapOfInjective (H.comap f) f hfinj).toEquiv
    have hcardZ : Nat.card ↥((f.range).subgroupOf H) = Nat.card ↥(f.range ⊓ H) := by
      rw [← Subgroup.subgroupOf_map_subtype f.range H]
      exact Nat.card_congr
        (Subgroup.equivMapOfInjective ((f.range).subgroupOf H) H.subtype
          H.subtype_injective).toEquiv
    have hZeq : Nat.card ↥((LargeEvenScalars (Fin N) K).subgroupOf H) =
        Nat.card ↥(H.comap f) := by
      rw [show (LargeEvenScalars (Fin N) K) = f.range from rfl, hcardZ, ← hcardC]
    rw [hZeq]
    exact hC

private theorem ggK1An_noglue_abstract {G R : Type} [Group G] [Finite G] [Group R]
    (π : G →* R) (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center G)
    {p : ℕ} {x : G} (hx : x ^ p = 1) (hcop : Nat.Coprime p (Nat.card π.ker)) :
    Subgroup.centralizer ({π x} : Set R) =
      (Subgroup.centralizer ({x} : Set G)).map π := by
  apply le_antisymm
  · intro ybar hy
    obtain ⟨y, rfl⟩ := hπ ybar
    rw [Subgroup.mem_map]
    refine ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    set w : G := y * x * y⁻¹ * x⁻¹ with hw
    have hwmem : w ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      calc π w = π y * π x * (π y)⁻¹ * (π x)⁻¹ := by simp only [hw, map_mul, map_inv]
        _ = (π x * π y) * (π y)⁻¹ * (π x)⁻¹ := by rw [hy]
        _ = 1 := by group
    have hwcenter : w ∈ Subgroup.center G := hker hwmem
    have hwp : w ^ p = 1 := by
      have hcomm : Commute w x := ((Subgroup.mem_center_iff.mp hwcenter) x).symm
      have hconj : y * x * y⁻¹ = w * x := by rw [hw]; group
      calc w ^ p = w ^ p * x ^ p := by rw [hx, mul_one]
        _ = (w * x) ^ p := (hcomm.mul_pow p).symm
        _ = (y * x * y⁻¹) ^ p := by rw [← hconj]
        _ = (MulAut.conj y x) ^ p := by rw [MulAut.conj_apply]
        _ = MulAut.conj y (x ^ p) := (map_pow (MulAut.conj y) x p).symm
        _ = MulAut.conj y 1 := by rw [hx]
        _ = 1 := by rw [map_one]
    have hw1 : w = 1 := by
      have h1 : orderOf w ∣ p := orderOf_dvd_of_pow_eq_one hwp
      have h2 : orderOf w ∣ Nat.card π.ker := Subgroup.orderOf_dvd_natCard _ hwmem
      have hcop' : Nat.Coprime (orderOf w) (Nat.card π.ker) :=
        Nat.Coprime.of_dvd_left h1 hcop
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop' (dvd_refl _) h2)
    have hwx : w * x = y * x * y⁻¹ := by rw [hw]; group
    calc y * x = (y * x * y⁻¹) * y := by group
      _ = x * y := by rw [← hwx, hw1, one_mul]
  · rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz' : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.mp hz
    rw [← map_mul, ← map_mul, hz']

theorem ggK1A_noglue {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (hnotRA : ¬ (p ∣ N ∧ p ∣ 2 ^ nf - 1))
    {xhat : ↥(LargeEvenSLGroup (Fin N) K)} (hxp : xhat ^ p = 1) :
    Subgroup.centralizer
        ({LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) xhat} :
          Set (LargeEvenProj (LargeEvenSLGroup (Fin N) K))) =
      (Subgroup.centralizer ({xhat} : Set ↥(LargeEvenSLGroup (Fin N) K))).map
        (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) := by
  classical
  let Z0 := (LargeEvenScalars (Fin N) K).subgroupOf (LargeEvenSLGroup (Fin N) K)
  have hker_eq : (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)).ker = Z0 :=
    QuotientGroup.ker_mk' _
  have hker_center : (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)).ker ≤
      Subgroup.center ↥(LargeEvenSLGroup (Fin N) K) := by
    rw [hker_eq]
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  have hSLle : LargeEvenSLGroup (Fin N) K ≤
      (Matrix.GeneralLinearGroup.det : GL (Fin N) K →* Kˣ).ker := le_refl _
  have hdivN : Nat.card Z0 ∣ N :=
    ggK1An_card_scalars_subgroupOf_dvd_dim (LargeEvenSLGroup (Fin N) K) hSLle
  have hdivQ : Nat.card Z0 ∣ Nat.card K - 1 :=
    CFSG.StandardType.SporadicShape.card_statedScalars_subgroupOf_dvd
      (LargeEvenSLGroup (Fin N) K)
  have hdiv : Nat.card Z0 ∣ Nat.gcd N (2 ^ nf - 1) := by
    rw [hK] at hdivQ
    exact Nat.dvd_gcd hdivN hdivQ
  have hpg : Nat.Coprime p (Nat.gcd N (2 ^ nf - 1)) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    exact hnotRA ⟨hd.trans (Nat.gcd_dvd_left N (2 ^ nf - 1)),
      hd.trans (Nat.gcd_dvd_right N (2 ^ nf - 1))⟩
  have hcop : Nat.Coprime p (Nat.card Z0) := Nat.Coprime.of_dvd_right hdiv hpg
  have hcop' : Nat.Coprime p
      (Nat.card (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)).ker) := by
    rw [hker_eq]
    exact hcop
  exact ggK1An_noglue_abstract (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
    (QuotientGroup.mk'_surjective Z0) hker_center hxp hcop'

theorem ggK1A_uni_noglue {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hnotRAu : ¬ (p ∣ N ∧ p ∣ 2 ^ nf + 1))
    {xhat : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf))} (hxp : xhat ^ p = 1) :
    Subgroup.centralizer
        ({LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)) xhat} :
          Set (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ nf)))) =
      (Subgroup.centralizer ({xhat} : Set ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf)))).map
        (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf))) := by
  classical
  let Z0 := (LargeEvenScalars (Fin N) K).subgroupOf (LargeEvenSUGroup (Fin N) K (2 ^ nf))
  have hker_eq : (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf))).ker = Z0 :=
    QuotientGroup.ker_mk' _
  have hker_center : (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf))).ker ≤
      Subgroup.center ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf)) := by
    rw [hker_eq]
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  have hSUle : LargeEvenSUGroup (Fin N) K (2 ^ nf) ≤
      (Matrix.GeneralLinearGroup.det : GL (Fin N) K →* Kˣ).ker := by
    change StatedSU N (2 ^ nf) K ≤ _
    rw [← CFSG.Open.StatedAPI.statedSL_eq_ker_det N K]
    exact CFSG.Open.StatedAPI.statedSU_le_statedSL N (2 ^ nf) K
  have hdivN : Nat.card Z0 ∣ N :=
    ggK1An_card_scalars_subgroupOf_dvd_dim (LargeEvenSUGroup (Fin N) K (2 ^ nf)) hSUle
  have hdivQ : Nat.card Z0 ∣ 2 ^ nf + 1 :=
    CFSG.StandardType.SporadicShape.card_statedScalars_subgroupOf_statedSU_dvd N (2 ^ nf) hK
  have hdiv : Nat.card Z0 ∣ Nat.gcd N (2 ^ nf + 1) := Nat.dvd_gcd hdivN hdivQ
  have hpg : Nat.Coprime p (Nat.gcd N (2 ^ nf + 1)) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hd
    exact hnotRAu ⟨hd.trans (Nat.gcd_dvd_left N (2 ^ nf + 1)),
      hd.trans (Nat.gcd_dvd_right N (2 ^ nf + 1))⟩
  have hcop : Nat.Coprime p (Nat.card Z0) := Nat.Coprime.of_dvd_right hdiv hpg
  have hcop' : Nat.Coprime p
      (Nat.card (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf))).ker) := by
    rw [hker_eq]
    exact hcop
  exact ggK1An_noglue_abstract (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)))
    (QuotientGroup.mk'_surjective Z0) hker_center hxp hcop'

end CFSG.StandardType

end
