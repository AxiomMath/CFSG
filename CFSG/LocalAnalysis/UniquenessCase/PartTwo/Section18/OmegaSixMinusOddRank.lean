module

public import CFSG.Open.StatedDefs
public import CFSG.LieType.BorelTits.OrthogonalModels
public import CFSG.Quasithin.Background.HStandard
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem two_mul_le_rkIdx_of_odd_omegaMinus {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K}
    (hg : g ∈ StatedOmega (StatedQuadMinus 3 K b c)) (hg1 : g ≠ 1)
    (hodd : Odd (orderOf g)) :
    2 * n ≤ rkIdx (fixV (Subgroup.zpowers (matAut g))) := by
  classical
  let Φ : QuadForm K (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :=
    quadMinusForm 3 K b c hirr
  let H : Subgroup (GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) :=
    StatedOmega (StatedQuadMinus 3 K b c)
  have hgH : g ∈ H := hg
  let h : H := ⟨g, hgH⟩
  set T : Module.End K (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) := natRep H h with hT
  set W : Submodule K (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :=
    LinearMap.ker (T - 1) with hWdef
  have hcard : Fintype.card (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) = 6 := by simp
  have hρ : IsIsometric Φ.polar (natRep H) := isIsometric_natRep_statedOmega Φ
  have hTv : ∀ v, T v =
      (g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
        (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) *ᵥ v := by
    intro v
    rw [hT, natRep_apply]
  have hWT : ∀ v, v ∈ W ↔ T v = v := by
    intro v
    change (T - 1) v = 0 ↔ T v = v
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact Iff.rfl
  have hW : ∀ v, v ∈ W ↔ toAddMap (matAut g) v = v := by
    intro v
    rw [hWT v, hTv v, toAddMap_matAut]
  have hrk : rkIdx (fixV (Subgroup.zpowers (matAut g))) =
      n * (6 - Module.finrank K W) := by
    have := rkIdx_fixV_eq_of_linear (K := K)
      (ι := Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) (m := n) hK (g := matAut g) W hW
    simpa [hcard] using this
  have hne6 : Module.finrank K W ≠ 6 := by
    intro h6
    have htop : W = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [h6, Module.finrank_fintype_fun_eq_card, hcard]
    have hT1 : T = 1 := by
      apply LinearMap.ext
      intro v
      have hv : v ∈ W := by rw [htop]; trivial
      exact (hWT v).mp hv
    have hH1 : h = 1 := natRep_injective H (by
      change T = natRep H 1
      rw [hT1, map_one])
    exact hg1 (by
      have hval : (h : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) = g := rfl
      rw [← hval]
      simpa using congrArg Subtype.val hH1)
  have hne5 : Module.finrank K W ≠ 5 := by
    intro hW5
    have hWne : W ≠ ⊤ := by
      intro htop
      have h6 : Module.finrank K W = 6 := by
        rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card, hcard]
      omega
    obtain ⟨u, -, huW⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hWne)
    have hu_ne : u ≠ 0 := by
      intro h0
      apply huW
      rw [h0]
      exact W.zero_mem
    have hsup_of_notMem : ∀ {y : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K},
        y ∉ W → W ⊔ Submodule.span K {y} = ⊤ := by
      intro y hy
      apply Submodule.eq_top_of_finrank_eq
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span K {y})
      have h2 : W ⊓ Submodule.span K {y} = ⊥ := by
        rw [eq_bot_iff]
        intro z hz
        obtain ⟨hzW, hzspan⟩ := Submodule.mem_inf.mp hz
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hzspan
        rw [Submodule.mem_bot]
        by_cases ha : a = 0
        · simp [ha]
        · exfalso
          apply hy
          have := W.smul_mem a⁻¹ hzW
          rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this
      have h3 : Module.finrank K (Submodule.span K {y}) = 1 :=
        finrank_span_singleton (fun h => hy (by rw [h]; exact W.zero_mem))
      rw [h2, finrank_bot, hW5, h3, add_zero] at h1
      rw [h1, Module.finrank_fintype_fun_eq_card, hcard]
    have hsup_u := hsup_of_notMem huW
    have hρT : ∀ a b, Φ.polar.β (T a) (T b) = Φ.polar.β a b := by
      intro a b
      simpa [hT] using hρ h a b
    have hperp_le : Φ.polar.perp W ≤ W := by
      intro x hx
      by_contra hxW
      have hsup_x := hsup_of_notMem hxW
      have hxalt : Φ.polar.β x x = 0 := by
        rw [QuadForm.polar_self Φ x]
        change ((2 : ℕ) : K) * Φ.Q x = 0
        rw [CharP.cast_eq_zero K 2, zero_mul]
      have hxzero : ∀ y, Φ.polar.β x y = 0 := by
        intro y
        have hy : y ∈ W ⊔ Submodule.span K {x} := by rw [hsup_x]; trivial
        obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
        rw [Φ.polar.add_right, Φ.polar.smul_right, Φ.polar.refl w x (hx w hw), hxalt,
          mul_zero, add_zero]
      exact hxW (by
        have hx0 : x = 0 := Φ.polar.nondeg x hxzero
        rw [hx0]
        exact W.zero_mem)
    have hTuW : T u - u ∈ W := by
      apply hperp_le
      rw [Φ.polar.mem_perp]
      intro w hw
      have hwfix : T w = w := (hWT w).mp hw
      calc Φ.polar.β w (T u - u)
          = Φ.polar.β w (T u) - Φ.polar.β w u := Φ.polar.β_sub_right w (T u) u
        _ = Φ.polar.β (T w) (T u) - Φ.polar.β w u := by rw [hwfix]
        _ = Φ.polar.β w u - Φ.polar.β w u := by rw [hρT w u]
        _ = 0 := sub_self _
    have hT2u : T (T u) = u := by
      have h1 : T (T u) - T u = T u - u := by
        simpa only [map_sub] using (hWT (T u - u)).mp hTuW
      have h2u : T u + T u = 0 := by
        rw [← two_smul K (T u)]
        change ((2 : ℕ) : K) • T u = 0
        rw [CharP.cast_eq_zero K 2, zero_smul]
      have hu2 : u + u = 0 := by
        rw [← two_smul K u]
        change ((2 : ℕ) : K) • u = 0
        rw [CharP.cast_eq_zero K 2, zero_smul]
      have hneg : -u = u := (add_eq_zero_iff_neg_eq').mp hu2
      calc T (T u) = (T u - u) + T u := eq_add_of_sub_eq h1
        _ = (T u + T u) - u := by abel
        _ = 0 - u := by rw [h2u]
        _ = -u := zero_sub u
        _ = u := hneg
    have hT2 : T ^ 2 = 1 := by
      apply LinearMap.ext
      intro v
      have hv : v ∈ W ⊔ Submodule.span K {u} := by rw [hsup_u]; trivial
      obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have hwfix : T w = w := (hWT w).mp hw
      change T (T (w + a • u)) = w + a • u
      calc T (T (w + a • u))
          = T (T w + a • T u) := by
              congr 1
              rw [map_add, map_smul]
        _ = T (T w) + a • T (T u) := by rw [map_add, map_smul]
        _ = w + a • u := by simp only [hwfix, hT2u]
    have hH2 : h ^ 2 = 1 :=
      natRep_injective H (by
        rw [map_pow, map_one]
        change T ^ 2 = 1
        exact hT2)
    have hg2 : g ^ 2 = 1 := by
      have := congrArg Subtype.val hH2
      simpa using this
    have ho1 : orderOf g = 1 := by
      have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
      have hne2 : orderOf g ≠ 2 := by
        intro h
        exact hodd.not_two_dvd_nat (by rw [h])
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact h
      · exact absurd h hne2
    exact hg1 (orderOf_eq_one_iff.mp ho1)
  have hle : Module.finrank K W ≤ 6 := by
    have := Submodule.finrank_le W
    rwa [Module.finrank_fintype_fun_eq_card, hcard] at this
  have hcodim : 2 ≤ 6 - Module.finrank K W := by omega
  rw [hrk]
  calc 2 * n = n * 2 := by ring
    _ ≤ n * (6 - Module.finrank K W) := Nat.mul_le_mul_left n hcodim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
