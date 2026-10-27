module

public import CFSG.RankThree.PartTwo.Sec8.Groups
import CFSG.RankThree.PartTwo.KFacts.K71Coprime
import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.PartTwo.Sec8.Pairs

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88F

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_centralizer_of_fixed {Y M : Subgroup G} (hMY : M ≤ Y) {d : G}
    (hdY : d ∈ Subgroup.normalizer (Y : Set G)) (hdM : d ∈ Subgroup.normalizer (M : Set G))
    (hd3 : d ^ 3 = 1) {m : G} (hm : m ∈ M)
    (hfix : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdY⟩)
        ((⟨m, hMY hm⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) =
      ((⟨m, hMY hm⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y)) :
    ∃ m' : M, (m' : G) ∈ Subgroup.centralizer ({d} : Set G) ∧
      ((⟨m', hMY m'.2⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) =
        ((⟨m, hMY hm⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ : Subgroup Y := aschbacherSolvableCore 3 Y with hθ
  set N : Subgroup M := θ.comap (Subgroup.inclusion hMY) with hN
  haveI hNn : N.Normal := Subgroup.normal_comap _
  have hNcard : ¬ 3 ∣ Nat.card N := by
    have hle : N.map (Subgroup.inclusion hMY) ≤ θ := by
      rintro _ ⟨n, hn, rfl⟩
      exact hn
    have h1 : Nat.card N = Nat.card (N.map (Subgroup.inclusion hMY)) :=
      (Subgroup.card_map_of_injective (Subgroup.inclusion_injective hMY)).symm
    rw [h1]
    exact fun h => KFacts.not_three_dvd_card_aschbacherSolvableCore Y
      (h.trans (Subgroup.card_dvd_of_le hle))
  set x : Subgroup.normalizer (M : Set G) := ⟨d, hdM⟩ with hx
  have hx3 : x ^ 3 = 1 := Subtype.ext (by simpa [hx] using hd3)
  set P : Subgroup (Subgroup.normalizer (M : Set G)) := Subgroup.zpowers x with hP
  have hPp : IsPGroup 3 P := by
    have hord : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h1 | h3
    · exact IsPGroup.of_card (n := 0) (by rw [hP, Nat.card_zpowers, h1]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [hP, Nat.card_zpowers, h3]; rfl)
  set φ : P →* MulAut M := M.normalizerMonoidHom.comp P.subtype with hφ
  have hPpow : ∀ g : P, ∃ k : ℤ, ((g : Subgroup.normalizer (M : Set G)) : G) = d ^ k := by
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    exact ⟨k, by rw [← hk]; simp [hx]⟩
  have hφN : ∀ g : P, ∀ n ∈ N, φ g n ∈ N := by
    intro g n hn
    obtain ⟨k, hk⟩ := hPpow g
    have hu : d ^ k ∈ Subgroup.normalizer (Y : Set G) := Subgroup.zpow_mem _ hdY k
    have h1 : Subgroup.inclusion hMY (φ g n) =
        Sec4.compAction Y ⟨d ^ k, hu⟩ (Subgroup.inclusion hMY n) := by
      apply Subtype.ext
      change ((g : Subgroup.normalizer (M : Set G)) : G) * (n : G) *
        ((g : Subgroup.normalizer (M : Set G)) : G)⁻¹ = d ^ k * (n : G) * (d ^ k)⁻¹
      rw [hk]
    rw [hN, Subgroup.mem_comap, h1]
    have hmap : θ.map (Sec4.compAction Y ⟨d ^ k, hu⟩ : Y →* Y) = θ :=
      Sec4.map_aschbacherSolvableCore (Sec4.compAction Y ⟨d ^ k, hu⟩)
    have hmem : (Sec4.compAction Y ⟨d ^ k, hu⟩) (Subgroup.inclusion hMY n) ∈
        θ.map (Sec4.compAction Y ⟨d ^ k, hu⟩ : Y →* Y) := ⟨_, hn, rfl⟩
    rw [hmap] at hmem
    exact hmem
  set y : M := ⟨m, hm⟩ with hy
  have hyfix : ∀ g : P, ((φ g y : M) : M ⧸ N) = (y : M ⧸ N) := by
    intro g
    obtain ⟨k, hk⟩ := hPpow g
    have hu : d ^ k ∈ Subgroup.normalizer (Y : Set G) := Subgroup.zpow_mem _ hdY k
    have h1 : Subgroup.inclusion hMY (φ g y) =
        Sec4.compAction Y ⟨d ^ k, hu⟩ (Subgroup.inclusion hMY y) := by
      apply Subtype.ext
      change ((g : Subgroup.normalizer (M : Set G)) : G) * (y : G) *
        ((g : Subgroup.normalizer (M : Set G)) : G)⁻¹ = d ^ k * (y : G) * (d ^ k)⁻¹
      rw [hk]
    have hxk : (⟨d ^ k, hu⟩ : Subgroup.normalizer (Y : Set G)) = ⟨d, hdY⟩ ^ k :=
      Subtype.ext (by simp)
    have h2 : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d ^ k, hu⟩)
        ((Subgroup.inclusion hMY y : Y) : Y ⧸ θ) = ((Subgroup.inclusion hMY y : Y) : Y ⧸ θ) := by
      rw [hxk, map_zpow, map_zpow]
      exact MulAction.mem_fixedBy_zpow (show ((Subgroup.inclusion hMY y : Y) : Y ⧸ θ) ∈
        MulAction.fixedBy _ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdY⟩)) from hfix) k
    rw [Sec4.thetaQuotMulAut_mk, ← h1] at h2
    have h3 := QuotientGroup.eq.mp h2
    refine QuotientGroup.eq.mpr ?_
    rw [hN, Subgroup.mem_comap, map_mul, map_inv]
    exact h3
  obtain ⟨y', hy'eq, hy'fix⟩ := KFacts.exists_fixed_of_coprime hPp φ N hNcard hφN y hyfix
  refine ⟨y', ?_, ?_⟩
  · have h1 := congrArg Subtype.val (hy'fix ⟨x, Subgroup.mem_zpowers x⟩)
    change d * (y' : G) * d⁻¹ = y' at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (y' : G) * d = d * (y' : G) * d⁻¹ * d := by rw [h1]
      _ = d * y' := by group
  · have h3 := QuotientGroup.eq.mp hy'eq
    rw [hN, Subgroup.mem_comap, map_mul, map_inv] at h3
    exact QuotientGroup.eq.mpr h3

theorem imageModTheta_mono' {Y X X' : Subgroup G} (h : X ≤ X') :
    imageModTheta Y X ≤ imageModTheta Y X' :=
  Subgroup.map_mono fun _ hz => Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hz))

theorem imageModTheta_inf_centralizer_eq {Y M : Subgroup G} (hMY : M ≤ Y) {d : G}
    (hdY : d ∈ Subgroup.normalizer (Y : Set G)) (hdM : d ∈ Subgroup.normalizer (M : Set G))
    (hd3 : d ^ 3 = 1) :
    imageModTheta Y (M ⊓ Subgroup.centralizer ({d} : Set G)) =
      imageModTheta Y M ⊓ barCentralizer (Subgroup.zpowers d) Y := by
  have hC := KFacts.imageModTheta_centralizer_eq hdY ⟨1, by simpa using hd3⟩
  ext yb
  constructor
  · intro h
    refine ⟨imageModTheta_mono' inf_le_left h, ?_⟩
    rw [← hC]
    exact imageModTheta_mono' (inf_le_inf_right _ hMY) h
  · rintro ⟨hM, hCy⟩
    obtain ⟨⟨m, hmY⟩, hm, rfl⟩ := hM
    have hm' : m ∈ M := Subgroup.mem_subgroupOf.mp hm
    have hCy' : (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨m, hmY⟩) ∈
        barCentralizer (Subgroup.zpowers d) Y := hCy
    rw [KFacts.mem_barCentralizer_zpowers_iff hdY] at hCy'
    obtain ⟨m', hm'c, hm'eq⟩ := exists_mem_centralizer_of_fixed hMY hdY hdM hd3 hm' hCy'
    refine ⟨⟨m', hMY m'.2⟩, Subgroup.mem_subgroupOf.mpr ⟨m'.2, hm'c⟩, ?_⟩
    exact hm'eq

theorem imageModTheta_inSubgroup_perfectResidual {Y S : Subgroup G} (hSY : S ≤ Y) :
    imageModTheta Y (inSubgroup perfectResidual S) =
      inSubgroup perfectResidual (imageModTheta Y S) := by
  set M' := S.subgroupOf Y with hM'
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hq
  set f : M' →* Y ⧸ aschbacherSolvableCore 3 Y := q.comp M'.subtype with hf
  have hrange : f.range = imageModTheta Y S := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have htrans := (CFSG.perfect_residual_transport f).1
  rw [imageModTheta, KFacts.subgroupOf_inSubgroup_perfectResidual hSY]
  change ((perfectResidual M').map M'.subtype).map q = _
  rw [Subgroup.map_map, ← hf, htrans]
  exact KFacts.inSubgroup_perfectResidual_congr hrange

theorem imageModTheta_residual_inf_centralizer_eq {Y M : Subgroup G} (hMY : M ≤ Y) {d : G}
    (hdY : d ∈ Subgroup.normalizer (Y : Set G)) (hdM : d ∈ Subgroup.normalizer (M : Set G))
    (hd3 : d ^ 3 = 1) :
    imageModTheta Y (inSubgroup perfectResidual (M ⊓ Subgroup.centralizer ({d} : Set G))) =
      inSubgroup perfectResidual (imageModTheta Y M ⊓ barCentralizer (Subgroup.zpowers d) Y) := by
  rw [imageModTheta_inSubgroup_perfectResidual (inf_le_left.trans hMY),
    imageModTheta_inf_centralizer_eq hMY hdY hdM hd3]

end Hering88F

end CFSG.RankThree.PartTwo.Sec8
