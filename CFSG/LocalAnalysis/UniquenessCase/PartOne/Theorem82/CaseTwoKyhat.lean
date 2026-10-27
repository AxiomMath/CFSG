module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoYhat
import CFSG.GroupTheory.Commutator.SubgroupOf
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPoints
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKyNormal
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKy

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

@[expose] noncomputable def Kyhat : Subgroup t.Xhat :=
  (t.Ky.subgroupOf t.Xz).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz))

@[expose] noncomputable def O2Kyhat : Subgroup t.Xhat :=
  ((t.Ky ⊓ t.d.N).subgroupOf t.Xz).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz))

theorem Kyhat_le_Yhat : t.Kyhat ≤ t.Yhat := by
  refine Subgroup.map_mono ?_
  refine Subgroup.subgroupOf_mono t.Xz ?_
  exact (t.Ky_le.trans inf_le_left).trans c.hyp81.1

private theorem mem_normalizer_Ky_of_mem_M_of_mem_Xz {m : G}
    (hmM : m ∈ c.S.M) (hmX : m ∈ t.Xz) :
    m ∈ Subgroup.normalizer (t.Ky : Set G) := by
  have hmC : m ∈ Subgroup.centralizer ({t.y} : Set G) := t.Xz_le_centralizer hmX
  have hmCzp : m ∈ Subgroup.centralizer (Subgroup.zpowers t.y : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact hmC
  have hmNzp : m ∈ Subgroup.normalizer (Subgroup.zpowers t.y : Set G) :=
    Subgroup.centralizer_le_normalizer _ hmCzp
  have hmNC : m ∈ Subgroup.normalizer
      ((Subgroup.centralizer ({t.y} : Set G) : Subgroup G) : Set G) := by
    have h := CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (Subgroup.zpowers t.y) hmNzp
    simpa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using h
  have hLnorm : c.S.M ≤ Subgroup.normalizer (c.L : Set G) := by
    rw [← t.hdM, ← t.hdL]
    exact CaseTwoTransitive.L_normal_in_M t
  have hmLC : m ∈ Subgroup.normalizer
      ((c.L ⊓ Subgroup.centralizer ({t.y} : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hLnorm hmM, hmNC⟩
  rw [CaseTwoTransitive.Ky]
  exact CFSG.Quasithin.normalizer_le_normalizer_perfectCore _ hmLC

theorem Yhat_le_normalizer_Kyhat : t.Yhat ≤ Subgroup.normalizer (t.Kyhat : Set t.Xhat) := by
  have hnorm : c.S.M ⊓ t.Xz ≤ Subgroup.normalizer (t.Ky : Set G) := by
    intro m hm
    exact mem_normalizer_Ky_of_mem_M_of_mem_Xz t (Subgroup.mem_inf.mp hm).1
      (Subgroup.mem_inf.mp hm).2
  have h := CFSG.GroupTheory.map_subgroupOf_le_normalizer
    (M := t.Xz) (B := c.S.M ⊓ t.Xz) (X := t.Ky)
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)) hnorm
  rw [Subgroup.inf_subgroupOf_right] at h
  simpa [Yhat, Kyhat] using h

theorem Yhat_le_normalizer_O2Kyhat :
    t.Yhat ≤ Subgroup.normalizer (t.O2Kyhat : Set t.Xhat) := by
  have hMN : c.S.M ≤ Subgroup.normalizer (t.d.N : Set G) := by
    rw [show t.d.N = CFSG.Open.pCoreOf 2 c.S.M by
      rw [show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl, t.hdM]]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M
  have hnorm : c.S.M ⊓ t.Xz ≤
      Subgroup.normalizer ((t.Ky ⊓ t.d.N : Subgroup G) : Set G) := by
    intro m hm
    obtain ⟨hmM, hmX⟩ := Subgroup.mem_inf.mp hm
    have hmKy := mem_normalizer_Ky_of_mem_M_of_mem_Xz t hmM hmX
    have hmN := hMN hmM
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hmKy, hmN⟩
  have h := CFSG.GroupTheory.map_subgroupOf_le_normalizer
    (M := t.Xz) (B := c.S.M ⊓ t.Xz) (X := t.Ky ⊓ t.d.N)
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)) hnorm
  rw [Subgroup.inf_subgroupOf_right] at h
  simpa [Yhat, O2Kyhat] using h

theorem Zhat_le_Kyhat : t.Zhat ≤ t.Kyhat := by
  refine Subgroup.map_mono ?_
  refine Subgroup.subgroupOf_mono t.Xz ?_
  exact t.Z_le_Dz.trans t.Dz_le_Ky

theorem commutator_Kyhat (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    ⁅t.Kyhat, t.Kyhat⁆ = t.Kyhat := by
  let π : ↥t.Xz →* t.Xhat := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)
  have hKyX : t.Ky ≤ t.Xz := t.Ky_le_Xz hK32 hGA hSp
  have hH : ⁅t.Ky.subgroupOf t.Xz, t.Ky.subgroupOf t.Xz⁆ = t.Ky.subgroupOf t.Xz := by
    apply Subgroup.map_injective t.Xz.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKyX, t.commutator_Ky]
  calc
    ⁅t.Kyhat, t.Kyhat⁆ = ⁅(t.Ky.subgroupOf t.Xz).map π,
        (t.Ky.subgroupOf t.Xz).map π⁆ := rfl
    _ = (⁅t.Ky.subgroupOf t.Xz, t.Ky.subgroupOf t.Xz⁆).map π :=
      (Subgroup.map_commutator _ _ π).symm
    _ = (t.Ky.subgroupOf t.Xz).map π := by rw [hH]
    _ = t.Kyhat := rfl

theorem le_O2Kyhat_or_eq (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) {N : Subgroup t.Xhat}
    (hNK : N ≤ t.Kyhat) (hN : t.Kyhat ≤ Subgroup.normalizer (N : Set t.Xhat)) :
    N ≤ t.O2Kyhat ∨ N = t.Kyhat := by
  classical
  let π : ↥t.Xz →* t.Xhat := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥t.Xz)
  have hKyX : t.Ky ≤ t.Xz := t.Ky_le_Xz hK32 hGA hSp
  let f : ↥t.Ky →* t.Xhat := π.comp (Subgroup.inclusion hKyX)
  have hf_range : f.range = t.Kyhat := by
    ext y
    constructor
    · rintro ⟨k, hk⟩
      rw [← hk]
      exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hKyX k,
        Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
    · intro hy
      obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.mp hy
      refine ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
      have hval : (Subgroup.inclusion hKyX ⟨x, Subgroup.mem_subgroupOf.mp hx⟩ :
          ↥t.Xz) = x := Subtype.ext rfl
      have hfval : f ⟨x, Subgroup.mem_subgroupOf.mp hx⟩ = π x := by
        change π (Subgroup.inclusion hKyX ⟨x, Subgroup.mem_subgroupOf.mp hx⟩) = π x
        rw [hval]
      rw [hfval]
      exact hxπ
  let N' : Subgroup ↥t.Ky := N.comap f
  let N'G : Subgroup G := N'.map t.Ky.subtype
  have hNmap : N'.map f = N := by
    have hle : N ≤ f.range := by rw [hf_range]; exact hNK
    simpa [N'] using Subgroup.map_comap_eq_self (f := f) (H := N) hle
  have hN'G_le : N'G ≤ t.Ky := Subgroup.map_subtype_le N'
  have hconj : ∀ {a x : G}, a ∈ t.Ky → x ∈ N'G → a * x * a⁻¹ ∈ N'G := by
    intro a x ha hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    let k : ↥t.Ky := ⟨a, ha⟩ * n * ⟨a, ha⟩⁻¹
    refine Subgroup.mem_map.mpr ⟨k, ?_, rfl⟩
    change f k ∈ N
    have hfa : f ⟨a, ha⟩ ∈ t.Kyhat := by
      rw [← hf_range]
      exact ⟨⟨a, ha⟩, rfl⟩
    have hfn : f n ∈ N := Subgroup.mem_comap.mp hn
    have hmem := (Subgroup.mem_normalizer_iff.mp (hN hfa) (f n)).1 hfn
    simpa [k, map_mul, map_inv] using hmem
  have hN'G_norm : t.Ky ≤ Subgroup.normalizer (N'G : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj hk hx
    · intro hx
      have h := hconj (a := k⁻¹) (t.Ky.inv_mem hk) hx
      simpa [mul_assoc] using h
  rcases t.le_N_or_eq_Ky hK32 hGA hSp hN'G_le hN'G_norm with hle | heq
  · left
    have hN'G_inf : N'G ≤ t.Ky ⊓ t.d.N := le_inf hN'G_le hle
    have hEq : N'.map (Subgroup.inclusion hKyX) = N'G.subgroupOf t.Xz := by
      ext x
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨n, hn, rfl⟩)
      · intro hx
        obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
        refine ⟨n, hn, ?_⟩
        ext
        exact hnx
    have hmap_le : N'.map f ≤ t.O2Kyhat := by
      have hmap_eq : N'.map f = (N'G.subgroupOf t.Xz).map π := by
        calc
          N'.map f = (N'.map (Subgroup.inclusion hKyX)).map π := by
            rw [show f = π.comp (Subgroup.inclusion hKyX) from rfl, ← Subgroup.map_map]
          _ = (N'G.subgroupOf t.Xz).map π := by rw [hEq]
      rw [hmap_eq]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono t.Xz hN'G_inf)
    rwa [← hNmap]
  · right
    have htop : N' = ⊤ := by
      apply Subgroup.map_injective t.Ky.subtype_injective
      rw [Subgroup.map_top, Subgroup.range_subtype]
      exact heq
    rw [← hNmap, htop, Subgroup.map_top]
    exact hf_range

theorem pCoreOf_Kyhat (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    CFSG.Open.pCoreOf 2 t.Kyhat = t.O2Kyhat := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN2 : IsPGroup 2 t.d.N := by
    rw [show t.d.N = CFSG.Open.pCoreOf 2 t.d.M from rfl, t.hdM]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.S.M
  have hS2 : IsPGroup 2 ((t.Ky ⊓ t.d.N).subgroupOf t.Xz) :=
    (hN2.comap_subtype).to_le (Subgroup.subgroupOf_mono t.Xz inf_le_right)
  have hO2leK : t.O2Kyhat ≤ t.Kyhat :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono t.Xz inf_le_left)
  have hO2leCore : t.O2Kyhat ≤ CFSG.Open.pCoreOf 2 t.Kyhat := by
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 hO2leK ?_ (hS2.map _)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hO2leK).mpr
      (t.Kyhat_le_Yhat.trans t.Yhat_le_normalizer_O2Kyhat)
  refine le_antisymm ?_ hO2leCore
  have hcore_norm : t.Kyhat ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 t.Kyhat : Set t.Xhat) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 t.Kyhat
  rcases t.le_O2Kyhat_or_eq hK32 hGA hSp
      (CFSG.LieType.BorelTits.pCoreOf_le 2 t.Kyhat) hcore_norm with hle | heq
  · exact hle
  · exfalso
    have hZle : t.Zhat ≤ CFSG.Open.pCoreOf 2 t.Kyhat := by
      rw [heq]
      exact t.Zhat_le_Kyhat
    have hZp : IsPGroup 2 t.Zhat :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 t.Kyhat).to_le hZle
    obtain ⟨n, hn⟩ := hZp.exists_card_eq
    rw [t.card_Zhat] at hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      norm_num at hn
    have h23 : 2 ∣ 3 := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    norm_num at h23

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
