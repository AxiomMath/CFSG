module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShape
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332T3
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeA
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoKyNormal
import CFSG.LocalAnalysis.SectionRank.AmbientRank
import CFSG.RankThree.PartOne.S11d.OutCentral

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem Z_le_Dz : t.Z ≤ t.Dz :=
  le_inf (t.Z_le_AA.trans t.d.AA_le_S) t.Z_le_centralizer

theorem Z_le_Ky : t.Z ≤ t.Ky := t.Z_le_Dz.trans t.Dz_le_Ky

private theorem exists_mem_Dz_mul_zpowers_of_mem_inf_centralizer_y {x : G}
    (hx : x ∈ t.P ⊓ Subgroup.centralizer ({t.y} : Set G)) :
    ∃ s ∈ t.Dz, ∃ k : ℤ, s * t.y ^ k = x := by
  obtain ⟨s, hsS, k, hsk⟩ := t.exists_mem_S_mul_zpowers_of_mem_inf_centralizer_y hx
  have hxK : Commute x t.y :=
    show Commute x t.y from Subgroup.mem_centralizer_singleton_iff.mp hx.2
  have hwk : Commute (t.y ^ k) t.y := (Commute.refl t.y).zpow_left k
  have hseq : s = x * (t.y ^ k)⁻¹ := by rw [← hsk]; group
  refine ⟨s, Subgroup.mem_inf.mpr ⟨hsS, ?_⟩, k, hsk⟩
  rw [Subgroup.mem_centralizer_singleton_iff, hseq]
  exact (hxK.mul_left hwk.inv_left).eq

theorem Ky_le_Xz (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) : t.Ky ≤ t.Xz := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKnormX : Subgroup.centralizer ({t.y} : Set G) ≤
      Subgroup.normalizer (t.Xz : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer t.Xz_le_centralizer).mp t.normal_Xz
  have hKyNormX : t.Ky ≤ Subgroup.normalizer (t.Xz : Set G) :=
    (t.Ky_le.trans inf_le_right).trans hKnormX
  have hN : t.Ky ≤ Subgroup.normalizer ((t.Ky ⊓ t.Xz : Subgroup G) : Set G) := by
    intro k hk
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := t.Ky) (K := t.Xz)
      ⟨Subgroup.le_normalizer hk, hKyNormX hk⟩
  rcases t.le_N_or_eq_Ky hK32 hGA hSp inf_le_left hN with hle | heq
  · exfalso
    have hZle : t.Z ≤ t.Ky ⊓ t.Xz := le_inf t.Z_le_Ky t.Z_le_Xz
    have hZ2 : IsPGroup 2 ↥t.Z := t.d.N_isPGroup.to_le (hZle.trans hle)
    obtain ⟨n, hn⟩ := hZ2.exists_card_eq
    rw [t.card_Z] at hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      norm_num at hn
    have h23 : 2 ∣ 3 := by
      rw [hn]
      exact dvd_pow_self 2 hn0
    norm_num at h23
  · exact (le_of_eq heq.symm).trans inf_le_right

theorem Ky_inf_Oz_le (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    t.Ky ⊓ t.Oz ≤ t.d.N := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hOnormal : (CFSG.pPrimeCore 3 ↥t.Xz).Normal := CFSG.pPrimeCore_normal
  have hKyX : t.Ky ≤ t.Xz := t.Ky_le_Xz hK32 hGA hSp
  have hKyNormOz : t.Ky ≤ Subgroup.normalizer (t.Oz : Set G) :=
    hKyX.trans
      (CFSG.ABGLocalTools.le_normalizer_map_subtype t.Xz (CFSG.pPrimeCore 3 ↥t.Xz))
  have hN : t.Ky ≤ Subgroup.normalizer ((t.Ky ⊓ t.Oz : Subgroup G) : Set G) := by
    intro k hk
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := t.Ky) (K := t.Oz)
      ⟨Subgroup.le_normalizer hk, hKyNormOz hk⟩
  rcases t.le_N_or_eq_Ky hK32 hGA hSp inf_le_left hN with hle | heq
  · exact hle
  · exfalso
    have hKyOz : t.Ky ≤ t.Oz := (le_of_eq heq.symm).trans inf_le_right
    have hZle : t.Z ≤ t.Oz := t.Z_le_Ky.trans hKyOz
    have h3dvd : 3 ∣ Nat.card t.Oz := by
      have h := Subgroup.card_dvd_of_le hZle
      rwa [t.card_Z] at h
    have hcardOz : Nat.card t.Oz = Nat.card (CFSG.pPrimeCore 3 ↥t.Xz) :=
      Subgroup.card_map_of_injective t.Xz.subtype_injective
    have hcop : Nat.Coprime 3 (Nat.card t.Oz) := by
      rw [hcardOz]
      exact CFSG.pPrimeCore_coprime_card
    have h1 : 3 = 1 := Nat.Coprime.eq_one_of_dvd hcop h3dvd
    norm_num at h1

private theorem conj_mem_Z_of_mem_normalizer_Dz {g x : G}
    (hgC : g ∈ Subgroup.centralizer ({t.y} : Set G))
    (hgN : g ∈ Subgroup.normalizer (t.Dz : Set G)) (hx : x ∈ t.Z) :
    g * x * g⁻¹ ∈ t.Z := by
  have hxD : x ∈ t.Dz := t.Z_le_Dz hx
  have hx3 : x ^ 3 = 1 := t.d.isElemAbelian_AA.2 x (t.Z_le_AA hx)
  have hconjD : g * x * g⁻¹ ∈ t.Dz := (Subgroup.mem_normalizer_iff.mp hgN x).mp hxD
  have hconj3 : (g * x * g⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hx3]
    group
  have hconjC : g * x * g⁻¹ ∈ Subgroup.centralizer ({t.y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hgy : Commute g t.y :=
      show Commute g t.y from Subgroup.mem_centralizer_singleton_iff.mp hgC
    have hxy : x * t.y = t.y * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (t.Z_le_centralizer hx)
    have hginv : g⁻¹ * t.y = t.y * g⁻¹ := hgy.inv_left.eq
    calc g * x * g⁻¹ * t.y = g * x * (g⁻¹ * t.y) := by group
      _ = g * x * (t.y * g⁻¹) := by rw [hginv]
      _ = g * (x * t.y) * g⁻¹ := by group
      _ = g * (t.y * x) * g⁻¹ := by rw [hxy]
      _ = t.y * (g * x * g⁻¹) := by
        calc g * (t.y * x) * g⁻¹ = (g * t.y) * x * g⁻¹ := by group
          _ = (t.y * g) * x * g⁻¹ := by rw [hgy.eq]
          _ = t.y * (g * x * g⁻¹) := by group
  exact Subgroup.mem_inf.mpr ⟨t.d.mem_AA_of_pow_eq_one hconjD.1 hconj3, hconjC⟩

section

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem inf_normalizer_Dz_le {p : ℕ}
    (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) :
    Subgroup.centralizer ({t.y} : Set G) ⊓ Subgroup.normalizer (t.Dz : Set G) ≤ c.S.M := by
  intro g hg
  obtain ⟨hgC, hgN⟩ := Subgroup.mem_inf.mp hg
  apply t.normalizer_Z_le hp hN hZ
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact t.conj_mem_Z_of_mem_normalizer_Dz hgC hgN
  · intro hx
    have hgC' : g⁻¹ ∈ Subgroup.centralizer ({t.y} : Set G) := Subgroup.inv_mem _ hgC
    have hgN' : g⁻¹ ∈ Subgroup.normalizer (t.Dz : Set G) := Subgroup.inv_mem _ hgN
    have h := t.conj_mem_Z_of_mem_normalizer_Dz (g := g⁻¹) hgC' hgN' hx
    have hxeq : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
    rwa [hxeq] at h

theorem isSylowOf_Dz_Xz (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) :
    CFSG.ABGLocalTools.IsSylowOf 3 t.Dz t.Xz := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let K : Subgroup G := Subgroup.centralizer ({t.y} : Set G)
  let T : Subgroup G := t.P ⊓ K
  have hKnormX : K ≤ Subgroup.normalizer (t.Xz : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer t.Xz_le_centralizer).mp t.normal_Xz
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T K :=
    t.isSylowOf_inf_centralizer_y_centralizer hOut hp hN hZ
  have hTXsyl : CFSG.ABGLocalTools.IsSylowOf 3 (T ⊓ t.Xz) t.Xz :=
    hTsyl.inf_of_le_normalizer t.Xz_le_centralizer hKnormX
  have hSP : t.d.S ≤ t.P := by
    rw [← t.hPy]
    exact le_sup_left
  have hDle : t.Dz ≤ T ⊓ t.Xz := by
    refine le_inf ?_ ?_
    · exact le_inf (inf_le_left.trans hSP) inf_le_right
    · exact t.Dz_le_Ky.trans (t.Ky_le_Xz hK32 hGA hSp)
  have hXrank : CFSG.pRank 3 ↥t.Xz ≤ 1 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact (t.pRank_Xz hK332 hOut hp hN hZ).le
  have hCpg : IsPGroup 3 ↥(T ⊓ t.Xz) := hTsyl.isPGroup.to_le inf_le_left
  have hCcyc : IsCyclic ↥(T ⊓ t.Xz) :=
    CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one Nat.prime_three (by norm_num)
      inf_le_right hCpg hXrank
  have h3dvdD : 3 ∣ Nat.card t.Dz := by
    have h := Subgroup.card_dvd_of_le t.Z_le_Dz
    rwa [t.card_Z] at h
  have hCexp : ∀ x ∈ T ⊓ t.Xz, x ^ Nat.card t.Dz = 1 := by
    intro x hx
    obtain ⟨s, hsD, k, hsk⟩ := t.exists_mem_Dz_mul_zpowers_of_mem_inf_centralizer_y hx.1
    have hcomm : Commute s (t.y ^ k) :=
      (show Commute s t.y from
        Subgroup.mem_centralizer_singleton_iff.mp hsD.2).zpow_right k
    have hs : s ^ Nat.card t.Dz = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard t.Dz hsD)
    have hy : (t.y ^ k) ^ Nat.card t.Dz = 1 := by
      obtain ⟨m, hm⟩ := h3dvdD
      rw [hm, pow_mul, t.zpow_y_pow_three k, one_pow]
    rw [← hsk, hcomm.mul_pow, hs, hy, mul_one]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(T ⊓ t.Xz))
  have htop : Subgroup.zpowers g = ⊤ := top_le_iff.mp (fun x _ => hg x)
  have hcardC : Nat.card ↥(T ⊓ t.Xz) = orderOf g := by
    rw [← Nat.card_zpowers (a := g), htop, Subgroup.card_top]
  have hgdvd : orderOf g ∣ Nat.card t.Dz := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact Subtype.ext (hCexp (g : G) g.2)
  have hCle : Nat.card ↥(T ⊓ t.Xz) ≤ Nat.card t.Dz := by
    rw [hcardC]
    exact Nat.le_of_dvd Nat.card_pos hgdvd
  have hEq : t.Dz = T ⊓ t.Xz :=
    Subgroup.eq_of_le_of_card_ge hDle hCle
  rw [← hEq] at hTXsyl
  exact hTXsyl

theorem centralizer_y_le_iff (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner) {p : ℕ}
    (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) :
    Subgroup.centralizer ({t.y} : Set G) ≤ c.S.M ↔ t.Xz ≤ c.S.M := by
  constructor
  · intro hH
    exact t.Xz_le_centralizer.trans hH
  · intro hX
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let K : Subgroup G := Subgroup.centralizer ({t.y} : Set G)
    have hD : CFSG.ABGLocalTools.IsSylowOf 3 t.Dz t.Xz :=
      t.isSylowOf_Dz_Xz hK32 hGA hSp hK332 hOut hp hN hZ
    have hKnormX : K ≤ Subgroup.normalizer (t.Xz : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer t.Xz_le_centralizer).mp t.normal_Xz
    intro h hh
    have hhXnorm : h ∈ Subgroup.normalizer (t.Xz : Set G) := hKnormX hh
    have hXmap : t.Xz.map (MulAut.conj h).toMonoidHom = t.Xz :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hhXnorm
    have hD'card : Nat.card (t.Dz.map (MulAut.conj h).toMonoidHom) =
        3 ^ (Nat.card t.Xz).factorization 3 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hD.card_eq]
    have hD'le : t.Dz.map (MulAut.conj h).toMonoidHom ≤ t.Xz := by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← hXmap]
      exact Subgroup.mem_map_of_mem _ (hD.le hd)
    have hD' : CFSG.ABGLocalTools.IsSylowOf 3
        (t.Dz.map (MulAut.conj h).toMonoidHom) t.Xz :=
      CFSG.ABGLocalTools.isSylowOf_of_card hD'le hD'card
    obtain ⟨k, hkX, hconj⟩ := hD.exists_mem_conj hD'
    have hmaple : t.Dz.map (MulAut.conj (k⁻¹ * h)).toMonoidHom ≤ t.Dz := by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
      have hd' : h * d * h⁻¹ ∈ t.Dz.map (MulAut.conj h).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hd
      have hmem := (hconj (h * d * h⁻¹)).mp hd'
      have heq : (MulEquiv.toMonoidHom (MulAut.conj (k⁻¹ * h))) d =
          k⁻¹ * (h * d * h⁻¹) * k := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [heq]
      exact hmem
    have hmapeq : t.Dz.map (MulAut.conj (k⁻¹ * h)).toMonoidHom = t.Dz :=
      Subgroup.eq_of_le_of_card_ge hmaple
        (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj (k⁻¹ * h)).injective).symm)
    have hkNh : k⁻¹ * h ∈ Subgroup.normalizer (t.Dz : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmapeq
    have hkNhK : k⁻¹ * h ∈ K := K.mul_mem (K.inv_mem (t.Xz_le_centralizer hkX)) hh
    have hkNhM : k⁻¹ * h ∈ c.S.M :=
      t.inf_normalizer_Dz_le hp hN hZ (Subgroup.mem_inf.mpr ⟨hkNhK, hkNh⟩)
    have hkM : k ∈ c.S.M := hX hkX
    have heq : h = k * (k⁻¹ * h) := by group
    rw [heq]
    exact c.S.M.mul_mem hkM hkNhM

end

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
