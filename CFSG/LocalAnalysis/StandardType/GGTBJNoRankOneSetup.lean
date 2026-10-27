module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneDefs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneCard
import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneBook
import CFSG.LocalAnalysis.StandardType.GGTableBTransport
import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneRank
import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l48nS_normalizerMonoidHom_mem_subgroupOf {G : Type*} [Group G]
    {J L : Subgroup G} (hJL : J ≤ L) (g : Subgroup.normalizer (L : Set G))
    (hgJ : (g : G) ∈ Subgroup.normalizer (J : Set G)) {j : ↥L} (hj : (j : G) ∈ J) :
    L.normalizerMonoidHom g j ∈ J.subgroupOf L := by
  rw [Subgroup.mem_subgroupOf, Subgroup.normalizerMonoidHom_apply_apply_coe]
  exact (Subgroup.mem_normalizer_iff.mp hgJ (j : G)).mp hj

theorem ggRankOne_setup {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {n : ℕ} (hn : 2 ≤ n)
    (hJ : GGHasLabel (⟨.A, 1, n⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) :
    ∃ (e a : MulAut ↥L) (J' : Subgroup ↥L) (A : Subgroup (MulAut ↥L)),
      e ≠ 1 ∧ e ^ p = 1 ∧ IsComponentOf J' (ggFixSub e) ∧
      GGHasLabel (⟨.A, 1, n⟩ : LargeEvenLabel) (↥J' ⧸ Subgroup.center ↥J') ∧
      a * e = e * a ∧ (∀ j ∈ J', a j ∈ J') ∧
      (¬ ∃ y : ↥J' ⧸ Subgroup.center ↥J', ∀ j j' : ↥J', a (j : ↥L) = (j' : ↥L) →
        (j' : ↥J' ⧸ Subgroup.center ↥J') = y * (j : ↥J' ⧸ Subgroup.center ↥J') * y⁻¹) ∧
      IsElemAbelian p A ∧ Nat.card A * p = Nat.card B ∧ e ∈ A ∧ a ∈ A ∧
      (∀ c ∈ A, ∃ b ∈ B, ∀ l : ↥L, ((c l : ↥L) : G) = b * l * b⁻¹) ∧
      (∀ c ∈ A, ∀ j ∈ J', c j ∈ J') := by
  classical
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType p B x L := hcfg.1.2.2.2.2.2.2.2
  have hpre : LargeEvenStdSubPre p B x L D J := hcfg.2.2.1
  have hB : IsElemAbelian p B := hS.1.1
  have hBL : B ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_largeEvenStandardType hst
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := le_normalizer_of_stdSub hS hst hpre
  have hDB : D ≤ B := hpre.1
  have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hpre.2.2.2.2.2.1
  have hJL : J ≤ L := hcomp.1.trans inf_le_left
  obtain ⟨hxL, hx1, hxp, -⟩ := GGConfig.data_L hcfg
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  obtain ⟨hp, -, -, -, b, hbB, hbnotinner⟩ := ggRankOne_card hcfg hn hJ
  haveI : Fact p.Prime := ⟨hp⟩
  let φ₀ : ↥B →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hBL)
  let A : Subgroup (MulAut ↥L) := φ₀.range
  have hmemker : ∀ c : ↥B, c ∈ φ₀.ker ↔ (c : G) ∈ Subgroup.centralizer (L : Set G) := by
    intro c
    rw [MonoidHom.mem_ker]
    show L.normalizerMonoidHom (Subgroup.inclusion hBL c) = 1 ↔ _
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    rfl
  have hker_eq : φ₀.ker.map B.subtype = B ⊓ Subgroup.centralizer (L : Set G) := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.2, (hmemker c).mp hc⟩
    · rintro ⟨hgB, hgC⟩
      exact ⟨⟨g, hgB⟩, (hmemker ⟨g, hgB⟩).mpr hgC, rfl⟩
  have hkercard : Nat.card φ₀.ker = p := by
    have h : Nat.card (φ₀.ker.map B.subtype) =
        Nat.card ((B ⊓ Subgroup.centralizer (L : Set G)) : Subgroup G) :=
      congrArg (fun s : Subgroup G => Nat.card s) hker_eq
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective B),
      inf_centralizer_eq_zpowers_of_sstar hp hS, Nat.card_zpowers,
      orderOf_eq_prime hxp hx1] at h
    exact h
  have hcardA : Nat.card A * p = Nat.card B := by
    show Nat.card φ₀.range * p = Nat.card B
    rw [mul_comm, ← hkercard]
    exact Subgroup.card_ker_mul_card_range φ₀
  obtain ⟨d₀, hdD, hdx⟩ := exists_mem_not_mem_zpowers hp hDcard hxp hx1
  have hDsup : D = Subgroup.zpowers x ⊔ Subgroup.zpowers d₀ :=
    eq_sup_zpowers_of_card hp (TableB.isElemAbelian_mono hB hDB) hDcard hxD hx1 hdD hdx
  let d : ↥B := ⟨d₀, hDB hdD⟩
  let e : MulAut ↥L := φ₀ d
  let bB : ↥B := ⟨b, hbB⟩
  let a : MulAut ↥L := φ₀ bB
  let J' : Subgroup ↥L := J.subgroupOf L
  have he_eq : e = L.normalizerMonoidHom (Subgroup.inclusion hBL d) := rfl
  have ha_eq : a = L.normalizerMonoidHom (Subgroup.inclusion hBL bB) := rfl
  have he1 : e ≠ 1 := by
    intro h1
    have hdker : d ∈ φ₀.ker := MonoidHom.mem_ker.mpr h1
    have hdC : (d : G) ∈ Subgroup.centralizer (L : Set G) := (hmemker d).mp hdker
    have hmem : (d : G) ∈ B ⊓ Subgroup.centralizer (L : Set G) := ⟨d.2, hdC⟩
    rw [inf_centralizer_eq_zpowers_of_sstar hp hS] at hmem
    exact hdx hmem
  have hep : e ^ p = 1 := by
    have hdp : (d : ↥B) ^ p = 1 := Subtype.ext (by simpa using hB.2 (d : G) d.2)
    show φ₀ d ^ p = 1
    rw [← map_pow, hdp, map_one]
  have hae : a * e = e * a := by
    haveI : IsMulCommutative ↥B := hB.1
    show φ₀ bB * φ₀ d = φ₀ d * φ₀ bB
    rw [← map_mul, ← map_mul]
    exact congrArg φ₀ (mul_comm' bB d)
  have hacoe : ∀ l : ↥L, ((a l : ↥L) : G) = b * (l : G) * b⁻¹ := by
    intro l
    rw [ha_eq]
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hcent_eq : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({(d : G)} : Set G) := by
    apply le_antisymm
    · intro l hl
      refine ⟨hl.1, ?_⟩
      change ∀ h ∈ ({(d : G)} : Set G), h * l = l * h
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (Subgroup.mem_centralizer_iff.mp hl.2) (d : G) hdD
    · intro l hl
      obtain ⟨hlL, hld⟩ := hl
      refine ⟨hlL, ?_⟩
      change ∀ h ∈ (D : Set G), h * l = l * h
      intro z hz
      have hcx : Commute (l : G) x := by
        have h := hLx hlL
        change ∀ k ∈ ({(x)} : Set G), k * l = l * k at h
        exact (h x (Set.mem_singleton x)).symm
      have hcd : Commute (l : G) (d : G) := by
        have h := hld
        change ∀ k ∈ ({(d : G)} : Set G), k * l = l * k at h
        exact (h (d : G) (Set.mem_singleton (d : G))).symm
      have hDcl : D ≤ Subgroup.centralizer ({(l : G)} : Set G) := by
        rw [hDsup]
        exact sup_le
          (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hcx.eq.symm))
          (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hcd.eq.symm))
      exact Subgroup.mem_centralizer_singleton_iff.mp (hDcl hz)
  have hcomp' : IsComponentOf J (L ⊓ Subgroup.centralizer ({(d : G)} : Set G)) := by
    rwa [← hcent_eq]
  have hcompL : IsComponentOf J' (ggFixSub e) := by
    rw [he_eq]
    exact ggIsComponentOf_ggFixSub_normalizerMonoidHom (g := (d : G)) (hBL d.2) hcomp'
  have hlabel : GGHasLabel (⟨.A, 1, n⟩ : LargeEvenLabel)
      (↥J' ⧸ Subgroup.center ↥J') :=
    ggHasLabel_of_mulEquiv
      (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJL)
        (Subgroup.map_center_eq _)).symm hJ
  have hAnormJ' : ∀ c ∈ A, ∀ j ∈ J', c j ∈ J' := by
    intro c hc j hj
    obtain ⟨c', rfl⟩ := MonoidHom.mem_range.mp hc
    exact l48nS_normalizerMonoidHom_mem_subgroupOf hJL (Subgroup.inclusion hBL c')
      (hBJ c'.2) (Subgroup.mem_subgroupOf.mp hj)
  have hE : IsElemAbelian p A := isElemAbelian_range_of_isElemAbelian hB φ₀
  have heA : e ∈ A := ⟨d, rfl⟩
  have haA : a ∈ A := ⟨bB, rfl⟩
  have hconj : ∀ c ∈ A, ∃ b₀ ∈ B, ∀ l : ↥L, ((c l : ↥L) : G) = b₀ * l * b₀⁻¹ := by
    intro c hc
    obtain ⟨c', rfl⟩ := MonoidHom.mem_range.mp hc
    refine ⟨(c' : G), c'.2, fun l => ?_⟩
    show ((L.normalizerMonoidHom (Subgroup.inclusion hBL c') l : ↥L) : G) =
      (c' : G) * (l : G) * (c' : G)⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have hnotinner' : ¬ ∃ y : ↥J' ⧸ Subgroup.center ↥J',
      ∀ j j' : ↥J', a (j : ↥L) = (j' : ↥L) →
        (j' : ↥J' ⧸ Subgroup.center ↥J') =
          y * (j : ↥J' ⧸ Subgroup.center ↥J') * y⁻¹ := by
    rintro ⟨y, hy⟩
    apply hbnotinner
    let σ : ↥J' ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJL
    let Ψ : ↥J' ⧸ Subgroup.center ↥J' ≃* ↥J ⧸ Subgroup.center ↥J :=
      QuotientGroup.congr (Subgroup.center ↥J') (Subgroup.center ↥J) σ
        (Subgroup.map_center_eq σ)
    refine ⟨Ψ y, ?_⟩
    intro j j' hrel
    let jL : ↥J' := ⟨⟨(j : G), hJL j.2⟩, j.2⟩
    let jL' : ↥J' := ⟨⟨(j' : G), hJL j'.2⟩, j'.2⟩
    have hσjL : σ jL = j := Subtype.ext rfl
    have hσjL' : σ jL' = j' := Subtype.ext rfl
    have haeq : a (jL : ↥L) = (jL' : ↥L) := by
      apply Subtype.ext
      rw [hacoe (jL : ↥L)]
      show b * (j : G) * b⁻¹ = (j' : G)
      exact hrel
    have hΨ := congrArg Ψ (hy jL jL' haeq)
    have hΨmk : ∀ x : ↥J', Ψ (QuotientGroup.mk x) = QuotientGroup.mk (σ x) :=
      fun x => QuotientGroup.congr_mk (Subgroup.center ↥J') (Subgroup.center ↥J) σ
        (Subgroup.map_center_eq σ) x
    rw [map_mul, map_mul, map_inv, hΨmk jL', hΨmk jL, hσjL', hσjL] at hΨ
    exact hΨ
  exact ⟨e, a, J', A, he1, hep, hcompL, hlabel, hae, hAnormJ' a haA, hnotinner',
    hE, hcardA, heA, haA, hconj, hAnormJ'⟩

end CFSG.StandardType

end
