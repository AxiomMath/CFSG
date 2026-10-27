module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Regimes
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.S2MathAs51642Interfaces

private theorem l02qj12_not_isCyclic {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {D : Subgroup G} (hDel : CFSG.Open.IsElemAbelian p D) (hDcard : Nat.card D = p ^ 2) :
    ¬ IsCyclic ↥D := by
  rintro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := D) (h := hcyc)
  have hgp : g ^ p = 1 := by
    apply Subtype.ext
    simpa using hDel.2 (g : G) g.2
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp
  have hcard : orderOf g = p ^ 2 := by rw [hg, hDcard]
  have hpp : p ^ 2 ∣ p := hcard ▸ hdvd
  have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hpp
  nlinarith [hp.two_le]

theorem l02qj12_closure_pair_eq_of_card {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {x d : G} {D : Subgroup G} (hxD : x ∈ D) (hx1 : x ≠ 1)
    (hDel : CFSG.Open.IsElemAbelian p D) (hDcard : Nat.card D = p ^ 2) (hdD : d ∈ D)
    (hdx : d ∉ Subgroup.zpowers x) : Subgroup.closure {x, d} = D := by
  have hxp : x ^ p = 1 := hDel.2 x hxD
  have hz : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (p := p) (hp := Fact.mk hp) hxp hx1
  set H : Subgroup G := Subgroup.closure {x, d} with hH
  have hHD : H ≤ D := (Subgroup.closure_le _).mpr (by
    intro g hg
    rcases hg with rfl | rfl
    · exact hxD
    · exact hdD)
  have hzH : Subgroup.zpowers x ≤ H :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hdH : d ∈ H := Subgroup.subset_closure (by simp)
  apply Subgroup.eq_of_le_of_card_ge hHD
  have hdvd : Nat.card H ∣ p ^ 2 := by
    rw [← hDcard]; exact Subgroup.card_dvd_of_le hHD
  obtain ⟨k, hk, hkH⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hpH : p ∣ Nat.card H := by rw [← hz]; exact Subgroup.card_dvd_of_le hzH
  interval_cases k
  · rw [pow_zero] at hkH
    rw [hkH] at hpH
    exact absurd (Nat.le_of_dvd one_pos hpH) (by have := hp.two_le; omega)
  · exfalso
    rw [pow_one] at hkH
    have : Subgroup.zpowers x = H :=
      Subgroup.eq_of_le_of_card_ge hzH (by rw [hz, hkH])
    exact hdx (this ▸ hdH)
  · rw [hkH, hDcard]

theorem l02qj12_inf_centralizer_eq {G : Type} [Group G] {x d : G} {L D : Subgroup G}
    (hDgen : Subgroup.closure {x, d} = D) (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) :
    L ⊓ Subgroup.centralizer (D : Set G) = L ⊓ Subgroup.centralizer ({d} : Set G) := by
  have hdD : d ∈ D := hDgen ▸ Subgroup.subset_closure (by simp)
  apply le_antisymm
  · exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdD))
  · rintro g ⟨hgL, hgy⟩
    refine ⟨hgL, ?_⟩
    show g ∈ Subgroup.centralizer (D : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ Subgroup.closure {x, d} := by rw [hDgen]; exact hh
    refine Subgroup.closure_induction (p := fun h _ => h * g = g * h) ?_ ?_ ?_ ?_ hh'
    · intro a ha
      rcases ha with rfl | rfl
      · exact (Subgroup.mem_centralizer_iff.mp (hLx hgL)) a rfl
      · exact (Subgroup.mem_centralizer_iff.mp hgy) a rfl
    · simp
    · intro a b _ _ ha hb
      rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
    · intro a _ ha
      calc a⁻¹ * g = a⁻¹ * (g * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * g) * a⁻¹ := by rw [← ha]
        _ = g * a⁻¹ := by group

theorem q1_fixed_component_layer_data {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (y : ↥Bs) (u : MulAut ↥L), (y : G) ∈ D ∧ ggGamma L hN y = u ∧ orderOf u = p ∧
      (∀ b : ↥Bs, Commute (ggGamma L hN b) u) ∧ J ≤ L ∧
      CFSG.Open.IsComponentOf (J.subgroupOf L) (ggAutFixedSubgroup u) ∧
        J.subgroupOf L = LargeEvenLayer (ggAutFixedSubgroup u) := by
  have hβ : p ∈ LargeEvenBeta 4 G := hcfg.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hBst : GGBstar p B Bs := hcfg.2.1
  have hBBs : B ≤ Bs := hBst.1
  have hEabBs : CFSG.Open.IsElemAbelian p Bs := hBst.2.1
  have hstd : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hDB : D ≤ B := hstd.1.1
  have hEabD : CFSG.Open.IsElemAbelian p D := hstd.1.2.1
  have hDcard : Nat.card D = p ^ 2 := hstd.1.2.2.1
  have hxD : x ∈ D := hstd.1.2.2.2.1
  have hJcomp : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hstd.1.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hDBs : D ≤ Bs := hDB.trans hBBs
  have hx_cent : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hDnotle : ¬ D ≤ Subgroup.centralizer (L : Set G) := by
    intro hDle
    have hDpg : IsPGroup p D := IsPGroup.of_card_dvd_pow (n := 2) (by rw [hDcard])
    have hDcyc : IsCyclic ↥D := hS.2.2.2.2 D hDle hDpg
    exact l02qj12_not_isCyclic hp hEabD hDcard hDcyc
  obtain ⟨d, hdD, hdnotC⟩ : ∃ d ∈ D, d ∉ Subgroup.centralizer (L : Set G) := by
    by_contra h
    apply hDnotle
    intro d hd
    by_contra hdc
    exact h ⟨d, hd, hdc⟩
  have hdx : d ∉ Subgroup.zpowers x := by
    intro hd
    exact hdnotC ((Subgroup.zpowers_le.mpr hx_cent) hd)
  have hDgen : Subgroup.closure {x, d} = D :=
    l02qj12_closure_pair_eq_of_card hp hxD hx1 hEabD hDcard hdD hdx
  have hcent : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({d} : Set G) :=
    l02qj12_inf_centralizer_eq hDgen hLx
  let y : ↥Bs := ⟨d, hDBs hdD⟩
  let u : MulAut ↥L := ggGamma L hN y
  refine ⟨y, u, hdD, rfl, ?_, ?_, ?_, ?_⟩
  · have hy_pow : y ^ p = 1 := by
      apply Subtype.ext
      simpa using hEabD.2 d hdD
    have hu_pow : u ^ p = 1 := by
      show (ggGamma L hN y) ^ p = 1
      rw [← map_pow, hy_pow, map_one]
    have hu_ne : u ≠ 1 := by
      intro h
      exact hdnotC ((ggGamma_eq_one_iff L hN y).mp h)
    exact orderOf_eq_prime (p := p) (hp := Fact.mk hp) hu_pow hu_ne
  · intro b
    have hbcomm : Commute b y := by
      rw [Commute]
      apply Subtype.ext
      simpa using TableB.IsElemAbelian.comm hEabBs b.2 y.2
    exact hbcomm.map (ggGamma L hN)
  · exact hJcomp.1.trans inf_le_left
  · have hJsub : CFSG.Assembly.IsComponentOf (J.subgroupOf L)
        ((L ⊓ Subgroup.centralizer (D : Set G)).subgroupOf L) := by
      have hmap : ((L ⊓ Subgroup.centralizer (D : Set G)).subgroupOf L).map L.subtype =
          L ⊓ Subgroup.centralizer (D : Set G) :=
        Subgroup.map_subgroupOf_eq_of_le inf_le_left
      have hJcomp_map : CFSG.Assembly.IsComponentOf J
          (((L ⊓ Subgroup.centralizer (D : Set G)).subgroupOf L).map L.subtype) := by
        rw [hmap]; exact hJcomp
      exact (isComponentOf_comap_of_injective L.subtype L.subtype_injective hJcomp_map).1
    have hfix : (L ⊓ Subgroup.centralizer (D : Set G)).subgroupOf L = ggAutFixedSubgroup u := by
      ext l
      rw [Subgroup.mem_subgroupOf]
      have hcent_l : (l : G) ∈ Subgroup.centralizer (D : Set G) ↔
          (l : G) ∈ Subgroup.centralizer ({d} : Set G) := by
        constructor
        · intro h
          have h' : (l : G) ∈ L ⊓ Subgroup.centralizer (D : Set G) := ⟨l.2, h⟩
          rw [hcent] at h'
          exact h'.2
        · intro h
          have h' : (l : G) ∈ L ⊓ Subgroup.centralizer ({d} : Set G) := ⟨l.2, h⟩
          rw [← hcent] at h'
          exact h'.2
      have hfix_l : l ∈ ggAutFixedSubgroup u ↔
          (l : G) ∈ Subgroup.centralizer ({d} : Set G) := by
        change (ggGamma L hN y) l = l ↔ (l : G) ∈ Subgroup.centralizer ({d} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff, ggGamma_coe,
          mul_inv_eq_iff_eq_mul]
        exact eq_comm
      rw [Subgroup.mem_inf, hfix_l]
      constructor
      · rintro ⟨-, hD⟩; exact hcent_l.mp hD
      · intro hy; exact ⟨l.2, hcent_l.mpr hy⟩
    have hJfix : CFSG.Assembly.IsComponentOf (J.subgroupOf L) (ggAutFixedSubgroup u) := by
      rwa [hfix] at hJsub
    refine ⟨CFSG.Assembly.isComponentOf_iff_open.mp hJfix, ?_⟩
    have hfixmap : (ggAutFixedSubgroup u).map L.subtype =
        L ⊓ Subgroup.centralizer (D : Set G) := by
      rw [← hfix]
      exact Subgroup.map_subgroupOf_eq_of_le inf_le_left
    apply (Subgroup.map_injective L.subtype_injective)
    rw [Subgroup.map_subgroupOf_eq_of_le (hJcomp.1.trans inf_le_left),
      ← largeEvenLayer_map_of_injective L.subtype L.subtype_injective, hfixmap]
    exact hstd.1.2.2.2.2.1

theorem q1_fixed_component_data {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (y : ↥Bs) (u : MulAut ↥L), (y : G) ∈ D ∧ ggGamma L hN y = u ∧ orderOf u = p ∧
      (∀ b : ↥Bs, Commute (ggGamma L hN b) u) ∧ J ≤ L ∧
      CFSG.Open.IsComponentOf (J.subgroupOf L) (ggAutFixedSubgroup u) := by
  obtain ⟨y, u, hy, hyu, hu, hc, hJL, hJcomp, -⟩ :=
    q1_fixed_component_layer_data hcfg hN
  exact ⟨y, u, hy, hyu, hu, hc, hJL, hJcomp⟩

end CFSG.StandardType
