module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3CtxDefs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155F1
import CFSG.RankThree.PartTwo.Sec14.Item1418Res2Proof1418
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.GF2Type.Smith1980Orth.S4Fixed
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

section Img

variable {G : Type} [Group G] {d : G}

private theorem mem_pPrimeCoreOf_iff {K : Subgroup G} {x : G} (hx : x ∈ K) :
    x ∈ pPrimeCoreOf 3 K ↔ (⟨x, hx⟩ : ↥K) ∈ CFSG.pPrimeCore 3 ↥K := by
  unfold pPrimeCoreOf
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hy' : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [hy'] at hy
  · intro hxK
    exact ⟨⟨x, hx⟩, hxK, rfl⟩

private theorem res3Pt_eq_one_iff {x : G} (hx : x ∈ res3C d) :
    res3Pt d x hx = 1 ↔ x ∈ pPrimeCoreOf 3 (res3C d) := by
  rw [mem_pPrimeCoreOf_iff hx]
  exact QuotientGroup.eq_one_iff (N := CFSG.pPrimeCore 3 ↥(res3C d)) ⟨x, hx⟩

private theorem mem_res3Img_iff {H : Subgroup G} {y : Res3Bar d} :
    y ∈ res3Img d H ↔ ∃ (x : G) (hx : x ∈ res3C d), x ∈ H ∧ res3Pt d x hx = y := by
  unfold res3Img
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, x.2, hx, rfl⟩
  · rintro ⟨x, hx, hxH, rfl⟩
    exact ⟨⟨x, hx⟩, hxH, rfl⟩

private theorem res3Pt_mem_res3Img {H : Subgroup G} {x : G} (hx : x ∈ res3C d) (hxH : x ∈ H) :
    res3Pt d x hx ∈ res3Img d H :=
  mem_res3Img_iff.mpr ⟨x, hx, hxH, rfl⟩

private theorem res3Img_mono {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) :
    res3Img d H₁ ≤ res3Img d H₂ := by
  intro y hy
  obtain ⟨x, hx, hxH, rfl⟩ := mem_res3Img_iff.mp hy
  exact res3Pt_mem_res3Img hx (h hxH)

private theorem res3Pt_mul {x y : G} (hx : x ∈ res3C d) (hy : y ∈ res3C d)
    (hxy : x * y ∈ res3C d) : res3Pt d (x * y) hxy = res3Pt d x hx * res3Pt d y hy :=
  map_mul (res3Proj d) ⟨x, hx⟩ ⟨y, hy⟩

private theorem res3Pt_commute {x y : G} (hx : x ∈ res3C d) (hy : y ∈ res3C d)
    (hxy : x * y = y * x) : Commute (res3Pt d x hx) (res3Pt d y hy) := by
  have h : (⟨x, hx⟩ : ↥(res3C d)) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := Subtype.ext hxy
  show res3Proj d ⟨x, hx⟩ * res3Proj d ⟨y, hy⟩ = res3Proj d ⟨y, hy⟩ * res3Proj d ⟨x, hx⟩
  rw [← map_mul, ← map_mul, h]

private theorem res3Img_commutator {H₁ H₂ : Subgroup G} (h₁ : H₁ ≤ res3C d) (h₂ : H₂ ≤ res3C d) :
    res3Img d ⁅H₁, H₂⁆ = ⁅res3Img d H₁, res3Img d H₂⁆ := by
  have hsub : ⁅H₁, H₂⁆.subgroupOf (res3C d) =
      ⁅H₁.subgroupOf (res3C d), H₂.subgroupOf (res3C d)⁆ := by
    apply Subgroup.map_injective (res3C d).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left h₁, inf_of_le_left h₂,
      inf_of_le_left (Subgroup.commutator_le_of_le h₁ h₂)]
  unfold res3Img
  rw [hsub, Subgroup.map_commutator]

private theorem res3Img_zpowers {g : G} (hg : g ∈ res3C d) :
    res3Img d (Subgroup.zpowers g) = Subgroup.zpowers (res3Pt d g hg) := by
  have hsub : (Subgroup.zpowers g).subgroupOf (res3C d) =
      Subgroup.zpowers (⟨g, hg⟩ : ↥(res3C d)) := by
    apply Subgroup.map_injective (res3C d).subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, MonoidHom.map_zpowers,
      inf_of_le_left (Subgroup.zpowers_le.mpr hg)]
    rfl
  unfold res3Img
  rw [hsub, MonoidHom.map_zpowers]

private theorem res3Pt_mem_normalizer {x : G} (hx : x ∈ res3C d) {H : Subgroup G}
    (hxH : x ∈ Subgroup.normalizer (H : Set G)) :
    res3Pt d x hx ∈ Subgroup.normalizer (res3Img d H : Set (Res3Bar d)) := by
  have h1 : (⟨x, hx⟩ : ↥(res3C d)) ∈ Subgroup.normalizer
      ((H.subgroupOf (res3C d) : Subgroup ↥(res3C d)) : Set ↥(res3C d)) := by
    have h2 : (⟨x, hx⟩ : ↥(res3C d)) ∈
        (Subgroup.normalizer (H : Set G)).comap (res3C d).subtype := hxH
    exact Subgroup.le_normalizer_comap _ h2
  exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ h1)

private theorem mem_normalizer_pCoreOf_inf_centralizer {M B : Subgroup G} {x : G} (hxM : x ∈ M)
    (hxB : x ∈ Subgroup.centralizer (B : Set G)) :
    x ∈ Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : Subgroup.normalizer (B : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (B : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have h1 := Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hxM)
  have h2 := Subgroup.mem_normalizer_iff.mp (hN (Subgroup.centralizer_le_normalizer _ hxB))
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr (h1 y) (h2 y)

private theorem mem_normalizer_commutator {H₁ H₂ : Subgroup G} {x : G}
    (h₁ : x ∈ Subgroup.normalizer (H₁ : Set G)) (h₂ : x ∈ Subgroup.normalizer (H₂ : Set G)) :
    x ∈ Subgroup.normalizer ((⁅H₁, H₂⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h₁ h₂ ⊢
  rw [Subgroup.map_commutator, h₁, h₂]

private theorem exists_fixed_lift [Finite G] {c : G} (hc : c ∈ res3C d) (hc3 : c ^ 3 = 1)
    {X : Subgroup G} (hXC : X ≤ res3C d) (hX2 : IsPGroup 2 X)
    (hcX : c ∈ Subgroup.normalizer (X : Set G))
    {v : G} (hvX : v ∈ X) (hcv : Commute (res3Pt d c hc) (res3Pt d v (hXC hvX))) :
    ∃ (y : G) (hy : y ∈ X), c * y = y * c ∧ res3Pt d y (hXC hy) = res3Pt d v (hXC hvX) := by
  have hvC : v ∈ res3C d := hXC hvX
  have hH2 : IsPGroup 2 (X ⊓ pPrimeCoreOf 3 (res3C d) : Subgroup G) := hX2.to_inf_left
  have hcH : ∀ n ∈ (X ⊓ pPrimeCoreOf 3 (res3C d) : Subgroup G),
      c * n * c⁻¹ ∈ (X ⊓ pPrimeCoreOf 3 (res3C d) : Subgroup G) := fun n hn =>
    ⟨(Subgroup.mem_normalizer_iff.mp hcX n).mp hn.1,
     (Subgroup.mem_normalizer_iff.mp (Sec14.le_normalizer_pPrimeCoreOf 3 (res3C d) hc) n).mp
       hn.2⟩
  have hz : v⁻¹ * (c * v * c⁻¹) ∈ (X ⊓ pPrimeCoreOf 3 (res3C d) : Subgroup G) := by
    refine ⟨X.mul_mem (X.inv_mem hvX) ((Subgroup.mem_normalizer_iff.mp hcX v).mp hvX), ?_⟩
    have hzC : v⁻¹ * (c * v * c⁻¹) ∈ res3C d :=
      (res3C d).mul_mem ((res3C d).inv_mem hvC)
        ((res3C d).mul_mem ((res3C d).mul_mem hc hvC) ((res3C d).inv_mem hc))
    refine (res3Pt_eq_one_iff hzC).mp ?_
    have hcomm : res3Proj d ⟨c, hc⟩ * res3Proj d ⟨v, hvC⟩ =
        res3Proj d ⟨v, hvC⟩ * res3Proj d ⟨c, hc⟩ := hcv.eq
    have h1 : res3Proj d (⟨v, hvC⟩⁻¹ * (⟨c, hc⟩ * ⟨v, hvC⟩ * ⟨c, hc⟩⁻¹)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hcomm]
      group
    exact h1
  obtain ⟨n, hnH, hfix⟩ :=
    CFSG.GF2Type.Smith1980Orth.exists_fixed_mem_coset hH2 hc3 hcH hz
  have hnX : n ∈ X := hnH.1
  have hnC : n ∈ res3C d := hXC hnX
  refine ⟨v * n, X.mul_mem hvX hnX, ?_, ?_⟩
  · calc c * (v * n) = (c * (v * n) * c⁻¹) * c := by group
      _ = (v * n) * c := by rw [hfix]
  · have hn1 : res3Pt d n hnC = 1 := (res3Pt_eq_one_iff hnC).mpr hnH.2
    rw [res3Pt_mul hvC hnC, hn1, mul_one]

end Img

section Fields

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {d : G}
  {K : Subgroup G}

private theorem centralizer_inf_le_C (h : Res3Ctx A c L d K) :
    Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) ≤ res3C d :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ⟨h.d_mem, h.d_L⟩)

theorem Res3Ctx.obs_g_cent (h : Res3Ctx A c L d K) {g : G}
    (hgA : g ∈ Subgroup.centralizer (A : Set G)) :
    res3Pt d g (h.centralizer_le_C hgA) ∈ Subgroup.centralizer (res3Img d A : Set (Res3Bar d)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨a, haC, haA, rfl⟩ := mem_res3Img_iff.mp hz
  exact (res3Pt_commute haC _ (Subgroup.mem_centralizer_iff.mp hgA a haA)).eq

theorem Res3Ctx.obs_g_primes (h : Res3Ctx A c L d K) {g : G}
    (hgA : g ∈ Subgroup.centralizer (A : Set G))
    (hgD : g ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) (hodd : Odd (orderOf g))
    (hT90 : ∀ x ∈ Subgroup.centralizer (A : Set G), (orderOf x).Prime →
      orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 5 ∨ orderOf x = 7) :
    ∀ p : ℕ, p.Prime → p ∣ orderOf (res3Pt d g (h.centralizer_le_C hgA)) → p = 5 ∨ p = 7 := by
  intro p hp hpd
  have hpg : p ∣ orderOf g := by
    refine hpd.trans ((orderOf_map_dvd (res3Proj d) ⟨g, h.centralizer_le_C hgA⟩).trans ?_)
    rw [Subgroup.orderOf_mk]
  have hg0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hx : orderOf (g ^ (orderOf g / p)) = p := orderOf_pow_orderOf_div hg0 hpg
  have h2357 := hT90 _ (Subgroup.pow_mem _ hgA _) (by rw [hx]; exact hp)
  rw [hx] at h2357
  rcases h2357 with rfl | rfl | h5 | h7
  · exfalso
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨m, hm⟩ := hpg
    omega
  · exfalso
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcop := Sec14.coprime_card_pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))
    have hdvd : orderOf g ∣ Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :=
      Subgroup.orderOf_dvd_natCard _ hgD
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop (hpg.trans hdvd)) (by norm_num)
  · exact Or.inl h5
  · exact Or.inr h7

theorem obs_V₀_isPGroup (d : G) (M B : Subgroup G) :
    IsPGroup 2 (res3Img d (CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (B : Set G))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_inf_left).comap_subtype.map _

theorem obs_V₀_le (d : G) (M B : Subgroup G) :
    res3Img d (CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (B : Set G)) ≤
      Subgroup.centralizer (res3Img d B : Set (Res3Bar d)) := by
  intro y hy
  obtain ⟨v, hvC, hvX, rfl⟩ := mem_res3Img_iff.mp hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨b, hbC, hbB, rfl⟩ := mem_res3Img_iff.mp hz
  exact (res3Pt_commute hbC hvC (Subgroup.mem_centralizer_iff.mp hvX.2 b hbB)).eq

theorem Res3Ctx.obs_c_memV₀ (h : Res3Ctx A c L d K) {M : Subgroup G} (hAM : A ≤ M) :
    res3Pt d c h.c_mem_C ∈ Subgroup.normalizer
      (res3Img d (CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) :
        Set (Res3Bar d)) := by
  refine res3Pt_mem_normalizer h.c_mem_C
    (mem_normalizer_pCoreOf_inf_centralizer (hAM h.c_mem) ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact h.R.toSec13Data.commute (Subgroup.mem_inf.mp hb).1 h.c_mem

theorem Res3Ctx.obs_g_memV₀ (h : Res3Ctx A c L d K) {M : Subgroup G} {g : G}
    (hgA : g ∈ Subgroup.centralizer (A : Set G)) (hgM : g ∈ M) :
    res3Pt d g (h.centralizer_le_C hgA) ∈ Subgroup.normalizer
      (res3Img d (CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) :
        Set (Res3Bar d)) :=
  res3Pt_mem_normalizer _ (mem_normalizer_pCoreOf_inf_centralizer hgM
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left) hgA))

theorem obs_U_le (d : G) {M B : Subgroup G} {g : G} (hgM : g ∈ M)
    (h14a : ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆ ≤ Subgroup.centralizer (B : Set G)) :
    res3Img d ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆ ≤
      res3Img d (CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (B : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine res3Img_mono (le_inf ?_ h14a)
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp
    (Subgroup.zpowers_le.mpr (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hgM))

theorem Res3Ctx.obs_g_memU (h : Res3Ctx A c L d K) {M : Subgroup G} {g : G}
    (hgA : g ∈ Subgroup.centralizer (A : Set G)) :
    res3Pt d g (h.centralizer_le_C hgA) ∈ Subgroup.normalizer
      (res3Img d ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆ : Set (Res3Bar d)) :=
  res3Pt_mem_normalizer _
    (Subgroup.normalizer_commutator_ge_right _ _ (Subgroup.mem_zpowers g))

theorem Res3Ctx.obs_U_comm_g (h : Res3Ctx A c L d K) {M : Subgroup G} {g : G}
    (hgA : g ∈ Subgroup.centralizer (A : Set G))
    (h14a : ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆ ≤
      Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G))
    (h14b : ⁅⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆, Subgroup.zpowers g⁆ =
      ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆) :
    ⁅res3Img d ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆,
        Subgroup.zpowers (res3Pt d g (h.centralizer_le_C hgA))⁆ =
      res3Img d ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆ := by
  rw [← res3Img_zpowers (h.centralizer_le_C hgA),
    ← res3Img_commutator (h14a.trans (centralizer_inf_le_C h))
      (Subgroup.zpowers_le.mpr (h.centralizer_le_C hgA)), h14b]

theorem Res3Ctx.obs_U_comm_c (h : Res3Ctx A c L d K) {M : Subgroup G} {g : G}
    (h14a : ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆ ≤
      Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G))
    (h14c : ⁅⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆, Subgroup.zpowers c⁆ =
      ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆) :
    ⁅res3Img d ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆,
        Subgroup.zpowers (res3Pt d c h.c_mem_C)⁆ =
      res3Img d ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆ := by
  rw [← res3Img_zpowers h.c_mem_C,
    ← res3Img_commutator (h14a.trans (centralizer_inf_le_C h))
      (Subgroup.zpowers_le.mpr h.c_mem_C), h14c]

theorem Res3Ctx.obs_U_ne (h : Res3Ctx A c L d K) {X K' Y M T : Subgroup G}
    (hC : Ctx155 A X K' Y M T) {g : G}
    (hgD : g ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ M)
    (hgZ : g ∈ Subgroup.centralizer (delta A (lB A) (CFSG.Open.pCoreOf 2 M) : Set G))
    (hodd : Odd (orderOf g)) (hg1 : g ≠ 1)
    (h14a : ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆ ≤
      Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G))
    (h14b : ⁅⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆, Subgroup.zpowers g⁆ =
      ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆) :
    res3Img d ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆ ≠ ⊥ := by
  intro hU
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstd : Sec14Std G A c L := h.R.toSec14Std
  have hgA : g ∈ Subgroup.centralizer (A : Set G) := Sec14.pPrimeCoreOf_le 3 _ hgD.1
  have hgM : g ∈ M := hgD.2
  have hAM : A ≤ M := fun a ha => hC.mem_m.2 (Subgroup.mem_sup_left ha)
  have hVN : M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hWC : ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆ ≤ res3C d :=
    h14a.trans (centralizer_inf_le_C h)
  have hWV : ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆ ≤ CFSG.Open.pCoreOf 2 M :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr (hVN hgM))
  have hWO : ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆ ≤ pPrimeCoreOf 3 (res3C d) := by
    intro w hw
    have hwC : w ∈ res3C d := hWC hw
    refine (res3Pt_eq_one_iff hwC).mp ?_
    have hmem : res3Pt d w hwC ∈ res3Img d ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆ :=
      res3Pt_mem_res3Img hwC hw
    rw [hU] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hWB : ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆ ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) := by
    have hle : (pPrimeCoreOf 3 (res3C d) ⊓ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) := by
      refine Sec14.le_pPrimeCoreOf inf_le_right ?_ ?_
      · intro x hx
        have hxC : x ∈ res3C d := centralizer_inf_le_C h hx
        rw [Subgroup.mem_normalizer_iff]
        intro y
        rw [Subgroup.mem_inf, Subgroup.mem_inf]
        exact and_congr
          (Subgroup.mem_normalizer_iff.mp (Sec14.le_normalizer_pPrimeCoreOf 3 (res3C d) hxC) y)
          (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y)
      · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
          (Sec14.coprime_card_pPrimeCoreOf 3 (res3C d))
    exact (le_inf hWO h14a).trans hle
  have hE : IsHyperplane A (A ⊓ L) :=
    ⟨inf_le_left, by have := hstd.isE27.2; have := h.AL_card; omega⟩
  have hAW : A ≤ Subgroup.normalizer
      ((⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆ : Subgroup G) : Set G) := by
    intro a ha
    refine mem_normalizer_commutator (hVN (hAM ha)) ?_
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute g a from (Subgroup.mem_centralizer_iff.mp hgA a ha).symm)
      k).eq
  have hWQ := Proof1418Res2.mem_scriptQ_of_le_pPrimeCoreOf hstd.isE27 hE hWB hAW
  have hWD := le_delta hWQ hWV
  have hgW : g ∈ Subgroup.centralizer
      ((⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆ : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hWD) hgZ
  have hWbot : ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆ = ⊥ := by
    refine h14b.symm.trans ?_
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute g w from (Subgroup.mem_centralizer_iff.mp hgW w hw).symm)
      k).eq
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hWbot
  have hgV : g ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.mp (hWbot hv) g (Subgroup.mem_zpowers g)).symm
  exact hg1 (Sylow155F1.eq_one_of_mem_centralizer_pCoreOf hstd hC hgM hgV hodd)

theorem Res3Ctx.obs_exists_hyperplane_ne (h : Res3Ctx A c L d K) :
    ∃ B : Subgroup G, IsHyperplane A B ∧ B ≠ A ⊓ L := by
  have hcd : c ∉ Subgroup.zpowers d := fun hc =>
    h.c_notMem (Subgroup.zpowers_le.mpr h.d_L hc)
  refine ⟨Subgroup.zpowers c ⊔ Subgroup.zpowers d, ⟨?_, ?_⟩, ?_⟩
  · exact sup_le (Subgroup.zpowers_le.mpr h.c_mem) (Subgroup.zpowers_le.mpr h.d_mem)
  · rw [Sec13.card_zpowers_sup_zpowers_eq_nine h.R.toSec13Data.isElemAbelian
      h.R.toSec13Data.card_eq h.c_mem h.d_mem h.d_ne hcd, h.R.toSec13Data.card_eq]
  · intro hEq
    have hc : c ∈ A ⊓ L := hEq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
    exact h.c_notMem hc.2

theorem Res3Ctx.obs_F_cent (h : Res3Ctx A c L d K) {M : Subgroup G} (hAM : A ≤ M) {g : G}
    (hgA : g ∈ Subgroup.centralizer (A : Set G))
    (hCV : ∀ B : Subgroup G, IsHyperplane A B → B ≠ A ⊓ L →
      CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (B : Set G) ≤
        Subgroup.centralizer ({g} : Set G)) :
    ∀ v ∈ res3Img d
        (CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)),
      Commute (res3Pt d c h.c_mem_C) v → Commute (res3Pt d g (h.centralizer_le_C hgA)) v := by
  intro vb hvb hcv
  obtain ⟨v, hvC, hvX, rfl⟩ := mem_res3Img_iff.mp hvb
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXC : (CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) ≤
      res3C d := inf_le_right.trans (centralizer_inf_le_C h)
  have hcB : c ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact h.R.toSec13Data.commute (Subgroup.mem_inf.mp hb).1 h.c_mem
  have hc3 : c ^ 3 = 1 := by
    have := pow_orderOf_eq_one c
    rwa [h.R.toSec13Data.orderOf_eq] at this
  obtain ⟨y, hyX, hcy, hyv⟩ := exists_fixed_lift h.c_mem_C hc3 hXC
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_inf_left)
    (mem_normalizer_pCoreOf_inf_centralizer (hAM h.c_mem) hcB) hvX hcv
  have hyA : y ∈ Subgroup.centralizer (A : Set G) := by
    have hle : A ≤ Subgroup.centralizer ({y} : Set G) := by
      refine h.A_eq.le.trans (sup_le (Subgroup.zpowers_le.mpr ?_) ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hcy
      · intro b hb
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hyX.2 b hb)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  obtain ⟨B, hB, hBL⟩ := h.obs_exists_hyperplane_ne
  have hyB : y ∈ Subgroup.centralizer (B : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hB.1) hyA
  have hgy : y * g = g * y :=
    Subgroup.mem_centralizer_singleton_iff.mp (hCV B hB hBL ⟨hyX.1, hyB⟩)
  rw [← hyv]
  exact res3Pt_commute (h.centralizer_le_C hgA) (hXC hyX) hgy.symm

end Fields

section Main

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {d : G}
  {K : Subgroup G}

theorem Res3Ctx.res3QObs (h : Res3Ctx A c L d K) {X K' Y M T : Subgroup G}
    (hC : Ctx155 A X K' Y M T) {g : G} (hgA : g ∈ Subgroup.centralizer (A : Set G))
    (hgD : g ∈ pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ M)
    (hgZ : g ∈ Subgroup.centralizer (delta A (lB A) (CFSG.Open.pCoreOf 2 M) : Set G))
    (hodd : Odd (orderOf g))
    (hCV : ∀ B : Subgroup G, IsHyperplane A B → B ≠ A ⊓ L →
      CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (B : Set G) ≤
        Subgroup.centralizer ({g} : Set G))
    (hg1 : g ≠ 1)
    (h14a : ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆ ≤
      Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G))
    (h14b : ⁅⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆, Subgroup.zpowers g⁆ =
      ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆)
    (h14c : ⁅⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆, Subgroup.zpowers c⁆ =
      ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆)
    (hT90 : ∀ x ∈ Subgroup.centralizer (A : Set G), (orderOf x).Prime →
      orderOf x = 2 ∨ orderOf x = 3 ∨ orderOf x = 5 ∨ orderOf x = 7) :
    Res3QObs (res3Pt d c h.c_mem_C) (res3Pt d g (h.centralizer_le_C hgA)) (res3Img d A)
      (res3Img d (A ⊓ L))
      (res3Img d (CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)))
      (res3Img d ⁅CFSG.Open.pCoreOf 2 M, Subgroup.zpowers g⁆) := by
  have hAM : A ≤ M := fun a ha => hC.mem_m.2 (Subgroup.mem_sup_left ha)
  exact
    { g_cent := h.obs_g_cent hgA
      g_primes := h.obs_g_primes hgA hgD.1 hodd hT90
      V₀_isPGroup := obs_V₀_isPGroup d M _
      V₀_le := obs_V₀_le d M _
      c_memV₀ := h.obs_c_memV₀ hAM
      g_memV₀ := h.obs_g_memV₀ hgA hgD.2
      U_le := obs_U_le d hgD.2 h14a
      g_memU := h.obs_g_memU hgA
      U_comm_g := h.obs_U_comm_g hgA h14a h14b
      U_comm_c := h.obs_U_comm_c h14a h14c
      U_ne := h.obs_U_ne hC hgD hgZ hodd hg1 h14a h14b
      F_cent := h.obs_F_cent hAM hgA hCV }

end Main

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
