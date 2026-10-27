module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Background.GoldschmidtS146RQuot

public section

namespace CFSG.Quasithin.F146Field

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace Case2a

section Generic

variable {G : Type} [Group G] [Finite G]

theorem le_of_le_normalizer {C S X : Subgroup G} (hS : IsSylowTwoOf S C)
    (hC : C ≤ Subgroup.normalizer (S : Set G)) (hX : IsPGroup 2 X) (hXC : X ≤ C) : X ≤ S := by
  obtain ⟨Q, hXQ, hQ⟩ := exists_isSylowTwoOf_of_le hXC hX
  obtain ⟨g, hg, hgQ⟩ := B6.isSylowTwoOf_exists_conj hS hQ
  rw [hgQ, B6.conjSub_eq_self (hC hg)] at hXQ
  exact hXQ

theorem mem_normalizer_of_conj_le {K P B : Subgroup G} (hP : IsSylowTwoOf P K) {x : G}
    (hx : x ∈ K) (hPB : P ≤ B) (hBK : B ≤ K) (hB : B ≤ Subgroup.normalizer (P : Set G))
    (hcj : ∀ p ∈ P, x * p * x⁻¹ ∈ B) : x ∈ Subgroup.normalizer (P : Set G) := by
  have hxK : B6.conjSub x K = K := B6.conjSub_eq_self (Subgroup.le_normalizer hx)
  have h1 : IsSylowTwoOf P B := B6.isSylowTwoOf_mono hP hPB hBK
  have h2 : IsSylowTwoOf (B6.conjSub x P) K := by
    have := B6.isSylowTwoOf_conjSub hP x
    rwa [hxK] at this
  have hle : B6.conjSub x P ≤ B := by
    intro y hy
    rw [B6.mem_conjSub] at hy
    have := hcj _ hy
    simpa [mul_assoc] using this
  have h3 : IsSylowTwoOf (B6.conjSub x P) B := B6.isSylowTwoOf_mono h2 hle hBK
  obtain ⟨g, hg, hgeq⟩ := B6.isSylowTwoOf_exists_conj h1 h3
  have h4 : B6.conjSub x P = P := by
    rw [hgeq]
    exact B6.conjSub_eq_self (hB hg)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h4

end Generic

section Star

variable {G : Type} [Group G]

theorem mem_star_iff {M H X : Subgroup G} (hXH : X ≤ H) (hJH : kerIn M H ≤ H) (h : ↥H) :
    (h : E2.StarQuot M H) ∈ E2.star M H X ↔ (h : G) ∈ X ⊔ kerIn M H :=
  GoldS146R.mk_mem_imgJ hXH hJH h

theorem exists_of_mem_star {M H X : Subgroup G} {q : E2.StarQuot M H} (hq : q ∈ E2.star M H X) :
    ∃ h : ↥H, (h : G) ∈ X ∧ (h : E2.StarQuot M H) = q :=
  GoldS146R.mem_imgJ.mp hq

theorem mk_mem_normalizer_star {M H X : Subgroup G} (hXH : X ≤ H) (hJH : kerIn M H ≤ H)
    {x : ↥H} (hx : (x : G) ∈ Subgroup.normalizer (X : Set G)) :
    (x : E2.StarQuot M H) ∈ Subgroup.normalizer (E2.star M H X : Set (E2.StarQuot M H)) := by
  have hn : (x : G) ∈ Subgroup.normalizer ((X ⊔ kerIn M H : Subgroup G) : Set G) :=
    F6.mem_normalizer_sup hx (le_normalizer_kerIn M H x.2)
  rw [Subgroup.mem_normalizer_iff]
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    mem_star_iff hXH hJH, mem_star_iff hXH hJH]
  exact Subgroup.mem_normalizer_iff.mp hn (y : G)

@[expose] def starHom {M H K : Subgroup G} (hKH : K ≤ H) : ↥K →* ↥(E2.star M H K) :=
  ((QuotientGroup.mk' ((kerIn M H).subgroupOf H)).comp (Subgroup.inclusion hKH)).codRestrict
    (E2.star M H K) (fun x => GoldS146R.mem_imgJ.mpr ⟨Subgroup.inclusion hKH x, x.2, rfl⟩)

theorem coe_starHom {M H K : Subgroup G} (hKH : K ≤ H) (x : ↥K) :
    ((starHom (M := M) hKH x : ↥(E2.star M H K)) : E2.StarQuot M H) =
      ((Subgroup.inclusion hKH x : ↥H) : E2.StarQuot M H) := rfl

theorem starHom_surjective {M H K : Subgroup G} (hKH : K ≤ H) :
    Function.Surjective (starHom (M := M) hKH) := by
  intro y
  obtain ⟨h, hh, hy⟩ := exists_of_mem_star y.2
  exact ⟨⟨h, hh⟩, Subtype.ext hy⟩

theorem starHom_eq_one_iff {M H K : Subgroup G} (hKH : K ≤ H) (x : ↥K) :
    starHom (M := M) hKH x = 1 ↔ (x : G) ∈ kerIn M H := by
  rw [← Subtype.coe_inj, coe_starHom, Subgroup.coe_one, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  rfl

theorem isSylowTwoOf_star {M H K P : Subgroup G} (hKH : K ≤ H) (hP : IsSylowTwoOf P K) :
    IsSylowTwoOf (E2.star M H P) (E2.star M H K) := by
  have hPK : P ≤ K := hP.1
  have hPH : P ≤ H := hPK.trans hKH
  have hmap : (P.subgroupOf K).map (starHom (M := M) hKH) =
      (E2.star M H P).subgroupOf (E2.star M H K) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact GoldS146R.mem_imgJ.mpr ⟨Subgroup.inclusion hKH x, hx, rfl⟩
    · intro hy
      obtain ⟨h, hh, hhy⟩ := exists_of_mem_star hy
      exact ⟨⟨h, hPK hh⟩, hh, Subtype.ext hhy⟩
  refine ⟨Subgroup.map_mono (Subgroup.comap_mono hPK), ?_, ?_⟩
  · have h2 : IsPGroup 2 (P.subgroupOf H) :=
      hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
    exact h2.map _
  · rw [← hmap]
    intro hd
    exact hP.2.2 (hd.trans (Subgroup.index_map_dvd _ (starHom_surjective hKH)))

end Star

end Case2a

end CFSG.Quasithin.F146Field
