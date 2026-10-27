module

public import CFSG.LocalAnalysis.StandardType.GGE6DepPairBlockDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepZpowersInf
public import CFSG.LocalAnalysis.StandardType.GGE6DepNormalizerOfConj
public import CFSG.LocalAnalysis.StandardType.GGE6DepCorootGamma
public import CFSG.LocalAnalysis.StandardType.GGE6DepFixedByCentresGamma
public import CFSG.LocalAnalysis.StandardType.GGE6DepMemOfConjEq
public import CFSG.LocalAnalysis.StandardType.GGE6DepNoTransvectionGamma

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

private theorem gg6B_map_ggFix_mul {Bs L : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (a b : ↥Bs) :
    Subgroup.map L.subtype (ggFix ((ggGamma L hBsN a) * (ggGamma L hBsN b))) =
      L ⊓ Subgroup.centralizer ({(a : G) * (b : G)} : Set G) := by
  rw [← map_mul]
  simpa only [Subgroup.coe_mul] using map_ggFix_ggGamma L hBsN (a * b)

private theorem gg6B_centralizer_pair (a b : G) :
    Subgroup.centralizer ({(a : G), (b : G)} : Set G) =
      Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · intro h
    exact ⟨fun y hy => h y (Or.inl hy), fun y hy => h y (Or.inr hy)⟩
  · rintro ⟨h1, h2⟩ y (rfl | rfl)
    · exact h1 _ rfl
    · exact h2 _ rfl

private theorem gg6B_map_ggFix_inf {Bs L : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (a b : ↥Bs) :
    Subgroup.map L.subtype (ggFix (ggGamma L hBsN a) ⊓ ggFix (ggGamma L hBsN b)) =
      L ⊓ Subgroup.centralizer ({(a : G), (b : G)} : Set G) := by
  rw [Subgroup.map_inf (ggFix (ggGamma L hBsN a)) (ggFix (ggGamma L hBsN b)) L.subtype
      L.subtype_injective,
    map_ggFix_ggGamma L hBsN a, map_ggFix_ggGamma L hBsN b,
    gg6B_centralizer_pair (a : G) (b : G)]
  ext x
  simp only [Subgroup.mem_inf]
  tauto

private theorem gg6B_component_transport {L : Subgroup G} {M D : Subgroup ↥L} {C : Subgroup G}
    (hmap : Subgroup.map L.subtype M = C)
    (huniq : ∀ J : Subgroup ↥L, IsComponentOf J M → J = D)
    (hcomp : IsComponentOf D M) :
    IsComponentOf (Subgroup.map L.subtype D) C ∧
      (∀ D' : Subgroup G, IsComponentOf D' C → D' = Subgroup.map L.subtype D) := by
  constructor
  · rw [← hmap]
    exact isComponentOf_map_of_injective L.subtype L.subtype_injective hcomp
  · intro D' hD'
    have hD'' : IsComponentOf D' (Subgroup.map L.subtype M) := by rwa [hmap]
    obtain ⟨hcomap, hmap'⟩ :=
      isComponentOf_comap_of_injective L.subtype L.subtype_injective hD''
    rw [← hmap', huniq _ hcomap]

private theorem gg6B_isCyclic_center_map {H K : Type*} [Group H] [Group K]
    (f : H →* K) (hf : Function.Injective f) (N : Subgroup H)
    (h : IsCyclic (Subgroup.center N)) : IsCyclic (Subgroup.center (N.map f)) := by
  let e : ↥N ≃* ↥(N.map f) := Subgroup.equivMapOfInjective N f hf
  have hmap : Subgroup.center ↥(N.map f) =
      (Subgroup.center ↥N).map (e : ↥N →* ↥(N.map f)) :=
    (Subgroup.map_center_eq e).symm
  rw [hmap]
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top (Subgroup.center N)).mp h
  rw [← hg, MonoidHom.map_zpowers]
  exact Subgroup.isCyclic_zpowers (e g)

theorem ggE6Dep_pairBlock {Bs L : Subgroup G} {x : G} (hBs : IsElemAbelian 3 Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hZ : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥L))
    (hBsL : ∀ b ∈ Bs, ∃ l ∈ L, ∃ k : ℕ, b = l * x ^ k) (hnt : GGNoTransvection 3 Bs)
    {R : Type} [Group R] {I : Set (MulAut R)} {ψ : ↥L →* R}
    (hTB : GGTorusTBGroup 3 5 R I ↥L ψ (ggGamma L hBsN).range)
    (hcard : Nat.card (ggGamma L hBsN).range = 3 ^ 5) (hBl : GGE6DepBlocks R I)
    {a b : ↥Bs} (haL : (a : G) ∈ L) (hbL : (b : G) ∈ L)
    (hab : GGCorootOrth 3 (ggAutomizer L Bs) a b) :
    ∃ Dv N : Subgroup G, GGE6DepPairBlock 3 Bs L a b Dv N := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by decide
  have hx_mem : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hker]; exact Subgroup.mem_zpowers x
  have hxL : Subgroup.zpowers x ⊓ L = ⊥ :=
    GGE6Dep.zpowers_inf_eq_bot_of_centralizer hp hx_mem.2 (hBs.2 x hx_mem.1) hZ
  have hNT : ∀ φ ∈ ggTorusAut (ggGamma L hBsN).range, ¬ GGIsTransvection 3 φ :=
    ggTorusAut_noTransvection_gamma hp hBs hBsN hker hZ hBsL hnt
  have hab' : GGCorootOrth 3 (ggTorusAut (ggGamma L hBsN).range)
      ((ggGamma L hBsN).rangeRestrict a) ((ggGamma L hBsN).rangeRestrict b) :=
    ggCorootOrth_gamma hp hp2 hBs hBsN hker hxL haL hbL hab
  obtain ⟨-, hpair⟩ := hBl ↥L ψ (ggGamma L hBsN).range hTB hcard hNT
  obtain ⟨Dv, N, hDvcomp, hDvuniq, hNcomp, hNuniq, hNleDv, hCyc, -, hperp, hmove⟩ :=
    hpair ((ggGamma L hBsN).rangeRestrict a) ((ggGamma L hBsN).rangeRestrict b) hab'
  have hDvT := gg6B_component_transport (L := L)
    (M := ggFix ((ggGamma L hBsN a) * (ggGamma L hBsN b))) (D := Dv)
    (C := L ⊓ Subgroup.centralizer ({(a : G) * (b : G)} : Set G))
    (gg6B_map_ggFix_mul hBsN a b) (fun J hJ => hDvuniq J hJ) hDvcomp
  have hNT' := gg6B_component_transport (L := L)
    (M := ggFix (ggGamma L hBsN a) ⊓ ggFix (ggGamma L hBsN b)) (D := N)
    (C := L ⊓ Subgroup.centralizer ({(a : G), (b : G)} : Set G))
    (gg6B_map_ggFix_inf hBsN a b) (fun J hJ => hNuniq J hJ) hNcomp
  refine ⟨Subgroup.map L.subtype Dv, Subgroup.map L.subtype N, hDvT.1, hDvT.2, hNT'.1,
    hNT'.2, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.map_mono hNleDv
  · exact gg6B_isCyclic_center_map L.subtype L.subtype_injective N hCyc
  ·
    intro u hu huL
    have hSL : ∀ c ∈ ({a, b} : Set ↥Bs), (c : G) ∈ L := by
      intro c hc
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with rfl | rfl
      · exact haL
      · exact hbL
    have hγu :=
      ggFixedByCentres_gamma hp hp2 hBs hBsN hker hZ hBsL ({a, b} : Set ↥Bs) hSL hu
    have himg : (ggGamma L hBsN).rangeRestrict '' ({a, b} : Set ↥Bs) =
        {((ggGamma L hBsN).rangeRestrict a), ((ggGamma L hBsN).rangeRestrict b)} :=
      Set.image_pair _ _ _
    obtain ⟨n, hnN, hnconj⟩ :=
      hperp ((ggGamma L hBsN).rangeRestrict u) (by simpa only [himg] using hγu)
    have hnGN : (n : G) ∈ Subgroup.map L.subtype N := ⟨n, hnN, rfl⟩
    refine GGE6Dep.mem_of_conj_eq_of_pow_eq_one hp (Subgroup.map_subtype_le N) hZ
      hnGN huL (hBs.2 (u : G) u.2) ?_
    intro l hl
    have h1 := congrArg (fun f : MulAut ↥L => ((f ⟨l, hl⟩ : ↥L) : G)) hnconj
    simpa only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk,
      MonoidHom.coe_rangeRestrict, ggGamma_coe] using h1
  ·
    obtain ⟨n₁, hn₁Dv, hn₁N, hn₁ne⟩ := hmove
    refine ⟨(n₁ : G), ⟨n₁, hn₁Dv, rfl⟩, ?_, ?_⟩
    · exact GGE6Dep.mem_normalizer_of_conj_mem_normalizer_range hp hBsN hBs hker hZ hBsL
        n₁.2 hn₁N
    · intro hconj
      have hb : (n₁ : G) * (a : G) * (n₁ : G)⁻¹ ∈ Bs := by
        rw [hconj]; exact a.2
      have hg := ggGamma_conj L hBsN n₁ a hb
      have hsub : (⟨(n₁ : G) * (a : G) * (n₁ : G)⁻¹, hb⟩ : ↥Bs) = a :=
        Subtype.ext hconj
      rw [hsub] at hg
      refine hn₁ne ?_
      rw [show (↑((ggGamma L hBsN).rangeRestrict a) : MulAut ↥L) = ggGamma L hBsN a from
        MonoidHom.coe_rangeRestrict _ _]
      exact hg.symm

end CFSG.StandardType

end
