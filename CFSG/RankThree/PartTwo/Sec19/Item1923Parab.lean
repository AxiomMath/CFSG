module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs
import CFSG.GroupTheory.SylowTwoOfConj
import CFSG.GroupTheory.PermSylowTwo.Alt

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec19 (starIm IsList194 IsSmall194 IsTripleA6 IsProperParabolic
  Item194UsedWide3 Item316)

variable {G : Type} [Group G] [Finite G] {A M N L K : Subgroup G} {c : G}

private theorem parab_isSylowTwoOf_top (X : Type) [Group X] [Finite X] (T : Sylow 2 X) :
    CFSG.QuasithinUnique.IsSylowTwoOf (T : Subgroup X) ⊤ := by
  refine ⟨le_top, T.isPGroup', ?_⟩
  change ¬ 2 ∣ (T : Subgroup X).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact Sylow.not_dvd_index T

private theorem parab_normalizer_le_of_isSylowTwoOf {X : Type} [Group X] [Finite X]
    {T P : Subgroup X} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T P)
    (hN : Subgroup.normalizer (T : Set X) ≤ P) :
    Subgroup.normalizer (P : Set X) ≤ P := by
  intro x hx
  have hxP : CFSG.Quasithin.conjSub x P = P := by
    ext z
    rw [CFSG.Quasithin.mem_conjSub]
    have h := Subgroup.mem_normalizer_iff.mp hx (x⁻¹ * z * x)
    rw [show x * (x⁻¹ * z * x) * x⁻¹ = z by group] at h
    exact h
  have hT' : CFSG.QuasithinUnique.IsSylowTwoOf (CFSG.Quasithin.conjSub x T) P := by
    have h := CFSG.Quasithin.F7.isSylowTwoOf_conj hT x
    rwa [hxP] at h
  obtain ⟨g, hgP, hg⟩ := CFSG.GroupTheory.exists_eq_conjSub_of_isSylowTwoOf hT hT'
  have hconj : CFSG.Quasithin.conjSub (x⁻¹ * g) T = T := by
    rw [CFSG.Quasithin.conjSub_mul, ← hg, CFSG.Quasithin.conjSub_conjSub_inv]
  have hy : g⁻¹ * x ∈ Subgroup.normalizer (T : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have e := CFSG.Quasithin.mem_conjSub (g := x⁻¹ * g) (x := h) (H := (T : Subgroup X))
    rw [hconj] at e
    have e2 : (x⁻¹ * g)⁻¹ * h * (x⁻¹ * g) = g⁻¹ * x * h * (g⁻¹ * x)⁻¹ := by group
    rw [e2] at e
    exact e
  have hgx := P.mul_mem hgP (hN hy)
  rwa [mul_inv_cancel_left] at hgx

private theorem parab_exists_isSylowTwoOf_top_of_isExtOf {X : Type} [Group X] [Finite X]
    {P : Subgroup X} (e : X ≃* alternatingGroup (Fin 10))
    (hext : Sec4.IsExtOf P (Equiv.Perm (Fin 5)) (Multiplicative (Fin 4 → ZMod 2))) :
    ∃ S : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ ∧ S ≤ P ∧
      Subgroup.normalizer (S : Set X) ≤ S := by
  obtain ⟨K, hKn, hKB, hQA⟩ := hext
  obtain ⟨eK⟩ := hKB
  obtain ⟨eQ⟩ := hQA
  have hKcard : Nat.card K = 16 := by
    rw [Nat.card_congr eK.toEquiv]
    show Nat.card (Fin 4 → ZMod 2) = 16
    norm_num [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card]
  have hKindex : K.index = 120 := by
    rw [Subgroup.index, Nat.card_congr eQ.toEquiv, Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  have hPcard : Nat.card P = 1920 := by
    have h := Subgroup.card_mul_index (H := K)
    rw [hKcard, hKindex] at h
    omega
  have hXcard : Nat.card X = 1814400 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.card_eq_fintype_card, Nat.factorial]
  obtain ⟨K2, hK2⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥P) 2 (n := 7)
    (by rw [hPcard]; norm_num)
  have hSP : K2.map P.subtype ≤ P := Subgroup.map_subtype_le K2
  have hScard : Nat.card (K2.map P.subtype) = 2 ^ 7 := by
    rw [Subgroup.card_map_of_injective (f := P.subtype) Subtype.val_injective, hK2]
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf (K2.map P.subtype) ⊤ := by
    refine ⟨le_top, IsPGroup.iff_card.mpr ⟨7, hScard⟩, ?_⟩
    change ¬ 2 ∣ (K2.map P.subtype).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    have h := Subgroup.card_mul_index (H := K2.map P.subtype)
    rw [hScard, hXcard] at h
    norm_num at h
    omega
  refine ⟨K2.map P.subtype, hS, hSP, ?_⟩
  intro y hy
  have h := CFSG.GroupTheory.PermSylowTwo.inf_normalizer_le_of_mulEquiv_alt (n := 10)
    (by norm_num) (Subgroup.topEquiv.trans e) hS
  exact h (Subgroup.mem_inf.mpr ⟨Subgroup.mem_top y, hy⟩)

private theorem parab_exists_isSylowTwoOf_normalizer_le {X : Type} [Group X] [Finite X]
    {P : Subgroup X} (hP : ParabolicShape X P) :
    ∃ T : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf T P ∧
      Subgroup.normalizer (T : Set X) ≤ P := by
  rcases hP with ⟨-, hpar⟩ | ⟨⟨e⟩, hext⟩
  · obtain ⟨-, T, hT⟩ := hpar
    have hTP : (T : Subgroup X) ≤ P := le_trans Subgroup.le_normalizer hT
    exact ⟨T, CFSG.Quasithin.F7.isSylowTwoOf_mono_right (parab_isSylowTwoOf_top X T) hTP le_top,
      hT⟩
  · obtain ⟨S, hS, hSP, hNS⟩ := parab_exists_isSylowTwoOf_top_of_isExtOf e hext
    exact ⟨S, CFSG.Quasithin.F7.isSylowTwoOf_mono_right hS hSP le_top, hNS.trans hSP⟩

theorem step1923_normalizer_parab {X : Type} [Group X] [Finite X] {P : Subgroup X}
    (hP : ParabolicShape X P) : Subgroup.normalizer (P : Set X) = P := by
  obtain ⟨T, hT, hN⟩ := parab_exists_isSylowTwoOf_normalizer_le hP
  exact le_antisymm (parab_normalizer_le_of_isSylowTwoOf hT hN) Subgroup.le_normalizer

private theorem parab_barAut_maps_starIm (g : Subgroup.normalizer (K : Set G))
    (hg : (g : G) ∈ N) :
    ∀ s ∈ starIm K N, Sec3.Sims321.barAut K g s ∈ starIm K N := by
  rintro s hs
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hs
  refine Subgroup.mem_map.mpr
    ⟨⟨(g : G) * z * (g : G)⁻¹, Sec3.Sims321.conj_mem_of_mem_normalizer K g z⟩, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mpr
      (N.mul_mem (N.mul_mem hg (Subgroup.mem_subgroupOf.mp hz)) (N.inv_mem hg))
  · exact (Sec3.Sims321.barAut_mk K g z).symm

private theorem parab_normalizes_starIm {x : G} {k : K ⧸ CFSG.pCore 2 K} (hxN : x ∈ N)
    (hx : x ∈ Subgroup.normalizer (K : Set G))
    (hk : MulAut.conj k = Sec3.Sims321.barAut K ⟨x, hx⟩) :
    k ∈ Subgroup.normalizer
      ((starIm K N : Subgroup (K ⧸ CFSG.pCore 2 K)) : Set (K ⧸ CFSG.pCore 2 K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    have h1 := parab_barAut_maps_starIm ⟨x, hx⟩ hxN s hs
    rw [← hk, MulAut.conj_apply] at h1
    exact h1
  · intro hs
    have h1 := parab_barAut_maps_starIm (⟨x, hx⟩ : Subgroup.normalizer (K : Set G))⁻¹
      (N.inv_mem hxN) (k * s * k⁻¹) hs
    rw [map_inv, ← hk, MulAut.conj_inv_apply] at h1
    have e : k⁻¹ * (k * s * k⁻¹) * k = s := by group
    rwa [e] at h1

theorem step1923_inner_mem_parab (h : Hyp1921 G A M N L)
    (hP : ParabolicShape (K ⧸ CFSG.pCore 2 K) (starIm K N)) {x : G} (hxN : x ∈ N)
    (hx : x ∈ Subgroup.normalizer (K : Set G))
    (hxi : Sec3.Sims321.barAut K ⟨x, hx⟩ ∈ inner (K ⧸ CFSG.pCore 2 K)) :
    Sec3.Sims321.barAut K ⟨x, hx⟩ ∈
      (starIm K N).map (MulAut.conj : (K ⧸ CFSG.pCore 2 K) →* MulAut (K ⧸ CFSG.pCore 2 K)) := by
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hxi
  have hkN := parab_normalizes_starIm hxN hx hk
  have hkS : k ∈ starIm K N := by
    rw [step1923_normalizer_parab hP] at hkN
    exact hkN
  exact Subgroup.mem_map.mpr ⟨k, hkS, hk⟩

end CFSG.RankThree.PartTwo.Late
