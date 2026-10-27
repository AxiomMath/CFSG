module

public import CFSG.Quasithin.H13.NQTermRadicalLocalization
public import CFSG.Quasithin.H13.NQTermComponentPair
public import CFSG.Quasithin.H13.NQBlockRadicalSylow
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFifteen.CoreFree
public import CFSG.Quasithin.SteinbergCCPrimeWitness

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open
open scoped Pointwise

section Core

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] [Fact p.Prime] in
theorem mem_normalizer_iff_of_ker_le {H : Type*} [Group H] (f : G →* H) {X : Subgroup G}
    (hX : f.ker ≤ X) {g : G} :
    g ∈ normalizer (X : Set G) ↔ f g ∈ normalizer ((X.map f : Subgroup H) : Set H) := by
  have key : ∀ x : G, x ∈ X ↔ f x ∈ X.map f := fun x => by
    rw [← mem_comap, comap_map_eq, sup_eq_left.mpr hX]
  constructor
  · intro hg
    exact le_normalizer_map f ⟨g, hg, rfl⟩
  · intro hg
    rw [mem_normalizer_iff] at hg ⊢
    intro h
    rw [key, key, map_mul, map_mul, map_inv]
    exact hg (f h)

theorem map_pCoreOf_le {H : Type*} [Group H] [Finite H] (f : G →* H) (Y : Subgroup G) :
    (pCoreOf p Y).map f ≤ pCoreOf p (Y.map f) := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
    (map_mono (CFSG.LieType.BorelTits.pCoreOf_le p Y)) ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup p Y).map f)
  exact (map_mono (le_normalizer.trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p Y))).trans (le_normalizer_map f)

theorem pCoreOf_eq_comap_inf {H : Type*} [Group H] [Finite H] (f : G →* H)
    (hf : IsPGroup p f.ker) (Y : Subgroup G) :
    pCoreOf p Y = (pCoreOf p (Y.map f)).comap f ⊓ Y := by
  refine le_antisymm (le_inf (map_le_iff_le_comap.mp (map_pCoreOf_le f Y))
    (CFSG.LieType.BorelTits.pCoreOf_le p Y)) ?_
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p inf_le_right (fun y hy => ?_)
    (((CFSG.LieType.BorelTits.pCoreOf_isPGroup p (Y.map f)).comap_of_ker_isPGroup f hf).to_le
      inf_le_left)
  have hyN : f y ∈ normalizer ((pCoreOf p (Y.map f) : Subgroup H) : Set H) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p (Y.map f)
      (le_normalizer ⟨y, hy, rfl⟩)
  rw [mem_normalizer_iff] at hyN ⊢
  intro x
  rw [mem_inf, mem_inf, mem_comap, mem_comap, map_mul, map_mul, map_inv, ← hyN (f x)]
  exact and_congr_right fun _ => (mem_normalizer_iff.mp (le_normalizer hy) x)

end Core

section Localize

variable {G : Type*} [Group G] [Finite G]

theorem prime_radical_normalizers_localize_to_actual_Ccomponents {p : ℕ} (hp : p.Prime)
    {S : Subgroup G} (hS : IsPGroup p S) (hSO : S = pCoreOf p (normalizer (S : Set G)))
    {L : Subgroup G} (hL : CFSG.IsCComponent L)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore p ↥L)) :
    (L : Set G) * ((S ⊓ normalizer (L : Set G) : Subgroup G) : Set G) =
        ((L ⊔ (S ⊓ normalizer (L : Set G)) : Subgroup G) : Set G) ∧
      S ⊓ L = pCoreOf p (L ⊓ normalizer (S : Set G)) ∧
      pCoreOf p (L ⊓ normalizer (S : Set G)) =
        pCoreOf p (L ⊓ normalizer ((S ⊓ L : Subgroup G) : Set G)) ∧
      S ⊓ normalizer (L : Set G) = pCoreOf p ((L ⊔ (S ⊓ normalizer (L : Set G))) ⊓
        normalizer ((S ⊓ normalizer (L : Set G) : Subgroup G) : Set G)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set N := CFSG.pCore p G with hN
  have hNn : N.Normal := CFSG.pCore_normal
  have hN2 : IsPGroup p N := CFSG.pCore_isPGroup
  have hNs : Group.IsSolvable N := by
    have := hN2.isNilpotent
    infer_instance
  have hNS : N ≤ S := NQTerm.le_of_isPGroup_of_le_normalizer hS hSO hN2 (by
    rw [normalizer_eq_top_iff.mpr hNn]
    exact le_top)
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hker2 : IsPGroup p π.ker := by rw [hker]; exact hN2
  have hcomap : ∀ X : Subgroup G, N ≤ X → (X.map π).comap π = X := fun X hX => by
    rw [comap_map_eq, hker, sup_eq_left.mpr hX]
  have hmemmap : ∀ X : Subgroup G, N ≤ X → ∀ x : G, x ∈ X ↔ π x ∈ X.map π := fun X hX x => by
    rw [← mem_comap, hcomap X hX]
  have hnorm : ∀ X : Subgroup G, N ≤ X → ∀ g : G,
      g ∈ normalizer (X : Set G) ↔ π g ∈ normalizer ((X.map π : Subgroup _) : Set _) :=
    fun X hX g => mem_normalizer_iff_of_ker_le π (by rw [hker]; exact hX)
  set Sb := S.map π with hSb
  set Lb := L.map π with hLb
  have hSbp : IsPGroup p Sb := hS.map π
  have hNSmap : (normalizer (S : Set G)).map π = normalizer (Sb : Set (G ⧸ N)) := by
    refine le_antisymm (le_normalizer_map π) fun x hx => ?_
    obtain ⟨g, rfl⟩ := hπs x
    exact ⟨g, (hnorm S hNS g).mpr hx, rfl⟩
  have hSbO : Sb = pCoreOf p (normalizer (Sb : Set (G ⧸ N))) := by
    refine le_antisymm (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p le_normalizer le_rfl
      hSbp) fun x hx => ?_
    have hx' : x ∈ normalizer (Sb : Set (G ⧸ N)) := CFSG.LieType.BorelTits.pCoreOf_le p _ hx
    rw [← hNSmap] at hx'
    obtain ⟨g, hg, rfl⟩ := hx'
    have h1 := pCoreOf_eq_comap_inf (p := p) π hker2 (normalizer (S : Set G))
    rw [← hSO, hNSmap] at h1
    have hgS : g ∈ S := h1.ge (mem_inf.mpr ⟨hx, hg⟩)
    exact mem_map_of_mem π hgS
  have hLsub : L.IsSubnormal := hL.2.2.1
  have hLN : (CFSG.pCore p ↥L).map L.subtype = L ⊓ N := by
    refine le_antisymm (le_inf (map_subtype_le _)
      (CFSG.LyonsUnitaryFour.map_pCore_le_pCore_of_isSubnormal hLsub)) ?_
    have h1 : N.subgroupOf L ≤ CFSG.pCore p ↥L := by
      refine SteinbergCC.le_pCore_of_normal_of_isPGroup ?_ hN2.comap_subtype
      exact hNn.subgroupOf L
    have h2 := map_mono (f := L.subtype) h1
    rwa [subgroupOf_map_subtype, inf_comm] at h2
  have hkerL : (π.subgroupMap L).ker = CFSG.pCore p ↥L := by
    apply map_injective L.subtype_injective
    rw [hLN]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : π (y : G) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
      rw [← MonoidHom.mem_ker, hker] at hy'
      exact ⟨y.2, hy'⟩
    · rintro ⟨hxL, hxN⟩
      refine ⟨⟨x, hxL⟩, MonoidHom.mem_ker.mpr (Subtype.ext ?_), rfl⟩
      show π x = 1
      rw [← MonoidHom.mem_ker, hker]
      exact hxN
  let eL : (↥L ⧸ CFSG.pCore p ↥L) ≃* ↥Lb :=
    (QuotientGroup.quotientMulEquivOfEq hkerL.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (π.subgroupMap L) (π.subgroupMap_surjective L))
  have hLbq : CFSG.IsQuasisimple ↥Lb := CFSG.LocalCores.isQuasisimple_of_mulEquiv eL hLq
  have hLbc : CFSG.IsComponent Lb := ⟨hLbq, hLsub.map hπs⟩
  set Δ : Set (Subgroup (G ⧸ N)) := {M | ∃ g : G ⧸ N, M = Lb.map (MulAut.conj g).toMonoidHom}
    with hΔ
  have hΔcomp : ∀ M ∈ Δ, CFSG.IsComponent M := by
    rintro _ ⟨g, rfl⟩
    have h1 := NQTerm.isComponent_conjugate hLbc g⁻¹
    rwa [CFSG.conjugate, inv_inv] at h1
  have hΔK : ∀ k ∈ normalizer (Sb : Set (G ⧸ N)), ∀ M ∈ Δ,
      M.map (MulAut.conj k).toMonoidHom ∈ Δ := by
    rintro k - _ ⟨g, rfl⟩
    exact ⟨k * g, (NQTerm.map_conj_mul Lb k g).symm⟩
  have hΔc : ∀ M₁ ∈ Δ, ∀ M₂ ∈ Δ, M₁ ≠ M₂ → ⁅M₁, M₂⁆ = ⊥ := fun M₁ h₁ M₂ h₂ hne =>
    (CFSG.LocalCores.distinct_components_commute (hΔcomp M₁ h₁) (hΔcomp M₂ h₂)).resolve_left hne
  have hLΔ : Lb ∈ Δ := ⟨1, by rw [map_one]; exact (Subgroup.map_id Lb).symm⟩
  obtain ⟨-, h1, h2, -, h3⟩ :=
    NQTerm.prime_radical_localization_on_commuting_orbits hp hSbp hSbO hΔK hΔc hLΔ
  have hSLc : (Sb ⊓ Lb).comap π ⊓ L = S ⊓ L := by
    ext x
    constructor
    · rintro ⟨⟨hxS, -⟩, hxL⟩
      exact ⟨(hmemmap S hNS x).mpr hxS, hxL⟩
    · rintro ⟨hxS, hxL⟩
      exact ⟨⟨mem_map_of_mem π hxS, mem_map_of_mem π hxL⟩, hxL⟩
  have hSLmap : (S ⊓ L).map π = Sb ⊓ Lb := by
    refine le_antisymm (map_inf_le _ _ _) fun x hx => ?_
    obtain ⟨l, hl, rfl⟩ := (mem_inf.mp hx).2
    exact ⟨l, ⟨(hmemmap S hNS l).mpr (mem_inf.mp hx).1, hl⟩, rfl⟩
  have hLR : (L : Set G) * ((S ⊓ normalizer (L : Set G) : Subgroup G) : Set G) =
      ((L ⊔ (S ⊓ normalizer (L : Set G)) : Subgroup G) : Set G) :=
    (coe_mul_of_right_le_normalizer_left L _ inf_le_right).symm
  have hY1 : (L ⊓ normalizer (S : Set G)).map π = Lb ⊓ normalizer (Sb : Set (G ⧸ N)) := by
    refine le_antisymm ((map_inf_le _ _ _).trans (inf_le_inf_left _ (le_normalizer_map π)))
      fun x hx => ?_
    obtain ⟨l, hl, rfl⟩ := (mem_inf.mp hx).1
    exact ⟨l, mem_inf.mpr ⟨hl, (hnorm S hNS l).mpr (mem_inf.mp hx).2⟩, rfl⟩
  have hSL1 : S ⊓ L = pCoreOf p (L ⊓ normalizer (S : Set G)) := by
    rw [pCoreOf_eq_comap_inf π hker2, hY1, ← h1]
    ext x
    constructor
    · intro hx
      have hx' : x ∈ (Sb ⊓ Lb).comap π ⊓ L := hSLc.ge hx
      exact ⟨hx'.1, hx'.2, (mem_normalizer_iff.mp (le_normalizer (mem_inf.mp hx).1))⟩
    · rintro ⟨hxc, hxL, -⟩
      exact hSLc.le ⟨hxc, hxL⟩
  have hnSL : ∀ l ∈ L, l ∈ normalizer ((S ⊓ L : Subgroup G) : Set G) ↔
      π l ∈ normalizer ((Sb ⊓ Lb : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    intro l hl
    constructor
    · intro h
      rw [← hSLmap]
      exact le_normalizer_map π ⟨l, h, rfl⟩
    · intro h
      have h1 : l ∈ normalizer (((Sb ⊓ Lb).comap π : Subgroup G) : Set G) := by
        rw [mem_normalizer_iff] at h ⊢
        intro y
        rw [mem_comap, mem_comap, map_mul, map_mul, map_inv]
        exact h (π y)
      rw [← hSLc]
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, le_normalizer hl⟩
  have hY2 : (L ⊓ normalizer ((S ⊓ L : Subgroup G) : Set G)).map π =
      Lb ⊓ normalizer ((Sb ⊓ Lb : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    apply le_antisymm
    · rintro _ ⟨l, hl, rfl⟩
      exact mem_inf.mpr ⟨mem_map_of_mem π (mem_inf.mp hl).1,
        (hnSL l (mem_inf.mp hl).1).mp (mem_inf.mp hl).2⟩
    · intro x hx
      obtain ⟨l, hl, rfl⟩ := (mem_inf.mp hx).1
      exact ⟨l, mem_inf.mpr ⟨hl, (hnSL l hl).mpr (mem_inf.mp hx).2⟩, rfl⟩
  have hSL2 : S ⊓ L = pCoreOf p (L ⊓ normalizer ((S ⊓ L : Subgroup G) : Set G)) := by
    rw [pCoreOf_eq_comap_inf π hker2, hY2, ← h2, ← h1]
    ext x
    constructor
    · intro hx
      have hx' : x ∈ (Sb ⊓ Lb).comap π ⊓ L := hSLc.ge hx
      exact ⟨hx'.1, hx'.2, mem_normalizer_iff.mp (le_normalizer hx)⟩
    · rintro ⟨hxc, hxL, -⟩
      exact hSLc.le ⟨hxc, hxL⟩
  have hnormL : ∀ g : G, g ∈ normalizer (L : Set G) ↔
      π g ∈ normalizer ((Lb : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    intro g
    constructor
    · intro hg
      exact le_normalizer_map π ⟨g, hg, rfl⟩
    · intro hg
      rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
      have hLg : CFSG.IsCComponent (L.map (MulAut.conj g).toMonoidHom) :=
        NQBlock.isCComponent_map_mulEquiv (MulAut.conj g) hL
      have himg : (L.map (MulAut.conj g).toMonoidHom).map π = Lb := by
        rw [map_map, ← hg, hLb, map_map]
        exact congrArg (fun f => L.map f) (MonoidHom.ext fun x => by simp [MulAut.conj_apply])
      have hinj := (NQBlock.Ccomponent_solvable_quotient_bijection N hNs).1.injOn
      exact hinj hLg hL himg
  have hNNL : N ≤ normalizer (L : Set G) := fun n hn => (hnormL n).mpr (by
    rw [show π n = 1 from (QuotientGroup.eq_one_iff n).mpr hn]
    exact one_mem _)
  set R := S ⊓ normalizer (L : Set G) with hR
  have hNR : N ≤ R := le_inf hNS hNNL
  have hRmap : R.map π = Sb ⊓ normalizer ((Lb : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    refine le_antisymm ((map_inf_le _ _ _).trans (inf_le_inf_left _ (le_normalizer_map π)))
      fun x hx => ?_
    obtain ⟨s, hs, rfl⟩ := (mem_inf.mp hx).1
    exact ⟨s, mem_inf.mpr ⟨hs, (hnormL s).mpr (mem_inf.mp hx).2⟩, rfl⟩
  have hY3 : ((L ⊔ R) ⊓ normalizer (R : Set G)).map π =
      (Lb ⊔ (Sb ⊓ normalizer ((Lb : Subgroup (G ⧸ N)) : Set (G ⧸ N)))) ⊓
        normalizer ((Sb ⊓ normalizer ((Lb : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :
          Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    rw [← hRmap, ← Subgroup.map_sup]
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact mem_inf.mpr ⟨mem_map_of_mem π (mem_inf.mp hy).1,
        (hnorm R hNR y).mp (mem_inf.mp hy).2⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := (mem_inf.mp hx).1
      exact ⟨y, mem_inf.mpr ⟨hy, (hnorm R hNR y).mpr (mem_inf.mp hx).2⟩, rfl⟩
  have hR3 : R = pCoreOf p ((L ⊔ R) ⊓ normalizer (R : Set G)) := by
    rw [pCoreOf_eq_comap_inf π hker2, hY3, ← h3, ← hRmap, hcomap R hNR]
    exact (inf_eq_left.mpr (le_inf le_sup_right le_normalizer)).symm
  exact ⟨hLR, hSL1, hSL1.symm.trans hSL2, hR3⟩

end Localize

end CFSG.Quasithin.H13.NQRigid
