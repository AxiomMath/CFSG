module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBar
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private abbrev O2sub (L : Subgroup G) : Subgroup ↥L := CFSG.pCore 2 ↥L

private theorem mem_O2sub_iff {L : Subgroup G} {x : ↥L} :
    x ∈ O2sub L ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 L := by
  rw [CFSG.Open.pCoreOf]
  exact (Subgroup.mem_map_iff_mem (f := L.subtype) L.subtype_injective).symm

private theorem O2sub_map (L : Subgroup G) (e : MulAut ↥L) :
    (O2sub L).map (e : ↥L →* ↥L) = O2sub L := by
  rw [← MulEquiv.toMonoidHom_eq_coe]
  exact Subgroup.characteristic_iff_map_eq.mp
    (inferInstance : (O2sub L).Characteristic) e

private theorem normalizerMonoidHom_apply_coe (L : Subgroup G)
    (n : Subgroup.normalizer (L : Set G)) (y : ↥L) :
    (((Subgroup.normalizerMonoidHom L) n) y : G) = (n : G) * (y : G) * (n : G)⁻¹ :=
  rfl

private noncomputable def barAction (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) →* MulAut (↥L ⧸ O2sub L) :=
  MonoidHom.mk'
    (fun n => QuotientGroup.congr (O2sub L) (O2sub L)
      ((Subgroup.normalizerMonoidHom L) n) (O2sub_map L ((Subgroup.normalizerMonoidHom L) n)))
    (by
      intro m n
      apply MulEquiv.ext
      intro a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
      rw [QuotientGroup.congr_mk, MulAut.mul_apply, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk, map_mul, MulAut.mul_apply])

private theorem barAction_mk (L : Subgroup G)
    (n : Subgroup.normalizer (L : Set G)) (y : ↥L) :
    barAction L n (QuotientGroup.mk y) =
      QuotientGroup.mk (((Subgroup.normalizerMonoidHom L) n) y) :=
  rfl

private theorem barAction_eq_one_iff (L : Subgroup G)
    (n : Subgroup.normalizer (L : Set G)) :
    barAction L n = 1 ↔ ∀ y ∈ L, ⁅(n : G), y⁆ ∈ CFSG.Open.pCoreOf 2 L := by
  constructor
  · intro h y hy
    let y' : ↥L := ⟨y, hy⟩
    have h1 : barAction L n (QuotientGroup.mk y') = QuotientGroup.mk y' := by
      rw [h, MulAut.one_apply]
    rw [barAction_mk] at h1
    have h2 : ((Subgroup.normalizerMonoidHom L) n y') / y' ∈ O2sub L :=
      QuotientGroup.eq_iff_div_mem.mp h1
    rw [mem_O2sub_iff] at h2
    simpa [commutatorElement_def, Subgroup.coe_div, normalizerMonoidHom_apply_coe,
      div_eq_mul_inv] using h2
  · intro h
    apply MulEquiv.ext
    intro a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
    rw [barAction_mk, MulAut.one_apply, QuotientGroup.eq_iff_div_mem, mem_O2sub_iff]
    simpa [commutatorElement_def, Subgroup.coe_div, normalizerMonoidHom_apply_coe,
      div_eq_mul_inv] using h (y : G) y.2

private theorem barAction_eq_of_inner {L : Subgroup G} {x l : G}
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hlL : l ∈ L)
    (h : ∀ y ∈ L, (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 L) :
    barAction L ⟨x, hxN⟩ = barAction L ⟨l, Subgroup.le_normalizer hlL⟩ := by
  apply MulEquiv.ext
  intro a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
  rw [barAction_mk, barAction_mk, QuotientGroup.eq_iff_div_mem, mem_O2sub_iff]
  simpa [Subgroup.coe_div, normalizerMonoidHom_apply_coe, div_eq_mul_inv] using h (y : G) y.2

theorem le_sup_centralizerBar_of_inner
    {G : Type} [Group G] [Finite G] {P L Q X : Subgroup G}
    (hQP : Q ≤ P) (hQL : Q ≤ L) (hQeq : Q = P ⊓ L)
    (hQnormP : (Q.subgroupOf P).Normal)
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q L)
    (hP3 : IsPGroup 3 P) (hPNL : P ≤ Subgroup.normalizer (L : Set G))
    (hX : X ≤ P)
    (hInner : ∀ x ∈ X, ∃ l ∈ L, ∀ y ∈ L,
      (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 L) :
    X ≤ Q ⊔ centralizerBar P L := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hHfin : Finite (↥L ⧸ O2sub L) :=
    Finite.of_surjective (QuotientGroup.mk' (O2sub L)) (QuotientGroup.mk'_surjective (O2sub L))
  haveI hAfin : Finite (MulAut (↥L ⧸ O2sub L)) :=
    Finite.of_injective
      (fun f : MulAut (↥L ⧸ O2sub L) => (f : (↥L ⧸ O2sub L) → (↥L ⧸ O2sub L)))
      DFunLike.coe_injective
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hPN : P ≤ N := hPNL
  have hQN : Q ≤ N := hQL.trans hLN
  let φ : N →* MulAut (↥L ⧸ O2sub L) := barAction L
  let P' : Subgroup N := P.subgroupOf N
  let L' : Subgroup N := L.subgroupOf N
  let Q' : Subgroup N := Q.subgroupOf N
  let B : Subgroup (MulAut (↥L ⧸ O2sub L)) := P'.map φ
  let I : Subgroup (MulAut (↥L ⧸ O2sub L)) := L'.map φ
  let J : Subgroup (MulAut (↥L ⧸ O2sub L)) := Q'.map φ
  have hQ'L' : Q' ≤ L' := Subgroup.subgroupOf_mono N hQL
  have hB3 : IsPGroup 3 B := (hP3.comap_subtype (K := N)).map φ
  have hQNm : IsSylowOf 3 Q' L' := by
    rw [← isSylowOf_map_subtype_iff N, Subgroup.map_subgroupOf_eq_of_le hQN,
      Subgroup.map_subgroupOf_eq_of_le hLN]
    exact hQ
  have hJ : IsSylowOf 3 J I := by
    let φL : L' →* MulAut (↥L ⧸ O2sub L) := φ.comp L'.subtype
    have htop : (⊤ : Subgroup L').map L'.subtype = L' := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
    have hrange : φL.range = I := by
      dsimp only [φL, I]
      rw [MonoidHom.range_eq_map, ← Subgroup.map_map, htop]
    have hJeq : (Q'.subgroupOf L').map φL = J := by
      dsimp only [J, Q', φL]
      ext a
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact Subgroup.mem_map.mpr ⟨(x : N), hx, rfl⟩
      · rintro ⟨n, hn, rfl⟩
        exact Subgroup.mem_map.mpr
          ⟨⟨n, hQ'L' hn⟩, Subgroup.mem_subgroupOf.mpr hn, rfl⟩
    obtain ⟨S, hS⟩ := hQNm.exists_sylow_eq_subgroupOf
    have hSyl' : IsSylowOf 3 ((Q'.subgroupOf L').map φL) φL.range := by
      refine ⟨S.mapSurjective (f := φL.rangeRestrict)
        (MonoidHom.rangeRestrict_surjective φL), ?_⟩
      rw [Sylow.coe_mapSurjective, Subgroup.map_map,
        MonoidHom.subtype_comp_rangeRestrict, hS]
    rw [← hrange, ← hJeq]
    exact hSyl'
  have hBI3 : IsPGroup 3 (B ⊓ I : Subgroup (MulAut (↥L ⧸ O2sub L))) :=
    hB3.to_inf_left (K := I)
  have hJI : J ≤ B ⊓ I := by
    refine le_inf ?_ hJ.le
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono N hQP)
  have hEq : B ⊓ I = J := hJ.eq_of_le hJI inf_le_right hBI3
  intro x hx
  have hxP : x ∈ P := hX hx
  have hxN : x ∈ N := hPN hxP
  obtain ⟨l, hlL, hinner⟩ := hInner x hx
  have hlN : l ∈ N := hLN hlL
  have hact : φ ⟨x, hxN⟩ = φ ⟨l, hlN⟩ := by
    dsimp only [φ]
    exact barAction_eq_of_inner hxN hlL hinner
  have hxB : φ ⟨x, hxN⟩ ∈ B := by
    dsimp only [B, P']
    exact Subgroup.mem_map_of_mem φ hxP
  have hxI : φ ⟨x, hxN⟩ ∈ I := by
    rw [hact]
    dsimp only [I, L']
    exact Subgroup.mem_map_of_mem φ hlL
  have hxJ : φ ⟨x, hxN⟩ ∈ J := by
    rw [← hEq]
    exact ⟨hxB, hxI⟩
  dsimp only [J, Q'] at hxJ
  rw [Subgroup.mem_map] at hxJ
  obtain ⟨qN, hqN, hqeq⟩ := hxJ
  let q : G := (qN : G)
  have hqQ : q ∈ Q := hqN
  have hqP : q ∈ P := hQP hqQ
  have hxqP : x * q⁻¹ ∈ P := P.mul_mem hxP (P.inv_mem hqP)
  have hxqN : x * q⁻¹ ∈ N := hPN hxqP
  have hlam1 : φ ⟨x * q⁻¹, hxqN⟩ = 1 := by
    have h1 : (⟨x * q⁻¹, hxqN⟩ : N) = ⟨x, hxN⟩ * qN⁻¹ := by
      ext
      rfl
    rw [h1, map_mul, map_inv, hqeq]
    simp
  have hcent : x * q⁻¹ ∈ centralizerBar P L := by
    rw [mem_centralizerBar_iff]
    refine ⟨hxqP, ?_⟩
    intro y hy
    exact (barAction_eq_one_iff L ⟨x * q⁻¹, hxqN⟩).mp hlam1 y hy
  have hmem : (x * q⁻¹) * q ∈ centralizerBar P L ⊔ Q :=
    Subgroup.mul_mem_sup hcent hqQ
  rw [sup_comm]
  rw [show x = (x * q⁻¹) * q by group]
  exact hmem

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
