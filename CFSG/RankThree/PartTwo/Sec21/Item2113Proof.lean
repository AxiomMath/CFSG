module

public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofStatements
public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofLinear
public import CFSG.RankThree.PartTwo.Sec21.Item2113ProofList

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2113Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

variable {G : Type} [Group G]

abbrev commGroupOf {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A) : CommGroup A :=
  { (inferInstance : Group A) with mul_comm := fun x y => hA.1.is_comm.comm x y }

theorem map_subtype_zpowers {A : Subgroup G} (x : A) :
    (Subgroup.zpowers x).map A.subtype = Subgroup.zpowers (x : G) :=
  MonoidHom.map_zpowers A.subtype x

theorem map_subtype_closure_pair {A : Subgroup G} (x y : A) :
    (Subgroup.closure ({x, y} : Set A)).map A.subtype =
      Subgroup.closure ({(x : G), (y : G)} : Set G) := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

theorem map_eq_iff_mem_normalizer [Finite G] {A : Subgroup G}
    (w : Subgroup.normalizer (A : Set G)) (Y : Subgroup A) :
    Y.map (A.normalizerMonoidHom w).toMonoidHom = Y ↔
      (w : G) ∈ Subgroup.normalizer ((Y.map A.subtype : Subgroup G) : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(A.normalizerMonoidHom w) y, h ▸ Subgroup.mem_map_of_mem _ hy, ?_⟩
      simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
    · rintro ⟨y', hy', hxy⟩
      have hxA : x ∈ A := by
        have hw' : (w : G)⁻¹ ∈ Subgroup.normalizer (A : Set G) := inv_mem w.2
        have h' := (Subgroup.mem_normalizer_iff.mp hw' (y' : G)).mp y'.2
        have hxy' : (y' : G) = (w : G) * x * (w : G)⁻¹ := hxy
        rw [hxy'] at h'
        simpa [mul_assoc] using h'
      refine ⟨⟨x, hxA⟩, ?_, rfl⟩
      have hσ : (A.normalizerMonoidHom w) ⟨x, hxA⟩ = y' :=
        Subtype.ext (by rw [Subgroup.normalizerMonoidHom_apply_apply_coe]; exact hxy.symm)
      have h' := inv_apply_mem_of_map_eq h hy'
      rwa [← hσ, MulAut.inv_apply_self] at h'
  · intro h
    apply map_eq_of_le
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨y', hy', hy'eq⟩ := (Subgroup.mem_normalizer_iff.mp h (y : G)).mp ⟨y, hy, rfl⟩
    have hσ : (A.normalizerMonoidHom w).toMonoidHom y = y' :=
      Subtype.ext (by
        simp only [MulEquiv.coe_toMonoidHom, Subgroup.normalizerMonoidHom_apply_apply_coe]
        exact hy'eq.symm)
    rw [hσ]
    exact hy'

theorem normalizer_le_of_forall [Finite G] {A : Subgroup G} {Y : Subgroup A}
    (h : ∀ σ ∈ wStar A, Y.map σ.toMonoidHom = Y) :
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Y.map A.subtype : Subgroup G) : Set G) := fun w hw =>
  (map_eq_iff_mem_normalizer ⟨w, hw⟩ Y).mp (h _ ⟨⟨w, hw⟩, rfl⟩)

theorem transvection_data {A L : Subgroup G} {c d : G} (hcA : c ∈ A) (hdA : d ∈ A)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) {t : MulAut A} (htL : t ∈ starOf A L)
    (ht : IsTransvectionOn t) (htd : (commOf t).map A.subtype = Subgroup.zpowers d) :
    t ∈ wStar A ∧ t ⟨c, hcA⟩ = ⟨c, hcA⟩ ∧ t ⟨d, hdA⟩ = ⟨d, hdA⟩ ∧ t ≠ 1 ∧
      ∀ x, x⁻¹ * t x ∈ Subgroup.zpowers (⟨d, hdA⟩ : A) := by
  have hcomm : commOf t = Subgroup.zpowers (⟨d, hdA⟩ : A) := by
    apply Subgroup.map_injective A.subtype_injective
    rw [htd, map_subtype_zpowers]
  refine ⟨starOf_le_wStar A L htL, ?_, ?_, ?_, fun x => hcomm ▸ mem_commOf t x⟩
  · obtain ⟨x, hxL, rfl⟩ := htL
    apply Subtype.ext
    have hxc : (x : G) * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp
      (hLc (Subgroup.mem_subgroupOf.mp hxL))
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [hxc, mul_inv_cancel_right]
  · have hmem : (⟨d, hdA⟩ : A) ∈ commOf t := hcomm ▸ Subgroup.mem_zpowers _
    exact (mem_fixedSubgroupOf t _).mp (ht.2 hmem)
  · intro h1
    have h := ht.1
    rw [(commOf_eq_bot_iff t).mpr h1, Subgroup.card_bot] at h
    omega

theorem mem_of_isCentral218 {L : Subgroup G} {d : G} (h : IsCentral218 L d) : d ∈ L := by
  obtain ⟨S, ⟨Q, rfl⟩, hd⟩ := h
  obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hd
  obtain ⟨y, -, hy⟩ := Subgroup.mem_map.mp x.2
  show (x : G) ∈ L
  rw [← hy]
  exact y.2

section Normal

theorem data_of_choice [Finite G] (h211 : Item211) {A E U L : Subgroup G} {c d : G}
    (hpair : Sec21Pair G A E U c L) (hL : IsList218 L) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdcen : IsCentral218 L d) :
    Nat.card A = 27 ∧ c ≠ 1 ∧ ∃ hcA : c ∈ A,
      (⟨d, hdA⟩ : A) ∉ Subgroup.zpowers (⟨c, hcA⟩ : A) := by
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAe := hpair.mem_S.1.1
  refine ⟨by rw [card_eq_of_isList218 h211 hpair hL]; norm_num, hc1, hcA, ?_⟩
  intro h
  have hdc : d ∈ Subgroup.zpowers c := by
    have h' := Subgroup.mem_map_of_mem A.subtype h
    rwa [map_subtype_zpowers] at h'
  have hcd : c ∈ Subgroup.zpowers d := mem_zpowers_of_mem_zpowers (hAe.2 c hcA) hd1 hdc
  exact not_mem_of_isList218 hpair hL
    ((Subgroup.zpowers_le.mpr (mem_of_isCentral218 hdcen)) hcd)

end Normal

end CFSG.RankThree.PartTwo.Sec21.Item2113Proof
