module

public import CFSG.LocalAnalysis.WeakClosure81.SixFiveE
public import CFSG.RankThree.GF2n.QuotPair
import CFSG.LocalAnalysis.WeakClosure81.SixFourShape

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def imgK (M V : Subgroup G) (g : G)
    [((KOf M V g).subgroupOf (LOf V g)).Normal] (A : Subgroup G) :
    Subgroup (↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)) :=
  (A.subgroupOf (LOf V g)).map (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)))

section Bookkeeping

variable (M V : Subgroup G) (g : G) [((KOf M V g).subgroupOf (LOf V g)).Normal]

theorem mk_eq_one_iff_mem_K (y : ↥(LOf V g)) :
    QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y = 1 ↔ (y : G) ∈ KOf M V g := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem imgK_conj (u : ↥(LOf V g)) (A : Subgroup G) :
    CFSG.CGT.Timmesfeld75.conjSubgroup
        (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) u) (imgK M V g A) =
      imgK M V g (conjSubgroup A (u : G)⁻¹) := by
  rw [timmesfeld_conjSubgroup_eq, ← map_inv]
  unfold imgK
  rw [map_conjSubgroup_of_hom (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)))
    (A.subgroupOf (LOf V g)) u⁻¹, conjSubgroup_subgroupOf]
  rfl

theorem exists_lift_of_mem_imgK {A : Subgroup G}
    {x : ↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)} (hx : x ∈ imgK M V g A) (hx1 : x ≠ 1) :
    ∃ y : ↥(LOf V g), (y : G) ∈ A ∧ (y : G) ∉ KOf M V g ∧
      QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y = x := by
  unfold imgK at hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  refine ⟨y, (Subgroup.mem_subgroupOf).1 hy, ?_, hyx⟩
  intro hyK
  exact hx1 (by rw [← hyx, mk_eq_one_iff_mem_K M V g y]; exact hyK)

theorem imgK_isElemAbelian {A : Subgroup G} (hA : IsElemAbelian 2 A) :
    IsElemAbelian 2 (imgK M V g A) :=
  IsElemAbelian.map (hA.subgroupOf (LOf V g)) _

theorem imgK_sup :
    imgK M V g V ⊔ imgK M V g (conjSubgroup V g) = ⊤ := by
  unfold imgK
  rw [← Subgroup.map_sup]
  have hsup : (V.subgroupOf (LOf V g)) ⊔
      ((conjSubgroup V g).subgroupOf (LOf V g)) = ⊤ := by
    change (V.subgroupOf (V ⊔ conjSubgroup V g)) ⊔
      ((conjSubgroup V g).subgroupOf (V ⊔ conjSubgroup V g)) = ⊤
    rw [← Subgroup.subgroupOf_sup (le_sup_left : V ≤ V ⊔ conjSubgroup V g)
      (le_sup_right : conjSubgroup V g ≤ V ⊔ conjSubgroup V g)]
    exact Subgroup.subgroupOf_self _
  rw [hsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

end Bookkeeping

namespace Hyp65

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G} [((KOf M V g).subgroupOf (LOf V g)).Normal]

private theorem s65_SixFiveG_eq_of_comm (h : Hyp65 n M V₀ V g) {A A' : Subgroup G}
    (hA : A ∈ pairConjOf V g) (hA' : A' ∈ pairConjOf V g) {y y' : ↥(LOf V g)}
    (hy : (y : G) ∈ A) (hyK : (y : G) ∉ KOf M V g)
    (hy' : (y' : G) ∈ A') (hy'K : (y' : G) ∉ KOf M V g)
    (hcomm : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y *
        QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y' =
      QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y' *
        QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y) : A = A' := by
  have hyC : (y : G) ∉ COf M V₀ V g := by
    intro hyC
    exact hyK (Hyp65.inf_C_le_K h hA (Subgroup.mem_inf.mpr ⟨hy, hyC⟩))
  have hy'C : (y' : G) ∉ COf M V₀ V g := by
    intro hy'C
    exact hy'K (Hyp65.inf_C_le_K h hA' (Subgroup.mem_inf.mpr ⟨hy', hy'C⟩))
  have h1 : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) ⁅y, y'⁆ = 1 := by
    rw [map_commutatorElement]
    exact (commutatorElement_eq_one_iff_mul_comm).2 hcomm
  have hKmem : ((⁅y, y'⁆ : ↥(LOf V g)) : G) ∈ KOf M V g :=
    (mk_eq_one_iff_mem_K M V g ⁅y, y'⁆).1 h1
  have hcommG : ⁅(y : G), (y' : G)⁆ ∈ COf M V₀ V g := by
    have hmem := Hyp65.K_le_C h hKmem
    simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] using hmem
  exact Hyp65.eq_of_comm_mod_C h hA hA' hy hyC hy' hy'C hcommG

theorem imgK_V_ne_bot (h : Hyp65 n M V₀ V g) : imgK M V g V ≠ ⊥ := by
  intro hbot
  have hbot' : (V.subgroupOf (LOf V g)).map
      (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g))) = ⊥ := hbot
  have hle : V.subgroupOf (LOf V g) ≤ (KOf M V g).subgroupOf (LOf V g) := by
    have h1 : V.subgroupOf (LOf V g) ≤
        (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g))).ker :=
      (Subgroup.map_eq_bot_iff (V.subgroupOf (LOf V g))).1 hbot'
    rwa [QuotientGroup.ker_mk'] at h1
  have hVK : V ≤ KOf M V g := by
    intro v hv
    exact hle (show (⟨v, (le_sup_left : V ≤ LOf V g) hv⟩ : ↥(LOf V g)) ∈
      V.subgroupOf (LOf V g) from hv)
  have hVeq : V = UOf M V g := by
    rw [← Hyp65.V_inf_K h]
    exact le_antisymm (le_inf le_rfl hVK) inf_le_left
  exact h.not_V_le_conjM (by rw [hVeq]; exact inf_le_right)

theorem imgK_conjV_ne_bot (h : Hyp65 n M V₀ V g) : imgK M V g (conjSubgroup V g) ≠ ⊥ := by
  intro hbot
  have hbot' : ((conjSubgroup V g).subgroupOf (LOf V g)).map
      (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g))) = ⊥ := hbot
  have hle : (conjSubgroup V g).subgroupOf (LOf V g) ≤ (KOf M V g).subgroupOf (LOf V g) := by
    have h1 : (conjSubgroup V g).subgroupOf (LOf V g) ≤
        (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g))).ker :=
      (Subgroup.map_eq_bot_iff ((conjSubgroup V g).subgroupOf (LOf V g))).1 hbot'
    rwa [QuotientGroup.ker_mk'] at h1
  have hVgK : conjSubgroup V g ≤ KOf M V g := by
    intro v hv
    exact hle (show (⟨v, (le_sup_right : conjSubgroup V g ≤ LOf V g) hv⟩ : ↥(LOf V g)) ∈
      (conjSubgroup V g).subgroupOf (LOf V g) from hv)
  have hVeq : conjSubgroup V g = BOf M V g := by
    rw [← Hyp65.conjV_inf_K h]
    exact le_antisymm (le_inf le_rfl hVgK) inf_le_left
  exact h.not_conjV_le_M (by rw [hVeq]; exact inf_le_right)

theorem imgK_closed (h : Hyp65 n M V₀ V g) {A A' : Subgroup G} (hA : A ∈ pairConjOf V g)
    (hA' : A' ∈ pairConjOf V g)
    {x x' : ↥(LOf V g) ⧸ (KOf M V g).subgroupOf (LOf V g)}
    (hx : x ∈ imgK M V g A) (hx1 : x ≠ 1) (hx' : x' ∈ imgK M V g A') (hx'1 : x' ≠ 1)
    (hcomm : x * x' = x' * x) : imgK M V g A = imgK M V g A' := by
  obtain ⟨y, hyA, hyK, hyx⟩ := exists_lift_of_mem_imgK M V g hx hx1
  obtain ⟨y', hyA', hy'K, hy'x'⟩ := exists_lift_of_mem_imgK M V g hx' hx'1
  have hcomm' : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y *
      QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y' =
      QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y' *
      QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y := by
    rw [hyx, hy'x']
    exact hcomm
  rw [s65_SixFiveG_eq_of_comm h hA hA' hyA hyK hyA' hy'K hcomm']

omit [((KOf M V g).subgroupOf (LOf V g)).Normal] in
theorem not_le_K_of_mem_pairConjOf (h : Hyp65 n M V₀ V g) {A : Subgroup G}
    (hA : A ∈ pairConjOf V g) : ¬ A ≤ KOf M V g := by
  intro hAK
  obtain ⟨x, hxL, hx | hx⟩ := hA
  · have hKx : conjSubgroup (KOf M V g) x⁻¹ = KOf M V g :=
      conjSubgroup_eq_iff_mem_normalizer.2 (h.L_le_normalizer_K ((LOf V g).inv_mem hxL))
    have hVK : V ≤ KOf M V g := by
      have hmono := conjSubgroup_mono hAK x⁻¹
      rw [hx, conjSubgroup_conjSubgroup_inv, hKx] at hmono
      exact hmono
    have hVeq : V = UOf M V g := by
      rw [← Hyp65.V_inf_K h]
      exact le_antisymm (le_inf le_rfl hVK) inf_le_left
    exact h.not_V_le_conjM (by rw [hVeq]; exact inf_le_right)
  · have hKx : conjSubgroup (KOf M V g) x⁻¹ = KOf M V g :=
      conjSubgroup_eq_iff_mem_normalizer.2 (h.L_le_normalizer_K ((LOf V g).inv_mem hxL))
    have hVgK : conjSubgroup V g ≤ KOf M V g := by
      have hmono := conjSubgroup_mono hAK x⁻¹
      rw [hx, conjSubgroup_conjSubgroup_inv, hKx] at hmono
      exact hmono
    have hVeq : conjSubgroup V g = BOf M V g := by
      rw [← Hyp65.conjV_inf_K h]
      exact le_antisymm (le_inf le_rfl hVgK) inf_le_left
    exact h.not_conjV_le_M (by rw [hVeq]; exact inf_le_right)

theorem eq_of_imgK_eq (h : Hyp65 n M V₀ V g) {A A' : Subgroup G} (hA : A ∈ pairConjOf V g)
    (hA' : A' ∈ pairConjOf V g) (he : imgK M V g A = imgK M V g A') : A = A' := by
  have hnotle : ¬ A ≤ KOf M V g := not_le_K_of_mem_pairConjOf h hA
  rw [SetLike.not_le_iff_exists] at hnotle
  obtain ⟨a, haA, haK⟩ := hnotle
  have haL : a ∈ LOf V g := le_LOf_of_mem_pairConjOf hA haA
  let y : ↥(LOf V g) := ⟨a, haL⟩
  have hyK : (y : G) ∉ KOf M V g := haK
  have hy1 : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y ≠ 1 :=
    fun h1 => haK ((mk_eq_one_iff_mem_K M V g y).1 h1)
  have hmemA : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y ∈ imgK M V g A := by
    unfold imgK
    rw [Subgroup.mem_map]
    exact ⟨y, (Subgroup.mem_subgroupOf).2 haA, rfl⟩
  have hmemA' : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y ∈ imgK M V g A' := by
    rw [← he]
    exact hmemA
  obtain ⟨y', hy'A', hy'K, hy'π⟩ := exists_lift_of_mem_imgK M V g hmemA' hy1
  have hcomm : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y *
      QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y' =
      QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y' *
      QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) y := by
    rw [hy'π]
  exact s65_SixFiveG_eq_of_comm h hA hA' haA hyK hy'A' hy'K hcomm

theorem imgK_ne (h : Hyp65 n M V₀ V g) : imgK M V g V ≠ imgK M V g (conjSubgroup V g) := by
  intro he
  have hVeq : V = conjSubgroup V g :=
    eq_of_imgK_eq h (V_mem_pairConjOf V g) (conjV_mem_pairConjOf V g) he
  refine h.not_conjV_le_M ?_
  rw [← hVeq]
  exact h.le_M

private theorem s65_SixFiveG_pairConj {U : Subgroup (↥(LOf V g) ⧸
      (KOf M V g).subgroupOf (LOf V g))}
    (hU : U ∈ CFSG.RankThree.GF2n.pairConj (imgK M V g V)
      (imgK M V g (conjSubgroup V g))) :
    ∃ A ∈ pairConjOf V g, U = imgK M V g A := by
  obtain ⟨z, hz | hz⟩ := hU
  · obtain ⟨x, rfl⟩ :=
      QuotientGroup.mk'_surjective ((KOf M V g).subgroupOf (LOf V g)) z
    refine ⟨conjSubgroup V (x : G)⁻¹,
      ⟨(x : G)⁻¹, (LOf V g).inv_mem x.2, Or.inl rfl⟩, ?_⟩
    rw [hz, imgK_conj M V g x V]
  · obtain ⟨x, rfl⟩ :=
      QuotientGroup.mk'_surjective ((KOf M V g).subgroupOf (LOf V g)) z
    refine ⟨conjSubgroup (conjSubgroup V g) (x : G)⁻¹,
      ⟨(x : G)⁻¹, (LOf V g).inv_mem x.2, Or.inr rfl⟩, ?_⟩
    rw [hz, imgK_conj M V g x (conjSubgroup V g)]

theorem quotPair (h : Hyp65 n M V₀ V g) :
    CFSG.RankThree.GF2n.QuotPair (imgK M V g V) (imgK M V g (conjSubgroup V g)) := by
  refine ⟨imgK_isElemAbelian M V g h.elemAbelian,
    imgK_isElemAbelian M V g
      (h.isElemAbelian_of_mem_pairConjOf (conjV_mem_pairConjOf V g)),
    imgK_V_ne_bot h, imgK_conjV_ne_bot h, imgK_ne h, imgK_sup M V g, ?_⟩
  intro U hU W hW u hu hu1 v hv hv1 hcomm
  obtain ⟨A, hA, rfl⟩ := s65_SixFiveG_pairConj hU
  obtain ⟨A', hA', rfl⟩ := s65_SixFiveG_pairConj hW
  exact imgK_closed h hA hA' hu hu1 hv hv1 hcomm

theorem card_imgK (h : Hyp65 n M V₀ V g) :
    Nat.card (imgK M V g V) = (conjSubgroup M g).relIndex V := by
  let L := LOf V g
  let π : ↥L →* (↥L ⧸ ((KOf M V g).subgroupOf L)) :=
    QuotientGroup.mk' ((KOf M V g).subgroupOf L)
  let f : ↥V →* (↥L ⧸ ((KOf M V g).subgroupOf L)) :=
    π.comp (Subgroup.inclusion (le_sup_left : V ≤ L))
  have hrange : f.range = (V.subgroupOf L).map π := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map]
    congr 1
    rw [← MonoidHom.range_eq_map]
    exact Subgroup.inclusion_range (le_sup_left : V ≤ L)
  have hker : f.ker = (UOf M V g).subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk' ((KOf M V g).subgroupOf L)
      (Subgroup.inclusion (le_sup_left : V ≤ L) v) = 1 ↔ (v : G) ∈ UOf M V g
    rw [mk_eq_one_iff_mem_K M V g (Subgroup.inclusion (le_sup_left : V ≤ L) v),
      Subgroup.coe_inclusion, ← Hyp65.V_inf_K h]
    constructor
    · intro hvK
      exact ⟨v.2, hvK⟩
    · intro hv
      exact hv.2
  change Nat.card ((V.subgroupOf L).map π) = (conjSubgroup M g).relIndex V
  calc Nat.card ((V.subgroupOf L).map π) = Nat.card f.range := by rw [hrange]
    _ = (f.ker).index :=
        (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv).symm
    _ = ((UOf M V g).subgroupOf V).index := by rw [hker]
    _ = (UOf M V g).relIndex V := rfl
    _ = (conjSubgroup M g).relIndex V := by rw [UOf, Subgroup.inf_relIndex_left]

theorem mem_M_of_image_mem_normalizer (h : Hyp65 n M V₀ V g) {l : ↥(LOf V g)}
    (hl : QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) l ∈
      Subgroup.normalizer (imgK M V g V : Set (↥(LOf V g) ⧸
        (KOf M V g).subgroupOf (LOf V g)))) :
    (l : G) ∈ M := by
  have h1 : CFSG.CGT.Timmesfeld75.conjSubgroup
      (QuotientGroup.mk' ((KOf M V g).subgroupOf (LOf V g)) l) (imgK M V g V) =
      imgK M V g V :=
    CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff.2 hl
  rw [imgK_conj M V g l V] at h1
  have heq : conjSubgroup V (l : G)⁻¹ = V :=
    eq_of_imgK_eq h ⟨(l : G)⁻¹, (LOf V g).inv_mem l.2, Or.inl rfl⟩
      (V_mem_pairConjOf V g) h1
  have hinv : (l : G)⁻¹ ∈ normalizer (V : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.1 heq
  rw [h.normalizer_eq] at hinv
  simpa using inv_mem hinv

end Hyp65

end CFSG.LocalAnalysis.WeakClosure81
