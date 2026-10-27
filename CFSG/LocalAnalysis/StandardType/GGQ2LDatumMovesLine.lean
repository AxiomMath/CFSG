module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemmaH4
import CFSG.LocalAnalysis.StandardType.GGQ2MixedCentreRefl
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitLabelTwo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem gg2ldml_zpowers_subtype_iff {G : Type} [Group G] {Bs : Subgroup G} {y : G}
    (hy : y ∈ Bs) (b : ↥Bs) :
    (b : G) ∈ Subgroup.zpowers y ↔ b ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

private theorem gg2ldml_zpow_mem_span {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    {Bs : Subgroup G} {x : G} (hx : x ∈ Bs) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {b : ↥Bs} (hb : b ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs)) :
    ι (Additive.ofMul b) ∈
      Submodule.span (ZMod p) ({ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))} : Set V) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [← hk, ofMul_zpow, map_zsmul]
  exact Submodule.mem_span_singleton.mpr ⟨(k : ZMod p), Int.cast_smul_eq_zsmul (R := ZMod p) k _⟩

private theorem gg2ldml_model_span_iff {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {y : G} (hy : y ∈ Bs) (b : ↥Bs) :
    ι (Additive.ofMul b) ∈
        Submodule.span (ZMod p) {ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))} ↔
      b ∈ Subgroup.zpowers (⟨y, hy⟩ : ↥Bs) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    have h1 : c.val • ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) = ι (Additive.ofMul b) := by
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) c.val, ZMod.natCast_zmod_val]
      exact hc
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(c.val : ℤ), ?_⟩
    rw [zpow_natCast]
    apply Additive.ofMul.injective
    apply ι.injective
    rw [ofMul_pow, show ι (c.val • Additive.ofMul (⟨y, hy⟩ : ↥Bs)) =
        c.val • ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) from
      (ι.toAddMonoidHom).map_nsmul c.val (Additive.ofMul (⟨y, hy⟩ : ↥Bs))]
    exact h1
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    rw [← hk]
    have h1 : ι (Additive.ofMul ((⟨y, hy⟩ : ↥Bs) ^ k)) =
        k • ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) := by
      rw [ofMul_zpow]
      exact (ι.toAddMonoidHom).map_zsmul k (Additive.ofMul (⟨y, hy⟩ : ↥Bs))
    rw [h1, ← Int.cast_smul_eq_zsmul (R := ZMod p) k]
    exact Submodule.smul_mem _ (k : ZMod p) (Submodule.mem_span_singleton_self _)

theorem GGQ2LDatum.root_eq_zero_of_line {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hcard : 3 ≤ Fintype.card M.Λ) (v : M.V)
    (hv : ∀ i, M.root i v • M.coroot i ∈ Submodule.span (ZMod 3) {v}) : ∀ i, M.root i v = 0 := by
  by_contra h
  rw [not_forall] at h
  obtain ⟨i₀, hi₀⟩ := h
  have hcoroot_mem : ∀ i, M.root i v ≠ 0 → M.coroot i ∈ Submodule.span (ZMod 3) {v} := by
    intro i hi
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hv i)
    refine Submodule.mem_span_singleton.mpr ⟨(M.root i v)⁻¹ * c, ?_⟩
    rw [mul_smul, hc, smul_smul, inv_mul_cancel₀ hi, one_smul]
  have hclosed : ∀ a b, M.root a (M.coroot b) ≠ 0 → M.root b (M.coroot a) ≠ 0 →
      M.root a v ≠ 0 → M.root b v ≠ 0 := by
    intro a b _ hba ha hb
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hcoroot_mem a ha)
    exact hba (by rw [← hc, map_smul, hb, smul_zero])
  have hall : ∀ j, M.root j v ≠ 0 := by
    intro j
    have hpath := M.pairing_connected hcard i₀ j
    induction hpath with
    | refl => exact hi₀
    | tail _ hstep ih => exact hclosed _ _ hstep.1 hstep.2 ih
  obtain ⟨a, b, hab, hlab⟩ :=
    ggWeylMatrix_exists_label_two M.isWeyl (by rwa [Nat.card_eq_fintype_card])
  have hcartan : M.cartan a b = 0 := by
    rcases M.isCartan.2 a b hab with ⟨-, h, -⟩ | ⟨h3, -, -⟩ | ⟨h4, -, -, -⟩ | ⟨h6, -, -, -⟩
    · exact h
    · rw [h3] at hlab; omega
    · rw [h4] at hlab; omega
    · rw [h6] at hlab; omega
  have hzero : M.root a (M.coroot b) = 0 := by
    rw [M.pairing a b, hcartan]
    simp
  have hbS : M.root b v ≠ 0 := hall b
  obtain ⟨cb, hcb⟩ := Submodule.mem_span_singleton.mp (hcoroot_mem b hbS)
  have hcb0 : cb ≠ 0 := by
    intro hcb0'
    have h2 := GGQ2LDatum.root_coroot_two M b
    rw [← hcb, hcb0', zero_smul, map_zero] at h2
    exact absurd h2 (by decide : (0 : ZMod 3) ≠ 2)
  have hnonzero : M.root a (M.coroot b) ≠ 0 := by
    rw [← hcb, map_smul]
    intro hz
    exact hall a ((smul_eq_zero.mp hz).resolve_left hcb0)
  exact hnonzero hzero

theorem GGQ2LDatum.exists_simple_movesLine {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hcard : 3 ≤ Fintype.card M.Λ) {y : G} (hy : y ∈ Bs)
    (hyx : y ∉ Subgroup.zpowers x) : ∃ i, GGQ2MovesLine Bs y (M.simple i) := by
  by_contra h
  rw [not_exists] at h
  have hfix : ∀ (i : M.Λ) (b : ↥Bs), (b : G) ∈ Subgroup.zpowers y →
      ((M.simple i b : ↥Bs) : G) ∈ Subgroup.zpowers y := by
    intro i b hb
    by_contra hb'
    exact h i ⟨b, hb, hb'⟩
  let yB : ↥Bs := ⟨y, hy⟩
  let yV : M.V := M.model (Additive.ofMul yB)
  have hspan : ∀ i, ggLin (p := 3) M.model (M.simple i) yV ∈
      Submodule.span (ZMod 3) {yV} := by
    intro i
    have hmem : M.simple i yB ∈ Subgroup.zpowers yB :=
      (gg2ldml_zpowers_subtype_iff hy (M.simple i yB)).mp
        (hfix i yB (Subgroup.mem_zpowers y))
    have h := gg2ldml_zpow_mem_span (p := 3) hy M.model hmem
    rw [ggLin_apply_ofMul]
    exact h
  have hroot : ∀ i, M.root i yV = 0 :=
    GGQ2LDatum.root_eq_zero_of_line M hcard yV (fun i => by
      have h1 : yV - ggLin (p := 3) M.model (M.simple i) yV ∈
          Submodule.span (ZMod 3) {yV} :=
        Submodule.sub_mem _ (Submodule.mem_span_singleton_self yV) (hspan i)
      have h2 : yV - ggLin (p := 3) M.model (M.simple i) yV =
          M.root i yV • M.coroot i := by
        rw [M.simple_apply i]
        abel
      rwa [h2] at h1)
  have hyV : yV ∈ Submodule.span (ZMod 3) {M.xV} :=
    GGQ2LDatum.mem_span_xV_of_root M hroot
  have hyB : yB ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) :=
    (gg2ldml_model_span_iff (p := 3) M.model M.hx yB).mp (by
      simpa [GGQ2LDatum.xV, yV] using hyV)
  have hyx' : y ∈ Subgroup.zpowers x := by
    have h := (gg2ldml_zpowers_subtype_iff (y := x) M.hx yB).mpr hyB
    simpa [yB] using h
  exact hyx hyx'

end CFSG.StandardType

end
