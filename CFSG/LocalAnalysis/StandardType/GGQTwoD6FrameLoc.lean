module

public import CFSG.LocalAnalysis.StandardType.GGQTwoD6Frame

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace QTwoD6

open CFSG.StandardType.QTwoLin

private lemma ggQ2d6l_fix_eq (v : V7) (h : ∀ j : Fin 6, j ≠ 4 → avec j v = 0) :
    v = v 0 • e0 + v 1 • wb := by
  revert v
  decide +kernel

theorem ggQ2_d6_fix_J6 (v : V7) (hv : ∀ j : Fin 6, j ≠ 4 → simpleD6 j v = v) :
    v ∈ Dplane := by
  have hvec_ne : ∀ j : Fin 6, hvec j ≠ 0 := by
    intro j hj
    have := congrFun hj j.succ
    simp [hvec] at this
  have h_avec : ∀ j : Fin 6, j ≠ 4 → avec j v = 0 := by
    intro j hj
    have hvj := hv j hj
    rw [simpleD6, Module.reflection_apply] at hvj
    have hzero : avec j v • hvec j = 0 := sub_eq_self.mp hvj
    have hcoord := congrFun hzero j.succ
    simpa [hvec] using hcoord
  rw [ggQ2d6l_fix_eq v h_avec, Dplane]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

theorem ggQ2_d6_ell_mem_Dplane {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {y : G} {K : Subgroup G}
    {N : GGQ2NbrDatum 3 Bs K} {b : N.Λ} {hy : y ∈ Bs} (hJ : ggAutomizer J Bs =
      Subgroup.closure (N.simple '' {k | k ≠ b})) (Fr : GGQ2D6Frame N b hy) (hx : x ∈ Bs) :
    ggEll N Fr.F hx ∈ Dplane := by
  have hpre : LargeEvenStdSubPre 3 B x L D J := hS.1.1.2.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hDeq : D = B ⊓ Subgroup.centralizer (J : Set G) := hpre.2.2.2.2.2.2
  have hxCent : x ∈ Subgroup.centralizer (J : Set G) := by
    have h := hxD
    rw [hDeq, Subgroup.mem_inf] at h
    exact h.2
  have hcomm : ∀ g ∈ J, g * x * g⁻¹ = x := by
    intro g hgJ
    have hg := Subgroup.mem_centralizer_iff.mp hxCent g hgJ
    rw [hg]
    group
  refine ggQ2_d6_fix_J6 (ggEll N Fr.F hx) fun j hj => ?_
  have hmemaut : N.simple (Fr.e j) ∈ ggAutomizer J Bs := by
    rw [hJ]
    refine Subgroup.subset_closure ⟨Fr.e j, ?_, rfl⟩
    intro hjb
    exact hj (Fr.e.injective (hjb.trans Fr.b_eq))
  obtain ⟨g, hgJ, _hgnorm, hgφ⟩ := mem_ggAutomizer_iff.mp hmemaut
  have hfixφ : N.simple (Fr.e j) ⟨x, hx⟩ = ⟨x, hx⟩ := by
    apply Subtype.ext
    rw [hgφ ⟨x, hx⟩]
    exact hcomm g hgJ
  have hmodelfix : ggLin (p := 3) N.model (N.simple (Fr.e j))
      (N.model (Additive.ofMul ⟨x, hx⟩)) = N.model (Additive.ofMul ⟨x, hx⟩) :=
    (ggLin_fix_iff N.model (N.simple (Fr.e j)) ⟨x, hx⟩).mp hfixφ
  have hcoord : ggCoord N Fr.F (N.simple (Fr.e j)) (ggEll N Fr.F hx) = ggEll N Fr.F hx := by
    rw [ggEll, ggQ2_d6_coord_apply, Fr.F.symm_apply_apply, hmodelfix]
  rw [← ggQ2_d6_coord_simple Fr j]
  exact hcoord

theorem ggQ2_d6_ell_not_mem {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {y : G} {K : Subgroup G}
    {N : GGQ2NbrDatum 3 Bs K} {b : N.Λ} {hy : y ∈ Bs} (hnb : GGNbr 3 B x D J y K)
    (Fr : GGQ2D6Frame N b hy) (hx : x ∈ Bs) :
    ggEll N Fr.F hx ∉ Submodule.span (ZMod 3) {e0} := by
  intro hmem
  have hpre : LargeEvenStdSubPre 3 B x L D J := hS.1.1.2.2.1
  have hcardD : Nat.card D = 3 ^ 2 := hpre.2.2.1
  have hBs : IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
  have hDclos : D = Subgroup.closure {x, y} := hnb.2.1
  have hmemF : Fr.F (N.model (Additive.ofMul ⟨x, hx⟩)) ∈
      Submodule.span (ZMod 3) {e0} := by
    simpa [ggEll] using hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmemF
  rw [← Fr.F_y] at hc
  have hc2 : c • N.model (Additive.ofMul ⟨y, hy⟩) =
      N.model (Additive.ofMul ⟨x, hx⟩) := by
    apply Fr.F.injective
    rw [map_smul]
    exact hc
  have hns : ∀ n : ℕ, N.model (n • Additive.ofMul ⟨y, hy⟩) =
      n • N.model (Additive.ofMul ⟨y, hy⟩) :=
    fun n => (N.model.toAddMonoidHom).map_nsmul n _
  have hc3 := hc2
  rw [← ZMod.natCast_zmod_val c] at hc3
  rw [Nat.cast_smul_eq_nsmul] at hc3
  have hmain : N.model (Additive.ofMul ((⟨y, hy⟩ : ↥Bs) ^ c.val)) =
      N.model (Additive.ofMul ⟨x, hx⟩) := by
    rw [ofMul_pow, hns, hc3]
  have hxy : (⟨y, hy⟩ : ↥Bs) ^ c.val = ⟨x, hx⟩ :=
    Additive.ofMul.injective (N.model.injective hmain)
  have hxy' : y ^ c.val = x := by
    have := congrArg Subtype.val hxy
    simpa using this
  have hxmem : x ∈ Subgroup.zpowers y :=
    Subgroup.mem_zpowers_iff.mpr ⟨(c.val : ℤ), by rw [zpow_natCast, hxy']⟩
  have hDle : D ≤ Subgroup.zpowers y := by
    rw [hDclos]
    refine (Subgroup.closure_le (Subgroup.zpowers y)).mpr ?_
    intro z hz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hxmem
    · exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
  have hcard_le : Nat.card D ≤ Nat.card (Subgroup.zpowers y) :=
    Nat.card_le_card_of_injective (fun d : D => (⟨(d : G), hDle d.2⟩ : Subgroup.zpowers y))
      (by
        intro a b h
        exact Subtype.ext (congrArg (fun t : Subgroup.zpowers y => (t : G)) h))
  have hy3 : y ^ 3 = 1 := hBs.2 y hy
  have horder : orderOf y ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hy3
  have hle3 : orderOf y ≤ 3 := Nat.le_of_dvd (by norm_num) horder
  have hcard9 : Nat.card D = 9 := by rw [hcardD]; norm_num
  have h93 : 9 ≤ 3 := by
    calc 9 = Nat.card D := hcard9.symm
      _ ≤ Nat.card (Subgroup.zpowers y) := hcard_le
      _ = orderOf y := Nat.card_zpowers y
      _ ≤ 3 := hle3
  omega

end QTwoD6

end CFSG.StandardType

end

