
module

public import CFSG.Monster.B.TwoA.Base.GeomResBase

public import CFSG.Monster.B.TwoA.Base.GeomObj
public import CFSG.Monster.B.TwoA.Base.PetersenC
public import CFSG.Monster.B.Cbar.Simple

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B Module

attribute [local instance] parAction

theorem flag_eq_smul_std
    {F : Set ParGeom} (hF : IsParFlag F) :
    ∃ g : Shat, F = (g • ·) '' stdSub (parType '' F) := by
  obtain ⟨g, hg, hFg⟩ := exists_conj_std_of_flag hF
  refine ⟨⟨g, hg⟩, Set.eq_of_subset_of_subset (fun x hx => ?_) ?_⟩
  · refine ⟨stdObj (parType x) (parType_bounds x).1 (parType_bounds x).2, ⟨rfl, x, hx, rfl⟩, ?_⟩
    exact obj_ext rfl (by rw [hFg x hx]; rfl)
  · rintro _ ⟨y, ⟨hy, x, hx, hxy⟩, rfl⟩
    have e : (⟨g, hg⟩ : Shat) • y = x := obj_ext (by rw [parType_smul, hxy]) (by
      rw [hFg x hx]
      change conjSub g y.1.2 = conjSub g (Echain (parType x))
      rw [show y.1.2 = Echain (parType y) from hy, hxy])
    show (⟨g, hg⟩ : Shat) • y ∈ F
    rw [e]
    exact hx

theorem parInc_of_res_between
    {F : Set ParGeom} {j m k : ℕ} (hjm : j < m) (hmk : m < k)
    (hm : m ∈ parType '' F) {x y : ParGeom} (hx : x ∈ parRes F) (hy : y ∈ parRes F)
    (hxj : parType x = j) (hyk : parType y = k) : parInc x y := by
  obtain ⟨z, hz, hzm⟩ := hm
  have hxz : x.1.2 ≤ z.1.2 := le_of_parInc (hx.2 z hz) (by omega)
  have hzy : z.1.2 ≤ y.1.2 := le_of_parInc (parInc_symm (hy.2 z hz)) (by omega)
  exact (parInc_iff_of_ne (by omega)).2 (.inl (hxz.trans hzy))

theorem exists_res_of_type
    {F : Set ParGeom} (hF : IsParFlag F) {j : ℕ} (hj1 : 1 ≤ j)
    (hj5 : j ≤ 5) (hj : j ∉ parType '' F) : ∃ x ∈ parRes F, parType x = j := by
  obtain ⟨C, hFC, hC, hCt⟩ := exists_chamber_of_flag hF
  obtain ⟨x, hx, hxj⟩ : j ∈ parType '' C := by rw [hCt]; exact ⟨hj1, hj5⟩
  exact ⟨x, ⟨by rw [hxj]; exact hj, fun y hy => hC x hx y (hFC hy)⟩, hxj⟩

theorem stdSub_123_res_iff
    (x : ParGeom) :
    x ∈ parRes (stdSub {1, 2, 3}) ↔ (parType x = 4 ∨ parType x = 5) ∧ E3 ≤ x.1.2 := by
  have hJ : ({1, 2, 3} : Set ℕ) ⊆ Set.Icc 1 5 := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩
  constructor
  · rintro ⟨hxt, hinc⟩
    rw [parType_stdSub _ hJ] at hxt
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hxt
    have hb := parType_bounds x
    have h45 : parType x = 4 ∨ parType x = 5 := by omega
    refine ⟨h45, ?_⟩
    have h3 := hinc (stdObj 3 (by norm_num) (by norm_num))
      ⟨stdObj_mem 3 _ _, .inr (.inr rfl)⟩
    exact le_of_parInc (parInc_symm h3) (by change 3 ≤ parType x; omega)
  · rintro ⟨h45, h3⟩
    refine ⟨?_, fun y hy => ?_⟩
    · rw [parType_stdSub _ hJ]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      omega
    · obtain ⟨hy1, hyJ⟩ := hy
      have hyt : parType y = 1 ∨ parType y = 2 ∨ parType y = 3 := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hyJ
      refine (parInc_iff_of_ne (by omega)).2 (.inr ?_)
      have hyE : y.1.2 = Echain (parType y) := hy1
      rw [hyE]
      exact (Echain_mono (parType_bounds y).1 (by omega : parType y ≤ 3) (by norm_num)).trans h3

@[expose] def res4Equiv :
    {x : ParGeom // x ∈ parRes (stdSub {1, 2, 3}) ∧ parType x = 4} ≃ X4 where
  toFun x := ⟨x.1.1.2, ⟨by
      obtain ⟨-, -, g, hg, hxg⟩ := x.1.2
      refine ⟨g, hg, ?_⟩
      change x.1.1.2 = conjSub g (Echain (parType x.1)) at hxg
      rw [hxg, x.2.2]
      rfl, ((stdSub_123_res_iff x.1).1 x.2.1).2⟩⟩
  invFun F := ⟨⟨(4, F.1), by norm_num, by norm_num, by
      obtain ⟨⟨g, hg, hFg⟩, -⟩ := F.2
      exact ⟨g, hg, hFg⟩⟩, (stdSub_123_res_iff _).2 ⟨.inl rfl, F.2.2⟩, rfl⟩
  left_inv x := Subtype.ext (obj_ext x.2.2.symm rfl)
  right_inv _ := rfl

@[expose] def res5Equiv :
    {x : ParGeom // x ∈ parRes (stdSub {1, 2, 3}) ∧ parType x = 5} ≃ X5 where
  toFun x := ⟨x.1.1.2, ⟨by
      obtain ⟨-, -, g, hg, hxg⟩ := x.1.2
      refine ⟨g, hg, ?_⟩
      change x.1.1.2 = conjSub g (Echain (parType x.1)) at hxg
      rw [hxg, x.2.2]
      rfl, ((stdSub_123_res_iff x.1).1 x.2.1).2⟩⟩
  invFun F := ⟨⟨(5, F.1), by norm_num, by norm_num, by
      obtain ⟨⟨g, hg, hFg⟩, -⟩ := F.2
      exact ⟨g, hg, hFg⟩⟩, (stdSub_123_res_iff _).2 ⟨.inr rfl, F.2.2⟩, rfl⟩
  left_inv x := Subtype.ext (obj_ext x.2.2.symm rfl)
  right_inv _ := rfl

theorem exists_petersen_res
    {F : Set ParGeom} (hF : IsParFlag F)
    (ht : parType '' F = {1, 2, 3}) :
    ∃ (φ : {x : ParGeom // x ∈ parRes F ∧ parType x = 5} ≃ PetVert)
      (χ : {x : ParGeom // x ∈ parRes F ∧ parType x = 4} ≃ PetEdge),
      ∀ a b, a.1.1.2 ≤ b.1.1.2 ↔ φ b ∈ (χ a).1 := by
  obtain ⟨g, hg⟩ := flag_eq_smul_std hF
  rw [ht] at hg
  subst hg
  refine ⟨(resTransport g _ 5).symm.trans (res5Equiv.trans vertEquiv),
    (resTransport g _ 4).symm.trans (res4Equiv.trans edgeEquiv), fun a b => ?_⟩
  have h := le_iff_mem_edge (res4Equiv ((resTransport g _ 4).symm a))
    (res5Equiv ((resTransport g _ 5).symm b))
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, ← h]
  change a.1.1.2 ≤ b.1.1.2 ↔ conjSub ((g⁻¹ : Shat) : Dfull) a.1.1.2 ≤
    conjSub ((g⁻¹ : Shat) : Dfull) b.1.1.2
  rw [conjSub_le_conjSub_iff]

theorem stabilizer_stdObj
    (i : ℕ) (h1 : 1 ≤ i) (h5 : i ≤ 5) :
    (MulAction.stabilizer Shat (stdObj i h1 h5)).map Shat.subtype = Kchain i := by
  ext d
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : g • stdObj i h1 h5 = stdObj i h1 h5 := hg
    have h := congrArg (fun x : ParGeom => x.1.2) hg'
    exact conjSub_eq_self_iff.1 h
  · intro hd
    refine ⟨⟨d, Kchain_le_Shat i h1 h5 hd⟩, ?_, rfl⟩
    show (⟨d, Kchain_le_Shat i h1 h5 hd⟩ : Shat) • stdObj i h1 h5 = stdObj i h1 h5
    exact obj_ext rfl (conjSub_eq_self_iff.2 hd)

instance isSimpleGroup_Shat :
    IsSimpleGroup Shat :=
  have : IsSimpleGroup Cbar := short_centralizer_generated_quotient_simple.2.2.1
  (MonoidHom.ofInjective iotaD_injective).symm.isSimpleGroup

theorem parAction_faithful
    (g : Shat) (hg : ∀ x : ParGeom, g • x = x) : g = 1 := by
  set N := (MulAction.toPermHom Shat ParGeom).ker
  have hgN : g ∈ N := by
    rw [MonoidHom.mem_ker]
    exact Equiv.ext fun x => hg x
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · rw [h] at hgN
    exact hgN
  · exfalso
    have ht : (⟨tauhat, tauhat_mem_Shat⟩ : Shat) ∈ N := by rw [h]; trivial
    rw [MonoidHom.mem_ker] at ht
    have h1 := congrArg (fun x : ParGeom => x.1.2)
      (congrArg (fun p : Equiv.Perm ParGeom => p (stdObj 1 le_rfl (by norm_num))) ht)
    change conjSub tauhat (Subgroup.zpowers xhat) = Subgroup.zpowers xhat at h1
    have hJ : tauhat ∈ Jhat := by
      rw [← normalizer_zpowers_xhat]
      exact conjSub_eq_self_iff.1 h1
    rw [← centralizer_xhat, Subgroup.mem_centralizer_singleton_iff] at hJ
    apply xhat_ne_iotaD_ybar
    rw [← tauhat_conj_xhat, hJ, mul_inv_cancel_right]

end CFSG.Monster.B.TwoA
