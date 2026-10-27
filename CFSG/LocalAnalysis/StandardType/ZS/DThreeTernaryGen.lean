module

public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.Fischer.Classification.PartIII.Beta.Forms
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTernaryPair
import CFSG.Fischer.Classification.Orthogonal3.Local
import CFSG.Fischer.Classification.PartIII.U.SixForms
public import CFSG.Fischer.Pairs
public import CFSG.Open.Defs
import CFSG.Fischer.Uniq.CompTau
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic

public section

namespace CFSG.StandardType.ZS

open CFSG.Fischer.Classification

local instance (priority := high) zgnTernaryGenAddCommGroup : AddCommGroup (ZMod 3) :=
  Ring.toAddCommGroup

theorem diagF3_apply_single {m : ℕ} (δ : ZMod 3) (x : Fin m → ZMod 3) (i : Fin m) :
    diagF3 m δ x (Pi.single i 1) = diagF3Entry m δ i * x i := by
  rw [diagF3_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, mul_one]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem diagF3Entry_two_of_ne_last {n : ℕ} {i : Fin (n + 1)}
    (hi : i ≠ Fin.last n) : diagF3Entry (n + 1) 2 i = 1 := by
  rw [diagF3Entry, if_neg]
  intro h
  have hlast : (Fin.last n : ℕ) = n := rfl
  exact hi (Fin.ext (by omega))

private theorem zgn_diagF3Entry_castSucc (n : ℕ) (i : Fin n) :
    diagF3Entry (n + 1) 2 i.castSucc = 1 := by
  rw [diagF3Entry, if_neg]
  have hval : (i.castSucc : ℕ) = i := rfl
  omega

theorem diagF3Entry_two_last (n : ℕ) : diagF3Entry (n + 1) 2 (Fin.last n) = 2 := by
  simp [diagF3Entry]

private theorem zgn_diagF3_apply_last (n : ℕ) (z : Fin (n + 1) → ZMod 3) :
    diagF3 (n + 1) 2 z (Pi.single (Fin.last n) 1) = 2 * z (Fin.last n) := by
  rw [diagF3_apply_single, diagF3Entry_two_last]

private noncomputable def zgn_lastEquiv (n : ℕ) :
    F3.perpOne (diagF3 (n + 1) 2) (Pi.single (Fin.last n) 1) ≃ₗ[ZMod 3]
      (Fin n → ZMod 3) where
  toFun z := Fin.init (z : Fin (n + 1) → ZMod 3)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨Fin.snoc y 0, by
    rw [F3.mem_perpOne, zgn_diagF3_apply_last, Fin.snoc_last, mul_zero]⟩
  left_inv z := Subtype.ext (by
    change Fin.snoc (Fin.init (z : Fin (n + 1) → ZMod 3)) 0 = (z : Fin (n + 1) → ZMod 3)
    have hz : (z : Fin (n + 1) → ZMod 3) (Fin.last n) = 0 := by
      have h := F3.mem_perpOne.1 z.2
      rw [zgn_diagF3_apply_last] at h
      exact (mul_eq_zero.1 h).resolve_left (by decide)
    funext i
    induction i using Fin.lastCases with
    | last => rw [Fin.snoc_last]; exact hz.symm
    | cast j => rw [Fin.snoc_castSucc]; rfl)
  right_inv y := by
    funext i
    change (Fin.snoc y (0 : ZMod 3) : Fin (n + 1) → ZMod 3) i.castSucc = y i
    rw [Fin.snoc_castSucc]

private theorem zgn_diagF3_restrict (n : ℕ) (u v : Fin n → ZMod 3) :
    diagF3 (n + 1) 2 (Fin.snoc u 0) (Fin.snoc v 0) = diagF3 n 1 u v := by
  rw [diagF3_apply, diagF3_apply, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, zgn_diagF3Entry_castSucc, diagF3Entry_two_last,
    mul_zero, add_zero]
  simp [diagF3Entry]

private theorem zgn_exists_coord {n : ℕ} {x : Fin (n + 1) → ZMod 3}
    (hx : diagF3 (n + 1) 2 x x = 1) (hxl : x (Fin.last n) = 1) :
    ∃ k : Fin (n + 1), k ≠ Fin.last n ∧
      (x - (Pi.single (Fin.last n) 1 : Fin (n + 1) → ZMod 3)) k ≠ 0 ∧
      diagF3 (n + 1) 2 (x - Pi.single (Fin.last n) 1) (x - Pi.single (Fin.last n) 1) = 2 := by
  have hf : IsF3Form (diagF3 (n + 1) 2) := isF3Form_diagF3 (by decide)
  have hen_norm : diagF3 (n + 1) 2 (Pi.single (Fin.last n) 1) (Pi.single (Fin.last n) 1) = 2 := by
    rw [zgn_diagF3_apply_last, Pi.single_eq_same]
    decide
  have hs_norm : diagF3 (n + 1) 2 (x - Pi.single (Fin.last n) 1)
      (x - Pi.single (Fin.last n) 1) = 2 := by
    rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.sub_right, hf.symm (Pi.single (Fin.last n) 1) x,
      zgn_diagF3_apply_last, hxl, hx, hen_norm]
    decide
  have hs_ne : x - Pi.single (Fin.last n) 1 ≠ 0 := by
    intro h
    rw [h, diagF3_apply] at hs_norm
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hs_norm
    exact absurd hs_norm (by decide)
  obtain ⟨k, hk⟩ : ∃ k : Fin (n + 1),
      (x - (Pi.single (Fin.last n) 1 : Fin (n + 1) → ZMod 3)) k ≠ 0 := by
    by_contra h
    exact hs_ne (funext fun i => by
      by_contra hi
      exact h ⟨i, hi⟩)
  have hklast : k ≠ Fin.last n := by
    intro h
    rw [h] at hk
    refine hk ?_
    rw [Pi.sub_apply, Pi.single_eq_same, hxl, sub_self]
  exact ⟨k, hklast, hk, hs_norm⟩

private theorem zgn_exists_decomposition {n : ℕ} {x : Fin (n + 1) → ZMod 3}
    (hx : diagF3 (n + 1) 2 x x = 1) (hxl : x (Fin.last n) = 1) :
    ∃ a b : Fin (n + 1) → ZMod 3, diagF3 (n + 1) 2 a a = 1 ∧ diagF3 (n + 1) 2 b b = 1 ∧
      diagF3 (n + 1) 2 a b = 0 ∧ a (Fin.last n) = 0 ∧ b (Fin.last n) = 0 ∧
      a + b + Pi.single (Fin.last n) 1 = x := by
  have hf : IsF3Form (diagF3 (n + 1) 2) := isF3Form_diagF3 (by decide)
  obtain ⟨k, hklast, hk, hs_norm⟩ := zgn_exists_coord hx hxl
  set s : Fin (n + 1) → ZMod 3 := x - Pi.single (Fin.last n) 1 with hs
  have hs_norm' : diagF3 (n + 1) 2 s s = 2 := by
    rw [hs]
    exact hs_norm
  have hk' : s k ≠ 0 := by
    rw [hs]
    exact hk
  set a : Fin (n + 1) → ZMod 3 := s k • Pi.single k 1 with ha
  set b : Fin (n + 1) → ZMod 3 := s - a with hb
  have hsa : diagF3 (n + 1) 2 s (Pi.single k 1) = s k := by
    rw [diagF3_apply_single, diagF3Entry_two_of_ne_last hklast, one_mul]
  have haa : diagF3 (n + 1) 2 a a = 1 := by
    rw [ha, F3.norm_smul, LocalU.diagF3_single, if_pos rfl,
      diagF3Entry_two_of_ne_last hklast, F3.mul_self_of_ne_zero hk', mul_one]
  have has : diagF3 (n + 1) 2 a s = 1 := by
    rw [ha, LinearMap.BilinForm.smul_left, hf.symm (Pi.single k 1) s, hsa,
      F3.mul_self_of_ne_zero hk']
  have hsa' : diagF3 (n + 1) 2 s a = 1 := by
    rw [ha, LinearMap.BilinForm.smul_right, hsa, F3.mul_self_of_ne_zero hk']
  have hab : diagF3 (n + 1) 2 a b = 0 := by
    rw [hb, LinearMap.BilinForm.sub_right, has, haa, sub_self]
  have hbb : diagF3 (n + 1) 2 b b = 1 := by
    rw [hb, sub_eq_add_neg, F3.norm_add hf s (-a), LinearMap.BilinForm.neg_right,
      LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right, neg_neg,
      hs_norm', hsa', haa]
    decide
  have hs_last : s (Fin.last n) = 0 := by
    rw [hs, Pi.sub_apply, Pi.single_eq_same, hxl, sub_self]
  have ha_last : a (Fin.last n) = 0 := by
    rw [ha, Pi.smul_apply, Pi.single_eq_of_ne hklast.symm, smul_zero]
  have hb_last : b (Fin.last n) = 0 := by
    rw [hb, Pi.sub_apply, ha_last, sub_zero]
    exact hs_last
  have hxab : a + b + Pi.single (Fin.last n) 1 = x := by
    have hab' : a + b = s := by
      rw [hb]
      abel
    rw [hab', hs]
    abel
  exact ⟨a, b, haa, hbb, hab, ha_last, hb_last, hxab⟩

private theorem zgn_std_pair {n : ℕ} (hn : 5 ≤ n) :
    (Pi.single 0 1 : Fin (n + 1) → ZMod 3) ∈
        F3.perpOne (diagF3 (n + 1) 2) (Pi.single (Fin.last n) 1) ∧
      (Pi.single 1 1 : Fin (n + 1) → ZMod 3) ∈
        F3.perpOne (diagF3 (n + 1) 2) (Pi.single (Fin.last n) 1) ∧
      diagF3 (n + 1) 2 (Pi.single 0 1) (Pi.single 0 1) = 1 ∧
      diagF3 (n + 1) 2 (Pi.single 1 1) (Pi.single 1 1) = 1 ∧
      diagF3 (n + 1) 2 (Pi.single 0 1) (Pi.single 1 1) = 0 := by
  have h0last : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have h1last : (1 : Fin (n + 1)) ≠ Fin.last n := by
    have hv : (1 : Fin (n + 1)).val = 1 := by
      simp
      omega
    intro h
    have := congrArg Fin.val h
    rw [hv, Fin.val_last] at this
    omega
  have h01 : (0 : Fin (n + 1)) ≠ 1 := by
    simp
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [F3.mem_perpOne, zgn_diagF3_apply_last, Pi.single_eq_of_ne h0last.symm, mul_zero]
  · rw [F3.mem_perpOne, zgn_diagF3_apply_last, Pi.single_eq_of_ne h1last.symm, mul_zero]
  · rw [LocalU.diagF3_single, if_pos rfl, diagF3Entry_two_of_ne_last h0last]
  · rw [LocalU.diagF3_single, if_pos rfl, diagF3Entry_two_of_ne_last h1last]
  · rw [LocalU.diagF3_single, if_neg h01]

private theorem zgn_lastEquiv_form (n : ℕ)
    (u v : F3.perpOne (diagF3 (n + 1) 2) (Pi.single (Fin.last n) 1)) :
    diagF3 n 1 (zgn_lastEquiv n u) (zgn_lastEquiv n v) =
      diagF3 (n + 1) 2 (u : Fin (n + 1) → ZMod 3) (v : Fin (n + 1) → ZMod 3) := by
  have hzu : (u : Fin (n + 1) → ZMod 3) = Fin.snoc (zgn_lastEquiv n u) 0 := by
    have h := F3.mem_perpOne.1 u.2
    rw [zgn_diagF3_apply_last] at h
    have hlast : (u : Fin (n + 1) → ZMod 3) (Fin.last n) = 0 :=
      (mul_eq_zero.1 h).resolve_left (by decide)
    rw [← hlast]
    exact (Fin.snoc_init_self _).symm
  have hzv : (v : Fin (n + 1) → ZMod 3) = Fin.snoc (zgn_lastEquiv n v) 0 := by
    have h := F3.mem_perpOne.1 v.2
    rw [zgn_diagF3_apply_last] at h
    have hlast : (v : Fin (n + 1) → ZMod 3) (Fin.last n) = 0 :=
      (mul_eq_zero.1 h).resolve_left (by decide)
    rw [← hlast]
    exact (Fin.snoc_init_self _).symm
  rw [hzu, hzv, zgn_diagF3_restrict]

private theorem zgn_exists_mem_act_eq {n : ℕ} (hn : 5 ≤ n) {x : Fin (n + 1) → ZMod 3}
    (hx : diagF3 (n + 1) 2 x x = 1) (hxl : x (Fin.last n) = 1) :
    ∃ g : ↥(F3.reflGroupPerp (diagF3 (n + 1) 2) (Pi.single (Fin.last n) 1)),
      F3.act (g : GL (Fin (n + 1)) (ZMod 3))
        (Pi.single 0 1 + Pi.single 1 1 + Pi.single (Fin.last n) 1) = x := by
  have hf : IsF3Form (diagF3 (n + 1) 2) := isF3Form_diagF3 (by decide)
  obtain ⟨h0_perp, h1_perp, h00, h11, ho01⟩ := zgn_std_pair hn
  obtain ⟨a, b, haa, hbb, hab, ha_last, hb_last, hxab⟩ := zgn_exists_decomposition hx hxl
  have ha_perp : a ∈ F3.perpOne (diagF3 (n + 1) 2) (Pi.single (Fin.last n) 1) := by
    rw [F3.mem_perpOne, zgn_diagF3_apply_last, ha_last, mul_zero]
  have hb_perp : b ∈ F3.perpOne (diagF3 (n + 1) 2) (Pi.single (Fin.last n) 1) := by
    rw [F3.mem_perpOne, zgn_diagF3_apply_last, hb_last, mul_zero]
  obtain ⟨g', hg'mem, hg'0, hg'1⟩ :=
    exists_mem_reflGroup_act_eq_pair (f := diagF3 n 1) (isF3Form_diagF3 one_ne_zero) hn
      (a := zgn_lastEquiv n ⟨Pi.single 0 1, h0_perp⟩)
      (b := zgn_lastEquiv n ⟨Pi.single 1 1, h1_perp⟩)
      (a' := zgn_lastEquiv n ⟨a, ha_perp⟩)
      (b' := zgn_lastEquiv n ⟨b, hb_perp⟩)
      (by rw [zgn_lastEquiv_form]; exact h00) (by rw [zgn_lastEquiv_form]; exact h11)
      (by rw [zgn_lastEquiv_form]; exact ho01) (by rw [zgn_lastEquiv_form]; exact haa)
      (by rw [zgn_lastEquiv_form]; exact hbb) (by rw [zgn_lastEquiv_form]; exact hab)
  rw [← range_perpToGL (f := diagF3 (n + 1) 2) (v := Pi.single (Fin.last n) 1)
    (zgn_lastEquiv n) (fun u v => zgn_lastEquiv_form n u v)] at hg'mem
  obtain ⟨g, hgg⟩ := MonoidHom.mem_range.1 hg'mem
  have hact0 : F3.act (g : GL (Fin (n + 1)) (ZMod 3)) (Pi.single 0 1) = a := by
    have h := coe_perpToGL_symm (f := diagF3 (n + 1) 2) (v := Pi.single (Fin.last n) 1)
      (zgn_lastEquiv n) g (zgn_lastEquiv n ⟨Pi.single 0 1, h0_perp⟩)
    rw [hgg, hg'0] at h
    simpa using h.symm
  have hact1 : F3.act (g : GL (Fin (n + 1)) (ZMod 3)) (Pi.single 1 1) = b := by
    have h := coe_perpToGL_symm (f := diagF3 (n + 1) 2) (v := Pi.single (Fin.last n) 1)
      (zgn_lastEquiv n) g (zgn_lastEquiv n ⟨Pi.single 1 1, h1_perp⟩)
    rw [hgg, hg'1] at h
    simpa using h.symm
  have hacte : F3.act (g : GL (Fin (n + 1)) (ZMod 3)) (Pi.single (Fin.last n) 1) =
      Pi.single (Fin.last n) 1 := F3.act_eq_of_mem_reflGroupPerp hf g.2
  refine ⟨g, ?_⟩
  rw [F3.act_add, F3.act_add, hact0, hact1, hacte, hxab]

private theorem zgn_range_perpToR3_le {n : ℕ} {H : Subgroup (R3 (diagF3 (n + 1) 2))}
    (hperp : ∀ w : Fin (n + 1) → ZMod 3, diagF3 (n + 1) 2 w w = 1 → w (Fin.last n) = 0 →
      reflBar (diagF3 (n + 1) 2) w ∈ H) :
    (perpToR3 (diagF3 (n + 1) 2) (Pi.single (Fin.last n) 1)).range ≤ H := by
  rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage
      (k := F3.reflSetPerp (diagF3 (n + 1) 2) (Pi.single (Fin.last n) 1)),
    MonoidHom.map_closure]
  rw [Subgroup.closure_le]
  rintro _ ⟨⟨g, hg⟩, ⟨w, hw, hwv, hgw⟩, rfl⟩
  have hmem : F3.refl (diagF3 (n + 1) 2) w ∈
      F3.reflSetPerp (diagF3 (n + 1) 2) (Pi.single (Fin.last n) 1) := ⟨w, hw, hwv, rfl⟩
  have hgen : F3.refl (diagF3 (n + 1) 2) w ∈
      F3.reflGroupPerp (diagF3 (n + 1) 2) (Pi.single (Fin.last n) 1) :=
    Subgroup.subset_closure hmem
  have heq : (⟨F3.refl (diagF3 (n + 1) 2) w, hgen⟩ :
      ↥(F3.reflGroupPerp (diagF3 (n + 1) 2) (Pi.single (Fin.last n) 1))) = ⟨g, hg⟩ :=
    Subtype.ext hgw
  rw [← heq, perpToR3_refl]
  refine hperp w hw ?_
  have h := hwv
  rw [zgn_diagF3_apply_last] at h
  exact (mul_eq_zero.1 h).resolve_left (by decide)

private theorem zgn_conj_reflBar_perp {n : ℕ}
    (g : ↥(F3.reflGroupPerp (diagF3 (n + 1) 2) (Pi.single (Fin.last n) 1)))
    (v : Fin (n + 1) → ZMod 3) :
    perpToR3 (diagF3 (n + 1) 2) (Pi.single (Fin.last n) 1) g *
        reflBar (diagF3 (n + 1) 2) v *
          (perpToR3 (diagF3 (n + 1) 2) (Pi.single (Fin.last n) 1) g)⁻¹ =
      reflBar (diagF3 (n + 1) 2) (F3.act (g : GL (Fin (n + 1)) (ZMod 3)) v) :=
  mk_conj_reflBar (isF3Form_diagF3 (by decide))
    (Subgroup.inclusion (F3.reflGroupPerp_le_reflGroup (Pi.single (Fin.last n) 1)) g) v

theorem closure_reflBar_last_eq_zero_insert_eq_top {n : ℕ} (hn : 5 ≤ n) :
    Subgroup.closure (insert (reflBar (diagF3 (n + 1) 2)
        (Pi.single 0 1 + Pi.single 1 1 + Pi.single (Fin.last n) 1))
      {q | ∃ w, diagF3 (n + 1) 2 w w = 1 ∧ w (Fin.last n) = 0 ∧
        reflBar (diagF3 (n + 1) 2) w = q}) = ⊤ := by
  set H : Subgroup (R3 (diagF3 (n + 1) 2)) :=
    Subgroup.closure (insert (reflBar (diagF3 (n + 1) 2)
        (Pi.single 0 1 + Pi.single 1 1 + Pi.single (Fin.last n) 1))
      {q | ∃ w, diagF3 (n + 1) 2 w w = 1 ∧ w (Fin.last n) = 0 ∧
        reflBar (diagF3 (n + 1) 2) w = q}) with hH
  change H = ⊤
  have hf : IsF3Form (diagF3 (n + 1) 2) := isF3Form_diagF3 (by decide)
  have htop : Subgroup.closure (D3 (diagF3 (n + 1) 2)) = ⊤ := by
    rw [D3_eq_image, ← QuotientGroup.coe_mk', ← MonoidHom.map_closure,
      Subgroup.closure_closure_coe_preimage]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  rw [eq_top_iff, ← htop]
  rw [Subgroup.closure_le]
  intro q hq
  obtain ⟨x, hx, rfl⟩ := (mem_D3_iff (f := diagF3 (n + 1) 2)).1 hq
  have hHperp : ∀ w : Fin (n + 1) → ZMod 3, diagF3 (n + 1) 2 w w = 1 →
      w (Fin.last n) = 0 → reflBar (diagF3 (n + 1) 2) w ∈ H := fun w hw hwl =>
    Subgroup.subset_closure (Or.inr ⟨w, hw, hwl, rfl⟩)
  have hH0 : reflBar (diagF3 (n + 1) 2)
      (Pi.single 0 1 + Pi.single 1 1 + Pi.single (Fin.last n) 1) ∈ H :=
    Subgroup.subset_closure (Or.inl rfl)
  by_cases hxl : x (Fin.last n) = 0
  · exact hHperp x hx hxl
  have hsplit : x (Fin.last n) = 1 ∨ x (Fin.last n) = -1 := by
    revert hxl
    generalize x (Fin.last n) = c
    revert c
    decide
  have hmain : ∀ y : Fin (n + 1) → ZMod 3, diagF3 (n + 1) 2 y y = 1 →
      y (Fin.last n) = 1 → reflBar (diagF3 (n + 1) 2) y ∈ H := by
    intro y hy hyl
    obtain ⟨g, hact⟩ := zgn_exists_mem_act_eq hn hy hyl
    have hrange := zgn_range_perpToR3_le (H := H) hHperp
    have hmem : perpToR3 (diagF3 (n + 1) 2) (Pi.single (Fin.last n) 1) g ∈ H :=
      hrange ⟨g, rfl⟩
    have hconj : reflBar (diagF3 (n + 1) 2) y =
        perpToR3 (diagF3 (n + 1) 2) (Pi.single (Fin.last n) 1) g *
          reflBar (diagF3 (n + 1) 2)
            (Pi.single 0 1 + Pi.single 1 1 + Pi.single (Fin.last n) 1) *
            (perpToR3 (diagF3 (n + 1) 2) (Pi.single (Fin.last n) 1) g)⁻¹ := by
      rw [zgn_conj_reflBar_perp, hact]
    rw [hconj]
    exact H.mul_mem (H.mul_mem hmem hH0) (H.inv_mem hmem)
  rcases hsplit with h | h
  · exact hmain x hx h
  · rw [← reflBar_neg]
    exact hmain (-x) (by
        rw [LinearMap.BilinForm.neg_left, LinearMap.BilinForm.neg_right, hx]
        decide)
      (by rw [Pi.neg_apply, h]; decide)

end CFSG.StandardType.ZS
