module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepKGlueDefs

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

private theorem matrix_eq_of_mulVec_eq {g h : Mat6} (key : ∀ v, g.mulVec v = h.mulVec v) : g = h := by
  refine Matrix.ext fun i j => ?_
  have := congrFun (key (Pi.single j (1 : ZMod 3))) i
  simpa [Matrix.mulVec_single_one] using this

theorem exists_matrix_of_addHom (f : Vec6 →+ Vec6) : ∃ M : Mat6, ∀ v, M.mulVec v = f v := by
  refine ⟨LinearMap.toMatrix' (AddMonoidHom.toZModLinearMap 3 f), fun v => ?_⟩
  rw [LinearMap.toMatrix'_mulVec, AddMonoidHom.coe_toZModLinearMap]

theorem exists_actsAs {Bs : Subgroup G} (ι : Additive ↥Bs ≃+ Vec6) (φ : MulAut ↥Bs) :
    ∃ g : Mat6, ActsAs ι φ g := by
  let f : Vec6 →+ Vec6 :=
    { toFun := fun v => ι (Additive.ofMul (φ (Additive.toMul (ι.symm v))))
      map_zero' := by
        simp only [map_zero, toMul_zero, map_one, ofMul_one]
      map_add' := by
        intro a b
        simp only [map_add, toMul_add, map_mul, ofMul_mul] }
  obtain ⟨M, hM⟩ := exists_matrix_of_addHom f
  refine ⟨M, fun b => ?_⟩
  rw [hM]
  change ι (Additive.ofMul (φ b)) =
    ι (Additive.ofMul (φ (Additive.toMul (ι.symm (ι (Additive.ofMul b))))))
  rw [AddEquiv.symm_apply_apply, toMul_ofMul]

theorem actsAs_inj {Bs : Subgroup G} {ι : Additive ↥Bs ≃+ Vec6} {φ : MulAut ↥Bs} {g g' : Mat6}
    (h : ActsAs ι φ g) (h' : ActsAs ι φ g') : g = g' := by
  refine matrix_eq_of_mulVec_eq fun v => ?_
  have hgv := h (Additive.toMul (ι.symm v))
  have hhv := h' (Additive.toMul (ι.symm v))
  simp only [ofMul_toMul, AddEquiv.apply_symm_apply] at hgv hhv
  rw [← hgv, ← hhv]

theorem ggIsReflection_of_actsAs {Bs : Subgroup G} {ι : Additive ↥Bs ≃+ Vec6} {φ : MulAut ↥Bs}
    {g : Mat6} (h : ActsAs ι φ g) (hg2 : g * g = 1)
    (hcard : Fintype.card {v : Vec6 // g.mulVec v = v} * 3 = 3 ^ 6) :
    GGIsReflection 3 φ := by
  have hkey : ∀ b : ↥Bs, ι (Additive.ofMul (φ (φ b))) = ι (Additive.ofMul b) := by
    intro b
    calc ι (Additive.ofMul (φ (φ b)))
        = g.mulVec (ι (Additive.ofMul (φ b))) := h (φ b)
      _ = g.mulVec (g.mulVec (ι (Additive.ofMul b))) := by rw [h b]
      _ = (g * g).mulVec (ι (Additive.ofMul b)) :=
            Matrix.mulVec_mulVec (ι (Additive.ofMul b)) g g
      _ = (1 : Mat6).mulVec (ι (Additive.ofMul b)) := by rw [hg2]
      _ = ι (Additive.ofMul b) := Matrix.one_mulVec _
  have hφ2 : φ ^ 2 = 1 := by
    refine MulEquiv.ext fun b => ?_
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
    have h1 := congrArg Additive.toMul (ι.injective (hkey b))
    simpa only [toMul_ofMul] using h1
  have hfix : ∀ b : ↥Bs,
      (φ b = b) ↔ g.mulVec (ι (Additive.ofMul b)) = ι (Additive.ofMul b) := by
    intro b
    rw [← h b]
    exact ⟨fun hb => by rw [hb], fun hb => by
      have h1 := congrArg Additive.toMul (ι.injective hb)
      simpa only [toMul_ofMul] using h1⟩
  have hfixcard : Nat.card {b : ↥Bs // φ b = b} = Nat.card {v : Vec6 // g.mulVec v = v} :=
    Nat.card_congr (Equiv.subtypeEquiv (Additive.ofMul.trans ι.toEquiv) hfix)
  have hcardNat : Nat.card {v : Vec6 // g.mulVec v = v} * 3 = 3 ^ 6 := by
    rw [Nat.card_eq_fintype_card]
    exact hcard
  have hBs : Nat.card ↥Bs = 3 ^ 6 := by
    rw [Nat.card_congr (Additive.ofMul.trans ι.toEquiv), Nat.card_fun (α := Fin 6) (β := ZMod 3),
      Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact ⟨hφ2, by rw [hfixcard, hcardNat, hBs]⟩

theorem mat_comm_of_acts {Bs : Subgroup G} {ι : Additive ↥Bs ≃+ Vec6} {κ : Additive ↥Bs →+ Vec6}
    {M : Mat6} (hκM : ∀ b : ↥Bs, κ (Additive.ofMul b) = M.mulVec (ι (Additive.ofMul b)))
    {φ : MulAut ↥Bs} {g k : Mat6} (hg : ActsAs ι φ g) (hk : ActsAsK κ φ k) : M * g = k * M := by
  refine matrix_eq_of_mulVec_eq fun w => ?_
  set b : ↥Bs := Additive.toMul (ι.symm w) with hb
  have hw : ι (Additive.ofMul b) = w := by simp [hb]
  calc (M * g).mulVec w
      = M.mulVec (g.mulVec w) := (Matrix.mulVec_mulVec w M g).symm
    _ = M.mulVec (g.mulVec (ι (Additive.ofMul b))) := by rw [hw]
    _ = M.mulVec (ι (Additive.ofMul (φ b))) := by rw [hg b]
    _ = κ (Additive.ofMul (φ b)) := (hκM (φ b)).symm
    _ = k.mulVec (κ (Additive.ofMul b)) := hk b
    _ = k.mulVec (M.mulVec (ι (Additive.ofMul b))) := by rw [hκM b]
    _ = k.mulVec (M.mulVec w) := by rw [hw]
    _ = (k * M).mulVec w := Matrix.mulVec_mulVec w k M

theorem kappa_matrix {Bs X : Subgroup G} {y : G} (hyBs : y ∈ Bs) {κ : Additive ↥Bs →+ Vec6}
    (hκ : GGE6DepKFrame Bs X y κ) {ι : Additive ↥Bs ≃+ Vec6} {c : ZMod 3}
    (hy : ι (Additive.ofMul ⟨y, hyBs⟩) = xs + c • xx) :
    ∃ M : Mat6, (∀ b : ↥Bs, κ (Additive.ofMul b) = M.mulVec (ι (Additive.ofMul b))) ∧
      (∀ v, M.mulVec v 5 = 0) ∧ (∀ v : Vec6, v 5 = 0 → ∃ u, M.mulVec u = v) ∧
      M.mulVec (kY c) = 0 ∧ (∀ v, M.mulVec v = 0 → ∃ j : ZMod 3, v = j • kY c) := by
  obtain ⟨M, hM⟩ := exists_matrix_of_addHom (κ.comp ι.symm.toAddMonoidHom)
  have hM' : ∀ v, M.mulVec v = κ (ι.symm v) := fun v => hM v
  have hMy : ι (Additive.ofMul ⟨y, hyBs⟩) = kY c := by rw [hy, kY_eq]
  refine ⟨M, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    rw [hM', AddEquiv.symm_apply_apply]
  · intro v
    rw [hM']
    simpa using hκ.2.1 (Additive.toMul (ι.symm v))
  · intro v hv
    obtain ⟨b, hb⟩ := hκ.2.2.1 v hv
    exact ⟨ι (Additive.ofMul b), by rw [hM', AddEquiv.symm_apply_apply]; exact hb⟩
  · rw [hM']
    have hyv : ι.symm (kY c) = Additive.ofMul ⟨y, hyBs⟩ := by
      rw [← hMy, AddEquiv.symm_apply_apply]
    rw [hyv]
    exact (hκ.1 ⟨y, hyBs⟩).mpr (Subgroup.mem_zpowers y)
  · intro v hv
    set b : ↥Bs := Additive.toMul (ι.symm v) with hb
    have hbval : Additive.ofMul b = ι.symm v := by simp [hb]
    have hkb : κ (Additive.ofMul b) = 0 := by
      rw [hbval, ← hM' v, hv]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp ((hκ.1 b).mp hkb)
    refine ⟨(n : ZMod 3), ?_⟩
    have hb_eq : b = (⟨y, hyBs⟩ : ↥Bs) ^ n :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hn.symm)
    calc v = ι (Additive.ofMul b) := by rw [hbval, AddEquiv.apply_symm_apply]
      _ = ι (Additive.ofMul ((⟨y, hyBs⟩ : ↥Bs) ^ n)) := by rw [hb_eq]
      _ = ι (n • Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) := by rw [ofMul_zpow]
      _ = n • ι (Additive.ofMul ⟨y, hyBs⟩) := map_zsmul ι n _
      _ = n • kY c := by rw [hMy]
      _ = (n : ZMod 3) • kY c := (Int.cast_smul_eq_zsmul (ZMod 3) n (kY c)).symm

end E6Dep

end CFSG.StandardType

end
