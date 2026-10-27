
module

public import CFSG.Monster.B.TwoA.Base.GeomNativeBase

public import CFSG.Monster.B.TwoA.Base.GeomConn

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B Module

open CFSG.Monster.B.Co2 (v0)

attribute [local instance] parAction

theorem Echain_eq_EU :
    ∀ t : ℕ, 2 ≤ t → t ≤ 5 → Echain t = EU (natStd t) := by
  intro t h2 h5
  interval_cases t
  · exact Vhat_eq_EU
  · exact E3_eq_EU
  · exact E4_eq_EU
  · exact E5_eq_EU

theorem mem_Res1_iff
    (x : ParGeom) : x ∈ Res1 ↔ 1 < parType x ∧ Echain 1 ≤ x.1.2 := by
  have h := mem_parRes_stdSub (J := {1}) (by
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact ⟨le_rfl, by norm_num⟩) x
  have e : stdSub {1} = {stdObj 1 le_rfl (by norm_num)} := by
    ext y
    constructor
    · rintro ⟨hy, hy1⟩
      exact obj_ext hy1 (by rw [show y.1.2 = Echain y.1.1 from hy]; exact congrArg Echain hy1)
    · rintro rfl
      exact ⟨rfl, rfl⟩
  change x ∈ parRes {stdObj 1 le_rfl (by norm_num)} ↔ _
  rw [← e, h]
  constructor
  · rintro ⟨h1, h2⟩
    have hb := parType_bounds x
    have hx1 : parType x ≠ 1 := h1
    exact ⟨by omega, (h2 1 rfl).1 (by omega)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => ?_, fun s hs => ?_⟩
    · rw [Set.mem_singleton_iff] at h
      omega
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact ⟨fun _ => h2, fun h => absurd h (by omega)⟩

theorem exists_Jhat_of_Res1
    {x : ParGeom} (hx : x ∈ Res1) :
    ∃ h ∈ Jhat, x.1.2 = conjSub h (Echain (parType x)) := by
  obtain ⟨h1, h2⟩ := (mem_Res1_iff x).1 hx
  obtain ⟨h, hh, hhx⟩ := exists_Kchain_smul_std le_rfl h1 h2
  rw [Kchain_one] at hh
  exact ⟨h, hh, (congrArg (fun y : ParGeom => y.1.2) hhx).symm⟩

theorem resNat_of_conj
    {x : ParGeom} {h : Dfull} (hh : h ∈ Jhat) (ht : 2 ≤ parType x)
    (hx : x.1.2 = conjSub h (Echain (parType x))) :
    (resNat x).2 = (natStd (parType x)).map (wAct v0 (jhatToKv0 ⟨h, hh⟩)⁻¹) ∧
      x.1.2 = EU ((natStd (parType x)).map (wAct v0 (jhatToKv0 ⟨h, hh⟩)⁻¹)) := by
  have e : x.1.2 = EU ((natStd (parType x)).map (wAct v0 (jhatToKv0 ⟨h, hh⟩)⁻¹)) := by
    rw [hx, Echain_eq_EU _ ht (parType_bounds x).2, conjSub_EU hh]
  exact ⟨by rw [resNat, e, psiSubImage_EU], e⟩

theorem resNat_mem
    {x : ParGeom} (hx : x ∈ Res1) : resNat x ∈ NatObj := by
  obtain ⟨h1, -⟩ := (mem_Res1_iff x).1 hx
  obtain ⟨h, hh, hhx⟩ := exists_Jhat_of_Res1 hx
  exact ⟨h1, (parType_bounds x).2, _, (resNat_of_conj hh h1 hhx).1⟩

theorem eq_EU_resNat
    {x : ParGeom} (hx : x ∈ Res1) : x.1.2 = EU (resNat x).2 := by
  obtain ⟨h1, -⟩ := (mem_Res1_iff x).1 hx
  obtain ⟨h, hh, hhx⟩ := exists_Jhat_of_Res1 hx
  rw [(resNat_of_conj hh h1 hhx).1]
  exact (resNat_of_conj hh h1 hhx).2

@[expose] def res1Equiv :
    Res1 ≃ NatObj where
  toFun x := ⟨resNat x.1, resNat_mem x.2⟩
  invFun y := ⟨⟨(y.1.1, EU y.1.2), by
      obtain ⟨h2, h5, k, hk⟩ := y.2
      obtain ⟨g, hg⟩ := jhatToKv0_surjective k⁻¹
      refine ⟨by omega, h5, g, Jhat_le_Shat g.2, ?_⟩
      change EU y.1.2 = conjSub (g : Dfull) (Echain y.1.1)
      rw [Echain_eq_EU _ h2 h5, conjSub_EU g.2, hk]
      congr 2
      change wAct v0 k = wAct v0 (jhatToKv0 g)⁻¹
      rw [hg, inv_inv]⟩, (mem_Res1_iff _).2 ⟨by
        change 1 < y.1.1
        have := y.2.1
        omega, Subgroup.zpowers_le.2 xhat_mem_EU⟩⟩
  left_inv x := Subtype.ext (obj_ext rfl (eq_EU_resNat x.2).symm)
  right_inv y := Subtype.ext (Prod.ext rfl (psiSubImage_EU y.1.2))

theorem coe_res1Equiv
    (x : Res1) : (res1Equiv x : ℕ × Submodule (ZMod 2) (Wv v0)) = resNat x :=
  rfl

theorem res1Equiv_le_iff
    (x y : Res1) :
    x.1.1.2 ≤ y.1.1.2 ↔ (res1Equiv x).1.2 ≤ (res1Equiv y).1.2 := by
  change x.1.1.2 ≤ y.1.1.2 ↔ psiSubImage x.1.1.2 ≤ psiSubImage y.1.1.2
  rw [eq_EU_resNat x.2, eq_EU_resNat y.2, EU_le_EU_iff, psiSubImage_EU, psiSubImage_EU]

theorem resNat_smul
    {x : ParGeom} (hx : x ∈ Res1) (h : Shat) (hh : (h : Dfull) ∈ Jhat) :
    resNat (h • x) = (parType x, (resNat x).2.map (wAct v0 (jhatToKv0 ⟨h, hh⟩)⁻¹)) := by
  refine Prod.ext rfl ?_
  change psiSubImage (conjSub (h : Dfull) x.1.2) = _
  rw [eq_EU_resNat hx, conjSub_EU hh, psiSubImage_EU]

end CFSG.Monster.B.TwoA
