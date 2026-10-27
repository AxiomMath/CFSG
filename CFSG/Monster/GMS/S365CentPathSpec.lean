
module

public import CFSG.Monster.GMS.S365CentPathSpecBase

public import CFSG.Monster.GMS.S365CosetSpec
public import CFSG.Monster.GMS.S365CentBasic
public import CFSG.Monster.GMS.S365Facts
public import Certificates.Data.CFSGNative.Co1.S365CentPath
public import CFSG.Monster.GMS.S365CentPathSpecInputs
public import Certificates.Certificate10037
public meta import CFSG.Sporadic.Co1.Module.PairsCheck
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import CFSG.Monster.GMS.S365CosetSpec
public meta import Certificates.Data.CFSGNative.Co1.S365CentPath
public import Certificates.Certificate10037Base
public meta import Certificates.Certificate10042Base
public import Certificates.Certificate10042Base

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

open scoped Matrix
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.Co1.S365Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.S365CentNative

theorem pathCheck_ok : pathCheck = true :=
  Certificates.certificate10037

theorem cosetElems_fix {gl : ℕ → Co1}
    (hgl : ∀ l < cosetRowsT.size, ∀ u, gl l • toVecD 24 u =
      toVecD 24 (vecMulN 24 cosetRowsT[l]! u)) :
    ∀ l < cosetRowsT.size, gl l • toVecD 24 2 = toVecD 24 2 ∧
      gl l • toVecD 24 4 = toVecD 24 4 := by
  have hc := pathCheck_ok
  unfold pathCheck at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, hfixall⟩, -⟩ := hc
  intro l hl
  have hf := Array.all_eq_true.1 hfixall l hl
  simp only [Bool.and_eq_true] at hf
  have e2 : vecMulN 24 cosetRowsT[l]! 2 = 2 := by
    rw [getElem!_pos cosetRowsT l hl]; exact beq_iff_eq.1 hf.1
  have e4 : vecMulN 24 cosetRowsT[l]! 4 = 4 := by
    rw [getElem!_pos cosetRowsT l hl]; exact beq_iff_eq.1 hf.2
  exact ⟨by rw [hgl l hl, e2], by rw [hgl l hl, e4]⟩

theorem exists_translation
    {κ : Fin 24 → ZMod 2}
    (hκ : InK (toVecD 24 2) (toVecD 24 4) κ) :
    ∃ τ : Co1, τ • toVecD 24 2 = toVecD 24 2 ∧ τ • toVecD 24 4 = toVecD 24 4 ∧
      τ • toVecD 24 cosetBase = toVecD 24 cosetBase + κ := by
  obtain ⟨gl, hgl⟩ := exists_cosetElems
  have hc := pathCheck_ok
  unfold pathCheck at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hp1, hp2⟩, hp3⟩, -⟩, -⟩ := hc
  have h3 : cosetRowsT.size = 3 := by decide
  have hs1 : ∀ l ∈ pathE1, l < cosetRowsT.size := by rw [h3]; decide
  have hs2 : ∀ l ∈ pathE2, l < cosetRowsT.size := by rw [h3]; decide
  have hs12 : ∀ l ∈ pathE12, l < cosetRowsT.size := by rw [h3]; decide
  have hstab := cosetElems_fix hgl
  have hfix2 := pathElem_fix (fun l hl => (hstab l hl).1)
  have hfix4 := pathElem_fix (fun l hl => (hstab l hl).2)
  rcases hκ with rfl | rfl | rfl | rfl
  · exact ⟨1, one_smul _ _, one_smul _ _, by rw [one_smul, add_zero]⟩
  · refine ⟨pathElem gl pathE1, hfix2 _ hs1, hfix4 _ hs1, ?_⟩
    rw [pathElem_smul hgl _ hs1, hp1, toVecD_xor]
  · refine ⟨pathElem gl pathE2, hfix2 _ hs2, hfix4 _ hs2, ?_⟩
    rw [pathElem_smul hgl _ hs2, hp2, toVecD_xor]
  · refine ⟨pathElem gl pathE12, hfix2 _ hs12, hfix4 _ hs12, ?_⟩
    rw [pathElem_smul hgl _ hs12, hp3, toVecD_xor, toVecD_xor, add_assoc]

theorem co1FourTV_ref
    {v v' : Fin 24 → ZMod 2} (hv : FourPattern (toVecD 24 2) (toVecD 24 4) v)
    (hv' : FourPattern (toVecD 24 2) (toVecD 24 4) v') :
    ∃ g : Co1, g • toVecD 24 2 = toVecD 24 2 ∧ g • toVecD 24 4 = toVecD 24 4 ∧ g • v = v' := by
  obtain ⟨g₁, h1x, h1y, h1c⟩ := co1FourT_ref v v' hv hv'
  obtain ⟨h, hhx, hhy, hhc⟩ := co1FourT_ref v' _ hv' refPattern
  obtain ⟨κ, hκ, hκv⟩ : ∃ κ, InK (toVecD 24 2) (toVecD 24 4) κ ∧ g₁ • v = v' + κ :=
    ⟨g₁ • v + v', h1c, by rw [add_comm v' _, vec_add_add_right]⟩
  obtain ⟨κ₁, hκ₁, hhv⟩ : ∃ κ₁, InK (toVecD 24 2) (toVecD 24 4) κ₁ ∧
      h • v' = toVecD 24 cosetBase + κ₁ :=
    ⟨h • v' + toVecD 24 cosetBase, hhc, by rw [add_comm (h • v') _, vec_add_add_left]⟩
  obtain ⟨τ, hτx, hτy, hτc⟩ := exists_translation hκ
  have hhκ : h⁻¹ • κ = κ := by
    have := InK.smul_eq hhx hhy hκ
    conv_lhs => rw [← this]
    exact inv_smul_smul h κ
  have hτκ₁ : τ • κ₁ = κ₁ := InK.smul_eq hτx hτy hκ₁
  have hτ'v : (h⁻¹ * τ * h) • v' = g₁ • v := by
    have e1 : τ • (h • v') = h • v' + κ := by
      calc τ • (h • v') = τ • (toVecD 24 cosetBase + κ₁) := by rw [← hhv]
        _ = (toVecD 24 cosetBase + κ) + κ₁ := by rw [smul_add, hτc, hτκ₁]
        _ = (toVecD 24 cosetBase + κ₁) + κ := add_right_comm _ _ _
        _ = h • v' + κ := by rw [← hhv]
    rw [mul_smul, mul_smul, e1, smul_add, inv_smul_smul, hhκ, hκv]
  have hfx : (h⁻¹ * τ * h) • toVecD 24 2 = toVecD 24 2 := by
    rw [mul_smul, mul_smul, hhx, hτx]
    exact inv_smul_eq_iff.2 hhx.symm
  have hfy : (h⁻¹ * τ * h) • toVecD 24 4 = toVecD 24 4 := by
    rw [mul_smul, mul_smul, hhy, hτy]
    exact inv_smul_eq_iff.2 hhy.symm
  refine ⟨(h⁻¹ * τ * h)⁻¹ * g₁, ?_, ?_, ?_⟩
  · rw [mul_smul, h1x]
    exact inv_smul_eq_iff.2 hfx.symm
  · rw [mul_smul, h1y]
    exact inv_smul_eq_iff.2 hfy.symm
  · rw [mul_smul, ← hτ'v, inv_smul_smul]

theorem co1FourTV :
    Co1FourTV := by
  intro a b ω a' b' ω' hP hP'
  obtain ⟨hx₀, hy₀, hxy₀⟩ := refPair
  obtain ⟨g₁, hg₁a, hg₁b⟩ := exists_co1Act_pair hP.1 hP.2.1 hP.2.2.1 hx₀ hy₀ hxy₀
  obtain ⟨g₂, hg₂a, hg₂b⟩ := exists_co1Act_pair hP'.1 hP'.2.1 hP'.2.2.1 hx₀ hy₀ hxy₀
  have hg₁a' : g₁ • a = toVecD 24 2 := hg₁a
  have hg₁b' : g₁ • b = toVecD 24 4 := hg₁b
  have hg₂a' : g₂ • a' = toVecD 24 2 := hg₂a
  have hg₂b' : g₂ • b' = toVecD 24 4 := hg₂b
  have hω₁ : FourPattern (toVecD 24 2) (toVecD 24 4) (g₁ • ω) := by
    have := hP.map g₁
    rwa [hg₁a', hg₁b'] at this
  have hω₂ : FourPattern (toVecD 24 2) (toVecD 24 4) (g₂ • ω') := by
    have := hP'.map g₂
    rwa [hg₂a', hg₂b'] at this
  obtain ⟨h, hh2, hh4, hhc⟩ := co1FourTV_ref hω₁ hω₂
  refine ⟨g₂⁻¹ * h * g₁, ?_, ?_, ?_⟩
  · show (g₂⁻¹ * h * g₁) • a = a'
    rw [mul_smul, mul_smul, hg₁a', hh2, ← hg₂a', inv_smul_smul]
  · show (g₂⁻¹ * h * g₁) • b = b'
    rw [mul_smul, mul_smul, hg₁b', hh4, ← hg₂b', inv_smul_smul]
  · show (g₂⁻¹ * h * g₁) • ω = ω'
    rw [mul_smul, mul_smul, hhc, inv_smul_smul]

theorem ncard_PatSet_ref :
    (PatSet (toVecD 24 2) (toVecD 24 4)).ncard = 1995840 := by
  have hc := pathCheck_ok
  unfold pathCheck at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨-, hcnt⟩ := hc
  rw [← hcnt]
  exact ncard_eq_countBelow (fun x hx => pat4_iff hx)

theorem ncard_PatSet
    {a b : Fin 24 → ZMod 2} (ha : a ∈ co1Orbit 0) (hb : b ∈ co1Orbit 0)
    (hab : a + b ∈ co1Orbit 0) : (PatSet a b).ncard = 1995840 := by
  obtain ⟨hx₀, hy₀, hxy₀⟩ := refPair
  obtain ⟨g, hga, hgb⟩ := exists_co1Act_pair hx₀ hy₀ hxy₀ ha hb hab
  have hga' : g • toVecD 24 2 = a := hga
  have hgb' : g • toVecD 24 4 = b := hgb
  subst hga' hgb'
  have himg : PatSet (g • toVecD 24 2) (g • toVecD 24 4) =
      (fun u => g • u) '' PatSet (toVecD 24 2) (toVecD 24 4) := by
    ext v
    constructor
    · intro hv
      refine ⟨g⁻¹ • v, ?_, smul_inv_smul g v⟩
      have := PatSet.map g⁻¹ hv
      rwa [inv_smul_smul, inv_smul_smul] at this
    · rintro ⟨u, hu, rfl⟩
      exact PatSet.map g hu
  rw [himg, Set.ncard_image_of_injective _ (MulAction.injective g), ncard_PatSet_ref]

theorem card_inf_stab_three
    {a b ω : Fin 24 → ZMod 2} (h : FourPattern a b ω) :
    Nat.card ↥(co1Stab a ⊓ co1Stab b ⊓ co1Stab ω) = 4608 := by
  have hT := Pairs.ncard_mul_card_inf_stabilizer (K := co1Stab a ⊓ co1Stab b) (w := ω)
    (T := PatSet a b) h.2.2.2 ?_ ?_
  · rw [← co1Stab_eq ω, ncard_PatSet h.1 h.2.1 h.2.2.1, card_inf_stab_pair h.1 h.2.1 h.2.2.1] at hT
    omega
  · intro t ht
    obtain ⟨g, hga, hgb, hgω⟩ := co1FourTV a b ω a b t h ⟨h.1, h.2.1, h.2.2.1, ht⟩
    exact ⟨g, Subgroup.mem_inf.2 ⟨hga, hgb⟩, hgω⟩
  · intro g hg t ht
    obtain ⟨hga, hgb⟩ := Subgroup.mem_inf.1 hg
    exact PatSet.smul_mem hga hgb ht

end S365

end CFSG.Monster.GMS
