module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveTwelveFA
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveTwelveFB
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveTwelveQ
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveElevenA
public import CFSG.LocalAnalysis.WeakClosure81.TwelveFour
import all CFSG.LocalAnalysis.WeakClosure81.FiveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped CFSG.Goldschmidt.G2

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

private theorem mem_fixSub_zpowers_iff {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {a : LGL 2 V} {v : V} : v ∈ fixSub (Subgroup.zpowers a) ↔ a v = v := by
  rw [mem_fixSub]
  constructor
  · intro h
    exact h a (Subgroup.mem_zpowers a)
  · intro h g hg
    have hle : Subgroup.zpowers a ≤ MulAction.stabilizer (LGL 2 V) v :=
      Subgroup.zpowers_le.mpr
        (by simpa only [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def] using h)
    simpa only [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def] using hle hg

private theorem fixSub_map_eRep [Fact (IsElemAbelian 2 (eSub V₀ X T))] {Y : Subgroup G}
    (hYX : Y ≤ X) :
    fixSub ((Y.subgroupOf X).map (eRep V₀ X T)) =
      CFSG.Goldschmidt.G2.sub (eSub V₀ X T) (Subgroup.centralizer (Y : Set G)) := by
  ext v
  rw [mem_fixSub, CFSG.Goldschmidt.G2.mem_sub, Subgroup.mem_centralizer_iff]
  constructor
  · intro hv y hy
    have hmem : (⟨y, hYX hy⟩ : ↥X) ∈ Y.subgroupOf X := Subgroup.mem_subgroupOf.2 hy
    have h1 : eRep V₀ X T ⟨y, hYX hy⟩ v = v :=
      hv (eRep V₀ X T ⟨y, hYX hy⟩) (Subgroup.mem_map_of_mem _ hmem)
    have h2 : y * ((Additive.toMul v : ↥(eSub V₀ X T)) : G) * y⁻¹ =
        ((Additive.toMul v : ↥(eSub V₀ X T)) : G) := by
      have hcong := congrArg (fun w => ((Additive.toMul w : ↥(eSub V₀ X T)) : G)) h1
      simpa [eRep_apply] using hcong
    calc y * ((Additive.toMul v : ↥(eSub V₀ X T)) : G)
        = y * ((Additive.toMul v : ↥(eSub V₀ X T)) : G) * y⁻¹ * y := by group
      _ = ((Additive.toMul v : ↥(eSub V₀ X T)) : G) * y := by rw [h2]
  · intro hv a ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 ha
    have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.1 hy
    have h := hv (y : G) hyY
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [eRep_apply, h]
    group

private theorem fixSub_zpowers_eRep [Fact (IsElemAbelian 2 (eSub V₀ X T))] (y : ↥X) :
    fixSub (Subgroup.zpowers (eRep V₀ X T y)) =
      CFSG.Goldschmidt.G2.sub (eSub V₀ X T)
        (Subgroup.centralizer ({(y : G)} : Set G)) := by
  ext v
  rw [mem_fixSub_zpowers_iff, CFSG.Goldschmidt.G2.mem_sub,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hv
    have h2 : (y : G) * ((Additive.toMul v : ↥(eSub V₀ X T)) : G) * (y : G)⁻¹ =
        ((Additive.toMul v : ↥(eSub V₀ X T)) : G) := by
      have hcong := congrArg (fun w => ((Additive.toMul w : ↥(eSub V₀ X T)) : G)) hv
      simpa [eRep_apply] using hcong
    calc ((Additive.toMul v : ↥(eSub V₀ X T)) : G) * (y : G)
        = ((y : G) * ((Additive.toMul v : ↥(eSub V₀ X T)) : G) * (y : G)⁻¹) * (y : G) := by
          rw [h2]
      _ = (y : G) * ((Additive.toMul v : ↥(eSub V₀ X T)) : G) := by group
  · intro hv
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [eRep_apply, ← hv]
    group

theorem Hyp167.lt_mSub_of_inf_centralizer_eq_bot
    (hI : NamedInputs15 G) (hS : Std15 G) (h152 : Thm152 G)
    (h1 : W16One G) (hX : Hyp167 M V₀ V U S H g X T) (hVO : V ≤ pCoreOf 2 H)
    (hm : 1 < mSub V₀)
    (hBC : conjSubgroup V₀ g ⊓ centralizer (eSub V₀ X T : Set G) = ⊥) :
    E3.mQuot V (U ⊔ V₀) < mSub V₀ := by
  have hV₀ : V₀ ≤ pCoreOf 2 H := hX.cex.hyp.h6.le.trans hVO
  have hE : IsElemAbelian 2 (eSub V₀ X T) := Hyp167.isElemAbelian_eSub h1 hS hV₀ hX
  haveI : Fact (IsElemAbelian 2 (eSub V₀ X T)) := ⟨hE⟩
  have hB : conjSubgroup V₀ g ≤ X :=
    (E3.conjSubgroup_mono_left g hX.cex.hyp.h6.le).trans hX.mem.2.2.A_le
  have hBE : conjSubgroup V₀ g ⊓ eSub V₀ X T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxB, hxE⟩ := Subgroup.mem_inf.1 hx
    have hxC : x ∈ centralizer (eSub V₀ X T : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun y hy => B2F.isElemAbelian_comm hE hy hxE
    have hx' : x ∈ conjSubgroup V₀ g ⊓ centralizer (eSub V₀ X T : Set G) := ⟨hxB, hxC⟩
    rwa [hBC] at hx'
  have hK : kerMOf M X ≤ centralizer (eSub V₀ X T : Set G) :=
    Hyp167.kerMOf_le_centralizer_of_inf_eq_bot hI hS h152 h1 hV₀ hX hBE
  obtain ⟨ρ, hρ⟩ := exists_eRepBar M V₀ X T hK
  have hA : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup hX.cex.hyp.h6.elemAbelian g
  have hpair : IsPairAt M X (conjSubgroup V g) := hX.mem.2.2
  have hXU : X ≤ centralizer (U : Set G) := hX.mem.1.trans hX.min.1.2.1
  have hKG : CFSG.Open.IsKGroup ↥X :=
    (hS.localsK _ ⟨U, hX.cex.ne_bot, hX.cex.hyp.isPGroup.to_le hX.cex.le, rfl⟩).of_le
      (hXU.trans (Subgroup.centralizer_le_normalizer (U : Set G)))
  have hbig : 2 < (conjSubgroup V g ⊓ kerMOf M X).relIndex (conjSubgroup V g) :=
    Hyp167.two_lt_relIndex_of_inf_eq_bot h1 hS h152 hV₀ hX hBE
  obtain ⟨⟨k, hk⟩, hBorel⟩ := five_nine_borel hI.thmB hpair hA hKG hbig
  have hquad := Hyp167.quad_of_inf_centralizer_eq_bot h1 hS hX hVO hBC
  have hquadE : ∀ a ∈ conjSubgroup V₀ g, ∀ b ∈ conjSubgroup V₀ g, ∀ e ∈ eSub V₀ X T,
      a * (b * e * b⁻¹ * e⁻¹) * a⁻¹ = b * e * b⁻¹ * e⁻¹ :=
    fun a ha b hb e he => hquad a ha b hb e
      (conjClosure_mono (inf_le_left.trans hX.cex.hyp.h6.le) le_rfl he)
  have h12 : Setting12One ρ (kerQuotImg M X M)
      (CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀)
      (kerQuotImg M X (conjSubgroup V₀ g)) k (mSub V₀) :=
    Hyp167.setting12One hX hm hBC hK hquadE hk hBorel hρ
  have hZ : Module.finrank (ZMod 2) (CFSG.Goldschmidt.G2.sub (eSub V₀ X T) V₀) ≤ mSub V₀ :=
    Hyp167.finrank_sub_le hX
  have hCA : ∀ a ∈ kerQuotImg M X (conjSubgroup V₀ g), a ≠ 1 →
      fixSub ((kerQuotImg M X (conjSubgroup V₀ g)).map ρ) =
        fixSub ((Subgroup.zpowers a).map ρ) := by
    intro a ha ha1
    have hker : kerQuotImg M X (conjSubgroup V₀ g) =
        ((conjSubgroup V₀ g).subgroupOf X).map (kerQuotMk M X) := rfl
    rw [hker] at ha
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 ha
    have hb : (y : G) ∈ conjSubgroup V₀ g := Subgroup.mem_subgroupOf.1 hy
    have hb1 : (y : G) ≠ 1 := by
      intro h
      apply ha1
      have hy1 : y = 1 := Subtype.ext h
      rw [← hyeq, hy1, map_one]
    have hinf := Hyp167.inf_centralizer_eq_of_inf_centralizer_eq_bot h1 hS hX hVO hBC hb hb1
    have hL : fixSub ((kerQuotImg M X (conjSubgroup V₀ g)).map ρ) =
        CFSG.Goldschmidt.G2.sub (eSub V₀ X T)
          (Subgroup.centralizer (conjSubgroup V₀ g : Set G)) := by
      unfold kerQuotImg
      rw [Subgroup.map_map,
        show (ρ.comp (kerQuotMk M X)) = eRep V₀ X T from MonoidHom.ext hρ]
      exact fixSub_map_eRep hB
    have hR : fixSub ((Subgroup.zpowers a).map ρ) =
        CFSG.Goldschmidt.G2.sub (eSub V₀ X T)
          (Subgroup.centralizer ({(y : G)} : Set G)) := by
      rw [MonoidHom.map_zpowers, ← hyeq, hρ y]
      exact fixSub_zpowers_eRep y
    rw [hL, hR]
    rw [← CFSG.Goldschmidt.G2.sub_inf_self (A := eSub V₀ X T)
          (H := Subgroup.centralizer (conjSubgroup V₀ g : Set G))]
    rw [← CFSG.Goldschmidt.G2.sub_inf_self (A := eSub V₀ X T)
          (H := Subgroup.centralizer ({(y : G)} : Set G))]
    rw [hinf]
  have hAU : kerQuotImg M X (conjSubgroup V₀ g) ≤ kerQuotImg M X (conjSubgroup V g) :=
    kerQuotImg_mono (E3.conjSubgroup_mono_left g hX.cex.hyp.h6.le)
  obtain ⟨S, hSB⟩ := exists_sylow_of_isBorelIn hBorel
  have hUO : kerQuotImg M X (conjSubgroup V g) ≤ pCoreOf 2 (kerQuotImg M X M) := by
    have hAM : kerQuotImg M X (conjSubgroup V g) ≤ kerQuotImg M X M :=
      kerQuotImg_mono hpair.A_le_M
    have hAN : kerQuotImg M X (conjSubgroup V g) ≤
        Subgroup.normalizer ((S : Subgroup (KerQuot M X)) : Set (KerQuot M X)) :=
      hAM.trans (le_of_eq hSB)
    have hAS : kerQuotImg M X (conjSubgroup V g) ≤ (S : Subgroup (KerQuot M X)) :=
      le_sylow_of_le_normalizer (isElemAbelian_kerQuotImg hA).isPGroup hAN
    have hSp : (S : Subgroup (KerQuot M X)) ≤ pCoreOf 2 (kerQuotImg M X M) := by
      rw [hSB]
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        Subgroup.le_normalizer le_rfl S.isPGroup'
    exact hAS.trans hSp
  have hIn : InCalAMod ρ (Min.min (E3.mQuot V (U ⊔ V₀) + mSub V₀)
      (mBar M V₀ V hX.cex.hyp.h6.elemAbelian))
      (kerQuotImg M X (conjSubgroup V g)) :=
    Hyp167.inCalAMod_kerQuotImg h1 hS hV₀ hX hBE hρ
  have hNot : ¬ InCalAMod ρ (mSub V₀ + 1) (kerQuotImg M X (conjSubgroup V g)) :=
    twelveFour h12 hCA hZ hAU hUO
  have hminle : Min.min (E3.mQuot V (U ⊔ V₀) + mSub V₀)
      (mBar M V₀ V hX.cex.hyp.h6.elemAbelian) ≤ mSub V₀ := by
    by_contra hlt
    have hle : mSub V₀ + 1 ≤ Min.min (E3.mQuot V (U ⊔ V₀) + mSub V₀)
        (mBar M V₀ V hX.cex.hyp.h6.elemAbelian) := by
      have := not_le.1 hlt
      omega
    refine hNot ?_
    obtain ⟨hne, hel, hfix⟩ := hIn
    exact ⟨hne, hel, fun D hD hrel => hfix D hD
      (lt_of_lt_of_le hrel (Nat.pow_le_pow_right (by norm_num) hle))⟩
  have hmbarle : mBar M V₀ V hX.cex.hyp.h6.elemAbelian ≤ mSub V₀ := by
    rcases min_le_iff.1 hminle with h | h
    · have h1n := Cex16.one_le_n h152 hX.cex
      omega
    · exact h
  exact lt_of_lt_of_le (Cex16.n_lt_mBar hX.cex) hmbarle

end CFSG.LocalAnalysis.WeakClosure81

end
