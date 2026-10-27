module

public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneFive
import CFSG.LocalAnalysis.StandardType.ZS.Flag
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneTwo
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

structure LemmaOneSixSetting (F H : Subgroup (U ≃ₗ[ZMod p] U)) (a : U ≃ₗ[ZMod p] U) (l : ℕ) :
    Prop where
  eq_closure : F = Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U)))
  transvectionFree : QTwoLin.TransvectionFree F
  isRefl : IsRefl p a
  reflGen : ReflGen p H
  splitSupport : SplitSupport H l
  maximal : ∀ K : Subgroup (U ≃ₗ[ZMod p] U), K ≤ F → H ≤ K → ReflGen p K → SplitSupport K l →
    K = H
  dLarge : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)
  finrank_eq : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) = l + 1
  degenerate : IsDegenerate F H

namespace LemmaOneSixSetting

variable {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U} {l : ℕ}

open Module in
private abbrev zsr8A_VF (F : Subgroup (U ≃ₗ[ZMod p] U)) : Submodule (ZMod p) U :=
  HardMathSupport.Kantor79.commutatorSpace F

open Module in
private abbrev zsr8A_Vc (F : Subgroup (U ≃ₗ[ZMod p] U)) : Submodule (ZMod p) U :=
  centralizerSpace F

open Module in
private abbrev zsr8A_W (F : Subgroup (U ≃ₗ[ZMod p] U)) : Submodule (ZMod p) U :=
  zsr8A_VF F ⊓ zsr8A_Vc F

open Module in
private abbrev zsr8A_V0 (F : Subgroup (U ≃ₗ[ZMod p] U)) : Submodule (ZMod p) U :=
  zsr8A_VF F ⊔ zsr8A_Vc F

open Module in
private theorem zsr8A_mem_commutatorSpace_of_mem {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {g : U ≃ₗ[ZMod p] U} (hg : g ∈ F) {v : U} (hv : v ∈ zsr8A_VF F) :
    g v ∈ zsr8A_VF F := by
  have h := Submodule.mem_map_of_mem (f := (g : U →ₗ[ZMod p] U)) hv
  rwa [map_commutatorSpace_of_mem_normalizer (H := F) (Subgroup.le_normalizer hg)] at h

open Module in
private theorem zsr8A_inf_eq_bot_of_not_le_of_finrank_eq_one
    {L W : Submodule (ZMod p) U} (hL : Module.finrank (ZMod p) L = 1)
    (h : ¬ L ≤ W) : L ⊓ W = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  by_contra hx0
  exact h (by
    rw [eq_span_singleton_of_mem_of_finrank_eq_one hL hx.1 hx0]
    exact Submodule.span_le.mpr (by rintro y rfl; exact hx.2))

open Module in
private theorem zsr8A_finrank_centralizerSpace_eq (hS : LemmaOneSixSetting F H a l)
    [Module.Finite (ZMod p) U] :
    Module.finrank (ZMod p) (centralizerSpace H) = Module.finrank (ZMod p) U - l := by
  have hcompl := hS.splitSupport.1
  have hdimH := hS.splitSupport.2.1
  have h := Submodule.finrank_sup_add_finrank_inf_eq
      (HardMathSupport.Kantor79.commutatorSpace H) (centralizerSpace H)
  rw [hcompl.inf_eq_bot, hcompl.sup_eq_top, finrank_bot, finrank_top, hdimH] at h
  omega

open Module in
private theorem zsr8A_finrank_ker_sub_one (hS : LemmaOneSixSetting F H a l)
    [Module.Finite (ZMod p) U] :
    Module.finrank (ZMod p) (LinearMap.ker ((a : U →ₗ[ZMod p] U) - 1)) =
      Module.finrank (ZMod p) U - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker ((a : U →ₗ[ZMod p] U) - 1)
  have hr : Module.finrank (ZMod p)
      (LinearMap.range ((a : U →ₗ[ZMod p] U) - 1)) = 1 := by
    rw [← HardMathSupport.Kantor79.movedSpace]
    exact hS.isRefl.2
  rw [hr] at h
  omega

open Module in
private theorem zsr8A_centralizerSpace_inf_le (hS : LemmaOneSixSetting F H a l) :
    centralizerSpace H ⊓ LinearMap.ker ((a : U →ₗ[ZMod p] U) - 1) ≤
      centralizerSpace F := by
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hvH, hva⟩ := hv
  rw [mem_centralizerSpace] at hvH ⊢
  have hva' : a v = v := by
    simpa [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] using hva
  rw [hS.eq_closure]
  intro f hf
  induction hf using Subgroup.closure_induction with
  | mem y hy =>
      rw [Set.mem_insert_iff] at hy
      rcases hy with rfl | hy
      · exact hva'
      · exact hvH y hy
  | one => rfl
  | mul y z hy hz ihy ihz => rw [LinearEquiv.mul_apply, ihz, ihy]
  | inv y hy ihy =>
      calc y⁻¹ v = y⁻¹ (y v) := by rw [ihy]
        _ = v := LinearEquiv.symm_apply_apply y v

open Module in
private def zsr8A_kerSub (F : Subgroup (U ≃ₗ[ZMod p] U)) :
    Subgroup (U ≃ₗ[ZMod p] U) where
  carrier := {t | t ∈ F ∧ ∀ v ∈ zsr8A_VF F, t v - v ∈ zsr8A_Vc F}
  one_mem' := by
    refine ⟨F.one_mem, fun v _ => ?_⟩
    simp
  mul_mem' := by
    rintro s t ⟨hsF, hs⟩ ⟨htF, ht⟩
    refine ⟨F.mul_mem hsF htF, fun v hv => ?_⟩
    have htv : t v ∈ zsr8A_VF F := zsr8A_mem_commutatorSpace_of_mem htF hv
    have h1 := hs (t v) htv
    have h2 := ht v hv
    have heq : (s * t) v - v = (s (t v) - t v) + (t v - v) := by
      rw [LinearEquiv.mul_apply]
      abel
    rw [heq]
    exact (zsr8A_Vc F).add_mem h1 h2
  inv_mem' := by
    rintro s ⟨hsF, hs⟩
    refine ⟨F.inv_mem hsF, fun v hv => ?_⟩
    have hsv : s v - v ∈ zsr8A_Vc F := hs v hv
    have hfix : s⁻¹ (s v - v) = s v - v :=
      (mem_centralizerSpace.mp hsv) s⁻¹ (F.inv_mem hsF)
    have heq : s⁻¹ v - v = -(s v - v) := by
      have h1 : s⁻¹ (s v) = v := by
        change s.symm (s v) = v
        exact LinearEquiv.symm_apply_apply s v
      calc s⁻¹ v - v = s⁻¹ v - s⁻¹ (s v) := by rw [h1]
        _ = s⁻¹ (v - s v) := by rw [map_sub]
        _ = s⁻¹ (-(s v - v)) := by congr 1; abel
        _ = -s⁻¹ (s v - v) := by rw [map_neg]
        _ = -(s v - v) := by rw [hfix]
    rw [heq]
    exact (zsr8A_Vc F).neg_mem hsv

open Module in
private theorem zsr8A_mem_kerSection {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {t : U ≃ₗ[ZMod p] U} (ht : t ∈ kerSection F) :
    t ∈ F ∧ ∀ v ∈ zsr8A_VF F, t v - v ∈ zsr8A_Vc F := by
  have hle : kerSection F ≤ zsr8A_kerSub F := by
    unfold kerSection
    exact (Subgroup.closure_le (zsr8A_kerSub F)).mpr fun t ht => ht
  exact hle ht

open Module in
private theorem zsr8A_moved_into_W {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {t : U ≃ₗ[ZMod p] U} (htF : t ∈ F)
    (htV : ∀ v ∈ zsr8A_VF F, t v - v ∈ zsr8A_Vc F) :
    ∀ v ∈ zsr8A_V0 F, t v - v ∈ zsr8A_W F := by
  intro v hv
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hv
  have htx : t x - x ∈ zsr8A_Vc F := htV x hx
  have htxV : t x - x ∈ zsr8A_VF F :=
    (zsr8A_VF F).sub_mem (zsr8A_mem_commutatorSpace_of_mem htF hx) hx
  have hty : t y = y := (mem_centralizerSpace.mp hy) t htF
  have heq : t v - v = t x - x := by
    rw [← hxy, map_add, hty]
    abel
  rw [heq]
  exact ⟨htxV, htx⟩

open Module in
private theorem zsr8A_V0_ne_top (hS : LemmaOneSixSetting F H a l) :
    zsr8A_V0 F ≠ ⊤ := by
  intro htop
  obtain ⟨t, htF, ht1, htV⟩ := hS.degenerate.2.2
  have hfix : ∀ w ∈ zsr8A_W F, t w = w := fun w hw =>
    (mem_centralizerSpace.mp hw.2) t htF
  have hquot : ∀ v : U, t v - v ∈ zsr8A_W F := by
    intro v
    have hv : v ∈ zsr8A_V0 F := by rw [htop]; exact Submodule.mem_top
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hv
    have htx : t x - x ∈ zsr8A_Vc F := htV x hx
    have htxV : t x - x ∈ zsr8A_VF F :=
      (zsr8A_VF F).sub_mem (zsr8A_mem_commutatorSpace_of_mem htF hx) hx
    have hty : t y = y := (mem_centralizerSpace.mp hy) t htF
    have heq : t v - v = t x - x := by
      rw [← hxy, map_add, hty]
      abel
    rw [heq]
    exact ⟨htxV, htx⟩
  have h1 : t = 1 := eq_one_of_forall_sub_mem_of_finrank_eq_one (A := F)
    (W := zsr8A_W F) hS.transvectionFree hS.degenerate.1 htF hfix hquot
  exact ht1 h1

open Module in
private theorem zsr8A_finrank_sup_eq {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U} {l : ℕ}
    (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2) [Module.Finite (ZMod p) U] :
    Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) =
        Module.finrank (ZMod p) U - 1 := by
  have := hp
  have hVH : Module.finrank (ZMod p) (zsr8A_Vc H) = Module.finrank (ZMod p) U - l :=
    zsr8A_finrank_centralizerSpace_eq hS
  have hKer : Module.finrank (ZMod p)
      (LinearMap.ker ((a : U →ₗ[ZMod p] U) - 1)) = Module.finrank (ZMod p) U - 1 :=
    zsr8A_finrank_ker_sub_one hS
  have hle : zsr8A_Vc H ⊓ LinearMap.ker ((a : U →ₗ[ZMod p] U) - 1) ≤ zsr8A_Vc F :=
    zsr8A_centralizerSpace_inf_le hS
  have hstep1 : (Module.finrank (ZMod p) U - l) + (Module.finrank (ZMod p) U - 1) ≤
      Module.finrank (ZMod p) U + Module.finrank (ZMod p) (zsr8A_Vc F) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (zsr8A_Vc H)
        (LinearMap.ker ((a : U →ₗ[ZMod p] U) - 1))
    have hsup : Module.finrank (ZMod p)
        ↥(zsr8A_Vc H ⊔ LinearMap.ker ((a : U →ₗ[ZMod p] U) - 1)) ≤
        Module.finrank (ZMod p) U := Submodule.finrank_le _
    have hinf : Module.finrank (ZMod p)
        ↥(zsr8A_Vc H ⊓ LinearMap.ker ((a : U →ₗ[ZMod p] U) - 1)) ≤
        Module.finrank (ZMod p) (zsr8A_Vc F) := Submodule.finrank_mono hle
    rw [hVH, hKer] at h
    omega
  have hstep2 : Module.finrank (ZMod p) (zsr8A_V0 F) + 1 =
      (l + 1) + Module.finrank (ZMod p) (zsr8A_Vc F) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (zsr8A_VF F) (zsr8A_Vc F)
    rw [hS.degenerate.1, hS.finrank_eq] at h
    simpa [zsr8A_V0] using h
  have hne : zsr8A_V0 F ≠ ⊤ := zsr8A_V0_ne_top hS
  have hlt : Module.finrank (ZMod p) (zsr8A_V0 F) < Module.finrank (ZMod p) U :=
    Submodule.finrank_lt hne
  have hlefin : Module.finrank (ZMod p) (zsr8A_V0 F) ≤ Module.finrank (ZMod p) U :=
    Submodule.finrank_le _
  change Module.finrank (ZMod p) (zsr8A_V0 F) = Module.finrank (ZMod p) U - 1
  omega

open Module in
private theorem zsr8A_isTransvectionLin_of_finrank_movedSpace_eq_one
    {t : U ≃ₗ[ZMod p] U}
    (hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 1)
    (hfix : ∀ x ∈ HardMathSupport.Kantor79.movedSpace t, t x = x) (ht : t ≠ 1) :
    QTwoLin.IsTransvectionLin t := by
  have hne : HardMathSupport.Kantor79.movedSpace t ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hfin
    exact Nat.zero_ne_one hfin
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hspan : HardMathSupport.Kantor79.movedSpace t = Submodule.span (ZMod p) {u} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfin hu hu0
  let Φ : U →ₗ[ZMod p] (Submodule.span (ZMod p) {u}) :=
    LinearMap.codRestrict (Submodule.span (ZMod p) {u}) ((t : U →ₗ[ZMod p] U) - 1)
      fun v => by rw [← hspan]; exact ⟨v, rfl⟩
  let ψ : U →ₗ[ZMod p] (ZMod p) :=
    (LinearEquiv.toSpanNonzeroSingleton (ZMod p) U u hu0).symm.toLinearMap.comp Φ
  have hψ : ∀ v, ψ v • u = t v - v := by
    intro v
    have h := LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul (R := ZMod p) (M := U) u hu0
      (Φ v)
    simp only [ψ, LinearEquiv.coe_toLinearMap, LinearMap.comp_apply] at h ⊢
    rw [h]
    rfl
  have hψ0 : ψ u = 0 := by
    have h := hψ u
    rw [hfix u hu, sub_self] at h
    exact (smul_eq_zero.mp h).resolve_right hu0
  have hψne : ψ ≠ 0 := by
    intro hzero
    apply ht
    ext v
    have h := hψ v
    rw [hzero, LinearMap.zero_apply, zero_smul] at h
    exact sub_eq_zero.mp h.symm
  exact ⟨u, ψ, hu0, hψne, hψ0, fun v => by rw [hψ v]; abel⟩

open Module in
private theorem zsr8A_t_fixes_movedSpace_of_finrank_eq_one
    {F : Subgroup (U ≃ₗ[ZMod p] U)} {t : U ≃ₗ[ZMod p] U} (htF : t ∈ F)
    (htV : ∀ v ∈ zsr8A_VF F, t v - v ∈ zsr8A_Vc F)
    (hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 1) :
    ∀ x ∈ HardMathSupport.Kantor79.movedSpace t, t x = x := by
  have hsub : ∀ y ∈ HardMathSupport.Kantor79.movedSpace t,
      t y - y ∈ HardMathSupport.Kantor79.movedSpace t ⊓ zsr8A_W F := by
    intro y hy
    have hyV : y ∈ zsr8A_VF F :=
      HardMathSupport.Kantor79.movedSpace_le_commutatorSpace htF hy
    refine ⟨⟨y, rfl⟩, ?_⟩
    exact ⟨(zsr8A_VF F).sub_mem (zsr8A_mem_commutatorSpace_of_mem htF hyV) hyV,
      htV y hyV⟩
  intro x hx
  by_cases hLW : HardMathSupport.Kantor79.movedSpace t ≤ zsr8A_W F
  · exact (mem_centralizerSpace.mp (hLW hx).2) t htF
  · have hbot := zsr8A_inf_eq_bot_of_not_le_of_finrank_eq_one hfin hLW
    have hy := hsub x hx
    rw [hbot] at hy
    simpa [sub_eq_zero] using hy

open Module in
private theorem zsr8A_movedSpace_le_sup_span
    {F : Subgroup (U ≃ₗ[ZMod p] U)} {t : U ≃ₗ[ZMod p] U}
    (htW : ∀ v ∈ zsr8A_V0 F, t v - v ∈ zsr8A_W F)
    {u₀ : U} (hu₀ : zsr8A_V0 F ⊔ Submodule.span (ZMod p) {u₀} = ⊤) :
    HardMathSupport.Kantor79.movedSpace t ≤
      zsr8A_W F ⊔ Submodule.span (ZMod p) {((t : U →ₗ[ZMod p] U) u₀ - u₀)} := by
  rintro y ⟨v, rfl⟩
  change t v - v ∈ zsr8A_W F ⊔
    Submodule.span (ZMod p) {((t : U →ₗ[ZMod p] U) u₀ - u₀)}
  have hv : v ∈ zsr8A_V0 F ⊔ Submodule.span (ZMod p) {u₀} := by
    rw [hu₀]; exact Submodule.mem_top
  obtain ⟨w, hw, z, hz, hwz⟩ := Submodule.mem_sup.mp hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
  have hwW : t w - w ∈ zsr8A_W F := htW w hw
  have heq : t v - v = (t w - w) + c • (t u₀ - u₀) := by
    rw [← hwz, ← hc, map_add, map_smul, smul_sub]
    abel_nf
  rw [heq]
  exact Submodule.add_mem_sup hwW
    (Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _)))

open Module in
private theorem zsr8A_exists_u0_sup_V0 {p : ℕ} [Fact p.Prime] {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] {F H : Subgroup (U ≃ₗ[ZMod p] U)}
    {a : U ≃ₗ[ZMod p] U} {l : ℕ} (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] :
    ∃ u₀ : U, zsr8A_V0 F ⊔ Submodule.span (ZMod p) {u₀} = ⊤ := by
  have hV0ne : zsr8A_V0 F ≠ ⊤ := zsr8A_V0_ne_top hS
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : U, u₀ ∉ zsr8A_V0 F := by
    by_contra h
    push Not at h
    exact hV0ne (Submodule.eq_top_iff'.mpr h)
  refine ⟨u₀, ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  have hsp := Submodule.finrank_sup_span_singleton (K := ZMod p) (p := zsr8A_V0 F) hu₀
  have hfin : Module.finrank (ZMod p) (zsr8A_V0 F) = Module.finrank (ZMod p) U - 1 :=
    zsr8A_finrank_sup_eq hS hp
  have hn : 1 ≤ Module.finrank (ZMod p) U := by
    have h1' : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace a) = 1 :=
      hS.isRefl.2
    have h2' := Submodule.finrank_le (HardMathSupport.Kantor79.movedSpace a)
    omega
  rw [hsp, hfin]
  omega

private theorem zsr8A_exists_moved_VF {p : ℕ} [Fact p.Prime] {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {t : U ≃ₗ[ZMod p] U} (htF : t ∈ F) {u₀ : U}
    (hV0top : zsr8A_V0 F ⊔ Submodule.span (ZMod p) {u₀} = ⊤)
    (hspanle : Module.finrank (ZMod p)
      (Submodule.span (ZMod p) {((t : U →ₗ[ZMod p] U) u₀ - u₀)}) ≤ 1)
    (hfin2 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 2) :
    ∃ v ∈ zsr8A_VF F, t v ≠ v := by
  by_contra h
  push Not at h
  have hsub : HardMathSupport.Kantor79.movedSpace t ≤
      Submodule.span (ZMod p) {((t : U →ₗ[ZMod p] U) u₀ - u₀)} := by
    rintro y ⟨v, rfl⟩
    change t v - v ∈ Submodule.span (ZMod p) {((t : U →ₗ[ZMod p] U) u₀ - u₀)}
    have hv : v ∈ zsr8A_V0 F ⊔ Submodule.span (ZMod p) {u₀} := by
      rw [hV0top]; exact Submodule.mem_top
    obtain ⟨w, hw, z, hz, hwz⟩ := Submodule.mem_sup.mp hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
    have hwfix : t w = w := by
      obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hw
      rw [← hxy, map_add, h x hx, (mem_centralizerSpace.mp hy) t htF]
    have heq : t v - v = c • (t u₀ - u₀) := by
      rw [← hwz, ← hc, map_add, map_smul, hwfix, smul_sub]
      abel_nf
    rw [heq]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))
  have hle1 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) ≤ 1 := by
    have h1' := Submodule.finrank_mono hsub
    omega
  omega

private theorem zsr8A_finrank_movedSpace_of_mem_kerSection {p : ℕ} [Fact p.Prime] {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] {F H : Subgroup (U ≃ₗ[ZMod p] U)}
    {a : U ≃ₗ[ZMod p] U} {l : ℕ} (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {t : U ≃ₗ[ZMod p] U} (ht : t ∈ kerSection F) (h1 : t ≠ 1) :
    (∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F,
        t v - v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) ∧
      Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 2 ∧
      ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace F, t v ≠ v := by
  obtain ⟨htF, htV⟩ := zsr8A_mem_kerSection ht
  have htW : ∀ v ∈ zsr8A_V0 F, t v - v ∈ zsr8A_W F := zsr8A_moved_into_W htF htV
  obtain ⟨u₀, hV0top⟩ := zsr8A_exists_u0_sup_V0 hS hp
  have hle := zsr8A_movedSpace_le_sup_span htW hV0top
  have hWfin : Module.finrank (ZMod p) (zsr8A_W F) = 1 := hS.degenerate.1
  have hspanle : Module.finrank (ZMod p)
      (Submodule.span (ZMod p) {((t : U →ₗ[ZMod p] U) u₀ - u₀)}) ≤ 1 := by
    have := finrank_span_le_card (R := ZMod p)
      ({((t : U →ₗ[ZMod p] U) u₀ - u₀)} : Set U)
    simpa using this
  have hup : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) ≤ 2 := by
    have h1' := Submodule.finrank_mono hle
    have h2' := Submodule.finrank_add_le_finrank_add_finrank (zsr8A_W F)
      (Submodule.span (ZMod p) {((t : U →ₗ[ZMod p] U) u₀ - u₀)})
    omega
  have hne : HardMathSupport.Kantor79.movedSpace t ≠ ⊥ := by
    intro hbot
    apply h1
    ext v
    have hmem : t v - v ∈ HardMathSupport.Kantor79.movedSpace t := ⟨v, rfl⟩
    rw [hbot] at hmem
    simpa [sub_eq_zero] using hmem
  have hone : 1 ≤ Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) :=
    Submodule.one_le_finrank_iff.mpr hne
  have h1fin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) ≠ 1 := by
    intro hf1
    have hfix := zsr8A_t_fixes_movedSpace_of_finrank_eq_one htF htV hf1
    have htv := zsr8A_isTransvectionLin_of_finrank_movedSpace_eq_one hf1 hfix h1
    exact hS.transvectionFree t htF htv
  have hfin2 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 2 := by
    omega
  exact ⟨htW, hfin2, zsr8A_exists_moved_VF htF hV0top hspanle hfin2⟩

open Module in
open CFSG.HardMathSupport.Kantor79 in
private theorem zsr8C_mem_kerSection {F : Subgroup (U ≃ₗ[ZMod p] U)} {t : U ≃ₗ[ZMod p] U}
    (ht : t ∈ kerSection F) :
    t ∈ F ∧ ∀ v ∈ commutatorSpace F, t v - v ∈ centralizerSpace F := by
  let S : Subgroup (U ≃ₗ[ZMod p] U) :=
    { carrier := {t | t ∈ F ∧ ∀ v ∈ commutatorSpace F, t v - v ∈ centralizerSpace F}
      one_mem' := ⟨F.one_mem, by intro v _; simp⟩
      mul_mem' := by
        rintro a b ⟨haF, ha⟩ ⟨hbF, hb⟩
        refine ⟨F.mul_mem haF hbF, fun v hv => ?_⟩
        have hbv : b v ∈ commutatorSpace F := by
          have hmap := map_commutatorSpace_of_mem_normalizer (Subgroup.le_normalizer hbF)
          rw [← hmap]
          exact Submodule.mem_map_of_mem (f := (b : U →ₗ[ZMod p] U)) hv
        have h1 : a (b v) - b v ∈ centralizerSpace F := ha (b v) hbv
        have h2 : b v - v ∈ centralizerSpace F := hb v hv
        rw [LinearEquiv.mul_apply]
        rw [show a (b v) - v = (a (b v) - b v) + (b v - v) by abel]
        exact (centralizerSpace F).add_mem h1 h2
      inv_mem' := by
        rintro a ⟨haF, ha⟩
        refine ⟨F.inv_mem haF, fun v hv => ?_⟩
        have hav : a.symm v ∈ commutatorSpace F := by
          have hmap := map_commutatorSpace_of_mem_normalizer
            (Subgroup.le_normalizer (F.inv_mem haF))
          rw [← hmap]
          exact Submodule.mem_map_of_mem (f := (a.symm : U →ₗ[ZMod p] U)) hv
        have h1 : a (a.symm v) - a.symm v ∈ centralizerSpace F := ha (a.symm v) hav
        rw [LinearEquiv.apply_symm_apply] at h1
        change a.symm v - v ∈ centralizerSpace F
        rw [show a.symm v - v = -(v - a.symm v) by abel]
        exact (centralizerSpace F).neg_mem h1 }
  exact (Subgroup.closure_le (K := S)).mpr (fun x hx => hx) ht

open Module in
open CFSG.HardMathSupport.Kantor79 in
private theorem zsr8C_movedSpace_mul_le (x y : U ≃ₗ[ZMod p] U) :
    movedSpace (x * y) ≤ movedSpace x ⊔ movedSpace y := by
  rintro w ⟨v, rfl⟩
  change x (y v) - v ∈ movedSpace x ⊔ movedSpace y
  rw [show x (y v) - v = (x (y v) - y v) + (y v - v) by abel]
  exact Submodule.add_mem_sup ⟨y v, rfl⟩ ⟨v, rfl⟩

open Module in
open CFSG.HardMathSupport.Kantor79 in
private theorem zsr8C_movedSpace_conj_le {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {t h : U ≃ₗ[ZMod p] U} (htF : t ∈ F)
    (htv : ∀ v ∈ commutatorSpace F, t v - v ∈ centralizerSpace F) (hhF : h ∈ F) :
    movedSpace (t * h * t⁻¹) ≤ movedSpace h ⊔ (commutatorSpace F ⊓ centralizerSpace F) := by
  rintro w ⟨v, rfl⟩
  change t (h (t.symm v)) - v ∈ movedSpace h ⊔ (commutatorSpace F ⊓ centralizerSpace F)
  set u : U := h (t.symm v) - t.symm v with hu
  have hu_mem : u ∈ movedSpace h := ⟨t.symm v, rfl⟩
  have hu_V : u ∈ commutatorSpace F := movedSpace_le_commutatorSpace hhF hu_mem
  have htu_V : t u ∈ commutatorSpace F := by
    have hmap := map_commutatorSpace_of_mem_normalizer (Subgroup.le_normalizer htF)
    rw [← hmap]
    exact Submodule.mem_map_of_mem (f := (t : U →ₗ[ZMod p] U)) hu_V
  have hdiff : t u - u ∈ commutatorSpace F ⊓ centralizerSpace F :=
    ⟨(commutatorSpace F).sub_mem htu_V hu_V, htv u hu_V⟩
  have hw : t (h (t.symm v)) - v = t u := by
    rw [hu, map_sub, LinearEquiv.apply_symm_apply]
  rw [hw, show t u = u + (t u - u) by abel]
  exact Submodule.add_mem_sup hu_mem hdiff

open Module in
open CFSG.HardMathSupport.Kantor79 in
private theorem zsr8C_movedSpace_one :
    movedSpace (1 : U ≃ₗ[ZMod p] U) = ⊥ := by
  rw [movedSpace, LinearMap.range_eq_bot]
  ext v
  simp

open Module in
open CFSG.HardMathSupport.Kantor79 in
private theorem zsr8C_isTransvectionLin_of_det_eq_one [Module.Finite (ZMod p) U]
    {g : U ≃ₗ[ZMod p] U}
    (hfin : Module.finrank (ZMod p) (movedSpace g) = 1)
    (hdet : LinearEquiv.det g = 1) : QTwoLin.IsTransvectionLin g := by
  have hle : Module.finrank (ZMod p)
      (LinearMap.range ((g : U →ₗ[ZMod p] U) - 1)) ≤ 1 := hfin.le
  have hdil : g ∈ LinearEquiv.dilatransvections (ZMod p) U := by
    rw [LinearEquiv.mem_dilatransvections_iff_finrank]
    exact hle
  obtain ⟨f, v, hg_eq⟩ := hdil
  have hfv : f v = 0 := by
    have h1 : LinearMap.det (g : U →ₗ[ZMod p] U) = 1 := by
      rw [← LinearEquiv.coe_det g]
      exact congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hdet
    rw [hg_eq, LinearMap.transvection.det] at h1
    have h1' : (1 : ZMod p) + f v = 1 + 0 := by simpa using h1
    exact add_left_cancel h1'
  have hg1_of : v = 0 ∨ f = 0 → g = 1 := by
    rintro (rfl | hf0)
    · ext x
      change (g : U →ₗ[ZMod p] U) x = x
      rw [hg_eq, LinearMap.transvection.apply]
      simp
    · ext x
      change (g : U →ₗ[ZMod p] U) x = x
      rw [hg_eq, LinearMap.transvection.apply, hf0]
      simp
  have hv : v ≠ 0 := by
    rintro rfl
    rw [hg1_of (Or.inl rfl), zsr8C_movedSpace_one, finrank_bot] at hfin
    omega
  have hf : f ≠ 0 := by
    rintro hf0
    rw [hg1_of (Or.inr hf0), zsr8C_movedSpace_one, finrank_bot] at hfin
    omega
  exact ⟨v, f, hv, hf, hfv, fun x => by
    change (g : U →ₗ[ZMod p] U) x = x + f x • v
    rw [hg_eq, LinearMap.transvection.apply]⟩

open Module in
open CFSG.HardMathSupport.Kantor79 in
private theorem zsr8C_eq_one_of_movedSpace_eq_bot {g : U ≃ₗ[ZMod p] U}
    (h : movedSpace g = ⊥) : g = 1 := by
  have h0 : ((g : U →ₗ[ZMod p] U) - 1) = 0 := by
    rw [movedSpace] at h
    exact LinearMap.range_eq_bot.mp h
  have h1 : (g : U →ₗ[ZMod p] U) = 1 := sub_eq_zero.mp h0
  exact LinearEquiv.toLinearMap_injective h1

open Module in
open CFSG.HardMathSupport.Kantor79 in
private theorem zsr8C_movedSpace_commutatorElement_ge {p : ℕ} [Fact p.Prime] {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] {F H : Subgroup (U ≃ₗ[ZMod p] U)}
    {a : U ≃ₗ[ZMod p] U} {l : ℕ} (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {t h : U ≃ₗ[ZMod p] U} (htF : t ∈ F) (hhF : h ∈ F)
    (hh' : IsRefl p h) (hs : t * h * t⁻¹ * h⁻¹ ≠ 1)
    (hle : movedSpace (t * h * t⁻¹ * h⁻¹) ≤ movedSpace h ⊔
      (commutatorSpace F ⊓ centralizerSpace F)) :
    movedSpace h ⊔ (commutatorSpace F ⊓ centralizerSpace F) ≤
      movedSpace (t * h * t⁻¹ * h⁻¹) := by
  set W : Submodule (ZMod p) U :=
    HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F with hW
  by_contra hnot
  have hlt : movedSpace (t * h * t⁻¹ * h⁻¹) < movedSpace h ⊔ W :=
    lt_of_le_of_ne hle (fun heq => hnot heq.ge)
  have hfin2 : Module.finrank (ZMod p) (movedSpace h ⊔ W : Submodule (ZMod p) U) ≤ 2 := by
    have h1 : Module.finrank (ZMod p) (movedSpace h) = 1 := hh'.2
    have h2 : Module.finrank (ZMod p) W = 1 := hS.degenerate.1
    have h3 := Submodule.finrank_add_le_finrank_add_finrank (movedSpace h) W
    omega
  have hfin_le : Module.finrank (ZMod p) (movedSpace (t * h * t⁻¹ * h⁻¹)) ≤ 1 := by
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hne_bot : movedSpace (t * h * t⁻¹ * h⁻¹) ≠ ⊥ := by
    intro hbot
    exact hs (zsr8C_eq_one_of_movedSpace_eq_bot hbot)
  have hfin_ge : 1 ≤ Module.finrank (ZMod p) (movedSpace (t * h * t⁻¹ * h⁻¹)) := by
    by_contra hc
    have h0 : Module.finrank (ZMod p) (movedSpace (t * h * t⁻¹ * h⁻¹)) = 0 := by omega
    exact hne_bot (Submodule.finrank_eq_zero.mp h0)
  have hfin1 : Module.finrank (ZMod p) (movedSpace (t * h * t⁻¹ * h⁻¹)) = 1 := by
    omega
  have hdet : LinearEquiv.det (t * h * t⁻¹ * h⁻¹) = 1 := by
    have hh_det : LinearEquiv.det h = -1 := det_eq_neg_one_of_isRefl hp hh'
    have hconj : LinearEquiv.det (t * h * t⁻¹) = -1 := by
      rw [map_mul, map_mul, map_inv, hh_det, mul_assoc, mul_comm (-1) (LinearEquiv.det t)⁻¹,
        ← mul_assoc, mul_inv_cancel, one_mul]
    rw [map_mul, hconj, map_inv, hh_det]
    exact mul_inv_cancel (-1)
  have htv' : QTwoLin.IsTransvectionLin (t * h * t⁻¹ * h⁻¹) :=
    zsr8C_isTransvectionLin_of_det_eq_one hfin1 hdet
  have hsF : t * h * t⁻¹ * h⁻¹ ∈ F :=
    F.mul_mem (F.mul_mem (F.mul_mem htF hhF) (F.inv_mem htF)) (F.inv_mem hhF)
  exact (hS.transvectionFree _ hsF) htv'

open Module in
open CFSG.HardMathSupport.Kantor79 in
private theorem zsr8C_movedSpace_commutatorElement {p : ℕ} [Fact p.Prime] {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] {F H : Subgroup (U ≃ₗ[ZMod p] U)}
    {a : U ≃ₗ[ZMod p] U} {l : ℕ}
    (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {t h : U ≃ₗ[ZMod p] U} (ht : t ∈ kerSection F) (hh : h ∈ H)
    (hh' : IsRefl p h) (hs : t * h * t⁻¹ * h⁻¹ ≠ 1) :
    HardMathSupport.Kantor79.movedSpace (t * h * t⁻¹ * h⁻¹) =
      HardMathSupport.Kantor79.movedSpace h ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) := by
  obtain ⟨htF, htv⟩ := zsr8C_mem_kerSection ht
  have hHF : H ≤ F := by
    rw [hS.eq_closure]
    intro x hx
    exact Subgroup.subset_closure (Set.mem_insert_of_mem a hx)
  have hhF : h ∈ F := hHF hh
  have hh_inv : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh'.1
  set W : Submodule (ZMod p) U :=
    HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F with hW
  have hle : movedSpace (t * h * t⁻¹ * h⁻¹) ≤ movedSpace h ⊔ W := by
    rw [hh_inv]
    calc movedSpace (t * h * t⁻¹ * h)
        = movedSpace ((t * h * t⁻¹) * h) := rfl
      _ ≤ movedSpace (t * h * t⁻¹) ⊔ movedSpace h := zsr8C_movedSpace_mul_le _ _
      _ ≤ movedSpace h ⊔ W :=
          sup_le (zsr8C_movedSpace_conj_le htF htv hhF) le_sup_left
  exact le_antisymm hle (zsr8C_movedSpace_commutatorElement_ge hS hp htF hhF hh' hs hle)

private theorem eq_of_finrank_eq_one_of_le [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {A B : Submodule (ZMod p) U}
    (hA : A ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (hB : B ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) ≤ 1)
    (hA1 : Module.finrank (ZMod p) A = 1) (hB1 : Module.finrank (ZMod p) B = 1) : A = B := by
  have hAeq : A = HardMathSupport.Kantor79.commutatorSpace H := by
    refine Submodule.eq_of_le_of_finrank_eq hA ?_
    have := Submodule.finrank_mono hA
    omega
  have hBeq : B = HardMathSupport.Kantor79.commutatorSpace H := by
    refine Submodule.eq_of_le_of_finrank_eq hB ?_
    have := Submodule.finrank_mono hB
    omega
  rw [hAeq, hBeq]

private theorem H_le_F (hS : LemmaOneSixSetting F H a l) : H ≤ F := by
  intro h hh
  rw [hS.eq_closure]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem a hh)

theorem two_le_of_dLarge (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] : 2 ≤ l := by
  by_contra h
  have h1 : l ≤ 1 := by omega
  obtain ⟨x, hxH, y, hyH, hxr, hyr, hxy⟩ := hS.dLarge
  have hHfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) = l :=
    hS.splitSupport.2.1
  have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) ≤ 1 := by
    rw [hHfin]; omega
  have hmov : HardMathSupport.Kantor79.movedSpace x =
      HardMathSupport.Kantor79.movedSpace y :=
    eq_of_finrank_eq_one_of_le (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hxH)
      (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hyH) hfin hxr.2 hyr.2
  have hxy_eq : x = y := eq_of_movedSpace_eq hp hS.transvectionFree
    (H_le_F hS hxH) (H_le_F hS hyH) hxr hyr hmov
  rw [hxy_eq, hyr.1] at hxy
  simp at hxy

private theorem kerSection_sub_mem_centralizerSpace {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {t : U ≃ₗ[ZMod p] U} (ht : t ∈ kerSection F) :
    ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F, t v - v ∈ centralizerSpace F := by
  have hVF : ∀ g ∈ F, ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace F,
      g w ∈ HardMathSupport.Kantor79.commutatorSpace F := by
    intro g hg w hw
    have hmap := map_commutatorSpace_of_mem_normalizer (H := F) (Subgroup.le_normalizer hg)
    rw [← hmap]
    exact ⟨w, hw, rfl⟩
  have hP : ∀ t ∈ Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ F ∧
      ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F, t v - v ∈ centralizerSpace F},
      t ∈ F ∧ (∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
        t v - v ∈ centralizerSpace F) := by
    intro t ht
    induction ht using Subgroup.closure_induction with
    | mem y hy => exact hy
    | one => exact ⟨F.one_mem, fun v hv => by simp⟩
    | mul x y hx hy ihx ihy =>
        refine ⟨F.mul_mem ihx.1 ihy.1, fun v hv => ?_⟩
        have hyv : y v ∈ HardMathSupport.Kantor79.commutatorSpace F := hVF y ihy.1 v hv
        have h1 : y v - v ∈ centralizerSpace F := ihy.2 v hv
        have h2 : x (y v) - y v ∈ centralizerSpace F := ihx.2 (y v) hyv
        have hxy : (x * y) v - v = (x (y v) - y v) + (y v - v) := by
          rw [LinearEquiv.mul_apply]; abel
        rw [hxy]
        exact (centralizerSpace F).add_mem h2 h1
    | inv x hx ihx =>
        refine ⟨F.inv_mem ihx.1, fun v hv => ?_⟩
        have hxv : x⁻¹ v ∈ HardMathSupport.Kantor79.commutatorSpace F :=
          hVF x⁻¹ (F.inv_mem ihx.1) v hv
        have h1 : x (x⁻¹ v) - x⁻¹ v ∈ centralizerSpace F := ihx.2 (x⁻¹ v) hxv
        have hxinv : x (x⁻¹ v) = v := by simp
        rw [hxinv] at h1
        have : x⁻¹ v - v = -(v - x⁻¹ v) := by abel
        rw [this]
        exact (centralizerSpace F).neg_mem h1
  exact (hP t (by simpa [kerSection] using ht)).2

private theorem kerSection_fixesFlag {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {t : U ≃ₗ[ZMod p] U} (ht : t ∈ kerSection F) :
    FixesFlag (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
      (HardMathSupport.Kantor79.commutatorSpace F) t := by
  have htF : t ∈ F := kerSection_le ht
  refine ⟨fun v => HardMathSupport.Kantor79.movedSpace_le_commutatorSpace htF ⟨v, rfl⟩,
    fun v hv => ⟨HardMathSupport.Kantor79.movedSpace_le_commutatorSpace htF ⟨v, rfl⟩,
      kerSection_sub_mem_centralizerSpace ht v hv⟩,
    fun v hv => (mem_centralizerSpace.mp hv.2) t htF⟩

theorem commute_of_mem_kerSection (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {t s : U ≃ₗ[ZMod p] U} (ht : t ∈ kerSection F)
    (hs : s ∈ kerSection F) : Commute t s := by
  have := hp
  exact commute_of_fixesFlag hS.transvectionFree hS.degenerate.1
    (kerSection_le ht) (kerSection_le hs)
    (kerSection_fixesFlag ht) (kerSection_fixesFlag hs)

theorem pow_eq_one_of_mem_kerSection (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {t : U ≃ₗ[ZMod p] U} (ht : t ∈ kerSection F) : t ^ p = 1 := by
  have := hS
  exact pow_eq_one_of_fixesFlag hp (kerSection_fixesFlag ht)

private def zsr8R8_translateSub (W : Submodule (ZMod p) U) : Subgroup (U ≃ₗ[ZMod p] U) where
  carrier := {g | ∀ v, g v - v ∈ W}
  one_mem' := by intro v; simp
  mul_mem' := by
    rintro a b ha hb v
    rw [LinearEquiv.mul_apply]
    rw [show a (b v) - v = (a (b v) - b v) + (b v - v) by abel]
    exact W.add_mem (ha (b v)) (hb v)
  inv_mem' := by
    rintro a ha v
    have h : a (a⁻¹ v) - a⁻¹ v ∈ W := ha (a⁻¹ v)
    have hv : a (a⁻¹ v) = v := LinearEquiv.apply_symm_apply a v
    rw [hv] at h
    rw [show a⁻¹ v - v = -(v - a⁻¹ v) by abel]
    exact W.neg_mem h

private theorem zsr8R8_commutatorSpace_mono {A B : Subgroup (U ≃ₗ[ZMod p] U)} (h : A ≤ B) :
    HardMathSupport.Kantor79.commutatorSpace A ≤ HardMathSupport.Kantor79.commutatorSpace B := by
  rw [HardMathSupport.Kantor79.commutatorSpace, HardMathSupport.Kantor79.commutatorSpace]
  refine Submodule.span_mono ?_
  rintro w ⟨a, ha, v, rfl⟩
  exact ⟨a, h ha, v, rfl⟩

private theorem zsr8R8_centralizerSpace_le {H K : Subgroup (U ≃ₗ[ZMod p] U)} (h : H ≤ K) :
    centralizerSpace K ≤ centralizerSpace H := by
  intro v hv
  rw [mem_centralizerSpace] at hv ⊢
  intro k hk
  exact hv k (h hk)

private theorem zsr8R8_commutatorSpace_eq_sup_W (hS : LemmaOneSixSetting F H a l)
    [Module.Finite (ZMod p) U] :
    HardMathSupport.Kantor79.commutatorSpace F =
      HardMathSupport.Kantor79.commutatorSpace H ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) := by
  have hHF : H ≤ F := H_le_F hS
  have hVHle : HardMathSupport.Kantor79.commutatorSpace H ≤
      HardMathSupport.Kantor79.commutatorSpace F := zsr8R8_commutatorSpace_mono hHF
  have hVFfixle : centralizerSpace F ≤ centralizerSpace H := zsr8R8_centralizerSpace_le hHF
  have hinf : HardMathSupport.Kantor79.commutatorSpace H ⊓
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = ⊥ := by
    refine le_bot_iff.mp ?_
    calc HardMathSupport.Kantor79.commutatorSpace H ⊓
          (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
        ≤ HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H :=
          le_inf inf_le_left (le_trans inf_le_right (le_trans inf_le_right hVFfixle))
      _ = ⊥ := hS.splitSupport.1.inf_eq_bot
  have hsupfin : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace H ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)) =
      Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.commutatorSpace H) +
        Module.finrank (ZMod p)
          ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (HardMathSupport.Kantor79.commutatorSpace H)
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
    rw [hinf, finrank_bot, add_zero] at h
    exact h
  have hle : HardMathSupport.Kantor79.commutatorSpace H ⊔
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) ≤
      HardMathSupport.Kantor79.commutatorSpace F := sup_le hVHle inf_le_left
  have hfin : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace H ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)) =
      Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.commutatorSpace F) := by
    rw [hsupfin, hS.splitSupport.2.1, hS.degenerate.1, hS.finrank_eq]
  exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm

private theorem zsr8R8_irredOnSection (hS : LemmaOneSixSetting F H a l)
    [Module.Finite (ZMod p) U] :
    IrredOnSection F (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
      (HardMathSupport.Kantor79.commutatorSpace F) := by
  intro X hWX hXVF hXinv
  have hHF : H ≤ F := H_le_F hS
  have hVF : HardMathSupport.Kantor79.commutatorSpace F =
      HardMathSupport.Kantor79.commutatorSpace H ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) :=
    zsr8R8_commutatorSpace_eq_sup_W hS
  have hXHinv : ∀ g ∈ H, ∀ x ∈ X ⊓ HardMathSupport.Kantor79.commutatorSpace H,
      g x ∈ X ⊓ HardMathSupport.Kantor79.commutatorSpace H := by
    intro g hg x hx
    exact ⟨hXinv g (hHF hg) x hx.1,
      zsr8A_mem_commutatorSpace_of_mem (F := H) hg hx.2⟩
  have hXH : X ⊓ HardMathSupport.Kantor79.commutatorSpace H = ⊥ ∨
      X ⊓ HardMathSupport.Kantor79.commutatorSpace H =
        HardMathSupport.Kantor79.commutatorSpace H :=
    hS.splitSupport.2.2 _ bot_le inf_le_right hXHinv
  rcases hXH with hbot | htop
  · left
    apply le_antisymm _ hWX
    intro x hx
    have hx' : x ∈ HardMathSupport.Kantor79.commutatorSpace H ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) := by
      rw [← hVF]; exact hXVF hx
    obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.mp hx'
    have hwX : w ∈ X := hWX hw
    have hvX : v ∈ X := by
      have : v = x - w := by rw [← hvw]; abel
      rw [this]; exact X.sub_mem hx hwX
    have hvbot : v ∈ X ⊓ HardMathSupport.Kantor79.commutatorSpace H := ⟨hvX, hv⟩
    rw [hbot] at hvbot
    have hv0 : v = 0 := by simpa using hvbot
    rw [← hvw, hv0, zero_add]
    exact hw
  · right
    apply le_antisymm hXVF
    have hVHX : HardMathSupport.Kantor79.commutatorSpace H ≤ X := by
      rw [← htop]; exact inf_le_left
    exact hVF ▸ sup_le hVHX hWX

private theorem zsr8R8_exists_notMem_V0 (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] :
    ∃ u₀ : U, u₀ ∉ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F := by
  have := hp
  by_contra h
  push Not at h
  exact zsr8A_V0_ne_top hS (Submodule.eq_top_iff'.mpr h)

private theorem zsr8R8_sup_span_eq_top (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {u₀ : U}
    (hu₀ : u₀ ∉ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) :
    (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) ⊔
      Submodule.span (ZMod p) {u₀} = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have hsp := Submodule.finrank_sup_span_singleton (K := ZMod p)
    (p := HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) hu₀
  have hfin : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) =
      Module.finrank (ZMod p) U - 1 := zsr8A_finrank_sup_eq hS hp
  rw [hsp, hfin]
  have hpos : 0 < Module.finrank (ZMod p) U := by
    have h1' : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace a) = 1 :=
      hS.isRefl.2
    have h2' := Submodule.finrank_le (HardMathSupport.Kantor79.movedSpace a)
    omega
  omega

private theorem zsr8R8_A_le_commutatorSpace {u₀ : U} {A : Submodule (ZMod p) U}
    (hA : A = Submodule.span (ZMod p) {w : U | ∃ t ∈ kerSection F,
      w = (t : U →ₗ[ZMod p] U) u₀ - u₀}) :
    A ≤ HardMathSupport.Kantor79.commutatorSpace F := by
  rw [hA]
  refine Submodule.span_le.mpr ?_
  rintro w ⟨t, htT, rfl⟩
  exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace
    (zsr8C_mem_kerSection htT).1 ⟨u₀, rfl⟩

private theorem zsr8R8_A_not_le_W (hS : LemmaOneSixSetting F H a l)
    [Module.Finite (ZMod p) U] {u₀ : U}
    (hV0top : (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) ⊔
      Submodule.span (ZMod p) {u₀} = ⊤)
    {A : Submodule (ZMod p) U}
    (hA : A = Submodule.span (ZMod p) {w : U | ∃ t ∈ kerSection F,
      w = (t : U →ₗ[ZMod p] U) u₀ - u₀}) :
    ¬ A ≤ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F := by
  intro hAW
  obtain ⟨t0, ht0F, ht0ne, ht0V⟩ := hS.degenerate.2.2
  have ht0T : t0 ∈ kerSection F := Subgroup.subset_closure ⟨ht0F, ht0V⟩
  have ht0u₀ : (t0 : U →ₗ[ZMod p] U) u₀ - u₀ ∈
      HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F :=
    hAW (by rw [hA]; exact Submodule.subset_span ⟨t0, ht0T, rfl⟩)
  have ht0W : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F,
      t0 v - v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F :=
    zsr8A_moved_into_W ht0F (zsr8C_mem_kerSection ht0T).2
  have hquot : ∀ v : U, t0 v - v ∈
      HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F := by
    intro v
    have hv : v ∈ (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) ⊔
        Submodule.span (ZMod p) {u₀} := by rw [hV0top]; exact Submodule.mem_top
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
    have hxW : t0 x - x ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F :=
      ht0W x hx
    have heq : t0 v - v = (t0 x - x) + c • ((t0 : U →ₗ[ZMod p] U) u₀ - u₀) := by
      rw [← hxy, ← hc, map_add, map_smul, smul_sub]; module
    rw [heq]
    exact (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F).add_mem hxW
      ((HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F).smul_mem c ht0u₀)
  have ht0fix : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F,
      t0 w = w := fun w hw => (mem_centralizerSpace.mp hw.2) t0 ht0F
  exact ht0ne (eq_one_of_forall_sub_mem_of_finrank_eq_one (A := F) hS.transvectionFree
    hS.degenerate.1 (zsr8C_mem_kerSection ht0T).1 ht0fix hquot)

private theorem zsr8R8_A_invariant_gen {u₀ : U} {A : Submodule (ZMod p) U}
    (hA : A = Submodule.span (ZMod p) {w : U | ∃ t ∈ kerSection F,
      w = (t : U →ₗ[ZMod p] U) u₀ - u₀})
    {f : U ≃ₗ[ZMod p] U} (hf : f ∈ F) {t : U ≃ₗ[ZMod p] U} (htT : t ∈ kerSection F) :
    (f : U →ₗ[ZMod p] U) ((t : U →ₗ[ZMod p] U) u₀ - u₀) ∈ A ⊔ centralizerSpace F := by
  set t' := f * t * f⁻¹ with ht'
  have ht'T : t' ∈ kerSection F := conj_mem_kerSection hf htT
  have hgen' : (t' : U →ₗ[ZMod p] U) u₀ - u₀ ∈ A := by
    rw [hA]; exact Submodule.subset_span ⟨t', ht'T, rfl⟩
  have hfu : (f : U →ₗ[ZMod p] U) u₀ - u₀ ∈ HardMathSupport.Kantor79.commutatorSpace F :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hf ⟨u₀, rfl⟩
  have ht'V : (t' : U →ₗ[ZMod p] U) ((f : U →ₗ[ZMod p] U) u₀ - u₀) -
      ((f : U →ₗ[ZMod p] U) u₀ - u₀) ∈ centralizerSpace F :=
    (zsr8C_mem_kerSection ht'T).2 _ hfu
  have ht'fm : (t' : U →ₗ[ZMod p] U) ((f : U →ₗ[ZMod p] U) u₀) =
      (f : U →ₗ[ZMod p] U) ((t : U →ₗ[ZMod p] U) u₀) := by
    rw [ht']; simp
  have heq : (f : U →ₗ[ZMod p] U) ((t : U →ₗ[ZMod p] U) u₀ - u₀) =
      ((t' : U →ₗ[ZMod p] U) u₀ - u₀) +
        ((t' : U →ₗ[ZMod p] U) ((f : U →ₗ[ZMod p] U) u₀ - u₀) -
          ((f : U →ₗ[ZMod p] U) u₀ - u₀)) := by
    rw [map_sub, map_sub, ht'fm]
    abel
  rw [heq]
  exact (A ⊔ centralizerSpace F).add_mem (Submodule.mem_sup_left hgen')
    (Submodule.mem_sup_right ht'V)

private theorem zsr8R8_A_invariant {u₀ : U} {A : Submodule (ZMod p) U}
    (hA : A = Submodule.span (ZMod p) {w : U | ∃ t ∈ kerSection F,
      w = (t : U →ₗ[ZMod p] U) u₀ - u₀}) :
    ∀ f ∈ F, ∀ x ∈ A ⊔ centralizerSpace F, f x ∈ A ⊔ centralizerSpace F := by
  intro f hf x hx
  obtain ⟨a, ha, w, hw, haw⟩ := Submodule.mem_sup.mp hx
  rw [← haw, map_add]
  refine (A ⊔ centralizerSpace F).add_mem ?_ ?_
  · rw [hA] at ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · rintro y ⟨t, htT, rfl⟩
      exact zsr8R8_A_invariant_gen hA hf htT
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro a b ha hb iha ihb
      rw [map_add]; exact (A ⊔ centralizerSpace F).add_mem iha ihb
    · intro c a ha iha
      rw [map_smul]; exact Submodule.smul_mem _ c iha
  · refine Submodule.mem_sup_right ?_
    rw [mem_centralizerSpace] at hw ⊢
    intro g hg
    have hmem : f⁻¹ * g * f ∈ F := F.mul_mem (F.mul_mem (F.inv_mem hf) hg) hf
    calc g (f w) = f ((f⁻¹ * g * f) w) := by simp [LinearEquiv.mul_apply]
      _ = f w := by rw [hw _ hmem]

private theorem zsr8R8_A_inf_commutatorSpace (hS : LemmaOneSixSetting F H a l)
    [Module.Finite (ZMod p) U] {A : Submodule (ZMod p) U}
    (hAle : A ≤ HardMathSupport.Kantor79.commutatorSpace F)
    (hAne : ¬ A ≤ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
    (hAinv : ∀ f ∈ F, ∀ x ∈ A ⊔ centralizerSpace F, f x ∈ A ⊔ centralizerSpace F) :
    (A ⊔ centralizerSpace F) ⊓ HardMathSupport.Kantor79.commutatorSpace F =
      HardMathSupport.Kantor79.commutatorSpace F := by
  have hWle : HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F ≤
      (A ⊔ centralizerSpace F) ⊓ HardMathSupport.Kantor79.commutatorSpace F :=
    fun w hw => ⟨Submodule.mem_sup_right hw.2, hw.1⟩
  have hne : (A ⊔ centralizerSpace F) ⊓ HardMathSupport.Kantor79.commutatorSpace F ≠
      HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F := by
    intro heq
    apply hAne
    intro a ha
    have hamem : a ∈ (A ⊔ centralizerSpace F) ⊓ HardMathSupport.Kantor79.commutatorSpace F :=
      ⟨Submodule.mem_sup_left ha, hAle ha⟩
    rw [heq] at hamem
    exact hamem
  rcases zsr8R8_irredOnSection hS _ hWle inf_le_right
      (fun g hg x hx => ⟨hAinv g hg x hx.1,
        zsr8A_mem_commutatorSpace_of_mem hg hx.2⟩) with hbot | htop
  · exact absurd hbot hne
  · exact htop

private theorem zsr8R8_A_fix (hS : LemmaOneSixSetting F H a l) {u₀ : U}
    {A : Submodule (ZMod p) U}
    (hA : A = Submodule.span (ZMod p) {w : U | ∃ t ∈ kerSection F,
      w = (t : U →ₗ[ZMod p] U) u₀ - u₀})
    {h : U ≃ₗ[ZMod p] U} (hh : h ∈ H) (hcon : ∀ t ∈ kerSection F, Commute h t) :
    ∀ a ∈ A, (h : U →ₗ[ZMod p] U) a - a ∈ centralizerSpace F := by
  intro a ha
  rw [hA] at ha
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · rintro y ⟨t, htT, rfl⟩
    have hcomm : (h : U →ₗ[ZMod p] U) ((t : U →ₗ[ZMod p] U) u₀) =
        (t : U →ₗ[ZMod p] U) ((h : U →ₗ[ZMod p] U) u₀) := by
      have hc := hcon t htT
      rw [Commute] at hc
      have h2 := congrArg (fun e : U ≃ₗ[ZMod p] U => e u₀) hc
      simpa [LinearEquiv.mul_apply] using h2
    have hhu : (h : U →ₗ[ZMod p] U) u₀ - u₀ ∈ HardMathSupport.Kantor79.commutatorSpace F :=
      HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (H_le_F hS hh) ⟨u₀, rfl⟩
    have hkey : (h : U →ₗ[ZMod p] U) ((t : U →ₗ[ZMod p] U) u₀ - u₀) -
        ((t : U →ₗ[ZMod p] U) u₀ - u₀) =
        (t : U →ₗ[ZMod p] U) ((h : U →ₗ[ZMod p] U) u₀ - u₀) -
          ((h : U →ₗ[ZMod p] U) u₀ - u₀) := by
      rw [map_sub, map_sub, hcomm]
      abel
    rw [hkey]
    exact (zsr8C_mem_kerSection htT).2 _ hhu
  · simp
  · intro a b ha hb iha ihb
    have hsum : (h : U →ₗ[ZMod p] U) (a + b) - (a + b) =
        ((h : U →ₗ[ZMod p] U) a - a) + ((h : U →ₗ[ZMod p] U) b - b) := by
      rw [map_add]; abel
    rw [hsum]; exact (centralizerSpace F).add_mem iha ihb
  · intro c a ha iha
    have hsum : (h : U →ₗ[ZMod p] U) (c • a) - c • a =
        c • ((h : U →ₗ[ZMod p] U) a - a) := by
      rw [map_smul, smul_sub]
    rw [hsum]; exact (centralizerSpace F).smul_mem c iha

private theorem zsr8R8_sup_fix (hS : LemmaOneSixSetting F H a l)
    {A : Submodule (ZMod p) U} {h : U ≃ₗ[ZMod p] U} (hh : h ∈ H)
    (hAfix : ∀ a ∈ A, (h : U →ₗ[ZMod p] U) a - a ∈ centralizerSpace F) :
    ∀ x ∈ A ⊔ centralizerSpace F,
      (h : U →ₗ[ZMod p] U) x - x ∈ centralizerSpace F := by
  intro x hx
  obtain ⟨a, ha, w, hw, haw⟩ := Submodule.mem_sup.mp hx
  rw [← haw]
  have hwfix : (h : U →ₗ[ZMod p] U) w = w := (mem_centralizerSpace.mp hw) h (H_le_F hS hh)
  have hsum : (h : U →ₗ[ZMod p] U) (a + w) - (a + w) =
      (h : U →ₗ[ZMod p] U) a - a := by
    rw [map_add, hwfix]; abel
  rw [hsum]
  exact hAfix a ha

private theorem zsr8R8_hfix_commutatorSpace_H (hS : LemmaOneSixSetting F H a l)
    [Module.Finite (ZMod p) U]
    (hVHinf : HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H = ⊥)
    {h : U ≃ₗ[ZMod p] U} (hh : h ∈ H) (hhT : h ∈ kerSection F) :
    ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace H, h v = v := by
  intro v hv
  have hvF : v ∈ HardMathSupport.Kantor79.commutatorSpace F :=
    zsr8R8_commutatorSpace_mono (H_le_F hS) hv
  have h1' : (h : U →ₗ[ZMod p] U) v - v ∈ centralizerSpace F :=
    (zsr8C_mem_kerSection hhT).2 v hvF
  have h2' : (h : U →ₗ[ZMod p] U) v - v ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    (HardMathSupport.Kantor79.commutatorSpace H).sub_mem
      (zsr8A_mem_commutatorSpace_of_mem (F := H) hh hv) hv
  have h3' : (h : U →ₗ[ZMod p] U) v - v ∈
      HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H :=
    ⟨h2', zsr8R8_centralizerSpace_le (H_le_F hS) h1'⟩
  rw [hVHinf] at h3'
  have h3z : (h : U →ₗ[ZMod p] U) v - v = 0 := by simpa using h3'
  simpa [sub_eq_zero] using h3z

private theorem zsr8R8_exists_not_commute_kerSection (hS : LemmaOneSixSetting F H a l)
    (hp : p ≠ 2) [Module.Finite (ZMod p) U] {h : U ≃ₗ[ZMod p] U} (hh : h ∈ H) (h1 : h ≠ 1) :
    ∃ t ∈ kerSection F, ¬ Commute h t := by
  set W := HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F with hW
  obtain ⟨u₀, hu₀⟩ := zsr8R8_exists_notMem_V0 hS hp
  have hV0top : (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) ⊔
      Submodule.span (ZMod p) {u₀} = ⊤ := zsr8R8_sup_span_eq_top hS hp hu₀
  set A : Submodule (ZMod p) U := Submodule.span (ZMod p) {w : U | ∃ t ∈ kerSection F,
      w = (t : U →ₗ[ZMod p] U) u₀ - u₀} with hA
  have hAle := zsr8R8_A_le_commutatorSpace hA
  have hAne := zsr8R8_A_not_le_W hS hV0top hA
  have hAinv := zsr8R8_A_invariant hA
  have hD := zsr8R8_A_inf_commutatorSpace hS hAle hAne hAinv
  have hVF_le : HardMathSupport.Kantor79.commutatorSpace F ≤ A ⊔ centralizerSpace F :=
    hD ▸ inf_le_left
  by_contra hcon
  push Not at hcon
  have hAfix := zsr8R8_A_fix hS hA hh hcon
  have hsupfix := zsr8R8_sup_fix hS hh hAfix
  have hhT : h ∈ kerSection F := by
    refine Subgroup.subset_closure ⟨H_le_F hS hh, ?_⟩
    intro v hv
    exact hsupfix v (hVF_le hv)
  have hVHinf : HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H = ⊥ :=
    hS.splitSupport.1.inf_eq_bot
  have hfixVH := zsr8R8_hfix_commutatorSpace_H hS hVHinf hh hhT
  have hR : IsRGroup p H :=
    ⟨hS.reflGen, fun g hg htv => hS.transvectionFree g (H_le_F hS hg) htv⟩
  have hbotH : H ⊓ fixingSubgroup (U ≃ₗ[ZMod p] U)
      (HardMathSupport.Kantor79.commutatorSpace H : Set U) = ⊥ :=
    fixing_commutatorSpace_eq_bot hp hR hVHinf
  have hmem : h ∈ H ⊓ fixingSubgroup (U ≃ₗ[ZMod p] U)
      (HardMathSupport.Kantor79.commutatorSpace H : Set U) :=
    ⟨hh, (mem_fixingSubgroup_iff (M := U ≃ₗ[ZMod p] U)).mpr hfixVH⟩
  rw [hbotH] at hmem
  exact h1 (Subgroup.mem_bot.mp hmem)

theorem exists_not_commute_kerSection (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {h : U ≃ₗ[ZMod p] U} (hh : h ∈ H) (h1 : h ≠ 1) :
    ∃ t ∈ kerSection F, ¬ Commute h t := by
  exact zsr8R8_exists_not_commute_kerSection hS hp hh h1

theorem movedSpace_commutatorElement (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {t h : U ≃ₗ[ZMod p] U} (ht : t ∈ kerSection F) (hh : h ∈ H)
    (hh' : IsRefl p h) (hs : t * h * t⁻¹ * h⁻¹ ≠ 1) :
    HardMathSupport.Kantor79.movedSpace (t * h * t⁻¹ * h⁻¹) =
      HardMathSupport.Kantor79.movedSpace h ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) := by
  exact zsr8C_movedSpace_commutatorElement hS hp ht hh hh' hs

private theorem zsr8R8_inf_sup_le_sup_inf {A : Submodule (ZMod p) U}
    (hA : A ≤ HardMathSupport.Kantor79.commutatorSpace F) {x : U}
    (hx : x ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓
      (A ⊔ centralizerSpace F)) :
    x ∈ A ⊔ (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx.2
  have hxF : x ∈ HardMathSupport.Kantor79.commutatorSpace F := hx.1
  have hbF : b ∈ HardMathSupport.Kantor79.commutatorSpace F := by
    have : b = x - a := by rw [← hab]; abel
    rw [this]
    exact (HardMathSupport.Kantor79.commutatorSpace F).sub_mem hxF (hA ha)
  rw [← hab]
  exact Submodule.add_mem_sup (S := A)
    (T := HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) ha ⟨hbF, hb⟩

private theorem zsr8R8_commutator_apply_mem_decomp {h t : U ≃ₗ[ZMod p] U} (v : U) {u w : U}
    (hu : u = h⁻¹ (t⁻¹ v)) (hw : w = (t : U →ₗ[ZMod p] U) u - u) :
    (h * t * h⁻¹ * t⁻¹ : U ≃ₗ[ZMod p] U) v - v =
      (h w - w) + ((w - ((t : U →ₗ[ZMod p] U) v - v)) -
        (((t⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ((t : U →ₗ[ZMod p] U) v - v) -
          ((t : U →ₗ[ZMod p] U) v - v))) := by
  have htv_inv : ((t⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ((t : U →ₗ[ZMod p] U) v) = v := by
    change (t : U ≃ₗ[ZMod p] U)⁻¹ ((t : U ≃ₗ[ZMod p] U) v) = v
    exact LinearEquiv.symm_apply_apply t v
  have htv1 : ((t⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ((t : U →ₗ[ZMod p] U) v - v) =
      v - ((t⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) v := by
    rw [map_sub, htv_inv]
  have htinv : ((t⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) v =
      v - ((t⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)
        ((t : U →ₗ[ZMod p] U) v - v) := by rw [htv1]; abel
  have hval : (h * t * h⁻¹ * t⁻¹ : U ≃ₗ[ZMod p] U) v =
      h w + ((t⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) v := by
    rw [show (h * t * h⁻¹ * t⁻¹ : U ≃ₗ[ZMod p] U) v = h ((t : U →ₗ[ZMod p] U) u) by
      simp only [LinearEquiv.mul_apply, hu]; rfl]
    have htu : (t : U →ₗ[ZMod p] U) u = w + u := by rw [hw]; abel
    rw [htu, map_add]
    have hhu : h u = ((t⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) v := by rw [hu]; simp
    rw [hhu]
  rw [hval, htinv]
  abel

private theorem zsr8R8_commutator_apply_mem (hS : LemmaOneSixSetting F H a l)
    {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H) {h t : U ≃ₗ[ZMod p] U}
    (hh : h ∈ H₁) (ht : t ∈ kerSection F) (v : U) :
    (h * t * h⁻¹ * t⁻¹ : U ≃ₗ[ZMod p] U) v - v ∈ HardMathSupport.Kantor79.commutatorSpace H₁ ⊔
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) := by
  have hhF : h ∈ F := H_le_F hS (hH₁ hh)
  have htF : t ∈ F := kerSection_le ht
  have htV : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace F,
      t w - w ∈ centralizerSpace F := (zsr8C_mem_kerSection ht).2
  set u : U := h⁻¹ (t⁻¹ v) with hu
  set w : U := (t : U →ₗ[ZMod p] U) u - u with hw
  have huV : u - v ∈ HardMathSupport.Kantor79.commutatorSpace F := by
    have h1 : h⁻¹ (t⁻¹ v) - t⁻¹ v ∈ HardMathSupport.Kantor79.commutatorSpace F :=
      HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (F.inv_mem hhF) ⟨t⁻¹ v, rfl⟩
    have h2 : t⁻¹ v - v ∈ HardMathSupport.Kantor79.commutatorSpace F :=
      HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (F.inv_mem htF) ⟨v, rfl⟩
    have heq : u - v = (h⁻¹ (t⁻¹ v) - t⁻¹ v) + (t⁻¹ v - v) := by rw [hu]; abel
    rw [heq]
    exact (HardMathSupport.Kantor79.commutatorSpace F).add_mem h1 h2
  have htvV : (t : U →ₗ[ZMod p] U) v - v ∈ HardMathSupport.Kantor79.commutatorSpace F :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace htF ⟨v, rfl⟩
  have h1 : h w - w ∈ HardMathSupport.Kantor79.commutatorSpace H₁ :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hh ⟨w, rfl⟩
  have h2 : w - ((t : U →ₗ[ZMod p] U) v - v) ∈ centralizerSpace F := by
    have heq : w - ((t : U →ₗ[ZMod p] U) v - v) =
        (t : U →ₗ[ZMod p] U) (u - v) - (u - v) := by rw [hw, map_sub]; abel
    rw [heq]; exact htV (u - v) huV
  have h3 : (t⁻¹ : U ≃ₗ[ZMod p] U) ((t : U →ₗ[ZMod p] U) v - v) -
      ((t : U →ₗ[ZMod p] U) v - v) ∈ centralizerSpace F :=
    (zsr8C_mem_kerSection ((kerSection F).inv_mem ht)).2 _ htvV
  have hmain := zsr8R8_commutator_apply_mem_decomp (h := h) (t := t) v hu hw
  have hxV : (h * t * h⁻¹ * t⁻¹ : U ≃ₗ[ZMod p] U) v - v ∈
      HardMathSupport.Kantor79.commutatorSpace F :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace
      (F.mul_mem (F.mul_mem (F.mul_mem hhF htF) (F.inv_mem hhF)) (F.inv_mem htF)) ⟨v, rfl⟩
  have hxsup : (h * t * h⁻¹ * t⁻¹ : U ≃ₗ[ZMod p] U) v - v ∈
      HardMathSupport.Kantor79.commutatorSpace H₁ ⊔ centralizerSpace F := by
    rw [hmain]
    refine Submodule.add_mem_sup (S := HardMathSupport.Kantor79.commutatorSpace H₁)
      (T := centralizerSpace F) h1 ?_
    exact (centralizerSpace F).sub_mem h2 h3
  exact zsr8R8_inf_sup_le_sup_inf (A := HardMathSupport.Kantor79.commutatorSpace H₁)
    (zsr8R8_commutatorSpace_mono (hH₁.trans (H_le_F hS))) ⟨hxV, hxsup⟩

private theorem zsr8R8_exists_refl_of_reflGen_ne_bot {H₁ : Subgroup (U ≃ₗ[ZMod p] U)}
    (hH₁' : ReflGen p H₁) (hH₁1 : H₁ ≠ ⊥) : ∃ r ∈ H₁, IsRefl p r := by
  by_contra h
  push Not at h
  apply hH₁1
  rw [hH₁']
  have hempty : {t : U ≃ₗ[ZMod p] U | t ∈ H₁ ∧ IsRefl p t} = ∅ := by
    ext t; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro ht htr; exact h t ht htr
  rw [hempty, Subgroup.closure_empty]

private theorem zsr8R8_W_le_commutatorSpace (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H)
    {r : U ≃ₗ[ZMod p] U} (hrH₁ : r ∈ H₁) (hrr : IsRefl p r) :
    HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F ≤
      HardMathSupport.Kantor79.commutatorSpace ⁅H₁, kerSection F⁆ := by
  have hr1 : r ≠ 1 := by
    intro h1
    have h0 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace
        (1 : U ≃ₗ[ZMod p] U)) = 1 := by rw [← h1]; exact hrr.2
    rw [zsr8C_movedSpace_one, finrank_bot] at h0
    exact Nat.zero_ne_one h0
  obtain ⟨t, htT, hnt⟩ := exists_not_commute_kerSection hS hp (hH₁ hrH₁) hr1
  have hs : t * r * t⁻¹ * r⁻¹ ≠ 1 := by
    intro h1
    exact hnt (commutatorElement_eq_one_iff_commute.mp h1).symm
  have hmov := movedSpace_commutatorElement hS hp htT (hH₁ hrH₁) hrr hs
  have hs_mem : t * r * t⁻¹ * r⁻¹ ∈ ⁅H₁, kerSection F⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator htT hrH₁
  have hWmov : HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F ≤
      HardMathSupport.Kantor79.movedSpace (t * r * t⁻¹ * r⁻¹) := by
    rw [hmov]; exact le_sup_right
  exact hWmov.trans (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hs_mem)

private theorem zsr8R8_commutatorSpace_commutator (hS : LemmaOneSixSetting F H a l)
    (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H) (hH₁' : ReflGen p H₁) (hH₁1 : H₁ ≠ ⊥) :
    HardMathSupport.Kantor79.commutatorSpace ⁅H₁, kerSection F⁆ =
      HardMathSupport.Kantor79.commutatorSpace H₁ ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) := by
  set T : Subgroup (U ≃ₗ[ZMod p] U) := kerSection F with hT
  set W := HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F with hW
  refine le_antisymm ?_ ?_
  · rw [commutatorSpace_le_iff]
    have hle : ⁅H₁, T⁆ ≤ zsr8R8_translateSub
        (HardMathSupport.Kantor79.commutatorSpace H₁ ⊔ W) := by
      refine Subgroup.commutator_le.mpr ?_
      intro h hh t ht v
      exact zsr8R8_commutator_apply_mem hS hH₁ hh ht v
    exact fun c hc v => hle hc v
  · obtain ⟨r, hrH₁, hrr⟩ := zsr8R8_exists_refl_of_reflGen_ne_bot hH₁' hH₁1
    have hWle : W ≤ HardMathSupport.Kantor79.commutatorSpace ⁅H₁, T⁆ :=
      zsr8R8_W_le_commutatorSpace hS hp hH₁ hrH₁ hrr
    have hVle : HardMathSupport.Kantor79.commutatorSpace H₁ ≤
        HardMathSupport.Kantor79.commutatorSpace ⁅H₁, T⁆ := by
      rw [commutatorSpace_eq_iSup_of_reflGen hH₁']
      refine iSup_le fun r => iSup_le fun hr => ?_
      have hr1 : r ≠ 1 := by
        intro h1
        have h0 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace
            (1 : U ≃ₗ[ZMod p] U)) = 1 := by rw [← h1]; exact hr.2.2
        rw [zsr8C_movedSpace_one, finrank_bot] at h0
        exact Nat.zero_ne_one h0
      obtain ⟨t, htT, hnt⟩ := exists_not_commute_kerSection hS hp (hH₁ hr.1) hr1
      have hs : t * r * t⁻¹ * r⁻¹ ≠ 1 := by
        intro h1
        exact hnt (commutatorElement_eq_one_iff_commute.mp h1).symm
      have hmov := movedSpace_commutatorElement hS hp htT (hH₁ hr.1) hr.2 hs
      have hs_mem : t * r * t⁻¹ * r⁻¹ ∈ ⁅H₁, T⁆ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator htT hr.1
      have hrle : HardMathSupport.Kantor79.movedSpace r ≤
          HardMathSupport.Kantor79.movedSpace (t * r * t⁻¹ * r⁻¹) := by
        rw [hmov]; exact le_sup_left
      exact hrle.trans (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hs_mem)
    exact sup_le hVle hWle

theorem commutatorSpace_commutator (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H)
    (hH₁' : ReflGen p H₁) (hH₁1 : H₁ ≠ ⊥) :
    HardMathSupport.Kantor79.commutatorSpace ⁅H₁, kerSection F⁆ =
      HardMathSupport.Kantor79.commutatorSpace H₁ ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) := by
  exact zsr8R8_commutatorSpace_commutator hS hp hH₁ hH₁' hH₁1

open Module in
open CFSG.HardMathSupport.Kantor79 in
private theorem zsr8C_le_of_eq_closure {F H : Subgroup (U ≃ₗ[ZMod p] U)}
    {a : U ≃ₗ[ZMod p] U}
    (h : F = Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U)))) : H ≤ F := by
  rw [h]
  intro x hx
  exact Subgroup.subset_closure (Set.mem_insert_of_mem a hx)

open Module in
open CFSG.HardMathSupport.Kantor79 in
private theorem zsr8C_commutatorSpace_mono {A B : Subgroup (U ≃ₗ[ZMod p] U)} (h : A ≤ B) :
    commutatorSpace A ≤ commutatorSpace B := by
  rw [commutatorSpace, commutatorSpace]
  refine Submodule.span_mono ?_
  rintro w ⟨a, ha, v, rfl⟩
  exact ⟨a, h ha, v, rfl⟩

open Module in
open CFSG.HardMathSupport.Kantor79 in
private theorem zsr8C_commutatorSpace_sup (A B : Subgroup (U ≃ₗ[ZMod p] U)) :
    commutatorSpace (A ⊔ B) = commutatorSpace A ⊔ commutatorSpace B := by
  refine le_antisymm ?_ (sup_le (zsr8C_commutatorSpace_mono le_sup_left)
    (zsr8C_commutatorSpace_mono le_sup_right))
  rw [commutatorSpace_le_iff]
  have key : ∀ g ∈ A ⊔ B, ∀ v, g v - v ∈ commutatorSpace A ⊔ commutatorSpace B := by
    intro g hg
    rw [Subgroup.sup_eq_closure] at hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      intro v
      rcases hy with hyA | hyB
      · exact Submodule.mem_sup_left ((commutatorSpace_le_iff).mp le_rfl y hyA v)
      · exact Submodule.mem_sup_right ((commutatorSpace_le_iff).mp le_rfl y hyB v)
    | one => intro v; simp
    | mul a b ha hb iha ihb =>
      intro v
      have h1 := iha (b v)
      have h2 := ihb v
      rw [LinearEquiv.mul_apply]
      rw [show a (b v) - v = (a (b v) - b v) + (b v - v) by abel]
      exact (commutatorSpace A ⊔ commutatorSpace B).add_mem h1 h2
    | inv a ha iha =>
      intro v
      have h1 := iha (a.symm v)
      change a.symm v - v ∈ commutatorSpace A ⊔ commutatorSpace B
      rw [show a.symm v - v = -(a (a.symm v) - a.symm v) by
        rw [LinearEquiv.apply_symm_apply]; abel]
      exact Submodule.neg_mem _ h1
  exact key

open Module in
open CFSG.HardMathSupport.Kantor79 in
private theorem zsr8C_commutator_mem_kerSection {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {t h : U ≃ₗ[ZMod p] U} (ht : t ∈ kerSection F) (hh : h ∈ F) :
    t * h * t⁻¹ * h⁻¹ ∈ kerSection F := by
  have hconj : h * t * h⁻¹ ∈ kerSection F := conj_mem_kerSection hh ht
  have heq : t * h * t⁻¹ * h⁻¹ = t * (h * t * h⁻¹)⁻¹ := by group
  rw [heq]
  exact (kerSection F).mul_mem ht ((kerSection F).inv_mem hconj)

open Module in
open CFSG.HardMathSupport.Kantor79 in
private theorem zsr8C_apply_eq_neg_of_mem_movedSpace {x : U ≃ₗ[ZMod p] U} (hx : x * x = 1)
    {v : U} (hv : v ∈ movedSpace x) : x v = -v := by
  obtain ⟨w, rfl⟩ := hv
  change x (x w - w) = -(x w - w)
  rw [map_sub]
  have hxx : x (x w) = w := by
    have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e w) hx
    simpa [LinearEquiv.mul_apply] using h
  rw [hxx]
  abel

open Module in
open CFSG.HardMathSupport.Kantor79 in
private theorem zsr8C_mem_movedSpace_of_apply_eq_neg {x : U ≃ₗ[ZMod p] U}
    (h2 : (2 : ZMod p) ≠ 0) {v : U} (hv : x v = -v) : v ∈ movedSpace x := by
  refine ⟨-((2 : ZMod p)⁻¹) • v, ?_⟩
  change (x : U →ₗ[ZMod p] U) (-((2 : ZMod p)⁻¹) • v) - (-((2 : ZMod p)⁻¹) • v) = v
  rw [map_smul, show (x : U →ₗ[ZMod p] U) v = -v from hv]
  have hsum : ((2 : ZMod p)⁻¹ + (2 : ZMod p)⁻¹) = 1 := by
    rw [← two_mul]
    exact mul_inv_cancel₀ h2
  have h1 : (-((2 : ZMod p)⁻¹)) • (-v) = (2 : ZMod p)⁻¹ • v := neg_smul_neg ((2 : ZMod p)⁻¹) v
  have h3 : (-((2 : ZMod p)⁻¹)) • v = -((2 : ZMod p)⁻¹ • v) := neg_smul ((2 : ZMod p)⁻¹) v
  rw [h1, h3, sub_neg_eq_add, ← add_smul, hsum, one_smul]

open Module in
open CFSG.HardMathSupport.Kantor79 in
private theorem zsr8C_movedSpace_le_of_reflection_moves
    {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} {X : Submodule (ZMod p) U} {h : U ≃ₗ[ZMod p] U}
    (hXinv : ∀ g ∈ ⁅H₁, kerSection F⁆ ⊔ H₁, ∀ x ∈ X, g x ∈ X)
    (hhH₁ : h ∈ H₁) (hh' : IsRefl p h) {x : U} (hxX : x ∈ X) (hxne : h x ≠ x) :
    HardMathSupport.Kantor79.movedSpace h ≤ X := by
  by_contra hmovnot
  exact hxne (apply_eq_self_of_not_movedSpace_le hh'.2
    (hXinv h (Subgroup.mem_sup_right hhH₁)) hmovnot hxX)

private theorem zsr8C_reflection_witness
    {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} {X : Submodule (ZMod p) U} {h : U ≃ₗ[ZMod p] U}
    (hXinv : ∀ g ∈ ⁅H₁, kerSection F⁆ ⊔ H₁, ∀ x ∈ X, g x ∈ X)
    (hhH₁ : h ∈ H₁) (hh' : IsRefl p h) {x : U} (hxX : x ∈ X) (hxne : h x ≠ x) :
    ∃ v ∈ X, v ∈ HardMathSupport.Kantor79.movedSpace h ∧ v ≠ 0 := by
  have hmovX := zsr8C_movedSpace_le_of_reflection_moves hXinv hhH₁ hh' hxX hxne
  have hVh_ne : HardMathSupport.Kantor79.movedSpace h ≠ ⊥ := by
    intro hbot
    have h1 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace h) = 1 := hh'.2
    rw [hbot, finrank_bot] at h1
    exact Nat.zero_ne_one h1
  obtain ⟨v, hv_h, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVh_ne
  exact ⟨v, hmovX hv_h, hv_h, hv_ne⟩

private theorem zsr8C_commutatorElement_sub_ne_zero (hS : LemmaOneSixSetting F H a l)
    (hp : p ≠ 2) [Module.Finite (ZMod p) U] {h : U ≃ₗ[ZMod p] U} (hhF : h ∈ F)
    (hh' : IsRefl p h) {v : U} (hv_h : v ∈ HardMathSupport.Kantor79.movedSpace h)
    (hv_ne : v ≠ 0) {t : U ≃ₗ[ZMod p] U} (htT : t ∈ kerSection F) (hnt : ¬ Commute h t) :
    (t * h * t⁻¹ * h⁻¹) v - v ≠ 0 := by
  intro hzero
  have hv_neg : h v = -v := zsr8C_apply_eq_neg_of_mem_movedSpace hh'.1 hv_h
  have hsfix : (t * h * t⁻¹ * h⁻¹) v = v := sub_eq_zero.mp hzero
  have hs_v : (t * h * t⁻¹ * h⁻¹) v = -(t * h * t⁻¹) v := by
    change t (h (t⁻¹ (h⁻¹ v))) = -(t (h (t⁻¹ v)))
    rw [inv_eq_of_mul_eq_one_right hh'.1, hv_neg]
    simp
  have hg_neg : (t * h * t⁻¹) v = -v := by
    have h' : -((t * h * t⁻¹) v) = -(-v) := by
      rw [← hs_v, hsfix]
      simp
    exact neg_inj.mp h'
  have hv_mem_g : v ∈ HardMathSupport.Kantor79.movedSpace (t * h * t⁻¹) :=
    zsr8C_mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp) hg_neg
  have hrefl_g : IsRefl p (t * h * t⁻¹) := IsRefl.conj hh' t
  have hmoveq : HardMathSupport.Kantor79.movedSpace (t * h * t⁻¹) =
      HardMathSupport.Kantor79.movedSpace h := by
    have hfin_g : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace
        (t * h * t⁻¹)) = 1 := hrefl_g.2
    have hfin_h : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace h) = 1 := hh'.2
    rw [eq_span_singleton_of_mem_of_finrank_eq_one hfin_g hv_mem_g hv_ne,
      eq_span_singleton_of_mem_of_finrank_eq_one hfin_h hv_h hv_ne]
  have htF : t ∈ F := (zsr8C_mem_kerSection htT).1
  have hconj_eq : t * h * t⁻¹ = h :=
    eq_of_movedSpace_eq hp hS.transvectionFree
      (F.mul_mem (F.mul_mem htF hhF) (F.inv_mem htF)) hhF hrefl_g hh' hmoveq
  have hcomm : Commute h t := by
    have ht_h : t * h = h * t := by
      calc t * h = (t * h * t⁻¹) * t := by group
        _ = h * t := by rw [hconj_eq]
    exact ht_h.symm
  exact hnt hcomm

private theorem zsr8C_sub_mem_W {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {s : U ≃ₗ[ZMod p] U} {v : U} (hsF : s ∈ F)
    (hsV : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace F,
      s w - w ∈ centralizerSpace F)
    (hvV : v ∈ HardMathSupport.Kantor79.commutatorSpace F) :
    s v - v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F := by
  refine ⟨?_, hsV v hvV⟩
  have hsv : s v ∈ HardMathSupport.Kantor79.commutatorSpace F := by
    have hmap := map_commutatorSpace_of_mem_normalizer (Subgroup.le_normalizer hsF)
    rw [← hmap]
    exact Submodule.mem_map_of_mem (f := (s : U →ₗ[ZMod p] U)) hvV
  exact (HardMathSupport.Kantor79.commutatorSpace F).sub_mem hsv hvV

private theorem zsr8C_reflection_inf_ne_bot (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} {X : Submodule (ZMod p) U}
    (hXinv : ∀ g ∈ ⁅H₁, kerSection F⁆ ⊔ H₁, ∀ x ∈ X, g x ∈ X)
    (hH₁ : H₁ ≤ H) {h : U ≃ₗ[ZMod p] U} (hhH₁ : h ∈ H₁) (hh' : IsRefl p h)
    {x : U} (hxX : x ∈ X) (hxne : h x ≠ x) :
    X ⊓ (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) ≠ ⊥ := by
  obtain ⟨v, hvX, hv_h, hv_ne⟩ :=
    zsr8C_reflection_witness hXinv hhH₁ hh' hxX hxne
  have hhF : h ∈ F := H_le_F hS (hH₁ hhH₁)
  have hh1 : h ≠ 1 := by
    intro h1
    rw [h1] at hh'
    have h0 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace
        (1 : U ≃ₗ[ZMod p] U)) = 1 := hh'.2
    rw [zsr8C_movedSpace_one, finrank_bot] at h0
    exact Nat.zero_ne_one h0
  obtain ⟨t, htT, hnt⟩ := exists_not_commute_kerSection hS hp (hH₁ hhH₁) hh1
  have hst : t * h * t⁻¹ * h⁻¹ ≠ 1 := by
    intro h1
    have hc' : Commute t h := (commutatorElement_eq_one_iff_commute).mp h1
    exact hnt hc'.symm
  have hsT : t * h * t⁻¹ * h⁻¹ ∈ kerSection F := zsr8C_commutator_mem_kerSection htT hhF
  have hsF : t * h * t⁻¹ * h⁻¹ ∈ F := (zsr8C_mem_kerSection hsT).1
  have hsV : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace F,
      (t * h * t⁻¹ * h⁻¹) w - w ∈ centralizerSpace F :=
    (zsr8C_mem_kerSection hsT).2
  have hsA : t * h * t⁻¹ * h⁻¹ ∈ ⁅H₁, kerSection F⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator htT hhH₁
  have hsF₁ : t * h * t⁻¹ * h⁻¹ ∈ ⁅H₁, kerSection F⁆ ⊔ H₁ :=
    Subgroup.mem_sup_left hsA
  have hsX : (t * h * t⁻¹ * h⁻¹) v - v ∈ X :=
    X.sub_mem (hXinv _ hsF₁ v hvX) hvX
  have hvV : v ∈ HardMathSupport.Kantor79.commutatorSpace F :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hhF hv_h
  have hsW : (t * h * t⁻¹ * h⁻¹) v - v ∈
      HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F :=
    zsr8C_sub_mem_W hsF hsV hvV
  have hsne : (t * h * t⁻¹ * h⁻¹) v - v ≠ 0 :=
    zsr8C_commutatorElement_sub_ne_zero hS hp hhF hh' hv_h hv_ne htT hnt
  intro hbot
  have hmem : (t * h * t⁻¹ * h⁻¹) v - v ∈ X ⊓
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) := ⟨hsX, hsW⟩
  rw [hbot] at hmem
  exact hsne (by simpa using hmem)

private theorem zsr8C_eq_W_of_le_of_ne_bot (hS : LemmaOneSixSetting F H a l)
    [Module.Finite (ZMod p) U] {X : Submodule (ZMod p) U}
    (hXW : X ≤ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
    (hXne : X ≠ ⊥) :
    X = HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F := by
  have hXfin : Module.finrank (ZMod p) X = 1 := by
    have hpos : 0 < Module.finrank (ZMod p) X := by
      rw [Nat.pos_iff_ne_zero]
      intro h0
      exact hXne (Submodule.finrank_eq_zero.mp h0)
    have hlefin : Module.finrank (ZMod p) X ≤ 1 := by
      rw [← hS.degenerate.1]
      exact Submodule.finrank_mono hXW
    omega
  exact Submodule.eq_of_le_of_finrank_eq hXW (by rw [hXfin, hS.degenerate.1])

private theorem zsr8C_le_of_invariant_reflection (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} {X : Submodule (ZMod p) U}
    (hXinv : ∀ g ∈ ⁅H₁, kerSection F⁆ ⊔ H₁, ∀ x ∈ X, g x ∈ X)
    (hH₁ : H₁ ≤ H) (hcase : ∃ h, h ∈ H₁ ∧ IsRefl p h ∧ ∃ x, x ∈ X ∧ h x ≠ x) :
    HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F ≤ X := by
  obtain ⟨h, hhH₁, hh', x, hxX, hxne⟩ := hcase
  have hXWne := zsr8C_reflection_inf_ne_bot hS hp hXinv hH₁ hhH₁ hh' hxX hxne
  have hXWeq : X ⊓ (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) =
      HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F :=
    zsr8C_eq_W_of_le_of_ne_bot hS inf_le_right hXWne
  exact (le_of_eq hXWeq.symm).trans inf_le_left

private theorem zsr8C_fixes_of_no_reflection {H₁ : Subgroup (U ≃ₗ[ZMod p] U)}
    {X : Submodule (ZMod p) U} (hH₁' : ReflGen p H₁)
    (hcase : ¬ ∃ h, h ∈ H₁ ∧ IsRefl p h ∧ ∃ x, x ∈ X ∧ h x ≠ x)
    (hXinv : ∀ g ∈ ⁅H₁, kerSection F⁆ ⊔ H₁, ∀ x ∈ X, g x ∈ X) :
    ∀ g ∈ H₁, ∀ x ∈ X, g x = x := by
  intro g hg
  rw [hH₁'] at hg
  induction hg using Subgroup.closure_induction with
  | mem t ht =>
    intro x hx
    by_contra hne
    exact hcase ⟨t, ht.1, ht.2, x, hx, hne⟩
  | one => intro x hx; rfl
  | mul a b ha hb iha ihb =>
    intro x hx
    rw [LinearEquiv.mul_apply, ihb x hx, iha x hx]
  | inv a ha iha =>
    intro x hx
    have haH₁ : a ∈ H₁ := by rw [hH₁']; exact ha
    have h1 := iha (a.symm x)
      (hXinv a.symm (Subgroup.mem_sup_right (H₁.inv_mem haH₁)) x hx)
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm

private theorem zsr8C_le_of_invariant_trivial (hS : LemmaOneSixSetting F H a l)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} {X : Submodule (ZMod p) U}
    (hHF : H ≤ F) (hH₁ : H₁ ≤ H) (hH₁' : ReflGen p H₁)
    (hc : HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace H₁ = ⊥)
    (hXle : X ≤ HardMathSupport.Kantor79.commutatorSpace H₁ ⊔
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F))
    (hXne : X ≠ ⊥)
    (hXinv : ∀ g ∈ ⁅H₁, kerSection F⁆ ⊔ H₁, ∀ x ∈ X, g x ∈ X)
    (hcase : ¬ ∃ h, h ∈ H₁ ∧ IsRefl p h ∧ ∃ x, x ∈ X ∧ h x ≠ x) :
    HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F ≤ X := by
  have htriv := zsr8C_fixes_of_no_reflection hH₁' hcase hXinv
  have hXc : X ≤ centralizerSpace H₁ := by
    intro x hx
    rw [mem_centralizerSpace]
    intro g hg
    exact htriv g hg x hx
  have hWc : HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F ≤
      centralizerSpace H₁ := by
    intro w hw
    rw [mem_centralizerSpace]
    intro g hg
    exact (mem_centralizerSpace.mp hw.2) g (hHF (hH₁ hg))
  have hXW : X ≤ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F := by
    intro x hx
    obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.mp (hXle hx)
    have hv_c : v ∈ centralizerSpace H₁ := by
      have hv_eq : v = x - w := by rw [← hvw]; abel
      rw [hv_eq]
      exact (centralizerSpace H₁).sub_mem (hXc hx) (hWc hw)
    have hv0 : v = 0 := by
      have hmem : v ∈ HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace H₁ :=
        ⟨hv, hv_c⟩
      rw [hc] at hmem
      simpa using hmem
    rw [← hvw, hv0, zero_add]
    exact hw
  exact le_of_eq (zsr8C_eq_W_of_le_of_ne_bot hS hXW hXne).symm

private theorem zsr8C_le_of_invariant_of_ne_bot {p : ℕ} [Fact p.Prime] {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] {F H : Subgroup (U ≃ₗ[ZMod p] U)}
    {a : U ≃ₗ[ZMod p] U} {l : ℕ}
    (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H) (hH₁' : ReflGen p H₁)
    (hH₁1 : H₁ ≠ ⊥)
    (hc : HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace H₁ = ⊥) :
    HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) =
        HardMathSupport.Kantor79.commutatorSpace H₁ ⊔
          (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) ∧
      ∀ X : Submodule (ZMod p) U,
        X ≤ HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) → X ≠ ⊥ →
        (∀ g ∈ ⁅H₁, kerSection F⁆ ⊔ H₁, ∀ x ∈ X, g x ∈ X) →
        HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F ≤ X := by
  have hHF : H ≤ F := zsr8C_le_of_eq_closure hS.eq_closure
  set W : Submodule (ZMod p) U :=
    HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F with hW
  have hfirst : HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) =
      HardMathSupport.Kantor79.commutatorSpace H₁ ⊔ W := by
    rw [zsr8C_commutatorSpace_sup,
      LemmaOneSixSetting.commutatorSpace_commutator hS hp hH₁ hH₁' hH₁1]
    rw [sup_assoc, sup_comm W (HardMathSupport.Kantor79.commutatorSpace H₁),
      ← sup_assoc, sup_idem]
  refine ⟨hfirst, ?_⟩
  intro X hXle hXne hXinv
  have hXle' : X ≤ HardMathSupport.Kantor79.commutatorSpace H₁ ⊔ W := hfirst ▸ hXle
  by_cases hcase : ∃ h, h ∈ H₁ ∧ IsRefl p h ∧ ∃ x, x ∈ X ∧ h x ≠ x
  · exact zsr8C_le_of_invariant_reflection hS hp hXinv hH₁ hcase
  · exact zsr8C_le_of_invariant_trivial hS hHF hH₁ hH₁' hc hXle' hXne hXinv hcase

theorem le_of_invariant_of_ne_bot (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H)
    (hH₁' : ReflGen p H₁) (hH₁1 : H₁ ≠ ⊥)
    (hc : HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace H₁ = ⊥) :
    HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) =
        HardMathSupport.Kantor79.commutatorSpace H₁ ⊔
          (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) ∧
      ∀ X : Submodule (ZMod p) U,
        X ≤ HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆ ⊔ H₁) → X ≠ ⊥ →
        (∀ g ∈ ⁅H₁, kerSection F⁆ ⊔ H₁, ∀ x ∈ X, g x ∈ X) →
        HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F ≤ X := by
  exact zsr8C_le_of_invariant_of_ne_bot hS hp hH₁ hH₁' hH₁1 hc

theorem finrank_sup_eq (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] :
    Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) =
        Module.finrank (ZMod p) U - 1 := by
  exact zsr8A_finrank_sup_eq hS hp

theorem finrank_movedSpace_of_mem_kerSection (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {t : U ≃ₗ[ZMod p] U} (ht : t ∈ kerSection F) (h1 : t ≠ 1) :
    (∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F,
      t v - v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) ∧
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 2 ∧
    ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace F, t v ≠ v := by
  exact zsr8A_finrank_movedSpace_of_mem_kerSection hS hp ht h1

open Module in
private theorem zsr8D_commutatorSpace_mono {F H : Subgroup (U ≃ₗ[ZMod p] U)} (hHF : H ≤ F) :
    HardMathSupport.Kantor79.commutatorSpace H ≤
      HardMathSupport.Kantor79.commutatorSpace F := by
  rw [HardMathSupport.Kantor79.commutatorSpace, HardMathSupport.Kantor79.commutatorSpace,
    Submodule.span_le]
  rintro w ⟨x, hx, v, rfl⟩
  exact Submodule.subset_span ⟨x, hHF hx, v, rfl⟩

open Module in
private theorem zsr8D_apply_mem_commutatorSpace {G : Subgroup (U ≃ₗ[ZMod p] U)}
    {k : U ≃ₗ[ZMod p] U} (hk : k ∈ G)
    {v : U} (hv : v ∈ HardMathSupport.Kantor79.commutatorSpace G) :
    k v ∈ HardMathSupport.Kantor79.commutatorSpace G := by
  have hm := Submodule.mem_map_of_mem (f := (k : U →ₗ[ZMod p] U)) hv
  rwa [map_commutatorSpace_of_mem_normalizer (Subgroup.le_normalizer hk)] at hm

open Module in
private theorem zsr8D_centralizerSpace_antitone {F H : Subgroup (U ≃ₗ[ZMod p] U)} (h : H ≤ F) :
    centralizerSpace F ≤ centralizerSpace H := by
  intro v hv
  rw [mem_centralizerSpace] at hv ⊢
  intro k hk
  exact hv k (h hk)

open Module in
private theorem zsr8D_kerSection_sub_mem_centralizerSpace {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {t : U ≃ₗ[ZMod p] U} (ht : t ∈ kerSection F) :
    ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F, t v - v ∈ centralizerSpace F := by
  have hVF : ∀ g ∈ F, ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace F,
      g w ∈ HardMathSupport.Kantor79.commutatorSpace F := fun g hg w hw =>
    zsr8D_apply_mem_commutatorSpace hg hw
  have hP : ∀ t ∈ Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ F ∧
      ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F, t v - v ∈ centralizerSpace F},
      t ∈ F ∧ (∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
        t v - v ∈ centralizerSpace F) := by
    intro t ht
    induction ht using Subgroup.closure_induction with
    | mem y hy => exact hy
    | one => exact ⟨F.one_mem, fun v _ => by simp⟩
    | mul x y hx hy ihx ihy =>
        refine ⟨F.mul_mem ihx.1 ihy.1, fun v hv => ?_⟩
        have hyv : y v ∈ HardMathSupport.Kantor79.commutatorSpace F := hVF y ihy.1 v hv
        have h1 : y v - v ∈ centralizerSpace F := ihy.2 v hv
        have h2 : x (y v) - y v ∈ centralizerSpace F := ihx.2 (y v) hyv
        have hxy : (x * y) v - v = (x (y v) - y v) + (y v - v) := by
          rw [LinearEquiv.mul_apply]; abel
        rw [hxy]
        exact (centralizerSpace F).add_mem h2 h1
    | inv x hx ihx =>
        refine ⟨F.inv_mem ihx.1, fun v hv => ?_⟩
        have hxv : x⁻¹ v ∈ HardMathSupport.Kantor79.commutatorSpace F :=
          hVF x⁻¹ (F.inv_mem ihx.1) v hv
        have h1 : x (x⁻¹ v) - x⁻¹ v ∈ centralizerSpace F := ihx.2 (x⁻¹ v) hxv
        have hxinv : x (x⁻¹ v) = v := by simp
        rw [hxinv] at h1
        have : x⁻¹ v - v = -(v - x⁻¹ v) := by abel
        rw [this]
        exact (centralizerSpace F).neg_mem h1
  exact (hP t (by simpa [kerSection] using ht)).2

open Module in
private theorem zsr8D_exists_reflection_notMem {H X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hHX : H < X) (hX : ReflGen p X) :
    ∃ g ∈ X, IsRefl p g ∧ g ∉ H := by
  by_contra h
  push Not at h
  have hXleH : X ≤ H := by
    rw [hX]
    exact (Subgroup.closure_le _).mpr fun t ht => h t ht.1 ht.2
  exact (not_le_of_gt hHX) hXleH

private theorem zsr8D_VH_inf_W (hS : LemmaOneSixSetting F H a l) (hHleF : H ≤ F) :
    HardMathSupport.Kantor79.commutatorSpace H ⊓
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = ⊥ := by
  have hcplH : IsCompl (HardMathSupport.Kantor79.commutatorSpace H) (centralizerSpace H) :=
    hS.splitSupport.1
  have hWleCenH : (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) ≤
      centralizerSpace H := le_trans inf_le_right (zsr8D_centralizerSpace_antitone hHleF)
  refine le_antisymm ?_ bot_le
  intro v hv
  have hmem : v ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H :=
    ⟨hv.1, hWleCenH hv.2⟩
  rw [hcplH.inf_eq_bot] at hmem
  exact hmem

private theorem zsr8D_VF_eq_sup (hS : LemmaOneSixSetting F H a l) (hHleF : H ≤ F)
    [Module.Finite (ZMod p) U]
    (hVH_inf_W : HardMathSupport.Kantor79.commutatorSpace H ⊓
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = ⊥) :
    HardMathSupport.Kantor79.commutatorSpace H ⊔
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) =
      HardMathSupport.Kantor79.commutatorSpace F := by
  refine Submodule.eq_of_le_of_finrank_eq
    (sup_le (zsr8D_commutatorSpace_mono hHleF) inf_le_left) ?_
  have e := Submodule.finrank_sup_add_finrank_inf_eq
      (HardMathSupport.Kantor79.commutatorSpace H)
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
  rw [hVH_inf_W, finrank_bot, add_zero, hS.splitSupport.2.1, hS.degenerate.1] at e
  rw [e, hS.finrank_eq]

private theorem zsr8D_special_element (hS : LemmaOneSixSetting F H a l) (hHleF : H ≤ F)
    {X : Subgroup (U ≃ₗ[ZMod p] U)} (hHleX : H ≤ X)
    {g : U ≃ₗ[ZMod p] U} (hgX : g ∈ X) (hgF : g ∈ F) (hgH : g ∉ H) :
    ∃ (h t : U ≃ₗ[ZMod p] U), h ∈ H ∧ t = g * h⁻¹ ∧
      t ∈ kerSection F ∧ t ≠ 1 ∧ t ∈ X := by
  obtain ⟨h, hhH, hh_agree⟩ := hS.degenerate.2.1 g hgF
  let t : U ≃ₗ[ZMod p] U := g * h⁻¹
  have hhF : h ∈ F := hHleF hhH
  have htF : t ∈ F := F.mul_mem hgF (F.inv_mem hhF)
  have htker : t ∈ kerSection F := by
    rw [kerSection]
    refine Subgroup.subset_closure ⟨htF, ?_⟩
    intro v hv
    have hvF : v ∈ HardMathSupport.Kantor79.commutatorSpace F := hv
    have hmem : g (h⁻¹ v) - h (h⁻¹ v) ∈ centralizerSpace F :=
      hh_agree (h⁻¹ v) (zsr8D_apply_mem_commutatorSpace (F.inv_mem hhF) hvF)
    have ht_eq : t v - v = g (h⁻¹ v) - h (h⁻¹ v) := by
      simp [t, LinearEquiv.mul_apply]
    rw [ht_eq]
    exact hmem
  have ht_ne : t ≠ 1 := by
    intro ht1
    have hgh : g = h := eq_of_mul_inv_eq_one (by simpa [t] using ht1)
    exact hgH (hgh.symm ▸ hhH)
  exact ⟨h, t, hhH, rfl, htker, ht_ne, X.mul_mem hgX (X.inv_mem (hHleX hhH))⟩

private theorem zsr8D_movedSpace_g_not_le (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H : Subgroup (U ≃ₗ[ZMod p] U)} (hHleF : H ≤ F)
    (hVF_eq : HardMathSupport.Kantor79.commutatorSpace H ⊔
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) =
      HardMathSupport.Kantor79.commutatorSpace F)
    {g : U ≃ₗ[ZMod p] U}
    (hcplH : IsCompl (HardMathSupport.Kantor79.commutatorSpace H) (centralizerSpace H))
    {h t : U ≃ₗ[ZMod p] U} (hhH : h ∈ H) (ht : t = g * h⁻¹)
    (htF : t ∈ F) (htker : t ∈ kerSection F) (ht_ne : t ≠ 1) :
    ¬ HardMathSupport.Kantor79.movedSpace g ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
  intro hgle
  have hg_pres : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace H,
      g v ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    intro v hv
    have h2 : g v - v ∈ HardMathSupport.Kantor79.commutatorSpace H := hgle ⟨v, rfl⟩
    have hv' : g v = v + (g v - v) := by abel
    rw [hv']
    exact (HardMathSupport.Kantor79.commutatorSpace H).add_mem hv h2
  have ht_pres : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace H,
      t v ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    intro v hv
    have hv' : h⁻¹ v ∈ HardMathSupport.Kantor79.commutatorSpace H :=
      zsr8D_apply_mem_commutatorSpace (H.inv_mem hhH) hv
    simpa [ht, LinearEquiv.mul_apply] using hg_pres (h⁻¹ v) hv'
  have ht_fix_VH : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace H, t v = v := by
    intro v hv
    have hdiff : t v - v ∈ centralizerSpace F :=
      zsr8D_kerSection_sub_mem_centralizerSpace htker v
        (zsr8D_commutatorSpace_mono hHleF hv)
    have hdiffVH : t v - v ∈ HardMathSupport.Kantor79.commutatorSpace H :=
      (HardMathSupport.Kantor79.commutatorSpace H).sub_mem (ht_pres v hv) hv
    have hmem : t v - v ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H :=
      ⟨hdiffVH, zsr8D_centralizerSpace_antitone hHleF hdiff⟩
    rw [hcplH.inf_eq_bot] at hmem
    exact sub_eq_zero.mp hmem
  have ht_fix_W : ∀ w ∈ (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F),
      t w = w := by
    intro w hw
    exact (mem_centralizerSpace.mp hw.2) t htF
  have ht_fix_VF : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F, t v = v := by
    intro v hv
    rw [← hVF_eq] at hv
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hv
    rw [← hxy, map_add, ht_fix_VH x hx, ht_fix_W y hy]
  obtain ⟨-, -, hvii3⟩ := hS.finrank_movedSpace_of_mem_kerSection hp htker ht_ne
  obtain ⟨v, hvVF, htv⟩ := hvii3
  exact htv (ht_fix_VF v hvVF)

private theorem zsr8D_sup_movedSpace_g (hS : LemmaOneSixSetting F H a l)
    [Module.Finite (ZMod p) U] (hHleF : H ≤ F)
    {g : U ≃ₗ[ZMod p] U} (hgF : g ∈ F) (hgRefl : IsRefl p g)
    (hVg_not_le : ¬ HardMathSupport.Kantor79.movedSpace g ≤
      HardMathSupport.Kantor79.commutatorSpace H) :
    HardMathSupport.Kantor79.commutatorSpace H ⊔
      HardMathSupport.Kantor79.movedSpace g = HardMathSupport.Kantor79.commutatorSpace F := by
  refine Submodule.eq_of_le_of_finrank_eq
    (sup_le (zsr8D_commutatorSpace_mono hHleF)
      (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hgF)) ?_
  have hinf : HardMathSupport.Kantor79.commutatorSpace H ⊓
      HardMathSupport.Kantor79.movedSpace g = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro v hv
    by_contra hv0
    have hvne : v ≠ 0 := by simpa [Submodule.mem_bot] using hv0
    have hmg : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace g) = 1 := hgRefl.2
    have hspan : HardMathSupport.Kantor79.movedSpace g = Submodule.span (ZMod p) {v} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hmg hv.2 hvne
    have hle : HardMathSupport.Kantor79.movedSpace g ≤
        HardMathSupport.Kantor79.commutatorSpace H := by
      rw [hspan]
      exact Submodule.span_le.mpr (by rintro w rfl; exact hv.1)
    exact hVg_not_le hle
  have e := Submodule.finrank_sup_add_finrank_inf_eq
      (HardMathSupport.Kantor79.commutatorSpace H) (HardMathSupport.Kantor79.movedSpace g)
  have hmg : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace g) = 1 := hgRefl.2
  rw [hinf, finrank_bot, add_zero, hS.splitSupport.2.1, hmg] at e
  rw [e, hS.finrank_eq]

private theorem zsr8D_V0_eq (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {X : Subgroup (U ≃ₗ[ZMod p] U)} (hXF : X ≤ F)
    {t : U ≃ₗ[ZMod p] U} (htF : t ∈ F) (htker : t ∈ kerSection F) (ht_ne : t ≠ 1)
    (htX : t ∈ X) :
    HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F =
      HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace X := by
  have hV0_le : HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F ≤
      HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace X :=
    sup_le le_sup_left (le_trans (zsr8D_centralizerSpace_antitone hXF) le_sup_right)
  have hne_top : HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace X ≠ ⊤ := by
    intro htop
    have hmov : HardMathSupport.Kantor79.movedSpace t ≤
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) := by
      rintro w ⟨u, rfl⟩
      change t u - u ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F
      have hu : u ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace X := by
        rw [htop]; trivial
      obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hu
      have htx : t y = y := (mem_centralizerSpace.mp hy) t htX
      have hxW : t x - x ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F :=
        ⟨(HardMathSupport.Kantor79.commutatorSpace F).sub_mem
            (zsr8D_apply_mem_commutatorSpace htF hx) hx,
          zsr8D_kerSection_sub_mem_centralizerSpace htker x hx⟩
      have htu : t u - u = (t x - x) + (t y - y) := by
        rw [← hxy, map_add]
        abel
      rw [htu, htx, sub_self, add_zero]
      exact hxW
    obtain ⟨-, hvii2, -⟩ := hS.finrank_movedSpace_of_mem_kerSection hp htker ht_ne
    have hmono := Submodule.finrank_mono hmov
    rw [hS.degenerate.1, hvii2] at hmono
    omega
  have hfin : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) =
      Module.finrank (ZMod p)
        ↥(HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace X) := by
    have hlt : HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace X <
        (⊤ : Submodule (ZMod p) U) := lt_top_iff_ne_top.mpr hne_top
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    rw [finrank_top] at h1
    have h2 := Submodule.finrank_mono hV0_le
    have h3 : Module.finrank (ZMod p)
        ↥(HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) =
        Module.finrank (ZMod p) U - 1 := hS.finrank_sup_eq hp
    omega
  exact Submodule.eq_of_le_of_finrank_eq hV0_le hfin

private theorem zsr8D_irred_X (hS : LemmaOneSixSetting F H a l)
    [Module.Finite (ZMod p) U] {X : Subgroup (U ≃ₗ[ZMod p] U)} (hHleX : H ≤ X)
    (hHleF : H ≤ F)
    (hVF_eq : HardMathSupport.Kantor79.commutatorSpace H ⊔
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) =
      HardMathSupport.Kantor79.commutatorSpace F)
    (hirrH : IrredOnSection H ⊥ (HardMathSupport.Kantor79.commutatorSpace H)) :
    IrredOnSection X (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
      (HardMathSupport.Kantor79.commutatorSpace F) := by
  intro Z hWZ hZF hZinv
  have hZH : ∀ k ∈ H, ∀ z ∈ Z, k z ∈ Z := fun k hk z hz => hZinv k (hHleX hk) z hz
  have hZHinv : ∀ k ∈ H, ∀ z ∈ Z ⊓ HardMathSupport.Kantor79.commutatorSpace H,
      k z ∈ Z ⊓ HardMathSupport.Kantor79.commutatorSpace H :=
    fun k hk z hz => ⟨hZH k hk z hz.1, zsr8D_apply_mem_commutatorSpace hk hz.2⟩
  rcases hirrH (Z ⊓ HardMathSupport.Kantor79.commutatorSpace H) bot_le inf_le_right
    hZHinv with hcase | hcase
  · left
    have hdimZ_le : Module.finrank (ZMod p) (Z : Submodule (ZMod p) U) ≤ 1 := by
      have e := Submodule.finrank_sup_add_finrank_inf_eq Z
        (HardMathSupport.Kantor79.commutatorSpace H)
      rw [hcase, finrank_bot, add_zero, hS.splitSupport.2.1] at e
      have hle : Module.finrank (ZMod p)
          ↥(Z ⊔ HardMathSupport.Kantor79.commutatorSpace H) ≤ l + 1 := by
        have hsup_le : Z ⊔ HardMathSupport.Kantor79.commutatorSpace H ≤
            HardMathSupport.Kantor79.commutatorSpace F :=
          sup_le hZF (zsr8D_commutatorSpace_mono hHleF)
        have := Submodule.finrank_mono hsup_le
        rw [hS.finrank_eq] at this
        exact this
      omega
    refine (Submodule.eq_of_le_of_finrank_eq hWZ ?_).symm
    have hmono := Submodule.finrank_mono hWZ
    rw [hS.degenerate.1] at hmono ⊢
    omega
  · right
    have hVH_le_Z : HardMathSupport.Kantor79.commutatorSpace H ≤ Z := by
      rw [← hcase]
      exact inf_le_left
    have hVF_le_Z : HardMathSupport.Kantor79.commutatorSpace F ≤ Z := by
      rw [← hVF_eq]
      exact sup_le hVH_le_Z hWZ
    exact le_antisymm hZF hVF_le_Z

private theorem zsr8D_VF_inf_centralizer_X (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {X : Subgroup (U ≃ₗ[ZMod p] U)} (hXF : X ≤ F)
    (hHleF : H ≤ F) (hHleX : H ≤ X)
    (hirrX : IrredOnSection X (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
      (HardMathSupport.Kantor79.commutatorSpace F))
    (hcplH : IsCompl (HardMathSupport.Kantor79.commutatorSpace H) (centralizerSpace H)) :
    HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace X =
      HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F := by
  have hZinv : ∀ k ∈ X, ∀ z ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace X,
      k z ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace X := by
    intro k hk z hz
    refine ⟨zsr8D_apply_mem_commutatorSpace (hXF hk) hz.1, ?_⟩
    have hm := Submodule.mem_map_of_mem (f := (k : U →ₗ[ZMod p] U)) hz.2
    rwa [map_centralizerSpace_of_mem_normalizer (H := X)
      (Subgroup.le_normalizer hk)] at hm
  rcases hirrX (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace X)
    (inf_le_inf_left _ (zsr8D_centralizerSpace_antitone hXF)) inf_le_left hZinv with
    hcase | hcase
  · exact hcase
  · exfalso
    have hVF_le_VX : HardMathSupport.Kantor79.commutatorSpace F ≤ centralizerSpace X := by
      rw [← hcase]
      exact inf_le_right
    have hVH_le_VHc : HardMathSupport.Kantor79.commutatorSpace H ≤ centralizerSpace H :=
      fun v hv => zsr8D_centralizerSpace_antitone hHleX
        (hVF_le_VX (zsr8D_commutatorSpace_mono hHleF hv))
    have hbot : HardMathSupport.Kantor79.commutatorSpace H = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro v hv
      have hmem : v ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H :=
        ⟨hv, hVH_le_VHc hv⟩
      rw [hcplH.inf_eq_bot] at hmem
      exact hmem
    have := congrArg (fun S : Submodule (ZMod p) U => Module.finrank (ZMod p) ↥S) hbot
    rw [hS.splitSupport.2.1, finrank_bot] at this
    have h2 := hS.two_le_of_dLarge hp
    omega

private theorem zsr8D_centralizer_X_eq
    [Module.Finite (ZMod p) U] {X : Subgroup (U ≃ₗ[ZMod p] U)} (hXF : X ≤ F)
    (hV0_eq : HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F =
      HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace X)
    (hZ_eq : HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace X =
      HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) :
    centralizerSpace X = centralizerSpace F := by
  have hle : centralizerSpace F ≤ centralizerSpace X := zsr8D_centralizerSpace_antitone hXF
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have eF := Submodule.finrank_sup_add_finrank_inf_eq
      (HardMathSupport.Kantor79.commutatorSpace F) (centralizerSpace F)
  have eX := Submodule.finrank_sup_add_finrank_inf_eq
      (HardMathSupport.Kantor79.commutatorSpace F) (centralizerSpace X)
  rw [← hV0_eq, hZ_eq] at eX
  omega

private theorem zsr8D_commutatorSpace_X_eq {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hHleX : H ≤ X) (hXF : X ≤ F)
    {g : U ≃ₗ[ZMod p] U} (hgX : g ∈ X)
    (hsupVH : HardMathSupport.Kantor79.commutatorSpace H ⊔
      HardMathSupport.Kantor79.movedSpace g = HardMathSupport.Kantor79.commutatorSpace F) :
    HardMathSupport.Kantor79.commutatorSpace X = HardMathSupport.Kantor79.commutatorSpace F := by
  have hVF_le_VX : HardMathSupport.Kantor79.commutatorSpace F ≤
      HardMathSupport.Kantor79.commutatorSpace X := by
    rw [← hsupVH]
    exact sup_le (zsr8D_commutatorSpace_mono hHleX)
      (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hgX)
  exact le_antisymm (zsr8D_commutatorSpace_mono hXF) hVF_le_VX

private theorem zsr8D_final (hp : p ≠ 2) {X : Subgroup (U ≃ₗ[ZMod p] U)} (hX : ReflGen p X)
    (hirrX' : IrredOnSection X
      (HardMathSupport.Kantor79.commutatorSpace X ⊓ centralizerSpace X)
      (HardMathSupport.Kantor79.commutatorSpace X))
    {Y : Submodule (ZMod p) U} (hY : ∀ g ∈ X, ∀ y ∈ Y, g y ∈ Y)
    (hVXcomm_eq : HardMathSupport.Kantor79.commutatorSpace X =
      HardMathSupport.Kantor79.commutatorSpace F)
    (hVXcen_eq : centralizerSpace X = centralizerSpace F) :
    ∀ g ∈ F, ∀ y ∈ Y, g y ∈ Y := by
  rcases commutatorSpace_le_or_le_centralizerSpace hp hX hirrX' hY with hle | hle
  · intro f hf y hy
    have hVFleY : HardMathSupport.Kantor79.commutatorSpace F ≤ Y := by
      rw [← hVXcomm_eq]
      exact hle
    have hfy : f y - y ∈ HardMathSupport.Kantor79.commutatorSpace F :=
      Submodule.subset_span ⟨f, hf, y, rfl⟩
    have hy' : f y - y ∈ Y := hVFleY hfy
    have hsum : f y = y + (f y - y) := by abel
    rw [hsum]
    exact Y.add_mem hy hy'
  · intro f hf y hy
    have hyV : y ∈ centralizerSpace F := by
      rw [← hVXcen_eq]
      exact hle hy
    rw [(mem_centralizerSpace.mp hyV) f hf]
    exact hy

open Module in
private theorem zsr8D_invariant_of_lt {p : ℕ} [Fact p.Prime] {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] {F H : Subgroup (U ≃ₗ[ZMod p] U)}
    {a : U ≃ₗ[ZMod p] U} {l : ℕ}
    (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hHX : H < X) (hXF : X ≤ F) (hX : ReflGen p X) {Y : Submodule (ZMod p) U}
    (hY : ∀ g ∈ X, ∀ y ∈ Y, g y ∈ Y) : ∀ g ∈ F, ∀ y ∈ Y, g y ∈ Y := by
  have hHleF : H ≤ F := fun h hh => by
    rw [hS.eq_closure]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem a hh)
  have hHleX : H ≤ X := le_of_lt hHX
  obtain ⟨g, hgX, hgRefl, hgH⟩ := zsr8D_exists_reflection_notMem hHX hX
  have hgF : g ∈ F := hXF hgX
  have hcplH : IsCompl (HardMathSupport.Kantor79.commutatorSpace H) (centralizerSpace H) :=
    hS.splitSupport.1
  have hirrH : IrredOnSection H ⊥ (HardMathSupport.Kantor79.commutatorSpace H) :=
    hS.splitSupport.2.2
  have hVH_inf_W := zsr8D_VH_inf_W hS hHleF
  have hVF_eq := zsr8D_VF_eq_sup hS hHleF hVH_inf_W
  obtain ⟨h, t, hhH, ht, htker, ht_ne, htX⟩ :=
    zsr8D_special_element hS hHleF hHleX hgX hgF hgH
  have htF : t ∈ F := (zsr8C_mem_kerSection htker).1
  have hVg_not_le := zsr8D_movedSpace_g_not_le hS hp hHleF hVF_eq hcplH hhH ht htF htker ht_ne
  have hsupVH := zsr8D_sup_movedSpace_g hS hHleF hgF hgRefl hVg_not_le
  have hVXcomm_eq := zsr8D_commutatorSpace_X_eq hHleX hXF hgX hsupVH
  have hV0_eq := zsr8D_V0_eq hS hp hXF htF htker ht_ne htX
  have hirrX := zsr8D_irred_X hS hHleX hHleF hVF_eq hirrH
  have hZ_eq := zsr8D_VF_inf_centralizer_X hS hp hXF hHleF hHleX hirrX hcplH
  have hVXcen_eq := zsr8D_centralizer_X_eq hXF hV0_eq hZ_eq
  have hirrX' : IrredOnSection X
      (HardMathSupport.Kantor79.commutatorSpace X ⊓ centralizerSpace X)
      (HardMathSupport.Kantor79.commutatorSpace X) := by
    rw [hVXcomm_eq, hVXcen_eq]
    exact hirrX
  exact zsr8D_final hp hX hirrX' hY hVXcomm_eq hVXcen_eq

private def zsr8D_kerSectionSubgroup (F : Subgroup (U ≃ₗ[ZMod p] U)) :
    Subgroup (U ≃ₗ[ZMod p] U) where
  carrier := {t | t ∈ F ∧ ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F,
    t v - v ∈ centralizerSpace F}
  one_mem' := ⟨F.one_mem, fun v _ => by simp⟩
  mul_mem' := by
    rintro t s ⟨htF, ht⟩ ⟨hsF, hs⟩
    refine ⟨F.mul_mem htF hsF, fun v hv => ?_⟩
    have hsv : s v ∈ HardMathSupport.Kantor79.commutatorSpace F :=
      zsr8D_apply_mem_commutatorSpace hsF hv
    have h1 : t (s v) - s v ∈ centralizerSpace F := ht (s v) hsv
    have h2 : s v - v ∈ centralizerSpace F := hs v hv
    have hsum : (t * s) v - v = (t (s v) - s v) + (s v - v) := by
      rw [LinearEquiv.mul_apply]; abel
    rw [hsum]
    exact (centralizerSpace F).add_mem h1 h2
  inv_mem' := by
    rintro t ⟨htF, ht⟩
    refine ⟨F.inv_mem htF, fun v hv => ?_⟩
    have htv : t v - v ∈ centralizerSpace F := ht v hv
    have h1 : t⁻¹ (t v - v) ∈ centralizerSpace F := by
      have hm := Submodule.mem_map_of_mem
        (f := ((t⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)) htv
      rwa [map_centralizerSpace_of_mem_normalizer (H := F)
        (Subgroup.le_normalizer (F.inv_mem htF))] at hm
    have heq : t⁻¹ v - v = -(t⁻¹ (t v - v)) := by
      rw [map_sub, show t⁻¹ (t v) = v from LinearEquiv.symm_apply_apply t v]
      abel
    rw [heq]
    exact (centralizerSpace F).neg_mem h1

open Module in
private theorem zsr8D_kerSection_eq (F : Subgroup (U ≃ₗ[ZMod p] U)) :
    kerSection F = zsr8D_kerSectionSubgroup F := by
  refine le_antisymm ?_ ?_
  · rw [kerSection]
    exact (Subgroup.closure_le _).mpr (fun x hx => hx)
  · intro x hx
    exact Subgroup.subset_closure hx

open Module in
private theorem zsr8D_commutator_le_kerSection {F H₁ : Subgroup (U ≃ₗ[ZMod p] U)}
    (hH₁F : H₁ ≤ F) : ⁅H₁, kerSection F⁆ ≤ kerSection F := by
  rw [zsr8D_kerSection_eq F]
  refine Subgroup.commutator_le.mpr ?_
  intro g hg t ht
  have hgt : g * t * g⁻¹ ∈ zsr8D_kerSectionSubgroup F := by
    refine ⟨F.mul_mem (F.mul_mem (hH₁F hg) ht.1) (F.inv_mem (hH₁F hg)), ?_⟩
    intro v hv
    have hgv : g⁻¹ v ∈ HardMathSupport.Kantor79.commutatorSpace F :=
      zsr8D_apply_mem_commutatorSpace (F.inv_mem (hH₁F hg)) hv
    have ht' : t (g⁻¹ v) - g⁻¹ v ∈ centralizerSpace F := ht.2 (g⁻¹ v) hgv
    have hgw : g (t (g⁻¹ v) - g⁻¹ v) ∈ centralizerSpace F := by
      have hm := Submodule.mem_map_of_mem (f := (g : U →ₗ[ZMod p] U)) ht'
      rwa [map_centralizerSpace_of_mem_normalizer (H := F)
        (Subgroup.le_normalizer (hH₁F hg))] at hm
    have heq : (g * t * g⁻¹) v - v = g (t (g⁻¹ v) - g⁻¹ v) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_sub,
        show g (g⁻¹ v) = v from LinearEquiv.apply_symm_apply g v]
    rw [heq]
    exact hgw
  have hprod : (g * t * g⁻¹) * t⁻¹ ∈ zsr8D_kerSectionSubgroup F :=
    (zsr8D_kerSectionSubgroup F).mul_mem hgt ((zsr8D_kerSectionSubgroup F).inv_mem ht)
  rw [commutatorElement_def]
  simpa only [mul_assoc] using hprod

open Module in
private theorem zsr8D_movedSpace_le_sup_span_of_codim_one {s : U ≃ₗ[ZMod p] U}
    {V₀ : Submodule (ZMod p) U} {W : Submodule (ZMod p) U} {u : U}
    (htop : V₀ ⊔ Submodule.span (ZMod p) {u} = ⊤)
    (hV0 : ∀ v ∈ V₀, s v - v ∈ W) :
    HardMathSupport.Kantor79.movedSpace s ≤
      W ⊔ Submodule.span (ZMod p) {s u - u} := by
  rw [HardMathSupport.Kantor79.movedSpace, LinearMap.range_eq_map, ← htop, Submodule.map_sup,
    Submodule.map_span]
  refine sup_le ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    intro v hv
    exact Submodule.mem_sup_left (hV0 v hv)
  · rw [Set.image_singleton]
    refine Submodule.span_le.mpr ?_
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Submodule.mem_sup_right (by
      have hval : ((s : U →ₗ[ZMod p] U) - 1) u = s u - u := by
        rw [LinearMap.sub_apply, Module.End.one_apply]; rfl
      rw [hval]
      exact Submodule.subset_span (Set.mem_singleton _))

open Module in
private theorem zsr8D_pow_H_data (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H)
    (hH₁' : ReflGen p H₁) (hH₁1 : H₁ ≠ ⊥) :
    H ≤ F ∧ H₁ ≤ F ∧ ⁅H₁, kerSection F⁆ ≤ kerSection F ∧
      HardMathSupport.Kantor79.commutatorSpace (⁅H₁, kerSection F⁆) =
        HardMathSupport.Kantor79.commutatorSpace H₁ ⊔
          (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) ∧
      HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace F = ⊥ := by
  have hHleF : H ≤ F := fun h hh => by
    rw [hS.eq_closure]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem a hh)
  have hH₁F : H₁ ≤ F := le_trans hH₁ hHleF
  have hSleT : ⁅H₁, kerSection F⁆ ≤ kerSection F := zsr8D_commutator_le_kerSection hH₁F
  have hVS := hS.commutatorSpace_commutator hp hH₁ hH₁' hH₁1
  have hcplH := hS.splitSupport.1
  have hVH₁_inf_C : HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace F = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro v hv
    have hvH : v ∈ HardMathSupport.Kantor79.commutatorSpace H :=
      zsr8D_commutatorSpace_mono hH₁ hv.1
    have hvHc : v ∈ centralizerSpace H := zsr8D_centralizerSpace_antitone hHleF hv.2
    have hmem : v ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H :=
      ⟨hvH, hvHc⟩
    rw [hcplH.inf_eq_bot] at hmem
    exact hmem
  exact ⟨hHleF, hH₁F, hSleT, hVS, hVH₁_inf_C⟩

private theorem zsr8D_pow_V0_data (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] :
    ∃ u₀ : U, u₀ ∉ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F ∧
      (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) ⊔
        Submodule.span (ZMod p) {u₀} = ⊤ := by
  have hn : 1 ≤ Module.finrank (ZMod p) U := by
    have hle : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace F) ≤
        Module.finrank (ZMod p) U := Submodule.finrank_le _
    rw [hS.finrank_eq] at hle
    have := hS.two_le_of_dLarge hp
    omega
  have hV0ne : (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) ≠ ⊤ := by
    intro htop
    have hfin := hS.finrank_sup_eq hp
    rw [htop, finrank_top] at hfin
    omega
  obtain ⟨u₀, hu₀⟩ : ∃ u, u ∉ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F := by
    by_contra h
    push Not at h
    exact hV0ne (eq_top_iff.mpr fun x _ => h x)
  refine ⟨u₀, hu₀, ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  rw [Submodule.finrank_sup_span_singleton hu₀, hS.finrank_sup_eq hp]
  omega

private theorem zsr8D_pow_q_data {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} :
    (Submodule.mkQ (centralizerSpace F) : U →ₗ[ZMod p] (U ⧸ centralizerSpace F)).ker =
        centralizerSpace F ∧
      Submodule.map (Submodule.mkQ (centralizerSpace F)) (centralizerSpace F) = ⊥ ∧
      Submodule.map (Submodule.mkQ (centralizerSpace F))
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = ⊥ ∧
      Submodule.comap (Submodule.mkQ (centralizerSpace F))
        (Submodule.map (Submodule.mkQ (centralizerSpace F))
          (HardMathSupport.Kantor79.commutatorSpace H₁)) =
        centralizerSpace F ⊔ HardMathSupport.Kantor79.commutatorSpace H₁ := by
  let q : U →ₗ[ZMod p] (U ⧸ centralizerSpace F) := Submodule.mkQ (centralizerSpace F)
  have hq_ker : q.ker = centralizerSpace F := by simp [q]
  have hqC : Submodule.map q (centralizerSpace F) = ⊥ := by simp [q]
  have hqW : Submodule.map q
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = ⊥ :=
    le_antisymm (le_trans (Submodule.map_mono inf_le_right) (le_of_eq hqC)) bot_le
  have hcomap : Submodule.comap q
      (Submodule.map q (HardMathSupport.Kantor79.commutatorSpace H₁)) =
      centralizerSpace F ⊔ HardMathSupport.Kantor79.commutatorSpace H₁ := by
    simp [q]
  exact ⟨hq_ker, hqC, hqW, hcomap⟩

private theorem zsr8D_pow_phi_mem {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} {u₀ : U}
    {Sgrp : Subgroup (U ≃ₗ[ZMod p] U)}
    {q : U →ₗ[ZMod p] (U ⧸ centralizerSpace F)}
    (hcomap : Submodule.comap q (Submodule.map q
        (HardMathSupport.Kantor79.commutatorSpace H₁)) =
      centralizerSpace F ⊔ HardMathSupport.Kantor79.commutatorSpace H₁)
    (hVS : HardMathSupport.Kantor79.commutatorSpace Sgrp =
      HardMathSupport.Kantor79.commutatorSpace H₁ ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F))
    (hSleT : Sgrp ≤ kerSection F) (s : Sgrp) :
    q (((s : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀) ∈
      Submodule.map q (HardMathSupport.Kantor79.commutatorSpace H₁) := by
  refine (Submodule.mem_comap (f := q) (p := Submodule.map q
    (HardMathSupport.Kantor79.commutatorSpace H₁))).mp ?_
  rw [hcomap]
  have hsT : ((s : Sgrp) : U ≃ₗ[ZMod p] U) ∈ kerSection F := hSleT s.2
  have h1 : ((s : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀ ∈
      HardMathSupport.Kantor79.movedSpace ((s : Sgrp) : U ≃ₗ[ZMod p] U) := ⟨u₀, rfl⟩
  have h2 : HardMathSupport.Kantor79.movedSpace ((s : Sgrp) : U ≃ₗ[ZMod p] U) ≤
      HardMathSupport.Kantor79.commutatorSpace H₁ ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) := by
    rw [← hVS]
    exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace s.2
  have h2' : HardMathSupport.Kantor79.commutatorSpace H₁ ⊔
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) ≤
      centralizerSpace F ⊔ HardMathSupport.Kantor79.commutatorSpace H₁ :=
    sup_le le_sup_right (le_trans inf_le_right le_sup_left)
  exact h2' (h2 h1)

private theorem zsr8D_pow_phi_add (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {u₀ : U}
    {Sgrp : Subgroup (U ≃ₗ[ZMod p] U)}
    {q : U →ₗ[ZMod p] (U ⧸ centralizerSpace F)} (hq_ker : q.ker = centralizerSpace F)
    (hSleT : Sgrp ≤ kerSection F) :
    ∀ s s' : Sgrp, q (((s * s' : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀) =
      q (((s : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀) +
        q (((s' : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀) := by
  intro s s'
  have htT : ((s : Sgrp) : U ≃ₗ[ZMod p] U) ∈ kerSection F := hSleT s.2
  have hs'F : ((s' : Sgrp) : U ≃ₗ[ZMod p] U) ∈ F := kerSection_le (hSleT s'.2)
  have hwV : ((s' : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀ ∈
      HardMathSupport.Kantor79.commutatorSpace F :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hs'F ⟨u₀, rfl⟩
  have hNW : ((s : Sgrp) : U ≃ₗ[ZMod p] U)
      (((s' : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀) -
        (((s' : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀) ∈ centralizerSpace F := by
    by_cases h1 : ((s : Sgrp) : U ≃ₗ[ZMod p] U) = 1
    · rw [h1]; simp
    · have hmem := (hS.finrank_movedSpace_of_mem_kerSection hp htT h1).1
        (((s' : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀) (Submodule.mem_sup_left hwV)
      exact (Submodule.mem_inf.mp hmem).2
  have hkey : (((s * s' : Sgrp) : U ≃ₗ[ZMod p] U)) u₀ - u₀ =
      (((s : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀ +
        (((s' : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀)) +
        (((s : Sgrp) : U ≃ₗ[ZMod p] U)
          (((s' : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀) -
            (((s' : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀)) := by
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, map_sub]
    abel
  rw [hkey, map_add, map_add]
  have hqN : q (((s : Sgrp) : U ≃ₗ[ZMod p] U)
      (((s' : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀) -
        (((s' : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀)) = 0 := by
    rw [← LinearMap.mem_ker, hq_ker]
    exact hNW
  rw [hqN, add_zero]

private theorem zsr8D_pow_span (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {u₀ : U}
    {Sgrp : Subgroup (U ≃ₗ[ZMod p] U)}
    (htop : (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) ⊔
      Submodule.span (ZMod p) {u₀} = ⊤)
    {q : U →ₗ[ZMod p] (U ⧸ centralizerSpace F)}
    (hqW : Submodule.map q
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = ⊥)
    (hSleT : Sgrp ≤ kerSection F) :
    Submodule.span (ZMod p)
        (Set.range (fun s : Sgrp => q (((s : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀))) =
      Submodule.map q (HardMathSupport.Kantor79.commutatorSpace Sgrp) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro y ⟨s, rfl⟩
    exact Submodule.mem_map_of_mem (f := q)
      (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace s.2 ⟨u₀, rfl⟩)
  · refine (Submodule.map_le_iff_le_comap).mpr ?_
    rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.span_le]
    rintro x ⟨s, hsS, v, rfl⟩
    change q ((s : U ≃ₗ[ZMod p] U) v - v) ∈ Submodule.span (ZMod p)
      (Set.range (fun t : Sgrp => q (((t : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀)))
    have hsT : (s : U ≃ₗ[ZMod p] U) ∈ kerSection F := hSleT hsS
    have hmov : (s : U ≃ₗ[ZMod p] U) v - v ∈
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) ⊔
          Submodule.span (ZMod p) {(s : U ≃ₗ[ZMod p] U) u₀ - u₀} := by
      by_cases h1 : (s : U ≃ₗ[ZMod p] U) = 1
      · rw [h1]; simp
      · exact zsr8D_movedSpace_le_sup_span_of_codim_one
          (V₀ := HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F)
          (W := HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
          htop (fun w hw => (hS.finrank_movedSpace_of_mem_kerSection hp hsT h1).1 w hw)
          ⟨v, rfl⟩
    have hmapmem : q ((s : U ≃ₗ[ZMod p] U) v - v) ∈
        Submodule.map q ((HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) ⊔
          Submodule.span (ZMod p) {(s : U ≃ₗ[ZMod p] U) u₀ - u₀}) :=
      Submodule.mem_map_of_mem (f := q) hmov
    rw [Submodule.map_sup, Submodule.map_span, hqW] at hmapmem
    simp only [bot_sup_eq] at hmapmem
    refine Submodule.span_mono ?_ hmapmem
    rintro z hz
    rcases hz with ⟨w, hw, rfl⟩
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨⟨s, hsS⟩, rfl⟩

private theorem zsr8D_pow_mapVS {H₁ : Subgroup (U ≃ₗ[ZMod p] U)}
    {Sgrp : Subgroup (U ≃ₗ[ZMod p] U)}
    {q : U →ₗ[ZMod p] (U ⧸ centralizerSpace F)}
    (hqC : Submodule.map q (centralizerSpace F) = ⊥)
    (hVS : HardMathSupport.Kantor79.commutatorSpace Sgrp =
      HardMathSupport.Kantor79.commutatorSpace H₁ ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)) :
    Submodule.map q (HardMathSupport.Kantor79.commutatorSpace Sgrp) =
      Submodule.map q (HardMathSupport.Kantor79.commutatorSpace H₁) := by
  have harg : HardMathSupport.Kantor79.commutatorSpace Sgrp ⊔ centralizerSpace F =
      HardMathSupport.Kantor79.commutatorSpace H₁ ⊔ centralizerSpace F := by
    rw [hVS, sup_assoc, sup_eq_right.mpr (inf_le_right : _ ≤ centralizerSpace F)]
  have hmap_sup : Submodule.map q (HardMathSupport.Kantor79.commutatorSpace Sgrp ⊔
      centralizerSpace F) = Submodule.map q (HardMathSupport.Kantor79.commutatorSpace Sgrp) := by
    rw [Submodule.map_sup, hqC, sup_bot_eq]
  have hmap_sup' : Submodule.map q (HardMathSupport.Kantor79.commutatorSpace H₁ ⊔
      centralizerSpace F) = Submodule.map q (HardMathSupport.Kantor79.commutatorSpace H₁) := by
    rw [Submodule.map_sup, hqC, sup_bot_eq]
  rw [← hmap_sup, ← hmap_sup', harg]

private theorem zsr8D_pow_finite [Module.Finite (ZMod p) U] (H₁ : Subgroup (U ≃ₗ[ZMod p] U)) :
    Finite (⁅H₁, kerSection F⁆ : Subgroup (U ≃ₗ[ZMod p] U)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have : Fintype U :=
    Fintype.ofEquiv (Fin (Module.finrank (ZMod p) U) → ZMod p)
      (Module.finBasis (ZMod p) U).equivFun.symm.toEquiv
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun e f h => LinearEquiv.ext (fun x => congrFun h x))
  exact Subtype.finite

private theorem zsr8D_pow_range_data (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {u₀ : U} {Sgrp : Subgroup (U ≃ₗ[ZMod p] U)}
    (htop : (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) ⊔
      Submodule.span (ZMod p) {u₀} = ⊤)
    {q : U →ₗ[ZMod p] (U ⧸ centralizerSpace F)} (hq_ker : q.ker = centralizerSpace F)
    (hqW : Submodule.map q
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = ⊥)
    (hSleT : Sgrp ≤ kerSection F) :
    (Submodule.map q (HardMathSupport.Kantor79.commutatorSpace Sgrp) :
      Set (U ⧸ centralizerSpace F)) ⊆
      Set.range (fun s : Sgrp => q (((s : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀)) := by
  have hφadd := zsr8D_pow_phi_add (u₀ := u₀) hS hp hq_ker hSleT
  let A : AddSubgroup (U ⧸ centralizerSpace F) :=
    { carrier := Set.range (fun s : Sgrp => q (((s : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀))
      zero_mem' := ⟨1, by simp⟩
      add_mem' := by
        rintro _ _ ⟨s, rfl⟩ ⟨s', rfl⟩
        exact ⟨s * s', hφadd s s'⟩
      neg_mem' := by
        rintro _ ⟨s, rfl⟩
        refine ⟨s⁻¹, ?_⟩
        have h := hφadd s⁻¹ s
        have h0 : q (((((s⁻¹ * s : Sgrp) : U ≃ₗ[ZMod p] U))) u₀ - u₀) = 0 := by
          rw [show (s⁻¹ * s : Sgrp) = 1 from inv_mul_cancel s]
          simp
        rw [h0] at h
        exact eq_neg_of_add_eq_zero_left h.symm }
  have hspan := zsr8D_pow_span hS hp htop hqW hSleT
  have hA_le : AddSubgroup.toZModSubmodule p A ≤
      Submodule.map q (HardMathSupport.Kantor79.commutatorSpace Sgrp) := by
    intro y hy
    rcases hy with ⟨s, rfl⟩
    exact Submodule.mem_map_of_mem (f := q)
      (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace s.2 ⟨u₀, rfl⟩)
  have hspan_le_A : Submodule.span (ZMod p)
      (Set.range (fun s : Sgrp => q (((s : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀))) ≤
      AddSubgroup.toZModSubmodule p A := by
    rw [Submodule.span_le]
    rintro z ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  have hrange : (Submodule.map q (HardMathSupport.Kantor79.commutatorSpace Sgrp) :
      Set (U ⧸ centralizerSpace F)) ⊆
      Set.range (fun s : Sgrp => q (((s : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀)) := by
    intro y hy
    have hle := le_trans (le_of_eq hspan.symm) hspan_le_A
    have h' := hle hy
    change y ∈ Set.range (fun s : Sgrp => q (((s : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀)) at h'
    exact h'
  exact hrange

private theorem zsr8D_pow_card_image_le (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} {u₀ : U}
    (htop : (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) ⊔
      Submodule.span (ZMod p) {u₀} = ⊤)
    {q : U →ₗ[ZMod p] (U ⧸ centralizerSpace F)} (hq_ker : q.ker = centralizerSpace F)
    (hqC : Submodule.map q (centralizerSpace F) = ⊥)
    (hqW : Submodule.map q
      (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = ⊥)
    (hcomap : Submodule.comap q (Submodule.map q
        (HardMathSupport.Kantor79.commutatorSpace H₁)) =
      centralizerSpace F ⊔ HardMathSupport.Kantor79.commutatorSpace H₁)
    (hSleT : ⁅H₁, kerSection F⁆ ≤ kerSection F)
    (hVS : HardMathSupport.Kantor79.commutatorSpace ⁅H₁, kerSection F⁆ =
      HardMathSupport.Kantor79.commutatorSpace H₁ ⊔
        (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)) :
    Nat.card ↥(Submodule.map q (HardMathSupport.Kantor79.commutatorSpace H₁)) ≤
      Nat.card (⁅H₁, kerSection F⁆ : Subgroup (U ≃ₗ[ZMod p] U)) := by
  let Sgrp : Subgroup (U ≃ₗ[ZMod p] U) := ⁅H₁, kerSection F⁆
  let φ : Sgrp → ↥(Submodule.map q (HardMathSupport.Kantor79.commutatorSpace H₁)) :=
    fun s => ⟨q (((s : Sgrp) : U ≃ₗ[ZMod p] U) u₀ - u₀),
      zsr8D_pow_phi_mem hcomap hVS hSleT s⟩
  have hrange := zsr8D_pow_range_data hS hp htop hq_ker hqW hSleT
  have hmapVS := zsr8D_pow_mapVS hqC hVS
  have hfin : Finite Sgrp := zsr8D_pow_finite H₁
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : (y : U ⧸ centralizerSpace F) ∈
        Submodule.map q (HardMathSupport.Kantor79.commutatorSpace Sgrp) := by
      rw [hmapVS]
      exact y.2
    obtain ⟨s, hs⟩ := hrange hy
    exact ⟨s, Subtype.ext hs⟩
  exact Nat.card_le_card_of_surjective φ hsurj

private theorem zsr8D_pow_card_eq [Module.Finite (ZMod p) U]
    {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} {q : U →ₗ[ZMod p] (U ⧸ centralizerSpace F)}
    (hq_ker : q.ker = centralizerSpace F)
    (hVH₁_inf_C : HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace F = ⊥) :
    Nat.card ↥(Submodule.map q (HardMathSupport.Kantor79.commutatorSpace H₁)) =
      p ^ Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H₁) := by
  have hfr : Module.finrank (ZMod p)
      ↥(Submodule.map q (HardMathSupport.Kantor79.commutatorSpace H₁)) =
      Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H₁) := by
    have hinj : Function.Injective
        (q.comp (HardMathSupport.Kantor79.commutatorSpace H₁).subtype) := by
      intro x y hxy
      have hxy' : q ((x : U)) = q ((y : U)) := by simpa using hxy
      have hmem : (x : U) - (y : U) ∈ centralizerSpace F := by
        rw [← hq_ker, LinearMap.mem_ker]
        rw [map_sub, hxy', sub_self]
      have hxmem : (x : U) - (y : U) ∈ HardMathSupport.Kantor79.commutatorSpace H₁ :=
        (HardMathSupport.Kantor79.commutatorSpace H₁).sub_mem x.2 y.2
      have hzero : (x : U) - (y : U) ∈
          HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace F := ⟨hxmem, hmem⟩
      rw [hVH₁_inf_C] at hzero
      exact Subtype.ext (sub_eq_zero.mp (by simpa using hzero))
    have hfr := LinearMap.finrank_range_of_inj hinj
    rwa [LinearMap.range_comp, Submodule.range_subtype] at hfr
  have : Module.Finite (ZMod p) (U ⧸ centralizerSpace F) :=
    Module.Finite.of_surjective (Submodule.mkQ (centralizerSpace F))
      (LinearMap.range_eq_top.mp (Submodule.range_mkQ (p := centralizerSpace F)))
  have : Module.Finite (ZMod p)
      ↥(Submodule.map q (HardMathSupport.Kantor79.commutatorSpace H₁)) :=
    Module.Finite.of_injective (Submodule.subtype _) Subtype.val_injective
  calc Nat.card ↥(Submodule.map q (HardMathSupport.Kantor79.commutatorSpace H₁))
      = Nat.card (ZMod p) ^ Module.finrank (ZMod p)
          ↥(Submodule.map q (HardMathSupport.Kantor79.commutatorSpace H₁)) :=
        Module.natCard_eq_pow_finrank
    _ = p ^ Module.finrank (ZMod p)
          ↥(Submodule.map q (HardMathSupport.Kantor79.commutatorSpace H₁)) := by
        rw [Nat.card_zmod]
    _ = p ^ Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H₁) := by
        rw [hfr]

open Module in
private theorem zsr8D_pow_finrank_le_card {p : ℕ} [Fact p.Prime] {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] {F H : Subgroup (U ≃ₗ[ZMod p] U)}
    {a : U ≃ₗ[ZMod p] U} {l : ℕ}
    (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H) (hH₁' : ReflGen p H₁)
    (hH₁1 : H₁ ≠ ⊥) :
    p ^ Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H₁) ≤
      Nat.card (⁅H₁, kerSection F⁆ : Subgroup (U ≃ₗ[ZMod p] U)) := by
  obtain ⟨-, -, hSleT, hVS, hVH₁_inf_C⟩ := zsr8D_pow_H_data hS hp hH₁ hH₁' hH₁1
  obtain ⟨u₀, hu₀, htop⟩ := zsr8D_pow_V0_data hS hp
  let q : U →ₗ[ZMod p] (U ⧸ centralizerSpace F) := Submodule.mkQ (centralizerSpace F)
  obtain ⟨hq_ker, hqC, hqW, hcomap⟩ := zsr8D_pow_q_data (H₁ := H₁)
  have hcard_le := zsr8D_pow_card_image_le hS hp htop hq_ker hqC hqW hcomap hSleT hVS
  have hcard_eq := zsr8D_pow_card_eq hq_ker hVH₁_inf_C
  rw [← hcard_eq]
  simpa only [q] using hcard_le

theorem invariant_of_lt (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {X : Subgroup (U ≃ₗ[ZMod p] U)}
    (hHX : H < X) (hXF : X ≤ F) (hX : ReflGen p X) {Y : Submodule (ZMod p) U}
    (hY : ∀ g ∈ X, ∀ y ∈ Y, g y ∈ Y) : ∀ g ∈ F, ∀ y ∈ Y, g y ∈ Y := by
  exact zsr8D_invariant_of_lt hS hp hHX hXF hX hY

theorem pow_finrank_le_card (hS : LemmaOneSixSetting F H a l) (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁ : H₁ ≤ H)
    (hH₁' : ReflGen p H₁) (hH₁1 : H₁ ≠ ⊥) :
    p ^ Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H₁) ≤
      Nat.card (⁅H₁, kerSection F⁆ : Subgroup (U ≃ₗ[ZMod p] U)) := by
  exact zsr8D_pow_finrank_le_card hS hp hH₁ hH₁' hH₁1

end LemmaOneSixSetting

end CFSG.StandardType.ZS
