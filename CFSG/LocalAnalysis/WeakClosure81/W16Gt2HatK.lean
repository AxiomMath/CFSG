module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2Hat
public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2Img

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem cj_eq_conjSubgroup' {p : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod p) W]
    (g : LGL p W) (A : Subgroup (LGL p W)) : cj g A = conjSubgroup A g⁻¹ := by
  ext x
  rw [mem_cj, mem_conjSubgroup_iff]
  simp

namespace Cfg1620

variable {M V₀ V U S R H : Subgroup G} {g : G} {B : Subgroup G}

theorem conjClosure_le_H (c : Cfg1620 M V₀ V U S R H g B) : conjClosure V H ≤ H := by
  have hVH : V ≤ H := c.V_le_R.trans c.mem.1
  exact conjClosure_le fun h hh v hv => H.mul_mem (H.mul_mem hh (hVH hv)) (H.inv_mem hh)

theorem eq_conjClosure_sup (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) : H = conjClosure V H ⊔ R :=
  c.cex.eq_conjClosure_sup_of_min h15 hS c.S_le c.mem c.min c.g_mem c.g_not

theorem exists_mem_conjClosure_conjSubgroup_eq (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) {h : G} (hh : h ∈ H) :
    ∃ k ∈ conjClosure V H, conjSubgroup V h = conjSubgroup V k ∧
      conjSubgroup V₀ h = conjSubgroup V₀ k := by
  have hh' : h ∈ R ⊔ conjClosure V H := by
    rw [sup_comm, ← eq_conjClosure_sup h15 hS c]
    exact hh
  have hnorm : R ≤ Subgroup.normalizer (conjClosure V H : Set G) :=
    c.mem.1.trans (le_normalizer_conjClosure V H)
  have hh'' : h ∈ (↑(R ⊔ conjClosure V H) : Set G) := hh'
  rw [Subgroup.coe_mul_of_left_le_normalizer_right R (conjClosure V H) hnorm] at hh''
  obtain ⟨r, hr, k, hk, rfl⟩ := hh''
  have hrM : r ∈ M := (c.sylow.le.trans (cTilde_le_M M V₀ V)) hr
  have hrV : r ∈ normalizer (V : Set G) := by
    rw [c.cex.hyp.h6.normalizer_eq]
    exact hrM
  have hrV₀ : r ∈ normalizer (V₀ : Set G) := by
    rw [c.cex.hyp.normalizer₀]
    exact hrM
  refine ⟨k, hk, ?_, ?_⟩
  · rw [← conjSubgroup_conjSubgroup V r k, conjSubgroup_eq_iff_mem_normalizer.2 hrV]
  · rw [← conjSubgroup_conjSubgroup V₀ r k, conjSubgroup_eq_iff_mem_normalizer.2 hrV₀]

theorem comm_le_of_relIndex_two_pow (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (hS : Std15 G) (c : Cfg1620 M V₀ V U S R H g B) {Y : Subgroup G}
    (hY : (Y.subgroupOf H).Normal)
    (hKY : conjClosure V H ⊓ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) ≤ Y)
    (hYK : Y ≤ conjClosure V H)
    (hY2 : ∃ k : ℕ, (conjClosure V H ⊓
      (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G))).relIndex Y = 2 ^ k) :
    ⁅Y, conjClosure V H⁆ ≤ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
  set I : Subgroup G := conjClosure (U ⊔ V₀) H with hI
  set CH : Subgroup G := H ⊓ centralizer (I : Set G) with hCH
  have hKH : conjClosure V H ≤ H := conjClosure_le_H c
  have hYH : Y ≤ H := hYK.trans hKH
  have hCHleH : CH ≤ H := by rw [hCH]; exact inf_le_left
  have hCHnormH : H ≤ Subgroup.normalizer (CH : Set G) := by
    intro h hh
    rw [hCH]
    exact mem_normalizer_inf_centralizer_wc16 (Subgroup.le_normalizer hh)
      (le_normalizer_conjClosure (U ⊔ V₀) H hh)
  have hYnormCH : Y ≤ Subgroup.normalizer (CH : Set G) := hYH.trans hCHnormH
  have hXsub : ((CH ⊔ Y).subgroupOf H).Normal := by
    rw [Subgroup.subgroupOf_sup (A := CH) (A' := Y) (B := H) hCHleH hYH]
    haveI : (CH.subgroupOf H).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (H := H) (N := CH) hCHnormH
    haveI : (Y.subgroupOf H).Normal := hY
    infer_instance
  have hX2 : ∃ k : ℕ, (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)).relIndex
      (CH ⊔ Y) = 2 ^ k := by
    obtain ⟨k, hk⟩ := hY2
    refine ⟨k, ?_⟩
    have hk' : (conjClosure V H ⊓ CH).relIndex Y = 2 ^ k := by rw [hCH]; exact hk
    have h1 : CH.relIndex (CH ⊔ Y) = CH.relIndex Y := by
      have h := B2F.relIndex_sup_eq_of_le_normalizer' (D := CH) (T := Y) hYnormCH
      rw [sup_comm] at h
      exact h
    have hinf : CH ⊓ Y = (conjClosure V H ⊓ CH) ⊓ Y := by
      apply le_antisymm
      · intro x hx; exact ⟨⟨hYK hx.2, hx.1⟩, hx.2⟩
      · intro x hx; exact ⟨hx.1.2, hx.2⟩
    have h2 : CH.relIndex Y = (conjClosure V H ⊓ CH).relIndex Y := by
      rw [← Subgroup.inf_relIndex_right CH Y, hinf,
        Subgroup.inf_relIndex_right (conjClosure V H ⊓ CH) Y]
    rw [← hCH]
    exact h1.trans (h2.trans hk')
  have hCX : H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) ≤ CH ⊔ Y := by
    rw [hCH]; exact le_sup_left
  have hXM : CH ⊔ Y ≤ M := by
    have h := le_conjSubgroup_of_relIndex_two_pow h1 h15 hS c hCX (sup_le hCHleH hYH)
      hXsub hX2 (h := 1) H.one_mem
    rwa [conjSubgroup_one] at h
  have hYM : Y ≤ M := le_trans le_sup_right hXM
  have hVX : V ⊓ (CH ⊔ Y) = U ⊔ V₀ :=
    inf_eq_sup_of_relIndex_two_pow h1 h5 h15 hS c hCX (sup_le hCHleH hYH) hXsub hX2
  have hV₀CH : V₀ ≤ CH := by
    rw [hCH]
    refine le_inf (c.cex.hyp.h6.le.trans (c.V_le_R.trans c.mem.1)) ?_
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    exact B2F.isElemAbelian_comm (c.mem.isElemAbelian c.cex) hi
      (le_conjClosure (U ⊔ V₀) H (Subgroup.mem_sup_right hw))
  have hUCH : U ≤ CH := by
    rw [hCH]
    refine le_inf (c.cex.le.trans (c.V_le_R.trans c.mem.1)) ?_
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    exact B2F.isElemAbelian_comm (c.mem.isElemAbelian c.cex) hi
      (le_sup_left.trans (le_conjClosure (U ⊔ V₀) H) hu)
  have hsupCH : U ⊔ V₀ ≤ CH := sup_le hUCH hV₀CH
  have hYnorm : H ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYH).1 hY
  have hYV : ⁅Y, V⁆ ≤ CH := by
    have h1 : ⁅Y, V⁆ ≤ Y := Subgroup.commutator_le.2 fun y hy v hv => by
      have hvy : v * y * v⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.1 (hYnorm ((c.V_le_R.trans c.mem.1) hv)) y).1 hy
      have hconj : y * v * y⁻¹ * v⁻¹ = y * (v * y * v⁻¹)⁻¹ := by group
      rw [commutatorElement_def, hconj]
      exact Y.mul_mem hy (Y.inv_mem hvy)
    have h2 : ⁅Y, V⁆ ≤ V := Subgroup.commutator_le.2 fun y hy v hv => by
      have hyN : y ∈ Subgroup.normalizer (V : Set G) := by
        rw [c.cex.hyp.h6.normalizer_eq]; exact hYM hy
      rw [commutatorElement_def]
      exact V.mul_mem ((Subgroup.mem_normalizer_iff.1 hyN v).1 hv) (V.inv_mem hv)
    have h3 : Y ⊓ V ≤ CH := by
      have hle : Y ⊓ V ≤ V ⊓ (CH ⊔ Y) := le_inf inf_le_right (inf_le_left.trans le_sup_right)
      rw [hVX] at hle
      exact hle.trans hsupCH
    exact le_trans (le_inf h1 h2) h3
  refine Subgroup.commutator_le.2 fun y hy k hk => ?_
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨h, hh, v, hv, rfl⟩ := hx
      have hhY : h⁻¹ * y * h ∈ Y := by
        simpa using (Subgroup.mem_normalizer_iff.1 (hYnorm (H.inv_mem hh)) y).1 hy
      have hcomm : ⁅h⁻¹ * y * h, v⁆ ∈ CH := hYV (Subgroup.commutator_mem_commutator hhY hv)
      have hconj : ⁅y, h * v * h⁻¹⁆ = h * ⁅h⁻¹ * y * h, v⁆ * h⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]; group
      rw [hconj]
      exact (Subgroup.mem_normalizer_iff.1 (hCHnormH hh) ⁅h⁻¹ * y * h, v⁆).1 hcomm
  | one => rw [commutatorElement_one_right]; exact CH.one_mem
  | mul x z hx hz ihx ihz =>
      have hxH : x ∈ H := conjClosure_le_H c hx
      have hmem : x * ⁅y, z⁆ * x⁻¹ ∈ CH :=
        (Subgroup.mem_normalizer_iff.1 (hCHnormH hxH) ⁅y, z⁆).1 ihz
      rw [commutatorElement_mul_right_eq_mul_conj]
      simpa [mul_assoc] using CH.mul_mem ihx hmem
  | inv x hx ih =>
      have hxH : x ∈ H := conjClosure_le_H c hx
      have hxinvH : x⁻¹ ∈ H := H.inv_mem hxH
      have hxy : ⁅x, y⁆ ∈ CH := by
        simpa [commutatorElement_inv] using CH.inv_mem ih
      rw [commutatorElement_inv_right]
      simpa using (Subgroup.mem_normalizer_iff.1 (hCHnormH hxinvH) ⁅x, y⁆).1 hxy

theorem inf_centralizer_conjClosure_eq_bot (c : Cfg1620 M V₀ V U S R H g B) :
    V ⊓ centralizer (conjClosure V H : Set G) = ⊥ := by
  have hCU : V ⊓ centralizer (conjClosure V H : Set G) ≤ U := by
    intro x hx
    have hxL : x ∈ V ⊓ centralizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G) :=
      ⟨hx.1, Subgroup.centralizer_le c.L_le_conjClosure hx.2⟩
    rwa [c.centralizer_L] at hxL
  have hCR : V ⊓ centralizer (conjClosure V H : Set G) ≤ centralizer (R : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hxV : x ∈ V := hx.1
    have hxK : x ∈ centralizer (conjClosure V H : Set G) := hx.2
    have hrM : r ∈ M := (c.sylow.le.trans (cTilde_le_M M V₀ V)) hr
    have hrV : r ∈ Subgroup.normalizer (V : Set G) := by
      rw [c.cex.hyp.h6.normalizer_eq]
      exact hrM
    have hrK : r ∈ Subgroup.normalizer (conjClosure V H : Set G) :=
      le_normalizer_conjClosure V H (c.mem.1 hr)
    have hcV : ⁅r, x⁆ ∈ V := by
      rw [commutatorElement_def]
      exact V.mul_mem ((Subgroup.mem_normalizer_iff.1 hrV x).1 hxV) (V.inv_mem hxV)
    have hnC : r ∈ Subgroup.normalizer
        (Subgroup.centralizer (conjClosure V H : Set G) : Set G) := by
      rw [← conjSubgroup_eq_iff_mem_normalizer, E3.conjSubgroup_centralizer,
        conjSubgroup_eq_iff_mem_normalizer.2 hrK]
    have hrxr : r * x * r⁻¹ ∈ centralizer (conjClosure V H : Set G) :=
      (Subgroup.mem_normalizer_iff.1 hnC x).1 hxK
    have hcK : ⁅r, x⁆ ∈ centralizer (conjClosure V H : Set G) := by
      rw [commutatorElement_def]
      exact (centralizer (conjClosure V H : Set G)).mul_mem hrxr
        ((centralizer (conjClosure V H : Set G)).inv_mem hxK)
    have hcV₀ : ⁅r, x⁆ ∈ V₀ := by
      rw [commutatorElement_def]
      exact (FourteenTwo.mem_cTilde_iff_comm.1 (c.sylow.le hr)).2.2 x hxV
    have hbot : ⁅r, x⁆ ∈ (⊥ : Subgroup G) := by
      have hmem : ⁅r, x⁆ ∈ U ⊓ V₀ := ⟨hCU ⟨hcV, hcK⟩, hcV₀⟩
      rwa [c.cex.inf_eq_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.1 (Subgroup.mem_bot.1 hbot)
  have hne : ¬ F11.CTilde M V₀ V ≤ centralizer (V : Set G) := by
    obtain ⟨a, ha, han⟩ := c.cex.hyp.exists_cTilde_not_le
    exact fun hle => han (hle ha)
  have h14 : V ⊓ centralizer (R : Set G) ≤ V₀ :=
    fourteen_four c.cex.hyp.h6.elemAbelian
      (by rw [c.cex.hyp.h6.normalizer_eq]) c.cex.hyp.h6.le_normalizer₀
      c.cex.hyp.h6.le (c.cex.hyp.h6.conjGenerated c.cex.hyp.ne_bot) hne c.sylow
  refine le_bot_iff.1 ?_
  rw [← c.cex.inf_eq_bot]
  exact le_inf hCU ((le_inf inf_le_left hCR).trans h14)

theorem eq_one_of_mul_of_comm_mem (c : Cfg1620 M V₀ V U S R H g B) {b v y : G} (hb : b ∈ B)
    (hv : v ∈ V) (hy : y ∈ H) (hby : b = v * y)
    (hK : ∀ k ∈ conjClosure V H,
      ⁅k, y⁆ ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) : b = 1 := by
  set I : Subgroup G := conjClosure (U ⊔ V₀) H with hI
  set L : Subgroup G := (V ⊔ conjSubgroup V g : Subgroup G) with hL
  have hVH : V ≤ H := c.V_le_R.trans c.mem.1
  have hUI : U ≤ I := by
    rw [hI]
    exact le_sup_left.trans (le_conjClosure (U ⊔ V₀) H)
  have hLcK : L ≤ conjClosure V H := by rw [hL]; exact c.L_le_conjClosure
  have hInorm : H ≤ Subgroup.normalizer (I : Set G) := by
    rw [hI]
    exact le_normalizer_conjClosure (U ⊔ V₀) H
  have hmemL : ∀ {l : G}, l ∈ L → l ∈ V ⊔ conjSubgroup V g := by
    intro l hl; simpa [hL] using hl
  have hyCI : ∀ u ∈ U, y⁻¹ * u * y ∈ I ⊓ centralizer (L : Set G) := by
    intro u hu
    have huI : u ∈ I := hUI hu
    have hyNinv : y⁻¹ ∈ Subgroup.normalizer (I : Set G) :=
      (Subgroup.normalizer (I : Set G)).inv_mem (hInorm hy)
    refine ⟨?_, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.1 hyNinv u).1 huI
    · refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
      have hul : u * l = l * u :=
        Subgroup.mem_centralizer_iff.1 (c.L_le_centralizer (hmemL hl)) u hu
      have h1C : ⁅l, y⁆ ∈ centralizer (I : Set G) := by
        rw [hI]
        exact (hK l (hLcK hl)).2
      have hDmem : ⁅l, y⁆⁻¹ ∈ centralizer (I : Set G) :=
        (centralizer (I : Set G)).inv_mem h1C
      have hDl : y * l * y⁻¹ = ⁅l, y⁆⁻¹ * l := by
        rw [commutatorElement_def]; group
      have hcommD : u * ⁅l, y⁆⁻¹ = ⁅l, y⁆⁻¹ * u :=
        Subgroup.mem_centralizer_iff.1 hDmem u huI
      have hcommDl : u * (⁅l, y⁆⁻¹ * l) = (⁅l, y⁆⁻¹ * l) * u :=
        (Commute.mul_right hcommD hul).eq
      have hXY : y * ((y⁻¹ * u * y) * l) * y⁻¹ = y * (l * (y⁻¹ * u * y)) * y⁻¹ := by
        calc y * ((y⁻¹ * u * y) * l) * y⁻¹ = u * (y * l * y⁻¹) := by group
          _ = u * (⁅l, y⁆⁻¹ * l) := by rw [hDl]
          _ = (⁅l, y⁆⁻¹ * l) * u := hcommDl
          _ = (y * l * y⁻¹) * u := by rw [hDl]
          _ = y * (l * (y⁻¹ * u * y)) * y⁻¹ := by group
      exact (mul_left_cancel (mul_right_cancel hXY)).symm
  have hfix : ∀ u ∈ U, y⁻¹ * u * y = u := by
    intro u hu
    have hCIu : u ∈ I ⊓ centralizer (L : Set G) :=
      ⟨hUI hu, Subgroup.mem_centralizer_iff.2 fun l hl =>
        (Subgroup.mem_centralizer_iff.1 (c.L_le_centralizer (hmemL hl)) u hu).symm⟩
    have hdCI : u⁻¹ * (y⁻¹ * u * y) ∈ I ⊓ centralizer (L : Set G) :=
      (I ⊓ centralizer (L : Set G)).mul_mem
        ((I ⊓ centralizer (L : Set G)).inv_mem hCIu) (hyCI u hu)
    have hb'T : b⁻¹ ∈ F11.CTilde M V₀ V :=
      (F11.CTilde M V₀ V).inv_mem (c.sylow.le (c.B_le hb))
    have hd : b⁻¹ * u * b * u⁻¹ ∈ V₀ := by
      simpa using (FourteenTwo.mem_cTilde_iff_comm.1 hb'T).2.2 u (c.cex.le hu)
    have hXeq : y⁻¹ * u * y = b⁻¹ * u * b := by
      rw [hby]
      have hv' : v⁻¹ * u * v = u := by
        calc v⁻¹ * u * v = v⁻¹ * (u * v) := by rw [mul_assoc]
          _ = v⁻¹ * (v * u) := by
                rw [B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian hv (c.cex.le hu)]
          _ = u := by group
      rw [show (v * y)⁻¹ * u * (v * y) = y⁻¹ * (v⁻¹ * u * v) * y by group, hv']
    have hXuV₀ : u⁻¹ * (y⁻¹ * u * y) ∈ V₀ := by
      rw [hXeq, show b⁻¹ * u * b = (b⁻¹ * u * b * u⁻¹) * u by group]
      have hcomm : (b⁻¹ * u * b * u⁻¹) * u = u * (b⁻¹ * u * b * u⁻¹) :=
        B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian (c.cex.hyp.h6.le hd) (c.cex.le hu)
      rw [hcomm, show u⁻¹ * (u * (b⁻¹ * u * b * u⁻¹)) = b⁻¹ * u * b * u⁻¹ by group]
      exact hd
    have hbot : u⁻¹ * (y⁻¹ * u * y) ∈ (⊥ : Subgroup G) := by
      have hm : u⁻¹ * (y⁻¹ * u * y) ∈
          V₀ ⊓ centralizer ((V ⊔ conjSubgroup V g : Subgroup G) : Set G) :=
        ⟨hXuV₀, by rw [← hL]; exact hdCI.2⟩
      rwa [c.inf_centralizer_L] at hm
    have h1 : u⁻¹ * (y⁻¹ * u * y) = 1 := Subgroup.mem_bot.1 hbot
    have := congrArg (fun z => u * z) h1
    simpa [mul_assoc] using this
  have hub : ∀ u ∈ U, u * b = b * u := by
    intro u hu
    have huy : u * y = y * u := by
      have := congrArg (fun z => y * z) (hfix u hu)
      simpa [mul_assoc] using this
    have huv : u * v = v * u :=
      B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian (c.cex.le hu) hv
    rw [hby]
    calc u * (v * y) = (u * v) * y := by rw [mul_assoc]
      _ = (v * u) * y := by rw [huv]
      _ = v * (u * y) := by rw [mul_assoc]
      _ = v * (y * u) := by rw [huy]
      _ = (v * y) * u := by rw [mul_assoc]
  by_contra hb1
  exact c.not_comm fun u hu => by
    have h1 : u ∈ V ⊓ centralizer ({b} : Set G) :=
      ⟨c.cex.le hu, Subgroup.mem_centralizer_iff.2 fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact (hub u hu).symm⟩
    rw [c.centralizer_B b hb hb1] at h1
    exact h1.2

theorem eq_one_of_conj_eq_of_mem_sup (c : Cfg1620 M V₀ V U S R H g B) {b k : G} (hb : b ∈ B)
    (hk : k ∈ conjClosure V H)
    (hbk : ∀ x ∈ conjClosure V H,
      (k * x * k⁻¹)⁻¹ * (b * x * b⁻¹) ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) :
    (∀ v ∈ V, ⁅k, v⁆ ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) ∧
      (k ∈ V ⊔ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) → b = 1) := by
  set CH : Subgroup G := H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) with hCH
  have hVH : V ≤ H := c.V_le_R.trans c.mem.1
  have hKH : conjClosure V H ≤ H := conjClosure_le_H c
  have hV₀CH : V₀ ≤ CH := by
    rw [hCH]
    refine le_inf (c.cex.hyp.h6.le.trans hVH) ?_
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    exact B2F.isElemAbelian_comm (c.mem.isElemAbelian c.cex) hi
      (le_conjClosure (U ⊔ V₀) H (Subgroup.mem_sup_right hw))
  constructor
  · intro v hv
    have hvK : v ∈ conjClosure V H := le_conjClosure V H hv
    have h1 : (k * v * k⁻¹)⁻¹ * (b * v * b⁻¹) ∈ CH := hbk v hvK
    have hCv : (b * v * b⁻¹) * v⁻¹ ∈ CH :=
      hV₀CH ((FourteenTwo.mem_cTilde_iff_comm.1 (c.sylow.le (c.B_le hb))).2.2 v hv)
    have hkH : k ∈ H := hKH hk
    have hbH : b ∈ H := c.mem.1 (c.B_le hb)
    have hvH : v ∈ H := hVH hv
    have hAH : k * v * k⁻¹ ∈ H := H.mul_mem (H.mul_mem hkH hvH) (H.inv_mem hkH)
    have hAnorm : k * v * k⁻¹ ∈ Subgroup.normalizer (CH : Set G) := by
      rw [hCH]
      exact mem_normalizer_inf_centralizer_wc16 (Subgroup.le_normalizer hAH)
        (le_normalizer_conjClosure (U ⊔ V₀) H hAH)
    have hCA : (b * v * b⁻¹) * (k * v * k⁻¹)⁻¹ ∈ CH := by
      have h := (Subgroup.mem_normalizer_iff.1 hAnorm
        ((k * v * k⁻¹)⁻¹ * (b * v * b⁻¹))).1 h1
      simpa [mul_assoc] using h
    have hACinv : (k * v * k⁻¹) * (b * v * b⁻¹)⁻¹ ∈ CH := by
      simpa using CH.inv_mem hCA
    have hAv : (k * v * k⁻¹) * v⁻¹ ∈ CH := by
      have h := CH.mul_mem hACinv hCv
      simpa [mul_assoc] using h
    rwa [commutatorElement_def]
  · intro hkvs
    have hVnormCH : V ≤ Subgroup.normalizer (CH : Set G) := by
      intro v hv
      rw [hCH]
      exact mem_normalizer_inf_centralizer_wc16 (Subgroup.le_normalizer (hVH hv))
        (le_normalizer_conjClosure (U ⊔ V₀) H (hVH hv))
    have hkvs' : k ∈ (↑(V ⊔ CH) : Set G) := hkvs
    rw [Subgroup.coe_mul_of_left_le_normalizer_right V CH hVnormCH] at hkvs'
    obtain ⟨v', hv', cc, hc, hk_eq⟩ := hkvs'
    have hbH : b ∈ H := c.mem.1 (c.B_le hb)
    have hv'H : v' ∈ H := hVH hv'
    have hcH : cc ∈ H := by
      have h := hc
      rw [hCH] at h
      exact h.1
    have hyH : v'⁻¹ * b ∈ H := H.mul_mem (H.inv_mem hv'H) hbH
    have hcomm : ∀ x ∈ conjClosure V H,
        ⁅x, v'⁻¹ * b⁆ ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G) := by
      intro x hx
      have hxH : x ∈ H := hKH hx
      have h1 : (k * x * k⁻¹)⁻¹ * (b * x * b⁻¹) ∈ CH := hbk x hx
      have hAeq : k * x * k⁻¹ = v' * (cc * x * cc⁻¹) * v'⁻¹ := by
        rw [← hk_eq]
        group
      have hxN : x ∈ Subgroup.normalizer (CH : Set G) := by
        rw [hCH]
        exact mem_normalizer_inf_centralizer_wc16 (Subgroup.le_normalizer hxH)
          (le_normalizer_conjClosure (U ⊔ V₀) H hxH)
      have hcx : cc * x * cc⁻¹ * x⁻¹ ∈ CH := by
        have h := (Subgroup.mem_normalizer_iff.1 hxN cc⁻¹).1 (CH.inv_mem hc)
        simpa [mul_assoc] using CH.mul_mem hc h
      have hv'N : v' ∈ Subgroup.normalizer (CH : Set G) := by
        rw [hCH]
        exact mem_normalizer_inf_centralizer_wc16 (Subgroup.le_normalizer hv'H)
          (le_normalizer_conjClosure (U ⊔ V₀) H hv'H)
      have hA₁ : (k * x * k⁻¹) * (v' * x * v'⁻¹)⁻¹ ∈ CH := by
        rw [hAeq]
        have h := (Subgroup.mem_normalizer_iff.1 hv'N (cc * x * cc⁻¹ * x⁻¹)).1 hcx
        simpa [mul_assoc] using h
      have hAnorm : k * x * k⁻¹ ∈ Subgroup.normalizer (CH : Set G) := by
        rw [hCH]
        have hAH : k * x * k⁻¹ ∈ H :=
          H.mul_mem (H.mul_mem (hKH hk) hxH) (H.inv_mem (hKH hk))
        exact mem_normalizer_inf_centralizer_wc16 (Subgroup.le_normalizer hAH)
          (le_normalizer_conjClosure (U ⊔ V₀) H hAH)
      have hAE : (k * x * k⁻¹) * ((k * x * k⁻¹)⁻¹ * (b * x * b⁻¹)) * (k * x * k⁻¹)⁻¹
          ∈ CH :=
        (Subgroup.mem_normalizer_iff.1 hAnorm
          ((k * x * k⁻¹)⁻¹ * (b * x * b⁻¹))).1 h1
      have hD : (b * x * b⁻¹) * (v' * x * v'⁻¹)⁻¹ ∈ CH := by
        have h := CH.mul_mem hAE hA₁
        simpa [mul_assoc] using h
      have hv'Ninv : v'⁻¹ ∈ Subgroup.normalizer (CH : Set G) :=
        (Subgroup.normalizer (CH : Set G)).inv_mem hv'N
      have hyx : (v'⁻¹ * (b * x * b⁻¹) * v') * x⁻¹ ∈ CH := by
        have h := (Subgroup.mem_normalizer_iff.1 hv'Ninv
          ((b * x * b⁻¹) * (v' * x * v'⁻¹)⁻¹)).1 hD
        simpa [mul_assoc] using h
      have hgoal : x * (v'⁻¹ * b) * x⁻¹ * (v'⁻¹ * b)⁻¹ ∈ CH := by
        have h := CH.inv_mem hyx
        simpa [mul_assoc] using h
      rw [commutatorElement_def, ← hCH]
      exact hgoal
    exact eq_one_of_mul_of_comm_mem c hb hv' hyH (by group) hcomm

theorem not_le_sup_inf_centralizer (c : Cfg1620 M V₀ V U S R H g B) :
    ¬ conjClosure V H ≤ (V ⊔ conjSubgroup V g) ⊔
      (conjClosure V H ⊓ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G))) := by
  intro hle
  have hU : U ≤ V ⊓ centralizer (conjClosure V H : Set G) := by
    refine le_inf c.cex.le ?_
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : k ∈ (V ⊔ conjSubgroup V g) ⊔
        (conjClosure V H ⊓ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G))) := hle hk
    have hA_cent : (V ⊔ conjSubgroup V g) ≤ Subgroup.centralizer ({u} : Set G) := by
      intro a ha
      exact Subgroup.mem_centralizer_iff.2 fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact Subgroup.mem_centralizer_iff.1 (c.L_le_centralizer ha) u hu
    have hB_cent : conjClosure V H ⊓ (H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) ≤
        Subgroup.centralizer ({u} : Set G) := by
      intro b hb
      exact Subgroup.mem_centralizer_iff.2 fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact Subgroup.mem_centralizer_iff.1 hb.2.2 u
          (le_sup_left.trans (le_conjClosure (U ⊔ V₀) H) hu)
    exact (Subgroup.mem_centralizer_iff.1 ((sup_le hA_cent hB_cent) hk')
      u (Set.mem_singleton u)).symm
  rw [inf_centralizer_conjClosure_eq_bot c] at hU
  exact c.cex.ne_bot (le_bot_iff.1 hU)

theorem not_le_sup_of_comm (h15 : W16Fifteen G) (hS : Std15 G)
    (c : Cfg1620 M V₀ V U S R H g B) {Z : Subgroup G} (hZK : Z ≤ conjClosure V H)
    (hZ : ∀ z ∈ Z, ∀ k ∈ conjClosure V H,
      ⁅z, k⁆ ∈ H ⊓ centralizer (conjClosure (U ⊔ V₀) H : Set G)) :
    ¬ conjClosure V H ≤ (V ⊔ conjSubgroup V g) ⊔ Z := by
  intro hle
  have hVH : V ≤ H := c.V_le_R.trans c.mem.1
  have hKH : conjClosure V H ≤ H := conjClosure_le_H c
  have hUV₀H : U ⊔ V₀ ≤ H := sup_le (c.cex.le.trans hVH) (c.cex.hyp.h6.le.trans hVH)
  let I : Subgroup G := conjClosure (U ⊔ V₀) H
  let L : Subgroup G := V ⊔ conjSubgroup V g
  have hLH : L ≤ H := c.L_le_conjClosure.trans hKH
  have hZH : Z ≤ H := hZK.trans hKH
  have hE : IsElemAbelian 2 I := c.mem.isElemAbelian c.cex
  have hJ : H ≤ Subgroup.normalizer (I : Set G) := le_normalizer_conjClosure (U ⊔ V₀) H
  let Mo : ModDataE H I := (exists_modDataE (J := H) (E := I) hE hJ).some
  have hle' : Mo.img (conjClosure V H) ≤ Mo.img L ⊔ Mo.img Z := by
    rw [← Mo.img_sup hLH hZH]
    exact Mo.img_mono hle
  have hZ_cent : Mo.img Z ≤ Subgroup.centralizer (Mo.img (conjClosure V H) :
      Set (LGL 2 Mo.W)) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨j, hjK, rfl⟩ := Mo.mem_img.1 hw
    obtain ⟨y, hyZ, rfl⟩ := Mo.mem_img.1 hz
    have hcomm : ⁅(y : G), (j : G)⁆ ∈ H ⊓ centralizer (I : Set G) := hZ (y : G) hyZ (j : G) hjK
    have hρ1 : Mo.ρ ⁅y, j⁆ = 1 :=
      (Mo.ρ_eq_one_iff _).2 (by simpa [commutatorElement_def] using hcomm.2)
    have hmap : Mo.ρ ⁅y, j⁆ = ⁅Mo.ρ y, Mo.ρ j⁆ := by rw [map_commutatorElement]
    have h1 : ⁅Mo.ρ y, Mo.ρ j⁆ = 1 := by rw [← hmap]; exact hρ1
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  have hLnormZ : Mo.img L ≤ Subgroup.normalizer (Mo.img Z : Set (LGL 2 Mo.W)) := by
    refine Subgroup.le_normalizer_iff.2 fun l hl z hz => ?_
    have hmem : l ∈ Mo.img (conjClosure V H) := Mo.img_mono c.L_le_conjClosure hl
    have hcomm : l * z = z * l := Subgroup.mem_centralizer_iff.1 (hZ_cent hz) l hmem
    have hzl : l * z * l⁻¹ = z := by rw [hcomm]; group
    rwa [hzl]
  have hLnorm : Mo.img (conjClosure V H) ≤ Subgroup.normalizer (Mo.img L :
      Set (LGL 2 Mo.W)) := by
    refine Subgroup.le_normalizer_iff.2 fun k hk l hl => ?_
    have hk' : k ∈ (↑(Mo.img L ⊔ Mo.img Z) : Set (LGL 2 Mo.W)) := hle' hk
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (Mo.img L) (Mo.img Z) hLnormZ] at hk'
    obtain ⟨l₁, hl₁, z, hz, rfl⟩ := hk'
    have hzl : z * l * z⁻¹ = l := by
      have hcomm : l * z = z * l := Subgroup.mem_centralizer_iff.1 (hZ_cent hz) l
        (Mo.img_mono c.L_le_conjClosure hl)
      rw [← hcomm]; group
    have hklk : (l₁ * z) * l * (l₁ * z)⁻¹ = l₁ * l * l₁⁻¹ := by
      rw [show (l₁ * z) * l * (l₁ * z)⁻¹ = l₁ * (z * l * z⁻¹) * l₁⁻¹ by group, hzl]
    rw [hklk]
    exact (Mo.img L).mul_mem ((Mo.img L).mul_mem hl₁ hl) ((Mo.img L).inv_mem hl₁)
  have hgen : ∀ h : ↥H, Mo.img (conjSubgroup V (h : G)⁻¹) ≤ Mo.img L := by
    intro h
    obtain ⟨k, hkK, hk_eq, -⟩ :=
      exists_mem_conjClosure_conjSubgroup_eq h15 hS c (h := (h : G)⁻¹) (H.inv_mem h.2)
    have hkH : k ∈ H := hKH hkK
    let k' : ↥H := ⟨k⁻¹, H.inv_mem hkH⟩
    have hk'K : (k' : G) ∈ conjClosure V H := (conjClosure V H).inv_mem hkK
    have hgN : Mo.ρ k' ∈ Subgroup.normalizer (Mo.img L : Set (LGL 2 Mo.W)) :=
      hLnorm (Mo.mem_img.2 ⟨k', hk'K, rfl⟩)
    have hgNinv : (Mo.ρ k')⁻¹ ∈ Subgroup.normalizer (Mo.img L : Set (LGL 2 Mo.W)) :=
      (Subgroup.normalizer _).inv_mem hgN
    have hcj : cj (Mo.ρ k') (Mo.img L) = Mo.img L := by
      rw [cj_eq_conjSubgroup']
      exact conjSubgroup_eq_iff_mem_normalizer.2 hgNinv
    have himg : cj (Mo.ρ k') (Mo.img V) = Mo.img (conjSubgroup V k) := by
      simpa [k'] using Mo.img_conj (A := V) hVH k'
    rw [hk_eq, ← himg]
    calc cj (Mo.ρ k') (Mo.img V)
        ≤ cj (Mo.ρ k') (Mo.img L) :=
          Subgroup.map_mono (f := (MulAut.conj (Mo.ρ k')).toMonoidHom)
            (Mo.img_mono (le_sup_left : V ≤ L))
      _ = Mo.img L := hcj
  have hmemK : ∀ (x : G) (hx : x ∈ conjClosure V H) (hxH : x ∈ H),
      Mo.ρ ⟨x, hxH⟩ ∈ Mo.img L := by
    intro x hx
    change x ∈ Subgroup.closure {y : G | ∃ h ∈ H, ∃ z ∈ V, h * z * h⁻¹ = y} at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        intro hyH
        obtain ⟨h, hh, v, hv, rfl⟩ := hy
        apply hgen ⟨h, hh⟩
        exact Mo.mem_img.2 ⟨⟨h * v * h⁻¹, hyH⟩,
          mem_conjSubgroup_iff.2 (by
            rw [show (h⁻¹) * (h * v * h⁻¹) * (h⁻¹)⁻¹ = v by group]
            exact hv), rfl⟩
    | one =>
        intro hyH
        have h1 : (⟨1, hyH⟩ : ↥H) = 1 := Subtype.ext rfl
        rw [h1, map_one]
        exact (Mo.img L).one_mem
    | mul a b ha hb iha ihb =>
        intro habH
        rw [show Mo.ρ ⟨a * b, habH⟩ =
          Mo.ρ ⟨a, hKH (by rw [conjClosure]; exact ha)⟩ *
            Mo.ρ ⟨b, hKH (by rw [conjClosure]; exact hb)⟩ by
          rw [show (⟨a * b, habH⟩ : ↥H) =
              ⟨a, hKH (by rw [conjClosure]; exact ha)⟩ *
                ⟨b, hKH (by rw [conjClosure]; exact hb)⟩ from rfl, map_mul]]
        exact (Mo.img L).mul_mem (iha _) (ihb _)
    | inv a ha iha =>
        intro haH
        rw [show Mo.ρ ⟨a⁻¹, haH⟩ = (Mo.ρ ⟨a, hKH (by rw [conjClosure]; exact ha)⟩)⁻¹ by
          rw [show (⟨a⁻¹, haH⟩ : ↥H) =
              (⟨a, hKH (by rw [conjClosure]; exact ha)⟩)⁻¹ from rfl, map_inv]]
        exact (Mo.img L).inv_mem (iha _)
  have hKhat_le_L : Mo.img (conjClosure V H) ≤ Mo.img L := by
    intro r hr
    obtain ⟨j, hjK, rfl⟩ := Mo.mem_img.1 hr
    exact hmemK (j : G) hjK j.2
  have hK_le : conjClosure V H ≤ L ⊔ (H ⊓ centralizer (I : Set G)) :=
    (Mo.img_le_img_iff hKH hLH).1 hKhat_le_L
  have hK_le' : conjClosure V H ≤ L ⊔ (conjClosure V H ⊓ (H ⊓ centralizer (I : Set G))) := by
    intro k hk
    have hLnormCH : L ≤ Subgroup.normalizer ((H ⊓ centralizer (I : Set G)) : Set G) := by
      intro l hl
      exact mem_normalizer_inf_centralizer_wc16 (Subgroup.le_normalizer (hLH hl))
        (le_normalizer_conjClosure (U ⊔ V₀) H (hLH hl))
    have hk' : k ∈ (↑(L ⊔ (H ⊓ centralizer (I : Set G))) : Set G) := hK_le hk
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L (H ⊓ centralizer (I : Set G))
      hLnormCH] at hk'
    obtain ⟨l, hl, c₀, hc, hcl⟩ := hk'
    have hcK : c₀ ∈ conjClosure V H := by
      have h1 : l⁻¹ * k ∈ conjClosure V H :=
        (conjClosure V H).mul_mem ((conjClosure V H).inv_mem (c.L_le_conjClosure hl)) hk
      have h2 : l⁻¹ * k = c₀ := by rw [← hcl]; group
      rwa [h2] at h1
    rw [← hcl]
    exact (L ⊔ (conjClosure V H ⊓ (H ⊓ centralizer (I : Set G)))).mul_mem
      (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right ⟨hcK, hc⟩)
  exact not_le_sup_inf_centralizer c hK_le'

end Cfg1620

end CFSG.LocalAnalysis.WeakClosure81
