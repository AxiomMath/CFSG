module

public import CFSG.LocalAnalysis.WeakClosure81.SixFour
public import CFSG.LocalAnalysis.WeakClosure81.FourteenSix
public import CFSG.LocalAnalysis.WeakClosure81.SixTen
public import CFSG.LocalAnalysis.WeakClosure81.SixSix

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mQuot_barSub_preBarSub_gen {V₀ V B : Subgroup G} (hV : IsElemAbelian 2 V)
    (hB : B ≤ stabTil V₀ V) {C : Subgroup (MulAut (Vtil V₀ V hV))}
    (hC : C ≤ barSub V₀ V hV B) :
    E3.mQuot (barSub V₀ V hV B) C = E3.mQuot B (preBarSub B V₀ V hV C) := by
  let f : B →* MulAut (Vtil V₀ V hV) :=
    { toFun := fun b => actTil V₀ V hV ⟨b.1, hB b.2⟩
      map_one' := by
        show actTil V₀ V hV ⟨(1 : B).1, hB (1 : B).2⟩ = 1
        rw [show (⟨(1 : B).1, hB (1 : B).2⟩ : stabTil V₀ V) = 1 from
          Subtype.ext (Subgroup.coe_one B)]
        exact map_one (actTil V₀ V hV)
      map_mul' := by
        intro a b
        show actTil V₀ V hV ⟨(a * b).1, hB (a * b).2⟩ =
          actTil V₀ V hV ⟨a.1, hB a.2⟩ * actTil V₀ V hV ⟨b.1, hB b.2⟩
        rw [show (⟨(a * b).1, hB (a * b).2⟩ : stabTil V₀ V) =
          ⟨a.1, hB a.2⟩ * ⟨b.1, hB b.2⟩ from Subtype.ext rfl]
        exact map_mul (actTil V₀ V hV) _ _ }
  have hfrange : f.range = barSub V₀ V hV B := by
    ext φ
    constructor
    · rintro ⟨b, rfl⟩
      exact actTil_mem_barSub V₀ V hV b.2 (hB b.2)
    · intro hφ
      obtain ⟨g, hg, hgφ⟩ := (mem_barSub V₀ V hV B φ).1 hφ
      exact ⟨⟨g.1, hg⟩, by simpa [f] using hgφ⟩
  set D : Subgroup G := preBarSub B V₀ V hV C with hDdef
  have hDB : D ≤ B := inf_le_left
  have hmapD : map f (D.subgroupOf B) = barSub V₀ V hV D := by
    ext φ
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact actTil_mem_barSub V₀ V hV hb (hB b.2)
    · intro hφ
      obtain ⟨g, hg, hgφ⟩ := (mem_barSub V₀ V hV D φ).1 hφ
      exact ⟨⟨g.1, hDB hg⟩, hg, by simpa [f] using hgφ⟩
  have hfD : map f (D.subgroupOf B) = C := by
    rw [hmapD]
    rw [barSub_preBarSub]
    exact inf_eq_left.2 hC
  have hker_le : f.ker ≤ D.subgroupOf B := by
    intro b hb
    rw [Subgroup.mem_subgroupOf]
    refine (mem_preBarSub B V₀ V hV C).2 ⟨b.2, hB b.2, ?_⟩
    have hb' : actTil V₀ V hV ⟨b.1, hB b.2⟩ = 1 := by simpa [f] using hb
    rw [hb']
    exact C.one_mem
  have hr := Subgroup.relIndex_map_map f (D.subgroupOf B) (⊤ : Subgroup B)
  rw [hfD, show map f (⊤ : Subgroup B) = f.range from (MonoidHom.range_eq_map f).symm,
    hfrange] at hr
  rw [sup_eq_left.2 hker_le, top_sup_eq] at hr
  rw [Subgroup.relIndex_top_right] at hr
  unfold E3.mQuot
  rw [hr]
  rfl

theorem barSub_eq_bot_iff {M V₀ V B : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ Subgroup.normalizer (V : Set G))
    (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G)) (hBM : B ≤ M) :
    barSub V₀ V hV B = ⊥ ↔ B ≤ F11.CTilde M V₀ V := by
  have hMs : M ≤ stabTil V₀ V := le_stabTil hM hM₀
  constructor
  · intro hbot b hb
    have hbs : b ∈ stabTil V₀ V := hMs (hBM hb)
    rw [mem_cTilde_iff hV hM]
    refine ⟨hBM hb, hbs, ?_⟩
    by_contra hne
    have hmem : actTil V₀ V hV ⟨b, hbs⟩ ∈ barSub V₀ V hV B :=
      actTil_mem_barSub V₀ V hV hb hbs
    rw [hbot] at hmem
    exact hne (Subgroup.mem_bot.1 hmem)
  · intro hB
    refine eq_bot_iff.2 fun φ hφ => ?_
    rw [Subgroup.mem_bot]
    obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV B φ).1 hφ
    obtain ⟨-, h, h1⟩ := (mem_cTilde_iff hV hM).1 (hB hg)
    have heq : g = (⟨(g : G), h⟩ : stabTil V₀ V) := Subtype.ext rfl
    rw [heq]
    exact h1

theorem mQuot_preCTilde (V₀ V D : Subgroup G) (hV : IsElemAbelian 2 V) :
    E3.mQuot V (preCTilde V₀ V D hV) = rkIdx (fixV (barSub V₀ V hV D)) :=
  mQuot_preTil V₀ V hV (fixV (barSub V₀ V hV D))

theorem preCTilde_eq_inf_centralizer {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) {D : Subgroup G}
    (hD : D ≤ BOf M V g) (hDC : ¬ D ≤ F11.CTilde M V₀ V) :
    preCTilde V₀ V D h.elemAbelian = V ⊓ Subgroup.centralizer (D : Set G) := by
  have hM_le : M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hDstab : D ≤ stabTil V₀ V :=
    (hD.trans inf_le_right).trans (le_stabTil hM_le h.le_normalizer₀)
  apply le_antisymm
  · intro u hu
    have huV : u ∈ V := preCTilde_le V₀ V D h.elemAbelian hu
    have hcomm : ∀ d ∈ D, ⁅u, d⁆ ∈ V₀ :=
      (mem_preCTilde_iff h.elemAbelian hDstab huV).1 hu
    exact (six_four_three_of_gen h hgen hD hDC).2 u huV hcomm
  · intro u hu
    rw [Subgroup.mem_inf] at hu
    refine (mem_preCTilde_iff h.elemAbelian hDstab hu.1).2 fun d hd => ?_
    have h1 : ⁅u, d⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_centralizer_iff.1 hu.2 d hd).symm
    rw [h1]
    exact V₀.one_mem

theorem mQuot_UOf_le {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp64 n M V₀ V g) :
    E3.mQuot V (UOf M V g) ≤ n := by
  have hO : InCalO n M V₀ V g := h.inCalOStar.1
  rw [UOf, mQuot_inf_left]
  exact hO.1.2.1

theorem mQuot_BOf_le {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp64 n M V₀ V g) :
    E3.mQuot (conjSubgroup V g) (BOf M V g) ≤ n := by
  have hO : InCalO n M V₀ V g := h.inCalOStar.1
  rw [BOf, mQuot_inf_left]
  exact hO.2.2.1

theorem isElemAbelian2_barSub_BOf {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) :
    IsElemAbelian2 (barSub V₀ V h.elemAbelian (BOf M V g)) := by
  have hV := h.elemAbelian
  have hBle : BOf M V g ≤ conjSubgroup V g := inf_le_left
  refine ⟨?_, ?_⟩
  · intro a ha b hb
    obtain ⟨ga, hga, rfl⟩ := (mem_barSub V₀ V hV (BOf M V g) a).1 ha
    obtain ⟨gb, hgb, rfl⟩ := (mem_barSub V₀ V hV (BOf M V g) b).1 hb
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (B2F.isElemAbelian_comm (E3.isElemAbelian_conjSubgroup hV g)
      (hBle hga) (hBle hgb))
  · intro a ha
    obtain ⟨ga, hga, rfl⟩ := (mem_barSub V₀ V hV (BOf M V g) a).1 ha
    rw [← map_pow]
    have hga2 : ga ^ 2 = 1 := Subtype.ext (by
      simpa using (E3.isElemAbelian_conjSubgroup hV g).2 (ga : G) (hBle hga))
    rw [hga2, map_one]

private theorem conjSubgroup_BOf_eq_UOf {n : ℕ} {M V₀ V : Subgroup G} {g l : G}
    (h : Hyp64 n M V₀ V g) (hlL : l ∈ LOf V g)
    (hlV : conjSubgroup V l = conjSubgroup V g) :
    conjSubgroup (BOf M V g) l⁻¹ = UOf M V g := by
  obtain ⟨K', hK_eq, hKnorm_L, -, -, hKset'⟩ := inCalOStar_K_facts h
  have hgl : g * l⁻¹ ∈ Subgroup.normalizer (V : Set G) := by
    rw [show g * l⁻¹ = (l * g⁻¹)⁻¹ by group]
    refine (Subgroup.normalizer (V : Set G)).inv_mem ?_
    rw [← conjSubgroup_eq_iff_mem_normalizer, ← conjSubgroup_conjSubgroup, hlV,
      conjSubgroup_conjSubgroup_inv]
  have hKl : conjSubgroup K' l⁻¹ = K' :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hKnorm_L ((LOf V g).inv_mem hlL))
  have hBK : BOf M V g = conjSubgroup V g ⊓ K' := by
    rw [hK_eq]; exact (conjSubgroup_V_inf_sup_U_B_eq_B h).symm
  rw [hBK, conjSubgroup_inf, conjSubgroup_conjSubgroup,
    conjSubgroup_eq_iff_mem_normalizer.2 hgl, hKl]
  exact V_inf_K_eq_U h hKset'

private theorem conjSubgroup_conjSubgroup_V₀_eq_V₀ {n : ℕ} {M V₀ V : Subgroup G} {g l : G}
    (h : Hyp64 n M V₀ V g) (hlV : conjSubgroup V l = conjSubgroup V g) :
    conjSubgroup (conjSubgroup V₀ g) l⁻¹ = V₀ := by
  obtain ⟨-, -, hM, hM0, -, -, -⟩ := h
  have hV0l : conjSubgroup V₀ l = conjSubgroup V₀ g :=
    conjSubgroup_V₀_eq_of_conjSubgroup_eq hM hM0 hlV
  calc conjSubgroup (conjSubgroup V₀ g) l⁻¹ = conjSubgroup (conjSubgroup V₀ l) l⁻¹ := by
        rw [hV0l]
    _ = conjSubgroup V₀ (l * l⁻¹) := by rw [conjSubgroup_conjSubgroup]
    _ = V₀ := by rw [mul_inv_cancel, conjSubgroup_one]

theorem inf_conjSubgroup_V₀_eq_bot {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) :
    V ⊓ conjSubgroup V₀ g = ⊥ := by
  rw [inf_comm]
  exact conjSubgroup_V₀_inf_V_eq_bot h

theorem barSub_BOf_ne_bot {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) :
    barSub V₀ V h.elemAbelian (BOf M V g) ≠ ⊥ := by
  intro hbot
  have hM_le : M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hBM : BOf M V g ≤ M := inf_le_right
  have hBleCT : BOf M V g ≤ F11.CTilde M V₀ V :=
    (barSub_eq_bot_iff h.elemAbelian hM_le h.le_normalizer₀ hBM).1 hbot
  have hB : BOf M V g = NOf M V g ⊔ conjSubgroup V₀ g := by
    rw [← six_four_four_centralizer_B_of_gen h hgen]
    exact (inf_eq_left.2 hBleCT).symm
  obtain ⟨-, -, -, hlK, -, -⟩ := inCalOStar_K_facts h
  obtain ⟨l, hlL, hlVg⟩ := hlK
  have hlV : conjSubgroup V l = conjSubgroup V g := hlVg.symm
  have hBm := conjSubgroup_BOf_eq_UOf h hlL hlV
  have hNm := conjSubgroup_NOf_eq h ((LOf V g).inv_mem hlL)
  have hV0m := conjSubgroup_conjSubgroup_V₀_eq_V₀ h hlV
  have hUeq : UOf M V g = NOf M V g ⊔ V₀ := by
    rw [← hBm, hB, conjSubgroup_sup, hNm, hV0m]
  have hVM : V ≤ M := by rw [← h.normalizer_eq]; exact Subgroup.le_normalizer
  obtain ⟨-, -, -, -, -, -, -, -, hne⟩ := h.inCalOStar
  refine hne ?_
  calc (V ⊓ conjSubgroup V g) ⊔ V₀
      = NOf M V g ⊔ V₀ := by rw [NOf_eq M V g hVM]
    _ = UOf M V g := hUeq.symm
    _ = V ⊓ conjSubgroup M g := rfl

theorem rk_barSub_eq_mQuot_inf_cTilde {M V₀ V B : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ Subgroup.normalizer (V : Set G)) (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G))
    (hBM : B ≤ M) :
    rk ↥(barSub V₀ V hV B) = E3.mQuot B (B ⊓ F11.CTilde M V₀ V) := by
  have hBstab : B ≤ stabTil V₀ V := hBM.trans (le_stabTil hM hM₀)
  have h1 := mQuot_barSub_preBarSub_gen (V₀ := V₀) hV hBstab
    (C := ⊥) bot_le
  have hmbot : E3.mQuot (barSub V₀ V hV B) (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) =
      rk ↥(barSub V₀ V hV B) := by
    unfold E3.mQuot rk
    rw [Subgroup.relIndex_bot_left]
  have hpre : preBarSub B V₀ V hV ⊥ = B ⊓ F11.CTilde M V₀ V := by
    ext x
    rw [Subgroup.mem_inf, mem_preBarSub, mem_cTilde_iff hV hM]
    constructor
    · rintro ⟨hxB, h, h1⟩
      exact ⟨hxB, hBM hxB, h, by simpa using h1⟩
    · rintro ⟨hxB, -, h, h1⟩
      exact ⟨hxB, h, by simpa using h1⟩
  rw [hmbot, hpre] at h1
  exact h1

theorem fourteen_nine_one {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) :
    mBar M V₀ V h.elemAbelian - n ≤ rk ↥(barSub V₀ V h.elemAbelian (BOf M V g)) ∧
      ∀ D : Subgroup G, D ≤ BOf M V g →
        E3.mQuot (BOf M V g) D < mBar M V₀ V h.elemAbelian - n →
          barSub V₀ V h.elemAbelian D ≠ ⊥ := by
  have hV := h.elemAbelian
  have hM_le : M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hM0 : M ≤ Subgroup.normalizer (V₀ : Set G) := h.le_normalizer₀
  have hBM : BOf M V g ≤ M := inf_le_right
  have hBne : barSub V₀ V hV (BOf M V g) ≠ ⊥ := barSub_BOf_ne_bot h hgen
  have hBnotCT : ¬ BOf M V g ≤ F11.CTilde M V₀ V := fun hle =>
    hBne ((barSub_eq_bot_iff hV hM_le hM0 hBM).2 hle)
  have hAle : barSub V₀ V hV (BOf M V g) ≤ Mbar M V₀ V hV := by
    simpa [Mbar] using barSub_mono V₀ V hV hBM
  have hm1 : mBar M V₀ V hV ≤ rkIdx (fixV (barSub V₀ V hV (BOf M V g))) := by
    simpa [mBar] using E3.e3_2 hAle (isElemAbelian2_barSub_BOf h) hBne
  have hm2 : rkIdx (fixV (barSub V₀ V hV (BOf M V g))) =
      E3.mQuot V (V ⊓ Subgroup.centralizer (BOf M V g : Set G)) := by
    rw [← mQuot_preCTilde V₀ V (BOf M V g) hV,
      preCTilde_eq_inf_centralizer h hgen (le_refl (BOf M V g)) hBnotCT]
  have hprod : E3.mQuot (BOf M V g) (BOf M V g ⊓ F11.CTilde M V₀ V) +
        E3.mQuot V (UOf M V g)
      = E3.mQuot V (V ⊓ Subgroup.centralizer (BOf M V g : Set G)) := by
    have hsf := six_four_five h hgen
    unfold E3.mQuot
    rw [← padicValNat.mul
      (E3.relIndex_ne_zero' (BOf M V g) (BOf M V g ⊓ F11.CTilde M V₀ V))
      (E3.relIndex_ne_zero' V (UOf M V g))]
    exact congrArg (padicValNat 2) hsf
  have hchain : mBar M V₀ V hV ≤ rk ↥(barSub V₀ V hV (BOf M V g)) + n := by
    have hh := hm1
    rw [hm2, ← hprod,
      ← rk_barSub_eq_mQuot_inf_cTilde hV hM_le hM0 hBM] at hh
    have hUn := mQuot_UOf_le h
    omega
  refine ⟨by omega, ?_⟩
  intro D hD hDlt hDbot
  have hDleCT : D ≤ F11.CTilde M V₀ V :=
    (barSub_eq_bot_iff hV hM_le hM0 (hD.trans hBM)).1 hDbot
  have hmono : E3.mQuot (BOf M V g) (BOf M V g ⊓ F11.CTilde M V₀ V) ≤
      E3.mQuot (BOf M V g) D :=
    E3.mQuot_mono (le_inf hD hDleCT)
  have hrk := rk_barSub_eq_mQuot_inf_cTilde hV hM_le hM0 hBM
  have hsub : mBar M V₀ V hV - n ≤
      rk ↥(barSub V₀ V hV (BOf M V g)) := by omega
  have hchain2 : mBar M V₀ V hV - n ≤ E3.mQuot (BOf M V g) D := by
    rw [hrk] at hsub
    exact hsub.trans hmono
  omega

theorem fourteen_nine_two {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    {D : Subgroup G} (hD : D ≤ BOf M V g)
    (hDlt : E3.mQuot (BOf M V g) D < mBar M V₀ V h.elemAbelian - n) :
    fixV (barSub V₀ V h.elemAbelian D) = fixV (barSub V₀ V h.elemAbelian (BOf M V g)) ∧
      V ⊓ Subgroup.centralizer (D : Set G) = V ⊓ Subgroup.centralizer (BOf M V g : Set G) := by
  have hV := h.elemAbelian
  have hM_le : M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hM0 : M ≤ Subgroup.normalizer (V₀ : Set G) := h.le_normalizer₀
  have hBM : BOf M V g ≤ M := inf_le_right
  have hBle : BOf M V g ≤ conjSubgroup V g := inf_le_left
  have hDB : D ≤ M := hD.trans hBM
  have hDle : D ≤ conjSubgroup V g := hD.trans hBle
  have hDne : barSub V₀ V hV D ≠ ⊥ := (fourteen_nine_one h hgen).2 D hD hDlt
  have hDnotCT : ¬ D ≤ F11.CTilde M V₀ V := fun hle =>
    hDne ((barSub_eq_bot_iff hV hM_le hM0 hDB).2 hle)
  have hBnotCT : ¬ BOf M V g ≤ F11.CTilde M V₀ V := fun hle =>
    (barSub_BOf_ne_bot h hgen) ((barSub_eq_bot_iff hV hM_le hM0 hBM).2 hle)
  have hCD_le : V ⊓ Subgroup.centralizer (D : Set G) ≤
      V ⊓ Subgroup.centralizer (BOf M V g : Set G) := by
    intro c hc
    rw [Subgroup.mem_inf] at hc
    obtain ⟨hcV, hcC⟩ := hc
    have hcU : c ∈ UOf M V g :=
      (six_four_three_of_gen h hgen hD hDnotCT).1 (Subgroup.mem_inf.2 ⟨hcV, hcC⟩)
    have hcMg : c ∈ conjSubgroup M g := (Subgroup.mem_inf.1 hcU).2
    have hVg := E3.isElemAbelian_conjSubgroup hV g
    have hV0g : conjSubgroup V₀ g ≤ conjSubgroup V g := conjSubgroup_mono h.le g
    have hMg : conjSubgroup M g ≤ Subgroup.normalizer (conjSubgroup V g : Set G) :=
      (conjSubgroup_mono hM_le g).trans (le_of_eq (E3.conjSubgroup_normalizer V g))
    have hM0g : conjSubgroup M g ≤ Subgroup.normalizer (conjSubgroup V₀ g : Set G) :=
      (conjSubgroup_mono hM0 g).trans (le_of_eq (E3.conjSubgroup_normalizer V₀ g))
    have hVp : IsPGroup 2 V := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hV
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hVp) (⟨c, hcV⟩ : V)
    have hck : orderOf c = 2 ^ k := (Subgroup.orderOf_coe (⟨c, hcV⟩ : V)).trans hk
    have hCtc : D ≤ Subgroup.centralizer ({c} : Set G) := by
      intro d hd
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hcC d hd
    have hmqB : E3.mQuot (conjSubgroup V g) (BOf M V g) ≤ n := mQuot_BOf_le h
    have hsum : E3.mQuot (conjSubgroup V g) D =
        E3.mQuot (BOf M V g) D + E3.mQuot (conjSubgroup V g) (BOf M V g) :=
      E3.mQuot_add hD hBle
    have hlt : (E3.mQuot (conjSubgroup V g) D : ℕ∞) <
        (mBar (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) hVg : ℕ∞) := by
      rw [mBar_conj M V₀ V hV h.le hM_le hM0 g, hsum]
      have hnat : E3.mQuot (BOf M V g) D +
          E3.mQuot (conjSubgroup V g) (BOf M V g) < mBar M V₀ V hV := by omega
      exact_mod_cast hnat
    have hcCt : c ∈ F11.CTilde (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) :=
      mem_cTilde_of_mQuot_lt hVg hV0g hMg hM0g hcMg ⟨k, hck⟩ hDle hCtc hlt
    obtain ⟨-, hcs, hact⟩ := (mem_cTilde_iff hVg hMg).1 hcCt
    have hcomm : ∀ b ∈ BOf M V g, b * c = c * b := by
      intro b hb
      have hbVg : b ∈ conjSubgroup V g := hBle hb
      have hmemV0 : ⁅c, b⁆ ∈ conjSubgroup V₀ g := by
        have h := (actTil_eq_one_iff (conjSubgroup V₀ g) (conjSubgroup V g) hVg
          ⟨c, hcs⟩).1 hact b hbVg
        simpa [commutatorElement_def] using h
      have hmemV : ⁅c, b⁆ ∈ V := by
        have hbc : b * c⁻¹ * b⁻¹ ∈ V :=
          (Subgroup.mem_normalizer_iff.1 (hM_le (hBM hb)) c⁻¹).1 (V.inv_mem hcV)
        have h1 : c * (b * c⁻¹ * b⁻¹) ∈ V := V.mul_mem hcV hbc
        simpa [commutatorElement_def, mul_assoc] using h1
      have h1 : ⁅c, b⁆ = 1 := by
        have h2 : ⁅c, b⁆ ∈ (⊥ : Subgroup G) := by
          rw [← inf_conjSubgroup_V₀_eq_bot h]
          exact Subgroup.mem_inf.2 ⟨hmemV, hmemV0⟩
        exact Subgroup.mem_bot.1 h2
      exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
    refine Subgroup.mem_inf.2 ⟨hcV, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    exact hcomm
  have hCD_ge : V ⊓ Subgroup.centralizer (BOf M V g : Set G) ≤
      V ⊓ Subgroup.centralizer (D : Set G) :=
    inf_le_inf_left V (Subgroup.centralizer_le hD)
  have hCV_eq : V ⊓ Subgroup.centralizer (D : Set G) =
      V ⊓ Subgroup.centralizer (BOf M V g : Set G) :=
    le_antisymm hCD_le hCD_ge
  have hpre : preTil V₀ V hV (fixV (barSub V₀ V hV D)) =
      preTil V₀ V hV (fixV (barSub V₀ V hV (BOf M V g))) := by
    have e : preCTilde V₀ V D hV = preCTilde V₀ V (BOf M V g) hV := by
      rw [preCTilde_eq_inf_centralizer h hgen hD hDnotCT,
        preCTilde_eq_inf_centralizer h hgen (le_refl (BOf M V g)) hBnotCT, hCV_eq]
    simpa only [preCTilde] using e
  exact ⟨preTil_injective V₀ V hV hpre, hCV_eq⟩

theorem fourteen_nine_three {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) :
    barSub V₀ V h.elemAbelian (BOf M V g) ∈
      calABar (mBar M V₀ V h.elemAbelian - n) M V₀ V h.elemAbelian := by
  have hV := h.elemAbelian
  have hM_le : M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hM0 : M ≤ Subgroup.normalizer (V₀ : Set G) := h.le_normalizer₀
  have hBM : BOf M V g ≤ M := inf_le_right
  have hBstab : BOf M V g ≤ stabTil V₀ V := hBM.trans (le_stabTil hM_le hM0)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Mbar] using barSub_mono V₀ V hV hBM
  · exact barSub_BOf_ne_bot h hgen
  · exact isElemAbelian2_barSub_BOf h
  · intro C hC hlt
    set D : Subgroup G := preBarSub (BOf M V g) V₀ V hV C with hDdef
    have hDB : D ≤ BOf M V g := inf_le_left
    have hbarD : barSub V₀ V hV D = C := by
      rw [hDdef, barSub_preBarSub]
      exact inf_eq_left.2 hC
    have hmq : E3.mQuot (BOf M V g) D =
        E3.mQuot (barSub V₀ V hV (BOf M V g)) C :=
      (mQuot_barSub_preBarSub_gen hV hBstab hC).symm
    have hDlt : E3.mQuot (BOf M V g) D < mBar M V₀ V hV - n := by
      rw [hmq]; exact hlt
    have hfix := (fourteen_nine_two h hgen hDB hDlt).1
    rw [hbarD] at hfix
    exact hfix

end CFSG.LocalAnalysis.WeakClosure81
