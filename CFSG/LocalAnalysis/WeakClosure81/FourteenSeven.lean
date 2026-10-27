module

public import CFSG.LocalAnalysis.WeakClosure81.FourteenNine
public import CFSG.GroupTheory.ThompsonAxBFaithful

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def cMbarBOf (M V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (g : G) :
    Subgroup (MulAut (Vtil V₀ V hV)) :=
  Subgroup.centralizer (barSub V₀ V hV (BOf M V g) : Set (MulAut (Vtil V₀ V hV))) ⊓
    Mbar M V₀ V hV

@[expose] def IsRegularTorus (M V : Subgroup G) (g : G) (Y : Subgroup G) : Prop :=
  Y ≤ LOf V g ⊓ M ⊓ conjSubgroup M g ∧
    Nat.card Y = 2 ^ E3.mQuot V (UOf M V g) - 1 ∧ IsCyclic ↥Y ∧
    ∀ v ∈ V, v ∉ UOf M V g → ∀ w ∈ V, w ∉ UOf M V g →
      ∃ y ∈ Y, y * v * y⁻¹ * w⁻¹ ∈ UOf M V g

private theorem fixV_ne_bot_of_isPGroup {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) [Nontrivial W] {P : Subgroup (MulAut W)}
    (hP : IsPGroup 2 ↥P) : fixV P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hP.card_modEq_card_fixedPoints W
  have hfix : Nat.card (MulAction.fixedPoints ↥P W) = Nat.card (fixV P) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x x.2
  rw [hfix] at hmod
  have hW2 : IsPGroup 2 W := fun v => ⟨1, by rw [pow_one]; exact hW v⟩
  obtain ⟨n, hn⟩ := hW2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hn
  have heven : Nat.card W % 2 = 0 := by
    rw [hn]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hn0)
  intro hbot
  rw [hbot, Subgroup.card_bot] at hmod
  have := hmod.symm
  unfold Nat.ModEq at this
  omega

theorem eq_bot_or_eq_top_of_stable {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ Subgroup.normalizer (V : Set G)) (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G))
    (hirr : ConjGenerated M V₀ V) {S : Subgroup (Vtil V₀ V hV)}
    (hS : ∀ m ∈ Mbar M V₀ V hV, ∀ s ∈ S, m s ∈ S) : S = ⊥ ∨ S = ⊤ := by
  have hMs : M ≤ stabTil V₀ V := le_stabTil hM hM₀
  have hconj : ∀ m ∈ M, ∀ x : G, x ∈ preTil V₀ V hV S → m * x * m⁻¹ ∈ preTil V₀ V hV S := by
    intro m hm x hx
    obtain ⟨y, hy, hyS⟩ := (mem_preTil V₀ V hV S).1 hx
    have hms : m ∈ stabTil V₀ V := hMs hm
    have hmem : actTil V₀ V hV ⟨m, hms⟩ (mkTil V₀ V hV y) ∈ S :=
      hS (actTil V₀ V hV ⟨m, hms⟩) (actTil_mem_barSub V₀ V hV hm hms)
        (mkTil V₀ V hV y) hyS
    rw [actTil_mk] at hmem
    refine (mem_preTil V₀ V hV S).2 ⟨actStab V₀ V hV ⟨m, hms⟩ y, ?_, hmem⟩
    rw [actStab_apply_val, hy]
  have hMW : M ≤ Subgroup.normalizer (preTil V₀ V hV S : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconj m hm x
    · intro hx
      have hmm : m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ = x := by group
      have h := hconj m⁻¹ (M.inv_mem hm) (m * x * m⁻¹) hx
      rwa [hmm] at h
  by_cases hWV0 : preTil V₀ V hV S ≤ V₀
  · left
    refine le_bot_iff.1 fun s hs => ?_
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV s
    rw [Subgroup.mem_bot, ← map_one (mkTil V₀ V hV), mkTil_eq_iff]
    simpa using hWV0 ((mem_preTil V₀ V hV S).2 ⟨x, rfl, hs⟩)
  · right
    have hW_eq : preTil V₀ V hV S = V :=
      eq_of_normalizer_of_not_le_of_conjGenerated hirr (preTil_le V₀ V hV S) hMW hWV0
    refine top_le_iff.1 fun s _ => ?_
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV s
    obtain ⟨y, hy, hyS⟩ := (mem_preTil V₀ V hV S).1 (by rw [hW_eq]; exact x.val_mem)
    have hyx : y = x := IntMod.val_injective hy
    simpa [hyx] using hyS

theorem eq_bot_of_isPGroup_of_stable {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ Subgroup.normalizer (V : Set G)) (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G))
    (hirr : ConjGenerated M V₀ V) [Nontrivial (Vtil V₀ V hV)]
    {P : Subgroup (MulAut (Vtil V₀ V hV))} (hP : IsPGroup 2 P)
    (hPM : ∀ m ∈ Mbar M V₀ V hV, ∀ p ∈ P, m * p * m⁻¹ ∈ P) : P = ⊥ := by
  have hstab : ∀ m ∈ Mbar M V₀ V hV, ∀ e ∈ fixV P, m e ∈ fixV P := by
    intro m hm e he
    rw [mem_fixV] at he ⊢
    intro p hp
    have hmemP : m⁻¹ * p * m ∈ P := by
      have h := hPM m⁻¹ ((Mbar M V₀ V hV).inv_mem hm) p hp
      rwa [inv_inv] at h
    rw [← MulAut.mul_apply]
    rw [show p * m = m * (m⁻¹ * p * m) by group]
    rw [MulAut.mul_apply, he _ hmemP]
  have hfixne : fixV P ≠ ⊥ := by
    refine fixV_ne_bot_of_isPGroup (W := Vtil V₀ V hV) ?_ hP
    intro v
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV v
    rw [← map_pow, IntMod.sq_eq_one, map_one]
  rcases eq_bot_or_eq_top_of_stable hV hM hM₀ hirr hstab with h | h
  · exact absurd h hfixne
  · refine le_bot_iff.1 fun p hp => ?_
    rw [Subgroup.mem_bot]
    ext w
    have hw : w ∈ fixV P := by rw [h]; exact Subgroup.mem_top w
    simpa using (mem_fixV.1 hw) p hp

theorem eq_one_of_acts_trivially_mod {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ Subgroup.normalizer (V : Set G)) (hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G))
    (hirr : ConjGenerated M V₀ V) {W : Subgroup (Vtil V₀ V hV)} (hW : W ≠ ⊤)
    {T : Set (MulAut (Vtil V₀ V hV))}
    (hT : ∀ m ∈ Mbar M V₀ V hV, ∀ t ∈ T, m * t * m⁻¹ ∈ T)
    (htriv : ∀ t ∈ T, ∀ w, t w * w⁻¹ ∈ W) : ∀ t ∈ T, t = 1 := by
  let S : Subgroup (Vtil V₀ V hV) := Subgroup.closure {s | ∃ t ∈ T, ∃ w, s = t w * w⁻¹}
  have hSstab : ∀ m ∈ Mbar M V₀ V hV, ∀ s ∈ S, m s ∈ S := by
    intro m hm s hs
    induction hs using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨t, ht, w, rfl⟩ := hx
        have hmt : m * t * m⁻¹ ∈ T := hT m hm t ht
        have h1 : m (t w) = (m * t * m⁻¹) (m w) := by
          conv_lhs => rw [← MulAut.mul_apply, show m * t = (m * t * m⁻¹) * m by group,
            MulAut.mul_apply]
        rw [map_mul, map_inv, h1]
        exact Subgroup.subset_closure ⟨m * t * m⁻¹, hmt, m w, rfl⟩
    | one => rw [map_one]; exact S.one_mem
    | mul x y _ _ ihx ihy => rw [map_mul]; exact S.mul_mem ihx ihy
    | inv x _ ihx => rw [map_inv]; exact S.inv_mem ihx
  have hSW : S ≤ W := by
    rw [Subgroup.closure_le]
    rintro x ⟨t, ht, w, rfl⟩
    exact htriv t ht w
  have hSne : S ≠ ⊤ := fun htop => hW (eq_top_iff.2 (htop ▸ hSW))
  rcases eq_bot_or_eq_top_of_stable hV hM hM₀ hirr hSstab with hbot | htop
  · intro t ht
    ext w
    have hgen : t w * w⁻¹ ∈ S := Subgroup.subset_closure ⟨t, ht, w, rfl⟩
    have h1 : t w * w⁻¹ = 1 := by
      rw [hbot] at hgen
      simpa using hgen
    simpa using (mul_inv_eq_one.1 h1)
  · exact absurd htop hSne

theorem barSub_normalizes_barSub_BOf {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) {Y : Subgroup G} (hY : Y ≤ M ⊓ conjSubgroup M g) :
    ∀ φ ∈ barSub V₀ V h.elemAbelian Y, ∀ b ∈ barSub V₀ V h.elemAbelian (BOf M V g),
      φ * b * φ⁻¹ ∈ barSub V₀ V h.elemAbelian (BOf M V g) := by
  have hV := h.elemAbelian
  have hM : M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := h.le_normalizer₀
  intro φ hφ b hb
  obtain ⟨φ₀, hφ₀Y, rfl⟩ := (mem_barSub V₀ V hV Y φ).1 hφ
  obtain ⟨b₀, hb₀B, rfl⟩ := (mem_barSub V₀ V hV (BOf M V g) b).1 hb
  have hφinf : (φ₀ : G) ∈ M ⊓ conjSubgroup M g := hY hφ₀Y
  have hφM : (φ₀ : G) ∈ M := (Subgroup.mem_inf.1 hφinf).1
  have hφMg : (φ₀ : G) ∈ conjSubgroup M g := (Subgroup.mem_inf.1 hφinf).2
  have hYB : (φ₀ : G) * (b₀ : G) * (φ₀ : G)⁻¹ ∈ BOf M V g := by
    refine ⟨?_, ?_⟩
    · have hnorm : conjSubgroup M g = Subgroup.normalizer (conjSubgroup V g : Set G) := by
        rw [← h.normalizer_eq]
        exact E3.conjSubgroup_normalizer V g
      rw [hnorm] at hφMg
      exact (Subgroup.mem_normalizer_iff.1 hφMg (b₀ : G)).1 hb₀B.1
    · exact M.mul_mem (M.mul_mem hφM hb₀B.2) (M.inv_mem hφM)
  have hstab : (φ₀ : G) * (b₀ : G) * (φ₀ : G)⁻¹ ∈ stabTil V₀ V :=
    (stabTil V₀ V).mul_mem ((stabTil V₀ V).mul_mem φ₀.2 b₀.2) ((stabTil V₀ V).inv_mem φ₀.2)
  have hmul : actTil V₀ V hV ⟨(φ₀ : G) * (b₀ : G) * (φ₀ : G)⁻¹, hstab⟩ =
      actTil V₀ V hV φ₀ * actTil V₀ V hV b₀ * (actTil V₀ V hV φ₀)⁻¹ := by
    rw [show (⟨(φ₀ : G) * (b₀ : G) * (φ₀ : G)⁻¹, hstab⟩ : stabTil V₀ V) =
        φ₀ * b₀ * φ₀⁻¹ from Subtype.ext rfl, map_mul, map_mul, map_inv]
  rw [← hmul]
  exact actTil_mem_barSub V₀ V hV hYB hstab

theorem isPGroup_barSub_BOf {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp64 n M V₀ V g) :
    IsPGroup 2 (barSub V₀ V h.elemAbelian (BOf M V g)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.elemAbelian
  have hM : M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := h.le_normalizer₀
  have hBVg : BOf M V g ≤ conjSubgroup V g := inf_le_left
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hBp : IsPGroup 2 (BOf M V g) := (hVg.mono hBVg).isPGroup
  have hBs : BOf M V g ≤ stabTil V₀ V := inf_le_right.trans (le_stabTil hM hM₀)
  have h1 : IsPGroup 2 ((BOf M V g).subgroupOf (stabTil V₀ V)) :=
    hBp.of_equiv (Subgroup.subgroupOfEquivOfLe hBs).symm
  show IsPGroup 2 (((BOf M V g).subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV))
  exact h1.map (actTil V₀ V hV)

theorem preTil_fixV_barSub_BOf {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) :
    preTil V₀ V h.elemAbelian (fixV (barSub V₀ V h.elemAbelian (BOf M V g))) =
      NOf M V g ⊔ V₀ := by
  have hV := h.elemAbelian
  have hM : M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := h.le_normalizer₀
  have hBne : ¬ BOf M V g ≤ F11.CTilde M V₀ V :=
    fun hb => barSub_BOf_ne_bot h hgen ((barSub_eq_bot_iff hV hM hM₀ inf_le_right).2 hb)
  have hF2 := six_four_three_of_gen h hgen (D := BOf M V g) le_rfl hBne
  have hF1 := six_four_four_centralizer_V h
  apply le_antisymm
  · intro v hv
    rw [mem_preTil] at hv
    obtain ⟨x, hx, hxfix⟩ := hv
    rw [← hx]
    have hcomm : ∀ d ∈ BOf M V g, ⁅x.val, d⁆ ∈ V₀ := by
      intro d hd
      have hds : d ∈ stabTil V₀ V := (inf_le_right.trans (le_stabTil hM hM₀)) hd
      have hfixd : actTil V₀ V hV ⟨d, hds⟩ (mkTil V₀ V hV x) = mkTil V₀ V hV x :=
        (mem_fixV.1 hxfix) _ (actTil_mem_barSub V₀ V hV hd hds)
      rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at hfixd
      have hdv : ⁅d, x.val⁆ ∈ V₀ := hfixd
      rw [show ⁅x.val, d⁆ = ⁅d, x.val⁆⁻¹ from (commutatorElement_inv d x.val).symm]
      exact V₀.inv_mem hdv
    rw [← hF1]
    exact hF2.2 x.val x.val_mem hcomm
  · intro v hv
    have hvV : v ∈ V := by
      have hle : NOf M V g ⊔ V₀ ≤ V := by rw [← hF1]; exact inf_le_left
      exact hle hv
    rw [mem_preTil_iff_of_mem V₀ V hV _ hvV, mem_fixV]
    intro φ hφ
    obtain ⟨d, hdB, rfl⟩ := (mem_barSub V₀ V hV (BOf M V g) φ).1 hφ
    rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]
    simp only [IntMod.mk, IntMod.val]
    have hCB : v ∈ V ⊓ Subgroup.centralizer (BOf M V g : Set G) := by
      rw [hF1]; exact hv
    have hcomm : (d : G) * v = v * (d : G) :=
      Subgroup.mem_centralizer_iff.1 hCB.2 (d : G) hdB
    rw [show (d : G) * v * (d : G)⁻¹ * v⁻¹ = 1 by rw [hcomm]; group]
    exact V₀.one_mem

theorem barSub_fixes_fixV_BOf {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g) {Y : Subgroup G}
    (hY : Y ≤ LOf V g ⊓ M ⊓ conjSubgroup M g) :
    ∀ φ ∈ barSub V₀ V h.elemAbelian Y,
      ∀ e ∈ fixV (barSub V₀ V h.elemAbelian (BOf M V g)), φ e = e := by
  have hV := h.elemAbelian
  have hM : M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := h.le_normalizer₀
  have hE := preTil_fixV_barSub_BOf h hgen
  intro φ hφ e he
  obtain ⟨y, hyY, rfl⟩ := (mem_barSub V₀ V hV Y φ).1 hφ
  have hyLM : (y : G) ∈ LOf V g ⊓ M := (Subgroup.mem_inf.1 (hY hyY)).1
  have hyL : (y : G) ∈ LOf V g := (Subgroup.mem_inf.1 hyLM).1
  have hyM : (y : G) ∈ M := (Subgroup.mem_inf.1 hyLM).2
  have hWy : NOf M V g ⊔ V₀ ≤
      preTil V₀ V hV (fixV (Subgroup.zpowers (actTil V₀ V hV y))) := by
    refine sup_le ?_ ?_
    · intro n hn
      have hnV : n ∈ V := by
        have hle : NOf M V g ⊔ V₀ ≤ V := by rw [← hE]; exact preTil_le V₀ V hV _
        exact hle (Subgroup.mem_sup_left hn)
      rw [mem_preTil_iff_of_mem V₀ V hV _ hnV, mem_fixV_zpowers, actTil_mk, mkTil_eq_iff,
        actStab_apply_val]
      simp only [IntMod.mk, IntMod.val]
      have hnL : n ∈ LOf V g :=
        Subgroup.mem_sup_left (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hn).1).1
      have hcomm := Subgroup.mem_centralizer_iff.1 (NOf_le_centralizer_L h hn) (y : G) hyL
      rw [show (y : G) * n * (y : G)⁻¹ * n⁻¹ = 1 by rw [hcomm]; group]
      exact V₀.one_mem
    · intro v hv
      rw [mem_preTil_iff_of_mem V₀ V hV _ (h.le hv), mem_fixV_zpowers, actTil_mk, mkTil_eq_iff,
        actStab_apply_val]
      simp only [IntMod.mk, IntMod.val]
      have hyV₀ : (y : G) * v * (y : G)⁻¹ ∈ V₀ :=
        (Subgroup.mem_normalizer_iff.1 (hM₀ hyM) v).1 hv
      exact V₀.mul_mem hyV₀ (V₀.inv_mem hv)
  obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV e
  have hxpre : x.val ∈ preTil V₀ V hV (fixV (barSub V₀ V hV (BOf M V g))) :=
    (mem_preTil V₀ V hV _).2 ⟨x, rfl, he⟩
  rw [hE] at hxpre
  have hmem := hWy hxpre
  have hqmem : mkTil V₀ V hV x ∈ fixV (Subgroup.zpowers (actTil V₀ V hV y)) := by
    obtain ⟨y', hy', hy'mem⟩ := (mem_preTil V₀ V hV _).1 hmem
    have hyx : y' = x := IntMod.val_injective hy'
    simpa [hyx] using hy'mem
  exact (mem_fixV_zpowers (actTil V₀ V hV y) (mkTil V₀ V hV x)).1 hqmem

theorem fourteen_seven_three {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    {Y : Subgroup G} (hY : Y ≤ LOf V g ⊓ M ⊓ conjSubgroup M g) :
    ⁅cMbarBOf M V₀ V h.elemAbelian g, barSub V₀ V h.elemAbelian Y⁆ ≤
      pCoreOf 2 (cMbarBOf M V₀ V h.elemAbelian g) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.elemAbelian
  have hM : M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := h.le_normalizer₀
  let Bb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV (BOf M V g)
  let E : Subgroup (Vtil V₀ V hV) := fixV Bb
  let Cb : Subgroup (MulAut (Vtil V₀ V hV)) := cMbarBOf M V₀ V hV g
  let Yb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV Y
  have hYM : Y ≤ M := fun y hy => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (hY hy)).1).2
  have hY' : Y ≤ M ⊓ conjSubgroup M g := by
    intro y hy
    exact ⟨hYM hy, (Subgroup.mem_inf.1 (hY hy)).2⟩
  have hYbM : Yb ≤ Mbar M V₀ V hV := barSub_mono V₀ V hV hYM
  have hBp : IsPGroup 2 Bb := isPGroup_barSub_BOf h
  have hB1 : ∀ y ∈ Yb, ∀ c ∈ Cb, y * c * y⁻¹ ∈ Cb := by
    intro y hy c hc
    have hyMbar : y ∈ Mbar M V₀ V hV := hYbM hy
    have hcMbar : c ∈ Mbar M V₀ V hV := hc.2
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, (Mbar M V₀ V hV).mul_mem
      ((Mbar M V₀ V hV).mul_mem hyMbar hcMbar) ((Mbar M V₀ V hV).inv_mem hyMbar)⟩
    intro b hb
    have hb' : y⁻¹ * b * y ∈ Bb := by
      have := barSub_normalizes_barSub_BOf h hY' y⁻¹ (Yb.inv_mem hy) b hb
      simpa using this
    have hcommb' : (y⁻¹ * b * y) * c = c * (y⁻¹ * b * y) :=
      Subgroup.mem_centralizer_iff.1 hc.1 _ hb'
    calc b * (y * c * y⁻¹) = y * ((y⁻¹ * b * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * b * y)) * y⁻¹ := by rw [hcommb']
      _ = (y * c * y⁻¹) * b := by group
  have hB2 : ∀ c ∈ Cb, ∀ e ∈ E, c e ∈ E := by
    intro c hc e he
    rw [mem_fixV] at he ⊢
    intro b hb
    rw [← MulAut.mul_apply, Subgroup.mem_centralizer_iff.1 hc.1 b hb, MulAut.mul_apply,
      he b hb]
  let W₀ : Subgroup (MulAut (Vtil V₀ V hV)) :=
    { carrier := {c | c ∈ Cb ∧ ∀ e ∈ E, c e = e}
      mul_mem' := by
        rintro x y ⟨hxC, hx⟩ ⟨hyC, hy⟩
        exact ⟨Cb.mul_mem hxC hyC, fun e he => by
          rw [MulAut.mul_apply, hy e he, hx e he]⟩
      one_mem' := ⟨Cb.one_mem, fun e _ => by rw [MulAut.one_apply]⟩
      inv_mem' := by
        rintro x ⟨hxC, hx⟩
        refine ⟨Cb.inv_mem hxC, fun e he => ?_⟩
        calc x⁻¹ e = x⁻¹ (x e) := by rw [hx e he]
          _ = (x⁻¹ * x) e := rfl
          _ = e := by rw [inv_mul_cancel, MulAut.one_apply]}
  have hW0le : W₀ ≤ Cb := fun c hc => hc.1
  have hconjW : ∀ c' ∈ Cb, ∀ c ∈ W₀, c' * c * c'⁻¹ ∈ W₀ := by
    intro c' hc' c hc
    refine ⟨⟨Subgroup.mem_centralizer_iff.mpr ?_, ?_⟩, ?_⟩
    · intro b hb
      have hbc' : b * c' = c' * b := Subgroup.mem_centralizer_iff.1 hc'.1 b hb
      have hbc : b * c = c * b := Subgroup.mem_centralizer_iff.1 hc.1.1 b hb
      have hbc'inv : b * c'⁻¹ = c'⁻¹ * b := (show Commute b c' from hbc').inv_right.eq
      calc b * (c' * c * c'⁻¹) = (b * c') * c * c'⁻¹ := by group
        _ = (c' * b) * c * c'⁻¹ := by rw [hbc']
        _ = c' * (b * c) * c'⁻¹ := by group
        _ = c' * (c * b) * c'⁻¹ := by rw [hbc]
        _ = c' * c * (b * c'⁻¹) := by group
        _ = c' * c * (c'⁻¹ * b) := by rw [hbc'inv]
        _ = (c' * c * c'⁻¹) * b := by group
    · exact (Mbar M V₀ V hV).mul_mem ((Mbar M V₀ V hV).mul_mem hc'.2 hc.1.2)
        ((Mbar M V₀ V hV).inv_mem hc'.2)
    · intro e he
      have hc'inv_E : c'⁻¹ e ∈ E := hB2 c'⁻¹ (Cb.inv_mem hc') e he
      calc (c' * c * c'⁻¹) e = c' (c (c'⁻¹ e)) := by simp only [MulAut.mul_apply]
        _ = c' (c'⁻¹ e) := by rw [hc.2 _ hc'inv_E]
        _ = e := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hW0norm : Cb ≤ Subgroup.normalizer (W₀ : Set (MulAut (Vtil V₀ V hV))) := by
    intro c' hc'
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · exact hconjW c' hc' c
    · intro hc
      have := hconjW c'⁻¹ (Cb.inv_mem hc') (c' * c * c'⁻¹) hc
      rwa [show c'⁻¹ * (c' * c * c'⁻¹) * (c'⁻¹)⁻¹ = c by group] at this
  have hW0p : IsPGroup 2 W₀ := by
    rw [isPGroup_iff_primeFactors_card_subset (p := 2) (by norm_num : 2 ≠ 0)]
    intro q hq
    obtain ⟨hqprime, hqdvdcard, -⟩ := Nat.mem_primeFactors.mp hq
    haveI : Fact q.Prime := ⟨hqprime⟩
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' q hqdvdcard
    have hqeq2 : q = 2 := by
      by_contra hne
      have hcop : Nat.Coprime (orderOf ((w : W₀) : MulAut (Vtil V₀ V hV))) 2 := by
        rw [Subgroup.orderOf_coe, hw]
        exact (Nat.coprime_primes hqprime Nat.prime_two).mpr hne
      have hWtil : IsPGroup 2 (Vtil V₀ V hV) := by
        intro v
        obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV v
        exact ⟨1, by rw [pow_one, ← map_pow, IntMod.sq_eq_one, map_one]⟩
      have hbcomm : ∀ a ∈ Bb, a * ((w : W₀) : MulAut (Vtil V₀ V hV)) =
          ((w : W₀) : MulAut (Vtil V₀ V hV)) * a :=
        fun a ha => Subgroup.mem_centralizer_iff.1 w.2.1.1 a ha
      have hfix : ∀ v : Vtil V₀ V hV, (∀ a ∈ Bb, a v = v) →
          ((w : W₀) : MulAut (Vtil V₀ V hV)) v = v :=
        fun v hv => w.2.2 v (mem_fixV.2 hv)
      have hw1 : ((w : W₀) : MulAut (Vtil V₀ V hV)) = 1 :=
        CFSG.GroupTheory.eq_one_of_forall_fixed_of_coprime hWtil hBp hcop hbcomm hfix
      have hw1' : w = 1 := Subtype.ext (by simpa using hw1)
      have hord : orderOf w = 1 := by rw [hw1', orderOf_one]
      rw [hw] at hord
      exact hqprime.one_lt.ne' hord
    rw [hqeq2]
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_rfl, (by norm_num : (2 : ℕ) ≠ 0)⟩
  have hB5 : ⁅Cb, Yb⁆ ≤ W₀ := by
    rw [Subgroup.commutator_le]
    intro c hc y hy
    refine ⟨?_, ?_⟩
    · have hcy : y * c⁻¹ * y⁻¹ ∈ Cb := hB1 y hy c⁻¹ (Cb.inv_mem hc)
      rw [commutatorElement_def, show c * y * c⁻¹ * y⁻¹ = c * (y * c⁻¹ * y⁻¹) by group]
      exact Cb.mul_mem hc hcy
    · intro e he
      have hyinv_e : y⁻¹ e = e :=
        barSub_fixes_fixV_BOf h hgen hY y⁻¹ (Yb.inv_mem hy) e he
      have hc_inv_e : c⁻¹ e ∈ E := hB2 c⁻¹ (Cb.inv_mem hc) e he
      have hy_cinv_e : y (c⁻¹ e) = c⁻¹ e :=
        barSub_fixes_fixV_BOf h hgen hY y hy _ hc_inv_e
      calc ⁅c, y⁆ e = c (y (c⁻¹ (y⁻¹ e))) := by
            rw [commutatorElement_def]; simp only [MulAut.mul_apply]
        _ = c (y (c⁻¹ e)) := by rw [hyinv_e]
        _ = c (c⁻¹ e) := by rw [hy_cinv_e]
        _ = e := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hB6 : W₀ ≤ pCoreOf 2 Cb :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hW0le hW0norm hW0p
  exact hB5.trans hB6

private theorem isPGroup_Vtil (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) :
    IsPGroup 2 (Vtil V₀ V hV) := by
  intro v
  obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV v
  exact ⟨1, by rw [pow_one, ← map_pow, IntMod.sq_eq_one, map_one]⟩

theorem V₀_le_UOf {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp64 n M V₀ V g)
    (hgen : GenHyp M V g) : V₀ ≤ UOf M V g := by
  have hV := h.elemAbelian
  have hM : M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := h.le_normalizer₀
  have hBne : ¬ BOf M V g ≤ F11.CTilde M V₀ V :=
    fun hb => barSub_BOf_ne_bot h hgen ((barSub_eq_bot_iff hV hM hM₀ inf_le_right).2 hb)
  have hF2 := six_four_three_of_gen h hgen (D := BOf M V g) le_rfl hBne
  have hF1 := six_four_four_centralizer_V h
  intro v hv
  apply hF2.1
  have hvCB : v ∈ V ⊓ Subgroup.centralizer (BOf M V g : Set G) := by
    rw [hF1]
    exact Subgroup.mem_sup_right hv
  exact hvCB

theorem preTil_imgTil_of_le {V₀ V U : Subgroup G} (hV : IsElemAbelian 2 V) (hUV : U ≤ V)
    (hV₀U : V₀ ≤ U) : preTil V₀ V hV (imgTil V₀ V hV U) = U := by
  apply le_antisymm
  · intro v hv
    rw [mem_preTil] at hv
    obtain ⟨x, hx, hxU⟩ := hv
    rw [mem_imgTil] at hxU
    obtain ⟨y, hyU, hyx⟩ := hxU
    rw [mkTil_eq_iff] at hyx
    rw [← hx]
    have : x.val = (y.val * x.val⁻¹)⁻¹ * y.val := by group
    rw [this]
    exact U.mul_mem (hV₀U (V₀.inv_mem hyx)) hyU
  · intro u hu
    have huV : u ∈ V := hUV hu
    rw [mem_preTil_iff_of_mem V₀ V hV _ huV, mem_imgTil]
    exact ⟨IntMod.mk hV ⟨u, huV⟩, hu, rfl⟩

theorem imgTil_UOf_ne_top {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp64 n M V₀ V g)
    (hgen : GenHyp M V g) : imgTil V₀ V h.elemAbelian (UOf M V g) ≠ ⊤ := by
  have hV := h.elemAbelian
  have hV0U : V₀ ≤ UOf M V g := V₀_le_UOf h hgen
  have hUV : UOf M V g ≤ V := inf_le_left
  intro htop
  have hpre : preTil V₀ V hV ⊤ = UOf M V g := by
    rw [← htop, preTil_imgTil_of_le hV hUV hV0U]
  rw [preTil_top] at hpre
  obtain ⟨hO, -⟩ := h.inCalOStar
  exact hO.2.1 (by rw [hpre]; exact inf_le_right)

theorem mem_imgTil_UOf_iff {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp64 n M V₀ V g)
    (hgen : GenHyp M V g) {b : G} (hb : b ∈ BOf M V g) (hbC : b ∉ F11.CTilde M V₀ V)
    (hbs : b ∈ stabTil V₀ V) (w : Vtil V₀ V h.elemAbelian) :
    w ∈ imgTil V₀ V h.elemAbelian (UOf M V g) ↔
      w * (actTil V₀ V h.elemAbelian ⟨b, hbs⟩ w)⁻¹ ∈
        fixV (barSub V₀ V h.elemAbelian (BOf M V g)) := by
  have hV := h.elemAbelian
  have hM : M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := h.le_normalizer₀
  obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV w
  have hmemV : ⁅x.val, b⁆ ∈ V := by
    have hbN : b ∈ Subgroup.normalizer (V : Set G) := hM hb.2
    rw [commutatorElement_def, show x.val * b * x.val⁻¹ * b⁻¹ =
      x.val * (b * x.val⁻¹ * b⁻¹) by group]
    exact V.mul_mem x.val_mem
      ((Subgroup.mem_normalizer_iff.1 hbN x.val⁻¹).1 (V.inv_mem x.val_mem))
  have hval : (x * (actStab V₀ V hV ⟨b, hbs⟩ x)⁻¹).val = ⁅x.val, b⁆ := by
    rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val, commutatorElement_def]
    group
  have heq : x * (actStab V₀ V hV ⟨b, hbs⟩ x)⁻¹ = IntMod.mk hV ⟨⁅x.val, b⁆, hmemV⟩ :=
    IntMod.val_injective hval
  have hw_eq : mkTil V₀ V hV x * (actTil V₀ V hV ⟨b, hbs⟩ (mkTil V₀ V hV x))⁻¹ =
      mkTil V₀ V hV (IntMod.mk hV ⟨⁅x.val, b⁆, hmemV⟩) := by
    rw [actTil_mk, ← map_inv, ← map_mul, heq]
  have h1 : mkTil V₀ V hV x * (actTil V₀ V hV ⟨b, hbs⟩ (mkTil V₀ V hV x))⁻¹ ∈
      fixV (barSub V₀ V hV (BOf M V g)) ↔
      ⁅x.val, b⁆ ∈ preTil V₀ V hV (fixV (barSub V₀ V hV (BOf M V g))) := by
    rw [hw_eq]
    exact (mem_preTil_iff_of_mem V₀ V hV _ hmemV).symm
  have hpre := preTil_fixV_barSub_BOf h hgen
  have hF1 := six_four_four_centralizer_V h
  have hF4 := six_four_four_iff_of_gen h hgen hb hbC
  have hU : x.val ∈ UOf M V g ↔ mkTil V₀ V hV x ∈ imgTil V₀ V hV (UOf M V g) := by
    change x.val ∈ V ⊓ conjSubgroup M g ↔
      mkTil V₀ V hV x ∈ imgTil V₀ V hV (V ⊓ conjSubgroup M g)
    have heqU := preTil_imgTil_of_le hV inf_le_left (V₀_le_UOf h hgen)
    constructor
    · intro hx
      have hxpre : x.val ∈ preTil V₀ V hV (imgTil V₀ V hV (V ⊓ conjSubgroup M g)) := by
        rwa [heqU]
      have hx' := (mem_preTil_iff_of_mem V₀ V hV _ x.val_mem).1 hxpre
      have hxeq : (IntMod.mk hV ⟨x.val, x.val_mem⟩ : IntMod V hV) = x :=
        IntMod.val_injective rfl
      rwa [hxeq] at hx'
    · intro hx
      have hx' : mkTil V₀ V hV (IntMod.mk hV ⟨x.val, x.val_mem⟩) ∈
          imgTil V₀ V hV (V ⊓ conjSubgroup M g) := by
        have hxeq : (IntMod.mk hV ⟨x.val, x.val_mem⟩ : IntMod V hV) = x :=
          IntMod.val_injective rfl
        rwa [hxeq]
      have hxpre : x.val ∈ preTil V₀ V hV (imgTil V₀ V hV (V ⊓ conjSubgroup M g)) :=
        (mem_preTil_iff_of_mem V₀ V hV _ x.val_mem).2 hx'
      rwa [heqU] at hxpre
  rw [← hU, h1, hpre, ← hF1]
  exact (hF4 x.val x.val_mem).symm

theorem mQuot_UOf_eq_rkIdx {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp64 n M V₀ V g)
    (hgen : GenHyp M V g) :
    E3.mQuot V (UOf M V g) = rkIdx (imgTil V₀ V h.elemAbelian (UOf M V g)) := by
  change E3.mQuot V (V ⊓ conjSubgroup M g) =
    rkIdx (imgTil V₀ V h.elemAbelian (V ⊓ conjSubgroup M g))
  conv_lhs => rw [← preTil_imgTil_of_le h.elemAbelian inf_le_left (V₀_le_UOf h hgen)]
  exact mQuot_preTil V₀ V h.elemAbelian (imgTil V₀ V h.elemAbelian (V ⊓ conjSubgroup M g))

theorem index_imgTil_UOf_eq_two {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp64 n M V₀ V g)
    (hgen : GenHyp M V g) (hν : E3.mQuot V (UOf M V g) ≤ 1) :
    (imgTil V₀ V h.elemAbelian (UOf M V g)).index = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUtop : imgTil V₀ V h.elemAbelian (UOf M V g) ≠ ⊤ := imgTil_UOf_ne_top h hgen
  obtain ⟨k, hk⟩ := (isPGroup_Vtil V₀ V h.elemAbelian).index
    (imgTil V₀ V h.elemAbelian (UOf M V g))
  have hνk : E3.mQuot V (UOf M V g) = k := by
    rw [mQuot_UOf_eq_rkIdx h hgen, rkIdx, hk, padicValNat.prime_pow]
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hUtop (Subgroup.index_eq_one.1 hk)
  have hk_le : k ≤ 1 := by rw [← hνk]; exact hν
  have hk1 : k = 1 := by omega
  rw [hk, hk1, pow_one]

theorem imgTil_UOf_stable_X {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp64 n M V₀ V g)
    (hgen : GenHyp M V g) {X : Subgroup (MulAut (Vtil V₀ V h.elemAbelian))}
    (hXB : ⁅X, barSub V₀ V h.elemAbelian (BOf M V g)⁆ = ⊥) :
    ∀ x ∈ X, ∀ u ∈ imgTil V₀ V h.elemAbelian (UOf M V g),
      x u ∈ imgTil V₀ V h.elemAbelian (UOf M V g) := by
  have hV := h.elemAbelian
  have hM : M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := h.le_normalizer₀
  have hBne : ¬ BOf M V g ≤ F11.CTilde M V₀ V :=
    fun hb => barSub_BOf_ne_bot h hgen ((barSub_eq_bot_iff hV hM hM₀ inf_le_right).2 hb)
  obtain ⟨b, hbB, hbC⟩ : ∃ b ∈ BOf M V g, b ∉ F11.CTilde M V₀ V := by
    by_contra hcon
    push Not at hcon
    exact hBne hcon
  have hbs : b ∈ stabTil V₀ V := (inf_le_right.trans (le_stabTil hM hM₀)) hbB
  intro x hx u hu
  have hbbar_mem : actTil V₀ V hV ⟨b, hbs⟩ ∈ barSub V₀ V hV (BOf M V g) :=
    actTil_mem_barSub V₀ V hV hbB hbs
  have hcomm : ∀ φ ∈ barSub V₀ V hV (BOf M V g), x * φ = φ * x := by
    intro φ hφ
    exact commutatorElement_eq_one_iff_mul_comm.1
      (Subgroup.mem_bot.1 ((Subgroup.commutator_le.1 hXB.le) x hx φ hφ))
  have hfixE : ∀ e ∈ fixV (barSub V₀ V hV (BOf M V g)),
      x e ∈ fixV (barSub V₀ V hV (BOf M V g)) := by
    intro e he
    rw [mem_fixV] at he ⊢
    intro φ hφ
    have hxφ := hcomm φ hφ
    rw [← MulAut.mul_apply, ← hxφ, MulAut.mul_apply, he φ hφ]
  have huE : u * (actTil V₀ V hV ⟨b, hbs⟩ u)⁻¹ ∈
      fixV (barSub V₀ V hV (BOf M V g)) :=
    (mem_imgTil_UOf_iff h hgen hbB hbC hbs u).1 hu
  have hxE := hfixE _ huE
  have hcommb : actTil V₀ V hV ⟨b, hbs⟩ (x u) = x (actTil V₀ V hV ⟨b, hbs⟩ u) := by
    rw [← MulAut.mul_apply, ← hcomm (actTil V₀ V hV ⟨b, hbs⟩) hbbar_mem, MulAut.mul_apply]
  rw [mem_imgTil_UOf_iff h hgen hbB hbC hbs]
  rw [hcommb, ← map_inv, ← map_mul]
  exact hxE

theorem imgTil_UOf_stable_barSub {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp64 n M V₀ V g)
    {Y : Subgroup G} (hY : Y ≤ M ⊓ conjSubgroup M g) :
    ∀ y ∈ barSub V₀ V h.elemAbelian Y, ∀ u ∈ imgTil V₀ V h.elemAbelian (UOf M V g),
      y u ∈ imgTil V₀ V h.elemAbelian (UOf M V g) := by
  have hV := h.elemAbelian
  intro y hy u hu
  obtain ⟨y₀, hy₀Y, rfl⟩ := (mem_barSub V₀ V hV Y y).1 hy
  obtain ⟨x, hxU, hxeq⟩ := (mem_imgTil V₀ V hV (UOf M V g) u).1 hu
  rw [← hxeq]
  have hy₀inf : (y₀ : G) ∈ M ⊓ conjSubgroup M g := hY hy₀Y
  have hy₀M : (y₀ : G) ∈ M := (Subgroup.mem_inf.1 hy₀inf).1
  have hy₀Mg : (y₀ : G) ∈ conjSubgroup M g := (Subgroup.mem_inf.1 hy₀inf).2
  rw [actTil_mk, mem_imgTil]
  refine ⟨actStab V₀ V hV y₀ x, ?_, rfl⟩
  rw [actStab_apply_val]
  exact ⟨(Subgroup.mem_normalizer_iff.1 (h.normalizer_eq.symm.le hy₀M) x.val).1 hxU.1,
    (conjSubgroup M g).mul_mem ((conjSubgroup M g).mul_mem hy₀Mg hxU.2)
      ((conjSubgroup M g).inv_mem hy₀Mg)⟩

theorem one_lt_mQuot_UOf {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp64 n M V₀ V g)
    (hgen : GenHyp M V g) (hirr : ConjGenerated M V₀ V)
    {X : Subgroup (MulAut (Vtil V₀ V h.elemAbelian))} (hX1 : X ≠ ⊥)
    (hXnorm : ∀ m ∈ Mbar M V₀ V h.elemAbelian, ∀ x ∈ X, m * x * m⁻¹ ∈ X)
    (hXB : ⁅X, barSub V₀ V h.elemAbelian (BOf M V g)⁆ = ⊥) :
    1 < E3.mQuot V (UOf M V g) := by
  have hV := h.elemAbelian
  have hM : M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := h.le_normalizer₀
  by_contra hle
  have hν : E3.mQuot V (UOf M V g) ≤ 1 := by omega
  have hidx := index_imgTil_UOf_eq_two h hgen hν
  have hUt : imgTil V₀ V hV (UOf M V g) ≠ ⊤ := imgTil_UOf_ne_top h hgen
  have htriv : ∀ t ∈ (X : Set (MulAut (Vtil V₀ V hV))), ∀ w,
      t w * w⁻¹ ∈ imgTil V₀ V hV (UOf M V g) := by
    intro t ht w
    rw [Subgroup.mul_mem_iff_of_index_two hidx]
    constructor
    · intro htw
      have h := imgTil_UOf_stable_X h hgen (X := X) hXB t⁻¹ (X.inv_mem ht) (t w) htw
      simpa using h
    · intro hw
      refine imgTil_UOf_stable_X h hgen (X := X) hXB t ht w ?_
      simpa using (imgTil V₀ V hV (UOf M V g)).inv_mem hw
  have hT : ∀ m ∈ Mbar M V₀ V hV, ∀ t ∈ (X : Set (MulAut (Vtil V₀ V hV))),
      m * t * m⁻¹ ∈ (X : Set (MulAut (Vtil V₀ V hV))) :=
    fun m hm t ht => hXnorm m hm t ht
  have hAr3 := eq_one_of_acts_trivially_mod hV hM hM₀ hirr hUt hT htriv
  apply hX1
  refine le_bot_iff.1 fun x hx => ?_
  rw [Subgroup.mem_bot]
  exact hAr3 x hx

theorem commutator_eq_bot_of_forall_normalizing
    {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp64 n M V₀ V g)
    (hgen : GenHyp M V g) (hirr : ConjGenerated M V₀ V) {Y : Subgroup G}
    (hY : Y ≤ LOf V g ⊓ M ⊓ conjSubgroup M g)
    {X : Subgroup (MulAut (Vtil V₀ V h.elemAbelian))}
    (hXM : X ≤ Mbar M V₀ V h.elemAbelian)
    (hXnorm : ∀ m ∈ Mbar M V₀ V h.elemAbelian, ∀ x ∈ X, m * x * m⁻¹ ∈ X)
    (hXB : ⁅X, barSub V₀ V h.elemAbelian (BOf M V g)⁆ = ⊥) :
    ⁅X, barSub V₀ V h.elemAbelian Y⁆ = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV := h.elemAbelian
  have hM : M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := h.le_normalizer₀
  let Bb := barSub V₀ V hV (BOf M V g)
  let Cb := cMbarBOf M V₀ V hV g
  let Yb := barSub V₀ V hV Y
  have hXcB : X ≤ Cb := by
    refine le_inf ?_ hXM
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (commutatorElement_eq_one_iff_mul_comm.1
      (Subgroup.mem_bot.1 ((Subgroup.commutator_le.1 hXB.le) x hx b hb))).symm
  have hYM : Y ≤ M := fun y hy => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (hY hy)).1).2
  have hYbM : Yb ≤ Mbar M V₀ V hV := barSub_mono V₀ V hV hYM
  have h1 : ⁅X, Yb⁆ ≤ pCoreOf 2 Cb :=
    (Subgroup.commutator_mono hXcB le_rfl).trans (fourteen_seven_three h hgen hY)
  have h2 : ⁅X, Yb⁆ ≤ X := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hyMbar : y ∈ Mbar M V₀ V hV := hYbM hy
    have hconj : y * x⁻¹ * y⁻¹ ∈ X := hXnorm y hyMbar x⁻¹ (X.inv_mem hx)
    rw [commutatorElement_def, show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
    exact X.mul_mem hx hconj
  have hQ : ⁅X, Yb⁆ ≤ X ⊓ pCoreOf 2 Cb := le_inf h2 h1
  have hQp : IsPGroup 2 ↥(X ⊓ pCoreOf 2 Cb) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup
      (G := MulAut (Vtil V₀ V hV)) 2 Cb).to_le inf_le_right
  have hQX : X ⊓ pCoreOf 2 Cb ≤ X := inf_le_left
  have hconjQ : ∀ x ∈ X, ∀ q ∈ X ⊓ pCoreOf 2 Cb,
      x * q * x⁻¹ ∈ X ⊓ pCoreOf 2 Cb := by
    intro x hx q hq
    refine ⟨hXnorm x (hXM hx) q hq.1, ?_⟩
    have hxnormCore : x ∈ Subgroup.normalizer (pCoreOf 2 Cb : Set (MulAut (Vtil V₀ V hV))) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Cb (hXcB hx)
    exact (Subgroup.mem_normalizer_iff.1 hxnormCore q).1 hq.2
  have hQnorm : X ≤ Subgroup.normalizer (X ⊓ pCoreOf 2 Cb :
      Set (MulAut (Vtil V₀ V hV))) := by
    intro x hx
    exact Subgroup.mem_normalizer_iff.mpr fun q =>
      ⟨fun hq => hconjQ x hx q hq, fun hq => by
        have h := hconjQ x⁻¹ (X.inv_mem hx) (x * q * x⁻¹) hq
        rwa [show x⁻¹ * (x * q * x⁻¹) * (x⁻¹)⁻¹ = q by group] at h⟩
  have hQXcore : X ⊓ pCoreOf 2 Cb ≤ pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQX hQnorm hQp
  haveI : Nontrivial (Vtil V₀ V hV) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply imgTil_UOf_ne_top h hgen
    refine eq_top_iff.2 fun u _ => ?_
    rw [show u = 1 from Subsingleton.elim u 1]
    exact (imgTil V₀ V hV (UOf M V g)).one_mem
  have hnormX : Mbar M V₀ V hV ≤
      Subgroup.normalizer (X : Set (MulAut (Vtil V₀ V hV))) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx; exact hXnorm m hm x hx
    · intro hx
      have h := hXnorm m⁻¹ ((Mbar M V₀ V hV).inv_mem hm) (m * x * m⁻¹) hx
      rwa [show m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ = x by group] at h
  have hnormCore : Mbar M V₀ V hV ≤
      Subgroup.normalizer (pCoreOf 2 X : Set (MulAut (Vtil V₀ V hV))) :=
    hnormX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hst : ∀ m ∈ Mbar M V₀ V hV, ∀ p ∈ pCoreOf 2 X, m * p * m⁻¹ ∈ pCoreOf 2 X := by
    intro m hm p hp
    exact (Subgroup.mem_normalizer_iff.1 (hnormCore hm) p).1 hp
  have hcorebot : pCoreOf 2 X = ⊥ :=
    eq_bot_of_isPGroup_of_stable hV hM hM₀ hirr
      (P := pCoreOf 2 X) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) hst
  exact le_bot_iff.1 (hQ.trans (hQXcore.trans (le_of_eq hcorebot)))

theorem barSub_comm_of_isCyclic {V₀ V Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hYs : Y ≤ stabTil V₀ V) (hYc : IsCyclic ↥Y) :
    ∀ a ∈ barSub V₀ V hV Y, ∀ b ∈ barSub V₀ V hV Y, a * b = b * a := by
  intro a ha b hb
  obtain ⟨ga, hgaY, rfl⟩ := (mem_barSub V₀ V hV Y a).1 ha
  obtain ⟨gb, hgbY, rfl⟩ := (mem_barSub V₀ V hV Y b).1 hb
  have hcommY : (⟨(ga : G), hgaY⟩ : ↥Y) * ⟨(gb : G), hgbY⟩ =
      ⟨(gb : G), hgbY⟩ * ⟨(ga : G), hgaY⟩ :=
    (IsCyclic.commGroup (α := ↥Y)).mul_comm _ _
  have hcomm : ga * gb = gb * ga := by
    apply Subtype.ext
    exact congrArg (fun y : ↥Y => (y : G)) hcommY
  rw [← map_mul, ← map_mul, hcomm]

theorem barSub_pow_card {V₀ V Y : Subgroup G} (hV : IsElemAbelian 2 V)
    (hYs : Y ≤ stabTil V₀ V) : ∀ a ∈ barSub V₀ V hV Y, a ^ Nat.card Y = 1 := by
  intro a ha
  obtain ⟨g, hgY, rfl⟩ := (mem_barSub V₀ V hV Y a).1 ha
  have hYpow : (⟨(g : G), hgY⟩ : ↥Y) ^ Nat.card Y = 1 := pow_card_eq_one'
  have hgpow : g ^ Nat.card Y = 1 := by
    refine Subtype.ext ?_
    have h := congrArg (fun y : ↥Y => (y : G)) hYpow
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h
  rw [← map_pow, hgpow, map_one]

private theorem mkTil_mul_inv_mem_imgTil_iff {V₀ V U : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV₀U : V₀ ≤ U) (x y : IntMod V hV) :
    mkTil V₀ V hV x * (mkTil V₀ V hV y)⁻¹ ∈ imgTil V₀ V hV U ↔
      x.val * y.val⁻¹ ∈ U := by
  have hxy : mkTil V₀ V hV x * (mkTil V₀ V hV y)⁻¹ = mkTil V₀ V hV (x * y⁻¹) := by
    rw [map_mul, map_inv]
  rw [hxy, mem_imgTil]
  constructor
  · rintro ⟨q, hqU, hq⟩
    rw [mkTil_eq_iff] at hq
    have hval : (x * y⁻¹).val = x.val * y.val⁻¹ := by
      rw [IntMod.val_mul, IntMod.val_inv]
    rw [hval] at hq
    have hq' : x.val * y.val⁻¹ = (q.val * (x.val * y.val⁻¹)⁻¹)⁻¹ * q.val := by group
    rw [hq']
    exact U.mul_mem (hV₀U (V₀.inv_mem hq)) hqU
  · intro hxyU
    refine ⟨x * y⁻¹, ?_, rfl⟩
    rw [IntMod.val_mul, IntMod.val_inv]
    exact hxyU

theorem exists_barSub_congr {n : ℕ} {M V₀ V : Subgroup G} {g : G} (h : Hyp64 n M V₀ V g)
    (hgen : GenHyp M V g) {Y : Subgroup G} (hY : IsRegularTorus M V g Y)
    {X : Subgroup (MulAut (Vtil V₀ V h.elemAbelian))}
    (hXB : ⁅X, barSub V₀ V h.elemAbelian (BOf M V g)⁆ = ⊥)
    (hXY : ⁅X, barSub V₀ V h.elemAbelian Y⁆ = ⊥)
    {x : MulAut (Vtil V₀ V h.elemAbelian)} (hx : x ∈ X) :
    ∃ y ∈ barSub V₀ V h.elemAbelian Y, ∀ w,
      x w * (y w)⁻¹ ∈ imgTil V₀ V h.elemAbelian (UOf M V g) := by
  have hV := h.elemAbelian
  have hM : M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := h.le_normalizer₀
  let H : Subgroup (Vtil V₀ V hV) := imgTil V₀ V hV (UOf M V g)
  have hUt : H ≠ ⊤ := imgTil_UOf_ne_top h hgen
  have hV0U : V₀ ≤ UOf M V g := V₀_le_UOf h hgen
  have hYM : Y ≤ M := fun y hy => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (hY.1 hy)).1).2
  have hY' : Y ≤ M ⊓ conjSubgroup M g := fun y hy =>
    ⟨hYM hy, (Subgroup.mem_inf.1 (hY.1 hy)).2⟩
  have hYs : Y ≤ stabTil V₀ V := hYM.trans (le_stabTil hM hM₀)
  obtain ⟨w₀, hw₀H⟩ : ∃ w₀, w₀ ∉ H := by
    by_contra hcon
    push Not at hcon
    exact hUt (eq_top_iff.2 fun w _ => hcon w)
  obtain ⟨x₀, rfl⟩ := mkTil_surjective V₀ V hV w₀
  obtain ⟨x₁, hx₁⟩ := mkTil_surjective V₀ V hV (x (mkTil V₀ V hV x₀))
  have hxw₀H : x (mkTil V₀ V hV x₀) ∉ H := by
    intro hmem
    have h := imgTil_UOf_stable_X h hgen (X := X) hXB x⁻¹ (X.inv_mem hx)
      (x (mkTil V₀ V hV x₀)) hmem
    exact hw₀H (by simpa using h)
  have hv₀U : x₀.val ∉ UOf M V g := by
    intro hmem
    exact hw₀H ((mem_imgTil V₀ V hV (UOf M V g) (mkTil V₀ V hV x₀)).2 ⟨x₀, hmem, rfl⟩)
  have hv₁U : x₁.val ∉ UOf M V g := by
    intro hmem
    apply hxw₀H
    rw [← hx₁]
    exact (mem_imgTil V₀ V hV (UOf M V g) (mkTil V₀ V hV x₁)).2 ⟨x₁, hmem, rfl⟩
  obtain ⟨y, hyY, hyU⟩ := hY.2.2.2 x₀.val x₀.val_mem hv₀U x₁.val x₁.val_mem hv₁U
  have hyStab : y ∈ stabTil V₀ V := hYs hyY
  let ybar := actTil V₀ V hV ⟨y, hyStab⟩
  have hybarHst : ∀ w ∈ H, ybar w ∈ H :=
    imgTil_UOf_stable_barSub h hY' ybar (actTil_mem_barSub V₀ V hV hyY hyStab)
  have hxHst : ∀ w ∈ H, x w ∈ H := imgTil_UOf_stable_X h hgen (X := X) hXB x hx
  have hstabc : ∀ φ : MulAut (Vtil V₀ V hV), (∀ w ∈ H, φ w ∈ H) →
      ∀ a b : Vtil V₀ V hV, a * b⁻¹ ∈ H → φ a * (φ b)⁻¹ ∈ H := by
    intro φ hφ a b hab
    rw [show φ a * (φ b)⁻¹ = φ (a * b⁻¹) by rw [map_mul, map_inv]]
    exact hφ _ hab
  have hwb : x (mkTil V₀ V hV x₀) * (ybar (mkTil V₀ V hV x₀))⁻¹ ∈ H := by
    have hiff := mkTil_mul_inv_mem_imgTil_iff hV hV0U x₁
      (actStab V₀ V hV ⟨y, hyStab⟩ x₀)
    rw [← hx₁, actTil_mk, hiff, actStab_apply_val]
    have h2 : x₁.val * (y * x₀.val * y⁻¹)⁻¹ = (y * x₀.val * y⁻¹ * x₁.val⁻¹)⁻¹ := by
      group
    rw [h2]
    exact (UOf M V g).inv_mem hyU
  refine ⟨ybar, actTil_mem_barSub V₀ V hV hyY hyStab, ?_⟩
  intro w
  by_cases hwH : w ∈ H
  · exact H.mul_mem (hxHst w hwH) (H.inv_mem (hybarHst w hwH))
  · obtain ⟨x₂, rfl⟩ := mkTil_surjective V₀ V hV w
    have hv₂U : x₂.val ∉ UOf M V g := by
      intro hmem
      exact hwH ((mem_imgTil V₀ V hV (UOf M V g) (mkTil V₀ V hV x₂)).2 ⟨x₂, hmem, rfl⟩)
    obtain ⟨y', hy'Y, hy'U⟩ := hY.2.2.2 x₀.val x₀.val_mem hv₀U x₂.val x₂.val_mem hv₂U
    have hy'Stab : y' ∈ stabTil V₀ V := hYs hy'Y
    let ybar' := actTil V₀ V hV ⟨y', hy'Stab⟩
    have hy'barHst : ∀ w ∈ H, ybar' w ∈ H :=
      imgTil_UOf_stable_barSub h hY' ybar' (actTil_mem_barSub V₀ V hV hy'Y hy'Stab)
    have hwa : mkTil V₀ V hV x₂ * (ybar' (mkTil V₀ V hV x₀))⁻¹ ∈ H := by
      have hiff := mkTil_mul_inv_mem_imgTil_iff hV hV0U x₂
        (actStab V₀ V hV ⟨y', hy'Stab⟩ x₀)
      rw [actTil_mk, hiff, actStab_apply_val]
      have h2 : x₂.val * (y' * x₀.val * y'⁻¹)⁻¹ =
          (y' * x₀.val * y'⁻¹ * x₂.val⁻¹)⁻¹ := by group
      rw [h2]
      exact (UOf M V g).inv_mem hy'U
    have haw : ybar' (mkTil V₀ V hV x₀) * (mkTil V₀ V hV x₂)⁻¹ ∈ H := by
      simpa [mul_inv_rev] using H.inv_mem hwa
    have hA : x (mkTil V₀ V hV x₂) * (x (ybar' (mkTil V₀ V hV x₀)))⁻¹ ∈ H :=
      hstabc x hxHst (mkTil V₀ V hV x₂) (ybar' (mkTil V₀ V hV x₀)) hwa
    have hB : ybar' (x (mkTil V₀ V hV x₀)) *
        (ybar' (ybar (mkTil V₀ V hV x₀)))⁻¹ ∈ H :=
      hstabc ybar' hy'barHst (x (mkTil V₀ V hV x₀))
        (ybar (mkTil V₀ V hV x₀)) hwb
    have hE : ybar (ybar' (mkTil V₀ V hV x₀)) *
        (ybar (mkTil V₀ V hV x₂))⁻¹ ∈ H :=
      hstabc ybar hybarHst (ybar' (mkTil V₀ V hV x₀)) (mkTil V₀ V hV x₂) haw
    have hxy' : x * ybar' = ybar' * x :=
      commutatorElement_eq_one_iff_mul_comm.1
        (Subgroup.mem_bot.1 ((Subgroup.commutator_le.1 hXY.le) x hx ybar'
          ⟨⟨y', hy'Stab⟩, hy'Y, rfl⟩))
    have hxa : x (ybar' (mkTil V₀ V hV x₀)) = ybar' (x (mkTil V₀ V hV x₀)) := by
      rw [← MulAut.mul_apply, hxy', MulAut.mul_apply]
    have hyy' : ybar' * ybar = ybar * ybar' :=
      barSub_comm_of_isCyclic hV hYs hY.2.2.1 ybar' ⟨⟨y', hy'Stab⟩, hy'Y, rfl⟩
        ybar ⟨⟨y, hyStab⟩, hyY, rfl⟩
    have hb : ybar' (ybar (mkTil V₀ V hV x₀)) = ybar (ybar' (mkTil V₀ V hV x₀)) := by
      rw [← MulAut.mul_apply, hyy', MulAut.mul_apply]
    have hprod : x (mkTil V₀ V hV x₂) * (ybar (mkTil V₀ V hV x₂))⁻¹ =
        (x (mkTil V₀ V hV x₂) * (x (ybar' (mkTil V₀ V hV x₀)))⁻¹) *
        (ybar' (x (mkTil V₀ V hV x₀)) * (ybar' (ybar (mkTil V₀ V hV x₀)))⁻¹) *
        (ybar (ybar' (mkTil V₀ V hV x₀)) * (ybar (mkTil V₀ V hV x₂))⁻¹) := by
      rw [hxa, hb]; group
    rw [hprod]
    exact H.mul_mem (H.mul_mem hA hB) hE

theorem fourteen_eight_one {n : ℕ} {M V₀ V : Subgroup G} {g : G}
    (h : Hyp64 n M V₀ V g) (hgen : GenHyp M V g)
    (hirr : ConjGenerated M V₀ V) {Y : Subgroup G} (hY : IsRegularTorus M V g Y)
    {X : Subgroup (MulAut (Vtil V₀ V h.elemAbelian))}
    (hX1 : X ≠ ⊥) (hXM : X ≤ Mbar M V₀ V h.elemAbelian)
    (hXnorm : ∀ m ∈ Mbar M V₀ V h.elemAbelian, ∀ x ∈ X, m * x * m⁻¹ ∈ X)
    (hXB : ⁅X, barSub V₀ V h.elemAbelian (BOf M V g)⁆ = ⊥) :
    1 < E3.mQuot V (UOf M V g) ∧ (∀ a ∈ X, ∀ b ∈ X, a * b = b * a) ∧
      ∀ x ∈ X, x ^ (2 ^ E3.mQuot V (UOf M V g) - 1) = 1 := by
  have hV := h.elemAbelian
  have hM : M ≤ Subgroup.normalizer (V : Set G) := h.normalizer_eq.symm.le
  have hM₀ : M ≤ Subgroup.normalizer (V₀ : Set G) := h.le_normalizer₀
  have hν := one_lt_mQuot_UOf h hgen hirr hX1 hXnorm hXB
  have hXY := commutator_eq_bot_of_forall_normalizing h hgen hirr hY.1 hXM hXnorm hXB
  let H : Subgroup (Vtil V₀ V hV) := imgTil V₀ V hV (UOf M V g)
  have hUt : H ≠ ⊤ := imgTil_UOf_ne_top h hgen
  have hYM : Y ≤ M := fun y hy => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (hY.1 hy)).1).2
  have hY' : Y ≤ M ⊓ conjSubgroup M g := fun y hy =>
    ⟨hYM hy, (Subgroup.mem_inf.1 (hY.1 hy)).2⟩
  have hYs : Y ≤ stabTil V₀ V := hYM.trans (le_stabTil hM hM₀)
  have hstabY : ∀ y ∈ barSub V₀ V hV Y, ∀ w ∈ H, y w ∈ H :=
    fun y hy => imgTil_UOf_stable_barSub h hY' y hy
  have hpartner : ∀ a ∈ X, ∃ y ∈ barSub V₀ V hV Y, ∀ w, a w * (y w)⁻¹ ∈ H :=
    fun a ha => exists_barSub_congr h hgen hY hXB hXY ha
  have hcomm_congr : ∀ a ∈ X, ∀ b ∈ X, ∀ v, (a * b) v * ((b * a) v)⁻¹ ∈ H := by
    intro a ha b hb v
    obtain ⟨ya, hya, hcona⟩ := hpartner a ha
    obtain ⟨yb, hyb, hconb⟩ := hpartner b hb
    have hyab : ya * yb = yb * ya :=
      barSub_comm_of_isCyclic hV hYs hY.2.2.1 ya hya yb hyb
    have hconab : (a * b) v * ((ya * yb) v)⁻¹ ∈ H := by
      have h1 := hcona (b v)
      have h2 := hconb v
      have h4 : ya ((b v) * (yb v)⁻¹) ∈ H := hstabY ya hya _ h2
      have h3 : ya (b v) * (ya (yb v))⁻¹ = ya ((b v) * (yb v)⁻¹) := by rw [map_mul, map_inv]
      have h4' : ya (b v) * (ya (yb v))⁻¹ ∈ H := by rw [h3]; exact h4
      have he : (a * b) v * ((ya * yb) v)⁻¹ = a (b v) * (ya (yb v))⁻¹ := by
        simp only [MulAut.mul_apply]
      rw [he]
      have he2 : a (b v) * (ya (yb v))⁻¹ =
          (a (b v) * (ya (b v))⁻¹) * (ya (b v) * (ya (yb v))⁻¹) := by group
      rw [he2]
      exact H.mul_mem h1 h4'
    have hconba : (b * a) v * ((ya * yb) v)⁻¹ ∈ H := by
      have h1 := hconb (a v)
      have h2 := hcona v
      have h4 : yb ((a v) * (ya v)⁻¹) ∈ H := hstabY yb hyb _ h2
      have h3 : yb (a v) * (yb (ya v))⁻¹ = yb ((a v) * (ya v)⁻¹) := by rw [map_mul, map_inv]
      have h4' : yb (a v) * (yb (ya v))⁻¹ ∈ H := by rw [h3]; exact h4
      have he : (b * a) v * ((ya * yb) v)⁻¹ = b (a v) * (yb (ya v))⁻¹ := by
        rw [MulAut.mul_apply, hyab, MulAut.mul_apply]
      rw [he]
      have he2 : b (a v) * (yb (ya v))⁻¹ =
          (b (a v) * (yb (a v))⁻¹) * (yb (a v) * (yb (ya v))⁻¹) := by group
      rw [he2]
      exact H.mul_mem h1 h4'
    have h2' : ((ya * yb) v) * ((b * a) v)⁻¹ ∈ H := by
      simpa [mul_inv_rev] using H.inv_mem hconba
    have he : (a * b) v * ((b * a) v)⁻¹ =
        ((a * b) v * ((ya * yb) v)⁻¹) * (((ya * yb) v) * ((b * a) v)⁻¹) := by group
    rw [he]
    exact H.mul_mem hconab h2'
  have habel : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
    let T1 : Set (MulAut (Vtil V₀ V hV)) :=
      {t | ∃ a ∈ X, ∃ b ∈ X, t = a * b * a⁻¹ * b⁻¹}
    have hT1 : ∀ m ∈ Mbar M V₀ V hV, ∀ t ∈ T1, m * t * m⁻¹ ∈ T1 := by
      rintro m hm t ⟨a, ha, b, hb, rfl⟩
      exact ⟨m * a * m⁻¹, hXnorm m hm a ha, m * b * m⁻¹, hXnorm m hm b hb, by group⟩
    have htriv1 : ∀ t ∈ T1, ∀ w, t w * w⁻¹ ∈ H := by
      rintro t ⟨a, ha, b, hb, rfl⟩ w
      have hw' : (a * b) (a⁻¹ (b⁻¹ w)) = (a * b * a⁻¹ * b⁻¹) w := by
        simp only [MulAut.mul_apply]
      have hw'' : (b * a) (a⁻¹ (b⁻¹ w)) = w := by
        simp only [MulAut.mul_apply, MulAut.apply_inv_self]
      have h := hcomm_congr a ha b hb (a⁻¹ (b⁻¹ w))
      rwa [hw', hw''] at h
    have h1 := eq_one_of_acts_trivially_mod hV hM hM₀ hirr hUt hT1 htriv1
    intro a ha b hb
    have h2 := h1 (a * b * a⁻¹ * b⁻¹) ⟨a, ha, b, hb, rfl⟩
    exact commutatorElement_eq_one_iff_mul_comm.1 (by rw [commutatorElement_def]; exact h2)
  have hexp : ∀ y ∈ X, y ^ (2 ^ E3.mQuot V (UOf M V g) - 1) = 1 := by
    intro a ha
    let T2 : Set (MulAut (Vtil V₀ V hV)) :=
      {t | ∃ x ∈ X, t = x ^ (2 ^ E3.mQuot V (UOf M V g) - 1)}
    have hT2 : ∀ m ∈ Mbar M V₀ V hV, ∀ t ∈ T2, m * t * m⁻¹ ∈ T2 := by
      rintro m hm t ⟨x, hx, rfl⟩
      exact ⟨m * x * m⁻¹, hXnorm m hm x hx, by
        rw [show m * x ^ (2 ^ E3.mQuot V (UOf M V g) - 1) * m⁻¹ =
          (m * x * m⁻¹) ^ (2 ^ E3.mQuot V (UOf M V g) - 1) by
            rw [conj_pow]]⟩
    have htriv2 : ∀ t ∈ T2, ∀ w, t w * w⁻¹ ∈ H := by
      rintro t ⟨x, hx, rfl⟩ w
      obtain ⟨y, hy, hcony⟩ := hpartner x hx
      have hstab : ∀ j, ∀ u ∈ H, (y ^ j) u ∈ H := by
        intro j
        induction j with
        | zero => intro u hu; simpa using hu
        | succ j ihj =>
          intro u hu
          rw [pow_succ, MulAut.mul_apply]
          exact ihj (y u) (hstabY y hy u hu)
      have hpow : ∀ k v, (x ^ k) v * ((y ^ k) v)⁻¹ ∈ H := by
        intro k
        induction k with
        | zero =>
          intro v
          simpa using H.one_mem
        | succ k ih =>
          intro v
          rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply]
          have h1 : (x ^ k) (x v) * ((y ^ k) (x v))⁻¹ ∈ H := ih (x v)
          have h2 : x v * (y v)⁻¹ ∈ H := hcony v
          have h3 : (y ^ k) (x v * (y v)⁻¹) ∈ H := hstab k _ h2
          have h4 : (y ^ k) (x v * (y v)⁻¹) = (y ^ k) (x v) * ((y ^ k) (y v))⁻¹ := by
            rw [map_mul, map_inv]
          have h3' : (y ^ k) (x v) * ((y ^ k) (y v))⁻¹ ∈ H := by rw [← h4]; exact h3
          have he : (x ^ k) (x v) * ((y ^ k) (y v))⁻¹ =
              ((x ^ k) (x v) * ((y ^ k) (x v))⁻¹) *
              ((y ^ k) (x v) * ((y ^ k) (y v))⁻¹) := by group
          rw [he]
          exact H.mul_mem h1 h3'
      have hN := hpow (2 ^ E3.mQuot V (UOf M V g) - 1) w
      have hyN : y ^ (2 ^ E3.mQuot V (UOf M V g) - 1) = 1 := by
        rw [← hY.2.1]
        exact barSub_pow_card hV hYs y hy
      rw [hyN, MulAut.one_apply] at hN
      simpa using hN
    have h2 := eq_one_of_acts_trivially_mod hV hM hM₀ hirr hUt hT2 htriv2
    exact h2 (a ^ (2 ^ E3.mQuot V (UOf M V g) - 1)) ⟨a, ha, rfl⟩
  exact ⟨hν, habel, hexp⟩

end CFSG.LocalAnalysis.WeakClosure81
