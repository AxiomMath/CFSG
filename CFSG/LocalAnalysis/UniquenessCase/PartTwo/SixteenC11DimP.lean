module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11DimS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16c11_inf_cTilde_eq_inf_centralizer_of_ti {M V₀ V W : Subgroup G}
    (hV : IsElemAbelian 2 V) (hM : M ≤ normalizer (V : Set G))
    (hM₀ : M ≤ normalizer (V₀ : Set G)) (hWM : W ≤ M)
    (hVW : V ≤ normalizer (W : Set G)) (hTI : V₀ ⊓ W = ⊥) :
    W ⊓ F11.CTilde M V₀ V = W ⊓ centralizer (V : Set G) := by
  ext w
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨hwW, hwC⟩
    obtain ⟨-, hws, hw1⟩ := (mem_cTilde_iff (M := M) (V₀ := V₀) (V := V) hV hM).1 hwC
    refine ⟨hwW, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hx0 : w * v * w⁻¹ * v⁻¹ ∈ V₀ :=
      (actTil_eq_one_iff V₀ V hV ⟨w, hws⟩).1 hw1 v hv
    have hxW : w * v * w⁻¹ * v⁻¹ ∈ W := by
      have hmem : v * w⁻¹ * v⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.1 (hVW hv) w⁻¹).1 (W.inv_mem hwW)
      have e : w * v * w⁻¹ * v⁻¹ = w * (v * w⁻¹ * v⁻¹) := by group
      rw [e]
      exact W.mul_mem hwW hmem
    have hx1 : w * v * w⁻¹ * v⁻¹ = 1 := by
      have hbot : w * v * w⁻¹ * v⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← hTI]
        exact ⟨hx0, hxW⟩
      exact Subgroup.mem_bot.1 hbot
    have hx1' : v * w * v⁻¹ * w⁻¹ = 1 := by
      have e : v * w * v⁻¹ * w⁻¹ = (w * v * w⁻¹ * v⁻¹)⁻¹ := by group
      rw [e, hx1, inv_one]
    refine mul_inv_eq_one.1 ?_
    have e : v * w * (w * v)⁻¹ = v * w * v⁻¹ * w⁻¹ := by group
    rw [e]
    exact hx1'
  · rintro ⟨hwW, hwcent⟩
    refine ⟨hwW, ?_⟩
    rw [mem_cTilde_iff (M := M) (V₀ := V₀) (V := V) hV hM]
    have hwM : w ∈ M := hWM hwW
    have hws : w ∈ stabTil V₀ V := le_stabTil hM hM₀ hwM
    refine ⟨hwM, hws, ?_⟩
    rw [actTil_eq_one_iff V₀ V hV ⟨w, hws⟩]
    intro v hv
    have hcomm : v * w = w * v := Subgroup.mem_centralizer_iff.1 hwcent v hv
    have e : w * v * w⁻¹ * v⁻¹ = 1 := by
      rw [← hcomm]
      group
    rw [e]
    exact V₀.one_mem

theorem s16c11_rkIdx_fixV_barSub_le_mQuot_inf_centralizer {V₀ V A : Subgroup G}
    (hV : IsElemAbelian 2 V) (hA : A ≤ stabTil V₀ V) :
    rkIdx (fixV (barSub V₀ V hV A)) ≤ E3.mQuot V (V ⊓ centralizer (A : Set G)) := by
  rw [← mQuot_preCTilde V₀ V A hV]
  refine E3.mQuot_mono (U := V ⊓ centralizer (A : Set G))
    (U' := preCTilde V₀ V A hV) fun u hu => ?_
  rw [Subgroup.mem_inf] at hu
  rw [mem_preCTilde_iff hV hA hu.1]
  intro d hd
  have hcomm : d * u = u * d := Subgroup.mem_centralizer_iff.1 hu.2 d hd
  have h1 : ⁅u, d⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hcomm.symm
  rw [h1]
  exact V₀.one_mem

@[expose] noncomputable def vtilConj (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (g : G) :
    Vtil V₀ V hV ≃*
      Vtil (conjSubgroup V₀ g) (conjSubgroup V g) (E3.isElemAbelian_conjSubgroup hV g) :=
  QuotientGroup.congr (modNull V₀ V hV)
    (modNull (conjSubgroup V₀ g) (conjSubgroup V g) (E3.isElemAbelian_conjSubgroup hV g))
    (E3.conjMod hV g (E3.isElemAbelian_conjSubgroup hV g)) (by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [mem_modNull] at hy ⊢
        show g⁻¹ * y.val * g ∈ conjSubgroup V₀ g
        rw [mem_conjSubgroup_iff]
        have e : g * (g⁻¹ * y.val * g) * g⁻¹ = y.val := by group
        rw [e]
        exact hy
      · intro hx
        rw [mem_modNull] at hx
        refine ⟨(E3.conjMod hV g (E3.isElemAbelian_conjSubgroup hV g)).symm x, ?_,
          MulEquiv.apply_symm_apply _ _⟩
        rw [mem_modNull]
        exact mem_conjSubgroup_iff.1 hx)

private theorem s16c11_dimp_vtilConj_mk (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (g : G)
    (x : IntMod V hV) :
    vtilConj V₀ V hV g (mkTil V₀ V hV x) =
      mkTil (conjSubgroup V₀ g) (conjSubgroup V g) (E3.isElemAbelian_conjSubgroup hV g)
        (E3.conjMod hV g (E3.isElemAbelian_conjSubgroup hV g) x) :=
  rfl

private theorem s16c11_dimp_mem_stabTil_conj {V₀ V : Subgroup G} (g y : G) :
    y ∈ stabTil (conjSubgroup V₀ g) (conjSubgroup V g) ↔ g * y * g⁻¹ ∈ stabTil V₀ V := by
  rw [stabTil, stabTil, Subgroup.mem_inf, Subgroup.mem_inf, ← E3.conjSubgroup_normalizer V g,
    ← E3.conjSubgroup_normalizer V₀ g, mem_conjSubgroup_iff, mem_conjSubgroup_iff]

private theorem s16c11_dimp_conjMod_actStab (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (g : G)
    {x y : G} (hx : x ∈ stabTil V₀ V)
    (hy : y ∈ stabTil (conjSubgroup V₀ g) (conjSubgroup V g)) (h : y = g⁻¹ * x * g)
    (w : IntMod V hV) :
    E3.conjMod hV g (E3.isElemAbelian_conjSubgroup hV g) (actStab V₀ V hV ⟨x, hx⟩ w) =
      actStab (conjSubgroup V₀ g) (conjSubgroup V g) (E3.isElemAbelian_conjSubgroup hV g)
        ⟨y, hy⟩ (E3.conjMod hV g (E3.isElemAbelian_conjSubgroup hV g) w) := by
  subst h
  refine IntMod.val_injective ?_
  show g⁻¹ * (actStab V₀ V hV ⟨x, hx⟩ w).val * g =
    (actStab (conjSubgroup V₀ g) (conjSubgroup V g) (E3.isElemAbelian_conjSubgroup hV g)
      ⟨g⁻¹ * x * g, hy⟩ (E3.conjMod hV g (E3.isElemAbelian_conjSubgroup hV g) w)).val
  simp only [actStab_apply_val]
  show g⁻¹ * (x * w.val * x⁻¹) * g =
    (g⁻¹ * x * g) * (g⁻¹ * w.val * g) * (g⁻¹ * x * g)⁻¹
  group

private theorem s16c11_dimp_actTil_conj (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (g : G)
    {x y : G} (hx : x ∈ stabTil V₀ V)
    (hy : y ∈ stabTil (conjSubgroup V₀ g) (conjSubgroup V g)) (h : y = g⁻¹ * x * g) :
    actTil (conjSubgroup V₀ g) (conjSubgroup V g) (E3.isElemAbelian_conjSubgroup hV g) ⟨y, hy⟩ =
      MulAut.congr (vtilConj V₀ V hV g) (actTil V₀ V hV ⟨x, hx⟩) := by
  refine MulEquiv.ext fun q => ?_
  obtain ⟨p, rfl⟩ := (vtilConj V₀ V hV g).surjective q
  obtain ⟨w, rfl⟩ := mkTil_surjective V₀ V hV p
  have hcongr : MulAut.congr (vtilConj V₀ V hV g) (actTil V₀ V hV ⟨x, hx⟩)
      (vtilConj V₀ V hV g (mkTil V₀ V hV w)) =
      vtilConj V₀ V hV g (actTil V₀ V hV ⟨x, hx⟩ (mkTil V₀ V hV w)) := by
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hcongr, s16c11_dimp_vtilConj_mk]
  simp only [actTil_mk]
  rw [s16c11_dimp_vtilConj_mk,
    s16c11_dimp_conjMod_actStab V₀ V hV g hx hy h w]

theorem s16c11_barSub_conj_eq_map {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (g : G)
    (X : Subgroup G) :
    barSub (conjSubgroup V₀ g) (conjSubgroup V g) (E3.isElemAbelian_conjSubgroup hV g)
        (conjSubgroup X g) =
      (barSub V₀ V hV X).map (MulAut.congr (vtilConj V₀ V hV g)).toMonoidHom := by
  ext θ
  rw [Subgroup.mem_map]
  constructor
  · intro hθ
    obtain ⟨y, hyX, hyact⟩ :=
      (mem_barSub (conjSubgroup V₀ g) (conjSubgroup V g)
        (E3.isElemAbelian_conjSubgroup hV g) (conjSubgroup X g) θ).1 hθ
    have hyG : g * (y : G) * g⁻¹ ∈ X := mem_conjSubgroup_iff.1 hyX
    have hxstab : g * (y : G) * g⁻¹ ∈ stabTil V₀ V :=
      (s16c11_dimp_mem_stabTil_conj (V₀ := V₀) (V := V) g (y : G)).1 y.2
    refine ⟨actTil V₀ V hV ⟨g * (y : G) * g⁻¹, hxstab⟩, ?_, ?_⟩
    · exact (mem_barSub V₀ V hV X _).2
        ⟨⟨g * (y : G) * g⁻¹, hxstab⟩, hyG, rfl⟩
    · have hconj := s16c11_dimp_actTil_conj V₀ V hV g hxstab y.2 (by group)
      exact hconj.symm.trans hyact
  · rintro ⟨η, hη, rfl⟩
    obtain ⟨x, hxX, hxact⟩ := (mem_barSub V₀ V hV X η).1 hη
    have hystab : g⁻¹ * (x : G) * g ∈ stabTil (conjSubgroup V₀ g) (conjSubgroup V g) :=
      (s16c11_dimp_mem_stabTil_conj (V₀ := V₀) (V := V) g (g⁻¹ * (x : G) * g)).2 (by
        rw [show g * (g⁻¹ * (x : G) * g) * g⁻¹ = (x : G) by group]
        exact x.2)
    have hyX : g⁻¹ * (x : G) * g ∈ conjSubgroup X g := by
      rw [mem_conjSubgroup_iff]
      rw [show g * (g⁻¹ * (x : G) * g) * g⁻¹ = (x : G) by group]
      exact hxX
    have hconj := s16c11_dimp_actTil_conj V₀ V hV g x.2 hystab rfl
    have hconj' : actTil (conjSubgroup V₀ g) (conjSubgroup V g)
        (E3.isElemAbelian_conjSubgroup hV g) ⟨g⁻¹ * (x : G) * g, hystab⟩ =
        MulAut.congr (vtilConj V₀ V hV g) η := by
      rw [hconj]
      exact congrArg (MulAut.congr (vtilConj V₀ V hV g)) hxact
    exact (mem_barSub (conjSubgroup V₀ g) (conjSubgroup V g)
      (E3.isElemAbelian_conjSubgroup hV g) (conjSubgroup X g) _).2
      ⟨⟨g⁻¹ * (x : G) * g, hystab⟩, hyX, hconj'⟩

theorem s16c11_pRank_Mbar_conj {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (g : G) :
    CFSG.Open.pRank 2 (Mbar (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g)
        (E3.isElemAbelian_conjSubgroup hV g)) = CFSG.Open.pRank 2 (Mbar M V₀ V hV) := by
  unfold Mbar
  rw [s16c11_barSub_conj_eq_map hV g M]
  exact E3.pRank_map_mulEquiv' (MulAut.congr (vtilConj V₀ V hV g)) Nat.prime_two _

theorem s16c11_barSub_conj_ne_bot {M V₀ V : Subgroup G} {g : G} (hV : IsElemAbelian 2 V)
    (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G))
    (hAM : conjSubgroup V g ≤ M) (hVMg : V ≤ conjSubgroup M g)
    (hTI : V₀ ⊓ conjSubgroup V g = ⊥ ∧ V ⊓ conjSubgroup V₀ g = ⊥)
    (hA1 : barSub V₀ V hV (conjSubgroup V g) ≠ ⊥) :
    barSub (conjSubgroup V₀ g) (conjSubgroup V g) (E3.isElemAbelian_conjSubgroup hV g) V ≠ ⊥ := by
  intro hbot
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hMg : conjSubgroup M g ≤ normalizer (conjSubgroup V g : Set G) := by
    rw [← E3.conjSubgroup_normalizer V g]
    exact E3.conjSubgroup_mono_left g hM
  have hM₀g : conjSubgroup M g ≤ normalizer (conjSubgroup V₀ g : Set G) := by
    rw [← E3.conjSubgroup_normalizer V₀ g]
    exact E3.conjSubgroup_mono_left g hM₀
  have hVgN : conjSubgroup V g ≤ normalizer (V : Set G) := hAM.trans hM
  have hVnVg : V ≤ normalizer (conjSubgroup V g : Set G) := hVMg.trans hMg
  have hTI' : conjSubgroup V₀ g ⊓ V = ⊥ := by rw [inf_comm]; exact hTI.2
  have hVCT : V ≤ F11.CTilde (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) :=
    (barSub_eq_bot_iff hVg hMg hM₀g hVMg).1 hbot
  have hEq : V ⊓ F11.CTilde (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) =
      V ⊓ centralizer (conjSubgroup V g : Set G) :=
    s16c11_inf_cTilde_eq_inf_centralizer_of_ti (M := conjSubgroup M g)
      (V₀ := conjSubgroup V₀ g) (V := conjSubgroup V g) (W := V) hVg hMg hM₀g hVMg hVgN hTI'
  have hVcent : V ≤ centralizer (conjSubgroup V g : Set G) := by
    have hle : V ≤ V ⊓ F11.CTilde (conjSubgroup M g) (conjSubgroup V₀ g)
        (conjSubgroup V g) := le_inf le_rfl hVCT
    rw [hEq] at hle
    exact (le_inf_iff.1 hle).2
  have hVgcent : conjSubgroup V g ≤ centralizer (V : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (Subgroup.mem_centralizer_iff.1 (hVcent hv) a ha).symm
  have hVgCT : conjSubgroup V g ≤ F11.CTilde M V₀ V := by
    have hEq2 : conjSubgroup V g ⊓ F11.CTilde M V₀ V =
        conjSubgroup V g ⊓ centralizer (V : Set G) :=
      s16c11_inf_cTilde_eq_inf_centralizer_of_ti (M := M) (V₀ := V₀) (V := V)
        (W := conjSubgroup V g) hV hM hM₀ hAM hVnVg hTI.1
    have hle : conjSubgroup V g ≤ conjSubgroup V g ⊓ centralizer (V : Set G) :=
      le_inf le_rfl hVgcent
    rw [← hEq2] at hle
    exact (le_inf_iff.1 hle).2
  exact hA1 ((barSub_eq_bot_iff hV hM hM₀ hAM).2 hVgCT)

theorem s16c11_mBar_le_rk_barSub_of_ti {M V₀ V : Subgroup G} {g : G} (hV : IsElemAbelian 2 V)
    (hV₀V : V₀ ≤ V) (hM : M ≤ normalizer (V : Set G)) (hM₀ : M ≤ normalizer (V₀ : Set G))
    (hAM : conjSubgroup V g ≤ M) (hVMg : V ≤ conjSubgroup M g)
    (hTI : V₀ ⊓ conjSubgroup V g = ⊥ ∧ V ⊓ conjSubgroup V₀ g = ⊥)
    (hA1 : barSub V₀ V hV (conjSubgroup V g) ≠ ⊥) :
    mBar M V₀ V hV ≤ rk ↥(barSub V₀ V hV (conjSubgroup V g)) := by
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hMg : conjSubgroup M g ≤ normalizer (conjSubgroup V g : Set G) := by
    rw [← E3.conjSubgroup_normalizer V g]
    exact E3.conjSubgroup_mono_left g hM
  have hM₀g : conjSubgroup M g ≤ normalizer (conjSubgroup V₀ g : Set G) := by
    rw [← E3.conjSubgroup_normalizer V₀ g]
    exact E3.conjSubgroup_mono_left g hM₀
  have hVgN : conjSubgroup V g ≤ normalizer (V : Set G) := hAM.trans hM
  have hA1' : barSub (conjSubgroup V₀ g) (conjSubgroup V g) hVg V ≠ ⊥ :=
    s16c11_barSub_conj_ne_bot hV hM hM₀ hAM hVMg hTI hA1
  have hstep1 : mBar M V₀ V hV =
      mBar (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) hVg :=
    (mBar_conj M V₀ V hV hV₀V hM hM₀ g).symm
  have hstep2 : mBar (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) hVg ≤
      rkIdx (fixV (barSub (conjSubgroup V₀ g) (conjSubgroup V g) hVg V)) := by
    unfold mBar Mbar
    exact E3.mParam_le_rkIdx_fixV (barSub_mono (conjSubgroup V₀ g) (conjSubgroup V g) hVg hVMg)
      (E3.isPGroup_of_isElemAbelian2 (isElemAbelian2_barSub hVg hV)) hA1'
  have hstep3 : rkIdx (fixV (barSub (conjSubgroup V₀ g) (conjSubgroup V g) hVg V)) ≤
      E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer (V : Set G)) :=
    s16c11_rkIdx_fixV_barSub_le_mQuot_inf_centralizer (V₀ := conjSubgroup V₀ g)
      (V := conjSubgroup V g) (A := V) hVg (hVMg.trans (le_stabTil hMg hM₀g))
  have hstep4 : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer (V : Set G)) =
      rk ↥(barSub V₀ V hV (conjSubgroup V g)) := by
    rw [rk_barSub_eq_mQuot_inf_cTilde hV hM hM₀ hAM,
      s16c11_inf_cTilde_eq_inf_centralizer_of_ti (M := M) (V₀ := V₀) (V := V)
        (W := conjSubgroup V g) hV hM hM₀ hAM (hVMg.trans hMg) hTI.1]
  rw [hstep1]
  exact hstep2.trans (hstep3.trans (le_of_eq hstep4))

theorem s16c11_rkIdx_fixV_barSub_le_pRank_of_ti {M V₀ V : Subgroup G} {g : G}
    (hV : IsElemAbelian 2 V) (hM : M ≤ normalizer (V : Set G))
    (hM₀ : M ≤ normalizer (V₀ : Set G)) (hAM : conjSubgroup V g ≤ M)
    (hVMg : V ≤ conjSubgroup M g)
    (hTI : V₀ ⊓ conjSubgroup V g = ⊥ ∧ V ⊓ conjSubgroup V₀ g = ⊥) :
    rkIdx (fixV (barSub V₀ V hV (conjSubgroup V g))) ≤
      CFSG.Open.pRank 2 (Mbar M V₀ V hV) := by
  have hVg : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hMg : conjSubgroup M g ≤ normalizer (conjSubgroup V g : Set G) := by
    rw [← E3.conjSubgroup_normalizer V g]
    exact E3.conjSubgroup_mono_left g hM
  have hM₀g : conjSubgroup M g ≤ normalizer (conjSubgroup V₀ g : Set G) := by
    rw [← E3.conjSubgroup_normalizer V₀ g]
    exact E3.conjSubgroup_mono_left g hM₀
  have hVgN : conjSubgroup V g ≤ normalizer (V : Set G) := hAM.trans hM
  have hTI' : conjSubgroup V₀ g ⊓ V = ⊥ := by rw [inf_comm]; exact hTI.2
  have hstep1 : rkIdx (fixV (barSub V₀ V hV (conjSubgroup V g))) ≤
      E3.mQuot V (V ⊓ centralizer (conjSubgroup V g : Set G)) :=
    s16c11_rkIdx_fixV_barSub_le_mQuot_inf_centralizer (V₀ := V₀) (V := V)
      (A := conjSubgroup V g) hV (hAM.trans (le_stabTil hM hM₀))
  have hstep2 : E3.mQuot V (V ⊓ centralizer (conjSubgroup V g : Set G)) =
      rk ↥(barSub (conjSubgroup V₀ g) (conjSubgroup V g) hVg V) := by
    rw [rk_barSub_eq_mQuot_inf_cTilde hVg hMg hM₀g hVMg,
      s16c11_inf_cTilde_eq_inf_centralizer_of_ti (M := conjSubgroup M g)
        (V₀ := conjSubgroup V₀ g) (V := conjSubgroup V g) (W := V) hVg hMg hM₀g hVMg hVgN hTI']
  have hstep3 : rk ↥(barSub (conjSubgroup V₀ g) (conjSubgroup V g) hVg V) ≤
      CFSG.Open.pRank 2 (Mbar (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) hVg) :=
    s16c11_rk_barSub_le_pRank hVg hVMg hV
  have hstep4 : CFSG.Open.pRank 2 (Mbar (conjSubgroup M g) (conjSubgroup V₀ g)
      (conjSubgroup V g) hVg) = CFSG.Open.pRank 2 (Mbar M V₀ V hV) :=
    s16c11_pRank_Mbar_conj hV g
  calc rkIdx (fixV (barSub V₀ V hV (conjSubgroup V g)))
      ≤ E3.mQuot V (V ⊓ centralizer (conjSubgroup V g : Set G)) := hstep1
    _ = rk ↥(barSub (conjSubgroup V₀ g) (conjSubgroup V g) hVg V) := hstep2
    _ ≤ CFSG.Open.pRank 2 (Mbar (conjSubgroup M g) (conjSubgroup V₀ g)
          (conjSubgroup V g) hVg) := hstep3
    _ = CFSG.Open.pRank 2 (Mbar M V₀ V hV) := hstep4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
