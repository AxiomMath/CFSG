module

public import CFSG.Quasithin.Vol2.Ch9Sec4Pts
public import CFSG.Quasithin.Background.A3Structure318Transfer

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem conj_lPt [Finite G] {m : G} (hm : m ∈ Subgroup.normalizer (fsuL0 T L : Set G))
    (W : Subgroup G) :
    (lPt T L W).map (MulAut.conj m).toMonoidHom =
      lPt T L (W.map (MulAut.conj m).toMonoidHom) := by
  have hinj : Function.Injective (MulAut.conj m).toMonoidHom := (MulAut.conj m).injective
  rw [lPt, lPt, ← oTwoUpper_map, Subgroup.map_inf_eq _ _ _ hinj]
  congr 1
  have h1 : (fsuL0 T L).map (MulAut.conj m).toMonoidHom = fsuL0 T L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hm
  have hmem : ∀ (X : Subgroup G) (h : G),
      h ∈ X.map (MulAut.conj m).toMonoidHom ↔ m⁻¹ * h * m ∈ X := by
    intro X h
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [mul_assoc] using hw
    · intro hh
      exact ⟨_, hh, by simp [mul_assoc]⟩
  have h2 : (Subgroup.normalizer (W : Set G)).map (MulAut.conj m).toMonoidHom =
      Subgroup.normalizer ((W.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) := by
    ext x
    rw [hmem, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro hy h
      rw [hmem, hmem, hy]
      constructor <;> intro hh <;> simpa [mul_assoc] using hh
    · intro hx h
      have := hx (m * h * m⁻¹)
      rw [hmem, hmem] at this
      constructor
      · intro hh
        have h' := this.mp (by simpa [mul_assoc] using hh)
        simpa [mul_assoc] using h'
      · intro hh
        exact (by simpa [mul_assoc] using this.mpr (by simpa [mul_assoc] using hh))
  rw [h1, h2]

namespace Setup

variable (S : Setup T L I n)
include S

theorem perfect_L0 (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) :
    ⁅fsuL0 T L, fsuL0 T L⁆ = fsuL0 T L := by
  obtain ⟨t, ht, htn⟩ := S.exists_not_mem_normalizer
  have hL := Vol2.Ch10.SecA.perfect_L S.hyp.fsu.maximal.1
  have hLt : ⁅CFSG.conjugate L t, CFSG.conjugate L t⁆ = CFSG.conjugate L t := by
    rw [Vol2.Ch10.SecA.conjugate_eq_map, ← Subgroup.map_commutator, hL]
  rw [Vol2.Ch10.SecA.fsuL0_eq_sup_of_fsu h37c h38c S.hyp.fsu S.not_le_normalizer_L ht htn]
  refine le_antisymm ((Subgroup.commutator_le).mpr fun a ha b hb => ?_) (sup_le ?_ ?_)
  · rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  · calc L = ⁅L, L⁆ := hL.symm
      _ ≤ _ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc CFSG.conjugate L t = ⁅CFSG.conjugate L t, CFSG.conjugate L t⁆ := hLt.symm
      _ ≤ _ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem e_conj_M {K : Type} [Field K] (e : ↥(fsuV T I) ≃* Om4.VM K) {m : G} (hm : m ∈ fsuM T L)
    (v : ↥(fsuV T I)) (h : m * v * m⁻¹ ∈ fsuV T I) :
    e ⟨m * v * m⁻¹, h⟩ = bar e ⟨m, S.hMN hm⟩ (e v) := by
  rw [bar_apply]

end Setup

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

variable {X₀ : Matrix (Fin 2) (Fin 2) K}

omit [Fintype K] [CharP K 2] hc in
theorem map_conj_inV_line {m : G} (hm : m ∈ fsuM T L) {σ : K ≃+* K}
    (hσ : ∀ (d : K) (Y : Matrix (Fin 2) (Fin 2) K),
      Multiplicative.toAdd (bar e ⟨m, S.hMN hm⟩ (Multiplicative.ofAdd (d • Y))) =
        σ d • Multiplicative.toAdd (bar e ⟨m, S.hMN hm⟩ (Multiplicative.ofAdd Y)))
    (X₀ : Matrix (Fin 2) (Fin 2) K) :
    (inV e (Om4Pt.lineM X₀)).map (MulAut.conj m).toMonoidHom =
      inV e (Om4Pt.lineM (Multiplicative.toAdd
        (bar e ⟨m, S.hMN hm⟩ (Multiplicative.ofAdd X₀)))) := by
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hwV, d, hd⟩ := mem_inV.mp hw
    have hu : m * w * m⁻¹ ∈ fsuV T I := (Subgroup.mem_normalizer_iff.mp (S.hMN hm) w).mp hwV
    refine mem_inV.mpr ⟨hu, σ d, ?_⟩
    have hew : e ⟨w, hwV⟩ = Multiplicative.ofAdd (d • X₀) := by rw [← hd]; rfl
    show Multiplicative.toAdd (e ⟨m * w * m⁻¹, hu⟩) = _
    rw [S.e_conj_M e hm ⟨w, hwV⟩ hu, hew, hσ]
  · intro hu
    obtain ⟨huV, d, hd⟩ := mem_inV.mp hu
    have hw : m⁻¹ * u * m⁻¹⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.mp (S.hMN ((fsuM T L).inv_mem hm)) u).mp huV
    refine ⟨m⁻¹ * u * m⁻¹⁻¹, mem_inV.mpr ⟨hw, σ.symm d, ?_⟩, by simp [mul_assoc]⟩
    have h1 : m * (m⁻¹ * u * m⁻¹⁻¹) * m⁻¹ ∈ fsuV T I := by simpa [mul_assoc] using huV
    have h2 := S.e_conj_M e hm ⟨_, hw⟩ h1
    have h3 : e ⟨m * (m⁻¹ * u * m⁻¹⁻¹) * m⁻¹, h1⟩ = e ⟨u, huV⟩ := by
      congr 1
      exact Subtype.ext (by group)
    rw [h3] at h2
    have h4 : bar e ⟨m, S.hMN hm⟩ (Multiplicative.ofAdd (σ.symm d • X₀)) = e ⟨u, huV⟩ := by
      apply Multiplicative.toAdd.injective
      rw [hσ, RingEquiv.apply_symm_apply, hd]
    have h5 : e ⟨_, hw⟩ = Multiplicative.ofAdd (σ.symm d • X₀) :=
      (bar e ⟨m, S.hMN hm⟩).injective (by rw [← h2, h4])
    rw [h5, toAdd_ofAdd]

theorem exists_conj_inV_line (hX : X₀.det ≠ 0) {m : G} (hm : m ∈ fsuM T L) :
    ∃ X₁ : Matrix (Fin 2) (Fin 2) K, X₁.det ≠ 0 ∧
      Multiplicative.toAdd (bar e ⟨m, S.hMN hm⟩ (Multiplicative.ofAdd X₀)) = X₁ ∧
      (inV e (Om4Pt.lineM X₀)).map (MulAut.conj m).toMonoidHom = inV e (Om4Pt.lineM X₁) := by
  obtain ⟨A, B, τ, hform | hform⟩ := hc.exists_form hm
  · refine ⟨_, ?_, rfl, map_conj_inV_line (S := S) hm (σ := τ) (fun d Y => by
      rw [hform]; exact Om4Pt.toAdd_lr_frM_smul A B τ d Y) X₀⟩
    rw [hform]
    exact Om4Pt.det_lr_frM_ne_zero A B τ hX
  · refine ⟨_, ?_, rfl, map_conj_inV_line (S := S) hm (σ := τ) (fun d Y => by
      rw [hform]; exact Om4Pt.toAdd_lr_frM_trM_smul A B τ d Y) X₀⟩
    rw [hform]
    exact Om4Pt.det_lr_frM_trM_ne_zero A B τ hX

omit [Finite G] [Fintype K] [CharP K 2] hc in
theorem symm_mem_inV_line (X₀ : Matrix (Fin 2) (Fin 2) K) :
    ((e.symm (Multiplicative.ofAdd X₀) : ↥(fsuV T I)) : G) ∈ inV e (Om4Pt.lineM X₀) :=
  mem_inV.mpr ⟨(e.symm _).2, by
    show e (e.symm (Multiplicative.ofAdd X₀)) ∈ _
    rw [MulEquiv.apply_symm_apply]
    exact ⟨1, by rw [toAdd_ofAdd, one_smul]⟩⟩

omit [Finite G] [Fintype K] [CharP K 2] hc in
theorem symm_ne_one {X₀ : Matrix (Fin 2) (Fin 2) K} (hX : X₀ ≠ 0) :
    ((e.symm (Multiplicative.ofAdd X₀) : ↥(fsuV T I)) : G) ≠ 1 := by
  intro h
  apply hX
  have h1 : e.symm (Multiplicative.ofAdd X₀) = 1 := Subtype.ext h
  have h2 : Multiplicative.ofAdd X₀ = 1 := by
    rw [← MulEquiv.apply_symm_apply e (Multiplicative.ofAdd X₀), h1, map_one]
  exact Multiplicative.ofAdd.injective (h2.trans ofAdd_zero.symm)

theorem sup_lPt_eq (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (hK4 : Fintype.card K = 4)
    {X₁ : Matrix (Fin 2) (Fin 2) K} (hX₀ : X₀.det ≠ 0) (hX₁ : X₁.det ≠ 0)
    (hne : ∀ c : K, X₁ ≠ c • X₀) :
    lPt T L (inV e (Om4Pt.lineM X₀)) ⊔ lPt T L (inV e (Om4Pt.lineM X₁)) = fsuL0 T L := by
  have h4 : 4 ≤ Nat.card K := by rw [Nat.card_eq_fintype_card, hK4]
  set H := lPt T L (inV e (Om4Pt.lineM X₀)) ⊔ lPt T L (inV e (Om4Pt.lineM X₁)) with hHdef
  have hHL : H ≤ fsuL0 T L := sup_le (lPt_le_L0 T L _) (lPt_le_L0 T L _)
  set H' := H.subgroupOf (fsuL0 T L) with hH'def
  have hmap : H'.map ψ = ⊤ := by
    rw [eq_top_iff, ← Om4Pt.dgM_sup_dgM_eq_top h4 hX₀ hX₁ hne, ← hc.map_lPt hK4 hX₀,
      ← hc.map_lPt hK4 hX₁, ← Subgroup.map_sup]
    exact Subgroup.map_mono (sup_le
      (fun x hx => Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)))
      (fun x hx => Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx))))
  have hker : ψ.ker ≤ Subgroup.normalizer (H' : Set ↥(fsuL0 T L)) := by
    intro k hk
    have hkM : (k : G) ∈ fsuM T L := Setup.L0_le_fsuM k.2
    have hkV := (hc.mem_Q_of_psi_eq_one h37c h38c k hk).2
    have hfix : ∀ X : Matrix (Fin 2) (Fin 2) K, X ≠ 0 →
        (k : G) ∈ Subgroup.normalizer (lPt T L (inV e (Om4Pt.lineM X)) : Set G) := by
      intro X hX0
      refine hc.mem_normalizer_lPt hkM (symm_mem_inV_line (e := e) X)
        (symm_ne_one (e := e) hX0) ?_
      have := Subgroup.mem_centralizer_iff.mp hkV _ (e.symm (Multiplicative.ofAdd X)).2
      rw [← this, mul_inv_cancel_right]
    have hX₀0 : X₀ ≠ 0 := fun h => hX₀ (by rw [h, Matrix.det_zero])
    have hX₁0 : X₁ ≠ 0 := fun h => hX₁ (by rw [h, Matrix.det_zero])
    have hkH : (k : G) ∈ Subgroup.normalizer (H : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at *
      have h0 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hfix X₀ hX₀0)
      have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hfix X₁ hX₁0)
      rw [hHdef, Subgroup.map_sup, h0, h1]
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hH'def, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp hkH (h : G))
  have htop : (⊤ : Subgroup ↥(fsuL0 T L)) ≤ H' ⊔ ψ.ker := by
    intro x _
    have hx : ψ x ∈ H'.map ψ := by rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨h, hh, hhx⟩ := Subgroup.mem_map.mp hx
    have e1 : x = h * (h⁻¹ * x) := by group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hhx, inv_mul_cancel]))
  have hnorm : H'.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    exact htop.trans (sup_le Subgroup.le_normalizer hker)
  have h2 : IsPGroup 2 ↥ψ.ker := by
    rintro ⟨k, hk⟩
    obtain ⟨j, hj⟩ := S.isPGroup_Q ⟨_, hc.mem_Q_of_psi_eq_one h37c h38c k hk⟩
    refine ⟨j, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hj
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable ↥ψ.ker := by
    have := h2.isNilpotent
    infer_instance
  have hperf : ⁅(⊤ : Subgroup ↥(fsuL0 T L)), (⊤ : Subgroup ↥(fsuL0 T L))⁆ = ⊤ := by
    apply Subgroup.map_injective (fsuL0 T L).subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact S.perfect_L0 h37c h38c
  have heq := A318.eq_of_le_sup_solvable hperf le_top hsolv htop
  refine le_antisymm hHL fun x hx => ?_
  have : (⟨x, hx⟩ : ↥(fsuL0 T L)) ∈ H' := by rw [← heq]; exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem mem_perp_of_fix (hX : X₀.det ≠ 0) (u : ↥(fsuL0 T L)) (hu : ψ u ∈ Om4Pt.dgM X₀)
    (hu1 : ψ u ≠ 1) (hu2 : ψ u * ψ u = 1) {v : G} (hv : v ∈ fsuV T I)
    (huv : (u : G) * v * (u : G)⁻¹ = v) : v ∈ inV e (Om4Pt.perpM X₀) := by
  refine mem_inV.mpr ⟨hv, Om4Pt.mem_perpM_of_rho_eq hX hu hu1 hu2 ?_⟩
  have huv' : (u : G) * v * (u : G)⁻¹ ∈ fsuV T I := by rw [huv]; exact hv
  rw [← hc.e_conj u ⟨v, hv⟩ huv']
  exact congrArg e (Subtype.ext huv)

theorem perp_le_closure (hK4 : Fintype.card K = 4) (hX : X₀.det ≠ 0) {z : G}
    (hz : z ∈ inV e (Om4Pt.perpM X₀)) (hzd : ∀ hzV : z ∈ fsuV T I,
      (Multiplicative.toAdd (e ⟨z, hzV⟩)).det = 0) (hz1 : z ≠ 1) :
    inV e (Om4Pt.perpM X₀) ≤ Subgroup.closure
      {y | ∃ l ∈ lPt T L (inV e (Om4Pt.lineM X₀)), y = l * z * l⁻¹} := by
  obtain ⟨hzV, hzp⟩ := mem_inV.mp hz
  have hz1' : e ⟨z, hzV⟩ ≠ 1 := by
    intro h
    exact hz1 (congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h))
  set f : Om4.VM K →* G := (fsuV T I).subtype.comp e.symm.toMonoidHom with hf
  intro y hy
  obtain ⟨hyV, hyp⟩ := mem_inV.mp hy
  have h1 := Om4Pt.mem_closure_rho hX hzp (hzd hzV) hz1' hyp
  have h2 := Subgroup.mem_map_of_mem f h1
  rw [MonoidHom.map_closure] at h2
  have hfy : f (e ⟨y, hyV⟩) = y := by simp [hf]
  rw [hfy] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨W', ⟨γ, hγ, rfl⟩, rfl⟩
  rw [← hc.map_lPt hK4 hX] at hγ
  obtain ⟨k, hk, rfl⟩ := hγ
  refine ⟨k, Subgroup.mem_subgroupOf.mp hk, ?_⟩
  have hkz : (k : G) * z * (k : G)⁻¹ ∈ fsuV T I :=
    (Subgroup.mem_normalizer_iff.mp (S.L0_le_normalizer_V k.2) z).mp hzV
  rw [← hc.e_conj k ⟨z, hzV⟩ hkz]
  simp [hf]

theorem mem_commutator_perp (hK4 : Fintype.card K = 4) (hX : X₀.det ≠ 0) {z : G}
    (hz : z ∈ inV e (Om4Pt.perpM X₀)) (hzd : ∀ hzV : z ∈ fsuV T I,
      (Multiplicative.toAdd (e ⟨z, hzV⟩)).det = 0) (hz1 : z ≠ 1) :
    z ∈ ⁅inV e (Om4Pt.perpM X₀), lPt T L (inV e (Om4Pt.lineM X₀))⁆ := by
  classical
  obtain ⟨hzV, hzp⟩ := mem_inV.mp hz
  have hz1' : e ⟨z, hzV⟩ ≠ 1 := by
    intro h
    exact hz1 (congrArg Subtype.val ((map_eq_one_iff e e.injective).mp h))
  have hU : Fintype.card Kˣ = 3 := by rw [Fintype.card_units, hK4]
  have : Nontrivial Kˣ := Fintype.one_lt_card_iff_nontrivial.mp (by rw [hU]; norm_num)
  obtain ⟨a, ha⟩ := exists_ne (1 : Kˣ)
  obtain ⟨γ, hγ, Y, hY, hzY⟩ := Om4Pt.exists_eq_rho_mul_inv hX hzp (hzd hzV) hz1' a.ne_zero
    (fun h => ha (Units.ext h))
  rw [← hc.map_lPt hK4 hX] at hγ
  obtain ⟨k, hk, rfl⟩ := hγ
  set y : ↥(fsuV T I) := e.symm Y with hydef
  have hyp : (y : G) ∈ inV e (Om4Pt.perpM X₀) :=
    mem_inV.mpr ⟨y.2, by show e y ∈ _; rw [hydef, MulEquiv.apply_symm_apply]; exact hY⟩
  have hky : (k : G) * y * (k : G)⁻¹ ∈ fsuV T I :=
    (Subgroup.mem_normalizer_iff.mp (S.L0_le_normalizer_V k.2) y).mp y.2
  have hcomm : z = (k : G) * y * (k : G)⁻¹ * (y : G)⁻¹ := by
    have h1 : e ⟨(k : G) * y * (k : G)⁻¹ * (y : G)⁻¹,
        (fsuV T I).mul_mem hky ((fsuV T I).inv_mem y.2)⟩ = e ⟨z, hzV⟩ := by
      have e1 : (⟨(k : G) * y * (k : G)⁻¹ * (y : G)⁻¹,
          (fsuV T I).mul_mem hky ((fsuV T I).inv_mem y.2)⟩ : ↥(fsuV T I)) =
          ⟨(k : G) * y * (k : G)⁻¹, hky⟩ * y⁻¹ := rfl
      rw [e1, map_mul, map_inv, hc.e_conj k y hky, hydef, MulEquiv.apply_symm_apply, ← hzY]
    exact (congrArg Subtype.val (e.injective h1)).symm
  rw [hcomm, Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hk) hyp

theorem exists_mul_mem_L0 (hX : X₀.det ≠ 0) {c : K} (hc0 : c ≠ 0) {z : G} (hzV : z ∈ fsuV T I)
    (hz : detPolarCh6 X₀ (Multiplicative.toAdd (e ⟨z, hzV⟩)) = 0)
    (hzd : (Multiplicative.toAdd (e ⟨z, hzV⟩)).det = 0) :
    ∃ g ∈ fsuL0 T L,
      g * (e.symm (Multiplicative.ofAdd (c • X₀)) : G) * g⁻¹ =
        (e.symm (Multiplicative.ofAdd (c • X₀)) : G) * z ∧
      g⁻¹ * (e.symm (Multiplicative.ofAdd (c • X₀)) : G) * g =
        (e.symm (Multiplicative.ofAdd (c • X₀)) : G) * z ∧
      (inV e (Om4Pt.lineM X₀)).map (MulAut.conj g).toMonoidHom =
        inV e (Om4Pt.lineM (X₀ + c⁻¹ • Multiplicative.toAdd (e ⟨z, hzV⟩))) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set Z := Multiplicative.toAdd (e ⟨z, hzV⟩) with hZ
  have hz' : detPolarCh6 X₀ (c⁻¹ • Z) = 0 := by
    simp only [detPolarCh6, Matrix.smul_apply, smul_eq_mul] at hz ⊢
    linear_combination c⁻¹ * hz
  have hzd' : (c⁻¹ • Z).det = 0 := by
    rw [Matrix.det_smul, hzd, mul_zero]
  obtain ⟨A, hA1, hA2⟩ := Om4Pt.exists_sl_mul_eq hX hz' hzd'
  obtain ⟨k, hk⟩ := hc.surj (A, 1)
  have hAi : ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X₀ =
      X₀ + c⁻¹ • Z := by
    have h3 : (A : Matrix (Fin 2) (Fin 2) K) * (X₀ + c⁻¹ • Z) = X₀ := by
      rw [Matrix.mul_add, hA1, hA2, add_assoc, ← two_smul K (c⁻¹ • Z), h2, zero_smul, add_zero]
    have hinv : ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        (A : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X₀
        = ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
            ((A : Matrix (Fin 2) (Fin 2) K) * (X₀ + c⁻¹ • Z)) := by rw [h3]
      _ = X₀ + c⁻¹ • Z := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
  set v : ↥(fsuV T I) := e.symm (Multiplicative.ofAdd (c • X₀)) with hvdef
  have hev : e v = Multiplicative.ofAdd (c • X₀) := by rw [hvdef, MulEquiv.apply_symm_apply]
  have hvz : e (v * ⟨z, hzV⟩) = Multiplicative.ofAdd (c • X₀ + Z) := by
    rw [map_mul, hev]
    rfl
  refine ⟨k, k.2, ?_, ?_, ?_⟩
  · have hkv : (k : G) * v * (k : G)⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.mp (S.L0_le_normalizer_V k.2) v).mp v.2
    have h1 : e ⟨(k : G) * v * (k : G)⁻¹, hkv⟩ = e (v * ⟨z, hzV⟩) := by
      rw [hc.e_conj k v hkv, hk, hvz, hev]
      apply Multiplicative.toAdd.injective
      rw [toAdd_rho, toAdd_ofAdd, toAdd_ofAdd]
      simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one,
        Matrix.mul_smul, hA1, smul_add, smul_smul, mul_inv_cancel₀ hc0, one_smul]
    exact congrArg Subtype.val (e.injective h1)
  · have hkv : (k⁻¹ : G) * v * (k⁻¹ : G)⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.mp (S.L0_le_normalizer_V k⁻¹.2) v).mp v.2
    have h1 : e ⟨(k⁻¹ : G) * v * (k⁻¹ : G)⁻¹, hkv⟩ = e (v * ⟨z, hzV⟩) := by
      have := hc.e_conj k⁻¹ v hkv
      simp only [Subgroup.coe_inv] at this
      rw [this, map_inv, hk, hvz, hev]
      apply Multiplicative.toAdd.injective
      rw [toAdd_rho, toAdd_ofAdd, toAdd_ofAdd]
      simp only [Prod.inv_mk, inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one,
        Matrix.mul_one, Matrix.mul_smul, hAi, smul_add, smul_smul, mul_inv_cancel₀ hc0,
        one_smul]
    have h3 := congrArg Subtype.val (e.injective h1)
    simpa using h3
  · have hkM : (k : G) ∈ fsuM T L := Setup.L0_le_fsuM k.2
    have hbar : bar e ⟨k, S.hMN hkM⟩ = Om4.rho (A, 1) := by
      rw [← hk, ← hc.bar_L0 k]
      rfl
    have hσ : ∀ (d : K) (Y : Matrix (Fin 2) (Fin 2) K),
        Multiplicative.toAdd (bar e ⟨k, S.hMN hkM⟩ (Multiplicative.ofAdd (d • Y))) =
          (RingEquiv.refl K) d • Multiplicative.toAdd (bar e ⟨k, S.hMN hkM⟩
            (Multiplicative.ofAdd Y)) := by
      intro d Y
      rw [hbar, toAdd_rho, toAdd_rho, toAdd_ofAdd, toAdd_ofAdd, Matrix.mul_smul, Matrix.smul_mul]
      rfl
    rw [map_conj_inV_line (S := S) hkM hσ X₀, hbar, toAdd_rho, toAdd_ofAdd]
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one, hA1]

omit [Finite G] [Fintype K] hc in
theorem inV_line_le_perp : inV e (Om4Pt.lineM X₀) ≤ inV e (Om4Pt.perpM X₀) := by
  intro w hw
  obtain ⟨hwV, c, hc'⟩ := mem_inV.mp hw
  refine mem_inV.mpr ⟨hwV, ?_⟩
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [Om4Pt.mem_perpM, hc']
  simp only [detPolarCh6, Matrix.smul_apply, smul_eq_mul]
  linear_combination c * (X₀ 0 0 * X₀ 1 1 + X₀ 0 1 * X₀ 1 0) * h2

theorem V_le_normalizer_lPt (hX : X₀.det ≠ 0) :
    fsuV T I ≤ Subgroup.normalizer (lPt T L (inV e (Om4Pt.lineM X₀)) : Set G) := by
  intro x hx
  have hX0 : X₀ ≠ 0 := fun h => hX (by rw [h, Matrix.det_zero])
  have hxM : x ∈ fsuM T L := Setup.T_le_fsuM (S.fsuV_le_T hx)
  refine hc.mem_normalizer_lPt hxM (symm_mem_inV_line (e := e) X₀) (symm_ne_one (e := e) hX0) ?_
  have hab := S.hV.1
  have : x * ((e.symm (Multiplicative.ofAdd X₀) : ↥(fsuV T I)) : G) =
      ((e.symm (Multiplicative.ofAdd X₀) : ↥(fsuV T I)) : G) * x := by
    have h := hab.is_comm.comm ⟨x, hx⟩ (e.symm (Multiplicative.ofAdd X₀))
    exact congrArg Subtype.val h
  rw [this, mul_inv_cancel_right]

theorem commutator_perp_le (hX : X₀.det ≠ 0) :
    ⁅inV e (Om4Pt.perpM X₀), lPt T L (inV e (Om4Pt.lineM X₀))⁆ ≤
      lPt T L (inV e (Om4Pt.lineM X₀)) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hab : a * b * a⁻¹ ∈ lPt T L (inV e (Om4Pt.lineM X₀)) :=
    (Subgroup.mem_normalizer_iff.mp (hc.V_le_normalizer_lPt hX (inV_le e _ ha)) b).mp hb
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ hab (Subgroup.inv_mem _ hb)

theorem lPt_le_normalizer_perp (hK4 : Fintype.card K = 4) (hX : X₀.det ≠ 0) :
    lPt T L (inV e (Om4Pt.lineM X₀)) ≤ Subgroup.normalizer (inV e (Om4Pt.perpM X₀) : Set G) := by
  have key : ∀ l ∈ lPt T L (inV e (Om4Pt.lineM X₀)), ∀ y ∈ inV e (Om4Pt.perpM X₀),
      l * y * l⁻¹ ∈ inV e (Om4Pt.perpM X₀) := by
    intro l hl y hy
    obtain ⟨hyV, hyp⟩ := mem_inV.mp hy
    have hlL : l ∈ fsuL0 T L := lPt_le_L0 T L _ hl
    have hψ : ψ ⟨l, hlL⟩ ∈ Om4Pt.dgM X₀ := by
      rw [← hc.map_lPt hK4 hX]
      exact ⟨⟨l, hlL⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    have hly : l * y * l⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.mp (S.L0_le_normalizer_V hlL) y).mp hyV
    refine mem_inV.mpr ⟨hly, ?_⟩
    rw [show (⟨l * y * l⁻¹, hly⟩ : ↥(fsuV T I)) = ⟨(⟨l, hlL⟩ : ↥(fsuL0 T L)) * y *
      ((⟨l, hlL⟩ : ↥(fsuL0 T L)) : G)⁻¹, hly⟩ from rfl, hc.e_conj ⟨l, hlL⟩ ⟨y, hyV⟩ hly]
    exact (Om4Pt.rho_mem_perpM_iff hψ _).mpr hyp
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key l hl y, fun hy => ?_⟩
  have := key l⁻¹ (Subgroup.inv_mem _ hl) _ hy
  simpa [mul_assoc] using this

theorem perp_le_commutator (hK4 : Fintype.card K = 4) (hX : X₀.det ≠ 0) :
    inV e (Om4Pt.perpM X₀) ≤ ⁅inV e (Om4Pt.perpM X₀), lPt T L (inV e (Om4Pt.lineM X₀))⁆ := by
  obtain ⟨Z, hZp, hZd, hZ0⟩ : ∃ Z : Matrix (Fin 2) (Fin 2) K, detPolarCh6 X₀ Z = 0 ∧
      Z.det = 0 ∧ Z ≠ 0 := by
    obtain ⟨Z₁, Z₂, Z₃, hsum, h1, h2', h3, d1, d2, d3⟩ := Om4Pt.exists_singular_decomp hX 1
    by_cases hZ₁ : Z₁ = 0
    · by_cases hZ₂ : Z₂ = 0
      · refine ⟨Z₃, h3, d3, fun hZ₃ => hX ?_⟩
        rw [one_smul, hZ₁, hZ₂, hZ₃, add_zero, add_zero] at hsum
        rw [hsum, Matrix.det_zero]
      · exact ⟨Z₂, h2', d2, hZ₂⟩
    · exact ⟨Z₁, h1, d1, hZ₁⟩
  set z : G := ((e.symm (Multiplicative.ofAdd Z) : ↥(fsuV T I)) : G) with hzdef
  have hzV : z ∈ fsuV T I := (e.symm _).2
  have hez : e ⟨z, hzV⟩ = Multiplicative.ofAdd Z := by
    show e (e.symm (Multiplicative.ofAdd Z)) = _
    rw [MulEquiv.apply_symm_apply]
  have hz : z ∈ inV e (Om4Pt.perpM X₀) :=
    mem_inV.mpr ⟨hzV, by rw [hez, Om4Pt.mem_perpM, toAdd_ofAdd]; exact hZp⟩
  have hzd : ∀ h : z ∈ fsuV T I, (Multiplicative.toAdd (e ⟨z, h⟩)).det = 0 := fun h => by
    rw [hez, toAdd_ofAdd]; exact hZd
  have hz1 : z ≠ 1 := symm_ne_one (e := e) hZ0
  have hzc := hc.mem_commutator_perp hK4 hX hz hzd hz1
  refine (hc.perp_le_closure hK4 hX hz hzd hz1).trans ((Subgroup.closure_le _).mpr ?_)
  rintro _ ⟨l, hl, rfl⟩
  have hlN := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hc.lPt_le_normalizer_perp hK4 hX hl)
  have hlN' := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.le_normalizer hl : l ∈ Subgroup.normalizer (lPt T L (inV e (Om4Pt.lineM X₀)) :
      Set G))
  have h1 := Subgroup.mem_map_of_mem (MulAut.conj l : G →* G) hzc
  rw [Subgroup.map_commutator, hlN, hlN'] at h1
  simpa using h1

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
