module

public import CFSG.Quasithin.Vol2.Ch9Sec4Forms
public import CFSG.Quasithin.Vol2.Ch9Sec4Sing

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H CFSG.Quasithin.E3 Matrix

namespace Om4Pt

variable {K : Type} [Field K]

theorem det_e21_sub (x y : K) :
    (Multiplicative.toAdd (Multiplicative.ofAdd !![(0 : K), 0; 1, 0] *
      (Om4.rho (uHom K (Multiplicative.ofAdd x), uHom K (Multiplicative.ofAdd y))
        (Multiplicative.ofAdd !![0, 0; 1, 0]))⁻¹)).det = 0 := by
  rw [toAdd_mul, toAdd_inv, Om4Pt.toAdd_rho_e21, toAdd_ofAdd]
  have : !![(0 : K), 0; 1, 0] + -!![x, 0; 1, 0] = !![-x, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [this, Matrix.det_fin_two_of]
  ring

theorem det_e12_sub (x y : K) :
    (Multiplicative.toAdd (Multiplicative.ofAdd !![(0 : K), 1; 0, 0] *
      (Om4.rho (uHom K (Multiplicative.ofAdd x), uHom K (Multiplicative.ofAdd y))
        (Multiplicative.ofAdd !![0, 1; 0, 0]))⁻¹)).det = 0 := by
  rw [toAdd_mul, toAdd_inv, Om4Pt.toAdd_rho_e12, toAdd_ofAdd]
  have : !![(0 : K), 1; 0, 0] + -!![y, 1; 0, 0] = !![-y, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [this, Matrix.det_fin_two_of]
  ring

end Om4Pt

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem bar_fix_of_det (hr : (3 : ℕ∞) < rParam (fsuV T I)) (h3108 : Stmt3_2_10_eight)
    (h2 : n = 2) {g : G} {A : Subgroup G} (hAV : A ≤ conjSubgroup (fsuV T I) g) (hAT : A ≤ T)
    (Y : Om4.VM K)
    (hB : 32 ≤ Nat.card ↥(A ⊓ Subgroup.centralizer ({(e.symm Y : G)} : Set G)))
    {a : G} (ha : a ∈ A)
    (hdet : (Multiplicative.toAdd (Y * (bar e ⟨a, S.hMN (Setup.T_le_fsuM (hAT ha))⟩ Y)⁻¹)).det =
      0) :
    bar e ⟨a, S.hMN (Setup.T_le_fsuM (hAT ha))⟩ Y = Y := by
  set x : ↥(Subgroup.normalizer (fsuV T I : Set G)) := ⟨a, S.hMN (Setup.T_le_fsuM (hAT ha))⟩
    with hx
  have hmem := comm_symm_mem e x Y
  have hE := e_comm_symm e x Y hmem
  have h1 := hc.comm_eq_one_of_det_eq_zero hr h3108 h2 (e.symm Y).2 (hAV ha)
    (inf_le_left.trans hAV) ((inf_le_left.trans hAT).trans Setup.T_le_fsuM) inf_le_right hB hmem
    (by rw [hE]; exact hdet)
  have h3 : (⟨(e.symm Y : G) * x * (e.symm Y : G)⁻¹ * (x : G)⁻¹, hmem⟩ : ↥(fsuV T I)) = 1 :=
    Subtype.ext h1
  rw [h3, map_one] at hE
  exact (mul_inv_eq_one.mp hE.symm).symm

theorem le_centralizer_V1 (hr : (3 : ℕ∞) < rParam (fsuV T I)) (h3108 : Stmt3_2_10_eight)
    (h2 : n = 2) {g : G} {A : Subgroup G} (hAV : A ≤ conjSubgroup (fsuV T I) g) (hAT : A ≤ T)
    (hA : 128 ≤ Nat.card A) :
    A ≤ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  classical
  set V₁ := fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) with hV₁
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  set Sset : Finset G := Finset.univ.image (fun c : K =>
    ((e.symm (Multiplicative.ofAdd (c • !![(1 : K), 0; 0, 0])) : ↥(fsuV T I)) : G)) with hSset
  have hSmem : ∀ w ∈ V₁, w ∈ Sset := by
    intro w hw
    rw [Finset.mem_image]
    refine ⟨Multiplicative.toAdd (e ⟨w, hw.1⟩) 0 0, Finset.mem_univ _, ?_⟩
    have h1 := hc.toAdd_e_eq hw
    have h3 : e ⟨w, hw.1⟩ = Multiplicative.ofAdd
        (Multiplicative.toAdd (e ⟨w, hw.1⟩) 0 0 • !![(1 : K), 0; 0, 0]) := by
      rw [← h1]
      rfl
    rw [← h3, MulEquiv.symm_apply_apply]
  have hS4 : Sset.card ≤ 4 := Finset.card_image_le.trans (by rw [Finset.card_univ, hK4])
  have hTV1 : ∀ h ∈ T, h * u * h⁻¹ ∈ V₁ := fun h hh =>
    (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_V1 hh) u).mp hu
  have hcardB := card_le_mul_card_centralizer A u Sset (fun h hh => hSmem _ (hTV1 h (hAT hh)))
  have hB : 32 ≤ Nat.card ↥(A ⊓ Subgroup.centralizer ({u} : Set G)) := by
    have := hcardB.trans (Nat.mul_le_mul_right _ hS4)
    omega
  have hx1 : u * a * u⁻¹ * a⁻¹ ∈ V₁ := by
    have e1 : u * a * u⁻¹ * a⁻¹ = u * (a * u * a⁻¹)⁻¹ := by group
    rw [e1]
    exact V₁.mul_mem hu (V₁.inv_mem (hTV1 a (hAT ha)))
  have hdet : (Multiplicative.toAdd (e ⟨u * a * u⁻¹ * a⁻¹, hx1.1⟩)).det = 0 := by
    rw [hc.toAdd_e_eq hx1, Matrix.det_smul]
    simp [Matrix.det_fin_two_of]
  have h1 := hc.comm_eq_one_of_det_eq_zero hr h3108 h2 hu.1 (hAV ha) (inf_le_left.trans hAV)
    ((inf_le_left.trans hAT).trans Setup.T_le_fsuM) inf_le_right hB hx1.1 hdet
  calc u * a = (u * a * u⁻¹ * a⁻¹) * a * u := by group
    _ = a * u := by rw [h1, one_mul]

theorem exists_swap (hr : (3 : ℕ∞) < rParam (fsuV T I)) (h3108 : Stmt3_2_10_eight) (h2 : n = 2)
    {g : G} {A : Subgroup G} (hAV : A ≤ conjSubgroup (fsuV T I) g) (hAT : A ≤ T)
    (hA : 128 ≤ Nat.card A) (hAC : ¬ A ≤ Subgroup.centralizer (fsuV T I : Set G)) :
    ∃ t : G, ∃ ht : t ∈ A, ∃ P : GL (Fin 2) K, Om4.IsUT P ∧
      bar e ⟨t, S.hMN (Setup.T_le_fsuM (hAT ht))⟩ = Om4.lr P P⁻¹ * Om4.trM := by
  classical
  by_contra hns
  push Not at hns
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  have hAV1 := hc.le_centralizer_V1 hr h3108 h2 hAV hAT hA
  have hVg := isElemAbelian_conjSubgroup S.hV g
  have hsq : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => hVg.2 a (hAV ha)
  have hlin : ∀ (a : G) (ha : a ∈ A), ∃ x y : K,
      bar e ⟨a, S.hMN (Setup.T_le_fsuM (hAT ha))⟩ =
        Om4.rho (uHom K (Multiplicative.ofAdd x), uHom K (Multiplicative.ofAdd y)) := by
    intro a ha
    rcases hc.form_of_mem_centralizer_V1 (hAT ha) (hAV1 ha) (hsq a ha) with h | ⟨P, hP, h⟩
    · exact h
    · exact absurd h (hns a ha P hP)
  have horb : ∀ (M : Matrix (Fin 2) (Fin 2) K) (F : K → Matrix (Fin 2) (Fin 2) K),
      (∀ x y : K, Multiplicative.toAdd (Om4.rho (uHom K (Multiplicative.ofAdd x),
        uHom K (Multiplicative.ofAdd y)) (Multiplicative.ofAdd M)) = F x ∨
        Multiplicative.toAdd (Om4.rho (uHom K (Multiplicative.ofAdd x),
          uHom K (Multiplicative.ofAdd y)) (Multiplicative.ofAdd M)) = F y) →
      32 ≤ Nat.card ↥(A ⊓ Subgroup.centralizer
        ({((e.symm (Multiplicative.ofAdd M)) : G)} : Set G)) := by
    intro M F hF
    set Sset : Finset G := Finset.univ.image (fun c : K =>
      ((e.symm (Multiplicative.ofAdd (F c))) : G)) with hSset
    have hS4 : Sset.card ≤ 4 := Finset.card_image_le.trans (by rw [Finset.card_univ, hK4])
    have hmem : ∀ h ∈ A, h * (e.symm (Multiplicative.ofAdd M) : G) * h⁻¹ ∈ Sset := by
      intro h hh
      obtain ⟨x, y, hxy⟩ := hlin h hh
      rw [show h * (e.symm (Multiplicative.ofAdd M) : G) * h⁻¹ =
        (e.symm (bar e ⟨h, S.hMN (Setup.T_le_fsuM (hAT hh))⟩ (Multiplicative.ofAdd M)) : G)
        from conj_symm e ⟨h, S.hMN (Setup.T_le_fsuM (hAT hh))⟩ _, hxy]
      rw [Finset.mem_image]
      rcases hF x y with h1 | h1
      · exact ⟨x, Finset.mem_univ _, by rw [← h1, ofAdd_toAdd]⟩
      · exact ⟨y, Finset.mem_univ _, by rw [← h1, ofAdd_toAdd]⟩
    have := (card_le_mul_card_centralizer A _ Sset hmem).trans (Nat.mul_le_mul_right _ hS4)
    omega
  have hB21 := horb !![0, 0; 1, 0] (fun c => !![c, 0; 1, 0])
    (fun x y => Or.inl (Om4Pt.toAdd_rho_e21 x y))
  have hB12 := horb !![0, 1; 0, 0] (fun c => !![c, 1; 0, 0])
    (fun x y => Or.inr (Om4Pt.toAdd_rho_e12 x y))
  apply hAC
  intro a ha
  obtain ⟨x, y, hxy⟩ := hlin a ha
  have h21 := hc.bar_fix_of_det hr h3108 h2 hAV hAT _ hB21 ha (by rw [hxy]; exact Om4Pt.det_e21_sub x y)
  have h12 := hc.bar_fix_of_det hr h3108 h2 hAV hAT _ hB12 ha (by rw [hxy]; exact Om4Pt.det_e12_sub x y)
  rw [hxy] at h21 h12
  have hx : x = 0 := by
    have h3 : !![x, 0; 1, 0] = !![(0 : K), 0; 1, 0] := by
      rw [← Om4Pt.toAdd_rho_e21 x y, h21, toAdd_ofAdd]
    have := congrFun (congrFun h3 0) 0
    simpa using this
  have hy : y = 0 := by
    have h3 : !![y, 1; 0, 0] = !![(0 : K), 1; 0, 0] := by
      rw [← Om4Pt.toAdd_rho_e12 x y, h12, toAdd_ofAdd]
    have := congrFun (congrFun h3 0) 0
    simpa using this
  rw [hx, hy, Om4Pt.rho_uHom_zero] at hxy
  exact mem_centralizer_of_bar e _ hxy

theorem bar_e12_of_swap {A : Subgroup G} (hAT : A ≤ T)
    (hAV1 : A ≤ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G))
    (hsq : ∀ a ∈ A, a ^ 2 = 1) {t : G} (ht : t ∈ A) {P : GL (Fin 2) K} (hP : Om4.IsUT P)
    (htP : bar e ⟨t, S.hMN (Setup.T_le_fsuM (hAT ht))⟩ = Om4.lr P P⁻¹ * Om4.trM)
    {a : G} (ha : a ∈ A) :
    (∃ x y : K, bar e ⟨a, S.hMN (Setup.T_le_fsuM (hAT ha))⟩ =
      Om4.rho (uHom K (Multiplicative.ofAdd x), uHom K (Multiplicative.ofAdd y))) ∨
    ∃ x y : K, bar e ⟨t * a, S.hMN (Setup.T_le_fsuM (hAT (A.mul_mem ht ha)))⟩ =
        Om4.rho (uHom K (Multiplicative.ofAdd x), uHom K (Multiplicative.ofAdd y)) ∧
      bar e ⟨a, S.hMN (Setup.T_le_fsuM (hAT ha))⟩ (Multiplicative.ofAdd !![0, 1; 0, 0]) =
        Multiplicative.ofAdd (Multiplicative.toAdd ((Om4.lr P P⁻¹ * Om4.trM : MulAut (Om4.VM K))
          (Multiplicative.ofAdd !![0, 1; 0, 0])) + y • !![(1 : K), 0; 0, 0]) := by
  rcases hc.form_of_mem_centralizer_V1 (hAT ha) (hAV1 ha) (hsq a ha) with h | ⟨Q, hQ, h⟩
  · exact Or.inl h
  · right
    have hta : t * a ∈ A := A.mul_mem ht ha
    have hbar : bar e ⟨t * a, S.hMN (Setup.T_le_fsuM (hAT hta))⟩ =
        bar e ⟨t, S.hMN (Setup.T_le_fsuM (hAT ht))⟩ * bar e ⟨a, S.hMN (Setup.T_le_fsuM (hAT ha))⟩ :=
      by rw [← map_mul]; rfl
    have hNS : Om4.IsNS (bar e ⟨t * a, S.hMN (Setup.T_le_fsuM (hAT hta))⟩) := by
      rw [hbar, htP, h]
      refine ⟨P * Q⁻¹, P⁻¹ * Q, 1, ?_⟩
      rw [Om4.frM_one, mul_one]
      calc Om4.lr P P⁻¹ * Om4.trM * (Om4.lr Q Q⁻¹ * Om4.trM)
          = Om4.lr P P⁻¹ * (Om4.trM * Om4.lr Q Q⁻¹) * Om4.trM := by group
        _ = Om4.lr P P⁻¹ * Om4.lr Q⁻¹ Q * (Om4.trM * Om4.trM) := by rw [Om4.trM_lr]; group
        _ = _ := by rw [Om4.trM_mul_self, mul_one, Om4.lr_mul]
    rcases hc.form_of_mem_centralizer_V1 (hAT hta) (hAV1 hta) (hsq _ hta) with
      ⟨x, y, hxy⟩ | ⟨R, -, hR⟩
    · refine ⟨x, y, hxy, ?_⟩
      have hat : bar e ⟨a, S.hMN (Setup.T_le_fsuM (hAT ha))⟩ =
          bar e ⟨t, S.hMN (Setup.T_le_fsuM (hAT ht))⟩ *
            bar e ⟨t * a, S.hMN (Setup.T_le_fsuM (hAT hta))⟩ := by
        rw [← map_mul]
        congr 1
        apply Subtype.ext
        show a = t * (t * a)
        rw [← mul_assoc, ← pow_two, hsq t ht, one_mul]
      rw [hat, MulAut.mul_apply, hxy, htP]
      have e1 : Om4.rho (uHom K (Multiplicative.ofAdd x), uHom K (Multiplicative.ofAdd y))
          (Multiplicative.ofAdd !![0, 1; 0, 0]) = Multiplicative.ofAdd !![(0 : K), 1; 0, 0] *
            Multiplicative.ofAdd (y • !![(1 : K), 0; 0, 0]) := by
        apply Multiplicative.toAdd.injective
        rw [Om4Pt.toAdd_rho_e12, toAdd_mul, toAdd_ofAdd, toAdd_ofAdd]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      rw [e1, map_mul, Om4Pt.swap_smul_e11 hP]
      rfl
    · exact absurd (hR ▸ hNS) (Om4Pt.not_isNS_lr_trM R R⁻¹)

theorem card_le_of_swap {A : Subgroup G} (hAT : A ≤ T)
    (hAV1 : A ≤ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G))
    (hsq : ∀ a ∈ A, a ^ 2 = 1) (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {t : G} (ht : t ∈ A) {P : GL (Fin 2) K} (hP : Om4.IsUT P)
    (htP : bar e ⟨t, S.hMN (Setup.T_le_fsuM (hAT ht))⟩ = Om4.lr P P⁻¹ * Om4.trM) :
    ∃ Yv : Finset K, (∀ y ∈ Yv, ∃ a : G, ∃ ha : a ∈ A, ∃ x : K,
      bar e ⟨a, S.hMN (Setup.T_le_fsuM (hAT ha))⟩ =
        Om4.rho (uHom K (Multiplicative.ofAdd x), uHom K (Multiplicative.ofAdd y))) ∧
      Nat.card A ≤ 2 * Yv.card * Nat.card ↥(A ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
  classical
  set Yv := Finset.univ.filter (fun y : K => ∃ a : G, ∃ ha : a ∈ A, ∃ x : K,
      bar e ⟨a, S.hMN (Setup.T_le_fsuM (hAT ha))⟩ =
        Om4.rho (uHom K (Multiplicative.ofAdd x), uHom K (Multiplicative.ofAdd y))) with hYv
  refine ⟨Yv, fun y hy => (Finset.mem_filter.mp hy).2, ?_⟩
  set Z := Multiplicative.toAdd ((Om4.lr P P⁻¹ * Om4.trM : MulAut (Om4.VM K))
    (Multiplicative.ofAdd !![0, 1; 0, 0])) with hZ
  set u₀ : G := (e.symm (Multiplicative.ofAdd !![(0 : K), 1; 0, 0]) : G) with hu₀
  set Sset : Finset G :=
    (Yv.image fun y => (e.symm (Multiplicative.ofAdd !![y, 1; 0, 0]) : G)) ∪
      (Yv.image fun y => (e.symm (Multiplicative.ofAdd (Z + y • !![(1 : K), 0; 0, 0])) : G))
    with hSset
  have hScard : Sset.card ≤ 2 * Yv.card := by
    refine (Finset.card_union_le _ _).trans ?_
    have h1 := Finset.card_image_le (s := Yv)
      (f := fun y => (e.symm (Multiplicative.ofAdd !![y, 1; 0, 0]) : G))
    have h3 := Finset.card_image_le (s := Yv)
      (f := fun y => (e.symm (Multiplicative.ofAdd (Z + y • !![(1 : K), 0; 0, 0])) : G))
    omega
  have hconj : ∀ (h : G) (hh : h ∈ A), h * u₀ * h⁻¹ =
      (e.symm (bar e ⟨h, S.hMN (Setup.T_le_fsuM (hAT hh))⟩
        (Multiplicative.ofAdd !![0, 1; 0, 0])) : G) := fun h hh =>
    conj_symm e ⟨h, S.hMN (Setup.T_le_fsuM (hAT hh))⟩ _
  have hmem : ∀ h ∈ A, h * u₀ * h⁻¹ ∈ Sset := by
    intro h hh
    rw [hconj h hh]
    rcases hc.bar_e12_of_swap hAT hAV1 hsq ht hP htP hh with ⟨x, y, hxy⟩ | ⟨x, y, hxy, hE⟩
    · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨y, ?_, ?_⟩)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, hh, x, hxy⟩
      · rw [hxy]
        congr 2
        apply Multiplicative.toAdd.injective
        rw [Om4Pt.toAdd_rho_e12, toAdd_ofAdd]
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, ?_, ?_⟩)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t * h, A.mul_mem ht hh, x, hxy⟩
      · rw [hE]
  have hstab : A ⊓ Subgroup.centralizer ({u₀} : Set G) ≤
      A ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    rintro h ⟨hh, hhu⟩
    refine ⟨hh, ?_⟩
    have hfix : bar e ⟨h, S.hMN (Setup.T_le_fsuM (hAT hh))⟩ (Multiplicative.ofAdd !![0, 1; 0, 0]) =
        Multiplicative.ofAdd !![0, 1; 0, 0] := by
      have h1 : h * u₀ * h⁻¹ = u₀ := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hhu, mul_inv_cancel_right]
      rw [hconj h hh, hu₀] at h1
      exact e.symm.injective (Subtype.ext h1)
    rcases hc.bar_e12_of_swap hAT hAV1 hsq ht hP htP hh with ⟨x, y, hxy⟩ | ⟨x, y, hxy, hE⟩
    · rw [hxy] at hfix
      have hy : y = 0 := by
        have h3 : !![y, 1; 0, 0] = !![(0 : K), 1; 0, 0] := by
          rw [← Om4Pt.toAdd_rho_e12 x y, hfix, toAdd_ofAdd]
        have := congrFun (congrFun h3 0) 0
        simpa using this
      have hcm : Om4.rho (uHom K (Multiplicative.ofAdd x), uHom K (Multiplicative.ofAdd y)) *
          (Om4.lr P P⁻¹ * Om4.trM) = (Om4.lr P P⁻¹ * Om4.trM) *
            Om4.rho (uHom K (Multiplicative.ofAdd x), uHom K (Multiplicative.ofAdd y)) := by
        rw [← hxy, ← htP, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hcomm h hh t ht)
      have h1 := Om4Pt.mul_eq_of_commute_swap hP hcm
      rw [hy, mul_zero] at h1
      have hx : x = 0 := (mul_eq_zero.mp h1).resolve_right hP.apply_ne_zero.2
      rw [hx, hy, Om4Pt.rho_uHom_zero] at hxy
      exact mem_centralizer_of_bar e _ hxy
    · exfalso
      have h3 : Z + y • !![(1 : K), 0; 0, 0] = !![0, 1; 0, 0] :=
        Multiplicative.ofAdd.injective (hE.symm.trans hfix)
      have h4 := congrFun (congrFun h3 1) 0
      simp at h4
      exact Om4Pt.swap_e12_apply_ne_zero hP h4
  calc Nat.card A ≤ Sset.card * Nat.card ↥(A ⊓ Subgroup.centralizer ({u₀} : Set G)) :=
        card_le_mul_card_centralizer A u₀ Sset hmem
    _ ≤ (2 * Yv.card) * Nat.card ↥(A ⊓ Subgroup.centralizer (fsuV T I : Set G)) :=
        Nat.mul_le_mul hScard (Nat.card_mono (Set.toFinite _) hstab)

theorem card_conj_inf_centralizer_le (hr : (3 : ℕ∞) < rParam (fsuV T I)) (h2 : n = 2) {g : G}
    (hgT : conjSubgroup (fsuV T I) g ≤ T)
    (hAC : ¬ conjSubgroup (fsuV T I) g ≤ Subgroup.centralizer (fsuV T I : Set G)) :
    Nat.card ↥(conjSubgroup (fsuV T I) g ⊓ Subgroup.centralizer (fsuV T I : Set G)) ≤ 16 := by
  set A := conjSubgroup (fsuV T I) g with hA
  have hA2 : IsPGroup 2 ↥A := isPGroup_conjSubgroup S.isPGroup_fsuV g
  have hAcard : Nat.card ↥A = 256 := by rw [hA, card_conjSubgroup, hc.card_fsuV h2]
  have hnc : ⁅fsuV T I, A⁆ ≠ ⊥ := by
    intro h
    apply hAC
    exact le_centralizer_iff_comm.mpr (commutator_eq_bot_iff_le_centralizer'.mp h)
  have hVN : ¬ fsuV T I ≤ Subgroup.normalizer (A : Set G) :=
    e3_11 S.hV (not_isFFModule_of_hyp702A S.hyp S.hV S.hNM)
      (hgT.trans S.T_le_normalizer_V) hnc
  have h1 := e3_4_two hVN
  have hm : 4 ≤ mQuot A (A ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
    have h3 : (3 : ℕ∞) < (mQuot A (A ⊓ Subgroup.centralizer (fsuV T I : Set G)) : ℕ∞) :=
      lt_of_lt_of_le hr h1
    have h4 : 3 < mQuot A (A ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by exact_mod_cast h3
    omega
  have h := card_eq_two_pow_mul hA2 (inf_le_left : A ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ A)
  rw [hAcard] at h
  have h4 : 2 ^ 4 ≤ 2 ^ mQuot A (A ⊓ Subgroup.centralizer (fsuV T I : Set G)) :=
    Nat.pow_le_pow_right (by norm_num) hm
  nlinarith

theorem conj_le_centralizer (hr : (3 : ℕ∞) < rParam (fsuV T I)) (h3108 : Stmt3_2_10_eight)
    (h2 : n = 2) {g : G} (hgT : conjSubgroup (fsuV T I) g ≤ T) :
    conjSubgroup (fsuV T I) g ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  classical
  by_contra hAC
  set A := conjSubgroup (fsuV T I) g with hA
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  have hAcard : Nat.card ↥A = 256 := by rw [hA, card_conjSubgroup, hc.card_fsuV h2]
  have h16 := hc.card_conj_inf_centralizer_le hr h2 hgT hAC
  have h128 : 128 ≤ Nat.card ↥(conjSubgroup (fsuV T I) g) := by
    rw [card_conjSubgroup, hc.card_fsuV h2]; norm_num
  obtain ⟨t, ht, P, hP, htP⟩ := hc.exists_swap hr h3108 h2 le_rfl hgT h128 hAC
  have hVg := isElemAbelian_conjSubgroup S.hV g
  have hsq : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => hVg.2 a ha
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVg.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨Yv, -, h1⟩ := hc.card_le_of_swap hgT
    (hc.le_centralizer_V1 hr h3108 h2 le_rfl hgT h128) hsq hcomm ht hP htP
  have hY : Yv.card ≤ 4 := (Finset.card_le_univ Yv).trans (by rw [hK4])
  have h3 := h1.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hY) h16)
  omega

theorem wClos_zero_le (h36 : A36ForSQTK) (h312 : A312ForSQTK)
    (h314 : A314Facts) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h3104 : Stmt3_2_10_four) (h3108 : Stmt3_2_10_eight) (hFa : A314QuasiRankFact)
    (hFb : A314FFCohomFact) (h3228 : Stmt3_2_2_eight) (hE610 : Ch6InE610Four)
    (h612 : ASInputs.AS_E_6_12) (h1 : zQ T I = fsuV T I) (h2 : n = 2) :
    wClos (fsuV T I) 0 T ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
  have hr := hc.three_lt_rParam h36 h312 h314 h37 h38 h39 h37c h38c h3104 h3108 hFa hFb h3228
    hE610 h612 h1 h2
  refine iSup₂_le fun A hA => ?_
  obtain ⟨hAT, g, hAg, hm⟩ := hA
  have hAeq : A = conjSubgroup (fsuV T I) g :=
    (mQuot_eq_zero_iff (isPGroup_conjSubgroup S.isPGroup_fsuV g) hAg).mp hm
  subst hAeq
  exact le_inf hAT (hc.conj_le_centralizer hr h3108 h2 hAT)

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
