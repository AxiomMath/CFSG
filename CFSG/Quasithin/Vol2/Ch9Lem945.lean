module

public import CFSG.Quasithin.Vol2.Ch9Lem944

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H CFSG.Quasithin.E3 Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem hyp_le_centralizer (h36 : A36ForSQTK) (h312 : A312ForSQTK)
    (h314 : A314Facts) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h3104 : Stmt3_2_10_four) (h3108 : Stmt3_2_10_eight) (hFa : A314QuasiRankFact)
    (hFb : A314FFCohomFact) (hr : (3 : ℕ∞) < rParam (fsuV T I))
    (hw : 0 < wParam T (fsuV T I)) (h2 : n = 2) {g : G} {A : Subgroup G}
    (hAg : A ≤ conjSubgroup (fsuV T I) g) (hAT : A ≤ T)
    (hm : mQuot (conjSubgroup (fsuV T I) g) A = 1) :
    A ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  classical
  by_contra hAC
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  have hVg2 : IsPGroup 2 ↥(conjSubgroup (fsuV T I) g) := isPGroup_conjSubgroup S.isPGroup_fsuV g
  have hVgcard : Nat.card ↥(conjSubgroup (fsuV T I) g) = 256 := by
    rw [card_conjSubgroup, hc.card_fsuV h2]
  have hAcard : Nat.card A = 128 := by
    have h := card_eq_two_pow_mul hVg2 hAg
    rw [hVgcard, hm] at h
    omega
  have hVg := isElemAbelian_conjSubgroup S.hV g
  have hsq : ∀ a ∈ A, a ^ 2 = 1 := fun a ha => hVg.2 a (hAg ha)
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVg.1.is_comm.comm ⟨a, hAg ha⟩ ⟨b, hAg hb⟩)
  have h16 : Nat.card ↥(A ⊓ Subgroup.centralizer (fsuV T I : Set G)) ≤ 16 := by
    by_contra hgt
    push Not at hgt
    set B := A ⊓ Subgroup.centralizer (fsuV T I : Set G) with hB
    have hBV : B ≤ conjSubgroup (fsuV T I) g := inf_le_left.trans hAg
    have hm3 : mQuot (conjSubgroup (fsuV T I) g) B ≤ 3 := by
      have h := card_eq_two_pow_mul hVg2 hBV
      rw [hVgcard] at h
      by_contra hlt
      push Not at hlt
      have h4 : 2 ^ 4 ≤ 2 ^ mQuot (conjSubgroup (fsuV T I) g) B :=
        Nat.pow_le_pow_right (by norm_num) hlt
      nlinarith
    have hVN : fsuV T I ≤ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) := by
      have hVC : fsuV T I ≤ fsuV T I ⊓ Subgroup.centralizer (B : Set G) :=
        le_inf le_rfl (le_centralizer_iff_comm.mp inf_le_right)
      refine hVC.trans ?_
      by_contra hle
      have h3 := e3_4_one (le_inf hBV (inf_le_left.trans (hAT.trans S.T_le_normalizer_V))) hle
      have h4 : (3 : ℕ∞) < (mQuot (conjSubgroup (fsuV T I) g) B : ℕ∞) := lt_of_lt_of_le hr h3
      have h5 : 3 < mQuot (conjSubgroup (fsuV T I) g) B := by exact_mod_cast h4
      omega
    have hT322 := hypE322_of_fsu S.hyp.fsu S.hV S.hN
    have hVC := (e3_25_centralizer_iff_normalizer S.hV hT322 hw g).mpr hVN
    exact hAC (hAg.trans (le_centralizer_iff_comm.mp hVC))
  have hAV1 := hc.le_centralizer_V1 hr h3108 h2 hAg hAT hAcard.ge
  obtain ⟨t, ht, P, hP, htP⟩ := hc.exists_swap hr h3108 h2 hAg hAT hAcard.ge hAC
  obtain ⟨Yv, hYv, hcardY⟩ := hc.card_le_of_swap hAT hAV1 hsq hcomm ht hP htP
  have hYle : Yv.card ≤ 4 := (Finset.card_le_univ Yv).trans (by rw [hK4])
  have hYuniv : Yv = Finset.univ := by
    refine Finset.eq_univ_of_card Yv ?_
    rw [hK4]
    by_contra hne
    have hY3 : Yv.card ≤ 3 := by omega
    have := hcardY.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hY3) h16)
    omega
  have h16' : 16 ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
    have := hcardY.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hYle))
    omega
  have hay : ∀ y : K, ∃ a : G, ∃ ha : a ∈ A, ∃ x : K,
      bar e ⟨a, S.hMN (Setup.T_le_fsuM (hAT ha))⟩ =
        Om4.rho (uHom K (Multiplicative.ofAdd x), uHom K (Multiplicative.ofAdd y)) ∧
      x * (P : Matrix (Fin 2) (Fin 2) K) 1 1 = (P : Matrix (Fin 2) (Fin 2) K) 0 0 * y := by
    intro y
    obtain ⟨a, ha, x, hx⟩ := hYv y (hYuniv ▸ Finset.mem_univ y)
    refine ⟨a, ha, x, hx, Om4Pt.mul_eq_of_commute_swap hP ?_⟩
    rw [← hx, ← htP, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm a ha t ht)
  set Y : Om4.VM K := Multiplicative.ofAdd ((P : Matrix (Fin 2) (Fin 2) K) * !![0, 0; 0, 1])
    with hY
  set Y₀ : G := (e.symm Y : G) with hY₀
  have htY : t * Y₀ = Y₀ * t := by
    have h1 := conj_symm e ⟨t, S.hMN (Setup.T_le_fsuM (hAT ht))⟩ Y
    rw [htP, hY, Om4Pt.swap_mul_e22] at h1
    calc t * Y₀ = (t * Y₀ * t⁻¹) * t := by group
      _ = Y₀ * t := by rw [hY₀, h1]
  have htC : t ∉ Subgroup.centralizer (fsuV T I : Set G) := by
    intro h
    have h1 := bar_eq_one_of_mem_centralizer e (S.hMN (Setup.T_le_fsuM (hAT ht))) h
    rw [htP] at h1
    exact Om4Pt.not_isNS_lr_trM P P⁻¹ (h1 ▸ Om4.isNS_one)
  have hcY : ∀ c ∈ A ⊓ Subgroup.centralizer (fsuV T I : Set G),
      c ∈ A ⊓ Subgroup.centralizer ({Y₀} : Set G) := by
    rintro c ⟨hcA, hcC⟩
    exact ⟨hcA, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hcC _ (e.symm Y).2).symm⟩
  have htcY : ∀ c ∈ A ⊓ Subgroup.centralizer (fsuV T I : Set G),
      t * c ∈ A ⊓ Subgroup.centralizer ({Y₀} : Set G) := by
    intro c hc'
    obtain ⟨hcA, hcY'⟩ := hcY c hc'
    refine ⟨A.mul_mem ht hcA, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : c * Y₀ = Y₀ * c := Subgroup.mem_centralizer_singleton_iff.mp hcY'
    calc t * c * Y₀ = t * (c * Y₀) := by group
      _ = t * Y₀ * c := by rw [h1]; group
      _ = Y₀ * (t * c) := by rw [htY]; group
  have h32 : 32 ≤ Nat.card ↥(A ⊓ Subgroup.centralizer ({Y₀} : Set G)) := by
    let f : ↥(A ⊓ Subgroup.centralizer (fsuV T I : Set G)) ⊕
        ↥(A ⊓ Subgroup.centralizer (fsuV T I : Set G)) →
          ↥(A ⊓ Subgroup.centralizer ({Y₀} : Set G)) := fun z => match z with
      | Sum.inl c => ⟨c, hcY c c.2⟩
      | Sum.inr c => ⟨t * c, htcY c c.2⟩
    have hf : Function.Injective f := by
      rintro (c | c) (c' | c') h <;> have h' := congrArg Subtype.val h
      · exact congrArg Sum.inl (Subtype.ext h')
      · exfalso
        apply htC
        have h3 : t = (c : G) * (c' : G)⁻¹ := by
          have h4 : (c : G) = t * c' := h'
          rw [h4]; group
        rw [h3]
        exact (Subgroup.centralizer (fsuV T I : Set G)).mul_mem c.2.2
          ((Subgroup.centralizer (fsuV T I : Set G)).inv_mem c'.2.2)
      · exfalso
        apply htC
        have h3 : t = (c' : G) * (c : G)⁻¹ := by
          have h4 : t * (c : G) = c' := h'
          rw [← h4]; group
        rw [h3]
        exact (Subgroup.centralizer (fsuV T I : Set G)).mul_mem c'.2.2
          ((Subgroup.centralizer (fsuV T I : Set G)).inv_mem c.2.2)
      · exact congrArg Sum.inr (Subtype.ext (mul_left_cancel h'))
    have h3 := Nat.card_le_card_of_injective f hf
    rw [Nat.card_sum] at h3
    omega
  have hY₀N : Y₀ ∈ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) :=
    hc.mem_normalizer_conj_of_card hr h2 (e.symm Y).2 (inf_le_left.trans hAg)
      (inf_le_left.trans (hAT.trans Setup.T_le_fsuM)) inf_le_right h32
  have hcommD : ∀ y : K, y ≠ 0 → ∃ z : G, z ∈ conjSubgroup (fsuV T I) g ∧
      z ∈ inV e (Om4Pt.lineM (Om4Pt.dMat (P : Matrix (Fin 2) (Fin 2) K) y)) ∧ z ≠ 1 := by
    intro y hy
    obtain ⟨a, ha, x, hx, hxy⟩ := hay y
    set a' : ↥(Subgroup.normalizer (fsuV T I : Set G)) := ⟨a, S.hMN (Setup.T_le_fsuM (hAT ha))⟩
      with ha'
    have hmem := comm_symm_mem e a' Y
    have hE := e_comm_symm e a' Y hmem
    have hbar : Multiplicative.toAdd (bar e a' Y) = (P : Matrix (Fin 2) (Fin 2) K) *
        !![0, 0; 0, 1] + Om4Pt.dMat (P : Matrix (Fin 2) (Fin 2) K) y := by
      rw [ha', hx, hY]
      exact Om4Pt.toAdd_rho_mul_e22 hP hxy
    have hE' : Multiplicative.toAdd (e ⟨Y₀ * a * Y₀⁻¹ * a⁻¹, hmem⟩) =
        (-1 : K) • Om4Pt.dMat (P : Matrix (Fin 2) (Fin 2) K) y := by
      rw [hE, toAdd_mul, toAdd_inv, hbar, hY, toAdd_ofAdd, neg_one_smul]
      abel
    refine ⟨Y₀ * a * Y₀⁻¹ * a⁻¹, ?_, mem_inV.mpr ⟨hmem, -1, hE'⟩, ?_⟩
    · have h1 : Y₀ * a * Y₀⁻¹ ∈ conjSubgroup (fsuV T I) g :=
        (Subgroup.mem_normalizer_iff.mp hY₀N a).mp (hAg ha)
      exact (conjSubgroup (fsuV T I) g).mul_mem h1
        ((conjSubgroup (fsuV T I) g).inv_mem (hAg ha))
    · intro h1
      have h3 : e ⟨Y₀ * a * Y₀⁻¹ * a⁻¹, hmem⟩ = 1 := by
        rw [show (⟨Y₀ * a * Y₀⁻¹ * a⁻¹, hmem⟩ : ↥(fsuV T I)) = 1 from Subtype.ext h1, map_one]
      rw [h3, toAdd_one, neg_one_smul, eq_comm, neg_eq_zero] at hE'
      exact Om4Pt.det_dMat_ne_zero hP hy (by rw [hE']; simp)
  obtain ⟨ω, hω⟩ : ∃ ω : K, ω ∉ ({0, 1} : Finset K) := by
    by_contra hall
    push Not at hall
    have h3 : (Finset.univ : Finset K) ⊆ {0, 1} := fun x _ => hall x
    have h4 := Finset.card_le_card h3
    rw [Finset.card_univ, hK4] at h4
    have h5 := Finset.card_le_two (a := (0 : K)) (b := 1)
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  obtain ⟨z₁, hz₁g, hz₁, hz₁1⟩ := hcommD 1 one_ne_zero
  obtain ⟨z₂, hz₂g, hz₂, hz₂1⟩ := hcommD ω hω.1
  have hpair := hc.centralizer_pair_le h36 h312 h314 h37 h38 h39 h37c h38c h3104 h3108 hFa hFb h2
    (Om4Pt.det_dMat_ne_zero hP one_ne_zero) (Om4Pt.det_dMat_ne_zero hP hω.1)
    (Om4Pt.dMat_ne_smul hP one_ne_zero hω.1 hω.2) hz₁ hz₁1 hz₂ hz₂1
  set D := Subgroup.closure ({z₁, z₂} : Set G) with hD
  have hDV : D ≤ fsuV T I := by
    rw [hD, Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact inV_le e _ hz₁
    · exact inV_le e _ hz₂
  have hDg : D ≤ (fsuV T I).map (MulAut.conj g⁻¹).toMonoidHom := by
    show D ≤ conjSubgroup (fsuV T I) g
    rw [hD, Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hz₁g
    · exact hz₂g
  have hDM : Subgroup.centralizer (D : Set G) ≤ fsuM T L := by
    refine le_trans (le_inf ?_ ?_) hpair
    · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.subset_closure
        (Set.mem_insert _ _)))
    · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.subset_closure
        (Set.mem_insert_of_mem _ rfl)))
  have hg := S.mem_fsuM_of_le_map_conj h3108 hDV hDM hDg
  have hgM : g ∈ fsuM T L := by simpa using hg
  have hgN : g ∈ Subgroup.normalizer (fsuV T I : Set G) := S.hMN hgM
  have hVg' : conjSubgroup (fsuV T I) g = fsuV T I := conjSubgroup_eq_iff_mem_normalizer.mpr hgN
  rw [hVg'] at hAg
  exact hAC (hAg.trans (S.fsuV_le_Q.trans inf_le_right))

theorem wClos_one_le (h36 : A36ForSQTK) (h312 : A312ForSQTK)
    (h314 : A314Facts) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h3104 : Stmt3_2_10_four) (h3108 : Stmt3_2_10_eight) (hFa : A314QuasiRankFact)
    (hFb : A314FFCohomFact) (h3228 : Stmt3_2_2_eight) (hE610 : Ch6InE610Four)
    (h612 : ASInputs.AS_E_6_12) (h1 : zQ T I = fsuV T I) (h2 : n = 2) :
    wClos (fsuV T I) 1 T ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
  have hr := hc.three_lt_rParam h36 h312 h314 h37 h38 h39 h37c h38c h3104 h3108 hFa hFb h3228
    hE610 h612 h1 h2
  have h944 := hc.wClos_zero_le h36 h312 h314 h37 h38 h39 h37c h38c h3104 h3108 hFa hFb h3228
    hE610 h612 h1 h2
  have hw : 0 < wParam T (fsuV T I) := by
    have := le_wParam_of_wClos_le (V := fsuV T I) (T := T) (n := 1) fun j hj => by
      interval_cases j
      exact h944
    exact lt_of_lt_of_le (by norm_num) this
  refine iSup₂_le fun A hA => ?_
  obtain ⟨hAT, g, hAg, hm⟩ := hA
  exact le_inf hAT (hc.hyp_le_centralizer h36 h312 h314 h37 h38 h39 h37c h38c h3104 h3108 hFa hFb
    hr hw h2 hAg hAT hm)

end IsCoord

end Setup

end CFSG.Quasithin.H13.Ch9
