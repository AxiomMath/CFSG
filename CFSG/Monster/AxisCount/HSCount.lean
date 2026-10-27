module

public import CFSG.Monster.AxisCount.HSIdent
public import CFSG.Monster.AxisCount.Balance
public import CFSG.Monster.AxisCount.SetupGroups
public import CFSG.Monster.AxisCount.Cover
public import CFSG.Monster.AxisCount.HSIdentBaby

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount.HS

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short

@[expose] def noTau (w : List Native.Gen) : Bool := w.all fun g => !isTauB g

theorem ne_tau_of_noTau {w : List Native.Gen} (h : noTau w = true) :
    ∀ g ∈ w, g ≠ Native.Gen.tau := by
  intro g hg e
  have := List.all_eq_true.1 h g hg
  subst e
  simp [isTauB] at this

theorem wordLin_mem_Gvis_of_noTau {w : List Native.Gen} (h : noTau w = true) :
    wordLin w ∈ Gvis :=
  wordLin_mem_Gvis w (ne_tau_of_noTau h)

@[expose] def visCheck : Bool :=
  (List.finRange 12).all fun i =>
    noTau (Cert.UA i) && noTau (Cert.UB i) &&
      (List.range (Cert.nW i)).all (fun r =>
        noTau (Cert.hW i r) && noTau (Cert.kappaW i r true) && noTau (Cert.kappaW i r false) &&
          noTau (hppL i r true) && noTau (hppL i r false)) &&
      (List.range 2).all fun k => noTau (hppU i k)

theorem visCheck_eq : visCheck = true := by decide +kernel

theorem visCheck_parts (h : visCheck = true) (i : Fin 12) :
    noTau (Cert.UA i) = true ∧ noTau (Cert.UB i) = true ∧
      (∀ r, r < Cert.nW i → noTau (Cert.hW i r) = true ∧ noTau (Cert.kappaW i r true) = true ∧
        noTau (Cert.kappaW i r false) = true ∧ noTau (hppL i r true) = true ∧
          noTau (hppL i r false) = true) ∧
      (∀ k, k < 2 → noTau (hppU i k) = true) := by
  have h1 := List.all_eq_true.1 h i (List.mem_finRange i)
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨⟨hA, hB⟩, hr⟩, hk⟩ := h1
  refine ⟨hA, hB, fun r hr' => ?_, fun k hk' => List.all_eq_true.1 hk k (List.mem_range.2 hk')⟩
  have := List.all_eq_true.1 hr r (List.mem_range.2 hr')
  simp only [Bool.and_eq_true] at this
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := this
  exact ⟨h1, h2, h3, h4, h5⟩

theorem wordLin_tpw (ε : Bool) : wordLin (tpw ε) = tpow tauB ε := by
  cases ε
  · exact wordLin_tauPow_two
  · simp [tpw, wordLin_cons, wordLin_nil, Native.Gen.toLin_tau]

theorem wordLin_xW (i : Fin 12) (r : Nat) (ε : Bool) :
    wordLin (xW i r ε) =
      wordLin (Cert.kappaW i r ε) * tpow tauB ε * wordLin (Cert.hW i r) := by
  simp only [xW, wordLin_append, wordLin_tpw, mul_assoc]

theorem mem_Cgen_of_E1 {σ c : SpaceB ≃ₗ[ℚ] SpaceB} (hσ : σ ∈ Gmat) (hσ₁ : σ aStar = aStar)
    (hc : c ∈ Cgen) (h : σ aStarMinus = c aStarMinus) : σ ∈ Cgen := by
  have hcG : c ∈ Gmat := Cgen_le_Gmat hc
  have hc₁ : c aStar = aStar := fix_aStar_of_mem_Cgen hc
  have hc₁' : c⁻¹ aStar = aStar := by
    calc c⁻¹ aStar = c⁻¹ (c aStar) := by rw [hc₁]
      _ = aStar := by simp
  have h1 : (c⁻¹ * σ) aStar = aStar := by
    rw [LinearEquiv.mul_apply, hσ₁, hc₁']
  have h2 : (c⁻¹ * σ) aStarMinus = aStarMinus := by
    rw [LinearEquiv.mul_apply, h]
    simp
  have h3 : c⁻¹ * σ ∈ Jstar :=
    mem_Jstar_of_fix_of_fix (Gmat.mul_mem (Gmat.inv_mem hcG) hσ) h1 h2
  have : σ = c * (c⁻¹ * σ) := by simp
  rw [this]
  exact Cgen.mul_mem hc (Jstar_le_Cgen h3)

theorem wordLin_mem_Jstar_of_fix {w : List Native.Gen} (hw : noTau w = true)
    (h : wordLin w aStar = aStar) : wordLin w ∈ Jstar :=
  mem_Jstar_of_fix (wordLin_mem_Gvis_of_noTau hw) h

@[expose] noncomputable def gm (i : Fin 12) : SpaceB ≃ₗ[ℚ] SpaceB := wordLin (Cert.gammaW i)

theorem Ui_le_stabilizer
    (i : Fin 12) :
    Cert.Ui i ≤ MulAction.stabilizer (SpaceB ≃ₗ[ℚ] SpaceB) (vv i) := by
  rw [Cert.Ui_eq]
  refine (Subgroup.closure_le _).2 ?_
  rintro x (rfl | rfl)
  · exact MulAction.mem_stabilizer_iff.2 (hs_stab i 0 (by norm_num))
  · exact MulAction.mem_stabilizer_iff.2 (hs_stab i 1 (by norm_num))

theorem kappa_mem_Gvis (i : Fin 12) (r : Nat) (hr : r < Cert.nW i) (ε : Bool) :
    wordLin (Cert.kappaW i r ε) ∈ Gvis := by
  obtain ⟨-, -, hr', -⟩ := visCheck_parts visCheck_eq i
  obtain ⟨-, h1, h2, -, -⟩ := hr' r hr
  cases ε
  · exact wordLin_mem_Gvis_of_noTau h2
  · exact wordLin_mem_Gvis_of_noTau h1

theorem hppL_noTau (i : Fin 12) (r : Nat) (hr : r < Cert.nW i) (ε : Bool) :
    noTau (hppL i r ε) = true := by
  obtain ⟨-, -, hr', -⟩ := visCheck_parts visCheck_eq i
  obtain ⟨-, -, -, h1, h2⟩ := hr' r hr
  cases ε
  · exact h2
  · exact h1

theorem hppU_noTau (i : Fin 12) (k : Nat) (hk : k < 2) : noTau (hppU i k) = true :=
  (visCheck_parts visCheck_eq i).2.2.2 k hk

theorem spec_hs
    (i : Fin 12) (r : Fin (Cert.nW i)) (ε : Bool) :
    (wordLin (Cert.kappaW i r ε) * tpow tauB ε * Cert.hh i r) • vv i = vv (Cert.tFin i r ε) := by
  have h := hs_trans i r r.2 ε
  rw [wordLin_xW] at h
  exact h

noncomputable def hsSetup :
    Setup (SpaceB ≃ₗ[ℚ] SpaceB) SpaceB (Fin 12) fun i => Fin (Cert.nW i) where
  H := Gvis
  N' := Nfr'
  N := Nfr
  τ := tauB
  a := CFSG.Monster.B.TwoA.hE0
  v := vv
  U := Cert.Ui
  h i r := Cert.hh i r
  κ i r ε := wordLin (Cert.kappaW i r ε)
  t i r ε := Cert.tFin i r ε
  N'_le_N := Nfr'_le_Nfr
  N_le_H := Nfr_le_Gvis
  relIndex_N'_N := relIndex_Nfr'_Nfr
  conj_mem := fun _ hn => tauB_conj_mem_Nfr' hn
  conj_inv_mem := fun _ hn => tauB_inv_conj_mem_Nfr' hn
  a_mem := hE0_mem_Nfr
  a_notMem := hE0_notMem_Nfr'
  a_conj := hE0_inv_mul_tauB_mul_hE0
  U_le_H := Cert.Ui_le_Gvis
  U_le_stabilizer := Ui_le_stabilizer
  h_mem := fun i r => Cert.hh_mem_Gvis i r.2
  κ_mem := fun i r ε => kappa_mem_Gvis i r r.2 ε
  cover := Cert.cover
  spec := spec_hs

instance :
    Finite hsSetup.H := finite_Gvis

theorem vv_zero : vv 0 = aStar := by
  simp [vv, Cert.gammaW, Cert.orbits, Cert.orbit0, wordLin_nil]

theorem gm_smul (i : Fin 12) : gm i aStar = vv i := rfl

theorem gm_mem_Gmat (i : Fin 12) : gm i ∈ Gmat := wordLin_mem_Gmat _

theorem mem_Cgen_of_words
    {X gi gt hpp : List Native.Gen} {j : Nat} (hj : j < 10)
    (hnt : noTau hpp = true) (h2 : wordLin hpp aStar = aStar)
    (h1 : wordLin X (wordLin gi aStarMinus) =
      wordLin (hpp ++ gt) (wordLin (babyW j) aStarMinus))
    (hfix : ((wordLin gt)⁻¹ * wordLin X * wordLin gi) aStar = aStar) :
    (wordLin gt)⁻¹ * wordLin X * wordLin gi ∈ Cgen := by
  have hc : wordLin hpp * wordLin (babyW j) ∈ Cgen :=
    Cgen.mul_mem (Jstar_le_Cgen (wordLin_mem_Jstar_of_fix hnt h2)) (babyW_mem_Cgen hj)
  refine mem_Cgen_of_E1 (Gmat.mul_mem (Gmat.mul_mem (Gmat.inv_mem (wordLin_mem_Gmat gt))
    (wordLin_mem_Gmat X)) (wordLin_mem_Gmat gi)) hfix hc ?_
  calc ((wordLin gt)⁻¹ * wordLin X * wordLin gi) aStarMinus
      = (wordLin gt)⁻¹ (wordLin X (wordLin gi aStarMinus)) := rfl
    _ = (wordLin gt)⁻¹ (wordLin (hpp ++ gt) (wordLin (babyW j) aStarMinus)) := by rw [h1]
    _ = (wordLin hpp * wordLin (babyW j)) aStarMinus := by
      rw [wordLin_append]
      simp

theorem lam_eq
    (i : Fin 12) (r : Fin (Cert.nW i)) (ε : Bool) :
    hsSetup.lam gm i r ε =
      (wordLin (Cert.gammaW (Cert.tFin i r ε)))⁻¹ * wordLin (xW i r ε) *
        wordLin (Cert.gammaW i) := by
  simp only [Setup.lam, hsSetup, gm, Cert.hh, wordLin_xW, mul_assoc]

theorem gm_smul_v
    (i : Fin 12) : gm i • hsSetup.v 0 = hsSetup.v i := by
  show gm i (vv 0) = vv i
  rw [vv_zero]
  rfl

theorem schreier_le_Cgen :
    Subgroup.closure (hsSetup.schreierGens gm 0) ≤ Cgen := by
  have hstab := hsSetup.schreierGens_subset_stabilizer (γ := gm) (i₀ := 0) gm_smul_v
  refine hsSetup.closure_schreierGens_le (K := Cgen) ?_ ?_ ?_
  · intro g hg hgv
    have : g aStar = aStar := by
      have h := hgv
      change g (vv 0) = vv 0 at h
      rwa [vv_zero] at h
    exact Jstar_le_Cgen (mem_Jstar_of_fix hg this)
  · intro i u hu
    have hgen : ∀ k, k < 2 → (gm i)⁻¹ * wordLin (uW i k) * gm i ∈ Cgen := by
      intro k hk
      obtain ⟨hb, h1⟩ := hs_e1U i k hk
      have hmem : wordLin (uW i k) ∈ hsSetup.U i := by
        show wordLin (uW i k) ∈ Cert.Ui i
        rw [Cert.Ui_eq]
        interval_cases k
        · exact Subgroup.subset_closure (Or.inl rfl)
        · exact Subgroup.subset_closure (Or.inr rfl)
      have hsg : (gm i)⁻¹ * wordLin (uW i k) * gm i ∈
          MulAction.stabilizer (SpaceB ≃ₗ[ℚ] SpaceB) (hsSetup.v 0) :=
        hstab (hsSetup.mem_schreierGens_iff.2 (Or.inr (Or.inl ⟨i, _, hmem, rfl⟩)))
      have hfix : ((wordLin (Cert.gammaW i))⁻¹ * wordLin (uW i k) * wordLin (Cert.gammaW i))
          aStar = aStar := by
        have := MulAction.mem_stabilizer_iff.1 hsg
        change ((gm i)⁻¹ * wordLin (uW i k) * gm i) (vv 0) = vv 0 at this
        rwa [vv_zero] at this
      exact mem_Cgen_of_words hb (hppU_noTau i k hk) (hs_e2U i k hk) h1 hfix
    have hK : Cert.Ui i ≤ Cgen.comap (MulAut.conj (gm i)⁻¹).toMonoidHom := by
      rw [Cert.Ui_eq]
      refine (Subgroup.closure_le _).2 ?_
      rintro x (rfl | rfl)
      · show (MulAut.conj (gm i)⁻¹) (wordLin (Cert.UA i)) ∈ Cgen
        rw [MulAut.conj_apply, inv_inv]
        exact hgen 0 (by norm_num)
      · show (MulAut.conj (gm i)⁻¹) (wordLin (Cert.UB i)) ∈ Cgen
        rw [MulAut.conj_apply, inv_inv]
        exact hgen 1 (by norm_num)
    have := hK hu
    simpa [MulAut.conj_apply] using this
  · intro i r ε
    obtain ⟨hb, h1⟩ := hs_e1L i r r.2 ε
    have hsg : hsSetup.lam gm i r ε ∈ MulAction.stabilizer (SpaceB ≃ₗ[ℚ] SpaceB)
        (hsSetup.v 0) :=
      hstab (hsSetup.mem_schreierGens_iff.2 (Or.inr (Or.inr ⟨i, r, ε, rfl⟩)))
    have hfix : ((wordLin (Cert.gammaW (Cert.tFin i r ε)))⁻¹ * wordLin (xW i r ε) *
        wordLin (Cert.gammaW i)) aStar = aStar := by
      rw [← lam_eq]
      have := MulAction.mem_stabilizer_iff.1 hsg
      change hsSetup.lam gm i r ε (vv 0) = vv 0 at this
      rwa [vv_zero] at this
    rw [lam_eq]
    exact mem_Cgen_of_words hb (hppL_noTau i r r.2 ε) (hs_e2L i r r.2 ε) h1 hfix

theorem gm_zero_mem_Gvis : gm 0 ∈ Gvis := by
  have : gm 0 = 1 := by simp [gm, Cert.gammaW, Cert.orbits, Cert.orbit0, wordLin_nil]
  rw [this]
  exact one_mem _

theorem orb_injective :
    Function.Injective hsSetup.orb :=
  hsSetup.orb_injective_of_trA2 (le_refl _) hs_trace_injective

theorem Gmat_inf_stabilizer_eq_closure :
    Gmat ⊓ MulAction.stabilizer (SpaceB ≃ₗ[ℚ] SpaceB) aStar =
      Subgroup.closure (hsSetup.schreierGens gm 0) := by
  have h := hsSetup.stabilizer_inf_closure_eq (γ := gm) (i₀ := 0) orb_injective gm_smul_v
    (fun i => gm_mem_Gmat i) gm_zero_mem_Gvis
  have e : hsSetup.v 0 = aStar := vv_zero
  rw [e] at h
  rw [inf_comm]
  exact h

theorem Gmat_inf_stabilizer_le_Cgen :
    Gmat ⊓ MulAction.stabilizer (SpaceB ≃ₗ[ℚ] SpaceB) aStar ≤ Cgen := by
  rw [Gmat_inf_stabilizer_eq_closure]
  exact schreier_le_Cgen

theorem Gmat_inf_stabilizer_eq_Cgen :
    Gmat ⊓ MulAction.stabilizer (SpaceB ≃ₗ[ℚ] SpaceB) aStar = Cgen :=
  le_antisymm Gmat_inf_stabilizer_le_Cgen Cgen_le_inf_stabilizer

theorem list_sum_range_map {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

@[expose] def Mfun (t i : Fin 12) : ℕ :=
  ((List.range (Cert.nW i)).map fun r => Cert.sizeW i r *
    ((if Cert.tW i r true = (t : ℕ) then 1 else 0) +
      (if Cert.tW i r false = (t : ℕ) then 1 else 0))).sum

theorem Mfun_eq : ∀ t i : Fin 12, Mfun t i = transM t i := by decide +kernel

theorem M_eq_transM :
    hsSetup.M = transM := by
  have hk : ∀ (i : Fin 12) (r : Fin (Cert.nW i)), hsSetup.k i r = Cert.sizeW i r :=
    fun i r => hsSetup.k_eq (Cert.natCard_doubleCoset_eq i r)
  funext t i
  rw [← Mfun_eq t i, Mfun, list_sum_range_map, Setup.M]
  rw [← Fin.sum_univ_eq_sum_range (fun r => Cert.sizeW i r *
    ((if Cert.tW i r true = (t : ℕ) then 1 else 0) +
      (if Cert.tW i r false = (t : ℕ) then 1 else 0)))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hk i r]
  simp only [hsSetup, Cert.tFin, Fin.ext_iff]

theorem X0_eq_orbit_Gmat :
    hsSetup.X0 = MulAction.orbit Gmat aStar := by
  have hX := hsSetup.X0_eq_orbit_of_exists 0 gm gm_smul_v (fun i => gm_mem_Gmat i)
  have e : hsSetup.v 0 = aStar := vv_zero
  rw [e] at hX
  exact hX

theorem card_orb_eq :
    (∀ i, Nat.card (hsSetup.orb i) = orbitSizes i) ∧ Nat.card hsSetup.X0 = totalAxes := by
  have hL : hsSetup.L = transL := two_mul_natCard_Gvis_div
  have h0 : Nat.card (hsSetup.orb 0) = 196560 := by
    show Nat.card (MulAction.orbit Gvis (vv 0)) = 196560
    rw [vv_zero]
    exact natCard_orbit_Gvis_aStar
  exact hsSetup.card_orb_eq_orbitSizes Cert.pairwise_disjoint orb_injective M_eq_transM hL h0

theorem natCard_orbit_Gmat_aStar :
    Nat.card (MulAction.orbit Gmat aStar) = 97239461142009186000 := by
  have h := card_orb_eq.2
  rw [X0_eq_orbit_Gmat] at h
  exact h

theorem natCard_Gmat :
    Nat.card Gmat = 97239461142009186000 * Nat.card Cgen := by
  rw [natCard_Gmat_eq_of_stabilizer_le Gmat_inf_stabilizer_le_Cgen, natCard_orbit_Gmat_aStar]

theorem centralizer_tStar_eq_Cgen :
    Gmat ⊓ Subgroup.centralizer {tStar} = Cgen :=
  Gmat_inf_centralizer_tStar_eq_Cgen Gmat_inf_stabilizer_le_Cgen

theorem centralizer_tStar_le_Cgen :
    ∀ g ∈ Gmat, g * tStar = tStar * g → g ∈ Cgen := fun _ hg h =>
  Gmat_inf_stabilizer_le_Cgen ⟨hg, MulAction.mem_stabilizer_iff.2 ((mul_tStar_comm_iff hg).1 h)⟩

end CFSG.Monster.AxisCount.HS
