module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSL
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelPSL
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoRootConversePSL
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSL
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDCommute
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPSL

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos
open scoped commutatorElement

private lemma nbrPSL_mem_sup_central {U : Type} [Group U] {K Z : Subgroup U}
    (hZ : Z ≤ Subgroup.center U) {x : U} : x ∈ K ⊔ Z ↔ ∃ k ∈ K, ∃ z ∈ Z, k * z = x := by
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  exact Subgroup.mem_sup_of_normal_right

private lemma nbrPSL_commutatorElement_mul_central_left {U : Type} [Group U]
    {c : U} (hc : c ∈ Subgroup.center U) (g h : U) : ⁅g * c, h⁆ = ⁅g, h⁆ := by
  have e : c * h * c⁻¹ = h := by
    rw [← Subgroup.mem_center_iff.mp hc h, mul_inv_cancel_right]
  simp only [commutatorElement_def, mul_inv_rev]
  calc g * c * h * (c⁻¹ * g⁻¹) * h⁻¹ = g * (c * h * c⁻¹) * g⁻¹ * h⁻¹ := by group
    _ = g * h * g⁻¹ * h⁻¹ := by rw [e]

private lemma nbrPSL_commutatorElement_mul_central_right {U : Type} [Group U]
    {c : U} (hc : c ∈ Subgroup.center U) (g h : U) : ⁅g, h * c⁆ = ⁅g, h⁆ := by
  have e : g * c * g⁻¹ = c := by
    rw [Subgroup.mem_center_iff.mp hc g, mul_inv_cancel_right]
  simp only [commutatorElement_def, mul_inv_rev]
  calc g * (h * c) * g⁻¹ * (c⁻¹ * h⁻¹)
      = (g * h * g⁻¹) * (g * c * g⁻¹) * (c⁻¹ * h⁻¹) := by group
    _ = (g * h * g⁻¹) * c * c⁻¹ * h⁻¹ := by rw [e]; group
    _ = g * h * g⁻¹ * h⁻¹ := by group

private lemma nbrPSL_commutator_sup_central_le {U : Type} [Group U] {K Z : Subgroup U}
    (hZ : Z ≤ Subgroup.center U) : ⁅K ⊔ Z, K ⊔ Z⁆ ≤ ⁅K, K⁆ := by
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  obtain ⟨k, hk, z, hz, rfl⟩ := (nbrPSL_mem_sup_central hZ).1 hx
  obtain ⟨k', hk', z', hz', rfl⟩ := (nbrPSL_mem_sup_central hZ).1 hy
  rw [nbrPSL_commutatorElement_mul_central_left (hZ hz),
    nbrPSL_commutatorElement_mul_central_right (hZ hz')]
  exact Subgroup.commutator_mem_commutator hk hk'

private lemma nbrPSL_perfect_le_of_le_sup_center {U : Type} [Group U] {J K Z : Subgroup U}
    (hZ : Z ≤ Subgroup.center U) (hle : J ≤ K ⊔ Z) (hperf : commutator ↥J = ⊤) : J ≤ K := by
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  have hmap2 : Subgroup.map (Subgroup.subtype J) (commutator ↥J) = ⁅J, J⁆ := by
    have hc : commutator ↥J = ⁅(⊤ : Subgroup ↥J), ⊤⁆ := rfl
    rw [hc, Subgroup.map_commutator]
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hJle : J ≤ ⁅J, J⁆ := by
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥J) ∈ commutator ↥J := by rw [hperf]; trivial
    have hxm : x ∈ Subgroup.map (Subgroup.subtype J) (commutator ↥J) :=
      ⟨⟨x, hx⟩, hx', rfl⟩
    rwa [hmap2] at hxm
  have hcommK : ⁅K ⊔ Z, K ⊔ Z⁆ ≤ K := by
    refine (nbrPSL_commutator_sup_central_le hZ).trans ?_
    simpa using Subgroup.commutator_le_sup K K
  exact hJle.trans ((Subgroup.commutator_mono hle hle).trans hcommK)

private lemma nbrPSL_le_of_le_sup_center {U : Type} [Group U] {R K : Subgroup U}
    (hRK : R ≤ K ⊔ Subgroup.center U) (hsq : ∀ r ∈ R, r ^ 2 = 1)
    (hodd : ∀ z ∈ Subgroup.center U, Odd (orderOf z)) : R ≤ K := by
  intro r hr
  have hmem : ∃ k ∈ K, ∃ z ∈ Subgroup.center U, k * z = r := by
    have h := hRK hr
    have hset := Subgroup.mul_normal K (Subgroup.center U)
    exact Set.mem_mul.mp (hset ▸ h)
  obtain ⟨k, hk, z, hz, hkz⟩ := hmem
  have hzc : z ∈ Subgroup.center U := hz
  have hcomm : Commute k z := Subgroup.mem_center_iff.mp hzc k
  have hsqr : (k * z) ^ 2 = 1 := by rw [hkz]; exact hsq r hr
  have hk2z2 : k ^ 2 * z ^ 2 = 1 := by
    have h : (k * z) ^ 2 = k ^ 2 * z ^ 2 := by
      rw [pow_two, pow_two, pow_two]
      calc (k * z) * (k * z) = k * (z * k) * z := by group
        _ = k * (k * z) * z := by rw [hcomm.eq.symm]
        _ = (k * k) * (z * z) := by group
    rw [h] at hsqr
    exact hsqr
  have hz2 : z ^ 2 = (k ^ 2)⁻¹ := by
    calc z ^ 2 = (k ^ 2)⁻¹ * (k ^ 2 * z ^ 2) := by rw [inv_mul_cancel_left]
      _ = (k ^ 2)⁻¹ * 1 := by rw [hk2z2]
      _ = (k ^ 2)⁻¹ := by rw [mul_one]
  have hz2K : z ^ 2 ∈ K := by
    rw [hz2]
    exact K.inv_mem (K.pow_mem hk 2)
  obtain ⟨t, ht⟩ := hodd z hzc
  have hzpow : (z ^ 2) ^ (t + 1) = z := by
    rw [← pow_mul]
    have h2 : 2 * (t + 1) = orderOf z + 1 := by rw [ht]; ring
    rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
  have hzK : z ∈ K := by
    rw [← hzpow]
    exact K.pow_mem hz2K (t + 1)
  rw [← hkz]
  exact K.mul_mem hk hzK

private lemma nbrPSL_conj_rootGroup_sq_one {m : ℕ} {F : Type} [Field F] [CharP F 2]
    {β : Fin m → ℤ} (hβ : β ∈ (SpecialLinear.rootDatum m F).roots)
    (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    ∀ x ∈ ((SpecialLinear.rootDatum m F).rootGroup β).map (MulAut.conj u).toMonoidHom,
      x ^ 2 = 1 := by
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  have hg' : g ∈ SpecialLinear.rootSubgroup m F (SpecialLinear.idx_spec m hβ).1 := by
    rwa [← SpecialLinear.rootGroup_eq_idx m F hβ]
  obtain ⟨c, hc⟩ :=
    (SpecialLinear.mem_rootSubgroup (SpecialLinear.idx_spec m hβ).1 g).mp hg'
  rw [← hc]
  have ht : (Matrix.SpecialLinearGroup.transvection (SpecialLinear.idx_spec m hβ).1 c) ^ 2 = 1 := by
    rw [pow_two, ← Matrix.SpecialLinearGroup.transvection_add,
      show c + c = 0 from by rw [← two_mul, CharTwo.two_eq_zero, zero_mul],
      Matrix.SpecialLinearGroup.transvection_coeff_zero]
  rw [← map_pow, ht, map_one]

private lemma nbrPSL_stepA
    {X : Type} [Group X] [Finite X] (m f : ℕ) (ψ : (ggU .PSL (m + 1) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .PSL (m + 1) f ψ p G₀ B₁ D J L x) :
    ∃ (S : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
      (J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))),
      (∀ s ∈ S, ∀ s' ∈ S, Commute s s') ∧ (∀ s ∈ S, Odd (orderOf s)) ∧
        IsComponentOf J' ((Subgroup.centralizer S).comap Matrix.SpecialLinearGroup.toGL) ∧
        J'.map ψ = J ∧
        (∀ s : GL (Fin (m + 1)) (GaloisField 2 f),
          (∃ d ∈ D, IsGLLift Matrix.SpecialLinearGroup.toGL ψ s d) → s ∈ S) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hadm : StatedLieAdmissible .PSL (m + 1) 2 f := by
    rcases h3 with ⟨_, hscm⟩ | ⟨hn0, hmem, _⟩ | ⟨hn0, hmem, _⟩ | ⟨hn0, hmem, _⟩
    · exact hscm.1
    · exact absurd hmem (by decide)
    · exact absurd hmem (by decide)
    · exact absurd hmem (by decide)
  have hadm' := hadm
  rcases hadm with ⟨-, hf, hn2, -⟩
  have hB₁N : B₁ ≤ Subgroup.normalizer (ψ.range : Set X) := by rw [h1]; exact h7
  have hB₁ : ∀ b ∈ B₁, GGPsiInnerDiag (SpecialLinear.rootDatum m (GaloisField 2 f)) ψ b :=
    fun b hb => h8 b hb
  have hJcomp : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set X)) := by
    rw [h1]; exact h15
  have hHN : p ∣ 2 ^ f - 1 → B₁ ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥ ∧
      p ^ ((m + 1) - 3) ≤ Nat.card B₁ := by
    intro hpdiv
    have h := h30 (Or.inl ⟨rfl, hpdiv⟩)
    rw [← h1] at h
    exact h
  let P : GL (Fin (m + 1)) (GaloisField 2 f) → Prop := fun _ => True
  have hlift : ∀ d ∈ D, ∃ s : GL (Fin (m + 1)) (GaloisField 2 f),
      P s ∧ IsGLLift Matrix.SpecialLinearGroup.toGL ψ s d := by
    intro d hd
    have hdB : d ∈ B₁ := h11 hd
    have hdN : d ∈ Subgroup.normalizer (ψ.range : Set X) := hB₁N hdB
    have hdID : GGPsiInnerDiag (SpecialLinear.rootDatum m (GaloisField 2 f)) ψ d := h8 d hdB
    obtain ⟨s, hs⟩ := exists_isGLLift_PSL m (GaloisField 2 f) ψ h2 hdN hdID
    exact ⟨s, trivial, hs⟩
  let S : Set (GL (Fin (m + 1)) (GaloisField 2 f)) :=
    {s | P s ∧ ∃ d ∈ D, IsGLLift Matrix.SpecialLinearGroup.toGL ψ s d}
  obtain ⟨J', hJ'comp, hJ'map⟩ :=
    StepA.exists_isComponentOf_comap_lift_of_isGLLift
      Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective
      ψ h2 P hJcomp hlift
  have hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s' := by
    intro s hs s' hs'
    obtain ⟨-, d, hd, hslift⟩ := hs
    obtain ⟨-, d', hd', hslift'⟩ := hs'
    exact isGLLift_commute_PSL m f ψ h2 hadm' h5 h6 hB₁N hB₁ h9 h10 hHN
      (h11 hd) (h11 hd') hslift hslift'
  have hodd : ∀ s ∈ S, Odd (orderOf s) := by
    intro s hs
    obtain ⟨-, d, hd, hslift⟩ := hs
    have hdB : d ∈ B₁ := h11 hd
    have hdpow : d ^ p = 1 := h9.2 d hdB
    have hslift_pow : IsGLLift Matrix.SpecialLinearGroup.toGL ψ (s ^ p) (d ^ p) :=
      hslift.pow p
    rw [hdpow] at hslift_pow
    obtain ⟨c, hc⟩ := isGLLift_unique_PSL m (GaloisField 2 f) ψ h2 hslift_pow
      (isGLLift_one (j := Matrix.SpecialLinearGroup.toGL) (ψ := ψ))
    have hzmat : ((s ^ p : GL (Fin (m + 1)) (GaloisField 2 f)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) =
        Matrix.scalar (Fin (m + 1)) c := by simpa using hc
    have hunit_sp : IsUnit (((s ^ p : GL (Fin (m + 1)) (GaloisField 2 f)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))) := ⟨s ^ p, rfl⟩
    have hscalar : IsUnit (Matrix.scalar (Fin (m + 1)) c) := hzmat ▸ hunit_sp
    have hcne : c ≠ 0 := by
      have hdiag : IsUnit (fun _ : Fin (m + 1) => c) :=
        (Matrix.isUnit_diagonal (v := fun _ : Fin (m + 1) => c)).mp hscalar
      exact IsUnit.ne_zero ((Pi.isUnit_iff.mp hdiag) ⟨0, Nat.succ_pos m⟩)
    let u : (GaloisField 2 f)ˣ := Units.mk0 c hcne
    have hscalar_eq : (s ^ p : GL (Fin (m + 1)) (GaloisField 2 f)) =
        Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) u := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, hzmat]
      simp [u]
    have hspk : s ^ (p * Nat.card (GaloisField 2 f)ˣ) = 1 := by
      rw [pow_mul, hscalar_eq, ← map_pow,
        orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard u), map_one]
    have hdvd : orderOf s ∣ p * Nat.card (GaloisField 2 f)ˣ :=
      orderOf_dvd_iff_pow_eq_one.mpr hspk
    have hcard : Nat.card (GaloisField 2 f)ˣ = 2 ^ f - 1 := by
      rw [Nat.card_units, GaloisField.card 2 f (by omega)]
    have hpodd : Odd p := h5.odd_of_ne_two h6
    have hodd2 : Odd (2 ^ f - 1) :=
      Nat.Even.sub_odd Nat.one_le_two_pow
        (even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))) odd_one
    have hoddprod : Odd (p * Nat.card (GaloisField 2 f)ˣ) := by
      rw [hcard]; exact hpodd.mul hodd2
    exact Odd.of_dvd_nat hoddprod hdvd
  have hSfull : ∀ s : GL (Fin (m + 1)) (GaloisField 2 f),
      (∃ d ∈ D, IsGLLift Matrix.SpecialLinearGroup.toGL ψ s d) → s ∈ S := by
    intro s hs
    obtain ⟨d, hd, hsl⟩ := hs
    exact ⟨trivial, d, hd, hsl⟩
  exact ⟨S, J', hS, hodd, hJ'comp, hJ'map, hSfull⟩

private lemma nbrPSL_blockDegree_J
    {X : Type} [Group X] [Finite X] (m f : ℕ) (ψ : (ggU .PSL (m + 1) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .PSL (m + 1) f ψ p G₀ B₁ D J L x)
    {S : Set (GL (Fin (m + 1)) (GaloisField 2 f))}
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e_J : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hJ'block : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e_J,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e_J⁆)
    (hJ'map : J'.map ψ = J) :
    blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hadm : StatedLieAdmissible .PSL (m + 1) 2 f := by
    rcases h3 with ⟨_, hscm⟩ | ⟨hn0, hmem, _⟩ | ⟨hn0, hmem, _⟩ | ⟨hn0, hmem, _⟩
    · exact hscm.1
    · exact absurd hmem (by decide)
    · exact absurd hmem (by decide)
    · exact absurd hmem (by decide)
  rcases hadm with ⟨-, hf, hn2, -⟩
  by_contra h
  have h' : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J :=
    not_lt.mp h
  have hfe := ggSixLSevenFieldExtCase_PSL m f hf ψ h2 S hS hodd heJ hJ'block h'
  exact h29 (hJ'map ▸ hfe)

private lemma nbrPSL_neighbourBlock
    {X : Type} [Group X] [Finite X] (m f : ℕ) (ψ : (ggU .PSL (m + 1) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hH : GGSixPosHyp .PSL (m + 1) f ψ p G₀ B₁ D J L x)
    (e : X) (heD : e ∈ D) (K : Subgroup X) (hKG0 : K ≤ G₀)
    (hKcomp : IsComponentOf K (Subgroup.centralizer {e})) (hJK : J ≤ K)
    {S : Set (GL (Fin (m + 1)) (GaloisField 2 f))}
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    (hJ'comp : IsComponentOf J'
      ((Subgroup.centralizer S).comap Matrix.SpecialLinearGroup.toGL))
    (hJ'map : J'.map ψ = J)
    (hSfull : ∀ s : GL (Fin (m + 1)) (GaloisField 2 f),
      (∃ d ∈ D, IsGLLift Matrix.SpecialLinearGroup.toGL ψ s d) → s ∈ S) :
    ∃ (S_e : Set (GL (Fin (m + 1)) (GaloisField 2 f)))
      (K' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
      (ε : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)),
      S_e ⊆ S ∧ (∀ s ∈ S_e, ∀ s' ∈ S_e, Commute s s') ∧ (∀ s ∈ S_e, Odd (orderOf s)) ∧
        IsComponentOf K' ((Subgroup.centralizer S_e).comap Matrix.SpecialLinearGroup.toGL) ∧
        K'.map ψ = K ∧
        IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S_e)) ε ∧
        IsComponentOf K' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S_e ε,
          glBlockCentralizer Matrix.SpecialLinearGroup.toGL S_e ε⁆ ∧
        J' ≤ K' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hadm : StatedLieAdmissible .PSL (m + 1) 2 f := by
    rcases h3 with ⟨_, hscm⟩ | ⟨hn0, hmem, _⟩ | ⟨hn0, hmem, _⟩ | ⟨hn0, hmem, _⟩
    · exact hscm.1
    · exact absurd hmem (by decide)
    · exact absurd hmem (by decide)
    · exact absurd hmem (by decide)
  rcases hadm with ⟨-, hf, hn2, -⟩
  have hKcomp' : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer ({e} : Set X)) := by
    rw [h1]
    exact IsComponentOf.of_le_of_le hKcomp (le_inf hKG0 hKcomp.1) inf_le_right
  have hcent : Subgroup.centralizer ((Subgroup.zpowers e : Set X)) =
      Subgroup.centralizer ({e} : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hKcomp'' : IsComponentOf K
      (ψ.range ⊓ Subgroup.centralizer ((Subgroup.zpowers e : Set X))) := by
    rw [hcent]
    exact hKcomp'
  let S_e : Set (GL (Fin (m + 1)) (GaloisField 2 f)) :=
    {s | True ∧ ∃ d ∈ Subgroup.zpowers e, IsGLLift Matrix.SpecialLinearGroup.toGL ψ s d}
  have hlift_e : ∀ d ∈ Subgroup.zpowers e, ∃ s : GL (Fin (m + 1)) (GaloisField 2 f),
      True ∧ IsGLLift Matrix.SpecialLinearGroup.toGL ψ s d := by
    intro d hd
    have hdD : d ∈ D := Subgroup.zpowers_le.mpr heD hd
    have hdB : d ∈ B₁ := h11 hdD
    have hdN : d ∈ Subgroup.normalizer (ψ.range : Set X) := by rw [h1]; exact h7 hdB
    have hdID : GGPsiInnerDiag (SpecialLinear.rootDatum m (GaloisField 2 f)) ψ d := h8 d hdB
    obtain ⟨s, hs⟩ := exists_isGLLift_PSL m (GaloisField 2 f) ψ h2 hdN hdID
    exact ⟨s, trivial, hs⟩
  obtain ⟨K', hK'comp, hK'map⟩ :=
    StepA.exists_isComponentOf_comap_lift_of_isGLLift
      Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective
      ψ h2 (fun _ => True) hKcomp'' hlift_e
  have hSe : S_e ⊆ S := by
    intro s hs
    obtain ⟨-, d, hd, hsl⟩ := hs
    exact hSfull s ⟨d, Subgroup.zpowers_le.mpr heD hd, hsl⟩
  have hS_e : ∀ s ∈ S_e, ∀ s' ∈ S_e, Commute s s' :=
    fun s hs s' hs' => hS s (hSe hs) s' (hSe hs')
  have hodd_e : ∀ s ∈ S_e, Odd (orderOf s) := fun s hs => hodd s (hSe hs)
  obtain ⟨ε, hε, hK'block⟩ :=
    exists_isComponentOf_glBlockCentralizer_PSL m (GaloisField 2 f) S_e hS_e hK'comp
  have hmapJK : J'.map ψ ≤ K'.map ψ := by
    calc J'.map ψ = J := hJ'map
      _ ≤ K := hJK
      _ = K'.map ψ := hK'map.symm
  have hleJK : J' ≤ K' ⊔ ψ.ker := Subgroup.map_le_map_iff.mp hmapJK
  have hperf : commutator ↥J' = ⊤ := hJ'comp.2.2.1
  have hJK' : J' ≤ K' := nbrPSL_perfect_le_of_le_sup_center h2 hleJK hperf
  exact ⟨S_e, K', ε, hSe, hS_e, hodd_e, hK'comp, hK'map, hε, hK'block, hJK'⟩

private lemma nbrPSL_commute_adjoin {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} {T : GL ι F} (hT : T ∈ Subgroup.centralizer S)
    {ε : Matrix ι ι F} (hε : ε ∈ Algebra.adjoin F (Units.val '' S)) :
    (T : Matrix ι ι F) * ε = ε * (T : Matrix ι ι F) := by
  have hgen : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F ({(T : Matrix ι ι F)} : Set (Matrix ι ι F)) :
        Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact congrArg (fun u : GL ι F => (u : Matrix ι ι F))
      ((Subgroup.mem_centralizer_iff.mp hT) s hs).symm
  have hA : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F ({(T : Matrix ι ι F)} : Set (Matrix ι ι F)) :=
    Algebra.adjoin_le hgen
  exact (Subalgebra.mem_centralizer_iff F).mp (hA hε) (T : Matrix ι ι F)
    (Set.mem_singleton (T : Matrix ι ι F))

private lemma nbrPSL_adjoin_commute {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {a b : Matrix ι ι F} (ha : a ∈ Algebra.adjoin F (Units.val '' S))
    (hb : b ∈ Algebra.adjoin F (Units.val '' S)) : a * b = b * a := by
  have hgen : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F (Units.val '' S) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    obtain ⟨s', hs', rfl⟩ := hy
    exact congrArg (fun u : GL ι F => (u : Matrix ι ι F)) ((hS s hs s' hs').eq).symm
  have hA : Algebra.adjoin F (Units.val '' S) ≤ Subalgebra.centralizer F (Units.val '' S) :=
    Algebra.adjoin_le hgen
  have haC : a ∈ Subalgebra.centralizer F (Units.val '' S) := hA ha
  refine Algebra.adjoin_induction (p := fun b _ => a * b = b * a) ?_ ?_ ?_ ?_ hb
  · intro x hx
    exact ((Subalgebra.mem_centralizer_iff F).mp haC x hx).symm
  · intro r
    exact (Algebra.commute_algebraMap_left r a).eq.symm
  · intro x y _ _ ihx ihy
    rw [mul_add, add_mul, ihx, ihy]
  · intro x y _ _ ihx ihy
    rw [← mul_assoc, ihx, mul_assoc, ihy, ← mul_assoc]

private lemma nbrPSL_eJ_mul_eps
    {m f : ℕ} {S S_e : Set (GL (Fin (m + 1)) (GaloisField 2 f))} (hSe : S_e ⊆ S)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e_J ε : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hε : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S_e)) ε)
    {J' K' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    (hJ' : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e_J,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e_J⁆)
    (hK' : IsComponentOf K' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S_e ε,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S_e ε⁆)
    (hJK : J' ≤ K') : e_J * ε = e_J := by
  have hAe_le : Algebra.adjoin (GaloisField 2 f) (Units.val '' S_e) ≤
      Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono hSe)
  have hεA : ε ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) := hAe_le hε.1
  have hcommA : ∀ a ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S),
      ∀ b ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S), a * b = b * a :=
    fun a ha b hb => nbrPSL_adjoin_commute hS ha hb
  have heJε_mem : e_J * ε ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
    Subalgebra.mul_mem _ heJ.1 hεA
  have heJε_idem : IsIdempotentElem (e_J * ε) := by
    rw [IsIdempotentElem]
    calc (e_J * ε) * (e_J * ε) = e_J * (ε * (e_J * ε)) := by rw [mul_assoc]
      _ = e_J * ((ε * e_J) * ε) := by rw [mul_assoc]
      _ = e_J * ((e_J * ε) * ε) := by rw [hcommA ε hεA e_J heJ.1]
      _ = e_J * (e_J * (ε * ε)) := by rw [mul_assoc]
      _ = e_J * (e_J * ε) := by rw [hε.2.1.eq]
      _ = (e_J * e_J) * ε := by rw [← mul_assoc]
      _ = e_J * ε := by rw [heJ.2.1.eq]
  have heJε_below : (e_J * ε) * e_J = e_J * ε := by
    rw [mul_assoc, hcommA ε hεA e_J heJ.1, ← mul_assoc, heJ.2.1.eq]
  have heJε : e_J * ε = e_J := by
    rcases heJ.2.2.2 (e_J * ε) heJε_mem heJε_idem heJε_below with h0 | heq
    · exfalso
      have hJ'bot : J' = ⊥ := by
        rw [eq_bot_iff]
        intro u hu
        have huG : u ∈ glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e_J := by
          have h := (Subgroup.commutator_le_sup _ _) (hJ'.1 hu)
          rwa [sup_idem] at h
        have huGe : u ∈ glBlockCentralizer Matrix.SpecialLinearGroup.toGL S_e ε := by
          have h := (Subgroup.commutator_le_sup _ _) (hK'.1 (hJK hu))
          rwa [sup_idem] at h
        have huG' : Matrix.SpecialLinearGroup.toGL u ∈
            Subgroup.centralizer S ⊓ glFixing (1 - e_J) := Subgroup.mem_comap.mp huG
        have huGe' : Matrix.SpecialLinearGroup.toGL u ∈
            Subgroup.centralizer S_e ⊓ glFixing (1 - ε) := Subgroup.mem_comap.mp huGe
        have huc : Matrix.SpecialLinearGroup.toGL u ∈ Subgroup.centralizer S := huG'.1
        have hfixJ : ((Matrix.SpecialLinearGroup.toGL u :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * (1 - e_J)) = 1 - e_J :=
          huG'.2
        have hfixe : ((Matrix.SpecialLinearGroup.toGL u :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * (1 - ε)) = 1 - ε :=
          huGe'.2
        have hcomm_u : ((Matrix.SpecialLinearGroup.toGL u :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * e_J) =
            e_J * ((Matrix.SpecialLinearGroup.toGL u :
              Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))) :=
          nbrPSL_commute_adjoin (S := S) huc heJ.1
        have h1 : e_J * (1 - ε) = e_J := by rw [mul_sub, mul_one, h0, sub_zero]
        have hmat_eJ : ((Matrix.SpecialLinearGroup.toGL u :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * e_J) = e_J := by
          calc ((Matrix.SpecialLinearGroup.toGL u :
                Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * e_J)
              = ((Matrix.SpecialLinearGroup.toGL u :
                  Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) *
                  (e_J * (1 - ε))) := by rw [h1]
            _ = (((Matrix.SpecialLinearGroup.toGL u :
                  Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * e_J) * (1 - ε)) := by
                  rw [mul_assoc]
            _ = ((e_J * (Matrix.SpecialLinearGroup.toGL u :
                  Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))) * (1 - ε)) := by
                  rw [hcomm_u]
            _ = e_J * ((Matrix.SpecialLinearGroup.toGL u :
                  Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * (1 - ε)) := by
                  rw [mul_assoc]
            _ = e_J * (1 - ε) := by rw [hfixe]
            _ = e_J := h1
        have hmat_one : ((Matrix.SpecialLinearGroup.toGL u :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))) = 1 := by
          calc ((Matrix.SpecialLinearGroup.toGL u :
                Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)))
              = ((Matrix.SpecialLinearGroup.toGL u :
                  Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * 1) := by rw [mul_one]
            _ = ((Matrix.SpecialLinearGroup.toGL u :
                  Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) *
                  (e_J + (1 - e_J))) := by rw [add_sub_cancel]
            _ = ((Matrix.SpecialLinearGroup.toGL u :
                  Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * e_J +
                  (Matrix.SpecialLinearGroup.toGL u :
                  Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * (1 - e_J)) := by
                  rw [mul_add]
            _ = e_J + (1 - e_J) := by rw [hmat_eJ, hfixJ]
            _ = 1 := by rw [add_sub_cancel]
        have hu1 : u = 1 := by
          apply Matrix.SpecialLinearGroup.toGL_injective
          rw [map_one]
          exact Units.ext hmat_one
        exact Subgroup.mem_bot.mpr hu1
      have hnt : Nontrivial ↥J' := CFSG.ComponentClassification.Quasisimple.nontrivial hJ'.2.2
      exact (Subgroup.nontrivial_iff_ne_bot J').mp hnt hJ'bot
    · exact heq
  exact heJε

private lemma nbrPSL_blockDegree_K
    {m f : ℕ} {S S_e : Set (GL (Fin (m + 1)) (GaloisField 2 f))} (hSe : S_e ⊆ S)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e_J ε : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (heJ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J)
    (hε : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S_e)) ε)
    {J' K' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    (hJ' : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e_J,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e_J⁆)
    (hK' : IsComponentOf K' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S_e ε,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S_e ε⁆)
    (hJK : J' ≤ K')
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J < 2) :
    blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S_e)) ε < 2 := by
  have hS_e : ∀ s ∈ S_e, ∀ s' ∈ S_e, Commute s s' :=
    fun s hs s' hs' => hS s (hSe hs) s' (hSe hs')
  have hodd_e : ∀ s ∈ S_e, Odd (orderOf s) := fun s hs => hodd s (hSe hs)
  have hAe_le : Algebra.adjoin (GaloisField 2 f) (Units.val '' S_e) ≤
      Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono hSe)
  have hεA : ε ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) := hAe_le hε.1
  have hcommA : ∀ a ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S),
      ∀ b ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S), a * b = b * a :=
    fun a ha b hb => nbrPSL_adjoin_commute hS ha hb
  have heJε : e_J * ε = e_J := nbrPSL_eJ_mul_eps hSe hS heJ hε hJ' hK' hJK
  obtain ⟨Ke, hKeField, hKeAlg, hKefin, πe, hπe_surj, hπe_ker, hπe_fin⟩ :=
    exists_blockField (F := GaloisField 2 f) hS_e hodd_e hε
  letI : Field Ke := hKeField
  letI : Algebra (GaloisField 2 f) Ke := hKeAlg
  letI : Finite Ke := hKefin
  obtain ⟨KJ, hKJField, hKJAlg, hKJfin, πJ, hπJ_surj, hπJ_ker, hπJ_fin⟩ :=
    exists_blockField (F := GaloisField 2 f) hS hodd heJ
  letI : Field KJ := hKJField
  letI : Algebra (GaloisField 2 f) KJ := hKJAlg
  letI : Finite KJ := hKJfin
  let φ : Algebra.adjoin (GaloisField 2 f) (Units.val '' S_e) →ₐ[GaloisField 2 f] KJ :=
    πJ.comp (Subalgebra.inclusion hAe_le)
  have hker_le : RingHom.ker πe ≤ RingHom.ker φ := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    have haε : (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * ε = 0 :=
      (hπe_ker a).mp ha
    have heJ_eq : e_J = ε * e_J := (heJε.symm).trans (hcommA e_J heJ.1 ε hεA)
    have hae : (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * e_J = 0 := by
      calc (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * e_J
          = (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * (ε * e_J) :=
            congrArg (fun x => (a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * x)
              heJ_eq
        _ = ((a : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * ε) * e_J := by
            rw [mul_assoc]
        _ = 0 := by rw [haε, zero_mul]
    exact (hπJ_ker (Subalgebra.inclusion hAe_le a)).mpr (by simpa using hae)
  let lift : (Algebra.adjoin (GaloisField 2 f) (Units.val '' S_e) ⧸ RingHom.ker πe)
      →ₐ[GaloisField 2 f] Ke :=
    Ideal.Quotient.liftₐ (RingHom.ker πe) πe (fun a ha => ha)
  have hlift_surj : Function.Surjective lift := by
    intro x
    obtain ⟨a, rfl⟩ := hπe_surj x
    exact ⟨Ideal.Quotient.mkₐ (GaloisField 2 f) (RingHom.ker πe) a, by
      rw [show lift (Ideal.Quotient.mkₐ (GaloisField 2 f) (RingHom.ker πe) a) = πe a from
        Ideal.Quotient.liftₐ_apply _ _ _ _]⟩
  have hlift_inj : Function.Injective lift := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective (GaloisField 2 f) (RingHom.ker πe) x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mkₐ_surjective (GaloisField 2 f) (RingHom.ker πe) y
    rw [show lift (Ideal.Quotient.mkₐ (GaloisField 2 f) (RingHom.ker πe) a) = πe a from
        Ideal.Quotient.liftₐ_apply _ _ _ _,
      show lift (Ideal.Quotient.mkₐ (GaloisField 2 f) (RingHom.ker πe) b) = πe b from
        Ideal.Quotient.liftₐ_apply _ _ _ _] at hxy
    have hab : a - b ∈ RingHom.ker πe := by
      rw [RingHom.mem_ker, map_sub, hxy, sub_self]
    have : Ideal.Quotient.mkₐ (GaloisField 2 f) (RingHom.ker πe) a =
        Ideal.Quotient.mkₐ (GaloisField 2 f) (RingHom.ker πe) b := by
      change Ideal.Quotient.mk (RingHom.ker πe) a = Ideal.Quotient.mk (RingHom.ker πe) b
      rw [Ideal.Quotient.eq]
      exact hab
    exact this
  let qe : (Algebra.adjoin (GaloisField 2 f) (Units.val '' S_e) ⧸ RingHom.ker πe)
      ≃ₐ[GaloisField 2 f] Ke :=
    AlgEquiv.ofBijective lift ⟨hlift_inj, hlift_surj⟩
  let ψ : Ke →ₐ[GaloisField 2 f] KJ :=
    (Ideal.Quotient.liftₐ (RingHom.ker πe) φ hker_le).comp qe.symm.toAlgHom
  have hψ_inj : Function.Injective ψ := by
    intro x y hxy
    have hmem : x - y ∈ RingHom.ker ψ := by
      rw [RingHom.mem_ker, map_sub, hxy, sub_self]
    have hbot : RingHom.ker ψ = ⊥ := by
      rcases Ideal.eq_bot_or_top (RingHom.ker ψ) with h | h
      · exact h
      · exfalso
        have h1 : ψ (1 : Ke) = 0 := by
          have : (1 : Ke) ∈ RingHom.ker ψ := by rw [h]; trivial
          rwa [RingHom.mem_ker] at this
        rw [map_one] at h1
        exact one_ne_zero h1
    rw [hbot, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  have hfin : Module.finrank (GaloisField 2 f) Ke ≤ Module.finrank (GaloisField 2 f) KJ :=
    LinearMap.finrank_le_finrank_of_injective (f := ψ.toLinearMap) hψ_inj
  have hdeg1 : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J = 1 := by
    let M : Submodule (GaloisField 2 f) (Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) :=
      (Subalgebra.toSubmodule (Algebra.adjoin (GaloisField 2 f) (Units.val '' S))).map
        (LinearMap.mulRight (GaloisField 2 f) e_J)
    have heM : e_J ∈ M := by
      rw [Submodule.mem_map]
      refine ⟨1, ?_, ?_⟩
      · simpa using (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)).one_mem
      · rw [LinearMap.mulRight_apply, one_mul]
    have hne : (⟨e_J, heM⟩ : M) ≠ 0 := by
      intro h
      exact heJ.2.2.1 (by simpa using congrArg Subtype.val h)
    haveI : Nontrivial M := ⟨⟨⟨e_J, heM⟩, 0, hne⟩⟩
    have hpos : 0 < Module.finrank (GaloisField 2 f) M :=
      Module.finrank_pos_iff.mpr inferInstance
    change Module.finrank (GaloisField 2 f) M = 1
    have hdegM : Module.finrank (GaloisField 2 f) M < 2 := hdeg
    omega
  rw [← hπe_fin]
  calc Module.finrank (GaloisField 2 f) Ke
      ≤ Module.finrank (GaloisField 2 f) KJ := hfin
    _ = blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e_J := hπJ_fin
    _ = 1 := hdeg1
    _ < 2 := by norm_num

private lemma nbrPSL_rootImage
    {X : Type} [Group X] (m f : ℕ) (hf : 1 ≤ f) (ψ : (ggU .PSL (m + 1) f).K →* X)
    (hψ : ψ.ker ≤ Subgroup.center (ggU .PSL (m + 1) f).K)
    {K' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    {K : Subgroup X} (hK'map : K'.map ψ = K)
    {R : Subgroup X} (hRK : R ≤ K)
    {β' : Fin (ggU .PSL (m + 1) f).D.rank → ℤ}
    (hβ'root : β' ∈ (ggU .PSL (m + 1) f).D.roots) (u' : (ggU .PSL (m + 1) f).K)
    (hR' : R = ggRootSub (ggU .PSL (m + 1) f).D ψ β' u')
    {k : ℕ} {ι : (ggU .PSL (k + 1) f).K →* (ggU .PSL (m + 1) f).K}
    (hclosure : ∀ v₀ φ₀ : Fin (m + 1) → GaloisField 2 f, v₀ ≠ 0 → φ₀ ≠ 0 → φ₀ ⬝ᵥ v₀ = 0 →
      matTransvGroup v₀ φ₀ ≤ K'.map Matrix.SpecialLinearGroup.toGL →
      ∃ (β : Fin (ggU .PSL (k + 1) f).D.rank → ℤ) (u : (ggU .PSL (k + 1) f).K),
        β ∈ (ggU .PSL (k + 1) f).D.roots ∧ GGLongRoot (ggU .PSL (k + 1) f).D β ∧
        ((((ggU .PSL (k + 1) f).D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ι).map
          Matrix.SpecialLinearGroup.toGL = matTransvGroup v₀ φ₀) :
    ∃ (β'' : Fin (ggU .PSL (k + 1) f).D.rank → ℤ) (u'' : (ggU .PSL (k + 1) f).K),
      β'' ∈ (ggU .PSL (k + 1) f).D.roots ∧ GGLongRoot (ggU .PSL (k + 1) f).D β'' ∧
      R = ggRootSub (ggU .PSL (k + 1) f).D (ψ.comp ι) β'' u'' := by
  let Rt : Subgroup (ggU .PSL (m + 1) f).K :=
    ((ggU .PSL (m + 1) f).D.rootGroup β').map (MulAut.conj u').toMonoidHom
  have hRtmap : Rt.map ψ = R := by rw [hR']; rfl
  obtain ⟨v, φ, hv, hφ, hφv, hconv⟩ :=
    exists_matTransvGroup_eq_rootGroup_PSL m (GaloisField 2 f) hβ'root u'
  have hRtconv : Rt.map Matrix.SpecialLinearGroup.toGL = matTransvGroup v φ := by
    change (((SpecialLinear.rootDatum m (GaloisField 2 f)).rootGroup β').map
      (MulAut.conj u').toMonoidHom).map Matrix.SpecialLinearGroup.toGL = matTransvGroup v φ
    exact hconv
  have hsq : ∀ r ∈ Rt, r ^ 2 = 1 := fun r hr => nbrPSL_conj_rootGroup_sq_one hβ'root u' r hr
  have hoddZ : ∀ z ∈ Subgroup.center (ggU .PSL (m + 1) f).K, Odd (orderOf z) := by
    intro z hz
    let zs : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) := z
    change Odd (orderOf zs)
    have hzs : zs ∈ Subgroup.center
        (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) := hz
    obtain ⟨c, hc, hzc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hzs
    have hc0 : c ≠ 0 := by
      intro hc0
      have hc' : c ^ (m + 1) = 1 := by simpa using hc
      rw [hc0, zero_pow (Nat.succ_ne_zero m)] at hc'
      exact one_ne_zero hc'.symm
    have hcf : c ^ (2 ^ f - 1) = 1 := by
      haveI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
      have h := FiniteField.pow_card_sub_one_eq_one c hc0
      have hcard : Fintype.card (GaloisField 2 f) = 2 ^ f := by
        rw [← Nat.card_eq_fintype_card, GaloisField.card 2 f (by omega)]
      rwa [hcard] at h
    have hzpow : zs ^ (2 ^ f - 1) = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_pow, hzc.symm,
        ← map_pow, hcf, map_one]
    have hdvd : orderOf zs ∣ 2 ^ f - 1 := orderOf_dvd_iff_pow_eq_one.mpr hzpow
    have hodd2 : Odd (2 ^ f - 1) :=
      Nat.Even.sub_odd Nat.one_le_two_pow (even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega)))
        odd_one
    exact Odd.of_dvd_nat hodd2 hdvd
  have hRtK' : Rt ≤ K' := by
    have hmap : Rt.map ψ ≤ K'.map ψ := by
      calc Rt.map ψ = R := hRtmap
        _ ≤ K := hRK
        _ = K'.map ψ := hK'map.symm
    have hle : Rt ≤ K' ⊔ ψ.ker := Subgroup.map_le_map_iff.mp hmap
    exact nbrPSL_le_of_le_sup_center (le_trans hle (sup_le_sup_left hψ K')) hsq hoddZ
  have hmatK : matTransvGroup v φ ≤ K'.map Matrix.SpecialLinearGroup.toGL := by
    rw [← hRtconv]
    exact Subgroup.map_mono hRtK'
  obtain ⟨β'', u'', hβ''root, hlong'', hclosure_eq⟩ := hclosure v φ hv hφ hφv hmatK
  have hsubeq : (((ggU .PSL (k + 1) f).D.rootGroup β'').map
      (MulAut.conj u'').toMonoidHom).map ι = Rt := by
    apply Subgroup.map_injective Matrix.SpecialLinearGroup.toGL_injective
    exact hclosure_eq.trans hRtconv.symm
  refine ⟨β'', u'', hβ''root, hlong'', ?_⟩
  have hfinal : (((ggU .PSL (k + 1) f).D.rootGroup β'').map
        (MulAut.conj u'').toMonoidHom).map (ψ.comp ι) = R := by
    calc (((ggU .PSL (k + 1) f).D.rootGroup β'').map
          (MulAut.conj u'').toMonoidHom).map (ψ.comp ι)
        = ((((ggU .PSL (k + 1) f).D.rootGroup β'').map
            (MulAut.conj u'').toMonoidHom).map ι).map ψ :=
            (Subgroup.map_map _ ψ ι).symm
      _ = Rt.map ψ := by rw [hsubeq]
      _ = R := hRtmap
  exact hfinal.symm

private lemma nbrPSL_rootVia
    {X : Type} [Group X] (m f : ℕ) (ψ : (ggU .PSL (m + 1) f).K →* X)
    (hψ : ψ.ker ≤ Subgroup.center (ggU .PSL (m + 1) f).K)
    {K' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))}
    {K : Subgroup X} (hK'map : K'.map ψ = K)
    {k : ℕ} {ι : (ggU .PSL (k + 1) f).K →* (ggU .PSL (m + 1) f).K}
    (hι_center : ∀ y, ι y ∈ Subgroup.center (ggU .PSL (m + 1) f).K →
      y ∈ Subgroup.center (ggU .PSL (k + 1) f).K)
    (hι_range : ι.range = K')
    {R : Subgroup X} {β'' : Fin (ggU .PSL (k + 1) f).D.rank → ℤ}
    (u'' : (ggU .PSL (k + 1) f).K)
    (hR : R = ggRootSub (ggU .PSL (k + 1) f).D (ψ.comp ι) β'' u'') :
    GGRootVia (ggU .PSL (k + 1) f) K R β'' := by
  refine ⟨ψ.comp ι, ?_, ?_, u'', hR⟩
  · calc (ψ.comp ι).range = Subgroup.map ψ ι.range := MonoidHom.range_comp ψ ι
      _ = Subgroup.map ψ K' := by rw [hι_range]
      _ = K := hK'map
  · intro y hy
    apply hι_center
    apply hψ
    rw [MonoidHom.mem_ker]
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hy
    exact hy

private lemma nbrPSL_mul_e_eq_smul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {A : Subalgebra F (Matrix ι ι F)} {e : Matrix ι ι F} (he : IsPrimIdemIn A e)
    (hdeg : blockDegree A e < 2) : ∀ a ∈ A, ∃ c : F, a * e = c • e := by
  let M : Submodule F (Matrix ι ι F) := (Subalgebra.toSubmodule A).map (LinearMap.mulRight F e)
  have heM : e ∈ M := ⟨1, by simpa using A.one_mem, by rw [LinearMap.mulRight_apply, one_mul]⟩
  have hne : (⟨e, heM⟩ : M) ≠ 0 := by
    intro h
    exact he.2.2.1 (by simpa using congrArg Subtype.val h)
  haveI : Nontrivial M := ⟨⟨⟨e, heM⟩, 0, hne⟩⟩
  have hpos : 0 < Module.finrank F M := Module.finrank_pos_iff.mpr inferInstance
  have hlt : Module.finrank F M < 2 := hdeg
  have hfin : Module.finrank F M = 1 := by omega
  have hspan : M = Submodule.span F {e} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hfin heM he.2.2.1
  intro a ha
  have hae : a * e ∈ M := ⟨a, ha, by rw [LinearMap.mulRight_apply]⟩
  rw [hspan] at hae
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hae
  exact ⟨c, hc.symm⟩

private lemma nbrPSL_finrank_lt_of_mul_eq {n : ℕ} {F : Type} [Field F]
    {a b : Matrix (Fin n) (Fin n) F} (ha : IsIdempotentElem a) (hab : a * b = a)
    (hba : b * a = a) (hne : a ≠ b) :
    Module.finrank F (LinearMap.range (Matrix.toLin' a)) <
      Module.finrank F (LinearMap.range (Matrix.toLin' b)) := by
  have hle : LinearMap.range (Matrix.toLin' a) ≤ LinearMap.range (Matrix.toLin' b) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨Matrix.toLin' a y, by rw [← Matrix.toLin'_mul_apply, hba]⟩
  have hlt : LinearMap.range (Matrix.toLin' a) < LinearMap.range (Matrix.toLin' b) := by
    refine lt_of_le_of_ne hle fun heq => hne ?_
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    have hx : Matrix.toLin' b x ∈ LinearMap.range (Matrix.toLin' a) := by
      rw [heq]
      exact ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := hx
    have h1 : Matrix.toLin' a (Matrix.toLin' b x) = Matrix.toLin' a x := by
      rw [← Matrix.toLin'_mul_apply, hab]
    have h2 : Matrix.toLin' a (Matrix.toLin' a z) = Matrix.toLin' a z := by
      rw [← Matrix.toLin'_mul_apply, ha.eq]
    rw [← h1, ← hz, h2]
  exact Submodule.finrank_lt_finrank_of_lt hlt

private lemma nbrPSL_eq_one_of_range_top {n : ℕ} {F : Type} [Field F]
    {a : Matrix (Fin n) (Fin n) F} (ha : IsIdempotentElem a)
    (htop : LinearMap.range (Matrix.toLin' a) = ⊤) : a = 1 := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, hy⟩ : x ∈ LinearMap.range (Matrix.toLin' a) := by
    rw [htop]
    trivial
  rw [Matrix.toLin'_one, LinearMap.id_apply, ← hy, ← Matrix.toLin'_mul_apply, ha.eq]

private lemma nbrPSL_glBlockCentralizer_le {m f : ℕ}
    {S S_e : Set (GL (Fin (m + 1)) (GaloisField 2 f))} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    (heSe : e ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S_e)) :
    glBlockCentralizer Matrix.SpecialLinearGroup.toGL S_e e ≤
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e := by
  intro u hu
  obtain ⟨huc, hufix⟩ : Matrix.SpecialLinearGroup.toGL u ∈
      Subgroup.centralizer S_e ⊓ glFixing (1 - e) := Subgroup.mem_comap.mp hu
  have hfix : ((Matrix.SpecialLinearGroup.toGL u : GL (Fin (m + 1)) (GaloisField 2 f)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * (1 - e) = 1 - e := hufix
  have hcomm_e : ((Matrix.SpecialLinearGroup.toGL u : GL (Fin (m + 1)) (GaloisField 2 f)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * e =
      e * ((Matrix.SpecialLinearGroup.toGL u : GL (Fin (m + 1)) (GaloisField 2 f)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) :=
    nbrPSL_commute_adjoin (S := S_e) huc heSe
  refine Subgroup.mem_comap.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, hufix⟩
  intro s hs
  have hsA : (s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) ∈
      Algebra.adjoin (GaloisField 2 f) (Units.val '' S) := Algebra.subset_adjoin ⟨s, hs, rfl⟩
  obtain ⟨c, hc⟩ := nbrPSL_mul_e_eq_smul he hdeg _ hsA
  have hse : (s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) * e =
      e * (s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) :=
    nbrPSL_adjoin_commute hS hsA he.1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  set G := ((Matrix.SpecialLinearGroup.toGL u : GL (Fin (m + 1)) (GaloisField 2 f)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) with hGdef
  set Sm := (s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) with hSmdef
  have hG : G = G * e + (1 - e) := by
    have h := hfix
    rw [Matrix.mul_sub, Matrix.mul_one] at h
    calc G = (G - G * e) + G * e := by abel
      _ = (1 - e) + G * e := by rw [h]
      _ = G * e + (1 - e) := by abel
  have hSG : Sm * G = c • (G * e) + (Sm - c • e) := by
    calc Sm * G = Sm * (G * e + (1 - e)) := by rw [← hG]
      _ = Sm * (G * e) + (Sm - Sm * e) := by
        rw [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one]
      _ = c • (G * e) + (Sm - c • e) := by
        rw [hc, hcomm_e, ← Matrix.mul_assoc, hc, Matrix.smul_mul]
  have hGS : G * Sm = c • (G * e) + (Sm - c • e) := by
    calc G * Sm = (G * e + (1 - e)) * Sm := by rw [← hG]
      _ = G * (e * Sm) + (Sm - e * Sm) := by
        rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = c • (G * e) + (Sm - c • e) := by rw [← hse, hc, Matrix.mul_smul]
  rw [hSG, hGS]

private lemma nbrPSL_scalar_lift_commute
    {X : Type} [Group X] {m f : ℕ}
    (ψ : (ggU .PSL (m + 1) f).K →* X) {s : GL (Fin (m + 1)) (GaloisField 2 f)} {b : X}
    (hs : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b)
    (hsc : ∃ c : GaloisField 2 f,
      (s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) = c • 1)
    (u : (ggU .PSL (m + 1) f).K) : b⁻¹ * ψ u * b = ψ u := by
  obtain ⟨u', hu'j, hu'ψ⟩ := hs u
  obtain ⟨c, hc⟩ := hsc
  have hcen : s * Matrix.SpecialLinearGroup.toGL u = Matrix.SpecialLinearGroup.toGL u * s := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hc, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one]
  have hu'u : u' = u := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [hu'j, mul_inv_eq_iff_eq_mul]
    exact hcen
  exact hu'ψ.trans (congrArg ψ hu'u)

theorem ggSixPSLPosExplicit_holds
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSL n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X) (hH : GGSixPosHyp .PSL n f ψ p G₀ B₁ D J L x) :
    ∃ (R Rm : Subgroup X) (kJ : ℕ) (βJ : Fin (ggU .PSL (kJ + 1) f).D.rank → ℤ),
      R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 .PSL n f p ψ R Rm ∧ 1 ≤ f ∧ kJ + 1 < n ∧
      βJ ∈ (ggU .PSL (kJ + 1) f).D.roots ∧ GGRootVia (ggU .PSL (kJ + 1) f) J R βJ ∧
      ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
        IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
        Odd (Nat.card (Subgroup.center ↥K)) →
        ∃ (kK : ℕ) (βK : Fin (ggU .PSL (kK + 1) f).D.rank → ℤ), kJ < kK ∧
          βK ∈ (ggU .PSL (kK + 1) f).D.roots ∧ GGRootVia (ggU .PSL (kK + 1) f) K R βK := by
  have hH' := hH
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := hH
  have hadm : StatedLieAdmissible .PSL n 2 f := by
    rcases h3 with ⟨_, hscm⟩ | ⟨hn0, hmem, _⟩ | ⟨hn0, hmem, _⟩ | ⟨hn0, hmem, _⟩
    · exact hscm.1
    · exact absurd hmem (by decide)
    · exact absurd hmem (by decide)
    · exact absurd hmem (by decide)
  rcases hadm with ⟨-, hf, hn2, -⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  subst hm
  have hm1 : 1 ≤ m := by omega
  obtain ⟨S, J', hS, hodd, hJ'comp, hJ'map, hSfull⟩ := nbrPSL_stepA m f ψ p G₀ B₁ D J L x hH'
  obtain ⟨e_J, heJ, hJ'block⟩ :=
    exists_isComponentOf_glBlockCentralizer_PSL m (GaloisField 2 f) S hS hJ'comp
  have hdegJ := nbrPSL_blockDegree_J m f ψ p G₀ B₁ D J L x hH' hS hodd heJ hJ'block hJ'map
  obtain ⟨kJ, ιJ, β₀, v, φ, v', φ', hlong₀, hcenJ, hrangeJ, hd1, hd2, hd3, hd4, hroot1, hroot2,
    hrankJ, hJeq, hβ₀root⟩ := exists_blockModel_PSL_rank m f S hS heJ hdegJ hJ'block
  obtain ⟨β, hβroot, hβlong, u, huX, huXneg⟩ :=
    exists_conj_rootGroup_eq_matTransvGroup_PSL m (GaloisField 2 f) hm1 v φ v' φ' hd1 hd2 hd3 hd4
  have hRX : ((ggU .PSL (kJ + 1) f).D.rootGroup β₀).map ιJ =
      ((ggU .PSL (m + 1) f).D.rootGroup β).map (MulAut.conj u).toMonoidHom :=
    Subgroup.map_injective Matrix.SpecialLinearGroup.toGL_injective (hroot1.trans huX.symm)
  have hRXneg : ((ggU .PSL (kJ + 1) f).D.rootGroup (-β₀)).map ιJ =
      ((ggU .PSL (m + 1) f).D.rootGroup (-β)).map (MulAut.conj u).toMonoidHom :=
    Subgroup.map_injective Matrix.SpecialLinearGroup.toGL_injective (hroot2.trans huXneg.symm)
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup X, R = ggRootSub (ggU .PSL (m + 1) f).D ψ β u := ⟨_, rfl⟩
  obtain ⟨Rm, hRmdef⟩ : ∃ Rm : Subgroup X, Rm = ggRootSub (ggU .PSL (m + 1) f).D ψ (-β) u :=
    ⟨_, rfl⟩
  have hRle : R ≤ J := by
    rw [← hJ'map, ← hrangeJ, hRdef]
    unfold ggRootSub
    exact (Subgroup.map_mono (le_of_eq hRX.symm)).trans
      (Subgroup.map_mono (Subgroup.map_le_range ιJ _))
  have hRmle : Rm ≤ J := by
    rw [← hJ'map, ← hrangeJ, hRmdef]
    unfold ggRootSub
    exact (Subgroup.map_mono (le_of_eq hRXneg.symm)).trans
      (Subgroup.map_mono (Subgroup.map_le_range ιJ _))
  have hRvia : R = ggRootSub (ggU .PSL (kJ + 1) f).D (ψ.comp ιJ) β₀ 1 := by
    have hconj : ∀ H : Subgroup (ggU .PSL (kJ + 1) f).K,
        H.map (MulAut.conj (1 : (ggU .PSL (kJ + 1) f).K)).toMonoidHom = H := by
      intro H
      ext y
      simp
    rw [hRdef]
    unfold ggRootSub
    rw [hconj, ← Subgroup.map_map]
    exact congrArg (Subgroup.map ψ) hRX.symm
  have hkJ : kJ + 1 < m + 1 := by
    have hle : kJ + 1 ≤ m + 1 := by
      rw [hrankJ]
      calc Module.finrank (GaloisField 2 f) (LinearMap.range (Matrix.toLin' e_J))
          ≤ Module.finrank (GaloisField 2 f) (Fin (m + 1) → GaloisField 2 f) :=
            Submodule.finrank_le _
        _ = m + 1 := by simp
    by_contra hnot
    have heq : kJ + 1 = m + 1 := by omega
    have htop : LinearMap.range (Matrix.toLin' e_J) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [← hrankJ, heq]
      simp
    have hone : e_J = 1 := nbrPSL_eq_one_of_range_top heJ.2.1 htop
    have hscal : ∀ s ∈ S, ∃ c : GaloisField 2 f,
        (s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) = c • 1 := by
      intro s hs
      obtain ⟨c, hc⟩ := nbrPSL_mul_e_eq_smul heJ hdegJ _ (Algebra.subset_adjoin ⟨s, hs, rfl⟩)
      rw [hone, Matrix.mul_one] at hc
      exact ⟨c, hc⟩
    apply h22
    intro d hd
    have hdB : d ∈ B₁ := h11 hd
    have hdN : d ∈ Subgroup.normalizer (ψ.range : Set X) := by
      rw [h1]
      exact h7 hdB
    obtain ⟨s, hs⟩ := exists_isGLLift_PSL m (GaloisField 2 f) ψ h2 hdN (h8 d hdB)
    have hsS : s ∈ S := hSfull s ⟨d, hd, hs⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hlG₀ : l ∈ ψ.range := by
      rw [h1]
      exact h19 hl
    obtain ⟨w, rfl⟩ := hlG₀
    have hcomm := nbrPSL_scalar_lift_commute ψ hs (hscal s hsS) w
    calc ψ w * d = d * (d⁻¹ * ψ w * d) := by group
      _ = d * ψ w := by rw [hcomm]
  refine ⟨R, Rm, kJ, β₀, hRle, hRmle, ⟨β, hβroot, Or.inl hβlong, u, hRdef, hRmdef⟩, hf, hkJ,
    hβ₀root, nbrPSL_rootVia m f ψ h2 hJ'map hcenJ hrangeJ 1 hRvia, ?_⟩
  intro e heD hene K hKG0 hKcomp hJK hKne hKodd
  obtain ⟨S_e, K', ε, hSe, hS_e, hodd_e, hK'comp, hK'map, hε, hK'block, hJK'⟩ :=
    nbrPSL_neighbourBlock m f ψ p G₀ B₁ D J L x hH' e heD K hKG0 hKcomp hJK hS hodd hJ'comp
      hJ'map hSfull
  have hdegK := nbrPSL_blockDegree_K hSe hS hodd heJ hε hJ'block hK'block hJK' hdegJ
  have hJε : e_J * ε = e_J := nbrPSL_eJ_mul_eps hSe hS heJ hε hJ'block hK'block hJK'
  obtain ⟨kK, ιK, hcenK, hrangeK, hclosureK, hrankK⟩ :=
    exists_blockModelClosure_PSL_rank m f S_e hS_e hε hdegK hK'block
  have hR0 : GGRootPosG0 .PSL (m + 1) f p ψ R Rm :=
    ⟨β, hβroot, Or.inl hβlong, u, hRdef, hRmdef⟩
  obtain ⟨β', hβ'root, hcl', u', hR', hRm'⟩ := hR0
  obtain ⟨β'', u'', hβ''root, hlong'', hR_eq⟩ :=
    nbrPSL_rootImage m f hf ψ h2 hK'map (le_trans hRle hJK) hβ'root u' hR' hclosureK
  refine ⟨kK, β'', ?_, hβ''root, nbrPSL_rootVia m f ψ h2 hK'map hcenK hrangeK u'' hR_eq⟩
  have hεA : ε ∈ Algebra.adjoin (GaloisField 2 f) (Units.val '' S) :=
    Algebra.adjoin_mono (Set.image_mono hSe) hε.1
  have hεJ : ε * e_J = e_J := (nbrPSL_adjoin_commute hS hεA heJ.1).trans hJε
  have hne : e_J ≠ ε := by
    intro heq
    have hK'G : K' ≤ glBlockCentralizer Matrix.SpecialLinearGroup.toGL S_e ε := fun w hw => by
      have h := (Subgroup.commutator_le_sup _ _) (hK'block.1 hw)
      rwa [sup_idem] at h
    have hle : glBlockCentralizer Matrix.SpecialLinearGroup.toGL S_e ε ≤
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e_J := by
      rw [← heq]
      exact nbrPSL_glBlockCentralizer_le hS heJ hdegJ (by rw [heq]; exact hε.1)
    have hK'J' : K' ≤ J' := fun w hw => by
      rw [hJeq]
      exact hle (hK'G hw)
    apply hKne
    rw [← hK'map, ← hJ'map, le_antisymm hJK' hK'J']
  have hlt := nbrPSL_finrank_lt_of_mul_eq heJ.2.1 hJε hεJ hne
  omega
end CFSG.StandardType.ClassicalPosition
