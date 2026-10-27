module

public import CFSG.Quasithin.Background.F6ResPGL2
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2FullSplitTorus
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.PGL2TorusCentralizer

public section

namespace CFSG.Quasithin

open CFSG.GorensteinWalter

namespace F6

namespace PSigmaRes

section FieldAut

variable {p : ℕ} {K : Type} [Field K] [Finite K]

theorem ringAut_mul_self (hp : p.Prime) (hK : Nat.card K = p ^ 2) (τ : K ≃+* K) :
    τ * τ = 1 := by
  have hc := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK).1
  have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by omega)
  have h := pow_card_eq_one' (G := RingAut K) (x := τ)
  rw [hc, pow_two] at h
  exact h

theorem ringAut_apply_eq_pow (hp : p.Prime) (hK : Nat.card K = p ^ 2) (τ : K ≃+* K)
    (hτ : τ ≠ 1) (x : K) : τ x = x ^ p := by
  let _ : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  let _ : Algebra (ZMod p) K := ZMod.algebra K p
  set φ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K
  have hφ : ∀ y, φ y = y ^ p := fun y => by
    rw [FiniteField.frobeniusAlgEquivOfAlgebraic_apply, ZMod.card]
  have hord : orderOf φ = 2 := by
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
    apply Nat.pow_right_injective hp.two_le
    change p ^ Module.finrank (ZMod p) K = p ^ 2
    rw [FiniteField.pow_finrank_eq_natCard, hK]
  have hφ1 : φ.toRingEquiv ≠ 1 := by
    intro h
    have : φ = 1 := by
      ext y
      exact congrArg (fun f : K ≃+* K => f y) h
    rw [this, orderOf_one] at hord
    norm_num at hord
  have hcard := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK).1
  obtain ⟨u, v, -, huniv⟩ := Nat.card_eq_two_iff.mp hcard
  have hmem : ∀ z : RingAut K, z = u ∨ z = v := fun z => by
    have : z ∈ ({u, v} : Set (RingAut K)) := huniv ▸ Set.mem_univ z
    simpa using this
  have hτφ : τ = φ.toRingEquiv := by
    rcases hmem τ with h1 | h1 <;> rcases hmem φ.toRingEquiv with h2 | h2 <;>
      rcases hmem 1 with h3 | h3
    all_goals first | exact h1.trans h2.symm | (exfalso; apply hτ; exact h1.trans h3.symm) |
      (exfalso; apply hφ1; exact h2.trans h3.symm)
  rw [hτφ]
  exact hφ x

end FieldAut

section Torus

variable {K : Type} [Field K]

@[expose] noncomputable def jGL (K : Type) [Field K] : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp [Matrix.det_fin_two])

@[expose] noncomputable def jPGL (K : Type) [Field K] : PGL2 K := Matrix.ProjGenLinGroup.mk (jGL K)

theorem jPGL_mul_self : jPGL K * jPGL K = 1 := by
  rw [jPGL, ← map_mul, Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  refine ⟨1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jGL, Matrix.mul_apply, Fin.sum_univ_two]

theorem jPGL_mul_torus (a : Kˣ) :
    jPGL K * pGammaL2FullSplitTorus K a = pGammaL2FullSplitTorus K a⁻¹ * jPGL K := by
  simp only [jPGL, pGammaL2FullSplitTorus, MonoidHom.comp_apply, ← map_mul]
  rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨a⁻¹, ?_⟩
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, jGL,
    pGammaL2FullSplitTorusGL, Matrix.GeneralLinearGroup.scalar,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
  fin_cases i <;> fin_cases j <;> simp

theorem torus_mul_j_mul_self (d : Kˣ) :
    pGammaL2FullSplitTorus K d * jPGL K * (pGammaL2FullSplitTorus K d * jPGL K) = 1 := by
  rw [mul_assoc, ← mul_assoc (jPGL K), jPGL_mul_torus, mul_assoc, jPGL_mul_self, mul_one,
    ← map_mul, mul_inv_cancel, map_one]

theorem eq_torus_or_eq_torus_mul_j (g : PGL2 K) {a b : Kˣ} (ha : a ≠ 1)
    (h : g * pGammaL2FullSplitTorus K a = pGammaL2FullSplitTorus K b * g) :
    (∃ d, g = pGammaL2FullSplitTorus K d ∧ b = a) ∨
      (∃ d, g = pGammaL2FullSplitTorus K d * jPGL K ∧ b = a⁻¹) := by
  obtain ⟨G, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  have h' : Matrix.ProjGenLinGroup.mk (G * pGammaL2FullSplitTorusGL K a) =
      Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL K b * G) := by
    rw [map_mul, map_mul]
    exact h
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h'
  have e00 := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 0 0) hu
  have e01 := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 0 1) hu
  have e10 := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 1 0) hu
  have e11 := congrArg (fun M : GL (Fin 2) K => (M : Matrix (Fin 2) (Fin 2) K) 1 1) hu
  simp [pGammaL2FullSplitTorusGL, Matrix.mul_apply, Matrix.GeneralLinearGroup.scalar,
    Matrix.diagonal] at e00 e01 e10 e11
  have hdet : (G : Matrix (Fin 2) (Fin 2) K) 0 0 * (G : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (G : Matrix (Fin 2) (Fin 2) K) 0 1 * (G : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
    rw [← Matrix.det_fin_two, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have ha' : (a : K) ≠ 1 := fun h1 => ha (Units.ext h1)
  obtain ⟨x, hxd⟩ : ∃ x, (G : Matrix (Fin 2) (Fin 2) K) 0 0 = x := ⟨_, rfl⟩
  obtain ⟨y, hyd⟩ : ∃ y, (G : Matrix (Fin 2) (Fin 2) K) 0 1 = y := ⟨_, rfl⟩
  obtain ⟨z, hzd⟩ : ∃ z, (G : Matrix (Fin 2) (Fin 2) K) 1 0 = z := ⟨_, rfl⟩
  obtain ⟨w, hwd⟩ : ∃ w, (G : Matrix (Fin 2) (Fin 2) K) 1 1 = w := ⟨_, rfl⟩
  rw [hxd, hyd, hzd, hwd] at hdet
  rw [hxd] at e00
  rw [hyd] at e01
  rw [hzd] at e10
  rw [hwd] at e11
  by_cases hw : w = 0
  · have hy : y ≠ 0 := fun hy => hdet (by rw [hw, hy]; ring)
    have hz : z ≠ 0 := fun hz => hdet (by rw [hw, hz]; ring)
    have hau : (a : K) * u = 1 := by
      have : z * ((a : K) * u - 1) = 0 := by linear_combination e10
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hz)
    have hub : (u : K) = b := by
      have : y * ((u : K) - b) = 0 := by linear_combination e01
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hy)
    have hb1 : (b : K) ≠ 1 := by
      intro hb
      apply ha'
      rw [hub, hb, mul_one] at hau
      exact hau
    have hx : x = 0 := by
      have : x * (1 - (b : K)) = 0 := by linear_combination e00 - x * hau
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm hb1))
    right
    refine ⟨Units.mk0 (y / z) (div_ne_zero hy hz), ?_, ?_⟩
    · rw [pGammaL2FullSplitTorus, MonoidHom.comp_apply, jPGL, ← map_mul,
        Matrix.ProjGenLinGroup.mk_eq_mk_iff]
      refine ⟨Units.mk0 z⁻¹ (inv_ne_zero hz), ?_⟩
      ext i j
      simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, jGL,
        pGammaL2FullSplitTorusGL, Matrix.GeneralLinearGroup.scalar,
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      fin_cases i <;> fin_cases j <;> simp [hxd, hyd, hzd, hwd, hx, hw] <;> field_simp
    · apply Units.ext
      rw [Units.val_inv_eq_inv_val, ← hub]
      exact eq_inv_of_mul_eq_one_right hau
  · have hu1 : (u : K) = 1 := by
      have : w * ((u : K) - 1) = 0 := by linear_combination e11
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hw)
    have hz : z = 0 := by
      have : z * ((a : K) - 1) = 0 := by linear_combination e10 - z * a * hu1
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr ha')
    have hx : x ≠ 0 := fun hx => hdet (by rw [hx, hz]; ring)
    have hab : (b : K) = a := by
      have : x * ((a : K) - b) = 0 := by linear_combination e00 - x * a * hu1
      exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hx)).symm
    have hy : y = 0 := by
      have : y * (1 - (a : K)) = 0 := by linear_combination e01 - y * hu1 + y * hab
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm ha'))
    left
    refine ⟨Units.mk0 (x / w) (div_ne_zero hx hw), ?_, Units.ext hab⟩
    rw [pGammaL2FullSplitTorus, MonoidHom.comp_apply, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨Units.mk0 w⁻¹ (inv_ne_zero hw), ?_⟩
    ext i j
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      pGammaL2FullSplitTorusGL, Matrix.GeneralLinearGroup.scalar]
    fin_cases i <;> fin_cases j <;> simp [hxd, hyd, hzd, hwd, hy, hz] <;> field_simp

end Torus

section Congruence

variable {p : ℕ} {K : Type} [Field K] [Finite K]

theorem mod_twentyfour_of_semilinear (hp : p.Prime) (hK : Nat.card K = p ^ 2)
    (hp8 : p % 8 = 3 ∨ p % 8 = 5) {σ : K ≃+* K} (hσ : σ ≠ 1) {w c g : PGL2 K}
    (hwc : w * c = c * w) (hw : orderOf w = 3) (hc : orderOf c = 4)
    (hgw : g * pgl2FieldAut K σ w = w * g) (hgc : g * pgl2FieldAut K σ c = c⁻¹ * g) :
    p % 24 = 5 ∨ p % 24 = 19 := by
  set T := pGammaL2FullSplitTorus K
  have hp2 : p ≠ 2 := by omega
  have hKodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 2, hp, hp.odd_of_ne_two hp2, by norm_num, hK⟩
  have hcard3 : 3 < Nat.card K := by
    rw [hK]
    have := hp.two_le
    nlinarith
  have hT : Function.Injective T := pGammaL2FullSplitTorus_injective K
  have hcomm : commutator (PGL2 K) =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three K hKodd hcard3
  have hsq : ∀ x : PGL2 K, x ^ 2 ∈ commutator (PGL2 K) := fun x => by
    rw [hcomm]
    exact Subgroup.sq_mem_of_index_two (pgl2_psl2Range_index_eq_two K hKodd) x
  have hc2 : BenderSuzuki.PFAppendixIII.IsInvolution (c ^ 2) := by
    refine ⟨fun h => ?_, by
      rw [← pow_mul, show 2 * 2 = orderOf c by rw [hc]]
      exact pow_orderOf_eq_one c⟩
    have := orderOf_dvd_of_pow_eq_one h
    rw [hc] at this
    norm_num at this
  obtain ⟨i, hi⟩ : ∃ i : Kˣ, i * i = -1 := by
    let _ : Fintype K := Fintype.ofFinite K
    have h4 : Fintype.card K % 4 ≠ 3 := by
      rw [← Nat.card_eq_fintype_card, hK]
      have := sq_mod_sixteen hp8
      omega
    obtain ⟨r, hr⟩ := FiniteField.isSquare_neg_one_iff.mpr h4
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
    exact ⟨Units.mk0 r hr0, Units.ext (by simp [hr])⟩
  have hneg1 : (-1 : Kˣ) ≠ 1 := by
    intro h
    have h2 : (2 : K) = 0 := by
      have := congrArg (fun u : Kˣ => (u : K)) h
      simp only [Units.val_neg, Units.val_one] at this
      linear_combination -this
    exact two_ne_zero_of_odd_card K (by rw [hK]; exact (hp.odd_of_ne_two hp2).pow) h2
  have hs0 : BenderSuzuki.PFAppendixIII.IsInvolution (T (-1)) :=
    ⟨fun h => hneg1 (hT (h.trans (map_one T).symm)), by rw [← map_pow, neg_one_sq, map_one]⟩
  have hs0J : T (-1) ∈ commutator (PGL2 K) := by
    rw [← hi, map_mul, ← pow_two]
    exact hsq _
  obtain ⟨h, -, hh⟩ := pgl2_inner_involutions_conjugate hKodd hcard3 (hsq c) hc2 hs0J hs0
  set κ := MulAut.conj h
  have hh' : κ (c ^ 2) = T (-1) := by rw [MulAut.conj_apply]; exact hh
  have hw's : κ w * T (-1) = T (-1) * κ w := by
    rw [← hh', ← map_mul, ← map_mul, (Commute.pow_right (show Commute w c from hwc) 2).eq]
  have hc's : κ c * T (-1) = T (-1) * κ c := by
    rw [← hh', ← map_mul, ← map_mul, ← pow_succ', ← pow_succ]
  have hdiag : ∀ x : PGL2 K, x * T (-1) = T (-1) * x → orderOf x ≠ 1 → orderOf x ≠ 2 →
      ∃ d, x = T d := by
    intro x hx h1 h2
    rcases eq_torus_or_eq_torus_mul_j x hneg1 hx with ⟨d, hd, -⟩ | ⟨d, hd, -⟩
    · exact ⟨d, hd⟩
    · exfalso
      have hxx : x ^ 2 = 1 := by rw [pow_two, hd]; exact torus_mul_j_mul_self d
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxx) with h | h
      exacts [h1 h, h2 h]
  obtain ⟨ω, hω⟩ := hdiag (κ w) hw's (by rw [MulEquiv.orderOf_eq, hw]; norm_num)
    (by rw [MulEquiv.orderOf_eq, hw]; norm_num)
  obtain ⟨γ, hγ⟩ := hdiag (κ c) hc's (by rw [MulEquiv.orderOf_eq, hc]; norm_num)
    (by rw [MulEquiv.orderOf_eq, hc]; norm_num)
  have hωo : orderOf ω = 3 := by rw [← orderOf_injective T hT, ← hω, MulEquiv.orderOf_eq, hw]
  have hγo : orderOf γ = 4 := by rw [← orderOf_injective T hT, ← hγ, MulEquiv.orderOf_eq, hc]
  set φ := pgl2FieldAut K σ
  set g' := h * g * (φ h)⁻¹
  have hg'w : g' * φ (κ w) = κ w * g' := by
    simp only [g', κ, MulAut.conj_apply, map_mul, map_inv]
    calc h * g * (φ h)⁻¹ * (φ h * φ w * (φ h)⁻¹) = h * (g * φ w) * (φ h)⁻¹ := by group
      _ = h * (w * g) * (φ h)⁻¹ := by rw [hgw]
      _ = h * w * h⁻¹ * (h * g * (φ h)⁻¹) := by group
  have hg'c : g' * φ (κ c) = (κ c)⁻¹ * g' := by
    simp only [g', κ, MulAut.conj_apply, map_mul, map_inv]
    calc h * g * (φ h)⁻¹ * (φ h * φ c * (φ h)⁻¹) = h * (g * φ c) * (φ h)⁻¹ := by group
      _ = h * (c⁻¹ * g) * (φ h)⁻¹ := by rw [hgc]
      _ = (h * c * h⁻¹)⁻¹ * (h * g * (φ h)⁻¹) := by group
  have hφT : ∀ a : Kˣ, φ (T a) = T (a ^ p) := fun a => by
    rw [pGammaL2FullSplitTorus_map_field]
    congr 1
    apply Units.ext
    simp [ringAut_apply_eq_pow hp hK σ hσ]
  rw [hω, hφT] at hg'w
  rw [hγ, hφT, ← map_inv] at hg'c
  have hp3 : p ≠ 3 := by
    rintro rfl
    have h3 := orderOf_dvd_natCard ω
    rw [hωo, Nat.card_units, hK] at h3
    norm_num at h3
  have hωp : ω ^ p ≠ 1 := fun h1 => by
    have h3 := orderOf_dvd_of_pow_eq_one h1
    rw [hωo] at h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3).symm
  have hγp : γ ^ p ≠ 1 := fun h1 => by
    have h4 := orderOf_dvd_of_pow_eq_one h1
    rw [hγo] at h4
    have h2 : 2 ∣ p := (by norm_num : (2 : ℕ) ∣ 4).trans h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  have hJ : ∀ d d' : Kˣ, T d ≠ T d' * jPGL K := by
    intro d d' hdd
    have hJ' : jPGL K = T (d'⁻¹ * d) := by rw [map_mul, map_inv, hdd]; group
    have hJω := jPGL_mul_torus ω
    rw [hJ', ← map_mul, ← map_mul] at hJω
    have hωω : ω * ω = 1 := by
      have := hT hJω
      have h' : ω * (d'⁻¹ * d) = ω⁻¹ * (d'⁻¹ * d) := by rw [mul_comm ω]; exact this
      exact eq_inv_iff_mul_eq_one.mp (mul_right_cancel h')
    have h2 := orderOf_dvd_of_pow_eq_one (show ω ^ 2 = 1 by rw [pow_two]; exact hωω)
    rw [hωo] at h2
    norm_num at h2
  have hsub : ∀ x : Kˣ, x ^ p = x → x ^ (p - 1) = 1 := fun x hx => by
    have h1 : x ^ (p - 1) * x = 1 * x := by rw [pow_sub_one_mul hp.ne_zero x, hx, one_mul]
    exact mul_right_cancel h1
  rcases eq_torus_or_eq_torus_mul_j g' hωp hg'w with ⟨d, hd, hωe⟩ | ⟨d, hd, hωe⟩ <;>
    rcases eq_torus_or_eq_torus_mul_j g' hγp hg'c with ⟨d', hd', hγe⟩ | ⟨d', hd', hγe⟩
  · have h3 : 3 ∣ p - 1 := hωo ▸ orderOf_dvd_of_pow_eq_one (hsub ω hωe.symm)
    have h4 : 4 ∣ p + 1 := hγo ▸ orderOf_dvd_of_pow_eq_one (by rw [pow_succ, ← hγe, inv_mul_cancel])
    omega
  · exact absurd (hd.symm.trans hd') (hJ d d')
  · exact absurd (hd'.symm.trans hd) (hJ d' d)
  · have h3 : 3 ∣ p + 1 := hωo ▸ orderOf_dvd_of_pow_eq_one (by
      rw [pow_succ]
      exact mul_eq_one_iff_eq_inv.mpr (inv_eq_iff_eq_inv.mpr hωe).symm)
    have h4 : 4 ∣ p - 1 := hγo ▸ orderOf_dvd_of_pow_eq_one (hsub γ (inv_injective hγe).symm)
    omega

end Congruence

section Embedding

abbrev S3D8 := Equiv.Perm (Fin 3) × DihedralGroup 4

@[expose] def w0 : S3D8 := (Equiv.swap 0 1 * Equiv.swap 1 2, 1)

@[expose] def r0 : S3D8 := (1, DihedralGroup.r 1)

@[expose] def s0 : S3D8 := (1, DihedralGroup.sr 0)

theorem s3d8_gen_facts : w0 ^ 3 = 1 ∧ w0 ≠ 1 ∧ r0 ^ 4 = 1 ∧ ¬ r0 ^ 2 = 1 := by decide

theorem s3d8_rel_facts : s0 * r0 = r0⁻¹ * s0 ∧ w0 * r0 = r0 * w0 ∧ w0 * s0 = s0 * w0 := by
  decide

@[expose] def v1Set : Finset S3D8 := {1, r0 ^ 2, s0, r0 ^ 2 * s0}

@[expose] def v2Set : Finset S3D8 := {1, r0 ^ 2, r0 * s0, r0 ^ 3 * s0}

theorem v1_mul : ∀ a ∈ v1Set, ∀ b ∈ v1Set, a * b ∈ v1Set := by decide

theorem v2_mul : ∀ a ∈ v2Set, ∀ b ∈ v2Set, a * b ∈ v2Set := by decide

theorem v1_inv : ∀ a ∈ v1Set, a⁻¹ ∈ v1Set := by decide

theorem v2_inv : ∀ a ∈ v2Set, a⁻¹ ∈ v2Set := by decide

theorem v1_sq : ∀ a ∈ v1Set, a * a = 1 := by decide

theorem v2_sq : ∀ a ∈ v2Set, a * a = 1 := by decide

theorem v1_comm : ∀ a ∈ v1Set, a * w0 = w0 * a := by decide

theorem v2_comm : ∀ a ∈ v2Set, a * w0 = w0 * a := by decide

theorem v1_card : v1Set.card = 4 := by decide

theorem v2_card : v2Set.card = 4 := by decide

@[expose] def finsetSubgroup (S : Finset S3D8) (h1 : (1 : S3D8) ∈ S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hinv : ∀ a ∈ S, a⁻¹ ∈ S) : Subgroup S3D8 where
  carrier := S
  mul_mem' ha hb := hmul _ ha _ hb
  one_mem' := h1
  inv_mem' ha := hinv _ ha

theorem card_finsetSubgroup (S : Finset S3D8) (h1 : (1 : S3D8) ∈ S)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hinv : ∀ a ∈ S, a⁻¹ ∈ S) :
    Nat.card (finsetSubgroup S h1 hmul hinv) = S.card := by
  rw [← Nat.card_eq_finsetCard]
  rfl

variable {p : ℕ} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem inl_left_of_right_eq_one {y : PGammaL2 K} (hy : y.right = 1) :
    SemidirectProduct.inl y.left = y := by
  conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right y]
  rw [hy, map_one, mul_one]

theorem false_of_kleinFour_inl
    (hK : IsOddPrimePower (Nat.card K)) {V : Subgroup (PGammaL2 K)}
    (hV4 : Nat.card V = 4) (hVsq : ∀ v ∈ V, v * v = 1) (hVr : ∀ v ∈ V, v.right = 1)
    {x : PGammaL2 K} (hx1 : x ≠ 1) (hxo : Odd (orderOf x)) (hxr : x.right = 1)
    (hc : ∀ v ∈ V, v * x = x * v) : False := by
  have hinj : Function.Injective (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) :=
    SemidirectProduct.inl_injective
  set V' := V.comap (SemidirectProduct.inl : PGL2 K →* PGammaL2 K)
  have hVV' : V'.map SemidirectProduct.inl = V :=
    Subgroup.map_comap_eq_self fun v hv => ⟨v.left, inl_left_of_right_eq_one (hVr v hv)⟩
  have hV'4 : Nat.card V' = 4 := by
    rw [← hV4, ← hVV', Subgroup.card_map_of_injective hinj]
  refine PGL2Res.false_of_kleinFour_commute (MulEquiv.refl (PGL2 K)) hK (V := V') hV'4 ?_
    (x := x.left) ?_ ?_ ?_
  · intro v hv
    apply hinj
    rw [map_mul, map_one]
    exact hVsq _ hv
  · intro h
    apply hx1
    rw [← inl_left_of_right_eq_one hxr, h, map_one]
  · rw [← orderOf_injective _ hinj, inl_left_of_right_eq_one hxr]
    exact hxo
  · intro v hv
    apply hinj
    rw [map_mul, map_mul, inl_left_of_right_eq_one hxr]
    exact hc _ hv

theorem mod_twentyfour_of_embedding
    (hp : p.Prime) (hK : Nat.card K = p ^ 2)
    (hp8 : p % 8 = 3 ∨ p % 8 = 5) (ι : S3D8 →* PGammaL2 K) (hι : Function.Injective ι) :
    p % 24 = 5 ∨ p % 24 = 19 := by
  have hp2 : p ≠ 2 := by omega
  have hKodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 2, hp, hp.odd_of_ne_two hp2, by norm_num, hK⟩
  obtain ⟨hw3, hw1, hr4, hr2⟩ := s3d8_gen_facts
  obtain ⟨hsr, hwr, hws⟩ := s3d8_rel_facts
  set χ : S3D8 →* (K ≃+* K) := SemidirectProduct.rightHom.comp ι
  have hχ : ∀ x, χ x = (ι x).right := fun x => rfl
  have hχsq : ∀ x, χ x * χ x = 1 := fun x => ringAut_mul_self hp hK _
  have hχw : χ w0 = 1 := by
    have h3 : χ w0 ^ 3 = 1 := by rw [← map_pow, hw3, map_one]
    calc χ w0 = χ w0 ^ 3 * (χ w0 * χ w0)⁻¹ := by group
      _ = 1 := by rw [h3, hχsq, inv_one, one_mul]
  have hfour : ∀ V : Subgroup S3D8, Nat.card V = 4 → (∀ v ∈ V, v * v = 1) →
      (∀ v ∈ V, v * w0 = w0 * v) → (∀ v ∈ V, χ v = 1) → False := by
    intro V hV4 hVsq hVw hVχ
    refine false_of_kleinFour_inl hKodd (V := V.map ι) ?_ ?_ ?_ (x := ι w0) ?_ ?_ ?_ ?_
    · rw [Subgroup.card_map_of_injective hι, hV4]
    · rintro _ ⟨v, hv, rfl⟩
      rw [← map_mul, hVsq v hv, map_one]
    · rintro _ ⟨v, hv, rfl⟩
      exact hVχ v hv
    · exact fun h => hw1 (hι (h.trans (map_one ι).symm))
    · rw [orderOf_injective ι hι, orderOf_eq_prime hw3 hw1]
      decide
    · exact hχw
    · rintro _ ⟨v, hv, rfl⟩
      rw [← map_mul, ← map_mul, hVw v hv]
  have hχs : χ s0 ≠ 1 := by
    intro h
    refine hfour (finsetSubgroup v1Set (by decide) v1_mul v1_inv)
      (by rw [card_finsetSubgroup, v1_card]) v1_sq v1_comm (fun v hv => ?_)
    simp only [finsetSubgroup, v1Set, Subgroup.mem_mk, Submonoid.mem_mk,
      Subsemigroup.mem_mk, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact map_one χ
    · rw [map_pow, pow_two, hχsq]
    · exact h
    · rw [map_mul, map_pow, pow_two, hχsq, h, one_mul]
  have hχr : χ r0 = 1 := by
    by_contra h
    have heq : χ r0 = χ s0 := RingEquiv.ext fun x => by
      rw [ringAut_apply_eq_pow hp hK _ h, ringAut_apply_eq_pow hp hK _ hχs]
    refine hfour (finsetSubgroup v2Set (by decide) v2_mul v2_inv)
      (by rw [card_finsetSubgroup, v2_card]) v2_sq v2_comm (fun v hv => ?_)
    simp only [finsetSubgroup, v2Set, Subgroup.mem_mk, Submonoid.mem_mk,
      Subsemigroup.mem_mk, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact map_one χ
    · rw [map_pow, pow_two, hχsq]
    · rw [map_mul, heq, hχsq]
    · rw [map_mul, map_pow, heq, pow_succ, pow_two, hχsq, one_mul, hχsq]
  have hinj : Function.Injective (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) :=
    SemidirectProduct.inl_injective
  have hWl := inl_left_of_right_eq_one (show (ι w0).right = 1 from hχw)
  have hRl := inl_left_of_right_eq_one (show (ι r0).right = 1 from hχr)
  have hwc : (ι w0).left * (ι r0).left = (ι r0).left * (ι w0).left := by
    apply hinj
    rw [map_mul, map_mul, hWl, hRl, ← map_mul, ← map_mul, hwr]
  have hwo : orderOf (ι w0).left = 3 := by
    rw [← orderOf_injective _ hinj, hWl, orderOf_injective ι hι, orderOf_eq_prime hw3 hw1]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hco : orderOf (ι r0).left = 4 := by
    rw [← orderOf_injective _ hinj, hRl, orderOf_injective ι hι]
    exact orderOf_eq_prime_pow (p := 2) (n := 1) hr2 hr4
  have hgw : (ι s0).left * pgl2FieldAut K (ι s0).right (ι w0).left =
      (ι w0).left * (ι s0).left := by
    have h := congrArg SemidirectProduct.left
      (show ι s0 * ι w0 = ι w0 * ι s0 by rw [← map_mul, ← map_mul, hws])
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left] at h
    rw [h, show (ι w0).right = 1 from hχw, map_one, MulAut.one_apply]
  have hgc : (ι s0).left * pgl2FieldAut K (ι s0).right (ι r0).left =
      (ι r0).left⁻¹ * (ι s0).left := by
    have h := congrArg SemidirectProduct.left
      (show ι s0 * ι r0 = (ι r0)⁻¹ * ι s0 by rw [← map_mul, ← map_inv, ← map_mul, hsr])
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.inv_left,
      SemidirectProduct.inv_right, show (ι r0).right = 1 from hχr, inv_one, map_one,
      MulAut.one_apply, MulAut.one_apply] at h
    exact h
  exact mod_twentyfour_of_semilinear hp hK hp8 hχs hwc hwo hco hgw hgc

end Embedding

end PSigmaRes

theorem pSigmaL2InspectionFact_holds
    : PSigmaL2InspectionFact := by
  intro p K _ _ hp hK hp8 G₁ G₂ _ ⟨e₂⟩
  exact PSigmaRes.mod_twentyfour_of_embedding hp hK hp8
    ((PSigmaL2 K).subtype.comp (G₂.subtype.comp e₂.symm.toMonoidHom))
    ((PSigmaL2 K).subtype_injective.comp (G₂.subtype_injective.comp e₂.symm.injective))

end F6

end CFSG.Quasithin
