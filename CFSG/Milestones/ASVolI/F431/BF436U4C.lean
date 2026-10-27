module

public import CFSG.Milestones.ASVolI.F431.BF436U4
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Open Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Quasithin.H13.U4Par

section F4Facts

@[expose] def burnsideF4m_W4 : Matrix (Fin 2) (Fin 2) CFSG.Fischer.F4 := !![0, 1; 1, 0]

theorem burnsideF4m_gu2_pow_six : ∀ A : Matrix (Fin 2) (Fin 2) CFSG.Fischer.F4,
    (A.map (· ^ 2))ᵀ * burnsideF4m_W4 * A = burnsideF4m_W4 → A ^ 6 = 1 := by
  decide +kernel

theorem burnsideF4m_gu2_cube_mul : ∀ A B : Matrix (Fin 2) (Fin 2) CFSG.Fischer.F4,
    A ^ 3 = 1 → B ^ 3 = 1 → (A.map (· ^ 2))ᵀ * burnsideF4m_W4 * A = burnsideF4m_W4 →
      (B.map (· ^ 2))ᵀ * burnsideF4m_W4 * B = burnsideF4m_W4 → (A * B) ^ 3 = 1 := by
  decide +kernel

end F4Facts

section Field

variable {K : Type} [Field K]

@[expose] noncomputable def burnsideF4m_eF4e (h : UnitaryFieldData 2 1 K) :
    CFSG.Fischer.F4 ≃+* K :=
  letI := h.finite
  letI : CharP K 2 := h.charP
  letI : Algebra (ZMod 2) K := ZMod.algebra K 2
  (CFSG.Fischer.F4.equivGaloisField).trans
    (GaloisField.algEquivGaloisField 2 2 (by rw [h.card])).toRingEquiv.symm

theorem burnsideF4m_bar_eF4e (h : UnitaryFieldData 2 1 K) (x : CFSG.Fischer.F4) :
    h.bar (burnsideF4m_eF4e h x) = burnsideF4m_eF4e h (x ^ 2) := by
  rw [h.bar_apply, map_pow, pow_one]

theorem burnsideF4m_W_map (h : UnitaryFieldData 2 1 K) :
    (burnsideF4m_W4.map (burnsideF4m_eF4e h) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideF4m_W4]

theorem burnsideF4m_gu2_K (h : UnitaryFieldData 2 1 K) :
    (∀ A : Matrix (Fin 2) (Fin 2) K,
      (A.map h.bar)ᵀ * !![0, 1; 1, 0] * A = !![0, 1; 1, 0] → A ^ 6 = 1) ∧
    (∀ A B : Matrix (Fin 2) (Fin 2) K, A ^ 3 = 1 → B ^ 3 = 1 →
      (A.map h.bar)ᵀ * !![0, 1; 1, 0] * A = !![0, 1; 1, 0] →
      (B.map h.bar)ᵀ * !![0, 1; 1, 0] * B = !![0, 1; 1, 0] → (A * B) ^ 3 = 1) := by
  set e := burnsideF4m_eF4e h with he
  set Em : Matrix (Fin 2) (Fin 2) CFSG.Fischer.F4 ≃+* Matrix (Fin 2) (Fin 2) K := e.mapMatrix
  have hEm : ∀ M, Em M = M.map e := fun M => rfl
  have hunit : ∀ A : Matrix (Fin 2) (Fin 2) CFSG.Fischer.F4,
      ((Em A).map h.bar)ᵀ * !![0, 1; 1, 0] * Em A = !![0, 1; 1, 0] ↔
        (A.map (· ^ 2))ᵀ * burnsideF4m_W4 * A = burnsideF4m_W4 := by
    intro A
    have ht : ((Em A).map h.bar)ᵀ = Em ((A.map (· ^ 2))ᵀ) := by
      ext i j
      simp [hEm, Matrix.transpose_apply, Matrix.map_apply, h.bar_apply]
    have hW : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) = Em burnsideF4m_W4 :=
      (burnsideF4m_W_map h).symm
    have h1 : ((Em A).map h.bar)ᵀ * !![0, 1; 1, 0] * Em A =
        Em ((A.map (· ^ 2))ᵀ * burnsideF4m_W4 * A) := by
      rw [ht, hW, ← map_mul, ← map_mul]
    rw [h1, ← burnsideF4m_W_map h, ← hEm]
    exact Em.injective.eq_iff
  refine ⟨fun A hA => ?_, fun A B hA hB hAu hBu => ?_⟩
  · obtain ⟨A', rfl⟩ := Em.surjective A
    rw [← map_pow, burnsideF4m_gu2_pow_six A' ((hunit A').mp hA), map_one]
  · obtain ⟨A', rfl⟩ := Em.surjective A
    obtain ⟨B', rfl⟩ := Em.surjective B
    rw [← map_pow] at hA hB
    have hA' : A' ^ 3 = 1 := Em.injective (by rw [hA, map_one])
    have hB' : B' ^ 3 = 1 := Em.injective (by rw [hB, map_one])
    rw [← map_mul, ← map_pow,
      burnsideF4m_gu2_cube_mul A' B' hA' hB' ((hunit A').mp hAu) ((hunit B').mp hBu), map_one]

theorem burnsideF4m_ringEquiv_sq (h : UnitaryFieldData 2 1 K) (τ : K ≃+* K) : τ * τ = 1 := by
  have hcard : Nat.card K = 2 ^ 2 := by rw [h.card]
  obtain ⟨-, -, -, -, hc, -, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality 2 2
      Nat.prime_two (by norm_num) K hcard
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have h2 := orderOf_dvd_natCard τ
  rw [hc] at h2
  rw [← pow_two]
  exact orderOf_dvd_iff_pow_eq_one.mp h2

end Field

section Model

variable {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)

theorem burnsideF4m_rho_unitary {g : hypSU h 2 0} (hg : g ∈ parP h) :
    ((rho h g).map h.bar)ᵀ * !![0, 1; 1, 0] * rho h g = !![0, 1; 1, 0] := by
  have hcol := (mem_parP_iff h g).mp hg
  have hrow := (row_if1_of_col h g hcol).1
  have r2 := hrow ie2 ie2_ne_if1
  have r4 := hrow if2 if2_ne_if1
  have hgram := (mem_gramSU.mp g.2).1
  have entry : ∀ i j, ∑ k, h.bar ((((g : GL Ix K) : Matrix Ix Ix K)) (hypPartner k) i) *
      ((g : GL Ix K) : Matrix Ix Ix K) k j = hypGram 2 0 K i j := by
    intro i j
    have := congrFun (congrFun hgram i) j
    rw [mul_apply] at this
    simpa only [mul_hypGram_apply, transpose_apply, map_apply] using this
  have e1 := entry ie2 ie2
  have e2 := entry ie2 if2
  have e3 := entry if2 ie2
  have e4 := entry if2 if2
  rw [sum_ix, hypGram_apply] at e1 e2 e3 e4
  simp [r2, r4] at e1 e2 e3 e4
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rho, Matrix.mul_apply, Fin.sum_univ_two] <;> grind

@[expose] noncomputable def burnsideF4m_u4psi : ↥(parP h) →* Kˣ × GL (Fin 2) K where
  toFun g := (⟨chi h g, chi h (g : hypSU h 2 0)⁻¹, chi_mul_inv h g.2, by
      have := chi_mul_inv h ((parP h).inv_mem g.2)
      rwa [inv_inv] at this⟩,
    ⟨rho h g, rho h (g : hypSU h 2 0)⁻¹, rho_mul_inv h g.2, by
      have := rho_mul_inv h ((parP h).inv_mem g.2)
      rwa [inv_inv] at this⟩)
  map_one' := by
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · exact chi_one h
    · exact rho_one h
  map_mul' g g' := by
    refine Prod.ext (Units.ext ?_) (Units.ext ?_)
    · exact chi_mul h g'.2
    · exact rho_mul h g.2 g'.2

theorem burnsideF4m_u4psi_apply (g : ↥(parP h)) :
    ((burnsideF4m_u4psi h g).1 : K) = chi h g ∧
      ((burnsideF4m_u4psi h g).2 : Matrix (Fin 2) (Fin 2) K) = rho h g :=
  ⟨rfl, rfl⟩

@[expose] noncomputable def burnsideF4m_u4S : Subgroup (Kˣ × GL (Fin 2) K) where
  carrier := {p | (((p.2 : Matrix (Fin 2) (Fin 2) K)).map h.bar)ᵀ * !![0, 1; 1, 0] *
      (p.2 : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] ∧ (p.2 : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := by
    rintro p p' ⟨hu, h3⟩ ⟨hu', h3'⟩
    refine ⟨?_, ?_⟩
    · simp only [Prod.snd_mul, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
      calc ((p'.2 : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ *
            ((p.2 : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * !![0, 1; 1, 0] *
            ((p.2 : Matrix (Fin 2) (Fin 2) K) * (p'.2 : Matrix (Fin 2) (Fin 2) K))
          = ((p'.2 : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ *
            (((p.2 : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * !![0, 1; 1, 0] *
              (p.2 : Matrix (Fin 2) (Fin 2) K)) * (p'.2 : Matrix (Fin 2) (Fin 2) K) := by
            simp only [Matrix.mul_assoc]
        _ = !![0, 1; 1, 0] := by rw [hu, hu']
    · simp only [Prod.snd_mul, Units.val_mul]
      exact (burnsideF4m_gu2_K h).2 _ _ h3 h3' hu hu'
  inv_mem' := by
    rintro p ⟨hu, h3⟩
    have hinv : ((p.2⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (p.2 : Matrix (Fin 2) (Fin 2) K) * (p.2 : Matrix (Fin 2) (Fin 2) K) := by
      have h1 : ((p.2⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          (p.2 : Matrix (Fin 2) (Fin 2) K) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      calc ((p.2⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
          = ((p.2⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
              ((p.2 : Matrix (Fin 2) (Fin 2) K) ^ 3) := by rw [h3, Matrix.mul_one]
        _ = _ := by
          rw [pow_succ, pow_two, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    refine ⟨?_, ?_⟩
    · simp only [Prod.snd_inv, hinv, Matrix.map_mul, Matrix.transpose_mul]
      calc ((p.2 : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ *
            ((p.2 : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * !![0, 1; 1, 0] *
            ((p.2 : Matrix (Fin 2) (Fin 2) K) * (p.2 : Matrix (Fin 2) (Fin 2) K))
          = ((p.2 : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ *
            (((p.2 : Matrix (Fin 2) (Fin 2) K).map h.bar)ᵀ * !![0, 1; 1, 0] *
              (p.2 : Matrix (Fin 2) (Fin 2) K)) * (p.2 : Matrix (Fin 2) (Fin 2) K) := by
            simp only [Matrix.mul_assoc]
        _ = !![0, 1; 1, 0] := by rw [hu, hu]
    · simp only [Prod.snd_inv, hinv]
      rw [← pow_two, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, h3, one_pow]

theorem burnsideF4m_u4S_cube {p : Kˣ × GL (Fin 2) K} (hp : p ∈ burnsideF4m_u4S h) : p ^ 3 = 1 := by
  have := h.finite
  have hK : Nat.card Kˣ = 3 := by
    have := Fintype.ofFinite K
    rw [Nat.card_units, h.card]
    norm_num
  refine Prod.ext ?_ (Units.ext ?_)
  · rw [Prod.pow_fst, Prod.fst_one, ← hK]
    exact pow_card_eq_one'
  · rw [Prod.pow_snd, Units.val_pow_eq_pow_val, hp.2, Prod.snd_one, Units.val_one]

theorem burnsideF4m_u4_parP_twoClosed :
    CFSG.QuasithinUnique.IsSylowTwoOf (pCoreOf 2 (oTwoRes (parP h))) (oTwoRes (parP h)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  set R := oTwoRes (parP h) with hR
  have hRP : R ≤ parP h := oTwoRes_le _
  set ψ : ↥R →* Kˣ × GL (Fin 2) K := (burnsideF4m_u4psi h).comp (Subgroup.inclusion hRP) with hψ
  have hgen : ∀ (r : hypSU h 2 0) (hr : r ∈ R),
      burnsideF4m_u4psi h ⟨r, hRP hr⟩ ∈ burnsideF4m_u4S h := by
    intro r hr
    induction hr using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hxP, m, hm, hxm⟩ := hx
      refine ⟨burnsideF4m_rho_unitary h hxP, ?_⟩
      have hρm : rho h x ^ m = 1 := by
        have := congrArg (fun g => ((g : Kˣ × GL (Fin 2) K).2 : Matrix (Fin 2) (Fin 2) K))
          (map_pow (burnsideF4m_u4psi h) ⟨x, hxP⟩ m)
        simp only [Prod.pow_snd, Units.val_pow_eq_pow_val] at this
        rw [← (burnsideF4m_u4psi_apply h ⟨x, hxP⟩).2, ← this]
        have e : (⟨x, hxP⟩ : ↥(parP h)) ^ m = 1 := Subtype.ext hxm
        rw [e, map_one]
        rfl
      have hρ6 := (burnsideF4m_gu2_K h).1 _ (burnsideF4m_rho_unitary h hxP)
      have h1 := orderOf_dvd_of_pow_eq_one hρm
      have h2 := orderOf_dvd_of_pow_eq_one hρ6
      have h3 : orderOf (rho h x) ∣ 3 := by
        have hg := Nat.dvd_gcd h1 h2
        have : Nat.gcd m 6 ∣ 3 := by
          have hodd : Nat.Coprime m 2 := Nat.coprime_two_right.mpr hm
          have hc : Nat.Coprime (Nat.gcd m 6) 2 :=
            Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left m 6) hodd
          exact Nat.Coprime.dvd_of_dvd_mul_right hc
            (show Nat.gcd m 6 ∣ 3 * 2 from Nat.gcd_dvd_right m 6)
        exact hg.trans this
      exact orderOf_dvd_iff_pow_eq_one.mp h3
    | one =>
      have e : (⟨1, hRP (Subgroup.one_mem _)⟩ : ↥(parP h)) = 1 := rfl
      rw [e, map_one]
      exact (burnsideF4m_u4S h).one_mem
    | mul x y hx hy ihx ihy =>
      have := (burnsideF4m_u4S h).mul_mem ihx ihy
      rw [← map_mul] at this
      exact this
    | inv x hx ihx =>
      have := (burnsideF4m_u4S h).inv_mem ihx
      rw [← map_inv] at this
      exact this
  have hrange : ψ.range ≤ burnsideF4m_u4S h := by
    rintro _ ⟨⟨r, hr⟩, rfl⟩
    exact hgen r hr
  have := h.finite
  haveI : Finite (Kˣ × GL (Fin 2) K) := inferInstance
  have hodd : ¬ 2 ∣ Nat.card ψ.range := by
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ψ.range) 2 h2
    have hx3 : x ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact burnsideF4m_u4S_cube h (hrange x.2))
    have := orderOf_dvd_of_pow_eq_one hx3
    rw [hx] at this
    norm_num at this
  have hker : ψ.ker ≤ (R ⊓ radQ h).subgroupOf R := by
    intro r hr
    rw [MonoidHom.mem_ker] at hr
    have h1 := congrArg (fun p : Kˣ × GL (Fin 2) K => ((p.1 : Kˣ) : K)) hr
    have h2 := congrArg (fun p : Kˣ × GL (Fin 2) K => ((p.2 : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K)) hr
    simp only [Prod.fst_one, Prod.snd_one, Units.val_one] at h1 h2
    rw [Subgroup.mem_subgroupOf]
    exact ⟨r.2, mem_radQ_of_chi_rho h (hRP r.2) h1 h2⟩
  have hidx : ¬ 2 ∣ ((R ⊓ radQ h).subgroupOf R).index := by
    intro h2
    apply hodd
    rw [← Subgroup.index_ker]
    exact h2.trans (Subgroup.index_dvd_of_le hker)
  have hNP : R ⊓ radQ h ≤ pCoreOf 2 R := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((radQ_isPGroup h).to_le inf_le_right)
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hN := Subgroup.mem_normalizer_iff.mp (parP_le_normalizer_radQ h (hRP hg)) y
    have hN' := Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoRes (parP h) (hRP hg)) y
    exact ⟨fun ⟨h1, h2⟩ => ⟨hN'.mp h1, hN.mp h2⟩, fun ⟨h1, h2⟩ => ⟨hN'.mpr h1, hN.mpr h2⟩⟩
  refine ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 R, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 R,
    fun h2 => hidx (h2.trans ?_)⟩
  exact Subgroup.index_dvd_of_le (fun x hx => hNP hx)

end Model

section Ext

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_u4_sq_mem (hyp : HypF_4_4g .U4 2 1 Gp M₁ M₂) (e : E) : e * e ∈ Gp := by
  haveI := hyp.normal
  obtain ⟨K, fK, h, Φ, -, -⟩ := burnsideF4m_U4_chart hyp
  set Θ : E →* MulAut (hypSU h 2 0) :=
    (MulAut.congr Φ.symm).toMonoidHom.comp (burnsideF4d_rho Gp) with hΘdef
  have hΘinj : Function.Injective Θ :=
    (MulAut.congr Φ.symm).injective.comp (burnsideF4d_rho_injective hyp.centralizer_trivial)
  have hΘapp : ∀ (e : E) (y : hypSU h 2 0), ((Φ (Θ e y) : ↥Gp) : E) = e * Φ y * e⁻¹ := by
    intro e y
    show ((Φ (Φ.symm (burnsideF4d_rho Gp e (Φ y))) : ↥Gp) : E) = _
    rw [MulEquiv.apply_symm_apply, burnsideF4d_rho_apply]
  obtain ⟨a, τ, hδ⟩ := burnsideF4m_U4_normalForm h (Θ e)
  have hττ : ∀ y, burnsideF4m_U4_fieldAut h τ (burnsideF4m_U4_fieldAut h τ y) = y := by
    intro y
    have := congrArg (fun α : MulAut (hypSU h 2 0) => α y)
      (show burnsideF4m_U4_fieldAut h τ * burnsideF4m_U4_fieldAut h τ = 1 by
        rw [← map_mul, burnsideF4m_ringEquiv_sq h τ, map_one])
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  set b : hypSU h 2 0 := a * burnsideF4m_U4_fieldAut h τ a with hb
  have hsq : Θ (e * e) = MulAut.conj b := by
    rw [map_mul, hδ]
    refine MulEquiv.ext fun y => ?_
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply,
      MulAut.conj_apply, map_mul, map_mul, map_inv, hττ, hb]
    group
  have hΘb : Θ ((Φ b : ↥Gp) : E) = MulAut.conj b := by
    refine MulEquiv.ext fun y => Φ.injective (Subtype.ext ?_)
    rw [hΘapp, MulAut.conj_apply]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have := hΘinj (hsq.trans hΘb.symm)
  rw [this]
  exact (Φ b).2

theorem burnsideF4m_u4_oTwoRes_eq (hyp : HypF_4_4g .U4 2 1 Gp M₁ M₂) (M : Subgroup E) :
    oTwoRes M = oTwoRes (Gp ⊓ M) := by
  apply le_antisymm
  · apply Subgroup.closure_mono
    rintro x ⟨hxM, m, hm, hxm⟩
    refine ⟨⟨?_, hxM⟩, m, hm, hxm⟩
    obtain ⟨k, rfl⟩ := hm
    have hx : x = (x * x) ^ (k + 1) := by
      rw [← pow_two, ← pow_mul, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, hxm, one_mul]
    rw [hx]
    exact Subgroup.pow_mem _ (burnsideF4m_u4_sq_mem hyp x) _
  · exact Subgroup.closure_mono fun x hx => ⟨hx.1.2, hx.2⟩

theorem burnsideF4m_core_isSylowTwoOf_map {D : Type} [Group D] (φ : D →* E)
    (hφ : Function.Injective φ) {S X : Subgroup D}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S X) :
    CFSG.QuasithinUnique.IsSylowTwoOf (S.map φ) (X.map φ) := by
  refine ⟨Subgroup.map_mono hS.1, hS.2.1.of_equiv (Subgroup.equivMapOfInjective S φ hφ), ?_⟩
  have e : ∀ (A B : Subgroup D), (A.subgroupOf B).index = A.relIndex B := fun _ _ => rfl
  have e' : ∀ (A B : Subgroup E), (A.subgroupOf B).index = A.relIndex B := fun _ _ => rfl
  have := hS.2.2
  rw [e] at this
  rw [e', Subgroup.relIndex_map_map_of_injective S X hφ]
  exact this

theorem burnsideF4m_f436_U4_twoClosed (hyp : HypF_4_4 .U4 2 1 Gp M₁ M₂) :
    CFSG.QuasithinUnique.IsSylowTwoOf (pCoreOf 2 (oTwoRes M₁)) (oTwoRes M₁) := by
  obtain ⟨K, fK, h, Φ, h1, -⟩ := burnsideF4m_U4_chart hyp.toHypF_4_4g
  have hφ : Function.Injective (Gp.subtype.comp Φ.toMonoidHom) :=
    Gp.subtype_injective.comp Φ.injective
  rw [burnsideF4m_u4_oTwoRes_eq hyp.toHypF_4_4g M₁, h1, burnsideF4m_oTwoRes_map _ hφ,
    CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφ]
  exact burnsideF4m_core_isSylowTwoOf_map _ hφ (burnsideF4m_u4_parP_twoClosed h)

theorem burnsideF4m_f436Input_U4 {f : ℕ} (hyp : HypF_4_4 .U4 2 f Gp M₁ M₂) (hf : f = 1) :
    CFSG.QuasithinUnique.IsSylowTwoOf (pCoreOf 2 (oTwoRes M₁)) (oTwoRes M₁) ∧
    ∀ Tb : Subgroup E, ChF.IsSylowOf 2 Tb (M₁ ⊓ M₂) →
      ∀ fb ∈ Tb, hyp.toHypF_4_4g.chart.IsGraphInv fb →
        ∃ r ∈ Tb, (∃ g : E, g * fb * g⁻¹ = r) ∧
          ((pCoreOf 2 (oTwoRes (cenIn (Gp ⊓ M₁) r)) ≤ cenIn (Gp ⊓ M₂) r ∧
              ¬ pCoreOf 2 (oTwoRes (cenIn (Gp ⊓ M₁) r)) ≤ pCoreOf 2 (cenIn (Gp ⊓ M₂) r)) ∨
            (pCoreOf 2 (oTwoRes (cenIn (Gp ⊓ M₂) r)) ≤ cenIn (Gp ⊓ M₁) r ∧
              ¬ pCoreOf 2 (oTwoRes (cenIn (Gp ⊓ M₂) r)) ≤ pCoreOf 2 (cenIn (Gp ⊓ M₁) r))) := by
  subst hf
  exact ⟨burnsideF4m_f436_U4_twoClosed hyp, burnsideF4m_f436_U4_V hyp⟩

end Ext

end CFSG.ASVolI
