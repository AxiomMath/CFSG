module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartF
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12c
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12
public import CFSG.Quasithin.Vol2.Ch11SecAFacts12b

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open Matrix CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat
  CFSG.ClassicalInvolution.ModelFacts.OddCover CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin.Vol2.Ch11.SecS CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Open (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedSL)

namespace C11P9B

variable {K : Type} [Field K] {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem exists_coord_torus3 [Finite K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hW : ∀ w : W, w ^ 2 = 1) (hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia H ⊤ Z π)
    {P : Subgroup (MulAut W)} (hP : QuasithinUnique.IsSylowTwoOf P H) {D : Subgroup (MulAut W)}
    (hD : QuasithinUnique.Lin2.IsHallTwoPrimeOf D
      (H ⊓ Subgroup.normalizer (P : Set (MulAut W)))) :
    ∃ (f : W → (Fin 3 → K)) (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
      (g : SpecialLinearGroup (Fin 3) K), D = (torus3 K).map (psiW π g) ∧
      (∀ U, IsFlagW H P Z (Nat.card K) 1 U →
        U = hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup) ∧
      ∀ U, IsFlagW H P Z (Nat.card K) 2 U →
        U = hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup := by
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  rw [eq_map_psiW_of_sylow hg, inf_normalizer_eq hf g] at hD
  obtain ⟨x, hx, hDx⟩ := exists_eq_map_torus3 hf g hD
  have hg' := sylow_conj_mul hg hx
  exact ⟨f, hf, g * x, hDx, fun U hU => eq_U1_of_isFlagW hW hf hg' hU,
    fun U hU => eq_U2_of_isFlagW hW hf hg' hU⟩

theorem centW_one_eq [Finite K] [CharP K 2] [Finite W]
    (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (g : SpecialLinearGroup (Fin 3) K) :
    centW ((torus3 K).map (psiW π g))
        (gammaW H (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)) =
      (torus3 K ⊓ sectionCentralizer (stabE0 K) (rad1 K)).map (psiW π g) := by
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hψ := psiW_injective hf g
  unfold centW
  rw [gammaW_one_eq hSL hf, pCoreOf_map_of_injective _ hψ, pCoreOf_stabE0,
    map_inf_sectionCentralizer _ hψ]

theorem mulVec_eq_of_triv (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    (g A : SpecialLinearGroup (Fin 3) K) {S : Submodule K (Fin 3 → K)}
    (htriv : ∀ u ∈ hf.pre (gmap g S).toAddSubgroup, psiW π g A u * u⁻¹ ∈ Z)
    {e : Fin 3 → K} (he : e ∈ S) : (A : Matrix (Fin 3) (Fin 3) K) *ᵥ e = e := by
  obtain ⟨u, hu⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ e)
  have hu1 : u ∈ hf.pre (gmap g S).toAddSubgroup := by
    show f u ∈ gmap g S
    rw [mem_gmap, hu, ginv_g_mulVec]
    exact he
  have h1 := htriv u hu1
  rw [← hf.ker, hf.map_mul_inv, psiW_apply, hf.act3, gconj_mulVec, hu, ginv_g_mulVec,
    sub_eq_zero] at h1
  have h2 := congrArg (fun v => ((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) *ᵥ v) h1
  simpa only [ginv_g_mulVec] using h2

theorem eq_one_of_sq_eq_one [CharP K 2] {s : Kˣ} (hs : s ^ 2 = 1) : s = 1 := by
  refine Units.ext (frobenius_inj K 2 ?_)
  rw [frobenius_def, frobenius_def, Units.val_one, one_pow, ← Units.val_pow_eq_pow_val, hs,
    Units.val_one]

theorem tvec_eq_of_three {t : Kˣ × Kˣ} (h1 : t.1 * t.2 ^ 2 = 1) (h3 : t.2 ^ 3 = 1) :
    tvec t = fun _ => (t.2 : K) := by
  have e1 : t.1 = t.2 := by
    rw [eq_inv_of_mul_eq_one_left h1]
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← pow_succ', h3]
  have e2 : (t.1 * t.2)⁻¹ = t.2 := by
    rw [e1, ← pow_two]
    exact (eq_inv_of_mul_eq_one_left (by rw [← pow_succ', h3])).symm
  funext i
  fin_cases i
  · show ((t.1 : Kˣ) : K) = t.2
    rw [e1]
  · rfl
  · show (((t.1 * t.2)⁻¹ : Kˣ) : K) = t.2
    rw [e2]

theorem tSL_mulVec_of_three {t : Kˣ × Kˣ} (h1 : t.1 * t.2 ^ 2 = 1) (h3 : t.2 ^ 3 = 1)
    (x : Fin 3 → K) :
    ((tSL t : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x =
      (t.2 : K) • x := by
  rw [coe_tSL, tvec_eq_of_three h1 h3, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
    Matrix.one_mulVec]

theorem tSL_comm_of_three {t : Kˣ × Kˣ} (h1 : t.1 * t.2 ^ 2 = 1) (h3 : t.2 ^ 3 = 1)
    (A : SpecialLinearGroup (Fin 3) K) : tSL t * A = A * tSL t := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_tSL,
    tvec_eq_of_three h1 h3, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]

end C11P9B

open C11P9B

theorem factCartanPointSL3_holds : FactCartanPointSL3 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U₁ hU₁ D hD
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  obtain ⟨f, hf, g, rfl, hU1, -⟩ := exists_coord_torus3 hn hK hW hπ hP hD
  rw [hU1 U₁ (by rw [hK]; exact hU₁)]
  intro d hd htriv
  rw [centW_one_eq hSL hf g] at hd
  obtain ⟨A, ⟨⟨t, rfl⟩, hA⟩, rfl⟩ := hd
  have h1 := (tSL_mem_sc1_iff t).mp hA
  have he0 := mulVec_eq_of_triv hf g (tSL t) htriv (e := ![1, 0, 0])
    (by rw [← stdLine_eq_flagSpace]; exact ⟨rfl, rfl⟩)
  rw [tSL_mulVec_e0] at he0
  have ht1 : t.1 = 1 := by
    have := congrFun he0 0
    simpa using this
  rw [ht1, one_mul] at h1
  rw [show t = 1 from Prod.ext ht1 (eq_one_of_sq_eq_one h1), map_one, map_one]

theorem factCartanLineSL3_holds : FactCartanLineSL3 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U₂ hU₂ D hD
  obtain ⟨f, hf, g, rfl, -, hU2⟩ := exists_coord_torus3 hn hK hW hπ hP hD
  rw [hU2 U₂ (by rw [hK]; exact hU₂)]
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩ htriv
  have h0 := mulVec_eq_of_triv hf g (tSL t) htriv (e := ![1, 0, 0])
    (by rw [← stdPlane_eq_flagSpace]; exact mem_stdPlane.mpr rfl)
  have h1 := mulVec_eq_of_triv hf g (tSL t) htriv (e := ![0, 1, 0])
    (by rw [← stdPlane_eq_flagSpace]; exact mem_stdPlane.mpr rfl)
  rw [tSL_mulVec] at h0 h1
  have ht1 : t.1 = 1 := by
    have := congrFun h0 0
    simpa using this
  have ht2 : t.2 = 1 := by
    have := congrFun h1 1
    simpa using this
  rw [show t = 1 from Prod.ext ht1 ht2, map_one, map_one]

theorem factSL34Center_holds : FactSL34Center := by
  intro K _ _ hK W _ _ hW H Z π hπ P hP U₁ hU₁ D hD
  have hK' : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK'
  have hSL := commutator_SL2_eq_top (four_le_card le_rfl hK')
  obtain ⟨f, hf, g, rfl, hU1, -⟩ := exists_coord_torus3 le_rfl hK' hW hπ hP hD
  rw [hU1 U₁ (by rw [hK]; exact hU₁), centW_one_eq hSL hf g]
  have h3 : ∀ s : Kˣ, s ^ 3 = 1 := fun s => by
    have h := pow_card_eq_one' (G := Kˣ) (x := s)
    rw [Nat.card_units, hK] at h
    exact h
  refine ⟨?_, ?_⟩
  · rintro _ ⟨_, ⟨⟨t, rfl⟩, hA⟩, rfl⟩ h hh
    obtain ⟨A, rfl⟩ := exists_psiW_eq hf g hh
    rw [← map_mul, ← map_mul, tSL_comm_of_three ((tSL_mem_sc1_iff t).mp hA) (h3 t.2) A]
  · rintro _ ⟨_, ⟨⟨t, rfl⟩, hA⟩, rfl⟩ hne w hw
    have h1 := (tSL_mem_sc1_iff t).mp hA
    have hc : (t.2 : K) ≠ 1 := by
      intro hc
      have ht2 : t.2 = 1 := Units.ext hc
      have ht1 : t.1 = 1 := by
        rw [ht2, one_pow, mul_one] at h1
        exact h1
      exact hne (by rw [show t = 1 from Prod.ext ht1 ht2, map_one, map_one])
    have hfw := congrArg f hw
    rw [psiW_apply, hf.act3, gconj_mulVec, tSL_mulVec_of_three h1 (h3 t.2), Matrix.mulVec_smul,
      g_ginv_mulVec] at hfw
    rw [← hf.ker]
    have h2 : ((t.2 : K) - 1) • f w = 0 := by rw [sub_smul, hfw, one_smul, sub_self]
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hc)

end CFSG.Quasithin.Vol2.Ch11.SecA
