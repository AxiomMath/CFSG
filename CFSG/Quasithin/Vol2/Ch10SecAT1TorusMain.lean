module

public import CFSG.Quasithin.Vol2.Ch10SecAT1Torus

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_torus_element
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) {n : ℕ} (h1 : Ch10.Case10_1_1One T L I n) :
    ∃ h ∈ L, h ∈ Subgroup.normalizer (T0 T L : Set G) ∧ Odd (orderOf h) ∧
      ¬ ∀ u ∈ fsuUL T L I, h * u * h⁻¹ = u := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    push Not at h
    exact hyp.not_normal h
  obtain ⟨hUab, F, _, _, _, hn, hF, ⟨c⟩⟩ := exists_natCoord hyp h1
  have := Fintype.ofFinite F
  have hloc := hyp.fsu.maximal.1
  have hLU : L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator ((le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I))
      Subgroup.le_normalizer
  obtain ⟨a, ha0, ha1⟩ : ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hs : Function.Surjective (fun b : Bool => if b then (1 : F) else 0) := by
      intro a
      by_cases h0 : a = 0
      · exact ⟨false, by simp [h0]⟩
      · exact ⟨true, by simp [hcon a h0]⟩
    have h2 := Nat.card_le_card_of_surjective _ hs
    rw [hF] at h2
    simp only [Nat.card_eq_fintype_card, Fintype.card_bool] at h2
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  set γ := c.g⁻¹ * diagSL ha0 * c.g with hγ
  have hφN := c.mem_normalizer (diagSL_conj_iff ha0)
  obtain ⟨g', hg'L, hg'⟩ := mem_autOn_iff'.mp (c.eρ γ).2
  have hchar : ∀ s (hs : s ∈ L), s ∈ T ⊓ L ↔
      conjAct (fsuUL T L I) ⟨s, hLU hs⟩ ∈ autOn (T ⊓ L) (fsuUL T L I) := by
    intro s hs
    refine ⟨fun h => mem_autOn_iff'.mpr ⟨_, h, rfl⟩, fun h => ?_⟩
    obtain ⟨s', hs'K, hs'⟩ := mem_autOn_iff'.mp h
    have h2 : conjAct (fsuUL T L I) (⟨s, hLU hs⟩ * s'⁻¹) = 1 := by
      rw [map_mul, map_inv, hs', mul_inv_cancel]
    have hy : ∀ u ∈ fsuUL T L I, s * (s' : G)⁻¹ * u * (s * (s' : G)⁻¹)⁻¹ = u := by
      intro u hu
      have e := congrArg (fun f : MulAut ↥(fsuUL T L I) => ((f ⟨u, hu⟩ : ↥(fsuUL T L I)) : G)) h2
      simp only [coe_conjAct_apply', MulAut.one_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at e
      exact e
    have hyT := mem_T_of_forall_conj_eq h37 h38 hyp ht htn (L.mul_mem hs (L.inv_mem hs'K.2)) hy
    refine ⟨?_, hs⟩
    have e : s = s * (s' : G)⁻¹ * s' := by group
    rw [e]
    exact T.mul_mem hyT hs'K.1
  have hlN : (g' : G) ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    by_cases hs : s ∈ L
    · have hls : (g' : G) * s * (g' : G)⁻¹ ∈ L := L.mul_mem (L.mul_mem hg'L hs) (L.inv_mem hg'L)
      rw [hchar s hs, hchar _ hls]
      have he : conjAct (fsuUL T L I) ⟨(g' : G) * s * (g' : G)⁻¹, hLU hls⟩ =
          ((c.eρ γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) *
            conjAct (fsuUL T L I) ⟨s, hLU hs⟩ *
              ((c.eρ γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I))⁻¹ := by
        rw [← hg', ← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [he]
      exact Subgroup.mem_normalizer_iff.mp hφN _
    · constructor
      · intro h
        exact absurd h.2 hs
      · intro h
        apply absurd _ hs
        have := L.mul_mem (L.mul_mem (L.inv_mem hg'L) h.2) hg'L
        simpa [mul_assoc] using this
  have hlLt := mem_normalizer_inf_conjugate h37 hyp ht htn hg'L
  have hlO : (g' : G) ∈ Subgroup.normalizer (pCoreOf 2 (fsuL0 T L) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (le_fsuL0 T L hg'L)
  have hT0eq : T0 T L = T ⊓ L ⊔ T ⊓ CFSG.conjugate L t ⊔ pCoreOf 2 (fsuL0 T L) :=
    le_antisymm (T0_le_sup h37 h38 hyp ht htn) (sup_le (sup_le
      (inf_le_inf_left T (le_fsuL0 T L)) (inf_le_inf_left T (conjugate_le_fsuL0 ht)))
      (pCoreOf_fsuL0_le_T0 hyp.fsu.sylow))
  have hlT0 : (g' : G) ∈ Subgroup.normalizer (T0 T L : Set G) := by
    rw [hT0eq]
    exact le_normalizer_sup (le_normalizer_sup ((Subgroup.zpowers_le).mpr hlN)
      ((Subgroup.zpowers_le).mpr hlLt)) ((Subgroup.zpowers_le).mpr hlO)
      (Subgroup.mem_zpowers _)
  obtain ⟨k, m, hm, hlord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g' : G)).ne'
  refine ⟨(g' : G) ^ 2 ^ k, L.pow_mem hg'L _, Subgroup.pow_mem _ hlT0 _, ?_, fun hall => ?_⟩
  · rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hlord⟩, hlord,
      Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
    exact hm
  have h1' : conjAct (fsuUL T L I) (g' ^ 2 ^ k) = 1 := by
    ext u
    rw [coe_conjAct_apply', MulAut.one_apply]
    simpa using hall u u.2
  rw [map_pow, hg'] at h1'
  have h2 : c.eρ (γ ^ 2 ^ k) = 1 := by
    apply Subtype.ext
    simp only [map_pow, SubgroupClass.coe_pow, h1', OneMemClass.coe_one]
  rw [MulEquiv.map_eq_one_iff, hγ,
    show c.g⁻¹ * diagSL ha0 * c.g = c.g⁻¹ * diagSL ha0 * c.g⁻¹⁻¹ by rw [inv_inv], conj_pow,
    conj_eq_one_iff] at h2
  have h4 := congrArg
    (fun A : Matrix.SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h2
  simp only [diagSL_pow_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at h4
  have h5 : a ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one a ha0
  rw [← Nat.card_eq_fintype_card, hF] at h5
  have hcop : Nat.Coprime (2 ^ k) (2 ^ n - 1) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (odd_two_pow_sub_one (by omega)))
  have h6 := pow_gcd_eq_one.mpr ⟨h4, h5⟩
  rw [hcop.gcd_eq_one, pow_one] at h6
  exact ha1 h6

end CFSG.Quasithin.Vol2.Ch10.SecA
