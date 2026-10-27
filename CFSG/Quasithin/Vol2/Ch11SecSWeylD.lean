module

public import CFSG.Quasithin.Vol2.Ch11SecSWeylC
public import CFSG.Quasithin.Vol2.Ch11SecB23Two
public import CFSG.Quasithin.Vol2.Ch11SecSWeylB
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.SWeyl

open CFSG.Open CFSG.Blueprint C11P9A CFSG.QuasithinUnique.Setup.X6
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem card_center_SL3_four (hK : Nat.card K = 4) :
    Nat.card ↥(Subgroup.center (SpecialLinearGroup (Fin 3) K)) = 3 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv,
    Fintype.card_fin]
  have hu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have htop : rootsOfUnity 3 K = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [mem_rootsOfUnity, ← hu]
    exact pow_card_eq_one'
  rw [htop, Subgroup.card_top, hu]

theorem exists_unit_ne_one (hK : Nat.card K = 4) : ∃ u : Kˣ, u ≠ 1 ∧ u ^ 3 = 1 := by
  have hu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have : Nontrivial Kˣ := by
    rw [← Finite.one_lt_card_iff_nontrivial, hu]
    norm_num
  obtain ⟨u, hu1⟩ := exists_ne (1 : Kˣ)
  exact ⟨u, hu1, hu ▸ pow_card_eq_one'⟩

@[expose] noncomputable def diag2 (u : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨Matrix.diagonal ![(u : K), ((u⁻¹ : Kˣ) : K)], by simp [Matrix.det_diagonal, Fin.prod_univ_two]⟩

omit [Finite K] in
theorem levi_diag (hK4 : ∃ s : Finset K, s.card = 4) {u : Kˣ} (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1)
    (j : Fin 2) :
    embSL j (diag2 u) ∈ perfectCore (Q3 K j) ∧ (∀ i, embSL j (diag2 u) ∈ Q3 K i) ∧
      orderOf (embSL j (diag2 u)) = 3 := by
  refine ⟨le_perfectCore_of_perfect (by rintro _ ⟨A, rfl⟩; exact embSL_mem_Q3 j A)
    (embSL_range_perfect hK4 j) ⟨_, rfl⟩, fun i => ?_, ?_⟩
  · show embSL j (diag2 u) ∈ stabilizer (flagSpace 3 K ((i : ℕ) + 1))
    refine mem_stabilizer_of_entries fun k l hk hl => ?_
    rw [coe_embSL]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [embMat, diag2] at hk hl ⊢
  · have hu3' : ((u : K)) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hu3, Units.val_one]
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have h : diag2 u ^ 3 = 1 := by
        apply Matrix.SpecialLinearGroup.ext
        intro a b
        rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
        simp only [diag2, Matrix.diagonal_pow]
        fin_cases a <;> fin_cases b <;> simp [hu3', inv_pow]
      rw [h, map_one]
    · intro h
      have hinj : Function.Injective (embSL (K := K) j) := fun A B e => by
        have := congrArg (fun M : SpecialLinearGroup (Fin 3) K =>
          blkAt (1 - (j : ℕ)) 2 (q3_blk_le j) (M : Matrix (Fin 3) (Fin 3) K)) e
        simp only [coe_embSL, blkAt_embMat] at this
        exact Subtype.ext this
      have h1 : diag2 u = 1 := hinj (h.trans (map_one _).symm)
      apply hu1
      apply Units.ext
      have := congrArg (fun A : SpecialLinearGroup (Fin 2) K =>
        (A : Matrix (Fin 2) (Fin 2) K) 0 0) h1
      simpa [diag2] using this

omit [Finite K] in
theorem center_le_Q3 (i : Fin 2) : Subgroup.center (SpecialLinearGroup (Fin 3) K) ≤ Q3 K i := by
  intro A hA
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  show A ∈ stabilizer (flagSpace 3 K ((i : ℕ) + 1))
  refine mem_stabilizer_of_entries fun k l hk hl => ?_
  have hkl : k ≠ l := fun h => by
    subst h
    omega
  rw [← hr]
  simp [hkl]

theorem part2_sl3 {Q : Type} [Group Q] [Finite Q] (hK : Nat.card K = 2 ^ 2)
    (e : Q ≃* SpecialLinearGroup (Fin 3) K) {S : Subgroup Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) {B₁ B₂ : Subgroup Q} (hne : B₁ ≠ B₂)
    (h₁ : IsL24Sub S B₁) (h₂ : IsL24Sub S B₂) {E : Subgroup Q} (hE : Nat.card ↥E = 9)
    (hE₁ : E ≤ Subgroup.normalizer (B₁ : Set Q)) (hE₂ : E ≤ Subgroup.normalizer (B₂ : Set Q))
    (E₂ : Subgroup Q) (hle : E₂ ≤ E ⊓ sectionCentralizer B₂ (pCoreOf 2 B₂)) (hne₂ : E₂ ≠ ⊥) :
    ¬ Subgroup.normalizer (E₂ : Set Q) ≤ Subgroup.normalizer (B₂ : Set Q) := by
  have hK' : Nat.card K = 4 := by rw [hK]; norm_num
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by norm_num) hK
  have hK4 : ∃ s : Finset K, s.card = 4 := exists_finset_card_four (by omega)
  obtain ⟨P0, hP0⟩ := exists_sylow_unitriangular (K := K) 2 (n := 3) (by norm_num)
  have hU₀ : QuasithinUnique.IsSylowTwoOf (unitriangular 3 K) ⊤ :=
    hP0 ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P0
  have h₀ := linear_three_residual_of_cover ⟨2, hK⟩ (MonoidHom.id _) Function.surjective_id
    (by rw [MonoidHom.ker_id]; exact bot_le)
  simp only [Subgroup.map_id] at h₀
  obtain ⟨φ, hφ, hres⟩ := h₀.exists_iso_of_isSylow e hU₀ hS
  have hS' : S = (unitriangular 3 K).map φ.symm.toMonoidHom := by
    rw [← hφ]
    ext x
    simp
  have hB : ∀ j, dInf ((Q3 K j).map φ.symm.toMonoidHom) ≠ ⊥ := fun j h => by
    apply embSL_range_ne_bot hK4 j
    have hX : ((embSL (K := K) j).range).map φ.symm.toMonoidHom ≤
        dInf ((Q3 K j).map φ.symm.toMonoidHom) :=
      le_dInf_of_perfect (map_isPerfect (Subgroup.isPerfect_iff.mpr (embSL_range_perfect hK4 j)) _)
        (Subgroup.map_mono (by rintro _ ⟨A, rfl⟩; exact embSL_mem_Q3 j A))
    rw [h] at hX
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.symm.injective).mp (le_bot_iff.mp hX)
  have hN : ∀ X : Subgroup Q, X.Normal → ⁅X, X⁆ = X → X ≠ ⊥ → X = ⊤ := fun X hXn hXp hX1 =>
    eq_top_of_normal_of_equiv e (fun Y hYn hYp hY1 => eq_top_of_normal_SL3 hYn hYp hY1) hXn hXp
      hX1
  have hcardQ : Nat.card Q = 60480 := by rw [Nat.card_congr e.toEquiv, card_SL3_four hK']
  have hinf : (Q3 K 0).map φ.symm.toMonoidHom ⊓ (Q3 K 1).map φ.symm.toMonoidHom ≤
      Subgroup.normalizer (S : Set Q) := by
    rw [← Subgroup.map_inf_eq _ _ _ φ.symm.injective, inf_eq_of_covBy (covBy_Q3 0) (covBy_Q3 1)
      Q3_ne, hS', ← Subgroup.map_equiv_normalizer_eq, normalizer_unitriangular]
  have hcard : Nat.card ↥(Subgroup.normalizer (S : Set Q)) = Nat.card ↥S * 9 := by
    rw [hS', ← Subgroup.map_equiv_normalizer_eq, normalizer_unitriangular,
      Subgroup.card_map_of_injective φ.symm.injective,
      Subgroup.card_map_of_injective φ.symm.injective, card_upperTriangular_three hK']
  refine part2_of_residual hS hres hB hN (top_not_of_card hcardQ) ?_ hne h₁ h₂ hE hE₁ hE₂ E₂ hle
    hne₂
  intro j hL E hEM hE9 E₂ hle _
  obtain ⟨u, hu1, hu3⟩ := exists_unit_ne_one hK'
  obtain ⟨hd1, hd2, hd3⟩ := levi_diag hK4 hu1 hu3 j
  have hNP := normalizer_dInf_eq hres hB hN j
  have hPj : (Q3 K j).map φ.symm.toMonoidHom ≠ ⊤ :=
    ((hres.2.2.1 _ (hres.2.1 j)).mpr ⟨j, rfl⟩).lt.ne
  obtain ⟨-, -, -, F, _, _, hF, ⟨eF⟩⟩ := hL
  have h := part2_of_center (M := (Q3 K 0).map φ.symm.toMonoidHom ⊓ (Q3 K 1).map φ.symm.toMonoidHom)
    (B := dInf ((Q3 K j).map φ.symm.toMonoidHom))
    (D := Subgroup.zpowers (φ.symm (embSL j (diag2 u))))
    (not_dvd_of_borel hS.2.1 hinf hcard) hEM hE9
    (by rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, card_center_SL3_four hK'])
    (fun z hz => by
      have hφz : φ z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) :=
        (Subgroup.centerCongr φ ⟨z, hz⟩).2
      exact ⟨⟨φ z, center_le_Q3 0 hφz, by simp⟩, ⟨φ z, center_le_Q3 1 hφz, by simp⟩⟩)
    (by
      rw [hNP]
      fin_cases j
      · exact inf_le_left
      · exact inf_le_right)
    (by
      rw [Subgroup.zpowers_le, dInf_map_equiv, dInf_eq_perfectCore]
      exact ⟨_, hd1, rfl⟩)
    (by
      rw [Subgroup.zpowers_le]
      exact ⟨⟨_, hd2 0, rfl⟩, ⟨_, hd2 1, rfl⟩⟩)
    (by rw [Nat.card_zpowers, MulEquiv.orderOf_eq, hd3])
    (SecB.inf_sectionCentralizer_le (n := 2) (by rw [hF]; norm_num) (by norm_num) eF)
    (by rw [hNP]; exact hPj) E₂ hle
  rwa [hNP] at h

end CFSG.Quasithin.Vol2.Ch11.SecS.SWeyl
