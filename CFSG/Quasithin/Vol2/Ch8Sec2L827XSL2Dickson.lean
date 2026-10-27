module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827XSL2Basis
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XSL2Matrix
public import CFSG.Quasithin.Background.F6CatDickson
public import CFSG.Quasithin.Background.DicksonPerfectBasic

public section

namespace CFSG.Quasithin.H13.L827X.SL2Orb

open scoped MatrixGroups

section Dickson

variable {p : ℕ} [Fact p.Prime]

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h'
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have h2 := (Fact.out (p := p.Prime)).two_le
  omega

variable {E : Type*} [AddCommGroup E] [Module (ZMod p) E]

@[expose] noncomputable def slHom (b : Module.Basis (Fin 2) (ZMod p) E) (Λ : Subgroup (E ≃ₗ[ZMod p] E))
    [Group.IsPerfect Λ] : Λ →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) where
  toFun g := ⟨matHom b (g : E ≃ₗ[ZMod p] E), by
    rw [det_matHom, det_eq_one_of_isPerfect Λ g]
    simp⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by
    show matHom b ((g * h : Λ) : E ≃ₗ[ZMod p] E) =
      matHom b (g : E ≃ₗ[ZMod p] E) * matHom b (h : E ≃ₗ[ZMod p] E)
    exact map_mul _ _ _)

theorem slHom_coe (b : Module.Basis (Fin 2) (ZMod p) E) (Λ : Subgroup (E ≃ₗ[ZMod p] E))
    [Group.IsPerfect Λ] (g : Λ) :
    ((slHom b Λ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) = matHom b (g : E ≃ₗ[ZMod p] E) := rfl

theorem slHom_injective (b : Module.Basis (Fin 2) (ZMod p) E) (Λ : Subgroup (E ≃ₗ[ZMod p] E))
    [Group.IsPerfect Λ] : Function.Injective (slHom b Λ) := by
  intro g h hgh
  apply Subtype.ext
  apply matHom_injective b
  exact congrArg Subtype.val hgh

@[expose] noncomputable def sigma (p : ℕ) [Fact p.Prime] : ZMod p →+* GaloisField p 1 :=
  (GaloisField.equivZmodP p).symm.toRingHom

theorem sigma_injective (p : ℕ) [Fact p.Prime] : Function.Injective (sigma p) :=
  (sigma p).injective

@[expose] noncomputable def psiHom (b : Module.Basis (Fin 2) (ZMod p) E) (Λ : Subgroup (E ≃ₗ[ZMod p] E))
    [Group.IsPerfect Λ] : Λ →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 1) :=
  (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1)))).comp
    ((Matrix.SpecialLinearGroup.map (sigma p)).comp (slHom b Λ))

theorem mapMatrix_neg_one (p : ℕ) [Fact p.Prime] :
    (RingHom.mapMatrix (sigma p)) (-1 : Matrix (Fin 2) (Fin 2) (ZMod p)) = -1 :=
  ((RingHom.mapMatrix (sigma p)).map_neg (1 : Matrix (Fin 2) (Fin 2) (ZMod p))).trans
    (congrArg Neg.neg (RingHom.mapMatrix (sigma p)).map_one)

theorem map_mem_center_of_pm (M : Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hM : (M : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 ∨
      (M : Matrix (Fin 2) (Fin 2) (ZMod p)) = -1) :
    Matrix.SpecialLinearGroup.map (sigma p) M ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1)) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rcases hM with hM | hM
  · refine ⟨1, by simp, ?_⟩
    rw [Matrix.SpecialLinearGroup.map_apply_coe, hM]
    exact (map_one (Matrix.scalar (Fin 2))).trans (map_one (RingHom.mapMatrix (sigma p))).symm
  · refine ⟨-1, by simp, ?_⟩
    rw [Matrix.SpecialLinearGroup.map_apply_coe, hM]
    exact ((Matrix.scalar (Fin 2)).map_neg (1 : GaloisField p 1)).trans
      ((congrArg Neg.neg (Matrix.scalar (Fin 2)).map_one).trans
        (mapMatrix_neg_one p).symm)

theorem psi_eq_one_iff (b : Module.Basis (Fin 2) (ZMod p) E) (Λ : Subgroup (E ≃ₗ[ZMod p] E))
    [Group.IsPerfect Λ] (g : Λ) :
    psiHom b Λ g = 1 ↔
      (matHom b (g : E ≃ₗ[ZMod p] E) = 1 ∨ matHom b (g : E ≃ₗ[ZMod p] E) = -1) := by
  constructor
  · intro hg
    have hmem : Matrix.SpecialLinearGroup.map (sigma p) (slHom b Λ g) ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1)) := by
      have h1 : (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1))))
          (Matrix.SpecialLinearGroup.map (sigma p) (slHom b Λ g)) = 1 := hg
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hpm := center_map_eq_pm (sigma p) (sigma_injective p) (slHom b Λ g) hmem
    rw [slHom_coe] at hpm
    exact hpm
  · intro hpm
    have hpm' : ((slHom b Λ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 ∨
        ((slHom b Λ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) = -1 := by
      rw [slHom_coe]
      exact hpm
    show (QuotientGroup.mk' (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1))))
          (Matrix.SpecialLinearGroup.map (sigma p) (slHom b Λ g)) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact map_mem_center_of_pm _ hpm'

theorem psi_ker_eq (b : Module.Basis (Fin 2) (ZMod p) E) (Λ : Subgroup (E ≃ₗ[ZMod p] E))
    [Group.IsPerfect Λ] (g : Λ) (hg : psiHom b Λ g = 1) :
    (g : E ≃ₗ[ZMod p] E) = 1 ∨ (g : E ≃ₗ[ZMod p] E) = LinearEquiv.neg (ZMod p) := by
  rcases (psi_eq_one_iff b Λ g).mp hg with h | h
  · left
    apply matHom_injective b
    rw [h, map_one]
  · right
    apply matHom_injective b
    rw [h, matHom_neg]
    rfl

theorem comm_of_pm (u v : E ≃ₗ[ZMod p] E) (hu : u = 1 ∨ u = LinearEquiv.neg (ZMod p)) :
    u * v = v * u := by
  rcases hu with rfl | rfl
  · simp
  · apply LinearEquiv.ext
    intro x
    simp

theorem psi_range_not_solvable (b : Module.Basis (Fin 2) (ZMod p) E)
    (Λ : Subgroup (E ≃ₗ[ZMod p] E)) [Group.IsPerfect Λ] (hns : ¬ Group.IsSolvable Λ) :
    ¬ Group.IsSolvable (psiHom b Λ).range := by
  intro hH
  have hkerComm : IsMulCommutative (psiHom b Λ).ker := by
    refine ⟨⟨fun a c => ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact comm_of_pm _ _ (psi_ker_eq b Λ a.1 a.2)
  haveI := hkerComm
  apply hns
  exact Group.isSolvable_of_ker_le_range (psiHom b Λ).ker.subtype (psiHom b Λ).rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

theorem neg_ne_one (hp2 : p ≠ 2) (b : Module.Basis (Fin 2) (ZMod p) E) :
    LinearEquiv.neg (ZMod p) ≠ (1 : E ≃ₗ[ZMod p] E) := by
  intro h
  have h0 : (LinearEquiv.neg (ZMod p) : E ≃ₗ[ZMod p] E) (b 0) = (1 : E ≃ₗ[ZMod p] E) (b 0) := by
    rw [h]
  have h0' : -(b 0) = b 0 := by simpa using h0
  have h2 : (2 : ZMod p) • b 0 = 0 := by
    rw [two_smul]
    exact neg_eq_iff_add_eq_zero.mp h0'
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact two_ne_zero_zmod hp2 h3
  · exact b.ne_zero 0 h3

theorem neg_mem_of_involution (hp2 : p ≠ 2) (b : Module.Basis (Fin 2) (ZMod p) E)
    (Λ : Subgroup (E ≃ₗ[ZMod p] E)) [Group.IsPerfect Λ]
    (h : (psiHom b Λ).range) (hh1 : h ≠ 1) (hh2 : h * h = 1) :
    ∃ n : Λ, (n : E ≃ₗ[ZMod p] E) = LinearEquiv.neg (ZMod p) := by
  obtain ⟨t, ht⟩ := h.2
  have hht : psiHom b Λ t = h.1 := ht
  have hu : psiHom b Λ (t * t) = 1 := by
    rw [map_mul, hht]
    have := congrArg Subtype.val hh2
    simpa using this
  rcases psi_ker_eq b Λ (t * t) hu with h1 | h1
  ·
    exfalso
    have hM : matHom b (t : E ≃ₗ[ZMod p] E) * matHom b (t : E ≃ₗ[ZMod p] E) = 1 := by
      rw [← map_mul, ← Subgroup.coe_mul, h1, map_one]
    have hdet : (matHom b (t : E ≃ₗ[ZMod p] E)).det = 1 := by
      rw [det_matHom, det_eq_one_of_isPerfect Λ t]
      simp
    have hpm := sq_eq_one_of_det_one _ hdet hM (two_ne_zero_zmod hp2)
    apply hh1
    apply Subtype.ext
    rw [← hht]
    simp only [OneMemClass.coe_one]
    exact (psi_eq_one_iff b Λ t).mpr hpm
  · exact ⟨t * t, h1⟩

theorem card_eq_two_mul_range (hp2 : p ≠ 2) (b : Module.Basis (Fin 2) (ZMod p) E)
    (Λ : Subgroup (E ≃ₗ[ZMod p] E)) [Group.IsPerfect Λ] (n : Λ)
    (hn : (n : E ≃ₗ[ZMod p] E) = LinearEquiv.neg (ZMod p)) :
    Nat.card Λ = 2 * Nat.card (psiHom b Λ).range := by
  have hnker : psiHom b Λ n = 1 :=
    (psi_eq_one_iff b Λ n).mpr (Or.inr (by rw [hn, matHom_neg]; rfl))
  have hcard : Nat.card (psiHom b Λ).ker = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨n, hnker⟩, ?_, ?_⟩
    · intro h
      apply neg_ne_one hp2 b
      rw [← hn]
      have := congrArg (fun z : (psiHom b Λ).ker => (z : Λ) : _ → E ≃ₗ[ZMod p] E) h
      simp only [OneMemClass.coe_one] at this
      exact this.symm
    · ext z
      simp only [Set.mem_univ, iff_true, Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases psi_ker_eq b Λ z.1 z.2 with h1 | h1
      · left
        exact Subtype.ext (Subtype.ext h1)
      · right
        exact Subtype.ext (Subtype.ext (h1.trans hn.symm))
  have hidx : (psiHom b Λ).ker.index = Nat.card (psiHom b Λ).range := Subgroup.index_ker _
  rw [← Subgroup.card_mul_index (psiHom b Λ).ker, hcard, hidx]

theorem core_disj [Module.Finite (ZMod p) E] (hp2 : p ≠ 2)
    (hE : Module.finrank (ZMod p) E = 2)
    (Λ : Subgroup (E ≃ₗ[ZMod p] E)) [Group.IsPerfect Λ] (hns : ¬ Group.IsSolvable Λ) :
    Nat.card Λ = 120 ∨ p * (p ^ 2 - 1) ≤ Nat.card Λ := by
  classical
  let b : Module.Basis (Fin 2) (ZMod p) E := Module.finBasisOfFinrankEq (ZMod p) E hE
  have hHns := psi_range_not_solvable b Λ hns
  have hdic := CFSG.Quasithin.F6.dicksonPSL2_holds p 1 (le_refl 1) (psiHom b Λ).range
  rcases hdic with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h8'
  ·
    exfalso
    obtain ⟨⟨hcomm, -⟩, -⟩ := h1
    haveI := hcomm
    exact hHns inferInstance
  ·
    exfalso
    obtain ⟨hcyc, -⟩ := h2
    haveI := hcyc
    exact hHns inferInstance
  ·
    exfalso
    obtain ⟨z, -, ⟨e⟩⟩ := h3
    haveI : Group.IsSolvable (DihedralGroup z) :=
      CFSG.Quasithin.Dickson.isSolvable_dihedral z
    exact hHns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  ·
    exfalso
    obtain ⟨-, ⟨e⟩⟩ := h4
    haveI : Group.IsSolvable (alternatingGroup (Fin 4)) :=
      alternatingGroup.isSolvable (by simp)
    exact hHns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  ·
    exfalso
    obtain ⟨-, ⟨e⟩⟩ := h5
    haveI : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
    exact hHns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  ·
    obtain ⟨-, ⟨e⟩⟩ := h6
    obtain ⟨τ, hτ1, hτ2⟩ := exists_involution_alt_five
    have hcard : Nat.card (psiHom b Λ).range = 60 := by
      rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fin_five]
    have hh1 : e.symm τ ≠ 1 := by
      intro hc
      apply hτ1
      have := congrArg e hc
      simpa using this
    have hh2 : e.symm τ * e.symm τ = 1 := by
      rw [← map_mul e.symm, hτ2, map_one]
    obtain ⟨n, hn⟩ := neg_mem_of_involution hp2 b Λ (e.symm τ) hh1 hh2
    have hΛcard := card_eq_two_mul_range hp2 b Λ n hn
    left
    rw [hΛcard, hcard]
  ·
    exfalso
    obtain ⟨m, t, P, hPn, hPel, -, hQcyc, -⟩ := h7
    haveI := hPn
    haveI := hPel.1
    haveI : IsCyclic ((psiHom b Λ).range ⧸ P) := hQcyc
    exact hHns (Group.isSolvable_of_subgroup_quotient P)
  ·
    obtain ⟨m, hm, ⟨e⟩⟩ := h8
    have hm1 : m = 1 := Nat.dvd_one.mp hm
    subst hm1
    obtain ⟨h0, hh0, hh0'⟩ := exists_involution_psl (GaloisField p 1)
    have hh1 : e.symm h0 ≠ 1 := by
      intro hc
      apply hh0
      have := congrArg e hc
      simpa using this
    have hh2 : e.symm h0 * e.symm h0 = 1 := by
      rw [← map_mul e.symm, hh0', map_one]
    obtain ⟨n, hn⟩ := neg_mem_of_involution hp2 b Λ (e.symm h0) hh1 hh2
    have hΛcard := card_eq_two_mul_range hp2 b Λ n hn
    have hcardH : Nat.card (psiHom b Λ).range =
        Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 1)) :=
      Nat.card_congr e.toEquiv
    have hGF : Nat.card (GaloisField p 1) = p := by
      rw [GaloisField.card p 1 one_ne_zero, pow_one]
    have hSL := card_SL_two (GaloisField p 1)
    rw [hGF] at hSL
    have hle := card_SL_le_two_mul_PSL (GaloisField p 1)
    right
    rw [hΛcard, hcardH, ← hSL]
    omega
  ·
    exfalso
    obtain ⟨m, hm, -⟩ := h8'
    have h2m : 2 * m = 1 := Nat.dvd_one.mp hm
    omega

end Dickson

end CFSG.Quasithin.H13.L827X.SL2Orb

end
