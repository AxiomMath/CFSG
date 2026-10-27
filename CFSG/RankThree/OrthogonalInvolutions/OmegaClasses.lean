module

public import CFSG.RankThree.OrthogonalInvolutions.Conjugacy
public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

namespace CFSG.RankThree.OrthogonalInvolutions

open Module QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem reflection_mul_comm {Q : QuadraticForm K V} {t : V ≃ₗ[K] V}
    (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {a : V} [Invertible (Q a)]
    (ha : t a = a) :
    t * TauCeti.QuadraticMap.reflection Q a = TauCeti.QuadraticMap.reflection Q a * t := by
  ext v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, TauCeti.QuadraticMap.reflection_apply,
    TauCeti.QuadraticMap.reflection_apply, map_sub, map_smul, ha]
  congr 3
  rw [← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup htO a v, ha]

theorem two_mul_finrank_le_of_forall_eq_zero [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {U : Submodule K V} (hU : ∀ x ∈ U, Q x = 0) :
    2 * finrank K U ≤ finrank K V :=
  CFSG.LieType.BorelTits.QuadForm.IsTotallySingular.two_mul_finrank_le
    (Φ := toQuadForm Q hQ) hU

section CharTwo

variable [CharP K 2] [FiniteDimensional K V]

theorem exists_mem_fixSpace_map_ne_zero {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hn : finrank K V = 2 * m) {t : V ≃ₗ[K] V}
    (htt : t * t = 1) (hte : Even (finrank K (commSpace t)))
    (hnot : ¬(suzukiLetter Q t = .a ∧ finrank K (commSpace t) = m)) :
    ∃ a ∈ fixSpace t, Q a ≠ 0 := by
  by_contra! h
  apply hnot
  have h1 := two_mul_finrank_le_of_forall_eq_zero hQ h
  have h2 := finrank_commSpace_add_finrank_fixSpace t
  have h3 := two_mul_finrank_commSpace_le htt
  have hl : finrank K (commSpace t) = m := by omega
  exact ⟨suzukiLetter_eq_a_iff.mpr ⟨hte, fun x hx => h x (commSpace_le_fixSpace htt hx)⟩, hl⟩

theorem omega_conj_eq_of_not_typeA_half {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hn : finrank K V = 2 * m) {t : V ≃ₗ[K] V}
    (htΩ : t ∈ omegaGroup Q hQ) (ht2 : orderOf t = 2)
    (hnot : ¬(suzukiLetter Q t = .a ∧ finrank K (commSpace t) = m)) :
    {x | ∃ g ∈ omegaGroup Q hQ, g * t * g⁻¹ = x} =
      {x | ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * t * g⁻¹ = x} := by
  have htt : t * t = 1 := by rw [← pow_two]; exact (orderOf_eq_prime_iff.mp ht2).1
  have htO := htΩ.1
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg.1, rfl⟩
  rintro ⟨g, hgO, rfl⟩
  by_cases hge : Even (finrank K (commSpace g))
  · exact ⟨g, ⟨hgO, hge⟩, rfl⟩
  obtain ⟨a, ha, hQa⟩ := exists_mem_fixSpace_map_ne_zero hQ hn htt htΩ.2 hnot
  let _ : Invertible (Q a) := invertibleOfNonzero hQa
  set r := TauCeti.QuadraticMap.reflection Q a with hr
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q a
  have hcomm : t * r = r * t := reflection_mul_comm htO (mem_fixSpace.mp ha)
  refine ⟨g * r, ⟨mul_mem hgO hrO, ?_⟩, ?_⟩
  · rw [← ZMod.natCast_eq_zero_iff_even, natCast_finrank_commSpace_mul hQ hgO hrO,
      finrank_commSpace_reflection hQ a, (ZMod.natCast_eq_one_iff_odd).mpr
        (Nat.not_even_iff_odd.mp hge), Nat.cast_one]
    rfl
  · have hrt : r * t * r⁻¹ = t := by rw [← hcomm, mul_inv_cancel_right]
    calc g * r * t * (g * r)⁻¹ = g * (r * t * r⁻¹) * g⁻¹ := by group
      _ = g * t * g⁻¹ := by rw [hrt]

theorem mem_omegaGroup_iff_even_finrank_inf {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hn : finrank K V = 2 * m) {t : V ≃ₗ[K] V}
    (hta : suzukiLetter Q t = .a) (htm : finrank K (commSpace t) = m)
    {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    g ∈ omegaGroup Q hQ ↔
      Even (finrank K ↥(commSpace (g * t * g⁻¹) ⊓ commSpace t)) := by
  obtain ⟨hme, hzero⟩ := suzukiLetter_eq_a_iff.mp hta
  rw [htm] at hme
  have hcrit := natCast_finrank_sub_finrank_inf_map hQ hzero (by omega) hgO
  rw [commSpace_conj, inf_comm, mem_omegaGroup]
  have hle := Submodule.finrank_mono
    (inf_le_left : commSpace t ⊓ (commSpace t).map (g : V →ₗ[K] V) ≤ commSpace t)
  rw [htm] at hcrit hle
  rw [← ZMod.natCast_eq_zero_iff_even (n := finrank K (commSpace g)), ← hcrit,
    ZMod.natCast_eq_zero_iff_even, Nat.even_sub hle]
  exact ⟨fun h => h.2.mp hme, fun h => ⟨hgO, iff_of_true hme h⟩⟩

theorem mem_omega_conj_iff_even [Finite K] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hn : finrank K V = 2 * m) {t : V ≃ₗ[K] V}
    (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ht2 : orderOf t = 2)
    (hta : suzukiLetter Q t = .a) (htm : finrank K (commSpace t) = m) {s : V ≃ₗ[K] V}
    (hsO : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs2 : orderOf s = 2)
    (hsa : suzukiLetter Q s = .a) (hsm : finrank K (commSpace s) = m) :
    s ∈ {x | ∃ g ∈ omegaGroup Q hQ, g * t * g⁻¹ = x} ↔
      Even (finrank K ↥(commSpace s ⊓ commSpace t)) := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (mem_omegaGroup_iff_even_finrank_inf hQ hn hta htm hh.1).mp hh
  · intro he
    obtain ⟨g, hgO, rfl⟩ := (isConj_iff_suzukiLetter_eq hQ htO ht2 hsO hs2).mpr
      ⟨hsa.trans hta.symm, hsm.trans htm.symm⟩
    exact ⟨g, (mem_omegaGroup_iff_even_finrank_inf hQ hn hta htm hgO).mpr he, rfl⟩

theorem omega_conj_two_classes {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hm : 1 ≤ m) (hn : finrank K V = 2 * m)
    {t : V ≃ₗ[K] V} (hta : suzukiLetter Q t = .a) (htm : finrank K (commSpace t) = m) :
    ∃ s₁ ∈ {x | ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * t * g⁻¹ = x},
      ∃ s₂ ∈ {x | ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * t * g⁻¹ = x},
        {x | ∃ g ∈ omegaGroup Q hQ, g * s₁ * g⁻¹ = x} ≠
            {x | ∃ g ∈ omegaGroup Q hQ, g * s₂ * g⁻¹ = x} ∧
          {x | ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g * t * g⁻¹ = x} =
            {x | ∃ g ∈ omegaGroup Q hQ, g * s₁ * g⁻¹ = x} ∪
              {x | ∃ g ∈ omegaGroup Q hQ, g * s₂ * g⁻¹ = x} := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (M := V) (by omega)
  obtain ⟨a, hQa⟩ := exists_map_ne_zero hQ
  let _ : Invertible (Q a) := invertibleOfNonzero hQa
  set r := TauCeti.QuadraticMap.reflection Q a with hr
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q a
  have hr1 : finrank K (commSpace r) = 1 := finrank_commSpace_reflection hQ a
  have hrΩ : r ∉ omegaGroup Q hQ := fun h => by
    have := h.2
    rw [hr1] at this
    exact Nat.not_even_one this
  refine ⟨t, ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one]⟩, r * t * r⁻¹, ⟨r, hrO, rfl⟩,
    fun heq => hrΩ ?_, ?_⟩
  ·
    have hmem : r * t * r⁻¹ ∈ {x | ∃ g ∈ omegaGroup Q hQ, g * (r * t * r⁻¹) * g⁻¹ = x} :=
      ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one]⟩
    rw [← heq] at hmem
    obtain ⟨h, hh, hht⟩ := hmem
    have h1 := (mem_omegaGroup_iff_even_finrank_inf hQ hn hta htm hh.1).mp hh
    rw [hht] at h1
    exact (mem_omegaGroup_iff_even_finrank_inf hQ hn hta htm hrO).mpr h1
  · ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨g, hgO, rfl⟩
      by_cases hge : Even (finrank K (commSpace g))
      · exact Or.inl ⟨g, ⟨hgO, hge⟩, rfl⟩
      · refine Or.inr ⟨g * r⁻¹, ⟨mul_mem hgO (inv_mem hrO), ?_⟩, by group⟩
        rw [← ZMod.natCast_eq_zero_iff_even,
          natCast_finrank_commSpace_mul hQ hgO (inv_mem hrO),
          natCast_finrank_commSpace_inv hQ hrO, hr1,
          (ZMod.natCast_eq_one_iff_odd).mpr (Nat.not_even_iff_odd.mp hge), Nat.cast_one]
        rfl
    · rintro (⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩)
      · exact ⟨g, hg.1, rfl⟩
      · exact ⟨g * r, mul_mem hg.1 hrO, by group⟩

omit [CharP K 2] in
theorem isGreatest_finrank_totallySingular {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hn : finrank K V = 2 * m) {t : V ≃ₗ[K] V}
    (hta : suzukiLetter Q t = .a) (htm : finrank K (commSpace t) = m) :
    IsGreatest {d | ∃ U : Submodule K V, (∀ x ∈ U, Q x = 0) ∧ finrank K U = d} m := by
  refine ⟨⟨commSpace t, (suzukiLetter_eq_a_iff.mp hta).2, htm⟩, ?_⟩
  rintro d ⟨U, hU, rfl⟩
  have := two_mul_finrank_le_of_forall_eq_zero hQ hU
  omega

end CharTwo

end CFSG.RankThree.OrthogonalInvolutions
