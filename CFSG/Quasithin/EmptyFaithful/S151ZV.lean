module

public import CFSG.Quasithin.EmptyFaithful.S151ZR

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {A : Type} [Group A]

@[expose] def borelIso_toSurjBorel {n : ℕ} {L B : Subgroup A} (D : BorelIso n L B) (hBL : B ≤ L) :
    SurjBorel n L B where
  e := D.e.toMonoidHom
  surj := D.e.surjective
  le_L := hBL
  ker_le := by
    have : D.e.toMonoidHom.ker = ⊥ := MonoidHom.ker_eq_bot_iff _ |>.mpr D.e.injective
    rw [this]
    exact bot_le
  hB := D.hB

theorem exists_That [Finite A] {L B P : Subgroup A} {n : ℕ} (D : SurjBorel n L B)
    (hker : D.e.ker ≤ CFSG.pCore 2 ↥L) (hBP : B ≤ P) (hPL : P ≤ L) {a : ℕ}
    (ha : a ∈ D.cutsOf P) :
    ∃ T : Subgroup A, T ≤ pCoreOf 2 P ∧ ∀ y : ↥L, (y : A) ∈ T ↔ D.e y ∈ Tgrp n a := by
  classical
  have hmodP : D.model P = QI n (cuts (D.model P)) := eq_QI_cuts (D.Ut_le_model hBP)
  have hstab : ∀ g ∈ D.model P, g ∈ stabilizer (flagSpace n (ZMod 2) a) := by
    intro g hg
    rw [hmodP] at hg
    exact (mem_flagStabilizer.mp hg) a ha
  have hTmodel : Tgrp n a ≤ D.model P := (Tgrp_le_Ut a).trans (D.Ut_le_model hBP)
  let That : Subgroup A := ((Tgrp n a).comap D.e).map L.subtype
  have hThat_mem : ∀ y : ↥L, (y : A) ∈ That ↔ D.e y ∈ Tgrp n a := by
    intro y
    constructor
    · rintro ⟨y', hy', hyy⟩
      have : y' = y := Subtype.ext hyy
      subst this
      exact hy'
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hThatP : That ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact (D.mem_model hBP y).1 (hTmodel hy)
  have hThat_conj : ∀ p ∈ P, ∀ y ∈ That, p * y * p⁻¹ ∈ That := by
    intro p hp y hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have hy₀' : D.e y₀ ∈ Tgrp n a := hy₀
    have hpL : p ∈ L := hPL hp
    have hp₁ : D.e ⟨p, hpL⟩ ∈ D.model P := (D.mem_model hBP _).2 hp
    have hbp := bcond_of_mem_stabilizer (hstab _ hp₁)
    have hbp' := bcond_of_mem_stabilizer (hstab _ (Subgroup.inv_mem _ hp₁))
    have hconj := Tgrp_conj hbp (by simpa using hbp') hy₀'
    show p * (y₀ : A) * p⁻¹ ∈ That
    have : p * (y₀ : A) * p⁻¹ = ((⟨p, hpL⟩ * y₀ * ⟨p, hpL⟩⁻¹ : ↥L) : A) := by simp
    rw [this, hThat_mem]
    simpa using hconj
  have hThat_p : IsPGroup 2 ↥That := by
    rintro ⟨y, hy⟩
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have hsq : D.e (y₀ * y₀) = 1 := by
      rw [map_mul]
      exact Tgrp_sq hy₀
    have hmem : y₀ * y₀ ∈ CFSG.pCore 2 ↥L := hker (MonoidHom.mem_ker.mpr hsq)
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨y₀ * y₀, hmem⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h1 : (y₀ * y₀) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    show ((y₀ : A)) ^ 2 ^ (k + 1) = 1
    have h2 : (y₀ : A) ^ 2 ^ (k + 1) = (((y₀ * y₀) ^ 2 ^ k : ↥L) : A) := by
      push_cast
      rw [← pow_two, ← pow_mul, pow_succ, mul_comm]
    rw [h2, h1]
    rfl
  exact ⟨That, CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hThatP (zn_le_normalizer hThat_conj)
      hThat_p, hThat_mem⟩

theorem charTwo_of_cut [Finite A] {L B P : Subgroup A} {n : ℕ} (D : SurjBorel n L B)
    (hker : D.e.ker ≤ CFSG.pCore 2 ↥L) (hBP : B ≤ P) (hPL : P ≤ L) {a : ℕ}
    (ha : a ∈ D.cutsOf P) : CharTwo P := by
  obtain ⟨ha1, ha2⟩ := D.isNode_of_mem_cutsOf ha
  obtain ⟨T, hTO, hTmem⟩ := exists_That D hker hBP hPL ha
  rintro x ⟨hxP, hxC⟩
  have hxL : x ∈ L := hPL hxP
  set x₀ : ↥L := ⟨x, hxL⟩ with hx₀
  have hcomm : ∀ t ∈ Tgrp n a, D.e x₀ * t = t * D.e x₀ := by
    intro t ht
    obtain ⟨y₀, rfl⟩ := D.surj t
    have hyT : (y₀ : A) ∈ T := (hTmem y₀).2 ht
    have hyO : (y₀ : A) ∈ pCoreOf 2 P := hTO hyT
    have h1 : (y₀ : A) * x = x * (y₀ : A) := Subgroup.mem_centralizer_iff.mp hxC (y₀ : A) hyO
    have h2 : y₀ * x₀ = x₀ * y₀ := Subtype.ext h1
    rw [← map_mul, ← map_mul, h2]
  have hT := mem_Tgrp_of_commute ha1 ha2 hcomm
  exact hTO ((hTmem x₀).2 hT)

theorem exists_minimal_parabolic [Finite A] {L B : Subgroup A} {n : ℕ} (D : SurjBorel n L B) {o : ℕ}
    (ho : IsNode n o) :
    ∃ Po : Subgroup A, B ≤ Po ∧ Po ≤ L ∧ D.cutsOf Po = nodeSet n \ {o} ∧
      Nat.card ↥Po = 3 * Nat.card ↥B := by
  obtain ⟨Po, hBP, hPL, hc⟩ := D.exists_cutsOf_eq (I := nodeSet n \ {o}) (fun x hx => hx.1)
  refine ⟨Po, hBP, hPL, hc, ?_⟩
  have hrel : B.relIndex Po = 3 := by
    have h1 := zr_relIndex_eq D hBP hPL
    have hmodel : D.model Po = QI n (D.cutsOf Po) := eq_QI_cuts (D.Ut_le_model hBP)
    rw [h1, hmodel, hc]
    exact index_single ho
  have h2 := Subgroup.relIndex_mul_card B Po
  rw [inf_of_le_left hBP, hrel] at h2
  exact h2.symm

theorem oPrimeResidualOf_mono {p : ℕ} {X Y : Subgroup A} (h : X ≤ Y) :
    oPrimeResidualOf p X ≤ oPrimeResidualOf p Y :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem oPrime_of_shape [Finite A] {L B P : Subgroup A} {n : ℕ} (D : SurjBorel n L B)
    (hB2 : IsPGroup 2 ↥B) (hBP : B ≤ P) (hPL : P ≤ L) {i : ℕ} (hi : IsNode n i)
    (hshape : D.cutsOf P = nodeSet n \ {i} ∨
      ∃ j, IsNode n j ∧ i < j ∧ D.cutsOf P = nodeSet n \ {i, j}) :
    oPrimeResidualOf 3 P ⊔ B = P := by
  rcases hshape with hc | ⟨j, hj, hij, hc⟩
  · obtain ⟨Po, hBPo, hPoL, hPoc, hPocard⟩ := exists_minimal_parabolic D hi
    have hPeq : P = Po := D.eq_of_cutsOf_eq hBP hPL hBPo hPoL (by rw [hc, hPoc])
    subst hPeq
    exact zb_oPrime_sup_eq hBP hPocard hB2
  · obtain ⟨Pi, hBPi, hPiL, hPic, hPicard⟩ := exists_minimal_parabolic D hi
    obtain ⟨Pj, hBPj, hPjL, hPjc, hPjcard⟩ := exists_minimal_parabolic D hj
    have hPij : P = Pi ⊔ Pj := by
      apply D.eq_of_cutsOf_eq hBP hPL (hBPi.trans le_sup_left) (sup_le hPiL hPjL)
      rw [D.cutsOf_sup hBPi hPiL hBPj hPjL, hc, hPic, hPjc]
      ext x
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        not_or]
      tauto
    have hPiP : Pi ≤ P := by rw [hPij]; exact le_sup_left
    have hPjP : Pj ≤ P := by rw [hPij]; exact le_sup_right
    have hXi : Pi ≤ oPrimeResidualOf 3 P ⊔ B := by
      rw [← zb_oPrime_sup_eq hBPi hPicard hB2]
      exact sup_le_sup_right (oPrimeResidualOf_mono hPiP) B
    have hXj : Pj ≤ oPrimeResidualOf 3 P ⊔ B := by
      rw [← zb_oPrime_sup_eq hBPj hPjcard hB2]
      exact sup_le_sup_right (oPrimeResidualOf_mono hPjP) B
    exact le_antisymm (sup_le zb_oPrime_le hBP) (hPij.le.trans (sup_le hXi hXj))

end CFSG.Quasithin
