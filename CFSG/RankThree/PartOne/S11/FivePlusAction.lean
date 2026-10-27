module

public import CFSG.RankThree.GroupTheory.SteinbergBMRelativeMinimalFrattini

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.GroupTheory
open scoped commutatorElement

theorem mulAut_conj_apply_automorphism {J : Type*} [Group J] (σ : MulAut J) (x : J) :
    MulAut.conj (σ x) = σ * MulAut.conj x * σ⁻¹ := by
  ext y
  simp [MulAut.conj_apply]

theorem exists_invariant_two_commutator_of_inner_action {J B : Type*} [Group J] [Finite J]
    [Group B] [Finite B] [MulDistribMulAction B J] (h2B : ¬ 2 ∣ Nat.card B)
    {Q : Subgroup (MulAut J)} (hQ2 : IsPGroup 2 Q) (hQ1 : Q ≠ ⊥)
    (hinn : Q ≤ (MulAut.conj : J →* MulAut J).range)
    (hBQ : (MulDistribMulAction.toMulAut B J).range ≤ normalizer (Q : Set (MulAut J)))
    (hQB : ⁅Q, (MulDistribMulAction.toMulAut B J).range⁆ = Q) :
    ∃ E : Subgroup J, E ≠ ⊥ ∧ IsPGroup 2 E ∧ (∀ b : B, ∀ x ∈ E, b • x ∈ E) ∧
      actionCommutator B E = E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := MulDistribMulAction.toMulAut B J with hρ
  set c : J →* MulAut J := MulAut.conj with hc
  set QJ : Subgroup J := Q.comap c with hQJ
  have hρQ : ∀ (b : B) (σ : MulAut J), σ ∈ Q → ρ b * σ * (ρ b)⁻¹ ∈ Q := fun b σ hσ =>
    (Subgroup.mem_normalizer_iff.mp (hBQ ⟨b, rfl⟩) σ).mp hσ
  have hQJinv : ∀ b : B, ∀ x ∈ QJ, b • x ∈ QJ := by
    intro b x hx
    have hx' : c x ∈ Q := hx
    show c (b • x) ∈ Q
    have e : c (b • x) = ρ b * c x * (ρ b)⁻¹ := mulAut_conj_apply_automorphism (ρ b) x
    rw [e]
    exact hρQ b _ hx'
  set F := actionCommutator B QJ with hF
  have hFle : F ≤ QJ := SteinbergBM.actionCommutator_le_of_invariant hQJinv
  have hFinv : ∀ b : B, ∀ x ∈ F, b • x ∈ F := fun b x hx =>
    SteinbergBM.smul_mem_actionCommutator_of_invariant hQJinv b hx
  let f : F →* Q := (c.comp F.subtype).codRestrict Q (fun x => hFle x.2)
  have hfker : f.ker ≤ Subgroup.center F := by
    intro x hx
    have hx1 : c (x : J) = 1 := by
      have h1 : f x = 1 := hx
      exact congrArg Subtype.val h1
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have h2 := congrArg (fun σ : MulAut J => σ (y : J)) hx1
    simp only [hc, MulAut.conj_apply, MulAut.one_apply] at h2
    show (y : J) * (x : J) = (x : J) * (y : J)
    calc (y : J) * (x : J) = ((x : J) * (y : J) * (x : J)⁻¹) * (x : J) := by rw [h2]
      _ = (x : J) * (y : J) := by group
  have : Group.IsNilpotent Q := hQ2.isNilpotent
  have : Group.IsNilpotent F := Subgroup.isNilpotent_of_ker_le_center f hfker
  let P₂ : Sylow 2 F := default
  have hP₂n : (P₂ : Subgroup F).Normal := inferInstance
  have : Unique (Sylow 2 F) := Sylow.unique_of_normal P₂ hP₂n
  set Pj : Subgroup J := (P₂ : Subgroup F).map F.subtype with hPj
  have hPjinv : ∀ b : B, ∀ x ∈ Pj, b • x ∈ Pj := by
    rintro b _ ⟨y, hy, rfl⟩
    have hyF : b • (y : J) ∈ F := hFinv b y y.2
    set y' : F := ⟨b • (y : J), hyF⟩ with hy'
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P₂.isPGroup' ⟨y, hy⟩
    have hyk : y ^ (2 ^ k) = 1 := by
      have h1 : (⟨y, hy⟩ : (P₂ : Subgroup F)) ^ (2 ^ k) = 1 := by
        rw [← hk]; exact pow_orderOf_eq_one _
      exact congrArg Subtype.val h1
    have hy'k : y' ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      have h2 : ((y ^ (2 ^ k) : F) : J) = 1 := by rw [hyk]; rfl
      show (b • (y : J)) ^ (2 ^ k) = 1
      rw [← smul_pow']
      have h3 : (y : J) ^ (2 ^ k) = 1 := by simpa using h2
      rw [h3, smul_one]
    have hord : orderOf y' ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hy'k
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    have hz2 : IsPGroup 2 (Subgroup.zpowers y') :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
    obtain ⟨S, hS⟩ := hz2.exists_le_sylow
    have hSP : S = P₂ := Subsingleton.elim S P₂
    have hy'mem : y' ∈ (P₂ : Subgroup F) := by
      have := hS (Subgroup.mem_zpowers y')
      rwa [hSP] at this
    exact ⟨y', hy'mem, rfl⟩
  have hPj2 : IsPGroup 2 Pj := P₂.isPGroup'.map F.subtype
  set E := actionCommutator B Pj with hE
  have hEle : E ≤ Pj := SteinbergBM.actionCommutator_le_of_invariant hPjinv
  refine ⟨E, ?_, hPj2.to_le hEle,
    fun b x hx => SteinbergBM.smul_mem_actionCommutator_of_invariant hPjinv b hx,
    SteinbergBM.actionCommutator_actionCommutator_of_isPGroup Nat.prime_two hPj2 h2B hPjinv⟩
  intro hE0
  have hfix : ∀ b : B, ∀ x ∈ Pj, b • x = x := by
    intro b x hx
    have h1 : x⁻¹ * (b • x) ∈ E := gen_mem_actionCommutator hx b
    rw [hE0, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1.symm
  have hQF : Q ≤ F.map c := by
    refine hQB.symm.le.trans ?_
    rw [Subgroup.commutator_le]
    rintro σ hσ _ ⟨b, rfl⟩
    obtain ⟨x, rfl⟩ := hinn hσ
    have hx : x ∈ QJ := hσ
    refine ⟨x * (b • x⁻¹), ?_, ?_⟩
    · have h1 := gen_mem_actionCommutator (A := B) (QJ.inv_mem hx) b
      simpa using h1
    · have e : c (b • x⁻¹) = ρ b * c x⁻¹ * (ρ b)⁻¹ := mulAut_conj_apply_automorphism (ρ b) x⁻¹
      rw [map_mul, e, map_inv, commutatorElement_def]
      group
  have hfs : Function.Surjective f := by
    rintro ⟨σ, hσ⟩
    obtain ⟨x, hx, hxσ⟩ := hQF hσ
    exact ⟨⟨x, hx⟩, Subtype.ext hxσ⟩
  have hmax := (P₂.mapSurjective hfs).is_maximal' (hQ2.to_subgroup ⊤) le_top
  rw [Sylow.coe_mapSurjective] at hmax
  have hQPj : ∀ σ ∈ Q, ∃ x ∈ Pj, c x = σ := by
    intro σ hσ
    have h1 : (⟨σ, hσ⟩ : Q) ∈ (P₂ : Subgroup F).map f := hmax ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hyσ⟩ := h1
    exact ⟨y, ⟨y, hy, rfl⟩, congrArg Subtype.val hyσ⟩
  apply hQ1
  rw [← hQB, eq_bot_iff, Subgroup.commutator_le]
  rintro σ hσ _ ⟨b, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hQPj σ hσ
  have h1 : ρ b * c x * (ρ b)⁻¹ = c x := by
    have e : c (b • x) = ρ b * c x * (ρ b)⁻¹ := mulAut_conj_apply_automorphism (ρ b) x
    rw [← e, hfix b x hx]
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (mul_inv_eq_iff_eq_mul.mp h1).symm

end CFSG.RankThree.PartOne
