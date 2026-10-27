module

public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProofHeis
import CFSG.CharacterTheory.Semidihedral.OddProjectiveCoverKernel
import CFSG.Models.PGLSimple
public import CFSG.RankThree.PartTwo.Sec11.LSSolvableProofKlein

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.L2CubeSolvable

open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.BenderSuzuki.PFchapter1section1 (TwoRankAtLeastTwo)
open CFSG.Semidihedral
open CFSG.Semidihedral.ProjectiveSL2Cover (NativeScalarProjective scalarQuotient
  nativeScalarKernel_eq_center)
open scoped MatrixGroups

section Field

variable {p : ℕ} {F : Type} [Field F]

theorem finite_of_card (hp : p.Prime) (hF : Nat.card F = p ^ 3) : Finite F :=
  Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero 3 hp.ne_zero)

theorem ringChar_ne_two (hp : p.Prime) (hp5 : 5 ≤ p) (hF : Nat.card F = p ^ 3) :
    ringChar F ≠ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := finite_of_card hp hF
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F p :=
    charP_of_card_eq_prime_pow (f := 3) (by rwa [← Nat.card_eq_fintype_card])
  rw [ringChar.eq F p]
  omega

theorem odd_card (hp : p.Prime) (hp5 : 5 ≤ p) (hF : Nat.card F = p ^ 3) :
    Odd (Nat.card F) := by
  rw [hF]
  exact (hp.odd_of_ne_two (by omega)).pow

theorem le_card_field (hp5 : 5 ≤ p) (hF : Nat.card F = p ^ 3) : 125 ≤ Nat.card F := by
  rw [hF]
  calc 125 = 5 ^ 3 := by norm_num
    _ ≤ p ^ 3 := Nat.pow_le_pow_left hp5 3

end Field

section Group

variable {p : ℕ} {F : Type} [Field F]

private noncomputable def eIso (F : Type) [Field F] : projSL 2 F ≃* NativeScalarProjective F 2 :=
  (CFSG.PGLModel.projSLEquivStatedProj 2 F).trans
    (CFSG.Semidihedral.ProjectiveSL2Cover.scalarProjectiveEquivStated F 2).symm

theorem isSimpleGroup_projSL_two (hp5 : 5 ≤ p) (hF : Nat.card F = p ^ 3) :
    IsSimpleGroup (projSL 2 F) := by
  have h125 := le_card_field hp5 hF
  exact CFSG.PGLModel.isSimpleGroup_projSL_of_two_le F le_rfl (Or.inr (by omega))
    (Or.inr (by omega))

theorem le_card_projSL_two (hp : p.Prime) (hp5 : 5 ≤ p) (hF : Nat.card F = p ^ 3) :
    262080 ≤ Nat.card (projSL 2 F) := by
  haveI := finite_of_card hp hF
  have h125 := le_card_field hp5 hF
  rw [Nat.card_congr (eIso F).toEquiv,
    OddProjectiveCoverKernel.S_card F (ringChar_ne_two hp hp5 hF)]
  generalize Nat.card F = q at h125 ⊢
  have h1 : 15624 ≤ q ^ 2 - 1 := by
    have : 125 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h125 2
    norm_num at this
    omega
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  calc 262080 * 2 ≤ 125 * 15624 := by norm_num
    _ ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul h125 h1

theorem kernel_eq_bot_of_central_odd (hp : p.Prime) (hp5 : 5 ≤ p) (hF : Nat.card F = p ^ 3)
    {E : Type} [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* projSL 2 F) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  set π' : E →* NativeScalarProjective F 2 := (eIso F).toMonoidHom.comp π with hπ'
  have hker : π'.ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hπ', MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  have hp9 : p ^ 3 ≠ 9 := by
    have : 5 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp5 3
    omega
  have h := (OddProjectiveCoverKernel.odd_projective_linear_two_perfect_odd_cover_kernel F hp
    hpodd (by norm_num : 1 ≤ 3) hF π' ((eIso F).surjective.comp hπ)
    (by rw [hker]; exact hC) (by rw [hker]; exact hodd)).1 hp9
  rwa [hker] at h

end Group

section Klein

variable {F : Type} [Field F]

theorem exists_klein_pair [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ a b : NativeScalarProjective F 2, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧
      a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have h2 : (2 : F) ≠ 0 := OddFieldSL2.two_ne_zero_of_odd_card F hodd
  obtain ⟨x, y, hxy⟩ := OddFieldSL2.sum_two_squares F hodd (-1)
  set i : SL(2, F) := OddLinearNormals.quarterTurn F with hi
  set j : SL(2, F) := OddFieldSL2.secondGenerator F x y hxy with hj
  have hinv : i * j = j * i⁻¹ := OddFieldSL2.generators_inversion F x y hxy
  have hker : ∀ g : SL(2, F), scalarQuotient F 2 g = 1 ↔ g ∈ Subgroup.center SL(2, F) :=
    fun g => by
      rw [← nativeScalarKernel_eq_center]
      exact QuotientGroup.eq_one_iff g
  have hi_sq : scalarQuotient F 2 i * scalarQuotient F 2 i = 1 := by
    rw [← map_mul, ← sq]
    exact (hker _).mpr (OddLinearNormals.quarterTurn_square_mem_center F)
  have hj2 : j ^ 2 = OddFieldSL2.minusIdentity F := OddFieldSL2.secondGenerator_square F x y hxy
  have hj_sq : scalarQuotient F 2 j * scalarQuotient F 2 j = 1 := by
    rw [← map_mul, ← sq, hj2]
    exact (hker _).mpr (OddFieldSL2.minusIdentity_mem_center F)
  have hjne : j ^ 2 ≠ 1 := by
    rw [hj2]
    exact OddFieldSL2.minusIdentity_ne_one F h2
  refine ⟨scalarQuotient F 2 i, scalarQuotient F 2 j, hi_sq, hj_sq, ?_, ?_, ?_, ?_⟩
  · have hq : (scalarQuotient F 2 i)⁻¹ = scalarQuotient F 2 i := inv_eq_of_mul_eq_one_right hi_sq
    rw [← map_mul, hinv, map_mul, map_inv, hq]
  · exact fun h => OddLinearNormals.quarterTurn_not_mem_center F ((hker i).mp h)
  · exact fun h => hjne (OddLinearNormals.center_square_eq_one F j ((hker j).mp h))
  · intro h
    have h1 : scalarQuotient F 2 (i⁻¹ * j) = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2' := OddLinearNormals.center_square_eq_one F _ ((hker _).mp h1)
    have hsq : (i⁻¹ * j) ^ 2 = j ^ 2 := by
      rw [sq, sq, mul_assoc, ← mul_assoc j, ← hinv, ← mul_assoc, inv_mul_cancel_left]
    exact hjne (hsq ▸ h2')

variable {p : ℕ}

private theorem twoRankAtLeastTwo_of_commuting {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    TwoRankAtLeastTwo G := by
  classical
  have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have h2 : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
  have h3 : a * b * a = b := by rw [hab, mul_assoc, ha, mul_one]
  have h4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have h5 : a * b * (a * b) = 1 := by rw [← mul_assoc, h3, hb]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hab1 : a * b ≠ 1 := fun h => hne ((mul_eq_one_iff_eq_inv.1 h).trans hbi)
  have haab : a ≠ a * b := fun h => hb1 (left_eq_mul.1 h)
  have hbab : b ≠ a * b := fun h => ha1 (right_eq_mul.1 h)
  let E : Subgroup G :=
    { carrier := {1, a, b, a * b}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
        rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;>
          simp [hx, hy, ha, hb, h1, h2, h3, h4, h5, hab.symm]
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        rcases hx with hx | hx | hx | hx <;> simp [hx, hai, hbi, hab.symm] }
  refine ⟨E, ?_, fun g => ?_⟩
  · have hcard : Nat.card E = Nat.card ((E : Set G)) := rfl
    have hset : (E : Set G) = {1, a, b, a * b} := rfl
    rw [hcard, hset, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_pair hbab]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, haab⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => ha1 h.symm, fun h => hb1 h.symm, fun h => hab1 h.symm⟩
  · apply Subtype.ext
    have hg : (g : G) ∈ ({1, a, b, a * b} : Set G) := g.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_two]
    rcases hg with hg | hg | hg | hg <;> simp [hg, ha, hb, h5]

theorem exists_klein_four_L2 (hp : p.Prime) (hp5 : 5 ≤ p) (hF : Nat.card F = p ^ 3)
    {Y : Type*} [Group Y] [Finite Y] (M : Subgroup Y) [M.Normal] (hM : Odd (Nat.card M))
    (e : Y ⧸ M ≃* projSL 2 F) :
    ∃ a b : Y, a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  haveI := finite_of_card hp hF
  obtain ⟨a, b, ha, hb, hab, ha1, hb1, hne⟩ := exists_klein_pair (F := F) (odd_card hp hp5 hF)
  let φ : NativeScalarProjective F 2 ≃* Y ⧸ M := (e.trans (eIso F)).symm
  have hrank : TwoRankAtLeastTwo (Y ⧸ M) :=
    twoRankAtLeastTwo_of_commuting (a := φ a) (b := φ b)
      (by rw [← map_mul, ha, map_one]) (by rw [← map_mul, hb, map_one])
      (by rw [← map_mul, ← map_mul, hab])
      (fun h => ha1 (φ.injective (h.trans (map_one φ).symm)))
      (fun h => hb1 (φ.injective (h.trans (map_one φ).symm)))
      (fun h => hne (φ.injective h))
  have hY : TwoRankAtLeastTwo Y := by
    by_contra h
    exact CFSG.BenderSuzuki.not_twoRankAtLeastTwo_quotient_of_odd M hM h hrank
  exact LSSolvableProof.exists_klein_of_twoRank hY

end Klein

section Irreducible

variable {p : ℕ} {F : Type} [Field F]

theorem index_lt_eq_top_L2 (hp : p.Prime) (hp5 : 5 ≤ p) (hF : Nat.card F = p ^ 3)
    {X : Type*} [Group X] [Finite X] [Group.IsPerfect X] {N : Subgroup X}
    [N.Normal] (hN : Group.IsSolvable N) (e : X ⧸ N ≃* projSL 2 F) :
    ∀ J : Subgroup X, J.Normal → J.index < 262080 → J = ⊤ := by
  intro J _ hidx
  by_contra hJ
  have : IsSimpleGroup (projSL 2 F) := isSimpleGroup_projSL_two hp5 hF
  have hsimple : IsSimpleGroup (X ⧸ N) := MulEquiv.isSimpleGroup e
  obtain ⟨x, hx⟩ : ∃ x, x ∉ J := by
    by_contra hall
    push Not at hall
    exact hJ (eq_top_iff.mpr fun x _ => hall x)
  have hρ : ∃ x, QuotientGroup.mk' J x ≠ 1 := ⟨x, by
    rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]; exact hx⟩
  have hJN : (QuotientGroup.mk' J).ker ≤ N :=
    LSSolvableProof.ker_le_of_perfect hN hsimple _ hρ
  rw [QuotientGroup.ker_mk'] at hJN
  have hdvd := Subgroup.index_dvd_of_le hJN
  have hpos : 0 < J.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hle := Nat.le_of_dvd hpos hdvd
  have hN' : N.index = Nat.card (projSL 2 F) := by
    rw [Subgroup.index_eq_card, Nat.card_congr e.toEquiv]
  have := le_card_projSL_two hp hp5 hF
  omega

theorem seven_le_finrank_of_irreducible_L2 (hp : p.Prime) (hp5 : 5 ≤ p)
    (hF : Nat.card F = p ^ 3) {r : ℕ} [Fact r.Prime]
    {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y] (M : Subgroup Y) [M.Normal]
    (hM : Group.IsSolvable M) (hModd : Odd (Nat.card M)) (hMne : M ≠ ⊥)
    (e : Y ⧸ M ≃* projSL 2 F)
    (hsmall : ∀ J : Subgroup Y, J.Normal → J.index < 262080 → J = ⊤)
    {V : Type} [AddCommGroup V] [Module (ZMod r) V] [Module.Finite (ZMod r) V] [Nontrivial V]
    (ρ : Y →* (V →ₗ[ZMod r] V)) (hρ : Function.Injective ρ)
    (hirr : LSSolvableProof.IsIrreducibleRep ρ) :
    7 ≤ Module.finrank (ZMod r) V := by
  by_contra hlt
  push Not at hlt
  have hdim : Module.finrank (ZMod r) V ≤ 6 := by omega
  by_cases hMZ : M ≤ Subgroup.center Y
  ·
    set π : Y →* projSL 2 F := e.toMonoidHom.comp (QuotientGroup.mk' M) with hπ
    have hπs : Function.Surjective π :=
      e.surjective.comp (QuotientGroup.mk'_surjective M)
    have hker : π.ker = M := by
      ext x
      rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine hMne ?_
    have h := kernel_eq_bot_of_central_odd hp hp5 hF π hπs (hker ▸ hMZ) (by rw [hker]; exact hModd)
    rwa [hker] at h
  · obtain ⟨R, hRn, hZR, hRZ, hRR, s, hs, hpow, hact⟩ :=
      LSSolvableProof.exists_noncentral_normal M hM hMZ
    have : R.Normal := hRn
    exact LSSolvableProof.false_of_noncentral_normal hρ hirr hdim hsmall R hZR hRZ hRR hs hpow
      hact

end Irreducible

end CFSG.RankThree.PartTwo.Sec11.SimsR1.L2CubeSolvable
