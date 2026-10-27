module

public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.Quasithin.Vol2.KGNatSL3PointFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace C11P9B

theorem exists_psl2_equiv {X : Type} [Group X] {p : ℕ} (h : IsPSL 2 p 1 X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ∧
      Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := by
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, by rw [hK, pow_one],
    ⟨φ.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm⟩⟩

theorem card_eq_sixty_of_le {Q : Type} [Group Q] {S : Subgroup Q} {K : Type} [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (hK : Nat.card K = p)
    (e : ↥S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) {J : Subgroup Q} (hJS : J ≤ S)
    (hJp : ¬ p ∣ Nat.card J) (hns : ¬ Group.IsSolvable J) : Nat.card J = 60 := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK])
  set ι : ↥S →* Matrix.ProjGenLinGroup (Fin 2) K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL.comp e.toMonoidHom with hιdef
  have hι : Function.Injective ι :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp e.injective
  let eJ : ↥((J.subgroupOf S).map ι) ≃* ↥J :=
    ((J.subgroupOf S).equivMapOfInjective ι hι).symm.trans (Subgroup.subgroupOfEquivOfLe hJS)
  have hcard : Nat.card ↥((J.subgroupOf S).map ι) = Nat.card J := Nat.card_congr eJ.toEquiv
  have h := CFSG.LinearGroups.tame_projective_linear_two_nonsolvable_order_sixty hp
    ((J.subgroupOf S).map ι) (by rw [hcard]; exact hJp)
    (fun hs => hns (Group.isSolvable_of_surjective (f := eJ.toMonoidHom) eJ.surjective))
  rw [← hcard]
  exact h.1

theorem not_isSolvable_of_commutator_eq_top {G : Type*} [Group G] [Nontrivial G]
    (h : commutator G = ⊤) : ¬ Group.IsSolvable G := by
  intro hs
  obtain ⟨n, hn⟩ := (Group.isSolvable_def G).mp hs
  have htop : ∀ m, derivedSeries G m = ⊤ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [derivedSeries_succ, ih, ← commutator_def, h]
  rw [htop n] at hn
  exact top_ne_bot hn

theorem facts_of_SL2_four {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (eB : X ⧸ CFSG.pCore 2 X ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ¬ Group.IsSolvable X ∧ ∃ k : ℕ, Nat.card X = 60 * 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h60 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 60 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num), hF]
    decide
  have hSL := CFSG.Quasithin.Vol2.KGNat.commutator_SL2_eq_top (K := F) (by rw [hF])
  have : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [h60]; norm_num)
  refine ⟨fun hs => not_isSolvable_of_commutator_eq_top hSL ?_, ?_⟩
  · have : Group.IsSolvable (X ⧸ CFSG.pCore 2 X) :=
      Group.isSolvable_of_surjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    exact Group.isSolvable_of_surjective (f := eB.toMonoidHom) eB.surjective
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := X))
    refine ⟨k, ?_⟩
    rw [(CFSG.pCore 2 X).card_eq_card_quotient_mul_card_subgroup, Nat.card_congr eB.toEquiv, h60,
      hk]

theorem pCore_eq_bot_of_card {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 4) (eB : X ⧸ CFSG.pCore 2 X ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hX : Nat.card X = 60) :
    CFSG.pCore 2 X = ⊥ ∧ ∀ b : X, (∀ c : X, b * c = c * b) → b = 1 := by
  have h60 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 60 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num), hF]
    decide
  have hP : CFSG.pCore 2 X = ⊥ := by
    have h := (CFSG.pCore 2 X).card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr eB.toEquiv, h60, hX] at h
    exact Subgroup.eq_bot_of_card_eq _ (by omega)
  refine ⟨hP, fun b hb => ?_⟩
  have : CharP F 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (n := 2) (by norm_num)
    (by rw [hF]; norm_num)
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (K := F)
    (by rw [hF])
  have := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple hK4
  obtain ⟨a₁, a₂, ha⟩ := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_nonabelian hK4
  let eX : X ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hP).symm).trans eB
  have hc : eX b ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨c, rfl⟩ := eX.surjective y
    rw [← map_mul, ← map_mul, hb c]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) with h | h
  · rw [h, Subgroup.mem_bot] at hc
    exact eX.injective (by rw [hc, map_one])
  · exfalso
    apply ha
    have h1 : a₁ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [h]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_center_iff.mp h1 a₂).symm

theorem ringEquiv_eq_one_of_card_prime {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p) (σ : K ≃+* K) : σ = 1 := by
  have := Fintype.ofFinite K
  let e₀ : ZMod p ≃+* K := ZMod.ringEquivOfPrime K hp (by rw [← Nat.card_eq_fintype_card, hK])
  have h := RingHom.ext_zmod (σ.toRingHom.comp e₀.toRingHom) e₀.toRingHom
  refine RingEquiv.ext fun c => ?_
  obtain ⟨z, rfl⟩ := e₀.surjective c
  exact congrArg (fun φ : ZMod p →+* K => φ z) h

theorem exists_inner_of_order_three {Q : Type} [Group Q] {S : Subgroup Q} [S.Normal]
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hK : Nat.card K = p)
    (e : ↥S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) {x : Q} (hx : x ^ 3 = 1) :
    ∃ s₀ ∈ S, s₀ ^ 3 = 1 ∧ ∀ s ∈ S, x * s * x⁻¹ = s₀ * s * s₀⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  have hKodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by rw [hK, pow_one]⟩
  have hcard : 3 < Nat.card K := by rw [hK]; exact hp3
  let α : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    MulAut.congr e (MulAut.conjNormal x)
  obtain ⟨y, hy⟩ := CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_surjective K (p := p) (f := 1)
    (by rw [hK, pow_one]) hKodd hcard α
  have hyl : CFSG.GorensteinWalter.pgl2InnerAutPSL2 K hKodd hcard y.left = α := by
    rw [← hy]
    conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right y]
    rw [map_mul, CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_inl,
      CFSG.GorensteinWalter.pGammaL2ToMulAutPSL2_inr, ringEquiv_eq_one_of_card_prime hp hK y.right,
      map_one, mul_one]
  have hα3 : α ^ 3 = 1 := by
    show (MulAut.congr e (MulAut.conjNormal x)) ^ 3 = 1
    rw [← map_pow, ← map_pow, hx, map_one, map_one]
  have hg3 : y.left ^ 3 = 1 := CFSG.GorensteinWalter.pgl2InnerAutPSL2_injective K hKodd hcard
    (by rw [map_pow, hyl, hα3, map_one])
  have hidx := CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two K hKodd
  have hgH : y.left ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
    have h2 := Subgroup.mul_self_mem_of_index_two hidx y.left
    have h3 : y.left = (y.left * y.left)⁻¹ * y.left ^ 3 := by group
    rw [h3, hg3, mul_one]
    exact Subgroup.inv_mem _ h2
  obtain ⟨s₀', hs₀'⟩ := hgH
  have hconj : α = MulAut.conj s₀' := by
    rw [← hyl, ← hs₀', CFSG.GorensteinWalter.pgl2InnerAutPSL2_toPGL]
  have hs₀'3 : s₀' ^ 3 = 1 := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    (by rw [map_pow, hs₀', hg3, map_one])
  refine ⟨(e.symm s₀' : Q), (e.symm s₀').2, ?_, fun s hs => ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, hs₀'3, map_one, Subgroup.coe_one]
  · have h1 : α (e ⟨s, hs⟩) = MulAut.conj s₀' (e ⟨s, hs⟩) := by rw [hconj]
    have h0 : α (e ⟨s, hs⟩) = e (MulAut.conjNormal x ⟨s, hs⟩) := by
      simp [α, MulAut.congr_apply]
    rw [h0, MulAut.conj_apply] at h1
    have h2 : MulAut.conjNormal x ⟨s, hs⟩ = e.symm s₀' * ⟨s, hs⟩ * (e.symm s₀')⁻¹ := by
      apply e.injective
      rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    have h3 := congrArg Subtype.val h2
    rw [MulAut.conjNormal_apply] at h3
    simpa using h3

end C11P9B

end CFSG.Quasithin.Vol2.Ch11.SecA
