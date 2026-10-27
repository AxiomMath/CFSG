module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoPSLCent
public import CFSG.CGT.T75P.Mat3
public import CFSG.HardMathSupport.Cooperstein.Transport

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp.KFact

open CFSG.SeitzReduction.LinearPilot CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Open
  CFSG.CGT.Timmesfeld75 Matrix

theorem card_pCoreOf_centralizer_mulEquiv {P Y : Type*} [Group P] [Group Y] (e : P ≃* Y) (x : P) :
    Nat.card (pCoreOf 2 (Subgroup.centralizer ({e x} : Set Y))) =
      Nat.card (pCoreOf 2 (Subgroup.centralizer ({x} : Set P))) := by
  have h1 : Subgroup.centralizer ({e x} : Set Y) =
      (Subgroup.centralizer ({x} : Set P)).map e.toMonoidHom := by
    ext g
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, Subgroup.mem_map,
      MulEquiv.coe_toMonoidHom]
    constructor
    · intro hg
      refine ⟨e.symm g, ?_, by simp⟩
      apply e.injective
      simpa using hg
    · rintro ⟨h, hh, rfl⟩
      simpa using congrArg e hh
  rw [h1, CFSG.HardMathSupport.Cooperstein.Transport.pCoreOf_map_mulEquiv]
  exact (Nat.card_congr ((pCoreOf 2 (Subgroup.centralizer ({x} : Set P))).equivMapOfInjective
    e.toMonoidHom e.injective).toEquiv).symm

theorem isTransvection_transvection {n : ℕ} {F : Type} [Field F] {i j : Fin n} (hij : i ≠ j)
    {c : F} (hc : c ≠ 0) : IsTransvection (SpecialLinearGroup.transvection hij c) := by
  refine CFSG.CGT.T75P.isTransvection_of_apply _ (c • LinearMap.proj j) (Pi.single i 1) ?_ ?_ ?_
  · simp [Pi.single_apply, hij.symm]
  · intro x
    ext l
    simp [SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.mulVec_single,
      Pi.single_apply]
    by_cases hl : l = i
    · subst hl
      simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
    · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, hl, Ne.symm hl]
  · intro h
    have := congrArg (fun g : SpecialLinearGroup (Fin n) F => (g : Matrix (Fin n) (Fin n) F) i j) h
    simp [SpecialLinearGroup.transvection_coe, Matrix.one_apply, hij] at this
    exact hc this


theorem card_radical_le {n : ℕ} {K : Type} [Field K] [Finite K] (P : InvPlacement n 1) :
    Nat.card (P.radical K) ≤ Nat.card K ^ (2 * n - 3) := by
  have hn : 2 ≤ n := by
    have h1 := (P.u 0).isLt
    have h2 := (P.w 0).isLt
    have h3 : (P.u 0).val ≠ (P.w 0).val := fun h => P.u_ne_w 0 0 (Fin.ext h)
    omega
  let F : P.radical K → (P.free → K) × (P.free → K) × K := fun B =>
    (fun j => (B.1 : Matrix (Fin n) (Fin n) K) (P.u 0) j.1,
      fun i => (B.1 : Matrix (Fin n) (Fin n) K) i.1 (P.w 0),
      (B.1 : Matrix (Fin n) (Fin n) K) (P.u 0) (P.w 0))
  have hF : Function.Injective F := by
    rintro ⟨B, hB⟩ ⟨B', hB'⟩ h
    simp only [F, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    show (B : Matrix (Fin n) (Fin n) K) i j = (B' : Matrix (Fin n) (Fin n) K) i j
    have hB0 := P.mem_radical.1 hB
    have hB0' := P.mem_radical.1 hB'
    by_cases hij : P.level j ≤ P.level i
    · rw [hB0 i j hij, hB0' i j hij]
    · have hi2 := P.level_le_two i
      have hj2 := P.level_le_two j
      have hlt : P.level i < P.level j := by omega
      obtain hi0 | hi1 : P.level i = 0 ∨ P.level i = 1 := by omega
      · obtain ⟨a, ha⟩ := P.level_eq_zero_iff.1 hi0
        obtain rfl : a = 0 := Subsingleton.elim a 0
        subst ha
        obtain hj1 | hj2' : P.level j = 1 ∨ P.level j = 2 := by omega
        · exact congrFun h1 ⟨j, P.mem_free.2 hj1⟩
        · obtain ⟨b, hb⟩ := P.level_eq_two_iff.1 hj2'
          obtain rfl : b = 0 := Subsingleton.elim b 0
          subst hb
          exact h3
      · have hj2' : P.level j = 2 := by omega
        obtain ⟨b, hb⟩ := P.level_eq_two_iff.1 hj2'
        obtain rfl : b = 0 := Subsingleton.elim b 0
        subst hb
        exact congrFun h2 ⟨i, P.mem_free.2 hi1⟩
  have hfree : Nat.card P.free = n - 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, P.card_free, Nat.mul_one]
  have hexp : 2 * n - 3 = (n - 2) + ((n - 2) + 1) := by omega
  calc Nat.card (P.radical K) ≤ Nat.card ((P.free → K) × (P.free → K) × K) :=
        Nat.card_le_card_of_injective F hF
    _ = Nat.card K ^ (2 * n - 3) := by
        rw [Nat.card_prod, Nat.card_prod, Nat.card_fun, hfree, hexp]
        ring


theorem exists_mulEquiv_projectiveSL {n : ℕ} {F : Type} [Field F] {Y : Type} [Group Y]
    (hZ : Subgroup.center Y = ⊥) (Ψ : SpecialLinearGroup (Fin n) F →* Y)
    (hs : Function.Surjective Ψ) (hk : Ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) F)) :
    ∃ e : projectiveSL n F ≃* Y, ∀ g, e (proj n F g) = Ψ g := by
  have hker : scalars n F = Ψ.ker := by
    apply le_antisymm
    · intro z hz
      rw [MonoidHom.mem_ker]
      have hzc : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) := by
        rw [← scalars_eq_center]; exact hz
      have : Ψ z ∈ Subgroup.center Y := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨g, rfl⟩ := hs y
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hzc g)]
      rw [hZ] at this
      exact Subgroup.mem_bot.mp this
    · intro z hz
      rw [scalars_eq_center]
      exact hk hz
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective Ψ hs), fun g => rfl⟩


theorem card_pCoreOf_centralizer_proj_transvection_le {m : ℕ} (hm : 2 ≤ m) {K : Type} [Field K]
    [Finite K] [CharP K 2] {t : SpecialLinearGroup (Fin (m + 1)) K} (ht : IsTransvection t) :
    Nat.card (pCoreOf 2 (Subgroup.centralizer
        ({proj (m + 1) K t} : Set (projectiveSL (m + 1) K)))) ≤ Nat.card K ^ (2 * m - 1) := by
  have hm1 : 1 ≤ m := by omega
  have hr : IsTransvection (CFSG.StandardType.AutPSL.rootInv (K := K) hm1) :=
    isTransvection_transvection _ one_ne_zero
  obtain ⟨W, hW⟩ := exists_conj_of_isTransvection hr ht
  let e : projectiveSL (m + 1) K ≃* projectiveSL (m + 1) K := MulAut.conj (proj (m + 1) K W)
  have he : e (CFSG.StandardType.KGPSL.r₀ (K := K) hm1) = proj (m + 1) K t := by
    rw [← hW]
    simp [e, CFSG.StandardType.KGPSL.r₀, map_mul, map_inv, MulAut.conj_apply]
  rw [← he, card_pCoreOf_centralizer_mulEquiv e,
    CFSG.StandardType.KGPSL.pCoreOf_centralizer_rootInv hm]
  have hrad : Nat.card (CFSG.StandardType.KGPSL.radical (K := K) hm1) ≤
      Nat.card (CFSG.StandardType.KGPSL.radicalSL (K := K) hm1) := by
    refine Nat.card_le_card_of_surjective
      (fun x : CFSG.StandardType.KGPSL.radicalSL (K := K) hm1 =>
        (⟨proj (m + 1) K x.1, Subgroup.mem_map_of_mem _ x.2⟩ :
          CFSG.StandardType.KGPSL.radical (K := K) hm1)) ?_
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine hrad.trans ?_
  have h2 := card_radical_le (K := K) (CFSG.StandardType.LinFusion.ggTransPlacement (m := m) hm1)
  have h3 : 2 * (m + 1) - 3 = 2 * m - 1 := by omega
  rw [h3] at h2
  exact h2

end CFSG.RankThree.GF2n.Smith81.Insp.KFact
