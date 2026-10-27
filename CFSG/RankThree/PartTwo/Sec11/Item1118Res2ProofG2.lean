module

public import CFSG.RankThree.PartTwo.Sec11.Item1118Res2ProofFamily
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofConj
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofCent

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace Item1118Res2Proof

theorem three_dvd_sq_sub_one' {q : ℕ} (h : ¬ 3 ∣ q) : 3 ∣ q ^ 2 - 1 := by
  have h1 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod]
    have : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases this with h | h <;> rw [h]
  generalize q ^ 2 = Q at h1 ⊢
  omega

theorem not_three_dvd_card {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3) :
    ¬ 3 ∣ Nat.card K := by
  intro h3
  have : Fintype K := Fintype.ofFinite K
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hcard] at h3
  exact hK3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)).symm

section Model


theorem exists_a2_model_of_short {L : Type} [Field L] [Finite L] (h31 : 3 ∣ Nat.card L - 1)
    {x : adjointGroup .G2 L} (hxS : x ∈ KS11Lie4Proof.g2ShortSL2 L) (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) :
    ∃ (m : adjointGroup .G2 L) (φ : Matrix.SpecialLinearGroup (Fin (2 + 1)) L →*
      adjointGroup .G2 L), Function.Injective φ ∧
      (∀ X, φ X * (m * x * m⁻¹) = (m * x * m⁻¹) * φ X) ∧
      ∀ w, w * (m * x * m⁻¹) = (m * x * m⁻¹) * w → ∃ X, φ X = w := by
  obtain ⟨A, hA⟩ := KS11Lie4Proof.mem_g2ShortSL2_iff.mp hxS
  have hinj := KS11Lie4Proof.rhoV_injective (K := L)
  have hA3 : A ^ 3 = 1 := hinj (by
    rw [map_pow, hA, map_one]
    exact congrArg Subtype.val hx3)
  obtain ⟨P, t, hPt⟩ := KS11Lie4Proof.exists_conj_HSL_of_three h31 A ⟨1, by simpa using hA3⟩
  have ht3 : orderOf t = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · apply KS11Lie4Proof.HSLHom_injective (K := L)
      rw [map_pow, KS11Lie4Proof.HSLHom_apply, ← hPt, conj_pow, hA3, mul_one, mul_inv_cancel,
        map_one]
    · rintro rfl
      apply hx1
      have h1 : A = 1 := by
        have : P * A * P⁻¹ = 1 := by rw [hPt]; exact (map_one (KS11Lie4Proof.HSLHom L))
        simpa using this
      apply Subtype.ext
      rw [← hA, h1, map_one]
      rfl
  set m : adjointGroup .G2 L := ⟨KS11Lie4Proof.rhoV L P, by
    rw [KS11Lie4Proof.rhoV_apply]
    exact mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ L _)
      (simpleRootSL2_mem_adjointGroup _ P)) (inv_mem (canonicalRep_mem_adjointGroup _ L _))⟩
    with hmdef
  have hdcoe : ((m * x * m⁻¹ : adjointGroup .G2 L) : ModGL .G2 L) =
      rootDiagUnit .G2 (Pi.mulSingle g2ir t) := by
    rw [KS11Lie4Proof.coe_conj, ← hA, ← KS11Lie4Proof.rhoV_HSL, ← hPt]
    simp only [map_mul, map_inv]
    rfl
  obtain ⟨φ, hφinj, hφ⟩ := exists_a2Hom_injective (K := L)
  have hKer := KS11Lie4Proof.rootCharKernel_threeA (K := L) ht3
  refine ⟨m, φ, hφinj, ?_, ?_⟩
  · have hle := KS11Lie4Proof.range_le_of_a2y φ hφ
      (Subgroup.centralizer ({m * x * m⁻¹} : Set (adjointGroup .G2 L))) fun γ hγ c => by
        rw [KS11Lie4Proof.mem_centralizer_iff_toral hdcoe, mem_toralCentralizer]
        refine ⟨(a2y γ c).2, ?_⟩
        rw [KS11Lie4Proof.coe_a2y hγ]
        have hmem : CFSG.LieType.Steinberg.RankTwo.g2CommRoot (a2pos (γ 0, γ 1)) ∈
            rootCharKernel (Pi.mulSingle g2ir t) := by
          rw [hKer]
          exact KS11Lie4Proof.a2_long_roots hγ
        rw [rootDiagUnit_conj_pinnedX _ hmem.1, hmem.2, Units.val_one, one_mul]
    intro X
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ⟨X, rfl⟩)
  · intro w hw
    have hw' : (w : ModGL .G2 L) ∈ toralCentralizer .G2 L (Pi.mulSingle g2ir t) :=
      (KS11Lie4Proof.mem_centralizer_iff_toral hdcoe).mp
        (Subgroup.mem_centralizer_singleton_iff.mpr hw)
    obtain ⟨w', ⟨X, rfl⟩, hX⟩ :=
      Sec4.Res417Seven.toralCentralizer_threeA_le_range_a2 φ hφ ht3 hw'
    exact ⟨X, Subtype.ext hX⟩

end Model

section G2


theorem exists_sl3_model_g2 {Z : Type} [Group Z] [Finite Z]
    (hZ : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p ≠ 3 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X))
    {z : Z} {J : Subgroup Z} (hz3 : MulAut.conj z ^ 3 = 1)
    (hJ : J ∈ thetaComponentsIn (Item426.fixSub (MulAut.conj z)))
    (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J)) {v : Z} (hvJ : v ∈ J) (hv3 : v ^ 3 = 1)
    (hv1 : v ≠ 1) :
    ∃ (L : Type) (_ : Field L) (ψ : Subgroup.centralizer ({v} : Set Z) →*
      Matrix.SpecialLinearGroup (Fin 3) L), Function.Injective ψ ∧
      ψ ⟨v, self_mem_centralizer v⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L) := by
  obtain ⟨K, _, _, hK3, -, e, -, h⟩ := KS11Lie4Proof.exists_g2_threeB
    (KS11Lie4Proof.g2ThreeConjSL2_of_minus KS11Lie7Proof.g2ThreeConjSL2Minus_holds)
    (KS11Lie4Proof.g2ThreeACent_of_minus KS11Lie7Proof.g2ThreeACentMinus_holds)
    KS11Lie4Proof.g2ThreeBCent_holds hZ hz3 hJ hJT
  have hJS := h.eq hJ
  have hevS : e v ∈ KS11Lie4Proof.g2ShortSL2 K := by
    have : v ∈ (KS11Lie4Proof.g2ShortSL2 K).comap e.toMonoidHom := hJS ▸ hvJ
    exact this
  obtain ⟨L, _, _, _, -, hdeg, -⟩ := KS11Lie4Proof.exists_quadratic_ext' K
  have h31 : 3 ∣ Nat.card L - 1 := by
    rw [KS11Lie4Proof.natCard_quadratic hdeg]
    exact three_dvd_sq_sub_one' (not_three_dvd_card hK3)
  set β := KS11Lie4Proof.bcG2 K L with hβdef
  have hβ : Function.Injective β := KS11Lie4Proof.bcG2_injective
  have hxS : β (e v) ∈ KS11Lie4Proof.g2ShortSL2 L := KS11Lie4Proof.bcG2_mem_g2ShortSL2 hevS
  have hx3 : β (e v) ^ 3 = 1 := by rw [← map_pow, ← map_pow, hv3, map_one, map_one]
  have hx1 : β (e v) ≠ 1 := by
    intro h1
    apply hv1
    apply e.injective
    apply hβ
    rw [h1, map_one, map_one]
  obtain ⟨m, φ, hφinj, hφd, hdφ⟩ := exists_a2_model_of_short h31 hxS hx3 hx1
  set Φ : Z →* adjointGroup .G2 L :=
    (MulAut.conj m).toMonoidHom.comp (β.comp e.toMonoidHom) with hΦdef
  have hΦ : ∀ x, Φ x = m * β (e x) * m⁻¹ := fun x => rfl
  have hΦinj : Function.Injective Φ := fun a b hab => by
    rw [hΦ, hΦ] at hab
    exact e.injective (hβ (mul_left_cancel (mul_right_cancel hab)))
  have hΦv : Φ v = m * β (e v) * m⁻¹ := hΦ v
  have hmem : ∀ x : Subgroup.centralizer ({v} : Set Z),
      (Φ.comp (Subgroup.centralizer ({v} : Set Z)).subtype) x ∈ φ.range := by
    intro x
    obtain ⟨X, hX⟩ := hdφ (Φ x) (by
      rw [← hΦv, ← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_centralizer_singleton_iff.mp x.2)
    exact ⟨X, hX⟩
  set ψ : Subgroup.centralizer ({v} : Set Z) →* Matrix.SpecialLinearGroup (Fin 3) L :=
    (MonoidHom.ofInjective hφinj).symm.toMonoidHom.comp
      ((Φ.comp (Subgroup.centralizer ({v} : Set Z)).subtype).codRestrict φ.range hmem)
    with hψdef
  have hφψ : ∀ x, φ (ψ x) = Φ x := fun x => by
    rw [hψdef, MonoidHom.comp_apply]
    exact MonoidHom.apply_ofInjective_symm hφinj _
  refine ⟨L, inferInstance, ψ, fun a b hab => ?_, ?_⟩
  · have h1 := congrArg φ hab
    rw [hφψ, hφψ] at h1
    exact Subtype.ext (hΦinj h1)
  · rw [Subgroup.mem_center_iff]
    intro X
    apply hφinj
    rw [map_mul, map_mul, hφψ]
    exact (hφd X).trans rfl

end G2

end Item1118Res2Proof

section KFacts


open Item1118Res2Proof in
theorem sl3Model1118For_g2 : SL3Model1118For fun X _ => ∃ (q : TauCeti.PrimePower)
    (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p ≠ 3 ∧
    Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group) := by
  intro Z _ _ hZ z v J hz3 hJ hJT hvJ hv3 hv1
  obtain ⟨L, _, ψ, hψ, hψv⟩ := exists_sl3_model_g2 hZ hz3 hJ hJT hvJ hv3 hv1
  exact ⟨(KS11Lie4Proof.g2_order_three hZ hz3 hJ hJT).1, L, inferInstance, ψ,
    isSL3Model_of_injective hψ hψv hv1⟩

theorem invElt1118G2Ss_holds : InvElt1118G2Ss :=
  Item1118Res2Proof.invElt1118For_of_sl3Model sl3Model1118For_g2

theorem comm1119G2Ss_holds : Comm1119G2Ss :=
  Item1118Res2Proof.comm1119For_of_sl3Model sl3Model1118For_g2

end KFacts

end CFSG.RankThree.PartTwo.Sec11
