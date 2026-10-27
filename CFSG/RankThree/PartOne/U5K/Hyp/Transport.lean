module

public import CFSG.RankThree.PartOne.U5K.Hyp.Assemble
public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveModelBridge

public noncomputable section

namespace CFSG.RankThree.PartOne.U5K

open CFSG
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.Sec4

theorem u5_center_eq_bot (f : ℕ) (hf : 1 ≤ f) : Subgroup.center (projSU 5 2 f) = ⊥ := by
  have hs := u5_isSimpleGroup f hf
  have hp := u5_isPerfect f hf
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (projSU 5 2 f)) with h | h
  · exact h
  · exfalso
    have h1 : commutator (projSU 5 2 f) = ⊥ := (commutator_eq_bot_iff_center_eq_top _).2 h
    have h2 : commutator (projSU 5 2 f) = ⊤ := hp.commutator_eq_top
    rw [h1] at h2
    obtain ⟨x, hx⟩ := exists_ne (1 : projSU 5 2 f)
    exact hx (Subgroup.mem_bot.1 (h2 ▸ Subgroup.mem_top x))

theorem mulAut_congr_conj {G H : Type*} [Group G] [Group H] (ι : G ≃* H) (x : G) :
    MulAut.congr ι (MulAut.conj x) = MulAut.conj (ι x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply, map_mul, map_inv]

theorem mulAut_congr_trans {G H L : Type*} [Group G] [Group H] [Group L] (e : G ≃* H)
    (e' : H ≃* L) (α : MulAut G) :
    MulAut.congr (e.trans e') α = MulAut.congr e' (MulAut.congr e α) := by
  ext y
  simp [MulAut.congr_apply]

theorem U5Inndiag_eq (f : ℕ) (hf : 1 ≤ f) : U5Inndiag f = (u5FieldFactor f hf).ker := by
  simp [U5Inndiag, hf]

theorem U5Inn_le_U5Inndiag (f : ℕ) (hf : 1 ≤ f) : U5Inn f ≤ U5Inndiag f := by
  rintro _ ⟨z, rfl⟩
  have hα : MulAut.congr (u5Equiv f hf) (MulAut.conj z) ∈
      (primeFormFieldFactor (u5FieldData f hf)
        (isPrimeFormGram_one_GL (n := 5) (K := GaloisField 2 (2 * f)))
        (by norm_num) (by omega)).ker := by
    rw [mulAut_congr_conj, ker_primeFormFieldFactor]
    obtain ⟨s, hs⟩ := (mem_inner_primeFormP (u5FieldData f hf) _ _).1
      ⟨u5Equiv f hf z, rfl⟩
    exact ⟨⟨s, s.2.1⟩, hs.symm⟩
  rw [U5Inndiag_eq f hf]
  exact hα

theorem u5Model : U5Model := by
  intro f hf p hp hp5 hpf H T hInnH hT
  classical
  set h : UnitaryFieldData 2 f (GaloisField 2 (2 * f)) := u5FieldData f hf with hh
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 2) (ε := 1) h
  set ι : projSU 5 2 f ≃* hypPSU h 2 1 :=
    (u5Equiv f hf).trans (KCEvenUnitaryFiveBridge.hypToPrimeForm h hR).symm with hι
  set θ : MulAut (projSU 5 2 f) ≃* MulAut (hypPSU h 2 1) := MulAut.congr ι with hθ
  have hZ : Subgroup.center (hypPSU h 2 1) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
    have hz' : ι.symm z ∈ Subgroup.center (projSU 5 2 f) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      apply ι.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz (ι y)
    rw [u5_center_eq_bot f hf, Subgroup.mem_bot] at hz'
    simpa using congrArg ι hz'
  have hfin : Finite (MulAut (hypPSU h 2 1)) := Hyp.finite_mulAut_hyp h
  have hfin' : Finite (MulAut (projSU 5 2 f)) := Finite.of_equiv _ θ.symm.toEquiv
  have hInn : (U5Inn f).map θ.toMonoidHom = Hyp.Pi h := by
    ext α
    constructor
    · rintro ⟨β, ⟨x, rfl⟩, rfl⟩
      exact ⟨ι x, (mulAut_congr_conj ι x).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := ι.surjective y
      exact ⟨MulAut.conj x, ⟨x, rfl⟩, mulAut_congr_conj ι x⟩
  have hDg : (U5Inndiag f).map θ.toMonoidHom ≤ Hyp.Dlin h := by
    rintro _ ⟨α, hα, rfl⟩
    have hα' : α ∈ (u5FieldFactor f hf).ker := by
      rwa [U5Inndiag_eq f hf] at hα
    have hα1 : MulAut.congr (u5Equiv f hf) α ∈
        (primeFormFieldFactor h (isPrimeFormGram_one_GL (n := 5) (K := GaloisField 2 (2 * f)))
          (by norm_num) (by omega)).ker := hα'
    rw [ker_primeFormFieldFactor] at hα1
    obtain ⟨A, hA⟩ := hα1
    have h2 : θ α = linearSimAut h (by norm_num : 1 ≤ 2) le_rfl
        (KCEvenUnitaryFiveBridge.toSimilitude h hR A) := by
      rw [hθ, hι, mulAut_congr_trans, ← hA]
      exact KCEvenUnitaryFiveBridge.mulAut_congr_conj_eq h hR A
    change θ α ∈ Hyp.Dlin h
    rw [h2]
    exact ⟨_, Hyp.mem_Gam1.2 rfl, rfl⟩
  have hHT : CFSG.ABGLocalTools.IsSylowOf 2 (T.map θ.toMonoidHom) (H.map θ.toMonoidHom) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨Subgroup.map_mono hT.1, hT.2.1.map _, ?_⟩
    rw [Subgroup.relIndex_map_map_of_injective _ _ θ.injective]
    exact hT.2.2
  have hPi : Hyp.Pi h ≤ H.map θ.toMonoidHom := hInn ▸ Subgroup.map_mono hInnH
  have hM := Hyp.modelFacts_sylow hZ hp hp5 hpf hPi hHT
  have hinj : ∀ X : Subgroup (MulAut (projSU 5 2 f)),
      Function.Injective (θ.toMonoidHom.comp X.subtype) := fun X =>
    θ.injective.comp X.subtype_injective
  have hS : (pushingUpS T).map θ.toMonoidHom = pushingUpS (T.map θ.toMonoidHom) :=
    map_pushingUpS θ.toMonoidHom (hinj T)
  have hV : (zOf (pushingUpS T)).map θ.toMonoidHom = zOf (pushingUpS (T.map θ.toMonoidHom)) := by
    rw [← hS]
    exact map_zOf θ.toMonoidHom (hinj _)
  have hM' : Hyp.ModelFacts p ((U5Inn f).map θ.toMonoidHom) ((U5Inndiag f).map θ.toMonoidHom)
      ((pushingUpS T).map θ.toMonoidHom) ((zOf (pushingUpS T)).map θ.toMonoidHom) := by
    rw [hInn, hS, hV]
    exact hM.mono hDg
  have hF := hM'.of_map hp θ
  exact ⟨hF.le_inn, hF.irreducible, hF.core, hF.faithful, hF.cyclic⟩

end CFSG.RankThree.PartOne.U5K
