module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Defs
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.HardMathSupport.U4FF.BOSemi
public import CFSG.Quasithin.MS93.S32U
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C124B51Hyp
public import CFSG.Quasithin.Background.C124Core
public import CFSG.Quasithin.Background.C124L2PClass
public import CFSG.Quasithin.Background.C124Star
public import CFSG.Quasithin.Background.C124Z3Class
public import CFSG.Quasithin.Background.C126A5Core4
public import CFSG.Quasithin.Background.C126Defs
public import CFSG.Quasithin.Background.C1GNA7
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.C1PackBasic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.HConj
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.SmithB51SL3A
public import CFSG.Quasithin.MS93.SkItems
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivStab
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.HardMathSupport.U4FF
open Matrix

theorem k_Omega6Minus_aSet_isometry_holds :
    ∀ {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)} {n : ℕ} {F : Type}
      [Field F] [Finite F] {b c : F}, Nat.card F = 2 ^ n →
        (∀ s : F, s ^ 2 + b * s + c ≠ 0) →
        (ε : ↥H ≃* ↥(StatedOmega (StatedQuadMinus 3 F b c))) →
        (ψ : ↥(⊤ : Subgroup W) ≃*
          Multiplicative (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)) →
        NatCoordsOmegaMinusOn H ⊤ (fun _ _ s _ => Subgroup.mem_top s) F b c ε ψ →
        ∀ (Y : Subgroup (MulAut W)), Y ≤ Subgroup.normalizer (H : Set (MulAut W)) → ∀ k : ℕ,
          (3 ≤ k ∨ (Nat.card F = 4 ∧ 2 ≤ k)) →
            ∀ A : Subgroup (MulAut W), A ∈ E3.aSet k Y → ∀ a ∈ A,
              ∃ g : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F,
                (∀ s : ↥(⊤ : Subgroup W),
                  ψ ⟨a s.1, Subgroup.mem_top _⟩ = Multiplicative.ofAdd
                    ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
                      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec
                      (Multiplicative.toAdd (ψ s)))) ∧
                ∀ v, StatedQuadMinus 3 F b c
                  ((g : Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
                    (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F).mulVec v) =
                  StatedQuadMinus 3 F b c v := by
  intro W _ _ H n F _ _ b c hF hbc ε ψ hcoords Y hY k hk A hA a ha
  classical
  have hchar : CharP F 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hF
  obtain ⟨hAel, hAfix⟩ := hA.2.2.1, hA.2.2.2
  let eM : W ≃* Multiplicative (OIdx → F) :=
    (Subgroup.topEquiv (G := W)).symm.trans ψ
  have eM_apply : ∀ w : W, eM w = ψ ⟨w, Subgroup.mem_top w⟩ := fun w => rfl
  let cf : MulAut W → (OIdx → F) ≃+ (OIdx → F) := fun a' =>
    { toFun := fun x => Multiplicative.toAdd
        (eM (a' (eM.symm (Multiplicative.ofAdd x))))
      invFun := fun x => Multiplicative.toAdd
        (eM (a'⁻¹ (eM.symm (Multiplicative.ofAdd x))))
      left_inv := by
        intro x
        calc Multiplicative.toAdd
              (eM (a'⁻¹ (eM.symm (Multiplicative.ofAdd
                (Multiplicative.toAdd (eM (a' (eM.symm (Multiplicative.ofAdd x)))))))))
            = Multiplicative.toAdd
              (eM (a'⁻¹ (eM.symm (eM (a' (eM.symm (Multiplicative.ofAdd x))))))) := by
                rw [ofAdd_toAdd]
          _ = Multiplicative.toAdd (eM (a'⁻¹ (a' (eM.symm (Multiplicative.ofAdd x))))) := by
                rw [eM.symm_apply_apply]
          _ = Multiplicative.toAdd (eM (eM.symm (Multiplicative.ofAdd x))) := by
                rw [show a'⁻¹ (a' (eM.symm (Multiplicative.ofAdd x))) =
                  eM.symm (Multiplicative.ofAdd x) from by
                    simpa using MulAut.apply_inv_self a'⁻¹
                      (eM.symm (Multiplicative.ofAdd x))]
          _ = Multiplicative.toAdd (Multiplicative.ofAdd x) := by rw [eM.apply_symm_apply]
          _ = x := by simp
      right_inv := by
        intro x
        calc Multiplicative.toAdd
              (eM (a' (eM.symm (Multiplicative.ofAdd
                (Multiplicative.toAdd (eM (a'⁻¹ (eM.symm (Multiplicative.ofAdd x)))))))))
            = Multiplicative.toAdd
              (eM (a' (eM.symm (eM (a'⁻¹ (eM.symm (Multiplicative.ofAdd x))))))) := by
                rw [ofAdd_toAdd]
          _ = Multiplicative.toAdd (eM (a' (a'⁻¹ (eM.symm (Multiplicative.ofAdd x))))) := by
                rw [eM.symm_apply_apply]
          _ = Multiplicative.toAdd (eM (eM.symm (Multiplicative.ofAdd x))) := by
                rw [MulAut.apply_inv_self]
          _ = Multiplicative.toAdd (Multiplicative.ofAdd x) := by rw [eM.apply_symm_apply]
          _ = x := by simp
      map_add' := by
        intro x y
        simp only [ofAdd_add, map_mul, toAdd_mul] }
  let coord : MulAut W → AddAut (OIdx → F) := fun a' => cf a'
  have coord_apply : ∀ (a' : MulAut W) (x : OIdx → F),
      coord a' x = Multiplicative.toAdd
        (eM (a' (eM.symm (Multiplicative.ofAdd x)))) := fun a' x => rfl
  have coord_eM : ∀ (a' : MulAut W) (w : W),
      coord a' (Multiplicative.toAdd (eM w)) = Multiplicative.toAdd (eM (a' w)) := by
    intro a' w
    rw [coord_apply, ofAdd_toAdd, eM.symm_apply_apply]
  have coord_one : coord 1 = 0 := by
    ext x
    simp [coord, cf]
  have coord_mul : ∀ a' b', coord (a' * b') = coord a' + coord b' := by
    intro a' b'
    ext x
    simp [coord, cf, MulAut.mul_apply]
  let B : AddSubgroup (AddAut (OIdx → F)) :=
    { carrier := {x | ∃ a' ∈ A, coord a' = x}
      zero_mem' := ⟨1, A.one_mem, coord_one⟩
      add_mem' := by
        rintro x y ⟨a', ha', rfl⟩ ⟨b', hb', rfl⟩
        exact ⟨a' * b', A.mul_mem ha' hb', (coord_mul a' b').trans rfl⟩
      neg_mem' := by
        rintro x ⟨a', ha', rfl⟩
        refine ⟨a'⁻¹, A.inv_mem ha', ?_⟩
        have h : coord (a'⁻¹ * a') = coord a'⁻¹ + coord a' := coord_mul a'⁻¹ a'
        rw [inv_mul_cancel, coord_one] at h
        exact eq_neg_of_add_eq_zero_left h.symm }
  let A₀ : Subgroup (MulAut W) :=
    { carrier := {a' | a' ∈ A ∧ boIsLin (coord a')}
      one_mem' := ⟨A.one_mem, by rw [coord_one]; exact bo_isLin_zero⟩
      mul_mem' := by
        rintro a' b' ⟨ha', hla⟩ ⟨hb', hlb⟩
        refine ⟨A.mul_mem ha' hb', ?_⟩
        rw [coord_mul]
        exact bo_isLin_add hla hlb
      inv_mem' := by
        rintro a' ⟨ha', hla⟩
        refine ⟨A.inv_mem ha', ?_⟩
        have h : coord (a'⁻¹ * a') = coord a'⁻¹ + coord a' := coord_mul a'⁻¹ a'
        rw [inv_mul_cancel, coord_one] at h
        have hneg : coord a'⁻¹ = - coord a' := eq_neg_of_add_eq_zero_left h.symm
        rw [hneg]
        exact bo_isLin_neg hla }
  have memB : ∀ x, x ∈ B ↔ ∃ a' ∈ A, coord a' = x := fun x => Iff.rfl
  have memA₀ : ∀ a', a' ∈ A₀ ↔ a' ∈ A ∧ boIsLin (coord a') := fun a' => Iff.rfl
  have coord_inj : Function.Injective coord := by
    intro a' b' h
    ext w
    have h' := congrArg (fun f : AddAut (OIdx → F) =>
      f (Multiplicative.toAdd (eM w))) h
    rw [coord_apply, coord_apply, ofAdd_toAdd, eM.symm_apply_apply] at h'
    have h2 : eM (a' w) = eM (b' w) := Multiplicative.toAdd.injective h'
    exact eM.injective h2
  have hcardB : Nat.card B = Nat.card A := by
    refine (Nat.card_congr ?_).symm
    refine Equiv.ofBijective
      (fun a' : ↥A => (⟨coord a'.1, ⟨a'.1, a'.2, rfl⟩⟩ : ↥B)) ⟨?_, ?_⟩
    · intro a' b' h
      exact Subtype.ext (coord_inj (congrArg Subtype.val h))
    · rintro ⟨x, a', ha', rfl⟩
      exact ⟨⟨a', ha'⟩, rfl⟩
  have hcardA₀ : Nat.card (boLinSub B) = Nat.card A₀ := by
    refine (Nat.card_congr ?_).symm
    refine Equiv.ofBijective
      (fun a' : ↥A₀ => (⟨coord a'.1, ⟨⟨a'.1, a'.2.1, rfl⟩, a'.2.2⟩⟩ : ↥(boLinSub B)))
      ⟨?_, ?_⟩
    · intro a' b' h
      exact Subtype.ext (coord_inj (congrArg Subtype.val h))
    · rintro ⟨x, hxB, hlx⟩
      obtain ⟨a', ha', rfl⟩ := (memB x).1 hxB
      exact ⟨⟨a', ha', hlx⟩, rfl⟩
  have hB2 : ∀ x ∈ B, x + x = 0 := by
    rintro x ⟨a', ha', rfl⟩
    have h := coord_mul a' a'
    rw [show a' * a' = 1 from hAel.2 a' ha', coord_one] at h
    exact h.symm
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x + y = y + x := by
    rintro x ⟨a', ha', rfl⟩ y ⟨b', hb', rfl⟩
    rw [← coord_mul a' b', ← coord_mul b' a']
    exact congrArg coord (hAel.1 a' ha' b' hb')
  have hN_of_mem : ∀ a' ∈ Y, ∀ g ∈ StatedOmega (StatedQuadMinus 3 F b c),
      ∃ g' ∈ StatedOmega (StatedQuadMinus 3 F b c),
        ∀ x : OIdx → F,
          coord a' (((g : GL (OIdx) F) : Matrix (OIdx) (OIdx) F) *ᵥ x) =
            ((g' : GL (OIdx) F) : Matrix (OIdx) (OIdx) F) *ᵥ coord a' x := by
    intro a' ha' g hg
    obtain ⟨h, hh⟩ := ε.surjective ⟨g, hg⟩
    have hgval : ((ε h : ↥(StatedOmega (StatedQuadMinus 3 F b c))) : GL (OIdx) F) = g :=
      congrArg Subtype.val hh
    have hnorm : a' * (h : MulAut W) * a'⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp (hY ha') (h : MulAut W)).mp h.2
    let h' : ↥H := ⟨a' * (h : MulAut W) * a'⁻¹, hnorm⟩
    refine ⟨((ε h' : ↥(StatedOmega (StatedQuadMinus 3 F b c))) : GL (OIdx) F),
      (ε h').2, ?_⟩
    intro x
    let w : W := eM.symm (Multiplicative.ofAdd x)
    have hw : eM w = Multiplicative.ofAdd x := eM.apply_symm_apply _
    have hpsi : ψ ⟨w, Subgroup.mem_top w⟩ = Multiplicative.ofAdd x := by
      rw [← eM_apply w, hw]
    have hx : Multiplicative.toAdd (ψ ⟨w, Subgroup.mem_top w⟩) = x := by
      rw [hpsi]
      simp
    have h1 : eM ((h : MulAut W) w) = Multiplicative.ofAdd (g *ᵥ x) := by
      rw [eM_apply]
      have hc := hcoords h ⟨w, Subgroup.mem_top w⟩
      rw [hc, hgval, hx]
    have hw2 : eM.symm (Multiplicative.ofAdd (g *ᵥ x)) = (h : MulAut W) w := by
      rw [← h1, eM.symm_apply_apply]
    have hact : a' ((h : MulAut W) w) = (h' : MulAut W) (a' w) := by
      change a' ((h : MulAut W) w) = (a' * (h : MulAut W) * a'⁻¹) (a' w)
      simp [MulAut.mul_apply]
    have hcoordx : coord a' x = Multiplicative.toAdd (eM (a' w)) := by
      rw [coord_apply]
    have h2 : eM ((h' : MulAut W) (a' w)) =
        Multiplicative.ofAdd ((((ε h' : ↥(StatedOmega (StatedQuadMinus 3 F b c))) :
          GL (OIdx) F) : Matrix (OIdx) (OIdx) F) *ᵥ coord a' x) := by
      rw [eM_apply]
      have hc := hcoords h' ⟨a' w, Subgroup.mem_top (a' w)⟩
      rw [hc, ← eM_apply (a' w), ← hcoordx]
    calc coord a' (((g : GL (OIdx) F) : Matrix (OIdx) (OIdx) F) *ᵥ x)
        = Multiplicative.toAdd (eM (a' (eM.symm (Multiplicative.ofAdd
            (((g : GL (OIdx) F) : Matrix (OIdx) (OIdx) F) *ᵥ x))))) :=
          coord_apply a' _
      _ = Multiplicative.toAdd (eM (a' ((h : MulAut W) w))) := by rw [hw2]
      _ = Multiplicative.toAdd (eM ((h' : MulAut W) (a' w))) := by rw [hact]
      _ = Multiplicative.toAdd (Multiplicative.ofAdd
            ((((ε h' : ↥(StatedOmega (StatedQuadMinus 3 F b c))) : GL (OIdx) F) :
              Matrix (OIdx) (OIdx) F) *ᵥ coord a' x)) := by rw [h2]
      _ = (((ε h' : ↥(StatedOmega (StatedQuadMinus 3 F b c))) : GL (OIdx) F) :
            Matrix (OIdx) (OIdx) F) *ᵥ coord a' x := by simp
  have hsemi : ∀ x ∈ B, ∃ θ : F →+* F, ∀ (c' : F) (y : OIdx → F),
      x (c' • y) = θ c' • x y := by
    intro x hx
    obtain ⟨a', ha', rfl⟩ := (memB x).1 hx
    exact @bo_exists_semilinear_omega F _ _ hchar b c hbc (coord a')
      (hB2 (coord a') ⟨a', ha', rfl⟩) (hN_of_mem a' (hA.1 ha'))
  have hA₀le : A₀ ≤ A := fun a' ha' => (memA₀ a').1 ha' |>.1
  have hcard : Nat.card A ≤ 2 * Nat.card A₀ := by
    by_cases hex : ∃ a' ∈ A, ¬ boIsLin (coord a')
    · obtain ⟨s, hsA, hsnl⟩ := hex
      have hsB : coord s ∈ B := ⟨s, hsA, rfl⟩
      have hle := bo_card_le_two B hB2 hsemi hsB hsnl
      rwa [hcardB, hcardA₀] at hle
    · have hA₀eq : A₀ = A := by
        refine le_antisymm hA₀le (fun a' ha' => ?_)
        refine (memA₀ a').2 ⟨ha', ?_⟩
        by_contra h
        exact hex ⟨a', ha', h⟩
      rw [hA₀eq]
      omega
  have hmq : E3.mQuot A A₀ ≤ 1 := by
    have hcard' := E3.card_eq_two_pow_mul hAel.isPGroup hA₀le
    have hpos : 0 < Nat.card A₀ := Nat.card_pos
    have h2 : 2 ^ E3.mQuot A A₀ ≤ 2 := by
      rw [hcard'] at hcard
      exact Nat.le_of_mul_le_mul_right (by simpa using hcard) hpos
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using h2)
  have hlt : E3.mQuot A A₀ < k := by
    rcases hk with hk3 | ⟨-, hk2⟩
    · omega
    · omega
  have hfixA₀ : fixV A₀ = fixV A := hAfix A₀ hA₀le hlt
  have hcardFixA : Nat.card {x : OIdx → F // ∀ b' ∈ B, b' x = x} =
      Nat.card (fixV A) := by
    let f : {x : OIdx → F // ∀ b' ∈ B, b' x = x} → ↥(fixV A) := fun x =>
      ⟨eM.symm (Multiplicative.ofAdd x.1), by
        rw [mem_fixV]
        intro a' ha'
        have hxB : coord a' x.1 = x.1 := x.2 (coord a') ⟨a', ha', rfl⟩
        have hto : Multiplicative.toAdd (eM (a' (eM.symm (Multiplicative.ofAdd x.1)))) = x.1 := by
          rw [← coord_apply, hxB]
        have hof : eM (a' (eM.symm (Multiplicative.ofAdd x.1))) =
            Multiplicative.ofAdd x.1 := by
          rw [← ofAdd_toAdd (eM (a' (eM.symm (Multiplicative.ofAdd x.1)))), hto]
        calc a' (eM.symm (Multiplicative.ofAdd x.1))
            = eM.symm (eM (a' (eM.symm (Multiplicative.ofAdd x.1)))) :=
              (eM.symm_apply_apply _).symm
          _ = eM.symm (Multiplicative.ofAdd x.1) := by rw [hof]⟩
    let g : ↥(fixV A) → {x : OIdx → F // ∀ b' ∈ B, b' x = x} := fun w =>
      ⟨Multiplicative.toAdd (eM (w : W)), by
        intro b' hb'
        obtain ⟨a', ha', rfl⟩ := (memB b').1 hb'
        rw [coord_eM]
        rw [show a' (w : W) = (w : W) from (mem_fixV.mp w.2) a' ha']⟩
    refine Nat.card_congr ⟨f, g, ?_, ?_⟩
    · intro x
      refine Subtype.ext ?_
      simp [f, g]
    · intro w
      refine Subtype.ext ?_
      simp [f, g]
  have hcardFixA₀ : Nat.card (boLinFix B) = Nat.card (fixV A₀) := by
    let f : {x : OIdx → F // ∀ b' ∈ boLinSub B, b' x = x} → ↥(fixV A₀) := fun x =>
      ⟨eM.symm (Multiplicative.ofAdd x.1), by
        rw [mem_fixV]
        intro a' ha'
        have hxB : coord a' x.1 = x.1 := x.2 (coord a')
          (mem_boLinSub.mpr ⟨⟨a', (memA₀ a').1 ha' |>.1, rfl⟩,
            (memA₀ a').1 ha' |>.2⟩)
        have hto : Multiplicative.toAdd (eM (a' (eM.symm (Multiplicative.ofAdd x.1)))) = x.1 := by
          rw [← coord_apply, hxB]
        have hof : eM (a' (eM.symm (Multiplicative.ofAdd x.1))) =
            Multiplicative.ofAdd x.1 := by
          rw [← ofAdd_toAdd (eM (a' (eM.symm (Multiplicative.ofAdd x.1)))), hto]
        calc a' (eM.symm (Multiplicative.ofAdd x.1))
            = eM.symm (eM (a' (eM.symm (Multiplicative.ofAdd x.1)))) :=
              (eM.symm_apply_apply _).symm
          _ = eM.symm (Multiplicative.ofAdd x.1) := by rw [hof]⟩
    let g : ↥(fixV A₀) → {x : OIdx → F // ∀ b' ∈ boLinSub B, b' x = x} := fun w =>
      ⟨Multiplicative.toAdd (eM (w : W)), by
        intro b' hb'
        obtain ⟨a', ha', hba⟩ := (memB b').1 (mem_boLinSub.mp hb').1
        subst hba
        rw [coord_eM]
        rw [show a' (w : W) = (w : W) from
          (mem_fixV.mp w.2) a' ((memA₀ a').2 ⟨ha', (mem_boLinSub.mp hb').2⟩)]⟩
    refine Nat.card_congr ⟨f, g, ?_, ?_⟩
    · intro x
      refine Subtype.ext ?_
      simp [f, g]
    · intro w
      refine Subtype.ext ?_
      simp [f, g]
  have hxx : ∀ x : F, x + x = 0 := fun x => by
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    calc x + x = 2 * x := (two_mul x).symm
      _ = 0 := by simp [h2]
  have hsqW : ∀ w : W, w ^ 2 = 1 := by
    intro w
    have h1 : ψ (⟨w, Subgroup.mem_top w⟩ * ⟨w, Subgroup.mem_top w⟩) = 1 := by
      rw [map_mul]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      funext i
      exact hxx _
    have h2 : (⟨w, Subgroup.mem_top w⟩ * ⟨w, Subgroup.mem_top w⟩ : ↥(⊤ : Subgroup W)) = 1 :=
      ψ.injective (h1.trans (map_one ψ).symm)
    simpa [pow_two] using congrArg Subtype.val h2
  have hV1 : 1 < Nat.card (OIdx → F) := Finite.one_lt_card
  have hW1 : 1 < Nat.card W := by
    rw [Nat.card_congr (eM.toEquiv.trans (Multiplicative.toAdd (α := OIdx → F)))]
    exact hV1
  have hntW : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp hW1
  have hfix_ne : fixV A ≠ ⊥ :=
    @CFSG.Quasithin.MS93.S32.fixV_ne_bot_of_isPGroup W _ _ hsqW hntW A hAel.isPGroup
  have hlinA : ∀ a' ∈ A, boIsLin (coord a') := by
    intro a' ha'
    by_contra hnl
    have hsq := @bo_nonlin_fix_sq OIdx _ _ F _ _ hchar _ B hB2 hBcomm hsemi
      (coord a') ⟨a', ha', rfl⟩ hnl
    rw [hcardFixA, hcardFixA₀, hfixA₀] at hsq
    have hgt : 1 < Nat.card (fixV A) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hfix_ne
    have h1 : Nat.card (fixV A) * Nat.card (fixV A) ≤ Nat.card (fixV A) := by
      simpa [sq] using hsq
    nlinarith
  obtain ⟨M, hM⟩ := bo_exists_matrix (hlinA a ha)
  have h2a : coord a + coord a = 0 := hB2 (coord a) ⟨a, ha, rfl⟩
  have hMM : M * M = 1 := by
    apply bo_matrix_eq_of_mulVec
    intro x
    rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hM, hM]
    exact bo_invol_apply h2a x
  let g : GL (OIdx) F := ⟨M, M, hMM, hMM⟩
  have hiso := @bo_isometry_of_isLin F _ _ hchar b c hbc (coord a) h2a
    (hlinA a ha) (hN_of_mem a (hA.1 ha))
  refine ⟨g, ?_, ?_⟩
  · intro s
    have h1 : M *ᵥ Multiplicative.toAdd (ψ s) =
        Multiplicative.toAdd (ψ ⟨a s.1, Subgroup.mem_top _⟩) := by
      rw [← eM_apply s.1, hM, coord_eM, eM_apply (a s.1)]
    calc ψ ⟨a s.1, Subgroup.mem_top _⟩
        = Multiplicative.ofAdd
            (Multiplicative.toAdd (ψ ⟨a s.1, Subgroup.mem_top _⟩)) := by simp
      _ = Multiplicative.ofAdd (M *ᵥ Multiplicative.toAdd (ψ s)) := by rw [h1]
      _ = Multiplicative.ofAdd (((g : GL (OIdx) F) : Matrix (OIdx) (OIdx) F) *ᵥ
            Multiplicative.toAdd (ψ s)) := rfl
  · intro v
    have := hiso v
    simpa [g, hM] using this

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
