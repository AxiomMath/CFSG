module

public import CFSG.RankThree.PartTwo.Sec19.Step1914MoreProofCore
public import CFSG.RankThree.PartTwo.Sec19.Step1914Split
public import CFSG.RankThree.PartTwo.Sec13.Steps
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec19.Step1914SplitUse
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item132
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item414Local
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof
import CFSG.RankThree.PartTwo.Sec13.Naturality

public section

namespace CFSG.RankThree.PartTwo.Sec19.Step1914MoreProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem card_autIn_of_m12
    (h131 : Item131) {A L E M : Subgroup G} {c : G} (hctx : Ctx1912 G A c L E M)
    (hθM : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12))
    (hE9 : Nat.card (E ⊓ L : Subgroup G) = 9) : Nat.card (Sec4.autIn L E) = 48 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  have hAE := isE27_of_mem_partTwoE hctx.mem_partTwoE
  have hA : CFSG.Assembly.IsElemAbelian 3 A := hctx.mem_partTwoE.1
  have hcA : c ∈ A := hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)
  have hcE : c ∈ E :=
    mem_of_le_centralizer hst hctx.partTwoS_eq hEE (hA.2 c hcA) hctx.le_centralizer
  have hcL : c ∉ L := hctx.hypS.2.2 c hctx.zpowers_mem_omegaA L hctx.mem_lA
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  have hFE : partTwoF G = partTwoE G :=
    (hctx.toTheoremFourHyp.partTwoF_eq_partTwoE hctx.partTwoS_eq).1
  have hD : Sec13Data G A c L := ⟨hst, hctx.partTwoS_eq, hFE ▸ hctx.mem_partTwoE,
    hctx.not_mem_partTwoT, hctx.zpowers_mem_omegaA, hctx.mem_lA⟩
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl)
  obtain ⟨-, hA9, ⟨eA⟩⟩ := facts_of_m12 h131 sporadicModels131 hD hθM
  have hAB : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
    Step1914TriProof.eq_zpowers_sup_of_nine_le hAE hcA hcL (by rw [hA9])
  have hEB : E = Subgroup.zpowers c ⊔ (E ⊓ L) :=
    Step1914TriProof.eq_zpowers_sup_of_nine_le hE hcE hcL (by rw [hE9])
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  have hQ3 : IsPGroup 3 (((E ⊔ A) ⊓ L).subgroupOf L) :=
    (hctx.isPGroup_sup.to_le inf_le_left).comap_subtype
  obtain ⟨S, hQS⟩ := hQ3.exists_le_sylow
  have hS3 : IsPGroup 3 (S : Subgroup L) := S.isPGroup'
  have hAbS : (A ⊓ L).subgroupOf L ≤ S :=
    (Subgroup.subgroupOf_mono L (inf_le_inf_right L le_sup_right)).trans hQS
  have hEbS : (E ⊓ L).subgroupOf L ≤ S :=
    (Subgroup.subgroupOf_mono L (inf_le_inf_right L le_sup_left)).trans hQS
  have hAb9 : Nat.card ((A ⊓ L).subgroupOf L) = 9 := by
    rw [← hA9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hEb9 : Nat.card ((E ⊓ L).subgroupOf L) = 9 := by
    rw [← hE9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hAp : IsPGroup 3 (A ⊓ L : Subgroup G) := IsPGroup.of_card (n := 2) (by rw [hA9]; norm_num)
  have hEp : IsPGroup 3 (E ⊓ L : Subgroup G) := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  have hBaut : Nat.card (Sec4.autIn ⊤ (((A ⊓ L).subgroupOf L).map π)) = 6 := by
    obtain ⟨e⟩ := nonempty_autIn_zpowers_sup_equiv hc3 hcL hLc inf_le_right hAp
    rw [← hAB] at e
    rw [Nat.card_congr (e.symm.trans eA).toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  obtain ⟨E₀, F₀, t₀, ht₀, -, hΔ, -, ⟨eE⟩, ⟨eF⟩, -⟩ := exists_bar_config
    Sec4.Sporadic.rank3II_4_14_local (fun X _ h => Toolkit.m12ThreeLocalData X h) hθM S hAbS
    hAb9 hBaut
  have hEbmem : ((E ⊓ L).subgroupOf L).map π ∈
      {Y : Subgroup (L ⧸ aschbacherSolvableCore 3 L) |
        Y ≤ (S : Subgroup L).map π ∧ Nat.card Y = 9} := by
    refine ⟨Subgroup.map_mono hEbS, ?_⟩
    rw [card_map_eq_of_injOn _ (injOn_mk_of_isPGroup Nat.prime_three (hS3.to_le hEbS)), hEb9]
  rw [hΔ] at hEbmem
  have hΦE : liftSup L c S (((E ⊓ L).subgroupOf L).map π) = E := by
    rw [liftSup_map hS3 hEbS, Subgroup.map_subgroupOf_eq_of_le inf_le_right, ← hEB]
  have hΦA : liftSup L c S (((A ⊓ L).subgroupOf L).map π) = A := by
    rw [liftSup_map hS3 hAbS, Subgroup.map_subgroupOf_eq_of_le inf_le_right, ← hAB]
  have hΦAt : liftSup L c S (conjugate (((A ⊓ L).subgroupOf L).map π) (π t₀)) =
      conjugate A (t₀ : G) := by
    rw [liftSup_conjugate hLc hS3 (Subgroup.map_mono hAbS) ht₀, hΦA]
  have hGL : Nonempty (Sec4.autIn ⊤ (((E ⊓ L).subgroupOf L).map π) ≃* GL (Fin 2) (ZMod 3)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hEbmem
    rcases hEbmem with h1 | h1 | h1 | h1
    · rw [h1]
      exact ⟨eE⟩
    · rw [h1]
      exact ⟨eF⟩
    · exfalso
      have hEA : E = A := by rw [← hΦE, h1, hΦA]
      exact hctx.not_mem_partTwoT (hEA ▸ hctx.mem_partTwoT)
    · exfalso
      have hEA : E = conjugate A (t₀ : G) := by rw [← hΦE, h1, hΦAt]
      apply hctx.not_mem_partTwoT
      have hT := hctx.mem_partTwoT
      rw [hEA, conjugate] at hT
      exact (map_mem_partTwoT_iff (MulAut.conj (t₀ : G)⁻¹)).mp hT
  obtain ⟨eGL⟩ := hGL
  obtain ⟨e⟩ := nonempty_autIn_zpowers_sup_equiv hc3 hcL hLc (inf_le_right : E ⊓ L ≤ L) hEp
  rw [← hEB] at e
  rw [Nat.card_congr (e.trans eGL).toEquiv]
  exact Asc83Table.card_GL23

theorem exists_realize {E B L : Subgroup G} {c X₁ X₂ : G} (h : BasisData E B c X₁ X₂)
    (hLc : ∀ l ∈ L, l * c = c * l)
    (hLB : ∀ l ∈ L, l ∈ Subgroup.normalizer (E : Set G) → l ∈ Subgroup.normalizer (B : Set G))
    (h48 : Nat.card (Sec4.autIn L E) = 48) (T : SL23) :
    ∃ l ∈ L, l ∈ Subgroup.normalizer (E : Set G) ∧ l ∈ Subgroup.normalizer (B : Set G) ∧
      l * X₁ * l⁻¹ = X₁ ^ ((T : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0).val *
        X₂ ^ ((T : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0).val ∧
      l * X₂ * l⁻¹ = X₁ ^ ((T : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1).val *
        X₂ ^ ((T : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 1).val := by
  obtain ⟨f, hf⟩ := h.exists_adapted
  set φ := KFacts.glHom f with hφ
  have hfix : ∀ σ ∈ Sec4.autIn L E, σ ⟨c, h.mem_c⟩ = ⟨c, h.mem_c⟩ ∧
      ∀ x : E, (x : G) ∈ B → (σ x : G) ∈ B := by
    intro σ hσ
    obtain ⟨l, hlN, hlL, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    refine ⟨Subtype.ext ?_, fun x hx => ?_⟩
    · rw [Sec13.normalizerMonoidHom_apply_val, hLc l hlL, mul_inv_cancel_right]
    · rw [Sec13.normalizerMonoidHom_apply_val]
      exact (Subgroup.mem_normalizer_iff.mp (hLB l hlL hlN) x).mp hx
  have hmat : ∀ σ ∈ Sec4.autIn L E, ∀ i : Fin 3,
      ((φ σ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) i 2 = (Pi.single 2 1 : Fin 3 → ZMod 3) i ∧
        ((φ σ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 0 = 0 ∧
        ((φ σ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 1 = 0 := by
    intro σ hσ i
    obtain ⟨hc, hB⟩ := hfix σ hσ
    have hrow := h.row_two_eq_zero hf hB
    refine ⟨?_, hrow.1, hrow.2⟩
    rw [hφ, glHom_entry]
    have e2 : f (Multiplicative.ofAdd (Pi.single 2 1)) = ⟨c, h.mem_c⟩ :=
      Subtype.ext (f_two hf)
    rw [e2, hc, ← e2]
    simp [Sec12.coordVec]
  have hblk : ∀ σ ∈ Sec4.autIn L E, ∀ τ ∈ Sec4.autIn L E,
      blkMat ((φ σ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) *
        blkMat ((φ τ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      blkMat ((φ (σ * τ) : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
    intro σ hσ τ hτ
    rw [map_mul, Units.val_mul, blkMat_mul (hmat τ hτ 0).2.1 (hmat τ hτ 0).2.2]
  let F : Sec4.autIn L E → GL (Fin 2) (ZMod 3) := fun σ =>
    ⟨blkMat ((φ σ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)),
      blkMat ((φ (σ : MulAut E)⁻¹ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)), by
        rw [hblk _ σ.2 _ (inv_mem σ.2), mul_inv_cancel, map_one, Units.val_one]
        ext i j
        fin_cases i <;> fin_cases j <;> rfl, by
        rw [hblk _ (inv_mem σ.2) _ σ.2, inv_mul_cancel, map_one, Units.val_one]
        ext i j
        fin_cases i <;> fin_cases j <;> rfl⟩
  have hF : Function.Injective F := by
    intro σ τ hστ
    have hb := congrArg (fun g : GL (Fin 2) (ZMod 3) => (g : Matrix (Fin 2) (Fin 2) (ZMod 3))) hστ
    simp only [F] at hb
    apply Subtype.ext
    apply KFacts.glHom_injective f
    apply Units.ext
    ext i j
    have hσ := hmat σ σ.2
    have hτ := hmat τ τ.2
    have hb' := fun a b => congrFun (congrFun hb a) b
    fin_cases i <;> fin_cases j
    · exact hb' 0 0
    · exact hb' 0 1
    · exact (hσ 0).1.trans (hτ 0).1.symm
    · exact hb' 1 0
    · exact hb' 1 1
    · exact (hσ 1).1.trans (hτ 1).1.symm
    · exact (hσ 0).2.1.trans (hτ 0).2.1.symm
    · exact (hσ 0).2.2.trans (hτ 0).2.2.symm
    · exact (hσ 2).1.trans (hτ 2).1.symm
  have hFbij : Function.Bijective F := by
    refine hF.bijective_of_nat_card_le ?_
    rw [h48, Asc83Table.card_GL23]
  obtain ⟨⟨σ, hσ⟩, hσT⟩ := hFbij.2 (Matrix.SpecialLinearGroup.toGL T)
  have hσT' : blkMat ((φ σ : GL33) : Matrix (Fin 3) (Fin 3) (ZMod 3)) =
      (T : Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
    congrArg (fun g : GL (Fin 2) (ZMod 3) => (g : Matrix (Fin 2) (Fin 2) (ZMod 3))) hσT
  obtain ⟨l, hlN, hlL, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
  refine ⟨l, hlL, hlN, hLB l hlL hlN, ?_, ?_⟩
  ·
    have hcol : Sec12.coordVec f (E.normalizerMonoidHom ⟨l, hlN⟩
        (f (Multiplicative.ofAdd (Pi.single 0 1)))) =
        ![(T : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0, (T : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0,
          0] := by
      funext i
      rw [← glHom_entry f _ i 0, ← hσT']
      fin_cases i
      · rfl
      · rfl
      · exact (hmat _ hσ 0).2.1
    have e := congrArg (fun v => (f (Multiplicative.ofAdd v) : G)) hcol
    simp only [Sec12.coordVec, ofAdd_toAdd, MulEquiv.apply_symm_apply] at e
    rw [Sec13.normalizerMonoidHom_apply_val, f_zero hf, coords_apply hf] at e
    rw [e, ZMod.val_zero, pow_zero, mul_one]
  ·
    have hcol : Sec12.coordVec f (E.normalizerMonoidHom ⟨l, hlN⟩
        (f (Multiplicative.ofAdd (Pi.single 1 1)))) =
        ![(T : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1, (T : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 1,
          0] := by
      funext i
      rw [← glHom_entry f _ i 1, ← hσT']
      fin_cases i
      · rfl
      · rfl
      · exact (hmat _ hσ 0).2.2
    have e := congrArg (fun v => (f (Multiplicative.ofAdd v) : G)) hcol
    simp only [Sec12.coordVec, ofAdd_toAdd, MulEquiv.apply_symm_apply] at e
    rw [Sec13.normalizerMonoidHom_apply_val, f_one hf, coords_apply hf] at e
    rw [e, ZMod.val_zero, pow_zero, mul_one]

theorem exists_coreData_of_m12
    (htri : Step1914Tri) (h131 : Item131) {A L E M : Subgroup G} {c : G}
    (hctx : Ctx1912 G A c L E M) (hLM : ¬ L ≤ M)
    (hM12 : Nonempty (L ⧸ CFSG.pCore 2 L ≃* CFSG.Blueprint.NativeSporadic.M12)) :
    ∃ X₁ X₂ M₁ M₂ : G, CoreData E (E ⊓ L) c X₁ X₂ M₁ M₂ ∧
      ∃ y ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G), y * c = c * y ∧
        (∀ b ∈ E ⊓ L, y ^ 3 * b * (y ^ 3)⁻¹ = b) ∧ ∃ b ∈ E ⊓ L, y * b * y⁻¹ ≠ b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  have hA : CFSG.Assembly.IsElemAbelian 3 A := hctx.mem_partTwoE.1
  have hcA : c ∈ A := hctx.zpowers_mem_omegaA.1 (Subgroup.mem_zpowers c)
  have hcE : c ∈ E :=
    mem_of_le_centralizer hst hctx.partTwoS_eq hEE (hA.2 c hcA) hctx.le_centralizer
  have hcL : c ∉ L := hctx.hypS.2.2 c hctx.zpowers_mem_omegaA L hctx.mem_lA
  have hFE : partTwoF G = partTwoE G :=
    (hctx.toTheoremFourHyp.partTwoF_eq_partTwoE hctx.partTwoS_eq).1
  have hD : Sec13Data G A c L := ⟨hst, hctx.partTwoS_eq, hFE ▸ hctx.mem_partTwoE,
    hctx.not_mem_partTwoT, hctx.zpowers_mem_omegaA, hctx.mem_lA⟩
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl)
  obtain ⟨φ⟩ := hM12
  obtain ⟨-, -, -, hsol⟩ := KFacts.ks18M12 _ ⟨φ⟩
  have hθeq := theta_eq_pCore_two_of_solvable hsol
  have hθM : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hθeq).trans φ⟩
  have hE9 := rank3II_19_14E_of_tri htri KFacts.ks18M12 G A c L E M hctx hLM
  have h48 := card_autIn_of_m12 h131 hctx hθM hE9
  have hEB : E = Subgroup.zpowers c ⊔ (E ⊓ L) :=
    Step1914TriProof.eq_zpowers_sup_of_nine_le hE hcE hcL (by rw [hE9])
  have hBne : E ⊓ L ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hE9
    norm_num at hE9
  obtain ⟨⟨X₁, hX₁B⟩, hX₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hX₁1' : X₁ ≠ 1 := fun h1 => hX₁1 (Subtype.ext h1)
  have hX₁3 : X₁ ^ 3 = 1 := hE.1.2 X₁ hX₁B.1
  have hX₁o : orderOf X₁ = 3 := orderOf_eq_prime hX₁3 hX₁1'
  have hnle : ¬ E ⊓ L ≤ Subgroup.zpowers X₁ := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    rw [hE9, Nat.card_zpowers, hX₁o] at h1
    omega
  obtain ⟨X₂, hX₂B, hX₂X₁⟩ := Set.not_subset.mp hnle
  have hX₂3 : X₂ ^ 3 = 1 := hE.1.2 X₂ hX₂B.1
  have hcomm : X₂ * X₁ = X₁ * X₂ :=
    congrArg Subtype.val (hE.1.1.is_comm.comm ⟨X₂, hX₂B.1⟩ ⟨X₁, hX₁B.1⟩)
  have hBX : E ⊓ L = Subgroup.zpowers X₁ ⊔ Subgroup.zpowers X₂ := by
    have hcard := Sec4.card_zpowers_sup_zpowers hX₂3 hX₁o hX₂X₁ hcomm
    exact (Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hX₁B)
      (Subgroup.zpowers_le.mpr hX₂B)) (by rw [hcard, hE9])).symm
  have hbasis : BasisData E (E ⊓ L) c X₁ X₂ :=
    ⟨hE.1, hE.2, hcE, hEB, fun h1 => hcL h1.2, hE9, hX₁1', hBX⟩
  have hLB : ∀ l ∈ L, l ∈ Subgroup.normalizer (E : Set G) →
      l ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) := fun l hl hlE =>
    inf_normalizer_le_normalizer_inf E L ⟨hl, hlE⟩
  obtain ⟨M₁, hM₁L, -, hM₁B, R1, R2⟩ := exists_realize hbasis hLc hLB h48 qOne
  obtain ⟨M₂, hM₂L, -, hM₂B, R3, R4⟩ := exists_realize hbasis hLc hLB h48 qTwo
  obtain ⟨y, hyL, -, hyB, R5, R6⟩ := exists_realize hbasis hLc hLB h48 tOne
  have v0 : (0 : ZMod 3).val = 0 := rfl
  have v1 : (1 : ZMod 3).val = 1 := rfl
  have v2 : (2 : ZMod 3).val = 2 := rfl
  simp only [qOne, qTwo, tOne, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, v0, v1, v2, pow_zero,
    pow_one, one_mul, mul_one] at R1 R2 R3 R4 R5 R6
  have hinv₁ : X₁⁻¹ = X₁ ^ 2 := inv_eq_sq_of_pow_three hX₁3
  have hinv₂ : X₂⁻¹ = X₂ ^ 2 := inv_eq_sq_of_pow_three hX₂3
  have hcore : CoreData E (E ⊓ L) c X₁ X₂ M₁ M₂ := by
    refine ⟨hbasis, hM₁B, hM₂B, hLc M₁ hM₁L, hLc M₂ hM₂L, ?_, R2, ?_, ?_⟩
    · rw [R1, hinv₂]
    · rw [R3, hinv₁, hinv₂]
      exact (Commute.pow_pow (show Commute X₁ X₂ from hcomm.symm) 2 2).eq
    · rw [R4, mul_assoc X₁ X₂ X₁, hcomm, ← mul_assoc, ← sq]
  refine ⟨X₁, X₂, M₁, M₂, hcore, y, hyB, hLc y hyL, ?_, X₂, hX₂B, ?_⟩
  ·
    have hy₁ : ∀ n : ℕ, y ^ n * X₁ * (y ^ n)⁻¹ = X₁ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc y ^ (n + 1) * X₁ * (y ^ (n + 1))⁻¹ = y * (y ^ n * X₁ * (y ^ n)⁻¹) * y⁻¹ := by
              group
          _ = X₁ := by rw [ih, R5]
    have hy₂ : y ^ 3 * X₂ * (y ^ 3)⁻¹ = X₂ := by
      have e1 : ∀ n : ℕ, y ^ n * X₂ * (y ^ n)⁻¹ = X₁ ^ n * X₂ := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          calc y ^ (n + 1) * X₂ * (y ^ (n + 1))⁻¹ = y * (y ^ n * X₂ * (y ^ n)⁻¹) * y⁻¹ := by
                group
            _ = y * (X₁ ^ n * X₂) * y⁻¹ := by rw [ih]
            _ = (y * X₁ * y⁻¹) ^ n * (y * X₂ * y⁻¹) := by rw [conj_pow]; group
            _ = X₁ ^ (n + 1) * X₂ := by rw [R5, R6, pow_succ, mul_assoc]
      rw [e1 3, hX₁3, one_mul]
    have hle : Subgroup.zpowers X₁ ⊔ Subgroup.zpowers X₂ ≤
        Subgroup.centralizer ({y ^ 3} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Sec13.Item138Proof.commute_of_conj_eq (hy₁ 3)).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Sec13.Item138Proof.commute_of_conj_eq hy₂).symm
    intro b hb
    have hyb := Subgroup.mem_centralizer_singleton_iff.mp (hle (hBX.le hb))
    rw [← hyb, mul_inv_cancel_right]
  ·
    rw [R6]
    intro h1
    apply hX₁1'
    calc X₁ = X₁ * X₂ * X₂⁻¹ := by group
      _ = 1 := by rw [h1, mul_inv_cancel]

end CFSG.RankThree.PartTwo.Sec19.Step1914MoreProof
