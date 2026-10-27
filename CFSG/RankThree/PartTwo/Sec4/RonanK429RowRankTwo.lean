module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowSpor
public import CFSG.RankThree.PartTwo.Sec10.Item1015Proof
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofLieP
public import CFSG.RankThree.PartTwo.Sec4.HeringK419UnitaryOdd
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSp
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSL
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2
public import CFSG.Models.PGL

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem autNoE27_of_card_le_nine {X : Type} [Group X]
    (h : ∀ B : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 B → Nat.card B ≤ 9) :
    AutNoE27 X := fun A hA => by
  have := h A hA.1
  rw [hA.2] at this
  omega

theorem autNoE27_of_forall_inner {S : Type} [Group S]
    (hin : ∀ α : MulAut S, α ^ 3 = 1 → α ∈ inner S) (hcen : Subgroup.center S = ⊥)
    (hE : NoE27 S) : AutNoE27 S := by
  intro A hA
  have hAin : A ≤ (MulAut.conj : S →* MulAut S).range := fun a ha => hin a (hA.1.2 a ha)
  have hinj := conj_injective_of_center_eq_bot hcen
  set P := A.comap (MulAut.conj : S →* MulAut S) with hP
  have hmap : P.map (MulAut.conj : S →* MulAut S) = A := Subgroup.map_comap_eq_self hAin
  apply hE P
  refine ⟨⟨⟨⟨fun x y => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩, ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact congrArg Subtype.val (hA.1.1.is_comm.comm ⟨_, x.2⟩ ⟨_, y.2⟩)
  · rw [map_pow, map_one]
    exact hA.1.2 _ hx
  · rw [← hA.2, ← hmap, Subgroup.card_map_of_injective hinj]

theorem mem_inner_of_outerFixedOrderBoundAt {t : StatedLieTag}
    (ht : CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundAt t) {X : Type} [Group X]
    [Finite X] {n ℓ : ℕ} (hadm : StatedLieAdmissible t n ℓ 1) (hX : LieModel X t n ℓ 1)
    (hTits : t ≠ .Tits) (hD4 : t ≠ .trialityD4) (hΩ : t ≠ .POmegaPlus)
    (hdiv : ¬ 3 ∣ lieOrderDivisor t n ℓ) {α : MulAut X} (hα : α ^ 3 = 1) : α ∈ inner X := by
  by_contra hin
  rcases ht X n ℓ 1 hadm hX hTits 3 Nat.prime_three (by norm_num) (by rwa [pow_one])
      (fun h => hΩ h.1) α hα hin with ⟨f₀, hf, -⟩ | ⟨h, -⟩
  · omega
  · exact hD4 h

theorem noE27_of_pRank_quot_le_two {X : Type} [Group X] [Finite X]
    (hcen : Subgroup.center X = ⊥)
    (h : CFSG.pRank 3 (X ⧸ Subgroup.center X) ≤ 2) : NoE27 X :=
  (noE27_of_forall (Item434Spor.noE27_of_pRank_le_two h)).of_mulEquiv (quotCenterEquivOfEqBot hcen)

theorem rowSOf429_two_SL (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (he2 : e ≤ 2) :
    RowSOf429 (projSL 3 (GaloisField p e)) :=
  rowSOf429_of_noCfg fun _ _ _ _ _ ⟨φ⟩ => noCfgS429_of_autNoE27
    ((autNoE27_of_card_le_nine (Sec10.Item1015Proof.card_le_nine_of_mulAut_projSL (by omega) he
      (by omega))).of_mulEquiv φ)

theorem rowSOf429_two_SU (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : 1 ≤ e) (he2 : e ≤ 2) :
    RowSOf429 (projSU 3 p e) := by
  have hq : 2 < p ^ e := by
    calc 2 < p := by omega
      _ ≤ p ^ e := Nat.le_self_pow (by omega) p
  exact rowSOf429_of_noCfg fun _ _ _ _ _ ⟨φ⟩ => noCfgS429_of_autNoE27
    ((autNoE27_of_card_le_nine (Sec10.Item1015Proof.card_le_nine_of_mulAut_projSU (by omega) he hq
      (by omega))).of_mulEquiv φ)

theorem rowSOf429_four_Sp (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    RowSOf429 (projSp 2 (GaloisField p 1)) := by
  refine rowSOf429_of_noCfg fun S _ _ hs hna ⟨φ⟩ => ?_
  have hadm : StatedLieAdmissible .PSp 2 p 1 :=
    ⟨Fact.out, le_rfl, le_rfl, fun h => by simp at h; omega⟩
  haveI : Finite (projSp 2 (GaloisField p 1)) := Finite.of_equiv _ φ.toEquiv
  have hX : LieModel (projSp 2 (GaloisField p 1)) .PSp 2 p 1 :=
    Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSp hadm (MulEquiv.refl _)⟩
  have hcen : Subgroup.center (projSp 2 (GaloisField p 1)) = ⊥ :=
    center_eq_bot_of_mulEquiv φ.symm (center_eq_bot_of_isSimpleGroup hs hna)
  refine noCfgS429_of_autNoE27 ((autNoE27_of_forall_inner (fun α hα =>
    mem_inner_of_outerFixedOrderBoundAt
      CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_PSp hadm hX
      (by decide) (by decide) (by decide) ?_ hα) hcen
    (noE27_of_pRank_quot_le_two hcen (HeringUnitary.pRank_projSp_four_le_two hp))).of_mulEquiv φ)
  intro h3
  have h2 : lieOrderDivisor .PSp 2 p ∣ 2 := Nat.gcd_dvd_left 2 _
  have := (h3.trans h2)
  omega

theorem rowSOf429_four_SL_of_mod_two (p : ℕ) [Fact p.Prime] (hp : 3 < p) (hp3 : p % 3 = 2) :
    RowSOf429 (projSL 4 (GaloisField p 1)) := by
  refine rowSOf429_of_noCfg fun S _ _ hs hna ⟨φ⟩ => ?_
  have hadm : StatedLieAdmissible .PSL 4 p 1 :=
    ⟨Fact.out, le_rfl, by norm_num, fun h => by simp at h, fun h => by simp at h⟩
  haveI : Finite (projSL 4 (GaloisField p 1)) := Finite.of_equiv _ φ.toEquiv
  have hX : LieModel (projSL 4 (GaloisField p 1)) .PSL 4 p 1 :=
    Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm (MulEquiv.refl _)⟩
  have hcen : Subgroup.center (projSL 4 (GaloisField p 1)) = ⊥ :=
    center_eq_bot_of_mulEquiv φ.symm (center_eq_bot_of_isSimpleGroup hs hna)
  refine noCfgS429_of_autNoE27 ((autNoE27_of_forall_inner (fun α hα =>
    mem_inner_of_outerFixedOrderBoundAt
      CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.outerFixedOrderBoundAt_PSL hadm hX
      (by decide) (by decide) (by decide) ?_ hα) hcen
    (noE27_of_pRank_quot_le_two hcen
      (HeringUnitary.pRank_projSL_four_le_two le_rfl (by rw [pow_one]; exact hp3)))).of_mulEquiv φ)
  intro h3
  have h2 : lieOrderDivisor .PSL 4 p ∣ 4 := Nat.gcd_dvd_left 4 _
  have := (h3.trans h2)
  omega

theorem rowSOf429_four_SU_of_mod_one (p : ℕ) [Fact p.Prime] (hp : 3 < p) (hp3 : p % 3 = 1) :
    RowSOf429 (projSU 4 p 1) := by
  refine rowSOf429_of_noCfg fun S _ _ hs hna ⟨φ⟩ => ?_
  have hadm : StatedLieAdmissible .PSU 4 p 1 :=
    ⟨Fact.out, le_rfl, by norm_num, fun h => by simp at h⟩
  haveI : Finite (projSU 4 p 1) := Finite.of_equiv _ φ.toEquiv
  have hX : LieModel (projSU 4 p 1) .PSU 4 p 1 :=
    Or.inl ⟨by decide, CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm (MulEquiv.refl _)⟩
  have hcen : Subgroup.center (projSU 4 p 1) = ⊥ :=
    center_eq_bot_of_mulEquiv φ.symm (center_eq_bot_of_isSimpleGroup hs hna)
  refine noCfgS429_of_autNoE27 ((autNoE27_of_forall_inner (fun α hα =>
    mem_inner_of_outerFixedOrderBoundAt
      CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundAt_PSU hadm hX
      (by decide) (by decide) (by decide) ?_ hα) hcen
    (noE27_of_pRank_quot_le_two hcen
      (HeringUnitary.pRank_projSU_four_le_two (by omega) le_rfl
        (by rw [pow_one]; exact hp3)))).of_mulEquiv φ)
  intro h3
  have h2 : lieOrderDivisor .PSU 4 p ∣ 4 := Nat.gcd_dvd_left 4 _
  have := (h3.trans h2)
  omega

theorem rowSOf429_four_G2 :
    ∀ (p : ℕ) [Fact p.Prime], 3 < p → ∀ q : TauCeti.PrimePower, q.p = p → q.exponent = 1 →
      ∀ hq : (TauCeti.LieTypeIndex.G2 q).Valid,
        RowSOf429 (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group := by
  intro p _ hp3 q hqp hqe hq
  refine rowSOf429_of_noCfg fun S _ _ hs hna ⟨φ⟩ => ?_
  have hM : ChevalleyExceptionalModel S .G2 p 1 := by
    have h := CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv φ
      (Census.chevalleyExceptionalModel_G2_of_odd q hq (by omega))
    rwa [hqp, hqe] at h
  have hX : LieModel S .G2 0 p 1 := Or.inr (Or.inl ⟨rfl, by decide, hM⟩)
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hs hna
  refine noCfgS429_of_autNoE27 (autNoE27_of_forall_inner (fun α hα =>
    mem_inner_of_outerFixedOrderBoundAt
      CFSG.HardMathSupport.Lang.E6Descent.outerFixedOrderBoundAt_G2 hM.1 hX
      (by decide) (by decide) (by decide)
      (by rw [show lieOrderDivisor .G2 0 p = 1 from rfl]; norm_num) hα) hcen
    (noE27_of_forall (Item434Spor.noE27_of_pRank_le_two
      (Res417Four.pRank_g2_le_two hp3 S hM))))

end CFSG.RankThree.PartTwo.Sec4.RonanK429
