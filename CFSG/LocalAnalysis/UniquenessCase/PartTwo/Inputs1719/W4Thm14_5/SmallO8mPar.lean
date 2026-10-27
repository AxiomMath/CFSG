module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusData
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bOmega8Minus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllRankThreeBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllResidSL
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapesFail
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllResidMinus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.O8mLine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.LeviTools
import all CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Levi
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreOmegaMinus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.OmegaMinusFourL2
import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Shapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAllShapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Par
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveKNshape
public import CFSG.ClassicalGroups.Orthogonal.BorelSolvableMinus
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3Natural
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneLeviDom

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open scoped Pointwise

namespace SmallO8mPar

theorem subgroupOf_eq_orthParab_of_weyl_nodes {K A : Type} [Field K] [AddCommGroup A]
    [Module K A] [FiniteDimensional K A] {r s : ℕ} {qA : QuadraticForm K A}
    (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0) {d : Fin (s + 1) → ℕ}
    (hd : ∀ j, d j ≤ r)
    {M : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))}
    (hMG : M ≤ orthElementaryGroup (quadTail r qA)) (hBM : tailBorel r qA ≤ M)
    (hW : ∀ i : Fin r, tailWeylElt r qA a₀ i ∈ M ↔ ∀ j, i.val + 1 ≠ d j) :
    M.subgroupOf (orthElementaryGroup (quadTail r qA)) = orthParab r qA d := by
  let E := orthElementaryGroup (quadTail r qA)
  let P := orthParab r qA d
  let N := P.map E.subtype
  have hNE : N ≤ E := Subgroup.map_subtype_le P
  have hBN : tailBorel r qA ≤ N := by
    intro g hg
    refine ⟨⟨g, tailBorel_le hg⟩, mem_orthParab.2 fun j => ?_, rfl⟩
    by_cases h0 : d j = 0
    · simp [h0, tailFlag_zero]
    · exact (mem_tailBorel.1 hg).2 (d j) (by omega) (hd j)
  have hWN : ∀ i : Fin r, tailWeylElt r qA a₀ i ∈ N ↔ ∀ j, i.val + 1 ≠ d j := by
    intro i
    have hmem : tailWeylElt r qA a₀ i ∈ N ↔
        (⟨tailWeylElt r qA a₀ i, tailWeylElt_mem a₀ i⟩ : ↥E) ∈ P := by
      constructor
      · rintro ⟨x, hx, heq⟩
        have heq' : x = (⟨tailWeylElt r qA a₀ i, tailWeylElt_mem a₀ i⟩ : ↥E) :=
          Subtype.ext heq
        exact heq' ▸ hx
      · intro h
        exact ⟨⟨_, tailWeylElt_mem a₀ i⟩, h, rfl⟩
    rw [hmem, mem_orthParab]
    apply forall_congr'
    intro j
    by_cases h0 : d j = 0
    · simp [h0, tailFlag_zero]
    · let k : Fin r := ⟨d j - 1, by have := hd j; omega⟩
      have hk : k.val + 1 = d j := by dsimp [k]; omega
      rw [← hk]
      change (tailWeylElt r qA a₀ i • tailFlag K A r (k.val + 1) =
        tailFlag K A r (k.val + 1)) ↔ i.val + 1 ≠ k.val + 1
      rw [tailWeylElt_smul_tailFlag hani ha₀]
      exact ⟨fun h heq => h (Fin.ext (by omega)), fun h heq => h (by rw [heq])⟩
  have hMN : M = N := by
    rw [tail_eq_closure_of_borel_le hani ha₀ hMG hBM,
      tail_eq_closure_of_borel_le hani ha₀ hNE hBN]
    congr 3
    ext i
    exact (hW i).trans (hWN i).symm
  rw [hMN]
  exact Subgroup.comap_map_eq_self_of_injective E.subtype_injective P

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem nonempty_bar2_hinf_orthParab_of_unit_blocks {r s : ℕ} {d : Fin (s + 1) → ℕ}
    (hrank : 3 ≤ r) (hd : OrthCuts r d) (hlen : ∀ l : Fin s, d l.succ - d l.castSucc = 1)
    (hr : 1 ≤ r - d (Fin.last s)) (hirr : ∀ x : K, x ^ 2 + b * x + c ≠ 0) :
    Nonempty (Bar2 (Hinf (orthParab r (minusTailForm K b c) d)) ≃*
      ↥(StatedOmega (StatedQuadMinus (r - d (Fin.last s) + 1) K b c))) := by
  have : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) := finite_orthLinearEquiv
  let B := orthLeviBlock K r d b c
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE := commutator_orthogonalGroup_quadTail_minus hrank hirr
  have hB : ∀ j, j ≠ Sum.inr () → B j = ⊥ := by
    rintro (l | u) hj
    · change (Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _).range = ⊥
      exact KTabD.range_toGL_eq_bot_of_eq_one (hlen l)
    · exact (hj (congrArg Sum.inr (Subsingleton.elim u ()))).elim
  have hperf : Group.IsPerfect ↥(StatedOmega
      (StatedQuadMinus (r - d (Fin.last s) + 1) K b c)) := by
    obtain ⟨e, he, hK⟩ := NatBorelIrr.exists_card_eq_two_pow_of_charP_two (K := K)
    obtain ⟨hs, hna, -⟩ := orthResDer_facts hK hr hirr
    have := hs
    have := CFSG.Quasithin.F6.isPerfect_of_isSimpleGroup hna
    exact Group.IsPerfect.ofSurjective
      (f := (orthResDerEquivStatedOmega (b := b) (c := c) (r - d (Fin.last s))).toMonoidHom)
      (orthResDerEquivStatedOmega (b := b) (c := c) (r - d (Fin.last s))).surjective
  exact KTabD.nonempty_bar2_hinf_equiv_of_leviHom_mulSingle _
    (orthLeviHom b c hd) (isPGroup_ker_orthLeviHom hd) (Sum.inr ()) B hB
    (fun y hy => ⟨orthLeviResElt b c hd hE ⟨y, hy⟩,
      orthLeviHom_orthLeviResElt hd hE ⟨y, hy⟩⟩)
    (commutator_range_orthLeviHom_le hd)
    (orthResDerEquivStatedOmega (b := b) (c := c) (r - d (Fin.last s))) hperf
    (KOrdNat.pCore_statedOmega_minus_eq_bot 2 (by omega) hirr)

theorem nonempty_bar2_hinf_of_solvable_levi_blocks {G : Type} [Group G] [Finite G]
    {ι : Type} [DecidableEq ι] {A : ι → Type} [∀ j, Group (A j)] (P : Subgroup G)
    (β : ↥P →* ∀ j, A j) (hker : IsPGroup 2 ↥β.ker) (B : ∀ j, Subgroup (A j)) (j₀ : ι)
    (hsolv : ∀ j, j ≠ j₀ → Group.IsSolvable ↥(B j))
    (hSR : ∀ y ∈ B j₀, Pi.mulSingle j₀ y ∈ β.range)
    (hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ B)
    {T : Type} [Group T] (eS : ↥(B j₀) ≃* T) (hperf : Group.IsPerfect T)
    (hT : CFSG.pCore 2 T = ⊥) : Nonempty (Bar2 (Hinf P) ≃* T) := by
  classical
  let D := CFSG.perfectResidual ↥P
  let f : A j₀ →* ∀ j, A j := MonoidHom.mulSingle A j₀
  let S := (B j₀).map f
  let e : ↥S ≃* T := ((B j₀).equivMapOfInjective f (Pi.mulSingle_injective j₀)).symm.trans eS
  have : Group.IsPerfect T := hperf
  have : Group.IsPerfect ↥S := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
    e.symm.surjective
  have hSR' : S ≤ β.range := by
    rintro _ ⟨y, hy, rfl⟩
    exact hSR y hy
  have hDB : D.map β ≤ Subgroup.pi Set.univ B := by
    calc D.map β ≤ (derivedSeries ↥P 1).map β := Subgroup.map_mono (iInf_le _ 1)
      _ = ⁅β.range, β.range⁆ := by
        rw [derivedSeries_one, commutator_def, Subgroup.map_commutator,
          Subgroup.map_top, MonoidHom.range_eq_map]
      _ ≤ Subgroup.pi Set.univ B := hcomm
  have : Group.IsPerfect ↥D := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect
  have : Group.IsPerfect ↥(D.map β) := Group.IsPerfect.map β
  have hDS : D.map β = S := by
    apply le_antisymm
    · rintro a ha
      refine ⟨a j₀, (Subgroup.mem_pi _).mp (hDB ha) j₀ (Set.mem_univ _), ?_⟩
      ext j
      by_cases hj : j = j₀
      · subst j
        change Pi.mulSingle j₀ (a j₀) j₀ = a j₀
        exact Pi.mulSingle_eq_same j₀ (a j₀)
      · let φ : ↥(D.map β) →* ↥(B j) :=
          ((Pi.evalMonoidHom A j).comp (D.map β).subtype).codRestrict (B j)
            fun a => (Subgroup.mem_pi _).mp (hDB a.2) j (Set.mem_univ _)
        have : Group.IsSolvable ↥(B j) := hsolv j hj
        have hφ : φ ⟨a, ha⟩ = 1 :=
          CFSG.QuasithinUnique.Vol2Native.A312L.hom_eq_one_of_perfect_of_solvable
            inferInstance φ ⟨a, ha⟩
        have haj : a j = 1 := congrArg Subtype.val hφ
        change Pi.mulSingle j₀ (a j₀) j = a j
        rw [Pi.mulSingle_eq_of_ne hj, haj]
    · have : Finite ↥β.range :=
        Finite.of_surjective β.rangeRestrict β.rangeRestrict_surjective
      have hm := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq
        β.rangeRestrict β.rangeRestrict_surjective
      have hm' := congrArg (Subgroup.map β.range.subtype) hm
      rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict] at hm'
      change S ≤ (CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥P).map β
      rw [hm']
      exact CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf
        S β.range inferInstance hSR'
  have hO2 : CFSG.pCore 2 ↥S = ⊥ := by
    have h := CFSG.pCore_map_iso 2 e
    rw [hT] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h
  obtain ⟨χ⟩ := KTabD.nonempty_bar2_hinf_equiv_quotient_D1 P β S hDS hker
  exact ⟨χ.trans (((QuotientGroup.quotientMulEquivOfEq hO2).trans
    QuotientGroup.quotientBot).trans e)⟩

theorem nonempty_bar2_hinf_orthParab_minus_two_of_card_two
    (hirr : ∀ x : K, x ^ 2 + b * x + c ≠ 0) (hK : Nat.card K = 2) :
    Nonempty (Bar2 (Hinf (orthParab 3 (minusTailForm K b c) ![0, 2])) ≃*
      ↥(StatedOmega (StatedQuadMinus 2 K b c))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let hd : OrthCuts 3 ![0, 2] := ⟨by decide, rfl, by decide⟩
  let B := orthLeviBlock K 3 ![0, 2] b c
  have hE := commutator_orthogonalGroup_quadTail_minus (le_refl 3) hirr
  have hperf : Group.IsPerfect ↥(StatedOmega (StatedQuadMinus 2 K b c)) :=
    ⟨by rw [commutator_def]; exact NatBorelIrr.commutator_top_statedOmega_quadMinus_two hirr⟩
  refine nonempty_bar2_hinf_of_solvable_levi_blocks _ (orthLeviHom b c hd)
    (isPGroup_ker_orthLeviHom hd) B (Sum.inr ()) ?_
    (fun y hy => ⟨orthLeviResElt b c hd hE ⟨y, hy⟩,
      orthLeviHom_orthLeviResElt hd hE ⟨y, hy⟩⟩)
    (commutator_range_orthLeviHom_le hd) (orthResDerEquivStatedOmega (b := b) (c := c) 1)
    hperf (KOrdNat.pCore_statedOmega_minus_eq_bot 2 le_rfl hirr)
  rintro (l | u) hj
  · have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) := by
      have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
        CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K
          (Or.inl hK)
      exact Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective
    have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin (![0, 2] l.succ -
        ![0, 2] l.castSucc)) K) := by
      have heq : (![0, 2] : Fin 2 → ℕ) l.succ - ![0, 2] l.castSucc = 2 := by
        fin_cases l
        rfl
      rw [heq]
      infer_instance
    exact Group.isSolvable_of_surjective
      (MonoidHom.rangeRestrict_surjective (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (![0, 2] l.succ - ![0, 2] l.castSucc)) K →* _))
  · exact (hj (congrArg Sum.inr (Subsingleton.elim u ()))).elim

theorem nonempty_bar2_hinf_orthParab_of_one_linear_block {s : ℕ} {d : Fin (s + 1) → ℕ}
    (hd : OrthCuts 3 d) (hlast : d (Fin.last s) = 3) (l₀ : Fin s) {m : ℕ}
    (hlen : d l₀.succ - d l₀.castSucc = m)
    (hunit : ∀ l : Fin s, l ≠ l₀ → d l.succ - d l.castSucc = 1)
    (hirr : ∀ x : K, x ^ 2 + b * x + c ≠ 0)
    (hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin m) K)) :
    Nonempty (Bar2 (Hinf (orthParab 3 (minusTailForm K b c) d)) ≃*
      Matrix.SpecialLinearGroup (Fin m) K) := by
  classical
  have hE := commutator_orthogonalGroup_quadTail_minus (le_refl 3) hirr
  let B := orthLeviBlock K 3 d b c
  refine nonempty_bar2_hinf_of_solvable_levi_blocks _ (orthLeviHom b c hd)
    (isPGroup_ker_orthLeviHom hd) B (Sum.inl l₀) ?_ ?_
    (commutator_range_orthLeviHom_le hd)
    ((slEquivToGLRange _).symm.trans
      (MulEquiv.cast (M := fun m => Matrix.SpecialLinearGroup (Fin m) K) hlen))
    hperf (pCore_specialLinearGroup_eq_bot m)
  · rintro (l | u) hj
    · have hb : B (Sum.inl l) = ⊥ :=
        KTabD.range_toGL_eq_bot_of_eq_one (hunit l fun heq => hj (congrArg Sum.inl heq))
      rw [hb]
      infer_instance
    · change Group.IsSolvable ↥(orthResDer K b c (3 - d (Fin.last s)))
      rw [hlast, Nat.sub_self]
      exact isSolvable_orthResDer_zero hirr
  · intro y hy
    exact pi_orthLeviBlock_le_range hd (le_refl 3) hE
      ((Subgroup.mulSingle_mem_pi _ _).mpr fun _ => hy)

theorem nonempty_bar2_hinf_orthParab_minus_two_three
    (hirr : ∀ x : K, x ^ 2 + b * x + c ≠ 0) (hK : 4 ≤ Nat.card K) :
    Nonempty (Bar2 (Hinf (orthParab 3 (minusTailForm K b c) ![0, 2, 3])) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K) := by
  exact nonempty_bar2_hinf_orthParab_of_one_linear_block
    (by constructor <;> decide) rfl 0 rfl (fun l hl => by fin_cases l <;> simp_all)
    hirr (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK)

theorem nonempty_bar2_hinf_orthParab_minus_one_three
    (hirr : ∀ x : K, x ^ 2 + b * x + c ≠ 0) (hK : 4 ≤ Nat.card K) :
    Nonempty (Bar2 (Hinf (orthParab 3 (minusTailForm K b c) ![0, 1, 3])) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K) := by
  exact nonempty_bar2_hinf_orthParab_of_one_linear_block
    (by constructor <;> decide) rfl 1 rfl (fun l hl => by fin_cases l <;> simp_all)
    hirr (CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK)

theorem hinf_orthParab_eq_bot_of_solvable_blocks {r s : ℕ} {d : Fin (s + 1) → ℕ}
    (hd : OrthCuts r d) (hs : ∀ j, Group.IsSolvable ↥(orthLeviBlock K r d b c j)) :
    Hinf (orthParab r (minusTailForm K b c) d) = ⊥ := by
  classical
  let β := orthLeviHom b c hd
  let B := orthLeviBlock K r d b c
  let R := β.range
  have : ∀ j, Group.IsSolvable ↥(B j) := hs
  have : Group.IsSolvable (∀ j, ↥(B j)) := isSolvable_pi hs
  let φ : ↥(Subgroup.pi Set.univ B) →* ∀ j, ↥(B j) :=
    { toFun := fun x j => ⟨(x : ∀ j, orthLeviGroup K r d j) j,
        (Subgroup.mem_pi _).mp x.2 j (Set.mem_univ _)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hφ : Function.Injective φ := fun x y h => Subtype.ext (funext fun j =>
    congrArg Subtype.val (congrFun h j))
  have : Group.IsSolvable ↥(Subgroup.pi Set.univ B) :=
    Group.isSolvable_of_isSolvable_injective hφ
  have hC : (commutator ↥R).map R.subtype ≤ Subgroup.pi Set.univ B := by
    rw [Subgroup.map_subtype_commutator]
    exact commutator_range_orthLeviHom_le hd
  let ψ : ↥(commutator ↥R) →* ↥(Subgroup.pi Set.univ B) :=
    (R.subtype.comp (commutator ↥R).subtype).codRestrict _ fun x => hC ⟨x, x.2, rfl⟩
  have hψ : Function.Injective ψ := by
    intro x y h
    apply (commutator ↥R).subtype_injective
    apply R.subtype_injective
    exact congrArg (fun z : ↥(Subgroup.pi Set.univ B) =>
      (z : ∀ j, orthLeviGroup K r d j)) h
  have : Group.IsSolvable ↥(commutator ↥R) :=
    Group.isSolvable_of_isSolvable_injective hψ
  exact KTabD.hinf_eq_bot_of_leviHom_solvable _ β (isPGroup_ker_orthLeviHom hd)
    ((Group.isSolvable_commutator_iff (G := ↥R)).mp inferInstance)

theorem hinf_orthParab_eq_bot_of_card_two {s : ℕ} {d : Fin (s + 1) → ℕ}
    (hd : OrthCuts 3 d) (hlast : d (Fin.last s) = 3)
    (hlen : ∀ l : Fin s, d l.succ - d l.castSucc ≤ 2)
    (hirr : ∀ x : K, x ^ 2 + b * x + c ≠ 0) (hK : Nat.card K = 2) :
    Hinf (orthParab 3 (minusTailForm K b c) d) = ⊥ := by
  apply hinf_orthParab_eq_bot_of_solvable_blocks hd
  rintro (l | u)
  · have : Group.IsSolvable (Matrix.SpecialLinearGroup
        (Fin (d l.succ - d l.castSucc)) K) :=
      CFSG.QuasithinUnique.Vol2Native.A312L.isSolvable_specialLinear_small hK (hlen l)
    exact Group.isSolvable_of_surjective
      (MonoidHom.rangeRestrict_surjective (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K →* _))
  · change Group.IsSolvable ↥(orthResDer K b c (3 - d (Fin.last s)))
    rw [hlast, Nat.sub_self]
    exact isSolvable_orthResDer_zero hirr

omit [Finite K] in
theorem nonempty_statedProj_equiv_statedOmegaMinus {m : ℕ} (hm : 2 ≤ m) (b c : K) :
    Nonempty (StatedProj (StatedOmega (StatedQuadMinus m K b c)) ≃*
      ↥(StatedOmega (StatedQuadMinus m K b c))) := by
  let Q := CFSG.LieType.Universal.Spin.quadMinus m K b c
  let P := CFSG.ClassicalGroups.Orthogonal.minusPair K b c
    (⟨0, by omega⟩ : Fin (m - 1))
  have hv : ∃ v, Q v ≠ 0 := by
    refine ⟨P.e + P.f, ?_⟩
    rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair P]
    exact one_ne_zero
  have hb := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
    (CFSG.LieType.Universal.Spin.coe_quadMinus m K b c) hv
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot⟩

theorem nParam_eq_or_of_borel_le {G : Type} [Group G] [Finite G] {R : Subgroup G}
    {Q : Subgroup ↥(T3G K b c)}
    (hirr : ∀ x : K, x ^ 2 + b * x + c ≠ 0) {e n : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) (hBQ : t3B K b c ≤ Q) (hQne : Hinf Q ≠ ⊥)
    (hN : NParam R n) (hbar : Bar2 R ≃* Bar2 (Hinf Q)) (_hn : 2 < n) : n = e ∨ n = 2 * e := by
  classical
  have : Finite (T3V K ≃ₗ[K] T3V K) := finite_orthLinearEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M := Q.map (T3G K b c).subtype
  have hME : M ≤ T3G K b c := Subgroup.map_subtype_le Q
  have hMQ : M.subgroupOf (T3G K b c) = Q :=
    Subgroup.comap_map_eq_self_of_injective (T3G K b c).subtype_injective Q
  have hBM : tailBorel 3 (minusTailForm K b c) ≤ M := by
    intro g hg
    exact ⟨⟨g, tailBorel_le hg⟩, hBQ (Subgroup.mem_subgroupOf.mpr hg), rfl⟩
  let w := tailWeylElt 3 (minusTailForm K b c) (t3a0 K)
  have hflag {s : ℕ} (d : Fin (s + 1) → ℕ) (hd : ∀ j, d j ≤ 3)
      (hW : ∀ i : Fin 3, w i ∈ M ↔ ∀ j, i.val + 1 ≠ d j) :
      Q = orthParab 3 (minusTailForm K b c) d := by
    rw [← hMQ]
    exact subgroupOf_eq_orthParab_of_weyl_nodes (t3q_anisotropic hirr)
      (t3a0_ne_zero K) hd hME hBM hW
  have hL2 : ∀ j, IsL2 (Bar2 R) j → n = j := fun j h =>
    kNshape_holds G R n j hN (Or.inl h)
  have hsl2 : ∀ he2 : 2 ≤ e, Bar2 R ≃* Matrix.SpecialLinearGroup (Fin 2) K → n = e :=
    fun he2 χ => hL2 e (KTabD.isL2_of_mulEquiv_sl2 he2 hK χ)
  have hK2 : e = 1 → Nat.card K = 2 := fun h => by rw [hK, h, pow_one]
  have hK4 : 2 ≤ e → 4 ≤ Nat.card K := fun h => by
    rw [hK]
    exact (show 4 = 2 ^ 2 by norm_num).trans_le (Nat.pow_le_pow_right (by norm_num) h)
  by_cases h0 : w 0 ∈ M <;> by_cases h1 : w 1 ∈ M <;> by_cases h2 : w 2 ∈ M
  ·
    have hQtop : Q = ⊤ := by
      have hMtop : M = T3G K b c := by
        have hall : ∀ i : Fin 3, w i ∈ M := by
          intro i
          fin_cases i
          exacts [h0, h1, h2]
        have hgen := tail_eq_closure_of_borel_le (t3q_anisotropic hirr)
          (t3a0_ne_zero K) (M := T3G K b c) le_rfl tailBorel_le
        refine le_antisymm hME ?_
        rw [hgen, Subgroup.closure_le]
        rintro g (hg | ⟨i, hi, rfl⟩)
        · exact hBM hg
        · exact hall i
      rw [← hMQ, hMtop, Subgroup.subgroupOf_self]
    obtain ⟨φ, -⟩ := KAdjE.exists_mulEquiv_omegaMinusQZero hirr
    have hq := CFSG.RankThree.GF2n.Stroth80.statedOmega_minus_quasisimple_of_two_le K
      (m := 4) (by norm_num) hirr
    have := hq.1
    have : Group.IsPerfect ↥(T3G K b c) :=
      Group.IsPerfect.ofSurjective (f := φ.toMonoidHom) φ.surjective
    have hperf : ⁅(⊤ : Subgroup ↥(T3G K b c)), (⊤ : Subgroup ↥(T3G K b c))⁆ =
        (⊤ : Subgroup ↥(T3G K b c)) := by
      exact Group.IsPerfect.commutator_eq_top (G := ↥(T3G K b c))
    have hO2 : CFSG.pCore 2 ↥(T3G K b c) = ⊥ := by
      have h := CFSG.pCore_map_iso 2 φ
      rw [KOrdNat.pCore_statedOmega_minus_eq_bot 2 (by norm_num) hirr,
        Subgroup.map_bot] at h
      exact h.symm
    have hO2Top : CFSG.pCore 2 ↥(⊤ : Subgroup ↥(T3G K b c)) = ⊥ := by
      let eTop : ↥(⊤ : Subgroup ↥(T3G K b c)) ≃* ↥(T3G K b c) := Subgroup.topEquiv
      have h := CFSG.pCore_map_iso 2 eTop
      rw [hO2] at h
      exact (Subgroup.map_eq_bot_iff_of_injective _ eTop.injective).mp h
    obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_eq hQtop hperf hO2Top
    obtain ⟨ε⟩ := nonempty_statedProj_equiv_statedOmegaMinus (by norm_num : 2 ≤ 4) b c
    have hOm : IsOmega8m (Bar2 R) e :=
      Or.inl ⟨by decide, ⟨Nat.prime_two, he, by norm_num⟩, K, inferInstance, inferInstance,
        hK, b, c, hirr, ⟨hbar.trans (χ.trans (Subgroup.topEquiv.trans (φ.symm.trans ε.symm)))⟩⟩
    exact (not_nParam_of_isOmega8m hOm hN).elim
  ·
    have hQ := hflag ![0, 3] (by intro j; fin_cases j <;> decide)
      (by intro i; fin_cases i <;> simp [h0, h1, h2, Fin.forall_fin_two])
    obtain ⟨χ⟩ := nonempty_bar2_hinf_orthParab_minus_three hirr
    rw [← hQ] at χ
    replace χ := hbar.trans χ
    left
    rcases (show e = 1 ∨ 2 ≤ e by omega) with h | h
    · simpa only [h] using nParam_eq_of_isSL3 hN
        (isSL3_of_mulEquiv_sl3_of_card_two (hK2 h) χ)
    · exact nParam_eq_of_mulEquiv_sl3 h hK hN χ
  ·
    have hQ := hflag ![0, 2] (by intro j; fin_cases j <;> decide)
      (by intro i; fin_cases i <;> simp [h0, h1, h2, Fin.forall_fin_two])
    rcases (show e = 1 ∨ 2 ≤ e by omega) with h | h
    · obtain ⟨χ⟩ := nonempty_bar2_hinf_orthParab_minus_two_of_card_two hirr (hK2 h)
      rw [← hQ] at χ
      replace χ := hbar.trans χ
      right
      exact hL2 (2 * e) (CFSG.Blueprint.LieModel.of_mulEquiv χ.symm
        (NatBorelIrr.isL2_statedOmega_quadMinus_two hirr he hK))
    · obtain ⟨χ⟩ := nonempty_bar2_hinf_orthParab_minus_two hirr (hK4 h)
      rw [← hQ] at χ
      replace χ := hbar.trans χ
      exact (not_nParam_of_mulEquiv_sl2_prod_statedOmegaMinus hirr h hK χ hN).elim
  ·
    have hQ := hflag ![0, 2, 3] (by intro j; fin_cases j <;> decide)
      (by intro i; fin_cases i <;> simp [h0, h1, h2, Fin.forall_fin_succ])
    rcases (show e = 1 ∨ 2 ≤ e by omega) with h | h
    · exact (hQne (hQ ▸ hinf_orthParab_eq_bot_of_card_two
        (by constructor <;> decide) rfl (by intro l; fin_cases l <;> decide) hirr (hK2 h))).elim
    · obtain ⟨χ⟩ := nonempty_bar2_hinf_orthParab_minus_two_three hirr (hK4 h)
      rw [← hQ] at χ
      replace χ := hbar.trans χ
      exact Or.inl (hsl2 h χ)
  ·
    have hQ := hflag ![0, 1] (by intro j; fin_cases j <;> decide)
      (by intro i; fin_cases i <;> simp [h0, h1, h2, Fin.forall_fin_two])
    obtain ⟨χ⟩ := nonempty_bar2_hinf_orthParab_of_unit_blocks (le_refl 3)
      (d := ![0, 1]) (by constructor <;> decide) (by intro l; fin_cases l; rfl)
      (by decide) hirr
    rw [← hQ] at χ
    replace χ := hbar.trans χ
    obtain ⟨ε⟩ := nonempty_statedProj_equiv_statedOmegaMinus (by norm_num : 2 ≤ 3) b c
    have hOm : IsOmegaMinus (Bar2 R) 6 e :=
      ⟨⟨3, rfl⟩, K, inferInstance, inferInstance, b, c, hK, hirr, ⟨χ.trans ε.symm⟩⟩
    exact (not_nParam_of_isOmegaMinus_six hOm he hN).elim
  ·
    have hQ := hflag ![0, 1, 3] (by intro j; fin_cases j <;> decide)
      (by intro i; fin_cases i <;> simp [h0, h1, h2, Fin.forall_fin_succ])
    rcases (show e = 1 ∨ 2 ≤ e by omega) with h | h
    · exact (hQne (hQ ▸ hinf_orthParab_eq_bot_of_card_two
        (by constructor <;> decide) rfl (by intro l; fin_cases l <;> decide) hirr (hK2 h))).elim
    · obtain ⟨χ⟩ := nonempty_bar2_hinf_orthParab_minus_one_three hirr (hK4 h)
      rw [← hQ] at χ
      replace χ := hbar.trans χ
      exact Or.inl (hsl2 h χ)
  ·
    have hQ := hflag ![0, 1, 2] (by intro j; fin_cases j <;> decide)
      (by intro i; fin_cases i <;> simp [h0, h1, h2, Fin.forall_fin_succ])
    obtain ⟨χ⟩ := nonempty_bar2_hinf_orthParab_of_unit_blocks (le_refl 3)
      (d := ![0, 1, 2]) (by constructor <;> decide) (by intro l; fin_cases l <;> rfl)
      (by decide) hirr
    rw [← hQ] at χ
    replace χ := hbar.trans χ
    exact Or.inr (hL2 (2 * e) (CFSG.Blueprint.LieModel.of_mulEquiv χ.symm
      (NatBorelIrr.isL2_statedOmega_quadMinus_two hirr he hK)))
  ·
    have hMB : M = tailBorel 3 (minusTailForm K b c) := by
      rw [tail_eq_closure_of_borel_le (t3q_anisotropic hirr) (t3a0_ne_zero K) hME hBM]
      have hset : {i : Fin 3 | w i ∈ M} = ∅ := by
        ext i; fin_cases i <;> simp [h0, h1, h2]
      change Subgroup.closure ((tailBorel 3 (minusTailForm K b c) : Set _) ∪ w ''
        {i : Fin 3 | w i ∈ M}) = _
      rw [hset, Set.image_empty, Set.union_empty, Subgroup.closure_eq]
    have hsolv : Group.IsSolvable ↥Q := by
      have : Group.IsSolvable ↥M := hMB ▸
        CFSG.ClassicalGroups.Orthogonal.isSolvable_borel_orth_minus hirr 3
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Q.equivMapOfInjective (T3G K b c).subtype
          (T3G K b c).subtype_injective).toMonoidHom)
        ((Q.equivMapOfInjective (T3G K b c).subtype
          (T3G K b c).subtype_injective).injective)
    exact (hQne (Hinf_eq_perfectCore Q ▸
      (isSolvable_iff_perfectCore_eq_bot Q).mp hsolv)).elim

end SmallO8mPar

theorem nParam_eq_of_isOmega8m_parabolic {G : Type} [Group G] [Finite G]
    {L P : Subgroup G} {e n : ℕ} (hS : IsOmega8m ↥L e) (hPL : P ≤ L)
    (hpar : IsParabolicTwo ↥L (P.subgroupOf L)) (hinf : Hinf P ≠ ⊥)
    (hN : NParam (Hinf P) n) (hn : 2 < n) : n = e ∨ n = 2 * e := by
  classical
  obtain ⟨hadm, K, hfield, hfinite, hK, b, c, hirr, ⟨φ₀⟩⟩ :=
    hS.statedClassicalModel (by decide)
  let : Field K := hfield
  let : Finite K := hfinite
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨ε⟩ := SmallO8mPar.nonempty_statedProj_equiv_statedOmegaMinus
    (by norm_num : 2 ≤ 4) b c
  obtain ⟨φ₁, -⟩ := KAdjE.exists_mulEquiv_omegaMinusQZero hirr
  let φ : ↥(T3G K b c) ≃* ↥L := (φ₁.symm.trans ε.symm).trans φ₀.symm
  obtain ⟨S, hSN⟩ := IsParabolicTwo.comap φ.toMonoidHom φ.surjective hpar
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(T3G K b c) S (t3Sylow hirr)
  let Q₀ := (P.subgroupOf L).comap φ.toMonoidHom
  let Q := Q₀.map (MulAut.conj g).toMonoidHom
  have heq : (S : Subgroup ↥(T3G K b c)).map (MulAut.conj g).toMonoidHom = t3U K b c := by
    calc (S : Subgroup ↥(T3G K b c)).map (MulAut.conj g).toMonoidHom =
        (t3Sylow hirr : Subgroup ↥(T3G K b c)) := by
          change MulAut.conj g • (S : Subgroup ↥(T3G K b c)) =
            (t3Sylow hirr : Subgroup ↥(T3G K b c))
          rw [← Sylow.coe_subgroup_smul, hg]
      _ = t3U K b c := t3Sylow_coe hirr
  have hBQ : t3B K b c ≤ Q := by
    rw [t3B_eq_normalizer hirr, ← heq, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hSN
  let ψ : ↥(T3G K b c) ≃* ↥L := (MulAut.conj g).symm.trans φ
  have hPQ : P.subgroupOf L = Q.map ψ.toMonoidHom := by
    dsimp only [Q]
    rw [Subgroup.map_map]
    have hid : ψ.toMonoidHom.comp (MulAut.conj g).toMonoidHom = φ.toMonoidHom := by
      ext x
      simp only [ψ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.trans_apply, MulAut.conj_symm_apply, MulAut.conj_apply]
      congr 1
      group
    rw [hid]
    dsimp only [Q₀]
    rw [Subgroup.map_comap_eq_self_of_surjective φ.surjective]
  have hQne : Hinf Q ≠ ⊥ := by
    intro hQ
    apply hinf
    have hPeq : (P.subgroupOf L).map L.subtype = P :=
      Subgroup.map_subgroupOf_eq_of_le hPL
    rw [← hPeq, ← Hinf_map L.subtype, hPQ, Hinf_map_eq_bot ψ Q hQ, Subgroup.map_bot]
  obtain ⟨χ⟩ := nonempty_bar2_hinf_equiv_of_subgroupOf_eq_map hPL ψ hPQ
  exact SmallO8mPar.nParam_eq_or_of_borel_le hirr he hK hBQ hQne hN χ hn

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
