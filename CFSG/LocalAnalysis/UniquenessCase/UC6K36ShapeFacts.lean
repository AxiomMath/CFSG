module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Shape
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Lam
import CFSG.LocalAnalysis.UniquenessCase.UC6K36Rank
import CFSG.LieType.Universal.SpecialLinear
import CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
import CFSG.RankThree.PartTwo.KFacts.L34Sylow
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36Stab

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.Open
open CFSG.ASVolI.ChIJK (IsGraphFieldAut F4)
open scoped MatrixGroups

theorem center_eq_bot_of_isSimpleGroup_of_isPerfect {H : Type*} [Group H] [IsSimpleGroup H]
    [Group.IsPerfect H] : center H = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center H) with h | h
  · exact h
  · exfalso
    haveI : IsMulCommutative H := ⟨⟨fun a b => by
      have ha : a ∈ center H := h ▸ Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.1 ha) b).symm⟩⟩
    haveI : Subsingleton H := inferInstance
    exact (not_subsingleton H) inferInstance

theorem card_F4 : Nat.card F4 = 4 := by
  have h := GaloisField.card 2 2 (by norm_num)
  simpa using h

theorem sl3F4_isQuasisimple : CFSG.IsQuasisimple SL(3, F4) :=
  CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F4 le_rfl

theorem sl3F4_isPerfect : Group.IsPerfect SL(3, F4) := sl3F4_isQuasisimple.1

theorem psl3F4_isSimple : IsSimpleGroup PSL(3, F4) := sl3F4_isQuasisimple.2.1

theorem psl3F4_isPerfect : Group.IsPerfect PSL(3, F4) := by
  haveI := sl3F4_isPerfect
  exact (inferInstance : Group.IsPerfect (SL(3, F4) ⧸ center SL(3, F4)))

theorem psl3F4_center : center PSL(3, F4) = ⊥ := by
  haveI := psl3F4_isSimple
  haveI := psl3F4_isPerfect
  exact center_eq_bot_of_isSimpleGroup_of_isPerfect

theorem sl3F4_card_center : Nat.card (center SL(3, F4)) = 3 := by
  rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
  exact CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine.card_scalars card_F4

theorem exists_elemAbelian_nine_psl3F4 :
    ∃ A : Subgroup PSL(3, F4), IsElemAbelian 3 A ∧ Nat.card A = 9 := by
  let e := CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F4
  haveI : CFSG.IsElementaryAbelian 3 ↥(CFSG.RankThree.PartTwo.KFacts.L34.eZero F4) :=
    CFSG.RankThree.PartTwo.KFacts.L34.isElementaryAbelian_eZero card_F4
  refine ⟨(CFSG.RankThree.PartTwo.KFacts.L34.eZero F4).map e.symm.toMonoidHom,
    (isElemAbelian_of_isElementaryAbelian).map _, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective]
  exact CFSG.RankThree.PartTwo.KFacts.L34.card_eZero card_F4

theorem exists_elemAbelian_nine_sl3F4 :
    ∃ A : Subgroup SL(3, F4), IsElemAbelian 3 A ∧ Nat.card A = 9 := by
  open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine in
  have hinj : Function.Injective (dHom (k := F4)) := by
    intro p q h
    have h2 : qElt (p, (0 : Fin 3)) = qElt (q, (0 : Fin 3)) := by
      simpa [qElt] using h
    exact (Prod.ext_iff.1 (qElt_injective h2)).1
  have hcube : ∀ u : F4ˣ, u ^ 3 = 1 := fun u => by
    have := pow_card_eq_one' (G := F4ˣ) (x := u)
    rwa [CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter.card_units_eq_three card_F4] at this
  refine ⟨(CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine.dHom (k := F4)).range,
    ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨p, hp⟩ := a.2
    obtain ⟨q, hq⟩ := b.2
    apply Subtype.ext
    show (a : SL(3, F4)) * b = b * a
    rw [← hp, ← hq, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨p, rfl⟩ := hx
    rw [← map_pow]
    have : p ^ 3 = 1 := Prod.ext (hcube p.1) (hcube p.2)
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod,
      CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter.card_units_eq_three card_F4]

theorem a11_isSimple : IsSimpleGroup (alternatingGroup (Fin 11)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem a11_isPerfect : Group.IsPerfect (alternatingGroup (Fin 11)) :=
  Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))

theorem a11_center : center (alternatingGroup (Fin 11)) = ⊥ := by
  haveI := a11_isSimple
  haveI := a11_isPerfect
  exact center_eq_bot_of_isSimpleGroup_of_isPerfect

private def cyc1 : Equiv.Perm (Fin 11) := Equiv.swap 0 1 * Equiv.swap 1 2

private def cyc2 : Equiv.Perm (Fin 11) := Equiv.swap 3 4 * Equiv.swap 4 5

private theorem cyc1_mem : cyc1 ∈ alternatingGroup (Fin 11) := by
  rw [Equiv.Perm.mem_alternatingGroup, cyc1, map_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  decide

private theorem cyc2_mem : cyc2 ∈ alternatingGroup (Fin 11) := by
  rw [Equiv.Perm.mem_alternatingGroup, cyc2, map_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  decide

theorem a11_exists_elemAbelian_nine :
    ∃ A : Subgroup (alternatingGroup (Fin 11)), IsElemAbelian 3 A ∧ Nat.card A = 9 := by
  set a : alternatingGroup (Fin 11) := ⟨cyc1, cyc1_mem⟩ with ha
  set b : alternatingGroup (Fin 11) := ⟨cyc2, cyc2_mem⟩ with hb
  have ha3 : a ^ 3 = 1 := by
    apply Subtype.ext
    show cyc1 ^ 3 = 1
    decide
  have hb3 : b ^ 3 = 1 := by
    apply Subtype.ext
    show cyc2 ^ 3 = 1
    decide
  have ha1 : a ≠ 1 := fun h => by
    have := congrArg (fun x : alternatingGroup (Fin 11) => (x : Equiv.Perm (Fin 11)) 0) h
    revert this
    decide
  have hb1 : b ≠ 1 := fun h => by
    have := congrArg (fun x : alternatingGroup (Fin 11) => (x : Equiv.Perm (Fin 11)) 3) h
    revert this
    decide
  have hab : Commute a b := by
    apply Subtype.ext
    show cyc1 * cyc2 = cyc2 * cyc1
    decide
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hob : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hcomm : ∀ x ∈ zpowers a, ∀ y ∈ zpowers b, x * y = y * x := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (hab.zpow_zpow i j).eq
  have hmem2 : ∀ y ∈ zpowers b, (y : Equiv.Perm (Fin 11)) 0 = 0 := by
    rintro _ ⟨j, rfl⟩
    have h0 : (cyc2 : Equiv.Perm (Fin 11)) 0 = 0 := by decide
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h0 j
  have hinf : zpowers a ⊓ zpowers b = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨n, hn0⟩, hxb⟩ := hx
    have hn1 : a ^ n = x := hn0
    rw [← hn1] at hxb ⊢
    have h0 := hmem2 _ hxb
    have hn : a ^ n = a ^ (n % (3 : ℤ)) := by
      rw [← zpow_mod_orderOf a n, hoa]
      simp
    have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rw [hn] at h0 ⊢
    rcases hr with hr | hr | hr
    · rw [hr]
      simp
    · rw [hr] at h0
      exact absurd h0 (by decide)
    · rw [hr] at h0
      exact absurd h0 (by decide)
  have hcard := card_sup_mul_card_inf_of_commute hcomm
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hoa, hob] at hcard
  refine ⟨zpowers a ⊔ zpowers b, isElemAbelian_sup_of_commute (isElemAbelian_zpowers ha3)
    (isElemAbelian_zpowers hb3) hcomm, hcard⟩

theorem a11_exists_inner (φ : MulAut (alternatingGroup (Fin 11))) (hφ : φ * φ * φ = 1) :
    ∃ g : alternatingGroup (Fin 11), ∀ x, φ x = g * x * g⁻¹ := by
  obtain ⟨hinj, hsurj⟩ :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 11 (by norm_num) (by norm_num)
  obtain ⟨σ, rfl⟩ := hsurj φ
  have h3 : σ ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one]
    simpa [pow_succ] using hφ
  have hsign : Equiv.Perm.sign σ = 1 := by
    have h := congrArg Equiv.Perm.sign h3
    rw [map_pow, map_one] at h
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
    · exact h1
    · rw [h1] at h
      exact absurd h (by decide)
  refine ⟨⟨σ, Equiv.Perm.mem_alternatingGroup.2 hsign⟩, fun x => ?_⟩
  apply Subtype.ext
  rfl

section Shape

variable {G : Type} [Group G] [Finite G]

theorem rank2Good_of_mulEquiv {K : Subgroup G} {X : Type*} [Group X] (e : ↥K ≃* X)
    (hA : ∃ A : Subgroup X, IsElemAbelian 3 A ∧ Nat.card A = 9) (hZ : Nat.card (center X) ≤ 3) :
    Rank2Good K := by
  obtain ⟨A, hAe, hAc⟩ := hA
  refine ⟨⟨(A.map e.symm.toMonoidHom).map K.subtype, Subgroup.map_subtype_le _,
    (hAe.map _).map _, ?_⟩, ?_⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, hAc]
  · calc Nat.card (center ↥K) = Nat.card ((center ↥K).map e.toMonoidHom) :=
          (Subgroup.card_map_of_injective e.injective).symm
      _ = Nat.card (center X) := by
          rw [show (center ↥K).map e.toMonoidHom = center X from Subgroup.map_center_eq e]
      _ ≤ 3 := hZ

theorem ShapeComp.rank2Good {t : G} {K : Subgroup G} (h : ShapeComp t K) : Rank2Good K := by
  rcases h with ⟨hK | hK, -⟩ | ⟨⟨e⟩, -⟩
  · obtain ⟨e⟩ := hK
    exact rank2Good_of_mulEquiv e exists_elemAbelian_nine_psl3F4 (by rw [psl3F4_center]; simp)
  · obtain ⟨e⟩ := hK
    exact rank2Good_of_mulEquiv e exists_elemAbelian_nine_sl3F4 (by rw [sl3F4_card_center])
  · exact rank2Good_of_mulEquiv e a11_exists_elemAbelian_nine (by rw [a11_center]; simp)

theorem ShapeComp.of_center_ne_bot {t : G} {K : Subgroup G} (h : ShapeComp t K) (hZ : center ↥K ≠ ⊥) :
    Nonempty (↥K ≃* SL(3, F4)) ∧ Nat.card (center ↥K) = 3 ∧ UC6.InducesGraphField t K := by
  have hbot : ∀ {X : Type} [Group X] (e : ↥K ≃* X), center X = ⊥ → center ↥K = ⊥ := by
    intro X _ e hX
    have := Subgroup.map_center_eq e
    rw [hX] at this
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 this
  rcases h with ⟨hK | hK, hgf⟩ | ⟨⟨e⟩, -⟩
  · obtain ⟨e⟩ := hK
    exact absurd (hbot e psl3F4_center) hZ
  · obtain ⟨e⟩ := hK
    refine ⟨⟨e⟩, ?_, hgf⟩
    calc Nat.card (center ↥K) = Nat.card ((center ↥K).map e.toMonoidHom) :=
          (Subgroup.card_map_of_injective e.injective).symm
      _ = Nat.card (center SL(3, F4)) := by
          rw [show (center ↥K).map e.toMonoidHom = center SL(3, F4) from Subgroup.map_center_eq e]
      _ = 3 := sl3F4_card_center
  · exact absurd (hbot e a11_center) hZ

theorem shape_isPerfect {t : G} {L : Subgroup G}
    (h : UC6.GraphFieldShape t L ∨
      (Nonempty (↥L ≃* alternatingGroup (Fin 11)) ∧ UC6.InducesTransposition t L)) :
    Group.IsPerfect L := by
  have hperf : ∀ {X : Type} [Group X] [Group.IsPerfect X] (e : X ≃* ↥L), Group.IsPerfect ↥L :=
    fun {X} _ _ e => Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  rcases h with (⟨hK | hK, -⟩ | ⟨L₁, L₂, hsup, -, ⟨e₁⟩, ⟨e₂⟩, -, -, -⟩) | ⟨⟨e⟩, -⟩
  · obtain ⟨e⟩ := hK
    haveI := psl3F4_isPerfect
    exact hperf e.symm
  · obtain ⟨e⟩ := hK
    haveI := sl3F4_isPerfect
    exact hperf e.symm
  · have h1 : Group.IsPerfect ↥L₁ := by
      haveI := sl3F4_isPerfect
      exact Group.IsPerfect.ofSurjective (f := e₁.symm.toMonoidHom) e₁.symm.surjective
    have h2 : Group.IsPerfect ↥L₂ := by
      haveI := sl3F4_isPerfect
      exact Group.IsPerfect.ofSurjective (f := e₂.symm.toMonoidHom) e₂.symm.surjective
    rw [Subgroup.isPerfect_iff]
    have hp1 : ⁅L₁, L₁⁆ = L₁ := Subgroup.isPerfect_iff.1 h1
    have hp2 : ⁅L₂, L₂⁆ = L₂ := Subgroup.isPerfect_iff.1 h2
    subst hsup
    refine le_antisymm (Subgroup.commutator_le.2 fun x hx y hy => ?_) ?_
    · rw [commutatorElement_def]
      exact (L₁ ⊔ L₂).mul_mem ((L₁ ⊔ L₂).mul_mem ((L₁ ⊔ L₂).mul_mem hx hy) ((L₁ ⊔ L₂).inv_mem hx))
        ((L₁ ⊔ L₂).inv_mem hy)
    · refine sup_le ?_ ?_
      · calc L₁ = ⁅L₁, L₁⁆ := hp1.symm
          _ ≤ ⁅L₁ ⊔ L₂, L₁ ⊔ L₂⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
      · calc L₂ = ⁅L₂, L₂⁆ := hp2.symm
          _ ≤ ⁅L₁ ⊔ L₂, L₁ ⊔ L₂⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
  · haveI := a11_isPerfect
    exact hperf e.symm

theorem conjOn_cube {x : G} {K : Subgroup G} (hx : x ∈ normalizer (K : Set G)) (hx3 : x * x * x = 1)
    (w : ↥K) : UC6.conjOn K hx (UC6.conjOn K hx (UC6.conjOn K hx w)) = w := by
  apply Subtype.ext
  show x * (x * (x * (w : G) * x⁻¹) * x⁻¹) * x⁻¹ = w
  calc x * (x * (x * (w : G) * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * (w : G) * (x * x * x)⁻¹ := by group
    _ = w := by rw [hx3]; group

theorem exists_inner_of_a11 {x : G} {K : Subgroup G} (e : ↥K ≃* alternatingGroup (Fin 11))
    (hx : x ∈ normalizer (K : Set G)) (hx3 : x * x * x = 1) :
    ∃ g ∈ K, ∀ y ∈ K, x * y * x⁻¹ = g * y * g⁻¹ := by
  let ε := UC6.conjOn K hx
  let φ : MulAut (alternatingGroup (Fin 11)) := (e.symm.trans ε).trans e
  have hφ : φ * φ * φ = 1 := by
    refine MulEquiv.ext fun z => ?_
    show e (ε (e.symm (e (ε (e.symm (e (ε (e.symm z)))))))) = z
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, conjOn_cube hx hx3,
      MulEquiv.apply_symm_apply]
  obtain ⟨g', hg'⟩ := a11_exists_inner φ hφ
  refine ⟨(e.symm g' : G), (e.symm g').2, fun y hy => ?_⟩
  have h1 : φ (e ⟨y, hy⟩) = g' * e ⟨y, hy⟩ * g'⁻¹ := hg' _
  have h2 : e (ε ⟨y, hy⟩) = g' * e ⟨y, hy⟩ * g'⁻¹ := by
    rw [← h1]
    show e (ε ⟨y, hy⟩) = e (ε (e.symm (e ⟨y, hy⟩)))
    rw [MulEquiv.symm_apply_apply]
  have h3 : ε ⟨y, hy⟩ = e.symm g' * ⟨y, hy⟩ * (e.symm g')⁻¹ := by
    apply e.injective
    rw [h2, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact congrArg Subtype.val h3

theorem ShapeComp.exists_inner (hOF : L34OuterFree) {t e : G} {K : Subgroup G} (h : ShapeComp t K)
    (ht2 : t * t = 1) (he : e ∈ normalizer (K : Set G)) (he3 : e * e * e = 1) (hte : t * e = e * t)
    (hrest : ∀ k ∈ K, e * k = k * e → t * k = k * t) :
    ∃ g ∈ K, ∀ y ∈ K, e * y * e⁻¹ = g * y * g⁻¹ := by
  rcases h with ⟨hK, ht, hgf⟩ | ⟨⟨eA⟩, -⟩
  · let τ := UC6.conjOn K ht
    let ε := UC6.conjOn K he
    have hττ : τ * τ = 1 := by
      refine MulEquiv.ext fun x => Subtype.ext ?_
      show t * (t * (x : G) * t⁻¹) * t⁻¹ = x
      calc t * (t * (x : G) * t⁻¹) * t⁻¹ = (t * t) * (x : G) * (t * t)⁻¹ := by group
        _ = x := by rw [ht2]; group
    have hεεε : ε * ε * ε = 1 := by
      refine MulEquiv.ext fun x => ?_
      exact conjOn_cube he he3 x
    have hτε : τ * ε = ε * τ := by
      refine MulEquiv.ext fun x => Subtype.ext ?_
      show t * (e * (x : G) * e⁻¹) * t⁻¹ = e * (t * (x : G) * t⁻¹) * e⁻¹
      calc t * (e * (x : G) * e⁻¹) * t⁻¹ = (t * e) * (x : G) * (t * e)⁻¹ := by group
        _ = (e * t) * (x : G) * (e * t)⁻¹ := by rw [hte]
        _ = e * (t * (x : G) * t⁻¹) * e⁻¹ := by group
    have hfix : ∀ k : ↥K, ε k = k → τ k = k := by
      intro k hk
      have h1 : e * (k : G) * e⁻¹ = k := congrArg Subtype.val hk
      have h2 : e * (k : G) = (k : G) * e := by
        calc e * (k : G) = (e * (k : G) * e⁻¹) * e := by group
          _ = (k : G) * e := by rw [h1]
      apply Subtype.ext
      show t * (k : G) * t⁻¹ = k
      have := hrest k k.2 h2
      calc t * (k : G) * t⁻¹ = ((k : G) * t) * t⁻¹ := by rw [this]
        _ = k := by group
    obtain ⟨g, hg⟩ := hOF ↥K hK τ ε hgf hττ hεεε hτε hfix
    exact ⟨g, g.2, fun y hy => congrArg Subtype.val (hg ⟨y, hy⟩)⟩
  · exact exists_inner_of_a11 eA he he3

end Shape

end CFSG.LocalAnalysis.UniquenessCase.UCK
