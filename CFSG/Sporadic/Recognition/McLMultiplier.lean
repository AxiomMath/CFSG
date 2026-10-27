module

public import CFSG.Sporadic.Recognition.McLMultiplierTables
public import CFSG.Sporadic.Recognition.CoverTransfer
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.Sporadic.Recognition.McLMultiplier

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Open CFSG.Sporadic.McL
  CFSG.Sporadic.Recognition.CoverTransfer Subgroup

theorem mclCommW_mem_commutator (i : Fin 6) : mclCommW i ∈ commutator (FreeGroup (Fin 6)) :=
  mk_commWords_mem_commutator _

theorem mclR0_mem : mclR0 ∈ mclRels := by decide

section Multiplier


theorem three_dvd_card_ker (hP : IsPresentation mclGen (wordSet mclRels))
    (hwg : ∀ i, FreeGroup.lift mclGen (mclCommW i) = mclGen i)
    (h3 : 3 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk mclR0) : MclCover)) :
    3 ∣ Nat.card (coverMap hP hwg).ker := by
  have hmem : (PresentedGroup.mk _ (FreeGroup.mk mclR0) : MclCover) ∈ (coverMap hP hwg).ker := by
    rw [MonoidHom.mem_ker, coverMap_mk]
    exact hP.lift_eq_one (List.mem_map_of_mem (f := FreeGroup.mk) mclR0_mem)
  have h2 := orderOf_dvd_natCard (⟨_, hmem⟩ : (coverMap hP hwg).ker)
  rw [← Subgroup.orderOf_coe] at h2
  exact h3.trans h2

theorem card_griessHopfMultiplier_J (hP : IsPresentation mclGen (wordSet mclRels))
    (hwg : ∀ i, FreeGroup.lift mclGen (mclCommW i) = mclGen i)
    (hcard : Finite MclCover ∧ Nat.card MclCover ≤ 2694384000)
    (h3 : 3 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk mclR0) : MclCover)) :
    Nat.card (griessHopfMultiplier J) = 3 := by
  obtain ⟨hfin, hle⟩ := hcard
  have hc := card_presentedCover hP mclCommW_mem_commutator hwg
  rw [card_J] at hc
  have hpos : 0 < Nat.card MclCover := Nat.card_pos
  rw [hc] at hle hpos
  have hM1 : 0 < Nat.card (griessHopfMultiplier J) := Nat.pos_of_mul_pos_left hpos
  have hM2 : Nat.card (griessHopfMultiplier J) ≤ 3 := by omega
  have hdvd : 3 ∣ Nat.card (griessHopfMultiplier J) := by
    rw [Nat.card_congr (griessHopfMultiplierEquivKer hP mclCommW_mem_commutator hwg).toEquiv]
    exact three_dvd_card_ker hP hwg h3
  have := Nat.le_of_dvd hM1 hdvd
  omega

theorem card_griessHopfMultiplier_of_mulEquiv (hP : IsPresentation mclGen (wordSet mclRels))
    (hwg : ∀ i, FreeGroup.lift mclGen (mclCommW i) = mclGen i) {Y : Type} [Group Y]
    (e : Y ≃* J) :
    Nat.card (griessHopfMultiplier Y) = Nat.card (griessHopfMultiplier J) := by
  have hP' := hP.mulEquiv e.symm
  have hwg' : ∀ i, FreeGroup.lift (fun i => e.symm (mclGen i)) (mclCommW i) =
      e.symm (mclGen i) := fun i => by rw [lift_mulEquiv, hwg]
  have hc := card_presentedCover hP' mclCommW_mem_commutator hwg'
  have hc' := card_presentedCover hP mclCommW_mem_commutator hwg
  rw [Nat.card_congr e.toEquiv, hc'] at hc
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos hc).symm

theorem card_griessHopfMultiplier_McL (hP : IsPresentation mclGen (wordSet mclRels))
    (hwg : ∀ i, FreeGroup.lift mclGen (mclCommW i) = mclGen i)
    (hcard : Finite MclCover ∧ Nat.card MclCover ≤ 2694384000)
    (h3 : 3 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk mclR0) : MclCover)) :
    Nat.card (griessHopfMultiplier CFSG.Blueprint.NativeSporadic.McL) = 3 := by
  have h1 : Nat.card (griessHopfMultiplier CFSG.Blueprint.NativeSporadic.McL) =
      Nat.card (griessHopfMultiplier J) :=
    card_griessHopfMultiplier_of_mulEquiv hP hwg mclEquivJ
  rw [h1]
  exact card_griessHopfMultiplier_J hP hwg hcard h3

theorem isCyclic_griessHopfMultiplier_McL (hP : IsPresentation mclGen (wordSet mclRels))
    (hwg : ∀ i, FreeGroup.lift mclGen (mclCommW i) = mclGen i)
    (hcard : Finite MclCover ∧ Nat.card MclCover ≤ 2694384000)
    (h3 : 3 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk mclR0) : MclCover)) :
    IsCyclic (griessHopfMultiplier CFSG.Blueprint.NativeSporadic.McL) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact isCyclic_of_prime_card (card_griessHopfMultiplier_McL hP hwg hcard h3)

theorem card_ker_dvd_three (hP : IsPresentation mclGen (wordSet mclRels))
    (hwg : ∀ i, FreeGroup.lift mclGen (mclCommW i) = mclGen i)
    (hcard : Finite MclCover ∧ Nat.card MclCover ≤ 2694384000)
    (h3 : 3 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk mclR0) : MclCover)) {E : Type} [Group E]
    [Group.IsPerfect E] (q : E →* J) (hq : Function.Surjective q) (hker : q.ker ≤ center E) :
    Nat.card q.ker ∣ 3 := by
  obtain ⟨φ, hφ, hcomp⟩ := exists_surjective_lift hP mclCommW_mem_commutator hwg q hq hker
  have hmap : q.ker = (coverMap hP hwg).ker.map φ := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := hφ x
      refine ⟨y, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, ← hcomp, MonoidHom.comp_apply]
      exact hx
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hy
      rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hcomp]
      exact hy
  have h3' : Nat.card (coverMap hP hwg).ker = 3 := by
    rw [← Nat.card_congr (griessHopfMultiplierEquivKer hP mclCommW_mem_commutator hwg).toEquiv]
    exact card_griessHopfMultiplier_J hP hwg hcard h3
  have hdvd := Subgroup.card_map_dvd (coverMap hP hwg).ker φ
  rw [h3', ← hmap] at hdvd
  exact hdvd

theorem exists_triple_cover (hP : IsPresentation mclGen (wordSet mclRels))
    (hwg : ∀ i, FreeGroup.lift mclGen (mclCommW i) = mclGen i)
    (hcard : Finite MclCover ∧ Nat.card MclCover ≤ 2694384000)
    (h3 : 3 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk mclR0) : MclCover)) :
    ∃ (L : Type) (_ : Group L) (_ : Finite L) (_ : Group.IsPerfect L) (q : L →* J),
      Function.Surjective q ∧ q.ker ≤ center L ∧ Nat.card q.ker = 3 := by
  refine ⟨MclCover, inferInstance, hcard.1, presentedCover_isPerfect mclCommW_mem_commutator,
    coverMap hP hwg, coverMap_surjective hP hwg, coverMap_ker_le_center hP hwg, ?_⟩
  rw [← Nat.card_congr (griessHopfMultiplierEquivKer hP mclCommW_mem_commutator hwg).toEquiv]
  exact card_griessHopfMultiplier_J hP hwg hcard h3

theorem exists_mulEquiv_of_triple_cover (hP : IsPresentation mclGen (wordSet mclRels))
    (hwg : ∀ i, FreeGroup.lift mclGen (mclCommW i) = mclGen i)
    (hcard : Finite MclCover ∧ Nat.card MclCover ≤ 2694384000) {L : Type} [Group L] [Finite L]
    [Group.IsPerfect L] (q : L →* J) (hq : Function.Surjective q) (hker : q.ker ≤ center L)
    (hcardq : Nat.card q.ker = 3) :
    ∃ φ : MclCover ≃* L, q.comp φ.toMonoidHom = coverMap hP hwg := by
  obtain ⟨hfin, hle⟩ := hcard
  have hcardL : Nat.card L = 2694384000 := by
    rw [q.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hq).toEquiv, card_J, hcardq]
  obtain ⟨φ, hφ, hcomp⟩ := exists_bijective_of_card_le hP mclCommW_mem_commutator hwg q hq hker
    (hcardL ▸ hle)
  exact ⟨MulEquiv.ofBijective φ hφ, hcomp⟩

theorem exists_mulEquiv_of_triple_covers (hP : IsPresentation mclGen (wordSet mclRels))
    (hwg : ∀ i, FreeGroup.lift mclGen (mclCommW i) = mclGen i)
    (hcard : Finite MclCover ∧ Nat.card MclCover ≤ 2694384000) {L₁ L₂ : Type} [Group L₁]
    [Group L₂] [Finite L₁] [Finite L₂] [Group.IsPerfect L₁] [Group.IsPerfect L₂] (q₁ : L₁ →* J)
    (q₂ : L₂ →* J) (hq₁ : Function.Surjective q₁) (hq₂ : Function.Surjective q₂)
    (hker₁ : q₁.ker ≤ center L₁) (hker₂ : q₂.ker ≤ center L₂) (hcard₁ : Nat.card q₁.ker = 3)
    (hcard₂ : Nat.card q₂.ker = 3) :
    ∃ ψ : L₁ ≃* L₂, q₂.comp ψ.toMonoidHom = q₁ := by
  obtain ⟨φ₁, h₁'⟩ := exists_mulEquiv_of_triple_cover hP hwg hcard q₁ hq₁ hker₁ hcard₁
  obtain ⟨φ₂, h₂'⟩ := exists_mulEquiv_of_triple_cover hP hwg hcard q₂ hq₂ hker₂ hcard₂
  refine ⟨φ₁.symm.trans φ₂, MonoidHom.ext fun x => ?_⟩
  have e1 := congrArg (fun f : MclCover →* J => f (φ₁.symm x)) h₁'
  have e2 := congrArg (fun f : MclCover →* J => f (φ₁.symm x)) h₂'
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at e1 e2
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply]
  rw [e2, ← e1]

end Multiplier

section Center

variable {S C : Type} [Group S] [Group C]

@[expose] def centerQuotMap (e : C ⧸ Subgroup.center C ≃* S) : C →* S :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center C))

theorem centerQuotMap_surjective (e : C ⧸ Subgroup.center C ≃* S) :
    Function.Surjective (centerQuotMap e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem ker_centerQuotMap (e : C ⧸ Subgroup.center C ≃* S) :
    (centerQuotMap e).ker = Subgroup.center C := by
  ext x
  rw [MonoidHom.mem_ker]
  change e (QuotientGroup.mk' (Subgroup.center C) x) = 1 ↔ _
  rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

end Center

section Multiplier


theorem exists_hom_center {S C : Type} [Group S] [Group C] (f : S ≃* J)
    (e : C ⧸ Subgroup.center C ≃* S) :
    ∃ q : C →* J, Function.Surjective q ∧ q.ker = Subgroup.center C := by
  refine ⟨(f : S →* J).comp (centerQuotMap e), f.surjective.comp (centerQuotMap_surjective e), ?_⟩
  rw [MonoidHom.ker_mulEquiv_comp]
  exact ker_centerQuotMap e

theorem exists_hom_center_McL {C : Type} [Group C]
    (e : C ⧸ Subgroup.center C ≃* CFSG.Blueprint.NativeSporadic.McL) :
    ∃ q : C →* J, Function.Surjective q ∧ q.ker = Subgroup.center C :=
  exists_hom_center (S := CFSG.Blueprint.NativeSporadic.McL) mclEquivJ e

theorem card_center_dvd_three (hP : IsPresentation mclGen (wordSet mclRels))
    (hwg : ∀ i, FreeGroup.lift mclGen (mclCommW i) = mclGen i)
    (hcard : Finite MclCover ∧ Nat.card MclCover ≤ 2694384000)
    (h3 : 3 ∣ orderOf (PresentedGroup.mk _ (FreeGroup.mk mclR0) : MclCover)) {Q : Type} [Group Q]
    (hQ : Group.IsPerfect Q) (e : Q ⧸ Subgroup.center Q ≃* CFSG.Blueprint.NativeSporadic.McL) :
    Nat.card (Subgroup.center Q) ∣ 3 := by
  have := hQ
  obtain ⟨q, hq, hk⟩ := exists_hom_center_McL e
  have hdvd := card_ker_dvd_three hP hwg hcard h3 q hq (le_of_eq hk)
  rwa [hk] at hdvd

theorem nonempty_mulEquiv_of_center_card_three (hP : IsPresentation mclGen (wordSet mclRels))
    (hwg : ∀ i, FreeGroup.lift mclGen (mclCommW i) = mclGen i)
    (hcard : Finite MclCover ∧ Nat.card MclCover ≤ 2694384000) {C₁ C₂ : Type} [Group C₁]
    [Group C₂] [Finite C₁] [Finite C₂] [Group.IsPerfect C₁] [Group.IsPerfect C₂]
    (e₁ : C₁ ⧸ Subgroup.center C₁ ≃* CFSG.Blueprint.NativeSporadic.McL)
    (e₂ : C₂ ⧸ Subgroup.center C₂ ≃* CFSG.Blueprint.NativeSporadic.McL)
    (hc₁ : Nat.card (Subgroup.center C₁) = 3) (hc₂ : Nat.card (Subgroup.center C₂) = 3) :
    Nonempty (C₁ ≃* C₂) := by
  obtain ⟨q₁, hq₁, hk₁⟩ := exists_hom_center_McL e₁
  obtain ⟨q₂, hq₂, hk₂⟩ := exists_hom_center_McL e₂
  have hn₁ : Nat.card q₁.ker = 3 := by rw [hk₁]; exact hc₁
  have hn₂ : Nat.card q₂.ker = 3 := by rw [hk₂]; exact hc₂
  obtain ⟨ψ, -⟩ := exists_mulEquiv_of_triple_covers hP hwg hcard q₁ q₂ hq₁ hq₂
    (le_of_eq hk₁) (le_of_eq hk₂) hn₁ hn₂
  exact ⟨ψ⟩

end Multiplier

end CFSG.Sporadic.Recognition.McLMultiplier
