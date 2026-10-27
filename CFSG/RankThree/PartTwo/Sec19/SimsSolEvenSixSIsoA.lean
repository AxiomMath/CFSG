module

import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixDefs
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixLen2

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (IsTI WeaklyClosedIn conjSubgroup mem_conjSubgroup)

namespace SixSIsoAAux

open scoped commutatorElement

theorem card_range_heart :
    Nat.card (AddMonoidHom.toMultiplicative (heartToBar (n := 6))).range = 16 := by
  have hinj : Function.Injective (AddMonoidHom.toMultiplicative (heartToBar (n := 6))) :=
    fun _ _ h => heartToBar_injective h
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_congr Multiplicative.toAdd,
    SimsTheoremC.card_altHeart_even (by norm_num) (by decide)]
  norm_num

theorem mul_sq_eq_commutator_mul {G : Type} [Group G] {q a : G} (hq : q * q = 1) :
    (q * a) ^ 2 = ⁅q, a⁆ * a ^ 2 := by
  have hq' : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  rw [commutatorElement_def, hq', sq, sq]
  group

section Cfg

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6}

theorem range_heart_le_piQ (D : C.PiData) :
    (AddMonoidHom.toMultiplicative (heartToBar (n := 6))).range ≤
      ((CFSG.Open.pCoreOf 2 M).subgroupOf (CFSG.Open.pCoreOf 2 M)).map D.piQ := by
  rintro _ ⟨a, rfl⟩
  exact D.heart_mem_piQ_Q (Multiplicative.toAdd a)

theorem card_Q_eq_card_R_mul (D : C.PiData) :
    Nat.card ↥(CFSG.Open.pCoreOf 2 M) = Nat.card ↥(Rc X) *
      Nat.card ↥(((CFSG.Open.pCoreOf 2 M).subgroupOf (CFSG.Open.pCoreOf 2 M)).map D.piQ) := by
  have h := D.card_eq_card_inf_R_mul (le_refl (CFSG.Open.pCoreOf 2 M))
  have hRQ : CFSG.Open.pCoreOf 2 M ⊓ Rc X = Rc X := inf_eq_right.2 (by
    rw [C.S.R_eq_inf]
    exact inf_le_left)
  rw [hRQ] at h
  exact h

theorem psiA_le_M (ψ : Equiv.Perm (Fin 6) →* ↥M) :
    (alternatingGroup (Fin 6)).map (M.subtype.comp ψ) ≤ M := by
  rintro _ ⟨σ, -, rfl⟩
  exact (ψ σ).2

theorem mem_Q_iff (hR : Nat.card ↥(Rc X) ≤ 2) (m : ↥M) :
    (m : G) ∈ CFSG.Open.pCoreOf 2 M ↔ C.θ m = 1 := by
  rw [← MonoidHom.mem_ker, C.theta_ker_eq hR, Subgroup.mem_subgroupOf]

theorem psiA_le_X (hR : Nat.card ↥(Rc X) ≤ 2) (hQX : CFSG.Open.pCoreOf 2 M ≤ X)
    {ψ : Equiv.Perm (Fin 6) →* ↥M} (hψ : ∀ σ, C.θ (ψ σ) = σ) :
    (alternatingGroup (Fin 6)).map (M.subtype.comp ψ) ≤ X := by
  rintro _ ⟨σ, hσ, rfl⟩
  obtain ⟨x, hx⟩ := C.exists_lift hσ
  have h1 : ((ψ σ * ⟨(x : G), C.S.le x.2⟩⁻¹ : ↥M) : G) ∈ CFSG.Open.pCoreOf 2 M := by
    rw [mem_Q_iff hR, map_mul, map_inv, hψ, hx, mul_inv_cancel]
  have h2 := X.mul_mem (hQX h1) x.2
  simpa using h2

theorem exists_mul_psiA (hR : Nat.card ↥(Rc X) ≤ 2) {ψ : Equiv.Perm (Fin 6) →* ↥M}
    (hψ : ∀ σ, C.θ (ψ σ) = σ) (x : ↥X) :
    ∃ q ∈ CFSG.Open.pCoreOf 2 M, ∃ a ∈ (alternatingGroup (Fin 6)).map (M.subtype.comp ψ),
      (x : G) = q * a := by
  set σ := C.θ ⟨(x : G), C.S.le x.2⟩ with hσ
  have hσA : σ ∈ alternatingGroup (Fin 6) := by
    rw [hσ, C.θ_X x]
    exact (C.α x).2
  refine ⟨(x : G) * (ψ σ : G)⁻¹, ?_, (ψ σ : G), ⟨σ, hσA, rfl⟩, by group⟩
  have h : ((⟨(x : G), C.S.le x.2⟩ * (ψ σ)⁻¹ : ↥M) : G) ∈ CFSG.Open.pCoreOf 2 M := by
    rw [mem_Q_iff hR, map_mul, map_inv, hψ, ← hσ, mul_inv_cancel]
  simpa using h

theorem X_le_commutator_sup (hR : Nat.card ↥(Rc X) ≤ 2)
    (hel : ∀ q ∈ CFSG.Open.pCoreOf 2 M, q * q = 1) {ψ : Equiv.Perm (Fin 6) →* ↥M}
    (hψ : ∀ σ, C.θ (ψ σ) = σ) :
    X ≤ ⁅CFSG.Open.pCoreOf 2 M, (alternatingGroup (Fin 6)).map (M.subtype.comp ψ)⁆ ⊔
      (alternatingGroup (Fin 6)).map (M.subtype.comp ψ) := by
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M
  set A : Subgroup G := (alternatingGroup (Fin 6)).map (M.subtype.comp ψ)
  have hQn : Q ≤ Subgroup.normalizer ((⁅Q, A⁆ ⊔ A : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro q hq t ht
    have hle : ⁅Q, A⁆ ⊔ A ≤ (⁅Q, A⁆ ⊔ A).comap (MulAut.conj q).toMonoidHom := by
      refine sup_le (fun w hw => ?_) (fun a ha => ?_)
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_left
          (Subgroup.le_normalizer_iff.1 (Subgroup.normalizer_commutator_ge_left Q A) q hq w hw)
      · rw [Subgroup.mem_comap]
        have h : (MulAut.conj q).toMonoidHom a = ⁅q, a⁆ * a := by
          simp [commutatorElement_def, MulAut.conj_apply]
        rw [h]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hq ha))
          (Subgroup.mem_sup_right ha)
    exact hle ht
  have hAn : A ≤ Subgroup.normalizer ((⁅Q, A⁆ ⊔ A : Subgroup G) : Set G) :=
    (le_inf (Subgroup.normalizer_commutator_ge_right Q A) Subgroup.le_normalizer).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hXn : X ≤ Subgroup.normalizer ((⁅Q, A⁆ ⊔ A : Subgroup G) : Set G) := by
    intro x hx
    obtain ⟨q, hq, a, ha, hxqa⟩ := exists_mul_psiA hR hψ ⟨x, hx⟩
    rw [show x = q * a from hxqa]
    exact Subgroup.mul_mem _ (hQn hq) (hAn ha)
  haveI : ((⁅Q, A⁆ ⊔ A).subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXn
  have h2 : IsPGroup 2 (↥X ⧸ (⁅Q, A⁆ ⊔ A).subgroupOf X) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    obtain ⟨q, hq, a, ha, hxqa⟩ := exists_mul_psiA hR hψ x
    rw [Subgroup.coe_pow, hxqa, mul_sq_eq_commutator_mul (hel q hq)]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hq ha))
      (Subgroup.mem_sup_right (pow_mem ha 2))
  exact Subgroup.subgroupOf_eq_top.1 (C.S.block.1.eq_twoResidual _ h2)

theorem Q_le_commutator (hR : Nat.card ↥(Rc X) ≤ 2)
    (hel : ∀ q ∈ CFSG.Open.pCoreOf 2 M, q * q = 1) (hQX : CFSG.Open.pCoreOf 2 M ≤ X)
    {ψ : Equiv.Perm (Fin 6) →* ↥M} (hψ : ∀ σ, C.θ (ψ σ) = σ) :
    CFSG.Open.pCoreOf 2 M ≤
      ⁅CFSG.Open.pCoreOf 2 M, (alternatingGroup (Fin 6)).map (M.subtype.comp ψ)⁆ := by
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M
  set A : Subgroup G := (alternatingGroup (Fin 6)).map (M.subtype.comp ψ)
  have hAnQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.le_normalizer_iff.2 fun a ha q hq => pCoreOf_normalized M (psiA_le_M ψ ha) hq
  have hWQ : ⁅Q, A⁆ ≤ Q := Subgroup.le_normalizer_iff_commutator_le_left.1 hAnQ
  intro q hq
  have hqWA : q ∈ ⁅Q, A⁆ ⊔ A := X_le_commutator_sup hR hel hψ (hQX hq)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (Subgroup.normalizer_commutator_ge_right Q A)] at hqWA
  obtain ⟨w, hw, a, ha, hwa⟩ := Set.mem_mul.1 hqWA
  have haQ : a ∈ Q := by
    have h : a = w⁻¹ * q := by rw [← hwa]; group
    rw [h]
    exact Q.mul_mem (Q.inv_mem (hWQ hw)) hq
  obtain ⟨σ, -, rfl⟩ := ha
  have h1 : C.θ (ψ σ) = 1 := (mem_Q_iff hR (ψ σ)).1 haQ
  rw [hψ] at h1
  subst h1
  rw [← hwa, map_one, mul_one]
  exact hw

end Cfg

end SixSIsoAAux

namespace Cfg.PiData

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6} (D : C.PiData)

include D in
theorem card_Q_ne_sixteen_of_card_Rc (hR2 : Nat.card ↥(Rc X) = 2) :
    Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16 := by
  have h16 := SixSIsoAAux.card_range_heart ▸
    Subgroup.card_le_of_le (SixSIsoAAux.range_heart_le_piQ D)
  have h := SixSIsoAAux.card_Q_eq_card_R_mul D
  rw [hR2] at h
  omega

section Split

variable (hR2 : Nat.card ↥(Rc X) = 2) (hsurj : Function.Surjective C.θ)
  (hel : ∀ q ∈ CFSG.Open.pCoreOf 2 M, q * q = 1) (hQX : CFSG.Open.pCoreOf 2 M ≤ X)
  {ψ : Equiv.Perm (Fin 6) →* ↥M} (hψ : ∀ σ, C.θ (ψ σ) = σ)
include hR2 hsurj hel hQX hψ

include D in
theorem sixIsoA_le_commutator :
    CFSG.Open.pCoreOf 2 M ≤
      ⁅CFSG.Open.pCoreOf 2 M, (alternatingGroup (Fin 6)).map (M.subtype.comp ψ)⁆ :=
  SixSIsoAAux.Q_le_commutator hR2.le hel hQX hψ

include D in
theorem sixIsoA_eq_blockU : CFSG.Open.pCoreOf 2 M = blockU X := by
  refine le_antisymm ?_ C.S.W_le_Q
  have hQY : CFSG.Open.pCoreOf 2 M ≤ CFSG.Open.pCoreOf 2 X :=
    le_pCoreOf_of_normalized hQX (fun k hk _ ha => pCoreOf_normalized M (C.S.le hk) ha)
      (isPGroup_pCoreOf' M)
  refine (sixIsoA_le_commutator D hR2 hsurj hel hQX hψ).trans ?_
  rw [blockU, blockQ]
  exact Subgroup.commutator_mono hQY (SixSIsoAAux.psiA_le_X hR2.le hQX hψ)

end Split

end Cfg.PiData

end CFSG.RankThree.PartTwo.Sec19.SolEven
