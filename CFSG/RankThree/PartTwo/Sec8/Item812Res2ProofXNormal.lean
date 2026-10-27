module

public import CFSG.RankThree.PartTwo.Sec8.Item812ProofFinal
public import CFSG.RankThree.PartTwo.KFacts.K71Sp48Graph
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.RankThree.PartOne.S10.PlaneAuxiliary

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.Assembly.RankThreeEven (localRank projSp)

namespace Item812Res2

open scoped MatrixGroups

section Unip

variable (F : Type) [Field F]

@[expose] def unipSL : SL(2, F) :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem unipSL_ne_one : unipSL F ≠ 1 := by
  intro h
  have := congrArg (fun B : SL(2, F) => (B : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [unipSL] at this

theorem unipSL_sq [CharP F 2] : unipSL F ^ 2 = 1 := by
  apply Subtype.ext
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  change (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) ^ 2 = 1
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

@[expose] noncomputable def sp4J : StatedSp 2 F := KFacts.planeSp 1 (unipSL F)

theorem sp4J_ne_one : sp4J F ≠ 1 := by
  rw [sp4J, Ne, ← map_one (KFacts.planeSp (F := F) 1), (KFacts.planeSp_injective 1).eq_iff]
  exact unipSL_ne_one F

theorem sp4J_sq [CharP F 2] : sp4J F ^ 2 = 1 := by
  rw [sp4J, ← map_pow, unipSL_sq, map_one]

theorem sp4T_mul_sp4J : KFacts.sp4T F * sp4J F = sp4J F * KFacts.sp4T F :=
  KFacts.planeSp_commute _ _

theorem sp4T'_ne_one : KFacts.sp4T' F ≠ 1 := fun h =>
  KFacts.sp4T'_not_mem_zpowers F (h ▸ Subgroup.one_mem _)

end Unip

section Pure

variable {Q : Type*} [Group Q]

theorem zpowers_mul_comm {M : Type*} [Group M] {g : M} (x y : Subgroup.zpowers g) :
    x * y = y * x := by
  obtain ⟨i, hi⟩ := x.2
  obtain ⟨k, hk⟩ := y.2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [← hi, ← hk]
  exact (Commute.zpow_zpow_self g i k).eq

theorem zpowers_pow_three {M : Type*} [Group M] {g : M} (hg : g ^ 3 = 1)
    (x : Subgroup.zpowers g) : x ^ 3 = 1 := by
  obtain ⟨i, hi⟩ := x.2
  apply Subtype.ext
  simp only [Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← hi]
  dsimp only
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]

theorem eq_one_of_forall_mul_comm {P : Type*} [Group P] (hP : Subgroup.center P = ⊥)
    {K : Subgroup Q} (ψ : P ≃* K) {k : Q} (hk : k ∈ K) (hc : ∀ y ∈ K, k * y = y * k) :
    k = 1 := by
  have hmem : ψ.symm ⟨k, hk⟩ ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (hc _ (ψ y).2).symm
  rw [hP, Subgroup.mem_bot] at hmem
  have h := congrArg (fun x : K => (x : Q)) (ψ.symm.injective (hmem.trans (map_one ψ.symm).symm))
  simpa using h

theorem eq_one_of_mul_central {P : Type*} [Group P] (hP : Subgroup.center P = ⊥)
    {K K' : Subgroup Q} (hKK' : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x) (ψ : P ≃* K) (ψ' : P ≃* K')
    {k k' : Q} (hk : k ∈ K) (hk' : k' ∈ K') (hc : ∀ y : Q, k * k' * y = y * (k * k')) :
    k = 1 ∧ k' = 1 := by
  have h1 : k = 1 := by
    refine eq_one_of_forall_mul_comm hP ψ hk fun y hy => ?_
    have h := hc y
    have hy' : k' * y = y * k' := (hKK' y hy k' hk').symm
    have e : k * k' * y = k * y * k' := by rw [mul_assoc, hy', ← mul_assoc]
    rw [e, ← mul_assoc] at h
    exact mul_right_cancel h
  subst h1
  refine ⟨rfl, eq_one_of_forall_mul_comm hP ψ' hk' fun y hy => ?_⟩
  simpa using hc y

variable [Finite Q] {F : Type} [Field F] [CharP F 2]

theorem four_le_localRank_of_commuting_sp4 {K K' : Subgroup Q}
    (hKK' : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x) (ψ : StatedSp 2 F ≃* K)
    (ψ' : StatedSp 2 F ≃* K') {z : Q} (hz : ∀ y : Q, z * y = y * z) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) : 4 ≤ localRank 3 Q := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : Subgroup.center (StatedSp 2 F) = ⊥ := KFacts.center_statedSp_eq_bot
  set t := KFacts.sp4T F with ht
  set t' := KFacts.sp4T' F with ht'
  have htt' : Commute t t' := KFacts.sp4T_commute F
  have hzc : ∀ w ∈ Subgroup.zpowers z, ∀ y : Q, w * y = y * w := by
    intro w hw y
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact (Commute.zpow_left (hz y) i).eq
  let f₁ : Subgroup.zpowers t →* Q :=
    K.subtype.comp (ψ.toMonoidHom.comp (Subgroup.zpowers t).subtype)
  let f₂ : Subgroup.zpowers t →* Q :=
    K'.subtype.comp (ψ'.toMonoidHom.comp (Subgroup.zpowers t).subtype)
  let f₃ : Subgroup.zpowers t' →* Q :=
    K'.subtype.comp (ψ'.toMonoidHom.comp (Subgroup.zpowers t').subtype)
  let f₄ : Subgroup.zpowers z →* Q := (Subgroup.zpowers z).subtype
  have hf₁ : ∀ m, f₁ m ∈ K := fun m => (ψ m).2
  have hf₂ : ∀ m, f₂ m ∈ K' := fun m => (ψ' m).2
  have hf₃ : ∀ m, f₃ m ∈ K' := fun m => (ψ' m).2
  have h34 : ∀ m n, Commute (f₃ m) (f₄ n) := fun m n => (hzc _ n.2 _).symm
  set f₃₄ := f₃.noncommCoprod f₄ h34 with hf₃₄
  have h234 : ∀ m n, Commute (f₂ m) (f₃₄ n) := by
    intro m n
    rw [hf₃₄, MonoidHom.noncommCoprod_apply]
    refine Commute.mul_right ?_ (hzc _ n.2.2 _).symm
    have hmn : Commute (m : StatedSp 2 F) (n.1 : StatedSp 2 F) := by
      obtain ⟨i, hi⟩ := m.2
      obtain ⟨k, hk⟩ := n.1.2
      rw [← hi, ← hk]
      exact htt'.zpow_zpow i k
    change Commute ((ψ' m : K') : Q) ((ψ' n.1 : K') : Q)
    have h := congrArg (fun x : K' => (x : Q)) (congrArg ψ' hmn.eq)
    simp only [map_mul, Subgroup.coe_mul] at h
    exact h
  set f₂₃₄ := f₂.noncommCoprod f₃₄ h234 with hf₂₃₄
  have h1234 : ∀ m n, Commute (f₁ m) (f₂₃₄ n) := by
    intro m n
    rw [hf₂₃₄, MonoidHom.noncommCoprod_apply, hf₃₄, MonoidHom.noncommCoprod_apply]
    refine Commute.mul_right (hKK' _ (hf₁ m) _ (hf₂ n.1)) (Commute.mul_right
      (hKK' _ (hf₁ m) _ (hf₃ n.2.1)) (hzc _ n.2.2.2 _).symm)
  set Φ := f₁.noncommCoprod f₂₃₄ h1234 with hΦ
  have hΦapply : ∀ x, Φ x = f₁ x.1 * (f₂ x.2.1 * (f₃ x.2.2.1 * f₄ x.2.2.2)) := fun x => rfl
  have hinf : Subgroup.zpowers t ⊓ Subgroup.zpowers t' = ⊥ := by
    have ht'3 : orderOf t' = 3 := orderOf_eq_prime (KFacts.sp4T'_pow_three F) (sp4T'_ne_one F)
    have hcard : Nat.card (Subgroup.zpowers t') = 3 := by rw [Nat.card_zpowers, ht'3]
    have : Fact (Nat.card (Subgroup.zpowers t')).Prime := ⟨by rw [hcard]; exact Nat.prime_three⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card
        ((Subgroup.zpowers t ⊓ Subgroup.zpowers t').subgroupOf (Subgroup.zpowers t')) with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      have h' := disjoint_iff.1 h
      rwa [inf_assoc, inf_idem] at h'
    · exfalso
      have hmem : (⟨t', Subgroup.mem_zpowers t'⟩ : Subgroup.zpowers t') ∈
          (Subgroup.zpowers t ⊓ Subgroup.zpowers t').subgroupOf (Subgroup.zpowers t') := by
        rw [h]
        exact Subgroup.mem_top _
      exact KFacts.sp4T'_not_mem_zpowers F (Subgroup.mem_subgroupOf.1 hmem).1
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [hΦapply] at hx
    have hkk' : f₁ x.1 * (f₂ x.2.1 * f₃ x.2.2.1) = (f₄ x.2.2.2)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← hx]
      group
    have hcen : ∀ y : Q, f₁ x.1 * (f₂ x.2.1 * f₃ x.2.2.1) * y =
        y * (f₁ x.1 * (f₂ x.2.1 * f₃ x.2.2.1)) := fun y => by
      rw [hkk']
      exact hzc _ (Subgroup.inv_mem _ x.2.2.2.2) y
    obtain ⟨hk1, hk'1⟩ := eq_one_of_mul_central hP hKK' ψ ψ' (hf₁ x.1)
      (K'.mul_mem (hf₂ x.2.1) (hf₃ x.2.2.1)) hcen
    have hx1 : x.1 = 1 := by
      have h : ψ (x.1 : StatedSp 2 F) = 1 := Subtype.ext hk1
      rw [map_eq_one_iff _ ψ.injective] at h
      exact Subtype.ext h
    have hx23 : (x.2.1 : StatedSp 2 F) * (x.2.2.1 : StatedSp 2 F) = 1 := by
      have h : ψ' ((x.2.1 : StatedSp 2 F) * (x.2.2.1 : StatedSp 2 F)) = 1 := by
        apply Subtype.ext
        rw [map_mul, Subgroup.coe_mul]
        exact hk'1
      rwa [map_eq_one_iff _ ψ'.injective] at h
    have hmem : (x.2.1 : StatedSp 2 F) ∈ Subgroup.zpowers t ⊓ Subgroup.zpowers t' := by
      refine ⟨x.2.1.2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hx23]
      exact Subgroup.inv_mem _ x.2.2.1.2
    rw [hinf, Subgroup.mem_bot] at hmem
    have hx2 : x.2.1 = 1 := Subtype.ext hmem
    have hx3 : x.2.2.1 = 1 := by
      apply Subtype.ext
      rw [hmem, one_mul] at hx23
      exact hx23
    have hx4 : x.2.2.2 = 1 := by
      have h : f₄ x.2.2.2 = 1 := by
        rw [hk1, hk'1, one_mul] at hkk'
        exact inv_eq_one.mp hkk'.symm
      exact Subtype.ext h
    exact Prod.ext hx1 (Prod.ext hx2 (Prod.ext hx3 hx4))
  set E := Φ.range with hE
  have hMcomm : ∀ x y : Subgroup.zpowers t × Subgroup.zpowers t × Subgroup.zpowers t' ×
      Subgroup.zpowers z, x * y = y * x := fun x y =>
    Prod.ext (zpowers_mul_comm _ _) (Prod.ext (zpowers_mul_comm _ _)
      (Prod.ext (zpowers_mul_comm _ _) (zpowers_mul_comm _ _)))
  have hEab : CFSG.Assembly.IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨x', hx'⟩ := b.2
      simp only [Subgroup.coe_mul]
      rw [← hx, ← hx', ← map_mul, ← map_mul, hMcomm]
    · obtain ⟨x, rfl⟩ := hy
      have ht3 : t ^ 3 = 1 := KFacts.sp4T_pow_three F
      have hx3 : x ^ 3 = 1 := Prod.ext (zpowers_pow_three ht3 _) (Prod.ext
        (zpowers_pow_three ht3 _) (Prod.ext (zpowers_pow_three (KFacts.sp4T'_pow_three F) _)
          (zpowers_pow_three hz3 _)))
      rw [← map_pow, hx3, map_one]
  have hEcard : Nat.card E = 3 ^ 4 := by
    have ht3 : orderOf t = 3 := orderOf_eq_prime (KFacts.sp4T_pow_three F) (KFacts.sp4T_ne_one F)
    have ht'3 : orderOf t' = 3 := orderOf_eq_prime (KFacts.sp4T'_pow_three F) (sp4T'_ne_one F)
    have hz3' : orderOf z = 3 := orderOf_eq_prime hz3 hz1
    rw [hE, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    simp only [Nat.card_prod, Nat.card_zpowers, ht3, ht'3, hz3']
    norm_num
  set jbar : Q := ((ψ (sp4J F) : K) : Q) with hjbar
  have hj2 : orderOf jbar = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hjbar, ← Subgroup.coe_pow, ← map_pow, sp4J_sq, map_one, OneMemClass.coe_one]
    · rw [hjbar, Ne, OneMemClass.coe_eq_one, map_eq_one_iff _ ψ.injective]
      exact sp4J_ne_one F
  have hEj : ∀ y ∈ E, y * jbar = jbar * y := by
    rintro _ ⟨x, rfl⟩
    rw [hΦapply]
    have h1 : f₁ x.1 * jbar = jbar * f₁ x.1 := by
      have hc : Commute (x.1 : StatedSp 2 F) (sp4J F) := by
        obtain ⟨i, hi⟩ := x.1.2
        rw [← hi]
        exact (Commute.zpow_left (sp4T_mul_sp4J F) i)
      have h := congrArg (fun w : K => (w : Q)) (congrArg ψ hc.eq)
      simp only [map_mul, Subgroup.coe_mul] at h
      exact h
    have hjK : jbar ∈ K := (ψ (sp4J F)).2
    have h2 : f₂ x.2.1 * (f₃ x.2.2.1 * f₄ x.2.2.2) * jbar =
        jbar * (f₂ x.2.1 * (f₃ x.2.2.1 * f₄ x.2.2.2)) := by
      have c2 := (hKK' _ hjK _ (hf₂ x.2.1)).symm
      have c3 := (hKK' _ hjK _ (hf₃ x.2.2.1)).symm
      have c4 : f₄ x.2.2.2 * jbar = jbar * f₄ x.2.2.2 := hzc _ x.2.2.2.2 jbar
      calc f₂ x.2.1 * (f₃ x.2.2.1 * f₄ x.2.2.2) * jbar
          = f₂ x.2.1 * (f₃ x.2.2.1 * (f₄ x.2.2.2 * jbar)) := by group
        _ = f₂ x.2.1 * (f₃ x.2.2.1 * (jbar * f₄ x.2.2.2)) := by rw [c4]
        _ = f₂ x.2.1 * ((f₃ x.2.2.1 * jbar) * f₄ x.2.2.2) := by group
        _ = f₂ x.2.1 * ((jbar * f₃ x.2.2.1) * f₄ x.2.2.2) := by rw [c3]
        _ = (f₂ x.2.1 * jbar) * (f₃ x.2.2.1 * f₄ x.2.2.2) := by group
        _ = (jbar * f₂ x.2.1) * (f₃ x.2.2.1 * f₄ x.2.2.2) := by rw [c2]
        _ = jbar * (f₂ x.2.1 * (f₃ x.2.2.1 * f₄ x.2.2.2)) := by group
    calc f₁ x.1 * (f₂ x.2.1 * (f₃ x.2.2.1 * f₄ x.2.2.2)) * jbar
        = f₁ x.1 * (f₂ x.2.1 * (f₃ x.2.2.1 * f₄ x.2.2.2) * jbar) := by group
      _ = f₁ x.1 * (jbar * (f₂ x.2.1 * (f₃ x.2.2.1 * f₄ x.2.2.2))) := by rw [h2]
      _ = (f₁ x.1 * jbar) * (f₂ x.2.1 * (f₃ x.2.2.1 * f₄ x.2.2.2)) := by group
      _ = (jbar * f₁ x.1) * (f₂ x.2.1 * (f₃ x.2.2.1 * f₄ x.2.2.2)) := by rw [h1]
      _ = jbar * (f₁ x.1 * (f₂ x.2.1 * (f₃ x.2.2.1 * f₄ x.2.2.2))) := by group
  have hEN : E ≤ Subgroup.normalizer (Subgroup.zpowers jbar : Set Q) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have hcw : ∀ w' ∈ Subgroup.zpowers jbar, y * w' * y⁻¹ = w' := by
      intro w' hw'
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw'
      rw [(Commute.zpow_right (hEj y hy) i).eq, mul_inv_cancel_right]
    constructor
    · intro hw
      rwa [hcw w hw]
    · intro hw
      have hw' : y⁻¹ * (y * w * y⁻¹) * y⁻¹⁻¹ ∈ Subgroup.zpowers jbar := by
        have hcw' : ∀ w' ∈ Subgroup.zpowers jbar, y⁻¹ * w' * y⁻¹⁻¹ = w' := by
          intro w' hw'
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw'
          have hc : Commute y⁻¹ jbar := (Commute.inv_left (hEj y hy))
          rw [(Commute.zpow_right hc i).eq, inv_inv, inv_mul_cancel_right]
        rw [hcw' _ hw]
        exact hw
      simpa [mul_assoc] using hw'
  have hDcard : Nat.card (Subgroup.zpowers jbar) = 2 := by rw [Nat.card_zpowers, hj2]
  exact CFSG.RankThree.Classical2.le_localRank_of_normalizes Nat.prime_three hEN hEab hEcard
    (by rw [hDcard]; norm_num) (by rw [hDcard])

end Pure

section Main

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def thetaQuotEquiv {X Y : Type*} [Group X] [Group Y] [Finite X]
    (φ : X ≃* Y) :
    X ⧸ aschbacherSolvableCore 3 X ≃* Y ⧸ aschbacherSolvableCore 3 Y :=
  QuotientGroup.congr _ _ φ (aschbacherSolvableCore_map_mulEquiv Nat.prime_three φ)

omit [Finite G] in
theorem mem_normalizer_centralizer_of_mem_normalizer_zpowers {b g : G}
    (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer ({b} : Set G) : Set G) := by
  have key : ∀ x ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G),
      ∀ h ∈ Subgroup.centralizer ({b} : Set G),
        x * h * x⁻¹ ∈ Subgroup.centralizer ({b} : Set G) := by
    intro x hx h hh
    rw [Subgroup.mem_centralizer_singleton_iff] at hh ⊢
    have h1 : x⁻¹ * b * x ∈ Subgroup.zpowers b := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hx) b).mp
        (Subgroup.mem_zpowers b)
      simpa using this
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hc : h * b ^ k = b ^ k * h := (Commute.zpow_right (show Commute h b from hh) k).eq
    calc x * h * x⁻¹ * b = x * (h * (x⁻¹ * b * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * b * x) * h) * x⁻¹ := by rw [← hk, hc]
      _ = b * (x * h * x⁻¹) := by group
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hgh => ?_⟩
  have := key g⁻¹ ((Subgroup.normalizer _).inv_mem hg) _ hgh
  simpa [mul_assoc] using this

theorem normalizer_zpowers_le_normalizer_of_statedSp (h3 : localRank 3 G ≤ 3) {b : G}
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) {X : Subgroup G} (hX : X ∈ thetaComponentsAt 3 b)
    {F : Type} [Field F] [CharP F 2] (e : X ⧸ aschbacherSolvableCore 3 X ≃* StatedSp 2 F) :
    Subgroup.normalizer (Subgroup.zpowers b : Set G) ≤ Subgroup.normalizer (X : Set G) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  intro g hg
  set H := Subgroup.centralizer ({b} : Set G) with hH
  obtain ⟨X₀, hX₀, rfl⟩ := hX
  have hgH : g ∈ Subgroup.normalizer (H : Set G) :=
    mem_normalizer_centralizer_of_mem_normalizer_zpowers hg
  set σ : MulAut H := H.normalizerMonoidHom ⟨g, hgH⟩ with hσ
  set X₀' := X₀.map σ.toMonoidHom with hX₀'
  have hX₀'mem : X₀' ∈ thetaComponents 3 H := map_mulEquiv_mem_thetaComponents hp σ hX₀
  have hconj : (X₀.map H.subtype).map (MulAut.conj g).toMonoidHom = X₀'.map H.subtype := by
    rw [hX₀', Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (X₀.map H.subtype).map (MulAut.conj g).toMonoidHom = X₀.map H.subtype
  rw [hconj]
  by_contra hne
  have hne₀ : X₀' ≠ X₀ := fun h => hne (by rw [h])
  set N := aschbacherSolvableCore 3 H with hN
  obtain ⟨-, -, hN3, -⟩ := solvable_prime_complement_core_characterization (H := H) hp
  set π := QuotientGroup.mk' N with hπ
  have hK := isComponent_map_of_mem_thetaComponents hp hX₀
  have hK' := isComponent_map_of_mem_thetaComponents hp hX₀'mem
  have hKne : X₀.map π ≠ X₀'.map π := fun h =>
    hne₀ ((theta_component_quotient_correspondence (H := H) hp).1.injOn hX₀'mem hX₀ h.symm)
  have hcomm := (CFSG.LocalCores.distinct_components_commute hK hK').resolve_left hKne
  have hKK' : ∀ x ∈ X₀.map π, ∀ y ∈ X₀'.map π, x * y = y * x := by
    intro x hx y hy
    have hxc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx
    exact (Subgroup.mem_centralizer_iff.mp hxc y hy).symm
  obtain ⟨η, -⟩ := exists_thetaQuotient_mulEquiv_map hp hX₀.2.1
  obtain ⟨η', -⟩ := exists_thetaQuotient_mulEquiv_map hp hX₀'mem.2.1
  set ι := X₀.equivMapOfInjective H.subtype H.subtype_injective with hι
  set ι' := X₀.equivMapOfInjective σ.toMonoidHom σ.injective with hι'
  set ψ : StatedSp 2 F ≃* X₀.map π := e.symm.trans ((thetaQuotEquiv ι).symm.trans η) with hψ
  set ψ' : StatedSp 2 F ≃* X₀'.map π :=
    e.symm.trans ((thetaQuotEquiv ι).symm.trans ((thetaQuotEquiv ι').trans η')) with hψ'
  have hbH : b ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set z := π ⟨b, hbH⟩ with hz
  have hzc : ∀ y, z * y = y * z := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      rw [hz, hπ, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm
  have hb3' : (⟨b, hbH⟩ : H) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
  have hz3 : z ^ 3 = 1 := by rw [hz, ← map_pow, hb3', map_one]
  have hz1 : z ≠ 1 := by
    intro h1
    have hmem : (⟨b, hbH⟩ : H) ∈ N := by
      rwa [hz, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hord : orderOf (⟨b, hbH⟩ : H) = 3 :=
      orderOf_eq_prime hb3' (fun h => hb1 (by simpa using congrArg Subtype.val h))
    have hdvd := Subgroup.orderOf_dvd_natCard N hmem
    rw [hord] at hdvd
    exact hN3 hdvd
  have h4 := Item812Res2.four_le_localRank_of_commuting_sp4 hKK' ψ ψ' hzc hz3 hz1
  have h5 := CFSG.RankThree.Classical2.localRank_quotient_le hp (by norm_num) N hN3
  have h6 := CFSG.RankThree.PartOne.PlaneAux.localRank_le_of_injective hp H.subtype
    H.subtype_injective
  omega

omit [Finite G] in
theorem mem_normalizer_zpowers_of_commute {b x : G} (hxb : x * b = b * x) :
    x ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro w
  have hcw : ∀ w' ∈ Subgroup.zpowers b, ∀ y : G, y * b = b * y → y * w' * y⁻¹ = w' := by
    intro w' hw' y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw'
    rw [(Commute.zpow_right (show Commute y b from hy) i).eq, mul_inv_cancel_right]
  constructor
  · intro hw
    rwa [hcw w hw x hxb]
  · intro hw
    have hxb' : x⁻¹ * b = b * x⁻¹ := (Commute.inv_left (show Commute x b from hxb)).eq
    have h' := hcw _ hw x⁻¹ hxb'
    rw [inv_inv] at h'
    rw [show w = x⁻¹ * (x * w * x⁻¹) * x by group, h']
    exact hw

theorem normalizer_zpowers_le_normalizer_of_projSp (h3 : localRank 3 G ≤ 3) {b : G}
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) {X : Subgroup G} (hX : X ∈ thetaComponentsAt 3 b)
    {F : Type} [Field F] [CharP F 2]
    (hXF : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 F)) :
    Subgroup.normalizer (Subgroup.zpowers b : Set G) ≤ Subgroup.normalizer (X : Set G) :=
  normalizer_zpowers_le_normalizer_of_statedSp h3 hb3 hb1 hX
    (hXF.some.trans (KFacts.statedSpEquivProjSpOfCharTwo F).symm)

theorem le_normalizer_of_projSp (h3 : localRank 3 G ≤ 3) {A : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) {b : G} (hbA : b ∈ A) (hb1 : b ≠ 1)
    {X : Subgroup G} (hX : X ∈ thetaComponentsAt 3 b) {F : Type} [Field F] [CharP F 2]
    (hXF : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 F)) :
    A ≤ Subgroup.normalizer (X : Set G) := by
  intro x hx
  refine normalizer_zpowers_le_normalizer_of_projSp h3 (hA.2 b hbA) hb1 hX hXF ?_
  exact mem_normalizer_zpowers_of_commute
    (congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨b, hbA⟩))

end Main

end Item812Res2

section Final


theorem Sec8Pair.normalizer_zpowers_le_normalizer {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ}
    (h : Sec8Pair G A c L a b X n) {F : Type} [Field F] [CharP F 2]
    (hX : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 F)) :
    Subgroup.normalizer (Subgroup.zpowers b : Set G) ≤ Subgroup.normalizer (X : Set G) :=
  Item812Res2.normalizer_zpowers_le_normalizer_of_projSp h.toTheoremFourHyp.localRank_three.le
    (h.mem_partTwoF.1.2 b h.mem_pairOmega.1) h.mem_pairOmega.2.1 h.mem_pairOmega.2.2.1 hX

theorem Sec8Pair.le_normalizer {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G} {X : Subgroup G} {n : ℕ}
    (h : Sec8Pair G A c L a b X n) {F : Type} [Field F] [CharP F 2]
    (hX : Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 F)) :
    A ≤ Subgroup.normalizer (X : Set G) :=
  Item812Res2.le_normalizer_of_projSp h.toTheoremFourHyp.localRank_three.le h.mem_partTwoF.1
    h.mem_pairOmega.1 h.mem_pairOmega.2.1 h.mem_pairOmega.2.2.1 hX

theorem fin812XNormal : Fin812XNormal := by
  intro G _ _ A c L a b X Y n h
  exact h.toSec8Pair.normalizer_zpowers_le_normalizer h.item89_X

end Final

end CFSG.RankThree.PartTwo.Sec8
