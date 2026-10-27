module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCKillOrb
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCStmt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBFive
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TC914.Kill

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.NFW CFSG.LocalAnalysis.WeakClosure81.NGW

variable {X : Type} [Group X]

@[expose, reducible] def killCore (Tb A : Subgroup X) : Subgroup X :=
  coreIn (Tb ⊓ centralizer (A : Set X)) Tb

@[expose, reducible] def killP (Lb Tb A : Subgroup X) : Subgroup X := orbJoin Lb (killCore Tb A)

@[expose, reducible] def killS (Lb Tb A : Subgroup X) : Subgroup X :=
  Tb ⊓ normalizer (killP Lb Tb A : Set X)

@[expose, reducible] def killH (Lb Tb A : Subgroup X) : Subgroup X :=
  killP Lb Tb A ⊔ killS Lb Tb A

@[expose, reducible] def killR (Lb Tb A : Subgroup X) : Subgroup X :=
  killS Lb Tb A ⊓ centralizer (killP Lb Tb A : Set X)

variable {Lb Tb A : Subgroup X}

theorem killCore_le_T : killCore Tb A ≤ Tb := coreIn_le_left _ _

theorem conj_eq_of_mem_killCore {d a : X} (hd : d ∈ killCore Tb A) (ha : a ∈ A) :
    d * a * d⁻¹ = a := by
  have h := (mem_centralizer_iff.mp (mem_inf.mp (coreIn_le_right _ _ hd)).2) a ha
  rw [← h, mul_inv_cancel_right]

theorem H_le_normalizer_P : killH Lb Tb A ≤ normalizer (killP Lb Tb A : Set X) :=
  sup_le le_normalizer inf_le_right

theorem core_le_S : killCore Tb A ≤ killS Lb Tb A :=
  le_inf killCore_le_T (le_normalizer_orbJoin_self Lb _)

theorem Lb_le_H : Lb ≤ killH Lb Tb A := (le_orbJoin Lb _).trans le_sup_left

theorem H_le_normalizer_R : killH Lb Tb A ≤ normalizer (killR Lb Tb A : Set X) := by
  refine sup_le ((le_centralizer_iff.mp inf_le_right).trans (centralizer_le_normalizer _)) ?_
  exact fun s hs => mem_normalizer_inf (le_normalizer hs)
    (mem_normalizer_centralizer (mem_inf.mp hs).2)

theorem A_le_S (hA : A ≤ tcT1 Lb Tb) : A ≤ killS Lb Tb A := by
  refine le_inf (hA.trans inf_le_left) (le_normalizer_orbJoin fun d hd a ha => ?_)
  apply mem_normalizer_conjSubgroup
  rw [conj_eq_of_mem_killCore hd ha]
  exact (mem_inf.mp (hA ha)).2

theorem mem_centralizer_P {a : X} (ha : a ∈ A) (haL : a ∈ centralizer (Lb : Set X)) :
    a ∈ centralizer (killP Lb Tb A : Set X) := by
  refine le_centralizer_orbJoin (M := zpowers a) (fun d hd => ?_) (mem_zpowers a)
  rw [zpowers_le, ← E3.conjSubgroup_centralizer, mem_conjSubgroup_iff,
    conj_eq_of_mem_killCore hd ha]
  exact haL

variable [Finite X] {B : Type} [Group B] {π : ↥(tcN1 Lb Tb) →* B} {Es : Subgroup B}
variable (c : TCBar Lb Tb π Es)
include c

theorem isPGroup_center_P :
    IsPGroup 3 ↥(killP Lb Tb A ⊓ centralizer (killP Lb Tb A : Set X)) :=
  isPGroup_center_orbJoin c killCore_le_T

theorem eq_bot_of_le_center {K : Subgroup X} (hK : IsPGroup 2 ↥K)
    (hKZ : K ≤ killP Lb Tb A ⊓ centralizer (killP Lb Tb A : Set X)) : K = ⊥ :=
  eq_bot_of_le_of_isPGroup_three hK (isPGroup_center_P c) hKZ

theorem R_inf_P : killR Lb Tb A ⊓ killP Lb Tb A = ⊥ :=
  eq_bot_of_le_center c (c.sylow.isPGroup.to_le (inf_le_left.trans (inf_le_left.trans
    inf_le_left))) (le_inf inf_le_right (inf_le_left.trans inf_le_right))

theorem isSylowIn_S : IsSylowIn 2 (killS Lb Tb A) (killH Lb Tb A) :=
  isSylowIn_of_le_of_le (c.isSylowIn_inf_normalizer' (base_le_normalizer_orbJoin c killCore_le_T))
    le_sup_right H_le_normalizer_P

theorem isSylowIn_R :
    IsSylowIn 2 (killR Lb Tb A) (killH Lb Tb A ⊓ centralizer (killP Lb Tb A : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : ((killH Lb Tb A ⊓ centralizer (killP Lb Tb A : Set X)).subgroupOf
      (killH Lb Tb A)).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr fun h hh =>
      mem_normalizer_inf (le_normalizer hh) (mem_normalizer_centralizer (H_le_normalizer_P hh))
  have h := (isSylowIn_S (A := A) c).inf_normal inf_le_left hn
  rwa [← inf_assoc, inf_eq_left.mpr (le_sup_right : killS Lb Tb A ≤ killH Lb Tb A)] at h

theorem R_inf_A (hA : A ≤ tcT1 Lb Tb) :
    killR Lb Tb A ⊓ A = pCoreOf 2 (tcN1 Lb Tb) ⊓ A := by
  refine le_antisymm (fun a ha => ?_) fun a ha => ?_
  · have haC : a ∈ centralizer (Lb : Set X) :=
      centralizer_le (SetLike.coe_subset_coe.mpr (le_orbJoin Lb _))
        (mem_inf.mp (mem_inf.mp ha).1).2
    exact mem_inf.mpr ⟨T1_inf_centralizer_le_pCore c (mem_inf.mpr ⟨hA (mem_inf.mp ha).2, haC⟩),
      (mem_inf.mp ha).2⟩
  · obtain ⟨haO, haA⟩ := mem_inf.mp ha
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨A_le_S hA haA,
      mem_centralizer_P haA (c.pCore_le_centralizer haO)⟩, haA⟩

theorem relIndex_R (hA : A ≤ tcT1 Lb Tb) (hA2 : Nat.card (barSub π A) = 2) :
    (killR Lb Tb A).relIndex A = 2 := by
  rw [← inf_relIndex_right, R_inf_A c hA, inf_relIndex_right,
    ← card_barSub c.ker (hA.trans le_sup_right), hA2]

omit [Finite X] in
theorem not_le_centralizer (hA : A ≤ tcT1 Lb Tb) (hA2 : Nat.card (barSub π A) = 2) :
    ¬ A ≤ centralizer (Lb : Set X) := by
  intro hAC
  have hbot := (barSub_eq_bot_iff c.ker (hA.trans le_sup_right)).mpr
    ((le_inf hA hAC).trans (T1_inf_centralizer_le_pCore c))
  rw [hbot, card_bot] at hA2
  exact absurd hA2 (by norm_num)

omit [Finite X] in
theorem P_le_of_normal (hA : A ≤ tcT1 Lb Tb) (hA2 : Nat.card (barSub π A) = 2) {M : Subgroup X}
    (hM : killH Lb Tb A ≤ normalizer (M : Set X)) (hAM : A ≤ M) : killP Lb Tb A ≤ M :=
  orbJoin_le (le_of_not_le_centralizer c.quasi (Lb_le_H.trans hM) hAM (hA.trans inf_le_right)
    (not_le_centralizer c hA hA2)) ((core_le_S.trans le_sup_right).trans hM)

theorem cP {Q : Subgroup X} (hQH : Q ≤ killH Lb Tb A)
    (hQ : killH Lb Tb A ≤ normalizer (Q : Set X)) (h2 : IsPGroup 2 ↥Q) :
    Q ≤ killR Lb Tb A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQS : Q ≤ killS Lb Tb A := (isSylowIn_S (A := A) c).le_of_normal hQH
    ((normal_subgroupOf_iff_le_normalizer hQH).mpr hQ) h2
  have hQP : Q ⊓ killP Lb Tb A = ⊥ := by
    refine eq_bot_of_le_center c (h2.to_le inf_le_left)
      (le_inf inf_le_right (le_centralizer_orbJoin fun d hd => ?_))
    have hconjH : conjSubgroup Lb d ≤ killH Lb Tb A := (conj_le_orbJoin hd).trans le_sup_left
    exact le_centralizer_conj c d
      (inf_le_right.trans (orbJoin_le_normalizer_conj c killCore_le_T (killCore_le_T hd)))
      (fun l hl => mem_normalizer_inf (hQ (hconjH hl)) (H_le_normalizer_P (hconjH hl)))
      (h2.to_le inf_le_left)
  refine le_inf hQS fun q hq => mem_centralizer_iff.mpr fun x hx => ?_
  have hmem : x * q * x⁻¹ * q⁻¹ ∈ Q ⊓ killP Lb Tb A := by
    refine mem_inf.mpr ⟨mul_mem ((mem_normalizer_iff.mp (hQ (mem_sup_left hx)) q).mp hq)
      (inv_mem hq), ?_⟩
    have h1 : q * x⁻¹ * q⁻¹ ∈ killP Lb Tb A :=
      (mem_normalizer_iff.mp (H_le_normalizer_P (hQH hq)) x⁻¹).mp (inv_mem hx)
    simpa [mul_assoc] using mul_mem hx h1
  rw [hQP, mem_bot] at hmem
  calc x * q = (x * q * x⁻¹ * q⁻¹) * (q * x) := by group
    _ = q * x := by rw [hmem, one_mul]

theorem cY (hA : A ≤ tcT1 Lb Tb) (hA2 : Nat.card (barSub π A) = 2) {Y : Subgroup X}
    (hYH : Y ≤ killH Lb Tb A) (hY : killH Lb Tb A ≤ normalizer (Y : Set X))
    (hYA : ∀ y ∈ Y, ∀ a ∈ A, y * a * y⁻¹ * a⁻¹ ∈ killR Lb Tb A) :
    ∀ y ∈ Y, ∃ k : ℕ, y ^ 3 ^ k ∈ killR Lb Tb A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, -, hHM, hmem⟩ := exists_relCent hY H_le_normalizer_R
  have hAM : A ≤ M := fun a ha => (hmem a ((A_le_S hA).trans le_sup_right ha)).mpr fun y hy => by
    have e : a * y * a⁻¹ * y⁻¹ = (y * a * y⁻¹ * a⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem (hYA y hy a ha)
  have hPM := P_le_of_normal c hA hA2 hHM hAM
  have hYC : Y ≤ centralizer (killP Lb Tb A : Set X) := fun y hy =>
    mem_centralizer_iff.mpr fun x hx => by
      have h1 : x * y * x⁻¹ * y⁻¹ ∈ killR Lb Tb A := (hmem x (mem_sup_left hx)).mp (hPM hx) y hy
      have h2 : x * y * x⁻¹ * y⁻¹ ∈ killP Lb Tb A := by
        have := (mem_normalizer_iff.mp (H_le_normalizer_P (hYH hy)) x⁻¹).mp (inv_mem hx)
        simpa [mul_assoc] using mul_mem hx this
      have h3 : x * y * x⁻¹ * y⁻¹ ∈ killR Lb Tb A ⊓ killP Lb Tb A := mem_inf.mpr ⟨h1, h2⟩
      rw [R_inf_P c, mem_bot] at h3
      calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
        _ = y * x := by rw [h3, one_mul]
  intro y hy
  have hyC : y ∈ killH Lb Tb A ⊓ centralizer (killP Lb Tb A : Set X) :=
    mem_inf.mpr ⟨hYH hy, hYC hy⟩
  obtain ⟨j, hj⟩ := exists_pow_two_mem_of_sup H_le_normalizer_P
    (c.sylow.isPGroup.to_le inf_le_left) (hYH hy)
  obtain ⟨k, hk⟩ := isPGroup_center_P (A := A) c ⟨y ^ 2 ^ j, mem_inf.mpr ⟨hj, pow_mem (hYC hy) _⟩⟩
  have hk' : (y ^ 2 ^ j) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k, mem_of_isSylowIn_of_le_normalizer (isSylowIn_R c)
    (inf_le_left.trans H_le_normalizer_R) (pow_mem hyC _) (j := j) ?_⟩
  rw [← pow_mul, mul_comm, pow_mul, hk']

theorem cD [Finite B] (hA : A ≤ tcT1 Lb Tb) (hA2 : Nat.card (barSub π A) = 2) {D : Subgroup X}
    (hD : killH Lb Tb A ≤ normalizer (D : Set X)) (hAD : A ≤ D) : ∃ y ∈ D, orderOf y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 c.facts.three_dvd
  obtain ⟨z, hz, hz3⟩ := exists_orderOf_eq_of_barSub y.2 ((orderOf_coe y).trans hy)
  exact ⟨z, P_le_of_normal c hA hA2 hD hAD (le_orbJoin Lb _ hz), hz3⟩

theorem pair [Finite B] (hA : A ≤ tcT1 Lb Tb) (hA2 : Nat.card (barSub π A) = 2)
    (hpair : ∀ x ∈ barSub π A, x ≠ 1 → PairProp914 (barSub π Lb) x) :
    ∃ n ∈ killH Lb Tb A, IsPGroup 2 ↥(A ⊔ A.map (MulAut.conj n).toMonoidHom) ∧
      ∃ a ∈ A, ∃ b ∈ A, a * (n * b * n⁻¹) ≠ n * b * n⁻¹ * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAN : A ≤ tcN1 Lb Tb := hA.trans le_sup_right
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' 2 (dvd_of_eq hA2.symm)
  obtain ⟨a₀, ha₀, hax⟩ := x₀.2
  have hx2 : orderOf (π a₀) = 2 := by rw [hax, orderOf_coe, hx₀]
  have hxA : π a₀ ∈ barSub π A := ⟨a₀, ha₀, rfl⟩
  have hx1 : π a₀ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  have hAx : barSub π A = zpowers (π a₀) :=
    (eq_of_le_of_card_ge (zpowers_le.mpr hxA) (by rw [Nat.card_zpowers, hx2, hA2])).symm
  obtain ⟨_, ⟨l₀, hl₀, rfl⟩, hP, hnc⟩ := hpair _ hxA hx1
  have hA'N : A.map (MulAut.conj (l₀ : X)).toMonoidHom ≤ tcN1 Lb Tb := by
    rintro _ ⟨a, ha, rfl⟩
    exact mul_mem (mul_mem l₀.2 (hAN ha)) (inv_mem l₀.2)
  have hconj : conjSubgroup A (l₀ : X)⁻¹ = A.map (MulAut.conj (l₀ : X)).toMonoidHom := by
    unfold conjSubgroup
    rw [inv_inv]
  have hle : barSub π (A ⊔ A.map (MulAut.conj (l₀ : X)).toMonoidHom) ≤
      closure {π a₀, π l₀ * π a₀ * (π l₀)⁻¹} := by
    rw [barSub_sup hAN hA'N, ← hconj]
    refine sup_le ?_ ((barSub_conj_le l₀).trans ?_)
    · rw [hAx, zpowers_le]
      exact subset_closure (Set.mem_insert _ _)
    · rw [hAx, MonoidHom.map_zpowers, zpowers_le]
      exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  refine ⟨(l₀ : X), Lb_le_H (mem_subgroupOf.mp hl₀),
    isPGroup_of_barSub c.ker (sup_le hAN hA'N) (hP.to_le hle), a₀, mem_subgroupOf.mp ha₀, a₀,
    mem_subgroupOf.mp ha₀, fun h => hnc ?_⟩
  have h' : a₀ * (l₀ * a₀ * l₀⁻¹) = l₀ * a₀ * l₀⁻¹ * a₀ := Subtype.ext h
  simpa only [map_mul, map_inv] using congrArg π h'

theorem fiveUseC [Finite B] (hA : A ≤ tcT1 Lb Tb) (hA2 : Nat.card (barSub π A) = 2)
    (hpair : ∀ x ∈ barSub π A, x ≠ 1 → PairProp914 (barSub π Lb) x) :
    FiveUseC Tb A (killH Lb Tb A) (killR Lb Tb A) where
  le := (A_le_S hA).trans le_sup_right
  R_le := inf_le_left.trans le_sup_right
  R_norm := H_le_normalizer_R
  R_le_T := inf_le_left.trans inf_le_left
  idx := relIndex_R c hA hA2
  core := core_le_S.trans le_sup_right
  cY := fun _ hYH hY hYA => cY c hA hA2 hYH hY hYA
  cP := fun _ hQH hQ h2 => cP c hQH hQ h2
  cD := fun _ _ hD hAD => cD c hA hA2 hD hAD
  pair := pair c hA hA2 hpair

end CFSG.LocalAnalysis.WeakClosure81.TC914.Kill

namespace CFSG.LocalAnalysis.WeakClosure81

theorem killStmt_holds : KillStmt := by
  intro X _ _ Lb Tb B _ _ π Es c A hA _ hA2 hpair
  exact ⟨_, _, TC914.Kill.fiveUseC c hA hA2 hpair⟩

end CFSG.LocalAnalysis.WeakClosure81
