module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res12ProofFrame
public import CFSG.RankThree.PartTwo.Sec8.Item812Res11ProofBMemY

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Subgroup

namespace Item812Res12

variable {G : Type} [Group G] [Finite G]

theorem shift_Y {Y : Subgroup G} (hY : Item812Res4.IsYQuot Y)
    {E P S K : Subgroup G} {u t : G} (hPY : P ≤ Y) (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) (hEP : E ≤ P) (hP : IsPGroup 3 P) (htP : t ∈ P) (htE : t ∉ E)
    (hSE : S ≤ E) (hS9 : Nat.card S = 9) (huE : u ∈ E) (huS : u ∉ S)
    (hK : Group.IsPerfect K) (hKY : K ≤ Y) (hSK : S ≤ K) (hKu : K ≤ Subgroup.centralizer {u}) :
    t * u * t⁻¹ ∉ zpowers u ∧ t ^ 2 * u * (t ^ 2)⁻¹ ∉ zpowers u ⊔ zpowers (t * u * t⁻¹) ∧
      ∃ s ∈ S, t * s * t⁻¹ ∉ S := by
  have hEY : E ≤ Y := hEP.trans hPY
  have hSY : S ≤ Y := hSE.trans hEY
  have huY : u ∈ Y := hEY huE
  have htY : t ∈ Y := hPY htP
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hπ
  set u' : Y := ⟨u, huY⟩ with hu'
  set t' : Y := ⟨t, htY⟩ with ht'
  have hP' : IsPGroup 3 (P.subgroupOf Y) := hP.comap_subtype
  have hinj := Item812Res4.injOn_mk_of_isPGroup hP'
  have hEP' : E.subgroupOf Y ≤ P.subgroupOf Y := fun x hx =>
    mem_subgroupOf.mpr (hEP (mem_subgroupOf.mp hx))
  have hSE' : S.subgroupOf Y ≤ E.subgroupOf Y := fun x hx =>
    mem_subgroupOf.mpr (hSE (mem_subgroupOf.mp hx))
  have hu'P : u' ∈ P.subgroupOf Y := mem_subgroupOf.mpr (hEP huE)
  have ht'P : t' ∈ P.subgroupOf Y := mem_subgroupOf.mpr htP
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := hE.2
  have hEbar : CFSG.Assembly.IsElemAbelian 3 (imageModTheta Y E) :=
    Item812Res11.isElemAbelian_map' (Item812Res4.isElemAbelian_subgroupOf Y hE) π
  have hE27' : Nat.card (imageModTheta Y E) = 27 := by
    rw [Item812Res11.card_imageModTheta_of_pow hEY hE3, hE27]
  have htE' : π t' ∉ imageModTheta Y E := by
    rintro ⟨x, hx, hxt⟩
    have h1 := hinj (hEP' hx) ht'P hxt
    apply htE
    rw [show t = (x : G) from congrArg Subtype.val h1.symm]
    exact mem_subgroupOf.mp hx
  have hS9' : Nat.card (imageModTheta Y S) = 9 := by
    rw [Item812Res11.card_imageModTheta_of_pow hSY (fun x hx => hE3 x (hSE hx)), hS9]
  have huS' : π u' ∉ imageModTheta Y S := by
    rintro ⟨x, hx, hxu⟩
    have h1 := hinj (hEP' (hSE' hx)) hu'P hxu
    apply huS
    rw [show u = (x : G) from congrArg Subtype.val h1.symm]
    exact mem_subgroupOf.mp hx
  have hKu' : imageModTheta Y K ≤ centralizer {π u'} := by
    rintro _ ⟨k, hk, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hKu (mem_subgroupOf.mp hk)))
  have hbar := kF812E27PerfShift_holds _ hY _ _ _ _ _ _ hEbar hE27'
    (Item812Res11.imageModTheta_mono hEP) (hP'.map π) (mem_map_of_mem π ht'P) htE'
    (Item812Res11.imageModTheta_mono hSE) hS9' (mem_map_of_mem π (mem_subgroupOf.mpr huE)) huS'
    (Item812Res11.isPerfect_imageModTheta hKY hK) (Item812Res11.imageModTheta_mono hSK) hKu'
  have hYc := shift_pullback π (S := S.subgroupOf Y) (u := u') (t := t') hbar
  have hG := shift_pushforward Y.subtype Y.subtype_injective hYc
  rw [subgroupOf_map_subtype, inf_eq_left.mpr hSY] at hG
  exact hG

theorem factorization_card_Y {Y : Subgroup G} (hY : Item812Res4.IsYQuot Y) :
    (Nat.card Y).factorization 3 = 4 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 Y),
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (Item812Res4.not_dvd_card_core Y), add_zero]
  rcases Item812Res4.card_of_isYGroup hY with h | h <;> rw [h]
  · rw [show (181440 : ℕ) = 3 ^ 4 * 2240 by norm_num,
      Sec4.Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)]
  · rw [show (1451520 : ℕ) = 3 ^ 4 * 17920 by norm_num,
      Sec4.Item434AltPerm.factorization_three_pow_mul 4 (by norm_num)]

theorem exists_central_of_normal {Q N : Subgroup G} (hQ : IsPGroup 3 Q) (hNQ : N ≤ Q)
    (hnorm : ∀ q ∈ Q, ∀ x ∈ N, q * x * q⁻¹ ∈ N) (hN : N ≠ ⊥) :
    ∃ z ∈ N, z ≠ 1 ∧ z ^ 3 = 1 ∧ ∀ q ∈ Q, q * z = z * q := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N' : Subgroup Q := N.subgroupOf Q with hN'
  have hN'n : N'.Normal := ⟨fun x hx q => by
    rw [hN', mem_subgroupOf] at hx ⊢
    simpa using hnorm q q.2 x hx⟩
  have hN'ne : N' ≠ ⊥ := by
    intro h
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hNQ hx⟩ : Q) ∈ N' := mem_subgroupOf.mpr hx
    rw [h, mem_bot] at h1
    rw [mem_bot]
    simpa using congrArg Subtype.val h1
  have := hQ.isNilpotent
  have hT := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'ne
  set T := N' ⊓ center Q with hTdef
  have hTp : IsPGroup 3 T := hQ.to_subgroup T
  obtain ⟨k, hk⟩ := hTp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hT (eq_bot_of_card_eq T (by rw [hk, pow_zero]))
  have h3 : 3 ∣ Nat.card T := by
    rw [hk]
    exact dvd_pow_self 3 hk0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨((z : Q) : G), mem_subgroupOf.mp z.2.1, ?_, ?_, ?_⟩
  · intro h1
    have h2 : z = 1 := Subtype.ext (Subtype.ext h1)
    rw [h2, orderOf_one] at hz
    norm_num at hz
  · have h1 : z ^ 3 = 1 := by
      rw [← hz]
      exact pow_orderOf_eq_one z
    have h2 := congrArg (fun w : T => ((w : Q) : G)) h1
    simpa using h2
  · intro q hq
    have h1 := (mem_center_iff.mp z.2.2) ⟨q, hq⟩
    exact congrArg Subtype.val h1

end Item812Res12

end CFSG.RankThree.PartTwo.Sec8
