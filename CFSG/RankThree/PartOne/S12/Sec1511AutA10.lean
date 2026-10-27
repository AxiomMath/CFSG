module

public import CFSG.RankThree.PartOne.S12.Sec1511AutCore
public import CFSG.RankThree.PartOne.K159.AutA10
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.RankThree.PartOne.CTP.OutEmbed

public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.K159 CFSG.RankThree.PartOne.StrongP

namespace Sec1511

theorem gP_pow_eight : gP ^ 8 = 1 := by decide

theorem uP_card_le : Nat.card uP ≤ 25 := by
  have hsurj : Function.Surjective
      (fun x : Fin 5 × Fin 5 => (⟨pairP x.1 x.2, x.1, x.2, rfl⟩ : uP)) := by
    rintro ⟨_, i, j, rfl⟩
    refine ⟨(⟨i % 5, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    apply Subtype.ext
    show pairP (i % 5) (j % 5) = pairP i j
    unfold pairP
    rw [← pow_eq_pow_mod i aP_pow, ← pow_eq_pow_mod j bP_pow]
  have := Nat.card_le_card_of_surjective _ hsurj
  simpa using this

theorem uP_moves_lt_eight : ∀ k : ℕ, 0 < k → k < 8 → gP ^ k * aP * (gP ^ k)⁻¹ ≠ aP := by
  intro k hk0 hk8
  interval_cases k <;> decide

theorem exactWit_alternating_ten : ExactWit 5 25 8 (alternatingGroup (Fin 10)) := by
  have hUA := uP_le_alternating
  refine ⟨uP.subgroupOf (alternatingGroup (Fin 10)), ⟨gP, gP_mem_alternating⟩, ?_, ?_, ?_,
    by norm_num, ?_, ?_⟩
  · rintro ⟨u, hu⟩ hu'
    apply Subtype.ext
    simpa using uP_exp u (Subgroup.mem_subgroupOf.1 hu')
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUA).toEquiv]
    exact le_antisymm uP_card_le card_uP
  · rintro ⟨u, hu⟩ hu'
    exact Subgroup.mem_subgroupOf.2 (by simpa using uP_normalized u (Subgroup.mem_subgroupOf.1 hu'))
  · intro u _
    have h8 : (⟨gP, gP_mem_alternating⟩ : alternatingGroup (Fin 10)) ^ 8 = 1 :=
      Subtype.ext (by simpa using gP_pow_eight)
    rw [h8]
    simp
  · intro k hk0 hk8
    refine ⟨⟨aP, ?_⟩, ?_, ?_⟩
    · exact (uP_le_alternating ⟨1, 0, by simp [pairP]⟩)
    · exact Subgroup.mem_subgroupOf.2 ⟨1, 0, by simp [pairP]⟩
    · intro h
      apply uP_moves_lt_eight k hk0 hk8
      simpa using congrArg Subtype.val h

theorem a10_row {H : Type} [Group H] [Finite H] {S : Subgroup H} [S.Normal]
    (hC : Subgroup.centralizer (S : Set H) = ⊥) (e : ↥S ≃* alternatingGroup (Fin 10))
    {P : Subgroup H} (hP : IsSylowOf 5 P ⊤) :
    Nat.card (omegaOne 5 P) = 25 ∧
      ∃ g ∈ Subgroup.normalizer ((omegaOne 5 P : Subgroup H) : Set H),
        OrderModC (omegaOne 5 P) g 8 := by
  have hp : Nat.Prime 5 := by norm_num
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 10 (by norm_num)
    (by norm_num)
  have hinj : Function.Injective (MulAut.conjNormal (H := S) : H →* MulAut S) :=
    CTP.conjNormal_injective_of_centralizer S hC
  have h2 : Nat.card H ∣ Nat.card (Equiv.Perm (Fin 10)) := by
    have h1 : Nat.card H ∣ Nat.card (MulAut S) := Subgroup.card_dvd_of_injective _ hinj
    have h3 : Nat.card (MulAut S) = Nat.card (Equiv.Perm (Fin 10)) :=
      (Nat.card_congr (MulAut.congr e).toEquiv).trans
        (Nat.card_congr (MulEquiv.ofBijective _ hbij).toEquiv).symm
    rwa [h3] at h1
  obtain ⟨a, ha⟩ := hP.2.1.exists_card_eq
  have h1 : Nat.card P ∣ Nat.card H := Subgroup.card_subgroup_dvd_card P
  have hfac : Nat.card (Equiv.Perm (Fin 10)) = 3628800 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  have hdvd : 5 ^ a ∣ 3628800 := by
    have := h1.trans h2
    rwa [ha, hfac] at this
  have ha2 : a ≤ 2 := by
    by_contra hcon
    have h125 : 5 ^ 3 ∣ 5 ^ a := pow_dvd_pow 5 (by omega)
    have := h125.trans hdvd
    norm_num at this
  have hPle : Nat.card P ≤ 25 := by
    rw [ha]
    calc 5 ^ a ≤ 5 ^ 2 := Nat.pow_le_pow_right (by norm_num) ha2
      _ = 25 := by norm_num
  have hΩle : Nat.card (omegaOne 5 P) ≤ 25 := by
    refine le_trans ?_ hPle
    exact Subgroup.card_le_of_le ((Subgroup.closure_le _).2 fun x hx => hx.1)
  exact (ExactWit.of_mulEquiv e.symm exactWit_alternating_ten).row hp hP hΩle

end Sec1511

end CFSG.RankThree.PartOne
