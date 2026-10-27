module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo1KQ

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block
open CFSG.KD.Co1K105 (letterOK)
open CFSG.Sporadic.Co1Schreier.Native (Rows)

@[expose] def aC : cA :=
  ⟨aG, Subgroup.mem_inf.2 ⟨iotaA_mem_GA, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩⟩

theorem coe_aC : (aC : GL24) = aG := Subtype.coe_mk _ _


theorem card_zpowers_aC : Nat.card (Subgroup.zpowers aC) = 2 := by
  rw [Nat.card_zpowers, aC, Subgroup.orderOf_mk, orderOf_aG]

@[expose] def conjQ (g : cA) (q : twoAQ) : twoAQ :=
  ⟨(g : GL24) * q * (g : GL24)⁻¹, twoAQ_normal _ g.2 _ q.2⟩

theorem conjQ_one (q : twoAQ) : conjQ 1 q = q :=
  Subtype.ext (by simp [conjQ])

theorem conjQ_mul (g h : cA) (q : twoAQ) : conjQ (g * h) q = conjQ g (conjQ h q) :=
  Subtype.ext (by simp [conjQ, mul_assoc])

theorem exists_centQ_le_two : ∃ T : Subgroup GL24, Nat.card T ≤ 2 ∧
    ∀ g ∈ cA, (∀ q ∈ twoAQ, g * q = q * g) → g ∈ T := by
  obtain ⟨b, hb⟩ := exists_roots qRep_twoA twoA_q_check
  have hT := card_mul_card_towerStab_brayE_le rep_iotaA twoA_cent_check twoA_q_check
    (fun i hi => (hb i hi).2)
  have hE : brayE aG twoAD1 twoABray = GA ⊓ Subgroup.centralizer {aG} := twoAE_eq
  rw [twoA_tower_prod, hE, card_cent_aG] at hT
  exact ⟨towerStab (GA ⊓ Subgroup.centralizer {aG}) b twoARoots.length, by omega,
    fun g hg hq => mem_towerStab_of_lt hg _ fun i hi => hq (b i) (hb i hi).1⟩


@[expose] def qPerm (g : cA) : Equiv.Perm (Fin 512) where
  toFun i := eQ.symm (conjQ g (eQ i))
  invFun i := eQ.symm (conjQ g⁻¹ (eQ i))
  left_inv i := by simp [← conjQ_mul, conjQ_one]
  right_inv i := by simp [← conjQ_mul, conjQ_one]

@[expose] def qHom : cA →* Equiv.Perm (Fin 512) where
  toFun := qPerm
  map_one' := Equiv.ext fun i => by simp [qPerm, conjQ_one]
  map_mul' g h := Equiv.ext fun i => by simp [qPerm, conjQ_mul]

theorem qG_qHom (g : cA) (i : Fin 512) :
    qG (qHom g i) = (g : GL24) * qG i * (g : GL24)⁻¹ :=
  congrArg Subtype.val (eQ.apply_symm_apply (conjQ g (eQ i)))

theorem qHom_apply_eq {g : cA} {i j : Fin 512} (h : (g : GL24) * qG i * (g : GL24)⁻¹ = qG j) :
    qHom g i = j :=
  Fin.ext (qG_inj (qHom g i).2 j.2 ((qG_qHom g i).trans h))

theorem comm_of_qHom_eq_one {g : cA} (h : qHom g = 1) : ∀ q ∈ twoAQ, (g : GL24) * q = q * g := by
  intro q hq
  obtain ⟨i, hi⟩ := eQ.surjective ⟨q, hq⟩
  have hqi : qG i = q := congrArg Subtype.val hi
  have e := qG_qHom g i
  rw [h, Equiv.Perm.one_apply, hqi] at e
  calc (g : GL24) * q = (g : GL24) * q * (g : GL24)⁻¹ * g := by group
    _ = q * g := by rw [← e]

theorem qHom_eq_one_of_comm {g : cA} (h : ∀ j < 8, (g : GL24) * twoAQg j = twoAQg j * g) :
    qHom g = 1 := by
  have hle : twoAQ ≤ Subgroup.centralizer {(g : GL24)} := by
    show Subgroup.closure (twoAQg '' {l | l < twoAQRows.length}) ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [Set.mem_setOf_eq, twoAQRows_length] at hj
    exact Subgroup.mem_centralizer_singleton_iff.2 (h j hj).symm
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.one_apply]
  refine qHom_apply_eq ?_
  have hc := Subgroup.mem_centralizer_singleton_iff.1 (hle (qG_mem i))
  rw [← hc, mul_inv_cancel_right]

theorem qHom_eq_one_of_fix {g : cA}
    (h : ∀ i : Fin 512, (∃ j < 8, (i : ℕ) = 2 ^ j) → qHom g i = i) : qHom g = 1 := by
  refine qHom_eq_one_of_comm fun j hj => ?_
  have hlt : 2 ^ j < 512 := lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hj) (by norm_num)
  have e := qG_qHom g ⟨2 ^ j, hlt⟩
  rw [h ⟨2 ^ j, hlt⟩ ⟨j, hj, rfl⟩] at e
  change qG (2 ^ j) = (g : GL24) * qG (2 ^ j) * (g : GL24)⁻¹ at e
  rw [qG_two_pow hj] at e
  calc (g : GL24) * twoAQg j = (g : GL24) * twoAQg j * (g : GL24)⁻¹ * g := by group
    _ = twoAQg j * g := by rw [← e]

theorem qHom_letter {l : ℕ} {R : Rows} {g : cA} (hR : MRep R g)
    (h : letterOK Native.one qArr CFSG.KD.Co1K105.L l R = true) (i : Fin 512) :
    ((qHom g i : Fin 512) : ℕ) = CFSG.KD.Co1K105.L l i ∧ CFSG.KD.Co1K105.L l i < 512 := by
  simp only [letterOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨hinv, hall⟩ := h
  obtain ⟨hlt, heq⟩ := hall i i.2
  have hq := rep_qG i
  rw [← qArr_get i.2] at hq
  have hq' := rep_qG (CFSG.KD.Co1K105.L l i)
  rw [← qArr_get hlt, ← heq] at hq'
  have e : (g : GL24) * qG i * (g : GL24)⁻¹ = qG (CFSG.KD.Co1K105.L l i) :=
    ((hR.mul hq).mul (hR.inv hinv)).eq hq'
  exact ⟨congrArg Fin.val (qHom_apply_eq (j := ⟨_, hlt⟩) e), hlt⟩

theorem qHom_aC : qHom aC = 1 :=
  qHom_eq_one_of_comm fun _ hj =>
    (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (twoAQ_le
      (twoAQg_mem hj))).2).symm

theorem ker_qHom : qHom.ker = Subgroup.zpowers aC := by
  obtain ⟨T, hT, hmem⟩ := exists_centQ_le_two
  have hinj : Function.Injective fun g : qHom.ker => (⟨((g : cA) : GL24),
      hmem _ (g : cA).2 (comm_of_qHom_eq_one (MonoidHom.mem_ker.1 g.2))⟩ : T) :=
    fun g h e => Subtype.ext (Subtype.ext (Subtype.mk.inj e))
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 (MonoidHom.mem_ker.2 qHom_aC))
    ?_).symm
  rw [card_zpowers_aC]
  exact (Nat.card_le_card_of_injective _ hinj).trans hT

theorem card_ker_qHom : Nat.card qHom.ker = 2 := by
  rw [ker_qHom, card_zpowers_aC]

theorem card_range_qHom : Nat.card qHom.range = 44590694400 := by
  have h := Subgroup.card_ker_mul_card_range qHom
  rw [card_ker_qHom, card_cent_aG] at h
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K
