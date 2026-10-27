module

public import CFSG.Sporadic.Th.Recog.MFactsB.ConjThree
public import CFSG.Sporadic.Th.Recog.MFactsB.ConjThreeSound
public import CFSG.Sporadic.Th.Recog.MFactsB.E8
public import CFSG.Sporadic.Th.Recog.MFactsB.G1
public import CFSG.Sporadic.Th.Recog.MFactsB.RowsSound
public import CFSG.Sporadic.Th.Recog.MFactsB.Seven
public import CFSG.Sporadic.Th.Recog.GlueTwist
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Layer
public import CFSG.Sporadic.ThI301.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Defs

public noncomputable section

namespace CFSG.Sporadic.ThI301

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Recog CFSG.Sporadic.Th.Recog.MFactsB
  CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H301
open CFSG.GH74.QTGen4.Recog.G23 (Ghat ghat_simple ghat_card)
open CFSG.Blueprint CFSG.Blueprint.Chevalley

section Catalogue


private def pp3 : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩

private theorem pp3_card : pp3.card = 3 := by
  rw [TauCeti.PrimePower.card_def]
  norm_num [pp3]

private theorem valid_G2_three : (TauCeti.LieTypeIndex.G2 pp3).Valid := by
  refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
  · simp [TauCeti.LieTypeIndex.inStandardRange_iff, pp3]
  · simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]

theorem catalogIs_isG2of_three {T : Type} [Group T] (e : T ≃* Ghat) : catalogIs T (isG2of 3) := by
  obtain ⟨b⟩ := CFSG.TauCetiBridge.untwistedBridge_G2 pp3 valid_G2_three (by decide) (ZMod 3)
    (by rw [Nat.card_zmod, pp3_card])
  let e₁ : AdjointQuotient .G2 (ZMod 3) ≃* ↥(adjointGroup .G2 (ZMod 3)) :=
    (QuotientGroup.quotientMulEquivOfEq CFSG.LieType.Chevalley.center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot
  exact ⟨.lie ⟨.G2 pp3, valid_G2_three⟩, pp3_card, ⟨e.trans (e₁.symm.trans b)⟩⟩

end Catalogue


@[expose] def B1 : Subgroup J := Subgroup.closure {hswJ 6, ((ω₁ : ↥Max3.M) : J), ((ω₂ : ↥Max3.M) : J)}

theorem M_le_normalizer_Q : Max3.M ≤ Subgroup.normalizer (Max3.Q : Set J) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    have h := Subgroup.mem_subgroupOf.1 (Max3.normal_Q_subgroupOf_M.conj_mem ⟨q, Max3.Q_le_M hq⟩
      (Subgroup.mem_subgroupOf.2 hq) ⟨g, hg⟩)
    rwa [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h
  · intro hq
    have h := Subgroup.mem_subgroupOf.1 (Max3.normal_Q_subgroupOf_M.conj_mem
      ⟨g * q * g⁻¹, Max3.Q_le_M hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨g, hg⟩⁻¹)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at h
    have e : g⁻¹ * (g * q * g⁻¹) * g = q := by group
    rwa [e] at h

theorem row_hR : IsExtraSpec2 Max3.Q ∧ Nat.card Max3.Q = 2 ^ Row.th.rexp := by
  obtain ⟨h2, hc, hf, hz⟩ := Max3.isExtraspecialPGroup_Q
  refine ⟨⟨h2, hc.trans hf.symm, hf, hz⟩, ?_⟩
  rw [Max3.card_Q]
  rfl

private theorem ω₂_pow_three' : ω₂ ^ 3 = 1 := by
  rw [ω₂, show uM * ω₁ * uM⁻¹ = MulAut.conj uM ω₁ from by rw [MulAut.conj_apply], ← map_pow,
    ω₁_pow_three, map_one]

private theorem coe_kap_facts :
    ((Max3.InvRep.kap tLetter : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)) = permT ∧
      ((Max3.InvRep.kap ω₁ : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)) = permW1 ∧
      ((Max3.InvRep.kap ω₂ : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)) = permW2 :=
  ⟨coe_kap_tLetter, coe_kap_ω₁, coe_kap_ω₂⟩

private theorem perm_indep : ∀ i j k : Fin 3,
    permT ^ i.val * permW1 ^ j.val * permW2 ^ k.val = 1 → i = 0 ∧ j = 0 ∧ k = 0 := by
  decide +kernel

theorem commute_facts : Commute (hswJ 6) ((ω₁ : ↥Max3.M) : J) ∧
    Commute (hswJ 6) ((ω₂ : ↥Max3.M) : J) ∧
    Commute ((ω₁ : ↥Max3.M) : J) ((ω₂ : ↥Max3.M) : J) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg Subtype.val ω₁_comm_tLetter
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    exact h.symm
  · have h := congrArg Subtype.val ω₂_comm_tLetter
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    exact h.symm
  · have h := congrArg Subtype.val ω₁_comm_ω₂
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    exact h

theorem pow_facts : hswJ 6 ^ 3 = 1 ∧ ((ω₁ : ↥Max3.M) : J) ^ 3 = 1 ∧
    ((ω₂ : ↥Max3.M) : J) ^ 3 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← orderOf_hswJ_six]
    exact pow_orderOf_eq_one _
  · rw [← Subgroup.coe_pow, ω₁_pow_three, Subgroup.coe_one]
  · rw [← Subgroup.coe_pow, ω₂_pow_three', Subgroup.coe_one]

theorem indep_facts : ∀ i j k : ℕ, i < 3 → j < 3 → k < 3 →
    hswJ 6 ^ i * ((ω₁ : ↥Max3.M) : J) ^ j * ((ω₂ : ↥Max3.M) : J) ^ k = 1 →
      i = 0 ∧ j = 0 ∧ k = 0 := by
  intro i j k hi hj hk h
  have hM : tLetter ^ i * ω₁ ^ j * ω₂ ^ k = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_pow,
      Subgroup.coe_one]
    exact h
  have hκ := congrArg (fun m => ((Max3.InvRep.kap m : alternatingGroup (Fin 9)) :
    Equiv.Perm (Fin 9))) hM
  simp only [map_mul, map_pow, map_one, Subgroup.coe_mul, Subgroup.coe_pow,
    Subgroup.coe_one] at hκ
  obtain ⟨hT, hW1, hW2⟩ := coe_kap_facts
  rw [hT, hW1, hW2] at hκ
  have := perm_indep ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ hκ
  simp only [Fin.ext_iff, Fin.val_zero] at this
  exact this

theorem row_hB : IsElemAbelian Row.th.prime B1 ∧ Nat.card B1 = Row.th.prime ^ (Row.th.rank - 1) := by
  obtain ⟨h1, h2, h12⟩ := commute_facts
  obtain ⟨ht3, hw1, hw2⟩ := pow_facts
  exact isElemAbelian_closure_three h1 h2 h12 ht3 hw1 hw2 indep_facts

theorem B1_le_M : B1 ≤ Max3.M := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl | rfl)
  · exact hswJ_mem_M 6 (by decide)
  · exact ω₁.2
  · exact ω₂.2

theorem row_hBN : B1 ≤ Subgroup.normalizer (Max3.Q : Set J) :=
  B1_le_M.trans M_le_normalizer_Q

theorem row_hd : hswJ 6 ∈ B1 ∧ hswJ 6 ≠ 1 := by
  refine ⟨Subgroup.subset_closure (Set.mem_insert _ _), fun h => ?_⟩
  have h3 := orderOf_hswJ_six
  rw [h, orderOf_one] at h3
  exact absurd h3 (by norm_num)

private theorem conj_mem_commutator {G : Type*} [Group G] {H : Subgroup G} {g : G} (hg : g ∈ H)
    {s : G} (hs : s ∈ ⁅H, H⁆) : g * s * g⁻¹ ∈ ⁅H, H⁆ := by
  have hH : H.map (MulAut.conj g).toMonoidHom = H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact H.mul_mem (H.mul_mem hg hy) (H.inv_mem hg)
    · intro hx
      refine ⟨g⁻¹ * x * g, H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have h1 : (⁅H, H⁆).map (MulAut.conj g).toMonoidHom = ⁅H, H⁆ := by
    rw [Subgroup.map_commutator, hH]
  rw [← h1]
  exact ⟨s, hs, by simp [MulAut.conj_apply]⟩

section Split


theorem split_t : ∃ K : Subgroup J, K ≤ Subgroup.centralizer ({hswJ 6} : Set J) ∧
    K ⊓ Subgroup.zpowers (hswJ 6) = ⊥ ∧
    K ⊔ Subgroup.zpowers (hswJ 6) = Subgroup.centralizer ({hswJ 6} : Set J) ∧
    K = ⁅Subgroup.centralizer ({hswJ 6} : Set J), Subgroup.centralizer ({hswJ 6} : Set J)⁆ ∧
    Nonempty (↥K ≃* Ghat) :=
  splitJ_of_core rfl (thCoreJ.centralizer_t_split ({ card_centralizer_t := card_centralizer_t,
                                                     conj_three := conj_three_of ω₁_comm_ω₂
                                                         eq_one_or_eq_z_of_comm_ω₁_mul_ω₂
                                                         eq_one_or_eq_z_of_comm_ω₁,
                                                     g1 := ⟨H₁, H₂, mg1_of y₁_mul_x₁ ω₁_mul_y₁
                                                         x₁_comm_x₂ x₁_comm_ω₂ ω₁_comm_x₂ ω₁_comm_ω₂⟩,
                                                     complement_t := exists_complement_t,
                                                     center_t := center_t,
                                                     e8 := ⟨E₀, e₀, e8Facts_of e₀_comm_e₁
                                                         e8_injective nE_comm_tLetter nE_conj_e₀
                                                         nE_conj_e₁ eq_e8_of_commute_pre_mul
                                                         cE_comm_e₀ cN_comm_e₀ of_commute_e₀⟩,
                                                     seven := seven_of_card_Q_inf_centralizer_s
                                                         card_Q_inf_centralizer_s,
                                                     card_D8 := card_D8M }))

theorem row_hI : RowI .th Row.th.prime (rowIOf Row.th.prime (hswJ 6)) := by
  obtain ⟨K, hKC, -, -, hKc, ⟨e⟩⟩ := split_t
  haveI : IsSimpleGroup Ghat := ghat_simple
  haveI hS : IsSimpleGroup ↥K := MulEquiv.isSimpleGroup e
  have hcard : Nat.card ↥K = 7371 * 576 := (Nat.card_congr e.toEquiv).trans ghat_card
  have h3 : 3 ∣ Nat.card ↥K := by rw [hcard]; norm_num
  have hnab : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 h3
    have hn : (Subgroup.zpowers x).Normal :=
      ⟨fun n hn g => by rw [hcon g n, mul_inv_cancel_right]; exact hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h | h
    · rw [Subgroup.zpowers_eq_bot] at h
      rw [h, orderOf_one] at hx
      exact absurd hx (by norm_num)
    · have h' := Nat.card_zpowers x
      rw [h, Subgroup.card_top, hx, hcard] at h'
      exact absurd h' (by norm_num)
  have hKn : ∀ g ∈ Subgroup.centralizer ({hswJ 6} : Set J), ∀ s ∈ K, g * s * g⁻¹ ∈ K := by
    intro g hg s hs
    rw [hKc] at hs ⊢
    exact conj_mem_commutator hg hs
  have hL : GLAPLayer 3 (Subgroup.centralizer ({hswJ 6} : Set J)) = K :=
    glaPLayer_eq_of_isSimple_normal_commutator_le Nat.prime_three hKC hKn hS hnab h3 hKc.ge
  show IsTypeWithCenter 3 (GLAPLayer 3 (Subgroup.centralizer ({hswJ 6} : Set J))) (isG2of 3) 1
  rw [hL]
  exact isTypeWithCenter_of_isSimple Nat.prime_three hS hnab h3 (catalogIs_isG2of_three e)

end Split

end CFSG.Sporadic.ThI301
