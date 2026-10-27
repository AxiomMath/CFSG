module

public import CFSG.Quasithin.MS93.FFTypes
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.Quasithin.EmptyFaithful.LRed6Hat
public import CFSG.Quasithin.Background.SmithC27RCaseIOrd
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.MS93.FFGlue

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open (quasithinG2)

section Centralizer

variable {V : Type} [CommGroup V] [Finite V] {X K : Subgroup (MulAut V)}

theorem FFHyp.centralizer_eq_one (h : FFHyp X K) (hZ : Subgroup.center ↥K = ⊥) :
    ∀ c ∈ X, (∀ k ∈ K, c * k = k * c) → c = 1 := by
  intro c hcX hck
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  have hcm : c ^ m = 1 := by
    refine h.cent _ (X.pow_mem hcX m) (fun l hl => ((Commute.pow_left (hck l hl) m)).eq) k ?_
    rw [← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
  have hodd : Odd (orderOf c) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hcm)
  obtain ⟨e, he⟩ := h.two c hcX
  have hcK : c ∈ K := InternalSec.mem_of_pow_mem_of_odd he hodd
  have hcZ : (⟨c, hcK⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hck g g.2).symm
  rw [hZ, Subgroup.mem_bot] at hcZ
  exact congrArg Subtype.val hcZ

end Centralizer

section Main

variable {V : Type} [CommGroup V] [Finite V] {X K : Subgroup (MulAut V)}

theorem conclusion_of_case1i
    (hI : B5.B51IrrInputs) (hV : ∀ v : V, v ^ 2 = 1) (h : FFHyp X K)
    (hU : commV K = ⊤) (hC : fixV K = ⊥) (hB : B51Hyp (ffJ X) K) (hi : B51Case1i (ffJ X) K) :
    (FFCaseSL3 K ∨ FFCaseHatA6 K ∨ FFCaseSp4 K ∨ FFCaseG2 X K) ∧
      ¬ FFExcludedType (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨hIrr, hpair, hsyl⟩ := hi
  have hZ : fixV K ⊓ commV K = ⊥ := by rw [hC, bot_inf_eq]
  rw [hZ, hU] at hpair
  have hR := h.rankTwo
  have hq := h.quasisimple
  have hexcl : ∀ m, ¬ ExcludedOrder m → Nat.card (↥K ⧸ Subgroup.center ↥K) = m →
      ¬ FFExcludedType (↥K ⧸ Subgroup.center ↥K) :=
    fun m hm hc hE => hm (hc ▸ excludedOrder_card hE)
  rcases hpair with ⟨n, F, iF, fF, hF, π, hπ⟩ | ⟨n, F, iF, fF, hF, π, hπ⟩ |
    ⟨n, F, iF, fF, hF, π, hπ⟩ | ⟨n, F, iF, fF, hF, π, hπ⟩ | hG2d | ⟨π, hπ⟩ | ⟨π, hπ⟩ |
    ⟨π, hπ⟩ | ⟨α, π, hπ⟩ | hHat | hSL4 | hSL5 | hE4 | hE5
  ·
    exact (false_of_equiv_statedSL_two hq hR hF
      (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ)).elim
  ·
    let e := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
    obtain ⟨hn, hP, hc⟩ := isPSL_quot_of_equiv_statedSL_three hF e
    exact ⟨Or.inl ⟨n, F, iF, fF, hn, hF, ⟨e.symm⟩, hP, Or.inl ⟨π, hπ⟩⟩,
      hexcl _ (not_excludedOrder_ordA_two hn) hc⟩
  ·
    let e := FFC.equivOfRealizes (FFModel.nat_faithful _) hπ
    have hn1 := R3c2.one_le_of_natCard_eq_two_pow hF
    have hn2 : 2 ≤ n := by
      by_contra hlt
      rw [show n = 1 by omega] at hF
      exact R3c2.not_isQuasisimple_statedSp_two (hF.trans (pow_one 2)) e.symm hq
    exact ⟨Or.inr (Or.inr (Or.inl (Or.inl ⟨n, hn2, F, iF, fF, hF, π, hπ⟩))),
      hexcl _ (not_excludedOrder_ordBC_two hn1) (card_quot_of_equiv_statedSp hF hn2 e)⟩
  ·
    have : CharP F 2 := FFC.charP_two_of_card_pow hF
    let e := FFC.equivOfRealizes (FFC.zornQ_faithful _ le_rfl) hπ
    have hn1 := R3c2.one_le_of_natCard_eq_two_pow hF
    have hn2 : 2 ≤ n := by
      by_contra hlt
      rw [show n = 1 by omega] at hF
      exact R3c2.not_isQuasisimple_quasithinG2_two (hF.trans (pow_one 2)) e.symm hq
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn2, F, iF, fF, hF, π, hπ⟩))),
      hexcl _ (not_excludedOrder_ordG2 hn2) (card_quot_of_equiv_quasithinG2 hF hn2 e)⟩
  ·
    obtain ⟨F, iF, fF, hF, π, hπ⟩ := id hG2d
    have hF2 : Nat.card F = 2 := hF.trans (pow_one 2)
    have : CharP F 2 := FFC.charP_two_of_card_pow hF
    let e := FFC.equivOfRealizes (FFC.zornQ_faithful _ (Subgroup.commutator_le_self _)) hπ
    obtain ⟨hT, hc⟩ := card_quot_of_equiv_g2Derived hF2 e
    have hG2' : G2NaturalDerived K (commV K) (fixV K ⊓ commV K) 1 := by
      rw [hZ, hU]
      exact hG2d
    have hJK : ffJ X ≠ K := SmithC27.ne_of_g2NaturalDerived hI hV hB hIrr hG2'
    have hKJ : K ≤ ffJ X := hB.2.2.2.1
    obtain ⟨T, hT2⟩ := B5.exists_isSylowTwoOf (ffJ X)
    rcases hsyl T hT2 with hJ | ⟨-, hmod⟩
    · exact absurd hJ hJK
    rw [hZ, hU] at hmod
    rcases hmod with ⟨m, hm5, hm8, σ, hσ⟩ | hG2J
    ·
      exfalso
      let eJ := FFC.equivOfRealizes (FFC.symDn_faithful hm5) hσ
      have hdvd : Nat.card K ∣ Nat.card (ffJ X) := Subgroup.card_dvd_of_le hKJ
      have hS : Nat.card (FFModel.symDn m).Gam = m.factorial := by
        show Nat.card (Equiv.Perm (Fin m)) = _
        rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rw [← Nat.card_congr eJ.toEquiv, hS, B42U33.card_of_b42TypeU33 hT] at hdvd
      interval_cases m <;> revert hdvd <;> decide
    ·
      obtain ⟨F', iF', fF', hF', π', hπ'⟩ := id hG2J
      have hF2' : Nat.card F' = 2 := hF'.trans (pow_one 2)
      have : CharP F' 2 := FFC.charP_two_of_card_pow hF'
      let eJ := FFC.equivOfRealizes (FFC.zornQ_faithful _ le_rfl) hπ'
      have hJcard : Nat.card (ffJ X) = 12096 := by
        rw [← Nat.card_congr eJ.toEquiv]
        show Nat.card ↥(quasithinG2 F') = _
        rw [SmithC27.card_quasithinG2' hF', hF2']
        norm_num
      have hXcard : Nat.card X ≤ 12096 :=
        card_le_of_b42TypeU33 h.le h.le_normalizer (h.centralizer_eq_one hT.1) hT
      have hXJ : ffJ X = X :=
        Subgroup.eq_of_le_of_card_ge (B6.ffJ_le X) (hXcard.trans hJcard.ge)
      refine ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨hG2d, fun hXK => hJK ?_, ?_⟩))),
        hexcl _ not_excludedOrder_6048 hc⟩
      · exact le_antisymm (hXK ▸ B6.ffJ_le X) hKJ
      · rw [hXJ] at hG2J
        exact hG2J
  ·
    exact (false_of_equiv_alt hR (Or.inl rfl)
      (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ)).elim
  ·
    exact ⟨Or.inr (Or.inr (Or.inl (Or.inr ⟨π, hπ⟩))), hexcl _ not_excludedOrder_360
      (card_quot_of_equiv_alt6 (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ))⟩
  ·
    exact (false_of_equiv_alt hR (Or.inr rfl)
      (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ)).elim
  ·
    exact (false_of_equiv_alt hR (Or.inr rfl)
      (FFC.equivOfRealizes (FFC.a7Four_faithful α) hπ)).elim
  ·
    obtain ⟨Kf, iK, fK, Γ₀, -, -, hhat, -, π, hπ⟩ := id hHat
    have hH : IsHat ↥K ↥(alternatingGroup (Fin 6)) :=
      IsHat.of_mulEquiv (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ) hhat
    have hirr : XMod.IsIrrSec ↥K (XMod.fixed ↥K (commV K)) (commV K) := hIrr.2.2.2
    have hfix : XMod.fixed ↥K (⊤ : Subgroup V) = ⊥ := by
      rw [eq_bot_iff, ← hC]
      rintro v ⟨-, hv⟩ x hx
      exact hv ⟨x, hx⟩
    rw [hU, hfix] at hirr
    exact ⟨Or.inr (Or.inl ⟨hHat, hH, (LRed6.hat_conclusion hHat).2, hirr⟩),
      hexcl _ not_excludedOrder_360 (card_quot_of_isHat hH)⟩
  ·
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hSL4
    exact (false_of_equiv_statedSL_zmod hR (Or.inl rfl)
      (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ)).elim
  ·
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hSL5
    exact (false_of_equiv_statedSL_zmod hR (Or.inr rfl)
      (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ)).elim
  ·
    obtain ⟨π, hπ⟩ := id hE4
    exact (false_of_equiv_statedSL_zmod hR (Or.inl rfl)
      (FFC.equivOfRealizes (FFC.extSq_faithful (by norm_num)) hπ)).elim
  ·
    obtain ⟨π, hπ⟩ := id hE5
    exact (false_of_equiv_statedSL_zmod hR (Or.inr rfl)
      (FFC.equivOfRealizes (FFC.extSq_faithful (by norm_num)) hπ)).elim

theorem conclusion_of_case1ii
    (hU : commV K = ⊤) (hii : B51Case1ii (ffJ X) K) :
    (FFCaseSL3 K ∨ FFCaseHatA6 K ∨ FFCaseSp4 K ∨ FFCaseG2 X K) ∧
      ¬ FFExcludedType (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨-, n, F, iF, fF, hF, I, π, hind, hsup, hreal, -, -⟩ := hii
  let e := FFC.equivOfRealizes (FFModel.nat_faithful _) (hreal 0)
  obtain ⟨hn, hP, hc⟩ := isPSL_quot_of_equiv_statedSL_three hF e
  refine ⟨Or.inl ⟨n, F, iF, fF, hn, hF, ⟨e.symm⟩, hP,
    Or.inr ⟨I, π, fun _ => bot_le, fun i => ?_, ?_, hreal⟩⟩,
    fun hE => not_excludedOrder_ordA_two hn (hc ▸ excludedOrder_card hE)⟩
  · rw [bot_sup_eq]
    exact disjoint_iff.mp (hind i)
  · rw [bot_sup_eq, hsup, hU]

theorem false_of_case1iii_or_iv
    (h : FFHyp X K)
    (hc : (∃ m, B51Case1iii (ffJ X) K m) ∨ B51Case1iv (ffJ X) K) : False := by
  rcases hc with ⟨m, -, hm, π, U₁, U₂, -, h1, -⟩ | ⟨-, n, hn, k, hk1, hkn, I, π, -, -, -, hreal⟩
  · exact false_of_equiv_statedSL_zmod h.rankTwo hm
      (FFC.equivOfRealizes (FFModel.nat_faithful _) h1)
  · exact false_of_equiv_statedSL_zmod h.rankTwo hn
      (FFC.equivOfRealizes (FFModel.nat_faithful _) (hreal ⟨0, by omega⟩))

theorem ms14AS_of
    (h51 : AsB51) (hI : B5.B51IrrInputs) : MS14AS := by
  intro V _ _ hV X K h
  have hU := h.commV_eq_top hV
  have hC := h.fixV_eq_bot hV
  have hB := h.b51Hyp
  obtain ⟨⟨-, hcases⟩, -⟩ := h51 V hV _ K hB
  refine ⟨hU, hC, ?_⟩
  rcases hcases with hi | hii | hiii | hiv
  · exact conclusion_of_case1i hI hV h hU hC hB hi
  · exact conclusion_of_case1ii hU hii
  · exact (false_of_case1iii_or_iv h (Or.inl hiii)).elim
  · exact (false_of_case1iii_or_iv h (Or.inr hiv)).elim

end Main

theorem ms14AS_holds :
    MS14AS :=
  ms14AS_of B5.asB51_holds
    (FFC.b51IrrInputs_of_ffc asB42_holds asI16Cover_of FFC.asB51NonsplitOffSp4_holds)

end CFSG.Quasithin.MS93
