module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2h
public import CFSG.Quasithin.Vol2.Ch11SecA02Recog
public import CFSG.Quasithin.Vol2.Ch11SecA11Bar
public import CFSG.Quasithin.Vol2.Ch10SecFAct
public import CFSG.Quasithin.Vol2.Ch10SecKITb
public import CFSG.Quasithin.Vol2.Ch10SecQ4A12

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch10.SecF
open CFSG.Quasithin.Vol2.Ch11.SecA (oSL2 BarData barData_of_quot_SL2)

variable {G : Type} [Group G] [Finite G] {L X : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem range_fK (hXL : X ≤ L) : (C10E4.fK hXL).range = modO2Image L X := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, hXL x.2⟩, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩

omit [Finite G] in
theorem IsNatBlock.nonempty_quot (h : IsNatBlock X n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
      Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨F, _, _, hF, α, hαs, hαk, -⟩ := h.2.1
  exact ⟨F, inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, hF],
    ⟨(QuotientGroup.quotientMulEquivOfEq hαk).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)⟩⟩

theorem xbar_barData (h : IsNatBlock X n) (hn : 2 ≤ n) (hXL : X ≤ L) :
    BarData (modO2Image L X) n := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h.nonempty_quot
  obtain ⟨eL⟩ := CFSG.Quasithin.Vol2.Ch10.SecC.C10KH.lbar_modO2_equiv (Γ := G) hXL
  exact barData_of_quot_SL2 hn hF (eL.trans e)

omit [Finite G] in
theorem xbar_equiv_of_inf_eq_bot (hXL : X ≤ L) (hA : X ⊓ pCoreOf 2 L = ⊥) :
    Nonempty (↥X ≃* ↥(modO2Image L X)) := by
  have hinj : Function.Injective (C10E4.fK hXL) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 : (x : G) ∈ X ⊓ pCoreOf 2 L := ⟨x.2, (C10E4.fK_eq_one_iff hXL x).mp hx⟩
    rw [hA, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext h1)
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (range_fK hXL))⟩

omit [Finite G] in
theorem xbar_equiv_of_inf_eq_U (h : IsNatBlock X n) (hXL : X ≤ L)
    (hB : X ⊓ pCoreOf 2 L = blockU X) :
    Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* ↥(modO2Image L X)) := by
  have hker : (C10E4.fK hXL).ker = CFSG.pCore 2 ↥X := by
    ext x
    rw [MonoidHom.mem_ker, C10E4.fK_eq_one_iff, ← h.mem_blockU_iff, ← hB]
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    ((QuotientGroup.quotientKerEquivRange (C10E4.fK hXL)).trans
      (MulEquiv.subgroupCongr (range_fK hXL)))⟩

theorem xbar_card_A (h : IsNatBlock X n) (hXL : X ≤ L) (hA : X ⊓ pCoreOf 2 L = ⊥) :
    Nat.card ↥(modO2Image L X) = 2 ^ (3 * n) * oSL2 n ∧
      Nat.card ↥(CFSG.pCore 2 ↥(modO2Image L X)) = 2 ^ (2 * n) := by
  obtain ⟨e⟩ := xbar_equiv_of_inf_eq_bot hXL hA
  refine ⟨by rw [← Nat.card_congr e.toEquiv, h.card], ?_⟩
  rw [← CFSG.pCore_map_iso 2 e, Subgroup.card_map_of_injective e.injective, h.card_pCore]

theorem xbar_card_B (h : IsNatBlock X n) (hn : 2 ≤ n) (hXL : X ≤ L)
    (hB : X ⊓ pCoreOf 2 L = blockU X) :
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        Nonempty (↥(modO2Image L X) ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
      Nat.card ↥(modO2Image L X) = 2 ^ n * oSL2 n ∧
      Nat.card ↥(CFSG.pCore 2 ↥(modO2Image L X)) = 1 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h.nonempty_quot
  obtain ⟨e'⟩ := xbar_equiv_of_inf_eq_U h hXL hB
  let e₁ : ↥(modO2Image L X) ≃* Matrix.SpecialLinearGroup (Fin 2) F := e'.symm.trans e
  have hc : Nat.card ↥(modO2Image L X) = 2 ^ n * oSL2 n := by
    rw [Nat.card_congr e₁.toEquiv, Ch11.SecA.card_SL_two hF]
  refine ⟨⟨F, inferInstance, inferInstance, hF, ⟨e₁⟩⟩, hc, ?_⟩
  have : Fintype F := Fintype.ofFinite F
  have hsimp : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.QuasithinUnique.AppE.sl2_isSimpleGroup hn (by rw [← Nat.card_eq_fintype_card, hF])
  have : IsSimpleGroup ↥(modO2Image L X) := e₁.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 ↥(modO2Image L X)) with hb | ht
  · rw [hb, Subgroup.card_bot]
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hP : IsPGroup 2 ↥(modO2Image L X) := by
      have h2 := CFSG.pCore_isPGroup (p := 2) (G := ↥(modO2Image L X))
      rw [ht] at h2
      exact h2.of_equiv Subgroup.topEquiv
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    rw [hc] at hk
    have hodd := Ch11.SecA.odd_oSL2 (m := n) (by omega)
    have h3 : oSL2 n ∣ 2 ^ k := hk ▸ dvd_mul_left _ _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    have h5 : 3 ≤ oSL2 n := by
      unfold oSL2
      have : 2 ^ 2 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rcases j with _ | j
    · rw [hj] at h5
      norm_num at h5
    · rw [hj, pow_succ] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_two.mul_left _)

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
