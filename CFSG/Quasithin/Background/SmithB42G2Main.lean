module

public import CFSG.Quasithin.Background.SmithB42G2Prop
public import CFSG.Quasithin.Background.SmithB42G2Nat
public import CFSG.Quasithin.Background.SmithB42Families
public import CFSG.Quasithin.Background.SmithB51LnB42
public import CFSG.Quasithin.Background.B3Q

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

theorem B42G2.padicValNat_two_pow (k : ℕ) : padicValNat 2 (2 ^ k) = k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact padicValNat.prime_pow k

theorem asB42G2Even_holds (hGM : GM04G2EvenFFNatural) : AsB42G2Even := by
  intro V _ _ hV G L hHyp hP A hA
  obtain ⟨hZ, f, hf2, hmodel⟩ := hP
  have hHyp' := hHyp
  obtain ⟨-, hLF, -, hirr⟩ := hHyp
  have hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    hLF ▸ le_normalizer_quasithinGenFitting G
  have hff : ∀ B, IsFFStarOffender G B → Nat.card V ≤ Nat.card B * Nat.card (fixV B) := by
    intro B hB
    have h := hB.2.2.2 ⊥ bot_le
    rwa [Subgroup.card_bot, one_mul, B1.fixV_bot, Subgroup.card_top] at h
  have hnat := hGM V hV L f hf2 hZ hmodel hirr A (hA.1.trans hGN) hA.2.1 hA.2.2.1 (hff A hA)
  obtain ⟨K, _, _, hK, hreal⟩ := hnat
  have : CharP K 2 := charP_two_of_card (by omega) hK
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one (two_lt_card hK hf2)
  have heq : ⁅quasithinG2 K, quasithinG2 K⁆ = quasithinG2 K :=
    (g2Derived_eq hc0 hc1).trans
      CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup.symm
  have hreal' : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Realizes L ⊤ ⊥ := by
    rw [heq]
    exact hreal
  obtain ⟨π, hπ⟩ := hreal'
  obtain ⟨fc, hfc⟩ := exists_isCoord (lmG K) hπ
  have key : ∀ B, IsFFStarOffender G B →
      B ≤ L ∧ Nat.card B = Nat.card K ^ 3 ∧ Nat.card (fixV B) = Nat.card K ^ 3 := fun B hB =>
    (offender_facts hK hf2 hfc (hB.1.trans hGN) hB.2.2.1).2 hB.2.1 (hff B hB)
  have hJ : ffJ G = L :=
    le_antisymm (iSup₂_le fun B hB => (key B hB).1) (B5.Ln.le_ffJ_of_center hHyp' hZ hA)
  have hcardV : Nat.card V = 2 ^ (6 * f) := by
    rw [card_W hfc, hK, ← pow_mul, mul_comm]
  have hrk : ∀ B, IsFFStarOffender G B → rk ↥B = 3 * f := fun B hB => by
    rw [rk, (key B hB).2.1, hK, ← pow_mul, padicValNat_two_pow, mul_comm]
  have hrAV : ∀ B, IsFFStarOffender G B → rAV B = 1 := by
    intro B hB
    have h1 := rk_add_rkIdx (fixV B)
    have h2 : rk ↥(fixV B) = 3 * f := by
      rw [rk, (key B hB).2.2, hK, ← pow_mul, padicValNat_two_pow, mul_comm]
    have h3 : rk V = 6 * f := by
      rw [rk, hcardV, padicValNat_two_pow]
    have h4 : rkIdx (fixV B) = 3 * f := by omega
    rw [rAV, h4, hrk B hB]
    have h5 : ((3 * f : ℕ) : ℚ) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      omega
    exact div_self h5
  have hq : qOf G = ((1 : ℚ) : WithTop ℚ) :=
    qOf_eq_of_offenders hV le_rfl (fun B hB => (hrAV B hB).ge) ⟨A, hA, (hrAV A hA).le⟩
  refine Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨f, ?_, hrk A hA, fun _ => hJ⟩, hq⟩)))
  rw [hJ]
  exact ⟨K, inferInstance, inferInstance, hK, hreal⟩

end CFSG.Quasithin
