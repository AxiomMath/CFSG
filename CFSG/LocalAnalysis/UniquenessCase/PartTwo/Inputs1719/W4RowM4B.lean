module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowMGe
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4ChainL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4HeisIndex
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4BF
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.B
import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.MDichotomy

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint CFSG.QuasithinUnique.Setup.X1
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open ArithmeticFunction

theorem w4Thm11_1RowM4_B_holds :
    W4Thm11_1RowM4 .B := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e⟩ := hs
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hZ2 : Nat.card (Subgroup.center ↥L) ∣ 2 := b_center_dvd ↥L hq e
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := odd_card_center_of_o2Trivial hO2
  have hZ : Nat.card (Subgroup.center ↥L) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hZ2 with h1 | h2
    · exact h1
    · rw [h2] at hZodd
      exact absurd hZodd (by decide)
  have hbot : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq (Subgroup.center ↥L) hZ
  let eL : ↥L ≃* NativeSporadic.B :=
    ((QuotientGroup.quotientMulEquivOfEq (M := Subgroup.center ↥L) (N := ⊥) hbot).trans
      QuotientGroup.quotientBot).symm.trans e
  let f : NativeSporadic.B →* MulAut W := L.subtype.comp (eL.symm : NativeSporadic.B →* ↥L)
  have hf_inj : Function.Injective f := L.subtype_injective.comp eL.symm.injective
  obtain ⟨x, y, z, u, hcfg, hy, huQ, huz, hconj⟩ := exists_noncentral_isConj_centre_B
  have hfz : f z ≠ 1 := fun h1 => hcfg.z1 (hf_inj (by rw [h1, map_one]))
  have hcfgmap : HeisCfg 3 4 (fun i : Fin 4 => f (x i)) (fun i : Fin 4 => f (y i)) (f z) :=
    hcfg.map f hfz
  have hy' : ∀ i : Fin 4, f (y i) ^ 3 = 1 := fun i => by rw [← map_pow, hy i, map_one]
  have huQ' : f u ∈ Subgroup.closure (Set.range (fun i : Fin 4 => f (x i)) ∪
      Set.range (fun i : Fin 4 => f (y i)) ∪ {f z}) := by
    have h1 : f u ∈ (Subgroup.closure (Set.range x ∪ Set.range y ∪ {z})).map f :=
      ⟨u, huQ, rfl⟩
    rw [MonoidHom.map_closure] at h1
    refine Subgroup.closure_mono ?_ h1
    rintro a ⟨b, hb, rfl⟩
    rcases hb with (hb | hb) | hb
    · obtain ⟨i, rfl⟩ := hb
      exact Or.inl (Or.inl ⟨i, rfl⟩)
    · obtain ⟨i, rfl⟩ := hb
      exact Or.inl (Or.inr ⟨i, rfl⟩)
    · rw [Set.mem_singleton_iff] at hb
      subst hb
      exact Or.inr rfl
  have huz' : f u ∉ Subgroup.zpowers (f z) := by
    intro hmem
    have h2 : f u ∈ (Subgroup.zpowers z).map f := by
      rw [MonoidHom.map_zpowers f z]
      exact hmem
    rw [Subgroup.mem_map] at h2
    obtain ⟨v, hv, hvu⟩ := h2
    exact huz ((hf_inj hvu) ▸ hv)
  have hconj' : ∃ g : MulAut W, g * f z * g⁻¹ = f u := by
    rw [isConj_iff] at hconj
    obtain ⟨c, hc⟩ := hconj
    refine ⟨(f c)⁻¹, ?_⟩
    have hc' : f c * f u * (f c)⁻¹ = f z := by
      simpa [← map_mul, ← map_inv] using congrArg f hc
    rw [← hc']
    group
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have h162 : 2 ^ 162 ≤ (fixV (Subgroup.zpowers (f z))).index := by
    have hbase : 2 ^ (3 ^ 4 * orderOf (2 : ZMod 3)) ≤ Nat.card (imgT (f z)) := by
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      exact two_pow_le_card_imgT_of_heisCfg hW' (p := 3) (n := 4) (by norm_num) hcfgmap
    have h2 : (2 : ZMod 3) ^ 2 = 1 := by decide
    have h1 : (2 : ZMod 3) ≠ 1 := by decide
    have hord : orderOf (2 : ZMod 3) = 2 := orderOf_eq_prime h2 h1
    rw [show 3 ^ 4 * orderOf (2 : ZMod 3) = 162 by rw [hord]; norm_num] at hbase
    rwa [← index_fixV_zpowers_eq_card_imgT (f z)] at hbase
  let E : Subgroup (MulAut W) := Subgroup.zpowers (f u) ⊔ Subgroup.zpowers (f z)
  have hEsub : E ≤ L := by
    refine sup_le ?_ ?_
    · exact Subgroup.zpowers_le.2 (eL.symm u).2
    · exact Subgroup.zpowers_le.2 (eL.symm z).2
  have hcube : 2 ^ 648 ≤ (fixV E).index ^ 3 := by
    have h := two_pow_four_mul_le_index_cube_of_heis_conj hW' hcfgmap hy' h162 huQ' huz'
      hconj'
    rw [show (4 : ℕ) * 162 = 648 by norm_num] at h
    exact h
  have hlt : 2 ^ 210 < (fixV E).index := by
    have h216 : 2 ^ 216 ≤ (fixV E).index := by
      have h := hcube
      rw [show (648 : ℕ) = 216 * 3 by norm_num, pow_mul] at h
      exact (Nat.pow_le_pow_iff_left (n := 3) (by decide)).1 h
    exact (Nat.pow_lt_pow_of_lt (by decide : 1 < 2) (by decide : 210 < 216)).trans_le h216
  have hΩ : cardFactors (Nat.card ↥L) = 69 := by
    rw [Nat.card_congr eL.toEquiv, CFSG.Monster.Existence.card_nativeB]
    norm_num [CFSG.Open.monsterBabyOrder, cardFactors, Nat.primeFactorsList]
  have hEchain : 2 ^ ((4 - 1) * (cardFactors (Nat.card ↥L) + 1)) < (fixV E).index := by
    rw [hΩ, show (4 - 1) * (69 + 1) = 210 by norm_num]
    exact hlt
  have hY2 : ∃ t ∈ Y, orderOf t = 2 := by
    have h2S : 2 ∣ Nat.card (NativeSporadic.Carrier .B) := by
      change 2 ∣ Nat.card NativeSporadic.B
      rw [CFSG.Monster.Existence.card_nativeB, CFSG.Open.monsterBabyOrder]
      norm_num
    have hS : Nat.card (NativeSporadic.Carrier .B) ∣ Nat.card L := by
      rw [← Nat.card_congr e.toEquiv]
      exact Subgroup.card_quotient_dvd_card _
    obtain ⟨t, hto⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 (h2S.trans hS)
    exact ⟨t, hLY t.2, by rwa [Subgroup.orderOf_coe]⟩
  exact le_mParam_of_chain_L hW' hLY hLn hF hq hO2 hY2 hEsub (c := 4) hEchain

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
