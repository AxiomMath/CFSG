module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenElevenShape
public import CFSG.CGT.PushingUpLit.ThmOne.ThreeOneOmegaSyl

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

theorem eleven11_mem_normalizer_block {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) {g : G} (hgM : g ∈ M)
    (hgU : g ∈ Subgroup.normalizer (U : Set G)) : g ∈ Subgroup.normalizer (L : Set G) := by
  obtain ⟨n, -, -, -, huniq, -⟩ := hd.ten
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  have hLM : ¬ L ≤ M := (mem_elevenBlocksB_iff.1 hd.mem_blocks).2
  have hgM' : g⁻¹ ∈ M := M.inv_mem hgM
  have hgU' : g⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normalizer (U : Set G)).inv_mem hgU
  have hU' : conjSubgroup U g⁻¹ = U := conjSubgroup_eq_iff_mem_normalizer.2 hgU'
  have hCg : conjSubgroup (Subgroup.centralizer (U : Set G)) g⁻¹ =
      Subgroup.centralizer (U : Set G) := by
    rw [E3.conjSubgroup_centralizer, hU']
  have hLg : IsBlockOfInX (Subgroup.centralizer (U : Set G)) (conjSubgroup L g⁻¹) := by
    have := isBlockOfInX_conjSubgroup g⁻¹ hLb
    rwa [hCg] at this
  have hLgM : ¬ conjSubgroup L g⁻¹ ≤ M := by
    intro hle
    apply hLM
    have h1 := (E3.conjSubgroup_le_iff_le_inv g⁻¹).1 hle
    rw [inv_inv, conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hgM)] at h1
    exact h1
  have hLeq : conjSubgroup L g⁻¹ = L := huniq _ hLg hLgM
  have hmem : g⁻¹ ∈ Subgroup.normalizer (L : Set G) := conjSubgroup_eq_iff_mem_normalizer.1 hLeq
  simpa using (Subgroup.normalizer (L : Set G)).inv_mem hmem

theorem eleven11_cent_le_normalizer {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) :
    M ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro g hg
  obtain ⟨hgM, hgC⟩ := Subgroup.mem_inf.1 hg
  refine eleven11_mem_normalizer_block hd hgM ?_
  have hUV : U ≤ V := (deltaEleven_subset_gammaEleven M V hd.mem_delta).1
  exact Subgroup.centralizer_le_normalizer (U : Set G)
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hUV) hgC)

theorem eleven11_Q_le_normalizer {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) : Q ≤ Subgroup.normalizer (L : Set G) := by
  exact hd.setting.sylowQ.1.trans (eleven11_cent_le_normalizer hd)

theorem eleven11_cent_normalized {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) :
    ∀ q ∈ Q, ∀ p ∈ Q ⊓ Subgroup.centralizer (L : Set G),
      q * p * q⁻¹ ∈ Q ⊓ Subgroup.centralizer (L : Set G) := by
  intro q hq p hp
  obtain ⟨hpQ, hpC⟩ := Subgroup.mem_inf.1 hp
  refine Subgroup.mem_inf.2 ⟨Q.mul_mem (Q.mul_mem hq hpQ) (Q.inv_mem hq), ?_⟩
  have hqN : q ∈ Subgroup.normalizer (L : Set G) := eleven11_Q_le_normalizer hd hq
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : q⁻¹ * l * q ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (L : Set G)).inv_mem hqN) l).1 hl
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.1 hpC _ hl'
  calc l * (q * p * q⁻¹) = q * ((q⁻¹ * l * q) * p) * q⁻¹ := by group
    _ = q * (p * (q⁻¹ * l * q)) * q⁻¹ := by rw [h1]
    _ = (q * p * q⁻¹) * l := by group

theorem eleven11_card_U {M V Q U L X : Subgroup G} (hd : Eleven11Data M V Q U L X)
    (h8 : Nat.card V = 8) : Nat.card U = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hUV : U ≤ V := hUΓ.1
  have hUne : U ≠ ⊥ := hUΓ.2.1
  have hVpg : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hd.setting.isElemAbelian
  have hcard : Nat.card V = 2 ^ E3.mQuot V U * Nat.card U := E3.card_eq_two_pow_mul hVpg hUV
  have hq : (E3.mQuot V U : ℕ∞) = rMV M V := hd.mem_delta.2
  have hr : 1 < rMV M V := hd.one_lt_r
  have hq2 : 2 ≤ E3.mQuot V U := by
    rw [← hq] at hr
    exact_mod_cast hr
  have hU2 : 2 ≤ Nat.card U := by
    have h0 : 0 < Nat.card U := Nat.card_pos
    have h1 : Nat.card U ≠ 1 := fun h => hUne (Subgroup.card_eq_one.1 h)
    omega
  have h4 : 4 ≤ 2 ^ E3.mQuot V U := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ E3.mQuot V U := Nat.pow_le_pow_right (by norm_num) hq2
  rw [h8] at hcard
  generalize 2 ^ E3.mQuot V U = a at h4 hcard
  nlinarith

theorem eleven11_card_autI {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) :
    ∃ n : ℕ, 1 < n ∧ rMV M V = (n : ℕ∞) ∧
      Nat.card (autI hd.setting.isElemAbelian X) = 2 ^ n - 1 := by
  obtain ⟨n, hn, h78, hr, -, hD⟩ := hd.ten
  refine ⟨n, hn, hr, ?_⟩
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hLb := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  have hLM : ¬ L ≤ M := (mem_elevenBlocksB_iff.1 hd.mem_blocks).2
  obtain ⟨-, -, -, hcomm, hcard, hfree, -⟩ :=
    eleven_nine_hall_structure hd.setting hUΓ hLb hLM h78 hd.isHall
  have hXM : X ≤ M := fun x hx => (hd.isHall.1 hx).2
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := fun x hx => hd.setting.normal (hXM hx)
  have hker : ∀ x ∈ X, x ∈ Subgroup.centralizer (V : Set G) → x = 1 := by
    intro x hx hxC
    by_contra hx1
    have h1 := hfree x hx hx1
    have hle : ⁅V, X⁆ ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.commutator_le]
      intro v hv d hd'
      have hdv : d * v * d⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hXN hd') v).mp hv
      have hc : ⁅v, d⁆ = v * (d * v * d⁻¹)⁻¹ := by group
      rw [hc, Subgroup.mem_centralizer_singleton_iff]
      have hx1' := Subgroup.mem_centralizer_iff.1 hxC
      have e1 := hx1' _ hv
      have e2 := hx1' _ (V.inv_mem hdv)
      symm
      calc x * (v * (d * v * d⁻¹)⁻¹) = (x * v) * (d * v * d⁻¹)⁻¹ := by group
        _ = (v * x) * (d * v * d⁻¹)⁻¹ := by rw [← e1]
        _ = v * (x * (d * v * d⁻¹)⁻¹) := by group
        _ = v * ((d * v * d⁻¹)⁻¹ * x) := by rw [← e2]
        _ = (v * (d * v * d⁻¹)⁻¹) * x := by group
    have hbot : ⁅V, X⁆ = ⊥ := by
      rw [← h1]
      exact (inf_eq_left.2 hle).symm
    have h2n : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    have : Nat.card (⁅V, X⁆ : Subgroup G) = 1 := by rw [hbot]; exact Subgroup.card_bot
    omega
  have hbot : X ⊓ Subgroup.centralizer (V : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (hker x hx.1 hx.2)
  have hmul := card_autI_mul_card_inf hd.setting.isElemAbelian hXN
  rw [hbot, Subgroup.card_bot, mul_one] at hmul
  rw [hmul]
  exact hcard

theorem eleven11_inf_centralizer_le {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) : V ⊓ Subgroup.centralizer (L : Set G) ≤ U := by
  obtain ⟨n, -, -, -, -, hD⟩ := hd.ten
  have hXU : V ⊓ Subgroup.centralizer (X : Set G) = U := (hD X hd.isHall).2.2.1
  intro v hv
  rw [← hXU]
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hv).1,
    Subgroup.centralizer_le (fun x hx => (hd.isHall.1 hx).1) (Subgroup.mem_inf.1 hv).2⟩

theorem eleven11_blockU_le_Q {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) : blockU L ≤ Q := by
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hL := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  exact (blockU_le_oTwoIn L).trans (eleven_nine_oTwoIn_le_Q hd.setting hUΓ hL)

theorem eleven11_blockU_comm {M V Q U L X : Subgroup G}
    (hd : Eleven11Data M V Q U L X) :
    ∀ x ∈ blockU L, ∀ y ∈ blockU L, x * y = y * x := by
  have hUΓ := deltaEleven_subset_gammaEleven M V hd.mem_delta
  have hL := isBlockOfInX_of_mem_elevenBlocksB hd.setting hUΓ hd.mem_blocks
  intro x hx y hy
  exact ThmOne.blockU_mul_comm hL.2.2.1 hx hy

end CFSG.LocalAnalysis.WeakClosure81
