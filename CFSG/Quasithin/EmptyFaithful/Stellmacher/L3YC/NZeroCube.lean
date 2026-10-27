module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.CaseFourCover
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.CyclicN0
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.LayerCube
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.SeriesTrivial
public import CFSG.Quasithin.MS93.S36Frat
public import CFSG.Quasithin.EmptyFaithful.SBd7Case3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417 CFSG.Quasithin.SBd7
open scoped commutatorElement Pointwise

namespace Stellmacher.L3YC

variable {G : Type} [Group G] [Finite G]

theorem cube_centralizes_c134Q {L S : Subgroup G} (hq : IsLnTwoQuot L 3)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (h4 : MS93.IsC134Case4Corr (L ⊔ S) S L)
    {z : G} (hz : z ∈ N0 L) {m : ℕ} (hzm : z ^ 3 ^ m = 1) :
    ∀ q ∈ c134Q (L ⊔ S) L, z ^ 3 * q * (z ^ 3)⁻¹ = q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQL : c134Q (L ⊔ S) L ≤ pCoreOf 2 L := Stellmacher.CD.L3YC.c134Q_le_pCoreOf hSL
  have hQeq : c134Q (L ⊔ S) L = ⁅pCoreOf 2 L, L⁆ :=
    Stellmacher.CD.L3YC.c134Q_eq_of_comm_self hSL
      (Stellmacher.CD.L3YC.comm_self_of_case4Corr h4)
  have hzQ : z ∈ Subgroup.normalizer ((c134Q (L ⊔ S) L : Subgroup G) : Set G) := by
    rw [hQeq]
    exact SBd5.mem_normalizer_commutator_of (normalizer_le_normalizer_pCoreOf 2 L hz.1) hz.1
  have hzC : z ∈ Subgroup.normalizer ((c134CQ (L ⊔ S) L : Subgroup G) : Set G) :=
    Stellmacher.CD.L3YC.normalizer_le_normalizer_c134CQ_of_case4 hSL h4 hz.1
  obtain ⟨⟨n, F, _, _, α, hFc, hα, hE2, hZc, hCU, hU, hΦ, hK, hQ'⟩, -⟩ := h4
  set Q : Subgroup G := c134Q (L ⊔ S) L with hQdef
  have hF : Fintype.card F = 2 := SBd5.card_eq_two_of_modO2Surj hq hFc hα
  have hn1 : n = 1 := by
    have h2 : 2 ^ n = 2 ^ 1 := by rw [← hFc, hF]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  subst hn1
  have hbotN : z ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp [Subgroup.mem_bot]
  have hzZ : z ∈ Subgroup.normalizer ((centerOf Q : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hzQ, S153F.mem_normalizer_centralizer_of_mem_normalizer hzQ⟩
  have hzΦ : z ∈ Subgroup.normalizer ((frattiniIn Q : Subgroup G) : Set G) :=
    (MS93.S36.le_normalizer_frattiniIn (M := Subgroup.zpowers z) (P := Q)
      (Subgroup.zpowers_le.mpr hzQ)) (Subgroup.mem_zpowers z)
  have hzK : z ∈ Subgroup.normalizer
      ((Q ⊓ Subgroup.centralizer (frattiniIn Q : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hzQ, S153F.mem_normalizer_centralizer_of_mem_normalizer hzΦ⟩
  have hzU : z ∈ Subgroup.normalizer ((⁅centerOf Q, L⁆ : Subgroup G) : Set G) :=
    SBd5.mem_normalizer_commutator_of hzZ hz.1
  have hlU := layer_cube_trivial hF (by norm_num) α hα false hU hz.1 hzU hbotN hz.2 hzm
  have hlΦ := layer_cube_trivial hF (by norm_num) α hα true hΦ hz.1 hzΦ hzZ hz.2 hzm
  have hlK := layer_cube_trivial hF (by norm_num) α hα true hK hz.1 hzK hzΦ hz.2 hzm
  have hlQ := layer_cube_trivial hF (by norm_num) α hα false hQ' hz.1 hzQ hzK hz.2 hzm
  obtain ⟨hC4', hCsq'⟩ := isE2_card_sq hE2
  have hC4 : Nat.card ↥(c134CQ (L ⊔ S) L) = 4 := by rw [hC4']; norm_num
  have hCsq : ∀ c ∈ c134CQ (L ⊔ S) L, c * c = 1 := fun c hc =>
    congrArg Subtype.val (hCsq' ⟨c, hc⟩)
  have hVc : ∀ x ∈ c134CQ (L ⊔ S) L, z ^ 3 * x * (z ^ 3)⁻¹ = x :=
    pow_three_centralizes (card_mulAut_of_card_four hC4 hCsq) hzC hzm
  have hUfix : ∀ x ∈ ⁅centerOf Q, L⁆, z ^ 3 * x * (z ^ 3)⁻¹ = x := by
    intro x hx
    have := hlU x hx
    rw [Subgroup.mem_bot, inv_mul_eq_one] at this
    exact this.symm
  have hVcZ : c134CQ (L ⊔ S) L ≤ centerOf Q :=
    le_sup_left.trans hZc.symm.le
  have hUZ : ⁅centerOf Q, L⁆ ≤ centerOf Q :=
    le_sup_right.trans hZc.symm.le
  have hZfix : ∀ x ∈ centerOf Q, z ^ 3 * x * (z ^ 3)⁻¹ = x := by
    intro x hx
    have hx' : x ∈ c134CQ (L ⊔ S) L ⊔ ⁅centerOf Q, L⁆ := hZc.le hx
    obtain ⟨a, ha, b, hb, rfl⟩ := SBd2.exists_mul_of_mem_sup'
      (fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hVcZ ha).2 b (hUZ hb).1).symm) hx'
    calc z ^ 3 * (a * b) * (z ^ 3)⁻¹
        = (z ^ 3 * a * (z ^ 3)⁻¹) * (z ^ 3 * b * (z ^ 3)⁻¹) := by group
      _ = a * b := by rw [hVc a ha, hUfix b hb]
  have hQ2 : IsPGroup 2 ↥Q := (pCoreOf_isPGroup 2 L).to_le hQL
  have hgm : (z ^ 3) ^ 3 ^ m = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hzm, one_pow]
  have s1 := fixes_of_fixes_sub_and_quotient (N := centerOf Q) (H := frattiniIn Q) hΦ.2.1
    (hQ2.to_le inf_le_left) (pow_mem hzΦ 3) hgm hZfix hlΦ
  have s2 := fixes_of_fixes_sub_and_quotient (N := frattiniIn Q)
    (H := Q ⊓ Subgroup.centralizer (frattiniIn Q : Set G)) hK.2.1
    (hQ2.to_le (MS93.S36.frattiniIn_le Q)) (pow_mem hzK 3) hgm s1 hlK
  have s3 := fixes_of_fixes_sub_and_quotient
    (N := Q ⊓ Subgroup.centralizer (frattiniIn Q : Set G)) (H := Q) hQ'.2.1
    (hQ2.to_le inf_le_left) (pow_mem hzQ 3) hgm s2 hlQ
  exact s3

end Stellmacher.L3YC

end CFSG.Quasithin
