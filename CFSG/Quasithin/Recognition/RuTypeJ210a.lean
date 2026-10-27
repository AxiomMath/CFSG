module

public import CFSG.Quasithin.Recognition.RuTypeJ29f
public import CFSG.Quasithin.Recognition.RuTypeSz8Sylow

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem eq_one_of_odd_comm_inv_Ls
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {u y : G}
    (hu : u ∈ Ls s) (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) (hy : y ∈ Ls s) (hyo : Odd (orderOf y))
    (hc : u * y = y * u) : y = 1 := by
  have huC := Ls_le_Cen s hu
  have hzu : IsConj M.z u := (M.isConj_z_iff hs hs1 huC).mpr ⟨hu, hu2, hu1⟩
  obtain ⟨l, hl, hlz⟩ := M.exists_Ls_conj_z hs hs1 hzu (mem_Cen.mp huC)
  rw [← hlz] at hc
  have h1 : l⁻¹ * y * l * M.z = M.z * (l⁻¹ * y * l) := by
    calc l⁻¹ * y * l * M.z = l⁻¹ * (y * (l * M.z * l⁻¹)) * l := by group
      _ = l⁻¹ * ((l * M.z * l⁻¹) * y) * l := by rw [hc]
      _ = M.z * (l⁻¹ * y * l) := by group
  have hmem : l⁻¹ * y * l ∈ Ls s := by
    have := conj_mem_Ls (inv_mem (Ls_le_Cen s hl)) hy
    simpa using this
  have hS1 := M.mem_S1_of_comm_V hs hs1 M.z_mem_V M.z_ne_one hmem h1
  have hord : orderOf (l⁻¹ * y * l) ∣ 2 ^ 6 := by
    rw [← M.card_S1]
    exact Subgroup.orderOf_dvd_natCard _ hS1
  have hyo' : orderOf (l⁻¹ * y * l) = orderOf y := by
    rw [show l⁻¹ * y * l = l⁻¹ * y * l⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq]
  rw [hyo'] at hord
  obtain ⟨i, -, hie⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hi0 : i = 0 := by
    by_contra h0
    rw [hie] at hyo
    exact Nat.not_even_iff_odd.mpr hyo ((Nat.even_pow' h0).mpr even_two)
  rw [hi0, pow_zero] at hie
  exact orderOf_eq_one_iff.mp hie

theorem hinv_Ls
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {p : ℕ} (hp : Odd p) (hp1 : p ≠ 1) :
    ∀ u y : Ls s, u ^ 2 = 1 → u ≠ 1 → orderOf y = p → u * y ≠ y * u := by
  intro u y hu2 hu1 hy hc
  have h := M.eq_one_of_odd_comm_inv_Ls hs hs1 u.2 (by simpa using congrArg Subtype.val hu2)
    (fun h => hu1 (Subtype.ext h)) y.2 (by rw [Subgroup.orderOf_coe, hy]; exact hp)
    (congrArg Subtype.val hc)
  have : y = 1 := Subtype.ext h
  rw [this, orderOf_one] at hy
  exact hp1 hy.symm

theorem normalizer_Ls_thirteen
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) (P : Sylow 13 (Ls s)) :
    Nat.card (Subgroup.normalizer ((P : Subgroup (Ls s)) : Set (Ls s))) = 52 ∧
      Subgroup.centralizer ((P : Subgroup (Ls s)) : Set (Ls s)) = P :=
  Sz8Sylow.normalizer_thirteen (M.card_Ls hs hs1) (M.hinv_Ls hs hs1 (by decide) (by decide)) P

theorem h713_Ls
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    ∀ y y' : Ls s, orderOf y = 7 → orderOf y' = 13 → y * y' ≠ y' * y := by
  intro y y' hy hy' hc
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hp : IsPGroup 13 (Subgroup.zpowers y') := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hy']
    exact ⟨1, by norm_num⟩
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hPc := Sz8Sylow.card_sylow_of_prime P 2240 (by rw [M.card_Ls hs hs1]) (by norm_num)
  have hPeq : Subgroup.zpowers y' = (P : Subgroup (Ls s)) :=
    Subgroup.eq_of_le_of_card_ge hP (by rw [hPc, Nat.card_zpowers, hy'])
  have hyC : y ∈ Subgroup.centralizer ((P : Subgroup (Ls s)) : Set (Ls s)) := by
    rw [← hPeq, Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left (show Commute y' y from hc.symm) k)).eq
  rw [(M.normalizer_Ls_thirteen hs hs1 P).2, ← hPeq] at hyC
  have h := Subgroup.orderOf_dvd_natCard _ hyC
  rw [Nat.card_zpowers, hy, hy'] at h
  norm_num at h

theorem normalizer_Ls_seven
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) (P : Sylow 7 (Ls s)) :
    Nat.card (Subgroup.normalizer ((P : Subgroup (Ls s)) : Set (Ls s))) = 14 ∧
      Subgroup.centralizer ((P : Subgroup (Ls s)) : Set (Ls s)) = P :=
  Sz8Sylow.normalizer_seven (M.card_Ls hs hs1) (M.hinv_Ls hs hs1 (by decide) (by decide))
    (M.h713_Ls hs hs1) P

@[expose] noncomputable def conjLs
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) : MulAut (Ls s) where
  toFun y := ⟨(M.bel : G) * y * (M.bel : G)⁻¹, M.bel_conj_Ls hs hs1 y.2⟩
  invFun y := ⟨(M.bel : G)⁻¹ * y * M.bel, by
    have h := (M.lemma_J29 hs hs1).2.1.2.1 _ (inv_mem (Subgroup.mem_zpowers _)) _ y.2
    simpa using h⟩
  left_inv y := Subtype.ext (by simp only; group)
  right_inv y := Subtype.ext (by simp only; group)
  map_mul' y y' := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjLs_apply
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) (y : Ls s) :
    ((M.conjLs hs hs1 y : Ls s) : G) = (M.bel : G) * y * (M.bel : G)⁻¹ := rfl

theorem conjLs_pow_three
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) : M.conjLs hs hs1 ^ 3 = 1 := by
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  show (M.bel : G) * ((M.bel : G) * ((M.bel : G) * y * (M.bel : G)⁻¹) * (M.bel : G)⁻¹) *
    (M.bel : G)⁻¹ = y
  have hb3 : (M.bel : G) * M.bel * M.bel = 1 := by
    rw [← M.bel_pow_three, pow_three, mul_assoc]
  calc (M.bel : G) * ((M.bel : G) * ((M.bel : G) * y * (M.bel : G)⁻¹) * (M.bel : G)⁻¹) *
      (M.bel : G)⁻¹ = ((M.bel : G) * M.bel * M.bel) * y * ((M.bel : G) * M.bel * M.bel)⁻¹ := by
        group
    _ = y := by rw [hb3]; group

theorem exists_bel_sylow_thirteen
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    ∃ P : Sylow 13 (Ls s), ∀ y ∈ (P : Subgroup (Ls s)),
      M.conjLs hs hs1 y ∈ (P : Subgroup (Ls s)) := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set α := M.conjLs hs hs1
  set K : Subgroup (MulAut (Ls s)) := Subgroup.zpowers α
  have hK : IsPGroup 3 K := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    have h := orderOf_dvd_of_pow_eq_one (M.conjLs_pow_three hs hs1)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  obtain ⟨P1⟩ := (inferInstance : Nonempty (Sylow 13 (Ls s)))
  have hcard : Nat.card (Sylow 13 (Ls s)) = 560 := by
    have h52 := (M.normalizer_Ls_thirteen hs hs1 P1).1
    have hX := M.card_Ls hs hs1
    have h := (Subgroup.normalizer ((P1 : Subgroup (Ls s)) : Set (Ls s))).card_mul_index
    rw [h52, hX] at h
    have hidx : (Subgroup.normalizer ((P1 : Subgroup (Ls s)) : Set (Ls s))).index = 560 := by
      omega
    rw [Sylow.card_eq_index_normalizer P1]
    exact hidx
  have hmod := hK.card_modEq_card_fixedPoints (Sylow 13 (Ls s))
  rw [hcard] at hmod
  have hne : Nat.card (MulAction.fixedPoints K (Sylow 13 (Ls s))) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact absurd hmod (by decide)
  obtain ⟨⟨P, hP⟩⟩ := (Nat.card_ne_zero.mp hne).1
  refine ⟨P, fun y hy => ?_⟩
  have hfix : (⟨α, Subgroup.mem_zpowers α⟩ : K) • P = P := hP ⟨α, Subgroup.mem_zpowers α⟩
  have hmem : (⟨α, Subgroup.mem_zpowers α⟩ : K) • y ∈
      (⟨α, Subgroup.mem_zpowers α⟩ : K) • (P : Subgroup (Ls s)) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hy
  have hfix' : (⟨α, Subgroup.mem_zpowers α⟩ : K) • (P : Subgroup (Ls s)) = P :=
    congrArg Sylow.toSubgroup hfix
  rw [hfix'] at hmem
  exact hmem

end RuDataM

end CFSG.Quasithin.RuType
