module

public import CFSG.Quasithin.Background.SmithB45SzIrr

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin CFSG.Quasithin.B45Sz CFSG.Open

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]

variable (a K) in
@[expose] noncomputable def szZ : Subgroup ↥(suzukiGroup a K) :=
  (suzukiZ0 a K).map (MulAut.conj (suzukiWElt a K)).toMonoidHom

theorem mem_szZ_iff (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : ↥(suzukiGroup a K)} :
    g ∈ szZ a K ↔ ∃ v : K, suzukiWElt a K * suzukiSElt a K 0 v * (suzukiWElt a K)⁻¹ = g := by
  rw [szZ, Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).mp hz
    exact ⟨v, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨_, (mem_suzukiZ0_iff hK).mpr ⟨v, rfl⟩, rfl⟩

theorem szZ_le_szUp :
    szZ a K ≤ szUp a K :=
  Subgroup.map_mono (suzukiZ0_le_suzukiU (a := a) (K := K))

theorem card_szZ (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (szZ a K) = 2 ^ (2 * a + 1) := by
  rw [szZ, Subgroup.card_map_of_injective (MulAut.conj (suzukiWElt a K)).injective]
  exact CFSG.QuasithinUnique.Setup.Family.card_suzukiZ0 (K := K) hK

theorem suzukiZ0_mul_self (hK : Nat.card K = 2 ^ (2 * a + 1))
    {z : ↥(suzukiGroup a K)} (hz : z ∈ suzukiZ0 a K) : z * z = 1 := by
  obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).mp hz
  rw [suzukiSElt_mul hK, CharTwo.add_self_eq_zero (0 : K), CharTwo.add_self_eq_zero v,
    zero_pow (pow_ne_zero _ two_ne_zero), zero_mul, add_zero, suzukiSElt_zero_zero hK]

theorem szZ_mul_self (hK : Nat.card K = 2 ^ (2 * a + 1))
    {z : ↥(suzukiGroup a K)} (hz : z ∈ szZ a K) : z * z = 1 := by
  obtain ⟨z₀, hz₀, rfl⟩ := Subgroup.mem_map.mp hz
  rw [← map_mul, suzukiZ0_mul_self hK hz₀, map_one]

theorem suzukiZ0_comm (hK : Nat.card K = 2 ^ (2 * a + 1))
    {y z : ↥(suzukiGroup a K)} (hy : y ∈ suzukiZ0 a K) (hz : z ∈ suzukiZ0 a K) :
    y * z = z * y :=
  (suzuki_unipotent_structure hK).2.2.2.2.1 y hy z hz

theorem szZ_comm (hK : Nat.card K = 2 ^ (2 * a + 1))
    {y z : ↥(suzukiGroup a K)} (hy : y ∈ szZ a K) (hz : z ∈ szZ a K) : y * z = z * y := by
  obtain ⟨y₀, hy₀, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨z₀, hz₀, rfl⟩ := Subgroup.mem_map.mp hz
  rw [← map_mul, ← map_mul, suzukiZ0_comm hK hy₀ hz₀]

theorem isElemAbelian_szZ (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsElemAbelian 2 (szZ a K) :=
  ⟨⟨⟨fun x y => Subtype.ext (szZ_comm hK x.2 y.2)⟩⟩, fun x hx => by
    rw [pow_two]
    exact szZ_mul_self hK hx⟩

theorem suzukiZ0_comm_suzukiU
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {z : ↥(suzukiGroup a K)} (hz : z ∈ suzukiZ0 a K)
    {u : ↥(suzukiGroup a K)} (hu : u ∈ suzukiU a K) : z * u = u * z :=
  (suzuki_unipotent_structure hK).2.2.2.2.2.1 z hz u hu

theorem szZ_normal_in_szUp
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : ((szZ a K).subgroupOf (szUp a K)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨z₀, hz₀, hz⟩ := Subgroup.mem_map.mp hn
  obtain ⟨u, hu, hg⟩ := Subgroup.mem_map.mp g.2
  have hzu : z₀ * u = u * z₀ := suzukiZ0_comm_suzukiU hK hz₀ hu
  have hmem : u * z₀ * u⁻¹ ∈ suzukiZ0 a K := by
    rw [show u * z₀ * u⁻¹ = z₀ from by rw [← hzu]; group]
    exact hz₀
  refine Subgroup.mem_map.mpr ⟨u * z₀ * u⁻¹, hmem, ?_⟩
  show (MulAut.conj (suzukiWElt a K)).toMonoidHom (u * z₀ * u⁻¹) =
    (g : ↥(suzukiGroup a K)) * (n : ↥(suzukiGroup a K)) * (g : ↥(suzukiGroup a K))⁻¹
  rw [← hg, ← hz, ← map_inv, ← map_mul, ← map_mul]

theorem card_szUp (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (szUp a K) = (2 ^ (2 * a + 1)) ^ 2 := by
  rw [szUp, Subgroup.card_map_of_injective (MulAut.conj (suzukiWElt a K)).injective]
  exact (suzuki_unipotent_structure hK).2.1

theorem card_szUp_quot_szZ
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    [((szZ a K).subgroupOf (szUp a K)).Normal] :
    Nat.card (↥(szUp a K) ⧸ (szZ a K).subgroupOf (szUp a K)) = 2 ^ (2 * a + 1) := by
  rw [← Subgroup.index_eq_card]
  have hcardSub : Nat.card ((szZ a K).subgroupOf (szUp a K)) = 2 ^ (2 * a + 1) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe szZ_le_szUp).toEquiv,
      card_szZ hK]
  have h := Subgroup.card_mul_index ((szZ a K).subgroupOf (szUp a K))
  rw [hcardSub, card_szUp hK, pow_two] at h
  exact Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ (2 * a + 1) by positivity) h

theorem suzukiSElt_sq_mem_suzukiZ0
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (x y : K) :
    suzukiSElt a K x y * suzukiSElt a K x y ∈ suzukiZ0 a K := by
  rw [suzukiSElt_mul hK, CharTwo.add_self_eq_zero x, CharTwo.add_self_eq_zero y, zero_add,
    ← pow_succ]
  exact (mem_suzukiZ0_iff hK).mpr ⟨_, rfl⟩

theorem szUp_quot_szZ_mul_self
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    [((szZ a K).subgroupOf (szUp a K)).Normal] :
    ∀ x : ↥(szUp a K) ⧸ (szZ a K).subgroupOf (szUp a K), x * x = 1 := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H g =>
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    obtain ⟨u, hu, hg⟩ := Subgroup.mem_map.mp g.2
    obtain ⟨x, y, rfl⟩ := (mem_suzukiU_iff hK).mp hu
    refine Subgroup.mem_map.mpr ⟨suzukiSElt a K x y * suzukiSElt a K x y,
      suzukiSElt_sq_mem_suzukiZ0 hK x y, ?_⟩
    show (MulAut.conj (suzukiWElt a K)).toMonoidHom
      (suzukiSElt a K x y * suzukiSElt a K x y) =
      (g : ↥(suzukiGroup a K)) * (g : ↥(suzukiGroup a K))
    rw [← hg, map_mul]

end CFSG.RankThree.GF2n.Tim81.Sec2
