module

public import CFSG.RankThree.PartTwo.Sec12.Hering129LOTwoL3Defs
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
import CFSG.LocalAnalysis.ComponentInitial.FourGroupCommuting

public section

namespace CFSG.RankThree.PartTwo.Sec12.Hering129L.OTwoL3

open CFSG.DisconnectedInvolutionGraph.Helpers
open CFSG.LocalAnalysis.ComponentInitial.FourGroup (kleinFourOf card_kleinFourOf
  left_mem_kleinFourOf right_mem_kleinFourOf)

private theorem four_noCommuting {Y : Type*} [Group Y] (hY : ¬ FourGroup Y) (H : Subgroup Y) :
    NoCommutingDistinctInvolutions H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro s t hst
  by_contra hne
  have hs := orderOf_eq_prime_iff.mp ((Subgroup.orderOf_coe (s : H)).trans s.2)
  have ht := orderOf_eq_prime_iff.mp ((Subgroup.orderOf_coe (t : H)).trans t.2)
  exact hY ⟨((s : H) : Y), ((t : H) : Y), hs.1, ht.1, hs.2, ht.2,
    fun h => hne (Subtype.ext (Subtype.ext h)), congrArg Subtype.val hst⟩

theorem four_mem_sylow {L : Type*} [Group L] [Finite L] (hF : FourGroup L) (Q : Sylow 2 L) :
    ∃ c₁ c₂ : L, c₁ ∈ Q ∧ c₂ ∈ Q ∧ c₁ ^ 2 = 1 ∧ c₂ ^ 2 = 1 ∧ c₁ ≠ 1 ∧ c₂ ≠ 1 ∧ c₁ ≠ c₂ ∧
      c₁ * c₂ = c₂ * c₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a₁, a₂, h1, h2, ha1, ha2, ha, hc⟩ := hF
  have h1' : a₁ * a₁ = 1 := by rw [← sq, h1]
  have h2' : a₂ * a₂ = 1 := by rw [← sq, h2]
  have hV : IsPGroup 2 (kleinFourOf a₁ a₂ h1' h2' hc) :=
    IsPGroup.of_card (n := 2) (by rw [card_kleinFourOf ha1 ha2 ha]; norm_num)
  obtain ⟨R, hR⟩ := hV.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq L R Q
  have hmem : ∀ a ∈ R, MulAut.conj g a ∈ g • R := fun a ha =>
    Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) (R : Subgroup L) ha
  refine ⟨MulAut.conj g a₁, MulAut.conj g a₂, hmem _ (hR left_mem_kleinFourOf),
    hmem _ (hR right_mem_kleinFourOf), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · exact fun h => ha1 ((MulAut.conj g).injective (h.trans (map_one _).symm))
  · exact fun h => ha2 ((MulAut.conj g).injective (h.trans (map_one _).symm))
  · exact fun h => ha ((MulAut.conj g).injective h)
  · rw [← map_mul, ← map_mul, hc]

theorem four_exists_involution_ker {Y L : Type*} [Group Y] [Finite Y] [Group L] (φ : Y →* L)
    (hφ : Function.Surjective φ) (hF : FourGroup L) (hY : ¬ FourGroup Y) (S : Sylow 2 Y) :
    ∃ z ∈ S, orderOf z = 2 ∧ φ z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite L := Finite.of_surjective φ hφ
  obtain ⟨c₁, c₂, hc₁, hc₂, h1, h2, hc1, hc2, hne, hc⟩ := four_mem_sylow hF (S.mapSurjective hφ)
  obtain ⟨s₁, hs₁, rfl⟩ := Subgroup.mem_map.mp hc₁
  obtain ⟨s₂, hs₂, rfl⟩ := Subgroup.mem_map.mp hc₂
  have hN : IsPGroup 2 ((S : Subgroup Y) ⊓ φ.ker : Subgroup Y) := S.isPGroup'.to_le inf_le_left
  rcases hN.card_eq_or_dvd with h1N | h2N
  · exfalso
    have hinj : ∀ x ∈ S, φ x = 1 → x = 1 := fun x hx hφx => by
      have hxN : x ∈ ((S : Subgroup Y) ⊓ φ.ker : Subgroup Y) := Subgroup.mem_inf.mpr ⟨hx, hφx⟩
      rwa [Subgroup.card_eq_one.mp h1N, Subgroup.mem_bot] at hxN
    refine hY ⟨s₁, s₂, hinj _ (pow_mem hs₁ 2) (by rw [map_pow, h1]),
      hinj _ (pow_mem hs₂ 2) (by rw [map_pow, h2]), ?_, ?_, ?_, ?_⟩
    · rintro rfl
      exact hc1 (map_one φ)
    · rintro rfl
      exact hc2 (map_one φ)
    · rintro rfl
      exact hne rfl
    · refine mul_inv_eq_one.mp (hinj _ (mul_mem (mul_mem hs₁ hs₂) (inv_mem (mul_mem hs₂ hs₁))) ?_)
      rw [map_mul, map_inv, map_mul, map_mul, hc, mul_inv_cancel]
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2N
    exact ⟨x, (Subgroup.mem_inf.mp x.2).1, by rw [Subgroup.orderOf_coe, hx],
      (Subgroup.mem_inf.mp x.2).2⟩

theorem four_map_eq_one_of_sq {Y L : Type*} [Group Y] [Finite Y] [Group L] (φ : Y →* L)
    (hφ : Function.Surjective φ) (hF : FourGroup L) (hY : ¬ FourGroup Y) (S : Sylow 2 Y) {w : Y}
    (hw : w ∈ S) (hw2 : w ^ 2 = 1) : φ w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hw1 : w = 1
  · rw [hw1, map_one]
  obtain ⟨z, hzS, hz2, hφz⟩ := four_exists_involution_ker φ hφ hF hY S
  have hz1 : z ≠ 1 := (orderOf_eq_prime_iff.mp hz2).2
  have : Nontrivial (S : Subgroup Y) := ⟨⟨⟨z, hzS⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, -, hc⟩ := rank_one_two_group_unique_involution S.isPGroup' (four_noCommuting hY S)
  have hw' := hc ⟨⟨w, hw⟩, (Subgroup.orderOf_mk w hw).trans (orderOf_eq_prime hw2 hw1)⟩
  have hz' := hc ⟨⟨z, hzS⟩, (Subgroup.orderOf_mk z hzS).trans hz2⟩
  have hwz : w = z := congrArg (fun t : Involution (S : Subgroup Y) => ((t : S) : Y))
    (hw'.trans hz'.symm)
  rw [hwz, hφz]

theorem four_mul_ne_mul {Y : Type*} [Group Y] {B : Subgroup Y} {b₁ b₂ h₁ h₂ u₁ u₂ : Y}
    (hb1B : b₁ ∈ B) (hb2B : b₂ ∈ B) (hb₂n : b₂ ∉ Subgroup.zpowers b₁) (hb₁ : b₁ ^ 3 = 1)
    (hb₂ : b₂ ^ 3 = 1) (r11 : h₁ * b₁ * h₁⁻¹ = b₂⁻¹) (r12 : h₁ * b₂ * h₁⁻¹ = b₁)
    (r21 : h₂ * b₁ * h₂⁻¹ = b₁⁻¹ * b₂⁻¹) (r22 : h₂ * b₂ * h₂⁻¹ = b₁⁻¹ * b₂)
    (hact₁ : ∀ b ∈ B, u₁ * b * u₁⁻¹ = h₁ * b * h₁⁻¹)
    (hact₂ : ∀ b ∈ B, u₂ * b * u₂⁻¹ = h₂ * b * h₂⁻¹) : u₁ * u₂ ≠ u₂ * u₁ := by
  intro h
  have e₁ : u₁ * u₂ * b₁ * (u₁ * u₂)⁻¹ = b₂ * b₁⁻¹ := by
    calc u₁ * u₂ * b₁ * (u₁ * u₂)⁻¹ = u₁ * (u₂ * b₁ * u₂⁻¹) * u₁⁻¹ := by group
      _ = h₁ * (b₁⁻¹ * b₂⁻¹) * h₁⁻¹ := by
        rw [hact₂ b₁ hb1B, r21, hact₁ _ (B.mul_mem (B.inv_mem hb1B) (B.inv_mem hb2B))]
      _ = (h₁ * b₁ * h₁⁻¹)⁻¹ * (h₁ * b₂ * h₁⁻¹)⁻¹ := by group
      _ = b₂ * b₁⁻¹ := by rw [r11, r12, inv_inv]
  have e₂ : u₂ * u₁ * b₁ * (u₂ * u₁)⁻¹ = b₂⁻¹ * b₁ := by
    calc u₂ * u₁ * b₁ * (u₂ * u₁)⁻¹ = u₂ * (u₁ * b₁ * u₁⁻¹) * u₂⁻¹ := by group
      _ = h₂ * b₂⁻¹ * h₂⁻¹ := by rw [hact₁ b₁ hb1B, r11, hact₂ _ (B.inv_mem hb2B)]
      _ = (h₂ * b₂ * h₂⁻¹)⁻¹ := by group
      _ = b₂⁻¹ * b₁ := by rw [r22, mul_inv_rev, inv_inv]
  have key : b₂ * b₁⁻¹ = b₂⁻¹ * b₁ := by rw [← e₁, ← e₂, h]
  have hsq : b₁ ^ 2 = b₂ ^ 2 := by
    calc b₁ ^ 2 = b₂ * (b₂⁻¹ * b₁) * b₁ := by rw [sq]; group
      _ = b₂ ^ 2 := by rw [← key, sq]; group
  have hb : b₂ = b₁ := by
    calc b₂ = (b₂ ^ 2) ^ 2 * (b₂ ^ 3)⁻¹ := by group
      _ = (b₁ ^ 2) ^ 2 * (b₁ ^ 3)⁻¹ := by rw [hb₁, hb₂, hsq]
      _ = b₁ := by group
  exact hb₂n (hb ▸ Subgroup.mem_zpowers b₁)

theorem four_sq_conj_one {Y : Type*} [Group Y] {B : Subgroup Y} {b₁ b₂ h₁ u₁ : Y}
    (hb1B : b₁ ∈ B) (hb2B : b₂ ∈ B) (r11 : h₁ * b₁ * h₁⁻¹ = b₂⁻¹) (r12 : h₁ * b₂ * h₁⁻¹ = b₁)
    (hact₁ : ∀ b ∈ B, u₁ * b * u₁⁻¹ = h₁ * b * h₁⁻¹) : u₁ ^ 2 * b₁ * (u₁ ^ 2)⁻¹ = b₁⁻¹ := by
  calc u₁ ^ 2 * b₁ * (u₁ ^ 2)⁻¹ = u₁ * (u₁ * b₁ * u₁⁻¹) * u₁⁻¹ := by rw [sq]; group
    _ = h₁ * b₂⁻¹ * h₁⁻¹ := by rw [hact₁ b₁ hb1B, r11, hact₁ _ (B.inv_mem hb2B)]
    _ = (h₁ * b₂ * h₁⁻¹)⁻¹ := by group
    _ = b₁⁻¹ := by rw [r12]

theorem four_sq_conj_two {Y : Type*} [Group Y] {B : Subgroup Y} {b₁ b₂ h₂ u₂ : Y}
    (hb1B : b₁ ∈ B) (hb2B : b₂ ∈ B) (hb₁ : b₁ ^ 3 = 1) (hbc : b₁ * b₂ = b₂ * b₁)
    (r21 : h₂ * b₁ * h₂⁻¹ = b₁⁻¹ * b₂⁻¹) (r22 : h₂ * b₂ * h₂⁻¹ = b₁⁻¹ * b₂)
    (hact₂ : ∀ b ∈ B, u₂ * b * u₂⁻¹ = h₂ * b * h₂⁻¹) : u₂ ^ 2 * b₁ * (u₂ ^ 2)⁻¹ = b₁⁻¹ := by
  calc u₂ ^ 2 * b₁ * (u₂ ^ 2)⁻¹ = u₂ * (u₂ * b₁ * u₂⁻¹) * u₂⁻¹ := by rw [sq]; group
    _ = h₂ * (b₁⁻¹ * b₂⁻¹) * h₂⁻¹ := by
      rw [hact₂ b₁ hb1B, r21, hact₂ _ (B.mul_mem (B.inv_mem hb1B) (B.inv_mem hb2B))]
    _ = (h₂ * b₁ * h₂⁻¹)⁻¹ * (h₂ * b₂ * h₂⁻¹)⁻¹ := by group
    _ = b₂ * b₁ * b₂⁻¹ * b₁ := by rw [r21, r22]; group
    _ = b₁ ^ 3 * b₁⁻¹ := by rw [← hbc, pow_three']; group
    _ = b₁⁻¹ := by rw [hb₁, one_mul]

theorem four_trichotomy {G : Type*} [Group G]
    (h : IsCyclic G ∨ ∃ n : ℕ, 1 ≤ n ∧ Nonempty (QuaternionGroup (2 ^ n) ≃* G)) (x y : G) :
    x ^ 4 = 1 ∨ y ^ 4 = 1 ∨ x * y = y * x := by
  rcases h with h | ⟨n, -, ⟨e⟩⟩
  · exact Or.inr (Or.inr (mul_comm' x y))
  · obtain ⟨p, rfl⟩ := e.surjective x
    obtain ⟨q, rfl⟩ := e.surjective y
    rcases p with i | i
    · rcases q with j | j
      · refine Or.inr (Or.inr ?_)
        rw [← map_mul, ← map_mul, QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_a, add_comm]
      · exact Or.inr (Or.inl (by rw [← map_pow, QuaternionGroup.xa_pow_four, map_one]))
    · exact Or.inl (by rw [← map_pow, QuaternionGroup.xa_pow_four, map_one])

theorem exists_commuting_involutions_of_acting {Y L : Type} [Group Y] [Finite Y] [Group L]
    (φ : Y →* L) (hφ : Function.Surjective φ) (hF : FourGroup L)
    {b₁ b₂ h₁ h₂ : Y} (hb₁1 : b₁ ≠ 1) (hb₂n : b₂ ∉ Subgroup.zpowers b₁) (hb₁ : b₁ ^ 3 = 1)
    (hb₂ : b₂ ^ 3 = 1) (hbc : b₁ * b₂ = b₂ * b₁)
    (r11 : h₁ * b₁ * h₁⁻¹ = b₂⁻¹) (r12 : h₁ * b₂ * h₁⁻¹ = b₁)
    (r21 : h₂ * b₁ * h₂⁻¹ = b₁⁻¹ * b₂⁻¹) (r22 : h₂ * b₂ * h₂⁻¹ = b₁⁻¹ * b₂)
    (hinj : ∀ b ∈ Subgroup.closure ({b₁, b₂} : Set Y), φ b = 1 → b = 1)
    (P : Subgroup Y) (u₁ u₂ : Y) (hP2 : IsPGroup 2 P) (hu₁ : u₁ ∈ P) (hu₂ : u₂ ∈ P)
    (hPB : ∀ b ∈ Subgroup.closure ({b₁, b₂} : Set Y), ∀ u ∈ P,
      u * b * u⁻¹ ∈ Subgroup.closure ({b₁, b₂} : Set Y))
    (hact₁ : ∀ b ∈ Subgroup.closure ({b₁, b₂} : Set Y), u₁ * b * u₁⁻¹ = h₁ * b * h₁⁻¹)
    (hact₂ : ∀ b ∈ Subgroup.closure ({b₁, b₂} : Set Y), u₂ * b * u₂⁻¹ = h₂ * b * h₂⁻¹) :
    ∃ s t : Y, s ^ 2 = 1 ∧ t ^ 2 = 1 ∧ s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t ∧ s * t = t * s := by
  by_contra hY
  change ¬ FourGroup Y at hY
  have hb1B : b₁ ∈ Subgroup.closure ({b₁, b₂} : Set Y) := Subgroup.subset_closure (by simp)
  have hb2B : b₂ ∈ Subgroup.closure ({b₁, b₂} : Set Y) := Subgroup.subset_closure (by simp)
  have hcomm := four_mul_ne_mul hb1B hb2B hb₂n hb₁ hb₂ r11 r12 r21 r22 hact₁ hact₂
  have hsq₁ := four_sq_conj_one hb1B hb2B r11 r12 hact₁
  have hsq₂ := four_sq_conj_two hb1B hb2B hb₁ hbc r21 r22 hact₂
  have hinv : b₁⁻¹ ≠ b₁ := by
    intro h
    apply hb₁1
    calc b₁ = b₁ ^ 3 * (b₁⁻¹ * b₁⁻¹) := by group
      _ = 1 := by
        rw [hb₁, one_mul]
        nth_rewrite 2 [h]
        exact inv_mul_cancel b₁
  obtain ⟨S, hPS⟩ := hP2.exists_le_sylow
  have hfix : ∀ w ∈ P, w ^ 2 = 1 → w * b₁ * w⁻¹ = b₁ := by
    intro w hw hw2
    have hφw := four_map_eq_one_of_sq φ hφ hF hY S (hPS hw) hw2
    have hmem : w * b₁ * w⁻¹ * b₁⁻¹ ∈ Subgroup.closure ({b₁, b₂} : Set Y) :=
      mul_mem (hPB b₁ hb1B w hw) (inv_mem hb1B)
    exact mul_inv_eq_one.mp (hinj _ hmem (by simp [hφw]))
  have hfour : ∀ u ∈ P, u ^ 2 * b₁ * (u ^ 2)⁻¹ = b₁⁻¹ → u ^ 4 ≠ 1 := by
    intro u hu hsq h4
    apply hinv
    rw [← hsq]
    exact hfix _ (pow_mem hu 2) (by rw [← pow_mul]; exact h4)
  rcases four_trichotomy (rank_one_two_cyclic_or_quaternion hP2 (four_noCommuting hY P))
      (⟨u₁, hu₁⟩ : P) ⟨u₂, hu₂⟩ with h | h | h
  · exact hfour u₁ hu₁ hsq₁ (by simpa using congrArg Subtype.val h)
  · exact hfour u₂ hu₂ hsq₂ (by simpa using congrArg Subtype.val h)
  · exact hcomm (by simpa using congrArg Subtype.val h)

end CFSG.RankThree.PartTwo.Sec12.Hering129L.OTwoL3
