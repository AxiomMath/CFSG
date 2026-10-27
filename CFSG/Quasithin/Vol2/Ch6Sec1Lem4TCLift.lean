module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.H13.T614.Lift

theorem exists_elemAbelian27_of_mod2 {G : Type} [Group G] [Finite G] {F N : Subgroup G}
    (hNF : N ≤ F) (hNn : (N.subgroupOf F).Normal) (hN2 : IsPGroup 2 N)
    (hcomm : ∀ f ∈ F, ∀ g ∈ F, f * g * f⁻¹ * g⁻¹ ∈ N)
    (hexp : ∀ f ∈ F, f ^ 3 ∈ N) (hcard : Nat.card F = 27 * Nat.card N) :
    ∃ S : Subgroup G, S ≤ F ∧ IsMulCommutative S ∧ (∀ x ∈ S, x ^ 3 = 1) ∧ Nat.card S = 27 := by
  have hcop : Nat.Coprime 27 (Nat.card N) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hN2
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  obtain ⟨S, hSF, hS27⟩ : ∃ S : Subgroup G, S ≤ F ∧ Nat.card S = 27 := by
    have hdvd : 3 ^ 3 ∣ Nat.card F := ⟨Nat.card N, by norm_num [hcard]⟩
    obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
    have hmap : Nat.card (H.map F.subtype) = Nat.card H :=
      Subgroup.card_map_of_injective F.subtype_injective
    refine ⟨H.map F.subtype, ?_, hmap.trans (hH.trans (by norm_num))⟩
    rintro _ ⟨h, -, rfl⟩
    exact h.2
  have hSN : S ⊓ N = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    have h1 : Nat.card ↥(S ⊓ N) ∣ 27 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : S ⊓ N ≤ S)
      rwa [hS27] at this
    have h2 : Nat.card ↥(S ⊓ N) ∣ Nat.card N :=
      Subgroup.card_dvd_of_le (inf_le_right : S ⊓ N ≤ N)
    have hg : Nat.gcd 27 (Nat.card N) = 1 := hcop
    have h3 : Nat.card ↥(S ⊓ N) ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [hg] at this
    exact Nat.dvd_one.mp h3
  have key : ∀ x : G, x ∈ S → x ∈ N → x = 1 := by
    intro x hxS hxN
    have hx : x ∈ S ⊓ N := Subgroup.mem_inf.mpr ⟨hxS, hxN⟩
    rw [hSN] at hx
    exact Subgroup.mem_bot.mp hx
  have hcommS : IsMulCommutative S := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    show (a : G) * (b : G) = (b : G) * (a : G)
    have hmemS : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ S :=
      S.mul_mem (S.mul_mem (S.mul_mem a.2 b.2) (S.inv_mem a.2)) (S.inv_mem b.2)
    have hmemN : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ N :=
      hcomm (a : G) (hSF a.2) (b : G) (hSF b.2)
    have h1 : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ = 1 := key _ hmemS hmemN
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  have hexpS : ∀ x ∈ S, x ^ 3 = 1 := fun x hx =>
    key (x ^ 3) (S.pow_mem hx 3) (hexp x (hSF hx))
  exact ⟨S, hSF, hcommS, hexpS, hS27⟩

end CFSG.Quasithin.H13.T614.Lift

end
