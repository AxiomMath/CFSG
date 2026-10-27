module

public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinCent
public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinO2
public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinExtra
public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinNormal
public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinMat
public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinArith
public import CFSG.LocalAnalysis.StandardType.FF81.RootFusionLinIndex

public section

namespace CFSG.StandardType.FF81.RootFusionLin

open Matrix

@[expose] def u1 (m₁ : ℕ) : Subgroup (Cent 1 m₁) := (uSub 1 m₁).subgroupOf (Cent 1 m₁)

instance normal_u1 (m₁ : ℕ) : (u1 m₁).Normal where
  conj_mem x hx g := by
    have h := normal_uSub 1 m₁ (g : GL (BlkIdx 1 m₁) (ZMod 2)) g.2
      (x : GL (BlkIdx 1 m₁) (ZMod 2)) (Subgroup.mem_subgroupOf.mp hx)
    exact Subgroup.mem_subgroupOf.mpr h

theorem card_u1 (m₁ : ℕ) : Nat.card (u1 m₁) = 2 ^ (1 * 1 + 2 * 1 * m₁) := by
  rw [← card_uSub 1 m₁]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (uSub_le_cent 1 m₁)).toEquiv

variable {r m m₁ : ℕ}

@[expose] def preU1 (ψ : Cent r m →* Cent 1 m₁) : Subgroup (GL (BlkIdx r m) (ZMod 2)) :=
  ((u1 m₁).comap ψ).map (Cent r m).subtype

theorem preU1_le_cent (ψ : Cent r m →* Cent 1 m₁) : preU1 ψ ≤ Cent r m :=
  Subgroup.map_subtype_le _

theorem card_preU1 (ψ : Cent r m →* Cent 1 m₁) :
    Nat.card (preU1 ψ) = Nat.card ((u1 m₁).comap ψ) :=
  Subgroup.card_map_of_injective (Subgroup.subtype_injective _)

theorem isPGroup_preU1 (ψ : Cent r m →* Cent 1 m₁) (hψ : Function.Injective ψ) :
    IsPGroup 2 (preU1 ψ) := by
  have hKdvd : Nat.card ((u1 m₁).comap ψ) ∣ Nat.card (u1 m₁) := by
    refine Subgroup.card_dvd_of_injective (ψ.subgroupComap (u1 m₁)) ?_
    intro a b h
    exact Subtype.ext (hψ (congrArg Subtype.val h))
  rw [card_u1] at hKdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hKdvd
  exact IsPGroup.of_card ((card_preU1 ψ).trans hj)

theorem preU1_normalized (ψ : Cent r m →* Cent 1 m₁) :
    ∀ g ∈ Cent r m, ∀ d ∈ preU1 ψ, g * d * g⁻¹ ∈ preU1 ψ := by
  intro g hg d hd
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hd
  refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹, ?_, by simp⟩
  rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact (normal_u1 m₁).conj_mem _ hk _

theorem card_le_of_commute_of_le_preU1 (ψ : Cent r m →* Cent 1 m₁) (hψ : Function.Injective ψ)
    (E : Subgroup (GL (BlkIdx r m) (ZMod 2))) (hED : E ≤ preU1 ψ)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : Nat.card E ≤ 2 ^ (m₁ + 1) := by
  let f : Cent r m →* GL (BlkIdx 1 m₁) (ZMod 2) := (Cent 1 m₁).subtype.comp ψ
  have hf : Function.Injective f := (Subgroup.subtype_injective _).comp hψ
  let E₀ : Subgroup (Cent r m) := E.subgroupOf (Cent r m)
  have hE0 : Nat.card E₀ = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hED.trans (preU1_le_cent ψ))).toEquiv
  have hE1 : Nat.card (E₀.map f) = Nat.card E₀ := Subgroup.card_map_of_injective hf
  have hE1U : E₀.map f ≤ uSub 1 m₁ := by
    rintro _ ⟨e, he, rfl⟩
    have heD : (e : GL (BlkIdx r m) (ZMod 2)) ∈ preU1 ψ := hED (Subgroup.mem_subgroupOf.mp he)
    obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.mp heD
    have hke' : k = e := Subtype.ext hke
    rw [hke'] at hk
    exact Subgroup.mem_subgroupOf.mp hk
  have hE1c : ∀ x ∈ E₀.map f, ∀ y ∈ E₀.map f, x * y = y * x := by
    rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp he₁) _
      (Subgroup.mem_subgroupOf.mp he₂))
  have h := card_le_of_commute_of_le_uSub_one m₁ (E₀.map f) hE1U hE1c
  rwa [hE1, hE0] at h

theorem preU1_le_zSub (ψ : Cent r m →* Cent 1 m₁) (hψ : Function.Injective ψ) (hr : 2 ≤ r)
    (hm : 1 ≤ m) (h3 : 3 ≤ r ∨ 3 ≤ m) (hrm : 2 * r + m = m₁ + 2) : preU1 ψ ≤ zSub r m :=
  le_zSub_of_normal_of_le_uSub r m (m₁ + 2) hr hm h3 hrm (preU1 ψ)
    (le_uSub_of_isPGroup_of_normal r m (preU1 ψ) (preU1_le_cent ψ) (preU1_normalized ψ)
      (isPGroup_preU1 ψ hψ))
    (preU1_normalized ψ)
    (fun E hED _ hcomm => by
      have h := card_le_of_commute_of_le_preU1 ψ hψ E hED hcomm
      rwa [show m₁ + 2 - 1 = m₁ + 1 from rfl])

theorem card_preU1_le_two (ψ : Cent 4 0 →* Cent 1 6) (hψ : Function.Injective ψ) :
    Nat.card (preU1 ψ) ≤ 2 := by
  have hDZ : preU1 ψ ≤ zSub 4 0 :=
    (le_uSub_of_isPGroup_of_normal 4 0 (preU1 ψ) (preU1_le_cent ψ) (preU1_normalized ψ)
      (isPGroup_preU1 ψ hψ)).trans (uSub_le_zSub_of_eq_zero 4)
  have hle : Nat.card (preU1 ψ) ≤ 2 ^ (6 + 1) :=
    card_le_of_commute_of_le_preU1 ψ hψ (preU1 ψ) le_rfl
      (fun x hx y hy => zSub_comm 4 0 (hDZ hx) (hDZ hy))
  exact card_le_two_of_normal_of_le_zSub (preU1 ψ) hDZ (preU1_normalized ψ)
    (lt_of_le_of_lt hle (by norm_num))

theorem card_preU1_le (N r m : ℕ) (hN : N = 8 ∨ N = 9) (hr : 2 ≤ r) (hrm : 2 * r + m = N)
    (ψ : Cent r m →* Cent 1 (N - 2)) (hψ : Function.Injective ψ) :
    Nat.card (preU1 ψ) ≤ 2 ^ (N - 1) ∧ (N = 8 → r = 4 → Nat.card (preU1 ψ) ≤ 2) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    obtain ⟨rfl, rfl⟩ : r = 4 ∧ N = 8 := by omega
    have h2 := card_preU1_le_two ψ hψ
    exact ⟨h2.trans (by norm_num), fun _ _ => h2⟩
  · have hN2 : 2 * r + m = (N - 2) + 2 := by omega
    have hDZ := preU1_le_zSub ψ hψ hr hm (by omega) hN2
    have hle := card_le_of_commute_of_le_preU1 ψ hψ (preU1 ψ) le_rfl
      (fun x hx y hy => zSub_comm r m (hDZ hx) (hDZ hy))
    refine ⟨?_, fun h8 h4 => by omega⟩
    rwa [show N - 2 + 1 = N - 1 by omega] at hle

theorem not_exists_injective_hom (N r m : ℕ) (hN : N = 8 ∨ N = 9) (hr : 2 ≤ r)
    (hrm : 2 * r + m = N) :
    ¬ ∃ ψ : Cent r m →* Cent 1 (N - 2), Function.Injective ψ := by
  rintro ⟨ψ, hψ⟩
  obtain ⟨hD1, hD2⟩ := card_preU1_le N r m hN hr hrm ψ hψ
  have hpos : 0 < Nat.card (preU1 ψ) := Nat.card_pos
  have hd1 : padicValNat 2 (Nat.card (preU1 ψ)) ≤ N - 1 :=
    padicValNat_le_of_le_two_pow hpos hD1
  have hd2 : N = 8 → r = 4 → padicValNat 2 (Nat.card (preU1 ψ)) ≤ 1 := fun h8 h4 =>
    padicValNat_le_of_le_two_pow hpos (by simpa using hD2 h8 h4)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hval := padicValNat_card_le_comap 2 ψ (u1 (N - 2))
  have h1 : padicValNat 2 (Nat.card ((u1 (N - 2)).comap ψ)) =
      padicValNat 2 (Nat.card (preU1 ψ)) := by rw [card_preU1]
  have h2 : padicValNat 2 (u1 (N - 2)).index = (N - 2).choose 2 :=
    padicValNat_index_uSub_cent_one (N - 2)
  have h3 : padicValNat 2 (Nat.card (Cent r m)) = (2 * r + m).choose 2 - r.choose 2 :=
    padicValNat_card_cent r m
  rw [h3, h2, h1, hrm] at hval
  have h4 := choose_add_lt_choose N r (padicValNat 2 (Nat.card (preU1 ψ))) hN hr (by omega)
    hd1 hd2
  have h5 : r.choose 2 ≤ N.choose 2 := Nat.choose_le_choose 2 (by omega)
  omega

end CFSG.StandardType.FF81.RootFusionLin

end
