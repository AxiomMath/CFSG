module

public import CFSG.RankThree.PartOne.Q1327C.BLift
public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.Dihedral.OriginalSylowControl
public import CFSG.RankThree.Theta.ThreeCoreComponentNormalization

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Torsion37
open CFSG.Assembly.RankThreeEven (localRank)

theorem card_comap_of_surjective {X H : Type} [Group X] [Finite X] [Group H] (ρ : X →* H)
    (hρ : Function.Surjective ρ) (B : Subgroup H) :
    Nat.card (B.comap ρ) = Nat.card ρ.ker * Nat.card B := by
  have hker_le : ρ.ker ≤ B.comap ρ := fun x hx => by
    show ρ x ∈ B
    rw [MonoidHom.mem_ker.1 hx]
    exact B.one_mem
  have h1 := Subgroup.card_ker_mul_card_range (ρ.comp (B.comap ρ).subtype)
  have hrange : (ρ.comp (B.comap ρ).subtype).range = B := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact Subgroup.map_comap_eq_self_of_surjective hρ B
  have hker' : (ρ.comp (B.comap ρ).subtype).ker = ρ.ker.subgroupOf (B.comap ρ) := by
    ext x
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  rw [hrange, hker'] at h1
  rw [← h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv]

theorem four_le_twoLocalOddRank_of_quotient_frame {X H : Type} [Group X] [Finite X] [Group H]
    (ρ : X →* H) (hρ : Function.Surjective ρ) (hN : ¬ 5 ∣ Nat.card ρ.ker) {A : Subgroup H}
    (hA : IsElementaryAbelian 5 A) (hAcard : Nat.card A = 5 ^ 3) {r y : H} (hr : orderOf r = 2)
    (hrA : ∀ a ∈ A, a * r = r * a) (hy5 : y ^ 5 = 1) (hyA : y ∉ A)
    (hyA' : ∀ a ∈ A, y * a = a * y) (hyr : y * r = r * y) : 4 ≤ CFSG.twoLocalOddRank X := by
  classical
  have : Finite H := Finite.of_surjective ρ hρ
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hy1 : y ≠ 1 := fun h1 => hyA (h1 ▸ A.one_mem)
  have hyord : orderOf y = 5 := orderOf_eq_prime hy5 hy1
  have hzy : IsElementaryAbelian 5 (Subgroup.zpowers y) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hy5
  have hcommAy : ∀ a ∈ A, ∀ z ∈ Subgroup.zpowers y, a * z = z * a := by
    intro a ha z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    exact ((Commute.zpow_right (show Commute a y from (hyA' a ha).symm) i)).eq
  have hFel : IsElementaryAbelian 5 ↥(A ⊔ Subgroup.zpowers y) :=
    isElementaryAbelian_sup_of_commute hA hzy hcommAy
  have hzycard : Nat.card ↥(Subgroup.zpowers y) = 5 := by rw [Nat.card_zpowers, hyord]
  have hdisj : Subgroup.zpowers y ⊓ A = ⊥ := by
    have hd' : Nat.card ↥(Subgroup.zpowers y ⊓ A) ∣ 5 :=
      hzycard ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_five).1 hd' with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      apply hyA
      have e : Subgroup.zpowers y ⊓ A = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hzycard])
      have : y ∈ Subgroup.zpowers y ⊓ A := by
        rw [e]
        exact Subgroup.mem_zpowers y
      exact this.2
  have hFcard : Nat.card ↥(A ⊔ Subgroup.zpowers y) = 5 ^ 4 := by
    rw [sup_comm, card_sup_of_commute_disjoint (fun k hk l hl => (hcommAy l hl k hk).symm)
      (disjoint_iff.2 hdisj), hzycard, hAcard]
    ring
  obtain ⟨F, hFe, hFmap, hFdis⟩ :=
    Q1327C.exists_lift_elementary Nat.prime_five ρ hρ hN hFel
  have hFc : Nat.card F = 5 ^ 4 := by
    rw [← N143.card_map_of_disjoint_ker ρ hFdis, hFmap, hFcard]
  have hFp : IsPGroup 5 F := IsElementaryAbelian.isPGroup 5 F
  have hFr : ∀ u ∈ F, ρ u * r = r * ρ u := by
    intro u hu
    have hmem : ρ u ∈ A ⊔ Subgroup.zpowers y := hFmap ▸ Subgroup.mem_map_of_mem _ hu
    obtain ⟨a, ha, z, hz, hu'⟩ :=
      exists_mul_of_mem_sup_of_commute (fun k hk l hl => hcommAy k hk l hl) hmem
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [hu']
    have hya : Commute y r := hyr
    have h1 : (y ^ i) * r = r * y ^ i := (Commute.zpow_left hya i).eq
    calc a * y ^ i * r = a * (y ^ i * r) := by rw [mul_assoc]
      _ = a * (r * y ^ i) := by rw [h1]
      _ = (a * r) * y ^ i := by rw [← mul_assoc]
      _ = (r * a) * y ^ i := by rw [hrA a ha]
      _ = r * (a * y ^ i) := by rw [mul_assoc]
  set R : Subgroup X := (Subgroup.zpowers r).comap ρ with hR
  have hRcard : Nat.card R = Nat.card ρ.ker * 2 := by
    rw [hR, card_comap_of_surjective ρ hρ, Nat.card_zpowers, hr]
  have hRnorm : F ≤ Subgroup.normalizer (R : Set X) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hc : ∀ i : ℤ, ρ u * r ^ i * (ρ u)⁻¹ = r ^ i := fun i => by
      have : Commute (ρ u) (r ^ i) := (Commute.zpow_right (show Commute (ρ u) r from hFr u hu) i)
      rw [this.eq]
      group
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (show ρ x ∈ Subgroup.zpowers r from hx)
      show ρ (u * x * u⁻¹) ∈ Subgroup.zpowers r
      rw [map_mul, map_mul, map_inv, ← hi, hc i]
      exact Subgroup.zpow_mem_zpowers r i
    · intro hx
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1
        (show ρ (u * x * u⁻¹) ∈ Subgroup.zpowers r from hx)
      rw [map_mul, map_mul, map_inv] at hi
      have : ρ x = r ^ i := by
        have h1 : ρ u * ρ x * (ρ u)⁻¹ = r ^ i := hi.symm
        calc ρ x = (ρ u)⁻¹ * (ρ u * ρ x * (ρ u)⁻¹) * ρ u := by group
          _ = (ρ u)⁻¹ * r ^ i * ρ u := by rw [h1]
          _ = r ^ i := by
            have := hc i
            calc (ρ u)⁻¹ * r ^ i * ρ u = (ρ u)⁻¹ * (ρ u * r ^ i * (ρ u)⁻¹) * ρ u := by rw [this]
              _ = r ^ i := by group
      show ρ x ∈ Subgroup.zpowers r
      rw [this]
      exact Subgroup.zpow_mem_zpowers r i
  have hcop : Nat.Coprime 5 (Nat.card R) := by
    rw [hRcard]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hN)
      (by norm_num)
  obtain ⟨S, hS, hSN⟩ := CFSG.DihedralBlueprint.normalized_exists_sylow 5 2 Nat.prime_five
    Nat.prime_two F R hFp hRnorm hcop
  have hSne : S ≠ ⊥ := by
    intro hbot
    have h2 : 2 ∣ Nat.card R := by
      rw [hRcard]
      exact Dvd.intro_left _ rfl
    have : Finite R := inferInstance
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 h2
    have hzord : orderOf (z : X) = 2 := by rw [Subgroup.orderOf_coe, hz]
    have hQ2 : IsPGroup 2 (Subgroup.zpowers (z : X)) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hzord]
      norm_num
    have hQR : Subgroup.zpowers (z : X) ≤ R := Subgroup.zpowers_le.2 z.2
    have hSQ : S ≤ Subgroup.zpowers (z : X) := by
      rw [hbot]
      exact bot_le
    have hQ := hS.2.2 _ hQR hQ2 hSQ
    have hz1 : (z : X) = 1 := by
      have : (z : X) ∈ Subgroup.zpowers (z : X) := Subgroup.mem_zpowers _
      rw [hQ, hbot] at this
      exact this
    rw [hz1, orderOf_one] at hzord
    omega
  have h4 : 4 ≤ localRank 5 X :=
    CFSG.RankThree.Theta.le_localRank_of_le_normalizer (by norm_num) hSne hS.2.1
      hFe.toIsMulCommutative (fun w hw => elemPow_eq_one_of_isElementaryAbelian (A := F) w hw)
      hFc hSN
  exact Census3.four_le_twoLocalOddRank_of_localRank Nat.prime_five (by norm_num) h4

end CFSG.RankThree.PartOne.K133B
