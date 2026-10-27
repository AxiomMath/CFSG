module

public import CFSG.Quasithin.Background.A3Structure320Radical
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.A3Structure320Basic

public section

namespace CFSG.Quasithin

namespace A320

open CFSG.Open CFSG.SectionRank
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

@[expose] def RadicalShape (L : Subgroup G) : Prop :=
  ¬ 3 ∣ Nat.card (solvRad L) ∨ (Nat.card (solvRad L) = 3 ∧ ⁅solvRad L, L⁆ = ⊥)

omit [Finite G] in
theorem zpowers_inf_radical {L : Subgroup G} {x : G} (hx : orderOf x = 3)
    (hxR : x ∉ solvRad L) {y : G} (hy : y ∈ Subgroup.zpowers x) (hyR : y ∈ solvRad L) :
    y = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hy1
  exact hxR ((Subgroup.zpowers_le.2 hyR) (mem_zpowers_of_mem_zpowers_prime hx hy hy1))

omit [Finite G] in
theorem isElemAbelian_zpowers {p : ℕ} {x : G} (hx : x ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

theorem pRank_centralizer_le {L : Subgroup G} [L.Normal] (hL : L ∈ cComp (⊤ : Subgroup G))
    (hG : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 2) (hR : RadicalShape L)
    (h3 : 1 ≤ CFSG.Open.pRank 3 L) : CFSG.Open.pRank 3 (centralizerModSolvRad L) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (solvRad L).Normal := solvRad_normal_of_normal L
  by_contra hcon
  push Not at hcon
  obtain ⟨E, hEC, hEel, hEcard⟩ := exists_pRank (p := 3) (by norm_num) (centralizerModSolvRad L)
  have hinfL := centralizerModSolvRad_inf_le hL
  rcases hR with hR3 | ⟨hR3, hRc⟩
  ·
    obtain ⟨X, hXL, hXel, hXcard⟩ := exists_subgroup_card_prime (p := 3) h3
    have hmain := pRank_add_le (solvRad L) hR3 hXel hEel
      (fun x hx e he => by
        rw [← commutatorElement_inv]
        exact Subgroup.inv_mem _ ((hEC he).2 x (hXL hx)))
      (fun x hx e he hxe => by
        have heL : e ∈ L := by
          have : e = x⁻¹ * (x * e) := by group
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hXL hx)) (solvRad_le L hxe)
        have heR : e ∈ solvRad L := hinfL ⟨hEC he, heL⟩
        have hxR : x ∈ solvRad L := by
          have : x = (x * e) * e⁻¹ := by group
          rw [this]
          exact Subgroup.mul_mem _ hxe (Subgroup.inv_mem _ heR)
        exact ⟨eq_one_of_pow_eq_one_of_not_dvd hR3 hxR (hXel.2 x hx),
          eq_one_of_pow_eq_one_of_not_dvd hR3 heR (hEel.2 e he)⟩)
      (a := 1) (b := CFSG.Open.pRank 3 (centralizerModSolvRad L)) (by simpa using hXcard) hEcard
    omega
  ·
    have hperf := perfect_of_mem_cComp hL
    have hperfL : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ :=
      A36A.top_commutator_of_mem_cComp hL
    have hZc : (solvRad L).subgroupOf L ≤ Subgroup.center ↥L := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : ⁅(z : G), (g : G)⁆ ∈ (⊥ : Subgroup G) :=
        hRc ▸ Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.1 hz) g.2
      have h2 : ⁅z, g⁆ = 1 := Subtype.ext (Subgroup.mem_bot.1 h1)
      exact (commutatorElement_eq_one_iff_mul_comm.1 h2).symm
    have hZ : Nat.card ((solvRad L).subgroupOf L) = 3 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (solvRad_le L)).toEquiv).trans hR3
    obtain ⟨x, hx3, hxZ⟩ := exists_orderOf_eq_three_not_mem hperfL hZc hZ
    have hxR : (x : G) ∉ solvRad L := fun h => hxZ (Subgroup.mem_subgroupOf.2 h)
    have hxo : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx3
    have hxL : (x : G) ∈ L := x.2
    have hxp : (x : G) ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one _
    have hmain := pRank_add_le (⊥ : Subgroup G) (by simp) (isElemAbelian_zpowers hxp) hEel
      (fun y hy e he => by
        have hyL : y ∈ L := (Subgroup.zpowers_le.2 hxL) hy
        have h1 := centralizes_of_central_radical hperf hRc (hEC he) hyL
        rw [← commutatorElement_inv, h1, inv_one]
        exact Subgroup.one_mem _)
      (fun y hy e he hye => by
        have hye1 : y * e = 1 := Subgroup.mem_bot.1 hye
        have hyL : y ∈ L := (Subgroup.zpowers_le.2 hxL) hy
        have hye' : y = e⁻¹ := eq_inv_of_mul_eq_one_left hye1
        have heL : e ∈ L := by
          have : e = y⁻¹ := (inv_eq_of_mul_eq_one_right hye1).symm
          rw [this]
          exact Subgroup.inv_mem _ hyL
        have heR : e ∈ solvRad L := hinfL ⟨hEC he, heL⟩
        have hyR : y ∈ solvRad L := by
          rw [hye']
          exact Subgroup.inv_mem _ heR
        have hy1 := zpowers_inf_radical hxo hxR hy hyR
        rw [hy1, one_mul] at hye1
        exact ⟨hy1, hye1⟩)
      (a := 1) (b := CFSG.Open.pRank 3 (centralizerModSolvRad L))
      (by simp [Nat.card_zpowers, hxo]) hEcard
    omega

theorem no_s3_of_centralizer {L : Subgroup G} [L.Normal] (hL : L ∈ cComp (⊤ : Subgroup G))
    (hG : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 2) (hR : RadicalShape L)
    (hL2 : CFSG.Open.pRank 3 L = 2) {K : Type*} [Group K] [Finite K] (f : K →* G)
    (hfker : ∀ x ∈ f.ker, ¬ 3 ∣ orderOf x) (hfC : ∀ k : K, f k ∈ centralizerModSolvRad L)
    (ρ : K →* Equiv.Perm (Fin 3)) (hρ : Function.Surjective ρ) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (solvRad L).Normal := solvRad_normal_of_normal L
  obtain ⟨E, hEL, hEel, hEcard⟩ := exists_pRank (p := 3) (by norm_num) L
  rw [hL2] at hEcard
  have hinfL := centralizerModSolvRad_inf_le hL
  have hord : ∀ y : K, orderOf y = 3 → orderOf (f y) = 3 := by
    intro y hy
    have h1 : (f y) ^ 3 = 1 := by rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
    have h2 : f y ≠ 1 := fun h => hfker y (MonoidHom.mem_ker.2 h) (by rw [hy])
    exact orderOf_eq_prime h1 h2
  obtain ⟨y, hy3⟩ := exists_orderOf_eq_three_of_surjective ρ hρ
  have hfy := hord y hy3
  rcases hR with hR3 | ⟨hR3, hRc⟩
  ·
    have hxp : (f y) ^ 3 = 1 := by rw [← hfy]; exact pow_orderOf_eq_one _
    have hmain := pRank_add_le (solvRad L) hR3 (X := Subgroup.zpowers (f y)) (E := E)
      (isElemAbelian_zpowers hxp) hEel
      (fun x hx e he => ((Subgroup.zpowers_le.2 (hfC y)) hx).2 e (hEL he))
      (fun x hx e he hxe => by
        have hxC := (Subgroup.zpowers_le.2 (hfC y)) hx
        have hxL : x ∈ L := by
          have : x = (x * e) * e⁻¹ := by group
          rw [this]
          exact Subgroup.mul_mem _ (solvRad_le L hxe) (Subgroup.inv_mem _ (hEL he))
        have hxR : x ∈ solvRad L := hinfL ⟨hxC, hxL⟩
        have hx1 := eq_one_of_pow_eq_one_of_not_dvd hR3 hxR
          ((isElemAbelian_zpowers hxp).2 x hx)
        rw [hx1, one_mul] at hxe
        exact ⟨hx1, eq_one_of_pow_eq_one_of_not_dvd hR3 hxe (hEel.2 e he)⟩)
      (a := 1) (b := 2) (by simp [Nat.card_zpowers, hfy]) hEcard
    omega
  ·
    have hperf := perfect_of_mem_cComp hL
    have hcent : ∀ k : K, ∀ z ∈ solvRad L, f k * z = z * f k := fun k z hz =>
      commutatorElement_eq_one_iff_mul_comm.1
        (centralizes_of_central_radical hperf hRc (hfC k) (solvRad_le L hz))
    have hU : ∀ y' : K, orderOf y' = 3 → f y' ∈ solvRad L := by
      intro y' hy'
      have hfy' := hord y' hy'
      have hxp : (f y') ^ 3 = 1 := by rw [← hfy']; exact pow_orderOf_eq_one _
      by_contra hnot
      have hmain := pRank_add_le (⊥ : Subgroup G) (by simp) (X := Subgroup.zpowers (f y'))
        (E := E) (isElemAbelian_zpowers hxp) hEel
        (fun x hx e he => by
          have hxC := (Subgroup.zpowers_le.2 (hfC y')) hx
          have h1 := centralizes_of_central_radical hperf hRc hxC (hEL he)
          rw [h1]
          exact Subgroup.one_mem _)
        (fun x hx e he hxe => by
          have hxe1 : x * e = 1 := Subgroup.mem_bot.1 hxe
          have hxC := (Subgroup.zpowers_le.2 (hfC y')) hx
          have hxL : x ∈ L := by
            have : x = e⁻¹ := eq_inv_of_mul_eq_one_left hxe1
            rw [this]
            exact Subgroup.inv_mem _ (hEL he)
          have hxR : x ∈ solvRad L := hinfL ⟨hxC, hxL⟩
          have hx1 := zpowers_inf_radical hfy' hnot hx hxR
          rw [hx1, one_mul] at hxe1
          exact ⟨hx1, hxe1⟩)
        (a := 1) (b := 2) (by simp [Nat.card_zpowers, hfy']) hEcard
      omega
    exact no_s3_section_of_hom f hfker hR3 hcent hU ρ hρ

end A320

end CFSG.Quasithin
