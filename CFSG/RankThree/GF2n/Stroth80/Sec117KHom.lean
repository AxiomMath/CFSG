module

public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import CFSG.RankThree.OddKernel.OddLift
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCLinearDegree

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

private theorem hom_eq_one_of_map_ker_eq_top_of_odd {X H : Type*} [Group X] [Group H]
    [Finite X] (hodd : Odd (Nat.card (Subgroup.center X))) {S : Set X}
    (hS : Subgroup.closure S = ⊤) (hS2 : ∀ s ∈ S, s ^ 2 = 1) (f : X →* H)
    (h : f.ker.map (QuotientGroup.mk' (Subgroup.center X)) = ⊤) : f = 1 := by
  have hs : ∀ s ∈ S, f s = 1 := by
    intro s hs
    have hmem : QuotientGroup.mk' (Subgroup.center X) s ∈
        f.ker.map (QuotientGroup.mk' (Subgroup.center X)) := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, hks⟩ := Subgroup.mem_map.mp hmem
    have hz : k⁻¹ * s ∈ Subgroup.center X := QuotientGroup.eq.mp hks
    have hfs : f s = f (k⁻¹ * s) := by
      rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, one_mul]
    have h1 : orderOf (f s) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hS2 s hs, map_one])
    have h2 : orderOf (f s) ∣ Nat.card (Subgroup.center X) := by
      rw [hfs]
      exact (orderOf_map_dvd f _).trans (Subgroup.orderOf_dvd_natCard _ hz)
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hodd) h1 h2)
  have hle : Subgroup.closure S ≤ f.ker :=
    (Subgroup.closure_le _).mpr fun s hs' => MonoidHom.mem_ker.mpr (hs s hs')
  rw [hS] at hle
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.one_apply]
  exact MonoidHom.mem_ker.mp (hle (Subgroup.mem_top g))

private theorem Ctx.ker_le_center_or_eq_one [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) (hX : IsSimpleGroup (XbarMod M Q Z B))
    {H : Type*} [Group H] (ρ : ↥(Xbar M Q Z B) →* H) :
    ρ.ker ≤ Subgroup.center ↥(Xbar M Q Z B) ∨ ρ = 1 := by
  have hN : (ρ.ker.map (QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B)))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (ρ.ker.map (QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B)))) with hbot | htop
  · left
    intro g hg
    have hmem : QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B)) g ∈
        ρ.ker.map (QuotientGroup.mk' (Subgroup.center ↥(Xbar M Q Z B))) :=
      Subgroup.mem_map_of_mem _ hg
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact hmem
  · right
    refine hom_eq_one_of_map_ker_eq_top_of_odd hc.odd_card_center_Xbar
      (S := ((↑) : ↥(Xbar M Q Z B) → Mbar M Q) ⁻¹' Ebar M Q Z B)
      Subgroup.closure_closure_coe_preimage (fun s hs => ?_) ρ htop
    have h2 : orderOf (s : Mbar M Q) = 2 := Ctx.orderOf_eq_two_of_mem_Ebar hs
    rw [Subgroup.orderOf_coe] at h2
    rw [← h2]
    exact pow_orderOf_eq_one s

private theorem card_quotient_center_dvd_of_ker_le {X H : Type*} [Group X] [Group H]
    (f : X →* H) (h : f.ker ≤ Subgroup.center X) :
    Nat.card (X ⧸ Subgroup.center X) ∣ Nat.card H := by
  have hsurj : Function.Surjective
      (QuotientGroup.map f.ker (Subgroup.center X) (MonoidHom.id X) h) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨g, rfl⟩
  have h2 : Nat.card (X ⧸ f.ker) ∣ Nat.card H := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  exact (Subgroup.card_dvd_of_surjective (hf := hsurj)).trans h2

theorem Ctx.hom_eq_one_of_prime_dvd [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) (hX : IsSimpleGroup (XbarMod M Q Z B))
    {ℓ : ℕ} (hℓX : ℓ ∣ Nat.card (XbarMod M Q Z B)) {H : Type} [Group H]
    (hℓH : ¬ ℓ ∣ Nat.card H) (ρ : ↥(Xbar M Q Z B) →* H) : ρ = 1 := by
  rcases hc.ker_le_center_or_eq_one hX ρ with h | h
  · exact absurd (hℓX.trans (card_quotient_center_dvd_of_ker_le ρ h)) hℓH
  · exact h

private theorem exists_orderOf_eq_eight_of_mk {X : Type*} [Group X] [Finite X]
    (hodd : Odd (Nat.card (Subgroup.center X))) {g : X ⧸ Subgroup.center X}
    (hg : orderOf g = 8) : ∃ y : X, orderOf y = 8 := by
  have hE : IsPGroup 2 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 3) (by rw [Nat.card_zpowers, hg]; norm_num)
  obtain ⟨A, -, hAE, hinj⟩ := CFSG.RankThree.OddKernel.exists_two_subgroup_map_eq
    (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _)
    (by rwa [QuotientGroup.ker_mk']) (Subgroup.zpowers g) hE
  have hgA : g ∈ A.map (QuotientGroup.mk' (Subgroup.center X)) := by
    rw [hAE]
    exact Subgroup.mem_zpowers g
  obtain ⟨y, hyA, hyg⟩ := Subgroup.mem_map.mp hgA
  refine ⟨y, ?_⟩
  have h1 := orderOf_injective _ hinj ⟨y, hyA⟩
  rw [MonoidHom.comp_apply, Subgroup.subtype_apply, hyg, hg, Subgroup.orderOf_mk] at h1
  exact h1.symm

theorem Ctx.hom_eq_one_of_orderOf_eq_eight [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) (hX : IsSimpleGroup (XbarMod M Q Z B))
    {g : XbarMod M Q Z B} (hg : orderOf g = 8) {K : Type} [Field K] [Finite K] [CharP K 2]
    {k : ℕ} (hk : k ≤ 3) (ρ : ↥(Xbar M Q Z B) →* GL (Fin k) K) : ρ = 1 := by
  rcases hc.ker_le_center_or_eq_one hX ρ with h | h
  · exfalso
    have hodd := hc.odd_card_center_Xbar
    obtain ⟨y, hy⟩ := exists_orderOf_eq_eight_of_mk hodd hg
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    ·
      have hyZ : y ∈ Subgroup.center ↥(Xbar M Q Z B) :=
        h (MonoidHom.mem_ker.mpr (Units.ext (Matrix.ext fun i => i.elim0)))
      have h8 := Subgroup.orderOf_dvd_natCard _ hyZ
      rw [hy] at h8
      exact (Nat.not_even_iff_odd.mpr hodd)
        (even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 8).trans h8))
    · have hρ8 : ρ y ^ 2 ^ 3 = 1 := by
        rw [← map_pow, show 2 ^ 3 = orderOf y by rw [hy]; norm_num, pow_orderOf_eq_one, map_one]
      have hρ4 := CFSG.ComponentClassification.UnbalancedGS.LinearDegree.pow_two_pow_eq_one_of_le
        hk0 hρ8 (j := 2) (by omega)
      have hyZ : y ^ 4 ∈ Subgroup.center ↥(Xbar M Q Z B) :=
        h (MonoidHom.mem_ker.mpr (by rw [map_pow]; simpa using hρ4))
      have h4 : orderOf (y ^ 4) = 2 := by
        refine orderOf_eq_prime ?_ ?_
        · rw [← pow_mul, show 4 * 2 = orderOf y by rw [hy], pow_orderOf_eq_one]
        · intro h1
          have := orderOf_dvd_of_pow_eq_one h1
          rw [hy] at this
          norm_num at this
      have h2 := Subgroup.orderOf_dvd_natCard _ hyZ
      rw [h4] at h2
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  · exact h

end CFSG.RankThree.GF2n.Stroth80
