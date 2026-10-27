module

public import CFSG.Quasithin.Vol2.Ch11SecA15GO4
public import CFSG.GH74.Uniqueness.SU.SU2Step3c

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.GH74.Uniqueness.SU CFSG.GH74.Uniqueness.SU.SU2
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace OnanData

variable {Z Y T V₁ C : Subgroup G} {d : G}

theorem dichotomy (D : OnanData Z Y T V₁ C d) :
    Y ≤ Subgroup.normalizer (C : Set G) ∨ T ≤ Subgroup.centralizer (Z : Set G) := by
  classical
  have hGO := D.goPair
  have hO := GOPair.onan hGO
  have hfix := D.fixSub_eq
  set ρ' : ↥Y →* ↥(onanX Z Y D.YZ) := (onanRho Z Y D.YZ).rangeRestrict with hρ'
  have hρ's : Function.Surjective ρ' := (onanRho Z Y D.YZ).rangeRestrict_surjective
  have hρy : ∀ y : ↥Y, ρ' y = D.ystar y := fun y => rfl
  set Ts := (T.subgroupOf Y).map ρ' with hTs
  have hstab : ∀ y : ↥Y, ρ' y • fixSub ↥Z (Subgroup.zpowers D.dstar) =
      fixSub ↥Z (Subgroup.zpowers D.dstar) ↔ C.map (MulAut.conj (y : G)).toMonoidHom = C := by
    intro y
    rw [hfix, hρy]
    exact D.smul_eq_iff y
  have hTsle : Ts ≤ MulAction.stabilizer ↥(onanX Z Y D.YZ)
      (fixSub ↥Z (Subgroup.zpowers D.dstar)) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [MulAction.mem_stabilizer_iff, hstab]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).mp (D.TC (Subgroup.mem_subgroupOf.mp ht))
  have hodd : Odd (SU2.omega ↥Z (Subgroup.zpowers D.dstar)).ncard := by
    rw [SU2.omega]
    erw [← MulAction.index_stabilizer]
    have h1 := Subgroup.index_dvd_of_le hTsle
    have h2 := Subgroup.index_map_dvd (T.subgroupOf Y) hρ's
    rw [← Subgroup.relIndex] at h2
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => D.Todd (h.trans (h1.trans h2)))
  have hfne : fixSub ↥Z (Subgroup.zpowers D.dstar) ≠ SU2.commSub ↥Z (Subgroup.zpowers D.dstar) := by
    intro heq
    apply hGO.fixSub_ne_bot
    have := hGO.commSub_inf_fixSub'
    rwa [← heq, inf_idem] at this
  rcases hO with ⟨-, hinv⟩ | ⟨hΩ, -⟩ | ⟨hΩ, -, -⟩ | ⟨-, -, h21, -⟩
  ·
    left
    intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact (hstab ⟨y, hy⟩).mp (hinv (ρ' ⟨y, hy⟩))
  ·
    rw [hΩ, Set.ncard_pair hfne] at hodd
    exact absurd hodd (by decide)
  ·
    exfalso
    have hlt : shapeK ↥Z (Subgroup.zpowers D.dstar) < shapeN ↥Z := by
      have hne : fixSub ↥Z (Subgroup.zpowers D.dstar) < ⊤ := by
        refine lt_top_iff_ne_top.mpr fun htop => ?_
        obtain ⟨v₀, hv₀, -, -, hv₀C, -, -⟩ := D.three
        have : (⟨v₀, D.VZ hv₀⟩ : ↥Z) ∈ fixSub ↥Z (Subgroup.zpowers D.dstar) := htop ▸ trivial
        rw [hfix, Subgroup.mem_subgroupOf] at this
        exact hv₀C this
      have hc := Subgroup.card_lt_of_lt hne
      rw [Subgroup.card_top, hGO.card_V, hGO.card_fixSub] at hc
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hc
    rw [hΩ] at hodd
    obtain ⟨j, hj⟩ : ∃ j, shapeN ↥Z - shapeK ↥Z (Subgroup.zpowers D.dstar) = j + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt hlt)).symm⟩
    rw [hj, pow_succ] at hodd
    exact Nat.not_even_iff_odd.mpr hodd (even_two.mul_left _)
  ·
    right
    have hTs2 : IsPGroup 2 ↥Ts := by
      have : IsPGroup 2 ↥(T.subgroupOf Y) :=
        D.T2.of_equiv (Subgroup.subgroupOfEquivOfLe D.TY).symm
      exact this.map ρ'
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hTs2)
    have hdvd := Subgroup.card_subgroup_dvd_card Ts
    rw [hk, h21] at hdvd
    have hk0 : k = 0 := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · exact h0
      · exfalso
        have : 2 ∣ 21 := (dvd_pow_self 2 hpos.ne').trans hdvd
        omega
    rw [hk0, pow_zero, Subgroup.card_eq_one] at hk
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 : ρ' ⟨t, D.TY ht⟩ = 1 := by
      have : ρ' ⟨t, D.TY ht⟩ ∈ Ts := ⟨⟨t, D.TY ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
      rw [hk] at this
      exact this
    have h2 : t * v * t⁻¹ = v := by
      have := congrArg (fun x : ↥(onanX Z Y D.YZ) => (((x : MulAut ↥Z) ⟨v, hv⟩ : ↥Z) : G)) h1
      simpa [hρy, ystar, onanRho_apply_coe] using this
    calc v * t = t * v * t⁻¹ * t := by rw [h2]
      _ = t * v := by group

end OnanData

end CFSG.Quasithin.Vol2.Ch11.SecA
