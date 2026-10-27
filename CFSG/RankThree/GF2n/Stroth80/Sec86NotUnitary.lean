module

public import CFSG.RankThree.GF2n.Stroth80.Sec86UnitaryAbstract
public import CFSG.RankThree.GF2n.Stroth80.Sec84InputStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec85F2
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem step86NotUnitary_of (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (hA : Sec8AExistsStatement) (h83 : Stroth83Statement) (hirr : Sec86IrredStatement)
    (hOut : PSU6OutSolvableStatement) (hTwo : PSU6TwoPartStatement) :
    Step86NotUnitaryStatement := by
  classical
  intro G _ _ M Q Z B _ hc n t hs hU
  have h5 := hs.toSec5
  have ht : t ∈ LB M Q B := h5.mem
  obtain ⟨m0, hm0, hmSp0⟩ := hs.sp
  have hC83 := h83 G M Q Z B hc n t h5 ⟨m0, hm0, hmSp0⟩
  obtain ⟨m, e, hm2, hmSp, hNcardZ, hme, he⟩ : ∃ m e : ℕ, 2 ≤ m ∧ SpMNat hc t m ∧
      Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ (e + 1) ∧ 15 < m ^ 2 + e ∧ 1 ≤ e := by
    rcases hC83 with ⟨-, hsp3, hN9⟩ | ⟨-, hsp4, hN17⟩
    · exact ⟨3, 8, by norm_num, hsp3, hN9, by norm_num, by norm_num⟩
    · exact ⟨4, 16, by norm_num, hsp4, hN17, by norm_num, by norm_num⟩
  obtain ⟨jj, kk0, hZ2, -⟩ := hc.hyp.cp
  have hZ4 : 4 ≤ 2 ^ jj := hZ2 ▸ hc.hyp.q4
  have hf : 2 ≤ jj := by
    by_contra hlt
    have hj1 : jj ≤ 1 := by omega
    interval_cases jj <;> norm_num at hZ4
  obtain ⟨K, fK, finK, hKZ, hnat⟩ := hmSp
  obtain ⟨φ, hφr, hφk, -⟩ := hnat
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKZ.trans hZ2)
  have hK4 : 4 ≤ Nat.card K := by rw [hKZ]; exact hc.hyp.q4
  obtain ⟨hSimple, h16, -⟩ := endg_sp_facts hK4 hm2
  obtain ⟨o₁, ho₁, hSp⟩ := exists_odd_card_statedSp (K := K) (f := jj) (by omega)
    (hKZ.trans hZ2) m
  have hU' : IsPSUModel 6 (2 ^ jj) ↥(generalizedFitting ↥(bar M Q (H0 M Z))) := by
    have h1 : IsPSUModel 6 (Nat.card Z) ↥(generalizedFitting ↥(bar M Q (H0 M Z))) := hU
    rwa [hZ2] at h1
  obtain ⟨o₂, ho₂, hFord⟩ := hTwo jj _ (by omega) hU'
  haveI hFnormal : (generalizedFitting ↥(bar M Q (H0 M Z))).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic).2
  have hsolv : IsSolvable (↥(bar M Q (H0 M Z)) ⧸ generalizedFitting ↥(bar M Q (H0 M Z))) :=
    hOut (Nat.card Z) _ _ hU (CFSG.centralizer_generalizedFitting_le _)
  obtain ⟨Z0, hZ0⟩ := hc.exists_centre ht
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun y hy => (Ctx.mem_CN.1 hy).1
  have hQN : Q ≤ hc.CN t := sec8_Q_le_CN hc ht
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hZ0N : Z0 ≤ hc.CN t := sec8_Z0_le_CN hc hs hZ0
  have hnormR : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have hN2 : IsPGroup 2 ↥(hc.CN t) := sec8_isPGroup_CN h34 h51 hA hc hs hZ0
  obtain ⟨kk, hQcard⟩ := (hN2.to_le hQN).exists_card_eq
  have hNcard : Nat.card ↥(hc.CN t) = Nat.card ↥Q * (2 ^ jj) ^ (e + 1) := by
    rw [hNcardZ, hZ2]
  have hZ0card : Nat.card ↥Z0 = Nat.card ↥Q * 2 ^ jj := by
    rw [sec86ZCard_of_51 h51 hA G M Q Z B hc n t hs Z0 hZ0, hZ2]
  have hirrC := hirr G M Q Z B hc n t hs Z0 hZ0
  let θ0 : ↥(Rt M (LB M Q B) t) →* Mbar M Q :=
    (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hRM)
  have hθ0 : ∀ r : ↥(Rt M (LB M Q B) t), θ0 r ∈ bar M Q (H0 M Z) := fun r =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hc.Rt_le_H0 t r.2))
  let θ : ↥(Rt M (LB M Q B) t) →* ↥(bar M Q (H0 M Z)) := θ0.codRestrict _ hθ0
  have hθ : ∀ r : ↥(Rt M (LB M Q B) t), θ r = 1 ↔ (r : G) ∈ Q := by
    intro r
    have h1 : θ r = 1 ↔ θ0 r = 1 := by
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [h1]
    exact (QuotientGroup.eq_one_iff (N := Q.subgroupOf M) (Subgroup.inclusion hRM r)).trans
      Subgroup.mem_subgroupOf
  let π : ↥(Rt M (LB M Q B) t) →* ↥(CFSG.Open.StatedSp m K) :=
    (MulEquiv.subgroupCongr hφr).toMonoidHom.comp φ.rangeRestrict
  have hπ : Function.Surjective π :=
    (MulEquiv.subgroupCongr hφr).surjective.comp (MonoidHom.rangeRestrict_surjective φ)
  have hπN : ∀ r : ↥(Rt M (LB M Q B) t), π r = 1 ↔ (r : G) ∈ hc.CN t := by
    intro r
    show (MulEquiv.subgroupCongr hφr) (φ.rangeRestrict r) = 1 ↔ _
    rw [map_eq_one_iff _ (MulEquiv.subgroupCongr hφr).injective]
    have h1 : φ.rangeRestrict r = 1 ↔ φ r = 1 := by
      rw [← Subtype.coe_inj]
      rfl
    rw [h1, ← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
  have hS : ¬ IsSolvable ↥(CFSG.Open.StatedSp m K) := not_isSolvable_of_simple_of_dvd h16
  exact step86_abstract hQZ0 hZ0N hNR (fun r hr x hx => hc.CN_conj_mem ht hr hx)
    (fun r hr z hz => (Subgroup.mem_normalizer_iff.mp (hZ0.mem_normalizer hnormR hr) z).mp hz)
    hirrC hN2 hf he hQcard hNcard hZ0card θ hθ hsolv π hπ hπN hS hSp ho₁ hFord ho₂ hme

end CFSG.RankThree.GF2n.Stroth80
