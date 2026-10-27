module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourU3Model
public import CFSG.LocalAnalysis.WeakClosure81.W16LKInput
public import CFSG.LocalAnalysis.WeakClosure81.W16QTIX

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.CGT.PushingUpLit.CGT6 (cenS)
open Subgroup

section Certified


theorem w16l_mem_of_sq_eq_one_of_map_mem {Q Λ : Type} [Group Q] [Group Λ] (ρ : Q →* Λ)
    (hker : ρ.ker ≤ Subgroup.center Q) (hodd : Odd (Nat.card ρ.ker)) {N : Subgroup Q} {a : Q}
    (ha : a * a = 1) (hρ : ρ a ∈ N.map ρ) : a ∈ N := by
  obtain ⟨n, hnN, hnρ⟩ := hρ
  let z : Q := n⁻¹ * a
  have hzker : z ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    show ρ (n⁻¹ * a) = 1
    rw [map_mul, map_inv, hnρ, inv_mul_cancel]
  have hzcenter : z ∈ Subgroup.center Q := hker hzker
  have hza : a = n * z := by
    show a = n * (n⁻¹ * a)
    group
  have hcomm : n * z = z * n := Subgroup.mem_center_iff.mp hzcenter n
  have hsq : a * a = (n * n) * (z * z) := by
    rw [hza, ← pow_two, ← pow_two, ← pow_two]
    exact (show Commute n z from hcomm).mul_pow 2
  have hzz : z * z = (n * n)⁻¹ := by
    rw [hsq] at ha
    exact eq_inv_of_mul_eq_one_right ha
  have hzzN : z * z ∈ N := by
    rw [hzz]
    exact N.inv_mem (N.mul_mem hnN hnN)
  have hoddz : Odd (orderOf z) :=
    Odd.of_dvd_nat hodd (ρ.ker.orderOf_dvd_natCard hzker)
  obtain ⟨m, hm⟩ := hoddz
  have hpow : (z * z) ^ (m + 1) = z := by
    rw [← pow_two, ← pow_mul]
    have h2 : 2 * (m + 1) = orderOf z + 1 := by omega
    rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
  have hzN : z ∈ N := by
    have h := N.pow_mem hzzN (m + 1)
    rwa [hpow] at h
  rw [hza]
  exact N.mul_mem hnN hzN

theorem w16l_exists_sylow_cenS_eq_map {Q Λ : Type} [Group Q] [Finite Q] [Group Λ] (ρ : Q →* Λ)
    (hρ : Function.Surjective ρ) (hodd : Odd (Nat.card ρ.ker)) (S₁ : Sylow 2 Q) :
    ∃ S : Sylow 2 Λ, cenS S = (sylowCenter S₁).map ρ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Sylow.mapSurjective hρ S₁, ?_⟩
  have hcoe : ((Sylow.mapSurjective hρ S₁ : Sylow 2 Λ) : Subgroup Λ) =
      (S₁ : Subgroup Q).map ρ := Sylow.coe_mapSurjective hρ S₁
  ext x
  constructor
  · intro hx
    rw [CFSG.CGT.PushingUpLit.CGT6.mem_cenS] at hx
    obtain ⟨hxS, hxcomm⟩ := hx
    rw [hcoe] at hxS
    obtain ⟨y, hyS, rfl⟩ := Subgroup.mem_map.mp hxS
    refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
    rw [sylowCenter, Subgroup.mem_inf]
    refine ⟨hyS, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hzS
    have hker : (y * z)⁻¹ * (z * y) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      show ρ ((y * z)⁻¹ * (z * y)) = 1
      have h1 : ρ y * ρ z = ρ z * ρ y :=
        hxcomm (ρ z) (by rw [hcoe]; exact Subgroup.mem_map_of_mem ρ hzS)
      rw [map_mul, map_inv, map_mul, map_mul, h1, inv_mul_cancel]
    have hmem : (y * z)⁻¹ * (z * y) ∈ (S₁ : Subgroup Q) ⊓ ρ.ker :=
      Subgroup.mem_inf.mpr ⟨(S₁ : Subgroup Q).mul_mem
        ((S₁ : Subgroup Q).inv_mem ((S₁ : Subgroup Q).mul_mem hyS hzS))
        ((S₁ : Subgroup Q).mul_mem hzS hyS), hker⟩
    have hbot : (y * z)⁻¹ * (z * y) = 1 := by
      have h := hmem
      rw [CFSG.RankThree.OddKernel.inf_eq_bot_of_odd S₁.isPGroup' hodd,
        Subgroup.mem_bot] at h
      exact h
    exact (inv_mul_eq_one.mp hbot).symm
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [CFSG.CGT.PushingUpLit.CGT6.mem_cenS]
    refine ⟨?_, ?_⟩
    · rw [hcoe]
      exact Subgroup.mem_map_of_mem ρ (Subgroup.mem_inf.mp hy).1
    · intro w hw
      rw [hcoe] at hw
      obtain ⟨z, hzS, rfl⟩ := Subgroup.mem_map.mp hw
      have hyc : y ∈ Subgroup.centralizer ((S₁ : Subgroup Q) : Set Q) :=
        (Subgroup.mem_inf.mp hy).2
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hyc z hzS]

theorem w16l_card_map_sup_root {Q Λ : Type} [Group Q] [Finite Q] [Group Λ] (ρ : Q →* Λ)
    (hker : ρ.ker ≤ Subgroup.center Q) {n : ℕ} (hX : IsU3Shape Q n) {R : Subgroup Q}
    (hR : IsElemAbelian 2 R) (hRc : Nat.card R = 2 ^ n) {g : Q}
    (hg : CFSG.Quasithin.conjSubgroup R g ≠ R) :
    Nat.card ↥((R ⊔ CFSG.Quasithin.conjSubgroup R g).map ρ) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  let L : Subgroup Q := R ⊔ CFSG.Quasithin.conjSubgroup R g
  have hn : 1 < n := by
    have h2 : 2 ≤ n := by
      obtain ⟨⟨-, hf, -, hne⟩, -⟩ :=
        CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hX.2.1
      by_contra hlt
      have hn1 : n = 1 := by omega
      subst hn1
      exact hne rfl
    omega
  have hK := kGroup1616Input_holds
  have hne : CFSG.Quasithin.conjSubgroup R 1 ≠ CFSG.Quasithin.conjSubgroup R g := by
    rw [CFSG.Quasithin.conjSubgroup_one]
    exact fun h => hg h.symm
  have hpair := isL2Pair_conj (X := Q) hK hn hX hR hRc (x := 1) (y := g) hne
  have hpair' : CFSG.CGT.Timmesfeld75.IsL2Pair ↥(R ⊔ CFSG.Quasithin.conjSubgroup R g)
      (R.subgroupOf (R ⊔ CFSG.Quasithin.conjSubgroup R g)) (2 ^ n) := by
    rw [CFSG.Quasithin.conjSubgroup_one] at hpair
    exact hpair
  have hbot : L ⊓ ρ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxL, hxker⟩ := hx
    rw [Subgroup.mem_bot]
    have hxcen : x ∈ Subgroup.center Q := hker hxker
    obtain ⟨F, hF, hFin, hChar, e, hq, hSmap, hSsym, hmemS, hmemN⟩ := hpair'.exists_data
    letI : Field F := hF
    letI : Finite F := hFin
    letI : CharP F 2 := hChar
    have hxcenter : e ⟨x, hxL⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [Subgroup.mem_center_iff]
      intro A
      obtain ⟨y, rfl⟩ := e.surjective A
      show e y * e ⟨x, hxL⟩ = e ⟨x, hxL⟩ * e y
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (Subgroup.mem_center_iff.mp hxcen (y : Q)))
    have hx1 : e ⟨x, hxL⟩ = 1 := by
      have h := hxcenter
      rw [CFSG.CGT.Timmesfeld75.center_sl2_eq_bot (F := F), Subgroup.mem_bot] at h
      exact h
    have hsub : (⟨x, hxL⟩ : ↥L) = 1 := e.injective (by rw [hx1, map_one])
    exact congrArg Subtype.val hsub
  rw [CFSG.card_map_eq_card_of_inf_ker_eq_bot ρ hbot]
  exact hpair'.card_eq_mul

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end