module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.RankThree.PartTwo.Sec4.Hering432

variable {L : Type*} [Group L] [Finite L]

theorem exists_sylow_ge_le_normalizer_aux {Z : Subgroup L} (hZ3 : Nat.card Z = 3)
    (hwc : ∀ g : L, Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set L) →
      Z.map (MulAut.conj g).toMonoidHom = Z) :
    ∃ P : Sylow 3 L, Z ≤ (P : Subgroup L) ∧
      (P : Subgroup L) ≤ Subgroup.normalizer (Z : Set L) := by
  classical
  have hmemN : ∀ g : L, g ∈ Subgroup.normalizer (Z : Set L) ↔
      ∀ h : L, h ∈ Z ↔ g * h * g⁻¹ ∈ Z := fun g => Subgroup.mem_normalizer_iff
  have hZN : Z ≤ Subgroup.normalizer (Z : Set L) := Subgroup.le_normalizer
  have hZsub : IsPGroup 3 (Z.subgroupOf (Subgroup.normalizer (Z : Set L))) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv, hZ3, pow_one]
  haveI hZnorm : (Z.subgroupOf (Subgroup.normalizer (Z : Set L))).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact ((hmemN (g : L)).mp g.2 (n : L)).mp hn⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 3 (Subgroup.normalizer (Z : Set L))) := inferInstance
  obtain ⟨P, hPQ⟩ := Sylow.exists_comap_subtype_eq Q
  have hPmem : ∀ g : Subgroup.normalizer (Z : Set L),
      (g : L) ∈ (P : Subgroup L) ↔ g ∈ (Q : Subgroup (Subgroup.normalizer (Z : Set L))) := by
    intro g
    rw [← hPQ]
    exact Iff.rfl
  have hZQ : Z.subgroupOf (Subgroup.normalizer (Z : Set L)) ≤
      (Q : Subgroup (Subgroup.normalizer (Z : Set L))) :=
    IsPGroup.le_sylow_of_normal hZsub Q
  have hZP : Z ≤ (P : Subgroup L) := by
    intro z hz
    have hzN : z ∈ Subgroup.normalizer (Z : Set L) := hZN hz
    have hmem : (⟨z, hzN⟩ : ↥(Subgroup.normalizer (Z : Set L))) ∈
        Z.subgroupOf (Subgroup.normalizer (Z : Set L)) := Subgroup.mem_subgroupOf.mpr hz
    exact (hPmem ⟨z, hzN⟩).mpr (hZQ hmem)
  refine ⟨P, hZP, ?_⟩
  by_contra hPN
  obtain ⟨R, hRmem⟩ : ∃ R : Subgroup L, ∀ g : L, g ∈ R ↔
      g ∈ (P : Subgroup L) ∧ g ∈ Subgroup.normalizer (Z : Set L) :=
    ⟨(P : Subgroup L) ⊓ Subgroup.normalizer (Z : Set L), fun g => Subgroup.mem_inf⟩
  have hRP : R < (P : Subgroup L) := by
    refine lt_of_le_of_ne (fun g hg => ((hRmem g).mp hg).1) (fun h => hPN ?_)
    intro g hg
    rw [← h] at hg
    exact ((hRmem g).mp hg).2
  haveI : Group.IsNilpotent ↥(P : Subgroup L) := IsPGroup.isNilpotent P.isPGroup'
  have hnc : NormalizerCondition ↥(P : Subgroup L) :=
    Group.normalizerCondition_of_isNilpotent
  have hnc' : ∀ H : Subgroup ↥(P : Subgroup L), H < ⊤ →
      H < Subgroup.normalizer (H : Set ↥(P : Subgroup L)) := hnc
  have hH'top : R.subgroupOf (P : Subgroup L) < ⊤ := by
    refine lt_of_le_of_ne le_top (fun h => ?_)
    exact lt_irrefl R (lt_of_lt_of_le hRP (Subgroup.subgroupOf_eq_top.mp h))
  obtain ⟨g', hg'N, hg'H⟩ := SetLike.exists_of_lt (hnc' _ hH'top)
  have hgR : ∀ z ∈ Z, (g' : L) * z * (g' : L)⁻¹ ∈ R := by
    intro z hz
    have hzP : z ∈ (P : Subgroup L) := hZP hz
    have hzN : z ∈ Subgroup.normalizer (Z : Set L) := hZN hz
    have hx : (⟨z, hzP⟩ : ↥(P : Subgroup L)) ∈ R.subgroupOf (P : Subgroup L) :=
      Subgroup.mem_subgroupOf.mpr ((hRmem z).mpr ⟨hzP, hzN⟩)
    exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hg'N _).mp hx)
  have hmapN : Z.map (MulAut.conj (g' : L)).toMonoidHom ≤ Subgroup.normalizer (Z : Set L) := by
    rintro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    exact ((hRmem _).mp (hgR z hz)).2
  have hconj := hwc (g' : L) hmapN
  have hgN : (g' : L) ∈ Subgroup.normalizer (Z : Set L) := by
    refine (hmemN _).mpr fun h => ⟨fun hh => ?_, fun hh => ?_⟩
    · have hmem : (g' : L) * h * (g' : L)⁻¹ ∈ Z.map (MulAut.conj (g' : L)).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
      rw [hconj] at hmem
      exact hmem
    · have hmem : (g' : L) * h * (g' : L)⁻¹ ∈ Z.map (MulAut.conj (g' : L)).toMonoidHom := by
        rw [hconj]
        exact hh
      obtain ⟨y, hy, hyh⟩ := Subgroup.mem_map.mp hmem
      have hyh' : (g' : L) * y * (g' : L)⁻¹ = (g' : L) * h * (g' : L)⁻¹ := hyh
      have hyh_eq : y = h := mul_left_cancel (mul_right_cancel hyh')
      rw [← hyh_eq]
      exact hy
  have hg'P : (g' : L) ∈ R := (hRmem _).mpr ⟨g'.2, hgN⟩
  exact hg'H (Subgroup.mem_subgroupOf.mpr hg'P)

theorem exists_sylow_le_center_of_weaklyClosed {Z : Subgroup L} (hZ3 : Nat.card Z = 3)
    (hwc : ∀ g : L, Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set L) →
      Z.map (MulAut.conj g).toMonoidHom = Z) :
    ∃ P : Sylow 3 L, Z ≤ (P : Subgroup L) ∧
      Z ≤ Subgroup.centralizer ((P : Subgroup L) : Set L) := by
  obtain ⟨P, hZP, hPN⟩ := exists_sylow_ge_le_normalizer_aux hZ3 hwc
  refine ⟨P, hZP, ?_⟩
  obtain ⟨x, hxZ, hxord⟩ : ∃ x ∈ Z, orderOf x = 3 := by
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 (by omega)
    exact ⟨(y : L), y.2, (Subgroup.orderOf_coe y).trans hy⟩
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hxord
    exact absurd hxord (by norm_num)
  have hx3 : x ^ 3 = 1 := by
    rw [← hxord]
    exact pow_orderOf_eq_one x
  have hzp : Subgroup.zpowers x = Z := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr hxZ
    · exact le_of_eq (by rw [Nat.card_zpowers, hxord, hZ3])
  have hcls : ∀ w ∈ Z, w = 1 ∨ w = x ∨ w = x⁻¹ := by
    intro w hw
    have hwz : w ∈ Subgroup.zpowers x := by
      rw [hzp]
      exact hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hwz
    have hmod := zpow_mod_orderOf x k
    rw [hxord] at hmod
    push_cast at hmod
    rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
    · left
      rw [h, zpow_zero] at hmod
      rw [← hmod]
    · right
      left
      rw [h, zpow_one] at hmod
      rw [← hmod]
    · right
      right
      rw [h] at hmod
      rw [← hmod, zpow_ofNat]
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hx3)
  have hcomm : ∀ p ∈ (P : Subgroup L), Commute p x := by
    intro p hp
    have hwZ : p * x * p⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hPN hp) x).mp hxZ
    rcases hcls _ hwZ with h1 | h1 | h1
    · exfalso
      apply hx1
      calc x = p⁻¹ * (p * x * p⁻¹) * p := by group
        _ = 1 := by rw [h1]; group
    · show p * x = x * p
      calc p * x = p * x * p⁻¹ * p := by group
        _ = x * p := by rw [h1]
    · exfalso
      have hsq : p ^ 2 * x * (p ^ 2)⁻¹ = x := by
        calc p ^ 2 * x * (p ^ 2)⁻¹ = p * (p * x * p⁻¹) * p⁻¹ := by rw [sq]; group
          _ = p * x⁻¹ * p⁻¹ := by rw [h1]
          _ = (p * x * p⁻¹)⁻¹ := by group
          _ = x := by rw [h1, inv_inv]
      have hodd : ∀ j : ℕ, p ^ (2 * j + 1) * x * (p ^ (2 * j + 1))⁻¹ = x⁻¹ := by
        intro j
        induction j with
        | zero => simpa using h1
        | succ n ih =>
          calc p ^ (2 * (n + 1) + 1) * x * (p ^ (2 * (n + 1) + 1))⁻¹
              = p ^ 2 * (p ^ (2 * n + 1) * x * (p ^ (2 * n + 1))⁻¹) * (p ^ 2)⁻¹ := by group
            _ = p ^ 2 * x⁻¹ * (p ^ 2)⁻¹ := by rw [ih]
            _ = (p ^ 2 * x * (p ^ 2)⁻¹)⁻¹ := by group
            _ = x⁻¹ := by rw [hsq]
      obtain ⟨m, hm⟩ := isPGroup_iff_pow_pow_eq_one.mp P.isPGroup' ⟨p, hp⟩
      have hpm : p ^ 3 ^ m = 1 := by
        have := congrArg Subtype.val hm
        simpa using this
      obtain ⟨j, hj⟩ : Odd (3 ^ m) := Odd.pow (⟨1, by norm_num⟩ : Odd (3 : ℕ))
      have hxj := hodd j
      rw [← hj, hpm, one_mul, inv_one, mul_one] at hxj
      have hx2 : x ^ 2 = 1 := by
        rw [sq]
        exact mul_eq_one_iff_eq_inv.mpr hxj
      have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
      rw [hxord] at hdvd
      omega
  intro z hz
  have hzx : z ∈ Subgroup.zpowers x := by
    rw [hzp]
    exact hz
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzx
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  exact (hcomm p hp).zpow_right j

end CFSG.RankThree.PartTwo.Sec4.Hering432
