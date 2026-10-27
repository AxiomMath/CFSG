module

public import CFSG.RankThree.PartOne.Q1327R.Act9
public import CFSG.RankThree.PartOne.Q1327R.Row9

public section

namespace CFSG.RankThree.PartOne.Q1327R

open CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.Torsion37

theorem gcd_four_two_pow_add_one {f : ℕ} (hf : 1 ≤ f) : Nat.gcd 4 (2 ^ f + 1) = 1 := by
  have h2 : Odd (2 ^ f + 1) := by
    have : Even (2 ^ f) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    exact this.add_one
  have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr h2)
  simpa using this

theorem kf1327Out_holds : Q1327.KF1327Out := by
  intro G _ _ p f X E hp hp5 hf2 hpf _ hZ hmodel hEel hEX hEcard hmax x hxN ⟨k, hk⟩
  by_contra hnot
  obtain ⟨K, _, ⟨C⟩⟩ := exists_frame hp hp5 hf2 hpf hZ hmodel hEel hEX hEcard
  have : Finite K := C.hU.finite
  have hgcd : Nat.gcd 4 (2 ^ f + 1) = 1 := gcd_four_two_pow_add_one (by omega)
  have : Fact p.Prime := ⟨hp⟩
  have hC1 : ∀ z ∈ Subgroup.centralizer (X : Set G), z ^ p = 1 → z = 1 := by
    intro z hzC hzp
    by_contra hz1
    have hcomm : ∀ e ∈ E, ∀ y ∈ Subgroup.zpowers z, e * y = y * e := by
      intro e he y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (show Commute e z from
        Subgroup.mem_centralizer_iff.mp hzC e (hEX he)) i).eq
    have hFel : IsElementaryAbelian p ↥(E ⊔ Subgroup.zpowers z) :=
      isElementaryAbelian_sup_of_commute hEel (IsElementaryAbelian.zpowers_of_pow_eq_one hzp) hcomm
    have hFle : E ⊔ Subgroup.zpowers z ≤ Subgroup.centralizer (E : Set G) := by
      refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
      · intro e he
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact congrArg Subtype.val (hEel.is_comm.comm (⟨a, ha⟩ : ↥E) ⟨e, he⟩)
      · rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact Subgroup.mem_centralizer_iff.mp hzC a (hEX ha)
    have hFE := hmax _ hFel hFle le_sup_left
    have hzE : z ∈ E := by
      rw [← hFE]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
    have hzX : z ∈ X := hEX hzE
    have hmem : (⟨z, hzX⟩ : ↥X) ∈ Subgroup.center ↥X := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC g g.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hz1 (congrArg Subtype.val hmem)
  let xN : ↥(Subgroup.normalizer (X : Set G)) := ⟨x, hxN⟩
  have hnotinn : C.Phi hgcd xN ∉ InnAut (P4 C.hU) := fun hin =>
    hnot (C.mem_sup_of_Phi_mem_inner hgcd xN hin)
  obtain ⟨m, hm⟩ : ∃ m, orderOf (C.Phi hgcd xN) = p ^ m := by
    have h1 : orderOf (C.Phi hgcd xN) ∣ orderOf xN := orderOf_map_dvd (C.Phi hgcd) xN
    have h2 : orderOf xN = p ^ k := by
      rw [← Subgroup.orderOf_coe]
      exact hk
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 (h2 ▸ h1)
    exact ⟨m, hm⟩
  obtain ⟨j, σ, s, hσ, hs, hα⟩ := exists_fieldFactor_of_pPow C.hU hgcd hp hnotinn hm
  obtain ⟨q, hq⟩ := hs
  obtain ⟨y₀, rfl⟩ := (C.eP hgcd).surjective q
  have hy₀N : (y₀ : G) ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer y₀.2
  have hΦy : C.Phi hgcd ⟨y₀, hy₀N⟩ = s := by
    rw [C.Phi_of_mem_X hgcd y₀ hy₀N]
    exact hq
  let n₀ : ↥(Subgroup.normalizer (X : Set G)) := ⟨y₀, hy₀N⟩⁻¹ * xN ^ (p ^ j)
  have hΦn₀ : C.Phi hgcd n₀ = fld C.hU σ := by
    rw [map_mul, map_inv, map_pow, hΦy, hα, inv_mul_cancel_left]
  have hσp : σ ^ p = 1 := by
    rw [← hσ]
    exact pow_orderOf_eq_one σ
  have hn₀p : ((n₀ ^ p : ↥(Subgroup.normalizer (X : Set G))) : G) ∈
      Subgroup.centralizer (X : Set G) := by
    have h1 : C.Phi hgcd (n₀ ^ p) = 1 := by
      rw [map_pow, hΦn₀, fld_pow, hσp, fld_one]
    have h2 := (C.Phi_eq_one_iff hgcd _).mp h1
    exact mem_centralizer_of_conj_eq h2
  have hn₀ord : 0 < orderOf n₀ := orderOf_pos n₀
  obtain ⟨e, m', hm', hom⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn₀ord.ne' p hp.ne_one
  have hm'0 : m' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hom
    exact hn₀ord.ne' hom
  set vN : ↥(Subgroup.normalizer (X : Set G)) := n₀ ^ m' with hvN
  have hov : orderOf vN = p ^ e := by
    rw [hvN, orderOf_pow_of_dvd hm'0 (Dvd.intro_left _ hom.symm), hom]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm'0)
  set σ₁ : K ≃+* K := σ ^ m' with hσ₁
  have hΦv : C.Phi hgcd vN = fld C.hU σ₁ := by
    rw [hvN, map_pow, hΦn₀, fld_pow]
  have hσ₁p : σ₁ ^ p = 1 := by
    rw [hσ₁, ← pow_mul, mul_comm, pow_mul, hσp, one_pow]
  have hσ₁1 : σ₁ ≠ 1 := by
    intro h1
    have : p ∣ m' := by
      rw [← hσ]
      exact orderOf_dvd_of_pow_eq_one h1
    exact hm' this
  have he1 : e = 1 := by
    rcases Nat.lt_trichotomy e 1 with h0 | h1 | h2
    · exfalso
      have : e = 0 := by omega
      rw [this, pow_zero, orderOf_eq_one_iff] at hov
      rw [hov, map_one] at hΦv
      exact hσ₁1 (fld_eq_one C.hU hΦv.symm)
    · exact h1
    · exfalso
      obtain ⟨d, hd⟩ : ∃ d, e = d + 2 := ⟨e - 2, by omega⟩
      set z : G := (vN : G) ^ (p ^ (d + 1)) with hz
      have hn₀p' : (n₀ : G) ^ p ∈ Subgroup.centralizer (X : Set G) := by
        simpa only [Subgroup.coe_pow] using hn₀p
      have hzC : z ∈ Subgroup.centralizer (X : Set G) := by
        have : z = (((n₀ : G) ^ p) ^ m') ^ (p ^ d) := by
          rw [hz, hvN]
          simp only [Subgroup.coe_pow, ← pow_mul]
          congr 1
          ring
        rw [this]
        exact pow_mem (pow_mem hn₀p' _) _
      have hzo : orderOf z = p := by
        have hvo : orderOf (vN : G) = p ^ (d + 2) := by
          rw [Subgroup.orderOf_coe, hov, hd]
        have hdiv : p ^ (d + 1) ∣ orderOf (vN : G) := by
          rw [hvo]
          exact pow_dvd_pow _ (by omega)
        rw [hz, orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hdiv, hvo,
          Nat.pow_div (by omega) hp.pos]
        simp
      have hzp : z ^ p = 1 := by
        rw [← hzo]
        exact pow_orderOf_eq_one z
      exact hp.one_lt.ne (by simpa [hC1 z hzC hzp] using hzo)
  have hvo : orderOf (vN : G) = p := by
    rw [Subgroup.orderOf_coe, hov, he1, pow_one]
  have hvp : (vN : G) ^ p = 1 := by
    rw [← hvo]
    exact pow_orderOf_eq_one _
  have hcentr : ∀ e' ∈ E, (vN : G) * e' * (vN : G)⁻¹ = e' := fun e' he' =>
    C.centralizes_of_Phi_fld hgcd hp vN hσ₁p hΦv he'
  have hcomm : ∀ e' ∈ E, ∀ y ∈ Subgroup.zpowers (vN : G), e' * y = y * e' := by
    intro e' he' y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine (Commute.zpow_right (show Commute e' (vN : G) from ?_) i).eq
    have := hcentr e' he'
    calc e' * (vN : G) = ((vN : G) * e' * (vN : G)⁻¹) * (vN : G) := by rw [this]
      _ = (vN : G) * e' := by group
  have hFel : IsElementaryAbelian p ↥(E ⊔ Subgroup.zpowers (vN : G)) :=
    isElementaryAbelian_sup_of_commute hEel (IsElementaryAbelian.zpowers_of_pow_eq_one hvp) hcomm
  have hFle : E ⊔ Subgroup.zpowers (vN : G) ≤ Subgroup.centralizer (E : Set G) := by
    refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
    · intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact congrArg Subtype.val (hEel.is_comm.comm (⟨b, hb⟩ : ↥E) ⟨a, ha⟩)
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm a ha (vN : G) (Subgroup.mem_zpowers _)
  have hFE := hmax _ hFel hFle le_sup_left
  have hvE : (vN : G) ∈ E := by
    rw [← hFE]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hvX : (vN : G) ∈ X := hEX hvE
  have hinn : C.Phi hgcd vN ∈ InnAut (P4 C.hU) := by
    have : vN = ⟨((⟨(vN : G), hvX⟩ : X) : G), vN.2⟩ := rfl
    rw [this, C.Phi_of_mem_X hgcd ⟨(vN : G), hvX⟩ vN.2]
    exact ⟨_, rfl⟩
  rw [hΦv] at hinn
  have hker : fld C.hU σ₁ ∈ (FF C.hU).ker := by
    rw [ker_FF]
    exact inner_le_D C.hU hinn
  rw [MonoidHom.mem_ker, FF_fld] at hker
  exact hσ₁1 hker

end CFSG.RankThree.PartOne.Q1327R
