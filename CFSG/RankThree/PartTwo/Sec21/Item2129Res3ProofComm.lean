module

public import CFSG.RankThree.PartTwo.Sec21.Item2129Res2ProofCore
import CFSG.RankThree.PartTwo.Sec21.Item2129Res2ProofNormal
import CFSG.ThirdParty.BrauerInduction.Background.Group.PDecomposition

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2129Res3Proof

open Item2129Res2Proof

variable {G : Type} [Group G] [Finite G] {F H Q Y : Subgroup G} {e d : G}

omit [Finite G] in
theorem conj_mem_C (hL : Loc2129 F H Q Y e d) {y o : G} (hy : y ∈ Y)
    (ho : o ∈ Y ⊓ Subgroup.centralizer (F : Set G)) :
    y * o * y⁻¹ ∈ Y ⊓ Subgroup.centralizer (F : Set G) := by
  refine Subgroup.mem_inf.mpr ⟨Y.mul_mem (Y.mul_mem hy ho.1) (Y.inv_mem hy), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hf' : y⁻¹ * f * y ∈ F := by
    have h := hL.conj_mem_F (Y.inv_mem hy) hf
    rwa [inv_inv] at h
  have h1 := Subgroup.mem_centralizer_iff.mp ho.2 _ hf'
  calc f * (y * o * y⁻¹) = y * ((y⁻¹ * f * y) * o) * y⁻¹ := by group
    _ = y * (o * (y⁻¹ * f * y)) * y⁻¹ := by rw [h1]
    _ = y * o * y⁻¹ * f := by group

omit [Finite G] in
theorem conj_mem_O (hL : Loc2129 F H Q Y e d) {y o : G} (hy : y ∈ Y)
    (ho : o ∈ Y ⊓ Subgroup.centralizer (F : Set G)) (ho3 : Nat.Coprime (orderOf o) 3) :
    y * o * y⁻¹ ∈ Y ⊓ Subgroup.centralizer (F : Set G) ∧
      Nat.Coprime (orderOf (y * o * y⁻¹)) 3 := by
  refine ⟨conj_mem_C hL hy ho, ?_⟩
  have hs : SemiconjBy y o (y * o * y⁻¹) := by
    unfold SemiconjBy
    group
  rwa [← SemiconjBy.orderOf_eq y hs]

omit [Finite G] in
theorem kap_inv (hL : Loc2129 F H Q Y e d) {y : G}
    (hy : y ∈ Y ⊓ Subgroup.centralizer (H : Set G)) :
    e⁻¹ * (y⁻¹ * e * y⁻¹⁻¹) = (e⁻¹ * (y * e * y⁻¹))⁻¹ := by
  have h := hL.kap_mul hy.1 hy.2 (Y.inv_mem hy.1)
  simp only [mul_inv_cancel, one_mul, inv_one, mul_one, inv_mul_cancel] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem comm_of_inv (hL : Loc2129 F H Q Y e d) {t : G} (htY : t ∈ Y)
    (htH : ∀ h ∈ H, t * h * t⁻¹ = h⁻¹)
    (htO : ∀ o ∈ Y ⊓ Subgroup.centralizer (F : Set G), Nat.Coprime (orderOf o) 3 →
      t * o = o * t) :
    ∀ x ∈ Y ⊓ Subgroup.centralizer (H : Set G), ∀ o ∈ Y ⊓ Subgroup.centralizer (F : Set G),
      (∃ n : ℕ, x ^ 3 ^ n = 1) → Nat.Coprime (orderOf o) 3 → x * o = o * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P : G → Prop := fun z => z ∈ Y ⊓ Subgroup.centralizer (H : Set G) ∧
    ∀ o ∈ Y ⊓ Subgroup.centralizer (F : Set G), Nat.Coprime (orderOf o) 3 → z * o = o * z
    with hP
  have hPconj : ∀ m ∈ Y, ∀ z, P z → P (m * z * m⁻¹) := by
    rintro m hm z ⟨hzK, hzO⟩
    refine ⟨⟨Y.mul_mem (Y.mul_mem hm hzK.1) (Y.inv_mem hm),
      hL.conj_mem_centralizer hm hzK.2⟩, fun o ho ho3 => ?_⟩
    obtain ⟨ho', ho3'⟩ := conj_mem_O hL (Y.inv_mem hm) ho ho3
    rw [inv_inv] at ho' ho3'
    have h1 := hzO _ ho' ho3'
    calc m * z * m⁻¹ * o = m * (z * (m⁻¹ * o * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * o * m) * z) * m⁻¹ := by rw [h1]
      _ = o * (m * z * m⁻¹) := by group
  obtain ⟨y, hyK, hyd⟩ := hL.exists_kap_eq_of_cent hL.mem_d
  have hyinvK : y⁻¹ ∈ Y ⊓ Subgroup.centralizer (H : Set G) := Subgroup.inv_mem _ hyK
  have hκyinv : e⁻¹ * (y⁻¹ * e * y⁻¹⁻¹) = d⁻¹ := by rw [kap_inv hL hyK, hyd]
  have htyt : t * y⁻¹ * t⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem htY hyinvK.1) (Y.inv_mem htY)
  have hκ1 := hL.kap_mul hyK.1 hyK.2 htyt
  have hκ2 := hL.kap_conj hyinvK.1 hyinvK.2 htY
  have htd : t * d⁻¹ * t⁻¹ = d := by rw [htH _ (H.inv_mem hL.mem_d), inv_inv]
  set x₀ := y * t * y⁻¹ * t⁻¹ with hx₀
  have hx₀eq : x₀ = y * (t * y⁻¹ * t⁻¹) := by rw [hx₀]; group
  have hx₀Y : x₀ ∈ Y := by
    rw [hx₀eq]
    exact Y.mul_mem hyK.1 htyt
  have hκx₀ : e⁻¹ * (x₀ * e * x₀⁻¹) = d * d := by
    rw [hx₀eq, hκ1, hκ2, hκyinv, htd, hyd]
  have hx₀H : x₀ ∈ Subgroup.centralizer (H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhinv : h⁻¹ ∈ H := H.inv_mem hh
    have e1 : t⁻¹ * h * t = h⁻¹ := by
      have h2 := htH _ hhinv
      rw [inv_inv] at h2
      calc t⁻¹ * h * t = t⁻¹ * (t * h⁻¹ * t⁻¹) * t := by rw [h2]
        _ = h⁻¹ := by group
    have e2 : y⁻¹ * h⁻¹ * y = h⁻¹ := by
      have h2 := Subgroup.mem_centralizer_iff.mp hyK.2 _ hhinv
      calc y⁻¹ * h⁻¹ * y = y⁻¹ * (h⁻¹ * y) := by group
        _ = y⁻¹ * (y * h⁻¹) := by rw [h2]
        _ = h⁻¹ := by group
    have e3 : t * h⁻¹ * t⁻¹ = h := by rw [htH _ hhinv, inv_inv]
    have e4 : y * h * y⁻¹ = h := by
      have h2 := Subgroup.mem_centralizer_iff.mp hyK.2 _ hh
      calc y * h * y⁻¹ = (h * y) * y⁻¹ := by rw [h2]
        _ = h := by group
    have key : x₀ * h * x₀⁻¹ = h := by
      calc x₀ * h * x₀⁻¹ = y * (t * (y⁻¹ * (t⁻¹ * h * t) * y) * t⁻¹) * y⁻¹ := by
            rw [hx₀]; group
        _ = h := by rw [e1, e2, e3, e4]
    calc h * x₀ = x₀ * h * x₀⁻¹ * x₀ := by rw [key]
      _ = x₀ * h := by group
  have hx₀O : ∀ o ∈ Y ⊓ Subgroup.centralizer (F : Set G), Nat.Coprime (orderOf o) 3 →
      x₀ * o = o * x₀ := by
    intro o ho ho3
    obtain ⟨ho', ho3'⟩ := conj_mem_O hL (Y.inv_mem hyK.1) ho ho3
    rw [inv_inv] at ho' ho3'
    have h1 := htO _ ho' ho3'
    have h2 := htO _ ho ho3
    have h3 : t⁻¹ * o = o * t⁻¹ := by
      calc t⁻¹ * o = t⁻¹ * (o * t) * t⁻¹ := by group
        _ = t⁻¹ * (t * o) * t⁻¹ := by rw [h2]
        _ = o * t⁻¹ := by group
    calc x₀ * o = y * t * y⁻¹ * (t⁻¹ * o) := by rw [hx₀]; group
      _ = y * t * y⁻¹ * (o * t⁻¹) := by rw [h3]
      _ = y * (t * (y⁻¹ * o * y)) * y⁻¹ * t⁻¹ := by group
      _ = y * ((y⁻¹ * o * y) * t) * y⁻¹ * t⁻¹ := by rw [h1]
      _ = o * x₀ := by rw [hx₀]; group
  have hx₀P : P x₀ := ⟨⟨hx₀Y, hx₀H⟩, hx₀O⟩
  have hd3 : d ^ 3 = 1 := hL.pow_H d hL.mem_d
  have hdd : d * d ≠ 1 := by
    intro h
    apply hL.ne_one_d
    calc d = d ^ 3 * (d * d)⁻¹ := by rw [pow_succ, pow_two]; group
      _ = 1 := by rw [hd3, h]; group
  have hZsurj : ∀ h ∈ H, ∃ z, P z ∧ e⁻¹ * (z * e * z⁻¹) = h := by
    intro h hh
    by_cases h1 : h = 1
    · refine ⟨1, ⟨Subgroup.one_mem _, fun o _ _ => by group⟩, ?_⟩
      rw [h1]
      group
    · obtain ⟨m, hmY, -, hm⟩ := hL.trans _ (H.mul_mem hL.mem_d hL.mem_d) _ hh hdd h1
      refine ⟨m * x₀ * m⁻¹, hPconj m hmY x₀ hx₀P, ?_⟩
      rw [hL.kap_conj hx₀Y hx₀H hmY, hκx₀, hm]
  intro x hx o ho ⟨n, hxn⟩ ho3
  obtain ⟨z, ⟨hzK, hzO⟩, hzx⟩ := hZsurj _ (hL.kap_mem hx.1)
  have hzinvK : z⁻¹ ∈ Y ⊓ Subgroup.centralizer (H : Set G) := Subgroup.inv_mem _ hzK
  have hcK : z⁻¹ * x ∈ Y ⊓ Subgroup.centralizer (H : Set G) := Subgroup.mul_mem _ hzinvK hx
  have hκc : e⁻¹ * (z⁻¹ * x * e * (z⁻¹ * x)⁻¹) = 1 := by
    rw [hL.kap_mul hzinvK.1 hzinvK.2 hx.1, kap_inv hL hzK, hzx, inv_mul_cancel]
  have hcC : z⁻¹ * x ∈ Y ⊓ Subgroup.centralizer (F : Set G) :=
    ⟨hcK.1, hL.mem_centralizer_F hcK.2 (Loc2129.kap_eq_one_iff.mp hκc)⟩
  have hfin : IsOfFinOrder (z⁻¹ * x) := isOfFinOrder_of_finite _
  have hdec : Group.pRegular 3 (z⁻¹ * x) * Group.pSingular 3 (z⁻¹ * x) = z⁻¹ * x :=
    Group.pDecomp' 3 hfin
  have hcr_mem : Group.pRegular 3 (z⁻¹ * x) ∈ Subgroup.zpowers (z⁻¹ * x) := by
    unfold Group.pRegular
    exact Subgroup.zpow_mem_zpowers _ _
  have hcs_mem : Group.pSingular 3 (z⁻¹ * x) ∈ Subgroup.zpowers (z⁻¹ * x) := by
    unfold Group.pSingular
    exact Subgroup.zpow_mem_zpowers _ _
  have hcrC := Subgroup.zpowers_le.mpr hcC hcr_mem
  have hcsC := Subgroup.zpowers_le.mpr hcC hcs_mem
  have hcr3 : Nat.Coprime (orderOf (Group.pRegular 3 (z⁻¹ * x))) 3 :=
    Group.isPRegular_pRegular 3 hfin
  obtain ⟨k, hk⟩ := Group.isPSingular_pSingular 3 (z⁻¹ * x)
  have hcs3 : Group.pSingular 3 (z⁻¹ * x) ^ 3 ^ k = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one _
  have hcsF : Group.pSingular 3 (z⁻¹ * x) ∈ F :=
    hL.le_F _ (Loc2129.isPGroup_zpowers hcs3) (Subgroup.zpowers_le.mpr hcsC.2)
      (Subgroup.mem_zpowers _)
  set cr := Group.pRegular 3 (z⁻¹ * x) with hcr
  set cs := Group.pSingular 3 (z⁻¹ * x) with hcs
  have hxe : x = z * (cr * cs) := by rw [hdec]; group
  have hkey : ∀ w ∈ Y ⊓ Subgroup.centralizer (F : Set G), Nat.Coprime (orderOf w) 3 →
      x * w * x⁻¹ = cr * w * cr⁻¹ := by
    intro w hw hw3
    obtain ⟨hw', hw3'⟩ := conj_mem_O hL hcrC.1 hw hw3
    have h1 := hzO _ hw' hw3'
    have h2 : cs * w = w * cs := Subgroup.mem_centralizer_iff.mp hw.2 _ hcsF
    calc x * w * x⁻¹ = z * (cr * (cs * w) * cs⁻¹ * cr⁻¹) * z⁻¹ := by rw [hxe]; group
      _ = z * (cr * w * cr⁻¹) * z⁻¹ := by rw [h2]; group
      _ = cr * w * cr⁻¹ := by rw [h1]; group
  have hiter : ∀ j : ℕ, x ^ j * o * (x ^ j)⁻¹ = cr ^ j * o * (cr ^ j)⁻¹ ∧
      cr ^ j * o * (cr ^ j)⁻¹ ∈ Y ⊓ Subgroup.centralizer (F : Set G) ∧
      Nat.Coprime (orderOf (cr ^ j * o * (cr ^ j)⁻¹)) 3 := by
    intro j
    induction j with
    | zero => exact ⟨by simp, by simpa using ho, by simpa using ho3⟩
    | succ j ih =>
      obtain ⟨ih1, ih2, ih3⟩ := ih
      obtain ⟨h2, h3⟩ := conj_mem_O hL hcrC.1 ih2 ih3
      have e1 : cr ^ (j + 1) * o * (cr ^ (j + 1))⁻¹ = cr * (cr ^ j * o * (cr ^ j)⁻¹) * cr⁻¹ := by
        rw [pow_succ']
        group
      refine ⟨?_, e1 ▸ h2, e1 ▸ h3⟩
      calc x ^ (j + 1) * o * (x ^ (j + 1))⁻¹ = x * (x ^ j * o * (x ^ j)⁻¹) * x⁻¹ := by
            rw [pow_succ']
            group
        _ = x * (cr ^ j * o * (cr ^ j)⁻¹) * x⁻¹ := by rw [ih1]
        _ = cr * (cr ^ j * o * (cr ^ j)⁻¹) * cr⁻¹ := hkey _ ih2 ih3
        _ = cr ^ (j + 1) * o * (cr ^ (j + 1))⁻¹ := e1.symm
  have h3n := (hiter (3 ^ n)).1
  rw [hxn, one_mul, inv_one, mul_one] at h3n
  have hcomm : Commute (cr ^ 3 ^ n) o := by
    show cr ^ 3 ^ n * o = o * cr ^ 3 ^ n
    calc cr ^ 3 ^ n * o = cr ^ 3 ^ n * o * (cr ^ 3 ^ n)⁻¹ * cr ^ 3 ^ n := by group
      _ = o * cr ^ 3 ^ n := by rw [← h3n]
  have hcr_in : cr ∈ Subgroup.zpowers (cr ^ 3 ^ n) := by
    rw [mem_zpowers_pow_iff]
    exact Nat.Coprime.pow_left n hcr3.symm
  have hcro : cr * o = o * cr := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hcr_in
    rw [← hi]
    exact (hcomm.zpow_left i).eq
  have h1 := hkey o ho ho3
  calc x * o = x * o * x⁻¹ * x := by group
    _ = cr * o * cr⁻¹ * x := by rw [h1]
    _ = o * x := by rw [hcro]; group

end CFSG.RankThree.PartTwo.Sec21.Item2129Res3Proof
