module

public import CFSG.Dihedral.Glauberman.DicksonMaxStructure
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3

public section

namespace CFSG.Quasithin

open scoped MatrixGroups

namespace E217R4

section Psl

variable {F : Type} [Field F] [Fintype F]

omit [Fintype F] in
theorem card_centralizer_conj {G : Type*} [Group G] (c z : G) :
    Nat.card (Subgroup.centralizer ({c * z * c⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({z} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨c⁻¹ * y * c, ?_⟩
      invFun := fun y => ⟨c * y * c⁻¹, ?_⟩
      left_inv := fun y => ?_
      right_inv := fun y => ?_ }
  · have := Subgroup.mem_centralizer_iff.1 y.2 (c * z * c⁻¹) rfl
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    calc z * (c⁻¹ * y * c) = c⁻¹ * ((c * z * c⁻¹) * y) * c := by group
      _ = c⁻¹ * (y * (c * z * c⁻¹)) * c := by rw [this]
      _ = c⁻¹ * y * c * z := by group
  · have := Subgroup.mem_centralizer_iff.1 y.2 z rfl
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    calc c * z * c⁻¹ * (c * y * c⁻¹) = c * (z * y) * c⁻¹ := by group
      _ = c * (y * z) * c⁻¹ := by rw [this]
      _ = c * y * c⁻¹ * (c * z * c⁻¹) := by group
  · apply Subtype.ext
    show c * (c⁻¹ * (y : G) * c) * c⁻¹ = y
    group
  · apply Subtype.ext
    show c⁻¹ * (c * (y : G) * c⁻¹) * c = y
    group

theorem psl7_basic (hF7 : Fintype.card F = 7) :
    ringChar F ≠ 2 ∧ Nat.card PSL(2, F) = 168 := by
  have hF2 : ringChar F ≠ 2 := by
    intro h2
    have : CharP F 2 := h2 ▸ ringChar.charP F
    obtain ⟨n, hp, hn⟩ := FiniteField.card F 2
    have h3 : 7 = 2 ^ (n : ℕ) := by rw [← hF7, hn]
    have h4 : 2 ∣ 7 := h3 ▸ dvd_pow_self 2 n.ne_zero
    omega
  refine ⟨hF2, ?_⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcard : Nat.card F = 7 ^ 1 := by rw [Nat.card_eq_fintype_card, hF7]; norm_num
  have := CFSG.Glauberman.Dickson.MaxUp.card_psl2_odd (F := F) hcard (by norm_num)
  rw [this]
  norm_num

omit [Fintype F] in
theorem sylow3_sub {K : Type*} [Group K] (hcard : Nat.card K = 168) {P P' : Subgroup K}
    (hP : Nat.card P = 3) (hP' : Nat.card P' = 3) :
    ∃ g : K, P.map (MulAut.conj g).toMonoidHom = P' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hsyl : ∀ Q : Subgroup K, Nat.card Q = 3 → ∃ S : Sylow 3 K, (S : Subgroup K) = Q := by
    intro Q hQ
    have hQp : IsPGroup 3 Q := IsPGroup.of_card (n := 1) (by rw [hQ]; norm_num)
    have hidx : ¬ 3 ∣ Q.index := by
      have h1 := Subgroup.card_mul_index Q
      rw [hQ, hcard] at h1
      have : Q.index = 56 := by omega
      omega
    exact ⟨hQp.toSylow hidx, rfl⟩
  obtain ⟨S, hS⟩ := hsyl P hP
  obtain ⟨S', hS'⟩ := hsyl P' hP'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S S'
  refine ⟨g, ?_⟩
  have h := congrArg (fun R : Sylow 3 K => (R : Subgroup K)) hg
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hS, hS'] at h
  exact h

omit [Fintype F] in
theorem sylow3_elem {K : Type*} [Group K] (hcard : Nat.card K = 168) {a a' : K} (ha : a ^ 3 = 1)
    (ha1 : a ≠ 1) (ha' : a' ^ 3 = 1) (ha'1 : a' ≠ 1) :
    ∃ g : K, ∃ i : ℕ, g * a * g⁻¹ = a' ^ i := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have hP : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha ha1
  have hP' : Nat.card (Subgroup.zpowers a') = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha' ha'1
  obtain ⟨g, hg⟩ := sylow3_sub hcard hP hP'
  have hmem : g * a * g⁻¹ ∈ Subgroup.zpowers a' := by
    rw [← hg]
    exact ⟨a, Subgroup.mem_zpowers a, by simp [MulAut.conj_apply]⟩
  obtain ⟨i, hi⟩ := (mem_powers_iff_mem_zpowers).2 hmem
  exact ⟨g, i, hi.symm⟩

theorem card_splitTorus_seven (hF7 : Fintype.card F = 7) :
    Nat.card (CFSG.PSL2Table.splitTorus F) = 3 := by
  rw [CFSG.Glauberman.Dickson.MaxStructure.card_splitTorus_eq (psl7_basic hF7).1, hF7]

theorem cent3_psl (hF7 : Fintype.card F = 7) {x : PSL(2, F)} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    {y : PSL(2, F)} (hyx : y * x = x * y) : ∃ i : ℕ, y = x ^ i := by
  classical
  obtain ⟨hF2, hcard⟩ := psl7_basic hF7
  have hq : 5 ≤ Fintype.card F := by omega
  have hPx : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  obtain ⟨g, hg⟩ := sylow3_sub hcard hPx (card_splitTorus_seven hF7)
  set t := g * x * g⁻¹ with ht
  have htT : t ∈ CFSG.PSL2Table.splitTorus F := by
    rw [← hg]
    exact ⟨x, Subgroup.mem_zpowers x, by simp [MulAut.conj_apply, ht]⟩
  have ht3 : t ^ 3 = 1 := by
    rw [ht, conj_pow, hx3]
    group
  have ht1 : t ≠ 1 := by
    intro h1
    apply hx1
    have : x = g⁻¹ * t * g := by rw [ht]; group
    rw [this, h1]
    group
  have ht2 : t ^ 2 ≠ 1 := by
    intro h2
    apply ht1
    calc t = t ^ 3 * (t ^ 2)⁻¹ := by group
      _ = 1 := by rw [ht3, h2]; group
  have hcentT : Nat.card (Subgroup.centralizer ({t} : Set PSL(2, F))) = 3 := by
    rw [CFSG.PSL2Table.card_centralizer_splitTorus hF2 hq htT ht1]
    simp only [ht2, ↓reduceIte]
    exact card_splitTorus_seven hF7
  have hzle : Subgroup.zpowers t ≤ Subgroup.centralizer ({t} : Set PSL(2, F)) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]
  have htcard : Nat.card (Subgroup.zpowers t) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ht3 ht1
  have heq := Subgroup.eq_of_le_of_card_ge hzle (by rw [hcentT, htcard])
  have hy' : g * y * g⁻¹ ∈ Subgroup.centralizer ({t} : Set PSL(2, F)) := by
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rw [Set.mem_singleton_iff.1 hh, ht]
    calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [hyx]
      _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
  rw [← heq] at hy'
  obtain ⟨i, hi⟩ := (mem_powers_iff_mem_zpowers).2 hy'
  have hi' : t ^ i = g * y * g⁻¹ := hi
  refine ⟨i, ?_⟩
  have h3 : g * y * g⁻¹ = g * x ^ i * g⁻¹ := by
    rw [← hi', ht, conj_pow]
  exact mul_left_cancel (mul_right_cancel h3)

end Psl

end E217R4

end CFSG.Quasithin
