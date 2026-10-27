module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Count
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open scoped Pointwise

theorem exists_sylow_center_conj {S : Type} [Group S] [Finite S] (n : ℕ) (Q : Subgroup S)
    (hQ : Nat.card Q = 3 ^ n) (hS : ¬ 3 ^ (n + 1) ∣ Nat.card S) {z : S} (hz : orderOf z = 3)
    (hidx : ¬ 3 ∣ (Subgroup.centralizer ({z} : Set S)).index) :
    ∃ h : S, h * z * h⁻¹ ∈ Q ∧ ∀ q ∈ Q, q * (h * z * h⁻¹) = (h * z * h⁻¹) * q := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hGne : Nat.card S ≠ 0 := Nat.card_pos.ne'
  have hfacS : (Nat.card S).factorization 3 = n := by
    have h3 : 3 ^ n ∣ Nat.card S := hQ ▸ Subgroup.card_subgroup_dvd_card Q
    have a := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hGne).mp h3
    have b : ¬ n + 1 ≤ (Nat.card S).factorization 3 := fun h =>
      hS ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hGne).mpr h)
    omega
  set C := Subgroup.centralizer ({z} : Set S) with hC
  have hCS : Nat.card C * C.index = Nat.card S := Subgroup.card_mul_index C
  have hCne : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hidxne : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hfacC : (Nat.card C).factorization 3 = n := by
    have h1 : (Nat.card C * C.index).factorization 3 = (Nat.card S).factorization 3 := by
      rw [hCS]
    rw [Nat.factorization_mul hCne hidxne, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hidx, add_zero] at h1
    omega
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let z' : C := ⟨z, hzC⟩
  have hz'central : ∀ c : C, c * z' = z' * c := by
    intro c
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.mp c.2
    exact this
  have hz'o : orderOf z' = 3 := by
    rw [← Subgroup.orderOf_coe z']
    exact hz
  have hpg : IsPGroup 3 (Subgroup.zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'o]; simp)
  obtain ⟨P', hP'⟩ := hpg.exists_le_sylow
  set R : Subgroup S := (P' : Subgroup C).map C.subtype with hR
  have hRcard : Nat.card R = 3 ^ n := by
    rw [hR, Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity P',
      hfacC]
  have hzR : z ∈ R := ⟨z', hP' (Subgroup.mem_zpowers z'), rfl⟩
  have hRC : ∀ r ∈ R, r * z = z * r := by
    intro r hr
    obtain ⟨c, -, rfl⟩ := hr
    have := hz'central c
    have h2 := congrArg Subtype.val this
    exact h2
  let R₀ : Sylow 3 S := Sylow.ofCard R (by rw [hRcard, hfacS])
  let Q₀ : Sylow 3 S := Sylow.ofCard Q (by rw [hQ, hfacS])
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq S R₀ Q₀
  have hQeq : (Q₀ : Subgroup S) = MulAut.conj h • (R₀ : Subgroup S) := by
    rw [← hh, Sylow.coe_subgroup_smul]
  have hQmem : ∀ x : S, x ∈ Q ↔ ∃ r ∈ R, h * r * h⁻¹ = x := by
    intro x
    have : x ∈ (Q₀ : Subgroup S) ↔ x ∈ MulAut.conj h • (R₀ : Subgroup S) := by rw [hQeq]
    rw [Subgroup.mem_smul_pointwise_iff_exists] at this
    exact this
  refine ⟨h, (hQmem _).mpr ⟨z, hzR, rfl⟩, fun q hq => ?_⟩
  obtain ⟨r, hr, rfl⟩ := (hQmem q).mp hq
  have := hRC r hr
  calc h * r * h⁻¹ * (h * z * h⁻¹) = h * (r * z) * h⁻¹ := by group
    _ = h * (z * r) * h⁻¹ := by rw [this]
    _ = h * z * h⁻¹ * (h * r * h⁻¹) := by group

theorem listRow_of_sylow_center {S : Type} [Group S] [Finite S] (n : ℕ) (Q : Subgroup S)
    (hQ : Nat.card Q = 3 ^ n) (hS : ¬ 3 ^ (n + 1) ∣ Nat.card S)
    (hw : ∀ u ∈ Q, orderOf u = 3 → (∀ q ∈ Q, q * u = u * q) →
      ∃ g : S, (g * u * g⁻¹) * u = u * (g * u * g⁻¹) ∧ g * u * g⁻¹ ∉ Subgroup.zpowers u) :
    ListRow S := by
  refine listRow_of_forall_not_weaklyClosed fun z hz hwc => ?_
  have hidx := three_not_dvd_index_centralizer_of_weaklyClosed hz hwc
  obtain ⟨h, huQ, huc⟩ := exists_sylow_center_conj n Q hQ hS hz hidx
  have huo : orderOf (h * z * h⁻¹) = 3 := by
    rw [← hz]
    have := MulEquiv.orderOf_eq (MulAut.conj h) z
    simpa using this
  obtain ⟨g, hc, hn⟩ := hw _ huQ huo huc
  refine (not_weaklyClosed_of_commute_conj (z := z) (g := h⁻¹ * g * h) ?_ ?_) hwc
  · have e : h⁻¹ * g * h * z * (h⁻¹ * g * h)⁻¹ = h⁻¹ * (g * (h * z * h⁻¹) * g⁻¹) * h := by group
    rw [e]
    calc h⁻¹ * (g * (h * z * h⁻¹) * g⁻¹) * h * z
        = h⁻¹ * ((g * (h * z * h⁻¹) * g⁻¹) * (h * z * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * z * h⁻¹) * (g * (h * z * h⁻¹) * g⁻¹)) * h := by rw [hc]
      _ = z * (h⁻¹ * (g * (h * z * h⁻¹) * g⁻¹) * h) := by group
  · intro hmem
    apply hn
    have e1 : h⁻¹ * g * h * z * (h⁻¹ * g * h)⁻¹ = h⁻¹ * (g * (h * z * h⁻¹) * g⁻¹) * h := by group
    rw [e1] at hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have hpow : (h * z * h⁻¹) ^ k = h * z ^ k * h⁻¹ := by
      have := conj_zpow (a := h) (b := z) (i := k)
      simpa using this
    rw [hpow]
    calc h * z ^ k * h⁻¹ = h * (h⁻¹ * (g * (h * z * h⁻¹) * g⁻¹) * h) * h⁻¹ := by rw [hk]
      _ = g * (h * z * h⁻¹) * g⁻¹ := by group

end CFSG.RankThree.PartTwo.Sec4.RonanK432
