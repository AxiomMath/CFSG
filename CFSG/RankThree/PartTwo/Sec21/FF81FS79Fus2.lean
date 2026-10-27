module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Fus
public import CFSG.RankThree.PartTwo.Sec21.CarterFS79CenOdd

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

theorem FS79Hyp.card_B (h : FS79Hyp b t b₁ b₂ J) :
    Nat.card (Subgroup.closure ({b, b₁, b₂} : Set H)) = 27 := by
  have := h.isElemAb_B.2
  simpa using this

theorem FS79Hyp.card_le_nine_of_cen (h : FS79Hyp b t b₁ b₂ J) {u : H} (hu2 : u * u = 1)
    (hu1 : u ≠ 1) {X : Subgroup H} (hX : IsPGroup 3 X) (hXu : X ≤ Cen u) :
    Nat.card X ≤ 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B : Subgroup H := Subgroup.closure ({b, b₁, b₂} : Set H) with hB
  obtain ⟨k, -, hk⟩ := L14.exists_conj_le_sylowOf h.isSylowOf_B_top (le_top : X ≤ ⊤) hX
  set X' : Subgroup H := X.map (MulAut.conj k).toMonoidHom with hX'
  have hX'B : X' ≤ B := by
    rintro _ ⟨x, hx, rfl⟩
    exact hk x hx
  have hcardX' : Nat.card X' = Nat.card X :=
    Subgroup.card_map_of_injective (MulAut.conj k).injective
  have hdvd : Nat.card X ∣ 27 := by
    have := Subgroup.card_dvd_of_le hX'B
    rwa [h.card_B, hcardX'] at this
  by_contra hgt'
  have hgt : 9 < Nat.card X := not_le.mp hgt'
  have h27 : Nat.card X = 27 := by
    have hmem : Nat.card X ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hd : Nat.divisors 27 = {1, 3, 9, 27} := by decide
    rw [hd] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hX'eq : X' = B :=
    Subgroup.eq_of_le_of_card_ge hX'B (by rw [hcardX', h27, h.card_B])
  have hcen : k * u * k⁻¹ ∈ CenS B := by
    rw [CenS, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← hX'eq] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp (hXu hx)
    have e : (MulAut.conj k).toMonoidHom x = k * x * k⁻¹ := by simp [MulAut.conj_apply]
    rw [e]
    calc k * x * k⁻¹ * (k * u * k⁻¹) = k * (x * u) * k⁻¹ := by group
      _ = k * (u * x) * k⁻¹ := by rw [hxu]
      _ = k * u * k⁻¹ * (k * x * k⁻¹) := by group
  have hu2' : (k * u * k⁻¹) ^ 2 = 1 := by
    calc (k * u * k⁻¹) ^ 2 = (k * u * k⁻¹) * (k * u * k⁻¹) := by rw [pow_two]
      _ = k * (u * u) * k⁻¹ := by group
      _ = 1 := by rw [hu2]; group
  have hu1' : k * u * k⁻¹ ≠ 1 := by
    intro h1
    apply hu1
    calc u = k⁻¹ * (k * u * k⁻¹) * k := by group
      _ = 1 := by rw [h1]; group
  have hord : orderOf (k * u * k⁻¹) = 2 := orderOf_eq_prime hu2' hu1'
  have hdvd2 : 2 ∣ Nat.card (CenS B) := by
    have := orderOf_dvd_natCard (⟨k * u * k⁻¹, hcen⟩ : ↥(CenS B))
    rwa [Subgroup.orderOf_mk, hord] at this
  exact (Nat.not_even_iff_odd.mpr h.odd_cenS_B) (even_iff_two_dvd.mpr hdvd2)


theorem FS79Hyp.isSylowOf_cen (h : FS79Hyp b t b₁ b₂ J) {u : H} (hu2 : u * u = 1) (hu1 : u ≠ 1)
    {E : Subgroup H} (hE3 : IsPGroup 3 E) (hEu : E ≤ Cen u) (hEc : Nat.card E = 9) :
    IsSylowOf 3 E (Cen u) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := L14.exists_sylowOf (G := H) (Cen u)
  have hScard := L14.isSylowOf_card hS
  have hS9 : Nat.card S ≤ 9 := h.card_le_nine_of_cen hu2 hu1 hS.2.1 hS.1
  obtain ⟨k, -, hk⟩ := L14.exists_conj_le_sylowOf hS hEu hE3
  have hEleS : Nat.card E ≤ Nat.card S := by
    have h1 : Nat.card (E.map (MulAut.conj k).toMonoidHom) = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj k).injective
    rw [← h1]
    refine Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact hk x hx
  have hS9' : Nat.card S = 9 := by omega
  refine L14.isSylowOf_of_card hEu ?_
  rw [hEc, ← hScard, hS9']

theorem isPGroup_zpowers_of_pow_three {w : H} (hw : w ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers w) := by
  intro x
  refine ⟨1, ?_⟩
  obtain ⟨x, hx⟩ := x
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  apply Subtype.ext
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw, one_zpow]

theorem FS79Hyp.conj_into_sylow (h : FS79Hyp b t b₁ b₂ J) {u v g : H} (hv2 : v * v = 1)
    (hv1 : v ≠ 1) (hgu : g * u * g⁻¹ = v) {X : Subgroup H} (hX3 : IsPGroup 3 X)
    (hXu : X ≤ Cen u) {E : Subgroup H} (hE3 : IsPGroup 3 E) (hEv : E ≤ Cen v)
    (hEc : Nat.card E = 9) :
    ∃ g' : H, g' * u * g'⁻¹ = v ∧ ∀ x ∈ X, g' * x * g'⁻¹ ∈ E := by
  have hE := h.isSylowOf_cen hv2 hv1 hE3 hEv hEc
  set X' : Subgroup H := X.map (MulAut.conj g).toMonoidHom with hX'
  have hX'3 : IsPGroup 3 X' := hX3.map _
  have hX'v : X' ≤ Cen v := by
    rintro _ ⟨x, hx, rfl⟩
    have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp (hXu hx)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := by simp [MulAut.conj_apply]
    rw [e, ← hgu]
    calc g * x * g⁻¹ * (g * u * g⁻¹) = g * (x * u) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [hxu]
      _ = g * u * g⁻¹ * (g * x * g⁻¹) := by group
  obtain ⟨c, hc, hcX⟩ := L14.exists_conj_le_sylowOf hE hX'v hX'3
  refine ⟨c * g, ?_, ?_⟩
  · have hcv : c * v = v * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    calc c * g * u * (c * g)⁻¹ = c * (g * u * g⁻¹) * c⁻¹ := by group
      _ = c * v * c⁻¹ := by rw [hgu]
      _ = v := by rw [hcv]; group
  · intro x hx
    have e : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := by simp [MulAut.conj_apply]
    have := hcX (g * x * g⁻¹) ⟨x, hx, e⟩
    rw [show c * g * x * (c * g)⁻¹ = c * (g * x * g⁻¹) * c⁻¹ by group]
    exact this

theorem FS79Hyp.fusion_B₁ (h : FS79Hyp b t b₁ b₂ J) {z g : H}
    (hz : z ∈ Subgroup.closure ({b₁, b₂} : Set H))
    (hg : g * z * g⁻¹ ∈ Subgroup.closure ({b, b₁, b₂} : Set H)) :
    ∃ j ∈ J, (∀ y ∈ Subgroup.closure ({b₁, b₂} : Set H),
        j * y * j⁻¹ ∈ Subgroup.closure ({b₁, b₂} : Set H)) ∧ g * z * g⁻¹ = j * z * j⁻¹ := by
  obtain ⟨n, hn, hnz⟩ := h.fusion_B (FS79Hyp.B₁_le_B b b₁ b₂ hz) hg rfl
  obtain ⟨k, hk, y, hy, j, hj, hn_eq, hconj, hjB⟩ := h.nor_B_decomp hn
  exact ⟨j, hj, hjB, by rw [← hnz]; exact hconj z hz⟩

end CFSG.RankThree.PartTwo.Sec21.FF81
