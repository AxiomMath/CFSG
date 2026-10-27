module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU62Dg
public import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCenter
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open Matrix CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
open CFSG.RankThree.PartTwo.Sec4.Item434AltPerm (factorization_three_pow_mul)
open CFSG.Assembly.RankThreeEven (projSU)

@[expose] noncomputable def torusD : Subgroup P6 := diagP6.range

@[expose] noncomputable def r0 : Subgroup P6 :=
  torusD ⊔ (Subgroup.zpowers (permP6 cyc1) ⊔ Subgroup.zpowers (permP6 cyc2))

theorem isPGroup_three_of_pow_three {G : Type} [Group G] {H : Subgroup G}
    (h : ∀ x ∈ H, x ^ 3 = 1) : IsPGroup 3 H := by
  intro x
  exact ⟨1, Subtype.ext (by simpa using h x.1 x.2)⟩

theorem diagSU_pow_three (d : diagSU) : d ^ 3 = 1 :=
  Subtype.ext (funext fun i => by
    rw [Subgroup.coe_pow, Pi.pow_apply]
    exact u62_units_pow_three _)

theorem isPGroup_torusD : IsPGroup 3 torusD := by
  refine isPGroup_three_of_pow_three ?_
  rintro _ ⟨d, rfl⟩
  rw [← map_pow, diagSU_pow_three, map_one]

theorem isPGroup_zpowers_permP6 {σ : Equiv.Perm (Fin 6)} (hσ : σ ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers (permP6 σ)) := by
  have h3 : permP6 σ ^ 3 = 1 := by rw [← map_pow, hσ, map_one]
  refine isPGroup_three_of_pow_three ?_
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← zpow_natCast, ← _root_.zpow_mul, Int.mul_comm, _root_.zpow_mul, zpow_natCast, h3,
    _root_.one_zpow]

theorem permP6_mem_normalizer (σ : Equiv.Perm (Fin 6)) :
    permP6 σ ∈ Subgroup.normalizer ((torusD : Subgroup P6) : Set P6) := by
  have key : ∀ τ : Equiv.Perm (Fin 6), ∀ x ∈ torusD, permP6 τ * x * (permP6 τ)⁻¹ ∈ torusD := by
    rintro τ _ ⟨d, rfl⟩
    rw [permP6_mul_diagP6]
    exact ⟨_, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key σ x, fun hx => ?_⟩
  have h := key σ⁻¹ _ hx
  have e : permP6 σ⁻¹ * (permP6 σ * x * (permP6 σ)⁻¹) * (permP6 σ⁻¹)⁻¹ = x := by
    rw [map_inv]
    group
  rwa [e] at h

theorem isPGroup_r0 : IsPGroup 3 r0 := by
  have h1 := isPGroup_zpowers_permP6 cyc1_pow_three
  have h2 := isPGroup_zpowers_permP6 cyc2_pow_three
  have hcomm : permP6 cyc2 * permP6 cyc1 = permP6 cyc1 * permP6 cyc2 := by
    rw [← map_mul, ← map_mul, cyc1_mul_cyc2.symm]
  have hW : IsPGroup 3 (Subgroup.zpowers (permP6 cyc1) ⊔ Subgroup.zpowers (permP6 cyc2) :
      Subgroup P6) :=
    h1.to_sup_of_normal_left' h2 (Subgroup.zpowers_le.mpr (mem_normalizer_zpowers_of_commute hcomm))
  exact isPGroup_torusD.to_sup_of_normal_left' hW
    (sup_le (Subgroup.zpowers_le.mpr (permP6_mem_normalizer _))
      (Subgroup.zpowers_le.mpr (permP6_mem_normalizer _)))

theorem diagP6_mem_r0 (d : diagSU) : diagP6 d ∈ r0 :=
  Subgroup.mem_sup_left ⟨d, rfl⟩

theorem permP6_cyc1_mem_r0 : permP6 cyc1 ∈ r0 :=
  Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))

theorem permP6_cyc2_mem_r0 : permP6 cyc2 ∈ r0 :=
  Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem factorization_card_P6 : (Nat.card P6).factorization 3 = 6 := by
  rw [← Nat.card_congr u6Equiv.toEquiv,
    CFSG.RankThree.PartTwo.Sec21.card_projSU (m := 6) (b := 1) (by norm_num) le_rfl,
    show CFSG.Open.ordTwistedA (6 - 1) (2 ^ 1) = 3 ^ 6 * 12615680 by decide]
  exact factorization_three_pow_mul 6 (by norm_num)

theorem not_dvd_card_P6 : ¬ 3 ^ (6 + 1) ∣ Nat.card P6 := by
  have hne : Nat.card P6 ≠ 0 := Nat.card_pos.ne'
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne, factorization_card_P6]
  norm_num

theorem comm_matrix6 {g h : S6} (hc : mk6 g * mk6 h = mk6 h * mk6 g) :
    ∃ c : F4ˣ, (g : GL (Fin 6) F4) * (h : GL (Fin 6) F4) =
      GeneralLinearGroup.scalar (Fin 6) c * ((h : GL (Fin 6) F4) * (g : GL (Fin 6) F4)) := by
  rw [← map_mul, ← map_mul, mk_eq_mk_iff6] at hc
  exact hc

theorem blockD_mem (a b : F4ˣ) : (![a, a, a, b, b, b] : Fin 6 → F4ˣ) ∈ diagSU := by
  rw [mem_diagSU, Fin.prod_univ_six]
  have ha := u62_units_pow_three a
  have hb := u62_units_pow_three b
  show a * a * a * b * b * b = 1
  calc a * a * a * b * b * b = (a * (a * a)) * (b * (b * b)) := by simp only [mul_assoc]
    _ = a ^ 3 * b ^ 3 := by simp only [pow_three]
    _ = 1 := by rw [ha, hb, one_mul]

theorem exists_witness_of_central {u : P6} (hu3 : orderOf u = 3) (hcomm : ∀ q ∈ r0, q * u = u * q) :
    ∃ g : P6, (g * u * g⁻¹) * u = u * (g * u * g⁻¹) ∧ g * u * g⁻¹ ∉ Subgroup.zpowers u := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective u
  have hu : u = mk6 g := hg.symm
  subst hu
  have h1 : ∀ d ∈ diagSU, ∃ c : F4ˣ, (g : GL (Fin 6) F4) * dgl d =
      GeneralLinearGroup.scalar (Fin 6) c * (dgl d * (g : GL (Fin 6) F4)) := fun d hd =>
    comm_matrix6 (g := g) (h := diagS6 ⟨d, hd⟩) (hcomm _ (diagP6_mem_r0 ⟨d, hd⟩)).symm
  have h2 : ∃ c : F4ˣ, (g : GL (Fin 6) F4) * pgl cyc1 =
      GeneralLinearGroup.scalar (Fin 6) c * (pgl cyc1 * (g : GL (Fin 6) F4)) :=
    comm_matrix6 (g := g) (h := permS6 cyc1) (hcomm _ permP6_cyc1_mem_r0).symm
  have h3 : ∃ c : F4ˣ, (g : GL (Fin 6) F4) * pgl cyc2 =
      GeneralLinearGroup.scalar (Fin 6) c * (pgl cyc2 * (g : GL (Fin 6) F4)) :=
    comm_matrix6 (g := g) (h := permS6 cyc2) (hcomm _ permP6_cyc2_mem_r0).symm
  obtain ⟨a, b, hab⟩ := u62_diag_block h1 h2 h3
  set d₀ : diagSU := ⟨![a, a, a, b, b, b], blockD_mem a b⟩ with hd₀
  have hgd : mk6 g = diagP6 d₀ := congrArg mk6 (Subtype.ext hab : g = diagS6 d₀)
  rw [hgd] at hu3 ⊢
  have hne : a ≠ b := by
    rintro rfl
    have h1' : diagP6 d₀ = diagP6 1 := by
      rw [diagP6_eq_iff]
      refine ⟨a, fun i => ?_⟩
      fin_cases i <;> simp [hd₀]
    rw [h1', map_one, orderOf_one] at hu3
    exact absurd hu3 (by norm_num)
  set τ : Equiv.Perm (Fin 6) := Equiv.swap 2 3 with hτ
  have hτ0 : τ⁻¹ 0 = 0 := by decide
  have hτ2 : τ⁻¹ 2 = 3 := by decide
  have key : ∀ e : diagSU, e.1 0 = e.1 2 → diagP6 (permAct τ d₀) ≠ diagP6 e := by
    intro e he h
    obtain ⟨c, hc⟩ := (diagP6_eq_iff _ _).mp h
    have h0 := hc 0
    have h2 := hc 2
    have e0 : (permAct τ d₀).1 0 = a := by
      show d₀.1 (τ⁻¹ 0) = a
      rw [hτ0]
      rfl
    have e2 : (permAct τ d₀).1 2 = b := by
      show d₀.1 (τ⁻¹ 2) = b
      rw [hτ2]
      rfl
    rw [e0] at h0
    rw [e2] at h2
    apply hne
    rw [h0, h2, he]
  refine ⟨permP6 τ, ?_, ?_⟩
  · rw [permP6_mul_diagP6, ← map_mul, ← map_mul]
    exact congrArg diagP6 (mul_comm (permAct τ d₀) d₀)
  · intro hmem
    rw [permP6_mul_diagP6] at hmem
    have hq3 : diagP6 d₀ ^ 3 = 1 := by rw [← map_pow, diagSU_pow_three, map_one]
    rcases mem_zpowers_cases_of_pow_three hq3 hmem with h | h | h
    · exact key 1 rfl (h.trans (map_one diagP6).symm)
    · exact key d₀ rfl h
    · exact key d₀⁻¹ rfl (h.trans (map_inv diagP6 d₀).symm)

theorem listRow_P6 : ListRow P6 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := isPGroup_r0.exists_le_sylow
  refine listRow_of_sylow_center 6 (Q : Subgroup P6)
    (by rw [Sylow.card_eq_multiplicity, factorization_card_P6]) not_dvd_card_P6 ?_
  intro u _ hu3 hcent
  exact exists_witness_of_central hu3 fun q hq => hcent q (hQ hq)

theorem listRow_u62 : ListRow (projSU 6 2 1) :=
  ListRow.of_mulEquiv u6Equiv.symm listRow_P6

end CFSG.RankThree.PartTwo.Sec4.RonanK432
