module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165SylC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Lift
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin CFSG.ABGLocalTools

namespace Om8Seven

theorem pow_eq_one_of_mem_sup_zpowers {G : Type*} [Group G] {p : ℕ} {x z : G} (hx : x ^ p = 1)
    (hz : z ^ p = 1) (hc : Commute x z) {g : G}
    (hg : g ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z) : g ^ p = 1 := by
  have key : ∀ g ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z, ∃ i j : ℤ, g = x ^ i * z ^ j := by
    intro g hg
    rw [Subgroup.sup_eq_closure] at hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact ⟨i, 0, by simp⟩
      · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact ⟨0, j, by simp⟩
    | one => exact ⟨0, 0, by simp⟩
    | mul a b _ _ ha hb =>
      obtain ⟨i, j, rfl⟩ := ha
      obtain ⟨k, l, rfl⟩ := hb
      refine ⟨i + k, j + l, ?_⟩
      have h1 : z ^ j * x ^ k = x ^ k * z ^ j := (hc.symm.zpow_zpow j k).eq
      calc x ^ i * z ^ j * (x ^ k * z ^ l) = x ^ i * (z ^ j * x ^ k) * z ^ l := by group
        _ = x ^ i * (x ^ k * z ^ j) * z ^ l := by rw [h1]
        _ = x ^ (i + k) * z ^ (j + l) := by rw [zpow_add, zpow_add]; group
    | inv a _ ha =>
      obtain ⟨i, j, rfl⟩ := ha
      refine ⟨-i, -j, ?_⟩
      have h1 : z ^ (-j) * x ^ (-i) = x ^ (-i) * z ^ (-j) := (hc.symm.zpow_zpow (-j) (-i)).eq
      rw [mul_inv_rev, ← zpow_neg, ← zpow_neg, h1]
  obtain ⟨i, j, rfl⟩ := key g hg
  have h1 : (x ^ i * z ^ j) ^ p = (x ^ i) ^ p * (z ^ j) ^ p :=
    (hc.zpow_zpow i j).mul_pow p
  rw [h1, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm i, mul_comm j,
    zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hx, hz]
  simp

theorem isPGroup_sup_zpowers {G : Type*} [Group G] {p : ℕ} {x z : G} (hx : x ^ p = 1)
    (hz : z ^ p = 1) (hc : Commute x z) :
    IsPGroup p ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers z) := fun g =>
  ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_eq_one_of_mem_sup_zpowers hx hz hc g.2)⟩

theorem not_isCyclic_sup_zpowers {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {x z : G} (hx : orderOf x = p) (hz : z ^ p = 1) (hc : Commute x z)
    (hzx : z ∉ Subgroup.zpowers x) :
    ¬ IsCyclic ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers z) := by
  intro hcyc
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers z) :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_eq_one_of_mem_sup_zpowers hxp hz hc g.2)
  have hle : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers z) ≤ p := by
    rw [← hord]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hgp)
  have hxH : Subgroup.zpowers x ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers z := le_sup_left
  have heq : Subgroup.zpowers x = Subgroup.zpowers x ⊔ Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge hxH (by rw [Nat.card_zpowers, hx]; exact hle)
  exact hzx (heq ▸ (le_sup_right : Subgroup.zpowers z ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers z)
    (Subgroup.mem_zpowers z))

theorem isSylowOf_map_range {M B : Type*} [Group M] [Finite M] [Group B] (φ : M →* B) {q : ℕ}
    (hq : q.Prime) {T : Subgroup M} (hT : IsPGroup q T) (hTi : ¬ q ∣ T.index) :
    IsSylowOf q (T.map φ) φ.range := by
  haveI : Fact q.Prime := ⟨hq⟩
  let P : Sylow q M := hT.toSylow hTi
  refine ⟨P.mapSurjective φ.rangeRestrict_surjective, ?_⟩
  rw [Sylow.coe_mapSurjective]
  change (T.map φ.rangeRestrict).map φ.range.subtype = T.map φ
  rw [Subgroup.map_map]
  rfl

theorem exists_isPGroup_noncyclic_le_normalizer_of_isSylowOf {M B : Type*} [Group M] [Finite M]
    [Group B] [Finite B] (φ : M →* B) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {T : Subgroup M}
    (hT : IsPGroup q T) (hTi : ¬ q ∣ T.index) {T' : Subgroup B} (hT' : IsSylowOf q T' φ.range)
    {X : Subgroup B} (hXr : X ≤ φ.range) (hXp : IsPGroup p X) (hXc : ¬ IsCyclic X)
    (hXN : X ≤ Subgroup.normalizer (T' : Set B)) :
    ∃ Y : Subgroup M, Y ≤ Subgroup.normalizer (T : Set M) ∧ IsPGroup p Y ∧ ¬ IsCyclic Y := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨k, hk, hconj⟩ := (isSylowOf_map_range φ hq hT hTi).exists_mem_conj hT'
  let c : MulAut B := MulAut.conj k⁻¹
  have hc : ∀ x : B, c x = k⁻¹ * x * k := fun x => by simp [c]
  let X₁ : Subgroup B := X.map c.toMonoidHom
  have hX₁r : X₁ ≤ φ.range := by
    rintro _ ⟨x, hx, rfl⟩
    have : c x = k⁻¹ * x * k := hc x
    change c x ∈ φ.range
    rw [this]
    exact φ.range.mul_mem (φ.range.mul_mem (φ.range.inv_mem hk) (hXr hx)) hk
  have hX₁p : IsPGroup p X₁ := hXp.map c.toMonoidHom
  have hX₁c : ¬ IsCyclic X₁ := fun hcyc =>
    hXc ((MulEquiv.isCyclic (Subgroup.equivMapOfInjective X c.toMonoidHom c.injective)).2 hcyc)
  have e : ∀ u : B, u ∈ T.map φ ↔ k * u * k⁻¹ ∈ T' := by
    intro u
    rw [hconj (k * u * k⁻¹)]
    have : k⁻¹ * (k * u * k⁻¹) * k = u := by group
    rw [this]
  have hX₁N : X₁ ≤ Subgroup.normalizer ((T.map φ : Subgroup B) : Set B) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hxN := Subgroup.mem_normalizer_iff.1 (hXN hx)
    have hy : c.toMonoidHom x = k⁻¹ * x * k := hc x
    rw [e h, e (c.toMonoidHom x * h * (c.toMonoidHom x)⁻¹), hy]
    have : k * (k⁻¹ * x * k * h * (k⁻¹ * x * k)⁻¹) * k⁻¹ = x * (k * h * k⁻¹) * x⁻¹ := by group
    rw [this]
    exact hxN (k * h * k⁻¹)
  exact Om8Lift.exists_isPGroup_noncyclic_le_normalizer φ hp hq hT hTi hX₁r hX₁p hX₁c hX₁N

end Om8Seven

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

theorem exists_orderOf_eq_seven_mem_scalarSub (hK : Nat.card S.K = 8) :
    ∃ z ∈ scalarSub S, orderOf z = 7 := by
  haveI := S.finite_mulAut_carrier
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := scalarSub S) 7
    (by rw [card_scalarSub S hK])
  exact ⟨z, z.2, by rw [Subgroup.orderOf_coe, hz]⟩

theorem exists_isPGroup_noncyclic_le_normalizer_of_seven_pow_three_dvd (hK : Nat.card S.K = 8)
    (hΩ : Nat.card S.omega = 254016) {M : Type*} [Group M] [Finite M] (φ : M →* MulAut W)
    (hΩr : S.omega ≤ φ.range) (hrN : φ.range ≤ omegaNorm S) (h7 : 7 ^ 3 ∣ Nat.card φ.range)
    {T : Subgroup M} (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) :
    ∃ Y : Subgroup M, Y ≤ Subgroup.normalizer (T : Set M) ∧ IsPGroup 7 Y ∧ ¬ IsCyclic Y := by
  haveI := S.finite_mulAut_carrier
  obtain ⟨T', d, -, hT'I, hT'S, hd7, hdN⟩ :=
    exists_isSylowOf_two_normalized_by_seven S hK hΩ hΩr hrN
  obtain ⟨z, hzS, hz7⟩ := exists_orderOf_eq_seven_mem_scalarSub S hK
  have hxΩ : S.jHom (d, d) ∈ S.omega := omega0_le_omega S ⟨(d, d), rfl⟩
  have hxI : S.jHom (d, d) ∈ isoSub S := omega_le_isoSub S hxΩ
  have hxL : S.jHom (d, d) ∈ linSub S := ((mem_isoSub_iff S).1 hxI).1
  have hzr : z ∈ φ.range := scalarSub_le_of_seven_pow_three_dvd S hK hrN h7 hzS
  have hcomm : Commute (S.jHom (d, d)) z := (scalarSub_commute S hzS hxL).symm
  have hzC : z ∈ Subgroup.centralizer (T' : Set (MulAut W)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (scalarSub_commute S hzS ((mem_isoSub_iff S).1 (hT'I hh)).1).symm
  have hzN : z ∈ Subgroup.normalizer (T' : Set (MulAut W)) :=
    Subgroup.centralizer_le_normalizer _ hzC
  have hzx : z ∉ Subgroup.zpowers (S.jHom (d, d)) := by
    intro hz'
    have hzI : z ∈ isoSub S := Subgroup.zpowers_le.2 hxI hz'
    have hz1 : z ∈ scalarSub S ⊓ isoSub S := Subgroup.mem_inf.2 ⟨hzS, hzI⟩
    rw [scalarSub_inf_isoSub S, Subgroup.mem_bot] at hz1
    rw [hz1, orderOf_one] at hz7
    exact absurd hz7 (by norm_num)
  have hz7' : z ^ 7 = 1 := by rw [← hz7]; exact pow_orderOf_eq_one z
  have hx7' : S.jHom (d, d) ^ 7 = 1 := by rw [← hd7]; exact pow_orderOf_eq_one _
  refine Om8Seven.exists_isPGroup_noncyclic_le_normalizer_of_isSylowOf φ Nat.prime_seven
    Nat.prime_two hT hTi hT'S
    (X := Subgroup.zpowers (S.jHom (d, d)) ⊔ Subgroup.zpowers z)
    (sup_le (Subgroup.zpowers_le.2 (hΩr hxΩ)) (Subgroup.zpowers_le.2 hzr))
    (Om8Seven.isPGroup_sup_zpowers hx7' hz7' hcomm)
    (Om8Seven.not_isCyclic_sup_zpowers Nat.prime_seven hd7 hz7' hcomm hzx)
    (sup_le (Subgroup.zpowers_le.2 hdN) (Subgroup.zpowers_le.2 hzN))

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
