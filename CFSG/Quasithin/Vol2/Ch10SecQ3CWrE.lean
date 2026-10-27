module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CG

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

theorem card_range_le_of_ker_le {A B₁ B₂ : Type*} [Group A] [Finite A] [Group B₁] [Group B₂]
    (f₁ : A →* B₁) (f₂ : A →* B₂) (h : f₂.ker ≤ f₁.ker) :
    Nat.card f₁.range ≤ Nat.card f₂.range := by
  rw [← Subgroup.index_ker, ← Subgroup.index_ker]
  exact Subgroup.index_antitone h

@[expose] noncomputable def autOnHom' (T B : Subgroup G) :
    ↥(T.subgroupOf (Subgroup.normalizer (B : Set G))) →* MulAut ↥B :=
  (conjAct B).comp (T.subgroupOf (Subgroup.normalizer (B : Set G))).subtype

theorem range_autOnHom' (T B : Subgroup G) : (autOnHom' T B).range = autOn T B := by
  rw [autOnHom', MonoidHom.range_comp, Subgroup.range_subtype]
  rfl

theorem autOnHom'_eq_one {T B : Subgroup G}
    (x : ↥(T.subgroupOf (Subgroup.normalizer (B : Set G))))
    (hx : ((x : Subgroup.normalizer (B : Set G)) : G) ∈ Subgroup.centralizer (B : Set G)) :
    autOnHom' T B x = 1 := by
  refine MulEquiv.ext fun b => Subtype.ext ?_
  rw [MulAut.one_apply]
  change ((x : Subgroup.normalizer (B : Set G)) : G) * b *
    ((x : Subgroup.normalizer (B : Set G)) : G)⁻¹ = b
  rw [Subgroup.mem_centralizer_iff] at hx
  rw [← hx b b.2, mul_inv_cancel_right]

theorem mul_mem_centralizer [Finite G] {Y Q B : Subgroup G} (hR : IsPGroup 2 ↥⁅Y, Y⁆)
    (hQ : IsPGroup 2 Q) (hYQ : Y ≤ Subgroup.normalizer (Q : Set G)) (hBY : B ≤ Y)
    (hBo : Odd (Nat.card B)) {k q : G} (hk : k ∈ Y) (hq : q ∈ Q)
    (hx : k * q ∈ Subgroup.normalizer (B : Set G)) :
    k * q ∈ Subgroup.centralizer (B : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hbY := hBY hb
  set z := k * q * b * (k * q)⁻¹ * b⁻¹ with hz
  have hzB : z ∈ B := B.mul_mem ((Subgroup.mem_normalizer_iff.mp hx b).mp hb) (B.inv_mem hb)
  have h1 : q * b * q⁻¹ * b⁻¹ ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (hYQ hbY) q⁻¹).mp (Q.inv_mem hq)
    simpa [mul_assoc] using Q.mul_mem hq this
  have h2 : k * (q * b * q⁻¹ * b⁻¹) * k⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hYQ hk) _).mp h1
  have h3 : k * b * k⁻¹ * b⁻¹ ∈ ⁅Y, Y⁆ := Subgroup.commutator_mem_commutator hk hbY
  have hz' : z = k * (q * b * q⁻¹ * b⁻¹) * k⁻¹ * (k * b * k⁻¹ * b⁻¹) := by
    rw [hz]; group
  have hP : IsPGroup 2 ↥(⁅Y, Y⁆ ⊔ Q) :=
    hR.to_sup_of_normal_right' hQ ((Subgroup.commutator_le.mpr fun a ha c hc => by
      rw [commutatorElement_def]
      exact Y.mul_mem (Y.mul_mem (Y.mul_mem ha hc) (Y.inv_mem ha)) (Y.inv_mem hc)).trans hYQ)
  have hzP : z ∈ ⁅Y, Y⁆ ⊔ Q := by
    rw [hz']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left h3)
  have hodd : Odd (orderOf z) := Odd.of_dvd_nat hBo (Subgroup.orderOf_dvd_natCard B hzB)
  have h1' := eq_one_of_mem_of_odd hP hzP hodd
  rw [hz, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1'
  exact h1'.symm

theorem index_le_four_of_dvd {P : Type*} [Group P] [Finite P] {K : Subgroup P} [K.Normal]
    (hC : Subgroup.centralizer (K : Set P) = ⊥) (h2 : ∀ x : P, ∃ k : ℕ, x ^ 2 ^ k ∈ K)
    (hAut : Nat.card (MulAut K) ∣ 12 * Nat.card K) : K.index ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (MulAut.conjNormal : P →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgC : g ∈ Subgroup.centralizer (K : Set P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := congrArg (fun φ : MulAut K => ((φ ⟨y, hy⟩ : K) : P)) hg
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc y * g = g * y * g⁻¹ * g := by rw [this]
        _ = g * y := by group
    rw [hC, Subgroup.mem_bot] at hgC
    exact hgC
  have h1 : Nat.card P ∣ Nat.card (MulAut K) := by
    have := Subgroup.card_subgroup_dvd_card (MulAut.conjNormal : P →* MulAut K).range
    rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at this
  have hK0 : 0 < Nat.card K := Nat.card_pos
  have h3 : K.index ∣ 12 := by
    have h4 := h1.trans hAut
    rw [← K.card_mul_index, mul_comm 12] at h4
    exact Nat.dvd_of_mul_dvd_mul_left hK0 h4
  have hQ2 : IsPGroup 2 (P ⧸ K) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := h2 x
      exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hQ2
  have hidx : K.index = 2 ^ m := hm
  rw [hidx] at h3 ⊢
  have hm2 : m ≤ 2 := by
    by_contra hm3
    have : 2 ^ 3 ∣ 2 ^ m := Nat.pow_dvd_pow 2 (by omega)
    have := this.trans h3
    norm_num at this
  calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
    _ = 4 := by norm_num

theorem centralizer_eq_bot_of {P : Type*} [Group P] [Finite P] {Y : Subgroup P} [Y.Normal]
    (hZ : ∀ y ∈ Y, (∀ z ∈ Y, y * z = z * y) → y = 1) (h2 : ∀ x : P, ∃ k : ℕ, x ^ 2 ^ k ∈ Y)
    (hO : ∀ C : Subgroup P, C.Normal → IsPGroup 2 C → C = ⊥) :
    Subgroup.centralizer (Y : Set P) = ⊥ := by
  apply hO
  · refine ⟨fun c hc g => ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    have hy' : g⁻¹ * y * g ∈ Y := by
      simpa using (‹Y.Normal›.conj_mem y hy g⁻¹)
    have := hc _ hy'
    calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = g * c * g⁻¹ * y := by group
  · intro c
    obtain ⟨k, hk⟩ := h2 c
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    refine hZ _ hk fun z hz => ?_
    exact ((Subgroup.mem_centralizer_iff.mp ((c ^ 2 ^ k).2) z hz)).symm

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
