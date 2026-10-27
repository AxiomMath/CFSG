module

public import CFSG.RankThree.PartOne.S11c.UnitaryFiveData

public section

namespace CFSG.RankThree.PartOne.HNRed

open Subgroup CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def FiveSubgroupsCommute (Γ : Type*) [Group Γ] : Prop :=
  ∀ P : Subgroup Γ, IsPGroup 5 P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a

section Heisenberg

variable {G : Type*} [Group G]

theorem isPGroup_zpowers_of_pow_five {g : G} (h : g ^ 5 = 1) : IsPGroup 5 (zpowers g) :=
  IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one h)

theorem zpowers_le_normalizer_of_commute {a b : G} (h : Commute a b) :
    zpowers a ≤ normalizer (zpowers b : Set G) := by
  have ha : a ∈ centralizer (zpowers b : Set G) := by
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
    exact (h.symm.zpow_left n).eq
  exact (zpowers_le).2 (centralizer_le_normalizer _ ha)

theorem mem_normalizer_of_conj_mem {N : Subgroup G} {y : G}
    (h1 : ∀ n ∈ N, y * n * y⁻¹ ∈ N) (h2 : ∀ n ∈ N, y⁻¹ * n * y ∈ N) :
    y ∈ normalizer (N : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => h1 g hg, fun hg => ?_⟩
  have h3 := h2 _ hg
  have e : y⁻¹ * (y * g * y⁻¹) * y = g := by group
  rwa [e] at h3

theorem isPGroup_closure_heisenberg {x y : G} (hx : x ^ 5 = 1) (hy : y ^ 5 = 1)
    (hzx : Commute ⁅y, x⁆ x) (hzy : Commute ⁅y, x⁆ y) (hz : ⁅y, x⁆ ^ 5 = 1) :
    IsPGroup 5 (Subgroup.closure {x, y}) := by
  set z : G := ⁅y, x⁆ with hzdef
  have hyx : y * x * y⁻¹ = z * x := by rw [hzdef, commutatorElement_def]; group
  have hyzy : y * z * y⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hzy.eq.symm
  have hyzy' : y⁻¹ * z * y = z := by
    calc y⁻¹ * z * y = y⁻¹ * (z * y) := by group
      _ = y⁻¹ * (y * z) := by rw [hzy.eq]
      _ = z := by group
  have hyx' : y⁻¹ * x * y = z⁻¹ * x := by
    have h1 : x = z * (y⁻¹ * x * y) := by
      calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
        _ = y⁻¹ * (z * x) * y := by rw [hyx]
        _ = (y⁻¹ * z * y) * (y⁻¹ * x * y) := by group
        _ = z * (y⁻¹ * x * y) := by rw [hyzy']
    calc y⁻¹ * x * y = z⁻¹ * (z * (y⁻¹ * x * y)) := by group
      _ = z⁻¹ * x := by rw [← h1]
  set N : Subgroup G := zpowers x ⊔ zpowers z with hN
  have hxN : x ∈ N := mem_sup_left (mem_zpowers x)
  have hzN : z ∈ N := mem_sup_right (mem_zpowers z)
  have hNp : IsPGroup 5 N :=
    (isPGroup_zpowers_of_pow_five hx).to_sup_of_normal_right' (isPGroup_zpowers_of_pow_five hz)
      (zpowers_le_normalizer_of_commute hzx.symm)
  have h1 : ∀ n ∈ N, y * n * y⁻¹ ∈ N := by
    have hle : N ≤ N.comap (MulAut.conj y).toMonoidHom := by
      refine sup_le ((zpowers_le).2 ?_) ((zpowers_le).2 ?_)
      · show y * x * y⁻¹ ∈ N
        rw [hyx]
        exact N.mul_mem hzN hxN
      · show y * z * y⁻¹ ∈ N
        rw [hyzy]
        exact hzN
    intro n hn
    exact hle hn
  have h2 : ∀ n ∈ N, y⁻¹ * n * y ∈ N := by
    have hle : N ≤ N.comap (MulAut.conj y⁻¹).toMonoidHom := by
      refine sup_le ((zpowers_le).2 ?_) ((zpowers_le).2 ?_)
      · show y⁻¹ * x * y⁻¹⁻¹ ∈ N
        rw [inv_inv, hyx']
        exact N.mul_mem (N.inv_mem hzN) hxN
      · show y⁻¹ * z * y⁻¹⁻¹ ∈ N
        rw [inv_inv, hyzy']
        exact hzN
    intro n hn
    have := hle hn
    simpa using this
  have hyN : y ∈ normalizer (N : Set G) := mem_normalizer_of_conj_mem h1 h2
  have hQ : IsPGroup 5 (zpowers y ⊔ N : Subgroup G) :=
    (isPGroup_zpowers_of_pow_five hy).to_sup_of_normal_right' hNp ((zpowers_le).2 hyN)
  refine hQ.to_le ?_
  rw [Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | hg
  · exact mem_sup_right hxN
  · rw [Set.mem_singleton_iff] at hg
    subst hg
    exact mem_sup_left (mem_zpowers g)

end Heisenberg

section Sylow

theorem exists_conj_le_of_card_dvd_pow {Γ : Type*} [Group Γ] [Finite Γ] {p : ℕ} [Fact p.Prime]
    (T : Subgroup Γ) (hT : p ^ (Nat.card Γ).factorization p ∣ Nat.card T) {A : Subgroup Γ}
    (hA : IsPGroup p A) : ∃ c : Γ, ∀ x ∈ A, c * x * c⁻¹ ∈ T := by
  classical
  have hTΓ : Nat.card T ∣ Nat.card Γ := Subgroup.card_subgroup_dvd_card T
  have hfac : (Nat.card T).factorization p = (Nat.card Γ).factorization p := by
    have h1 : (Nat.card T).factorization p ≤ (Nat.card Γ).factorization p :=
      ((Nat.factorization_le_iff_dvd (Nat.card_pos.ne') (Nat.card_pos.ne')).2 hTΓ) p
    have h2 : (Nat.card Γ).factorization p ≤ (Nat.card T).factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization Fact.out (Nat.card_pos.ne')).1 hT
    exact le_antisymm h1 h2
  obtain ⟨P⟩ : Nonempty (Sylow p T) := inferInstance
  set P' : Subgroup Γ := (P : Subgroup T).map T.subtype with hP'
  have hP'card : Nat.card P' = p ^ (Nat.card Γ).factorization p := by
    have h1 : Nat.card P' = Nat.card (P : Subgroup T) :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ T.subtype_injective).symm.toEquiv
    rw [h1, P.card_eq_multiplicity, hfac]
  let Q₀ : Sylow p Γ := Sylow.ofCard P' hP'card
  obtain ⟨Q, hQ⟩ := hA.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ Q₀ Q
  refine ⟨g⁻¹, fun x hx => ?_⟩
  have hxQ : x ∈ (Q : Subgroup Γ) := hQ hx
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  have hQ₀ : ((Q₀ : Subgroup Γ)) = P' := rfl
  rw [hQ₀] at hxQ
  obtain ⟨t, -, ht⟩ := hxQ
  have h2 : g⁻¹ * x * g = (t : Γ) := by
    have : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
      simp [MulAut.smul_def]
    rw [← this, ← ht]
    rfl
  rw [inv_inv, h2]
  exact t.2

theorem fiveSubgroupsCommute_of_conj_abelian {C : Type*} [Group C] (H : Subgroup C)
    (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x)
    (hcon : ∀ P : Subgroup C, IsPGroup 5 P → ∃ g : C, ∀ x ∈ P, g * x * g⁻¹ ∈ H) :
    FiveSubgroupsCommute C := by
  intro P hP a ha b hb
  obtain ⟨g, hg⟩ := hcon P hP
  have h := hH _ (hg a ha) _ (hg b hb)
  have h2 : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
    calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      _ = (g * b * g⁻¹) * (g * a * g⁻¹) := h
      _ = g * (b * a) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h2)

theorem fiveSubgroupsCommute_of_abelian {Γ : Type*} [Group Γ] [Finite Γ] (T : Subgroup Γ)
    (hT : 5 ^ (Nat.card Γ).factorization 5 ∣ Nat.card T)
    (hab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) : FiveSubgroupsCommute Γ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact fiveSubgroupsCommute_of_conj_abelian T hab fun P hP =>
    exists_conj_le_of_card_dvd_pow T hT hP

end Sylow

section Unitary

theorem no_unitary_three_five_of_fiveSubgroupsCommute {Γ : Type*} [Group Γ]
    (hab : FiveSubgroupsCommute Γ) {B : Type} [Group B]
    (hB : StatedClassicalModel B .PSU 3 5 1) (ι : B →* Γ) (hι : Function.Injective ι) :
    False := by
  obtain ⟨x, y, h, m, hm, hx, hy, hcx, hcy, hz5, hz1, -⟩ := unitary_three_five_heisenberg_data hB
  have hP : IsPGroup 5 ((Subgroup.closure {x, y}).map ι) :=
    (isPGroup_closure_heisenberg hx hy hcx hcy hz5).map ι
  have hxm : ι x ∈ (Subgroup.closure {x, y}).map ι :=
    ⟨x, Subgroup.subset_closure (by simp), rfl⟩
  have hym : ι y ∈ (Subgroup.closure {x, y}).map ι :=
    ⟨y, Subgroup.subset_closure (by simp), rfl⟩
  have hc := hab _ hP _ hxm _ hym
  have hxy : x * y = y * x := hι (by rw [map_mul, map_mul]; exact hc)
  exact hz1 (commutatorElement_eq_one_iff_mul_comm.2 hxy.symm)

end Unitary

end CFSG.RankThree.PartOne.HNRed
