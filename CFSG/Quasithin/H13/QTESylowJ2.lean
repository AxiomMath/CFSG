module

public import CFSG.Quasithin.H13.QTESylowPipe
public import CFSG.Quasithin.H13.QTESylowJ2Data
public import CFSG.Quasithin.H13.NQBlockOddRankOneBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2Tab

public section

namespace CFSG.Quasithin.H13.QTESylow

open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Blueprint
open scoped Pointwise

theorem j2_sylow_overgroup_orders
    : ∃ R : Subgroup CFSG.Sporadic.J2.J, Nat.card R = 2 ^ 7 ∧
    ∀ W : Subgroup CFSG.Sporadic.J2.J, R ≤ W → ∃ s : ℕ, (s = 1 ∨ 3 ∣ s) ∧
      Nat.card W = 2 ^ 7 * s := by
  have hta : j2Data.ta = (tab 315 (CFSG.Sporadic.J2.a : CFSG.Sporadic.J2.J)).toArray := by
    rw [j2_tab_a, ← j2_ta_eq, Array.toArray_toList]
  have htb : j2Data.tb = (tab 315 (CFSG.Sporadic.J2.b : CFSG.Sporadic.J2.J)).toArray := by
    rw [j2_tab_b, ← j2_tb_eq, Array.toArray_toList]
  obtain ⟨R, hR, hW⟩ := pipeline_ordersOver (n := 315) (by norm_num) CFSG.Sporadic.J2.a
    CFSG.Sporadic.J2.b CFSG.Sporadic.J2.closure_ab hta htb (k := 7) (m := 4725)
    (by rw [CFSG.Sporadic.J2.card_J]; norm_num) (by decide) rfl j2_invValid j2_slpValid j2_qpOK
    CFSG.QuasithinUnique.Setup.X1.j2Enum.1 CFSG.QuasithinUnique.Setup.X1.j2Enum.2.1
    CFSG.QuasithinUnique.Setup.X1.j2Enum.2.2 CFSG.QuasithinUnique.Setup.X1.j2_enumOK
    (by rw [CFSG.QuasithinUnique.Setup.X1.j2_enum_size]; norm_num) j2_treeValid
    j2_edgeOK j2_aszOK j2_xsOK j2ROm rfl j2_blocksClosed j2_repsOK j2_closureOK
  refine ⟨R, hR, fun W hRW => ?_⟩
  obtain ⟨h, hh, hcard⟩ := hW W hRW
  refine ⟨_, ?_, hcard⟩
  have := List.all_eq_true.1 j2BlockSizes_check h (List.mem_range.2 hh)
  simp only [Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h1 | h3
  · exact Or.inl h1
  · exact Or.inr (Nat.dvd_of_mod_eq_zero h3)

theorem index_dvd_card_of_le_mul {G : Type*} [Group G] [Finite G] {A R M : Subgroup G}
    (hAM : A ≤ M) (hRM : R ≤ M) (hM : ∀ m ∈ M, ∃ a ∈ A, ∃ r ∈ R, m = a * r) :
    (R.subgroupOf M).index ∣ Nat.card A := by
  classical
  let incl : A →* M := Subgroup.inclusion hAM
  let _ : MulAction A (M ⧸ R.subgroupOf M) := MulAction.compHom _ incl
  have hsmul : ∀ (x : A) (q : M ⧸ R.subgroupOf M), x • q = incl x • q := fun _ _ => rfl
  have horbit : MulAction.orbit A (QuotientGroup.mk 1 : M ⧸ R.subgroupOf M) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, r, hr, hm⟩ := hM m m.2
    refine ⟨⟨a, ha⟩, ?_⟩
    show incl ⟨a, ha⟩ • (QuotientGroup.mk 1 : M ⧸ R.subgroupOf M) = QuotientGroup.mk m
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq]
    have : (incl ⟨a, ha⟩)⁻¹ * m = ⟨r, hRM hr⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, incl, Subgroup.coe_inclusion, hm]
      group
    rw [this, Subgroup.mem_subgroupOf]
    exact hr
  have hidx := MulAction.index_stabilizer A (QuotientGroup.mk 1 : M ⧸ R.subgroupOf M)
  rw [horbit, Set.ncard_univ, ← Subgroup.index_eq_card] at hidx
  rw [← hidx]
  exact Subgroup.index_dvd_card _

theorem three_free_le_sylow_of_orders {X : Type*} [Group X] [Finite X] {k : ℕ} {R : Subgroup X}
    (hR : Nat.card R = 2 ^ k)
    (hW : ∀ W : Subgroup X, R ≤ W → ∃ s : ℕ, (s = 1 ∨ 3 ∣ s) ∧ Nat.card W = 2 ^ k * s)
    (S : Sylow 2 X) (A : Subgroup X) (hA : ¬ 3 ∣ Nat.card A)
    (hAS : (A : Set X) * (S : Set X) = (S : Set X) * (A : Set X)) : A ≤ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRp : IsPGroup 2 R := IsPGroup.of_card hR
  obtain ⟨Q, hRQ⟩ := hRp.exists_le_sylow
  have hQR : (Q : Subgroup X) = R := by
    obtain ⟨s, hs, hcard⟩ := hW Q hRQ
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp Q.isPGroup'
    rcases hs with rfl | h3
    · exact (Subgroup.eq_of_le_of_card_ge hRQ (by rw [hcard, hR, mul_one])).symm
    · exfalso
      rw [hj] at hcard
      have h3' : 3 ∣ 2 ^ j := hcard ▸ Dvd.dvd.mul_left h3 _
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3')
      norm_num at this
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S Q
  set A' := A.map (MulAut.conj g).toMonoidHom with hA'
  have hA'card : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hSQ : (S : Subgroup X).map (MulAut.conj g).toMonoidHom = R := by
    rw [← hQR, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hA'R : (A' : Set X) * (R : Set X) = (R : Set X) * (A' : Set X) := by
    have hAS' : (A : Set X) * ((S : Subgroup X) : Set X) =
        ((S : Subgroup X) : Set X) * (A : Set X) := hAS
    rw [← hSQ, hA', Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hAS', Set.image_mul]
  set M := CFSG.Quasithin.H13.NQBlock.mulCommSubgroup A' R hA'R with hMdef
  have hAM : A' ≤ M := fun x hx => ⟨x, hx, 1, R.one_mem, mul_one x⟩
  have hRM : R ≤ M := fun x hx => ⟨1, A'.one_mem, x, hx, one_mul x⟩
  have hidx : (R.subgroupOf M).index ∣ Nat.card A' :=
    index_dvd_card_of_le_mul hAM hRM fun m hm => by
      obtain ⟨a, ha, r, hr, rfl⟩ := hm
      exact ⟨a, ha, r, hr, rfl⟩
  obtain ⟨s, hs, hcard⟩ := hW M hRM
  have hidxs : (R.subgroupOf M).index = s := by
    have h1 := Subgroup.card_mul_index (R.subgroupOf M)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv, hR, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hs1 : s = 1 := by
    rcases hs with h | h3
    · exact h
    · exfalso
      rw [hidxs, hA'card] at hidx
      exact hA (h3.trans hidx)
  have hMR : M = R := (Subgroup.eq_of_le_of_card_ge hRM (by rw [hcard, hs1, hR, mul_one])).symm
  have hA'le : A' ≤ R := hMR ▸ hAM
  intro x hx
  have hgx : g * x * g⁻¹ ∈ R := hA'le ⟨x, hx, rfl⟩
  rw [← hSQ] at hgx
  obtain ⟨y, hy, hyx⟩ := hgx
  have : y = x := by
    have e : g * y * g⁻¹ = g * x * g⁻¹ := hyx
    exact mul_left_cancel (mul_right_cancel e)
  rw [← this]
  exact hy

theorem sylow_product_ne_of_three_free {X : Type*} [Group X] [Finite X] (S : Sylow 2 X)
    (hrig : ∀ A : Subgroup X, ¬ 3 ∣ Nat.card A →
      (A : Set X) * (S : Set X) = (S : Set X) * (A : Set X) → A ≤ S)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (P : Subgroup X) (hP : IsPGroup p P) (hP1 : P ≠ ⊥) :
    (P : Set X) * (S : Set X) ≠ (S : Set X) * (P : Set X) := by
  intro hPS
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have h3 : ¬ 3 ∣ Nat.card P := by
    rw [hn]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hle := hrig P h3 hPS
  apply hP1
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    S.isPGroup'.to_le ((Subgroup.zpowers_le).2 (hle hx))
  have hxp : IsPGroup p (Subgroup.zpowers x) := hP.to_le ((Subgroup.zpowers_le).2 hx)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop := IsPGroup.coprime_card_of_ne 2 p (by omega) _ _ hx2 hxp
  have h1 : Nat.card (Subgroup.zpowers x) = 1 := (Nat.coprime_self _).1 hcop
  rw [Subgroup.card_eq_one, Subgroup.zpowers_eq_bot] at h1
  exact h1

theorem overgroup_orders_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) {k : ℕ}
    (h : ∃ R : Subgroup Y, Nat.card R = 2 ^ k ∧ ∀ W : Subgroup Y, R ≤ W →
      ∃ s : ℕ, (s = 1 ∨ 3 ∣ s) ∧ Nat.card W = 2 ^ k * s) :
    ∃ R : Subgroup X, Nat.card R = 2 ^ k ∧ ∀ W : Subgroup X, R ≤ W →
      ∃ s : ℕ, (s = 1 ∨ 3 ∣ s) ∧ Nat.card W = 2 ^ k * s := by
  obtain ⟨R, hR, hW⟩ := h
  refine ⟨R.comap φ.toMonoidHom, ?_, fun W hW0 => ?_⟩
  · rw [← hR]
    exact Nat.card_congr (φ.toEquiv.subtypeEquiv fun _ => Iff.rfl)
  · have hle : R ≤ W.map φ.toMonoidHom := by
      intro y hy
      refine ⟨φ.symm y, hW0 ?_, φ.apply_symm_apply y⟩
      show φ (φ.symm y) ∈ R
      rw [φ.apply_symm_apply]
      exact hy
    obtain ⟨s, hs, hcard⟩ := hW _ hle
    exact ⟨s, hs, by rw [← hcard, Subgroup.card_map_of_injective φ.injective]⟩

theorem three_free_rigidity_of_orders {X : Type*} [Group X] [Finite X] {k : ℕ}
    (h : ∃ R : Subgroup X, Nat.card R = 2 ^ k ∧ ∀ W : Subgroup X, R ≤ W →
      ∃ s : ℕ, (s = 1 ∨ 3 ∣ s) ∧ Nat.card W = 2 ^ k * s) (S : Sylow 2 X) :
    (∀ A : Subgroup X, ¬ 3 ∣ Nat.card A →
      (A : Set X) * (S : Set X) = (S : Set X) * (A : Set X) → A ≤ S) ∧
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ P : Subgroup X, IsPGroup p P → P ≠ ⊥ →
      (P : Set X) * (S : Set X) ≠ (S : Set X) * (P : Set X) := by
  obtain ⟨R, hR, hW⟩ := h
  have hrig : ∀ A : Subgroup X, ¬ 3 ∣ Nat.card A →
      (A : Set X) * (S : Set X) = (S : Set X) * (A : Set X) → A ≤ S :=
    fun A hA hAS => three_free_le_sylow_of_orders hR hW S A hA hAS
  exact ⟨hrig, fun p hp hp5 P hP hP1 => sylow_product_ne_of_three_free S hrig hp hp5 P hP hP1⟩

theorem j2_three_free_sylow_product_rigidity
    {K : Type*} [Group K] [Finite K]
    (e : K ≃* NativeSporadic.J2) (S : Sylow 2 K) :
    (∀ A : Subgroup K, ¬ 3 ∣ Nat.card A →
      (A : Set K) * (S : Set K) = (S : Set K) * (A : Set K) → A ≤ S) ∧
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ P : Subgroup K, IsPGroup p P → P ≠ ⊥ →
      (P : Set K) * (S : Set K) ≠ (S : Set K) * (P : Set K) :=
  three_free_rigidity_of_orders (@overgroup_orders_of_mulEquiv K ↥CFSG.Sporadic.J2.J
    inferInstance inferInstance (e.trans CFSG.Sporadic.J2.nativeEquiv) 7
    j2_sylow_overgroup_orders) S

end CFSG.Quasithin.H13.QTESylow
