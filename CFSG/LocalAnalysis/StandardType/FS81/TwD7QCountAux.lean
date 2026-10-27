module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7QCent
public import CFSG.LocalAnalysis.StandardType.FS81.TwD7BetaNormElements

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81

open Subgroup
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_subgroupOf_eq {G : Type} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥H := by
  rw [← Subgroup.card_subtype K (H.subgroupOf K), Subgroup.map_subgroupOf_eq_of_le h]

private theorem ggAutomizer_eq_range_normalizerMonoidHom {G : Type} [Group G] (A : Subgroup G) :
    ggAutomizer ⊤ A = A.normalizerMonoidHom.range := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨g, -, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφ
    exact ⟨⟨g, hgN⟩, MulEquiv.ext fun b => Subtype.ext (by
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact (hφg b).symm)⟩
  · rintro ⟨x, rfl⟩
    have hx : A.normalizerMonoidHom x = ggConjAut A x.2 := by
      refine MulEquiv.ext fun b => Subtype.ext ?_
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, ggConjAut_apply]
    rw [hx]
    exact ggConjAut_mem_ggAutomizer (Subgroup.mem_top (x : G)) x.2

theorem card_ggAutomizer_mul_card_centralizer {G : Type} [Group G] [Finite G] (A : Subgroup G) :
    Nat.card ↥(ggAutomizer ⊤ A) * Nat.card ↥(Subgroup.centralizer (A : Set G)) =
      Nat.card ↥(Subgroup.normalizer (A : Set G)) := by
  have hmain := Subgroup.card_ker_mul_card_range A.normalizerMonoidHom
  rw [Subgroup.normalizerMonoidHom_ker,
    card_subgroupOf_eq (Subgroup.centralizer_le_normalizer (A : Set G)),
    ← ggAutomizer_eq_range_normalizerMonoidHom, Nat.mul_comm] at hmain
  exact hmain

private theorem b_mul_b_pow_three {G : Type} [Group G] (B : Basis3 G 8) (i j : Fin 8) :
    (B.b i * B.b j) ^ 3 = 1 := by
  rw [(B.comm i j).mul_pow,
    show B.b i ^ 3 = 1 from by simpa [B.ord i] using pow_orderOf_eq_one (B.b i),
    show B.b j ^ 3 = 1 from by simpa [B.ord j] using pow_orderOf_eq_one (B.b j), mul_one]

private theorem b_mul_b_ne_one {G : Type} [Group G] {B : Basis3 G 8} {i j : Fin 8} (hij : i ≠ j) :
    B.b i * B.b j ≠ 1 := by
  intro h
  have hv : B.vec (Pi.single i 1 + Pi.single j 1) = B.vec (0 : Coords 8) := by
    rw [B.vec_add, B.vec_single, B.vec_single, B.vec_zero]; exact h
  have hz : (Pi.single i 1 + Pi.single j 1 : Coords 8) = 0 := B.vec_injective hv
  have hi := congrFun hz i
  simp [Pi.single_apply, hij, Ne.symm hij] at hi

theorem orderOf_b_mul_b {G : Type} [Group G] (B : Basis3 G 8) {i j : Fin 8} (hij : i ≠ j) :
    orderOf (B.b i * B.b j) = 3 :=
  orderOf_eq_prime (b_mul_b_pow_three B i j) (b_mul_b_ne_one hij)

private theorem vec_pow_three {G : Type} [Group G] (B : Basis3 G 8) (e : Coords 8) :
    B.vec e ^ 3 = 1 := by
  have h3 : e + e + e = 0 := by
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize e i = x
    revert x
    decide
  rw [pow_succ, pow_two, ← B.vec_add, ← B.vec_add, h3, B.vec_zero]

theorem beta_mem_span {G : Type} [Group G] (B : Basis3 G 8) :
    B.b 0 * B.b 1 ∈ B.span := by
  rw [← B.vec_single 0, ← B.vec_single 1, ← B.vec_add]
  exact B.vec_mem_span _

theorem span_le_cen_beta {G : Type} [Group G] (B : Basis3 G 8) :
    B.span ≤ TwD7Q.cen (B.b 0 * B.b 1) := by
  simpa only [B.twD7Beta_span] using
    (B.twD7Beta.span_le_cen (β := B.b 0 * B.b 1) B.twD7Beta_b_zero)

theorem commute_vec {G : Type} [Group G] (B : Basis3 G 8) (e e' : Coords 8) :
    Commute (B.vec e) (B.vec e') := by
  show B.vec e * B.vec e' = B.vec e' * B.vec e
  rw [← B.vec_add, ← B.vec_add, add_comm]

private theorem conj_inv_of_eq_conj {G : Type} [Group G] {β c n k : G}
    (hn : n * β * n⁻¹ = c) (hk : k * c * k⁻¹ = c⁻¹) :
    (n⁻¹ * k * n) * β * (n⁻¹ * k * n)⁻¹ = β⁻¹ := by
  have hβ : β = n⁻¹ * c * n := by rw [← hn]; group
  calc (n⁻¹ * k * n) * β * (n⁻¹ * k * n)⁻¹
      = n⁻¹ * (k * (n * β * n⁻¹) * k⁻¹) * n := by group
    _ = n⁻¹ * (k * c * k⁻¹) * n := by rw [hn]
    _ = n⁻¹ * c⁻¹ * n := by rw [hk]
    _ = β⁻¹ := by rw [hβ]; group

private theorem pow_eq_or_eq_inv {G : Type} [Group G] {x y : G} (hx : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hy : y ∈ Subgroup.zpowers x) (hy1 : y ≠ 1) : y = x ∨ y = x⁻¹ := by
  classical
  have hord : orderOf x = 3 := orderOf_eq_prime hx hx1
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, hx⟩
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hord] at hy
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
  rw [Finset.mem_range] at hn
  interval_cases n
  · rw [pow_zero] at hy1
    exact absurd rfl hy1
  · left; rw [pow_one]
  · right
    have h2 : x ^ 2 * x = 1 := by
      calc x ^ 2 * x = x ^ (2 + 1) := by rw [pow_add, pow_one]
        _ = x ^ 3 := by norm_num
        _ = 1 := hx
    exact eq_inv_of_mul_eq_one_left h2

private theorem exists_beta_inverter_span {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD7 B b₀) :
    ∃ t ∈ Subgroup.normalizer (B.span : Set G),
      t * (B.b 0 * B.b 1) * t⁻¹ = (B.b 0 * B.b 1)⁻¹ := by
  classical
  have hrec' := hrec
  rw [← hB.2.1] at hrec'
  have hwt : wt (Pi.single 2 1 + Pi.single 3 1 : Coords 8) = 2 := by decide
  have hne : (Pi.single 2 1 + Pi.single 3 1 : Coords 8) ≠ 0 := by decide
  have hline23 : B.line (Pi.single 2 1 + Pi.single 3 1) = Subgroup.zpowers (B.b 2 * B.b 3) := by
    show Subgroup.zpowers (B.vec (Pi.single 2 1 + Pi.single 3 1)) = _
    rw [B.vec_add, B.vec_single, B.vec_single]
  obtain ⟨n₁, hn₁N, hn₁⟩ :=
    (hrec'.2.2 (Pi.single 2 1 + Pi.single 3 1) hne).mpr (Or.inl hwt)
  rw [hline23] at hn₁
  obtain ⟨k, -, hkN, hk⟩ :=
    exists_even_sign_action_of_std_twD7 hstd B hB hrec {2, 3} (by decide) (by decide)
  have hk2 : k * B.b 2 * k⁻¹ = (B.b 2)⁻¹ := by simpa using hk 2
  have hk3 : k * B.b 3 * k⁻¹ = (B.b 3)⁻¹ := by simpa using hk 3
  have hkc : k * (B.b 2 * B.b 3) * k⁻¹ = (B.b 2 * B.b 3)⁻¹ := by
    calc k * (B.b 2 * B.b 3) * k⁻¹
        = (k * B.b 2 * k⁻¹) * (k * B.b 3 * k⁻¹) := by group
      _ = (B.b 2)⁻¹ * (B.b 3)⁻¹ := by rw [hk2, hk3]
      _ = (B.b 3)⁻¹ * (B.b 2)⁻¹ := ((B.comm 2 3).inv_inv).eq
      _ = (B.b 2 * B.b 3)⁻¹ := by rw [mul_inv_rev]
  have hkc' : k * (B.b 2 * B.b 3)⁻¹ * k⁻¹ = (B.b 2 * B.b 3)⁻¹⁻¹ := by
    have h := congrArg Inv.inv hkc
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using h
  have hne0 : B.b 0 * B.b 1 ≠ 1 := b_mul_b_ne_one (by decide : (0 : Fin 8) ≠ 1)
  have hy1 : n₁ * (B.b 0 * B.b 1) * n₁⁻¹ ≠ 1 := by
    intro h
    apply hne0
    calc B.b 0 * B.b 1 = n₁⁻¹ * (n₁ * (B.b 0 * B.b 1) * n₁⁻¹) * n₁ := by group
      _ = 1 := by rw [h]; group
  have hy : n₁ * (B.b 0 * B.b 1) * n₁⁻¹ ∈ Subgroup.zpowers (B.b 2 * B.b 3) := by
    rw [← hn₁]; exact Subgroup.mem_zpowers _
  have hkN' : k ∈ Subgroup.normalizer (B.span : Set G) := by simpa only [hB.1] using hkN
  rcases pow_eq_or_eq_inv (b_mul_b_pow_three B 2 3)
    (b_mul_b_ne_one (i := 2) (j := 3) (by decide))
    hy hy1 with hc | hc
  · exact ⟨n₁⁻¹ * k * n₁, Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn₁N) hkN') hn₁N, conj_inv_of_eq_conj hc hkc⟩
  · exact ⟨n₁⁻¹ * k * n₁, Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn₁N) hkN') hn₁N, conj_inv_of_eq_conj hc hkc'⟩

private abbrev PB : Set (Coords 8) := {e | wt e = 2 ∨ (wt e = 8 ∧ ∏ i : Fin 8, e i = -1)}

private theorem card_PB : Nat.card ↥PB = 240 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem orbit_eq_vec_image {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8} (hB : Adapted B b₀ K E)
    (hrec : RecOutTwD7 B b₀) :
    {x : G | ∃ n ∈ Subgroup.normalizer (B.span : Set G), n * (B.b 0 * B.b 1) * n⁻¹ = x}
      = B.vec '' PB := by
  have hrec' := hrec
  rw [← hB.2.1] at hrec'
  have hβE : B.b 0 * B.b 1 ∈ B.span := beta_mem_span B
  ext x
  constructor
  · rintro ⟨n, hnN, rfl⟩
    have hxE : n * (B.b 0 * B.b 1) * n⁻¹ ∈ B.span :=
      (Subgroup.mem_normalizer_iff.mp hnN (B.b 0 * B.b 1)).mp hβE
    obtain ⟨e, he⟩ := B.exists_vec_eq hxE
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [B.vec_zero] at he
      have hβ1 : B.b 0 * B.b 1 = 1 := by
        have h1 : B.b 0 * B.b 1 = n⁻¹ * (n * (B.b 0 * B.b 1) * n⁻¹) * n := by group
        rw [h1, ← he]
        group
      exact b_mul_b_ne_one (i := 0) (j := 1) (by decide) hβ1
    have hline : Subgroup.zpowers (n * (B.b 0 * B.b 1) * n⁻¹) = B.line e := by
      show Subgroup.zpowers (n * (B.b 0 * B.b 1) * n⁻¹) = Subgroup.zpowers (B.vec e)
      rw [← he]
    exact ⟨e, (hrec'.2.2 e he0).mp ⟨n, hnN, hline⟩, he⟩
  · rintro ⟨e, he, rfl⟩
    have he0 : e ≠ 0 := by
      rintro rfl
      simp only [PB, Set.mem_setOf_eq] at he
      have h : ¬ (wt (0 : Coords 8) = 2 ∨ (wt (0 : Coords 8) = 8 ∧
          ∏ i : Fin 8, (0 : Coords 8) i = -1)) := by decide
      exact h he
    obtain ⟨n, hnN, hnline⟩ := (hrec'.2.2 e he0).mpr he
    have hzy : Subgroup.zpowers (n * (B.b 0 * B.b 1) * n⁻¹) = Subgroup.zpowers (B.vec e) := by
      rw [hnline]; rfl
    have hy : n * (B.b 0 * B.b 1) * n⁻¹ ∈ Subgroup.zpowers (B.vec e) := by
      rw [← hzy]; exact Subgroup.mem_zpowers _
    have hx3 : (B.vec e) ^ 3 = 1 := vec_pow_three B e
    have hx1 : B.vec e ≠ 1 := by
      intro h; apply he0; apply B.vec_injective; rw [h, B.vec_zero]
    have hy1 : n * (B.b 0 * B.b 1) * n⁻¹ ≠ 1 := by
      intro h
      have hβ1 : B.b 0 * B.b 1 = 1 := by
        have h1 : B.b 0 * B.b 1 = n⁻¹ * (n * (B.b 0 * B.b 1) * n⁻¹) * n := by group
        rw [h1, h]
        group
      exact b_mul_b_ne_one (i := 0) (j := 1) (by decide) hβ1
    rcases pow_eq_or_eq_inv hx3 hx1 hy hy1 with h | h
    · exact ⟨n, hnN, h⟩
    · obtain ⟨t, htN, ht⟩ := exists_beta_inverter_span hstd hB hrec
      refine ⟨n * t, Subgroup.mul_mem _ hnN htN, ?_⟩
      have hconj : (n * t) * (B.b 0 * B.b 1) * (n * t)⁻¹
          = n * (B.b 0 * B.b 1)⁻¹ * n⁻¹ := by
        calc (n * t) * (B.b 0 * B.b 1) * (n * t)⁻¹
            = n * (t * (B.b 0 * B.b 1) * t⁻¹) * n⁻¹ := by group
          _ = n * (B.b 0 * B.b 1)⁻¹ * n⁻¹ := by rw [ht]
      rw [hconj, show n * (B.b 0 * B.b 1)⁻¹ * n⁻¹
          = (n * (B.b 0 * B.b 1) * n⁻¹)⁻¹ by group, h, inv_inv]

theorem card_normalizer_eq_orbit_mul_centralizer {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G 8} (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀) :
    Nat.card ↥(Subgroup.normalizer (B.span : Set G)) =
      240 * Nat.card ↥(Subgroup.normalizer (B.span : Set G) ⊓
        Subgroup.centralizer ({B.b 0 * B.b 1} : Set G)) := by
  classical
  let β : G := B.b 0 * B.b 1
  let N : Subgroup G := Subgroup.normalizer (B.span : Set G)
  letI : MulAction ↥N G :=
    { smul := fun n x => (n : G) * x * (n : G)⁻¹
      one_smul := fun x => by
        show ((1 : ↥N) : G) * x * ((1 : ↥N) : G)⁻¹ = x
        rw [Subgroup.coe_one, one_mul, inv_one, mul_one]
      mul_smul := fun m n x => by
        show (((m * n : ↥N)) : G) * x * (((m * n : ↥N)) : G)⁻¹
          = (m : G) * ((n : G) * x * (n : G)⁻¹) * (m : G)⁻¹
        rw [Subgroup.coe_mul]
        group }
  have hset : (MulAction.orbit ↥N β : Set G)
      = {x : G | ∃ n ∈ Subgroup.normalizer (B.span : Set G),
          n * (B.b 0 * B.b 1) * n⁻¹ = x} := by
    ext x
    exact ⟨fun ⟨n, hn⟩ => ⟨n, n.2, hn⟩, fun ⟨n, hnN, hn⟩ => ⟨⟨n, hnN⟩, hn⟩⟩
  have horbit : (MulAction.orbit ↥N β : Set G) = B.vec '' PB := by
    rw [hset, orbit_eq_vec_image hstd hB hrec]
  have horbit_card : Nat.card (MulAction.orbit ↥N β) = 240 := by
    rw [horbit, Nat.card_image_of_injective B.vec_injective PB, card_PB]
  have hstab : Nat.card (MulAction.stabilizer ↥N β) =
      Nat.card ↥(N ⊓ Subgroup.centralizer ({β} : Set G)) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun n => ⟨(n.1 : G), ?_⟩
        invFun := fun x => ⟨⟨(x.1 : G), x.2.1⟩, ?_⟩
        left_inv := fun n => rfl
        right_inv := fun x => rfl }
    · have h := n.2
      change (n.1 : G) * β * (n.1 : G)⁻¹ = β at h
      refine Subgroup.mem_inf.mpr ⟨n.1.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc (n.1 : G) * β = (n.1 : G) * β * (n.1 : G)⁻¹ * (n.1 : G) := by group
        _ = β * (n.1 : G) := by rw [h]
    · have hc := Subgroup.mem_centralizer_singleton_iff.mp x.2.2
      show (x.1 : G) * β * (x.1 : G)⁻¹ = β
      rw [show (x.1 : G) * β = β * (x.1 : G) from hc]
      group
  have hOS := MulAction.orbitProdStabilizerEquivGroup (G := ↥N) (X := G) β
  have hcard : Nat.card ↥N =
      Nat.card (MulAction.orbit ↥N β) * Nat.card (MulAction.stabilizer ↥N β) := by
    rw [← Nat.card_prod, Nat.card_congr hOS]
  rw [hcard, horbit_card, hstab]

end CFSG.StandardType.FrameRoute.FS81
