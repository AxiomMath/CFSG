module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR5Lift
public import CFSG.RankThree.PartTwo.Sec13.F135LastR4Cube

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem r4f_centralizer_le_normalizer {G : Type*} [Group G] {J T : Subgroup G} (hTJ : T ≤ J)
    {g : G} (hg : g ∈ Subgroup.centralizer (J : Set G)) :
    g ∈ Subgroup.normalizer (T : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hg
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hc : h * g = g * h := hg h (hTJ hh)
    have e : g * h * g⁻¹ = h := by
      rw [mul_inv_eq_iff_eq_mul, hc]
    rw [e]
    exact hh
  · intro hh
    have hc : g * h * g⁻¹ * g = g * (g * h * g⁻¹) := hg _ (hTJ hh)
    rw [inv_mul_cancel_right] at hc
    have e : h = g * h * g⁻¹ := mul_left_cancel hc
    rw [e]
    exact hh

theorem r4f_image_central_mem {M : Type*} [Group M] (R : Subgroup M) [R.Normal]
    (J : Subgroup (M ⧸ R)) {y : M} (hy : y ∈ Subgroup.center M) :
    QuotientGroup.mk' R y ∈ Subgroup.centralizer (J : Set (M ⧸ R)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro j _
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective R j
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hy m]

theorem r4f_commutator_map_le {M : Type*} [Group M] {E X : Subgroup M} (hXE : X ≤ E) :
    (commutator ↥X).map X.subtype ≤ (commutator ↥E).map E.subtype := by
  have h1 : (commutator ↥X).map (Subgroup.inclusion hXE) ≤ commutator ↥E := by
    unfold commutator
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have h2 : E.subtype.comp (Subgroup.inclusion hXE) = X.subtype := rfl
  have h4 : (commutator ↥X).map X.subtype =
      ((commutator ↥X).map (Subgroup.inclusion hXE)).map E.subtype := by
    rw [Subgroup.map_map, h2]
  rw [h4]
  exact Subgroup.map_mono h1

theorem r4f_card_cube {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {K X Y : Subgroup G} (hX : IsPGroup p X) (hKX : K ≤ X) (hKX' : K ≠ X)
    (hYK : Y ≤ K) (hY : Nat.card Y = p) (hYK' : Y ≠ K) : p ^ 3 ≤ Nat.card X := by
  have hpr : p.Prime := hp.out
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hX
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (hX.to_le hKX)
  have hYKc : p ≤ p ^ b := by
    have h := Subgroup.card_le_of_le hYK
    rw [hY, hb] at h
    exact h
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hYKc
    have := hpr.two_le
    omega
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply hYK'
    apply Subgroup.eq_of_le_of_card_ge hYK
    exact le_of_eq (by rw [hb, pow_one, hY])
  have hb2 : 2 ≤ b := by omega
  have hdvd : p ^ b ∣ p ^ a := by
    have h := Subgroup.card_dvd_of_le hKX
    rw [hb, ha] at h
    exact h
  have hba : b ≤ a := (Nat.pow_dvd_pow_iff_le_right hpr.one_lt).mp hdvd
  have hne : b ≠ a := by
    rintro rfl
    apply hKX'
    apply Subgroup.eq_of_le_of_card_ge hKX
    exact le_of_eq (by rw [ha, hb])
  have hlt : b < a := lt_of_le_of_ne hba hne
  have h3a : 3 ≤ a := by omega
  rw [ha]
  exact Nat.pow_le_pow_right hpr.pos h3a

theorem r4_Eker {M : Type} [Group M] [Finite M] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (R : Subgroup M) [R.Normal] (hR : ¬ p ∣ Nat.card R)
    (Y E : Subgroup M) (hY : Nat.card Y = p) (hYc : Y ≤ Subgroup.center M)
    (hE : IsPGroup p E) (hEexp : ∀ e ∈ E, e ^ p = 1) (hYE : Y ≤ E)
    (hYΦ : Y ⊓ (commutator ↥E).map E.subtype = ⊥)
    (J : Subgroup (M ⧸ R))
    (f : M) (hfE : f ∈ E)
    (hfJ : QuotientGroup.mk' R f ∉ Subgroup.centralizer (J : Set (M ⧸ R)))
    (T : Subgroup (M ⧸ R)) (hTJ : T ≤ J) (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hTf : QuotientGroup.mk' R f ∈ Subgroup.normalizer (T : Set (M ⧸ R)))
    (hno : ∀ A T : Subgroup M, CFSG.Open.IsElemAbelian p A → Nat.card A = p ^ 3 → T ≠ ⊥ →
      IsPGroup 2 T → ¬ A ≤ Subgroup.normalizer (T : Set M)) :
    ∀ e ∈ E, QuotientGroup.mk' R e ∈ Subgroup.centralizer (J : Set (M ⧸ R)) → e ∈ Y := by
  intro e₀ he₀E he₀C
  by_contra he₀Y
  have hp : p.Prime := Fact.out
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup M,
      K = E ⊓ (Subgroup.centralizer (J : Set (M ⧸ R))).comap (QuotientGroup.mk' R) :=
    ⟨_, rfl⟩
  have hmemK : ∀ x : M, x ∈ K ↔
      x ∈ E ∧ QuotientGroup.mk' R x ∈ Subgroup.centralizer (J : Set (M ⧸ R)) := by
    intro x
    rw [hKdef, Subgroup.mem_inf, Subgroup.mem_comap]
  have hKE : K ≤ E := fun x hx => ((hmemK x).mp hx).1
  have hYK : Y ≤ K := by
    intro y hy
    exact (hmemK y).mpr ⟨hYE hy, r4f_image_central_mem R J (hYc hy)⟩
  have he₀K : e₀ ∈ K := (hmemK e₀).mpr ⟨he₀E, he₀C⟩
  have hfK : f ∉ K := fun h => hfJ ((hmemK f).mp h).2
  have hYK_ne : Y ≠ K := fun h => he₀Y (by rw [h]; exact he₀K)
  obtain ⟨X, hXdef⟩ : ∃ X : Subgroup M, X = K ⊔ Subgroup.zpowers f := ⟨_, rfl⟩
  have hKX : K ≤ X := by
    rw [hXdef]
    exact le_sup_left
  have hfX : f ∈ X := by
    rw [hXdef]
    exact (le_sup_right : Subgroup.zpowers f ≤ K ⊔ Subgroup.zpowers f) (Subgroup.mem_zpowers f)
  have hXE : X ≤ E := by
    rw [hXdef]
    exact sup_le hKE (Subgroup.zpowers_le.mpr hfE)
  have hX_p : IsPGroup p X := hE.to_le hXE
  have hKX_ne : K ≠ X := fun h => hfK (by rw [h]; exact hfX)
  have hXmap : X.map (QuotientGroup.mk' R) ≤ Subgroup.normalizer (T : Set (M ⧸ R)) := by
    rw [Subgroup.map_le_iff_le_comap, hXdef]
    apply sup_le
    · intro x hx
      rw [Subgroup.mem_comap]
      exact r4f_centralizer_le_normalizer hTJ ((hmemK x).mp hx).2
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      exact hTf
  obtain ⟨T', hT'ne, hT'2, hXT'⟩ := exists_two_lift hp hp2 R hR hX_p hT hT2 hXmap
  have hYΦX : Y ⊓ (commutator ↥X).map X.subtype = ⊥ := by
    have h := inf_le_inf_left Y (r4f_commutator_map_le hXE)
    rw [hYΦ] at h
    exact le_bot_iff.mp h
  have hYcX : ∀ y ∈ Y, ∀ x ∈ X, y * x = x * y := fun y hy x _ =>
    ((Subgroup.mem_center_iff.mp (hYc hy)) x).symm
  have hexpX : ∀ x ∈ X, x ^ p = 1 := fun x hx => hEexp x (hXE hx)
  have h3 : p ^ 3 ≤ Nat.card X := r4f_card_cube hX_p hKX hKX_ne hYK hY hYK_ne
  obtain ⟨A, hAX, hAel, hAcard⟩ := r4_exists_cube hX_p hexpX (hYK.trans hKX) hY hYcX hYΦX h3
  exact hno A T' hAel hAcard hT'ne hT'2 (le_trans hAX hXT')

end CFSG.RankThree.PartTwo.Sec13.F135Last
