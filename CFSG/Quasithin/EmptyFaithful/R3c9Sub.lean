module

public import CFSG.Quasithin.EmptyFaithful.R3c9Four
public import CFSG.Quasithin.EmptyFaithful.R3c9Alt4

public section

namespace CFSG.Quasithin.R3c9

open Equiv

theorem exists_abelian_twoGroup_sup {X : Type} [Group X] [Finite X] {V : Subgroup X} {c : X} {k : ℕ}
    (hV4 : Nat.card V = 4) (hVc : ∀ u ∈ V, ∀ v ∈ V, u * v = v * u) (hc : ∀ v ∈ V, c * v = v * c)
    (hk : orderOf c = 2 ^ k) :
    ∃ W : Subgroup X, V ≤ W ∧ c ∈ W ∧ IsPGroup 2 W ∧ ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
  classical
  have hcomm : ∀ (v : ↥V) (x : ↥(Subgroup.zpowers c)),
      Commute (V.subtype v) ((Subgroup.zpowers c).subtype x) := by
    intro v x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.2
    have h1 : Commute (v : X) c := (hc v v.2).symm
    show Commute (v : X) (x : X)
    rw [← hn]
    exact h1.zpow_right n
  let φ : ↥V × ↥(Subgroup.zpowers c) →* X := V.subtype.noncommCoprod (Subgroup.zpowers c).subtype hcomm
  have hφ : ∀ a : ↥V × ↥(Subgroup.zpowers c), φ a = (a.1 : X) * (a.2 : X) := fun a => rfl
  refine ⟨φ.range, fun v hv => ⟨(⟨v, hv⟩, 1), by simp [hφ]⟩,
    ⟨(1, ⟨c, Subgroup.mem_zpowers c⟩), by simp [hφ]⟩, ?_, ?_⟩
  · have hWcard : Nat.card φ.range ∣ 2 ^ (k + 2) := by
      have h1 : Nat.card φ.range ∣ Nat.card (↥V × ↥(Subgroup.zpowers c)) := Subgroup.card_range_dvd φ
      have h2 : Nat.card (↥V × ↥(Subgroup.zpowers c)) = 2 ^ (k + 2) := by
        rw [Nat.card_prod, hV4, Nat.card_zpowers, hk]
        ring
      rw [← h2]
      exact h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hWcard
    exact IsPGroup.of_card hj
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    refine Prod.ext (Subtype.ext (hVc _ a.1.2 _ b.1.2)) (Subtype.ext ?_)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2.2
    show (a.2 : X) * (b.2 : X) = (b.2 : X) * (a.2 : X)
    rw [← hm, ← hn]
    exact (Commute.zpow_zpow_self c m n).eq

theorem fourSelfCentTwo_of_sylow_card_le_four {X : Type} [Group X] [Finite X]
    (h : ∀ P : Sylow 2 X, Nat.card P ≤ 4) : FourSelfCentTwo X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro V hV4 hV2 hVc c hc ⟨k, hk⟩
  by_contra hcV
  obtain ⟨W, hVW, hcW, hW2, -⟩ := exists_abelian_twoGroup_sup hV4 hVc hc hk
  obtain ⟨P, hP⟩ := hW2.exists_le_sylow
  have h1 : Nat.card W ≤ Nat.card P := Subgroup.card_le_of_le hP
  have h2 : Nat.card P ≤ 4 := h P
  have hgt : 4 < Nat.card W := by
    by_contra hle
    push Not at hle
    have := Subgroup.eq_of_le_of_card_ge hVW (by rw [hV4]; exact hle)
    exact hcV (this ▸ hcW)
  omega

theorem fpf_of_orderOf_threePow {G : Type} [Group G] {V : Subgroup G} (hV4 : Nat.card V = 4) {y : G} {k : ℕ}
    (hy : orderOf y = 3 ^ k) (hyN : y ∈ Subgroup.normalizer (V : Set G))
    (hnc : ¬ ∀ v ∈ V, y * v = v * y) : ∀ v ∈ V, v ≠ 1 → y * v * y⁻¹ ≠ v := by
  classical
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV4]; norm_num)
  obtain ⟨ι, hιinj, hιfix⟩ := exists_mulAut_embedding ↥V hV4
  let ψ : MulAut ↥V := Subgroup.normalizerMonoidHom V ⟨y, hyN⟩
  have hψ : ∀ v : ↥V, ((ψ v : ↥V) : G) = y * v * y⁻¹ := fun v =>
    Subgroup.normalizerMonoidHom_apply_apply_coe V ⟨y, hyN⟩ v
  have hψ1 : ψ ≠ 1 := by
    intro h1
    apply hnc
    intro v hv
    have h2 := congrArg (fun f : MulAut ↥V => ((f ⟨v, hv⟩ : ↥V) : G)) h1
    simp only [hψ, MulAut.one_apply] at h2
    calc y * v = (y * v * y⁻¹) * y := by group
      _ = v * y := by rw [h2]
  have hιψ3 : (ι ψ) ^ 3 = 1 := by
    apply perm3_pow3_of_threePow (k := k)
    rw [← map_pow]
    have : ψ ^ 3 ^ k = 1 := by
      have h3 : y ^ 3 ^ k = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
      have h4 : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 3 ^ k = 1 :=
        Subtype.ext (by simpa using h3)
      show (Subgroup.normalizerMonoidHom V ⟨y, hyN⟩) ^ 3 ^ k = 1
      rw [← map_pow, h4, map_one]
    rw [this, map_one]
  have hιψ1 : ι ψ ≠ 1 := fun h1 => hψ1 (hιinj (by rw [h1, map_one]))
  intro v hv hv1 hfix
  have hvne : (⟨v, hv⟩ : ↥V) ≠ 1 := by
    intro h
    apply hv1
    simpa using congrArg Subtype.val h
  have hfix' : ψ ⟨v, hv⟩ = ⟨v, hv⟩ := Subtype.ext (by rw [hψ]; exact hfix)
  obtain ⟨i, hi⟩ := hιfix ψ ⟨v, hv⟩ hvne hfix'
  exact perm3_no_fixed (ι ψ) hιψ1 hιψ3 i hi

end CFSG.Quasithin.R3c9
