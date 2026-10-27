module

public import CFSG.RankThree.PartOne.S9.Sylow.GlobalBridge
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores

public section

namespace CFSG.RankThree.PartOne.Sec9B

open CFSG Subgroup CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem card_zpowers_eq {p : ℕ} (hp : p.Prime) {A : Subgroup G} (hA : IsElementaryAbelian p ↥A)
    {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) : Nat.card ↥(Subgroup.zpowers a) = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hap : a ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian a haA
  rw [Nat.card_zpowers, orderOf_eq_prime hap ha1]

theorem relIndex_inf_centralizer_eq {p : ℕ} (hp : p.Prime) {A R : Subgroup G}
    (hAcard : Nat.card ↥A = p ^ 3)
    (hB : Nat.card ↥(A ⊓ Subgroup.centralizer (R : Set G)) = p ^ 2) :
    (A ⊓ Subgroup.centralizer (R : Set G)).relIndex A = p := by
  have h := Subgroup.relIndex_mul_card (A ⊓ Subgroup.centralizer (R : Set G)) A
  rw [inf_eq_left.mpr (inf_le_left : A ⊓ Subgroup.centralizer (R : Set G) ≤ A), hB, hAcard] at h
  have : (A ⊓ Subgroup.centralizer (R : Set G)).relIndex A * p ^ 2 = p * p ^ 2 := by
    rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) this

theorem exists_mem_not_mem_centralizer {p : ℕ} (hp : p.Prime) [Finite G] {A R : Subgroup G}
    (hAcard : Nat.card ↥A = p ^ 3)
    (hB : Nat.card ↥(A ⊓ Subgroup.centralizer (R : Set G)) = p ^ 2) :
    ∃ a ∈ A, a ∉ Subgroup.centralizer (R : Set G) := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hle : A ≤ A ⊓ Subgroup.centralizer (R : Set G) := le_inf le_rfl h
  have := Subgroup.card_le_of_le hle
  rw [hAcard, hB] at this
  have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem mem_normalizer_zpowers_of_commute {a b : G} (hab : a * b = b * a) :
    a ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
  have h : a ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hab
  rw [CFSG.RankThree.GroupTheory.SteinbergBY.centralizer_singleton_eq_centralizer_zpowers] at h
  exact Subgroup.centralizer_le_normalizer _ h

theorem isPGroup_of_forall_pow_eq_one {q : ℕ} {X : Subgroup G} (h : ∀ x ∈ X, x ^ q = 1) :
    IsPGroup q ↥X := fun x => ⟨1, Subtype.ext (by simpa using h x x.2)⟩

theorem commutator_zpowers_eq {p : ℕ} (hp : p.Prime) [Finite G] {A R : Subgroup G}
    (hA : IsElementaryAbelian p ↥A) (hAcard : Nat.card ↥A = p ^ 3)
    (hAN : A ≤ Subgroup.normalizer (R : Set G)) (hRA : ⁅R, A⁆ = R)
    (hB : Nat.card ↥(A ⊓ Subgroup.centralizer (R : Set G)) = p ^ 2) {a : G} (haA : a ∈ A)
    (haB : a ∉ Subgroup.centralizer (R : Set G)) : ⁅R, Subgroup.zpowers a⁆ = R := by
  classical
  set B := A ⊓ Subgroup.centralizer (R : Set G) with hBdef
  have hBA : B ≤ A := inf_le_left
  have hidx : B.relIndex A = p := relIndex_inf_centralizer_eq hp hAcard hB
  have haBn : a ∉ B := fun h => haB h.2
  have hzA : Subgroup.zpowers a ≤ A := (Subgroup.zpowers_le).mpr haA
  set M := B ⊔ Subgroup.zpowers a with hM
  have hMA : M ≤ A := sup_le hBA hzA
  have hAM : A ≤ M := by
    have h1 := Subgroup.relIndex_mul_relIndex B M A le_sup_left hMA
    rw [hidx] at h1
    have h2 : B.relIndex M ∣ p := ⟨M.relIndex A, h1.symm⟩
    rcases (Nat.dvd_prime hp).mp h2 with h3 | h3
    · exfalso
      have := Subgroup.relIndex_eq_one.mp h3
      exact haBn (this (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)))
    · rw [h3] at h1
      have h4 : M.relIndex A = 1 := by
        have : p * M.relIndex A = p * 1 := by rw [h1, mul_one]
        exact Nat.eq_of_mul_eq_mul_left hp.pos this
      exact Subgroup.relIndex_eq_one.mp h4
  have hdecomp : ∀ x ∈ A, ∃ b' ∈ B, ∃ z ∈ Subgroup.zpowers a, x = b' * z := by
    intro x hx
    let : CommGroup A := IsMulCommutative.instCommGroup
    have hx' : (⟨x, hx⟩ : A) ∈ B.subgroupOf A ⊔ (Subgroup.zpowers a).subgroupOf A := by
      rw [← Subgroup.subgroupOf_sup hBA hzA]
      exact hAM hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.mp hx'
    exact ⟨y, hy, z, hz, by simpa using congrArg Subtype.val hyz.symm⟩
  apply le_antisymm
  · exact (Subgroup.commutator_mono le_rfl hzA).trans hRA.le
  · calc R = ⁅R, A⁆ := hRA.symm
      _ ≤ ⁅R, Subgroup.zpowers a⁆ := by
        rw [Subgroup.commutator_le]
        intro r hr x hx
        obtain ⟨b', hb', z, hz, rfl⟩ := hdecomp x hx
        have hzN : z ∈ Subgroup.normalizer (R : Set G) := hAN (hzA hz)
        have hb'c : ∀ s ∈ R, s * b' = b' * s := Subgroup.mem_centralizer_iff.mp hb'.2
        have h1 : ⁅r, z⁆ ∈ R := by
          have := (Subgroup.mem_normalizer_iff.mp hzN r⁻¹).mp (R.inv_mem hr)
          rw [commutatorElement_def]
          have e : r * z * r⁻¹ * z⁻¹ = r * (z * r⁻¹ * z⁻¹) := by group
          rw [e]
          exact R.mul_mem hr this
        have hcomm : ⁅r, z⁆ * b' = b' * ⁅r, z⁆ := hb'c _ h1
        have key : ⁅r, b' * z⁆ = ⁅r, z⁆ := by
          calc ⁅r, b' * z⁆ = (r * b') * z * r⁻¹ * z⁻¹ * b'⁻¹ := by
                simp only [commutatorElement_def]; group
            _ = (b' * r) * z * r⁻¹ * z⁻¹ * b'⁻¹ := by rw [hb'c r hr]
            _ = b' * ⁅r, z⁆ * b'⁻¹ := by simp only [commutatorElement_def]; group
            _ = (⁅r, z⁆ * b') * b'⁻¹ := by rw [hcomm]
            _ = ⁅r, z⁆ := by group
        rw [key]
        exact Subgroup.commutator_mem_commutator hr hz

section Relative

variable {G : Type} [Group G] [Finite G]

theorem relative_twoLocalRankTwoOddCoreAction (hI2 : TwoLocalRankTwoOddCoreAction)
    (H A R : Subgroup G) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp3 : 3 < p) (hq3 : 3 < q)
    (hpq : p ≠ q) (hAH : A ≤ H) (hRH : R ≤ H) (hAcard : Nat.card ↥A = p)
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hR2 : IsPGroup 2 ↥R) (hR1 : R ≠ ⊥)
    (hRA : ⁅R, A⁆ = R) (hRO : ⁅R, inSubgroup (pCore q) H⁆ ≠ ⊥) (hloc : localRank q ↥H ≤ 2) :
    p = 5 ∧ Nonempty (↥R ≃* QD32) ∧ IsQDShape q (omegaOne q (inSubgroup (pCore q) H)) := by
  have hι := H.subtype_injective
  have hA : (A.subgroupOf H).map H.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAH]
  have hR : (R.subgroupOf H).map H.subtype = R := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRH]
  have h1 : Nat.card ↥(A.subgroupOf H) = p := by
    rw [← hAcard, ← Subgroup.card_map_of_injective hι, hA]
  have h2 : A.subgroupOf H ≤ Subgroup.normalizer (R.subgroupOf H : Set ↥H) := by
    rw [← map_le_normalizer_map_iff hι, hA, hR]
    exact hAR
  have h3 : IsPGroup 2 ↥(R.subgroupOf H) := by
    rw [← isPGroup_map_iff hι, hR]
    exact hR2
  have h4 : R.subgroupOf H ≠ ⊥ := fun h => hR1 (by rw [← hR, h, Subgroup.map_bot])
  have h5 : ⁅R.subgroupOf H, A.subgroupOf H⁆ = R.subgroupOf H := by
    apply Subgroup.map_injective hι
    rw [Subgroup.map_commutator, hA, hR, hRA]
  have h6 : ⁅R.subgroupOf H, pCore q ↥H⁆ ≠ ⊥ := by
    intro h
    apply hRO
    have := congrArg (Subgroup.map H.subtype) h
    rw [Subgroup.map_commutator, hR, Subgroup.map_bot] at this
    exact this
  obtain ⟨hp5, ⟨e⟩, hsh⟩ := hI2 ↥H p q (A.subgroupOf H) (R.subgroupOf H) hp hq hp3 hq3 hpq
    h1 h2 h3 h4 h5 h6 hloc
  refine ⟨hp5, ⟨(Subgroup.subgroupOfEquivOfLe hRH).symm.trans e⟩, ?_⟩
  have h := (isQDShape_map_iff hι (q := q) (Y := omegaOne q (pCore q ↥H))).mpr hsh
  rw [map_omegaOne hι] at h
  exact h

end Relative

end CFSG.RankThree.PartOne.Sec9B
