module

public import CFSG.Quasithin.Vol2.Ch11SecE42Rad
public import CFSG.Quasithin.Vol2.Ch11SecE42SL2
public import CFSG.Quasithin.Vol2.Ch11SecA02Quot
public import CFSG.Quasithin.Vol2.Ch11SecDK

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem eq_bot_of_perfect_of_solvable {B : Subgroup G} (hB : ⁅B, B⁆ = B)
    (hs : Group.IsSolvable B) : B = ⊥ := by
  have htop : commutator B = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_subtype_commutator, hB, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hder : ∀ k, derivedSeries B k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [derivedSeries_succ, ih, ← commutator_def, htop]
  obtain ⟨k, hk⟩ := hs.solvable
  rw [hder] at hk
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : B) ∈ (⊥ : Subgroup B) := hk ▸ Subgroup.mem_top _
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp this))

theorem not_isQuasisimple_of_fitting {X : Type*} [Group X] [Finite X]
    (hF : CFSG.generalizedFitting X = CFSG.fittingSubgroup X)
    (hne : CFSG.fittingSubgroup X ≠ ⊤) : ¬ CFSG.IsQuasisimple X := by
  intro hQ
  have hZ := SecA.le_center_of_normal_ne_top hQ hne
  apply hne
  rw [eq_top_iff]
  have hC : (⊤ : Subgroup X) ≤ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff, hF]
    intro f hf
    exact (Subgroup.mem_center_iff.mp (hZ hf) x).symm
  have := hC.trans (CFSG.centralizer_generalizedFitting_le X)
  rwa [hF] at this

theorem fitting_ne_top_of_a36 {X : Type} [Group X] (h : A36Case4 X) :
    CFSG.fittingSubgroup X ≠ ⊤ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, -, ⟨e⟩, -⟩ := h
  intro htop
  have hsub : ∀ a : X ⧸ CFSG.fittingSubgroup X, a = 1 := fun a => by
    induction a using QuotientGroup.induction_on with
    | H x => exact (QuotientGroup.eq_one_iff x).mpr (htop ▸ Subgroup.mem_top x)
  apply A1c.sl2NegOne_ne_one (p := 5) (by norm_num)
  rw [← e.apply_symm_apply (A1c.sl2NegOne 5), hsub (e.symm _), map_one]

theorem odd_card_fitting_of_a36 {X : Type} [Group X] (h : A36Case4 X) :
    Odd (Nat.card (CFSG.fittingSubgroup X)) := by
  obtain ⟨-, -, -, hp⟩ := h
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  rcases (hp 2 Nat.prime_two h2).1 with h | h | h <;> norm_num at h

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem lOf_not_le_oTwoTwoPrime (h1110 : Stmt11_1_0) (h : Hyp11 G T L I n) {V₁ K : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) : ¬ LOf L V₁ ≤ oTwoTwoPrime K := by
  intro hle
  have : Group.IsSolvable ↥(oTwoTwoPrime K) := SecD.isSolvable_oTwoTwoPrime K
  have hs : Group.IsSolvable ↥(LOf L V₁) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  exact SecD.lOf_ne_bot h1110 h hV₁ (eq_bot_of_perfect_of_solvable (perfectCore_perfect _) hs)

theorem le_centralizer_of_a36
    (h3214 : TmpL6_3_2_14) (hP : SecB.PointFacts) (h1102 : Stmt11_0_2)
    (h1110 : Stmt11_1_0) (h : Hyp11 G T L I n) {V₁ K : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hloc : quasithinIsLocal T K) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hLK : LOf L V₁ ≤ K) (hA : A36Case4 (↥K ⧸ CFSG.pCore 2 ↥K)) :
    K ≤ Subgroup.centralizer (V₁ : Set G) := by
  have hnq := not_isQuasisimple_of_fitting hA.1 (fitting_ne_top_of_a36 hA)
  have hY := oTwoTwoPrime_le_centralizer h3214 hP h1102 h hV₁ hloc hTK hLK hnq
  have hFO : CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K) ≤ CFSG.oddCore (↥K ⧸ CFSG.pCore 2 ↥K) :=
    le_sSup ⟨inferInstance, odd_card_fitting_of_a36 hA⟩
  obtain ⟨-, -, ⟨e⟩, -⟩ := hA
  set φ : ↥K →* SL(2, ZMod 5) := e.toMonoidHom.comp
    ((QuotientGroup.mk' _).comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) with hφ
  have hker : ∀ k : ↥K, φ k = 1 → (k : G) ∈ oTwoTwoPrime K := by
    intro k hk
    rw [SecD.mem_oTwoTwoPrime_iff]
    apply hFO
    have h1 : QuotientGroup.mk' (CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K))
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K) k) = 1 := by
      apply e.injective
      rw [map_one]
      exact hk
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  set ψ : ↥(LOf L V₁) →* SL(2, ZMod 5) := φ.comp (Subgroup.inclusion hLK) with hψ
  have hLperf : commutator ↥(LOf L V₁) = ⊤ := by
    apply Subgroup.map_injective (LOf L V₁).subtype_injective
    rw [Subgroup.map_subtype_commutator, perfectCore_perfect, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hperf : ⁅ψ.range, ψ.range⁆ = ψ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hLperf]
  have hne : ψ.range ≠ ⊥ := by
    intro h0
    apply lOf_not_le_oTwoTwoPrime h1110 h hV₁ (K := K)
    intro l hl
    have h1 : ψ ⟨l, hl⟩ = 1 := by
      have : ψ ⟨l, hl⟩ ∈ ψ.range := ⟨_, rfl⟩
      rwa [h0, Subgroup.mem_bot] at this
    exact hker _ h1
  have htop := eq_top_of_perfect_sl2_five hperf hne
  have hL₁C := SecB.lOf_le_centralizer hP h1102 h hV₁
  intro k hk
  obtain ⟨l, hl⟩ : ∃ l : ↥(LOf L V₁), ψ l = φ ⟨k, hk⟩ := by
    have : φ ⟨k, hk⟩ ∈ ψ.range := htop ▸ Subgroup.mem_top _
    exact this
  have hkl : φ (⟨k, hk⟩ * (Subgroup.inclusion hLK l)⁻¹) = 1 := by
    rw [map_mul, map_inv, ← hl]
    exact mul_inv_cancel _
  have h1 := hY (hker _ hkl)
  have h2 : (l : G) ∈ Subgroup.centralizer (V₁ : Set G) := hL₁C l.2
  have hk' : k = ((⟨k, hk⟩ * (Subgroup.inclusion hLK l)⁻¹ : ↥K) : G) * (l : G) := by
    simp [Subgroup.coe_inclusion]
  rw [hk']
  exact Subgroup.mul_mem _ h1 h2

end CFSG.Quasithin.Vol2.Ch11.SecE
