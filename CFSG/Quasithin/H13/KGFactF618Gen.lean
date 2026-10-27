module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Quasithin

namespace KGF618

theorem oTwoUpper_eq_self_of_perfect {Γ : Type*} [Group Γ] [Finite Γ] {K : Subgroup Γ}
    (hK : ⁅K, K⁆ = K) : oTwoUpper K = K := by
  refine le_antisymm (oTwoUpper_le K) ?_
  let N : Subgroup ↥K := (oTwoUpper K).subgroupOf K
  have hN : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := conj_mem_oTwoUpper (X := K) (g := (g : Γ)) (Subgroup.le_normalizer g.2) hn
    simpa using this⟩
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hK
  have hP : IsPGroup 2 (↥K ⧸ N) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper K g.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have : Group.IsNilpotent (↥K ⧸ N) := hP.isNilpotent
  have : Subsingleton (↥K ⧸ N) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent (↥K ⧸ N) ‹_›
  intro g hg
  have : (QuotientGroup.mk ⟨g, hg⟩ : ↥K ⧸ N) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff] at this
  exact this

theorem oTwoUpper_top_eq {D : Type*} [Group D] [Finite D] {N : Subgroup D}
    (hsq : ∀ x : D, x * x ∈ N) (hN : ⁅N, N⁆ = N) : oTwoUpper (⊤ : Subgroup D) = N :=
  (eq_oTwoUpper_of_pow_mem le_top (fun x _ => ⟨1, by rw [pow_one, sq]; exact hsq x⟩)
    (oTwoUpper_eq_self_of_perfect hN).symm).symm

@[expose] def Good (X : Type*) [Group X] : Prop :=
  CFSG.IsQuasisimple X ∧ ∀ b : ℕ, Nat.card X ≠ 60 * 2 ^ b

theorem isQuasisimple_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : CFSG.IsQuasisimple X) : CFSG.IsQuasisimple Y := by
  obtain ⟨hp, hs, a, b, hab⟩ := h
  have hc : (Subgroup.center X).map (e : X →* Y) = Subgroup.center Y := Subgroup.map_center_eq e
  let e' : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y := QuotientGroup.congr _ _ e hc
  refine ⟨?_, ?_, e' a, e' b, fun h => hab (e'.injective ?_)⟩
  · rw [Group.isPerfect_def, _root_.commutator_def] at hp ⊢
    rw [← Subgroup.map_top_of_surjective (e : X →* Y) e.surjective, ← Subgroup.map_commutator,
      hp]
  · have := hs
    exact e'.symm.isSimpleGroup
  · rw [map_mul, map_mul, h]

theorem good_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : Good X) : Good Y :=
  ⟨isQuasisimple_of_mulEquiv e h.1, fun b hb => h.2 b ((Nat.card_congr e.toEquiv).trans hb)⟩

theorem conclusion_of_good {D : Type*} [Group D] [Finite D] {N : Subgroup D}
    (hsq : ∀ x : D, x * x ∈ N) (h : Good ↥N) :
    CFSG.IsQuasisimple ↥(oTwoUpper (⊤ : Subgroup D)) ∧
      ∀ b : ℕ, Nat.card ↥(oTwoUpper (⊤ : Subgroup D)) ≠ 60 * 2 ^ b := by
  have hN : ⁅N, N⁆ = N := Subgroup.isPerfect_iff.1 h.1.1
  rw [oTwoUpper_top_eq hsq hN]
  exact h

theorem conclusion_of_good_top {D : Type*} [Group D] [Finite D] (h : Good D) :
    CFSG.IsQuasisimple ↥(oTwoUpper (⊤ : Subgroup D)) ∧
      ∀ b : ℕ, Nat.card ↥(oTwoUpper (⊤ : Subgroup D)) ≠ 60 * 2 ^ b :=
  conclusion_of_good (N := ⊤) (fun _ => Subgroup.mem_top _)
    (good_of_mulEquiv Subgroup.topEquiv.symm h)

theorem ne_sixty_mul_two_pow {n d : ℕ} (hd : d ∣ n) (h2 : Nat.Coprime d 2) (h15 : ¬ d ∣ 15)
    (b : ℕ) : n ≠ 60 * 2 ^ b := by
  rintro rfl
  apply h15
  have h' : d ∣ 15 * 2 ^ (b + 2) := by
    rw [show 15 * 2 ^ (b + 2) = 60 * 2 ^ b by rw [pow_add]; ring]
    exact hd
  exact (Nat.Coprime.dvd_mul_right (Nat.Coprime.pow_right (b + 2) h2)).1 h'

theorem exists_ne_comm {X : Type*} [Group X] [Finite X] [IsSimpleGroup X]
    (h : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hcon
  have hcomm : ∀ a b : X, a * b = b * a := fun a b => by
    by_contra hab
    exact hcon ⟨a, b, hab⟩
  let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hcomm }
  exact h (IsSimpleGroup.prime_card (α := X))

theorem good_of_isSimpleGroup {X : Type*} [Group X] [Finite X] [IsSimpleGroup X] {d : ℕ}
    (hp : ¬ (Nat.card X).Prime) (hd : d ∣ Nat.card X) (h2 : Nat.Coprime d 2)
    (h15 : ¬ d ∣ 15) : Good X :=
  ⟨CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_of_isSimpleGroup (exists_ne_comm hp),
    ne_sixty_mul_two_pow hd h2 h15⟩

end KGF618

end CFSG.Quasithin.H13.A5
