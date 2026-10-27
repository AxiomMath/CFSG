module

public import CFSG.Quasithin.Vol2.GoldschmidtF431BNRad
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYam

public section

namespace CFSG.Quasithin.H13.F431.BN

open CFSG.GH74.BNPair CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Sec53F.Yam

variable {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)

theorem eq_B_or_P_or_top {A : Subgroup X} (hBA : D.B ≤ A) :
    A = D.B ∨ (∃ i : Bool, A = P D i) ∨ A = ⊤ := by
  classical
  obtain ⟨J, hJ, rfl⟩ := D.isTits.exists_parabolic hBA
  have hmem : ∀ x ∈ J, x = D.w₁ ∨ x = D.w₂ := by
    intro x hx
    simpa using hJ hx
  by_cases h1 : D.w₁ ∈ J <;> by_cases h2 : D.w₂ ∈ J
  · right; right
    have : J = {D.w₁, D.w₂} := by
      refine Finset.Subset.antisymm hJ ?_
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact h1
      · rw [Finset.mem_singleton.1 hx]; exact h2
    subst this
    exact D.isTits.parabolic_univ
  · right; left
    refine ⟨true, ?_⟩
    have : J = {D.w₁} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨h1, fun x hx => ?_⟩
      rcases hmem x hx with rfl | rfl
      · rfl
      · exact absurd hx h2
    subst this
    simp [P, pgen, gen]
  · right; left
    refine ⟨false, ?_⟩
    have : J = {D.w₂} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨h2, fun x hx => ?_⟩
      rcases hmem x hx with rfl | rfl
      · exact absurd hx h1
      · rfl
    subst this
    simp [P, pgen, gen]
  · left
    have : J = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.2 fun x hx => ?_
      rcases hmem x hx with rfl | rfl
      · exact h1 hx
      · exact h2 hx
    subst this
    simpa using parabolic_empty (B := D.B) (N := D.N)

theorem mi_not_mem_P_not (i : Bool) : mi D i ∉ P D (!i) := by
  intro h
  rcases (mem_P_iff D).1 h with hB | hd
  · exact D.rank2.not_mem_B_of_mem_dc (D.rank2.gen_mem i) (mi_mem_dc D i) hB
  · exact D.rank2.gen_ne i (D.isTits.dc_injective (dc_eq_of_mem (mi_mem_dc D i) hd))

theorem not_le_P (i : Bool) : ¬ P D i ≤ P D (!i) :=
  fun h => mi_not_mem_P_not D i (h (mi_mem_P D i))

theorem P_ne_top (i : Bool) : P D i ≠ ⊤ := by
  intro h
  have := mi_not_mem_P_not D (!i)
  rw [Bool.not_not] at this
  exact this (h ▸ Subgroup.mem_top _)

theorem isCoatom_P (i : Bool) : IsCoatom (P D i) := by
  refine ⟨P_ne_top D i, fun A hA => ?_⟩
  have hBA : D.B ≤ A := (B_le_P D i).trans hA.le
  rcases eq_B_or_P_or_top D hBA with h | ⟨j, h⟩ | h
  · exact absurd (h ▸ B_le_P D i) (not_le_of_gt hA)
  · subst h
    by_cases hj : j = i
    · subst hj
      exact absurd hA (lt_irrefl _)
    · have : j = !i := by cases i <;> cases j <;> simp_all
      subst this
      exact absurd hA.le (not_le_P D i)
  · exact h

theorem over_of_ne_top {A : Subgroup X} (hBA : D.B ≤ A) (hA : A ≠ ⊤) :
    A ≤ D.P₁ ∨ A ≤ D.P₂ := by
  rcases eq_B_or_P_or_top D hBA with h | ⟨j, h⟩ | h
  · exact Or.inl (h ▸ B_le_P D true)
  · cases j
    · exact Or.inr h.le
    · exact Or.inl h.le
  · exact absurd h hA

theorem P₁_ne_P₂ : D.P₁ ≠ D.P₂ := fun h => not_le_P D true h.le

include D in
theorem not_comm : ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨m₁, hm₁⟩ := QuotientGroup.mk_surjective D.w₁
  obtain ⟨m₂, hm₂⟩ := QuotientGroup.mk_surjective D.w₂
  refine ⟨m₁, m₂, fun h => ?_⟩
  have hc : D.w₁ * D.w₂ = D.w₂ * D.w₁ := by
    rw [← hm₁, ← hm₂, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext h)
  have h2 : (D.w₁ * D.w₂) ^ 2 = 1 := by
    calc (D.w₁ * D.w₂) ^ 2 = D.w₁ * (D.w₂ * D.w₁) * D.w₂ := by rw [pow_two]; simp only [mul_assoc]
      _ = D.w₁ * (D.w₁ * D.w₂) * D.w₂ := by rw [← hc]
      _ = (D.w₁ * D.w₁) * (D.w₂ * D.w₂) := by group
      _ = 1 := by rw [D.w₁_mul_self, D.w₂_mul_self, one_mul]
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [D.rank2.dih.orderOf_mul] at h3
  have := Nat.le_of_dvd (by norm_num) h3
  have := D.three_le
  omega

theorem eq_bot_of_normal_isPGroup [Finite X] [IsSimpleGroup X] (hnc : ∃ a b : X, a * b ≠ b * a)
    (R : Subgroup X) (hR : R.Normal) (h2 : IsPGroup 2 R) : R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hR.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    rw [h] at h2
    have hX : IsPGroup 2 X := h2.of_equiv Subgroup.topEquiv
    obtain ⟨a, b, hab⟩ := hnc
    have : Nontrivial X := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
    have hz : Nontrivial (Subgroup.center X) := hX.center_nontrivial
    rcases (inferInstance : (Subgroup.center X).Normal).eq_bot_or_eq_top with h3 | h3
    · obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : Subgroup.center X)
      rw [h3, Subgroup.mem_bot] at hx
      exact hx1 (Subtype.ext hx)
    · have : a ∈ Subgroup.center X := by rw [h3]; exact Subgroup.mem_top a
      exact hab ((Subgroup.mem_center_iff.mp this b).symm)

theorem yamStd {X : Type} [Group X] {n : ℕ} (D : RankTwoSystem X n) [Finite X] [IsSimpleGroup X]
    (hU : IsSylowTwoOf D.U ⊤) : YamStd X D.U D.P₁ D.P₂ where
  sylow := hU
  no_normal := fun R hR h2 => eq_bot_of_normal_isPGroup (not_comm D) R hR h2
  ne := P₁_ne_P₂ D
  le₀ := (normalizer_U_eq_B D).le.trans (B_le_P D true)
  le₁ := (normalizer_U_eq_B D).le.trans (B_le_P D false)
  coatom₀ := isCoatom_P D true
  coatom₁ := isCoatom_P D false
  above := fun _ hA hne => over_of_ne_top D ((normalizer_U_eq_B D).symm.le.trans hA) hne
  twoLoc₀ := ⟨Q D true, Q_ne_bot D hU true, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P D true),
    (normalizer_Q D hU true).symm⟩
  twoLoc₁ := ⟨Q D false, Q_ne_bot D hU false, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P D false),
    (normalizer_Q D hU false).symm⟩

theorem isYAmalgamPair {X : Type} [Group X] {n : ℕ} (D : RankTwoSystem X n) [Finite X]
    [IsSimpleGroup X] (hU : IsSylowTwoOf D.U ⊤) : IsYAmalgamPair D.U D.P₁ D.P₂ :=
  (yamStd D hU).isYAmalgamPair

theorem map_symm_map_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (M : Subgroup H) :
    (M.map e.symm.toMonoidHom).map e.toMonoidHom = M := by
  rw [Subgroup.map_map]
  have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem exists_iso_of_yam {X : Type} [Group X] {n : ℕ} (D : RankTwoSystem X n) [Finite X]
    [IsSimpleGroup X] (hU : IsSylowTwoOf D.U ⊤) {D' : Type} [Group D'] (e : X ≃* D')
    (A : CFSG.Quasithin.H13.F431.LieAmalgamExt D') :
    ∃ e' : X ≃* D', A.TD = D.U.map e'.toMonoidHom ∧
      ((A.P1 = D.P₁.map e'.toMonoidHom ∧ A.P2 = D.P₂.map e'.toMonoidHom) ∨
        (A.P1 = D.P₂.map e'.toMonoidHom ∧ A.P2 = D.P₁.map e'.toMonoidHom)) := by
  obtain ⟨c, hT, hP⟩ := (yamStd D hU).pair e.symm A.yam
  have key : ∀ (M : Subgroup D') (M' : Subgroup X), M.map e.symm.toMonoidHom =
      M'.map (MulAut.conj c).toMonoidHom →
      M = M'.map ((MulAut.conj c).trans e).toMonoidHom := by
    intro M M' h
    rw [← map_symm_map_equiv e M, h, Subgroup.map_map]
    rfl
  refine ⟨(MulAut.conj c).trans e, key _ _ hT, ?_⟩
  rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨key _ _ h1, key _ _ h2⟩
  · exact Or.inr ⟨key _ _ h1, key _ _ h2⟩

end CFSG.Quasithin.H13.F431.BN
