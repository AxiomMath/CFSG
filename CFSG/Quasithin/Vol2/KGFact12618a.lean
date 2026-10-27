module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin.H13.KG12618

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Equiv

section General

variable {Γ : Type} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem inf_centralizer_eq_bot {Y K T : Subgroup Γ}
    (hYK : Y ≤ Subgroup.normalizer (K : Set Γ)) (hKs : IsSimpleGroup ↥K)
    (hnc : ∃ a b : ↥K, a * b ≠ b * a) (hT : IsSylowTwoOf T Y) (hYeq : Y = K ⊔ T)
    (hO2 : pCoreOf 2 Y = ⊥) : Y ⊓ Subgroup.centralizer (K : Set Γ) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Y ⊓ Subgroup.centralizer (K : Set Γ) with hC
  have hCK : ∀ x ∈ C, x ∈ K → x = 1 := by
    intro x hx hxK
    have hz : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hx.2 g g.2)
    have hZ : Subgroup.center ↥K = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥K) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnc
        exact hab ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a)
    rw [hZ, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  have hTK : T ≤ Subgroup.normalizer (K : Set Γ) := hT.1.trans hYK
  have hpow : ∀ y ∈ Y, ∃ k : ℕ, y ^ 2 ^ k ∈ K := by
    intro y hy
    have hy' : y ∈ (↑(K ⊔ T) : Set Γ) := hYeq ▸ hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K T hTK] at hy'
    obtain ⟨a, ha, t, ht, hat⟩ := hy'
    obtain ⟨j, hj⟩ := hT.2.1 ⟨t, ht⟩
    have hj' : t ^ 2 ^ j = 1 := congrArg Subtype.val hj
    obtain ⟨a', ha', hp⟩ := A4.exists_pow_mul_eq ha (hTK ht) (2 ^ j)
    refine ⟨j, ?_⟩
    rw [← hat, hp, hj', mul_one]
    exact ha'
  have hC2 : IsPGroup 2 ↥C := by
    intro c
    obtain ⟨k, hk⟩ := hpow c c.2.1
    refine ⟨k, Subtype.ext ?_⟩
    have hcC : (c : Γ) ^ 2 ^ k ∈ C := C.pow_mem c.2 _
    simpa using hCK _ hcC hk
  have hYC : Y ≤ Subgroup.normalizer (C : Set Γ) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy,
      B2F.le_normalizer_centralizer hYK hy⟩
  have hle := le_pCoreOf_of_le_normalizer inf_le_left hYC hC2
  rw [hO2] at hle
  exact le_bot_iff.1 hle

theorem exists_perm_of_ker_eq' {X : Type*} [Group X] {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    {α β : X →* alternatingGroup (Fin n)} (hα : Function.Surjective α)
    (hβ : Function.Surjective β) (hker : α.ker = β.ker) :
    ∃ π : Perm (Fin n), ∀ x, (α x : Perm (Fin n)) = π * (β x : Perm (Fin n)) * π⁻¹ := by
  let eα := QuotientGroup.quotientKerEquivOfSurjective α hα
  let eβ := QuotientGroup.quotientKerEquivOfSurjective β hβ
  let ψ : alternatingGroup (Fin n) ≃* alternatingGroup (Fin n) :=
    eβ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans eα)
  have hψ : ∀ x, ψ (β x) = α x := by
    intro x
    have h1 : eβ.symm (β x) = QuotientGroup.mk x := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show eα ((QuotientGroup.quotientMulEquivOfEq hker.symm) (eβ.symm (β x))) = α x
    rw [h1]
    rfl
  obtain ⟨π, hπ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn
    hn6).2 ψ
  refine ⟨π, fun x => ?_⟩
  rw [← hψ x, ← hπ, MulAut.conjNormal_apply]

omit [Finite Γ] in
theorem exists_perm_conj {K : Subgroup Γ} {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : ↥K ≃* ↥(alternatingGroup (Fin n))) {y : Γ}
    (hy : y ∈ Subgroup.normalizer (K : Set Γ)) :
    ∃ π : Perm (Fin n), ∀ (k : Γ) (hk : k ∈ K),
      ((e ⟨y * k * y⁻¹, (Subgroup.mem_normalizer_iff.1 hy k).1 hk⟩ :
        ↥(alternatingGroup (Fin n))) : Perm (Fin n)) =
        π * (e ⟨k, hk⟩ : Perm (Fin n)) * π⁻¹ := by
  let c : ↥K →* ↥K :=
    { toFun := fun k => ⟨y * k * y⁻¹, (Subgroup.mem_normalizer_iff.1 hy k).1 k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hcs : Function.Surjective c := by
    intro k
    have hk' : y⁻¹ * k * y ∈ K := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hy) k).1 k.2
      simpa using this
    exact ⟨⟨y⁻¹ * k * y, hk'⟩, Subtype.ext (by simp [c, mul_assoc])⟩
  have hci : Function.Injective c := by
    intro a b hab
    have h := congrArg Subtype.val hab
    simp only [c, MonoidHom.coe_mk, OneHom.coe_mk] at h
    exact Subtype.ext (by simpa using h)
  obtain ⟨π, hπ⟩ := exists_perm_of_ker_eq' hn hn6
    (α := e.toMonoidHom.comp c) (β := e.toMonoidHom)
    (e.surjective.comp hcs) e.surjective (by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective, (MonoidHom.ker_eq_bot_iff _).2 hci,
        (MonoidHom.ker_eq_bot_iff _).2 e.injective])
  exact ⟨π, fun k hk => hπ ⟨k, hk⟩⟩

theorem eq_top_of_index_le {X : Type*} [Group X] [Finite X] (hs : IsSimpleGroup X) {k : ℕ}
    (hk : ∀ m ≤ k, ¬ Nat.card X ∣ m.factorial) (M : Subgroup X) (hM : M.index ≤ k) :
    M = ⊤ := by
  have hNn := M.normalCore_normal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M.normalCore with h | h
  · exfalso
    have hd := M.index_normalCore_dvd_factorial_index
    rw [h, Subgroup.index_bot] at hd
    exact hk _ hM hd
  · exact top_le_iff.1 (h ▸ M.normalCore_le)

end General

section Seven

theorem exists_fixed_seven {H : Subgroup (Perm (Fin 7))}
    (hsmall : ∀ M : Subgroup ↥H, M.index ≤ 5 → M = ⊤) (h7 : ¬ 7 ∣ Nat.card ↥H) :
    ∃ p : Fin 7, ∀ h ∈ H, h p = p := by
  classical
  by_contra hno
  push Not at hno
  have horb : ∀ p : Fin 7, (MulAction.orbit ↥H p).ncard = 6 := by
    intro p
    have hidx := MulAction.index_stabilizer ↥H p
    have hle : (MulAction.orbit ↥H p).ncard ≤ 7 := by
      calc (MulAction.orbit ↥H p).ncard ≤ (Set.univ : Set (Fin 7)).ncard :=
            Set.ncard_le_ncard (Set.subset_univ _)
        _ = 7 := by rw [Set.ncard_univ, Nat.card_fin]
    have hne : MulAction.stabilizer ↥H p ≠ ⊤ := by
      intro htop
      obtain ⟨h, hh, hhp⟩ := hno p
      have : (⟨h, hh⟩ : ↥H) ∈ MulAction.stabilizer ↥H p := htop ▸ Subgroup.mem_top _
      exact hhp this
    have h6 : 6 ≤ (MulAction.orbit ↥H p).ncard := by
      by_contra hlt
      exact hne (hsmall _ (by omega))
    have hdvd : (MulAction.orbit ↥H p).ncard ∣ Nat.card ↥H := by
      rw [← hidx]
      exact (MulAction.stabilizer ↥H p).index_dvd_card
    interval_cases h : (MulAction.orbit ↥H p).ncard
    · rfl
    · exact absurd hdvd h7
  obtain ⟨q, hq⟩ : ∃ q : Fin 7, q ∉ MulAction.orbit ↥H (0 : Fin 7) := by
    by_contra hall
    push Not at hall
    have : MulAction.orbit ↥H (0 : Fin 7) = Set.univ := Set.eq_univ_of_forall hall
    have h := horb 0
    rw [this, Set.ncard_univ, Nat.card_fin] at h
    exact absurd h (by decide)
  have hdisj : Disjoint (MulAction.orbit ↥H (0 : Fin 7)) (MulAction.orbit ↥H q) := by
    rw [Set.disjoint_left]
    intro x hx0 hxq
    have h1 : MulAction.orbit ↥H x = MulAction.orbit ↥H q := MulAction.orbit_eq_iff.2 hxq
    have h2 : MulAction.orbit ↥H x = MulAction.orbit ↥H (0 : Fin 7) := MulAction.orbit_eq_iff.2 hx0
    apply hq
    rw [← h2, h1]
    exact MulAction.mem_orbit_self q
  have hu := Set.ncard_union_eq hdisj
  rw [horb 0, horb q] at hu
  have hle : (MulAction.orbit ↥H (0 : Fin 7) ∪ MulAction.orbit ↥H q).ncard ≤ 7 := by
    calc _ ≤ (Set.univ : Set (Fin 7)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
      _ = 7 := by rw [Set.ncard_univ, Nat.card_fin]
  omega

theorem eq_one_of_commute_c3 (σ : Perm (Fin 7))
    (h₁ : σ * (swap 0 2 * swap 0 1) = (swap 0 2 * swap 0 1) * σ)
    (h₂ : σ * (swap 2 4 * swap 2 3) = (swap 2 4 * swap 2 3) * σ)
    (h₃ : σ * (swap 4 0 * swap 4 5) = (swap 4 0 * swap 4 5) * σ) : σ = 1 := by
  set c₁ : Perm (Fin 7) := swap 0 2 * swap 0 1 with hc₁
  set c₂ : Perm (Fin 7) := swap 2 4 * swap 2 3 with hc₂
  set c₃ : Perm (Fin 7) := swap 4 0 * swap 4 5 with hc₃
  have e₁ : ∀ x, σ (c₁ x) = c₁ (σ x) := fun x => by
    simpa [Perm.mul_apply] using congrArg (fun τ : Perm (Fin 7) => τ x) h₁
  have e₂ : ∀ x, σ (c₂ x) = c₂ (σ x) := fun x => by
    simpa [Perm.mul_apply] using congrArg (fun τ : Perm (Fin 7) => τ x) h₂
  have e₃ : ∀ x, σ (c₃ x) = c₃ (σ x) := fun x => by
    simpa [Perm.mul_apply] using congrArg (fun τ : Perm (Fin 7) => τ x) h₃
  have s1 : σ 1 = c₁ (σ 0) := by rw [← e₁]; rfl
  have s2 : σ 2 = c₁ (σ 1) := by rw [← e₁]; rfl
  have s3 : σ 3 = c₂ (σ 2) := by rw [← e₂]; rfl
  have s4 : σ 4 = c₂ (σ 3) := by rw [← e₂]; rfl
  have s4' : σ 4 = c₃ (σ 0) := by rw [← e₃]; rfl
  have s5 : σ 5 = c₃ (σ 4) := by rw [← e₃]; rfl
  have h10 : σ 1 ≠ σ 0 := fun h => absurd (σ.injective h) (by decide)
  have key : ∀ a : Fin 7, c₁ a ≠ a → c₃ a = c₂ (c₂ (c₁ (c₁ a))) → a = 0 := by
    rw [hc₁, hc₂, hc₃]
    decide
  have h0 : σ 0 = 0 := key (σ 0) (by rw [← s1]; exact h10) (by rw [← s4', s4, s3, s2, s1])
  have f1 : σ 1 = 1 := by rw [s1, h0, hc₁]; decide
  have f2 : σ 2 = 2 := by rw [s2, f1, hc₁]; decide
  have f3 : σ 3 = 3 := by rw [s3, f2, hc₂]; decide
  have f4 : σ 4 = 4 := by rw [s4', h0, hc₃]; decide
  have f5 : σ 5 = 5 := by rw [s5, f4, hc₃]; decide
  have hfix : ∀ i : Fin 7, i ≠ 6 → σ i = i := by
    intro i hi
    fin_cases i
    · exact h0
    · exact f1
    · exact f2
    · exact f3
    · exact f4
    · exact f5
    · exact absurd rfl hi
  have h6 : σ 6 = 6 := by
    by_contra h
    have h1 := hfix (σ 6) h
    exact h (σ.injective h1)
  ext i
  by_cases hi : i = 6
  · rw [hi, h6]; rfl
  · rw [hfix i hi]; rfl

end Seven

end CFSG.Quasithin.H13.KG12618
