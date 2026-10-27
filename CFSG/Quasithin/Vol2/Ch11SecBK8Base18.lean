module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base17
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base14
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base16

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K]

@[expose] def natSubOf (a b : K) (S : Submodule K (Fin 3 → K)) : Subgroup (W6 K) :=
  (AddSubgroup.toSubgroup S.toAddSubgroup).map (natEmb a b)

theorem mem_natSubOf {a b : K} {S : Submodule K (Fin 3 → K)} {x : W6 K} :
    x ∈ natSubOf a b S ↔ ∃ u ∈ S, natEmb a b (Multiplicative.ofAdd u) = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Multiplicative.toAdd y, hy, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨Multiplicative.ofAdd u, hu, rfl⟩

theorem card_natSubOf {a b : K} (hab : a ≠ 0 ∨ b ≠ 0) (S : Submodule K (Fin 3 → K)) :
    Nat.card ↥(natSubOf a b S) = Nat.card ↥S := by
  rw [natSubOf, Subgroup.card_map_of_injective (natEmb_injective hab)]
  exact Nat.card_congr
    { toFun := fun x => ⟨Multiplicative.toAdd x.1, x.2⟩
      invFun := fun u => ⟨Multiplicative.ofAdd u.1, u.2⟩
      left_inv := fun x => rfl
      right_inv := fun u => rfl }

theorem scalHom_natEmb (c a b : K) (u : StdMod (Fin 3) K) :
    scalHom c (natEmb a b u) = natEmb a b (Multiplicative.ofAdd (c • Multiplicative.toAdd u)) := by
  apply Multiplicative.toAdd.injective
  change c • natVec a b (Multiplicative.toAdd u) = natVec a b (c • Multiplicative.toAdd u)
  funext i
  rcases i with i | i <;> simp [natVec, mul_left_comm]

variable {G : Type} [Group G] {W : Subgroup G} {hW : IsElemAbelian 2 W}

theorem exists_subspace (Φ : IntMod W hW ≃* W6 K) {V U : Subgroup G} {a b : K}
    (hV : V.comap (psi Φ) = natSub a b) (hUV : U ≤ V)
    (hs : ∀ (c : K) (x : W6 K), psi Φ x ∈ U → psi Φ (scalHom c x) ∈ U) :
    ∃ S : Submodule K (Fin 3 → K), U.comap (psi Φ) = natSubOf a b S := by
  let S : Submodule K (Fin 3 → K) :=
    { carrier := {u | psi Φ (natEmb a b (Multiplicative.ofAdd u)) ∈ U}
      add_mem' := fun {u u'} hu hu' => by
        change psi Φ (natEmb a b (Multiplicative.ofAdd (u + u'))) ∈ U
        rw [ofAdd_add, map_mul, map_mul]
        exact U.mul_mem hu hu'
      zero_mem' := by
        change psi Φ (natEmb a b (Multiplicative.ofAdd 0)) ∈ U
        rw [ofAdd_zero, map_one, map_one]
        exact U.one_mem
      smul_mem' := fun c u hu => by
        have := hs c _ hu
        rw [scalHom_natEmb, toAdd_ofAdd] at this
        exact this }
  refine ⟨S, le_antisymm (fun x hx => ?_) ?_⟩
  · have hxV : x ∈ V.comap (psi Φ) := hUV hx
    rw [hV] at hxV
    obtain ⟨y, rfl⟩ := hxV
    exact mem_natSubOf.mpr ⟨Multiplicative.toAdd y, hx, rfl⟩
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := mem_natSubOf.mp hx
    exact hu

theorem exists_natSub_V [Finite K] (Φ : IntMod W hW ≃* W6 K) {L V V₁ : Subgroup G}
    (hL : (autI hW L).map (congrHom Φ) = diagSL K) (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hVW : V ≤ W) (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hV₁V : V₁ ≤ V)
    (hV₁ : IsEndStable L V ⊥ V₁) (hcard : Nat.card ↥V₁ = Nat.card K) :
    ∃ a b : K, (a ≠ 0 ∨ b ≠ 0) ∧ V.comap (psi Φ) = natSub a b := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  rcases eq_of_isInvD (isInvD_comap Φ hL hLV) with h | h | h
  · exfalso
    have hV : V = ⊥ := by rw [← map_comap_psi Φ hVW, h, Subgroup.map_bot]
    have h1 : V₁ = ⊥ := le_bot_iff.mp (hV ▸ hV₁V)
    rw [h1, Subgroup.card_bot] at hcard
    omega
  · exfalso
    have hTV : ∀ (T : W6 K →* W6 K) (x : W6 K), psi Φ x ∈ V → psi Φ (T x) ∈ V := fun T x _ => by
      have : T x ∈ V.comap (psi Φ) := by rw [h]; trivial
      exact this
    have hstab : ∀ (T : W6 K →* W6 K),
        (∀ γ ∈ StatedSL 3 K, ∀ v, T (matAut (dgHom γ) v) = matAut (dgHom γ) (T v)) →
        ∀ x, psi Φ x ∈ V₁ → psi Φ (T x) ∈ V₁ := fun T hT x hx =>
      psi_mem_of_isEndStable Φ hL hLW hVW hV₁V hV₁ T (hTV T) hT hx
    let F : Submodule K (Fin 3 → K) :=
      { carrier := {u | psi Φ (Multiplicative.ofAdd (Sum.elim u (0 : Fin 3 → K))) ∈ V₁}
        add_mem' := fun {u u'} hu hu' => by
          change psi Φ (Multiplicative.ofAdd (Sum.elim (u + u') (0 : Fin 3 → K))) ∈ V₁
          have e : Multiplicative.ofAdd (Sum.elim (u + u') (0 : Fin 3 → K)) =
              Multiplicative.ofAdd (Sum.elim u (0 : Fin 3 → K)) *
                Multiplicative.ofAdd (Sum.elim u' (0 : Fin 3 → K)) := by
            apply Multiplicative.toAdd.injective
            funext i
            rcases i with i | i <;> simp
          rw [e, map_mul]
          exact V₁.mul_mem hu hu'
        zero_mem' := by
          change psi Φ (Multiplicative.ofAdd (Sum.elim (0 : Fin 3 → K) (0 : Fin 3 → K))) ∈ V₁
          have e : Multiplicative.ofAdd (Sum.elim (0 : Fin 3 → K) (0 : Fin 3 → K)) = 1 := by
            apply Multiplicative.toAdd.injective
            funext i
            rcases i with i | i <;> rfl
          rw [e, map_one]
          exact V₁.one_mem
        smul_mem' := fun c u hu => by
          have := hstab (scalHom c) (fun γ _ v => scalHom_comm c γ v) _ hu
          have e : scalHom c (Multiplicative.ofAdd (Sum.elim u (0 : Fin 3 → K))) =
              Multiplicative.ofAdd (Sum.elim (c • u) (0 : Fin 3 → K)) := by
            apply Multiplicative.toAdd.injective
            funext i
            rcases i with i | i <;> simp [scalHom]
          rw [e] at this
          exact this }
    have hsq : V₁.comap (psi Φ) = sqSub F := by
      apply le_antisymm
      · intro x hx
        have h1 := hstab pr1Hom (fun γ _ v => pr1Hom_comm γ v) x hx
        have h2 := hstab pr1Hom (fun γ _ v => pr1Hom_comm γ v) _
          (hstab swapHom (fun γ _ v => swapHom_comm γ v) x hx)
        exact ⟨h1, h2⟩
      · intro x hx
        have h1 : psi Φ (Multiplicative.ofAdd
            (Sum.elim (Multiplicative.toAdd x ∘ Sum.inl) (0 : Fin 3 → K))) ∈ V₁ := hx.1
        have h2 := hstab swapHom (fun γ _ v => swapHom_comm γ v) _ hx.2
        have e : x = Multiplicative.ofAdd
            (Sum.elim (Multiplicative.toAdd x ∘ Sum.inl) (0 : Fin 3 → K)) *
            swapHom (Multiplicative.ofAdd
              (Sum.elim (Multiplicative.toAdd x ∘ Sum.inr) (0 : Fin 3 → K))) := by
          apply Multiplicative.toAdd.injective
          funext i
          rcases i with i | i <;> simp [swapHom]
        change psi Φ x ∈ V₁
        rw [e, map_mul]
        exact V₁.mul_mem h1 h2
    have h1 := card_comap_psi Φ (hV₁V.trans hVW)
    rw [hsq, card_sqSub, hcard, Module.natCard_eq_pow_finrank (K := K), ← pow_mul] at h1
    have h2 := Nat.pow_right_injective hq (h1.trans (pow_one _).symm)
    omega
  · exact h

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
