module

public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

theorem conjClosure_eq_self' {K T : Subgroup G} (h : T ≤ Subgroup.normalizer (K : Set G)) :
    conjClosure K T = K :=
  le_antisymm (conjClosure_le fun _ ht k hk => (Subgroup.mem_normalizer_iff.1 (h ht) k).1 hk)
    (le_conjClosure K T)

theorem isExt_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {PV PY : ∀ (V : Type) [Group V], Prop}
    (hPV : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → PV V → PV W)
    (hPY : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → PY V → PY W)
    (h : IsExt X PV PY) : IsExt Y PV PY := by
  obtain ⟨N, hN, hPN, hPQ⟩ := h
  have hN' : (N.map e.toMonoidHom).Normal := Subgroup.Normal.map hN _ e.surjective
  refine ⟨N.map e.toMonoidHom, hN', ?_, ?_⟩
  · exact hPV _ _ (N.equivMapOfInjective e.toMonoidHom e.injective) hPN
  · exact hPY _ _ (QuotientGroup.congr N (N.map e.toMonoidHom) e rfl) hPQ

theorem isE2_of_mulEquiv (n : ℕ) : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) →
    IsE2 n V → IsE2 n W := fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩

theorem isAlt_of_mulEquiv (n : ℕ) : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) →
    IsAlt n V → IsAlt n W := fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩

theorem isPSL_of_mulEquiv (n p f : ℕ) : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) →
    IsPSL n p f V → IsPSL n p f W := by
  intro V W _ _ e ⟨hadm, K, hK, hKf, hcard, ⟨g⟩⟩
  exact ⟨hadm, K, hK, hKf, hcard, ⟨e.symm.trans g⟩⟩

@[expose] noncomputable def imageModCenterEquiv {S M₀ : Subgroup G} (hM₀S : M₀ ≤ S)
    (hc : Subgroup.center ↥S = ⊥) : ↥(imageModCenter S M₀) ≃* ↥M₀ := by
  have hinj : Function.Injective (QuotientGroup.mk' (Subgroup.center ↥S)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hc]
  exact ((M₀.subgroupOf S).equivMapOfInjective _ hinj).symm.trans
    (Subgroup.subgroupOfEquivOfLe hM₀S)

theorem isSporadic_quot_center {S : Subgroup G} {s : TauCeti.SporadicName}
    (hc : Subgroup.center ↥S = ⊥) (h : IsSporadic s ↥S) :
    IsSporadic s (↥S ⧸ Subgroup.center ↥S) := by
  obtain ⟨e⟩ := h
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e⟩

theorem summand_le [Finite G] {A V : Subgroup G} {N : Subgroup ↥A} (hV : Nat.card V ≤ 16)
    {m k : ℕ} (hm : 3 ≤ m)
    (h : IsSumOfNaturalModules A V ⊥ N (StatedSL m (ZMod 2)) false k) : k ≤ 1 := by
  obtain ⟨-, -, -, -, -, β, hβ, -, -⟩ := h
  have hcard := Nat.card_le_card_of_surjective β hβ
  have hc : Nat.card (Multiplicative (Fin k → Fin m → ZMod 2)) = 2 ^ (k * m) := by
    rw [Nat.card_eq_fintype_card]
    simp [ZMod.card, ← pow_mul, mul_comm]
  rw [hc] at hcard
  by_contra hk
  have h2 : 2 ^ (2 * 3) ≤ 2 ^ (k * m) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul (by omega) hm)
  omega

end CFSG.Quasithin.KGC31

end
