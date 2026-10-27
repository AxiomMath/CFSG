module

public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.Background.JonesParshallNatural

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C48Pf.FMod

open Matrix

variable {k m : ℕ}

@[expose] def diagAct (g : Matrix (Fin m) (Fin m) (ZMod 2)) (v : Fin k → Fin m → ZMod 2) :
    Fin k → Fin m → ZMod 2 :=
  fun i => g *ᵥ v i

theorem diagAct_add_left (g h : Matrix (Fin m) (Fin m) (ZMod 2)) (v : Fin k → Fin m → ZMod 2) :
    diagAct (g + h) v = diagAct g v + diagAct h v := by
  funext i
  simp [diagAct, Matrix.add_mulVec]

theorem diagAct_one (v : Fin k → Fin m → ZMod 2) : diagAct 1 v = v := by
  funext i
  simp [diagAct]

theorem diagAct_mul (g h : Matrix (Fin m) (Fin m) (ZMod 2)) (v : Fin k → Fin m → ZMod 2) :
    diagAct (g * h) v = diagAct g (diagAct h v) := by
  funext i
  simp [diagAct, Matrix.mulVec_mulVec]

@[expose] def rowOf (v : Fin k → Fin m → ZMod 2) (r : Fin m) : Fin k → ZMod 2 := fun i => v i r

@[expose] def placeRow (r : Fin m) (ρ : Fin k → ZMod 2) : Fin k → Fin m → ZMod 2 :=
  fun i => Pi.single r (ρ i)

theorem diagAct_single (r s : Fin m) (v : Fin k → Fin m → ZMod 2) :
    diagAct (Matrix.single r s 1) v = placeRow r (rowOf v s) := by
  funext i j
  simp only [diagAct, placeRow, rowOf, Matrix.single_mulVec, one_mul]
  rfl

theorem rowOf_placeRow (r : Fin m) (ρ : Fin k → ZMod 2) : rowOf (placeRow r ρ) r = ρ := by
  funext i
  show (Pi.single r (ρ i) : Fin m → ZMod 2) r = ρ i
  simp

theorem sum_placeRow (v : Fin k → Fin m → ZMod 2) : ∑ r, placeRow r (rowOf v r) = v := by
  funext i j
  simp [placeRow, rowOf, Finset.sum_apply, Pi.single_apply]

theorem placeRow_add (r : Fin m) (ρ σ : Fin k → ZMod 2) :
    placeRow r (ρ + σ) = placeRow r ρ + placeRow r σ := by
  funext i j
  simp [placeRow, Pi.single_apply]
  split_ifs <;> simp

theorem placeRow_zero (r : Fin m) : placeRow r (0 : Fin k → ZMod 2) = 0 := by
  funext i j
  simp [placeRow]

theorem placeRow_neg (r : Fin m) (ρ : Fin k → ZMod 2) : placeRow r (-ρ) = -placeRow r ρ := by
  funext i j
  simp [placeRow, Pi.single_apply]

theorem diagAct_single_mem (hm : 2 ≤ m) {W : AddSubgroup (Fin k → Fin m → ZMod 2)}
    (hW : ∀ r s : Fin m, r ≠ s → ∀ v ∈ W, diagAct (1 + Matrix.single r s 1) v ∈ W)
    (r s : Fin m) {v : Fin k → Fin m → ZMod 2} (hv : v ∈ W) :
    diagAct (Matrix.single r s 1) v ∈ W := by
  have key : ∀ r s : Fin m, r ≠ s → ∀ v ∈ W, diagAct (Matrix.single r s 1) v ∈ W := by
    intro r s hrs v hv
    have h1 := W.sub_mem (hW r s hrs v hv) hv
    rw [diagAct_add_left, diagAct_one] at h1
    simpa using h1
  by_cases hrs : r = s
  · subst hrs
    obtain ⟨t, ht⟩ : ∃ t : Fin m, t ≠ r := by
      by_cases h0 : (r : ℕ) = 0
      · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at h0; simp at h0⟩
      · exact ⟨⟨0, by omega⟩, fun h => h0 (by rw [← h])⟩
    have h2 := key r t (Ne.symm ht) _ (key t r ht v hv)
    rwa [← diagAct_mul, Matrix.single_mul_single_same, one_mul] at h2
  · exact key r s hrs v hv

@[expose] def rowSub (hm : 0 < m) (W : AddSubgroup (Fin k → Fin m → ZMod 2)) :
    AddSubgroup (Fin k → ZMod 2) where
  carrier := {ρ | placeRow ⟨0, hm⟩ ρ ∈ W}
  add_mem' := fun {a b} ha hb => by
    show placeRow ⟨0, hm⟩ (a + b) ∈ W
    rw [placeRow_add]
    exact W.add_mem ha hb
  zero_mem' := by
    show placeRow ⟨0, hm⟩ 0 ∈ W
    rw [placeRow_zero]
    exact W.zero_mem
  neg_mem' := fun {a} ha => by
    show placeRow ⟨0, hm⟩ (-a) ∈ W
    rw [placeRow_neg]
    exact W.neg_mem ha

theorem mem_rowSub (hm : 0 < m) {W : AddSubgroup (Fin k → Fin m → ZMod 2)}
    {ρ : Fin k → ZMod 2} : ρ ∈ rowSub hm W ↔ placeRow ⟨0, hm⟩ ρ ∈ W := Iff.rfl

theorem mem_iff_rows (hm : 2 ≤ m) {W : AddSubgroup (Fin k → Fin m → ZMod 2)}
    (hW : ∀ r s : Fin m, r ≠ s → ∀ v ∈ W, diagAct (1 + Matrix.single r s 1) v ∈ W)
    (v : Fin k → Fin m → ZMod 2) :
    v ∈ W ↔ ∀ r, rowOf v r ∈ rowSub (by omega) W := by
  constructor
  · intro hv r
    rw [mem_rowSub, ← diagAct_single]
    exact diagAct_single_mem hm hW _ _ hv
  · intro hr
    rw [← sum_placeRow v]
    refine AddSubgroup.sum_mem _ fun r _ => ?_
    have h1 := diagAct_single_mem hm hW r ⟨0, by omega⟩ (hr r)
    rwa [diagAct_single, rowOf_placeRow] at h1

theorem exists_equiv_copies (hm : 2 ≤ m) (W : AddSubgroup (Fin k → Fin m → ZMod 2))
    (hW : ∀ r s : Fin m, r ≠ s → ∀ v ∈ W, diagAct (1 + Matrix.single r s 1) v ∈ W) :
    ∃ (k' : ℕ) (e : ↥W ≃+ (Fin k' → Fin m → ZMod 2)), k' ≤ k ∧
      ∀ (g : Matrix (Fin m) (Fin m) (ZMod 2)) (w : ↥W) (hgw : diagAct g (w : _) ∈ W),
        e ⟨diagAct g w, hgw⟩ = diagAct g (e w) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : 0 < m := by omega
  set R : Submodule (ZMod 2) (Fin k → ZMod 2) := AddSubgroup.toZModSubmodule 2 (rowSub hm0 W)
    with hR
  have hmemR : ∀ ρ : Fin k → ZMod 2, ρ ∈ R ↔ ρ ∈ rowSub hm0 W := fun ρ => by
    rw [hR, AddSubgroup.mem_toZModSubmodule]
  have hrow : ∀ (v : Fin k → Fin m → ZMod 2), v ∈ W → ∀ r, rowOf v r ∈ R := fun v hv r =>
    (hmemR _).2 ((mem_iff_rows hm hW v).1 hv r)
  set b := Module.finBasis (ZMod 2) R with hb
  set c : R ≃ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) R) → ZMod 2) := b.equivFun with hc
  have hinvmem : ∀ T : Fin (Module.finrank (ZMod 2) R) → Fin m → ZMod 2,
      (fun i r => ((c.symm (fun j => T j r) : R) : Fin k → ZMod 2) i) ∈ W := by
    intro T
    refine (mem_iff_rows hm hW _).2 fun r => (hmemR _).1 ?_
    exact (c.symm (fun j => T j r)).2
  refine ⟨Module.finrank (ZMod 2) R,
    { toFun := fun w j r => c ⟨rowOf (w : Fin k → Fin m → ZMod 2) r, hrow _ w.2 r⟩ j
      invFun := fun T => ⟨fun i r => ((c.symm (fun j => T j r) : R) : Fin k → ZMod 2) i,
        hinvmem T⟩
      left_inv := fun w => by
        apply Subtype.ext
        funext i r
        have h1 : (fun j => c ⟨rowOf (w : Fin k → Fin m → ZMod 2) r, hrow _ w.2 r⟩ j) =
            c ⟨rowOf (w : Fin k → Fin m → ZMod 2) r, hrow _ w.2 r⟩ := rfl
        simp only [h1, LinearEquiv.symm_apply_apply]
        rfl
      right_inv := fun T => by
        funext j r
        have h1 : (⟨rowOf (fun i r => ((c.symm (fun j => T j r) : R) : Fin k → ZMod 2) i) r,
            hrow _ (hinvmem T) r⟩ : R) = c.symm (fun j => T j r) := by
          apply Subtype.ext
          rfl
        simp only [h1, LinearEquiv.apply_symm_apply]
      map_add' := fun v w => by
        funext j r
        have h1 : (⟨rowOf ((v + w : ↥W) : Fin k → Fin m → ZMod 2) r, hrow _ (v + w).2 r⟩ : R) =
            ⟨rowOf (v : Fin k → Fin m → ZMod 2) r, hrow _ v.2 r⟩ +
              ⟨rowOf (w : Fin k → Fin m → ZMod 2) r, hrow _ w.2 r⟩ := by
          apply Subtype.ext
          rfl
        simp only [h1, map_add, Pi.add_apply] }, ?_, ?_⟩
  · have := Submodule.finrank_le R
    rwa [Module.finrank_fin_fun] at this
  · intro g w hgw
    funext j r
    simp only [AddEquiv.coe_mk, Equiv.coe_fn_mk]
    have h1 : (⟨rowOf (diagAct g (w : Fin k → Fin m → ZMod 2)) r, hrow _ hgw r⟩ : R) =
        ∑ s, g r s • (⟨rowOf (w : Fin k → Fin m → ZMod 2) s, hrow _ w.2 s⟩ : R) := by
      apply Subtype.ext
      funext i
      simp [rowOf, diagAct, Matrix.mulVec, dotProduct, Finset.sum_apply]
    rw [h1, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp [diagAct, Matrix.mulVec, dotProduct]

section Concl

open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

theorem isSumOfNaturalModulesVia_of_inj {A V : Subgroup G} {m k : ℕ} (hm : 2 ≤ m)
    (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (α : ↥A →* Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) (hα : Function.Surjective α)
    (Ψ : ↥V →* Multiplicative (Fin k → Fin m → ZMod 2)) (hΨ : Function.Injective Ψ)
    (hequiv : ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (Ψ v) =
        diagAct ((α a : Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) :
          Matrix (Fin m) (Fin m) (ZMod 2)) (Multiplicative.toAdd (Ψ u))) :
    ∃ k', k' ≤ k ∧ (V ≠ ⊥ → 1 ≤ k') ∧
      IsSumOfNaturalModulesVia A V ⊥
        ((specialLinearGroupEquivStatedSL m (ZMod 2)).toMonoidHom.comp α) false k' := by
  classical
  have hconj : ∀ (a : ↥A) (u : ↥V), (a : G) * u * (a : G)⁻¹ ∈ V := fun a u =>
    (Subgroup.mem_normalizer_iff.1 (hAV a.2) u).1 u.2
  let W : AddSubgroup (Fin k → Fin m → ZMod 2) :=
    { carrier := {w | ∃ v : ↥V, Multiplicative.toAdd (Ψ v) = w}
      add_mem' := by
        rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
        exact ⟨u * v, by rw [map_mul, toAdd_mul]⟩
      zero_mem' := ⟨1, by rw [map_one, toAdd_one]⟩
      neg_mem' := by
        rintro _ ⟨u, rfl⟩
        exact ⟨u⁻¹, by rw [map_inv, toAdd_inv]⟩ }
  have hmemW : ∀ v : ↥V, Multiplicative.toAdd (Ψ v) ∈ W := fun v => ⟨v, rfl⟩
  have hW : ∀ r s : Fin m, r ≠ s → ∀ w ∈ W, diagAct (1 + Matrix.single r s 1) w ∈ W := by
    rintro r s hrs _ ⟨u, rfl⟩
    obtain ⟨a, ha⟩ := hα (Matrix.SpecialLinearGroup.transvection hrs (1 : ZMod 2))
    refine ⟨⟨_, hconj a u⟩, ?_⟩
    rw [hequiv a u ⟨_, hconj a u⟩ rfl, ha]
    rfl
  obtain ⟨k', e, hk', he⟩ := exists_equiv_copies hm W hW
  let β : ↥V →* Multiplicative (Fin k' → Fin m → ZMod 2) :=
    { toFun := fun v => Multiplicative.ofAdd (e ⟨Multiplicative.toAdd (Ψ v), hmemW v⟩)
      map_one' := by
        have h1 : (⟨Multiplicative.toAdd (Ψ 1), hmemW 1⟩ : ↥W) = 0 := by
          apply Subtype.ext
          simp
        simp only [h1, map_zero, ofAdd_zero]
      map_mul' := fun u v => by
        have h1 : (⟨Multiplicative.toAdd (Ψ (u * v)), hmemW (u * v)⟩ : ↥W) =
            ⟨Multiplicative.toAdd (Ψ u), hmemW u⟩ + ⟨Multiplicative.toAdd (Ψ v), hmemW v⟩ := by
          apply Subtype.ext
          simp
        simp only [h1, map_add, ofAdd_add] }
  have hβ : ∀ v, Multiplicative.toAdd (β v) = e ⟨Multiplicative.toAdd (Ψ v), hmemW v⟩ :=
    fun v => rfl
  have hβinj : Function.Injective β := by
    intro u v huv
    have h1 := congrArg Multiplicative.toAdd huv
    rw [hβ, hβ] at h1
    have h2 := congrArg Subtype.val (e.injective h1)
    exact hΨ (Multiplicative.toAdd.injective h2)
  have hβsurj : Function.Surjective β := by
    intro t
    obtain ⟨⟨_, v, rfl⟩, hv⟩ := e.surjective (Multiplicative.toAdd t)
    exact ⟨v, by apply Multiplicative.toAdd.injective; rw [hβ]; exact hv⟩
  refine ⟨k', hk', fun hV => ?_, hAV, bot_le, β, hβsurj, ?_, ?_⟩
  · by_contra hk0
    have hk0' : k' = 0 := by omega
    apply hV
    rw [eq_bot_iff]
    intro x hx
    have h1 : β ⟨x, hx⟩ = β 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      exact absurd i.2 (by omega)
    have h2 := hβinj h1
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h2
  · ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · intro hv
      have h1 : β v = β 1 := by rw [hv, map_one]
      exact congrArg Subtype.val (hβinj h1)
    · intro hv
      have : v = 1 := Subtype.ext hv
      rw [this, map_one]
  · intro a u v huv i
    have hvmem : Multiplicative.toAdd (Ψ v) = diagAct ((α a : Matrix.SpecialLinearGroup
        (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) (Multiplicative.toAdd (Ψ u)) :=
      hequiv a u v huv
    have h1 : (⟨Multiplicative.toAdd (Ψ v), hmemW v⟩ : ↥W) =
        ⟨diagAct ((α a : Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) :
          Matrix (Fin m) (Fin m) (ZMod 2)) ((⟨Multiplicative.toAdd (Ψ u), hmemW u⟩ : ↥W) :
            Fin k → Fin m → ZMod 2), by rw [← hvmem]; exact hmemW v⟩ :=
      Subtype.ext hvmem
    rw [hβ, hβ, h1, he]
    rfl

theorem isSumOfNaturalModules_of_inj {A V : Subgroup G} {N : Subgroup ↥A} {m k : ℕ}
    (hm : 2 ≤ m) (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (α : ↥A →* Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) (hα : Function.Surjective α)
    (hker : α.ker = N)
    (Ψ : ↥V →* Multiplicative (Fin k → Fin m → ZMod 2)) (hΨ : Function.Injective Ψ)
    (hequiv : ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (Ψ v) =
        diagAct ((α a : Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) :
          Matrix (Fin m) (Fin m) (ZMod 2)) (Multiplicative.toAdd (Ψ u))) :
    ∃ k', k' ≤ k ∧ (V ≠ ⊥ → 1 ≤ k') ∧
      IsSumOfNaturalModules A V ⊥ N (StatedSL m (ZMod 2)) false k' := by
  obtain ⟨k', hk', hk1, hvia⟩ := isSumOfNaturalModulesVia_of_inj hm hAV α hα Ψ hΨ hequiv
  refine ⟨k', hk', hk1, _, (specialLinearGroupEquivStatedSL m (ZMod 2)).surjective.comp hα, ?_,
    hvia⟩
  rw [← hker]
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]

theorem isSumOfNaturalModules_of_inj_dual {A V : Subgroup G} {N : Subgroup ↥A} {m k : ℕ}
    (hm : 2 ≤ m) (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (α : ↥A →* Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) (hα : Function.Surjective α)
    (hker : α.ker = N)
    (Ψ : ↥V →* Multiplicative (Fin k → Fin m → ZMod 2)) (hΨ : Function.Injective Ψ)
    (hequiv : ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * a⁻¹ →
      Multiplicative.toAdd (Ψ v) =
        diagAct (((α a)⁻¹ : Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) :
          Matrix (Fin m) (Fin m) (ZMod 2))ᵀ (Multiplicative.toAdd (Ψ u))) :
    ∃ k', k' ≤ k ∧ (V ≠ ⊥ → 1 ≤ k') ∧
      IsSumOfNaturalModules A V ⊥ N (StatedSL m (ZMod 2)) false k' := by
  refine isSumOfNaturalModules_of_inj hm hAV
    ((JonesParshall.invTransposeSL m (ZMod 2)).toMonoidHom.comp α)
    ((JonesParshall.invTransposeSL m (ZMod 2)).surjective.comp hα) ?_ Ψ hΨ ?_
  · rw [← hker]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  · intro a u v huv
    rw [hequiv a u v huv]
    rfl

end Concl

end CFSG.Quasithin.C48Pf.FMod
