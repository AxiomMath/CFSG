module

public import CFSG.Timmesfeld.RankTwo.Positive
public import CFSG.Timmesfeld.RankTwo.Levi

public section

namespace CFSG.Timmesfeld

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.Timmesfeld.Levi

variable {K : Type*} [Group K] {D : UniversalRootDatum K}

theorem apply_eq_of_index_eq {G : Type*} {X : (Fin D.rank → ℤ) → Subgroup K}
    (φ : ∀ γ, X γ → G) {γ₁ γ₂ : Fin D.rank → ℤ} (e : γ₁ = γ₂) (y₁ : X γ₁) (y₂ : X γ₂)
    (hy : (y₁ : K) = y₂) : φ γ₁ y₁ = φ γ₂ y₂ := by
  subst e
  exact congrArg _ (Subtype.ext hy)

theorem extendsToHom_cone_pairRoots {i j : Fin D.rank} (n : Fin D.rank → K)
    (hn : ∀ k, (k = i ∨ k = j) → ∀ γ ∈ pairRoots D i j, ∀ x ∈ D.rootGroup γ,
      n k * x * (n k)⁻¹ ∈
        D.rootGroup ((Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible).refl k γ))
    {G : Type*} [Group G] (ñ : Fin D.rank → G) {φ : ∀ γ, D.rootGroup γ → G}
    (hñ : ∀ k, (k = i ∨ k = j) → ∀ γ ∈ pairRoots D i j, ∀ (x : D.rootGroup γ)
      (y : D.rootGroup ((Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible).refl k γ)),
      (y : K) = n k * x * (n k)⁻¹ →
        ñ k * φ γ x * (ñ k)⁻¹ =
          φ ((Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible).refl k γ) y)
    (hpos : ExtendsToHom D.rootGroup
      (pairRoots D i j ∩ (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible).pos) φ)
    (hrank : ∀ k, (k = i ∨ k = j) → ExtendsToHom D.rootGroup {Pi.single k 1, -Pi.single k 1} φ) :
    ∀ α ∈ pairRoots D i j, ∀ β ∈ pairRoots D i j, ¬ Universal.IsNegMultiple α β →
      ExtendsToHom D.rootGroup (D.cone α β ∩ pairRoots D i j) φ := by
  set Φ := Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible with hΦ
  set J : Finset (Fin D.rank) := {i, j} with hJdef
  have hJ : HasParabolicWords Φ J := hasParabolicWords_ofCartan _ _ J
  have hmemJ : ∀ k : J, (k : Fin D.rank) = i ∨ (k : Fin D.rank) = j := fun k => by
    rcases Finset.mem_insert.1 k.2 with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.1 h)
  have hiJ : i ∈ J := Finset.mem_insert_self i {j}
  have hjJ : j ∈ J := Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
  have hsuppJ : ∀ v : J → ℤ, ∀ l, l ≠ i → l ≠ j → incl J v l = 0 := fun v l hi hj =>
    incl_apply_of_notMem v (fun hl => by
      rcases Finset.mem_insert.1 hl with h | h
      · exact hi h
      · exact hj (Finset.mem_singleton.1 h))
  have hpair : ∀ γ : J → ℤ, γ ∈ (subsystem hJ).roots → incl J γ ∈ pairRoots D i j :=
    fun γ hγ => ⟨hγ, hsuppJ γ⟩
  have hreflJ : ∀ (k : J) (γ : J → ℤ),
      incl J ((subsystem hJ).refl k γ) = Φ.refl k (incl J γ) :=
    fun k γ => incl_subsystem_refl hJ k γ
  have hcc := coneCompatible_of_pos (Φ := subsystem hJ)
    (X := fun γ => D.rootGroup (incl J γ)) (fun k => n k)
    (fun k γ hγ x hx => by
      rw [hreflJ]
      exact hn k (hmemJ k) _ (hpair γ hγ) x hx)
    (fun k => ñ k) (φ := fun γ x => φ (incl J γ) x)
    (fun k γ hγ x y hy => by
      have hy' : (y : K) ∈ D.rootGroup (Φ.refl k (incl J γ)) := by
        rw [← hreflJ]
        exact y.2
      rw [hñ k (hmemJ k) _ (hpair γ hγ) x ⟨y, hy'⟩ hy]
      exact apply_eq_of_index_eq φ (hreflJ k γ).symm _ _ rfl)
    (by
      obtain ⟨S, θ, hθ⟩ := hpos
      exact ⟨S, θ, fun γ hγ x =>
        hθ (incl J γ) ⟨hpair γ hγ.1, (mem_subsystem_pos hJ).1 hγ⟩ x⟩)
    (fun k => by
      obtain ⟨S, θ, hθ⟩ := hrank k (hmemJ k)
      refine ⟨S, θ, fun γ hγ x => hθ (incl J γ) ?_ x⟩
      rcases hγ with rfl | rfl
      · exact Or.inl (incl_single k)
      · exact Or.inr (by rw [Set.mem_singleton_iff, map_neg, incl_single]))
  intro α hα β hβ hneg
  have hαs : ∀ l ∉ J, α l = 0 := fun l hl =>
    hα.2 l (fun e => hl (e ▸ hiJ)) (fun e => hl (e ▸ hjJ))
  have hβs : ∀ l ∉ J, β l = 0 := fun l hl =>
    hβ.2 l (fun e => hl (e ▸ hiJ)) (fun e => hl (e ▸ hjJ))
  have hα' : proj J α ∈ (subsystem hJ).roots := by
    change incl J (proj J α) ∈ Φ.roots
    rw [incl_proj hαs]
    exact hα.1
  have hβ' : proj J β ∈ (subsystem hJ).roots := by
    change incl J (proj J β) ∈ Φ.roots
    rw [incl_proj hβs]
    exact hβ.1
  have hneg' : ¬ Steinberg.IsNegMultiple (proj J α) (proj J β) := by
    rw [Steinberg.isNegMultiple_iff]
    rintro ⟨a, b, ha, hb, hab⟩
    refine hneg ⟨a, b, ha, hb, ?_⟩
    have := congrArg (incl J) hab
    rwa [map_nsmul, map_neg, map_nsmul, incl_proj hαs, incl_proj hβs] at this
  obtain ⟨S, θ, hθ⟩ := hcc.cone _ hα' _ hβ' hneg'
  refine ⟨S, θ, fun γ hγ x => ?_⟩
  obtain ⟨⟨hγr, a, b, hγab⟩, hγp⟩ := hγ
  have hγs : ∀ l ∉ J, γ l = 0 := fun l hl =>
    hγp.2 l (fun e => hl (e ▸ hiJ)) (fun e => hl (e ▸ hjJ))
  obtain ⟨γ', hγ', rfl⟩ : ∃ γ', γ' ∈ Steinberg.cone (subsystem hJ).roots (proj J α) (proj J β) ∧
      incl J γ' = γ := by
    refine ⟨proj J γ, ⟨?_, a, b, ?_⟩, incl_proj hγs⟩
    · change incl J (proj J γ) ∈ Φ.roots
      rw [incl_proj hγs]
      exact hγr
    · rw [hγab, map_add, map_nsmul, map_nsmul]
  exact hθ γ' hγ' x

end CFSG.Timmesfeld
