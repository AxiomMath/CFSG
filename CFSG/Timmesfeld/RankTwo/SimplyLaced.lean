module

public import CFSG.Timmesfeld.RankTwo.LeviFrame
public import CFSG.LinearAlgebra.LinearGroups.Generation

public section

namespace CFSG.Timmesfeld

open CFSG.LieType CFSG.LieType.Universal Matrix

section Elem

variable {F : Type*} [Field F]

@[expose] def tv {n : ℕ} (i j : Fin n) (c : F) : SpecialLinearGroup (Fin n) F :=
  if h : i = j then 1 else SpecialLinearGroup.transvection h c

theorem tv_of_ne {n : ℕ} {i j : Fin n} (h : i ≠ j) (c : F) :
    tv i j c = SpecialLinearGroup.transvection h c := by
  simp [tv, h]

theorem closure_tv_two : Subgroup.closure ({g | ∃ c : F, g = tv 0 1 c} ∪
    {g | ∃ c : F, g = tv 1 0 c} : Set (SpecialLinearGroup (Fin 2) F)) = ⊤ := by
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 2) (K := F),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  apply Subgroup.subset_closure
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact Or.inl ⟨c, (tv_of_ne hij c).symm⟩
  · exact Or.inr ⟨c, (tv_of_ne hij c).symm⟩
  · exact absurd rfl hij

end Elem

section Roots

variable {r : ℕ}

abbrev sroot (k : Fin r) : Fin r → ℤ := Pi.single k 1

theorem sroot_self (k : Fin r) : sroot k k = 1 := by simp [sroot]

theorem sroot_of_ne {k l : Fin r} (h : l ≠ k) : sroot k l = 0 := by simp [sroot, h]

theorem eq_of_sroot_eq_one {k l : Fin r} (h : sroot k l = 1) : l = k := by
  by_contra hlk
  rw [sroot_of_ne hlk] at h
  exact zero_ne_one h

theorem sroot_injective : Function.Injective (sroot : Fin r → Fin r → ℤ) := by
  intro k l h
  have := congrFun h k
  rw [sroot_self] at this
  exact (eq_of_sroot_eq_one this.symm)

theorem sroot_ne_neg (k l : Fin r) : sroot k ≠ -sroot l := by
  intro h
  have := congrFun h k
  rw [Pi.neg_apply, sroot_self] at this
  by_cases hkl : k = l
  · subst hkl
    rw [sroot_self] at this
    omega
  · rw [sroot_of_ne hkl] at this
    omega

theorem sroot_ne_add {i j : Fin r} (hij : i ≠ j) (k : Fin r) : sroot k ≠ sroot i + sroot j := by
  intro h
  have hi := congrFun h i
  have hj := congrFun h j
  rw [Pi.add_apply, sroot_self, sroot_of_ne hij] at hi
  rw [Pi.add_apply, sroot_self, sroot_of_ne (Ne.symm hij)] at hj
  by_cases hki : i = k
  · subst hki
    rw [sroot_of_ne (Ne.symm hij)] at hj
    omega
  · rw [sroot_of_ne hki] at hi
    omega

theorem neg_sroot_ne_add {i j : Fin r} (hij : i ≠ j) (k : Fin r) :
    -sroot k ≠ sroot i + sroot j := by
  intro h
  have hi := congrFun h i
  rw [Pi.neg_apply, Pi.add_apply, sroot_self, sroot_of_ne hij] at hi
  by_cases hki : i = k
  · subst hki
    rw [sroot_self] at hi
    omega
  · rw [sroot_of_ne hki] at hi
    omega

theorem sroot_ne_neg_add {i j : Fin r} (hij : i ≠ j) (k : Fin r) :
    sroot k ≠ -(sroot i + sroot j) := by
  intro h
  have hk := congrFun h k
  rw [Pi.neg_apply, Pi.add_apply, sroot_self] at hk
  have h1 : 0 ≤ sroot i k := by
    by_cases hki : k = i
    · subst hki; rw [sroot_self]; omega
    · rw [sroot_of_ne hki]
  have h2 : 0 ≤ sroot j k := by
    by_cases hkj : k = j
    · subst hkj; rw [sroot_self]; omega
    · rw [sroot_of_ne hkj]
  omega

theorem neg_sroot_ne_neg_add {i j : Fin r} (hij : i ≠ j) (k : Fin r) :
    -sroot k ≠ -(sroot i + sroot j) := fun h => sroot_ne_add hij k (neg_injective h)

theorem add_ne_neg_add {i j : Fin r} (hij : i ≠ j) (i' j' : Fin r) :
    sroot i + sroot j ≠ -(sroot i' + sroot j') := by
  intro h
  have hi := congrFun h i
  rw [Pi.neg_apply, Pi.add_apply, Pi.add_apply, sroot_self, sroot_of_ne hij] at hi
  have h1 : 0 ≤ sroot i' i := by
    by_cases hki : i = i'
    · subst hki; rw [sroot_self]; omega
    · rw [sroot_of_ne hki]
  have h2 : 0 ≤ sroot j' i := by
    by_cases hkj : i = j'
    · subst hkj; rw [sroot_self]; omega
    · rw [sroot_of_ne hkj]
  omega

theorem eq_of_add_eq_add {i j i' j' : Fin r} (hij : i ≠ j)
    (h : sroot i + sroot j = sroot i' + sroot j') :
    (i' = i ∧ j' = j) ∨ (i' = j ∧ j' = i) := by
  have hi := congrFun h i
  have hj := congrFun h j
  rw [Pi.add_apply, Pi.add_apply, sroot_self, sroot_of_ne hij] at hi
  rw [Pi.add_apply, Pi.add_apply, sroot_self, sroot_of_ne (Ne.symm hij)] at hj
  by_cases h1 : i' = i
  · subst h1
    rw [sroot_of_ne (Ne.symm hij)] at hj
    exact Or.inl ⟨rfl, (eq_of_sroot_eq_one (by omega)).symm⟩
  · rw [sroot_of_ne (Ne.symm h1)] at hi
    have hj' : j' = i := (eq_of_sroot_eq_one (by omega)).symm
    subst hj'
    rw [sroot_of_ne (Ne.symm hij)] at hj
    exact Or.inr ⟨(eq_of_sroot_eq_one (by omega)).symm, rfl⟩

end Roots

variable {K : Type} [Group K] (D : UniversalRootDatum K) (F : Type) [Field F]

structure SimplyLacedLevis (adj : Fin D.rank → Fin D.rank → Prop)
    (x : (Fin D.rank → ℤ) → F → K) : Prop where
  asymm : ∀ i j, adj i j → ¬ adj j i
  ne : ∀ i j, adj i j → i ≠ j
  mem : ∀ γ ∈ D.roots, ∀ c, x γ c ∈ D.rootGroup γ
  surj : ∀ γ ∈ D.roots, ∀ g ∈ D.rootGroup γ, ∃ c, x γ c = g
  pairRoots_adj : ∀ i j, adj i j → pairRoots D i j ⊆
    {sroot i, -sroot i, sroot j, -sroot j, sroot i + sroot j, -(sroot i + sroot j)}
  pairRoots_nonadj : ∀ i j, ¬ adj i j → ¬ adj j i →
    pairRoots D i j ⊆ {sroot i, -sroot i, sroot j, -sroot j}
  sl3 : ∀ i j, adj i j → ∃ l : SpecialLinearGroup (Fin 3) F →* K, Function.Injective l ∧
    ∀ c, l (tv 0 1 c) = x (sroot i) c ∧ l (tv 1 0 c) = x (-sroot i) c ∧
      l (tv 1 2 c) = x (sroot j) c ∧ l (tv 2 1 c) = x (-sroot j) c ∧
      l (tv 0 2 c) = x (sroot i + sroot j) c ∧ l (tv 2 0 c) = x (-(sroot i + sroot j)) c
  sl2 : ∀ k, ∃ l : SpecialLinearGroup (Fin 2) F →* K, Function.Injective l ∧
    ∀ c, l (tv 0 1 c) = x (sroot k) c ∧ l (tv 1 0 c) = x (-sroot k) c
  sl2sl2 : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i →
    ∃ l : SpecialLinearGroup (Fin 2) F × SpecialLinearGroup (Fin 2) F →* K,
      Function.Injective l ∧ ∀ c, l (tv 0 1 c, 1) = x (sroot i) c ∧
        l (tv 1 0 c, 1) = x (-sroot i) c ∧ l (1, tv 0 1 c) = x (sroot j) c ∧
        l (1, tv 1 0 c) = x (-sroot j) c

structure SimplyLacedFrame (adj : Fin D.rank → Fin D.rank → Prop) {H : Type*} [Group H]
    (u v : Fin D.rank → F → H) : Prop where
  sl3 : ∀ i j, adj i j → ∃ φ : SpecialLinearGroup (Fin 3) F →* H, ∀ c,
    φ (tv 0 1 c) = u i c ∧ φ (tv 1 0 c) = v i c ∧ φ (tv 1 2 c) = u j c ∧ φ (tv 2 1 c) = v j c
  sl2 : ∀ k, ∃ ρ : SpecialLinearGroup (Fin 2) F →* H, ∀ c, ρ (tv 0 1 c) = u k c ∧
    ρ (tv 1 0 c) = v k c
  commute : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ c d, Commute (u i c) (u j d) ∧
    Commute (u i c) (v j d) ∧ Commute (v i c) (u j d) ∧ Commute (v i c) (v j d)

section Recognition

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

variable {D F}

theorem extendsToHom_of_injective {M H : Type*} [Group M] [Group H] {l : M →* K}
    (hl : Function.Injective l) (φ : M →* H) {Ψ : Set (Fin D.rank → ℤ)}
    {ψ : ∀ γ, D.rootGroup γ → H}
    (h : ∀ γ ∈ Ψ, ∀ g : D.rootGroup γ, ∃ a, l a = g ∧ ψ γ g = φ a) :
    ExtendsToHom D.rootGroup Ψ ψ := by
  refine ⟨l.range, φ.comp (MonoidHom.ofInjective hl).symm.toMonoidHom, fun γ hγ g => ?_⟩
  obtain ⟨a, hag, hψ⟩ := h γ hγ g
  refine ⟨⟨a, hag⟩, ?_⟩
  have he : (⟨(g : K), ⟨a, hag⟩⟩ : l.range) = MonoidHom.ofInjective hl a :=
    Subtype.ext hag.symm
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, he, MulEquiv.symm_apply_apply, hψ]

theorem commute_of_tv {H : Type*} [Group H] (ρ ρ' : SpecialLinearGroup (Fin 2) F →* H)
    (h : ∀ c d : F, Commute (ρ (tv 0 1 c)) (ρ' (tv 0 1 d)) ∧
      Commute (ρ (tv 0 1 c)) (ρ' (tv 1 0 d)) ∧ Commute (ρ (tv 1 0 c)) (ρ' (tv 0 1 d)) ∧
      Commute (ρ (tv 1 0 c)) (ρ' (tv 1 0 d)))
    (a b : SpecialLinearGroup (Fin 2) F) : Commute (ρ a) (ρ' b) := by
  have hgen := closure_tv_two (F := F)
  set S : Set (SpecialLinearGroup (Fin 2) F) :=
    {g | ∃ c : F, g = tv 0 1 c} ∪ {g | ∃ c : F, g = tv 1 0 c} with hS
  have hmem : ∀ g : SpecialLinearGroup (Fin 2) F, g ∈ Subgroup.closure S := fun g => by
    rw [hgen]; trivial
  have hb : ∀ s ∈ S, ∀ b, Commute (ρ s) (ρ' b) := by
    intro s hs b
    induction hmem b using Subgroup.closure_induction with
    | mem y hy =>
      rcases hs with ⟨c, rfl⟩ | ⟨c, rfl⟩ <;> rcases hy with ⟨d, rfl⟩ | ⟨d, rfl⟩
      exacts [(h c d).1, (h c d).2.1, (h c d).2.2.1, (h c d).2.2.2]
    | one => rw [map_one]; exact Commute.one_right _
    | mul y z _ _ hy hz => rw [map_mul]; exact hy.mul_right hz
    | inv y _ hy => rw [map_inv]; exact hy.inv_right
  induction hmem a using Subgroup.closure_induction with
  | mem y hy => exact hb y hy b
  | one => rw [map_one]; exact Commute.one_left _
  | mul y z _ _ hy hz => rw [map_mul]; exact hy.mul_left hz
  | inv y _ hy => rw [map_inv]; exact hy.inv_left

theorem pairRoots_comm (i j : Fin D.rank) : pairRoots D i j = pairRoots D j i := by
  ext γ
  exact ⟨fun h => ⟨h.1, fun k hj hi => h.2 k hi hj⟩, fun h => ⟨h.1, fun k hi hj => h.2 k hj hi⟩⟩

theorem exists_surjective_of_simplyLacedFrame {adj : Fin D.rank → Fin D.rank → Prop}
    {x : (Fin D.rank → ℤ) → F → K} {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hD : SimplyLacedLevis D F adj x) {H : Type} [Group H]
    {u v : Fin D.rank → F → H} (hfr : SimplyLacedFrame D F adj u v)
    (hgen : Subgroup.closure (⋃ k, Set.range (u k) ∪ Set.range (v k)) = ⊤)
    (hnt : ∃ k c, u k c ≠ 1) :
    ∃ Ψ : K →* H, (∀ k c, Ψ (x (sroot k) c) = u k c) ∧ (∀ k c, Ψ (x (-sroot k) c) = v k c) ∧
      Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center K ∧ IsQuasisimple H ∧
      Subgroup.center H = (Subgroup.center K).map Ψ ∧
      LieModel (H ⧸ Subgroup.center H) t n p f := by
  classical
  choose l3 hl3inj hl3 using hD.sl3
  choose l2 hl2inj hl2 using hD.sl2
  choose l22 hl22inj hl22 using hD.sl2sl2
  choose φ3 hφ3 using hfr.sl3
  choose ρ hρ using hfr.sl2
  let ψ : ∀ γ, D.rootGroup γ → H := fun γ g =>
    if h1 : ∃ k, γ = sroot k ∨ γ = -sroot k then
      ρ (Classical.choose h1) (Function.invFun (l2 (Classical.choose h1)) (g : K))
    else if h2 : ∃ q : Fin D.rank × Fin D.rank, adj q.1 q.2 ∧
        (γ = sroot q.1 + sroot q.2 ∨ γ = -(sroot q.1 + sroot q.2)) then
      φ3 _ _ (Classical.choose_spec h2).1
        (Function.invFun (l3 _ _ (Classical.choose_spec h2).1) (g : K))
    else 1
  have hψk : ∀ k γ, (γ = sroot k ∨ γ = -sroot k) → ∀ g : D.rootGroup γ,
      ψ γ g = ρ k (Function.invFun (l2 k) (g : K)) := by
    intro k γ hγ g
    have h1 : ∃ k', γ = sroot k' ∨ γ = -sroot k' := ⟨k, hγ⟩
    have hk : Classical.choose h1 = k := by
      rcases hγ with rfl | rfl <;> rcases Classical.choose_spec h1 with h | h
      · exact (sroot_injective h).symm
      · exact absurd h (sroot_ne_neg _ _)
      · exact absurd h.symm (sroot_ne_neg _ _)
      · exact (sroot_injective (neg_injective h)).symm
    show (if h1 : ∃ k, γ = sroot k ∨ γ = -sroot k then
      ρ (Classical.choose h1) (Function.invFun (l2 (Classical.choose h1)) (g : K)) else _) = _
    rw [dite_eq_left_of_eq_true (eq_true h1), hk]
  have hψe : ∀ i j (hij : adj i j) γ, (γ = sroot i + sroot j ∨ γ = -(sroot i + sroot j)) →
      ∀ g : D.rootGroup γ, ψ γ g = φ3 i j hij (Function.invFun (l3 i j hij) (g : K)) := by
    intro i j hij γ hγ g
    have hne := hD.ne i j hij
    have h1 : ¬ ∃ k, γ = sroot k ∨ γ = -sroot k := by
      rintro ⟨k, hk | hk⟩ <;> rcases hγ with hγ | hγ <;> rw [hγ] at hk
      · exact sroot_ne_add hne k hk.symm
      · exact sroot_ne_neg_add hne k hk.symm
      · exact neg_sroot_ne_add hne k hk.symm
      · exact neg_sroot_ne_neg_add hne k hk.symm
    have h2 : ∃ q : Fin D.rank × Fin D.rank, adj q.1 q.2 ∧
        (γ = sroot q.1 + sroot q.2 ∨ γ = -(sroot q.1 + sroot q.2)) := ⟨(i, j), hij, hγ⟩
    have key : ∀ (q : Fin D.rank × Fin D.rank) (hq : adj q.1 q.2),
        (γ = sroot q.1 + sroot q.2 ∨ γ = -(sroot q.1 + sroot q.2)) →
        φ3 q.1 q.2 hq (Function.invFun (l3 q.1 q.2 hq) (g : K)) =
          φ3 i j hij (Function.invFun (l3 i j hij) (g : K)) := by
      rintro ⟨i', j'⟩ hq hq'
      have hsum : sroot i + sroot j = sroot i' + sroot j' := by
        rcases hγ with hγ | hγ <;> rcases hq' with hq' | hq'
        · exact hγ.symm.trans hq'
        · exact absurd (hγ.symm.trans hq') (add_ne_neg_add hne _ _)
        · exact absurd (hq'.symm.trans hγ) (add_ne_neg_add (hD.ne _ _ hq) _ _)
        · exact neg_injective (hγ.symm.trans hq')
      rcases eq_of_add_eq_add hne hsum with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact absurd hij (hD.asymm _ _ hq)
    show (if h1 : ∃ k, γ = sroot k ∨ γ = -sroot k then _ else
      if h2 : ∃ q : Fin D.rank × Fin D.rank, adj q.1 q.2 ∧
        (γ = sroot q.1 + sroot q.2 ∨ γ = -(sroot q.1 + sroot q.2)) then
      φ3 _ _ (Classical.choose_spec h2).1
        (Function.invFun (l3 _ _ (Classical.choose_spec h2).1) (g : K)) else 1) = _
    rw [dite_eq_right_of_eq_false (eq_false h1), dite_eq_left_of_eq_true (eq_true h2)]
    exact key _ _ (Classical.choose_spec h2).2
  have hroot : ∀ i j, ∀ γ ∈ pairRoots D i j, γ ∈ D.roots := fun _ _ _ hγ => hγ.1
  have hsr : ∀ k, sroot k ∈ D.roots ∧ -sroot k ∈ D.roots := fun k =>
    ⟨(Levi.single_mem_pairRoots (D := D) (i := k) (j := k) (Or.inl rfl)).1.1,
      (Levi.single_mem_pairRoots (D := D) (i := k) (j := k) (Or.inl rfl)).2.1⟩
  have hψu : ∀ k c, ψ (sroot k) ⟨x (sroot k) c, hD.mem _ (hsr k).1 c⟩ = u k c := by
    intro k c
    rw [hψk k _ (Or.inl rfl)]
    simp only
    rw [← (hl2 k c).1, Function.leftInverse_invFun (hl2inj k), (hρ k c).1]
  have hψv : ∀ k c, ψ (-sroot k) ⟨x (-sroot k) c, hD.mem _ (hsr k).2 c⟩ = v k c := by
    intro k c
    rw [hψk k _ (Or.inr rfl)]
    simp only
    rw [← (hl2 k c).2, Function.leftInverse_invFun (hl2inj k), (hρ k c).2]
  have hedge : ∀ i j (hij : adj i j), ExtendsToHom D.rootGroup (pairRoots D i j) ψ := by
    intro i j hij
    refine extendsToHom_of_injective (hl3inj i j hij) (φ3 i j hij) fun γ hγ g => ?_
    obtain ⟨c, hc⟩ := hD.surj γ (hroot i j γ hγ) g g.2
    have hsub := hD.pairRoots_adj i j hij hγ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
    obtain ⟨h01, h10, h12, h21, h02, h20⟩ := hl3 i j hij c
    rcases hsub with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨tv 0 1 c, h01.trans hc, ?_⟩
      rw [hψk i _ (Or.inl rfl), ← hc, ← (hl2 i c).1, Function.leftInverse_invFun (hl2inj i),
        (hρ i c).1, (hφ3 i j hij c).1]
    · refine ⟨tv 1 0 c, h10.trans hc, ?_⟩
      rw [hψk i _ (Or.inr rfl), ← hc, ← (hl2 i c).2, Function.leftInverse_invFun (hl2inj i),
        (hρ i c).2, (hφ3 i j hij c).2.1]
    · refine ⟨tv 1 2 c, h12.trans hc, ?_⟩
      rw [hψk j _ (Or.inl rfl), ← hc, ← (hl2 j c).1, Function.leftInverse_invFun (hl2inj j),
        (hρ j c).1, (hφ3 i j hij c).2.2.1]
    · refine ⟨tv 2 1 c, h21.trans hc, ?_⟩
      rw [hψk j _ (Or.inr rfl), ← hc, ← (hl2 j c).2, Function.leftInverse_invFun (hl2inj j),
        (hρ j c).2, (hφ3 i j hij c).2.2.2]
    · refine ⟨tv 0 2 c, h02.trans hc, ?_⟩
      rw [hψe i j hij _ (Or.inl rfl), ← hc, ← h02, Function.leftInverse_invFun (hl3inj i j hij)]
    · refine ⟨tv 2 0 c, h20.trans hc, ?_⟩
      rw [hψe i j hij _ (Or.inr rfl), ← hc, ← h20, Function.leftInverse_invFun (hl3inj i j hij)]
  have hnon : ∀ i j (hne : i ≠ j) (hij : ¬ adj i j) (hji : ¬ adj j i),
      ExtendsToHom D.rootGroup (pairRoots D i j) ψ := by
    intro i j hne hij hji
    have hcomm : ∀ a b, Commute (ρ i a) (ρ j b) := commute_of_tv (ρ i) (ρ j) fun c d => by
      rw [(hρ i c).1, (hρ i c).2, (hρ j d).1, (hρ j d).2]
      exact hfr.commute i j hne hij hji c d
    refine extendsToHom_of_injective (hl22inj i j hne hij hji)
      ((ρ i).noncommCoprod (ρ j) hcomm) fun γ hγ g => ?_
    obtain ⟨c, hc⟩ := hD.surj γ (hroot i j γ hγ) g g.2
    have hsub := hD.pairRoots_nonadj i j hij hji hγ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
    obtain ⟨h1, h2, h3, h4⟩ := hl22 i j hne hij hji c
    rcases hsub with rfl | rfl | rfl | rfl
    · refine ⟨(tv 0 1 c, 1), h1.trans hc, ?_⟩
      rw [hψk i _ (Or.inl rfl), ← hc, ← (hl2 i c).1, Function.leftInverse_invFun (hl2inj i),
        MonoidHom.noncommCoprod_apply, map_one, mul_one]
    · refine ⟨(tv 1 0 c, 1), h2.trans hc, ?_⟩
      rw [hψk i _ (Or.inr rfl), ← hc, ← (hl2 i c).2, Function.leftInverse_invFun (hl2inj i),
        MonoidHom.noncommCoprod_apply, map_one, mul_one]
    · refine ⟨(1, tv 0 1 c), h3.trans hc, ?_⟩
      rw [hψk j _ (Or.inl rfl), ← hc, ← (hl2 j c).1, Function.leftInverse_invFun (hl2inj j),
        MonoidHom.noncommCoprod_apply, map_one, one_mul]
    · refine ⟨(1, tv 1 0 c), h4.trans hc, ?_⟩
      rw [hψk j _ (Or.inr rfl), ← hc, ← (hl2 j c).2, Function.leftInverse_invFun (hl2inj j),
        MonoidHom.noncommCoprod_apply, map_one, one_mul]
  have hdiag : ∀ k, ExtendsToHom D.rootGroup (pairRoots D k k) ψ := by
    intro k
    have hkk : ¬ adj k k := fun h => hD.ne k k h rfl
    refine extendsToHom_of_injective (hl2inj k) (ρ k) fun γ hγ g => ?_
    obtain ⟨c, hc⟩ := hD.surj γ (hroot k k γ hγ) g g.2
    have hsub := hD.pairRoots_nonadj k k hkk hkk hγ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsub
    have hsub' : γ = sroot k ∨ γ = -sroot k := by
      rcases hsub with h | h | h | h <;> simp [h]
    rcases hsub' with rfl | rfl
    · refine ⟨tv 0 1 c, (hl2 k c).1.trans hc, ?_⟩
      rw [hψk k _ (Or.inl rfl), ← hc, ← (hl2 k c).1, Function.leftInverse_invFun (hl2inj k)]
    · refine ⟨tv 1 0 c, (hl2 k c).2.trans hc, ?_⟩
      rw [hψk k _ (Or.inr rfl), ← hc, ← (hl2 k c).2, Function.leftInverse_invFun (hl2inj k)]
  have hpair : ∀ i j, ExtendsToHom D.rootGroup (pairRoots D i j) ψ := by
    intro i j
    by_cases hij : adj i j
    · exact hedge i j hij
    by_cases hji : adj j i
    · rw [pairRoots_comm]; exact hedge j i hji
    by_cases hne : i = j
    · subst hne; exact hdiag i
    exact hnon i j hne hij hji
  have hrange_u : ∀ k, Set.range (ψ (sroot k)) = Set.range (u k) := by
    intro k
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨c, hc⟩ := hD.surj _ (hsr k).1 g g.2
      have hg : g = ⟨x (sroot k) c, hD.mem _ (hsr k).1 c⟩ := Subtype.ext hc.symm
      exact ⟨c, by rw [hg, hψu]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨_, hψu k c⟩
  have hrange_v : ∀ k, Set.range (ψ (-sroot k)) = Set.range (v k) := by
    intro k
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨c, hc⟩ := hD.surj _ (hsr k).2 g g.2
      have hg : g = ⟨x (-sroot k) c, hD.mem _ (hsr k).2 c⟩ := Subtype.ext hc.symm
      exact ⟨c, by rw [hg, hψv]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨_, hψv k c⟩
  obtain ⟨Ψ, hΨu, hΨv, hsurj, hker, hqs, hcent, hmodel⟩ :=
    exists_surjective_of_frame hCT hL ψ (fun i j α _ β _ _ => (hpair i j).mono
      Set.inter_subset_right) (fun k => (hdiag k).mono fun γ hγ => by
        rcases hγ with rfl | rfl
        exacts [(Levi.single_mem_pairRoots (Or.inl rfl)).1,
          (Levi.single_mem_pairRoots (Or.inl rfl)).2])
      (by simp_rw [hrange_u, hrange_v]; exact hgen)
      (by obtain ⟨k, c, hkc⟩ := hnt
          exact ⟨k, ⟨x (sroot k) c, hD.mem _ (hsr k).1 c⟩, by rw [hψu]; exact hkc⟩)
  refine ⟨Ψ, fun k c => ?_, fun k c => ?_, hsurj, hker, hqs, hcent, hmodel⟩
  · rw [← hψu k c]
    exact hΨu k ⟨x (sroot k) c, hD.mem _ (hsr k).1 c⟩
  · rw [← hψv k c]
    exact hΨv k ⟨x (-sroot k) c, hD.mem _ (hsr k).2 c⟩

theorem lieModel_of_simplyLacedFrame {adj : Fin D.rank → Fin D.rank → Prop}
    {x : (Fin D.rank → ℤ) → F → K} {t : StatedLieTag} {n p f : ℕ}
    (hCT : CurtisTits.CurtisTitsConclusion.{0} D t n p f) (hL : LeviConePresented D)
    (hD : SimplyLacedLevis D F adj x) {H : Type} [Group H] (hZ : Subgroup.center H = ⊥)
    {u v : Fin D.rank → F → H} (hfr : SimplyLacedFrame D F adj u v)
    (hgen : Subgroup.closure (⋃ k, Set.range (u k) ∪ Set.range (v k)) = ⊤)
    (hnt : ∃ k c, u k c ≠ 1) : LieModel H t n p f := by
  obtain ⟨-, -, -, -, -, -, -, hmodel⟩ :=
    exists_surjective_of_simplyLacedFrame hCT hL hD hfr hgen hnt
  exact lieModel_of_center_eq_bot hZ hmodel

end Recognition

end CFSG.Timmesfeld
