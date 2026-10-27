module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7.FinalAux3

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35

section Concl

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

structure Concl71 (p : ℕ) (A : Subgroup G) (θ : G → Subgroup G) (E B : Subgroup G)
    (W : Fin p → Subgroup G) : Prop where
  inj : Function.Injective W
  dp : IsDirectProduct (Set.range W) (wsub p A θ)
  perm : ∀ a ∈ A, ∀ i, ∃ j, cj a (W i) = W j
  trans : ∀ i j, ∃ a ∈ A, cj a (W i) = W j
  stab : ∀ i, A ⊓ Subgroup.normalizer (W i : Set G) = B
  comp : ∀ b ∈ B, b ∉ E →
    IsDirectProduct (Set.range fun i => W i ⊓ kOf (θ b)) (kOf (θ b))

variable {E B : Subgroup G} {W : Fin p → Subgroup G}

theorem sup_zpowers_eq_of_not_mem (hp : p.Prime) (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 3)
    (hB : B ∈ signalizerFunctorEk p 2 A) {f : G} (hfA : f ∈ A) (hfB : f ∉ B) :
    B ⊔ Subgroup.zpowers f = A ∧ B ⊓ Subgroup.zpowers f = ⊥ := by
  have hf1 : f ≠ 1 := fun h => hfB (h ▸ one_mem B)
  have hcard : Nat.card (Subgroup.zpowers f) = p :=
    Sec6Gen.card_zpowers_of_pow_eq_one hp (hA.2 f hfA) hf1
  have hdisj : B ⊓ Subgroup.zpowers f = ⊥ :=
    CFSG.SignalizerFunctorTheorem.inf_eq_bot_of_not_le hp hcard
      (fun hle => hfB (hle (Subgroup.mem_zpowers f)))
  refine ⟨?_, hdisj⟩
  have hsub : B ⊔ Subgroup.zpowers f ≤ A := sup_le hB.1 (Subgroup.zpowers_le.mpr hfA)
  refine Subgroup.eq_of_le_of_card_ge hsub ?_
  rw [CFSG.SignalizerFunctorTheorem.card_sup_of_le_elemAbelian hA hB.1
    (Subgroup.zpowers_le.mpr hfA) hdisj, hB.2, hcard, hAc]
  ring_nf
  exact le_rfl

theorem Concl71.exists_mem_zpowers (hC : Concl71 p A θ E B W) (hp : p.Prime)
    (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 3) (hB : B ∈ signalizerFunctorEk p 2 A)
    {f : G} (hfA : f ∈ A) (hfB : f ∉ B) (i j : Fin p) :
    ∃ c ∈ Subgroup.zpowers f, cj c (W i) = W j := by
  obtain ⟨hsup, -⟩ := sup_zpowers_eq_of_not_mem hp hA hAc hB hfA hfB
  obtain ⟨a, ha, hij⟩ := hC.trans i j
  have haA : a ∈ B ⊔ Subgroup.zpowers f := hsup ▸ ha
  have hcomm : ∀ x ∈ B, ∀ y ∈ Subgroup.zpowers f, Commute x y := fun x hx y hy =>
    commute_of_mem hA.1 (hB.1 hx) ((Subgroup.zpowers_le.mpr hfA) hy)
  obtain ⟨β, hβ, c, hc, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp haA
  obtain ⟨j', hj'⟩ := hC.perm c ((Subgroup.zpowers_le.mpr hfA) hc) i
  have hβ' : β ∈ A ⊓ Subgroup.normalizer (W j' : Set G) := by
    rw [hC.stab j']
    exact hβ
  have h1 : cj β (W j') = W j' := cj_eq_of_mem_normalizer hβ'.2
  rw [← cj_cj, hj', h1] at hij
  exact ⟨c, hc, hj'.trans hij⟩

omit [Finite G] in
theorem Concl71.cj_inf_eq {X : Subgroup G} (hXA : Admits A X) {a : G}
    (ha : a ∈ A) {i j : Fin p} (hij : cj a (W i) = W j) : cj a (W i ⊓ X) = W j ⊓ X := by
  rw [cj_inf, hij, cj_eq_of_mem_normalizer (hXA ha)]

theorem Concl71.projIn_eq (hC : Concl71 p A θ E B W) (hp : p.Prime)
    {X : Subgroup G} (hXA : Admits A X)
    (hQ : IsDirectProduct (Set.range fun i => W i ⊓ X) X) (hQne : ∀ i, W i ⊓ X ≠ ⊥)
    {f : G} (hfA : f ∈ A) (hfp : f ^ p = 1) (hfB : f ∉ B) (i₀ : Fin p) :
    projIn (Set.range fun i => W i ⊓ X) (W i₀ ⊓ X)
        (X ⊓ Subgroup.centralizer (Subgroup.zpowers f : Set G)) = W i₀ ⊓ X := by
  have hzA : Subgroup.zpowers f ≤ A := Subgroup.zpowers_le.mpr hfA
  have hA' : ∀ a ∈ Subgroup.zpowers f, ∀ J ∈ Set.range (fun i => W i ⊓ X),
      J.map (MulAut.conj a).toMonoidHom ∈ Set.range (fun i => W i ⊓ X) := by
    rintro a ha _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hC.perm a (hzA ha) i
    exact ⟨j, (Concl71.cj_inf_eq hXA (hzA ha) hj).symm⟩
  have hproj := CFSG.SignalizerFunctorTheorem.McBride.projIn_centralizer_eq hQ hA'
    (⟨i₀, rfl⟩ : W i₀ ⊓ X ∈ Set.range fun i => W i ⊓ X)
  have hinf : Subgroup.zpowers f ⊓ Subgroup.normalizer ((W i₀ ⊓ X : Subgroup G) : Set G) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun a ha => ?_
    obtain ⟨haz, haN⟩ := Subgroup.mem_inf.mp ha
    obtain ⟨j, hj⟩ := hC.perm a (hzA haz) i₀
    have hQj := Concl71.cj_inf_eq hXA (hzA haz) hj
    rw [cj_eq_of_mem_normalizer haN] at hQj
    have hji : j = i₀ := by
      by_contra hne
      apply hQne i₀
      have hdisj : W i₀ ⊓ W j = ⊥ := by
        have := hC.dp.indep.pairwiseDisjoint (x := W i₀) ⟨i₀, rfl⟩ (y := W j) ⟨j, rfl⟩
          (fun e => hne (hC.inj e).symm)
        exact disjoint_iff.mp this
      rw [eq_bot_iff, ← hdisj]
      exact le_inf inf_le_left (hQj ▸ inf_le_left)
    subst hji
    have haB : a ∈ B := by
      have : a ∈ A ⊓ Subgroup.normalizer (W j : Set G) :=
        ⟨hzA haz, Subgroup.mem_normalizer_iff_map_conj_eq.mpr hj⟩
      rwa [hC.stab j] at this
    have hfne : f ≠ 1 := fun h1 => hfB (h1 ▸ one_mem B)
    have hdisj := CFSG.SignalizerFunctorTheorem.inf_eq_bot_of_not_le hp (E := B)
      (R := Subgroup.zpowers f) (Sec6Gen.card_zpowers_of_pow_eq_one hp hfp hfne)
      (fun hle => hfB (hle (Subgroup.mem_zpowers f)))
    have : a ∈ B ⊓ Subgroup.zpowers f := ⟨haB, haz⟩
    rw [hdisj] at this
    exact this
  rw [hinf] at hproj
  rw [hproj]
  refine le_antisymm inf_le_left (le_inf le_rfl fun x hx => ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [SetLike.mem_coe, Subgroup.mem_bot] at hy
  rw [hy, one_mul, mul_one]

omit [Finite G] in
theorem Concl71.map_mem_range (hC : Concl71 p A θ E B W) {X : Subgroup G} (hXA : Admits A X)
    {a : G} (ha : a ∈ A) {J : Subgroup G} (hJ : J ∈ Set.range fun i => W i ⊓ X) :
    cj a J ∈ Set.range fun i => W i ⊓ X := by
  obtain ⟨i, rfl⟩ := hJ
  obtain ⟨j, hj⟩ := hC.perm a ha i
  exact ⟨j, (Concl71.cj_inf_eq hXA ha hj).symm⟩

theorem Concl71.isPerfect_cen (hC : Concl71 p A θ E B W) (hp : p.Prime)
    (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 3) (hB : B ∈ signalizerFunctorEk p 2 A)
    {X : Subgroup G} (hXA : Admits A X)
    (hQ : IsDirectProduct (Set.range fun i => W i ⊓ X) X) (hQne : ∀ i, W i ⊓ X ≠ ⊥)
    {f : G} (hfA : f ∈ A) (hfp : f ^ p = 1) (hfB : f ∉ B) (hX : Group.IsPerfect ↥X) :
    Group.IsPerfect ↥(X ⊓ Subgroup.centralizer ({f} : Set G)) := by
  have hzA : Subgroup.zpowers f ≤ A := Subgroup.zpowers_le.mpr hfA
  set i₀ : Fin p := ⟨0, hp.pos⟩ with hi₀
  set S : Set (Subgroup G) := Set.range fun i => W i ⊓ X with hS
  have hJ : W i₀ ⊓ X ∈ S := ⟨i₀, rfl⟩
  have hA' : ∀ a ∈ Subgroup.zpowers f, ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S :=
    fun a ha J hJ' => hC.map_mem_range hXA (hzA ha) hJ'
  have htrans : ∀ K' ∈ S, ∃ a ∈ Subgroup.zpowers f,
      K' = (W i₀ ⊓ X).map (MulAut.conj a).toMonoidHom := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨c, hc, hcj⟩ := hC.exists_mem_zpowers hp hA hAc hB hfA hfB i₀ j
    exact ⟨c, hc, (Concl71.cj_inf_eq hXA (hzA hc) hcj).symm⟩
  have hcen : Subgroup.centralizer (Subgroup.zpowers f : Set G) =
      Subgroup.centralizer ({f} : Set G) := centralizer_zpowers_eq_singleton f
  have hproj := hC.projIn_eq hp hXA hQ hQne hfA hfp hfB i₀
  rw [hcen] at hproj
  let φ : ↥X →* ↥(W i₀ ⊓ X) := hQ.coord hJ
  have hφs : Function.Surjective φ := fun x => ⟨⟨x, (Subgroup.mem_inf.mp x.2).2⟩, Subtype.ext
    (hQ.coord_of_mem hJ x.2)⟩
  have : Group.IsPerfect ↥(W i₀ ⊓ X) := Group.IsPerfect.ofSurjective hφs
  let ψ : ↥(X ⊓ Subgroup.centralizer ({f} : Set G)) →* ↥(W i₀ ⊓ X) :=
    φ.comp (Subgroup.inclusion inf_le_left)
  have hψi : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    have hyX : (y : G) ∈ X := (Subgroup.mem_inf.mp y.2).1
    have hyC : (y : G) ∈ Subgroup.centralizer ({f} : Set G) := (Subgroup.mem_inf.mp y.2).2
    have hy1 : φ ⟨y, hyX⟩ = 1 := hy
    have hys : (y : G) ∈ sSup (S \ {W i₀ ⊓ X}) := (hQ.coord_eq_one_iff hJ _).mp hy1
    have hbot := inf_centralizer_inf_sSup_eq_bot_of_transitive hQ hA' hJ htrans
    have : (y : G) ∈ X ⊓ Subgroup.centralizer (Subgroup.zpowers f : Set G) ⊓
        sSup (S \ {W i₀ ⊓ X}) := ⟨⟨hyX, by rw [hcen]; exact hyC⟩, hys⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp this))
  have hψs : Function.Surjective ψ := by
    intro x
    have hx : (x : G) ∈ projIn S (W i₀ ⊓ X) (X ⊓ Subgroup.centralizer ({f} : Set G)) := by
      rw [hproj]; exact x.2
    obtain ⟨y, hyK, hyx⟩ := (hQ.mem_projIn_iff hJ).mp hx
    exact ⟨⟨y, hyK⟩, Subtype.ext hyx⟩
  let e := MulEquiv.ofBijective ψ ⟨hψi, hψs⟩
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

end Concl

section Key

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {E B : Subgroup G} {W : Fin p → Subgroup G}

theorem Data.wsub_eq_sup
    {h : Counterexample p A θ} {E B₂ : Subgroup G} (D : Data h E)
    (hS₂ : Setting p A E B₂) {f₁ f₂ : G} (hf₁A : f₁ ∈ A) (hf₁E : f₁ ∉ E) (hf₂ : f₂ ∈ B₂)
    (hf₂E : f₂ ∉ E) (hf₁B₂ : f₁ ∉ B₂) : wsub p A θ = kOf (θ f₁) ⊔ kOf (θ f₂) := by
  have hθ := h.hyp.nearFunctor
  have hf₂A := hS₂.mem_A hf₂
  have hmem1 := kOf_mem_assoc hθ hf₁A (ne_one_of_not_mem hf₁E)
  have hmem2 := kOf_mem_assoc hθ hf₂A (ne_one_of_not_mem hf₂E)
  have hsub : ({kOf (θ f₁), kOf (θ f₂)} : Set (Subgroup G)) ⊆ assoc p A θ := by
    rintro _ (rfl | rfl)
    · exact hmem1
    · exact hmem2
  rcases h.sSup_mem_assoc_or_le hsub with hle | hmem
  · rw [sSup_pair] at hle
    refine le_antisymm (sSup_le hle) (sup_le (le_sSup hmem1) (le_sSup hmem2))
  · exfalso
    rw [sSup_pair] at hmem
    have h1 : kOf (θ f₁) ⊔ kOf (θ f₂) ≤ θ f₁ :=
      D.le_of_mem f₁ hf₁A hf₁E _ hmem le_sup_left
    obtain ⟨L, hL⟩ := D.lcal_nonempty hf₂A hf₂E
    have hLK : L ≤ kOf (θ f₂) := ((D.isDirectProduct_lcal hf₂A hf₂E).le hL)
    have hcomm : ∀ x ∈ L, Commute f₁ x := by
      intro x hx
      have hx1 : x ∈ θ f₁ := h1 (le_sup_right (a := kOf (θ f₁)) (hLK hx))
      have := hθ.isFunctor.le_centralizer f₁ hf₁A (ne_one_of_not_mem hf₁E) hx1
      exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm
    have hN : f₁ ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_of_forall_commute hcomm
    have : f₁ ∈ A ⊓ Subgroup.normalizer (L : Set G) := ⟨hf₁A, hN⟩
    rw [D.inf_normalizer_lcal hS₂ hf₂ hf₂E hL] at this
    exact hf₁B₂ this

theorem Concl71.le_projIn_of_diag (hC : Concl71 p A θ E B W) {K₁ K₂ : Subgroup G}
    (hQ : IsDirectProduct (Set.range fun i => W i ⊓ K₁) K₁) (hWK : wsub p A θ = K₁ ⊔ K₂)
    (i₀ : Fin p)
    (hdiag : ∀ x ∈ W i₀ ⊓ K₁, ∃ l ∈ sSup (Set.range W \ {W i₀}), x * l ∈ K₂) :
    W i₀ ≤ projIn (Set.range W) (W i₀) K₂ := by
  have hdp := hC.dp
  have hJ₀ : W i₀ ∈ Set.range W := ⟨i₀, rfl⟩
  have hK₁W : K₁ ≤ wsub p A θ := hWK ▸ le_sup_left
  have hK₂W : K₂ ≤ wsub p A θ := hWK ▸ le_sup_right
  have h1 : ∀ y (hy : y ∈ K₁), ((hdp.coord hJ₀ ⟨y, hK₁W hy⟩ : W i₀) : G) ∈ W i₀ ⊓ K₁ := by
    intro y hy
    have hy' : y ∈ sSup (Set.range fun i => W i ⊓ K₁) := by rw [hQ.sSup_eq]; exact hy
    have hXK : ∀ Y ∈ Set.range (fun i => W i ⊓ K₁), Y ≤ wsub p A θ := by
      rintro _ ⟨i, rfl⟩
      exact inf_le_right.trans hK₁W
    refine coord_mem_of_mem_sSup hdp hJ₀ hXK ?_ hy'
    rintro _ ⟨i, rfl⟩ x hx
    by_cases hi : i = i₀
    · subst hi
      rw [hdp.coord_of_mem hJ₀ hx.1]
      exact hx
    · have hne : W i ≠ W i₀ := fun e => hi (hC.inj e)
      rw [hdp.coord_of_mem_ne hJ₀ ⟨i, rfl⟩ hne hx.1]
      exact one_mem _
  have h2 : W i₀ ⊓ K₁ ≤ projIn (Set.range W) (W i₀) K₂ := by
    intro x hx
    obtain ⟨l, hl, hxl⟩ := hdiag x hx
    refine (hdp.mem_projIn_iff hJ₀).mpr ⟨⟨x * l, hK₂W hxl⟩, hxl, ?_⟩
    exact hdp.coord_mul hJ₀ hx.1 hl
  intro w hw
  have hww : w ∈ wsub p A θ := hdp.le hJ₀ hw
  have hw' : w ∈ sSup ({K₁, K₂} : Set (Subgroup G)) := by
    rw [sSup_pair, ← hWK]
    exact hww
  have hXK : ∀ Y ∈ ({K₁, K₂} : Set (Subgroup G)), Y ≤ wsub p A θ := by
    rintro Y (rfl | rfl)
    · exact hK₁W
    · exact hK₂W
  have := coord_mem_of_mem_sSup hdp hJ₀ (Z := projIn (Set.range W) (W i₀) K₂) hXK ?_ hw'
  · rwa [hdp.coord_of_mem hJ₀ hw] at this
  · rintro Y (rfl | rfl) y hy
    · exact h2 (h1 y hy)
    · exact (hdp.mem_projIn_iff hJ₀).mpr ⟨⟨y, hK₂W hy⟩, hy, rfl⟩

theorem Concl71.card_inf_centralizer_le (hC : Concl71 p A θ E B W) (hp : p.Prime)
    (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 3) (hB : B ∈ signalizerFunctorEk p 2 A)
    {f : G} (hfA : f ∈ A) (hfB : f ∉ B) (i₀ : Fin p) :
    Nat.card ↥(wsub p A θ ⊓ Subgroup.centralizer ({f} : Set G)) ≤ Nat.card ↥(W i₀) := by
  have hzA : Subgroup.zpowers f ≤ A := Subgroup.zpowers_le.mpr hfA
  have hdp := hC.dp
  have hJ₀ : W i₀ ∈ Set.range W := ⟨i₀, rfl⟩
  have hA' : ∀ a ∈ Subgroup.zpowers f, ∀ J ∈ Set.range W,
      J.map (MulAut.conj a).toMonoidHom ∈ Set.range W := by
    rintro a ha _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hC.perm a (hzA ha) i
    exact ⟨j, hj.symm⟩
  have htrans : ∀ K' ∈ Set.range W, ∃ a ∈ Subgroup.zpowers f,
      K' = (W i₀).map (MulAut.conj a).toMonoidHom := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨c, hc, hcj⟩ := hC.exists_mem_zpowers hp hA hAc hB hfA hfB i₀ j
    exact ⟨c, hc, hcj.symm⟩
  have hbot := inf_centralizer_inf_sSup_eq_bot_of_transitive hdp hA' hJ₀ htrans
  have hcen : Subgroup.centralizer (Subgroup.zpowers f : Set G) =
      Subgroup.centralizer ({f} : Set G) := centralizer_zpowers_eq_singleton f
  rw [hcen] at hbot
  let ψ : ↥(wsub p A θ ⊓ Subgroup.centralizer ({f} : Set G)) →* ↥(W i₀) :=
    (hdp.coord hJ₀).comp (Subgroup.inclusion inf_le_left)
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    have hyW : (y : G) ∈ wsub p A θ := (Subgroup.mem_inf.mp y.2).1
    have hyC : (y : G) ∈ Subgroup.centralizer ({f} : Set G) := (Subgroup.mem_inf.mp y.2).2
    have hy1 : hdp.coord hJ₀ ⟨y, hyW⟩ = 1 := hy
    have hys : (y : G) ∈ sSup (Set.range W \ {W i₀}) := (hdp.coord_eq_one_iff hJ₀ _).mp hy1
    have : (y : G) ∈ wsub p A θ ⊓ Subgroup.centralizer ({f} : Set G) ⊓
        sSup (Set.range W \ {W i₀}) := ⟨⟨hyW, hyC⟩, hys⟩
    rw [hbot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp this))
  exact Nat.card_le_card_of_injective ψ hψ

theorem nearPSolvable_of_dp {S : Set (Subgroup G)} {K : Subgroup G} (hK : IsDirectProduct S K)
    (hcop : Nat.Coprime p (Nat.card K)) (hS : ∀ J ∈ S, signalizerNearPSolvable p ↥J) :
    signalizerNearPSolvable p ↥K := by
  refine signalizerNearPSolvable_iff.mpr ⟨hcop, fun X _ _ hX hnab => ?_⟩
  have h1 : IsSectionOf X (∀ J : S, ↥(J : Subgroup G)) :=
    hX.trans (IsSectionOf.of_mulEquiv hK.equiv)
  obtain ⟨J, hJ⟩ := IsSectionOf.of_pi hnab h1
  exact (signalizerNearPSolvable_iff.mp (hS J J.2)).2 X hJ hnab

omit [Finite G] in
theorem Concl71.inf_ne_bot {E B : Subgroup G} {W : Fin p → Subgroup G}
    (hC : Concl71 p A θ E B W) {X : Subgroup G} (hXA : Admits A X)
    (hQ : IsDirectProduct (Set.range fun i => W i ⊓ X) X) (hX : X ≠ ⊥) (i : Fin p) :
    W i ⊓ X ≠ ⊥ := by
  intro hbot
  apply hX
  rw [← hQ.sSup_eq]
  refine le_bot_iff.mp (sSup_le ?_)
  rintro _ ⟨j, rfl⟩
  obtain ⟨a, ha, haij⟩ := hC.trans i j
  have := Concl71.cj_inf_eq hXA ha haij
  rw [hbot, cj_bot] at this
  exact this.symm.le

theorem key_lemma
    (h : Counterexample p A θ) {E B₁ B₂ : Subgroup G} (D : Data h E)
    (hS₁ : Setting p A E B₁) (hS₂ : Setting p A E B₂) {W : Fin p → Subgroup G}
    (hC : Concl71 p A θ E B₁ W) {f₁ f₂ : G} (hf₁ : f₁ ∈ B₁) (hf₁E : f₁ ∉ E) (hf₂ : f₂ ∈ B₂)
    (hf₂E : f₂ ∉ E) (hf₂B₁ : f₂ ∉ B₁) (hf₁B₂ : f₁ ∉ B₂) :
    wsub p A θ ⊓ Subgroup.centralizer ({f₂} : Set G) ≤ θ f₂ ∧
      Nat.Coprime p (Nat.card ↥(wsub p A θ)) ∧ signalizerNearPSolvable p ↥(wsub p A θ) := by
  have hθ := h.hyp.nearFunctor
  have hp := h.hyp.prime
  have hf₁A := hS₁.mem_A hf₁
  have hf₂A := hS₂.mem_A hf₂
  have hf₁1 := ne_one_of_not_mem hf₁E
  have hf₂1 := ne_one_of_not_mem hf₂E
  have hWK := D.wsub_eq_sup hS₂ hf₁A hf₁E hf₂ hf₂E hf₁B₂
  have hK₁A : Admits A (kOf (θ f₁)) :=
    Thm41Aux.admits_kOf (hθ.isFunctor.normalized f₁ hf₁A hf₁1)
  have hQ := hC.comp f₁ hf₁ hf₁E
  have hK₁perf : Group.IsPerfect ↥(kOf (θ f₁)) := h.isPerfect_kOf (D.cset_apply hf₁A hf₁E)
  have hK₁ne : kOf (θ f₁) ≠ ⊥ :=
    Counterexample.kOf_ne_bot_of_not_isSolvable (D.nonsolv f₁ hf₁A hf₁E)
  have hQne := hC.inf_ne_bot hK₁A hQ hK₁ne
  have hf₂p : f₂ ^ p = 1 := hθ.elemAbelian.2 f₂ hf₂A
  have hcen : Subgroup.centralizer (Subgroup.zpowers f₂ : Set G) =
      Subgroup.centralizer ({f₂} : Set G) := centralizer_zpowers_eq_singleton f₂
  set i₀ : Fin p := ⟨0, hp.pos⟩ with hi₀
  have hKperf := hC.isPerfect_cen hp hθ.elemAbelian h.hyp.card hS₁.hB hK₁A hQ hQne hf₂A hf₂p
    hf₂B₁ hK₁perf
  have hKθ : kOf (θ f₁) ⊓ Subgroup.centralizer ({f₂} : Set G) ≤ θ f₂ := fun x hx =>
    hθ.isFunctor.balance f₁ hf₁A hf₁1 f₂ hf₂A hf₂1 ⟨kOf_le _ hx.1, hx.2⟩
  have hKK₂ : kOf (θ f₁) ⊓ Subgroup.centralizer ({f₂} : Set G) ≤ kOf (θ f₂) := by
    have h1 := Nonsolvable.le_perfectResidual_map_of_isPerfect hKperf hKθ
    have h2 := h.perfRes_eq_kOf (D.cset_apply hf₂A hf₂E)
    exact h2 ▸ h1
  have hproj := hC.projIn_eq hp hK₁A hQ hQne hf₂A hf₂p hf₂B₁ i₀
  have hdiag : ∀ x ∈ W i₀ ⊓ kOf (θ f₁), ∃ l ∈ sSup (Set.range W \ {W i₀}),
      x * l ∈ kOf (θ f₂) := by
    intro x hx
    have hxp : x ∈ projIn (Set.range fun i => W i ⊓ kOf (θ f₁)) (W i₀ ⊓ kOf (θ f₁))
        (kOf (θ f₁) ⊓ Subgroup.centralizer (Subgroup.zpowers f₂ : Set G)) := by
      rw [hproj]; exact hx
    rw [projIn, mem_proj_iff (hQ.commute_sSup_diff (⟨i₀, rfl⟩ : W i₀ ⊓ kOf (θ f₁) ∈
      Set.range fun i => W i ⊓ kOf (θ f₁)))] at hxp
    obtain ⟨-, l, hl, hxl⟩ := hxp
    refine ⟨l, ?_, ?_⟩
    · have hle : sSup ((Set.range fun i => W i ⊓ kOf (θ f₁)) \ {W i₀ ⊓ kOf (θ f₁)}) ≤
          sSup (Set.range W \ {W i₀}) := by
        refine sSup_le ?_
        rintro _ ⟨⟨i, rfl⟩, hne⟩
        have hi : i ≠ i₀ := fun e => hne (by rw [e]; rfl)
        exact inf_le_left.trans (le_sSup ⟨⟨i, rfl⟩, fun e => hi (hC.inj e)⟩)
      exact hle hl
    · rw [hcen] at hxl
      exact hKK₂ hxl
  have hJ₀ : W i₀ ∈ Set.range W := ⟨i₀, rfl⟩
  have hJle := hC.le_projIn_of_diag hQ hWK i₀ hdiag
  have hK₂W : kOf (θ f₂) ≤ wsub p A θ := hWK ▸ le_sup_right
  have c1 := hC.card_inf_centralizer_le hp hθ.elemAbelian h.hyp.card hS₁.hB hf₂A hf₂B₁ i₀
  have c2 : Nat.card ↥(W i₀) ≤
      Nat.card ↥(projIn (Set.range W) (W i₀) (kOf (θ f₂))) := Subgroup.card_le_of_le hJle
  have c3 : Nat.card ↥(projIn (Set.range W) (W i₀) (kOf (θ f₂))) ≤ Nat.card ↥(kOf (θ f₂)) :=
    Nat.card_le_card_of_surjective _ (Thm210.projInHom_surjective hC.dp hJ₀ hK₂W)
  have c4 : Nat.card ↥(kOf (θ f₂)) ≤ Nat.card ↥(θ f₂) := Subgroup.card_le_of_le (kOf_le _)
  have c5 : θ f₂ ≤ wsub p A θ ⊓ Subgroup.centralizer ({f₂} : Set G) :=
    le_inf (le_sSup (apply_mem_assoc hθ hf₂A hf₂1)) (hθ.isFunctor.le_centralizer f₂ hf₂A hf₂1)
  have c6 := Subgroup.card_le_of_le c5
  have hchain : Nat.card ↥(wsub p A θ ⊓ Subgroup.centralizer ({f₂} : Set G)) =
      Nat.card ↥(θ f₂) := le_antisymm (c1.trans (c2.trans (c3.trans c4))) c6
  have heq : θ f₂ = wsub p A θ ⊓ Subgroup.centralizer ({f₂} : Set G) :=
    Subgroup.eq_of_le_of_card_ge c5 hchain.le
  have hW0 : Nat.card ↥(W i₀) = Nat.card ↥(kOf (θ f₂)) :=
    le_antisymm (c2.trans c3) (c4.trans (hchain.symm.le.trans c1))
  have hcop0 : Nat.Coprime p (Nat.card ↥(W i₀)) := by
    rw [hW0]
    exact (hθ.isFunctor.coprime f₂ hf₂A hf₂1).coprime_dvd_right
      (Subgroup.card_dvd_of_le (kOf_le _))
  have hcopi : ∀ i, Nat.Coprime p (Nat.card ↥(W i)) := by
    intro i
    obtain ⟨a, ha, hai⟩ := hC.trans i₀ i
    rw [← hai, Subgroup.card_map_of_injective (MulAut.conj a).injective] 
    exact hcop0
  have : Fintype ↥(Set.range W) := Fintype.ofFinite _
  have hcardW : Nat.card ↥(wsub p A θ) = ∏ J : ↥(Set.range W), Nat.card ↥(J : Subgroup G) := by
    rw [← Nat.card_congr hC.dp.equiv.toEquiv, Nat.card_pi]
  have hcopW : Nat.Coprime p (Nat.card ↥(wsub p A θ)) := by
    rw [hcardW]
    refine Nat.Coprime.prod_right fun J _ => ?_
    obtain ⟨i, hi⟩ := J.2
    rw [← hi]
    exact hcopi i
  have hnear₀ : ∀ (X : Type u) [Group X] [IsSimpleGroup X], IsSectionOf X ↥(W i₀) →
      (∃ a b : X, a * b ≠ b * a) → signalizerNearSimpleModel p X := by
    intro X _ _ hX hnab
    have h1 : IsSectionOf ↥(W i₀) ↥(W i₀) := IsSectionOf.refl _
    have h2 : IsSectionOf ↥(W i₀) ↥(projIn (Set.range W) (W i₀) (kOf (θ f₂))) :=
      h1.of_injective (Subgroup.inclusion hJle) (Subgroup.inclusion_injective hJle)
    have h3 : IsSectionOf ↥(projIn (Set.range W) (W i₀) (kOf (θ f₂))) ↥(kOf (θ f₂)) :=
      IsSectionOf.of_surjective (Thm210.projInHom hC.dp hJ₀ hK₂W)
        (Thm210.projInHom_surjective hC.dp hJ₀ hK₂W)
    have h4 : IsSectionOf X ↥(θ f₂) :=
      (hX.trans (h2.trans h3)).of_injective (Subgroup.inclusion (kOf_le (θ f₂)))
        (Subgroup.inclusion_injective _)
    exact (signalizerNearPSolvable_iff.mp (hθ.near f₂ hf₂A hf₂1).1).2 X h4 hnab
  refine ⟨heq.ge, hcopW, nearPSolvable_of_dp hC.dp hcopW ?_⟩
  rintro _ ⟨i, rfl⟩
  refine signalizerNearPSolvable_iff.mpr ⟨hcopi i, fun X _ _ hX hnab => hnear₀ X ?_ hnab⟩
  obtain ⟨a, ha, hai⟩ := hC.trans i₀ i
  rw [← hai] at hX
  exact hX.trans (IsSectionOf.of_mulEquiv
    (Subgroup.equivMapOfInjective (W i₀) (MulAut.conj a).toMonoidHom (MulAut.conj a).injective))

end Key

end CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7S35
