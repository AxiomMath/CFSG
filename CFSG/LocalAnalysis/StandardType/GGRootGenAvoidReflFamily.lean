module

public import CFSG.LocalAnalysis.StandardType.GGTorusRootGenAvoidModel
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly Multiplicative

private lemma add_of_conj {p k : ℕ} {G : Type} [Group G]
    {T : Multiplicative (Fin k → ZMod p) →* G} (hT : Function.Injective T) {w : G}
    {f : (Fin k → ZMod p) → Fin k → ZMod p}
    (hw : ∀ t, w * T (ofAdd t) * w⁻¹ = T (ofAdd (f t))) :
    ∀ t u, f (t + u) = f t + f u := by
  intro t u
  refine ofAdd.injective (hT ?_)
  calc T (ofAdd (f (t + u))) = w * T (ofAdd (t + u)) * w⁻¹ := (hw (t + u)).symm
    _ = w * (T (ofAdd t) * T (ofAdd u)) * w⁻¹ := by rw [ofAdd_add, map_mul]
    _ = T (ofAdd (f t)) * T (ofAdd (f u)) := by rw [← hw t, ← hw u]; group
    _ = T (ofAdd (f t + f u)) := by rw [ofAdd_add, map_mul]

private def addEquivOfInvolutive {p k : ℕ} {f : (Fin k → ZMod p) → Fin k → ZMod p}
    (hadd : ∀ t u, f (t + u) = f t + f u) (hinv : ∀ t, f (f t) = t) :
    (Fin k → ZMod p) ≃+ (Fin k → ZMod p) where
  toFun := f
  invFun := f
  left_inv := hinv
  right_inv := hinv
  map_add' := hadd

private lemma mulAut_congr_addEquiv_apply {A B : Type} [AddGroup A] [Group B]
    (e : Multiplicative A ≃* B) (σ : A ≃+ A) (x : B) :
    MulAut.congr e (AddEquiv.toMultiplicative σ) x =
      e (ofAdd (σ (toAdd (e.symm x)))) := by
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    AddEquiv.toMultiplicative_apply_apply]

private lemma fixed_iff_mulAut_congr_addEquiv {A B : Type} [AddGroup A] [Group B]
    (e : Multiplicative A ≃* B) (σ : A ≃+ A) (x : B) :
    MulAut.congr e (AddEquiv.toMultiplicative σ) x = x ↔
      σ (toAdd (e.symm x)) = toAdd (e.symm x) := by
  rw [mulAut_congr_addEquiv_apply]
  constructor
  · intro h
    have h1 : ofAdd (σ (toAdd (e.symm x))) = e.symm x := by
      simpa using congrArg e.symm h
    simpa using congrArg toAdd h1
  · intro h
    change e (ofAdd (σ (toAdd (e.symm x)))) = x
    rw [show ofAdd (σ (toAdd (e.symm x))) = e.symm x by rw [h, ofAdd_toAdd]]
    exact e.apply_symm_apply x

private lemma fixedSet_mulAut_congr_addEquiv {A B : Type} [AddGroup A] [Group B]
    (e : Multiplicative A ≃* B) (σ : A ≃+ A) :
    {x : B | MulAut.congr e (AddEquiv.toMultiplicative σ) x = x} =
      e '' {t : Multiplicative A | σ (toAdd t) = toAdd t} := by
  ext x
  rw [Set.mem_setOf_eq, fixed_iff_mulAut_congr_addEquiv, Set.mem_image]
  constructor
  · intro h
    exact ⟨e.symm x, h, e.apply_symm_apply x⟩
  · rintro ⟨t, ht, rfl⟩
    simpa using ht

private lemma card_fixed_mulAut_congr_addEquiv {A B : Type} [AddGroup A] [Group B]
    (e : Multiplicative A ≃* B) (σ : A ≃+ A) :
    Nat.card {x : B // MulAut.congr e (AddEquiv.toMultiplicative σ) x = x} =
      Nat.card {t : Multiplicative A // σ (toAdd t) = toAdd t} :=
  Nat.card_congr (Equiv.subtypeEquiv e.symm.toEquiv fun x =>
    fixed_iff_mulAut_congr_addEquiv e σ x)

private lemma card_fixed_toAdd {p k : ℕ} (f : (Fin k → ZMod p) → Fin k → ZMod p) :
    Nat.card {t : Multiplicative (Fin k → ZMod p) // f (toAdd t) = toAdd t} =
      Nat.card {t : Fin k → ZMod p // f t = t} := by
  refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd ?_)
  intro t
  rfl

private lemma mulAut_congr_addEquiv_mul_self {A B : Type} [AddGroup A] [Group B]
    (e : Multiplicative A ≃* B) (σ : A ≃+ A) (h : ∀ t, σ (σ t) = t) :
    MulAut.congr e (AddEquiv.toMultiplicative σ) *
      MulAut.congr e (AddEquiv.toMultiplicative σ) = 1 := by
  have h2 : AddEquiv.toMultiplicative σ * AddEquiv.toMultiplicative σ = 1 := by
    ext t
    simp only [MulAut.mul_apply, AddEquiv.toMultiplicative_apply_apply, MulAut.one_apply,
      toAdd_ofAdd, h, ofAdd_toAdd]
  rw [← map_mul, h2, map_one]

private lemma mulAut_congr_addEquiv_eq_iff {A B : Type} [AddGroup A] [Group B]
    (e : Multiplicative A ≃* B) (σ τ : A ≃+ A) :
    MulAut.congr e (AddEquiv.toMultiplicative σ) =
      MulAut.congr e (AddEquiv.toMultiplicative τ) ↔ σ = τ := by
  constructor
  · intro h
    have h' : AddEquiv.toMultiplicative σ = AddEquiv.toMultiplicative τ :=
      (MulAut.congr e).injective h
    exact AddEquiv.toMultiplicative.injective h'
  · rintro rfl
    rfl

private lemma image_comp_symm_image {A B C : Type} (e : A ≃ B) (T : A → C) (s : Set A) :
    (T ∘ e.symm) '' (e '' s) = T '' s := by
  ext x
  simp only [Set.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, by rw [Equiv.symm_apply_apply]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨e a, ⟨a, ha, rfl⟩, by rw [Equiv.symm_apply_apply]⟩

private lemma exists_piCoords {p k : ℕ} {G : Type} [Group G]
    {T : Multiplicative (Fin k → ZMod p) →* G} (hT : Function.Injective T)
    {ι : Type} (w : ι → G) (f : ι → (Fin k → ZMod p) → Fin k → ZMod p)
    (hw : ∀ i t, w i * T (ofAdd t) * (w i)⁻¹ = T (ofAdd (f i t)))
    (hinv : ∀ i t, f i (f i t) = t)
    (hfix : ∀ i, Nat.card {t // f i t = t} * p = p ^ k) :
    ∃ (τ : (Fin k → Multiplicative (ZMod p)) →* G)
      (s : ι → MulAut (Fin k → Multiplicative (ZMod p))),
      Function.Injective τ ∧ τ.range = T.range ∧
      (∀ i g, w i * τ g * (w i)⁻¹ = τ (s i g)) ∧ (∀ i, s i * s i = 1) ∧
      (∀ i, τ '' {g | s i g = g} = SuSplitRootGen.torusFix T (f i)) ∧
      (∀ i, Nat.card {g // s i g = g} * p =
        Nat.card (Fin k → Multiplicative (ZMod p))) ∧
      (∀ i j, s i = s j ↔ f i = f j) := by
  classical
  let ε : Multiplicative (Fin k → ZMod p) ≃* (Fin k → Multiplicative (ZMod p)) :=
    MulEquiv.piMultiplicative _
  let τ : (Fin k → Multiplicative (ZMod p)) →* G := T.comp ε.symm.toMonoidHom
  have hτ : Function.Injective τ := fun x y h => ε.symm.injective (hT h)
  have hτrange : τ.range = T.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ε.symm.surjective,
      ← MonoidHom.range_eq_map]
  let σ : ι → (Fin k → ZMod p) ≃+ (Fin k → ZMod p) := fun i =>
    addEquivOfInvolutive (add_of_conj hT (hw i)) (hinv i)
  have hσ : ∀ (i : ι) (t : Fin k → ZMod p), σ i t = f i t := fun i t => rfl
  let s' : ι → MulAut (Fin k → Multiplicative (ZMod p)) := fun i =>
    MulAut.congr ε (AddEquiv.toMultiplicative (σ i))
  have hw' : ∀ (i : ι) (g : Fin k → Multiplicative (ZMod p)),
      w i * τ g * (w i)⁻¹ = τ (s' i g) := by
    intro i g
    change w i * τ g * (w i)⁻¹ =
      τ (MulAut.congr ε (AddEquiv.toMultiplicative (σ i)) g)
    rw [mulAut_congr_addEquiv_apply]
    have hτe : ∀ x : Multiplicative (Fin k → ZMod p), τ (ε x) = T x := by
      intro x
      change T (ε.symm (ε x)) = T x
      rw [MulEquiv.symm_apply_apply]
    rw [hτe]
    have hτg : τ g = T (ofAdd (toAdd (ε.symm g))) := by
      change T (ε.symm g) = T (ofAdd (toAdd (ε.symm g)))
      rw [ofAdd_toAdd]
    rw [hτg, hσ]
    exact hw i (toAdd (ε.symm g))
  have hinv' : ∀ i, s' i * s' i = 1 := fun i =>
    mulAut_congr_addEquiv_mul_self ε (σ i) fun t => by
      rw [hσ, hσ]
      exact hinv i t
  have hfixSet : ∀ i, τ '' {g | s' i g = g} = SuSplitRootGen.torusFix T (f i) := by
    intro i
    change τ '' {g | MulAut.congr ε (AddEquiv.toMultiplicative (σ i)) g = g} =
      SuSplitRootGen.torusFix T (f i)
    rw [fixedSet_mulAut_congr_addEquiv]
    change (T ∘ (ε.toEquiv).symm) '' ((ε.toEquiv) '' {t | σ i (toAdd t) = toAdd t}) =
      SuSplitRootGen.torusFix T (f i)
    rw [image_comp_symm_image]
    rfl
  have hfix' : ∀ i, Nat.card {g // s' i g = g} * p =
      Nat.card (Fin k → Multiplicative (ZMod p)) := by
    intro i
    have h1 : Nat.card {g // s' i g = g} = Nat.card {t // f i t = t} := by
      change Nat.card {g // MulAut.congr ε (AddEquiv.toMultiplicative (σ i)) g = g} =
        Nat.card {t : Fin k → ZMod p // f i t = t}
      rw [card_fixed_mulAut_congr_addEquiv]
      exact card_fixed_toAdd (f i)
    have h2 : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
      rw [← Nat.card_congr ε.toEquiv,
        Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin k → ZMod p) ≃ _),
        Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]
    rw [h1, h2]
    exact hfix i
  have hs'eq : ∀ i j, s' i = s' j ↔ f i = f j := by
    intro i j
    change MulAut.congr ε (AddEquiv.toMultiplicative (σ i)) =
      MulAut.congr ε (AddEquiv.toMultiplicative (σ j)) ↔ f i = f j
    rw [mulAut_congr_addEquiv_eq_iff]
    constructor
    · intro h
      funext t
      rw [← hσ i t, ← hσ j t, h]
    · intro h
      ext t
      rw [hσ i t, hσ j t, congrFun h t]
  exact ⟨τ, s', hτ, hτrange, hw', hinv', hfixSet, hfix', hs'eq⟩

theorem ggTorusModelAt_of_reflFamily {p k : ℕ} {G : Type} [Group G]
    {T : Multiplicative (Fin k → ZMod p) →* G} (hT : Function.Injective T) {ι : Type} [Nonempty ι]
    (w : ι → G) (f : ι → (Fin k → ZMod p) → Fin k → ZMod p) (S : ι → Subgroup G)
    (hw : ∀ i t, w i * T (ofAdd t) * (w i)⁻¹ = T (ofAdd (f i t)))
    (hinv : ∀ i t, f i (f i t) = t) (hfix : ∀ i, Nat.card {t // f i t = t} * p = p ^ k)
    (hwS : ∀ i, w i ∈ S i)
    (hcomp : ∀ i, IsComponentOf (S i) (Subgroup.centralizer (SuSplitRootGen.torusFix T (f i))))
    (hdvd : ∀ i, p ∣ Nat.card (S i)) (hS : ∀ i j, f i = f j → S i = S j)
    (hgen : ∀ j, (⨆ (i : ι) (_ : f i ≠ f j), S i) = ⊤) :
    GGTorusModelAt p T.range := by
  classical
  obtain ⟨τ, s', hτ, hτrange, hw', hinv', hfixSet, hfix', hs'eq⟩ :=
    exists_piCoords hT w f hw hinv hfix
  let r : Set.range f → ι := fun ρ => Classical.choose ρ.2
  have hr : ∀ ρ : Set.range f, f (r ρ) = ρ.1 := fun ρ => Classical.choose_spec ρ.2
  let w' : Set.range f → G := fun ρ => w (r ρ)
  let s'' : Set.range f → MulAut (Fin k → Multiplicative (ZMod p)) := fun ρ => s' (r ρ)
  let S' : Set.range f → Subgroup G := fun ρ => S (r ρ)
  have hs''inj : Function.Injective s'' := by
    intro ρ₁ ρ₂ h
    have h1 : f (r ρ₁) = f (r ρ₂) := (hs'eq (r ρ₁) (r ρ₂)).mp h
    have h2 : ρ₁.1 = ρ₂.1 := by
      rw [← hr ρ₁, ← hr ρ₂]
      exact h1
    exact Subtype.ext h2
  have hw'' : ∀ (ρ : Set.range f) (g : Fin k → Multiplicative (ZMod p)),
      w' ρ * τ g * (w' ρ)⁻¹ = τ (s'' ρ g) := fun ρ g => hw' (r ρ) g
  have hinv'' : ∀ ρ : Set.range f, s'' ρ * s'' ρ = 1 := fun ρ => hinv' (r ρ)
  have hfix'' : ∀ ρ : Set.range f, Nat.card {g // s'' ρ g = g} * p =
      Nat.card (Fin k → Multiplicative (ZMod p)) := fun ρ => hfix' (r ρ)
  have hgen' : ∀ ρ₀ : Set.range f,
      (⨆ (ρ : Set.range f) (_ : ρ ≠ ρ₀), S' ρ) = ⊤ := by
    intro ρ₀
    rw [eq_top_iff, ← hgen (r ρ₀)]
    refine iSup_le fun i => iSup_le fun hi => ?_
    let ρ : Set.range f := ⟨f i, ⟨i, rfl⟩⟩
    have hρ : ρ ≠ ρ₀ := by
      intro h
      exact hi (by rw [hr ρ₀]; simpa using congrArg Subtype.val h)
    refine le_iSup_of_le ρ (le_iSup_of_le hρ ?_)
    have hSr : S' ρ = S i := hS (r ρ) i (by rw [hr ρ])
    exact le_of_eq hSr.symm
  exact ⟨k, τ, Set.range f, w', s'', S',
    ⟨⟨f (Classical.arbitrary ι), Classical.arbitrary ι, rfl⟩⟩, hτ, hτrange, hw'', hinv'',
    hfix'', hs''inj, fun ρ => hwS (r ρ), fun ρ => by
      rw [hfixSet (r ρ)]
      exact hcomp (r ρ), fun ρ => hdvd (r ρ), hgen'⟩

end CFSG.StandardType

end
