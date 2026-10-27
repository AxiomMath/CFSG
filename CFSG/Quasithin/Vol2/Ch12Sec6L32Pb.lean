module

public import CFSG.Quasithin.EmptyFaithful.LRed5Twist

public section

namespace CFSG.Quasithin.H13.L1232

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix

variable {V : Type} [CommGroup V] {k : Type} [Field k]

theorem natAct_irreducible_stated (X : Subgroup (Multiplicative (Fin 3 → k)))
    (hX : ∀ (γ : ↥(StatedSL 3 k)) (x : Multiplicative (Fin 3 → k)), x ∈ X →
      natAct (StatedSL 3 k) γ x ∈ X) : X = ⊥ ∨ X = ⊤ := by
  refine SL3Model.natAct3_irreducible X fun A x hx => ?_
  have := hX (specialLinearGroupEquivStatedSL 3 k A) x hx
  have h : SL3Model.natAct3 A x =
      natAct (StatedSL 3 k) (specialLinearGroupEquivStatedSL 3 k A) x := by
    apply Multiplicative.toAdd.injective
    simp only [SL3Model.natAct3_apply, natAct, toAdd_ofAdd]
    rw [specialLinearGroupEquivStatedSL_coe]
    rfl
  rwa [h]

theorem exists_equivariant_of_natural_section {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(StatedSL 3 k) →* ↥L} (hπ : (FFModel.nat (StatedSL 3 k)).RealizesVia L U Z π)
    {s : MulAut V} (hU : ∀ u ∈ U, s u ∈ U) (hU' : ∀ u ∈ U, s⁻¹ u ∈ U) (hZ : ∀ z ∈ Z, s z ∈ Z)
    (hZ' : ∀ z ∈ Z, s⁻¹ z ∈ Z) {α : MulAut ↥(StatedSL 3 k)}
    (hα : ∀ γ, ((π (α γ) : ↥L) : MulAut V) = s * (π γ : ↥L) * s⁻¹) :
    ∃ φ : (Fin 3 → k) → (Fin 3 → k), Function.Bijective φ ∧
      ∀ (γ : ↥(StatedSL 3 k)) (v : Fin 3 → k),
        φ (((γ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v) =
          ((α γ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ φ v := by
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.exists_natMap hπ
  obtain ⟨Θ, hΘ⟩ := LRed5.exists_equiv_of_section hfs hfk hU hU' hZ hZ'
  refine ⟨fun v => Multiplicative.toAdd (Θ (Multiplicative.ofAdd v)),
    Multiplicative.toAdd.bijective.comp (Θ.bijective.comp Multiplicative.ofAdd.bijective),
    fun γ v => ?_⟩
  obtain ⟨u, hu⟩ := hfs (Multiplicative.ofAdd v)
  have hγu : ((π γ : ↥L) : MulAut V) (u : V) ∈ U := hπ.2.2.2.1 (π γ) u u.2
  have hsu : ((π (α γ) : ↥L) : MulAut V) (s (u : V)) ∈ U := hπ.2.2.2.1 _ _ (hU u u.2)
  have h1 : Multiplicative.ofAdd (((γ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v) =
      f ⟨_, hγu⟩ := by
    rw [hfe γ u hγu, hu]
    rfl
  have h3 : (⟨s (((π γ : ↥L) : MulAut V) (u : V)), hU _ hγu⟩ : ↥U) =
      ⟨((π (α γ) : ↥L) : MulAut V) (s (u : V)), hsu⟩ := by
    apply Subtype.ext
    show s (((π γ : ↥L) : MulAut V) (u : V)) = ((π (α γ) : ↥L) : MulAut V) (s (u : V))
    rw [hα γ]
    simp [MulAut.mul_apply]
  have h5 : f ⟨s (u : V), hU u u.2⟩ = Θ (f u) := (hΘ u).symm
  show Multiplicative.toAdd (Θ (Multiplicative.ofAdd
      (((γ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v))) =
    ((α γ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ
      Multiplicative.toAdd (Θ (Multiplicative.ofAdd v))
  rw [h1, hΘ ⟨_, hγu⟩, h3, hfe (α γ) ⟨s (u : V), hU u u.2⟩ hsu, h5, hu]
  rfl

theorem exists_equivariant_of_two_natural [Finite k] {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    {I : Fin 2 → Subgroup V} {π : ↥(StatedSL 3 k) →* ↥L}
    (hind : ∀ i, I i ⊓ (Z ⊔ ⨆ (j : Fin 2) (_ : j ≠ i), I j) = Z) (hsup : (Z ⊔ ⨆ i, I i) = U)
    (hreal : ∀ i, (FFModel.nat (StatedSL 3 k)).RealizesVia L (I i) Z π) {s : MulAut V}
    (hU : ∀ u ∈ U, s u ∈ U) (hU' : ∀ u ∈ U, s⁻¹ u ∈ U) (hZ : ∀ z ∈ Z, s z ∈ Z)
    (hZ' : ∀ z ∈ Z, s⁻¹ z ∈ Z) {α : MulAut ↥(StatedSL 3 k)}
    (hαπ : ∀ γ, ((π (α γ) : ↥L) : MulAut V) = s * (π γ : ↥L) * s⁻¹) :
    ∃ φ : (Fin 3 → k) → (Fin 3 → k), Function.Bijective φ ∧
      ∀ (γ : ↥(StatedSL 3 k)) (v : Fin 3 → k),
        φ (((γ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v) =
          ((α γ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ φ v := by
  classical
  set M := Multiplicative (Fin 3 → k)
  have hIU : ∀ i, I i ≤ U := fun i => hsup ▸ (le_iSup I i).trans le_sup_right
  have hZU : Z ≤ U := hsup ▸ le_sup_left
  have hfin : ∀ i, ∃ f : ↥(I i) →* M, Function.Surjective f ∧
      (∀ u : ↥(I i), f u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (γ : ↥(StatedSL 3 k)) (u : ↥(I i)) (hu : ((π γ : ↥L) : MulAut V) (u : V) ∈ I i),
        f ⟨_, hu⟩ = natAct (StatedSL 3 k) γ (f u) := fun i => FFC.exists_natMap (hreal i)
  choose f hfs hfk hfe using hfin
  have hsup2 : (⨆ i : Fin 2, I i) = I 0 ⊔ I 1 :=
    le_antisymm (iSup_le (Fin.forall_fin_two.2 ⟨le_sup_left, le_sup_right⟩))
      (sup_le (le_iSup I 0) (le_iSup I 1))
  have hrest0 : (⨆ (j : Fin 2) (_ : j ≠ 0), I j) = I 1 := by
    refine le_antisymm (iSup₂_le fun j hj => ?_) (le_iSup₂_of_le (1 : Fin 2) (by decide) le_rfl)
    have : j = 1 := by revert j; decide
    rw [this]
  have hrest1 : (⨆ (j : Fin 2) (_ : j ≠ 1), I j) = I 0 := by
    refine le_antisymm (iSup₂_le fun j hj => ?_) (le_iSup₂_of_le (0 : Fin 2) (by decide) le_rfl)
    have : j = 0 := by revert j; decide
    rw [this]
  have hsplit : ∀ a b : V, a ∈ I 0 → b ∈ I 1 → a * b ∈ Z → a ∈ Z ∧ b ∈ Z := by
    intro a b ha hb hab
    constructor
    · have h1 : a ∈ I 0 ⊓ (Z ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j) := by
        refine ⟨ha, ?_⟩
        rw [hrest0, ← mul_inv_cancel_right a b]
        exact (Z ⊔ I 1).mul_mem (Subgroup.mem_sup_left hab)
          ((Z ⊔ I 1).inv_mem (Subgroup.mem_sup_right hb))
      rwa [hind 0] at h1
    · have h1 : b ∈ I 1 ⊓ (Z ⊔ ⨆ (j : Fin 2) (_ : j ≠ 1), I j) := by
        refine ⟨hb, ?_⟩
        rw [hrest1, ← inv_mul_cancel_left a b]
        exact (Z ⊔ I 0).mul_mem ((Z ⊔ I 0).inv_mem (Subgroup.mem_sup_right ha))
          (Subgroup.mem_sup_left hab)
      rwa [hind 1] at h1
  let mP : (↥(I 0) × ↥(I 1) × ↥Z) →* ↥U :=
    { toFun := fun p => ⟨(p.1 : V) * (p.2.1 : V) * (p.2.2 : V),
        mul_mem (mul_mem (hIU 0 p.1.2) (hIU 1 p.2.1.2)) (hZU p.2.2.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        ac_rfl) }
  have hmP : ∀ p, ((mP p : ↥U) : V) = (p.1 : V) * (p.2.1 : V) * (p.2.2 : V) := fun p => rfl
  have hmPs : Function.Surjective mP := by
    rintro ⟨u, hu⟩
    rw [← hsup, hsup2] at hu
    obtain ⟨z, hz, w, hw, rfl⟩ := Subgroup.mem_sup.1 hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hw
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩, ⟨z, hz⟩), Subtype.ext (by rw [hmP]; ac_rfl)⟩
  let F₀ : (↥(I 0) × ↥(I 1) × ↥Z) →* M × M :=
    ((f 0).comp (MonoidHom.fst _ _)).prod
      ((f 1).comp ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _)))
  have hF₀ : ∀ p, F₀ p = (f 0 p.1, f 1 p.2.1) := fun p => rfl
  have hker : mP.ker ≤ F₀.ker := by
    intro p hp
    have hp1 : (p.1 : V) * (p.2.1 : V) * (p.2.2 : V) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.1 hp)
    have hab : (p.1 : V) * (p.2.1 : V) ∈ Z := by
      rw [eq_inv_of_mul_eq_one_left hp1]
      exact Z.inv_mem p.2.2.2
    obtain ⟨ha, hb⟩ := hsplit _ _ p.1.2 p.2.1.2 hab
    rw [MonoidHom.mem_ker, hF₀]
    exact Prod.ext ((hfk 0 p.1).2 ha) ((hfk 1 p.2.1).2 hb)
  let F : ↥U →* M × M := mP.liftOfSurjective hmPs ⟨F₀, hker⟩
  have hF : ∀ p, F (mP p) = F₀ p := fun p =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨F₀, hker⟩ p
  have hFs : Function.Surjective F := by
    rintro ⟨m₀, m₁⟩
    obtain ⟨a, rfl⟩ := hfs 0 m₀
    obtain ⟨b, rfl⟩ := hfs 1 m₁
    exact ⟨mP (a, b, 1), by rw [hF, hF₀]⟩
  have hFk : ∀ u : ↥U, F u = 1 ↔ (u : V) ∈ Z := by
    intro u
    obtain ⟨p, rfl⟩ := hmPs u
    rw [hF, hF₀, hmP]
    constructor
    · intro h1
      have h2 : f 0 p.1 = 1 := congrArg Prod.fst h1
      have h3 : f 1 p.2.1 = 1 := congrArg Prod.snd h1
      exact mul_mem (mul_mem ((hfk 0 p.1).1 h2) ((hfk 1 p.2.1).1 h3)) p.2.2.2
    · intro h1
      have hab : (p.1 : V) * (p.2.1 : V) ∈ Z := by
        have := mul_mem h1 (Z.inv_mem p.2.2.2)
        rwa [mul_inv_cancel_right] at this
      obtain ⟨ha, hb⟩ := hsplit _ _ p.1.2 p.2.1.2 hab
      exact Prod.ext ((hfk 0 p.1).2 ha) ((hfk 1 p.2.1).2 hb)
  have hFe : ∀ (γ : ↥(StatedSL 3 k)) (u : ↥U),
      ∃ hu : ((π γ : ↥L) : MulAut V) (u : V) ∈ U,
        F ⟨_, hu⟩ = (natAct (StatedSL 3 k) γ (F u).1, natAct (StatedSL 3 k) γ (F u).2) := by
    intro γ u
    obtain ⟨p, rfl⟩ := hmPs u
    have hpa : ((π γ : ↥L) : MulAut V) (p.1 : V) ∈ I 0 := (hreal 0).2.2.2.1 (π γ) _ p.1.2
    have hpb : ((π γ : ↥L) : MulAut V) (p.2.1 : V) ∈ I 1 := (hreal 1).2.2.2.1 (π γ) _ p.2.1.2
    have hpz : ((π γ : ↥L) : MulAut V) (p.2.2 : V) ∈ Z := (hreal 0).2.2.2.2.1 (π γ) _ p.2.2.2
    have hq : ((π γ : ↥L) : MulAut V) ((mP p : ↥U) : V) =
        (((π γ : ↥L) : MulAut V) (p.1 : V)) * (((π γ : ↥L) : MulAut V) (p.2.1 : V)) *
          (((π γ : ↥L) : MulAut V) (p.2.2 : V)) := by
      rw [hmP, map_mul, map_mul]
    have hu : ((π γ : ↥L) : MulAut V) ((mP p : ↥U) : V) ∈ U := by
      rw [hq]
      exact mul_mem (mul_mem (hIU 0 hpa) (hIU 1 hpb)) (hZU hpz)
    refine ⟨hu, ?_⟩
    have : (⟨_, hu⟩ : ↥U) = mP (⟨_, hpa⟩, ⟨_, hpb⟩, ⟨_, hpz⟩) :=
      Subtype.ext (by show ((π γ : ↥L) : MulAut V) ((mP p : ↥U) : V) = _; rw [hq, hmP])
    rw [this, hF, hF, hF₀, hF₀]
    simp only
    rw [hfe 0 γ p.1 hpa, hfe 1 γ p.2.1 hpb]
  have hinvU : ∀ (γ : ↥(StatedSL 3 k)) (u : V), u ∈ U → ((π γ : ↥L) : MulAut V) u ∈ U :=
    fun γ u hu => (hFe γ ⟨u, hu⟩).1
  obtain ⟨Θ, hΘ⟩ := LRed5.exists_equiv_of_section hFs hFk hU hU' hZ hZ'
  have hΘrel : ∀ (γ : ↥(StatedSL 3 k)) (q : M × M),
      Θ (natAct (StatedSL 3 k) γ q.1, natAct (StatedSL 3 k) γ q.2) =
        (natAct (StatedSL 3 k) (α γ) (Θ q).1, natAct (StatedSL 3 k) (α γ) (Θ q).2) := by
    intro γ q
    obtain ⟨u, rfl⟩ := hFs q
    obtain ⟨hu, hFu⟩ := hFe γ u
    obtain ⟨hu', hFu'⟩ := hFe (α γ) ⟨s u, hU u u.2⟩
    have e1 : Θ (natAct (StatedSL 3 k) γ (F u).1, natAct (StatedSL 3 k) γ (F u).2) =
        F ⟨s (((π γ : ↥L) : MulAut V) (u : V)), hU _ hu⟩ := by
      rw [← hFu]
      exact hΘ ⟨_, hu⟩
    have e2 : (⟨s (((π γ : ↥L) : MulAut V) (u : V)), hU _ hu⟩ : ↥U) =
        ⟨((π (α γ) : ↥L) : MulAut V) (s (u : V)), hu'⟩ := by
      apply Subtype.ext
      show s (((π γ : ↥L) : MulAut V) (u : V)) = ((π (α γ) : ↥L) : MulAut V) (s (u : V))
      rw [hαπ γ]
      simp [MulAut.mul_apply]
    have e3 : F ⟨s (u : V), hU u u.2⟩ = Θ (F u) := (hΘ u).symm
    rw [e1, e2, hFu', e3]
  have key : ∀ Ψ : M →* M,
      (∀ (γ : ↥(StatedSL 3 k)) (m : M),
        Ψ (natAct (StatedSL 3 k) γ m) = natAct (StatedSL 3 k) (α γ) (Ψ m)) →
      (∃ x, Ψ x ≠ 1) →
      ∃ φ : (Fin 3 → k) → (Fin 3 → k), Function.Bijective φ ∧
        ∀ (γ : ↥(StatedSL 3 k)) (v : Fin 3 → k),
          φ (((γ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v) =
            ((α γ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ φ v := by
    intro Ψ hΨ ⟨x₀, hx₀⟩
    have hker : Ψ.ker = ⊥ := by
      rcases natAct_irreducible_stated Ψ.ker (fun γ x hx => by
          rw [MonoidHom.mem_ker] at hx ⊢
          rw [hΨ γ x, hx, FFC.natAct_one_right]) with h | h
      · exact h
      · exact absurd (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top x₀)) hx₀
    have hinj : Function.Injective Ψ := (MonoidHom.ker_eq_bot_iff Ψ).1 hker
    have hsurj : Function.Surjective Ψ := Finite.surjective_of_injective hinj
    have hbij : Function.Bijective Ψ := ⟨hinj, hsurj⟩
    refine ⟨fun v => Multiplicative.toAdd (Ψ (Multiplicative.ofAdd v)),
      Multiplicative.toAdd.bijective.comp (hbij.comp Multiplicative.ofAdd.bijective),
      fun γ v => ?_⟩
    have := hΨ γ (Multiplicative.ofAdd v)
    simp only [natAct, toAdd_ofAdd] at this
    show Multiplicative.toAdd (Ψ (Multiplicative.ofAdd
        (((γ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) *ᵥ v))) = _
    rw [this, toAdd_ofAdd]
  let Ψ₁ : M →* M := (MonoidHom.fst M M).comp (Θ.toMonoidHom.comp (MonoidHom.inl M M))
  let Ψ₂ : M →* M := (MonoidHom.snd M M).comp (Θ.toMonoidHom.comp (MonoidHom.inl M M))
  have hΨ₁ : ∀ (γ : ↥(StatedSL 3 k)) (m : M),
      Ψ₁ (natAct (StatedSL 3 k) γ m) = natAct (StatedSL 3 k) (α γ) (Ψ₁ m) := by
    intro γ m
    have := hΘrel γ (m, 1)
    simp only [FFC.natAct_one_right] at this
    exact congrArg Prod.fst this
  have hΨ₂ : ∀ (γ : ↥(StatedSL 3 k)) (m : M),
      Ψ₂ (natAct (StatedSL 3 k) γ m) = natAct (StatedSL 3 k) (α γ) (Ψ₂ m) := by
    intro γ m
    have := hΘrel γ (m, 1)
    simp only [FFC.natAct_one_right] at this
    exact congrArg Prod.snd this
  let x₀ : M := Multiplicative.ofAdd (Pi.single 0 1)
  have hx₀ : x₀ ≠ 1 := by
    intro h
    have := congrFun (congrArg Multiplicative.toAdd h) 0
    simp [x₀] at this
  have hne : Θ (x₀, 1) ≠ 1 := by
    intro h
    have h1 : (x₀, (1 : M)) = 1 := Θ.injective (h.trans (map_one Θ).symm)
    exact hx₀ (congrArg Prod.fst h1)
  by_cases h1 : Ψ₁ x₀ = 1
  · refine key Ψ₂ hΨ₂ ⟨x₀, fun h2 => hne ?_⟩
    exact Prod.ext h1 h2
  · exact key Ψ₁ hΨ₁ ⟨x₀, h1⟩

end CFSG.Quasithin.H13.L1232
