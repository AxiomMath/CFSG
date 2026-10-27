module

public import CFSG.Assembly.GL83SuzukiModel
public import CFSG.Assembly.LargeEvenDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

noncomputable section

namespace MarkChev

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (S : (Fin r → ℤ) → Prop) (K : Type) [Field K]

abbrev Index : Type :=
  Fin r ⊕ {v : Fin r → ℤ // S v}

abbrev Space : Type :=
  Index S →₀ K

abbrev GLS : Type :=
  LinearMap.GeneralLinearGroup K (Space S K)

@[expose] def hVec (i : Fin r) : Space S K :=
  Finsupp.single (Sum.inl i) 1

open Classical in
@[expose] def rootVec (β : Fin r → ℤ) : Space S K :=
  if h : S β then Finsupp.single (Sum.inr ⟨β, h⟩) 1 else 0

@[expose] def stringUp (i : Fin r) (α : Fin r → ℤ) : ℕ :=
  sSup {k : ℕ | S (α + (k : ℤ) • Pi.single i 1)}

@[expose] def stringDown (i : Fin r) (α : Fin r → ℤ) : ℕ :=
  sSup {k : ℕ | S (α - (k : ℤ) • Pi.single i 1)}

open Classical in
@[expose] def xOp (i : Fin r) (c : K) : Module.End K (Space S K) :=
  Finsupp.linearCombination K fun b =>
    match b with
    | Sum.inl j => hVec S K j + (((A j i).natAbs : K) * c) • rootVec S K (Pi.single i 1)
    | Sum.inr α =>
      if α.1 = Pi.single i 1 then rootVec S K α.1
      else if α.1 = -Pi.single i 1 then
        rootVec S K α.1 + c • hVec S K i + c ^ 2 • rootVec S K (Pi.single i 1)
      else
        ∑ k ∈ Finset.range (stringUp S i α.1 + 1),
          (((stringDown S i α.1 + k).choose k : K) * c ^ k) •
            rootVec S K (α.1 + (k : ℤ) • Pi.single i 1)

open Classical in
@[expose] def yOp (i : Fin r) (c : K) : Module.End K (Space S K) :=
  Finsupp.linearCombination K fun b =>
    match b with
    | Sum.inl j => hVec S K j + (((A j i).natAbs : K) * c) • rootVec S K (-Pi.single i 1)
    | Sum.inr α =>
      if α.1 = -Pi.single i 1 then rootVec S K α.1
      else if α.1 = Pi.single i 1 then
        rootVec S K α.1 + c • hVec S K i + c ^ 2 • rootVec S K (-Pi.single i 1)
      else
        ∑ k ∈ Finset.range (stringDown S i α.1 + 1),
          (((stringUp S i α.1 + k).choose k : K) * c ^ k) •
            rootVec S K (α.1 - (k : ℤ) • Pi.single i 1)

@[expose] def chevGroup : Subgroup (GLS S K) :=
  Subgroup.closure {g | ∃ (i : Fin r) (c : K),
    (g : Module.End K (Space S K)) = xOp A S K i c ∨
      (g : Module.End K (Space S K)) = yOp A S K i c}

@[expose] def chevH (derived : Bool) : Subgroup (GLS S K) :=
  if derived then ⁅chevGroup A S K, chevGroup A S K⁆ else chevGroup A S K

@[expose] def entrywise (f : K → K) (hf : f 0 = 0) (g : Module.End K (Space S K)) :
    Module.End K (Space S K) :=
  Finsupp.linearCombination K fun b => Finsupp.mapRange f hf (g (Finsupp.single b 1))

@[expose] def diagramMap (ρ : Equiv.Perm (Fin r)) : Module.End K (Space S K) :=
  Finsupp.linearCombination K fun b =>
    match b with
    | Sum.inl i => hVec S K (ρ i)
    | Sum.inr α => rootVec S K (α.1 ∘ ρ.symm)

@[expose] def twistedF (ρ : Equiv.Perm (Fin r)) (n : ℕ) : Subgroup (GLS S K) :=
  Subgroup.closure {g | g ∈ chevGroup A S K ∧
    diagramMap S K ρ *
        entrywise S K (fun c => c ^ 2 ^ n) (zero_pow (pow_ne_zero n two_ne_zero))
          (g : Module.End K (Space S K)) =
      (g : Module.End K (Space S K)) * diagramMap S K ρ}

@[expose] def twistedH (ρ : Equiv.Perm (Fin r)) (n : ℕ) : Subgroup (GLS S K) :=
  ⁅twistedF A S K ρ n, twistedF A S K ρ n⁆

end MarkChev

@[expose] def MarkChev.twF4R (S : (Fin 4 → ℤ) → Prop) (a : ℕ) (K : Type) [Field K] :
    Subgroup (MarkChev.GLS S K × MarkChev.GLS S K) :=
  Subgroup.closure {gh | ∃ (i : Fin 4) (c : K),
    ((gh.1 : Module.End K _) = MarkChev.xOp LargeEvenCartanF4 S K i c ∧
        (gh.2 : Module.End K _) =
          MarkChev.xOp LargeEvenCartanF4 S K (LargeEvenRhoF4 i) (c ^ LargeEvenTwF4Exp a i)) ∨
      ((gh.1 : Module.End K _) = MarkChev.yOp LargeEvenCartanF4 S K i c ∧
        (gh.2 : Module.End K _) =
          MarkChev.yOp LargeEvenCartanF4 S K (LargeEvenRhoF4 i) (c ^ LargeEvenTwF4Exp a i))}

@[expose] def MarkChev.twF4F (S : (Fin 4 → ℤ) → Prop) (a : ℕ) (K : Type) [Field K] :
    Subgroup (MarkChev.GLS S K) :=
  MarkChev.chevGroup LargeEvenCartanF4 S K ⊓
    (MarkChev.twF4R S a K).comap ((MonoidHom.id _).prod (MonoidHom.id _))

@[expose] def MarkChev.twF4H (S : (Fin 4 → ℤ) → Prop) (a : ℕ) (K : Type) [Field K] :
    Subgroup (MarkChev.GLS S K) :=
  ⁅MarkChev.twF4F S a K, MarkChev.twF4F S a K⁆

section LargeEven

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K]

theorem largeEvenXOp_eq (i : Fin r) (c : K) :
    LargeEvenXOp A K i c = MarkChev.xOp A (LargeEvenIsRoot A) K i c := by
  unfold LargeEvenXOp MarkChev.xOp
  congr 1
  funext b
  cases b <;> rfl

theorem largeEvenYOp_eq (i : Fin r) (c : K) :
    LargeEvenYOp A K i c = MarkChev.yOp A (LargeEvenIsRoot A) K i c := by
  unfold LargeEvenYOp MarkChev.yOp
  congr 1
  funext b
  cases b <;> rfl

theorem largeEvenDiagramMap_eq (ρ : Equiv.Perm (Fin r)) :
    LargeEvenDiagramMap A K ρ = MarkChev.diagramMap (LargeEvenIsRoot A) K ρ := by
  unfold LargeEvenDiagramMap MarkChev.diagramMap
  congr 1
  funext b
  cases b <;> rfl

theorem largeEvenChevGroup_eq :
    LargeEvenChevGroup A K = MarkChev.chevGroup A (LargeEvenIsRoot A) K := by
  unfold LargeEvenChevGroup MarkChev.chevGroup
  simp only [largeEvenXOp_eq, largeEvenYOp_eq]

theorem largeEvenChevH_eq (d : Bool) :
    LargeEvenChevH A K d = MarkChev.chevH A (LargeEvenIsRoot A) K d := by
  unfold LargeEvenChevH MarkChev.chevH
  rw [largeEvenChevGroup_eq]

theorem largeEvenTwistedH_eq (ρ : Equiv.Perm (Fin r)) (n : ℕ) :
    LargeEvenTwistedH A K ρ n = MarkChev.twistedH A (LargeEvenIsRoot A) K ρ n := by
  unfold LargeEvenTwistedH MarkChev.twistedH MarkChev.twistedF
  simp only [largeEvenChevGroup_eq, largeEvenDiagramMap_eq]
  rfl

end LargeEven

theorem largeEvenTwF4H_eq (a : ℕ) (K : Type) [Field K] :
    LargeEvenTwF4H a K = MarkChev.twF4H (LargeEvenIsRoot LargeEvenCartanF4) a K := by
  unfold LargeEvenTwF4H LargeEvenTwF4Parent MarkChev.twF4H MarkChev.twF4F MarkChev.twF4R
  simp only [largeEvenChevGroup_eq, largeEvenXOp_eq, largeEvenYOp_eq]

section Blueprint

variable (τ : Tag) (K : Type) [Field K]

theorem largeEvenIsRoot_eq_isRoot : LargeEvenIsRoot τ.cartan = IsRoot τ := by
  funext v
  apply propext
  constructor
  · intro h
    induction h with
    | simple j => exact .basis j
    | reflect i _ ih => exact .reflect i ih
  · intro h
    induction h with
    | basis j => exact .simple j
    | reflect i _ ih => exact .reflect i ih

theorem markChev_rootVec_root (α : {v : Fin τ.rank → ℤ // IsRoot τ v}) :
    MarkChev.rootVec (IsRoot τ) K α.1 = Finsupp.single (Sum.inr α) 1 := by
  simp [MarkChev.rootVec, α.2]

theorem xOp_eq_markChev (i : Fin τ.rank) (c : K) :
    xOp τ K i c = MarkChev.xOp τ.cartan (IsRoot τ) K i c := by
  unfold xOp MarkChev.xOp
  congr 1
  funext b
  rcases b with j | α
  · rfl
  · dsimp only
    rw [markChev_rootVec_root]
    rfl

theorem yOp_eq_markChev (i : Fin τ.rank) (c : K) :
    yOp τ K i c = MarkChev.yOp τ.cartan (IsRoot τ) K i c := by
  unfold yOp MarkChev.yOp
  congr 1
  funext b
  rcases b with j | α
  · rfl
  · dsimp only
    rw [markChev_rootVec_root]
    rfl

theorem adjointGroup_eq_markChev :
    adjointGroup τ K = MarkChev.chevGroup τ.cartan (IsRoot τ) K := by
  unfold adjointGroup MarkChev.chevGroup
  simp only [xOp_eq_markChev, yOp_eq_markChev]

end Blueprint

section Twisted

variable (K : Type) [Field K]

theorem diagramMap_eq_markChev (t : TwistTag) :
    (diagramMap t K : Module.End K (RootModule t.tag K)) =
      MarkChev.diagramMap (IsRoot t.tag) K t.perm := by
  apply Finsupp.lhom_ext'
  intro b
  apply LinearMap.ext_ring
  rcases b with i | α
  · simp [diagramMap, MarkChev.diagramMap, MarkChev.hVec, labelPerm]
  · have h := α.2.permLattice t.cartan_perm
    simp [diagramMap, MarkChev.diagramMap, MarkChev.rootVec, labelPerm, permLattice] at h ⊢
    simp [h]

theorem entrywise_eq_markChev (t : TwistTag) (n : ℕ) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (g : Module.End K (MarkChev.Space (IsRoot t.tag) K)) :
    MarkChev.entrywise (IsRoot t.tag) K (fun c => c ^ 2 ^ n)
        (zero_pow (pow_ne_zero n two_ne_zero)) g = entrywise (τ := t.tag) σ g := by
  unfold MarkChev.entrywise entrywise
  congr 1
  funext b
  ext l
  simp [hσ]

theorem twistedF_eq_twistedFixedGroup (t : TwistTag) (n : ℕ) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    MarkChev.twistedF t.tag.cartan (IsRoot t.tag) K t.perm n = twistedFixedGroup t K σ := by
  rw [← Subgroup.closure_eq (twistedFixedGroup t K σ)]
  unfold MarkChev.twistedF
  congr 1
  ext g
  rw [Set.mem_ofPred_eq, ← adjointGroup_eq_markChev, ← diagramMap_eq_markChev,
    entrywise_eq_markChev K t n σ hσ]
  change _ ↔ g ∈ adjointGroup t.tag K ∧ twistHom t K σ g = g
  refine and_congr_right' ?_
  rw [Units.ext_iff, coe_twistHom, Units.mul_inv_eq_iff_eq_mul]

theorem twistedH_eq_commutator (t : TwistTag) (n : ℕ) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    MarkChev.twistedH t.tag.cartan (IsRoot t.tag) K t.perm n =
      ⁅twistedFixedGroup t K σ, twistedFixedGroup t K σ⁆ := by
  unfold MarkChev.twistedH
  rw [twistedF_eq_twistedFixedGroup K t n σ hσ]

theorem largeEvenTwF4Exp_eq (a : ℕ) :
    (fun i : Fin Tag.F4.rank => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)) =
      LargeEvenTwF4Exp a := by
  have h : ∀ i : Fin Tag.F4.rank, i ∈ reeF4Long ↔ i.val < 2 := by
    intro i
    fin_cases i <;> decide
  funext i
  unfold LargeEvenTwF4Exp
  exact if_congr (h i) rfl rfl

theorem twF4R_eq_reeRelationGroup (a : ℕ) :
    MarkChev.twF4R (IsRoot .F4) a K =
      reeRelationGroup .F4 K reeF4Perm
        (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)) := by
  rw [largeEvenTwF4Exp_eq]
  unfold MarkChev.twF4R reeRelationGroup
  simp only [xOp_eq_markChev, yOp_eq_markChev]
  rfl

theorem twF4H_eq_commutator (a : ℕ) :
    MarkChev.twF4H (IsRoot .F4) a K =
      ⁅reeFixedGroup .F4 K reeF4Perm (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)),
        reeFixedGroup .F4 K reeF4Perm (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1))⁆ := by
  have hF : MarkChev.twF4F (IsRoot .F4) a K =
      reeFixedGroup .F4 K reeF4Perm (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)) := by
    unfold MarkChev.twF4F reeFixedGroup
    rw [twF4R_eq_reeRelationGroup, adjointGroup_eq_markChev]
    rfl
  unfold MarkChev.twF4H
  rw [hF]
  rfl

end Twisted

section CenterQuot

theorem nonempty_centerQuot_congr {M : Type} [Group M] {H H' : Subgroup M} (h : H = H') :
    Nonempty (LargeEvenCenterQuot H ≃* LargeEvenCenterQuot H') := by
  subst h
  exact ⟨MulEquiv.refl _⟩

theorem nonempty_centerQuot_root {r : ℕ} {S S' : (Fin r → ℤ) → Prop} (h : S = S') (K : Type)
    [Field K] (H : (S : (Fin r → ℤ) → Prop) → Subgroup (MarkChev.GLS S K)) :
    Nonempty (LargeEvenCenterQuot (H S) ≃* LargeEvenCenterQuot (H S')) := by
  subst h
  exact ⟨MulEquiv.refl _⟩

variable (K : Type) [Field K]

theorem chevH_false_eq_adjointGroup (τ : Tag) :
    MarkChev.chevH τ.cartan (IsRoot τ) K false = adjointGroup τ K := by
  rw [adjointGroup_eq_markChev]
  rfl

theorem chevH_true_eq_commutator (τ : Tag) :
    MarkChev.chevH τ.cartan (IsRoot τ) K true = ⁅adjointGroup τ K, adjointGroup τ K⁆ := by
  rw [adjointGroup_eq_markChev]
  rfl

theorem centerQuot_chevH_equiv (τ : Tag) (d : Bool) :
    Nonempty (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K d) ≃*
      LargeEvenCenterQuot (MarkChev.chevH τ.cartan (IsRoot τ) K d)) := by
  obtain ⟨e₁⟩ := nonempty_centerQuot_congr (largeEvenChevH_eq τ.cartan K d)
  obtain ⟨e₂⟩ := nonempty_centerQuot_root (largeEvenIsRoot_eq_isRoot τ) K
    (fun S => MarkChev.chevH τ.cartan S K d)
  exact ⟨e₁.trans e₂⟩

theorem centerQuot_chevGroup_equiv (τ : Tag) :
    Nonempty (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false) ≃* AdjointQuotient τ K) := by
  obtain ⟨e₁⟩ := centerQuot_chevH_equiv K τ false
  obtain ⟨e₂⟩ := nonempty_centerQuot_congr (chevH_false_eq_adjointGroup K τ)
  exact ⟨e₁.trans e₂⟩

theorem centerQuot_commutator_chevGroup_equiv (τ : Tag) :
    Nonempty (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K true) ≃*
      DerivedCentralQuotient (adjointGroup τ K)) := by
  obtain ⟨e₁⟩ := centerQuot_chevH_equiv K τ true
  obtain ⟨e₂⟩ := nonempty_centerQuot_congr (chevH_true_eq_commutator K τ)
  exact ⟨e₁.trans e₂⟩

theorem centerQuot_twistedH_equiv (t : TwistTag) (n : ℕ) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) :
    Nonempty (LargeEvenCenterQuot (LargeEvenTwistedH t.tag.cartan K t.perm n) ≃*
      DerivedCentralQuotient (twistedFixedGroup t K σ)) := by
  obtain ⟨e₁⟩ := nonempty_centerQuot_congr (largeEvenTwistedH_eq t.tag.cartan K t.perm n)
  obtain ⟨e₂⟩ := nonempty_centerQuot_root (largeEvenIsRoot_eq_isRoot t.tag) K
    (fun S => MarkChev.twistedH t.tag.cartan S K t.perm n)
  obtain ⟨e₃⟩ := nonempty_centerQuot_congr (twistedH_eq_commutator K t n σ hσ)
  exact ⟨e₁.trans (e₂.trans e₃)⟩

theorem centerQuot_twF4H_equiv (a : ℕ) :
    Nonempty (LargeEvenCenterQuot (LargeEvenTwF4H a K) ≃*
      DerivedCentralQuotient (reeFixedGroup .F4 K reeF4Perm
        (fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)))) := by
  obtain ⟨e₁⟩ := nonempty_centerQuot_congr (largeEvenTwF4H_eq a K)
  obtain ⟨e₂⟩ := nonempty_centerQuot_root (r := 4) (largeEvenIsRoot_eq_isRoot .F4) K
    (fun S => MarkChev.twF4H S a K)
  obtain ⟨e₃⟩ := nonempty_centerQuot_congr (twF4H_eq_commutator K a)
  exact ⟨e₁.trans (e₂.trans e₃)⟩

end CenterQuot

theorem largeEvenSzGroup_eq (a : ℕ) (K : Type) [Field K] :
    LargeEvenSzGroup a K = suzukiGroup a K :=
  largeEvenSzGroup_eq_suzukiGroup a K

end

end CFSG.StandardType
