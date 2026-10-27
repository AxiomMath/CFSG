module

public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestCore
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley InndiagE6 RecipeFieldE6

open scoped commutatorElement

namespace InndiagCommRest

section Generic

theorem mem_commutator_top_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (E : X ≃* Y) {x : X}
    (h : E x ∈ commutator Y) : x ∈ commutator X := by
  rw [commutator_def, ← Subgroup.map_top_of_surjective E.toMonoidHom E.surjective,
    ← Subgroup.map_commutator] at h
  obtain ⟨y, hy, hxy⟩ := h
  rwa [E.injective hxy] at hy

theorem frob_conj_eq_sq {G : Type*} [Group G] {C : Subgroup G} (F : G →* G) (β : MulAut C)
    (hβ : ∀ c : C, (β c : G) = F c) {d : G} (hd : F d = d * d) (ψ : MulAut C)
    (hψ : ∀ c : C, (ψ c : G) = d * c * d⁻¹) : β * ψ * β⁻¹ = ψ * ψ := by
  refine MulEquiv.ext fun c => Subtype.ext ?_
  have h1 : F ((β⁻¹ c : C) : G) = c := by
    rw [← hβ, MulAut.apply_inv_self]
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hβ, hψ, map_mul, map_mul, map_inv,
    h1, hd, hψ, hψ]
  group

theorem mem_commutator_of_frob {G : Type*} [Group G] {C : Subgroup G} (F : G →* G)
    (β : MulAut C) (hβ : ∀ c : C, (β c : G) = F c) {d : G} (hd : F d = d * d) (ψ : MulAut C)
    (hψ : ∀ c : C, (ψ c : G) = d * c * d⁻¹) : ψ ∈ commutator (MulAut C) := by
  have h := frob_conj_eq_sq F β hβ hd ψ hψ
  have e : ψ = ⁅β, ψ⁆ := by
    rw [commutatorElement_def, h, mul_inv_cancel_right]
  rw [e]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem ggInndiagCommEq_chevID_of {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {K : Type} [Field K]
    {H : Subgroup (LargeEvenChevGL A K)} {F : Set (MulAut (LargeEvenCenterQuot H))}
    (hcomm : ∀ α β : MulAut (LargeEvenCenterQuot H),
      α * β * α⁻¹ * β⁻¹ ∈ LargeEvenChevIDImage A K H)
    (hdiag : ∀ (a : Fin r → Kˣ) (ψ : MulAut (LargeEvenCenterQuot H)),
      IsConjOn H ψ (TableB.diagHom A K a) →
        ψ ∈ commutator (MulAut (LargeEvenCenterQuot H))) :
    GGInndiagCommEq (LargeEvenCenterQuot H) (LargeEvenChevIDImage A K H) F := by
  show ggInndiag _ _ = ggInndiagComm _
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
  · rw [Subgroup.closure_le]
    intro φ hφ
    obtain ⟨g, hg, a, -, -, hφc⟩ := exists_isConjOn_of_mem_chevID hφ
    set g₀ : H := ⟨g, hg⟩
    have hψ : IsConjOn H ((MulAut.conj (LargeEvenCenterMk H g₀))⁻¹ * φ)
        (TableB.diagHom A K a) := by
      have h1 := isConjOn_inv (isConjOn_conj g₀) (fun h hh =>
        H.mul_mem (H.mul_mem (H.inv_mem hg) hh) hg)
      exact isConjOn_of_eq (isConjOn_mul h1 hφc) (by simp [g₀])
    have e : φ = MulAut.conj (LargeEvenCenterMk H g₀) *
        ((MulAut.conj (LargeEvenCenterMk H g₀))⁻¹ * φ) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, rfl⟩)
      (Subgroup.mem_sup_right (hdiag a _ hψ))
  · rw [Subgroup.commutator_le]
    intro α _ β _
    rw [commutatorElement_def]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure (hcomm α β))

end Generic

@[expose] def E6DiagCommOn (K : Type) [Field K] (S : (Fin TwistTag.E6.tag.rank → ℤ) → Prop) :
    Prop :=
  ∀ (a : Fin TwistTag.E6.tag.rank → Kˣ)
    (ψ : MulAut (LargeEvenCenterQuot (MarkChev.chevH TwistTag.E6.tag.cartan S K false))),
    IsConjOn (MarkChev.chevH TwistTag.E6.tag.cartan S K false) ψ (markDiagUnit S K a) →
      ψ ∈ commutator (MulAut (LargeEvenCenterQuot
        (MarkChev.chevH TwistTag.E6.tag.cartan S K false)))

theorem E6DiagCommOn.of_eq {K : Type} [Field K] {S S' : (Fin TwistTag.E6.tag.rank → ℤ) → Prop}
    (hS : S = S') (h : E6DiagCommOn K S) : E6DiagCommOn K S' :=
  hS ▸ h

@[expose] def TwE6DiagCommOn (K : Type) [Field K] (n : ℕ)
    (S : (Fin TwistTag.E6.tag.rank → ℤ) → Prop) : Prop :=
  ∀ (a : Fin TwistTag.E6.tag.rank → Kˣ)
    (ψ : MulAut (LargeEvenCenterQuot
      (MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n))),
    IsConjOn (MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n) ψ
      (markDiagUnit S K a) →
      ψ ∈ commutator (MulAut (LargeEvenCenterQuot
        (MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n)))

theorem TwE6DiagCommOn.of_eq {K : Type} [Field K] {n : ℕ}
    {S S' : (Fin TwistTag.E6.tag.rank → ℤ) → Prop} (hS : S = S') (h : TwE6DiagCommOn K n S) :
    TwE6DiagCommOn K n S' :=
  hS ▸ h

theorem units_map_frob_rootDiagUnit (K : Type) [Field K] [Finite K] [CharP K 2] (τ : Tag)
    (a : Fin τ.rank → Kˣ) :
    Units.map (entrywiseHom (frobeniusEquiv K 2).toRingHom) (rootDiagUnit τ a) =
      rootDiagUnit τ a * rootDiagUnit τ a := by
  rw [units_map_entrywiseHom_rootDiagUnit_ringEquiv, ← rootDiagUnit_mul]
  congr 1
  funext i
  apply Units.ext
  rw [Units.coe_map, Pi.mul_apply, Units.val_mul]
  change frobeniusEquiv K 2 (a i : K) = _
  rw [frobeniusEquiv_apply, frobenius_def, sq]


theorem e6DiagCommOn_isRoot (K : Type) [Field K] [Finite K] [CharP K 2] :
    E6DiagCommOn K (IsRoot TwistTag.E6.tag) := by
  unfold E6DiagCommOn
  rw [markDiagUnit_isRoot]
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot TwistTag.E6.tag) K),
      H = adjointGroup TwistTag.E6.tag K → ∀ (a : Fin TwistTag.E6.tag.rank → Kˣ)
        (ψ : MulAut (LargeEvenCenterQuot H)), IsConjOn H ψ (rootDiagUnit TwistTag.E6.tag a) →
          ψ ∈ commutator (MulAut (LargeEvenCenterQuot H)) from
    key _ (chevH_false_eq_adjointGroup K TwistTag.E6.tag)
  intro H hH
  subst hH
  intro a ψ hψ
  have hZ : Subgroup.center (adjointGroup TwistTag.E6.tag K) = ⊥ := center_adjointGroup_eq_bot
  refine mem_commutator_top_of_mulEquiv (MulAut.congr (centerQuotEquivOfBot hZ))
    (mem_commutator_of_frob (Units.map (entrywiseHom (frobeniusEquiv K 2).toRingHom))
      (entrywiseAdjointAut TwistTag.E6.tag (frobeniusEquiv K 2))
      (fun c => coe_entrywiseAdjointAut TwistTag.E6.tag (frobeniusEquiv K 2) c)
      (units_map_frob_rootDiagUnit K TwistTag.E6.tag a) _ fun h => ?_)
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, centerQuotEquivOfBot_symm,
    hψ.2 h (hψ.1 h h.2), centerQuotEquivOfBot_mk]

theorem twE6DiagCommOn_isRoot {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) : TwE6DiagCommOn K n (IsRoot TwistTag.E6.tag) := by
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hZ, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  have hC : MarkChev.twistedH TwistTag.E6.tag.cartan (IsRoot TwistTag.E6.tag) K TwistTag.E6.perm
      n = twistedE6RootGroup K σ := by
    rw [twistedH_eq_commutator K .E6 n σ.toRingHom hσ]
    exact (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ.toRingHom hσ).2.2.1
  unfold TwE6DiagCommOn
  rw [markDiagUnit_isRoot]
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot TwistTag.E6.tag) K),
      H = twistedE6RootGroup K σ → ∀ (a : Fin TwistTag.E6.tag.rank → Kˣ)
        (ψ : MulAut (LargeEvenCenterQuot H)), IsConjOn H ψ (rootDiagUnit TwistTag.E6.tag a) →
          ψ ∈ commutator (MulAut (LargeEvenCenterQuot H)) from key _ hC
  intro H hH
  subst hH
  intro a ψ hψ
  refine mem_commutator_top_of_mulEquiv (MulAut.congr (centerQuotEquivOfBot hZ))
    (mem_commutator_of_frob (Units.map (entrywiseHom (frobeniusEquiv K 2).toRingHom))
      (fieldActor σ (frobeniusEquiv K 2)) (fun c => coe_fieldActor σ (frobeniusEquiv K 2) c)
      (units_map_frob_rootDiagUnit K TwistTag.E6.tag a) _ fun h => ?_)
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, centerQuotEquivOfBot_symm,
    hψ.2 h (hψ.1 h h.2), centerQuotEquivOfBot_mk]

theorem ggInndiagCommEq_E6 (K : Type) [Field K] [Finite K] [CharP K 2] :
    GGInndiagCommEq (LargeEvenCenterQuot (LargeEvenChevH TwistTag.E6.tag.cartan K false))
      (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
        (LargeEvenChevH TwistTag.E6.tag.cartan K false))
      (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
        (LargeEvenChevH TwistTag.E6.tag.cartan K false)) := by
  obtain ⟨hZ, hNF⟩ := (commNFOn_isRoot_E6 K).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
  have hD := (e6DiagCommOn_isRoot K).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
  refine ggInndiagCommEq_chevID_of (fun α β => commutator_mem_chevID_of_commNF ?_ ?_ α β) ?_
  · rw [largeEvenChevH_eq]
    exact hZ
  · rw [largeEvenChevH_eq, diagHom_eq_markDiagUnit]
    exact hNF
  · rw [largeEvenChevH_eq, diagHom_eq_markDiagUnit]
    exact hD

theorem ggInndiagCommEq_twE6 {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    GGInndiagCommEq
      (LargeEvenCenterQuot (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n))
      (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n))
      (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)) := by
  obtain ⟨hZ, hNF⟩ :=
    (twistedCommNFOn_isRoot_E6 hn K hK).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
  have hD := (twE6DiagCommOn_isRoot hn K hK).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
  refine ggInndiagCommEq_chevID_of (fun α β => commutator_mem_chevID_of_commNF ?_ ?_ α β) ?_
  · rw [largeEvenTwistedH_eq]
    exact hZ
  · rw [largeEvenTwistedH_eq, diagHom_eq_markDiagUnit]
    exact hNF
  · rw [largeEvenTwistedH_eq, diagHom_eq_markDiagUnit]
    exact hD

end InndiagCommRest

open InndiagCommRest

section Labels


theorem largeEvenLabelAll_inndiagComm_E6 {lab : LargeEvenLabel} (ht : lab.tag = .E6) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  intro Q hQ
  exact recipeChevalley_and (P := LargeEvenSimpleGuard GGInndiagCommEq) (fun K _ _ hK _ _ => by
    have := charP_two_of_card hK
    exact ggInndiagCommEq_E6 K) hQ

theorem largeEvenLabelAll_inndiagComm_twE6 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twE6) : LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht
  subst ht
  intro Q hQ
  exact recipeTwisted_and (P := LargeEvenSimpleGuard GGInndiagCommEq)
    (fun K _ _ hK _ _ => ggInndiagCommEq_twE6 hn K hK) hQ

end Labels

end CFSG.StandardType

end
