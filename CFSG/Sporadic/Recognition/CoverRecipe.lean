module

public import CFSG.Sporadic.Recognition.CoverTransfer
public import CFSG.Sporadic.Recognition.CoverTransferWords

public section

namespace CFSG.Sporadic.Recognition.CoverRecipe

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Open CFSG.Sporadic.Recognition.CoverTransfer
  CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.Bridge.TwoGen.Native Subgroup

@[expose] def natWord {m : ℕ} (w : List (Fin m × Bool)) : List (ℕ × Bool) :=
  w.map fun l => (l.1.val, l.2)

@[expose] def abLetter (z : ℤ) : Fin 2 × Bool :=
  (if z.natAbs = 1 then 0 else 1, decide (0 < z))

section Tables

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)] [FaithfulSMul G (Fin n)]
  {x y : G} {α αi β βi : CFSG.Sporadic.Th.Native.Table}

theorem lift_eq_one_of_relCheck (hn : n < 2 ^ 32) (hx : CFSG.Sporadic.Th.Rep n α x)
    (hxi : CFSG.Sporadic.Th.Rep n αi x⁻¹) (hy : CFSG.Sporadic.Th.Rep n β y)
    (hyi : CFSG.Sporadic.Th.Rep n βi y⁻¹) {ws : List (List (Fin 2 × Bool))}
    (h : relCheck n α αi β βi (ws.map natWord) = true) {w : List (Fin 2 × Bool)} (hw : w ∈ ws) :
    FreeGroup.lift (fun i : Fin 2 => img2 x y i.val) (FreeGroup.mk w) = 1 := by
  have h1 := wordProd_eq_one_of_relCheck hn hx hxi hy hyi h (natWord w)
    (List.mem_map_of_mem hw)
  exact (lift_mk_eq_wordProd (img2 x y) w).trans h1

theorem lift_eq_of_inv_mem (hn : n < 2 ^ 32) (hx : CFSG.Sporadic.Th.Rep n α x)
    (hxi : CFSG.Sporadic.Th.Rep n αi x⁻¹) (hy : CFSG.Sporadic.Th.Rep n β y)
    (hyi : CFSG.Sporadic.Th.Rep n βi y⁻¹) {ws : List (List (Fin 2 × Bool))}
    (h : relCheck n α αi β βi (ws.map natWord) = true) {u : List (Fin 2 × Bool)} {i : Fin 2}
    (hu : u ++ [(i, false)] ∈ ws) :
    FreeGroup.lift (fun j : Fin 2 => img2 x y j.val) (FreeGroup.mk u) = img2 x y i.val := by
  have h1 := wordProd_eq_one_of_relCheck hn hx hxi hy hyi h (natWord (u ++ [(i, false)]))
    (List.mem_map_of_mem hu)
  exact lift_mk_eq_of_wordProd (img2 x y) h1

end Tables

theorem closure_range_eq_top {G : Type*} [Group G] {m : ℕ} {gen : Fin m → G} {x₀ y₀ : G}
    (hxy : Subgroup.closure ({x₀, y₀} : Set G) = ⊤) {sA sB : List (Fin m × Bool)}
    (hA : x₀ = FreeGroup.lift gen (FreeGroup.mk sA))
    (hB : y₀ = FreeGroup.lift gen (FreeGroup.mk sB)) :
    Subgroup.closure (Set.range gen) = ⊤ := by
  have hmem : ∀ v : FreeGroup (Fin m),
      FreeGroup.lift gen v ∈ Subgroup.closure (Set.range gen) := by
    intro v
    induction v using FreeGroup.induction_on with
    | one => simp
    | of i =>
      rw [FreeGroup.lift_apply_of]
      exact Subgroup.subset_closure (Set.mem_range_self i)
    | inv_of i =>
      rw [map_inv, FreeGroup.lift_apply_of]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_range_self i))
    | mul _ _ h₁ h₂ => rw [map_mul]; exact Subgroup.mul_mem _ h₁ h₂
  rw [eq_top_iff, ← hxy, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · rw [hA]; exact hmem _
  · rw [hB]; exact hmem _

theorem card_PG_le_chain {m : ℕ} {ws : List (List (Fin m × Bool))} {S : List ℕ}
    {c₂ c₁ n₂ n₁ : ℕ} (h₂ : subsetCheckCC ws S c₂ n₂ = true)
    (h₁ : subsetCheckCC (restrictWords (subsetOf m S) ws) [] c₁ n₁ = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n₂ * n₁ := by
  obtain ⟨f1, c1⟩ := card_le_of_subsetCheckCC_nil _ h₁
  obtain ⟨f2, c2⟩ := card_le_of_subsetCheckCC ws S h₂
  exact ⟨f2, c2.trans (Nat.mul_le_mul_left _ c1)⟩

theorem card_PG_le_chain_short {m : ℕ} {ws : List (List (Fin m × Bool))} {S : List ℕ}
    {k c₂ c₁ n₂ n₁ : ℕ} (h₂ : subsetCheckShortCC ws S k c₂ n₂ = true)
    (h₁ : subsetCheckShortCC (restrictWords (subsetOf m S) ws) [] k c₁ n₁ = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n₂ * n₁ := by
  obtain ⟨f1, c1⟩ := card_PG_le_of_subsetCheckShortCC_nil _ h₁
  obtain ⟨f2, c2⟩ := card_le_of_subsetCheckShortCC ws S h₂
  exact ⟨f2, c2.trans (Nat.mul_le_mul_left _ c1)⟩

theorem card_presentedCover_le_chain {m : ℕ} (R : List (List (Fin m × Bool)))
    (cw : Fin m → List (Fin m × Bool)) {S : List ℕ} {k c₂ c₁ n₂ n₁ : ℕ}
    (h₂ : subsetCheckShortCC (coverWords R cw) S k c₂ n₂ = true)
    (h₁ : subsetCheckShortCC (restrictWords (subsetOf m S) (coverWords R cw)) [] k c₁ n₁ =
      true) :
    Finite (PresentedCover (wordSet R) fun i => FreeGroup.mk (cw i)) ∧
      Nat.card (PresentedCover (wordSet R) fun i => FreeGroup.mk (cw i)) ≤ n₂ * n₁ := by
  change Finite (PresentedGroup (coverRelators (wordSet R) fun i => FreeGroup.mk (cw i))) ∧
    Nat.card (PresentedGroup (coverRelators (wordSet R) fun i => FreeGroup.mk (cw i))) ≤ n₂ * n₁
  rw [coverRelators_wordSet]
  exact card_PG_le_chain_short h₂ h₁

theorem card_PG_le_chain₃ {m : ℕ} {ws : List (List (Fin m × Bool))} {S₁ S₂ : List ℕ}
    {c₃ c₂ c₁ n₃ n₂ n₁ : ℕ} (h₃ : subsetCheckCC ws S₁ c₃ n₃ = true)
    (h₂ : subsetCheckCC (restrictWords (subsetOf m S₁) ws) S₂ c₂ n₂ = true)
    (h₁ : subsetCheckCC (restrictWords (subsetOf (subsetOf m S₁).length S₂)
      (restrictWords (subsetOf m S₁) ws)) [] c₁ n₁ = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n₃ * (n₂ * n₁) := by
  obtain ⟨f1, c1⟩ := card_PG_le_chain h₂ h₁
  obtain ⟨f2, c2⟩ := card_le_of_subsetCheckCC ws S₁ h₃
  exact ⟨f2, c2.trans (Nat.mul_le_mul_left _ c1)⟩

theorem card_PG_le_chain₃_short {m : ℕ} {ws : List (List (Fin m × Bool))} {S₁ S₂ : List ℕ}
    {k c₃ c₂ c₁ n₃ n₂ n₁ : ℕ} (h₃ : subsetCheckShortCC ws S₁ k c₃ n₃ = true)
    (h₂ : subsetCheckShortCC (restrictWords (subsetOf m S₁) ws) S₂ k c₂ n₂ = true)
    (h₁ : subsetCheckShortCC (restrictWords (subsetOf (subsetOf m S₁).length S₂)
      (restrictWords (subsetOf m S₁) ws)) [] k c₁ n₁ = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n₃ * (n₂ * n₁) := by
  obtain ⟨f1, c1⟩ := card_PG_le_chain_short h₂ h₁
  obtain ⟨f2, c2⟩ := card_le_of_subsetCheckShortCC ws S₁ h₃
  exact ⟨f2, c2.trans (Nat.mul_le_mul_left _ c1)⟩

theorem card_presentedCover_le_chain₃ {m : ℕ} (R : List (List (Fin m × Bool)))
    (cw : Fin m → List (Fin m × Bool)) {S₁ S₂ : List ℕ} {k c₃ c₂ c₁ n₃ n₂ n₁ : ℕ}
    (h₃ : subsetCheckShortCC (coverWords R cw) S₁ k c₃ n₃ = true)
    (h₂ : subsetCheckShortCC (restrictWords (subsetOf m S₁) (coverWords R cw)) S₂ k c₂ n₂ = true)
    (h₁ : subsetCheckShortCC (restrictWords (subsetOf (subsetOf m S₁).length S₂)
      (restrictWords (subsetOf m S₁) (coverWords R cw))) [] k c₁ n₁ = true) :
    Finite (PresentedCover (wordSet R) fun i => FreeGroup.mk (cw i)) ∧
      Nat.card (PresentedCover (wordSet R) fun i => FreeGroup.mk (cw i)) ≤ n₃ * (n₂ * n₁) := by
  change Finite (PresentedGroup (coverRelators (wordSet R) fun i => FreeGroup.mk (cw i))) ∧
    Nat.card (PresentedGroup (coverRelators (wordSet R) fun i => FreeGroup.mk (cw i))) ≤
      n₃ * (n₂ * n₁)
  rw [coverRelators_wordSet]
  exact card_PG_le_chain₃_short h₃ h₂ h₁

section Multiplier

variable {X : Type} [Group X] {m : ℕ} {g : Fin m → X} {R : List (List (Fin m × Bool))}
  {cw : Fin m → List (Fin m × Bool)}

theorem card_griessHopfMultiplier_le_of_cover (hP : IsPresentation g (wordSet R))
    (hw : ∀ i, FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (cw i)) = g i) {p : ℕ}
    (hcov : Finite (PresentedCover (wordSet R) fun i => FreeGroup.mk (cw i)) ∧
      Nat.card (PresentedCover (wordSet R) fun i => FreeGroup.mk (cw i)) ≤ p * Nat.card X) :
    0 < Nat.card (griessHopfMultiplier X) ∧ Nat.card (griessHopfMultiplier X) ≤ p := by
  have := hcov.1
  have hc := card_presentedCover hP hw hwg
  have hpos : 0 < Nat.card (PresentedCover (wordSet R) fun i => FreeGroup.mk (cw i)) :=
    Nat.card_pos
  have hXpos : 0 < Nat.card X := by
    have : Finite X := Finite.of_surjective _ (coverMap_surjective hP hwg)
    exact Nat.card_pos
  have hle := hcov.2
  rw [hc, mul_comm] at hle
  refine ⟨?_, Nat.le_of_mul_le_mul_right hle hXpos⟩
  rw [hc] at hpos
  exact Nat.pos_of_mul_pos_left hpos

theorem card_ker_dvd_of_cover (hP : IsPresentation g (wordSet R))
    (hw : ∀ i, FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (cw i)) = g i) {p : ℕ}
    (hM : Nat.card (griessHopfMultiplier X) = p) {E : Type} [Group E] [Group.IsPerfect E]
    (q : E →* X) (hq : Function.Surjective q) (hker : q.ker ≤ center E) :
    Nat.card q.ker ∣ p := by
  obtain ⟨φ, hφ, hcomp⟩ := exists_surjective_lift (w := fun i => FreeGroup.mk (cw i)) hP hw hwg q hq
    hker
  have hmap : q.ker = (coverMap hP hwg).ker.map φ := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, rfl⟩ := hφ z
      refine ⟨y, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, ← hcomp, MonoidHom.comp_apply]
      exact hz
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hy
      rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hcomp]
      exact hy
  have h3 : Nat.card (coverMap hP hwg).ker = p := by
    rw [← Nat.card_congr (griessHopfMultiplierEquivKer hP hw hwg).toEquiv]
    exact hM
  have hdvd := Subgroup.card_map_dvd (coverMap hP hwg).ker φ
  rw [h3, ← hmap] at hdvd
  exact hdvd


theorem card_ker_dvd_multiplier (hP : IsPresentation g (wordSet R))
    (hw : ∀ i, FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (cw i)) = g i) {E : Type} [Group E]
    [Group.IsPerfect E] (q : E →* X) (hq : Function.Surjective q) (hker : q.ker ≤ center E) :
    Nat.card q.ker ∣ Nat.card (griessHopfMultiplier X) :=
  card_ker_dvd_of_cover hP hw hwg rfl q hq hker

theorem isPresentation_of_chain (hrels : ∀ r ∈ wordSet R, FreeGroup.lift g r = 1)
    (hgen : Subgroup.closure (Set.range g) = ⊤) {S : List ℕ} {c₂ c₁ n₂ n₁ : ℕ}
    (h₂ : subsetCheckCC R S c₂ n₂ = true)
    (h₁ : subsetCheckCC (restrictWords (subsetOf m S) R) [] c₁ n₁ = true)
    (hle : n₂ * n₁ ≤ Nat.card X) : IsPresentation g (wordSet R) := by
  obtain ⟨hfin, hcard⟩ := card_PG_le_chain h₂ h₁
  have : Finite (PresentedGroup (wordSet R)) := hfin
  exact IsPresentation.of_card_le hrels hgen (hcard.trans hle)

theorem card_griessHopfMultiplier_le_of_chains (hrels : ∀ r ∈ wordSet R, FreeGroup.lift g r = 1)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hw : ∀ i, FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (cw i)) = g i) {S : List ℕ}
    {c₂ c₁ c₄ c₃ k n₂ n₁ n₂' n₁' p : ℕ} (h₂ : subsetCheckCC R S c₂ n₂ = true)
    (h₁ : subsetCheckCC (restrictWords (subsetOf m S) R) [] c₁ n₁ = true)
    (h₄ : subsetCheckShortCC (coverWords R cw) S k c₄ n₂' = true)
    (h₃ : subsetCheckShortCC (restrictWords (subsetOf m S) (coverWords R cw)) [] k c₃ n₁' = true)
    (hX : n₂ * n₁ ≤ Nat.card X) (hp : n₂' * n₁' ≤ p * Nat.card X) :
    0 < Nat.card (griessHopfMultiplier X) ∧ Nat.card (griessHopfMultiplier X) ≤ p := by
  have hP := isPresentation_of_chain hrels hgen h₂ h₁ hX
  obtain ⟨hfin, hcard⟩ := card_presentedCover_le_chain R cw h₄ h₃
  exact card_griessHopfMultiplier_le_of_cover hP hw hwg ⟨hfin, hcard.trans hp⟩

theorem card_griessHopfMultiplier_eq_one_of_chains
    (hrels : ∀ r ∈ wordSet R, FreeGroup.lift g r = 1)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hw : ∀ i, FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (cw i)) = g i) {S : List ℕ}
    {c₂ c₁ c₄ c₃ k n₂ n₁ n₂' n₁' : ℕ} (h₂ : subsetCheckCC R S c₂ n₂ = true)
    (h₁ : subsetCheckCC (restrictWords (subsetOf m S) R) [] c₁ n₁ = true)
    (h₄ : subsetCheckShortCC (coverWords R cw) S k c₄ n₂' = true)
    (h₃ : subsetCheckShortCC (restrictWords (subsetOf m S) (coverWords R cw)) [] k c₃ n₁' = true)
    (hX : n₂ * n₁ ≤ Nat.card X) (hp : n₂' * n₁' ≤ Nat.card X) :
    Nat.card (griessHopfMultiplier X) = 1 := by
  obtain ⟨hpos, hle⟩ := card_griessHopfMultiplier_le_of_chains hrels hgen hw hwg h₂ h₁ h₄ h₃ hX
    (p := 1) (by rw [one_mul]; exact hp)
  omega

end Multiplier

@[expose] def centerQuotMap {S C : Type} [Group S] [Group C] (e : C ⧸ Subgroup.center C ≃* S) :
    C →* S :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center C))

theorem centerQuotMap_surjective {S C : Type} [Group S] [Group C]
    (e : C ⧸ Subgroup.center C ≃* S) : Function.Surjective (centerQuotMap e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem ker_centerQuotMap {S C : Type} [Group S] [Group C] (e : C ⧸ Subgroup.center C ≃* S) :
    (centerQuotMap e).ker = Subgroup.center C := by
  ext x
  rw [MonoidHom.mem_ker]
  change e (QuotientGroup.mk' (Subgroup.center C) x) = 1 ↔ _
  rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem card_center_dvd_of_cover {X : Type} [Group X] {m : ℕ} {g : Fin m → X}
    {R : List (List (Fin m × Bool))} {cw : Fin m → List (Fin m × Bool)}
    (hP : IsPresentation g (wordSet R))
    (hw : ∀ i, FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (cw i)) = g i) {p : ℕ}
    (hM : Nat.card (griessHopfMultiplier X) = p) {Q : Type} [Group Q] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* X) : Nat.card (Subgroup.center Q) ∣ p := by
  have := hQ
  have h := card_ker_dvd_of_cover hP hw hwg hM (centerQuotMap e) (centerQuotMap_surjective e)
    (le_of_eq (ker_centerQuotMap e))
  rwa [ker_centerQuotMap e] at h

theorem card_center_dvd_multiplier {X : Type} [Group X] {m : ℕ} {g : Fin m → X}
    {R : List (List (Fin m × Bool))} {cw : Fin m → List (Fin m × Bool)}
    (hP : IsPresentation g (wordSet R))
    (hw : ∀ i, FreeGroup.mk (cw i) ∈ commutator (FreeGroup (Fin m)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (cw i)) = g i) {Q : Type} [Group Q]
    (hQ : Group.IsPerfect Q) (e : Q ⧸ Subgroup.center Q ≃* X) :
    Nat.card (Subgroup.center Q) ∣ Nat.card (griessHopfMultiplier X) :=
  card_center_dvd_of_cover hP hw hwg rfl hQ e

end CFSG.Sporadic.Recognition.CoverRecipe
