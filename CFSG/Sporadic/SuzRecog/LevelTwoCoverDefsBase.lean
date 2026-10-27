
module

public import CFSG.Sporadic.SuzRecog.LevelTwoComplex
public import CFSG.Sporadic.SuzRecog.LevelTwoCoverElim
import CFSG.Certificates.Kernel.RankElimSound

public section

namespace CFSG.Sporadic.SuzRecog.LevelTwoCover

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.LevelTwoData
  CFSG.Sporadic.SuzRecog.LevelTwoCoverData CFSG.Sporadic.SuzRecog.ElimCert
  CFSG.Sporadic.SuzRecog.LevelTwo

attribute [local irreducible] nbr volt nbrC vtab vtabs aPts wPts trips aIdx vIdx cells p1 cellReps
  shift deck

theorem nbr_of_ge {x : ℕ} (hx : 2835 ≤ x) : nbr[x]! = #[] := by
  by_cases hx' : x < 2997
  · unfold nbr
    rw [CFSG.ComponentClassification.AS81.SuzB0.getElem!_ofFn' _ hx']
    simp only [show ¬ x < 2835 by omega, ↓reduceIte]
  · unfold nbr
    rw [getElem!_neg _ x (by simpa using hx')]
    rfl

theorem occB_nbr_of_ge {x : ℕ} (hx : 2835 ≤ x) (y : ℕ) : occB nbr[x]! y = false := by
  rw [nbr_of_ge hx]
  rfl

@[expose] def pr (u : Fin 8991) : Fin 2997 := ⟨u.1 % 2997, Nat.mod_lt _ (by norm_num)⟩

theorem nbrC_eq {u : ℕ} (hu : u < 8991) : nbrC[u]! = coverList nbr volt u := by
  unfold nbrC coverLists
  exact CFSG.ComponentClassification.AS81.SuzB0.getElem!_ofFn' _ hu

theorem nbrC_get {u : ℕ} (hu : u < 8991) (hx : u % 2997 < 2835) {k : ℕ} (hk : k < 36) :
    (nbrC[u]!)[k]! =
      (nbr[u % 2997]!)[k]! + 2997 * ((u / 2997 + volt[36 * (u % 2997) + k]!) % 3) := by
  rw [nbrC_eq hu]
  simp only [coverList, hx, ↓reduceIte]
  exact CFSG.ComponentClassification.AS81.SuzB0.getElem!_ofFn' _ hk

theorem nbrC_size {u : ℕ} (hu : u < 8991) (hx : u % 2997 < 2835) : (nbrC[u]!).size = 36 := by
  rw [nbrC_eq hu]
  simp only [coverList, hx, ↓reduceIte, Array.size_ofFn]

theorem nbrC_of_ge {u : ℕ} (hu : u < 8991) (hx : 2835 ≤ u % 2997) : nbrC[u]! = #[] := by
  rw [nbrC_eq hu]
  simp only [coverList, show ¬ u % 2997 < 2835 by omega, ↓reduceIte]

theorem occB_nbrC_of_ge {u : ℕ} (hu : u < 8991) (hx : 2835 ≤ u % 2997) (w : ℕ) :
    occB nbrC[u]! w = false := by
  rw [nbrC_of_ge hu hx]
  rfl

abbrev Γc : SimpleGraph (Fin 8991) := nbrGraph 8991 nbrC

theorem adjC_iff_of_ge {u w : Fin 8991} (hx : 2835 ≤ u.1 % 2997) :
    Γc.Adj u w ↔ w.1 % 2997 < 2835 ∧ ∃ k < 36, (nbrC[w.1]!)[k]! = u.1 := by
  constructor
  · rintro ⟨-, h | h⟩
    · rw [occB_nbrC_of_ge u.2 hx] at h
      exact absurd h (by simp)
    · by_cases hw : w.1 % 2997 < 2835
      · obtain ⟨k, hk, e⟩ := occB_iff.1 h
        rw [nbrC_size w.2 hw] at hk
        exact ⟨hw, k, hk, e⟩
      · rw [occB_nbrC_of_ge w.2 (by omega)] at h
        exact absurd h (by simp)
  · rintro ⟨hw, k, hk, e⟩
    refine ⟨fun h => by rw [h] at hx; omega, Or.inr (occB_iff.2 ⟨k, ?_, e⟩)⟩
    rw [nbrC_size w.2 hw]
    exact hk

theorem eq_of_adj_lift {V W : Type*} {G : SimpleGraph V} (hconn : G.Preconnected) (pr : V → W)
    (hinj : ∀ {u w₁ w₂ : V}, G.Adj u w₁ → G.Adj u w₂ → pr w₁ = pr w₂ → w₁ = w₂)
    {f g : V → V} (hf : ∀ {a b : V}, G.Adj a b → G.Adj (f a) (f b))
    (hg : ∀ {a b : V}, G.Adj a b → G.Adj (g a) (g b)) (hpr : ∀ u, pr (f u) = pr (g u))
    {u₀ : V} (h0 : f u₀ = g u₀) : f = g := by
  funext u
  obtain ⟨p⟩ := hconn u₀ u
  induction p with
  | nil => exact h0
  | cons hadj p ih => exact ih (hinj (hf hadj) (h0 ▸ hg hadj) (hpr _))

@[expose] def deck : Equiv.Perm (Fin 8991) := Equiv.addRight 2997

theorem deck_val (u : Fin 8991) : (deck u).1 = (u.1 + 2997) % 8991 := by
  simp [deck, Fin.val_add]

theorem pr_deck (u : Fin 8991) : pr (deck u) = pr u := by
  apply Fin.ext
  show (deck u).1 % 2997 = u.1 % 2997
  rw [deck_val]
  have := u.2
  omega

theorem deck_cube : deck ^ 3 = 1 := by
  ext u
  simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, deck_val]
  have := u.2
  omega

theorem eq_or_deck {u w : Fin 8991} (h : pr w = pr u) : w = u ∨ w = deck u ∨ w = deck (deck u) := by
  have h' : w.1 % 2997 = u.1 % 2997 := congrArg Fin.val h
  have := u.2
  have := w.2
  have e1 := deck_val u
  have e2 := deck_val (deck u)
  rw [e1] at e2
  rcases (by omega : w.1 = u.1 ∨ w.1 = (u.1 + 2997) % 8991 ∨
      w.1 = ((u.1 + 2997) % 8991 + 2997) % 8991) with e | e | e
  · exact Or.inl (Fin.ext e)
  · exact Or.inr (Or.inl (Fin.ext (e.trans e1.symm)))
  · exact Or.inr (Or.inr (Fin.ext (e.trans e2.symm)))

theorem rep_deck : Rep 8991 deckArr deck := fun x => by
  unfold deckArr
  rw [CFSG.ComponentClassification.AS81.SuzB0.getElem!_ofFn' _ x.2, deck_val]

theorem presAdj_spec {nb : Array (Array ℕ)} {L : Array ℕ} {σ : Equiv.Perm (Fin 8991)}
    (hL : Rep 8991 L σ) (h : presAdj nb L = true) {a b : Fin 8991}
    (hab : (nbrGraph 8991 nb).Adj a b) : (nbrGraph 8991 nb).Adj (σ a) (σ b) := by
  obtain ⟨-, h1 | h1⟩ := hab
  · obtain ⟨k, hk, e⟩ := occB_iff.1 h1
    have : adjB nb L[a.1]! L[(nb[a.1]!)[k]!]! = true := allLt_spec (allLt_spec h a.2) hk
    rw [e, hL a, hL b] at this
    exact nbrGraph_adj_iff.2 this
  · obtain ⟨k, hk, e⟩ := occB_iff.1 h1
    have : adjB nb L[b.1]! L[(nb[b.1]!)[k]!]! = true := allLt_spec (allLt_spec h b.2) hk
    rw [e, hL a, hL b] at this
    exact (nbrGraph_adj_iff.2 this).symm

@[expose] noncomputable def liftP (s : ℕ) : Equiv.Perm (Fin 8991) := permC 8991 (liftArr s)

theorem liftArr_get {s u : ℕ} (hu : u < 8991) :
    (liftArr s)[u]! = (vtab s)[u % 2997]! + 2997 * ((u / 2997 + (shift s)[u % 2997]!) % 3) := by
  unfold liftArr liftOf
  exact CFSG.ComponentClassification.AS81.SuzB0.getElem!_ofFn' _ hu

@[expose] noncomputable def xt (s : ℕ) : Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991) :=
  (permC 1782 gens[s]!, liftP s)

@[expose] noncomputable def F : Subgroup (Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991)) :=
  Subgroup.closure {xt 0, xt 1}

theorem xt_mem {s : ℕ} (hs : s < 2) : xt s ∈ F := by
  interval_cases s
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem F_induction {P : Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991) → Prop} (h0 : P (xt 0))
    (h1 : P (xt 1)) (hone : P 1) (hmul : ∀ a b, P a → P b → P (a * b))
    {g : Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991)} (hg : g ∈ F) : P g := by
  have hg' : g ∈ (F.toSubmonoid : Submonoid (Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991))) := hg
  rw [F, Subgroup.closure_toSubmonoid_of_finite] at hg'
  clear hg
  induction hg' using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact h0
    · rw [Set.mem_singleton_iff] at hx; exact hx ▸ h1
  | one => exact hone
  | mul a b _ _ ha hb => exact hmul a b ha hb

theorem fst_mem_xGroup {g : Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991)} (hg : g ∈ F) :
    g.1 ∈ xGroup := by
  have hle : F ≤ xGroup.prod ⊤ := (Subgroup.closure_le _).2 (Set.pair_subset_iff.2
    ⟨Subgroup.mem_prod.2 ⟨gens_mem_xGroup (by norm_num), Subgroup.mem_top _⟩,
      Subgroup.mem_prod.2 ⟨gens_mem_xGroup (by norm_num), Subgroup.mem_top _⟩⟩)
  exact (Subgroup.mem_prod.1 (hle hg)).1

noncomputable instance instMulActionF : MulAction F (Fin 8991) :=
  MulAction.compHom (Fin 8991) ((MonoidHom.snd _ _).comp F.subtype)

theorem smul_def (g : F) (u : Fin 8991) :
    g • u = (g : Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991)).2 u :=
  rfl

@[expose] noncomputable def projX : F →* xGroup where
  toFun g := ⟨(g : Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991)).1, fst_mem_xGroup g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem coe_projX (g : F) :
    ((projX g : xGroup) : Equiv.Perm (Fin 1782)) =
      (g : Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991)).1 :=
  rfl

theorem projX_surjective : Function.Surjective projX := by
  intro h
  refine xGroup_elt_induction (P := fun h => ∃ g, projX g = h)
    ⟨⟨xt 0, xt_mem (by norm_num)⟩, rfl⟩ ⟨⟨xt 1, xt_mem (by norm_num)⟩, rfl⟩ ⟨1, map_one _⟩
    ?_ h
  rintro a b ⟨g₁, rfl⟩ ⟨g₂, rfl⟩
  exact ⟨g₁ * g₂, map_mul _ _ _⟩

@[expose] noncomputable def proj :
    F →* Model.Crho1 :=
  (MulEquiv.subgroupCongr xGroup_eq_Crho1).toMonoidHom.comp projX

theorem coe_proj
    (g : F) :
    ((proj g : Model.Crho1) : Equiv.Perm (Fin 1782)) =
      (g : Equiv.Perm (Fin 1782) × Equiv.Perm (Fin 8991)).1 :=
  rfl

theorem proj_surjective :
    Function.Surjective proj :=
  (MulEquiv.subgroupCongr xGroup_eq_Crho1).surjective.comp projX_surjective

@[expose] def pt : Fin 8991 := 0

theorem pr_pt : pr pt = pV := rfl

end CFSG.Sporadic.SuzRecog.LevelTwoCover
