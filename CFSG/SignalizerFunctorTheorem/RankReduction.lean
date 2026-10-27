module

public import CFSG.SignalizerFunctorTheorem.Basic
public import CFSG.SignalizerFunctorTheorem.ElementaryAbelian

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem

variable {G : Type*} [Group G] [Finite G]

@[expose] def RankOneOracle (p : ℕ) (A : Subgroup G) (P : Subgroup G → Prop) : Prop :=
  ∀ F ≤ A, p ^ 3 ≤ Nat.card F → ∀ Φ : Subgroup G → Subgroup G, IsSignalizerFunctor p 1 F Φ →
    (∀ R ∈ signalizerFunctorEk p 1 F, P (Φ R)) → IsComplete p 1 F Φ ∧ P (completion p 1 F Φ)

@[expose] def lowerFunctor (p k : ℕ) (A : Subgroup G) (Θ : Subgroup G → Subgroup G)
    (E : Subgroup G) : Subgroup G :=
  ⨆ S ∈ {S | S ∈ signalizerFunctorEk p (k + 1) A ∧ E ≤ S}, Θ S

omit [Finite G] in
theorem inf_eq_bot_of_le_right {E F R : Subgroup G} (hdisj : E ⊓ F = ⊥) (hRF : R ≤ F) :
    E ⊓ R = ⊥ := by
  rw [eq_bot_iff, ← hdisj]
  exact inf_le_inf_left E hRF

@[expose] def sliceFunctor (Θ : Subgroup G → Subgroup G) (E R : Subgroup G) : Subgroup G :=
  Θ (E ⊔ R)

omit [Finite G] in
theorem le_lowerFunctor {p k : ℕ} {A : Subgroup G} {Θ : Subgroup G → Subgroup G}
    {E S : Subgroup G} (hS : S ∈ signalizerFunctorEk p (k + 1) A) (hES : E ≤ S) :
    Θ S ≤ lowerFunctor p k A Θ E :=
  le_iSup₂_of_le S ⟨hS, hES⟩ le_rfl

theorem slice_isSignalizerFunctor {p k : ℕ} {A E F : Subgroup G}
    {Θ : Subgroup G → Subgroup G} (hA : IsElemAbelian p A) (hΘ : IsSignalizerFunctor p (k + 1) A Θ)
    (hE : E ∈ signalizerFunctorEk p k A) (hF : F ≤ A) (hdisj : E ⊓ F = ⊥) :
    IsSignalizerFunctor p 1 F (sliceFunctor Θ E) := by
  have member : ∀ R ∈ signalizerFunctorEk p 1 F, E ⊔ R ∈ signalizerFunctorEk p (k + 1) A :=
    fun R hR => sup_mem_Ek_succ hA hE (mem_Ek_of_le hF hR) (inf_eq_bot_of_le_right hdisj hR.1)
  refine ⟨fun R hR => ?_, fun R hR => hΘ.coprime _ (member R hR),
    fun R hR => hF.trans (hΘ.normalized _ (member R hR)), fun R hR R' hR' => ?_⟩
  · exact (hΘ.central _ (member R hR)).trans
      (Subgroup.centralizer_le (by exact_mod_cast (le_sup_right : R ≤ E ⊔ R)))
  · intro x hx
    have hxE : x ∈ Subgroup.centralizer (E : Set G) :=
      Subgroup.centralizer_le (by exact_mod_cast (le_sup_left : E ≤ E ⊔ R))
        (hΘ.central _ (member R hR) hx.1)
    have hx' : x ∈ Subgroup.centralizer ((E ⊔ R' : Subgroup G) : Set G) := by
      rw [centralizer_sup]
      exact ⟨hxE, hx.2⟩
    exact hΘ.balanced _ (member R hR) _ (member R' hR') ⟨hx.1, hx'⟩

theorem completion_slice {p k : ℕ} (hp : p.Prime) {A E F : Subgroup G}
    {Θ : Subgroup G → Subgroup G} (hA : IsElemAbelian p A) (hE : E ∈ signalizerFunctorEk p k A)
    (hF : F ≤ A) (hdisj : E ⊓ F = ⊥) (hsup : E ⊔ F = A) :
    completion p 1 F (sliceFunctor Θ E) = lowerFunctor p k A Θ E := by
  apply le_antisymm
  · refine completion_le fun R hR => ?_
    change Θ (E ⊔ R) ≤ lowerFunctor p k A Θ E
    exact le_lowerFunctor (Θ := Θ)
      (sup_mem_Ek_succ hA hE (mem_Ek_of_le hF hR) (inf_eq_bot_of_le_right hdisj hR.1))
      le_sup_left
  · refine iSup₂_le fun S hS => ?_
    obtain ⟨hSF, hSeq⟩ := inf_complement_mem_E1 hp hA hE hF hdisj hsup hS.1 hS.2
    have h := le_completion (Θ := sliceFunctor Θ E) hSF
    rwa [sliceFunctor, hSeq] at h

theorem lowerFunctor_inf_centralizer {p k : ℕ} (hp : p.Prime) {A : Subgroup G}
    {P : Subgroup G → Prop} {Θ : Subgroup G → Subgroup G} (hA : IsElemAbelian p A)
    (hlarge : p ^ (k + 3) ≤ Nat.card A) (oracle : RankOneOracle p A P)
    (hΘ : IsSignalizerFunctor p (k + 1) A Θ) (hP : ∀ S ∈ signalizerFunctorEk p (k + 1) A, P (Θ S))
    {E R : Subgroup G} (hE : E ∈ signalizerFunctorEk p k A) (hR : R ∈ signalizerFunctorEk p 1 A)
    (hdisj : E ⊓ R = ⊥) :
    lowerFunctor p k A Θ E ⊓ Subgroup.centralizer (R : Set G) = Θ (E ⊔ R) := by
  obtain ⟨F, hFA, hRF, hEF, hsup⟩ := exists_complement_containing hp hA hE.1 hR.1 hdisj
  have hslice := slice_isSignalizerFunctor hA hΘ hE hFA hEF
  have hsliceP : ∀ R' ∈ signalizerFunctorEk p 1 F, P (sliceFunctor Θ E R') := fun R' hR' =>
    hP _ (sup_mem_Ek_succ hA hE (mem_Ek_of_le hFA hR') (inf_eq_bot_of_le_right hEF hR'.1))
  have complete := (oracle F hFA (complement_large hp hA hE hFA hEF hsup hlarge) _ hslice
    hsliceP).1
  have h := complete.2 R ⟨hRF, hR.2⟩
  rwa [completion_slice hp hA hE hFA hEF hsup] at h

theorem lowerFunctor_coprime_and {p k : ℕ} (hp : p.Prime) {A : Subgroup G}
    {P : Subgroup G → Prop} {Θ : Subgroup G → Subgroup G} (hA : IsElemAbelian p A)
    (hlarge : p ^ (k + 3) ≤ Nat.card A) (oracle : RankOneOracle p A P)
    (hΘ : IsSignalizerFunctor p (k + 1) A Θ) (hP : ∀ S ∈ signalizerFunctorEk p (k + 1) A, P (Θ S))
    {E : Subgroup G} (hE : E ∈ signalizerFunctorEk p k A) :
    Nat.Coprime p (Nat.card (lowerFunctor p k A Θ E)) ∧ P (lowerFunctor p k A Θ E) := by
  obtain ⟨F, hFA, -, hEF, hsup⟩ := exists_complement_containing hp hA hE.1 bot_le (inf_bot_eq E)
  have hslice := slice_isSignalizerFunctor hA hΘ hE hFA hEF
  have hsliceP : ∀ R' ∈ signalizerFunctorEk p 1 F, P (sliceFunctor Θ E R') := fun R' hR' =>
    hP _ (sup_mem_Ek_succ hA hE (mem_Ek_of_le hFA hR') (inf_eq_bot_of_le_right hEF hR'.1))
  obtain ⟨⟨hcop, -⟩, hPc⟩ :=
    oracle F hFA (complement_large hp hA hE hFA hEF hsup hlarge) _ hslice hsliceP
  rw [completion_slice hp hA hE hFA hEF hsup] at hcop hPc
  exact ⟨hcop, hPc⟩

theorem lowerFunctor_isSignalizerFunctor {p k : ℕ} (hp : p.Prime) {A : Subgroup G}
    {P : Subgroup G → Prop} {Θ : Subgroup G → Subgroup G} (hA : IsElemAbelian p A)
    (hlarge : p ^ (k + 3) ≤ Nat.card A) (oracle : RankOneOracle p A P)
    (hΘ : IsSignalizerFunctor p (k + 1) A Θ) (hP : ∀ S ∈ signalizerFunctorEk p (k + 1) A, P (Θ S)) :
    IsSignalizerFunctor p k A (lowerFunctor p k A Θ) := by
  have central : ∀ E ∈ signalizerFunctorEk p k A,
      lowerFunctor p k A Θ E ≤ Subgroup.centralizer (E : Set G) := fun E _ =>
    iSup₂_le fun S hS => (hΘ.central S hS.1).trans
      (Subgroup.centralizer_le (by exact_mod_cast hS.2))
  refine ⟨central, fun E hE => (lowerFunctor_coprime_and hp hA hlarge oracle hΘ hP hE).1,
    fun E _ => CFSG.SignalizerFunctor.Helpers.normalizer_biSup_of_le A _ Θ
      fun S hS => hΘ.normalized S hS.1, fun E hE E' hE' => ?_⟩
  by_cases hne : E = E'
  · subst hne
    exact inf_le_left
  obtain ⟨R, hR, hRE', hER⟩ := exists_rankOne_disjoint_of_ne hp hA hE hE' hne
  obtain ⟨R', hR', hR'E, hE'R'⟩ := exists_rankOne_disjoint_of_ne hp hA hE' hE (Ne.symm hne)
  intro x hx
  have hxR : x ∈ Subgroup.centralizer (R : Set G) :=
    Subgroup.centralizer_le (by exact_mod_cast hRE') hx.2
  have hxΘ : x ∈ Θ (E ⊔ R) := by
    rw [← lowerFunctor_inf_centralizer hp hA hlarge oracle hΘ hP hE hR hER]
    exact ⟨hx.1, hxR⟩
  have hxE : x ∈ Subgroup.centralizer (E : Set G) := central E hE hx.1
  have hxR' : x ∈ Subgroup.centralizer ((E' ⊔ R' : Subgroup G) : Set G) := by
    rw [centralizer_sup]
    exact ⟨hx.2, Subgroup.centralizer_le (by exact_mod_cast hR'E) hxE⟩
  have hbal := hΘ.balanced _ (sup_mem_Ek_succ hA hE hR hER) _
    (sup_mem_Ek_succ hA hE' hR' hE'R') ⟨hxΘ, hxR'⟩
  exact le_lowerFunctor (sup_mem_Ek_succ hA hE' hR' hE'R') le_sup_left hbal

theorem completion_lowerFunctor {p k : ℕ} (hp : p.Prime) {A : Subgroup G}
    {Θ : Subgroup G → Subgroup G} (hA : IsElemAbelian p A) :
    completion p k A (lowerFunctor p k A Θ) = completion p (k + 1) A Θ := by
  apply le_antisymm
  · exact completion_le fun E _ => iSup₂_le fun S hS => le_completion hS.1
  · refine completion_le fun S hS => ?_
    obtain ⟨E, hE, hES, -⟩ := exists_hyperplane_decomposition hp hA hS
    exact (le_lowerFunctor hS hES).trans (le_completion hE)

theorem isComplete_of_rankOneOracle {p : ℕ} (hp : p.Prime) {A : Subgroup G}
    (hA : IsElemAbelian p A) {P : Subgroup G → Prop} (oracle : RankOneOracle p A P) :
    ∀ k : ℕ, 1 ≤ k → p ^ (k + 2) ≤ Nat.card A → ∀ Θ : Subgroup G → Subgroup G,
      IsSignalizerFunctor p k A Θ → (∀ S ∈ signalizerFunctorEk p k A, P (Θ S)) →
      IsComplete p k A Θ ∧ P (completion p k A Θ) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact fun hlarge Θ hΘ hP => oracle A le_rfl hlarge Θ hΘ hP
  | succ k hk ih =>
    intro hlarge Θ hΘ hP
    have hlarge' : p ^ (k + 2) ≤ Nat.card A :=
      (Nat.pow_le_pow_right hp.pos (by omega)).trans hlarge
    have hΨ := lowerFunctor_isSignalizerFunctor hp hA hlarge oracle hΘ hP
    have hΨP : ∀ E ∈ signalizerFunctorEk p k A, P (lowerFunctor p k A Θ E) := fun E hE =>
      (lowerFunctor_coprime_and hp hA hlarge oracle hΘ hP hE).2
    obtain ⟨⟨hcop, hcent⟩, hPW⟩ := ih hlarge' _ hΨ hΨP
    rw [completion_lowerFunctor hp hA] at hcop hcent hPW
    refine ⟨⟨hcop, fun S hS => ?_⟩, hPW⟩
    obtain ⟨E, hE, -, R, hR, -, hER, rfl⟩ := exists_hyperplane_decomposition hp hA hS
    rw [centralizer_sup, ← inf_assoc, hcent E hE,
      lowerFunctor_inf_centralizer hp hA hlarge oracle hΘ hP hE hR hER]

end CFSG.SignalizerFunctorTheorem
