module

public import CFSG.Quasithin.Background.FLc3Core
public import CFSG.Quasithin.Background.FLc2Cases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def ExclConcl {V : Type} [CommGroup V] (Ls : Subgroup (MulAut V)) (UL' : Subgroup V) : Prop :=
  ∃ (n : ℕ) (I I' : Set ℕ) (ρ : SLt n →* MulAut V), 3 ≤ n ∧ (∀ g, ρ g ∈ Ls) ∧ (∀ k ∈ Ls, ∃ g, ρ g = k) ∧
    UL' ≠ ⊥ ∧ I ⊆ I' ∧ (∀ i ∈ I', IsNode n i) ∧ (∃ i ∈ I', n - i ∉ I') ∧
    (∀ h : SLt n, ∀ v ∈ UL', (∀ s ∈ Ut n, ρ (h * s * h⁻¹) v = v) → ∀ x ∈ QI n I, ρ (h * x * h⁻¹) v = v) ∧
    (Function.Injective ρ → ∀ h : SLt n, ∀ A'' : Subgroup (SLt n), A'' ≤ Ut n →
      (∀ y ∈ A'', ∀ i j : Fin n, i < j → (∀ d ∈ I, (i : ℕ) < d → (j : ℕ) < d) → mat y i j = 0) →
      A'' ≠ ⊥ →
      Nat.card (A''.map (ρ.comp (MulAut.conj h).toMonoidHom)) *
        Nat.card (fixV (A''.map (ρ.comp (MulAut.conj h).toMonoidHom))) < Nat.card V)

section

variable {V : Type} [CommGroup V]

theorem injective_comp_conj {n : ℕ} {ρ : SLt n →* MulAut V} (hρ : Function.Injective ρ) (h : SLt n) :
    Function.Injective (ρ.comp (MulAut.conj h).toMonoidHom) :=
  fun _ _ hxy => (MulAut.conj h).injective (hρ hxy)

theorem fixQ_of_sum {n k : ℕ} {ρ : SLt n →* MulAut V} {I : Fin k → Subgroup V} (hind : iSupIndep I)
    {X : Type} [CommGroup X] {act : SLt n → X → X} (D : ∀ j, VModel n ρ (I j) ⊥ X act)
    (hV2 : ∀ w : V, w ^ 2 = 1) (hn : 1 ≤ n) {c : ℕ}
    (hFix : ∀ a : X, (∀ g ∈ Ut n, act g a = a) → ∀ i, ∀ hi : IsNode n i, i ≠ c →
      act (reflection n (ZMod 2) i hi.1 hi.2) a = a)
    {v : V} (hv : v ∈ ⨆ j, I j) (hvf : ∀ s ∈ Ut n, (ρ s) v = v) : ∀ x ∈ QI n {c}, (ρ x) v = v := by
  let H : Subgroup (SLt n) := (MulAction.stabilizer (MulAut V) v).comap ρ
  have hUH : Ut n ≤ H := fun s hs => hvf s hs
  have hrH : ∀ i, ∀ hi : IsNode n i, i ≠ c → reflection n (ZMod 2) i hi.1 hi.2 ∈ H := by
    intro i hi hic
    have h1 := fix_reflection_sum hind D hV2 hn hFix 1 hv (by simpa using hvf) hi hic
    have h2 : (ρ (reflection n (ZMod 2) i hi.1 hi.2)) v = v := by simpa using h1
    exact h2
  intro x hx
  exact QI_le_of_reflections hUH hrH hx

variable [Finite V]

theorem excl_ext4 (hV2 : ∀ w : V, w ^ 2 = 1) {Ls : Subgroup (MulAut V)} {UL' Z : Subgroup V}
    (hZ : Z ≤ CFSG.Quasithin.fixV Ls) (h : SLExteriorTwo Ls UL' Z 4) : ExclConcl Ls UL' := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨D⟩ := vmodelExtSq hπ (fun g hg z hz => hZ hz g hg)
  refine ⟨4, {2}, {2, 3}, rhoOf π, by norm_num, rhoOf_mem π, rhoOf_surj hπ.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := exists_ne_one_wedge4
    exact ne_bot_of_surj D.β D.surj a ha
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    simp
  · intro i hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    rcases hi with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩
  · exact ⟨3, by simp, by norm_num⟩
  · intro h v hv hvf x hx
    exact fixQ_of_model (D.rtwist h) hV2 (by norm_num) (c := 2)
      (fun a ha i hi hic => fix_extSq4 a ha i hi hic) hv hvf x hx
  · intro hρ h A'' hU hR hne
    exact not_ff_ext4 (injective_comp_conj hρ h) (D.rtwist h) A'' hU hR hne

theorem excl_ext5 (hV2 : ∀ w : V, w ^ 2 = 1) {Ls : Subgroup (MulAut V)} {UL' : Subgroup V}
    (h : SLExteriorTwo Ls UL' ⊥ 5) : ExclConcl Ls UL' := by
  obtain ⟨π, hπ⟩ := h
  obtain ⟨D⟩ := vmodelExtSq hπ (fun g hg z hz => by rw [Subgroup.mem_bot.1 hz]; exact map_one g)
  refine ⟨5, {2}, {2}, rhoOf π, by norm_num, rhoOf_mem π, rhoOf_surj hπ.1, ?_, le_rfl, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := exists_ne_one_wedge5
    exact ne_bot_of_surj D.β D.surj a ha
  · intro i hi
    rw [Set.mem_singleton_iff] at hi
    subst hi
    exact ⟨by norm_num, by norm_num⟩
  · exact ⟨2, by simp, by norm_num⟩
  · intro h v hv hvf x hx
    exact fixQ_of_model (D.rtwist h) hV2 (by norm_num) (c := 2)
      (fun a ha i hi hic => fix_extSq5 a ha i hi hic) hv hvf x hx
  · intro hρ h A'' hU hR hne
    exact not_ff_ext5 (injective_comp_conj hρ h) (D.rtwist h) A'' hU hR hne

theorem excl_nat2 (hV2 : ∀ w : V, w ^ 2 = 1) {Ls : Subgroup (MulAut V)} {UL' : Subgroup V} {n k : ℕ}
    (hn : 4 ≤ n) (hk : 2 ≤ k)
    (h : DirectSumOfCopies Ls UL' ⊥ (FFModel.nat (StatedSL n (ZMod 2))) k) : ExclConcl Ls UL' := by
  obtain ⟨I, π, -, hind, hsup, hreal⟩ := h
  have D : ∀ j, VModel n (rhoOf π) (I j) ⊥ (Multiplicative (Vt n)) (fun g a => actM g a) :=
    fun j => Classical.choice
      (vmodelNat (hreal j) (fun g hg z hz => by rw [Subgroup.mem_bot.1 hz]; exact map_one g))
  have hindep : iSupIndep I := by
    intro i
    have := hind i
    rw [bot_sup_eq] at this
    exact disjoint_iff.2 this
  have hsup' : UL' = ⨆ j, I j := by rw [← hsup, bot_sup_eq]
  have h0 : (0 : ℕ) < k := by omega
  have h1 : (1 : ℕ) < k := by omega
  refine ⟨n, {1}, {1}, rhoOf π, by omega, rhoOf_mem π, rhoOf_surj (hreal ⟨0, h0⟩).1, ?_, le_rfl, ?_, ?_, ?_,
    ?_⟩
  · obtain ⟨a, ha⟩ := exists_ne_one_nat (by omega : 1 ≤ n)
    have h0' : I ⟨0, h0⟩ ≠ ⊥ := ne_bot_of_surj (D ⟨0, h0⟩).β (D ⟨0, h0⟩).surj a ha
    intro hbot
    apply h0'
    rw [eq_bot_iff]
    exact (le_iSup I ⟨0, h0⟩).trans (hsup' ▸ hbot).le
  · intro i hi
    rw [Set.mem_singleton_iff] at hi
    subst hi
    exact ⟨le_rfl, by omega⟩
  · exact ⟨1, by simp, by simp; omega⟩
  · intro h v hv hvf x hx
    rw [hsup'] at hv
    exact fixQ_of_sum hindep (fun j => (D j).rtwist h) hV2 (by omega) (c := 1)
      (fun a ha i hi hic => fix_nat a ha i hi hic) hv hvf x hx
  · intro hρ h A'' hU hR hne
    have hne01 : (⟨0, h0⟩ : Fin k) ≠ ⟨1, h1⟩ := by
      intro hh
      have := congrArg Fin.val hh
      simp at this
    have hdisj : I ⟨0, h0⟩ ⊓ I ⟨1, h1⟩ = ⊥ := disjoint_iff.1 (hindep.pairwiseDisjoint hne01)
    exact not_ff_nat2 (by omega) (injective_comp_conj hρ h) hdisj
      ((D ⟨0, h0⟩).rtwist h) ((D ⟨1, h1⟩).rtwist h) A'' hU hR hne

end

end CFSG.Quasithin.FLc
