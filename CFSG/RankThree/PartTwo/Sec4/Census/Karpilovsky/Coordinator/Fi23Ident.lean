module

public import CFSG.Sporadic.Recognition.Fi24PrimeMultiplierPG
public import CFSG.Sporadic.Bridge.Fi23Surj
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt
public import Certificates.Certificate291373

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

open CFSG.CosetTable CFSG.Sporadic.Recognition.PresentedWords
  CFSG.Sporadic.Recognition.Fi24PrimeMultiplier CFSG.Certificates.CosetEnumeration
  CFSG.YGroups CFSG.AGLEmbedding

theorem kernelTrivialAt_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : Y ≃* X) {p : ℕ}
    (h : KernelTrivialAt X p) : KernelTrivialAt Y p := by
  intro E _ _ _ π hπ hc hp
  have hk : (e.toMonoidHom.comp π).ker = π.ker := by
    ext x
    simp [MonoidHom.mem_ker]
  have := h E (e.toMonoidHom.comp π) (e.surjective.comp hπ) (hk ▸ hc) (hk ▸ hp)
  rwa [hk] at this

section Model


theorem wprod_letters {n : ℕ} (L : ℕ → ℕ) (w : List (Fin n × Bool)) :
    wprod (fun i : Fin n => y432FGen (L i.val)) w =
      evalWord y432FGen (w.map fun l => L l.1.val) := by
  induction w with
  | nil => simp [evalWord_nil]
  | cons l w ih =>
    rw [wprod_cons, ih, List.map_cons, evalWord_cons]
    congr 1
    obtain ⟨i, b⟩ := l
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact inv_eq_of_mul_eq_one_right (y432FGen_mul_self _)
    · simp

end Model

section Ident


theorem t23_rels : ∀ r ∈ TauCeti.SporadicName.Fi23.presentation.relatorSet,
    FreeGroup.lift (fun i : Fin TauCeti.SporadicName.Fi23.presentation.generatorCount =>
      y432FGen (t23Letter i.val)) r = 1 := by
  intro r hr
  rw [CFSG.Sporadic.Presentation.relatorSet_eq] at hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  rw [lift_mk, wprod_letters]
  have h := CFSG.YGroups.evalWord_arrGen_eq_one (n := 31671) (O := y432FArrays)
    y432F_check.2.1 Certificates.certificate291373.2
  exact h _ (List.mem_map_of_mem hw)

noncomputable def t23Hom : TauCeti.SporadicName.Fi23.Group →* Equiv.Perm (Fin 31671) :=
  PresentedGroup.toGroup t23_rels

theorem t23Hom_of (j : Fin TauCeti.SporadicName.Fi23.presentation.generatorCount) :
    t23Hom (PresentedGroup.of j) = y432FGen (t23Letter j.val) :=
  PresentedGroup.toGroup.of _

theorem t23Letter_lt (i : ℕ) : t23Letter i < 10 := by
  unfold t23Letter
  rcases Nat.lt_or_ge i 10 with h | h
  · revert i; decide
  · rw [List.getD_eq_default _ _ (by simpa using h)]; norm_num

theorem t23Letter_surj : ∀ k < 10, ∃ i < 10, t23Letter i = k := by decide

theorem range_t23Hom : t23Hom.range = rho432F.range := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    refine PresentedGroup.generated_by _ (rho432F.range.comap t23Hom) (fun j => ?_) x
    show t23Hom (PresentedGroup.of j) ∈ rho432F.range
    rw [t23Hom_of, ← rho432F_yGen (t23Letter_lt j.val)]
    exact ⟨_, rfl⟩
  · rw [range_rho432F, arrClosure, Subgroup.closure_le]
    rintro g ⟨k, hk, rfl⟩
    have hk10 : k < 10 := by rw [y432F_check.1] at hk; exact hk
    rw [← y432FGen_eq hk10]
    obtain ⟨i, hi, hik⟩ := t23Letter_surj k hk10
    have hgc := Certificates.certificate291373.1
    refine ⟨PresentedGroup.of ⟨i, by omega⟩, ?_⟩
    rw [t23Hom_of]
    simp [hik]

noncomputable def t23Hom' : TauCeti.SporadicName.Fi23.Group →* rho432F.range :=
  t23Hom.codRestrict _ fun x => range_t23Hom ▸ ⟨x, rfl⟩

theorem t23Hom'_surjective : Function.Surjective t23Hom' := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := range_t23Hom.ge hy
  exact ⟨x, Subtype.ext hx⟩

theorem t23Hom'_bijective :
    Function.Bijective t23Hom' := by
  have := CFSG.Sporadic.Presentation.Fi23.finite_card_le.1
  refine t23Hom'_surjective.bijective_of_nat_card_le ?_
  rw [card_range_rho432F]
  exact CFSG.Sporadic.Presentation.Fi23.finite_card_le.2

noncomputable def pg10EquivT23 :
    PG10 ≃* TauCeti.SporadicName.Fi23.Group :=
  (MulEquiv.ofBijective rho10' rho10'_bijective).trans
    (MulEquiv.ofBijective t23Hom' t23Hom'_bijective).symm

theorem nonempty_pg10_equiv_native :
    Nonempty (PG10 ≃* CFSG.Blueprint.NativeSporadic.Carrier .Fi23) := by
  obtain ⟨b⟩ : Nonempty (CFSG.Blueprint.NativeSporadic.Carrier .Fi23 ≃*
      TauCeti.SporadicName.Fi23.Group) := CFSG.Sporadic.Bridge.Fi23.nonempty_mulEquiv
  exact ⟨MulEquiv.trans (M := PG10) (N := TauCeti.SporadicName.Fi23.Group)
    (P := CFSG.Blueprint.NativeSporadic.Carrier .Fi23) pg10EquivT23 b.symm⟩

theorem kernelTrivial_PG10
    (h : KernelTrivialAt (CFSG.Blueprint.NativeSporadic.Carrier .Fi23) 3) :
    KernelTrivialAt PG10 3 := by
  obtain ⟨e⟩ := nonempty_pg10_equiv_native
  exact kernelTrivialAt_of_mulEquiv (X := CFSG.Blueprint.NativeSporadic.Carrier .Fi23)
    (Y := PG10) e h

end Ident

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three
