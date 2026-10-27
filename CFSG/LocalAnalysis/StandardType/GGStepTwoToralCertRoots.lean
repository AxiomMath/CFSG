module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertKac

public section

namespace CFSG.StandardType.StepTwoToralCert

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {p : ℕ}

@[expose] def tcRootSet (τ : Tag) (C : List ℕ) : Set (Fin τ.rank → ℤ) :=
  {β | ∃ j ∈ C, j < τ.rootCertificate.roots.length ∧ β = τ.rootCertificate.root j}

theorem tcR_tcRoots_getElem? (τ : Tag) {i : ℕ} (hi : i < τ.rootCertificate.roots.length) :
    (tcRoots τ ())[i]? = some (Array.ofFn (τ.rootCertificate.root i)) := by
  simp [tcRoots, hi]

theorem tcRoots_size (τ : Tag) : (tcRoots τ ()).size = τ.rootCertificate.roots.length := by
  simp [tcRoots]

theorem tcRoots_getD (τ : Tag) {i : ℕ} (hi : i < τ.rootCertificate.roots.length) :
    (tcRoots τ ()).getD i #[] = Array.ofFn (τ.rootCertificate.root i) := by
  simp [tcR_tcRoots_getElem? τ hi]

theorem isRoot_iff_exists_index {α : Fin τ.rank → ℤ} :
    IsRoot τ α ↔ ∃ i, i < τ.rootCertificate.roots.length ∧ α = τ.rootCertificate.root i := by
  rw [RootCertificate.isRoot_iff τ.rootCertificate_check]
  exact exists_congr fun k => and_congr_right fun _ => eq_comm

theorem tcIsRoot_certRoot {i : ℕ} (hi : i < τ.rootCertificate.roots.length) :
    IsRoot τ (τ.rootCertificate.root i) :=
  RootCertificate.isRoot_root τ.rootCertificate_check i hi

theorem tcGramMat_getD (τ : Tag) (i j : Fin τ.rank) :
    tcEnt ((tcGramMat τ ()).getD i #[]) j = τ.symmetrizedCartan i j := by
  simp [tcGramMat, tcEnt]

theorem tcR_symmetrizedCartan_isSymm (τ : Tag) : τ.symmetrizedCartan.IsSymm := by
  cases τ <;> decide +kernel

theorem latGram_symmetrizedCartan_comm (τ : Tag) (α β : Fin τ.rank → ℤ) :
    latGram τ.symmetrizedCartan α β = latGram τ.symmetrizedCartan β α := by
  simp only [latGram]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [(tcR_symmetrizedCartan_isSymm τ).apply i j]
  ring

theorem tcR_tcDot_ofFn {n : ℕ} (a b : Fin n → ℤ) :
    tcDot n (Array.ofFn a) (Array.ofFn b) = ∑ k, a k * b k := by
  simp only [tcDot_eq_sum, tcEnt_ofFn]

theorem tcR_latGram_single_left {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (k : Fin N)
    (α : Fin N → ℤ) : latGram S (Pi.single k 1) α = ∑ l, S k l * α l := by
  rw [latGram, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem tcR_latGram_eq_sum {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (β α : Fin N → ℤ) :
    latGram S β α = ∑ k, latGram S (Pi.single k 1) α * β k := by
  simp only [tcR_latGram_single_left, Finset.sum_mul]
  rw [latGram]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem tcR_gramRow (τ : Tag) (k : Fin τ.rank) (α : Fin τ.rank → ℤ) :
    tcDot τ.rank (((tcGramMat τ ())[(k : ℕ)]?).getD #[]) (Array.ofFn α) =
      latGram τ.symmetrizedCartan (Pi.single k 1) α := by
  rw [← Array.getD_eq_getD_getElem?, tcDot_eq_sum, tcR_latGram_single_left]
  simp only [tcGramMat_getD, tcEnt_ofFn]

theorem tcGramTab_getD (τ : Tag) {i j : ℕ} (hi : i < τ.rootCertificate.roots.length)
    (hj : j < τ.rootCertificate.roots.length) :
    tcEnt ((tcGramTab τ ()).getD i #[]) j =
      latGram τ.symmetrizedCartan (τ.rootCertificate.root i) (τ.rootCertificate.root j) := by
  simp only [tcEnt, tcGramTab, Array.getD_eq_getD_getElem?, Array.map_map, Array.getElem?_map,
    tcR_tcRoots_getElem? τ hi, tcR_tcRoots_getElem? τ hj, Option.map_some, Function.comp_apply,
    tcR_gramRow, Option.getD_some, tcR_tcDot_ofFn]
  exact (tcR_latGram_eq_sum _ _ _).symm.trans (latGram_symmetrizedCartan_comm τ _ _)

theorem tcCoTab_getD (τ : Tag) {i : ℕ} (hi : i < τ.rootCertificate.roots.length)
    (k : Fin τ.rank) :
    tcEnt ((tcCoTab τ ()).getD i #[]) k =
      latCorootZ τ.symmetrizedCartan (τ.rootCertificate.root i) k := by
  simp only [tcEnt, tcCoTab, Array.getD_eq_getD_getElem?, Array.map_ofFn, Array.getElem?_map,
    tcR_tcRoots_getElem? τ hi, Option.map_some, tcR_gramRow, tcR_tcDot_ofFn, Option.getD_some,
    Array.size_ofFn, Fin.is_lt, getElem?_pos, Array.getElem_ofFn, Fin.eta, Function.comp_apply,
    latCorootZ]
  rw [← tcR_latGram_eq_sum]

theorem tcR_getD_mem {C : List ℕ} {j : ℕ} (hj : j < C.length) : C.getD j 0 ∈ C :=
  List.getD_eq_getElem _ _ hj ▸ List.getElem_mem hj

theorem mem_tcPhi_iff (μ : Array ℤ) (i : ℕ) :
    i ∈ (List.range (tcRoots τ ()).size).filter
        (fun r => tcDot τ.rank ((tcRoots τ ()).getD r #[]) μ % (p : ℤ) == 0) ↔
      i < τ.rootCertificate.roots.length ∧
        latChar p (tcVec p τ.rank μ) (τ.rootCertificate.root i) = 0 := by
  rw [List.mem_filter, List.mem_range, tcRoots_size, beq_iff_eq]
  refine and_congr_right fun hi => ?_
  rw [tcRoots_getD τ hi, tcDot_mod_eq_zero_iff]
  simp only [tcFun, latChar, tcEnt_ofFn]

theorem tcClassOK_sound (f : Fin τ.rank → ZMod p) (phi : List ℕ)
    (hphi : ∀ i, i ∈ phi ↔
      i < τ.rootCertificate.roots.length ∧ latChar p f (τ.rootCertificate.root i) = 0)
    {C : List ℕ} (hC : tcClassOK (tcGramTab τ ()) phi C = true) {i : ℕ} (hi : i ∈ C) :
    {β | latLinked τ.symmetrizedCartan (latPhi {α | IsRoot τ α} p f)
        (τ.rootCertificate.root i) β} = tcRootSet τ C := by
  simp only [tcClassOK, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, List.contains_iff_mem, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true, bne_iff_ne, ne_eq] at hC
  obtain ⟨⟨⟨-, hsub⟩, hlink⟩, hclosed⟩ := hC
  have hmem : ∀ x ∈ C, x < τ.rootCertificate.roots.length ∧
      τ.rootCertificate.root x ∈ latPhi {α | IsRoot τ α} p f := fun x hx =>
    have h := (hphi x).1 (hsub x hx)
    ⟨h.1, tcIsRoot_certRoot h.1, h.2⟩
  have hrel : ∀ x ∈ C, ∀ y ∈ C, tcEnt ((tcGramTab τ ()).getD x #[]) y ≠ 0 →
      latLinked τ.symmetrizedCartan (latPhi {α | IsRoot τ α} p f)
        (τ.rootCertificate.root x) (τ.rootCertificate.root y) := fun x hx y hy hxy =>
    Relation.EqvGen.rel _ _ ⟨(hmem x hx).2, (hmem y hy).2, by
      rwa [← tcGramTab_getD τ (hmem x hx).1 (hmem y hy).1]⟩
  have hhead : ∀ j < C.length, latLinked τ.symmetrizedCartan (latPhi {α | IsRoot τ α} p f)
      (τ.rootCertificate.root (C.getD 0 0)) (τ.rootCertificate.root (C.getD j 0)) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      rcases hlink j hj with rfl | ⟨k, hkj, hk⟩
      · exact Relation.EqvGen.refl _
      · exact Relation.EqvGen.trans _ _ _ (ih k hkj (hkj.trans hj))
          (hrel _ (tcR_getD_mem (hkj.trans hj)) _ (tcR_getD_mem hj) hk)
  have hlinked : ∀ x ∈ C, latLinked τ.symmetrizedCartan (latPhi {α | IsRoot τ α} p f)
      (τ.rootCertificate.root (C.getD 0 0)) (τ.rootCertificate.root x) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
    rw [← List.getD_eq_getElem _ _ hj]
    exact hhead j hj
  have hstep : ∀ x y, latGram τ.symmetrizedCartan x y ≠ 0 →
      y ∈ latPhi {α | IsRoot τ α} p f → x ∈ tcRootSet τ C → y ∈ tcRootSet τ C := by
    rintro x y hxy ⟨hy, hyf⟩ ⟨a, haC, haL, rfl⟩
    obtain ⟨b, hbL, rfl⟩ := isRoot_iff_exists_index.1 hy
    refine ⟨b, (hclosed a haC b ((hphi b).2 ⟨hbL, hyf⟩)).resolve_left ?_, hbL, rfl⟩
    rwa [tcGramTab_getD τ haL hbL]
  have hiff : ∀ x y, latLinked τ.symmetrizedCartan (latPhi {α | IsRoot τ α} p f) x y →
      (x ∈ tcRootSet τ C ↔ y ∈ tcRootSet τ C) := by
    intro x y h
    induction h with
    | rel x y h =>
      exact ⟨hstep x y h.2.2 h.2.1,
        hstep y x (by rw [latGram_symmetrizedCartan_comm]; exact h.2.2) h.1⟩
    | refl x => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  ext β
  refine ⟨fun h => (hiff _ _ h).1 ⟨i, hi, (hmem i hi).1, rfl⟩, ?_⟩
  rintro ⟨j, hj, -, rfl⟩
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hlinked i hi)) (hlinked j hj)

end CFSG.StandardType.StepTwoToralCert
