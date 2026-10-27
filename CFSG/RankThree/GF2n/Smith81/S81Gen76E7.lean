module

public import CFSG.RankThree.GF2n.Smith81.S81E7Basic
public import CFSG.RankThree.GF2n.Smith81.S81Gen76Line

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.RankThree.GF2n.Smith81.Gen76


abbrev topIdx : Fin e7Data.d := ⟨0, by decide⟩

abbrev node7 : Fin (Tag.rank .E7) := ⟨6, by decide⟩

theorem wt_topIdx : e7Data.wt topIdx = Pi.single node7 1 := by decide +kernel

theorem pr_sRefl_reflect (i : Fin (Tag.rank .E7)) (a : Fin e7Data.d)
    (γ : Fin (Tag.rank .E7) → ℤ) : pr (e7Data_valid.sRefl i a) (reflect .E7 i γ) = pr a γ := by
  unfold pr
  rw [e7Data_valid.wt_sRefl, MinData.Valid.reflectWeight_dotProduct cartan_symm_E7,
    reflect_reflect]

theorem sRefl_shift {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) {a : Fin e7Data.d}
    (h : pr a γ = -1) (i : Fin (Tag.rank .E7)) :
    e7Data_valid.sRefl i (shift γ a) = shift (reflect .E7 i γ) (e7Data_valid.sRefl i a) := by
  symm
  apply shift_eq
  rw [e7Data_valid.wt_sRefl, e7Data_valid.wt_sRefl, wt_shift hγ h, MinData.reflectWeight_add,
    MinData.toWeight_reflect]

@[expose] def Adj (a b : Fin e7Data.d) : Prop :=
  ∃ γ, IsRoot .E7 γ ∧ pr a γ = -1 ∧ shift γ a = b

theorem Adj.sRefl {a b : Fin e7Data.d} (h : Adj a b) (i : Fin (Tag.rank .E7)) :
    Adj (e7Data_valid.sRefl i a) (e7Data_valid.sRefl i b) := by
  obtain ⟨γ, hγ, hpr, rfl⟩ := h
  exact ⟨reflect .E7 i γ, hγ.reflect i, by rw [pr_sRefl_reflect, hpr], (sRefl_shift hγ hpr i).symm⟩

private theorem exists_raise : ∀ a : Fin e7Data.d, a ≠ topIdx →
    ∃ i, e7Data.wt a i = -1 ∧ e7Data.weyl a i < a := by
  decide +kernel

private theorem exists_raise_top : ∀ a : Fin e7Data.d, (a : ℕ) ≠ e7Data.weyl 0 node7 →
    (∃ k : Fin 126, pr a ((Tag.rootCertificate .E7).root k) = -1 ∧
      e7Data.wt topIdx = e7Data.wt a + MinData.toWeight ((Tag.rootCertificate .E7).root k)) →
    ∃ i, e7Data.wt topIdx i = 0 ∧ e7Data.wt a i = -1 ∧ e7Data.weyl a i < a := by
  unfold pr
  decide +kernel

variable {K : Type} [Field K]

theorem moves_nm [CharP K 2] (i : Fin (Tag.rank .E7)) :
    Moves ((e7Data_valid.nm K i : ↥(EGrp K)) : (Module.End K (V K))ˣ)
      (e7Data_valid.sRefl i) := by
  intro a
  change e7Data_valid.endo K (e7Data_valid.nm K i) (Finsupp.single a 1) = _
  rw [e7Data_valid.endo_nm, e7Data_valid.nOp_single]
  split_ifs
  · rw [← Finsupp.single_neg, CharTwo.neg_eq]
  · rfl

variable (K) in
@[expose] def InOrb (a b : Fin e7Data.d) : Prop :=
  ∃ g ∈ EGrp K, ∃ σ : Fin e7Data.d → Fin e7Data.d, Moves g σ ∧
    σ (e7Data_valid.sRefl node7 topIdx) = a ∧ σ topIdx = b

theorem InOrb.sRefl [CharP K 2] {a b : Fin e7Data.d} (h : InOrb K a b) (i : Fin (Tag.rank .E7)) :
    InOrb K (e7Data_valid.sRefl i a) (e7Data_valid.sRefl i b) := by
  obtain ⟨g, hg, σ, hσ, ha, hb⟩ := h
  exact ⟨_ * g, (EGrp K).mul_mem (e7Data_valid.nm K i).2 hg, _, (moves_nm i).mul hσ,
    by rw [Function.comp_apply, ha], by rw [Function.comp_apply, hb]⟩

theorem inOrb_top [CharP K 2] (a : Fin e7Data.d) (h : Adj a topIdx) : InOrb K a topIdx := by
  suffices ∀ n, ∀ a : Fin e7Data.d, (a : ℕ) = n → Adj a topIdx → InOrb K a topIdx from
    this _ a rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a ha hadj
    by_cases h1 : (a : ℕ) = e7Data.weyl 0 node7
    · refine ⟨1, (EGrp K).one_mem, id, Moves.one, ?_, rfl⟩
      exact Fin.ext (by rw [id, e7Data_valid.sRefl_val, h1])
    obtain ⟨γ, hγ, hpr, hsh⟩ := hadj
    have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
    obtain ⟨k, hk, hkγ⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hγ
    obtain ⟨i, hi0, -, hlt⟩ := exists_raise_top a h1 ⟨⟨k, by omega⟩, by
      refine ⟨?_, ?_⟩
      · show pr a ((Tag.rootCertificate .E7).root k) = -1
        rw [hkγ]
        exact hpr
      · show e7Data.wt topIdx = e7Data.wt a + MinData.toWeight ((Tag.rootCertificate .E7).root k)
        rw [hkγ, ← hsh]
        exact wt_shift hγ hpr⟩
    have hfix : e7Data_valid.sRefl i topIdx = topIdx := e7Data_valid.sRefl_eq_self hi0
    have hadj' : Adj (e7Data_valid.sRefl i a) topIdx := by
      have := (show Adj a topIdx from ⟨γ, hγ, hpr, hsh⟩).sRefl i
      rwa [hfix] at this
    have h' := (ih _ (by rw [← ha, e7Data_valid.sRefl_val]; exact hlt) _ rfl hadj').sRefl i
    rwa [e7Data_valid.sRefl_sRefl, hfix] at h'

theorem inOrb_of_adj [CharP K 2] {a b : Fin e7Data.d} (h : Adj a b) : InOrb K a b := by
  suffices ∀ n, ∀ b : Fin e7Data.d, (b : ℕ) = n → ∀ a, Adj a b → InOrb K a b from
    this _ b rfl a h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hb a hadj
    by_cases h1 : b = topIdx
    · subst h1
      exact inOrb_top a hadj
    obtain ⟨i, -, hlt⟩ := exists_raise b h1
    have h' := (ih _ (by rw [← hb, e7Data_valid.sRefl_val]; exact hlt) _ rfl _
      (hadj.sRefl i)).sRefl i
    rwa [e7Data_valid.sRefl_sRefl, e7Data_valid.sRefl_sRefl] at h'

theorem isLine_rootLine [CharP K 2] {a b : Fin e7Data.d} (h : Adj a b) :
    IsLine (EGrp K) (rootLine (e7Data_valid.sRefl node7 topIdx) topIdx) (rootLine a b) := by
  obtain ⟨g, hg, σ, hσ, ha, hb⟩ := inOrb_of_adj (K := K) h
  exact ⟨g, hg, by rw [hσ.image_rootLine, ha, hb]⟩

theorem weightPoints_generate [CharP K 2] {S : Set (Submodule K (V K))}
    (hS : IsLineClosed (EGrp K) (rootLine (e7Data_valid.sRefl node7 topIdx) topIdx) S)
    (hP : ∀ c : Fin e7Data.d, (K ∙ (Finsupp.single c 1 : V K)) ∈ S)
    {g : (Module.End K (V K))ˣ} (hg : g ∈ EGrp K) (c : Fin e7Data.d) :
    (K ∙ (g : Module.End K (V K)) (Finsupp.single c 1)) ∈ S := by
  refine span_mem_of_rootLines rfl ?_ ?_ hS hP hg c
  · rintro _ ⟨γ, hγ, t, rfl⟩
    refine ⟨γ, hγ, -t, inv_eq_of_mul_eq_one_right ?_⟩
    rw [← e7Data_valid.xu_add, add_neg_cancel, e7Data_valid.xu_zero]
  · rintro _ ⟨γ, hγ, t, rfl⟩ c
    rw [e7Data_valid.xu_apply, rootOp_single hγ]
    split_ifs with h
    · refine Or.inr ⟨shift γ c, ?_, isLine_rootLine ⟨γ, hγ, h, rfl⟩, t, rfl⟩
      intro he
      have := pr_shift_self hγ h
      rw [he, h] at this
      norm_num at this
    · left
      rw [smul_zero, add_zero]

end CFSG.RankThree.GF2n.Smith81.E7Model
