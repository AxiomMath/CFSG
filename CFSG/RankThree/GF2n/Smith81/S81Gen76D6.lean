module

public import CFSG.RankThree.GF2n.Smith81.S81D6Fe3a
public import CFSG.RankThree.GF2n.Smith81.S81Gen76E7
public import CFSG.RankThree.GF2n.Smith81.S81D6Ops

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.RankThree.GF2n.Smith81.E7Model CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley
  CFSG.RankThree.GF2n.Smith81.Gen76


abbrev dnode (j : Fin 6) : Fin (Tag.rank .E7) := j.succ

private theorem reflect_theta : ∀ j : Fin 6, reflect .E7 (dnode j) theta = theta := by
  decide +kernel

theorem reflect_mem_Perp {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ Perp) (j : Fin 6) :
    reflect .E7 (dnode j) β ∈ Perp := by
  have hβ' : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
  refine ⟨hβ'.1.reflect _, ?_⟩
  rw [MinData.toWeight_reflect, MinData.Valid.reflectWeight_dotProduct cartan_symm_E7,
    reflect_theta j, hβ'.2]

theorem pr_theta_sRefl (a : Fin e7Data.d) (j : Fin 6) :
    pr (e7Data_valid.sRefl (dnode j) a) theta = pr a theta := by
  have h := pr_sRefl_reflect (dnode j) a theta
  rwa [reflect_theta j] at h

@[expose] def sReflW (j : Fin 6) (a : Idx0) : Idx0 :=
  ⟨e7Data_valid.sRefl (dnode j) a, mem_idx0.2 (by rw [pr_theta_sRefl]; exact mem_idx0.1 a.2)⟩

theorem sReflW_val (j : Fin 6) (a : Idx0) :
    (sReflW j a : Fin e7Data.d) = e7Data_valid.sRefl (dnode j) a := rfl

theorem sReflW_sReflW (j : Fin 6) (a : Idx0) : sReflW j (sReflW j a) = a :=
  Subtype.ext (e7Data_valid.sRefl_sRefl _ _)

theorem sReflW_eq_self {j : Fin 6} {a : Idx0} (h : e7Data.wt a (dnode j) = 0) : sReflW j a = a :=
  Subtype.ext (e7Data_valid.sRefl_eq_self h)

@[expose] def AdjW (a b : Idx0) : Prop :=
  ∃ β ∈ Perp, pr a β = -1 ∧ shift β a = b

theorem AdjW.sReflW {a b : Idx0} (h : AdjW a b) (j : Fin 6) :
    AdjW (sReflW j a) (sReflW j b) := by
  obtain ⟨β, hβ, hpr, hb⟩ := h
  have hβ' : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
  refine ⟨reflect .E7 (dnode j) β, reflect_mem_Perp hβ j, by rw [sReflW_val, pr_sRefl_reflect, hpr],
    ?_⟩
  rw [sReflW_val, sReflW_val, ← hb]
  exact (sRefl_shift hβ'.1 hpr _).symm

private theorem exists_raiseW : ∀ a : Fin e7Data.d, pr a theta = 0 → (a : ℕ) ≠ 8 →
    ∃ j : Fin 6, e7Data.wt a (dnode j) = -1 ∧ e7Data.weyl a (dnode j) < a := by
  unfold pr
  decide +kernel

private theorem exists_raiseW_a0 : ∀ a : Fin e7Data.d, pr a theta = 0 →
    (a : ℕ) ≠ e7Data.weyl 8 (dnode 0) →
    (∃ k : Fin 126, pr a ((Tag.rootCertificate .E7).root k) = -1 ∧
      e7Data.wt 8 = e7Data.wt a + MinData.toWeight ((Tag.rootCertificate .E7).root k)) →
    ∃ j : Fin 6, e7Data.wt 8 (dnode j) = 0 ∧ e7Data.wt a (dnode j) = -1 ∧
      e7Data.weyl a (dnode j) < a := by
  unfold pr
  decide +kernel

variable {K : Type} [Field K]

@[expose] def weylW [CharP K 2] (j : Fin 6) : (Module.End K (W K))ˣ :=
  Classical.choose (exists_induces (nm_mem_Lam (K := K) (Fin.succ_ne_zero j)))

theorem weylW_induces [CharP K 2] (j : Fin 6) :
    Induces (weylW (K := K) j)
      ((e7Data_valid.nm K (dnode j) : ↥(EGrp K)) : (Module.End K (V K))ˣ) :=
  Classical.choose_spec (exists_induces (nm_mem_Lam (K := K) (Fin.succ_ne_zero j)))

theorem weylW_mem [CharP K 2] (j : Fin 6) : weylW (K := K) j ∈ LamW K :=
  ⟨_, nm_mem_Lam (K := K) (Fin.succ_ne_zero j), weylW_induces j⟩

theorem moves_weylW [CharP K 2] (j : Fin 6) : Moves (weylW (K := K) j) (sReflW j) := by
  intro a
  apply emb_injective
  rw [weylW_induces j (Finsupp.single a 1), emb_single, emb_single, sReflW_val]
  exact moves_nm (dnode j) a

abbrev a1W : Idx0 := sReflW 0 a0

variable (K) in
@[expose] def InOrbW (a b : Idx0) : Prop :=
  ∃ g ∈ LamW K, ∃ σ : Idx0 → Idx0, Moves g σ ∧ σ a1W = a ∧ σ a0 = b

theorem InOrbW.sReflW [CharP K 2] {a b : Idx0} (h : InOrbW K a b) (j : Fin 6) :
    InOrbW K (sReflW j a) (sReflW j b) := by
  obtain ⟨g, hg, σ, hσ, ha, hb⟩ := h
  exact ⟨_ * g, (LamW K).mul_mem (weylW_mem j) hg, _, (moves_weylW j).mul hσ,
    by rw [Function.comp_apply, ha], by rw [Function.comp_apply, hb]⟩

theorem inOrbW_a0 [CharP K 2] (a : Idx0) (h : AdjW a a0) : InOrbW K a a0 := by
  suffices ∀ n, ∀ a : Idx0, ((a : Fin e7Data.d) : ℕ) = n → AdjW a a0 → InOrbW K a a0 from
    this _ a rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a ha hadj
    by_cases h1 : ((a : Fin e7Data.d) : ℕ) = e7Data.weyl (a0 : Fin e7Data.d) (dnode 0)
    · refine ⟨1, (LamW K).one_mem, id, Moves.one, ?_, rfl⟩
      exact Subtype.ext (Fin.ext (by rw [id, sReflW_val, e7Data_valid.sRefl_val, h1]))
    obtain ⟨β, hβ, hpr, hsh⟩ := hadj
    have hβ' : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
    have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
    obtain ⟨k, hk, hkβ⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hβ'.1
    obtain ⟨j, hj0, -, hlt⟩ := exists_raiseW_a0 a (mem_idx0.1 a.2) h1 ⟨⟨k, by omega⟩, by
      refine ⟨?_, ?_⟩
      · show pr a ((Tag.rootCertificate .E7).root k) = -1
        rw [hkβ]
        exact hpr
      · show e7Data.wt (a0 : Fin e7Data.d) =
          e7Data.wt a + MinData.toWeight ((Tag.rootCertificate .E7).root k)
        rw [hkβ, ← hsh]
        exact wt_shift hβ'.1 hpr⟩
    have hfix : sReflW j a0 = a0 := sReflW_eq_self hj0
    have hadj' : AdjW (sReflW j a) a0 := by
      have := (show AdjW a a0 from ⟨β, hβ, hpr, hsh⟩).sReflW j
      rwa [hfix] at this
    have h' := (ih _ (by rw [← ha, sReflW_val, e7Data_valid.sRefl_val]; exact hlt) _ rfl
      hadj').sReflW j
    rwa [sReflW_sReflW, hfix] at h'

theorem inOrbW_of_adj [CharP K 2] {a b : Idx0} (h : AdjW a b) : InOrbW K a b := by
  suffices ∀ n, ∀ b : Idx0, ((b : Fin e7Data.d) : ℕ) = n → ∀ a, AdjW a b → InOrbW K a b from
    this _ b rfl a h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hb a hadj
    by_cases h1 : b = a0
    · rw [h1] at hadj ⊢
      exact inOrbW_a0 a hadj
    have h1' : ((b : Fin e7Data.d) : ℕ) ≠ 8 := fun h => h1 (Subtype.ext (Fin.ext h))
    obtain ⟨j, -, hlt⟩ := exists_raiseW b (mem_idx0.1 b.2) h1'
    have h' := (ih _ (by rw [← hb, sReflW_val, e7Data_valid.sRefl_val]; exact hlt) _ rfl _
      (hadj.sReflW j)).sReflW j
    rwa [sReflW_sReflW, sReflW_sReflW] at h'

theorem isLine_rootLineW [CharP K 2] {a b : Idx0} (h : AdjW a b) :
    IsLine (LamW K) (rootLine a1W a0) (rootLine a b) := by
  obtain ⟨g, hg, σ, hσ, ha, hb⟩ := inOrbW_of_adj (K := K) h
  exact ⟨g, hg, by rw [hσ.image_rootLine, ha, hb]⟩

variable (K) in
@[expose] def rootGensW : Set (Module.End K (W K))ˣ :=
  {g | ∃ β ∈ Perp, ∃ c : K, Induces g (e7Data_valid.xu K β c)}

theorem closure_rootGensW [CharP K 2] : Subgroup.closure (rootGensW K) = LamW K := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ?_
  · rintro g ⟨β, hβ, c, hg⟩
    exact ⟨_, xu_mem_Lam hβ c, hg⟩
  · intro g hg
    obtain ⟨⟨l, hl⟩, rfl⟩ := mem_LamW_iff.1 hg
    clear hg
    have hl' : l ∈ Subgroup.closure {g | ∃ β ∈ Perp, ∃ c : K, g = e7Data_valid.xu K β c} := hl
    induction hl' using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨β, hβ, c, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨β, hβ, c, resV0_induces _⟩
    | one =>
      show resV0 K 1 ∈ _
      rw [map_one]
      exact one_mem _
    | mul x y hx hy ihx ihy =>
      show resV0 K (⟨x, hx⟩ * ⟨y, hy⟩) ∈ _
      rw [map_mul]
      exact mul_mem (ihx hx) (ihy hy)
    | inv x hx ih =>
      show resV0 K (⟨x, hx⟩⁻¹) ∈ _
      rw [map_inv]
      exact inv_mem (ih hx)

theorem inv_mem_rootGensW {g : (Module.End K (W K))ˣ} (hg : g ∈ rootGensW K) :
    g⁻¹ ∈ rootGensW K := by
  obtain ⟨β, hβ, c, h⟩ := hg
  refine ⟨β, hβ, -c, ?_⟩
  have : (e7Data_valid.xu K β c)⁻¹ = e7Data_valid.xu K β (-c) :=
    inv_eq_of_mul_eq_one_right (by rw [← e7Data_valid.xu_add, add_neg_cancel, e7Data_valid.xu_zero])
  rw [← this]
  exact h.inv

theorem rootGensW_single [CharP K 2] {g : (Module.End K (W K))ˣ} (hg : g ∈ rootGensW K)
    (a : Idx0) :
    (g : Module.End K (W K)) (Finsupp.single a 1) = Finsupp.single a 1 ∨
    ∃ b, b ≠ a ∧ IsLine (LamW K) (rootLine a1W a0) (rootLine a b) ∧ ∃ t : K,
      (g : Module.End K (W K)) (Finsupp.single a 1) =
        Finsupp.single a 1 + t • Finsupp.single b 1 := by
  obtain ⟨β, hβ, c, h⟩ := hg
  have hβ' : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
  obtain rfl : g = xuWUnit hβ c := h.unique (xuWUnit_induces hβ c)
  rw [xuWUnit_apply, EW_single hβ]
  by_cases hpr : pr (a : Fin e7Data.d) β = -1
  · rw [if_pos hpr]
    refine Or.inr ⟨shiftW β a, ?_, isLine_rootLineW ⟨β, hβ, hpr, (shiftW_val hβ hpr).symm⟩, c, rfl⟩
    intro hba
    have h1 := pr_shift_self hβ'.1 hpr
    rw [← shiftW_val hβ hpr, hba, hpr] at h1
    norm_num at h1
  · rw [if_neg hpr, smul_zero, add_zero]
    exact Or.inl rfl

theorem weightPointsW_generate [CharP K 2] {S : Set (Submodule K (W K))}
    (hS : IsLineClosed (LamW K) (rootLine a1W a0) S)
    (hP : ∀ c : Idx0, (K ∙ (Finsupp.single c 1 : W K)) ∈ S)
    {g : (Module.End K (W K))ˣ} (hg : g ∈ LamW K) (c : Idx0) :
    (K ∙ (g : Module.End K (W K)) (Finsupp.single c 1)) ∈ S :=
  span_mem_of_rootLines closure_rootGensW (fun _ => inv_mem_rootGensW)
    (fun _ hu c => rootGensW_single hu c) hS hP hg c

end CFSG.RankThree.GF2n.Smith81.D6Spin
