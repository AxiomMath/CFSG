module

public import CFSG.RankThree.GF2n.Smith81.S81XE7Grp
public import CFSG.RankThree.GF2n.Smith81.S81E7Fe7
public import CFSG.RankThree.GF2n.Smith81.S81XE7Def

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7X

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model


variable {K : Type} [Field K]

theorem IsMon.one : IsMon (1 : Gp K) id id := by
  refine ⟨fun a => ?_, fun γ hγ => hγ, fun γ _ => rfl, fun γ _ c => ?_,
    fun γ' hγ' => ⟨γ', hγ', rfl⟩⟩
  · change e7Data_valid.endo K 1 (Finsupp.single a 1) = Finsupp.single a 1
    rw [e7Data_valid.endo_one, Module.End.one_apply]
  · simp

theorem IsMon.mul {n n' : Gp K} {σ σ' : Fin e7Data.d → Fin e7Data.d}
    {ρ ρ' : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (h : IsMon n σ ρ)
    (h' : IsMon n' σ' ρ') : IsMon (n * n') (σ ∘ σ') (ρ ∘ ρ') := by
  refine ⟨fun a => ?_, fun γ hγ => h.isRoot _ (h'.isRoot γ hγ), fun γ hγ => ?_,
    fun γ hγ c => ?_, fun γ' hγ' => ?_⟩
  · change e7Data_valid.endo K (n * n') (Finsupp.single a 1) = Finsupp.single (σ (σ' a)) 1
    rw [e7Data_valid.endo_mul, Module.End.mul_apply, h'.weight a, h.weight]
  · show ρ (ρ' (-γ)) = -(ρ (ρ' γ))
    rw [h'.neg γ hγ, h.neg _ (h'.isRoot γ hγ)]
  · show n * n' * xE γ c * (n * n')⁻¹ = xE (ρ (ρ' γ)) c
    calc n * n' * xE γ c * (n * n')⁻¹ = n * (n' * xE γ c * n'⁻¹) * n⁻¹ := by group
      _ = n * xE (ρ' γ) c * n⁻¹ := by rw [h'.conj γ hγ c]
      _ = xE (ρ (ρ' γ)) c := h.conj _ (h'.isRoot γ hγ) c
  · obtain ⟨γ, hγ1, hγ2⟩ := h.surj γ' hγ'
    obtain ⟨γ'', hγ3, hγ4⟩ := h'.surj γ hγ1
    exact ⟨γ'', hγ3, by show ρ (ρ' γ'') = γ'; rw [hγ4, hγ2]⟩

theorem IsMon.endo_inv_single {n : Gp K} {σ : Fin e7Data.d → Fin e7Data.d}
    {ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (h : IsMon n σ ρ) (a : Fin e7Data.d) :
    endoE n⁻¹ (Finsupp.single (σ a) 1) = Finsupp.single a 1 := by
  have key : endoE n⁻¹ * endoE n = 1 := e7Data_valid.endo_inv_mul K n
  rw [← h.weight a, ← Module.End.mul_apply, key, Module.End.one_apply]

theorem IsMon.sigma_injective {n : Gp K} {σ : Fin e7Data.d → Fin e7Data.d}
    {ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (h : IsMon n σ ρ) :
    Function.Injective σ := by
  intro a b hab
  have ha := h.endo_inv_single a
  have hb := h.endo_inv_single b
  rw [hab] at ha
  have h1 : (Finsupp.single a (1 : K) : V K) = Finsupp.single b 1 := ha.symm.trans hb
  exact Finsupp.single_left_injective one_ne_zero h1

theorem IsMon.sigma_surjective {n : Gp K} {σ : Fin e7Data.d → Fin e7Data.d}
    {ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (h : IsMon n σ ρ) :
    Function.Surjective σ :=
  Finite.injective_iff_surjective.1 h.sigma_injective

theorem IsMon.rootOp_conj {n : Gp K} {σ : Fin e7Data.d → Fin e7Data.d}
    {ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (h : IsMon n σ ρ)
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    endoE n * e7Data.rootOp K γ * endoE n⁻¹ = e7Data.rootOp K (ρ γ) := by
  have h1 := congrArg (e7Data_valid.endo K) (h.conj γ hγ 1)
  rw [e7Data_valid.endo_mul, e7Data_valid.endo_mul, e7Data_valid.endo_xm,
    e7Data_valid.endo_xm] at h1
  simp only [one_smul] at h1
  have hinv : e7Data_valid.endo K n * e7Data_valid.endo K n⁻¹ = 1 :=
    e7Data_valid.endo_mul_inv K n
  have h2 : e7Data_valid.endo K n * (1 + e7Data.rootOp K γ) * e7Data_valid.endo K n⁻¹ =
      1 + e7Data_valid.endo K n * e7Data.rootOp K γ * e7Data_valid.endo K n⁻¹ := by
    rw [mul_add, mul_one, add_mul, hinv]
  rw [h2] at h1
  show e7Data_valid.endo K n * e7Data.rootOp K γ * e7Data_valid.endo K n⁻¹ = e7Data.rootOp K (ρ γ)
  exact add_left_cancel h1

section CharTwo

variable [CharP K 2]

private theorem mon_rootOp_sigma {n : Gp K} {σ : Fin e7Data.d → Fin e7Data.d}
    {ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (h : IsMon n σ ρ)
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (a : Fin e7Data.d) :
    e7Data.rootOp K (ρ γ) (Finsupp.single (σ a) 1) =
      endoE n (e7Data.rootOp K γ (Finsupp.single a 1)) := by
  rw [← h.rootOp_conj hγ, Module.End.mul_apply, Module.End.mul_apply, h.endo_inv_single a]

theorem IsMon.pr_neg_one_iff {n : Gp K} {σ : Fin e7Data.d → Fin e7Data.d}
    {ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (h : IsMon n σ ρ)
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (a : Fin e7Data.d) :
    pr (σ a) (ρ γ) = -1 ↔ pr a γ = -1 := by
  have hmain := mon_rootOp_sigma h hγ a
  rw [rootOp_single (K := K) (h.isRoot γ hγ) (σ a), rootOp_single (K := K) hγ a] at hmain
  constructor
  · intro h2
    by_contra h1
    rw [if_pos h2, if_neg h1, map_zero] at hmain
    exact Finsupp.single_ne_zero.2 (one_ne_zero : (1 : K) ≠ 0) hmain
  · intro h1
    by_contra h2
    rw [if_neg h2, if_pos h1, h.weight] at hmain
    exact Finsupp.single_ne_zero.2 (one_ne_zero : (1 : K) ≠ 0) hmain.symm

theorem IsMon.pr_eq {n : Gp K} {σ : Fin e7Data.d → Fin e7Data.d}
    {ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (h : IsMon n σ ρ)
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (a : Fin e7Data.d) :
    pr (σ a) (ρ γ) = pr a γ := by
  have hγ' := h.isRoot γ hγ
  have hn1 := h.pr_neg_one_iff hγ a
  have hn2 := h.pr_neg_one_iff (isRoot_neg hγ) a
  rw [h.neg γ hγ, pr_neg, pr_neg] at hn2
  rcases pr_mem hγ a with hx | hx | hx
  · have hy : pr (σ a) (ρ γ) = -1 := hn1.2 hx
    omega
  · rcases pr_mem hγ' (σ a) with hy | hy | hy
    · have := hn1.1 hy
      omega
    · omega
    · have := hn2.1 (by omega)
      omega
  · have := hn2.2 (by omega)
    omega

theorem IsMon.shift_eq {n : Gp K} {σ : Fin e7Data.d → Fin e7Data.d}
    {ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (h : IsMon n σ ρ)
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) {a : Fin e7Data.d} (ha : pr a γ = -1) :
    σ (shift γ a) = shift (ρ γ) (σ a) := by
  have hγ' := h.isRoot γ hγ
  have hmain := mon_rootOp_sigma h hγ a
  have hp : pr (σ a) (ρ γ) = -1 := (h.pr_neg_one_iff hγ a).2 ha
  rw [rootOp_single (K := K) hγ' (σ a), if_pos hp, rootOp_single (K := K) hγ a, if_pos ha,
    h.weight] at hmain
  exact (Finsupp.single_left_injective (one_ne_zero : (1 : K) ≠ 0) hmain).symm

theorem IsMon.conj_UA {n : Gp K} {σ : Fin e7Data.d → Fin e7Data.d}
    {ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (h : IsMon n σ ρ) (a : Fin e7Data.d) :
    ∀ x ∈ UA K a, n * x * n⁻¹ ∈ UA K (σ a) := by
  have hgen : ∀ γ, γ ∈ Phi a → ∀ c : K, xE (ρ γ) c ∈ UA K (σ a) := by
    intro γ hγ c
    obtain ⟨hr, hp⟩ := mem_Phi.1 hγ
    apply Subgroup.subset_closure
    exact ⟨ρ γ, mem_Phi.2 ⟨h.isRoot γ hr, (h.pr_eq hr a).trans hp⟩, c, rfl⟩
  have hle : UA K a ≤ (UA K (σ a)).comap (MulAut.conj n).toMonoidHom := by
    show Subgroup.closure (XA K a) ≤ _
    rw [Subgroup.closure_le]
    rintro g ⟨γ, hγ, c, rfl⟩
    show n * xE γ c * n⁻¹ ∈ UA K (σ a)
    rw [h.conj γ (mem_Phi.1 hγ).1 c]
    exact hgen γ hγ c
  intro x hx
  exact hle hx

theorem IsMon.nearW_iff {n : Gp K} {σ : Fin e7Data.d → Fin e7Data.d}
    {ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)} (h : IsMon n σ ρ) (a b : Fin e7Data.d) :
    NearW (σ a) (σ b) ↔ NearW a b := by
  constructor
  · intro hN γ hγ hpa hpb
    have hN' := hN (ρ γ) (h.isRoot γ hγ) ((h.pr_eq hγ a).trans hpa) ((h.pr_eq hγ b).trans hpb)
    have hs1 : E7Model.shift (ρ γ) (σ b) = σ a := E7Model.shift_eq hN'
    have hs2 : σ (E7Model.shift γ b) = E7Model.shift (ρ γ) (σ b) := h.shift_eq hγ hpb
    have hs3 : E7Model.shift γ b = a := h.sigma_injective (hs2.trans hs1)
    rw [← hs3]
    exact E7Model.wt_shift hγ hpb
  · intro hN γ' hγ' hpa hpb
    obtain ⟨γ, hγ, rfl⟩ := h.surj γ' hγ'
    have hpa' : pr a γ = 1 := (h.pr_eq hγ a).symm.trans hpa
    have hpb' : pr b γ = -1 := (h.pr_eq hγ b).symm.trans hpb
    have hs1 : E7Model.shift γ b = a := E7Model.shift_eq (hN γ hγ hpa' hpb')
    have hs2 : σ (E7Model.shift γ b) = E7Model.shift (ρ γ) (σ b) := h.shift_eq hγ hpb'
    rw [hs1] at hs2
    rw [hs2]
    exact E7Model.wt_shift (h.isRoot γ hγ) hpb

private theorem mon_reflect_neg (i : Fin (Tag.rank .E7)) (u : Fin (Tag.rank .E7) → ℤ) :
    reflect .E7 i (-u) = -reflect .E7 i u := by
  funext j
  simp only [reflect, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, mul_neg,
    Finset.sum_neg_distrib]
  ring

theorem IsMon.nm (i : Fin (Tag.rank .E7)) :
    IsMon (e7Data_valid.nm K i) (e7Data_valid.sRefl i) (reflect .E7 i) := by
  refine ⟨fun a => ?_, fun γ hγ => (isRoot_reflect_iff i).2 hγ, fun γ _ => mon_reflect_neg i γ,
    fun γ hγ c => ?_, fun γ' hγ' => ⟨reflect .E7 i γ', (isRoot_reflect_iff i).2 hγ',
      reflect_reflect .E7 i γ'⟩⟩
  · change e7Data_valid.endo K (e7Data_valid.nm K i) (Finsupp.single a 1) = _
    rw [e7Data_valid.endo_nm, e7Data_valid.nOp_single (R := K)]
    by_cases h : e7Data.wt a i = 1
    · rw [if_pos h, ← Finsupp.single_neg, CharTwo.neg_eq]
    · rw [if_neg h]
  · obtain ⟨σ', hσ', hc⟩ := e7Data_valid.nm_conj_xm (k := K) hγ i
    have hσ1 : σ' = 1 := by
      rcases hσ' with h1 | h1
      · exact h1
      · rw [h1]
        exact CharTwo.neg_eq 1
    rw [hc c, hσ1, one_mul]

private theorem mon_prod_nm (l : List (Fin (Tag.rank .E7))) :
    ∃ (σ : Fin e7Data.d → Fin e7Data.d) (ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)),
      IsMon ((l.map (e7Data_valid.nm K)).prod) σ ρ := by
  induction l with
  | nil =>
    refine ⟨id, id, ?_⟩
    rw [List.map_nil, List.prod_nil]
    exact IsMon.one
  | cons i l ih =>
    obtain ⟨σ, ρ, hm⟩ := ih
    refine ⟨e7Data_valid.sRefl i ∘ σ, reflect .E7 i ∘ ρ, ?_⟩
    rw [List.map_cons, List.prod_cons]
    exact (IsMon.nm i).mul hm

theorem isMon_nW (w : W7 K) : ∃ σ ρ, IsMon (nW K w) σ ρ := by
  obtain ⟨ω, hω, hw⟩ :=
    (coxeterMatrix (e7Datum K).isFiniteType).toCoxeterSystem.exists_isReduced w
  have h : nW K w = (ω.map (e7Data_valid.nm K)).prod := by
    rw [hw]
    exact CFSG.LieType.Steinberg.nrep_wordProd (e7Datum_isCTGroupDatum K) hω
  rw [h]
  exact mon_prod_nm ω

theorem bruhat_mon (g : Gp K) :
    ∃ b₁ ∈ Bor K, ∃ b₂ ∈ Bor K, ∃ (n : Gp K) (σ : Fin e7Data.d → Fin e7Data.d)
      (ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)), IsMon n σ ρ ∧ g = b₁ * n * b₂ := by
  obtain ⟨w, b₁, hb₁, b₂, hb₂, hg⟩ := bruhat_decomp g
  obtain ⟨σ, ρ, hm⟩ := isMon_nW w
  exact ⟨b₁, hb₁, b₂, hb₂, nW K w, σ, ρ, hm, hg⟩

private theorem mon_orbit_actWord (ω : List ℕ) : ∀ a : Fin e7Data.d,
    (∃ (n : Gp K) (σ : Fin e7Data.d → Fin e7Data.d)
      (ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)), IsMon n σ ρ ∧
        σ (⟨0, by decide⟩ : Fin e7Data.d) = a) →
    ∃ (n : Gp K) (σ : Fin e7Data.d → Fin e7Data.d)
      (ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)), IsMon n σ ρ ∧
        ((σ (⟨0, by decide⟩ : Fin e7Data.d) : Fin e7Data.d) : ℕ) = actWord ω (a : ℕ) := by
  induction ω with
  | nil =>
    rintro a ⟨n, σ, ρ, hm, ha⟩
    exact ⟨n, σ, ρ, hm, congrArg Fin.val ha⟩
  | cons i ω ih =>
    rintro a ⟨n, σ, ρ, hm, ha⟩
    have hm' : IsMon (e7Data_valid.nm K (letter i) * n)
        (e7Data_valid.sRefl (letter i) ∘ σ) (reflect .E7 (letter i) ∘ ρ) :=
      (IsMon.nm (letter i)).mul hm
    have hfold : actWord (i :: ω) (a : ℕ) =
        actWord ω ((e7Data_valid.sRefl (letter i) a : Fin e7Data.d) : ℕ) := by
      rw [e7Data_valid.sRefl_val]
      try rfl
    obtain ⟨n', σ', ρ', hm'', hs⟩ := ih (e7Data_valid.sRefl (letter i) a)
      ⟨_, _, _, hm', congrArg (e7Data_valid.sRefl (letter i)) ha⟩
    exact ⟨n', σ', ρ', hm'', hs.trans hfold.symm⟩

theorem exists_isMon_of_weight (c : Fin e7Data.d) :
    ∃ (n : Gp K) (σ : Fin e7Data.d → Fin e7Data.d)
      (ρ : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ)), IsMon n σ ρ ∧
        σ (⟨0, by decide⟩ : Fin e7Data.d) = c := by
  obtain ⟨n, σ, ρ, hm, hσ⟩ := mon_orbit_actWord (K := K) (weightWords.getD c [])
    ⟨0, by decide⟩ ⟨1, id, id, IsMon.one, rfl⟩
  exact ⟨n, σ, ρ, hm, Fin.ext (hσ.trans (weightWords_correct c))⟩

end CharTwo

end CFSG.RankThree.GF2n.Smith81.E7X
