module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.Sporadic.Suz.Simple
public import Certificates.Data.SUSmallBase

public section

namespace CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma hdRo7SmBDAux_ext {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) (SMV m))
    {e₁ e₂ : SMGL m} (h : ∀ k, e₁ (b k) = e₂ (b k)) : e₁ = e₂ := by
  apply LinearEquiv.ext
  intro v
  have h' : (e₁ : SMV m →ₗ[ZMod 3] SMV m) = (e₂ : SMV m →ₗ[ZMod 3] SMV m) := by
    apply Module.Basis.ext
    exact h
  exact congrArg (fun f : SMV m →ₗ[ZMod 3] SMV m => f v) h'

lemma hdRo7SmBDAux_diagMap_apply {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (d : Fin m → (ZMod 3)ˣ) (k : Fin m) :
    ZS.diagMap 3 b d (b k) = (d k : ZMod 3) • b k := by
  apply b.equivFun.injective
  rw [map_smul]
  rw [ZS.diagMap, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  have hk : b.equivFun (b k) = Pi.single k 1 := by
    funext j
    rw [Module.Basis.equivFun_self, Pi.single_apply]
    by_cases h : k = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  rw [hk]
  funext j
  by_cases h : j = k
  · subst h; rfl
  · simp [Pi.single_apply, h]

lemma hdRo7SmBDAux_permMap_apply {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (σ : Equiv.Perm (Fin m)) (k : Fin m) :
    ZS.permMap 3 b σ (b k) = b (σ k) :=
  Module.Basis.equiv_apply (b := b) (b' := b) (e := σ) (i := k)

lemma hdRo7SmBDAux_permMap_mul {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (σ τ : Equiv.Perm (Fin m)) :
    ZS.permMap 3 b (σ * τ) = ZS.permMap 3 b σ * ZS.permMap 3 b τ := by
  apply hdRo7SmBDAux_ext b
  intro k
  rw [LinearEquiv.mul_apply, hdRo7SmBDAux_permMap_apply, hdRo7SmBDAux_permMap_apply,
    hdRo7SmBDAux_permMap_apply, Equiv.Perm.mul_apply]

lemma hdRo7SmBDAux_permMap_one {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) :
    ZS.permMap 3 b (1 : Equiv.Perm (Fin m)) = 1 := by
  rw [ZS.permMap, show (1 : Equiv.Perm (Fin m)) = Equiv.refl (Fin m) from rfl,
    Module.Basis.equiv_refl]
  rfl

@[expose]
noncomputable def hdRo7SmBDAux_sgn {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (k : Fin m) : SMGL m :=
  ZS.diagMap 3 b (fun l => if l = k then -1 else 1)

lemma hdRo7SmBDAux_sgn_apply {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (k l : Fin m) :
    hdRo7SmBDAux_sgn b k (b l) = (if l = k then -1 else 1 : ZMod 3) • b l := by
  rw [hdRo7SmBDAux_sgn, hdRo7SmBDAux_diagMap_apply]
  congr 1
  by_cases h : l = k <;> simp [h]

lemma hdRo7SmBDAux_permMap_inv {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (σ : Equiv.Perm (Fin m)) :
    (ZS.permMap 3 b σ)⁻¹ = ZS.permMap 3 b σ⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← hdRo7SmBDAux_permMap_mul, mul_inv_cancel, hdRo7SmBDAux_permMap_one]

lemma hdRo7SmBDAux_conj_perm_sgn {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (σ : Equiv.Perm (Fin m)) (k : Fin m) :
    ZS.permMap 3 b σ * hdRo7SmBDAux_sgn b k * (ZS.permMap 3 b σ)⁻¹ =
      hdRo7SmBDAux_sgn b (σ k) := by
  rw [hdRo7SmBDAux_permMap_inv]
  apply hdRo7SmBDAux_ext b
  intro l
  simp only [hdRo7SmBDAux_permMap_apply, hdRo7SmBDAux_sgn_apply, LinearEquiv.mul_apply,
    map_smul]
  simp [Equiv.symm_apply_eq]

lemma hdRo7SmBDAux_sgn_mem_of_conj {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (G : Subgroup (SMGL m))
    (hperm : ∀ σ, ZS.permMap 3 b σ ∈ G) {k₀ k : Fin m}
    (hk : hdRo7SmBDAux_sgn b k₀ ∈ G) : hdRo7SmBDAux_sgn b k ∈ G := by
  have h := hdRo7SmBDAux_conj_perm_sgn b (Equiv.swap k₀ k) k₀
  rw [Equiv.swap_apply_left] at h
  rw [← h]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hperm _) hk) (Subgroup.inv_mem _ (hperm _))

lemma hdRo7SmBDAux_list_prod_sgn_apply {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (l : List (Fin m)) (k : Fin m) :
    (l.map (fun i => hdRo7SmBDAux_sgn b i)).prod (b k) =
      (l.map (fun i => (if k = i then -1 else 1 : ZMod 3))).prod • b k := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, LinearEquiv.mul_apply, ih, map_smul,
      hdRo7SmBDAux_sgn_apply, smul_smul]
    rw [mul_comm]

lemma hdRo7SmBDAux_list_prod_sign {m : ℕ} (l : List (Fin m)) (hnd : l.Nodup)
    (k : Fin m) :
    (l.map (fun i => (if k = i then -1 else 1 : ZMod 3))).prod =
      (if k ∈ l then -1 else 1) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    have hnd' : l.Nodup := (List.nodup_cons.mp hnd).2
    have hnot : i ∉ l := (List.nodup_cons.mp hnd).1
    rw [List.map_cons, List.prod_cons, ih hnd']
    by_cases hki : k = i
    · subst hki
      rw [if_pos rfl, if_neg hnot, if_pos (List.mem_cons_self)]
      ring
    · rw [if_neg hki]
      by_cases hmem : k ∈ l
      · rw [if_pos hmem, if_pos (List.mem_cons_of_mem i hmem)]
        ring
      · rw [if_neg hmem, if_neg (fun h => by
            rcases List.mem_cons.mp h with h' | h'
            · exact hki h'
            · exact hmem h')]
        ring

@[expose]
def hdRo7SmBDAux_fullPred {m : ℕ} (b : Module.Basis (Fin m) (ZMod 3) (SMV m))
    (a : SMGL m) : Prop :=
  ∃ (σ : Equiv.Perm (Fin m)) (c : Fin m → ZMod 3),
    (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i)

@[expose]
noncomputable def hdRo7SmBDAux_fullSubgroup {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) : Subgroup (SMGL m) where
  carrier := {a | hdRo7SmBDAux_fullPred b a}
  one_mem' := by
    refine ⟨1, fun _ => 1, ?_, ?_⟩
    · intro i; left; rfl
    · intro i; simp
  mul_mem' := by
    rintro a a' ⟨σ, c, hc, ha⟩ ⟨σ', c', hc', ha'⟩
    refine ⟨σ * σ', fun i => c' i * c (σ' i), ?_, ?_⟩
    · intro i
      change c' i * c (σ' i) = 1 ∨ c' i * c (σ' i) = -1
      rcases hc' i with h | h <;> rcases hc (σ' i) with h2 | h2
      · left; rw [h, h2]; ring
      · right; rw [h, h2]; ring
      · right; rw [h, h2]; ring
      · left; rw [h, h2]; ring
    · intro i
      rw [LinearEquiv.mul_apply, ha', map_smul, ha, Equiv.Perm.mul_apply, smul_smul]
  inv_mem' := by
    rintro a ⟨σ, c, hc, ha⟩
    refine ⟨σ.symm, fun j => c (σ.symm j), ?_, ?_⟩
    · intro j; exact hc (σ.symm j)
    · intro j
      change a.symm (b j) = c (σ.symm j) • b (σ.symm j)
      rw [LinearEquiv.symm_apply_eq, map_smul, ha, Equiv.apply_symm_apply, smul_smul]
      have hcc : c (σ.symm j) * c (σ.symm j) = 1 := by
        rcases hc (σ.symm j) with h | h <;> rw [h] <;> ring
      rw [hcc, one_smul]

lemma hdRo7SmBDAux_fullPred_mem {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (G : Subgroup (SMGL m))
    (hperm : ∀ σ, ZS.permMap 3 b σ ∈ G)
    (hsgn : ∀ k, hdRo7SmBDAux_sgn b k ∈ G)
    {a : SMGL m} (ha : hdRo7SmBDAux_fullPred b a) : a ∈ G := by
  obtain ⟨σ, c, hc, ha'⟩ := ha
  let l : List (Fin m) := (Finset.univ.filter (fun k => c k = -1)).toList
  have hnd : l.Nodup := Finset.nodup_toList _
  have hmem : ∀ k, k ∈ l ↔ c k = -1 := by
    intro k
    simp only [l, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  have hdM : (l.map (fun i => hdRo7SmBDAux_sgn b i)).prod ∈ G := by
    induction l with
    | nil => simp
    | cons i l ih =>
      rw [List.map_cons, List.prod_cons]
      exact Subgroup.mul_mem _ (hsgn i) ih
  have hdecomp : a = ZS.permMap 3 b σ * (l.map (fun i => hdRo7SmBDAux_sgn b i)).prod := by
    apply hdRo7SmBDAux_ext b
    intro k
    rw [LinearEquiv.mul_apply, hdRo7SmBDAux_list_prod_sgn_apply, map_smul,
      hdRo7SmBDAux_permMap_apply, ha' k, hdRo7SmBDAux_list_prod_sign l hnd k]
    congr 1
    by_cases hkl : k ∈ l
    · rw [if_pos hkl]; exact (hmem k).mp hkl
    · rw [if_neg hkl]
      have hcne : c k ≠ -1 := fun h => hkl ((hmem k).mpr h)
      rcases hc k with h | h
      · exact h
      · exact absurd h hcne
  rw [hdecomp]
  exact Subgroup.mul_mem _ (hperm σ) hdM

lemma hdRo7SmBDAux_isPerm_permMap {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    SMIsPerm (ZS.permMap 3 (Pi.basisFun (ZMod 3) (Fin m)) σ) := by
  let b := Pi.basisFun (ZMod 3) (Fin m)
  refine ⟨σ, fun v i => ?_⟩
  let ψ : SMV m →ₗ[ZMod 3] SMV m :=
    LinearMap.pi (fun i => (LinearMap.proj (σ.symm i) : SMV m →ₗ[ZMod 3] ZMod 3))
  have hψ : ∀ k, ZS.permMap 3 b σ (b k) = ψ (b k) := by
    intro k
    funext i
    rw [hdRo7SmBDAux_permMap_apply]
    simp [ψ, b, Pi.basisFun_apply, Pi.single_apply, Equiv.symm_apply_eq]
  have hφψ : (ZS.permMap 3 b σ : SMV m →ₗ[ZMod 3] SMV m) = ψ :=
    Module.Basis.ext (b := b) hψ
  have h := congrFun (congrArg (fun f : SMV m →ₗ[ZMod 3] SMV m => f v) hφψ) i
  exact h.trans (by simp [ψ])

lemma hdRo7SmBDAux_fullPred_of_isPerm {m : ℕ}
    (b : Module.Basis (Fin m) (ZMod 3) (SMV m)) (hb : ∀ k, b k = Pi.single k (1 : ZMod 3))
    {g : SMGL m} (h : SMIsPerm g) : hdRo7SmBDAux_fullPred b g := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ, fun _ => 1, fun i => Or.inl rfl, fun i => ?_⟩
  rw [one_smul]
  funext j
  rw [hb i, hb (σ i)]
  have h1 := hσ (b i) j
  rw [hb i] at h1
  rw [h1]
  simp [Pi.single_apply, Equiv.symm_apply_eq]

end CFSG.StandardType.HdRo7SU.Small
