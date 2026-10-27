module

public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairsRoots
public import CFSG.LieType.Steinberg.Minuscule.Form
public import CFSG.LieType.Steinberg.Minuscule.Group

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

abbrev V (K : Type) [Field K] : Type := Fin e7Data.d →₀ K

abbrev EGrp (K : Type) [Field K] : Subgroup (Module.End K (V K))ˣ := e7Data_valid.minGroup K

abbrev theta : Fin (Tag.rank .E7) → ℤ := CFSG.SeitzReduction.highRoot .E7

@[expose] def pr (a : Fin e7Data.d) (γ : Fin (Tag.rank .E7) → ℤ) : ℤ := e7Data.wt a ⬝ᵥ γ

open _root_.Classical in
@[expose] def shift (γ : Fin (Tag.rank .E7) → ℤ) (a : Fin e7Data.d) : Fin e7Data.d :=
  if h : ∃ b : Fin e7Data.d, e7Data.wt b = e7Data.wt a + MinData.toWeight γ then h.choose else a

@[expose] def Perp : Set (Fin (Tag.rank .E7) → ℤ) :=
  {β | IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0}

@[expose] def idx0 : Finset (Fin e7Data.d) := Finset.univ.filter fun a => pr a theta = 0

theorem forall_isRoot_iff (P : (Fin (Tag.rank .E7) → ℤ) → Prop) :
    (∀ γ, IsRoot .E7 γ → P γ) ↔ ∀ k : Fin 126, P ((Tag.rootCertificate .E7).root k) := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  constructor
  · intro h k
    exact h _ (RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega))
  · intro h γ hγ
    obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hγ
    exact h ⟨k, by omega⟩

theorem isRoot_theta : IsRoot .E7 theta := CFSG.SeitzReduction.isRoot_highRoot .E7

theorem pr_mem {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (a : Fin e7Data.d) :
    pr a γ = -1 ∨ pr a γ = 0 ∨ pr a γ = 1 := by
  revert a
  refine (forall_isRoot_iff fun γ => ∀ a : Fin e7Data.d,
    pr a γ = -1 ∨ pr a γ = 0 ∨ pr a γ = 1).2 ?_ γ hγ
  unfold pr
  decide +kernel

theorem card_pr {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    (Finset.univ.filter fun a : Fin e7Data.d => pr a γ = 1).card = 12 ∧
    (Finset.univ.filter fun a : Fin e7Data.d => pr a γ = -1).card = 12 ∧
    (Finset.univ.filter fun a : Fin e7Data.d => pr a γ = 0).card = 32 := by
  refine (forall_isRoot_iff fun γ =>
    (Finset.univ.filter fun a : Fin e7Data.d => pr a γ = 1).card = 12 ∧
    (Finset.univ.filter fun a : Fin e7Data.d => pr a γ = -1).card = 12 ∧
    (Finset.univ.filter fun a : Fin e7Data.d => pr a γ = 0).card = 32).2 ?_ γ hγ
  unfold pr
  decide +kernel

theorem card_idx0 : idx0.card = 32 := (card_pr isRoot_theta).2.2

theorem mem_idx0 {a : Fin e7Data.d} : a ∈ idx0 ↔ pr a theta = 0 := by simp [idx0]

abbrev node1 : Fin (Tag.rank .E7) := ⟨0, by decide⟩

theorem toWeight_theta : MinData.toWeight theta = Pi.single node1 1 := by
  funext i
  fin_cases i <;> decide +kernel

theorem pair_theta (γ : Fin (Tag.rank .E7) → ℤ) : MinData.toWeight γ ⬝ᵥ theta = γ node1 := by
  rw [form_comm posDef_cartan_E7, toWeight_theta, single_dotProduct, one_mul]

theorem perp_iff {β : Fin (Tag.rank .E7) → ℤ} : β ∈ Perp ↔ IsRoot .E7 β ∧ β node1 = 0 := by
  simp only [Perp, Set.mem_setOf_eq, pair_theta]

theorem wt_injective {a b : Fin e7Data.d} (h : e7Data.wt a = e7Data.wt b) : a = b :=
  e7Data_valid.wt_injective h

theorem shift_eq {γ : Fin (Tag.rank .E7) → ℤ} {a b : Fin e7Data.d}
    (hb : e7Data.wt b = e7Data.wt a + MinData.toWeight γ) : shift γ a = b := by
  classical
  have h : ∃ b : Fin e7Data.d, e7Data.wt b = e7Data.wt a + MinData.toWeight γ := ⟨b, hb⟩
  rw [shift, dif_pos h]
  exact wt_injective (h.choose_spec.trans hb.symm)

theorem exists_wt_shift_aux : ∀ γ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 γ →
    ∀ a : Fin e7Data.d, pr a γ = -1 →
      ∃ b : Fin e7Data.d, e7Data.wt b = e7Data.wt a + MinData.toWeight γ := by
  refine (forall_isRoot_iff fun γ => ∀ a : Fin e7Data.d, pr a γ = -1 →
    ∃ b : Fin e7Data.d, e7Data.wt b = e7Data.wt a + MinData.toWeight γ).2 ?_
  unfold pr
  decide +kernel

theorem exists_wt_shift {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) {a : Fin e7Data.d}
    (h : pr a γ = -1) : ∃ b : Fin e7Data.d, e7Data.wt b = e7Data.wt a + MinData.toWeight γ :=
  exists_wt_shift_aux γ hγ a h

theorem wt_shift {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) {a : Fin e7Data.d}
    (h : pr a γ = -1) : e7Data.wt (shift γ a) = e7Data.wt a + MinData.toWeight γ := by
  obtain ⟨b, hb⟩ := exists_wt_shift hγ h
  rw [shift_eq hb]
  exact hb

theorem pr_shift {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) {a : Fin e7Data.d}
    (h : pr a γ = -1) (δ : Fin (Tag.rank .E7) → ℤ) :
    pr (shift γ a) δ = pr a δ + MinData.toWeight γ ⬝ᵥ δ := by
  unfold pr
  rw [wt_shift hγ h, add_dotProduct]

theorem cartan_symm_E7 (i j : Fin (Tag.rank .E7)) :
    (Tag.cartan .E7) i j = (Tag.cartan .E7) j i := cartan_symm posDef_cartan_E7 i j

set_option maxRecDepth 20000 in
theorem rootOp_single {K : Type} [Field K] [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ}
    (hγ : IsRoot .E7 γ) (a : Fin e7Data.d) :
    e7Data.rootOp K γ (Finsupp.single a 1) =
      if pr a γ = -1 then Finsupp.single (shift γ a) 1 else 0 := by
  by_cases h : pr a γ = -1
  · rw [if_pos h]
    have hne : e7Data.rootOp K γ (Finsupp.single a 1) ≠ 0 :=
      (e7Data_valid.rootOp_single_ne_zero_iff cartan_symm_E7 hγ a).2 h
    rcases e7Data_valid.isSignedMap_rootOp (R := K) hγ a with h0 | ⟨b, hb, hs⟩
    · exact absurd h0 hne
    · rw [shift_eq hb]
      rcases hs with hs | hs
      · exact hs
      · rw [hs, ← Finsupp.single_neg, CharTwo.neg_eq]
  · rw [if_neg h]
    by_contra hne
    exact h ((e7Data_valid.rootOp_single_ne_zero_iff cartan_symm_E7 hγ a).1 hne)

theorem isRoot_neg {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) : IsRoot .E7 (-γ) :=
  CFSG.LieType.Chevalley.IsRoot.neg hγ

theorem pr_shift_self {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) {a : Fin e7Data.d}
    (h : pr a γ = -1) : pr (shift γ a) γ = 1 := by
  rw [pr_shift hγ h, h, form_self_root posDef_cartan_E7 hγ]
  norm_num

theorem pr_neg (a : Fin e7Data.d) (γ : Fin (Tag.rank .E7) → ℤ) : pr a (-γ) = - pr a γ := by
  simp [pr]

theorem shift_neg_shift {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) {a : Fin e7Data.d}
    (h : pr a γ = -1) : shift (-γ) (shift γ a) = a := by
  apply shift_eq
  rw [wt_shift hγ h, MinData.toWeight_neg]
  abel

theorem pr_shift_neg {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) {b : Fin e7Data.d}
    (h : pr b γ = 1) : pr (shift (-γ) b) γ = -1 := by
  have h1 : pr b (-γ) = -1 := by rw [pr_neg, h]
  have h3 := pr_shift (isRoot_neg hγ) h1 γ
  rw [h, MinData.toWeight_neg, neg_dotProduct, form_self_root posDef_cartan_E7 hγ] at h3
  omega

theorem shift_shift_neg {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) {b : Fin e7Data.d}
    (h : pr b γ = 1) : shift γ (shift (-γ) b) = b := by
  have h1 : pr b (-γ) = -1 := by rw [pr_neg, h]
  have h2 := pr_shift_neg hγ h
  apply shift_eq
  rw [wt_shift (isRoot_neg hγ) h1, MinData.toWeight_neg]
  abel

theorem rootOp_apply {K : Type} [Field K] [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ}
    (hγ : IsRoot .E7 γ) (v : V K) (b : Fin e7Data.d) :
    (e7Data.rootOp K γ v) b = if pr b γ = 1 then v (shift (-γ) b) else 0 := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw =>
    rw [map_add, Finsupp.add_apply, hv, hw, Finsupp.add_apply]
    split_ifs <;> simp
  | single a c =>
    have e : (Finsupp.single a c : V K) = c • Finsupp.single a 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [e, map_smul, rootOp_single hγ]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    by_cases ha : pr a γ = -1
    · rw [if_pos ha]
      by_cases hb : shift γ a = b
      · have hb1 : pr b γ = 1 := hb ▸ pr_shift_self hγ ha
        have hab : a = shift (-γ) b := by rw [← hb, shift_neg_shift hγ ha]
        simp [hb, hb1, ← hab, Finsupp.single_apply]
      · by_cases hb1 : pr b γ = 1
        · have hab : a ≠ shift (-γ) b := by
            intro hab
            apply hb
            rw [hab, shift_shift_neg hγ hb1]
          simp [hb, hb1, hab, Finsupp.single_apply]
        · simp [hb, hb1, Finsupp.single_apply]
    · rw [if_neg ha]
      by_cases hb1 : pr b γ = 1
      · have hab : a ≠ shift (-γ) b := by
          intro hab
          apply ha
          rw [hab]
          exact pr_shift_neg hγ hb1
        simp [hb1, hab, Finsupp.single_apply]
      · simp [hb1]

theorem xu_apply_coord {K : Type} [Field K] [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ}
    (hγ : IsRoot .E7 γ) (c : K) (v : V K) (b : Fin e7Data.d) :
    ((e7Data_valid.xu K γ c : (Module.End K (V K))ˣ) : Module.End K (V K)) v b =
      v b + c * (if pr b γ = 1 then v (shift (-γ) b) else 0) := by
  rw [e7Data_valid.xu_apply, Finsupp.add_apply, Finsupp.smul_apply, rootOp_apply hγ, smul_eq_mul]

end CFSG.RankThree.GF2n.Smith81.E7Model
