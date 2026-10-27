module

public import CFSG.Quasithin.Background.HA7Row
public import CFSG.Quasithin.Background.HL42Aut

public section

namespace CFSG.Quasithin

namespace H

namespace A7

open CFSG.Open Matrix Equiv PairG
open scoped Matrix

theorem add_self_vec (x : Fin 4 → ZMod 2) : x + x = 0 := by
  funext i
  have : ∀ y : ZMod 2, y + y = 0 := by decide
  exact this (x i)

theorem exists_comm_of_card_fix_four (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (hM : M * M = 1)
    (h4 : (Finset.univ.filter fun v : Fin 4 → ZMod 2 => M *ᵥ v = v).card = 4)
    (v : Fin 4 → ZMod 2) (hv : M *ᵥ v = v) : ∃ w : Fin 4 → ZMod 2, M *ᵥ w + w = v := by
  let φ : (Fin 4 → ZMod 2) →+ (Fin 4 → ZMod 2) :=
    { toFun := fun w => M *ᵥ w + w
      map_zero' := by rw [Matrix.mulVec_zero, add_zero]
      map_add' := fun a b => by
        change M *ᵥ (a + b) + (a + b) = M *ᵥ a + a + (M *ᵥ b + b)
        rw [Matrix.mulVec_add]
        abel }
  have hφ : ∀ w, φ w = M *ᵥ w + w := fun w => rfl
  have hker : ∀ w, w ∈ φ.ker ↔ M *ᵥ w = w := by
    intro w
    rw [AddMonoidHom.mem_ker, hφ]
    constructor
    · intro h
      calc M *ᵥ w = M *ᵥ w + (w + w) := by rw [add_self_vec, add_zero]
        _ = M *ᵥ w + w + w := (add_assoc _ _ _).symm
        _ = w := by rw [h, zero_add]
    · intro h
      rw [h, add_self_vec]
  have hcard : Nat.card φ.ker = 4 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hker), Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    exact h4
  have hle : φ.range ≤ φ.ker := by
    rintro _ ⟨w, rfl⟩
    rw [hker, hφ, Matrix.mulVec_add, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec,
      add_comm (M *ᵥ w) w]
  have hrange : Nat.card φ.range = 4 := by
    have h1 := AddSubgroup.card_ker_mul_card_range φ
    rw [hcard, card_fin_four_fun] at h1
    omega
  have heq : φ.range = φ.ker := AddSubgroup.eq_of_le_of_card_ge hle (by rw [hcard, hrange])
  have hv' : v ∈ φ.range := by
    rw [heq, hker]
    exact hv
  obtain ⟨w, hw⟩ := hv'
  exact ⟨w, hw⟩

theorem dot_comm_eq_zero {g : GL (Fin 4) (ZMod 2)} {b : Fin 4 → ZMod 2}
    (hb : ((L4.dual4 g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ b = b)
    (v : Fin 4 → ZMod 2) :
    ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v + v) ⬝ᵥ b = 0 := by
  have h1 : (g : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ b = b := by
    have h := congrArg (fun w => (g : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ w) hb
    simp only [L4.coe_dual4, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.transpose_one, Matrix.one_mulVec] at h
    exact h.symm
  have h2 : ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) ⬝ᵥ b = v ⬝ᵥ b := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h1,
      dotProduct_comm]
  rw [add_dotProduct, h2]
  have : ∀ y : ZMod 2, y + y = 0 := by decide
  exact this _

theorem exists_fix_add_comm {γ : GL (Fin 4) (ZMod 2)} {k : ℕ} (hγm : γ ^ (2 * k + 1) = 1)
    (v : Fin 4 → ZMod 2) : ∃ a w : Fin 4 → ZMod 2,
      (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ a = a ∧
        v = a + ((γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w + w) := by
  set g := (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) with hg
  have hgm : g ^ (2 * k + 1) = 1 := by rw [hg, ← Units.val_pow_eq_pow_val, hγm, Units.val_one]
  have key : ∀ j : ℕ, ∑ i ∈ Finset.range (2 * j + 1), g ^ i *ᵥ v =
      v + (g *ᵥ (∑ i ∈ Finset.range j, g ^ (2 * i + 1) *ᵥ v) +
        ∑ i ∈ Finset.range j, g ^ (2 * i + 1) *ᵥ v) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, Finset.sum_range_succ, Matrix.mulVec_add, Matrix.mulVec_mulVec,
        ← pow_succ']
      abel
  have hfix : g *ᵥ (∑ i ∈ Finset.range (2 * k + 1), g ^ i *ᵥ v) =
      ∑ i ∈ Finset.range (2 * k + 1), g ^ i *ᵥ v := by
    rw [Matrix.mulVec_sum]
    simp only [Matrix.mulVec_mulVec, ← pow_succ']
    rw [Finset.sum_range_succ, hgm, Finset.sum_range_succ', pow_zero]
  refine ⟨_, ∑ i ∈ Finset.range k, g ^ (2 * i + 1) *ᵥ v, hfix, ?_⟩
  rw [key k, add_assoc, add_self_vec, add_zero]

theorem eq_zero_of_dual_fix {γ d : GL (Fin 4) (ZMod 2)} {k : ℕ} (hγm : γ ^ (2 * k + 1) = 1)
    (hγ4 : (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v).card = 4)
    (hd2 : d * d = 1) (hd4 : (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      (d : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v).card ≤ 4)
    (hsub : ∀ v, (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v →
      (d : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v) {b : Fin 4 → ZMod 2}
    (hbd : ((L4.dual4 d : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ b = b)
    (hbγ : ((L4.dual4 γ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ b = b) :
    b = 0 := by
  classical
  have hd4' : (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      (d : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v).card = 4 := by
    refine le_antisymm hd4 ?_
    calc 4 = _ := hγ4.symm
      _ ≤ _ := Finset.card_le_card fun v hv => by
        rw [Finset.mem_filter] at hv ⊢
        exact ⟨hv.1, hsub v hv.2⟩
  have hdd : (d : Matrix (Fin 4) (Fin 4) (ZMod 2)) * d = 1 := by
    rw [← Units.val_mul, hd2, Units.val_one]
  have hperp : ∀ v, v ⬝ᵥ b = 0 := by
    intro v
    obtain ⟨a, w, ha, rfl⟩ := exists_fix_add_comm hγm v
    obtain ⟨w', hw'⟩ := exists_comm_of_card_fix_four _ hdd hd4' a (hsub a ha)
    rw [add_dotProduct, dot_comm_eq_zero hbγ w, ← hw', dot_comm_eq_zero hbd w', add_zero]
  funext i
  have h := hperp (Pi.single i 1)
  rw [single_one_dotProduct] at h
  exact h


variable (α : ↥(alternatingGroup (Fin 8)) ≃* GL (Fin 4) (ZMod 2))

theorem θ_not_inner : ¬ ∃ g : Γ α, ∀ γ : Γ α, θ α γ = g * γ * g⁻¹ := by
  rintro ⟨g₀, hg₀⟩
  obtain ⟨g, rfl⟩ := (ψ α).surjective g₀
  have hθg : ∀ σ : alternatingGroup (Fin 7),
      MulAut.conjNormal (H := alternatingGroup (Fin 7)) s σ = g * σ * g⁻¹ := by
    intro σ
    apply (ψ α).injective
    rw [← θ_apply, hg₀, map_mul, map_mul, map_inv]
  have hsg : (MulAut.conjNormal (H := alternatingGroup (Fin 7)) s) =
      MulAut.conjNormal (H := alternatingGroup (Fin 7)) (g : Perm (Fin 7)) := by
    refine MulEquiv.ext fun σ => Subtype.ext ?_
    rw [hθg, MulAut.conjNormal_apply]
    rfl
  have hs := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)).1 hsg
  have h1 := sign_s
  rw [hs, Equiv.Perm.mem_alternatingGroup.mp g.2] at h1
  exact absurd h1 (by decide)

@[expose] def s8 : Perm (Fin 8) := swap 0 1

omit α in
theorem viaEmbedding_s : Equiv.Perm.viaEmbedding s Fin.castSuccEmb = s8 := by
  ext j : 1
  induction j using Fin.lastCases with
  | last =>
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem]
    · decide
    · rintro ⟨i, hi⟩
      exact Fin.castSucc_ne_last i hi
  | cast i =>
    have h := Equiv.Perm.viaEmbedding_apply s Fin.castSuccEmb i
    rw [show Fin.castSucc i = Fin.castSuccEmb i from rfl, h]
    fin_cases i <;> decide

omit α in
theorem altLift7_conj (σ : alternatingGroup (Fin 7)) :
    altLift7 (MulAut.conjNormal (H := alternatingGroup (Fin 7)) s σ) =
      MulAut.conjNormal (H := alternatingGroup (Fin 8)) s8 (altLift7 σ) := by
  apply Subtype.ext
  rw [coe_altLift7, MulAut.conjNormal_apply, MulAut.conjNormal_apply, coe_altLift7,
    ← Equiv.Perm.viaEmbeddingHom_apply, map_mul, map_mul, map_inv,
    Equiv.Perm.viaEmbeddingHom_apply, viaEmbedding_s]
  rfl

theorem exists_dual : ∃ c : GL (Fin 4) (ZMod 2), ∀ γ : Γ α,
    ((θ α γ : Γ α) : GL (Fin 4) (ZMod 2)) = c * L4.dual4 γ * c⁻¹ := by
  let Θ : MulAut (GL (Fin 4) (ZMod 2)) :=
    (α.symm.trans (MulAut.conjNormal (H := alternatingGroup (Fin 8)) s8)).trans α
  have hΘ : ∀ γ : Γ α, Θ γ = ((θ α γ : Γ α) : GL (Fin 4) (ZMod 2)) := by
    intro γ
    obtain ⟨σ, rfl⟩ := (ψ α).surjective γ
    rw [θ_apply, coe_ψ, coe_ψ]
    change α (MulAut.conjNormal (H := alternatingGroup (Fin 8)) s8 (α.symm (α (altLift7 σ)))) =
      α (altLift7 _)
    rw [MulEquiv.symm_apply_apply, altLift7_conj]
  obtain ⟨c, hc | hc⟩ := L4.exists_aut4 Θ
  · exfalso
    have hcN : c ∈ Subgroup.normalizer (Γ α : Set (GL (Fin 4) (ZMod 2))) := by
      refine mem_normalizer_of_matAut (fun γ hγ => ⟨_, (θ α ⟨γ, hγ⟩).2, ?_⟩) fun γ hγ => ?_
      · rw [← hc]
        exact hΘ ⟨γ, hγ⟩
      · obtain ⟨δ, hδ⟩ := (θ α).surjective ⟨γ, hγ⟩
        refine ⟨δ, δ.2, ?_⟩
        have h1 := hc δ
        rw [hΘ, hδ] at h1
        have h2 : (γ : GL (Fin 4) (ZMod 2)) = c * δ * c⁻¹ := h1
        rw [h2]
        group
    rw [normalizer_eq] at hcN
    exact θ_not_inner α ⟨⟨c, hcN⟩, fun γ => Subtype.ext (by rw [← hΘ, hc]; rfl)⟩
  · exact ⟨c, fun γ => by rw [← hΘ, hc]⟩

omit α in
theorem dual4_dual4 (g : GL (Fin 4) (ZMod 2)) : L4.dual4 (L4.dual4 g) = g :=
  Units.ext (Matrix.transpose_transpose _)

omit α in
theorem card_fix_mat (g : GL (Fin 4) (ZMod 2)) :
    Nat.card {a : StdMod (Fin 4) (ZMod 2) // matAut g a = a} =
      (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
        (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v).card := by
  have e : Nat.card {a : StdMod (Fin 4) (ZMod 2) // matAut g a = a} =
      Nat.card {v : Fin 4 → ZMod 2 // (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v} :=
    Nat.card_congr
      { toFun := fun v => ⟨Multiplicative.toAdd v.1, congrArg Multiplicative.toAdd v.2⟩
        invFun := fun v => ⟨Multiplicative.ofAdd v.1, congrArg Multiplicative.ofAdd v.2⟩
        left_inv := fun v => rfl
        right_inv := fun v => rfl }
  rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype]

omit α in
theorem card_filter_conj (c g : GL (Fin 4) (ZMod 2)) :
    (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      ((c * g * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v).card =
    (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact card_fix_conj_mat c g

omit α in
theorem mulVec_conj (c g : GL (Fin 4) (ZMod 2)) (w : Fin 4 → ZMod 2) :
    ((c * g * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w = w ↔
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        (((c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w) =
        ((c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w := by
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    have h' := congrArg (fun z => ((c⁻¹ : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ z) h
    simp only [mulVec_inv_mulVec] at h'
    exact h'
  · intro h
    rw [h, mulVec_mulVec_inv]

omit α in
theorem eq_zero_caseA {γ d c : GL (Fin 4) (ZMod 2)} {k : ℕ} (hγm : γ ^ (2 * k + 1) = 1)
    (hγ4 : (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v).card = 4)
    (hd2 : d * d = 1) (hd4 : (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      (d : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v).card ≤ 4)
    (hsub : ∀ v, (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v →
      (d : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v) {b : Fin 4 → ZMod 2}
    (hbd : ((c * L4.dual4 d * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      b = b)
    (hbγ : ((c * L4.dual4 γ * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      b = b) : b = 0 := by
  have h := eq_zero_of_dual_fix hγm hγ4 hd2 hd4 hsub ((mulVec_conj c _ b).mp hbd)
    ((mulVec_conj c _ b).mp hbγ)
  have h2 := mulVec_mulVec_inv c b
  rw [h, Matrix.mulVec_zero] at h2
  exact h2.symm

omit α in
theorem eq_zero_caseB {γ d c : GL (Fin 4) (ZMod 2)} {k : ℕ} (hγm : γ ^ (2 * k + 1) = 1)
    (hγ4 : (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      ((c * L4.dual4 γ * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v =
        v).card = 4)
    (hd2 : d * d = 1) (hd4 : (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      ((c * L4.dual4 d * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v =
        v).card ≤ 4)
    (hsub : ∀ w, ((c * L4.dual4 γ * c⁻¹ : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w = w → ((c * L4.dual4 d * c⁻¹ : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w = w) {a : Fin 4 → ZMod 2}
    (had : (d : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ a = a)
    (haγ : (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ a = a) : a = 0 := by
  rw [card_filter_conj] at hγ4 hd4
  refine eq_zero_of_dual_fix (γ := L4.dual4 γ) (d := L4.dual4 d) (k := k)
    (by rw [← map_pow, hγm, map_one]) hγ4 (by rw [← map_mul, hd2, map_one]) hd4
    (fun v hv => ?_) ?_ ?_
  · have h1 : ((c * L4.dual4 γ * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        ((c : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) =
        (c : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v :=
      (mulVec_conj c _ _).mpr (by rw [mulVec_inv_mulVec]; exact hv)
    have h2 := (mulVec_conj c _ _).mp (hsub _ h1)
    rwa [mulVec_inv_mulVec] at h2
  · rw [dual4_dual4]
    exact had
  · rw [dual4_dual4]
    exact haγ

omit α in
@[expose] def fixAdd (P : Matrix (Fin 4) (Fin 4) (ZMod 2)) : AddSubgroup (Fin 4 → ZMod 2) :=
  ({ carrier := {v | P *ᵥ v = v}
     add_mem' := fun {v w} hv hw => by
       have hv' : P *ᵥ v = v := hv
       have hw' : P *ᵥ w = w := hw
       change P *ᵥ (v + w) = v + w
       rw [Matrix.mulVec_add, hv', hw']
     zero_mem' := Matrix.mulVec_zero P
     smul_mem' := fun c v hv => by
       have hv' : P *ᵥ v = v := hv
       change P *ᵥ (c • v) = c • v
       rw [Matrix.mulVec_smul, hv'] } : Submodule (ZMod 2) (Fin 4 → ZMod 2)).toAddSubgroup

omit α in
theorem card_fixAdd (P : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    Nat.card ↥(fixAdd P) = (Finset.univ.filter fun v : Fin 4 → ZMod 2 => P *ᵥ v = v).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  rfl

omit α in
theorem card_fixAdd_inf (P Q : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    Nat.card ↥(fixAdd P ⊓ fixAdd Q) =
      (Finset.univ.filter fun v : Fin 4 → ZMod 2 => P *ᵥ v = v ∧ Q *ᵥ v = v).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  rfl

omit α in
theorem full_of_three {P Q : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (hP : (Finset.univ.filter fun v : Fin 4 → ZMod 2 => P *ᵥ v = v).card ≤ 4)
    (h3 : 3 ≤ (Finset.univ.filter fun v : Fin 4 → ZMod 2 => P *ᵥ v = v ∧ Q *ᵥ v = v).card) :
    (Finset.univ.filter fun v : Fin 4 → ZMod 2 => P *ᵥ v = v).card = 4 ∧
      ∀ v : Fin 4 → ZMod 2, P *ᵥ v = v → Q *ᵥ v = v := by
  rw [← card_fixAdd] at hP ⊢
  rw [← card_fixAdd_inf] at h3
  have hle : fixAdd P ⊓ fixAdd Q ≤ fixAdd P := inf_le_left
  have hd1 : Nat.card ↥(fixAdd P ⊓ fixAdd Q) ∣ Nat.card ↥(fixAdd P) :=
    AddSubgroup.card_dvd_of_le hle
  have hd2 : Nat.card ↥(fixAdd P) ∣ 2 ^ 4 := by
    have := AddSubgroup.card_addSubgroup_dvd_card (fixAdd P)
    rwa [card_fin_four_fun] at this
  have hle' : Nat.card ↥(fixAdd P ⊓ fixAdd Q) ≤ Nat.card ↥(fixAdd P) :=
    Nat.le_of_dvd Nat.card_pos hd1
  obtain ⟨k, hk, hPk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
  have hP4 : Nat.card ↥(fixAdd P) = 4 := by
    rw [hPk] at hP hle' ⊢
    interval_cases k <;> omega
  have hd3 : Nat.card ↥(fixAdd P ⊓ fixAdd Q) ∣ 2 ^ 2 := by
    rw [hP4] at hd1
    exact hd1
  obtain ⟨j, hj, hQj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd3
  have hQ4 : Nat.card ↥(fixAdd P ⊓ fixAdd Q) = 4 := by
    rw [hQj] at h3 ⊢
    interval_cases j <;> omega
  have heq : fixAdd P ⊓ fixAdd Q = fixAdd P :=
    AddSubgroup.eq_of_le_of_card_ge hle (by rw [hP4, hQ4])
  refine ⟨hP4, fun v hv => ?_⟩
  have hv0 : v ∈ fixAdd P := hv
  have hv' : v ∈ fixAdd P ⊓ fixAdd Q := by
    rw [heq]
    exact hv0
  exact (AddSubgroup.mem_inf.mp hv').2

omit α in
theorem card_mul_lt_eight {γ d c : GL (Fin 4) (ZMod 2)} {k : ℕ} (hγm : γ ^ (2 * k + 1) = 1)
    (hd2 : d * d = 1)
    (hγ4 : (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v).card ≤ 4)
    (hd4 : (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      (d : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v).card ≤ 4)
    (hγ4' : (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      ((c * L4.dual4 γ * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v =
        v).card ≤ 4)
    (hd4' : (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      ((c * L4.dual4 d * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v =
        v).card ≤ 4) :
    (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
        (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v ∧
          (d : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v).card *
      (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
        ((c * L4.dual4 γ * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v =
            v ∧
          ((c * L4.dual4 d * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v =
            v).card < 8 := by
  by_contra h8
  push Not at h8
  have ha : (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v ∧
        (d : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v).card ≤ 4 :=
    (Finset.card_le_card fun v hv => by
      rw [Finset.mem_filter] at hv ⊢
      exact ⟨hv.1, hv.2.1⟩).trans hγ4
  have hb : (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      ((c * L4.dual4 γ * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v =
          v ∧
        ((c * L4.dual4 d * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v =
          v).card ≤ 4 :=
    (Finset.card_le_card fun v hv => by
      rw [Finset.mem_filter] at hv ⊢
      exact ⟨hv.1, hv.2.1⟩).trans hγ4'
  rcases Nat.lt_or_ge (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
      (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v ∧
        (d : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v).card 3 with ha3 | ha3
  ·
    have hb3 : 3 ≤ (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
        ((c * L4.dual4 γ * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v =
            v ∧
          ((c * L4.dual4 d * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v =
            v).card := by
      by_contra h
      push Not at h
      have := Nat.mul_le_mul (Nat.le_of_lt_succ ha3) (Nat.le_of_lt_succ h)
      omega
    obtain ⟨h4, hsub⟩ := full_of_three hγ4' hb3
    have ha2 : 1 < (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
        (γ : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v ∧
          (d : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v).card := by
      by_contra h
      push Not at h
      have := Nat.mul_le_mul h hb
      omega
    obtain ⟨v, hv, hv0⟩ := Finset.exists_mem_ne ha2 0
    rw [Finset.mem_filter] at hv
    exact hv0 (eq_zero_caseB hγm h4 hd2 hd4' hsub hv.2.2 hv.2.1)
  ·
    obtain ⟨h4, hsub⟩ := full_of_three hγ4 ha3
    have hb2 : 1 < (Finset.univ.filter fun v : Fin 4 → ZMod 2 =>
        ((c * L4.dual4 γ * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v =
            v ∧
          ((c * L4.dual4 d * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v =
            v).card := by
      by_contra h
      push Not at h
      have := Nat.mul_le_mul ha h
      omega
    obtain ⟨w, hw, hw0⟩ := Finset.exists_mem_ne hb2 0
    rw [Finset.mem_filter] at hw
    exact hw0 (eq_zero_caseA hγm h4 hd2 hd4 hsub hw.2.2 hw.2.1)

omit α in
theorem natCard_subtype (p : (Fin 4 → ZMod 2) → Prop) [DecidablePred p] :
    Nat.card {v // p v} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

omit α in
theorem le_fixV_zpowers {V : Type*} [CommGroup V] {x : MulAut V} {U : Subgroup V}
    (h : ∀ u ∈ U, x u = u) : U ≤ fixV (Subgroup.zpowers x) := by
  intro u hu a ha
  have hle : Subgroup.zpowers x ≤ MulAction.stabilizer (MulAut V) u :=
    Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact h u hu)
  have h1 := hle ha
  rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h1

theorem no_involution_of_odd
    {y : MulAut (PairMod (Fin 4) (ZMod 2))} (hy : y ∈ pairNormA7 α)
    (hodd : Odd (orderOf y)) (hy1 : y ≠ 1) {U : Subgroup (PairMod (Fin 4) (ZMod 2))}
    (hyU : ∀ u ∈ U, y u = u) (hU8 : 8 ≤ Nat.card U) {x : MulAut (PairMod (Fin 4) (ZMod 2))}
    (hx : x ∈ pairNormA7 α) (hx2 : x * x = 1) (hxU : ∀ u ∈ U, x u = u) : x = 1 := by
  obtain ⟨γ, hγ⟩ := mem_pairA7_of_odd α hy hodd
  have hγo : orderOf γ = orderOf y := by
    rw [← orderOf_injective _ (pairHom_injective α) γ, hγ]
  have hγ1 : γ ≠ 1 := fun h => hy1 (by rw [← hγ, h, map_one])
  have hθ1 : θ α γ ≠ 1 := fun h => hγ1 ((θ α).injective (by rw [h, map_one]))
  have hθo : orderOf (θ α γ) = orderOf y := by rw [MulEquiv.orderOf_eq, hγo]
  have hF1 := card_fix_natAut_le_of_odd α hγ1 (hγo ▸ hodd)
  have hF2 := card_fix_natAut_le_of_odd α hθ1 (hθo ▸ hodd)
  have hyU' : ∀ u ∈ U, natAut (Γ α) γ (u : PairMod (Fin 4) (ZMod 2)).1 = u.1 ∧
      natAut (Γ α) (θ α γ) u.2 = u.2 := by
    intro u hu
    have h := hyU u hu
    rw [← hγ, pairHom_apply, pairAut_apply] at h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  rcases map_V₁_eq_or' α hx with hV | hV
  · obtain ⟨d, rfl⟩ := mem_pairA7_of_map α hx hV
    by_contra hx1
    have hd1 : d ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have hd2 : d * d = 1 := pairHom_injective α (by rw [map_mul, hx2, map_one])
    have hθd2 : θ α d * θ α d = 1 := by rw [← map_mul, hd2, map_one]
    have hθd1 : θ α d ≠ 1 := fun h => hd1 ((θ α).injective (by rw [h, map_one]))
    have hD1 := card_fix_natAut_le α hd2 hd1
    have hD2 := card_fix_natAut_le α hθd2 hθd1
    obtain ⟨c, hc⟩ := exists_dual α
    obtain ⟨k, hk⟩ := hodd
    have hγm : (γ : GL (Fin 4) (ZMod 2)) ^ (2 * k + 1) = 1 := by
      have h := pow_orderOf_eq_one γ
      rw [hγo, hk] at h
      have h' := congrArg Subtype.val h
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h'
    have hd2' : (d : GL (Fin 4) (ZMod 2)) * d = 1 := by
      have h' := congrArg Subtype.val hd2
      rwa [Subgroup.coe_mul, Subgroup.coe_one] at h'
    have hb1 := (card_fix_mat (γ : GL (Fin 4) (ZMod 2))).symm.trans_le hF1
    have hb2 := (card_fix_mat (d : GL (Fin 4) (ZMod 2))).symm.trans_le hD1
    have hb3 := (card_fix_mat ((θ α γ : Γ α) : GL (Fin 4) (ZMod 2))).symm.trans_le hF2
    have hb4 := (card_fix_mat ((θ α d : Γ α) : GL (Fin 4) (ZMod 2))).symm.trans_le hD2
    rw [hc γ] at hb3
    rw [hc d] at hb4
    have hlt := card_mul_lt_eight hγm hd2' hb1 hb2 hb3 hb4
    have hcomp : ∀ u ∈ U,
        (((γ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
            Multiplicative.toAdd (u : PairMod (Fin 4) (ZMod 2)).1 = Multiplicative.toAdd u.1 ∧
          ((d : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
            Multiplicative.toAdd u.1 = Multiplicative.toAdd u.1) ∧
        (((c * L4.dual4 γ * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
            Multiplicative.toAdd u.2 = Multiplicative.toAdd u.2 ∧
          ((c * L4.dual4 d * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
            Multiplicative.toAdd u.2 = Multiplicative.toAdd u.2) := by
      intro u hu
      have hx' := hxU u hu
      rw [pairHom_apply, pairAut_apply] at hx'
      have e1 := congrArg Multiplicative.toAdd (hyU' u hu).1
      have e2 := congrArg Multiplicative.toAdd (hyU' u hu).2
      have e3 := congrArg (fun z : PairMod (Fin 4) (ZMod 2) => Multiplicative.toAdd z.1) hx'
      have e4 := congrArg (fun z : PairMod (Fin 4) (ZMod 2) => Multiplicative.toAdd z.2) hx'
      rw [← hc γ, ← hc d]
      exact ⟨⟨e1, e3⟩, e2, e4⟩
    have hemb : Nat.card U ≤ Nat.card ({v : Fin 4 → ZMod 2 //
          ((γ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v ∧
            ((d : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = v} ×
        {w : Fin 4 → ZMod 2 //
          ((c * L4.dual4 γ * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w =
              w ∧
            ((c * L4.dual4 d * c⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
              w = w}) :=
      Nat.card_le_card_of_injective
        (fun u => (⟨Multiplicative.toAdd (u : PairMod (Fin 4) (ZMod 2)).1, (hcomp u u.2).1⟩,
          ⟨Multiplicative.toAdd (u : PairMod (Fin 4) (ZMod 2)).2, (hcomp u u.2).2⟩)) (by
        intro u w h
        have h1 := congrArg (fun p => (p.1 : Fin 4 → ZMod 2)) h
        have h2 := congrArg (fun p => (p.2 : Fin 4 → ZMod 2)) h
        exact Subtype.ext (Prod.ext (Multiplicative.toAdd.injective h1)
          (Multiplicative.toAdd.injective h2)))
    rw [Nat.card_prod, natCard_subtype, natCard_subtype] at hemb
    exact lt_irrefl 8 (hU8.trans_lt (hemb.trans_lt hlt))
  ·
    exfalso
    have hfix := le_fixV_zpowers hxU
    have hinj : Function.Injective fun u : U =>
        (⟨(u : PairMod (Fin 4) (ZMod 2)).1, (hyU' u u.2).1⟩ :
          {v : StdMod (Fin 4) (ZMod 2) // natAut (Γ α) γ v = v}) := by
      intro u w h
      have h1 : (u : PairMod (Fin 4) (ZMod 2)).1 = (w : PairMod (Fin 4) (ZMod 2)).1 :=
        congrArg Subtype.val h
      have h2 := fst_injective_of_swap (A := Subgroup.zpowers x) (Subgroup.mem_zpowers x) hx2 hV
        (v := ⟨u, hfix u.2⟩) (w := ⟨w, hfix w.2⟩) h1
      have h3 := congrArg (fun z : ↥(fixV (Subgroup.zpowers x)) =>
        (z : PairMod (Fin 4) (ZMod 2))) h2
      exact Subtype.ext h3
    have := Nat.card_le_card_of_injective _ hinj
    omega

theorem card_le_sixteen_of_odd
    {y : MulAut (PairMod (Fin 4) (ZMod 2))} (hy : y ∈ pairNormA7 α)
    (hodd : Odd (orderOf y)) (hy1 : y ≠ 1) {U : Subgroup (PairMod (Fin 4) (ZMod 2))}
    (hyU : ∀ u ∈ U, y u = u) : Nat.card U ≤ 16 := by
  obtain ⟨γ, hγ⟩ := mem_pairA7_of_odd α hy hodd
  have hγo : orderOf γ = orderOf y := by
    rw [← orderOf_injective _ (pairHom_injective α) γ, hγ]
  have hγ1 : γ ≠ 1 := fun h => hy1 (by rw [← hγ, h, map_one])
  have hθ1 : θ α γ ≠ 1 := fun h => hγ1 ((θ α).injective (by rw [h, map_one]))
  have hθo : orderOf (θ α γ) = orderOf y := by rw [MulEquiv.orderOf_eq, hγo]
  rw [← hγ] at hyU
  calc Nat.card U ≤ Nat.card {x : PairMod (Fin 4) (ZMod 2) //
        pairAut (natAut (Γ α) γ) (natAut (Γ α) (θ α γ)) x = x} :=
        Nat.card_le_card_of_injective (fun u => ⟨u, hyU u u.2⟩)
          fun u w h => Subtype.ext (congrArg Subtype.val h :)
    _ = Nat.card {v : StdMod (Fin 4) (ZMod 2) // natAut (Γ α) γ v = v} *
        Nat.card {w : StdMod (Fin 4) (ZMod 2) // natAut (Γ α) (θ α γ) w = w} :=
        card_fix_pairAut _ _
    _ ≤ 4 * 4 := Nat.mul_le_mul (card_fix_natAut_le_of_odd α hγ1 (hγo ▸ hodd))
        (card_fix_natAut_le_of_odd α hθ1 (hθo ▸ hodd))

omit α in
theorem orderOf_ne_fifteen_perm (σ : Perm (Fin 7)) : orderOf σ ≠ 15 := by
  intro h
  have hsum := σ.sum_cycleType_le
  rw [Fintype.card_fin] at hsum
  have hmem : ∀ n ∈ σ.cycleType, n = 3 ∨ n = 5 := by
    intro n hn
    have h1 : n ∣ 15 := h ▸ σ.dvd_of_mem_cycleType hn
    have h2 : n ≤ 7 := (Multiset.le_sum_of_mem hn).trans hsum
    have h3 : 2 ≤ n := σ.two_le_of_mem_cycleType hn
    interval_cases n <;> simp_all
  have h3 : 3 ∈ σ.cycleType := by
    by_contra h3
    have h1 : σ.cycleType.lcm ∣ 5 := Multiset.lcm_dvd.mpr fun n hn => by
      rcases hmem n hn with rfl | rfl
      · exact absurd hn h3
      · exact dvd_rfl
    rw [σ.lcm_cycleType, h] at h1
    norm_num at h1
  have h5 : 5 ∈ σ.cycleType := by
    by_contra h5
    have h1 : σ.cycleType.lcm ∣ 3 := Multiset.lcm_dvd.mpr fun n hn => by
      rcases hmem n hn with rfl | rfl
      · exact dvd_rfl
      · exact absurd hn h5
    rw [σ.lcm_cycleType, h] at h1
    norm_num at h1
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem h3
  rw [ht] at h5 hsum
  have h5' : 5 ∈ t := (Multiset.mem_cons.mp h5).resolve_left (by norm_num)
  obtain ⟨t', ht'⟩ := Multiset.exists_cons_of_mem h5'
  rw [ht', Multiset.sum_cons, Multiset.sum_cons] at hsum
  omega

theorem orderOf_ne_fifteen
    {x : MulAut (PairMod (Fin 4) (ZMod 2))} (hx : x ∈ pairNormA7 α) :
    orderOf x ≠ 15 := by
  intro h15
  obtain ⟨γ, hγ⟩ := mem_pairA7_of_odd α hx (by rw [h15]; exact ⟨7, rfl⟩)
  have hγo : orderOf γ = 15 := by
    rw [← orderOf_injective _ (pairHom_injective α) γ, hγ, h15]
  obtain ⟨σ, rfl⟩ := (ψ α).surjective γ
  have hσ : orderOf σ = 15 := by rw [← MulEquiv.orderOf_eq (ψ α), hγo]
  exact orderOf_ne_fifteen_perm (σ : Perm (Fin 7)) ((Subgroup.orderOf_coe σ).trans hσ)

theorem orderOf_ne_thirty_one
    {x : MulAut (PairMod (Fin 4) (ZMod 2))} (hx : x ∈ pairNormA7 α) :
    orderOf x ≠ 31 := by
  intro h31
  obtain ⟨γ, hγ⟩ := mem_pairA7_of_odd α hx (by rw [h31]; exact ⟨15, rfl⟩)
  have hγo : orderOf γ = 31 := by
    rw [← orderOf_injective _ (pairHom_injective α) γ, hγ, h31]
  have h1 := orderOf_dvd_natCard γ
  rw [hγo, card_Γ] at h1
  exact absurd h1 (by norm_num)

theorem H8_A7Pair_cent
    {V : Type*} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    {V₁ : Subgroup V} (hreal : A7Four H V₁ ⊥) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom))
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) :
    Nat.card V = 2 ^ 8 ∧ (∀ x ∈ M, orderOf x ≠ 15 ∧ orderOf x ≠ 31) ∧
      ∀ y ∈ M, y ≠ 1 → Odd (orderOf y) → ∀ U : Subgroup V, U ≤ fixV (Subgroup.zpowers y) →
        4 ≤ rkIdx U ∧ (rkIdx U ≤ 5 → ∀ x ∈ M, x * x = 1 → U ≤ fixV (Subgroup.zpowers x) →
          x = 1) := by
  obtain ⟨α', e, h2⟩ := exists_model hreal hφ hinf hsup hniso hMN
  have hV : Nat.card V = 2 ^ 8 := (Nat.card_congr e.toEquiv).trans card_pairMod_four
  have hmem : ∀ z ∈ M, congrHom e z ∈ pairNormA7 α' := fun z hz => h2 ⟨z, hz, rfl⟩
  refine ⟨hV, fun x hx => ?_, fun y hy hy1 hodd U hU => ?_⟩
  · rw [← orderOf_injective _ (congrHom_injective e) x]
    exact ⟨orderOf_ne_fifteen α' (hmem x hx), orderOf_ne_thirty_one α' (hmem x hx)⟩
  · have hodd' : Odd (orderOf (congrHom e y)) := by
      rwa [orderOf_injective _ (congrHom_injective e) y]
    have hy1' : congrHom e y ≠ 1 := fun h =>
      hy1 (congrHom_injective e (h.trans (map_one _).symm))
    have hcardU : Nat.card ↥(U.map e.toMonoidHom) = Nat.card U :=
      Subgroup.card_map_of_injective e.injective
    have hfix : ∀ z : MulAut V, U ≤ fixV (Subgroup.zpowers z) →
        ∀ u ∈ U.map e.toMonoidHom, congrHom e z u = u := by
      rintro z hz _ ⟨u, hu, rfl⟩
      change e (z (e.symm (e u))) = e u
      rw [MulEquiv.symm_apply_apply, hz hu z (Subgroup.mem_zpowers z)]
    have h16 := card_le_sixteen_of_odd α' (hmem y hy) hodd' hy1' (hfix y hU)
    rw [hcardU] at h16
    refine ⟨SL3Pair.le_rkIdx_of_card_mul_le hV U (by
      calc Nat.card U * 2 ^ 4 ≤ 16 * 2 ^ 4 := Nat.mul_le_mul_right _ h16
        _ = 2 ^ 8 := by norm_num), fun h5 x hx hx2 hxU => ?_⟩
    have hU8 : 8 ≤ Nat.card ↥(U.map e.toMonoidHom) := by
      rw [hcardU, SL3Pair.card_eq_two_pow_sub_rkIdx hV U]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (8 - rkIdx U) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hx2' : congrHom e x * congrHom e x = 1 :=
      (map_mul (congrHom e) x x).symm.trans ((congrArg (congrHom e) hx2).trans (map_one _))
    have h1 := no_involution_of_odd α' (hmem y hy) hodd' hy1' (hfix y hU) hU8 (hmem x hx) hx2'
      (hfix x hxU)
    exact congrHom_injective e (h1.trans (map_one _).symm)

end A7

end H

end CFSG.Quasithin
