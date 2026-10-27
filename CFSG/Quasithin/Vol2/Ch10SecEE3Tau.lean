module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Q

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique Equiv

@[expose] def pr (b₀ b₁ : Bool) : Perm (Fin 5) := (if b₀ then sA else 1) * (if b₁ then sB else 1)

theorem pr_mul : ∀ a b c d : Bool, pr a b * pr c d = pr (Bool.xor a c) (Bool.xor b d) := by
  decide

theorem pr_inj : ∀ a b c d : Bool, pr a b = pr c d → a = c ∧ b = d := by decide

theorem pr_mem_eFour : ∀ a b : Bool, pr a b ∈ eFour := by decide

theorem exists_pr (σ : Perm (Fin 5)) (hσ : σ ∈ eFour) : ∃ a b : Bool, pr a b = σ := by
  rcases (eFour_mem_iff σ).mp hσ with rfl | rfl | rfl | rfl
  exacts [⟨false, false, by decide⟩, ⟨true, false, by decide⟩, ⟨false, true, by decide⟩,
    ⟨true, true, by decide⟩]

theorem mul_mul_comm_mid {M : Type*} [Monoid M] {x y z w : M} (h : z * y = y * z) :
    x * y * (z * w) = x * z * (y * w) := by
  rw [← mul_assoc, mul_assoc x y z, ← h, ← mul_assoc, mul_assoc]

theorem decide_mem_symmDiff (i : Fin 4) (S S' : Finset (Fin 4)) :
    decide (i ∈ symmDiff S S') = Bool.xor (decide (i ∈ S)) (decide (i ∈ S')) := by
  by_cases h : i ∈ S <;> by_cases h' : i ∈ S' <;> simp [Finset.mem_symmDiff, h, h']

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

namespace Case2Data

variable {hyp : Hyp10 G T L I} {t : G} (D : Case2Data hyp t)

@[expose] noncomputable def tauS (S : Finset (Fin 4)) :
    MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)) :=
  ((D.θ₁.symm (pr (decide (0 ∈ S)) (decide (1 ∈ S))) : ↥D.K₁) : MulAut _) *
    ((D.θ₂.symm (pr (decide (2 ∈ S)) (decide (3 ∈ S))) : ↥D.K₂) : MulAut _)

theorem tauS_mul (S S' : Finset (Fin 4)) : D.tauS S * D.tauS S' = D.tauS (symmDiff S S') := by
  unfold tauS
  rw [decide_mem_symmDiff, decide_mem_symmDiff, decide_mem_symmDiff, decide_mem_symmDiff,
    ← pr_mul, ← pr_mul, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
  have hc := D.comm _ (D.θ₁.symm (pr (decide (0 ∈ S')) (decide (1 ∈ S')))).2 _
    (D.θ₂.symm (pr (decide (2 ∈ S)) (decide (3 ∈ S)))).2
  exact mul_mul_comm_mid hc

theorem tauS_empty : D.tauS ∅ = 1 := by
  simp [tauS, pr]

theorem tauS_singleton (i : Fin 4) : D.tauS {i} = D.tau i := by
  fin_cases i <;> simp [tauS, tau, pr]

theorem tauS_mul_self (S : Finset (Fin 4)) : D.tauS S * D.tauS S = 1 := by
  rw [tauS_mul, symmDiff_self, Finset.bot_eq_empty, tauS_empty]

theorem tauS_injective {S S' : Finset (Fin 4)} (h : D.tauS S = D.tauS S') : S = S' := by
  obtain ⟨h1, h2⟩ := eq_of_mul_eq_mul D.inf (D.θ₁.symm _).2 (D.θ₁.symm _).2 (D.θ₂.symm _).2
    (D.θ₂.symm _).2 h
  obtain ⟨a0, a1⟩ := pr_inj _ _ _ _ (D.θ₁.symm.injective (Subtype.ext h1))
  obtain ⟨a2, a3⟩ := pr_inj _ _ _ _ (D.θ₂.symm.injective (Subtype.ext h2))
  ext i
  fin_cases i
  · exact decide_eq_decide.mp a0
  · exact decide_eq_decide.mp a1
  · exact decide_eq_decide.mp a2
  · exact decide_eq_decide.mp a3

theorem tauS_mem (S : Finset (Fin 4)) : D.tauS S ∈ D.P₁ ⊔ D.P₂ := by
  refine Subgroup.mul_mem_sup ((D.memP₁ _ (D.θ₁.symm _).2).mpr ?_)
    ((D.memP₂ _ (D.θ₂.symm _).2).mpr ?_)
  · simpa using pr_mem_eFour _ _
  · simpa using pr_mem_eFour _ _

theorem exists_tauS {p : MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))}
    (hp : p ∈ D.P₁ ⊔ D.P₂) : ∃ S, D.tauS S = p := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup (A := D.P₁) (B := D.P₂)
    (fun a ha b hb => D.comm a ha.1 b hb.1) hp
  obtain ⟨x, y, hxy⟩ := exists_pr _ ((D.memP₁ a ha.1).mp ha)
  obtain ⟨z, w, hzw⟩ := exists_pr _ ((D.memP₂ b hb.1).mp hb)
  refine ⟨Finset.univ.filter fun i => ![x, y, z, w] i = true, ?_⟩
  have h0 : decide ((0 : Fin 4) ∈ Finset.univ.filter fun i => ![x, y, z, w] i = true) = x := by
    simp
  have h1 : decide ((1 : Fin 4) ∈ Finset.univ.filter fun i => ![x, y, z, w] i = true) = y := by
    simp
  have h2 : decide ((2 : Fin 4) ∈ Finset.univ.filter fun i => ![x, y, z, w] i = true) = z := by
    simp
  have h3 : decide ((3 : Fin 4) ∈ Finset.univ.filter fun i => ![x, y, z, w] i = true) = w := by
    simp
  rw [tauS, h0, h1, h2, h3, hxy, hzw]
  simp

@[expose] noncomputable def Yg (γ : Finset (Fin 4)) :
    Subgroup (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))) where
  carrier := {p | ∃ S ⊆ γ, D.tauS S = p}
  mul_mem' := by
    rintro _ _ ⟨S, hS, rfl⟩ ⟨S', hS', rfl⟩
    exact ⟨symmDiff S S', symmDiff_le_sup.trans (sup_le hS hS'), (D.tauS_mul S S').symm⟩
  one_mem' := ⟨∅, Finset.empty_subset _, D.tauS_empty⟩
  inv_mem' := by
    rintro _ ⟨S, hS, rfl⟩
    exact ⟨S, hS, (inv_eq_of_mul_eq_one_right (D.tauS_mul_self S)).symm⟩

theorem mem_Yg {γ : Finset (Fin 4)} {p : MulAut (IntMod (fsuVM T L I)
      (SecA.isElemAbelian_fsuVM hyp))} : p ∈ D.Yg γ ↔ ∃ S ⊆ γ, D.tauS S = p :=
  Iff.rfl

theorem tauS_mem_Yg_iff {γ S : Finset (Fin 4)} : D.tauS S ∈ D.Yg γ ↔ S ⊆ γ := by
  refine ⟨fun ⟨S', hS', e⟩ => D.tauS_injective e ▸ hS', fun h => ⟨S, h, rfl⟩⟩

theorem tau_mem_Yg_iff {γ : Finset (Fin 4)} {i : Fin 4} : D.tau i ∈ D.Yg γ ↔ i ∈ γ := by
  rw [← D.tauS_singleton, tauS_mem_Yg_iff, Finset.singleton_subset_iff]

theorem Yg_mono {ε δ : Finset (Fin 4)} (h : ε ⊆ δ) : D.Yg ε ≤ D.Yg δ := by
  rintro _ ⟨S, hS, rfl⟩
  exact ⟨S, hS.trans h, rfl⟩

theorem Yg_inf (ε δ : Finset (Fin 4)) : D.Yg ε ⊓ D.Yg δ = D.Yg (ε ∩ δ) := by
  refine le_antisymm ?_ (le_inf (D.Yg_mono Finset.inter_subset_left)
    (D.Yg_mono Finset.inter_subset_right))
  rintro _ ⟨⟨S, hS, rfl⟩, h2⟩
  exact ⟨S, Finset.subset_inter hS (D.tauS_mem_Yg_iff.mp h2), rfl⟩

theorem Yg_le_P (γ : Finset (Fin 4)) : D.Yg γ ≤ D.P₁ ⊔ D.P₂ := by
  rintro _ ⟨S, -, rfl⟩
  exact D.tauS_mem S

theorem Yg_le_of {γ : Finset (Fin 4)} {Y : Subgroup (MulAut (IntMod (fsuVM T L I)
      (SecA.isElemAbelian_fsuVM hyp)))} (h : ∀ i ∈ γ, D.tau i ∈ Y) : D.Yg γ ≤ Y := by
  classical
  rintro _ ⟨S, hS, rfl⟩
  induction S using Finset.induction_on with
  | empty => rw [tauS_empty]; exact Y.one_mem
  | insert i S hi ih =>
    have e : (insert i S : Finset (Fin 4)) = symmDiff {i} S := by
      ext j
      by_cases hj : j = i
      · subst hj; simp [Finset.mem_symmDiff, hi]
      · simp [Finset.mem_symmDiff, hj]
    rw [e, ← D.tauS_mul, D.tauS_singleton]
    exact Y.mul_mem (h i (hS (Finset.mem_insert_self i S)))
      (ih ((Finset.subset_insert i S).trans hS))

theorem Yg_sup (ε δ : Finset (Fin 4)) : D.Yg ε ⊔ D.Yg δ = D.Yg (ε ∪ δ) := by
  refine le_antisymm (sup_le (D.Yg_mono Finset.subset_union_left)
    (D.Yg_mono Finset.subset_union_right)) (D.Yg_le_of fun i hi => ?_)
  rcases Finset.mem_union.mp hi with h | h
  · exact Subgroup.mem_sup_left (D.tau_mem_Yg_iff.mpr h)
  · exact Subgroup.mem_sup_right (D.tau_mem_Yg_iff.mpr h)

theorem card_Yg (γ : Finset (Fin 4)) : Nat.card ↥(D.Yg γ) = 2 ^ γ.card := by
  classical
  have e : (D.Yg γ : Set (MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)))) =
      ↑(γ.powerset.image D.tauS) := by
    ext p
    simp only [SetLike.mem_coe, mem_Yg, Finset.coe_image, Finset.coe_powerset, Set.mem_image,
      Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
  rw [← SetLike.coe_sort_coe, e, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Finset.card_image_of_injective _ fun _ _ h => D.tauS_injective h, Finset.card_powerset]

end Case2Data

end CFSG.Quasithin.Vol2.Ch10.SecE
