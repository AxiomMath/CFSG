module

public import CFSG.RankThree.SubgroupLists.SymplecticReducible
public import CFSG.Assembly.LowTwoRank
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.FeitThompson.OddOrderTheorem
public import Certificates.Certificate110
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate117
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank

local notation "V₄" => Fin 2 ⊕ Fin 2

section Eigenspaces

variable {K : Type} [Field K]

@[expose] noncomputable def eigSp (M : Matrix V₄ V₄ K) (μ : K) : Submodule K (V₄ → K) :=
  Module.End.eigenspace (Matrix.toLin' M) μ

theorem mem_eigSp {M : Matrix V₄ V₄ K} {μ : K} {v : V₄ → K} : v ∈ eigSp M μ ↔ M *ᵥ v = μ • v := by
  rw [eigSp, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]

theorem spForm_eq_zero_of_finrank_eq_one {U : Submodule K (V₄ → K)} (hU : Module.finrank K U = 1)
    {u v : V₄ → K} (hu : u ∈ U) (hv : v ∈ U) : spForm 2 K u v = 0 :=
  mem_orth.mp (le_orth_of_finrank_eq_one hU hv) u hu

theorem eq_zero_of_forall_spForm {v : V₄ → K} (h : ∀ x, spForm 2 K x v = 0) : v = 0 :=
  spForm_separatingLeft v fun x => spForm_isRefl _ _ (h x)

theorem false_of_line_orth {U L : Submodule K (V₄ → K)} (hUL : U ⊔ L = ⊤)
    (hL : Module.finrank K L = 1) (hLU : ∀ u ∈ U, ∀ l ∈ L, spForm 2 K u l = 0) : False := by
  have hL0 : L ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at hL
    exact zero_ne_one hL
  obtain ⟨l, hl, hl0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL0
  apply hl0
  apply eq_zero_of_forall_spForm
  intro x
  have hx : x ∈ U ⊔ L := hUL ▸ Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, LinearMap.add_apply, hLU u hu l hl, spForm_eq_zero_of_finrank_eq_one hL hw hl,
    add_zero]

variable (h2 : (2 : K) ≠ 0)
include h2

theorem spForm_eq_zero_of_eig {A : GL V₄ K} (hA : A ∈ StatedSp 2 K) {u v : V₄ → K}
    (hu : u ∈ eigSp (A : Matrix V₄ V₄ K) 1) (hv : v ∈ eigSp (A : Matrix V₄ V₄ K) (-1)) :
    spForm 2 K u v = 0 := by
  have h := spForm_mulVec hA u v
  rw [mem_eigSp.mp hu, mem_eigSp.mp hv, one_smul, neg_one_smul, map_neg] at h
  have h' : (2 : K) * spForm 2 K u v = 0 := by linear_combination -h
  exact (mul_eq_zero.mp h').resolve_left h2

theorem mem_eig_add_mem_eig {A : Matrix V₄ V₄ K} (hA : A * A = 1) (v : V₄ → K) :
    (2 : K)⁻¹ • (v + A *ᵥ v) ∈ eigSp A 1 ∧ (2 : K)⁻¹ • (v - A *ᵥ v) ∈ eigSp A (-1) ∧
      v = (2 : K)⁻¹ • (v + A *ᵥ v) + (2 : K)⁻¹ • (v - A *ᵥ v) := by
  have hAA : A *ᵥ (A *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_eigSp, Matrix.mulVec_smul, Matrix.mulVec_add, hAA, one_smul, add_comm]
  · rw [mem_eigSp, Matrix.mulVec_smul, Matrix.mulVec_sub, hAA, neg_smul, one_smul, ← smul_neg,
      neg_sub]
  · rw [← smul_add, show v + A *ᵥ v + (v - A *ᵥ v) = (2 : K) • v by rw [two_smul]; abel,
      smul_smul, inv_mul_cancel₀ h2, one_smul]

theorem eig_sup_eig {A : Matrix V₄ V₄ K} (hA : A * A = 1) : eigSp A 1 ⊔ eigSp A (-1) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨h1, h2', hv⟩ := mem_eig_add_mem_eig h2 hA v
  rw [hv]
  exact Submodule.add_mem_sup h1 h2'

theorem eig_inf_eig (A : Matrix V₄ V₄ K) : eigSp A 1 ⊓ eigSp A (-1) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨h1, h2'⟩ := Submodule.mem_inf.mp hv
  rw [mem_eigSp] at h1 h2'
  rw [h1, one_smul] at h2'
  have : (2 : K) • v = 0 := by rw [two_smul]; nth_rw 2 [h2']; rw [neg_one_smul, add_neg_cancel]
  rw [Submodule.mem_bot]
  exact (smul_eq_zero.mp this).resolve_left h2

theorem finrank_eig_add_finrank_eig {A : Matrix V₄ V₄ K} (hA : A * A = 1) :
    Module.finrank K (eigSp A 1) + Module.finrank K (eigSp A (-1)) = 4 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (eigSp A 1) (eigSp A (-1))
  rw [eig_sup_eig h2 hA, eig_inf_eig h2, finrank_top, finrank_bot, add_zero] at h
  rw [← h]
  simp

theorem finrank_eig_neg_one_eq_two {A : GL V₄ K} (hA : A ∈ StatedSp 2 K) (hA2 : A * A = 1)
    (hA1 : A ≠ 1) (hAm : A ≠ -1) : Module.finrank K (eigSp (A : Matrix V₄ V₄ K) (-1)) = 2 := by
  have hAA : (A : Matrix V₄ V₄ K) * A = 1 := by rw [← Units.val_mul, hA2, Units.val_one]
  have hsum := finrank_eig_add_finrank_eig h2 hAA
  have hposm : Module.finrank K (eigSp (A : Matrix V₄ V₄ K) (-1)) ≠ 0 := by
    intro h0
    apply hA1
    have htop : eigSp (A : Matrix V₄ V₄ K) 1 = ⊤ := by
      have := eig_sup_eig h2 hAA
      rwa [Submodule.finrank_eq_zero.mp h0, sup_bot_eq] at this
    apply Units.ext
    rw [Units.val_one]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have hv := mem_eigSp.mp (htop ▸ Submodule.mem_top : v ∈ eigSp (A : Matrix V₄ V₄ K) 1)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hv, one_smul, Matrix.one_mulVec]
  have hposp : Module.finrank K (eigSp (A : Matrix V₄ V₄ K) 1) ≠ 0 := by
    intro h0
    apply hAm
    have htop : eigSp (A : Matrix V₄ V₄ K) (-1) = ⊤ := by
      have := eig_sup_eig h2 hAA
      rwa [Submodule.finrank_eq_zero.mp h0, bot_sup_eq] at this
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have hv := mem_eigSp.mp (htop ▸ Submodule.mem_top : v ∈ eigSp (A : Matrix V₄ V₄ K) (-1))
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hv, Units.val_neg, Units.val_one,
      Matrix.neg_mulVec, Matrix.one_mulVec, neg_one_smul]
  have horth : ∀ u ∈ eigSp (A : Matrix V₄ V₄ K) 1, ∀ v ∈ eigSp (A : Matrix V₄ V₄ K) (-1),
      spForm 2 K u v = 0 := fun u hu v hv => spForm_eq_zero_of_eig h2 hA hu hv
  have horth' : ∀ v ∈ eigSp (A : Matrix V₄ V₄ K) (-1), ∀ u ∈ eigSp (A : Matrix V₄ V₄ K) 1,
      spForm 2 K v u = 0 := fun v hv u hu => spForm_isRefl _ _ (horth u hu v hv)
  rcases (by omega : Module.finrank K (eigSp (A : Matrix V₄ V₄ K) (-1)) = 1 ∨
      Module.finrank K (eigSp (A : Matrix V₄ V₄ K) (-1)) = 2 ∨
      Module.finrank K (eigSp (A : Matrix V₄ V₄ K) 1) = 1) with h1 | h2' | h3
  · exact (false_of_line_orth (eig_sup_eig h2 hAA) h1 horth).elim
  · exact h2'
  · exact (false_of_line_orth (by rw [sup_comm]; exact eig_sup_eig h2 hAA) h3 horth').elim

theorem eq_smul_on_plane {B : GL V₄ K} (hB : B ∈ StatedSp 2 K) (hB2 : B * B = 1)
    {E F : Submodule K (V₄ → K)} (hEF : E ⊔ F = ⊤) (hE2 : Module.finrank K E = 2)
    (horth : ∀ f ∈ F, ∀ e ∈ E, spForm 2 K f e = 0)
    (hBE : ∀ e ∈ E, (B : Matrix V₄ V₄ K) *ᵥ e ∈ E) :
    (∀ e ∈ E, (B : Matrix V₄ V₄ K) *ᵥ e = e) ∨ (∀ e ∈ E, (B : Matrix V₄ V₄ K) *ᵥ e = -e) := by
  have hBB : (B : Matrix V₄ V₄ K) * B = 1 := by rw [← Units.val_mul, hB2, Units.val_one]
  set X := E ⊓ eigSp (B : Matrix V₄ V₄ K) 1 with hX
  set Y := E ⊓ eigSp (B : Matrix V₄ V₄ K) (-1) with hY
  have hXY : X ⊔ Y = E := by
    apply le_antisymm (sup_le inf_le_left inf_le_left)
    intro e he
    obtain ⟨h1, h2', hv⟩ := mem_eig_add_mem_eig h2 hBB e
    rw [hv]
    refine Submodule.add_mem_sup ⟨E.smul_mem _ (E.add_mem he (hBE e he)), h1⟩
      ⟨E.smul_mem _ (E.sub_mem he (hBE e he)), h2'⟩
  have hXY0 : X ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have := eig_inf_eig h2 (B : Matrix V₄ V₄ K)
    rw [← this]
    exact ⟨hv.1.2, hv.2.2⟩
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq X Y
  rw [hXY, hXY0, finrank_bot, add_zero, hE2] at hdim
  by_cases hY0 : Y = ⊥
  · left
    intro e he
    have he' : e ∈ X := by
      rw [← hXY, hY0, sup_bot_eq] at he
      exact he
    rw [mem_eigSp.mp he'.2, one_smul]
  by_cases hX0 : X = ⊥
  · right
    intro e he
    have he' : e ∈ Y := by
      rw [← hXY, hX0, bot_sup_eq] at he
      exact he
    rw [mem_eigSp.mp he'.2, neg_one_smul]
  exfalso
  have hYpos : Module.finrank K Y ≠ 0 := fun h => hY0 (Submodule.finrank_eq_zero.mp h)
  have hXpos : Module.finrank K X ≠ 0 := fun h => hX0 (Submodule.finrank_eq_zero.mp h)
  have hX1 : Module.finrank K X = 1 := by omega
  apply false_of_line_orth (U := Y ⊔ F) (L := X)
  · rw [sup_comm Y F, sup_assoc, sup_comm Y X, hXY, sup_comm]
    exact hEF
  · exact hX1
  · intro u hu x hx
    obtain ⟨y, hy, f, hf, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add, LinearMap.add_apply, horth f hf x hx.1, add_zero]
    exact spForm_isRefl _ _ (spForm_eq_zero_of_eig h2 hB hx.2 hy.2)

theorem eq_of_commute_involution {A B : GL V₄ K} (hA : A ∈ StatedSp 2 K) (hB : B ∈ StatedSp 2 K)
    (hA2 : A * A = 1) (hB2 : B * B = 1) (hAB : A * B = B * A) (hA1 : A ≠ 1) (hAm : A ≠ -1) :
    B = 1 ∨ B = -1 ∨ B = A ∨ B = -A := by
  have hAA : (A : Matrix V₄ V₄ K) * A = 1 := by rw [← Units.val_mul, hA2, Units.val_one]
  have hABm : (A : Matrix V₄ V₄ K) * B = B * A := by rw [← Units.val_mul, hAB, Units.val_mul]
  have hsum := finrank_eig_add_finrank_eig h2 hAA
  have hm2 := finrank_eig_neg_one_eq_two h2 hA hA2 hA1 hAm
  have hp2 : Module.finrank K (eigSp (A : Matrix V₄ V₄ K) 1) = 2 := by omega
  set Ep := eigSp (A : Matrix V₄ V₄ K) 1 with hEp
  set Em := eigSp (A : Matrix V₄ V₄ K) (-1) with hEm
  have hBpres : ∀ μ : K, ∀ v ∈ eigSp (A : Matrix V₄ V₄ K) μ,
      (B : Matrix V₄ V₄ K) *ᵥ v ∈ eigSp (A : Matrix V₄ V₄ K) μ := by
    intro μ v hv
    rw [mem_eigSp] at hv ⊢
    rw [Matrix.mulVec_mulVec, hABm, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have horth : ∀ u ∈ Ep, ∀ v ∈ Em, spForm 2 K u v = 0 := fun u hu v hv =>
    spForm_eq_zero_of_eig h2 hA hu hv
  have hsup := eig_sup_eig h2 hAA
  have hEmB := eq_smul_on_plane h2 hB hB2 (E := Em) (F := Ep) (by rw [sup_comm]; exact hsup) hm2
    horth (hBpres (-1))
  have hEpB := eq_smul_on_plane h2 hB hB2 (E := Ep) (F := Em) hsup hp2
    (fun v hv u hu => spForm_isRefl _ _ (horth u hu v hv)) (hBpres 1)
  have hdet : ∀ C : GL V₄ K, (∀ v ∈ Ep, (C : Matrix V₄ V₄ K) *ᵥ v = (B : Matrix V₄ V₄ K) *ᵥ v) →
      (∀ v ∈ Em, (C : Matrix V₄ V₄ K) *ᵥ v = (B : Matrix V₄ V₄ K) *ᵥ v) → B = C := by
    intro C hCp hCm
    apply Units.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    obtain ⟨h1, h2', hv⟩ := mem_eig_add_mem_eig h2 hAA v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hv, Matrix.mulVec_add, Matrix.mulVec_add,
      hCp _ h1, hCm _ h2']
  have hAon : ∀ μ : K, ∀ v ∈ eigSp (A : Matrix V₄ V₄ K) μ, (A : Matrix V₄ V₄ K) *ᵥ v = μ • v :=
    fun μ v hv => mem_eigSp.mp hv
  rcases hEpB with hpB | hpB <;> rcases hEmB with hmB | hmB
  · left
    refine hdet 1 (fun v hv => ?_) (fun v hv => ?_)
    · rw [Units.val_one, Matrix.one_mulVec, hpB v hv]
    · rw [Units.val_one, Matrix.one_mulVec, hmB v hv]
  · right; right; left
    refine hdet A (fun v hv => ?_) (fun v hv => ?_)
    · rw [hAon 1 v hv, one_smul, hpB v hv]
    · rw [hAon (-1) v hv, neg_one_smul, hmB v hv]
  · right; right; right
    refine hdet (-A) (fun v hv => ?_) (fun v hv => ?_)
    · rw [Units.val_neg, Matrix.neg_mulVec, hAon 1 v hv, one_smul, hpB v hv]
    · rw [Units.val_neg, Matrix.neg_mulVec, hAon (-1) v hv, neg_one_smul, neg_neg, hmB v hv]
  · right; left
    refine hdet (-1) (fun v hv => ?_) (fun v hv => ?_)
    · rw [Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec, hpB v hv]
    · rw [Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec, hmB v hv]

theorem neg_one_mem_of_commute_involutions {A B : GL V₄ K} (hA : A ∈ StatedSp 2 K)
    (hB : B ∈ StatedSp 2 K) (hA2 : A * A = 1) (hB2 : B * B = 1) (hAB : A * B = B * A)
    (hA1 : A ≠ 1) (hB1 : B ≠ 1) (hAB1 : A ≠ B) : A = -1 ∨ B = -1 ∨ A * B = -1 := by
  by_cases hAm : A = -1
  · exact Or.inl hAm
  rcases eq_of_commute_involution h2 hA hB hA2 hB2 hAB hA1 hAm with h | h | h | h
  · exact absurd h hB1
  · exact Or.inr (Or.inl h)
  · exact absurd h.symm hAB1
  · right; right
    rw [h, mul_neg, hA2]

end Eigenspaces

variable {p : ℕ} [Fact p.Prime]

theorem twoRank_le_one_of_neg_one_not_mem (hp2 : p ≠ 2) {G : Subgroup (GL V₄ (ZMod p))}
    (hGS : G ≤ StatedSp 2 (ZMod p)) (hneg : (-1 : GL V₄ (ZMod p)) ∉ G) :
    CFSG.Assembly.twoRank G ≤ 1 := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)
  unfold CFSG.Assembly.twoRank CFSG.Assembly.pRank
  refine csSup_le ⟨0, ⊥, bot_le, ?_, by simp⟩ ?_
  · refine ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => ?_⟩
    rw [Subgroup.mem_bot] at hx
    rw [hx, one_pow]
  rintro k ⟨E, -, ⟨hEc, hE2⟩, hcard⟩
  by_contra hk
  push Not at hk
  have hcard4 : 4 ≤ Nat.card E := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have : Finite E := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨a, ha⟩ : ∃ a : E, a ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Subsingleton E := ⟨fun x y => (hall x).trans (hall y).symm⟩
    rw [Nat.card_unique] at hcard4
    omega
  obtain ⟨b, hb1, hba⟩ : ∃ b : E, b ≠ 1 ∧ b ≠ a := by
    by_contra hall
    push Not at hall
    have hsub : (Set.univ : Set E) ⊆ {1, a} := fun x _ => by
      by_cases hx : x = 1
      · exact Or.inl hx
      · exact Or.inr (hall x hx)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ, Set.ncard_pair ha.symm] at this
    omega
  set A : GL V₄ (ZMod p) := ((a : G) : GL V₄ (ZMod p)) with hAdef
  set B : GL V₄ (ZMod p) := ((b : G) : GL V₄ (ZMod p)) with hBdef
  have hsq : ∀ x : E, ((x : G) : GL V₄ (ZMod p)) * ((x : G) : GL V₄ (ZMod p)) = 1 := by
    intro x
    have := hE2 x x.2
    rw [← sq, ← Subgroup.coe_pow, this, Subgroup.coe_one]
  have hcomm : A * B = B * A := by
    have h := hEc.is_comm.comm a b
    have := congrArg (fun x : E => ((x : G) : GL V₄ (ZMod p))) h
    simpa using this
  have hne : ∀ x y : E, x ≠ y → ((x : G) : GL V₄ (ZMod p)) ≠ ((y : G) : GL V₄ (ZMod p)) :=
    fun x y hxy h => hxy (Subtype.ext (Subtype.ext h))
  have hne1 : ∀ x : E, x ≠ 1 → ((x : G) : GL V₄ (ZMod p)) ≠ 1 := fun x hx h =>
    hx (Subtype.ext (Subtype.ext h))
  rcases neg_one_mem_of_commute_involutions h2 (hGS (a : G).2) (hGS (b : G).2) (hsq a) (hsq b)
      hcomm (hne1 a ha) (hne1 b hb1) (hne a b hba.symm) with h | h | h
  · exact hneg (h ▸ (a : G).2)
  · exact hneg (h ▸ (b : G).2)
  · exact hneg (h ▸ G.mul_mem (a : G).2 (b : G).2)

theorem two_dvd_card_center_of_neg_one_not_mem (hp2 : p ≠ 2) {G : Subgroup (GL V₄ (ZMod p))}
    (hGS : G ≤ StatedSp 2 (ZMod p)) (hq : CFSG.IsQuasisimple G)
    (hneg : (-1 : GL V₄ (ZMod p)) ∉ G) : 2 ∣ Nat.card (Subgroup.center G) := by
  by_contra h2Z
  obtain ⟨hperf, hsimple, hnonab⟩ := hq
  have heq := CFSG.GroupTheory.PRankCoprimeQuotient.assembly_pRank_quotient_eq_of_not_dvd
    Nat.prime_two (Subgroup.center G) h2Z
  have hle : CFSG.Assembly.twoRank (G ⧸ Subgroup.center G) ≤ 1 := by
    unfold CFSG.Assembly.twoRank
    rw [heq]
    exact twoRank_le_one_of_neg_one_not_mem hp2 hGS hneg
  have hge : 2 ≤ CFSG.Assembly.twoRank (G ⧸ Subgroup.center G) := by
    apply two_le_twoRank _ hnonab
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have : Nontrivial (G ⧸ Subgroup.center G) := hsimple.toNontrivial
    exact Group.IsPerfect.not_isSolvable (G ⧸ Subgroup.center G) hsolv
  omega

end CFSG.RankThree.SubgroupLists
