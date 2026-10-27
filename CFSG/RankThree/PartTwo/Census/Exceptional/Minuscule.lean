module

public import CFSG.LieType.Steinberg.Minuscule.ChevExtras
public import CFSG.LieType.Steinberg.Adjoint.Brackets
public import CFSG.LieType.Chevalley.RootCommutatorReduction
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.CentralCover.SteinbergBNSL2Elements

public section

namespace CFSG.RankThree.PartTwo.Census.Exceptional

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.RankThree.CentralCover
open scoped MatrixGroups commutatorElement

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type*) [Field k]

theorem exists_weyl_transport {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ (j : Fin τ.rank) (N : hV.minGroup k) (σ σ' : k), IsSign σ ∧ IsSign σ' ∧ ∀ c : k,
      N * hV.xm k (Pi.single j 1) c * N⁻¹ = hV.xm k γ (σ * c) ∧
      N * hV.xm k (-Pi.single j 1) c * N⁻¹ = hV.xm k (-γ) (σ' * c) := by
  induction hγ with
  | basis j => exact ⟨j, 1, 1, 1, isSign_one, isSign_one, fun c => by simp⟩
  | @reflect i v hv ih =>
    obtain ⟨j, N, σ, σ', hσ, hσ', h⟩ := ih
    obtain ⟨σ₁, hσ₁, h₁⟩ := hV.nm_conj_xm k hv i
    obtain ⟨σ₂, hσ₂, h₂⟩ := hV.nm_conj_xm k (CFSG.LieType.Chevalley.IsRoot.neg hv) i
    refine ⟨j, hV.nm k i * N, σ₁ * σ, σ₂ * σ', hσ₁.mul hσ, hσ₂.mul hσ', fun c => ⟨?_, ?_⟩⟩
    · calc hV.nm k i * N * hV.xm k (Pi.single j 1) c * (hV.nm k i * N)⁻¹
          = hV.nm k i * (N * hV.xm k (Pi.single j 1) c * N⁻¹) * (hV.nm k i)⁻¹ := by group
        _ = hV.xm k (reflect τ i v) (σ₁ * σ * c) := by rw [(h c).1, h₁, mul_assoc]
    · calc hV.nm k i * N * hV.xm k (-Pi.single j 1) c * (hV.nm k i * N)⁻¹
          = hV.nm k i * (N * hV.xm k (-Pi.single j 1) c * N⁻¹) * (hV.nm k i)⁻¹ := by group
        _ = hV.xm k (-reflect τ i v) (σ₂ * σ' * c) := by
          rw [(h c).2, h₂, mul_assoc, CFSG.LieType.Steinberg.Adjoint.reflect_neg]

@[expose] noncomputable def simpleSL2 (i : Fin τ.rank) : SL(2, k) →* hV.minGroup k :=
  (hV.slHom k i).codRestrict _ (hV.slHom_mem k i)

theorem endo_simpleSL2 (i : Fin τ.rank) (A : SL(2, k)) :
    hV.endo k (simpleSL2 hV k i A) = hV.blockOp k i A := rfl

theorem simpleSL2_injective (i : Fin τ.rank) : Function.Injective (simpleSL2 hV k i) :=
  fun _ _ h => Subtype.ext (hV.blockOp_injective k i (congrArg (hV.endo k) h))

theorem simpleSL2_upper (i : Fin τ.rank) (c : k) :
    simpleSL2 hV k i (sl2Upper c) = hV.xm k (Pi.single i 1) c :=
  hV.endo_injective k (by rw [endo_simpleSL2, hV.endo_xm, coe_sl2Upper, hV.blockOp_upper])

theorem simpleSL2_diag (i : Fin τ.rank) (t : kˣ) :
    simpleSL2 hV k i (sl2Diag t) = hV.hm k i t :=
  hV.endo_injective k (by rw [endo_simpleSL2, hV.endo_hm, coe_sl2Diag, hV.blockOp_diag])

theorem simpleSL2_mem (i : Fin τ.rank) (A : SL(2, k)) :
    simpleSL2 hV k i A ∈ hV.rootGroup k (Pi.single i 1) ⊔ hV.rootGroup k (-Pi.single i 1) := by
  have hX : ∀ c : k, hV.xm k (Pi.single i 1) c ∈
      hV.rootGroup k (Pi.single i 1) ⊔ hV.rootGroup k (-Pi.single i 1) := fun c =>
    Subgroup.mem_sup_left (hV.xm_mem_rootGroup k _ _)
  have hH : ∀ t : kˣ, hV.hm k i t ∈
      hV.rootGroup k (Pi.single i 1) ⊔ hV.rootGroup k (-Pi.single i 1) := fun t =>
    hV.torus_le_rankOne k i (hV.hm_mem_torus k i t)
  have hN : hV.nm k i ∈ hV.rootGroup k (Pi.single i 1) ⊔ hV.rootGroup k (-Pi.single i 1) :=
    hV.nm_mem_rankOne k i
  by_cases h0 : (A : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
  · obtain ⟨t, c, hc⟩ := MinData.Valid.sl_eq_of_lower_eq_zero k A h0
    have e : simpleSL2 hV k i A = hV.hm k i t * hV.xm k (Pi.single i 1) c := by
      refine hV.endo_injective k ?_
      rw [endo_simpleSL2, hc, hV.blockOp_mul, hV.blockOp_diag, hV.blockOp_upper, hV.endo_mul,
        hV.endo_hm, hV.endo_xm]
    rw [e]
    exact mul_mem (hH t) (hX c)
  · obtain ⟨u, t, v, hc⟩ := MinData.Valid.sl_eq_of_lower_ne_zero k A h0
    have e : simpleSL2 hV k i A = hV.xm k (Pi.single i 1) u * hV.nm k i * hV.hm k i t *
        hV.xm k (Pi.single i 1) v := by
      refine hV.endo_injective k ?_
      rw [endo_simpleSL2, hc, hV.blockOp_mul, hV.blockOp_mul, hV.blockOp_mul, hV.blockOp_diag,
        hV.blockOp_upper, hV.blockOp_upper, hV.blockOp_weyl, hV.endo_mul, hV.endo_mul,
        hV.endo_mul, hV.endo_xm, hV.endo_nm, hV.endo_hm, hV.endo_xm]
    rw [e]
    exact mul_mem (mul_mem (mul_mem (hX u) hN) (hH t)) (hX v)

theorem map_conj_rootGroup_le {δ ε : Fin τ.rank → ℤ} {N : hV.minGroup k} {σ : k}
    (h : ∀ c : k, N * hV.xm k δ c * N⁻¹ = hV.xm k ε (σ * c)) :
    (hV.rootGroup k δ).map (MulAut.conj N).toMonoidHom ≤ hV.rootGroup k ε := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hg
  change N * hV.xm k δ c * N⁻¹ ∈ _
  rw [h c]
  exact hV.xm_mem_rootGroup k _ _

theorem exists_rootSL2 {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ ρ : SL(2, k) →* hV.minGroup k, Function.Injective ρ ∧
      (∀ A, ρ A ∈ hV.rootGroup k γ ⊔ hV.rootGroup k (-γ)) ∧
      ∃ (j : Fin τ.rank) (N : hV.minGroup k), ρ (sl2Diag (-1)) = N * hV.hm k j (-1) * N⁻¹ := by
  obtain ⟨j, N, σ, σ', -, -, h⟩ := exists_weyl_transport hV k hγ
  refine ⟨(MulAut.conj N).toMonoidHom.comp (simpleSL2 hV k j),
    (MulAut.conj N).injective.comp (simpleSL2_injective hV k j), fun A => ?_,
    j, N, by rw [MonoidHom.comp_apply, simpleSL2_diag]; rfl⟩
  have hle : (hV.rootGroup k (Pi.single j 1) ⊔ hV.rootGroup k (-Pi.single j 1)).map
      (MulAut.conj N).toMonoidHom ≤ hV.rootGroup k γ ⊔ hV.rootGroup k (-γ) := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (map_conj_rootGroup_le hV k fun c => (h c).1)
      (map_conj_rootGroup_le hV k fun c => (h c).2)
  exact hle ⟨_, simpleSL2_mem hV k j A, rfl⟩

theorem commute_xm {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (hne : β + γ ≠ 0) (hnr : ¬ IsRoot τ (β + γ)) (c d : k) :
    hV.xm k β c * hV.xm k γ d = hV.xm k γ d * hV.xm k β c := by
  have h := (hV.commutator_xm k hβ hγ hne).2 hnr c d
  rw [commutatorElement_def] at h
  calc hV.xm k β c * hV.xm k γ d
      = (hV.xm k β c * hV.xm k γ d * (hV.xm k β c)⁻¹ * (hV.xm k γ d)⁻¹) *
          (hV.xm k γ d * hV.xm k β c) := by group
    _ = hV.xm k γ d * hV.xm k β c := by rw [h, one_mul]

theorem rootGroup_le_centralizer {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (hne : β + γ ≠ 0) (hnr : ¬ IsRoot τ (β + γ)) :
    hV.rootGroup k β ≤ Subgroup.centralizer (hV.rootGroup k γ : Set (hV.minGroup k)) := by
  intro x hx
  obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨d, rfl⟩ := (hV.mem_rootGroup k).1 hy
  exact (commute_xm hV k hβ hγ hne hnr c d).symm

theorem rootGroup_le_centralizer_rankOne {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hγ : IsRoot τ γ) (h1 : β + γ ≠ 0) (h2 : β - γ ≠ 0) (h3 : ¬ IsRoot τ (β + γ))
    (h4 : ¬ IsRoot τ (β - γ)) :
    hV.rootGroup k β ≤
      Subgroup.centralizer ((hV.rootGroup k γ ⊔ hV.rootGroup k (-γ) : Subgroup _) :
        Set (hV.minGroup k)) := by
  rw [Subgroup.le_centralizer_iff]
  refine sup_le (Subgroup.le_centralizer_iff.1 (rootGroup_le_centralizer hV k hβ hγ h1 h3))
    (Subgroup.le_centralizer_iff.1 (rootGroup_le_centralizer hV k hβ
      (CFSG.LieType.Chevalley.IsRoot.neg hγ) ?_ ?_))
  · rwa [← sub_eq_add_neg]
  · rwa [← sub_eq_add_neg]

theorem rankOne_le_centralizer {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (h1 : β + γ ≠ 0) (h2 : β - γ ≠ 0) (h3 : ¬ IsRoot τ (β + γ)) (h4 : ¬ IsRoot τ (β - γ)) :
    hV.rootGroup k β ⊔ hV.rootGroup k (-β) ≤
      Subgroup.centralizer ((hV.rootGroup k γ ⊔ hV.rootGroup k (-γ) : Subgroup _) :
        Set (hV.minGroup k)) := by
  have e1 : -β + γ = -(β - γ) := by abel
  have e2 : -β - γ = -(β + γ) := by abel
  refine sup_le (rootGroup_le_centralizer_rankOne hV k hβ hγ h1 h2 h3 h4)
    (rootGroup_le_centralizer_rankOne hV k (CFSG.LieType.Chevalley.IsRoot.neg hβ) hγ ?_ ?_ ?_ ?_)
  · rw [e1, neg_ne_zero]
    exact h2
  · rw [e2, neg_ne_zero]
    exact h1
  · rw [e1]
    exact fun h => h4 (by simpa using CFSG.LieType.Chevalley.IsRoot.neg h)
  · rw [e2]
    exact fun h => h3 (by simpa using CFSG.LieType.Chevalley.IsRoot.neg h)

theorem hm_neg_one_not_mem_center (hk : ringChar k ≠ 2) {j l : Fin τ.rank}
    (hjl : τ.cartan j l = -1) : hV.hm k j (-1) ∉ Subgroup.center (hV.minGroup k) := by
  intro hc
  have h := hV.hm_conj_xm k (IsRoot.basis l) j (-1) 1
  rw [← (Subgroup.mem_center_iff.1 hc (hV.xm k (Pi.single l 1) 1)), mul_inv_cancel_right,
    MinData.toWeight_single, hjl] at h
  have h1 := hV.xm_injective k (IsRoot.basis l) h
  simp only [zpow_neg, zpow_one, inv_neg, inv_one, Units.val_neg, Units.val_one, mul_one] at h1
  exact hk (neg_one_eq_one_iff.1 h1.symm)

theorem eq_one_or_eq_neg_one_of_mem_center {A : SL(2, k)} (hA : A ∈ Subgroup.center (SL(2, k))) :
    A = 1 ∨ (ringChar k ≠ 2 ∧ A = sl2Diag (-1)) := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin, sq] at hr
  rcases mul_self_eq_one_iff.1 hr with rfl | rfl
  · left
    refine Subtype.ext ?_
    rw [← hrA, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · by_cases h2 : ringChar k = 2
    · left
      refine Subtype.ext ?_
      rw [← hrA, Matrix.SpecialLinearGroup.coe_one, neg_one_eq_one_iff.2 h2]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · refine Or.inr ⟨h2, Subtype.ext ?_⟩
      rw [← hrA, coe_sl2Diag]
      ext i j
      fin_cases i <;> fin_cases j <;> simp

theorem exists_rootSL2' (hnb : ∀ j, ∃ l, τ.cartan j l = -1) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) :
    ∃ ρ : SL(2, k) →* hV.minGroup k, Function.Injective ρ ∧
      (∀ A, ρ A ∈ hV.rootGroup k γ ⊔ hV.rootGroup k (-γ)) ∧
      ∀ A, ρ A ∈ Subgroup.center (hV.minGroup k) → A = 1 := by
  obtain ⟨ρ, hinj, hmem, j, N, hN⟩ := exists_rootSL2 hV k hγ
  refine ⟨ρ, hinj, hmem, fun A hA => ?_⟩
  have hAc : A ∈ Subgroup.center (SL(2, k)) := by
    rw [Subgroup.mem_center_iff]
    intro B
    apply hinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hA (ρ B)
  rcases eq_one_or_eq_neg_one_of_mem_center k hAc with h | ⟨h2, rfl⟩
  · exact h
  · exfalso
    obtain ⟨l, hl⟩ := hnb j
    apply hm_neg_one_not_mem_center hV k h2 hl
    rw [Subgroup.mem_center_iff]
    intro g
    have hc := Subgroup.mem_center_iff.1 hA (N * g * N⁻¹)
    rw [hN] at hc
    have : N * (g * hV.hm k j (-1)) * N⁻¹ = N * (hV.hm k j (-1) * g) * N⁻¹ := by
      calc N * (g * hV.hm k j (-1)) * N⁻¹
          = N * g * N⁻¹ * (N * hV.hm k j (-1) * N⁻¹) := by group
        _ = N * hV.hm k j (-1) * N⁻¹ * (N * g * N⁻¹) := hc
        _ = N * (hV.hm k j (-1) * g) * N⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel this)

theorem exists_commuting_minuscule_SL2 (hnb : ∀ j, ∃ l, τ.cartan j l = -1) {n : ℕ}
    (α : Fin n → Fin τ.rank → ℤ)
    (h : (∀ i, CFSG.LieType.Chevalley.RootOps.isRootB τ (α i) = true) ∧
      ∀ i j, i ≠ j → α i + α j ≠ 0 ∧ α i - α j ≠ 0 ∧
        CFSG.LieType.Chevalley.RootOps.isRootB τ (α i + α j) = false ∧
        CFSG.LieType.Chevalley.RootOps.isRootB τ (α i - α j) = false) :
    ∃ ρ : Fin n → (SL(2, k) →* hV.minGroup k), (∀ i, Function.Injective (ρ i)) ∧
      (∀ i j, i ≠ j → ∀ A B : SL(2, k), ρ i A * ρ j B = ρ j B * ρ i A) ∧
      ∀ i A, ρ i A ∈ Subgroup.center (hV.minGroup k) → A = 1 := by
  have hroot : ∀ i, IsRoot τ (α i) := fun i =>
    CFSG.LieType.Chevalley.RootOps.isRootB_iff.1 (h.1 i)
  have hnot : ∀ {v : Fin τ.rank → ℤ}, CFSG.LieType.Chevalley.RootOps.isRootB τ v = false →
      ¬ IsRoot τ v := fun hv hr => by
    rw [← CFSG.LieType.Chevalley.RootOps.isRootB_iff, hv] at hr
    exact Bool.false_ne_true hr
  choose ρ hinj hmem hcen using fun i => exists_rootSL2' hV k hnb (hroot i)
  refine ⟨ρ, hinj, fun i j hij A B => ?_, hcen⟩
  obtain ⟨h1, h2, h3, h4⟩ := h.2 i j hij
  exact Subgroup.mem_centralizer_iff.1
    (rankOne_le_centralizer hV k (hroot i) (hroot j) h1 h2 (hnot h3) (hnot h4) (hmem i A))
    (ρ j B) (hmem j B) |>.symm

end CFSG.RankThree.PartTwo.Census.Exceptional
