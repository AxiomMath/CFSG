module

public import CFSG.RankThree.GF2n.Smith81.S81UGen
public import CFSG.RankThree.GF2n.Smith81.S81NModel1
public import CFSG.RankThree.GF2n.Smith81.S81UPureComb

public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.A5Cube Matrix exteriorPower
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F}

private theorem h80_tv_unitary (hσ : ∀ c, σ (σ c) = c) {a b : Fin 6} (hb : b = partner a)
    {c : F} (hc : σ c = c) :
    conjTr σ (Matrix.transvection a b c) * hypGram F * Matrix.transvection a b c = hypGram F := by
  subst hb
  exact transvection_long_unitary hσ a hc

theorem tInv1_unitary (hσ : ∀ c, σ (σ c) = c) :
    conjTr σ ((tInv1 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * hypGram F *
      ((tInv1 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = hypGram F := by
  have hT : ((tInv1 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      Matrix.transvection (0 : Fin 6) 1 1 := by
    simp only [tInv1, transvGL_val]
  rw [hT]
  exact h80_tv_unitary hσ (a := (0 : Fin 6)) (b := 1) (by decide) (map_one σ)

theorem tInv1_det : ((tInv1 F : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det = 1 := by
  unfold tInv1
  exact det_transvGL 0 1 (by decide) 1

theorem tInv1_mul_self : tInv1 F * tInv1 F = 1 := by
  have h2 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two, CharTwo.two_eq_zero]
  have hz : ∀ (i j : Fin 6) (hij : i ≠ j), transvGL F i j hij 0 = 1 := by
    intro i j hij
    apply Units.ext
    simp only [transvGL_val, Matrix.transvection_zero, Units.val_one]
  unfold tInv1
  rw [transvGL_mul_same, h2, hz]

@[expose] noncomputable def tSU1 (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) : SUid σ 6 :=
  ⟨frameGL σ ω hω * tInv1 F * (frameGL σ ω hω)⁻¹,
    frame_conj_mem_SUid hσ.invol hω tInv1_det (tInv1_unitary hσ.invol)⟩

@[expose] def adm1 (a b : Fin 6) : Prop := a ≠ 1 ∧ b ≠ 0

instance (a b : Fin 6) : Decidable (adm1 a b) := inferInstanceAs (Decidable (a ≠ 1 ∧ b ≠ 0))

theorem adm1_comm (a b : Fin 6) (hab : a ≠ b) (h : adm1 a b) (c : F) :
    transvGL F a b hab c * tInv1 F = tInv1 F * transvGL F a b hab c := by
  obtain ⟨ha1, hb0⟩ := h
  unfold tInv1
  exact transvGL_commute a b 0 1 hab (by decide) hb0 (fun e => ha1 e.symm) c 1

theorem adm1_pair (a b : Fin 6) (h : adm1 a b) : adm1 (partner b) (partner a) := by
  revert a b
  decide

theorem adm1_cover (I : Set.powersetCard (Fin 6) 3) : ∃ a ∈ I.val, ∃ b, b ∉ I.val ∧ adm1 a b := by
  have key : ∀ J : Finset (Fin 6), J.card = 3 → ∃ a ∈ J, ∃ b, b ∉ J ∧ (a ≠ 1 ∧ b ≠ 0) := by
    decide
  exact key I.val (Set.powersetCard.mem_iff.mp I.property)

private theorem h81_Nop_ub {a b : Fin 6} (hab : a ≠ b) (i j k i' j' k' : Fin 6)
    (hij : i < j) (hjk : j < k) (hij' : i' < j') (hjk' : j' < k')
    (hc : b ∈ ({i, j, k} : Finset (Fin 6))) (ha : a ∉ ({i, j, k} : Finset (Fin 6)))
    (he : insert a (({i, j, k} : Finset (Fin 6)).erase b) = {i', j', k'}) :
    Nop F a b hab (ub F i j k hij hjk) = ub F i' j' k' hij' hjk' := by
  unfold ub
  rw [Nop_cubeBasis]
  split_ifs with h
  · congr 1
    exact Subtype.ext he
  · exact (h ⟨hc, ha⟩).elim

private theorem h81_mem_ker (j : Fin 14) : kerG1 F j ∈ LinearMap.ker (rho F (tInv1 F) - 1) := by
  rw [(ker_range_eq1 (K := F)).1]
  exact Submodule.subset_span (Set.mem_range_self j)

private theorem h81_mem_range (j : Fin 6) :
    ranG1 F j ∈ LinearMap.range (rho F (tInv1 F) - 1) := by
  rw [(ker_range_eq1 (K := F)).2]
  exact Submodule.subset_span (Set.mem_range_self j)

theorem covC1_gens : ∀ u ∈ Set.range (kerG1 F), u ∈ LinearMap.range (rho F (tInv1 F) - 1) ∨
    ∃ (a b : Fin 6) (hab : a ≠ b), adm1 a b ∧ ∃ v ∈ LinearMap.ker (rho F (tInv1 F) - 1),
      Nop F a b hab v = u := by
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact Or.inr ⟨2, 3, by decide, by decide, kerG1 F 1, h81_mem_ker 1,
      h81_Nop_ub (a := 2) (b := 3) (by decide) 0 1 3 0 1 2 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  · exact Or.inr ⟨3, 2, by decide, by decide, kerG1 F 0, h81_mem_ker 0,
      h81_Nop_ub (a := 3) (b := 2) (by decide) 0 1 2 0 1 3 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  · exact Or.inr ⟨4, 2, by decide, by decide, kerG1 F 0, h81_mem_ker 0,
      h81_Nop_ub (a := 4) (b := 2) (by decide) 0 1 2 0 1 4 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  · exact Or.inr ⟨5, 2, by decide, by decide, kerG1 F 0, h81_mem_ker 0,
      h81_Nop_ub (a := 5) (b := 2) (by decide) 0 1 2 0 1 5 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  · exact Or.inl (h81_mem_range 0)
  · exact Or.inl (h81_mem_range 1)
  · exact Or.inl (h81_mem_range 2)
  · exact Or.inl (h81_mem_range 3)
  · exact Or.inl (h81_mem_range 4)
  · exact Or.inl (h81_mem_range 5)
  · exact Or.inr ⟨2, 5, by decide, by decide, kerG1 F 13, h81_mem_ker 13,
      h81_Nop_ub (a := 2) (b := 5) (by decide) 3 4 5 2 3 4 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  · exact Or.inr ⟨2, 4, by decide, by decide, kerG1 F 13, h81_mem_ker 13,
      h81_Nop_ub (a := 2) (b := 4) (by decide) 3 4 5 2 3 5 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  · exact Or.inr ⟨2, 3, by decide, by decide, kerG1 F 13, h81_mem_ker 13,
      h81_Nop_ub (a := 2) (b := 3) (by decide) 3 4 5 2 4 5 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  · exact Or.inr ⟨3, 2, by decide, by decide, kerG1 F 12, h81_mem_ker 12,
      h81_Nop_ub (a := 3) (b := 2) (by decide) 2 4 5 3 4 5 (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)⟩

theorem pos1_pair (a b : Fin 6) (h : pos1 a b) : pos1 (partner b) (partner a) := by
  have key : ∀ x y : Fin 6, pos1 x y → pos1 (partner y) (partner x) := by decide
  exact key a b h

theorem pos1_adm (a b : Fin 6) (h : pos1 a b) : adm1 a b := by
  have key : ∀ x y : Fin 6, pos1 x y → adm1 x y := by decide
  exact key a b h

theorem hUC1 (a b : Fin 6) (hab : a ≠ b) (c : F) (h : pos1 a b) :
    ∀ ξ ∈ LinearMap.ker (rho F (tInv1 F) - 1),
      rho F (transvGL F a b hab c) ξ - ξ ∈ LinearMap.range (rho F (tInv1 F) - 1) := by
  have hp : (a = 0 ∧ 1 ≤ b.val) ∨ (b = 1 ∧ 2 ≤ a.val) := by
    have key : ∀ x y : Fin 6, pos1 x y → (x = 0 ∧ 1 ≤ y.val) ∨ (y = 1 ∧ 2 ≤ x.val) := by
      decide
    exact key a b h
  intro ξ hξ
  exact model1_hUC (K := F) (u := transvGL F a b hab c) ⟨a, b, hab, c, hp, rfl⟩ ξ hξ

theorem hUfix1 : ∀ ξ ∈ LinearMap.ker (rho F (tInv1 F) - 1),
    (∀ (a b : Fin 6) (hab : a ≠ b) (c : F), pos1 a b → rho F (transvGL F a b hab c) ξ = ξ) →
      ξ ∈ LinearMap.range (rho F (tInv1 F) - 1) := by
  intro ξ hξ hfix
  refine model1_hUfix (K := F) ξ hξ ?_
  rintro u ⟨a, b, hab, c, hpos, rfl⟩
  have hp : pos1 a b := by
    have key : ∀ x y : Fin 6, (x = 0 ∧ 1 ≤ y.val) ∨ (y = 1 ∧ 2 ≤ x.val) → pos1 x y := by
      decide
    exact key a b hpos
  exact hfix a b hab c hp

@[expose] def posP1 (a b : Fin 6) : Prop :=
  (a = 2 ∧ b = 4) ∨ (a = 2 ∧ b = 5) ∨ (a = 4 ∧ b = 3) ∨ (a = 5 ∧ b = 3)

@[expose] def lev1 : Fin 6 → ℕ := ![0, 0, 0, 3, 1, 2]

theorem lev1_le (i : Fin 6) : lev1 i ≤ 3 := by
  revert i
  decide

theorem posP1_lev (a b : Fin 6) (h : posP1 a b) :
    lev1 a < lev1 b ∧ lev1 (partner b) < lev1 (partner a) := by
  unfold posP1 at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem posP1_ne (a b : Fin 6) (h : posP1 a b) : b ≠ partner a := by
  unfold posP1 at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

private theorem h83_posP1_adm (a b : Fin 6) (h : posP1 a b) : adm1 a b := by
  unfold posP1 at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem posP1_comm (hσ : IsUnitaryInvolution σ) {ω : F} (hω : ω + σ ω = 1) (t : SUid σ 6)
    (ht : (t : GL (Fin 6) F) = frameGL σ ω hω * tInv1 F * (frameGL σ ω hω)⁻¹)
    {l : F} (hl : σ l = l) (hl0 : l ≠ 0) (hl1 : l ≠ 1) :
    ∀ (a b : Fin 6) (hab : a ≠ b) (hb : b ≠ partner a), posP1 a b → ∀ c : F,
      ∃ A ∈ Gcent σ t, ∃ B ∈ Gcent σ t, gShort hσ hω hab hb c = ⁅A, B⁆ := by
  intro a b hab hb hpos c
  have hadm : adm1 a b := h83_posP1_adm a b hpos
  have hd : ∀ i : Fin 6, (![1, 1, l, l⁻¹, 1, 1] : Fin 6 → F) i ≠ 0 := by
    intro i
    fin_cases i <;> simp [hl0]
  have hu : ∀ i : Fin 6, σ ((![1, 1, l, l⁻¹, 1, 1] : Fin 6 → F) i) *
      (![1, 1, l, l⁻¹, 1, 1] : Fin 6 → F) (partner i) = 1 := by
    intro i
    fin_cases i <;> simp [partner, map_one, map_inv₀, hl, hl0]
  have hdet : ∏ i, (![1, 1, l, l⁻¹, 1, 1] : Fin 6 → F) i = 1 := by
    rw [Fin.prod_univ_six]
    simp [hl0]
  have hdx := diagGL_commute_transvGL (![1, 1, l, l⁻¹, 1, 1] : Fin 6 → F) hd 0 1 (by decide) 1 rfl
  have hl1' : (1 : F) ≠ l⁻¹ := fun h => hl1 (inv_eq_one.mp h.symm)
  have hne : (![1, 1, l, l⁻¹, 1, 1] : Fin 6 → F) a ≠ (![1, 1, l, l⁻¹, 1, 1] : Fin 6 → F) b := by
    unfold posP1 at hpos
    rcases hpos with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hl1, hl1']
  exact gShort_eq_comm hσ hω t (tInv1 F) ht hab hb
    (fun c => adm1_comm a b hab hadm c)
    (fun c => adm1_comm (partner b) (partner a) (partner_ne_partner hab) (adm1_pair a b hadm) c)
    (![1, 1, l, l⁻¹, 1, 1] : Fin 6 → F) hd hu hdet hdx hne c

theorem hpure1 : ∀ ξ ∈ LinearMap.range (rho F (tInv1 F) - 1),
    (∀ (a b : Fin 6) (hab : a ≠ b), posP1 a b → rho F (transvGL F a b hab 1) ξ = ξ) → IsPure F ξ := by
  intro ξ hξR hfix
  rw [(ker_range_eq1 (K := F)).2] at hξR
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hξR
  have hz : ∀ (i j : Fin 6) (hij : i ≠ j),
      (i = 2 ∧ j = 4) ∨ (i = 2 ∧ j = 5) ∨ (i = 4 ∧ j = 3) ∨ (i = 5 ∧ j = 3) →
        rho F (transvGL F i j hij 1) ξ = ξ :=
    fun i j hij hp => hfix i j hij hp
  have hs_eq : ξ = cfm F ξ 21 • ub F 0 2 4 + cfm F ξ 37 • ub F 0 2 5 := by
    apply cfm_ext3
    intro m hm hc'
    rcases exists_mask3 hm hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | (simp (config := {decide := true}) [cfm_add, cfm_smul, cfm_ub_mask]; done)
    | (rw [cfm_zero_of_fixed (fun p q : Fin 6 => (p = 2 ∧ q = 4) ∨ (p = 2 ∧ q = 5) ∨
          (p = 4 ∧ q = 3) ∨ (p = 5 ∧ q = 3)) hz _ hm (by decide)]
       simp (config := {decide := true}) [cfm_add, cfm_smul, cfm_ub_mask]; done)
    | (rw [← hc]
       simp (config := {decide := true}) [ranG1, cfm_add, cfm_smul, cfm_ub_mask, Fin.sum_univ_succ,
         cfm_zero]; done)
  rw [hs_eq]
  exact isPure_comb_024_025 _ _

theorem involModel12_tSU1 [Finite F] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (h4 : 4 ≤ 2 ^ f)
    {ω : F} (hω : ω + unitaryInvolution F 2 f ω = 1) :
    UInvolModel12 (unitaryInvolution F 2 f)
      (tSU1 (isUnitaryInvolution_unitaryInvolution hF) hω) := by
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨l, hl, hl0, hl1⟩ := exists_fixed_ne_zero_one hF h4
  have ht : ((tSU1 hσ hω : SUid (unitaryInvolution F 2 f) 6) : GL (Fin 6) F) =
      frameGL (unitaryInvolution F 2 f) ω hω * tInv1 F *
        (frameGL (unitaryInvolution F 2 f) ω hω)⁻¹ := rfl
  have H1 : ∀ (a b : Fin 6) (hab : a ≠ b), adm1 a b → ∀ c : F,
      transvGL F a b hab c * tInv1 F = tInv1 F * transvGL F a b hab c :=
    fun a b hab h c => adm1_comm a b hab h c
  have H2 : ∀ a b : Fin 6, adm1 a b → adm1 (partner b) (partner a) := fun a b h => adm1_pair a b h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact covW_of_F hσ _ (covW_F_of_adm hσ hω _ (tInv1 F) ht adm1 H1 H2 adm1_cover)
  · exact covC_of_F hσ _ (covC_F_of_gens hσ hω _ (tInv1 F) ht adm1 H1 H2
      (Set.range (kerG1 F)) (ker_range_eq1 (K := F)).1.le covC1_gens)
  · obtain ⟨hU, h1, h2⟩ := P3_F_of_pos hσ hω _ (tInv1 F) ht tInv1_mul_self pos1 pos1_pair
      (fun a b hab h c => adm1_comm a b hab (pos1_adm a b h) c)
      (fun a b hab c h => hUC1 a b hab c h) hUfix1
    exact ⟨rootFam hσ hω pos1, P3_of_F hσ _ _ hU h1 h2⟩
  · exact P2_of_roots hσ hω _ (tInv1 F) ht posP1 lev1 lev1_le posP1_lev posP1_ne
      (posP1_comm hσ hω _ ht hl hl0 hl1) hpure1

end CFSG.RankThree.GF2n.Smith81.U6Cube
