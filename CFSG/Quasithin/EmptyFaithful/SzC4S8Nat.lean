module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.SzC4S8

open Matrix

theorem card_statedSL_three_eq_168 {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2) :
    Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) = 168 := by
  rw [← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).toEquiv,
    Matrix.card_SL_field, hF]
  simp [Fin.prod_univ_succ]

theorem card_le_four_of_fix_two {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    {T : Type*} (m : T → Matrix (Fin 3) (Fin 3) F) (hm : Function.Injective m)
    (hu : ∀ t, IsUnit (m t)) (x y : Fin 3 → F) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (hfx : ∀ t, m t *ᵥ x = x) (hfy : ∀ t, m t *ᵥ y = y) : Nat.card T ≤ 4 := by
  classical
  have h01 : ∀ a : F, a = 0 ∨ a = 1 := by
    have hs : ({0, 1} : Finset F) = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [Finset.card_pair zero_ne_one, hF])
    intro a
    have : a ∈ ({0, 1} : Finset F) := by rw [hs]; exact Finset.mem_univ a
    simpa using this
  have hli : LinearIndependent F ![x, y] := by
    rw [LinearIndependent.pair_iff' hx]
    intro a ha
    rcases h01 a with rfl | rfl
    · exact hy (by simpa using ha.symm)
    · exact hxy (by simpa using ha)
  have hfr : 2 < Module.finrank F (Fin 3 → F) := by simp
  obtain ⟨z, hz⟩ := exists_linearIndependent_cons_of_lt_finrank hli hfr
  have hzW : z ∉ Submodule.span F (Set.range ![x, y]) := (linearIndependent_finCons.1 hz).2
  have hspan : Submodule.span F (Set.range (Fin.cons z ![x, y] : Fin 3 → Fin 3 → F)) = ⊤ :=
    hz.span_eq_top_of_card_eq_finrank (by simp)
  set W : Submodule F (Fin 3 → F) := Submodule.span F (Set.range ![x, y]) with hW
  have hfixW : ∀ t, ∀ w ∈ W, m t *ᵥ w = w := by
    intro t w hw
    induction hw using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      fin_cases i <;> simp [hfx t, hfy t]
    | zero => simp
    | add a b _ _ ha hb => simp [Matrix.mulVec_add, ha, hb]
    | smul c a _ ha => simp [Matrix.mulVec_smul, ha]
  have hext : ∀ M₁ M₂ : Matrix (Fin 3) (Fin 3) F, M₁ *ᵥ z = M₂ *ᵥ z → M₁ *ᵥ x = M₂ *ᵥ x →
      M₁ *ᵥ y = M₂ *ᵥ y → M₁ = M₂ := by
    intro M₁ M₂ h1 h2 h3
    apply Matrix.toLin'.injective
    apply LinearMap.ext_on_range hspan
    intro i
    fin_cases i <;> simp [h1, h2, h3]
  have hnot : ∀ t, m t *ᵥ z ∉ W := by
    intro t hmem
    have h1 := hfixW t _ hmem
    have h2 : m t *ᵥ z = z := Matrix.mulVec_injective_iff_isUnit.2 (hu t) (by simpa using h1)
    exact hzW (h2 ▸ hmem)
  have hfinrankW : Module.finrank F W = 2 := by
    rw [hW, finrank_span_eq_card hli]; simp
  have hcardW : Fintype.card W = 4 := by
    rw [Module.card_eq_pow_finrank (K := F) (V := W), hF, hfinrankW]; norm_num
  have hcardV : Fintype.card (Fin 3 → F) = 8 := by simp [hF]
  have hcardC : Nat.card {v : Fin 3 → F // v ∉ W} = 4 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, hcardV]
    have : Fintype.card {v : Fin 3 → F // v ∈ W} = 4 := hcardW
    omega
  let φ : T → {v : Fin 3 → F // v ∉ W} := fun t => ⟨m t *ᵥ z, hnot t⟩
  have hφ : Function.Injective φ := by
    intro t₁ t₂ h
    have h1 : m t₁ *ᵥ z = m t₂ *ᵥ z := congrArg Subtype.val h
    apply hm
    exact hext _ _ h1 ((hfx t₁).trans (hfx t₂).symm) ((hfy t₁).trans (hfy t₂).symm)
  calc Nat.card T ≤ Nat.card {v : Fin 3 → F // v ∉ W} := Nat.card_le_card_of_injective φ hφ
    _ = 4 := hcardC

theorem no_two_fixed_vectors {Γ : Type} [Group Γ] {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) (α : Γ →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (hα : Function.Surjective α) (B : Subgroup Γ) (hB : ¬ 2 ∣ B.index)
    (x y : Fin 3 → F) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (hfx : ∀ b ∈ B,
      ((α b : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x = x)
    (hfy : ∀ b ∈ B,
      ((α b : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec y = y) :
    False := by
  classical
  have hcardG : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) = 168 :=
    card_statedSL_three_eq_168 hF
  have hidx : (B.map α).index ∣ B.index := Subgroup.index_map_dvd B hα
  have hodd : ¬ 2 ∣ (B.map α).index := fun h => hB (h.trans hidx)
  have hmul : Nat.card (B.map α) * (B.map α).index = 168 := by
    rw [Subgroup.card_mul_index, hcardG]
  have hcop : Nat.Coprime 8 (B.map α).index := by
    have h2 : Nat.Coprime 2 (B.map α).index :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
    simpa using h2.pow_left 3
  have h8 : 8 ∣ Nat.card (B.map α) :=
    hcop.dvd_of_dvd_mul_right (by rw [hmul]; norm_num)
  have hpos : Nat.card (B.map α) ≠ 0 := by
    intro h
    rw [h] at hmul
    omega
  have h4 : Nat.card (B.map α) ≤ 4 := by
    refine card_le_four_of_fix_two hF
      (fun b : B.map α => (((b : CFSG.Assembly.LowTwoRank.StatedSL 3 F) :
        Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ?_ ?_ x y hx hy hxy ?_ ?_
    · intro b₁ b₂ h
      exact Subtype.ext (Subtype.ext (Units.ext h))
    · intro b
      exact Units.isUnit _
    · intro b
      obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.1 b.2
      rw [← hcb]
      exact hfx c hc
    · intro b
      obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.1 b.2
      rw [← hcb]
      exact hfy c hc
  have h8' := Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) h8
  omega

end CFSG.Quasithin.SzC4S8
