module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedF4ClassDefs
public import CFSG.HardMathSupport.Dickson.Bal207.FamF42Class
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane
public import CFSG.LocalAnalysis.StandardType.GGLieCoreCent
public import CFSG.LocalAnalysis.StandardType.GGSixA6F4ClsKilled
public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcF4Kernel2

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Assembly.LowTwoRank
  CFSG.StandardType.LieCore

private theorem ggA6F4_exists_zeta_seven (L : Type) [Field L] [CharP L 2] [IsAlgClosed L] :
    ∃ ζ : Lˣ, orderOf ζ = 7 := by
  have hp : (7 : L) ≠ 0 := by
    intro h
    have h27 : (2 : ℕ) ∣ 7 := (CharP.cast_eq_zero_iff L 2 7).1 (by exact_mod_cast h)
    norm_num at h27
  have : NeZero ((7 : ℕ) : L) := ⟨hp⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 7
  lift ζ₀ to Lˣ using hζ₀.isUnit (by norm_num)
  rw [IsPrimitiveRoot.coe_units_iff] at hζ₀
  exact ⟨ζ₀, hζ₀.eq_orderOf.symm⟩

private theorem ggA6F4_closure_eq_zpowers_of_mem {G : Type*} [Group G] {x y : G}
    (h : x ∈ Subgroup.zpowers y) :
    Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers y := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz
    · rw [hz]
      exact h
    · rw [hz]
      exact Subgroup.mem_zpowers_iff.mpr ⟨1, by rw [zpow_one]⟩
  · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))

private theorem ggA6F4_unit_eq_pow_of_smul {L : Type} [Field L] {ζ : Lˣ}
    (hζ : orderOf ζ = 7) {a₁ a₂ : Fin Tag.F4.rank → Lˣ} {c₁ c₂ : Fin Tag.F4.rank → ZMod 7}
    (hc₁ : ∀ i, ζ ^ (c₁ i).val = a₁ i) (hc₂ : ∀ i, ζ ^ (c₂ i).val = a₂ i)
    {t : ZMod 7} (h : c₁ = fun i => t * c₂ i) :
    rootDiagUnit Tag.F4 a₁ = (rootDiagUnit Tag.F4 a₂) ^ t.val := by
  have hζp : ζ ^ 7 = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hpoint : a₁ = a₂ ^ t.val := by
    funext i
    show a₁ i = (a₂ i) ^ t.val
    have hm : (((t.val * (c₂ i).val : ℕ) : ℤ) : ZMod 7) = t * c₂ i := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rw [← hc₁ i, ← hc₂ i, h]
    rw [CFSG.RankThree.Chevalley.pow_val_eq_zpow_of_pow_eq_one hζp (t * c₂ i)
      ((t.val * (c₂ i).val : ℕ) : ℤ) hm]
    rw [zpow_natCast, ← pow_mul]
    congr 1
    ring
  rw [hpoint, ← rootDiagUnit_pow]

private theorem ggA6F4_char_sq {L : Type} [Field L] [CharP L 2] {ζ : Lˣ}
    (hζ : orderOf ζ = 7) {a : Fin Tag.F4.rank → Lˣ} {c : Fin Tag.F4.rank → ZMod 7}
    (hc : ∀ i, ζ ^ (c i).val = a i) {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)}
    (hchar : ∀ γ, IsRoot Tag.F4 γ → rootChar a (ρ γ) = rootChar a γ ^ 2) :
    ∀ γ, IsRoot Tag.F4 γ → ggA6F4Val c (ρ γ) = 2 * ggA6F4Val c γ := by
  intro γ hγ
  have hζp : ζ ^ 7 = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hpow1 : rootChar a γ = ζ ^ ((ggA6F4Val c γ).val) := by
    rw [CFSG.LocalAnalysis.GLTheoremA.T173O.rootChar_eq_zeta_pow hζ hc γ]
    rfl
  have hpow2 : rootChar a (ρ γ) = ζ ^ ((ggA6F4Val c (ρ γ)).val) := by
    rw [CFSG.LocalAnalysis.GLTheoremA.T173O.rootChar_eq_zeta_pow hζ hc (ρ γ)]
    rfl
  have hrel : ζ ^ ((ggA6F4Val c (ρ γ)).val) = ζ ^ (2 * (ggA6F4Val c γ).val) := by
    rw [← hpow2, hchar γ hγ, hpow1, ← pow_mul]
    congr 1
    ring
  have hm : ((((2 * (ggA6F4Val c γ).val : ℕ) : ℤ)) : ZMod 7) = 2 * ggA6F4Val c γ := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  have h2n : ζ ^ ((2 * ggA6F4Val c γ)).val = ζ ^ (2 * (ggA6F4Val c γ).val) := by
    rw [CFSG.RankThree.Chevalley.pow_val_eq_zpow_of_pow_eq_one hζp (2 * ggA6F4Val c γ)
      ((2 * (ggA6F4Val c γ).val : ℕ) : ℤ) hm]
    rw [zpow_natCast]
  exact CFSG.RankThree.Chevalley.eq_of_pow_val_eq_pow_val hζ (hrel.trans h2n.symm)

private theorem ggA6F4_independent_of_card {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {ζ : Lˣ} (hζ : orderOf ζ = 7)
    {a₁ a₂ : Fin Tag.F4.rank → Lˣ} {c₁ c₂ : Fin Tag.F4.rank → ZMod 7}
    (hc₁ : ∀ i, ζ ^ (c₁ i).val = a₁ i) (hc₂ : ∀ i, ζ ^ (c₂ i).val = a₂ i)
    (h₁ : rootDiagUnit Tag.F4 a₁ ^ 7 = 1) (h₂ : rootDiagUnit Tag.F4 a₂ ^ 7 = 1)
    (hcard : Nat.card (Subgroup.closure {rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
      Subgroup (ModGL Tag.F4 L)) = 7 ^ 2) :
    ∀ a b : ZMod 7, (a ≠ 0 ∨ b ≠ 0) → ∃ i, a * c₁ i + b * c₂ i ≠ 0 := by
  classical
  intro a b hne
  by_contra h
  push Not at h
  have hle : Nat.card (Subgroup.closure {rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
      Subgroup (ModGL Tag.F4 L)) ≤ 7 := by
    by_cases ha : a = 0
    · have hb : b ≠ 0 := by rcases hne with h' | h' <;> [exact absurd ha h'; exact h']
      have hc₂_eq : c₂ = fun i => (0 : ZMod 7) * c₁ i := by
        funext i
        have hi := h i
        rw [ha, zero_mul, zero_add] at hi
        have hzi : c₂ i = 0 := (mul_eq_zero.mp hi).resolve_left hb
        rw [hzi, zero_mul]
      have ht : rootDiagUnit Tag.F4 a₂ = (rootDiagUnit Tag.F4 a₁) ^ (0 : ZMod 7).val :=
        ggA6F4_unit_eq_pow_of_smul hζ hc₂ hc₁ hc₂_eq
      have hmem : rootDiagUnit Tag.F4 a₂ ∈ Subgroup.zpowers (rootDiagUnit Tag.F4 a₁) :=
        Subgroup.mem_zpowers_iff.mpr ⟨(0 : ZMod 7).val, by rw [zpow_natCast, ht]⟩
      have heq : Subgroup.closure ({rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
          Set (ModGL Tag.F4 L)) = Subgroup.zpowers (rootDiagUnit Tag.F4 a₁) := by
        rw [Set.pair_comm]
        exact ggA6F4_closure_eq_zpowers_of_mem hmem
      rw [heq, Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h₁)
    · have hc₁_eq : c₁ = fun i => (-b * a⁻¹) * c₂ i := by
        funext i
        have hi : a * c₁ i = -(b * c₂ i) := by
          have h0 := h i
          rw [add_eq_zero_iff_eq_neg] at h0
          exact h0
        calc c₁ i = a⁻¹ * (a * c₁ i) := by rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
          _ = a⁻¹ * (-(b * c₂ i)) := by rw [hi]
          _ = (-b * a⁻¹) * c₂ i := by ring
      have ht : rootDiagUnit Tag.F4 a₁ = (rootDiagUnit Tag.F4 a₂) ^ (-b * a⁻¹).val :=
        ggA6F4_unit_eq_pow_of_smul hζ hc₁ hc₂ hc₁_eq
      have hmem : rootDiagUnit Tag.F4 a₁ ∈ Subgroup.zpowers (rootDiagUnit Tag.F4 a₂) :=
        Subgroup.mem_zpowers_iff.mpr ⟨(-b * a⁻¹).val, by rw [zpow_natCast, ht]⟩
      rw [ggA6F4_closure_eq_zpowers_of_mem hmem, Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h₂)
  rw [hcard] at hle
  norm_num at hle

theorem ggA6F4_rootsTrivialOn_eq_empty
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (a₁ a₂ : Fin Tag.F4.rank → Lˣ) (h₁ : rootDiagUnit Tag.F4 a₁ ^ 7 = 1)
    (h₂ : rootDiagUnit Tag.F4 a₂ ^ 7 = 1)
    (hcard : Nat.card (Subgroup.closure {rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
      Subgroup (ModGL Tag.F4 L)) = 7 ^ 2)
    (ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)) (hroot : ∀ γ, IsRoot Tag.F4 (ρ γ) ↔ IsRoot Tag.F4 γ)
    (hchar : ∀ γ, IsRoot Tag.F4 γ →
      rootChar a₁ (ρ γ) = rootChar a₁ γ ^ 2 ∧ rootChar a₂ (ρ γ) = rootChar a₂ γ ^ 2) :
    rootsTrivialOn (Subgroup.closure {rootDiagUnit Tag.F4 a₁, rootDiagUnit Tag.F4 a₂} :
      Subgroup (ModGL Tag.F4 L)) = ∅ := by
  classical
  obtain ⟨ζ, hζ⟩ := ggA6F4_exists_zeta_seven L
  have ha₁ : ∀ i, a₁ i ^ 7 = 1 := by
    have h : a₁ ^ 7 = 1 :=
      rootDiagUnit_injective (by rw [← rootDiagUnit_pow, h₁, rootDiagUnit_one])
    intro i
    simpa using congrFun h i
  have ha₂ : ∀ i, a₂ i ^ 7 = 1 := by
    have h : a₂ ^ 7 = 1 :=
      rootDiagUnit_injective (by rw [← rootDiagUnit_pow, h₂, rootDiagUnit_one])
    intro i
    simpa using congrFun h i
  choose c₁ hc₁ using fun i =>
    CFSG.RankThree.Chevalley.exists_pow_val_eq_of_pow_eq_one hζ (ha₁ i)
  choose c₂ hc₂ using fun i =>
    CFSG.RankThree.Chevalley.exists_pow_val_eq_of_pow_eq_one hζ (ha₂ i)
  have hind : ∀ a b : ZMod 7, (a ≠ 0 ∨ b ≠ 0) → ∃ i, a * c₁ i + b * c₂ i ≠ 0 :=
    ggA6F4_independent_of_card hζ hc₁ hc₂ h₁ h₂ hcard
  have h₁' : ∀ γ, IsRoot Tag.F4 γ → ggA6F4Val c₁ (ρ γ) = 2 * ggA6F4Val c₁ γ :=
    ggA6F4_char_sq hζ hc₁ fun γ hγ => (hchar γ hγ).1
  have h₂' : ∀ γ, IsRoot Tag.F4 γ → ggA6F4Val c₂ (ρ γ) = 2 * ggA6F4Val c₂ γ :=
    ggA6F4_char_sq hζ hc₂ fun γ hγ => (hchar γ hγ).2
  have hkilled := ggA6F4_killed_root c₁ c₂ hind ρ hroot h₁' h₂'
  rw [Set.eq_empty_iff_forall_notMem]
  intro γ hγ
  unfold rootsTrivialOn at hγ
  obtain ⟨hγroot, hγchar⟩ := hγ
  have hchar₁ : rootChar a₁ γ = 1 :=
    hγchar a₁ (Subgroup.subset_closure (by simp))
  have hchar₂ : rootChar a₂ γ = 1 :=
    hγchar a₂ (Subgroup.subset_closure (by simp))
  have hz₁ : ggA6F4Val c₁ γ = 0 := by
    simpa [ggA6F4Val] using
      (CFSG.LocalAnalysis.GLTheoremA.T173O.rootChar_eq_one_iff hζ hc₁ γ).1 hchar₁
  have hz₂ : ggA6F4Val c₂ γ = 0 := by
    simpa [ggA6F4Val] using
      (CFSG.LocalAnalysis.GLTheoremA.T173O.rootChar_eq_one_iff hζ hc₂ γ).1 hchar₂
  exact hkilled γ hγroot ⟨hz₁, hz₂⟩

end CFSG.StandardType.A6Red
