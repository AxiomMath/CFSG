module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTri8Def
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTri8Invol
public import CFSG.Quasithin.Background.G64NatSec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V} {K₁ K₂ : Type} [Field K₁] [Field K₂] [Finite K₁] [Finite K₂]
  {I₁ I₂ : Subgroup (Vtil V₀ V hV)}
  {π₁ : ↥(StatedOmega (StatedQuadPlus 4 K₁)) →* ↥(lBar V₀ V hV L)}
  {π₂ : ↥(StatedOmega (StatedQuadPlus 4 K₂)) →* ↥(lBar V₀ V hV L)}

private theorem s16k_natAct_ofAdd_mul_inv {K : Type} [Field K] [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K)}
    (g : ↥Γ) (v : Fin 4 ⊕ Fin 4 → K) :
    natAct Γ g (Multiplicative.ofAdd v) * (Multiplicative.ofAdd v)⁻¹ =
      Multiplicative.ofAdd ((((g : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K)).mulVec v - v) := by
  simp only [natAct, toAdd_ofAdd]
  rw [← ofAdd_neg, ← ofAdd_add, sub_eq_add_neg]

private theorem s16k_exists_two_comm {V : Type} [CommGroup V]
    {K : Type} [Field K] [Finite K]
    {H : Subgroup (MulAut V)} {I : Subgroup V}
    {π : ↥(StatedOmega (StatedQuadPlus 4 K)) →* ↥H}
    {f : ↥I →* Multiplicative (Fin 4 ⊕ Fin 4 → K)}
    (hfs : Function.Surjective f)
    (hfe : ∀ (γ : ↥(StatedOmega (StatedQuadPlus 4 K))) (u : ↥I)
        (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ I), f ⟨_, hu⟩ = natAct _ γ (f u))
    (hI : ∀ h : ↥H, ∀ u ∈ I, (h : MulAut V) u ∈ I)
    {g : ↥(StatedOmega (StatedQuadPlus 4 K))} {t : MulAut V} (ht : t ∈ H)
    (hgt : (π g : ↥H) = ⟨t, ht⟩)
    {u₁ u₂ : Fin 4 ⊕ Fin 4 → K} (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₁₂ : u₁ ≠ u₂)
    {v₁ v₂ : Fin 4 ⊕ Fin 4 → K}
    (hv₁ : u₁ = ((g : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K).mulVec v₁ - v₁)
    (hv₂ : u₂ = ((g : Matrix.GeneralLinearGroup (Fin 4 ⊕ Fin 4) K) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K).mulVec v₂ - v₂) :
    ∃ c₁ c₂ : ↥I, f c₁ = Multiplicative.ofAdd u₁ ∧ f c₂ = Multiplicative.ofAdd u₂ ∧
      (c₁ : V) ∈ commSub ⊤ (Subgroup.zpowers t) ∧
      (c₂ : V) ∈ commSub ⊤ (Subgroup.zpowers t) := by
  obtain ⟨w₁, hw₁⟩ := hfs (Multiplicative.ofAdd v₁)
  obtain ⟨w₂, hw₂⟩ := hfs (Multiplicative.ofAdd v₂)
  have hmem₁ : ((π g : ↥H) : MulAut V) (w₁ : V) ∈ I := by
    rw [hgt]; exact hI ⟨t, ht⟩ w₁ w₁.2
  have hmem₂ : ((π g : ↥H) : MulAut V) (w₂ : V) ∈ I := by
    rw [hgt]; exact hI ⟨t, ht⟩ w₂ w₂.2
  let c₁ : ↥I := ⟨((π g : ↥H) : MulAut V) (w₁ : V) * (w₁ : V)⁻¹,
    I.mul_mem hmem₁ (I.inv_mem w₁.2)⟩
  let c₂ : ↥I := ⟨((π g : ↥H) : MulAut V) (w₂ : V) * (w₂ : V)⁻¹,
    I.mul_mem hmem₂ (I.inv_mem w₂.2)⟩
  have hc₁eq : c₁ = ⟨((π g : ↥H) : MulAut V) (w₁ : V), hmem₁⟩ * w₁⁻¹ := Subtype.ext rfl
  have hc₂eq : c₂ = ⟨((π g : ↥H) : MulAut V) (w₂ : V), hmem₂⟩ * w₂⁻¹ := Subtype.ext rfl
  have hf₁ : f c₁ = Multiplicative.ofAdd u₁ := by
    rw [hc₁eq, map_mul, map_inv, hfe g w₁ hmem₁, hw₁, s16k_natAct_ofAdd_mul_inv, ← hv₁]
  have hf₂ : f c₂ = Multiplicative.ofAdd u₂ := by
    rw [hc₂eq, map_mul, map_inv, hfe g w₂ hmem₂, hw₂, s16k_natAct_ofAdd_mul_inv, ← hv₂]
  refine ⟨c₁, c₂, hf₁, hf₂, ?_, ?_⟩
  · have hcoe : (c₁ : V) = t (w₁ : V) * (w₁ : V)⁻¹ := by
      show ((π g : ↥H) : MulAut V) (w₁ : V) * (w₁ : V)⁻¹ = t (w₁ : V) * (w₁ : V)⁻¹
      rw [show ((π g : ↥H) : MulAut V) = t from congrArg Subtype.val hgt]
    rw [hcoe]
    exact Subgroup.subset_closure
      ⟨t, Subgroup.mem_zpowers t, (w₁ : V), Subgroup.mem_top _, rfl⟩
  · have hcoe : (c₂ : V) = t (w₂ : V) * (w₂ : V)⁻¹ := by
      show ((π g : ↥H) : MulAut V) (w₂ : V) * (w₂ : V)⁻¹ = t (w₂ : V) * (w₂ : V)⁻¹
      rw [show ((π g : ↥H) : MulAut V) = t from congrArg Subtype.val hgt]
    rw [hcoe]
    exact Subgroup.subset_closure
      ⟨t, Subgroup.mem_zpowers t, (w₂ : V), Subgroup.mem_top _, rfl⟩

private theorem s16k_two_le_rk_map_closure {V : Type} [CommGroup V] [Finite V]
    (hV2 : ∀ w : V, w ^ 2 = 1) {Z : Subgroup V} [Z.Normal] {I : Subgroup V} {c₁ c₂ : ↥I}
    {K : Type} [Field K] [Finite K]
    {u₁ u₂ : Fin 4 ⊕ Fin 4 → K}
    {f : ↥I →* Multiplicative (Fin 4 ⊕ Fin 4 → K)}
    (hfk : ∀ u : ↥I, f u = 1 ↔ (u : V) ∈ Z)
    (hf₁ : f c₁ = Multiplicative.ofAdd u₁) (hf₂ : f c₂ = Multiplicative.ofAdd u₂)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₁₂ : u₁ ≠ u₂) :
    2 ≤ rk ↥(Subgroup.map (QuotientGroup.mk' Z)
      (Subgroup.closure ({(c₁ : V), (c₂ : V)} : Set V))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α : V ⧸ Z := (QuotientGroup.mk' Z) (c₁ : V) with hαdef
  set β : V ⧸ Z := (QuotientGroup.mk' Z) (c₂ : V) with hβdef
  have hα2 : α ^ 2 = 1 := by
    rw [hαdef, ← map_pow, hV2 (c₁ : V), map_one]
  have hβ2 : β ^ 2 = 1 := by
    rw [hβdef, ← map_pow, hV2 (c₂ : V), map_one]
  have hα1 : α ≠ 1 := by
    intro h
    have h1 : (QuotientGroup.mk' Z) (c₁ : V) = 1 := by rw [← hαdef]; exact h
    have hZ : (c₁ : V) ∈ Z := by
      rw [← QuotientGroup.ker_mk' Z]
      exact MonoidHom.mem_ker.mpr h1
    have hf : f c₁ = 1 := (hfk c₁).mpr hZ
    rw [hf₁] at hf
    exact hu₁ (Multiplicative.ofAdd.injective (by simpa using hf))
  have hβ1 : β ≠ 1 := by
    intro h
    have h1 : (QuotientGroup.mk' Z) (c₂ : V) = 1 := by rw [← hβdef]; exact h
    have hZ : (c₂ : V) ∈ Z := by
      rw [← QuotientGroup.ker_mk' Z]
      exact MonoidHom.mem_ker.mpr h1
    have hf : f c₂ = 1 := (hfk c₂).mpr hZ
    rw [hf₂] at hf
    exact hu₂ (Multiplicative.ofAdd.injective (by simpa using hf))
  have hαβ : α ≠ β := by
    intro h
    have hv : (QuotientGroup.mk' Z) (c₁ : V) = (QuotientGroup.mk' Z) (c₂ : V) := by
      rw [← hαdef, ← hβdef]; exact h
    have h1 : (QuotientGroup.mk' Z) ((c₁ : V) * (c₂ : V)⁻¹) = 1 := by
      rw [map_mul, map_inv, hv, mul_inv_cancel]
    have hZ : (c₁ : V) * (c₂ : V)⁻¹ ∈ Z := by
      rw [← QuotientGroup.ker_mk' Z]
      exact MonoidHom.mem_ker.mpr h1
    have hmemI : (c₁ : V) * (c₂ : V)⁻¹ ∈ I := I.mul_mem c₁.2 (I.inv_mem c₂.2)
    have hf : f ⟨(c₁ : V) * (c₂ : V)⁻¹, hmemI⟩ = 1 := (hfk _).mpr hZ
    rw [show (⟨(c₁ : V) * (c₂ : V)⁻¹, hmemI⟩ : ↥I) = c₁ * c₂⁻¹ from Subtype.ext rfl,
      map_mul, map_inv, hf₁, hf₂] at hf
    have h2 : Multiplicative.ofAdd (u₁ + -u₂) = 1 := by
      rw [ofAdd_add, ofAdd_neg]; exact hf
    have h3 : u₁ + -u₂ = 0 := Multiplicative.ofAdd.injective (by simpa using h2)
    exact hu₁₂ (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h3))
  set Xb : Subgroup (V ⧸ Z) := Subgroup.map (QuotientGroup.mk' Z)
    (Subgroup.closure ({(c₁ : V), (c₂ : V)} : Set V)) with hXb
  have ha : α ∈ Xb := by
    rw [hXb, hαdef]
    exact Subgroup.mem_map.mpr ⟨(c₁ : V), Subgroup.subset_closure (by simp), rfl⟩
  have hbmem : β ∈ Xb := by
    rw [hXb, hβdef]
    exact Subgroup.mem_map.mpr ⟨(c₂ : V), Subgroup.subset_closure (by simp), rfl⟩
  set P : Subgroup (V ⧸ Z) := Subgroup.zpowers α ⊔ Subgroup.zpowers β with hP
  have hPle : P ≤ Xb := by
    rw [hP, sup_le_iff]
    exact ⟨Subgroup.zpowers_le.mpr ha, Subgroup.zpowers_le.mpr hbmem⟩
  have hcardα : Nat.card ↥(Subgroup.zpowers α) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) hα2 hα1]
  have hcardβ : Nat.card ↥(Subgroup.zpowers β) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) hβ2 hβ1]
  have hinfP : Subgroup.zpowers α ⊓ Subgroup.zpowers β = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rw [Subgroup.mem_inf] at hy
    have hyα : y = 1 ∨ y = α := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy.1
      rw [← hk, ← zpow_mod_orderOf, orderOf_eq_prime (p := 2) hα2 hα1]
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · exact Or.inl (by rw [show k % ((2 : ℕ) : ℤ) = 0 from by simpa using h0, zpow_zero])
      · exact Or.inr (by rw [show k % ((2 : ℕ) : ℤ) = 1 from by simpa using h1, zpow_one])
    have hyβ : y = 1 ∨ y = β := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy.2
      rw [← hk, ← zpow_mod_orderOf, orderOf_eq_prime (p := 2) hβ2 hβ1]
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · exact Or.inl (by rw [show k % ((2 : ℕ) : ℤ) = 0 from by simpa using h0, zpow_zero])
      · exact Or.inr (by rw [show k % ((2 : ℕ) : ℤ) = 1 from by simpa using h1, zpow_one])
    rcases hyα with h | h <;> rcases hyβ with h' | h'
    · exact h
    · exact absurd (h.symm.trans h') (Ne.symm hβ1)
    · exact absurd (h.symm.trans h') hα1
    · exact absurd (h.symm.trans h') hαβ
  have hcardP : Nat.card ↥P = 4 := by
    have h := card_sup_mul_card_inf (Subgroup.zpowers α) (Subgroup.zpowers β)
    rw [hinfP, hcardα, hcardβ] at h
    rw [hP]
    simpa using h
  have hrkP : rk ↥P = 2 := by
    rw [rk, hcardP, show (4 : ℕ) = 2 ^ 2 from by norm_num, padicValNat.prime_pow]
  calc 2 = rk ↥P := hrkP.symm
    _ ≤ rk ↥Xb := rk_mono hPle

theorem s16k_tri8_rank_four (h : S16gRowCtx D V₀ V L hV)
    (hc : S16kTri8Cfg D V₀ V L hV I₁ I₂ π₁ π₂) {t : MulAut (Vtil V₀ V hV)}
    (htL : t ∈ lBar V₀ V hV L) (ht1 : t ≠ 1) :
    4 ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
  classical
  have hVt : ∀ w : Vtil V₀ V hV, w ^ 2 = 1 := s15_Infra_vtil_sq_eq_one V₀ V hV
  obtain ⟨f₁, hf₁surj, hf₁ker, hf₁eq⟩ :=
    CFSG.Quasithin.G64.exists_natMap
      (Γ := StatedOmega (StatedQuadPlus 4 K₁)) hc.real₁
  obtain ⟨f₂, hf₂surj, hf₂ker, hf₂eq⟩ :=
    CFSG.Quasithin.G64.exists_natMap
      (Γ := StatedOmega (StatedQuadPlus 4 K₂)) hc.real₂
  have hI₁ : ∀ k : ↥(lBar V₀ V hV L), ∀ u ∈ I₁, (k : MulAut (Vtil V₀ V hV)) u ∈ I₁ :=
    hc.real₁.2.2.2.1
  have hI₂ : ∀ k : ↥(lBar V₀ V hV L), ∀ u ∈ I₂, (k : MulAut (Vtil V₀ V hV)) u ∈ I₂ :=
    hc.real₂.2.2.2.1
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : ↥(StatedOmega (StatedQuadPlus 4 K₁)),
      π₁ x₁ = ⟨t, htL⟩ := hc.real₁.1 ⟨t, htL⟩
  have hx₁coe : ((π₁ x₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) = t := by
    rw [hx₁]
  have hx₁ne : x₁ ≠ 1 := by
    intro hx
    apply ht1
    have h1 : ((π₁ x₁ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) = 1 := by
      rw [hx, map_one]; rfl
    rwa [hx₁coe] at h1
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : ↥(StatedOmega (StatedQuadPlus 4 K₂)),
      π₂ x₂ = ⟨t, htL⟩ := hc.real₂.1 ⟨t, htL⟩
  have hx₂coe : ((π₂ x₂ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) = t := by
    rw [hx₂]
  have hx₂ne : x₂ ≠ 1 := by
    intro hx
    apply ht1
    have h1 : ((π₂ x₂ : ↥(lBar V₀ V hV L)) : MulAut (Vtil V₀ V hV)) = 1 := by
      rw [hx, map_one]; rfl
    rwa [hx₂coe] at h1
  obtain ⟨u₁, u₂, hu₁, hu₂, hu₁₂, ⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩⟩ :=
    s16k_statedOmega_moves hc.card₁ hx₁ne
  obtain ⟨u₃, u₄, hu₃, hu₄, hu₃₄, ⟨v₃, hv₃⟩, ⟨v₄, hv₄⟩⟩ :=
    s16k_statedOmega_moves hc.card₂ hx₂ne
  obtain ⟨c₁, c₂, hf₁c₁, hf₁c₂, hc₁X, hc₂X⟩ :=
    s16k_exists_two_comm hf₁surj hf₁eq hI₁ htL hx₁ hu₁ hu₂ hu₁₂ hv₁ hv₂
  obtain ⟨c₃, c₄, hf₂c₃, hf₂c₄, hc₃X, hc₄X⟩ :=
    s16k_exists_two_comm hf₂surj hf₂eq hI₂ htL hx₂ hu₃ hu₄ hu₃₄ hv₃ hv₄
  set Z : Subgroup (Vtil V₀ V hV) := fixV (lBar V₀ V hV L) with hZ
  have hf₁ker' : ∀ u : ↥I₁, f₁ u = 1 ↔ (u : Vtil V₀ V hV) ∈ Z := by
    intro u; rw [hZ]; exact hf₁ker u
  have hf₂ker' : ∀ u : ↥I₂, f₂ u = 1 ↔ (u : Vtil V₀ V hV) ∈ Z := by
    intro u; rw [hZ]; exact hf₂ker u
  set X₁ : Subgroup (Vtil V₀ V hV) :=
    Subgroup.closure ({(c₁ : Vtil V₀ V hV), (c₂ : Vtil V₀ V hV)} : Set (Vtil V₀ V hV))
    with hX₁
  set X₂ : Subgroup (Vtil V₀ V hV) :=
    Subgroup.closure ({(c₃ : Vtil V₀ V hV), (c₄ : Vtil V₀ V hV)} : Set (Vtil V₀ V hV))
    with hX₂
  haveI hZN : Z.Normal := Subgroup.normal_of_comm Z
  set Xb₁ : Subgroup (Vtil V₀ V hV ⧸ Z) := X₁.map (QuotientGroup.mk' Z) with hXb₁
  set Xb₂ : Subgroup (Vtil V₀ V hV ⧸ Z) := X₂.map (QuotientGroup.mk' Z) with hXb₂
  have hX₁I₁ : X₁ ≤ I₁ := by
    rw [hX₁, Subgroup.closure_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact c₁.2
    · exact c₂.2
  have hX₂I₂ : X₂ ≤ I₂ := by
    rw [hX₂, Subgroup.closure_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact c₃.2
    · exact c₄.2
  have hX₁X : X₁ ≤ commSub ⊤ (Subgroup.zpowers t) := by
    rw [hX₁, Subgroup.closure_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hc₁X
    · exact hc₂X
  have hX₂X : X₂ ≤ commSub ⊤ (Subgroup.zpowers t) := by
    rw [hX₂, Subgroup.closure_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hc₃X
    · exact hc₄X
  have hinf : Xb₁ ⊓ Xb₂ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    rw [Subgroup.mem_inf] at hq
    obtain ⟨hq₁, hq₂⟩ := hq
    rw [hXb₁, Subgroup.mem_map] at hq₁
    rw [hXb₂, Subgroup.mem_map] at hq₂
    obtain ⟨y₁, hy₁X₁, hy₁q⟩ := hq₁
    obtain ⟨y₂, hy₂X₂, hy₂q⟩ := hq₂
    have hy₁I₁ : y₁ ∈ I₁ := hX₁I₁ hy₁X₁
    have hy₂I₂ : y₂ ∈ I₂ := hX₂I₂ hy₂X₂
    have hyZ : y₁ * y₂⁻¹ ∈ Z := by
      have hmk : (QuotientGroup.mk' Z) (y₁ * y₂⁻¹) = 1 := by
        rw [map_mul, map_inv, hy₁q, hy₂q, mul_inv_cancel]
      rw [← QuotientGroup.ker_mk' Z]
      exact MonoidHom.mem_ker.mpr hmk
    have hy₁Z : y₁ ∈ Z := by
      refine hc.ind₁ (Subgroup.mem_inf.mpr ⟨hy₁I₁, ?_⟩)
      rw [hZ] at hyZ
      exact Subgroup.mem_sup.mpr ⟨y₁ * y₂⁻¹, hyZ, y₂, hy₂I₂, by group⟩
    have hq1 : (QuotientGroup.mk' Z) y₁ = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff y₁).mpr hy₁Z
    rw [← hy₁q]
    exact hq1
  have h2₁ : 2 ≤ rk ↥(Subgroup.map (QuotientGroup.mk' Z)
      (Subgroup.closure ({(c₁ : Vtil V₀ V hV), (c₂ : Vtil V₀ V hV)} : Set (Vtil V₀ V hV)))) :=
    s16k_two_le_rk_map_closure (Z := Z) hVt hf₁ker' hf₁c₁ hf₁c₂ hu₁ hu₂ hu₁₂
  have h2₂ : 2 ≤ rk ↥(Subgroup.map (QuotientGroup.mk' Z)
      (Subgroup.closure ({(c₃ : Vtil V₀ V hV), (c₄ : Vtil V₀ V hV)} : Set (Vtil V₀ V hV)))) :=
    s16k_two_le_rk_map_closure (Z := Z) hVt hf₂ker' hf₂c₃ hf₂c₄ hu₃ hu₄ hu₃₄
  have h2b₁ : 2 ≤ rk ↥Xb₁ := by rw [hXb₁, hX₁]; exact h2₁
  have h2b₂ : 2 ≤ rk ↥Xb₂ := by rw [hXb₂, hX₂]; exact h2₂
  have hsup : rk ↥(Xb₁ ⊔ Xb₂) = rk ↥Xb₁ + rk ↥Xb₂ := by
    have hh := rk_sup_add_rk_inf Xb₁ Xb₂
    rw [hinf, rk_bot] at hh
    omega
  have h4 : 4 ≤ rk ↥(Xb₁ ⊔ Xb₂) := by rw [hsup]; omega
  have hmap : rk ↥((commSub ⊤ (Subgroup.zpowers t)).map (QuotientGroup.mk' Z)) ≤
      rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
    have hdvd : Nat.card ↥((commSub ⊤ (Subgroup.zpowers t)).map (QuotientGroup.mk' Z)) ∣
        Nat.card ↥(commSub ⊤ (Subgroup.zpowers t)) :=
      Subgroup.card_map_dvd (commSub ⊤ (Subgroup.zpowers t)) (QuotientGroup.mk' Z)
    exact padicValNat_two_le_of_dvd (card_subgroup_pos _).ne' hdvd
  have hle : Xb₁ ⊔ Xb₂ ≤ (commSub ⊤ (Subgroup.zpowers t)).map (QuotientGroup.mk' Z) := by
    rw [hXb₁, hXb₂]
    exact sup_le (Subgroup.map_mono hX₁X) (Subgroup.map_mono hX₂X)
  calc 4 ≤ rk ↥(Xb₁ ⊔ Xb₂) := h4
    _ ≤ rk ↥((commSub ⊤ (Subgroup.zpowers t)).map (QuotientGroup.mk' Z)) := rk_mono hle
    _ ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) := hmap

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
