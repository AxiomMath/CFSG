module

public import CFSG.Quasithin.Background.SmithB42SL3Trace
public import CFSG.Quasithin.Background.SL3SmallCoord
public import CFSG.Quasithin.Background.SL3SmallSect
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBasic
public import CFSG.Quasithin.Background.JonesParshallSL3Perfect
public import CFSG.Quasithin.Background.SmithB42SL3Label

public section

namespace CFSG.Quasithin.SL3Small

open CFSG.QuasithinUnique.Setup.X7a Matrix
open scoped MatrixGroups

section Natural

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {f : ℕ}

omit [Fintype F] in
theorem up3_mul_self : up3 (0 : F) 0 1 * up3 0 0 1 = 1 := by
  rw [up3_mul, ← up3_zero]
  congr 1
  · simp
  · simp
  · exact CharTwo.add_self_eq_zero 1

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

omit [Finite W] in
theorem add_self_zmod_two (w : W) : w + w = 0 := by
  rw [← two_smul (ZMod 2) w, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem two_mul_finrank_range_le {G : Type} [Group G] (ρ : Representation (ZMod 2) G W) {g : G}
    (hg : g * g = 1) :
    2 * Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) ≤ Module.finrank (ZMod 2) W := by
  have hfin : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hsq : ∀ w, (ρ g - 1) ((ρ g - 1) w) = 0 := by
    intro w
    have h1 : ρ g (ρ g w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, hg, map_one, Module.End.one_apply]
    have e : (ρ g - 1) ((ρ g - 1) w) = (w + w) - (ρ g w + ρ g w) := by
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, h1]
      abel
    rw [e, add_self_zmod_two, add_self_zmod_two, sub_zero]
  have hle : LinearMap.range (ρ g - 1) ≤ LinearMap.ker (ρ g - 1) := by
    rintro _ ⟨w, rfl⟩
    exact hsq w
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.finrank_range_add_finrank_ker (ρ g - 1)
  omega

theorem natural_of_irreducible (hF : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (ρ : Representation (ZMod 2) SL(3, F) W) (hirr : ρ.IsIrreducible) (hnt : ∃ x, ρ x ≠ 1)
    (hdim : Module.finrank (ZMod 2) W ≤ 3 * f + 1) :
    ∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧ ∃ E : W ≃+ (Fin 3 → F), ∀ g w,
      E (ρ g w) = ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E w := by
  classical
  have hfin : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  let bas := Module.finBasis (ZMod 2) W
  obtain ⟨a, b, hne, hsum, W₀, ⟨e₀⟩⟩ := B42SL3.exists_label hF (by omega) ρ bas hirr hnt
  have hdim' : ∀ c : (Fin f → Bool) × (Fin f → Bool),
      3 ^ cntS c.1 c.2 * 8 ^ cntH c.1 c.2 ≤
        2 * (tensorRep (F := F) F c.1 c.2 (up3 0 0 1) - 1).rank + 1 :=
    fun c => dim_le_two_mul_rank_tensorRep c.1 c.2
  have hrank := two_mul_finrank_range_le ρ (up3_mul_self (F := F))
  rcases B42SL3.label_cases (by omega) a b hne _ hdim' hsum with ⟨hS, hH⟩ | ⟨-, -, hR⟩ | hR
  · exact B42SL3.exists_natural_of_single hF ρ bas hirr hS hH W₀ e₀
  · omega
  · omega

end Natural

section Sect

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {U U' : Submodule (ZMod 2) V}
  (hinv : ∀ g, ∀ v ∈ U', ρ g v ∈ U') (hUinv : ∀ g, ∀ u ∈ U, ρ g u ∈ U)

@[expose] def resRep : Representation (ZMod 2) G ↥U' :=
  (⟨U', fun g _ hv => hinv g _ hv⟩ : Subrepresentation ρ).toRepresentation

theorem coe_resRep (g : G) (w : ↥U') : ((resRep ρ hinv g w : ↥U') : V) = ρ g w := rfl

@[expose] def sectRep : Representation (ZMod 2) G (↥U' ⧸ U.comap U'.subtype) :=
  (resRep ρ hinv).quotient (U.comap U'.subtype) (fun g w hw => by
    show ((resRep ρ hinv g w : ↥U') : V) ∈ U
    exact hUinv g _ hw)

theorem sectRep_mk (g : G) (w : ↥U') :
    sectRep ρ hinv hUinv g (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (resRep ρ hinv g w) := rfl

theorem sectRep_isIrreducible (hUU' : U < U')
    (hmax : ∀ X : Submodule (ZMod 2) V, U ≤ X → X ≤ U' → (∀ g, ∀ v ∈ X, ρ g v ∈ X) →
      X = U ∨ X = U') : (sectRep ρ hinv hUinv).IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  set U₁ := U.comap U'.subtype with hU₁
  refine ⟨?_, fun X hX => ?_⟩
  · obtain ⟨v, hvU', hvU⟩ := IsConcreteLE.exists_of_lt hUU'
    refine ⟨⟨Submodule.Quotient.mk ⟨v, hvU'⟩, 0, ?_⟩⟩
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hvU
  · set Y := (X.comap U₁.mkQ).map U'.subtype with hY
    have hmemY : ∀ w : ↥U', (w : V) ∈ Y ↔ Submodule.Quotient.mk w ∈ X := by
      intro w
      rw [hY, Submodule.mem_map]
      constructor
      · rintro ⟨w', hw', hww'⟩
        have : w' = w := Subtype.ext hww'
        rw [← this]
        exact hw'
      · intro hw
        exact ⟨w, hw, rfl⟩
    have hUY : U ≤ Y := fun u hu => by
      have hw := (hmemY ⟨u, hUU'.le hu⟩).mpr (by
        rw [(Submodule.Quotient.mk_eq_zero U₁).mpr hu]
        exact X.zero_mem)
      exact hw
    have hYU' : Y ≤ U' := by
      rw [hY]
      exact Submodule.map_subtype_le U' _
    have hYinv : ∀ g, ∀ v ∈ Y, ρ g v ∈ Y := by
      intro g v hv
      have hvU' := hYU' hv
      have h1 := (hmemY ⟨v, hvU'⟩).mp hv
      have h2 := hX g _ h1
      rw [sectRep_mk] at h2
      exact (hmemY (resRep ρ hinv g ⟨v, hvU'⟩)).mpr h2
    rcases hmax Y hUY hYU' hYinv with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      induction x using Submodule.Quotient.induction_on with
      | H w =>
        have h1 := (hmemY w).mpr hx
        rw [h] at h1
        rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
        exact h1
    · right
      rw [eq_top_iff]
      intro x _
      induction x using Submodule.Quotient.induction_on with
      | H w =>
        have h1 : (w : V) ∈ Y := by
          rw [h]
          exact w.2
        exact (hmemY w).mp h1

end Sect

section Split

variable {F : Type} [Field F] [CharP F 2]

@[expose] noncomputable def dk {c : F} (hc : c ≠ 0) (k : Fin 3) : SL(3, F) :=
  ⟨diagonal (fun l => if l = k then (c * c)⁻¹ else c), by
    rw [det_diagonal, Fin.prod_univ_three]
    fin_cases k <;> simp <;> field_simp⟩

omit [CharP F 2] in
theorem dk_coe {c : F} (hc : c ≠ 0) (k : Fin 3) :
    ((dk hc k : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      diagonal (fun l => if l = k then (c * c)⁻¹ else c) := rfl

theorem mul_self_ne_one {c : F} (hc1 : c ≠ 1) : c * c ≠ 1 := by
  intro h
  apply hc1
  have h2 : (c + 1) * (c + 1) = 0 := by
    have : (c + 1) * (c + 1) = c * c + 1 + (c + c) := by ring
    rw [this, h, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
  have h3 := mul_self_eq_zero.mp h2
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h3
  exact h3

theorem dk_mulVec_eq_self {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (k : Fin 3) {x : Fin 3 → F}
    (hx : ((dk hc0 k : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x) : x = 0 := by
  have hcc := mul_self_ne_one hc1
  have hinv1 : (c * c)⁻¹ ≠ 1 := fun h => hcc (inv_eq_one.mp h)
  ext l
  have h1 := congrFun hx l
  rw [dk_coe, mulVec_diagonal] at h1
  have key : ∀ a : F, a ≠ 1 → a * x l = x l → x l = 0 := fun a ha h => by
    have : (a - 1) * x l = 0 := by rw [sub_mul, h, one_mul, sub_self]
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') ha
    · exact h'
  by_cases hl : l = k
  · subst hl
    simp only [↓reduceIte] at h1
    exact key _ hinv1 h1
  · simp only [hl, ↓reduceIte] at h1
    exact key _ hc1 h1

omit [CharP F 2] in
theorem commute_of_diagonal {g h : SL(3, F)} {a b : Fin 3 → F}
    (hg : (g : Matrix (Fin 3) (Fin 3) F) = diagonal a)
    (hh : (h : Matrix (Fin 3) (Fin 3) F) = diagonal b) : g * h = h * g := by
  have h1 : (g : Matrix (Fin 3) (Fin 3) F) * (h : Matrix (Fin 3) (Fin 3) F) =
      (h : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) := by
    rw [hg, hh, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    ext l
    exact mul_comm _ _
  exact Subtype.ext h1

omit [CharP F 2] in
theorem transvection_mul_dk {c : F} (hc0 : c ≠ 0) {i j k : Fin 3} (hij : i ≠ j) (hki : k ≠ i)
    (hkj : k ≠ j) (a : F) :
    SpecialLinearGroup.transvection hij a * dk hc0 k =
      dk hc0 k * SpecialLinearGroup.transvection hij a := by
  have h1 : ((SpecialLinearGroup.transvection hij a : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
      ((dk hc0 k : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      ((dk hc0 k : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
        ((SpecialLinearGroup.transvection hij a : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
    rw [dk_coe, SpecialLinearGroup.transvection_coe]
    ext r t
    rw [mul_diagonal, diagonal_mul]
    by_cases hrt : r = t
    · subst hrt
      ring
    · simp only [Matrix.add_apply, one_apply_ne hrt, zero_add, single_apply]
      by_cases h : i = r ∧ j = t
      · obtain ⟨rfl, rfl⟩ := h
        simp only [and_self, ↓reduceIte, Ne.symm hkj, Ne.symm hki]
        ring
      · simp only [h, ↓reduceIte, zero_mul, mul_zero]
  exact Subtype.ext h1

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_fixed_compl {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (ρ : Representation (ZMod 2) SL(3, F) V) {W : Submodule (ZMod 2) V}
    (hWinv : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (E : ↥W ≃+ (Fin 3 → F))
    (hE : ∀ g (w : ↥W), E ⟨ρ g w, hWinv g w w.2⟩ =
      ((g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E w)
    (hq : ∀ g v, ρ g v - v ∈ W) :
    ∃ C : Submodule (ZMod 2) V, IsCompl W C ∧ ∀ g, ∀ v ∈ C, ρ g v = v := by
  classical
  set Ck : Fin 3 → Submodule (ZMod 2) V := fun k => LinearMap.ker (ρ (dk hc0 k) - 1) with hCk
  have hmemC : ∀ k v, v ∈ Ck k ↔ ρ (dk hc0 k) v = v := fun k v => by
    simp [hCk, sub_eq_zero]
  have hWC : ∀ k, ∀ w ∈ W, ρ (dk hc0 k) w = w → w = 0 := by
    intro k w hw hfix
    have h1 := hE (dk hc0 k) ⟨w, hw⟩
    have h2 : (⟨ρ (dk hc0 k) w, hWinv _ w hw⟩ : ↥W) = ⟨w, hw⟩ := Subtype.ext hfix
    rw [h2] at h1
    have h3 := dk_mulVec_eq_self hc0 hc1 k h1.symm
    have h4 : (⟨w, hw⟩ : ↥W) = 0 := E.injective (by rw [h3, map_zero])
    exact congrArg Subtype.val h4
  have hfixC : ∀ k (g : SL(3, F)), g * dk hc0 k = dk hc0 k * g → ∀ v ∈ Ck k, ρ g v = v := by
    intro k g hg v hv
    rw [hmemC] at hv
    have h1 : ρ (dk hc0 k) (ρ g v) = ρ g v := by
      rw [← Module.End.mul_apply, ← map_mul, ← hg, map_mul, Module.End.mul_apply, hv]
    have h2 : ρ (dk hc0 k) (ρ g v - v) = ρ g v - v := by rw [map_sub, h1, hv]
    exact sub_eq_zero.mp (hWC k _ (hq g v) h2)
  have hdd : ∀ k k', dk hc0 k * dk hc0 k' = dk hc0 k' * dk hc0 k := fun k k' =>
    commute_of_diagonal (dk_coe hc0 k) (dk_coe hc0 k')
  have hCeq : ∀ k, Ck k = Ck 2 := by
    intro k
    apply le_antisymm
    · intro v hv
      rw [hmemC]
      exact hfixC k (dk hc0 2) (hdd 2 k) v hv
    · intro v hv
      rw [hmemC]
      exact hfixC 2 (dk hc0 k) (hdd k 2) v hv
  set C := Ck 2 with hC
  have hcompl : IsCompl W C := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      rintro v ⟨hvW, hvC⟩
      rw [Submodule.mem_bot]
      exact hWC 2 v hvW ((hmemC 2 v).mp hvC)
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      let φ : ↥W → ↥W := fun w => ⟨ρ (dk hc0 2) w - w, hq _ w⟩
      have hφ : Function.Injective φ := by
        intro a b hab
        have e1 : ρ (dk hc0 2) (a : V) - a = ρ (dk hc0 2) b - b := congrArg Subtype.val hab
        have e2 : ρ (dk hc0 2) ((a : V) - b) = (a : V) - b := by
          rw [map_sub]
          calc ρ (dk hc0 2) (a : V) - ρ (dk hc0 2) b
              = (ρ (dk hc0 2) (a : V) - a) - (ρ (dk hc0 2) b - b) + (a - b) := by abel
            _ = (a : V) - b := by rw [e1, sub_self, zero_add]
        exact Subtype.ext (sub_eq_zero.mp (hWC 2 _ (W.sub_mem a.2 b.2) e2))
      obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.mp hφ) ⟨ρ (dk hc0 2) v - v, hq _ v⟩
      have hw' : ρ (dk hc0 2) (w : V) - w = ρ (dk hc0 2) v - v := congrArg Subtype.val hw
      have hvw : v - w ∈ C := by
        rw [hC, hmemC, map_sub]
        calc ρ (dk hc0 2) v - ρ (dk hc0 2) w
            = (ρ (dk hc0 2) v - v) - (ρ (dk hc0 2) (w : V) - w) + (v - w) := by abel
          _ = v - w := by rw [hw', sub_self, zero_add]
      have e : v = (w : V) + (v - w) := by abel
      rw [e]
      exact Submodule.add_mem_sup w.2 hvw
  refine ⟨C, hcompl, fun g => ?_⟩
  refine SpecialLinearGroup.diagonal_transvection_induction' (fun M => ∀ v ∈ C, ρ M v = v) g
    ?_ ?_ ?_
  · intro i j hij a ha v hv
    exact hfixC 2 _ (commute_of_diagonal (SpecialLinearGroup.diag2n_coe hij a ha)
      (dk_coe hc0 2)) v hv
  · intro i j hij a v hv
    obtain ⟨k, hki, hkj⟩ := exists_third hij
    rw [← hCeq k] at hv
    exact hfixC k _ (transvection_mul_dk hc0 hij hki hkj a) v hv
  · intro A B hA hB v hv
    rw [map_mul, Module.End.mul_apply, hB v hv, hA v hv]

end Split

section Proj

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {f : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

omit [CharP F 2] in
theorem exists_ne_zero_ne_one (hF : Fintype.card F = 2 ^ f) (hf : 2 ≤ f) :
    ∃ c : F, c ≠ 0 ∧ c ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun x _ => by
    by_cases hx : x = 0
    · simp [hx]
    · simp [h x hx]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, hF] at h1
  have h2 : (({0, 1} : Finset F)).card ≤ 2 := Finset.card_le_two
  have h3 : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  omega

theorem exists_natural_proj (hF : Fintype.card F = 2 ^ f) (hf : 2 ≤ f)
    (ρ : Representation (ZMod 2) SL(3, F) V) (hdim : Module.finrank (ZMod 2) V ≤ 3 * f + 1)
    (hnt : ∃ g v, ρ g v ≠ v) :
    ∃ ψ : SL(3, F) →* SL(3, F), (∀ g, ψ (ψ g) = g) ∧ ∃ π : V →+ (Fin 3 → F),
      Function.Surjective π ∧ (∀ v, π v = 0 → ∀ g, ρ g v = v) ∧
      ∀ g v, π (ρ g v) = ((ψ g : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ π v := by
  classical
  have hfinV : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one hF hf
  have hc2 : c ^ 2 ≠ 1 := by
    rw [sq]
    exact mul_self_ne_one hc1
  have hG : commutator SL(3, F) = ⊤ := JonesParshall.sl3_commutator_eq_top hc0 hc2
  obtain ⟨U, U', hlt, hinv, hUtriv, hmax, g₀, v₀, hv₀U', hv₀⟩ := exists_section hG hnt
  have hUinv : ∀ g, ∀ u ∈ U, ρ g u ∈ U := fun g u hu => by rw [hUtriv g u hu]; exact hu
  set U₁ := U.comap U'.subtype with hU₁
  set σ := sectRep ρ hinv hUinv with hσ
  have hirr : σ.IsIrreducible := sectRep_isIrreducible ρ hinv hUinv hlt hmax
  have hnt' : ∃ x, σ x ≠ 1 := by
    refine ⟨g₀, fun h1 => hv₀ ?_⟩
    have h2 := congrArg (fun T => T (Submodule.Quotient.mk (⟨v₀, hv₀U'⟩ : ↥U'))) h1
    simp only [Module.End.one_apply] at h2
    rw [hσ, sectRep_mk, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
      Submodule.Quotient.mk_eq_zero] at h2
    exact h2
  have hdim' : Module.finrank (ZMod 2) (↥U' ⧸ U₁) ≤ 3 * f + 1 :=
    (Submodule.finrank_quotient_le _).trans ((Submodule.finrank_le U').trans hdim)
  obtain ⟨ψ, hψ, E, hE⟩ := natural_of_irreducible hF hf σ hirr hnt' hdim'
  refine ⟨ψ, hψ, ?_⟩
  by_cases htop : U' = ⊤
  ·
    let ι : V →+ ↥U' := ((LinearEquiv.ofTop U' htop).symm : V →ₗ[ZMod 2] ↥U').toAddMonoidHom
    have hι : ∀ v, ((ι v : ↥U') : V) = v := fun v => rfl
    refine ⟨E.toAddMonoidHom.comp ((U₁.mkQ).toAddMonoidHom.comp ι), ?_, ?_, ?_⟩
    · intro y
      obtain ⟨x, rfl⟩ := E.surjective y
      induction x using Submodule.Quotient.induction_on with
      | H w =>
        refine ⟨w, ?_⟩
        show E (Submodule.Quotient.mk (ι w)) = E (Submodule.Quotient.mk w)
        congr 2
    · intro v hv g
      have h1 : Submodule.Quotient.mk (ι v) = (0 : ↥U' ⧸ U₁) :=
        E.injective (by rw [map_zero]; exact hv)
      rw [Submodule.Quotient.mk_eq_zero] at h1
      exact hUtriv g v h1
    · intro g v
      show E (Submodule.Quotient.mk (ι (ρ g v))) = _ *ᵥ E (Submodule.Quotient.mk (ι v))
      rw [← hE]
      congr 1
  ·
    have hcV : Nat.card V ≤ 2 ^ (3 * f + 1) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
      exact Nat.pow_le_pow_right (by norm_num) hdim
    have hcS : Nat.card (↥U' ⧸ U₁) = 2 ^ (3 * f) := by
      rw [Nat.card_congr E.toEquiv, Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card (α := F),
        hF, ← pow_mul, mul_comm]
    have hcU' : Nat.card ↥U' = Nat.card ↥U * Nat.card (↥U' ⧸ U₁) := by
      rw [Submodule.card_eq_card_quotient_mul_card U₁,
        Nat.card_congr (Submodule.comapSubtypeEquivOfLe hlt.le).toEquiv]
    have hcVU' := Submodule.card_eq_card_quotient_mul_card U'
    have hq2 : 2 ≤ Nat.card (V ⧸ U') := by
      have : Nontrivial (V ⧸ U') := Submodule.Quotient.nontrivial_iff.mpr htop
      exact Finite.one_lt_card
    have hU1 : 1 ≤ Nat.card ↥U := Nat.card_pos
    have hprod : Nat.card ↥U * Nat.card (V ⧸ U') ≤ 2 := by
      rw [hcVU', hcU', hcS] at hcV
      have h4 : 2 ^ (3 * f + 1) = 2 * 2 ^ (3 * f) := by ring
      rw [h4] at hcV
      have h5 : 0 < 2 ^ (3 * f) := by positivity
      nlinarith
    have hUc : Nat.card ↥U = 1 := by nlinarith
    have hqc : Nat.card (V ⧸ U') = 2 := by nlinarith
    have hUbot : U = ⊥ := by
      have : Subsingleton ↥U := (Nat.card_eq_one_iff_unique.mp hUc).1
      exact Submodule.eq_bot_of_subsingleton
    have hU₁bot : U₁ = ⊥ := by
      rw [hU₁, hUbot, Submodule.comap_bot, Submodule.ker_subtype]
    have hq : ∀ g v, ρ g v - v ∈ U' := by
      intro g v
      by_cases hv : v ∈ U'
      · exact U'.sub_mem (hinv g v hv) hv
      · have hgv : ρ g v ∉ U' := fun h => hv (by
          have := hinv g⁻¹ _ h
          rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply] at this)
        obtain ⟨a, b, hab, hall⟩ := Nat.card_eq_two_iff.mp hqc
        have hmem : ∀ x : V ⧸ U', x = a ∨ x = b := fun x => by
          have : x ∈ ({a, b} : Set (V ⧸ U')) := by rw [hall]; trivial
          simpa using this
        have h0 : ∀ x : V, x ∉ U' → (Submodule.Quotient.mk x : V ⧸ U') ≠ 0 := fun x hx h =>
          hx ((Submodule.Quotient.mk_eq_zero U').mp h)
        have heq : (Submodule.Quotient.mk (ρ g v) : V ⧸ U') = Submodule.Quotient.mk v := by
          rcases hmem 0 with h00 | h00 <;>
            rcases hmem (Submodule.Quotient.mk (ρ g v)) with h1 | h1 <;>
            rcases hmem (Submodule.Quotient.mk v) with h2 | h2
          all_goals first
            | exact h1.trans h2.symm
            | exact absurd (h1.trans h00.symm) (h0 _ hgv)
            | exact absurd (h2.trans h00.symm) (h0 _ hv)
        exact (Submodule.Quotient.eq U').mp heq
    let E' : ↥U' ≃+ (Fin 3 → F) :=
      ((Submodule.quotEquivOfEqBot U₁ hU₁bot).symm.toAddEquiv).trans E
    have hE' : ∀ h (w : ↥U'), E' ⟨ρ (ψ h) w, hinv (ψ h) w w.2⟩ =
        ((h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ E' w := by
      intro h w
      have h1 := hE (ψ h) (Submodule.Quotient.mk w)
      rw [hψ] at h1
      exact h1
    obtain ⟨C, hcompl, hC⟩ := exists_fixed_compl hc0 hc1 (ρ.comp ψ)
      (fun h w hw => hinv (ψ h) w hw) E' hE' (fun h v => hq (ψ h) v)
    have hCfix : ∀ g, ∀ v ∈ C, ρ g v = v := fun g v hv => by
      have := hC (ψ g) v hv
      rwa [MonoidHom.comp_apply, hψ] at this
    have hCinv : ∀ g, ∀ v ∈ C, ρ g v ∈ C := fun g v hv => by rw [hCfix g v hv]; exact hv
    set P := Submodule.projectionOnto U' C hcompl with hP
    have hPsub : ∀ v, v - (P v : V) ∈ C := fun v => by
      have : P (v - (P v : V)) = 0 := by
        rw [map_sub, Submodule.projectionOnto_apply_left hcompl, sub_self]
      exact (Submodule.projectionOnto_apply_eq_zero_iff hcompl).mp this
    have hPeq : ∀ g v, P (ρ g v) = ⟨ρ g (P v), hinv g _ (P v).2⟩ := by
      intro g v
      have e : ρ g v = ρ g (P v) + ρ g (v - (P v : V)) := by rw [← map_add, add_sub_cancel]
      rw [e, map_add, (Submodule.projectionOnto_apply_eq_zero_iff hcompl).mpr
        (hCinv g _ (hPsub v)), add_zero]
      exact Submodule.projectionOnto_apply_left hcompl ⟨ρ g (P v), hinv g _ (P v).2⟩
    refine ⟨E'.toAddMonoidHom.comp P.toAddMonoidHom, ?_, ?_, ?_⟩
    · intro y
      obtain ⟨w, rfl⟩ := E'.surjective y
      exact ⟨w, by
        show E' (P w) = E' w
        rw [Submodule.projectionOnto_apply_left hcompl]⟩
    · intro v hv g
      have h1 : P v = 0 := E'.injective (by rw [map_zero]; exact hv)
      have h2 : v ∈ C := (Submodule.projectionOnto_apply_eq_zero_iff hcompl).mp h1
      exact hCfix g v h2
    · intro g v
      show E' (P (ρ g v)) = _ *ᵥ E' (P v)
      rw [hPeq]
      have h1 := hE' (ψ g) (P v)
      rw [hψ] at h1
      exact h1

end Proj

end CFSG.Quasithin.SL3Small
