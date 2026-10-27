module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2PSet

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Pair

open Subgroup CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.QuasithinUnique.Setup.X7b
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Norm
open CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac
open CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Br
open CFSG.RankThree.GF2n.Tim81.Sec2 (IsOrthModule)
open scoped MatrixGroups

section Irr

variable {K X₁ X₂ Y : Type} [Group K] [AddCommGroup X₁] [Module (ZMod 2) X₁] [AddCommGroup X₂]
  [Module (ZMod 2) X₂] [AddCommGroup Y] [Module (ZMod 2) Y]

theorem isIrreducible_of_equiv {σ₁ : Representation (ZMod 2) K X₁}
    {σ₂ : Representation (ZMod 2) K X₂} (h : σ₁.IsIrreducible) (f : X₂ ≃ₗ[ZMod 2] X₁)
    (hf : ∀ g x, f (σ₂ g x) = σ₁ g (f x)) : σ₂.IsIrreducible := by
  obtain ⟨hnt, hU⟩ := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff σ₁).mp h
  refine (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff σ₂).mpr
    ⟨f.toEquiv.nontrivial, fun U hU' => ?_⟩
  have hinv : ∀ g, ∀ u ∈ U.map (f : X₂ →ₗ[ZMod 2] X₁),
      σ₁ g u ∈ U.map (f : X₂ →ₗ[ZMod 2] X₁) := by
    rintro g _ ⟨u, hu, rfl⟩
    exact ⟨σ₂ g u, hU' g u hu, hf g u⟩
  have hc := Submodule.comap_map_eq_of_injective (f := (f : X₂ →ₗ[ZMod 2] X₁)) f.injective U
  rcases hU _ hinv with h0 | h0
  · left
    rw [← hc, h0]
    simp
  · right
    rw [← hc, h0]
    simp

theorem eq_bot_or_eq_of_isIrreducible {U D : Submodule (ZMod 2) Y}
    (τ : Representation (ZMod 2) K ↥U) (hirr : τ.IsIrreducible) (hDU : D ≤ U)
    (hD : ∀ k (u : ↥U), (u : Y) ∈ D → (τ k u : Y) ∈ D) : D = ⊥ ∨ D = U := by
  have hD' : (D.comap U.subtype).map U.subtype = D := by
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr hDU
  rcases ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff τ).mp hirr).2 (D.comap U.subtype)
      (fun k u hu => hD k u hu) with h | h
  · left
    rw [← hD', h, Submodule.map_bot]
  · right
    rw [← hD', h, Submodule.map_subtype_top]

theorem eq_or_isCompl {P : Submodule (ZMod 2) Y → Prop}
    (hinf : ∀ A B, P A → P B → P (A ⊓ B)) (hsup : ∀ A B, P A → P B → P (A ⊔ B))
    {U C D : Submodule (ZMod 2) Y} (hUC : IsCompl U C) (hPU : P U) (hPC : P C)
    (hU : ∀ E ≤ U, P E → E = ⊥ ∨ E = U) (hC : ∀ E ≤ C, P E → E = ⊥ ∨ E = C) (hPD : P D)
    (hD0 : D ≠ ⊥) (hD1 : D ≠ ⊤) : D = U ∨ IsCompl U D := by
  by_cases hDU : D ⊓ U = ⊥
  · right
    refine IsCompl.of_eq (by rw [inf_comm]; exact hDU) ?_
    rcases hC ((U ⊔ D) ⊓ C) inf_le_right (hinf _ _ (hsup _ _ hPU hPD) hPC) with h | h
    · exfalso
      have h1 := sup_inf_assoc_of_le C (le_sup_left : U ≤ U ⊔ D)
      rw [hUC.sup_eq_top, top_inf_eq, inf_comm, h, sup_bot_eq] at h1
      apply hD0
      rw [eq_bot_iff, ← hDU]
      exact le_inf le_rfl (le_sup_right.trans h1.le)
    · rw [eq_top_iff, ← hUC.sup_eq_top]
      exact sup_le le_sup_left (h.ge.trans inf_le_left)
  · rcases hU (D ⊓ U) inf_le_right (hinf _ _ hPD hPU) with h | h
    · exact absurd h hDU
    · have hUD : U ≤ D := h.ge.trans inf_le_left
      rcases hC (D ⊓ C) inf_le_right (hinf _ _ hPD hPC) with h' | h'
      · left
        have h1 := sup_inf_assoc_of_le C hUD
        rw [hUC.sup_eq_top, top_inf_eq, inf_comm, h', sup_bot_eq] at h1
        exact h1
      · exfalso
        apply hD1
        rw [eq_top_iff, ← hUC.sup_eq_top]
        exact sup_le hUD (h'.ge.trans inf_le_left)

end Irr

section Abs

variable {H : Type} [Group H] {L : Subgroup H} [hL : L.Normal] {t : H} {F : Type} [Field F]
  [Fintype F] [CharP F 2]

theorem disp_or_orth_irr {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y] [Finite Y]
    (ht : t * t = 1) (e : ↥L ≃* SL(2, F)) {n : ℕ} (hn : 3 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (hl₀ : ∃ l ∈ L, t * l ≠ l * t) (σ : Representation (ZMod 2) ↥(L ⊔ zpowers t) Y)
    (hirr : σ.IsIrreducible) (hNT : NoTrivSec (σ.comp (incL L t))) :
    n + 3 ≤ 2 * (Module.finrank (ZMod 2) Y -
        Module.finrank (ZMod 2) (repFixedSpace σ {tElt L t})) ∨
      ∃ s, n = 2 * s ∧
        Module.finrank (ZMod 2) Y - Module.finrank (ZMod 2) (repFixedSpace σ {tElt L t}) = s ∧
        Representation.IsIrreducible (σ.comp (incL L t)) ∧
        ∃ hs : Fintype.card F = 2 ^ (2 * s),
          IsOrthModule hs ((σ.comp (incL L t)).comp e.symm.toMonoidHom) := by
  rcases irreducible_or_split σ hirr (incL L t) (tElt L t) (Subtype.ext ht)
      (exists_incL_mul_tElt L t) (fun U hU hUt => invariant_of_incL_tElt L t ht σ U hU hUt) with
    hL' | ⟨Y₀, hY₀, hY₀0, hY₀d⟩
  · obtain ⟨hX, hnt, h | ⟨s, hs, hd, hs', ho⟩ | ⟨s, hs, hd⟩⟩ :=
      trichotomy_incL ht e hn hF hl₀ σ hL' hNT
    · have := two_mul_le_finrank (by omega) hF _ hX hnt
      left
      omega
    · exact Or.inr ⟨s, hs, hd, hL', hs', ho⟩
    · left
      omega
  · have := two_mul_le_finrank_of_invariant e (by omega) hF (σ.comp (incL L t)) hNT hY₀ hY₀0
    left
    omega

theorem nat_or_orth_or_eight_or_split {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y] [Finite Y]
    (σ : Representation (ZMod 2) H Y) (hirr : σ.IsIrreducible) (e : ↥L ≃* SL(2, F)) {n : ℕ}
    (hn : 3 ≤ n) (hF : Fintype.card F = 2 ^ n) (hnt : ∃ l ∈ L, σ l ≠ 1) (ht : t * t = 1)
    (hl₀ : ∃ l ∈ L, t * l ≠ l * t)
    (hδ : Module.finrank (ZMod 2) Y - Module.finrank (ZMod 2) (repFixedSpace σ {t}) ≤ n + 1) :
    (Representation.IsIrreducible (σ.comp L.subtype) ∧
      (IsNaturalModule ((σ.comp L.subtype).comp e.symm.toMonoidHom) ∨
        (∃ s, n = 2 * s ∧ ∃ hs : Fintype.card F = 2 ^ (2 * s),
          IsOrthModule hs ((σ.comp L.subtype).comp e.symm.toMonoidHom)) ∨
        (n = 3 ∧ Module.finrank (ZMod 2) Y = 8))) ∨
    ∃ s, n = 2 * s ∧ ∃ hs : Fintype.card F = 2 ^ (2 * s),
      (∀ D (hD : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant σ L D), D ≠ ⊥ → D ≠ ⊤ →
        (restr σ hD).IsIrreducible ∧ IsOrthModule hs ((restr σ hD).comp e.symm.toMonoidHom)) ∧
      ∃ U C : Submodule (ZMod 2) Y, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant σ L U ∧ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant σ L C ∧ IsCompl U C ∧
        U ≠ ⊥ ∧ C ≠ ⊥ := by
  have hNTL := noTrivSec_of_normal σ hirr hL hnt
  let π : Representation (ZMod 2) ↥(L ⊔ zpowers t) Y := σ.comp (L ⊔ zpowers t).subtype
  have hπL : π.comp (incL L t) = σ.comp L.subtype := MonoidHom.ext fun _ => rfl
  have hNT : NoTrivSec (π.comp (incL L t)) := by
    rw [hπL]
    exact hNTL
  have hfix : repFixedSpace π {tElt L t} = repFixedSpace σ {t} :=
    repFixedSpace_comp_subtype σ _ _
  have hδ' : Module.finrank (ZMod 2) Y - Module.finrank (ZMod 2) (repFixedSpace π {tElt L t}) ≤
      n + 1 := by
    rw [hfix]
    exact hδ
  by_cases hπ : π.IsIrreducible
  ·
    left
    rcases irreducible_or_split π hπ (incL L t) (tElt L t) (Subtype.ext ht)
        (exists_incL_mul_tElt L t) (fun U hU hUt => invariant_of_incL_tElt L t ht π U hU hUt) with
      hLi | ⟨Y₀, hY₀, hY₀0, hY₀d⟩
    · obtain ⟨hX, hnt', h | ⟨s, hs, -, hs', ho⟩ | ⟨s, hs, hd⟩⟩ :=
        trichotomy_incL ht e hn hF hl₀ π hLi hNT
      · rw [hπL] at hLi hX hnt'
        refine ⟨hLi, ?_⟩
        rcases nat_or_orth_or_eight hn hF _ hX hnt' (by omega) with
          hnat | ⟨l, hl, hnl, ho⟩ | h8
        · exact Or.inl hnat
        · exact Or.inr (Or.inl ⟨l, hnl, hl, ho⟩)
        · exact Or.inr (Or.inr h8)
      · rw [hπL] at hLi ho
        exact ⟨hLi, Or.inr (Or.inl ⟨s, hs, hs', ho⟩)⟩
      · omega
    · have := two_mul_le_finrank_of_invariant e (by omega) hF (π.comp (incL L t)) hNT hY₀ hY₀0
      omega
  ·
    right
    have hVnt : Nontrivial Y := ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff σ).mp hirr).1
    obtain ⟨U, hU, hU0, hUt⟩ : ∃ U : Submodule (ZMod 2) Y, (∀ h, ∀ u ∈ U, π h u ∈ U) ∧
        U ≠ ⊥ ∧ U ≠ ⊤ := by
      by_contra hc
      push Not at hc
      exact hπ ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff π).mpr
        ⟨hVnt, fun U hU => or_iff_not_imp_left.mpr (hc U hU)⟩)
    obtain ⟨U', hU'U, hU'⟩ := exists_irreducible_sub π hU hU0
    have hU'top : U'.toSubmodule ≠ ⊤ := fun h => hUt (top_le_iff.mp (by rw [← h]; exact hU'U))
    haveI : Nontrivial U'.toSubmodule :=
      ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff _).mp hU').1
    haveI : Finite (Y ⧸ U'.toSubmodule) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
    haveI : Nontrivial (Y ⧸ U'.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hU'top
    have hNTU := NoTrivSec.sub hNT U'
    have hNTQ := NoTrivSec.quot hNT U'
    have hcod := codim_sub_quot π U' {tElt L t}
    have hlow : ∀ {Y' : Type} [AddCommGroup Y'] [Module (ZMod 2) Y'] [Finite Y']
        (τ : Representation (ZMod 2) ↥(L ⊔ zpowers t) Y'), τ.IsIrreducible →
          NoTrivSec (τ.comp (incL L t)) → n ≤ 2 * (Module.finrank (ZMod 2) Y' -
            Module.finrank (ZMod 2) (repFixedSpace τ {tElt L t})) := by
      intro Y' _ _ _ τ hτ hτNT
      rcases disp_or_orth ht e hn hF hl₀ τ hτ hτNT with h | ⟨s, hs, hd, -⟩ <;> omega
    have hQ := le_disp_of_forall_irreducible (incL L t) (tElt L t) hlow U'.quotient hNTQ
    obtain hU1 | ⟨s, hs, hdU, hUL, hsF, hoU⟩ :=
      disp_or_orth_irr ht e hn hF hl₀ U'.toRepresentation hU' hNTU
    · omega
    have hQirr := isIrreducible_of_disp_lt (incL L t) (tElt L t) hlow U'.quotient hNTQ
      (by omega)
    obtain hQ1 | ⟨s', hs', -, hQL, hsF', hoQ⟩ :=
      disp_or_orth_irr ht e hn hF hl₀ U'.quotient hQirr hNTQ
    · omega
    obtain rfl : s = s' := by omega
    obtain ⟨C, hC, hcompl⟩ := exists_isCompl_of_normal σ hirr hL (N := U'.toSubmodule)
      (fun l hl v hv => U'.apply_mem_toSubmodule (incL L t ⟨l, hl⟩) hv)
    have hUinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant σ L U'.toSubmodule :=
      fun l hl v hv => U'.apply_mem_toSubmodule (incL L t ⟨l, hl⟩) hv
    have hUirr : (restr σ hUinv).IsIrreducible :=
      isIrreducible_of_equiv hUL (LinearEquiv.refl _ _) fun _ _ => rfl
    have hCirr : (restr σ hC).IsIrreducible := isIrreducible_of_equiv hQL
      (Submodule.quotientEquivOfIsCompl _ _ hcompl).symm fun _ _ => rfl
    have hinf : ∀ A B : Submodule (ZMod 2) Y, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant σ L A → CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant σ L B →
        CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant σ L (A ⊓ B) := fun A B hA hB l hl v hv => ⟨hA l hl v hv.1, hB l hl v hv.2⟩
    have hsup : ∀ A B : Submodule (ZMod 2) Y, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant σ L A → CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant σ L B →
        CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant σ L (A ⊔ B) := fun A B hA hB l hl v hv => by
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add]
      exact Submodule.add_mem_sup (hA l hl a ha) (hB l hl b hb)
    refine ⟨s, hs, hsF, fun D hD hD0 hD1 => ?_, U'.toSubmodule, C, hUinv, hC, hcompl,
      Submodule.nontrivial_iff_ne_bot.mp inferInstance,
      fun h0 => hU'top (by simpa [h0] using hcompl.sup_eq_top)⟩
    rcases eq_or_isCompl hinf hsup hcompl hUinv hC
        (fun E hEU hE => eq_bot_or_eq_of_isIrreducible _ hUirr hEU fun k u hu => hE k k.2 u hu)
        (fun E hEC hE => eq_bot_or_eq_of_isIrreducible _ hCirr hEC fun k u hu => hE k k.2 u hu)
        hD hD0 hD1 with rfl | hUD
    · exact ⟨hUirr, isOrthModule_of_equiv hoU (AddEquiv.refl _) fun _ _ => rfl⟩
    · let f := (Submodule.quotientEquivOfIsCompl _ _ hUD).symm
      exact ⟨isIrreducible_of_equiv hQL f fun _ _ => rfl,
        isOrthModule_of_equiv hoQ f.toAddEquiv fun _ _ => rfl⟩

end Abs

section Sub

variable {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {H L : Subgroup G} {A : Submodule (ZMod 2) V}
  (hA : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ H A)

theorem isInvariant_map_subtype (hLH : L ≤ H) {U : Submodule (ZMod 2) ↥A}
    (hU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (restr ρ hA) (L.subgroupOf H) U) : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L (U.map A.subtype) := by
  rintro l hl _ ⟨u, hu, rfl⟩
  exact ⟨_, hU ⟨l, hLH hl⟩ hl u hu, rfl⟩

theorem exists_equiv_map_subtype (hLH : L ≤ H) {U : Submodule (ZMod 2) ↥A}
    (hU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (restr ρ hA) (L.subgroupOf H) U) :
    ∃ f : ↥(U.map A.subtype) ≃ₗ[ZMod 2] ↥U, ∀ (l : ↥L) x,
      f (restr ρ (isInvariant_map_subtype ρ hA hLH hU) l x) =
        restr (restr ρ hA) hU ((subgroupOfEquivOfLe hLH).symm l) (f x) := by
  let φ := Submodule.equivMapOfInjective A.subtype A.injective_subtype U
  refine ⟨φ.symm, fun l x => φ.injective ?_⟩
  rw [φ.apply_symm_apply]
  apply Subtype.ext
  have hx : (((φ.symm x : ↥U) : ↥A) : V) = x :=
    Submodule.map_equivMapOfInjective_symm_apply A.subtype A.injective_subtype U x
  show ρ l x = ρ l (((φ.symm x : ↥U) : ↥A) : V)
  rw [hx]

theorem eq_bot_or_eq_map_subtype (hLH : L ≤ H) {U : Submodule (ZMod 2) ↥A}
    (hU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (restr ρ hA) (L.subgroupOf H) U)
    (hirr : (restr (restr ρ hA) hU).IsIrreducible) {D : Submodule (ZMod 2) V}
    (hDU : D ≤ U.map A.subtype) (hD : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L D) : D = ⊥ ∨ D = U.map A.subtype := by
  obtain ⟨f, hf⟩ := exists_equiv_map_subtype ρ hA hLH hU
  exact eq_bot_or_eq_of_isIrreducible _ (isIrreducible_of_equiv
    (isIrreducible_comp_equiv _ (subgroupOfEquivOfLe hLH).symm hirr) f hf) hDU
    fun l u hu => hD l l.2 u hu

theorem isOrthModule_of_map_eq (hLH : L ≤ H) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (e : ↥L ≃* SL(2, F)) {s : ℕ} {hs : Fintype.card F = 2 ^ (2 * s)}
    {U : Submodule (ZMod 2) ↥A} (hU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (restr ρ hA) (L.subgroupOf H) U)
    {D : Submodule (ZMod 2) V} (hUD : U.map A.subtype = D) (hD : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L D)
    (ho : IsOrthModule hs ((restr (restr ρ hA) hU).comp
      ((subgroupOfEquivOfLe hLH).trans e).symm.toMonoidHom)) :
    IsOrthModule hs ((restr ρ hD).comp e.symm.toMonoidHom) := by
  subst hUD
  obtain ⟨f, hf⟩ := exists_equiv_map_subtype ρ hA hLH hU
  exact isOrthModule_of_equiv ho f.toAddEquiv fun g x => hf (e.symm g) x

theorem nat_or_orth_or_eight_or_split_sub [Finite V] (hLH : L ≤ H)
    (hHN : H ≤ normalizer (L : Set G)) (hmin : IsMinInv ρ H A) (hAL : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L A)
    (hmov : ∃ l ∈ L, ∃ a ∈ A, ρ l a ≠ a) {F : Type} [Field F] [Fintype F] [CharP F 2]
    (e : ↥L ≃* SL(2, F)) {n : ℕ} (hn : 3 ≤ n) (hF : Fintype.card F = 2 ^ n) {t : G}
    (htH : t ∈ H) (ht : t * t = 1) (hl₀ : ∃ l ∈ L, t * l ≠ l * t)
    (hδ : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (repFixedSpace ρ {t}) ≤ n + 1) :
    ((∀ C ≤ A, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L C → C = ⊥ ∨ C = A) ∧
      (IsNaturalModule ((restr ρ hAL).comp e.symm.toMonoidHom) ∨
        (∃ s, n = 2 * s ∧ ∃ hs : Fintype.card F = 2 ^ (2 * s),
          IsOrthModule hs ((restr ρ hAL).comp e.symm.toMonoidHom)) ∨
        (n = 3 ∧ Module.finrank (ZMod 2) A = 8))) ∨
    ∃ s, n = 2 * s ∧ ∃ hs : Fintype.card F = 2 ^ (2 * s),
      (∀ D ≤ A, ∀ hD : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L D, D ≠ ⊥ → D ≠ A →
        (∀ E ≤ D, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L E → E = ⊥ ∨ E = D) ∧
          IsOrthModule hs ((restr ρ hD).comp e.symm.toMonoidHom)) ∧
      ∃ U C : Submodule (ZMod 2) V, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L U ∧ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L C ∧ U ⊔ C = A ∧
        U ⊓ C = ⊥ ∧ U ≠ ⊥ ∧ C ≠ ⊥ := by
  obtain ⟨hA, hA0, hAmin⟩ := hmin
  haveI : (L.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hLH).mpr hHN
  let σ : Representation (ZMod 2) ↥H ↥A := restr ρ hA
  let t' : ↥H := ⟨t, htH⟩
  have hirr : σ.IsIrreducible := by
    refine (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff σ).mpr
      ⟨Submodule.nontrivial_iff_ne_bot.mpr hA0, fun U hU => ?_⟩
    by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    · right
      have hUA : U.map A.subtype = A := hAmin _ (Submodule.map_subtype_le A U)
        (by rintro h hh _ ⟨u, hu, rfl⟩; exact ⟨_, hU ⟨h, hh⟩ u hu, rfl⟩)
        (fun h0 => hU0 (Submodule.map_injective_of_injective A.injective_subtype
          (h0.trans (Submodule.map_bot _).symm)))
      exact Submodule.map_injective_of_injective A.injective_subtype
        (hUA.trans (Submodule.map_subtype_top A).symm)
  have hnt : ∃ l ∈ L.subgroupOf H, σ l ≠ 1 := by
    obtain ⟨l, hl, a, ha, hne⟩ := hmov
    exact ⟨⟨l, hLH hl⟩, hl, fun h => hne (congrArg Subtype.val (LinearMap.congr_fun h ⟨a, ha⟩))⟩
  have ht' : t' * t' = 1 := Subtype.ext ht
  have hl₀' : ∃ l ∈ L.subgroupOf H, t' * l ≠ l * t' := by
    obtain ⟨l, hl, hne⟩ := hl₀
    exact ⟨⟨l, hLH hl⟩, hl, fun h => hne (congrArg Subtype.val h)⟩
  have hδ' : Module.finrank (ZMod 2) A - Module.finrank (ZMod 2) (repFixedSpace σ {t'}) ≤
      n + 1 := by
    have h1 : Module.finrank (ZMod 2) A - Module.finrank (ZMod 2) (repFixedSpace σ {t'}) ≤
        Module.finrank (ZMod 2) V -
          Module.finrank (ZMod 2) (repFixedSpace (ρ.comp H.subtype) {t'}) :=
      le_trans (Nat.le_add_right _ _)
        (codim_sub_quot (ρ.comp H.subtype) ⟨A, fun h _ hv => hA h h.2 _ hv⟩ {t'})
    have h2 : repFixedSpace (ρ.comp H.subtype) {t'} = repFixedSpace ρ {t} :=
      repFixedSpace_comp_subtype ρ H t'
    rw [h2] at h1
    omega
  rcases nat_or_orth_or_eight_or_split σ hirr ((subgroupOfEquivOfLe hLH).trans e) hn hF hnt ht'
      hl₀' hδ' with
    ⟨hLirr, hcase⟩ | ⟨s, hs, hsF, hall, U, C, hU, hC, hcompl, hU0, hC0⟩
  · left
    refine ⟨fun D hDA hD => eq_bot_or_eq_of_isIrreducible
      ((σ.comp (L.subgroupOf H).subtype).comp (subgroupOfEquivOfLe hLH).symm.toMonoidHom)
      (isIrreducible_comp_equiv _ _ hLirr) hDA fun l u hu => hD l l.2 u hu, ?_⟩
    rcases hcase with hnat | ⟨s, hs, hsF, ho⟩ | h8
    · exact Or.inl (isNaturalModule_of_equiv hnat (AddEquiv.refl _) fun _ _ => rfl)
    · exact Or.inr (Or.inl ⟨s, hs, hsF,
        isOrthModule_of_equiv ho (AddEquiv.refl _) fun _ _ => rfl⟩)
    · exact Or.inr (Or.inr h8)
  · right
    have hinj := Submodule.map_injective_of_injective A.injective_subtype
    refine ⟨s, hs, hsF, fun D hDA hD hD0 hD1 => ?_, U.map A.subtype, C.map A.subtype,
      isInvariant_map_subtype ρ hA hLH hU, isInvariant_map_subtype ρ hA hLH hC, ?_, ?_,
      fun h => hU0 (hinj (h.trans (Submodule.map_bot _).symm)),
      fun h => hC0 (hinj (h.trans (Submodule.map_bot _).symm))⟩
    · have hD' : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant σ (L.subgroupOf H) (D.comap A.subtype) :=
        fun k hk x hx => hD k hk x hx
      have heq : (D.comap A.subtype).map A.subtype = D := by
        rw [Submodule.map_comap_subtype]
        exact inf_eq_right.mpr hDA
      obtain ⟨hirrD, hoD⟩ := hall _ hD' (fun h => hD0 (by rw [← heq, h, Submodule.map_bot]))
        (fun h => hD1 (by rw [← heq, h, Submodule.map_subtype_top]))
      refine ⟨fun E hED hE => ?_, isOrthModule_of_map_eq ρ hA hLH e hD' heq hD hoD⟩
      have := eq_bot_or_eq_map_subtype ρ hA hLH hD' hirrD (hED.trans heq.ge) hE
      rwa [heq] at this
    · rw [← Submodule.map_sup, hcompl.sup_eq_top, Submodule.map_subtype_top]
    · rw [← Submodule.map_inf _ A.injective_subtype, hcompl.inf_eq_bot, Submodule.map_bot]

end Sub

end CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Pair
