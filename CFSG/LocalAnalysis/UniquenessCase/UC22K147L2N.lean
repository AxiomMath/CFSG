module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2Disp
public import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2Fac
public import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2Br
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22finA
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Norm

open Subgroup CFSG.QuasithinUnique.Setup.X7b CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac
open scoped MatrixGroups

section Rep

variable {H X : Type} [Group H] [AddCommGroup X] [Module (ZMod 2) X]

theorem ker_sub_one_eq_repFixedSpace (σ : Representation (ZMod 2) H X) (h : H) :
    LinearMap.ker (σ h - 1) = repFixedSpace σ {h} := by
  ext v
  simp [mem_repFixedSpace, sub_eq_zero]

theorem repFixedSpace_comp_subtype {G : Type} [Group G] (ρ : Representation (ZMod 2) G X)
    (K : Subgroup G) (h : ↥K) :
    repFixedSpace (ρ.comp K.subtype) {h} = repFixedSpace ρ {(h : G)} := by
  ext v
  simp [mem_repFixedSpace]

theorem isIrreducible_comp_equiv {K : Type} [Group K] (σ : Representation (ZMod 2) H X)
    (f : K ≃* H) (h : σ.IsIrreducible) : Representation.IsIrreducible (σ.comp f.toMonoidHom) := by
  obtain ⟨hnt, hU⟩ := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff σ).mp h
  refine (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff _).mpr
    ⟨hnt, fun U hU' => hU U fun g u hu => ?_⟩
  simpa using hU' (f.symm g) u hu

end Rep

section SL2

variable {K X : Type} [Group K] [AddCommGroup X] [Module (ZMod 2) X] {F : Type} [Field F]

theorem NoTrivSec.exists_ne_one [Nontrivial X] {σ : Representation (ZMod 2) K X}
    (h : NoTrivSec σ) (e : K ≃* SL(2, F)) : ∃ g, σ.comp e.symm.toMonoidHom g ≠ 1 := by
  obtain ⟨k, y, -, hy⟩ := h.exists_ne (Y := ⊤) top_ne_bot
  refine ⟨e k, fun h1 => hy ?_⟩
  simpa using LinearMap.congr_fun h1 y

theorem NoTrivSec.injective [Nontrivial X] [Finite F] [CharP F 2]
    {σ : Representation (ZMod 2) K X} (h : NoTrivSec σ) (h4 : 4 ≤ Nat.card F)
    (e : K ≃* SL(2, F)) : Function.Injective (σ.comp e.symm.toMonoidHom) := by
  haveI := CFSG.LocalAnalysis.UniquenessCase.UC22.P22y.isSimpleGroup_sl2 h4
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (σ.comp e.symm.toMonoidHom).ker with h0 | h0
  · exact (MonoidHom.ker_eq_bot_iff _).mp h0
  · obtain ⟨g, hg⟩ := h.exists_ne_one e
    have hg' : g ∈ (σ.comp e.symm.toMonoidHom).ker := by
      rw [h0]
      exact mem_top g
    exact absurd (MonoidHom.mem_ker.mp hg') hg

theorem two_mul_le_finrank_of_invariant [Finite X] [Fintype F] [CharP F 2] (e : K ≃* SL(2, F))
    {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n) (σ : Representation (ZMod 2) K X)
    (h : NoTrivSec σ) {Y : Submodule (ZMod 2) X} (hY : ∀ k, ∀ y ∈ Y, σ k y ∈ Y) (hY0 : Y ≠ ⊥) :
    2 * n ≤ Module.finrank (ZMod 2) Y := by
  obtain ⟨U, hUY, hU⟩ := exists_irreducible_sub σ hY hY0
  have hNT : NoTrivSec (U.toRepresentation.comp (MonoidHom.id K)) :=
    NoTrivSec.sub (ι := MonoidHom.id K) (by rwa [MonoidHom.comp_id]) U
  rw [MonoidHom.comp_id] at hNT
  haveI : Nontrivial U.toSubmodule :=
    ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff _).mp hU).1
  exact (two_mul_le_finrank hn hF _ (isIrreducible_comp_equiv _ e.symm hU)
    (hNT.exists_ne_one e)).trans (Submodule.finrank_mono hUY)

end SL2

section LT

variable {G : Type} [Group G] {L : Subgroup G} [hL : L.Normal] {t : G} {F : Type} [Field F]
  [Fintype F] [CharP F 2] {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y] [Finite Y]

theorem trichotomy_incL (ht : t * t = 1) (e : ↥L ≃* SL(2, F)) {n : ℕ} (hn : 3 ≤ n)
    (hF : Fintype.card F = 2 ^ n) (hl₀ : ∃ l ∈ L, t * l ≠ l * t)
    (σ : Representation (ZMod 2) ↥(L ⊔ zpowers t) Y)
    (hirr : Representation.IsIrreducible (σ.comp (incL L t)))
    (hNT : NoTrivSec (σ.comp (incL L t))) :
    Representation.IsIrreducible ((σ.comp (incL L t)).comp e.symm.toMonoidHom) ∧
      (∃ g, (σ.comp (incL L t)).comp e.symm.toMonoidHom g ≠ 1) ∧
      (Module.finrank (ZMod 2) Y ≤ 2 * (Module.finrank (ZMod 2) Y -
          Module.finrank (ZMod 2) (repFixedSpace σ {tElt L t})) ∨
        (∃ s, n = 2 * s ∧
          Module.finrank (ZMod 2) Y - Module.finrank (ZMod 2) (repFixedSpace σ {tElt L t}) = s ∧
          ∃ hs : Fintype.card F = 2 ^ (2 * s), CFSG.RankThree.GF2n.Tim81.Sec2.IsOrthModule hs
            ((σ.comp (incL L t)).comp e.symm.toMonoidHom)) ∨
        (∃ s, n = 2 * s ∧ 3 * s ≤
          Module.finrank (ZMod 2) Y - Module.finrank (ZMod 2) (repFixedSpace σ {tElt L t}))) := by
  haveI : Nontrivial Y := ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff _).mp hirr).1
  have h4 : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hX := isIrreducible_comp_equiv _ e.symm hirr
  refine ⟨hX, hNT.exists_ne_one e, ?_⟩
  let τ : SL(2, F) → SL(2, F) := fun g =>
    e ⟨t * ((e.symm g : ↥L) : G) * t⁻¹, hL.conj_mem _ (e.symm g).2 t⟩
  have hτ : ∀ g, σ (tElt L t) * (σ.comp (incL L t)).comp e.symm.toMonoidHom g =
      (σ.comp (incL L t)).comp e.symm.toMonoidHom (τ g) * σ (tElt L t) := by
    intro g
    simp only [τ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply]
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, coe_incL, coe_tElt]
    group
  have hτ1 : ∃ g, τ g ≠ g := by
    obtain ⟨l, hl, hne⟩ := hl₀
    refine ⟨e ⟨l, hl⟩, fun h => hne ?_⟩
    have h1 := congrArg (fun x => ((e.symm x : ↥L) : G)) h
    simp only [τ, MulEquiv.symm_apply_apply] at h1
    calc t * l = t * l * t⁻¹ * t := by group
      _ = l * t := by rw [h1]
  have ha2 : σ (tElt L t) * σ (tElt L t) = 1 := by
    rw [← map_mul, show tElt L t * tElt L t = 1 from Subtype.ext ht, map_one]
  have h := finrank_le_or_orth_or hn hF _ (hNT.injective h4 e) hX (σ (tElt L t)) ha2 τ hτ hτ1
  rw [ker_sub_one_eq_repFixedSpace] at h
  rcases h with h | ⟨s, hs, hd, -, hs', ho⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨s, hs, hd, hs', ho⟩)
  · exact Or.inr (Or.inr h)

theorem disp_or_orth (ht : t * t = 1) (e : ↥L ≃* SL(2, F)) {n : ℕ} (hn : 3 ≤ n)
    (hF : Fintype.card F = 2 ^ n) (hl₀ : ∃ l ∈ L, t * l ≠ l * t)
    (σ : Representation (ZMod 2) ↥(L ⊔ zpowers t) Y) (hirr : σ.IsIrreducible)
    (hNT : NoTrivSec (σ.comp (incL L t))) :
    n + 3 ≤ 2 * (Module.finrank (ZMod 2) Y -
        Module.finrank (ZMod 2) (repFixedSpace σ {tElt L t})) ∨
      ∃ s, n = 2 * s ∧
        Module.finrank (ZMod 2) Y - Module.finrank (ZMod 2) (repFixedSpace σ {tElt L t}) = s ∧
        ∃ hs : Fintype.card F = 2 ^ (2 * s), CFSG.RankThree.GF2n.Tim81.Sec2.IsOrthModule hs
          ((σ.comp (incL L t)).comp e.symm.toMonoidHom) := by
  rcases irreducible_or_split σ hirr (incL L t) (tElt L t) (Subtype.ext ht)
      (exists_incL_mul_tElt L t) (fun U hU hUt => invariant_of_incL_tElt L t ht σ U hU hUt) with
    hL' | ⟨Y₀, hY₀, hY₀0, hY₀d⟩
  · obtain ⟨hX, hnt, h | h | ⟨s, hs, hd⟩⟩ := trichotomy_incL ht e hn hF hl₀ σ hL' hNT
    · have := two_mul_le_finrank (by omega) hF _ hX hnt
      left
      omega
    · exact Or.inr h
    · left
      omega
  · have := two_mul_le_finrank_of_invariant e (by omega) hF (σ.comp (incL L t)) hNT hY₀ hY₀0
    left
    omega

end LT

end CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Norm

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

open Subgroup CFSG.QuasithinUnique.Setup.X7b CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Norm
open CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Fac
open CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Br
open scoped MatrixGroups

theorem k147L2N_holds : K147L2N := by
  intro G _ _ V _ _ _ ρ _ _ hρ hirr L _ n hcase h1 hm
  obtain ⟨hn2, hL2, -⟩ := hcase
  have hn : 3 ≤ n := hn2
  haveI hLn : L.Normal := normal_of_numConj_eq_one h1
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := P22y.exists_equiv_sl2 (P22fin.isL2Ev_of_isL2 hL2).1
  letI : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact hF
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  haveI := P22y.isSimpleGroup_sl2 h4
  have hnt : ∃ l ∈ L, ρ l ≠ 1 := by
    obtain ⟨g, hg⟩ := exists_ne (1 : SL(2, F))
    refine ⟨(e.symm g : G), (e.symm g).2, fun h => hg ?_⟩
    have h2 : e.symm g = 1 := Subtype.ext (hρ (h.trans (map_one ρ).symm))
    simpa using congrArg e h2
  refine Or.inl ⟨fun g hg => (hg (by rw [normalizer_eq_top_iff.mpr hLn]; exact mem_top g)).elim,
    ?_⟩
  rw [commOn_eq_top_of_normal ρ hirr hLn hnt]
  have hev : Even (Nat.card G) := by
    have h2 : Nat.card (rootSub F) ∣ Nat.card SL(2, F) := Subgroup.card_subgroup_dvd_card _
    rw [natCard_rootSub, hF', ← Nat.card_congr e.toEquiv] at h2
    exact even_iff_two_dvd.mpr ((dvd_pow_self 2 (by omega)).trans
      (h2.trans (Subgroup.card_subgroup_dvd_card L)))
  obtain ⟨t, ht2, htd⟩ := exists_involution_of_mGV_le ρ hev hm
  have ht : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    omega
  have hNTL := noTrivSec_of_normal ρ hirr hLn hnt
  have hl₀ : ∃ l ∈ L, t * l ≠ l * t := by
    by_contra hc
    push Not at hc
    obtain ⟨Y, hY, hY0, hYd⟩ := exists_le_disp_of_commute ρ hρ ht1 hc
    have := two_mul_le_finrank_of_invariant e (by omega) hF' (ρ.comp L.subtype) hNTL
      (fun k y hy => hY k k.2 y hy) hY0
    omega
  let π : Representation (ZMod 2) ↥(L ⊔ zpowers t) V := ρ.comp (L ⊔ zpowers t).subtype
  have hNT : NoTrivSec (π.comp (incL L t)) := by
    have heq : π.comp (incL L t) = ρ.comp L.subtype := MonoidHom.ext fun _ => rfl
    rw [heq]
    exact hNTL
  have hfix : repFixedSpace π {tElt L t} = repFixedSpace ρ {t} := repFixedSpace_comp_subtype ρ _ _
  have hδ : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (repFixedSpace π {tElt L t}) ≤
      n + 1 := by
    rw [hfix]
    exact htd
  have hTop : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L ⊤ :=
    fun _ _ _ _ => Submodule.mem_top
  by_cases hπ : π.IsIrreducible
  ·
    rcases irreducible_or_split π hπ (incL L t) (tElt L t) (Subtype.ext ht)
        (exists_incL_mul_tElt L t) (fun U hU hUt => invariant_of_incL_tElt L t ht π U hU hUt) with
      hL | ⟨Y₀, hY₀, hY₀0, hY₀d⟩
    · obtain ⟨hX, hnt', h | ⟨s, hs, -, hs', ho⟩ | ⟨s, hs, hd⟩⟩ :=
        trichotomy_incL ht e hn hF' hl₀ π hL hNT
      · rcases nat_or_orth_or_eight hn hF' _ hX hnt' (by omega) with
          hnat | ⟨l, hl, hnl, ho⟩ | ⟨rfl, h8⟩
        · exact Or.inl (natL2_of_isNaturalModule ρ hF e hTop (restr ρ hTop) (fun _ _ => rfl)
            (isNaturalModule_of_equiv hnat Submodule.topEquiv.toAddEquiv (fun _ _ => rfl)))
        · exact Or.inr (Or.inl ⟨l, hnl, Or.inl (secSum_one (natOmegaMinus4_of_isOrthModule ρ
            (by omega) hl e hTop (restr ρ hTop) (fun _ _ => rfl)
            (isOrthModule_of_equiv ho Submodule.topEquiv.toAddEquiv (fun _ _ => rfl))))⟩)
        · refine Or.inr (Or.inr ⟨rfl, hL2, secIrr_of_card ρ hTop ?_ fun C _ hC =>
            ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff _).mp hL).2 C
              fun g u hu => hC g g.2 u hu⟩)
          rw [natCard_eq_two_pow, finrank_top, h8]
      · exact Or.inr (Or.inl ⟨s, hs, Or.inl (secSum_one (natOmegaMinus4_of_isOrthModule ρ
          (by omega) hs' e hTop (restr ρ hTop) (fun _ _ => rfl)
          (isOrthModule_of_equiv ho Submodule.topEquiv.toAddEquiv (fun _ _ => rfl))))⟩)
      · omega
    · have := two_mul_le_finrank_of_invariant e (by omega) hF' (π.comp (incL L t)) hNT hY₀ hY₀0
      omega
  ·
    have hVnt : Nontrivial V := ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).1
    obtain ⟨U, hU, hU0, hUt⟩ : ∃ U : Submodule (ZMod 2) V, (∀ h, ∀ u ∈ U, π h u ∈ U) ∧
        U ≠ ⊥ ∧ U ≠ ⊤ := by
      by_contra hc
      push Not at hc
      exact hπ ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff π).mpr
        ⟨hVnt, fun U hU => or_iff_not_imp_left.mpr (hc U hU)⟩)
    obtain ⟨U', hU'U, hU'⟩ := exists_irreducible_sub π hU hU0
    have hU'top : U'.toSubmodule ≠ ⊤ := fun h => hUt (top_le_iff.mp (by rw [← h]; exact hU'U))
    haveI : Nontrivial U'.toSubmodule :=
      ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff _).mp hU').1
    haveI : Finite (V ⧸ U'.toSubmodule) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
    haveI : Nontrivial (V ⧸ U'.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hU'top
    have hNTU := NoTrivSec.sub hNT U'
    have hNTQ := NoTrivSec.quot hNT U'
    have hcod := codim_sub_quot π U' {tElt L t}
    have hlow : ∀ {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y] [Finite Y]
        (σ : Representation (ZMod 2) ↥(L ⊔ zpowers t) Y), σ.IsIrreducible →
          NoTrivSec (σ.comp (incL L t)) → n ≤ 2 * (Module.finrank (ZMod 2) Y -
            Module.finrank (ZMod 2) (repFixedSpace σ {tElt L t})) := by
      intro Y _ _ _ σ hσ hσNT
      rcases disp_or_orth ht e hn hF' hl₀ σ hσ hσNT with h | ⟨s, hs, hd, -⟩ <;> omega
    have hQ := le_disp_of_forall_irreducible (incL L t) (tElt L t) hlow U'.quotient hNTQ
    obtain hU1 | ⟨s, hs, hdU, hsF, hoU⟩ :=
      disp_or_orth ht e hn hF' hl₀ U'.toRepresentation hU' hNTU
    · omega
    have hQirr := isIrreducible_of_disp_lt (incL L t) (tElt L t) hlow U'.quotient hNTQ
      (by omega)
    obtain hQ1 | ⟨s', hs', -, hsF', hoQ⟩ := disp_or_orth ht e hn hF' hl₀ U'.quotient hQirr hNTQ
    · omega
    have hss : s' = s := by omega
    obtain ⟨C, hC, hcompl⟩ := exists_isCompl_of_normal ρ hirr hLn (N := U'.toSubmodule)
      (fun l hl v hv => U'.apply_mem_toSubmodule (incL L t ⟨l, hl⟩) hv)
    have hUinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ L U'.toSubmodule :=
      fun l hl v hv => U'.apply_mem_toSubmodule (incL L t ⟨l, hl⟩) hv
    have hUo : NatOmegaMinus4 ρ L U'.toSubmodule ⊥ s :=
      natOmegaMinus4_of_isOrthModule ρ (by omega) hsF e hUinv
        (U'.toRepresentation.comp (incL L t)) (fun _ _ => rfl) hoU
    have hCo : NatOmegaMinus4 ρ L C ⊥ s' :=
      natOmegaMinus4_of_isOrthModule ρ (by omega) hsF' e hC (restr ρ hC) (fun _ _ => rfl)
        (isOrthModule_of_equiv hoQ
          (Submodule.quotientEquivOfIsCompl _ _ hcompl).symm.toAddEquiv (fun _ _ => rfl))
    exact Or.inr (Or.inl ⟨s, hs, Or.inr (secSum_two hUo (hss ▸ hCo) hcompl.sup_eq_top
      hcompl.inf_eq_bot)⟩)

end CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
