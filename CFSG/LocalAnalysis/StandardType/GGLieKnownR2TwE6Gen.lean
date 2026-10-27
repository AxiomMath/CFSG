module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Rad
public import CFSG.LieType.HighestRoot.Gen
public import CFSG.LieType.Steinberg.TwistedE6.Clause0

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
open scoped commutatorElement

private theorem form_toRat_twE6Alpha (v : Fin (Tag.rank .F4) → ℤ) :
    form (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) (toRat v) (toRat twE6Alpha) =
      symmetrizer (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) twE6Last *
        (v twE6Last : ℚ) := by
  rw [form_comm, form_eq_sum]
  have hsingle : ∀ l : Fin (Tag.rank .F4),
      form (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) (toRat twE6Alpha)
        (Pi.single l 1) =
      symmetrizer (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) l *
        (coroot (Tag.cartan .F4) l twE6Alpha : ℚ) := by
    intro l
    rw [form_single_right, coroot_apply]
    congr 1
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [toRat_apply]
  have hcor : ∀ l : Fin (Tag.rank .F4),
      coroot (Tag.cartan .F4) l twE6Alpha = if l = twE6Last then 1 else 0 := by
    intro l
    fin_cases l <;> decide
  simp only [hsingle, hcor]
  rw [Finset.sum_eq_single twE6Last]
  · simp [toRat_apply, mul_comm]
  · intro l _ hl
    rw [if_neg hl]
    ring
  · intro h
    exact absurd (Finset.mem_univ twE6Last) h

private theorem weylAction_twE6Last_eq_neg
    {s : (coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)).Group}
    (hs : weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) s twE6Alpha = -twE6Alpha)
    (v : Fin (Tag.rank .F4) → ℤ) :
    weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) s v twE6Last = - v twE6Last := by
  have hα : weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) s (-twE6Alpha) =
      twE6Alpha := by rw [map_neg, hs, neg_neg]
  have h2 : form (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)
      (toRat (weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) s v))
      (toRat twE6Alpha) =
      - form (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) (toRat v) (toRat twE6Alpha) := by
    have h := form_weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) s v (-twE6Alpha)
    rw [hα, map_neg] at h
    rw [h, map_neg]
  rw [form_toRat_twE6Alpha (weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) s v),
    form_toRat_twE6Alpha v] at h2
  have hd : symmetrizer (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) twE6Last ≠ 0 :=
    ne_of_gt (symmetrizer_pos (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) twE6Last)
  have h3 : symmetrizer (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) twE6Last *
      ((weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) s v twE6Last : ℤ) : ℚ) =
      symmetrizer (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) twE6Last *
        ((-(v twE6Last) : ℤ) : ℚ) := by
    rw [Int.cast_neg, h2, mul_neg]
  exact Int.cast_injective (mul_left_cancel₀ hd h3)

private theorem linIndepPair_of_last_eq_zero
    {γ δ : Fin (Tag.rank .F4) → ℤ} (hγ : γ twE6Last ≠ 0) (hδ0 : δ ≠ 0)
    (hδ : δ twE6Last = 0) : LinIndepPair δ γ := by
  intro a b hab
  have h := congrFun hab twE6Last
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hδ, mul_zero,
    zero_add] at h
  have hb : b = 0 := by
    rcases mul_eq_zero.1 h with h' | h'
    · exact h'
    · exact absurd h' hγ
  refine ⟨?_, hb⟩
  have hab' : a • δ = 0 := by simpa [hb] using hab
  by_contra ha
  have : δ = 0 := by
    funext j
    have h2 : a * δ j = 0 := by
      have := congrFun hab' j
      simpa [Pi.smul_apply, smul_eq_mul] using this
    rcases mul_eq_zero.1 h2 with h' | h'
    · exact absurd h' ha
    · exact h'
  exact hδ0 this

private theorem teGen_normal_eq_top_or_le_center {Q : Type} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hperf, hs, -⟩ := hQ
  haveI : (N.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hcomm : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    exact eq_top_iff.mpr (hperf.commutator_eq_top ▸ hcomm)

theorem twE6_rad_sup_rankOne_eq_top
    {k : Type} [Field k] [Finite k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (hk : 4 ≤ Nat.card k) :
    twE6Rad θ ⊔ ((twistedDatum k θ).rootGroup twE6Alpha ⊔
      (twistedDatum k θ).rootGroup (-twE6Alpha)) = ⊤ := by
  let last : Fin (twistedDatum k θ).rank := twE6Last
  let S : Set (Fin (twistedDatum k θ).rank → ℤ) :=
    {γ | γ ∈ (twistedDatum k θ).roots ∧ γ last ≠ 0}
  let N' : Subgroup (fixedGroup k θ) := ggSub (twistedDatum k θ) S
  have hct : IsCTGroupDatum (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem
      (weylAction (twistedDatum k θ).isFiniteType) (twistedDatum k θ).roots
      (twistedDatum k θ).rootGroup (nHat θ) (hHat k θ) :=
    twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ)
  have hext : SteinbergExtras (twistedDatum k θ) (nHat θ) (hHat k θ) :=
    twistedDatum_steinbergExtras θ hθ
  have hBU : BruhatExtras (twistedDatum k θ) (hHat k θ) := twistedDatum_bruhatExtras θ
  have hW : CFSG.LieType.HighestRoot.DivisibleWeylMem (twistedDatum k θ) (nHat θ) :=
    CFSG.LieType.HighestRoot.divisibleWeylMem_of_divisible_eq_empty rfl
  have hN'eq : N' = twE6Rad θ ⊔ ((twistedDatum k θ).rootGroup twE6Alpha ⊔
      (twistedDatum k θ).rootGroup (-twE6Alpha)) := by
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun γ hγ => ?_
      rcases lt_trichotomy (γ last) 0 with hlt | heq | hgt
      · obtain ⟨m, hm, s, hms, hs⟩ :=
          CFSG.LieType.HighestRoot.exists_mem_rankOneGroup_actsAs (D := twistedDatum k θ) hct hW
            (twE6_alpha_mem_roots θ)
        have hlast : (weylAction (twistedDatum k θ).isFiniteType s γ) last = -(γ last) :=
          weylAction_twE6Last_eq_neg hs γ
        have hpos : 1 ≤ (weylAction (twistedDatum k θ).isFiniteType s γ) last := by
          rw [hlast]; omega
        have hmem : weylAction (twistedDatum k θ).isFiniteType s γ ∈ (twistedDatum k θ).roots :=
          weylAction_mem_roots (twistedDatum k θ).isFiniteType s hγ.1
        have hQ : (twistedDatum k θ).rootGroup
            (weylAction (twistedDatum k θ).isFiniteType s γ) ≤ twE6Rad θ :=
          rootGroup_le_ggSub (D := twistedDatum k θ)
            (S := {γ | γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ last}) ⟨hmem, hpos⟩
        have hmN : m ∈ twE6Rad θ ⊔ ((twistedDatum k θ).rootGroup twE6Alpha ⊔
            (twistedDatum k θ).rootGroup (-twE6Alpha)) :=
          Subgroup.mem_sup_right hm
        have hconj : (twistedDatum k θ).rootGroup γ =
            ((twistedDatum k θ).rootGroup (weylAction (twistedDatum k θ).isFiniteType s γ)).map
              (MulAut.conj m⁻¹).toMonoidHom := by
          rw [← hms γ hγ.1, Subgroup.map_map]
          have hcomp : (MulAut.conj m⁻¹).toMonoidHom.comp (MulAut.conj m).toMonoidHom =
              MonoidHom.id _ := by
            ext x
            simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
              MulAut.conj_apply]
            group
          rw [hcomp, Subgroup.map_id]
        rw [hconj]
        rintro _ ⟨y, hy, rfl⟩
        exact mul_mem (mul_mem (inv_mem hmN) ((hQ.trans le_sup_left) hy)) hmN
      · exact absurd heq hγ.2
      · exact (rootGroup_le_ggSub (D := twistedDatum k θ)
          (S := {γ | γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ last})
          ⟨hγ.1, by omega⟩).trans le_sup_left
    · refine sup_le ?_ (sup_le ?_ ?_)
      · refine iSup₂_le fun γ hγ => rootGroup_le_ggSub (D := twistedDatum k θ) (S := S)
          ⟨hγ.1, ne_of_gt (lt_of_lt_of_le zero_lt_one hγ.2)⟩
      · exact rootGroup_le_ggSub (D := twistedDatum k θ) (S := S)
          ⟨twE6_alpha_mem_roots θ, by decide⟩
      · refine rootGroup_le_ggSub (D := twistedDatum k θ) (S := S) ⟨?_, by decide⟩
        show -twE6Alpha ∈ (twistedDatum k θ).roots
        exact OfCartan.neg_mem_roots (twistedDatum k θ).isFiniteType (twE6_alpha_mem_roots θ)
  have hnorm : N'.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    rw [eq_top_iff, ← iSup_twistedDatum_rootGroup (k := k) θ hθ]
    refine iSup₂_le fun δ hδ => ?_
    by_cases hδ0 : δ last = 0
    · refine CFSG.LieType.Steinberg.le_normalizer_iSup₂
        (A := (twistedDatum k θ).rootGroup δ)
        (X := fun γ => (twistedDatum k θ).rootGroup γ) (P := S) ?_
      intro x hx γ hγ y hy
      have hlin : LinIndepPair δ γ :=
        linIndepPair_of_last_eq_zero hγ.2
          (ne_zero_of_mem_roots (twistedDatum k θ).isFiniteType (twistedDatum k θ).divisible hδ)
          hδ0
      have hsup : (⨆ ε ∈ openCone {β | IsRoot .F4 β} δ γ, twistedRootGroup k θ ε) ≤ N' := by
        refine iSup₂_le fun ε hε => rootGroup_le_ggSub (D := twistedDatum k θ) (S := S) ?_
        obtain ⟨hεroot, a, b, ha, hb, rfl⟩ := hε
        refine ⟨?_, ?_⟩
        · show a • δ + b • γ ∈ (twistedDatum k θ).roots
          rw [twistedDatum_roots]
          exact hεroot
        · change a * (δ last) + b * (γ last) ≠ 0
          rw [hδ0, mul_zero, zero_add]
          exact mul_ne_zero (by exact_mod_cast (ne_of_gt hb)) hγ.2
      have hcomm : ⁅x, y⁆ ∈ N' :=
        hsup (commutator_mem_iSup_twistedRootGroup hlin hx hy)
      have hxy : x * y * x⁻¹ = ⁅x, y⁆ * y := by
        rw [commutatorElement_def]
        group
      rw [hxy]
      exact mul_mem hcomm (rootGroup_le_ggSub (D := twistedDatum k θ) (S := S) hγ hy)
    · exact (rootGroup_le_ggSub (D := twistedDatum k θ) (S := S) ⟨hδ, hδ0⟩).trans
        Subgroup.le_normalizer
  have hx : ∃ x ∈ N', x ∉ Subgroup.center (fixedGroup k θ) := by
    have hcenter : Subgroup.center (fixedGroup k θ) ≤ ⨆ i, hHat k θ i := by
      rw [CFSG.LieType.TitsSimplicity.center_eq_normalCore_borel hct hext hBU]
      exact CFSG.LieType.TitsSimplicity.normalCore_borel_le_iSup hct hBU
    have hbot : (twistedDatum k θ).rootGroup twE6Alpha ⊓ Subgroup.center (fixedGroup k θ) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_inf] at hx
      have hxpos : x ∈ ⨆ γ ∈ {γ | IsRoot .F4 γ ∧ 0 < ht γ}, twistedRootGroup k θ γ :=
        Subgroup.mem_iSup_of_mem twE6Alpha
          (Subgroup.mem_iSup_of_mem
            ⟨isRoot_of_mem_twistedDatum_roots θ (twE6_alpha_mem_roots θ), by decide⟩ hx.1)
      have h := Subgroup.mem_inf.2 ⟨hcenter hx.2, hxpos⟩
      rw [torus_inf_posPart_twisted θ, Subgroup.mem_bot] at h
      exact Subgroup.mem_bot.2 h
    have hne : (twistedDatum k θ).rootGroup twE6Alpha ≠ ⊥ :=
      twistedRootGroup_ne_bot θ hθ (isRoot_of_mem_twistedDatum_roots θ (twE6_alpha_mem_roots θ))
    obtain ⟨x, hx1⟩ :=
      (Subgroup.ne_bot_iff_exists_ne_one (H := (twistedDatum k θ).rootGroup twE6Alpha)).1 hne
    refine ⟨(x : fixedGroup k θ),
      rootGroup_le_ggSub (D := twistedDatum k θ) (S := S)
        ⟨twE6_alpha_mem_roots θ, by decide⟩ x.2, ?_⟩
    intro hxc
    have : (x : fixedGroup k θ) ∈
        (twistedDatum k θ).rootGroup twE6Alpha ⊓ Subgroup.center (fixedGroup k θ) :=
      ⟨x.2, hxc⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hx1 (Subtype.ext this)
  rw [← hN'eq]
  rcases teGen_normal_eq_top_or_le_center
      (fixedGroup_isQuasisimple_of_four_le_card θ hθ hk) hnorm with
    htop | hle
  · exact htop
  · exfalso
    obtain ⟨x, hxN', hxnotcenter⟩ := hx
    exact hxnotcenter (hle hxN')

end CFSG.StandardType.LieKnownR2.Short
