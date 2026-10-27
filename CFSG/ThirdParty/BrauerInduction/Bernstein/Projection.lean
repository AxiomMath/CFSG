module

public import CFSG.ThirdParty.BrauerInduction.Cyclotomic.Projection
public import CFSG.ThirdParty.BrauerInduction.Bernstein.GlobalIdeal
public import CFSG.ThirdParty.BrauerInduction.Span

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Bernstein's coefficient-projection step

This file applies the cyclotomic coefficient projection to Bernstein's induced
`Q`-functions.

The generator theorem `nuStar_projects_E` shows that the projection of a
function induced from a `p`-elementary subgroup lies in `BrauerSpanChar`. This
is extended to `JGlobalIdeal`. Applying `nuStarLinear` to `1 ∈ JGlobalIdeal`
yields `1 ∈ BrauerIdeal` and hence `BrauerIdeal = ⊤`.
-/

open ClassFun
open BrauerInduction.Cyclotomic

namespace CFSG.BrauerInduction
namespace Bernstein

section CharacterCoefficientProjection

variable {k G : Type u} [Group G] [Finite G] [Field k] [CharZero k]

/--
The coefficient projection of a `Q`-function induced from a `p`-elementary
subgroup lies in `BrauerSpanChar`.

This is the generator-level projection theorem used for both the additive and
ideal formulations of Bernstein's global argument.
-/
lemma nuStar_projects_E
    (B : ClassFun.IrrepCharBasis k G)
    (p : ℕ) [Fact p.Prime]
    (E : Subgroup G) (hE : IsPElementary p E)
    (q : ClassFun k E)
    (hq : q ∈ ClassFun.Q_sys k G E) :
    ClassFun.HasLambdaCoords B (ClassFun.ind E q) ∧
      nuStar B (ClassFun.ind E q) ∈ BrauerSpanChar (k := k) (G := G) := by
  have h_Q :
      ∃ l : List (FDRep k E × ClassFun.Lambda k G),
        q =
          (l.map fun P =>
            (P.2 : k) • ClassFun.character P.1).sum := by
    have hqR : q ∈ ClassFun.R_Lambda k G E := hq.1
    unfold ClassFun.R_Lambda at hqR
    refine Submodule.span_induction
      (p := fun q _ =>
        ∃ l : List (FDRep k E × ClassFun.Lambda k G),
          q =
            (l.map fun P =>
              (P.2 : k) • ClassFun.character P.1).sum)
      ?gen ?zero ?add ?smul hqR
    · rintro χ ⟨W, rfl⟩
      refine ⟨[(W, 1)], ?_⟩
      simp
    · refine ⟨[], ?_⟩
      simp
    · intro q₁ q₂ _ _ hq₁ hq₂
      rcases hq₁ with ⟨l₁, rfl⟩
      rcases hq₂ with ⟨l₂, rfl⟩
      refine ⟨l₁ ++ l₂, ?_⟩
      simp [List.map_append, List.sum_append]
    · intro a q _ hq
      rcases hq with ⟨l, rfl⟩
      refine ⟨l.map fun P => (P.1, a * P.2), ?_⟩
      have scale_list :
          ∀ l : List (FDRep k E × ClassFun.Lambda k G),
            a •
                (l.map fun P =>
                  (P.2 : k) • ClassFun.character P.1).sum
              =
                ((l.map fun P => (P.1, a * P.2)).map fun P =>
                  (P.2 : k) • ClassFun.character P.1).sum := by
        intro l
        induction l with
        | nil =>
            simp
        | cons hd tl ih_tl =>
            simp only [List.map_cons, List.sum_cons]
            have hhead :
                a • ((hd.2 : k) • ClassFun.character hd.1)
                  =
                (((a * hd.2 : ClassFun.Lambda k G) : k) • ClassFun.character hd.1) := by
              change
                (a : k) • ((hd.2 : k) • ClassFun.character hd.1)
                  =
                (((a * hd.2 : ClassFun.Lambda k G) : k) • ClassFun.character hd.1)
              rw [show ((a * hd.2 : ClassFun.Lambda k G) : k) =
                    (a : k) * (hd.2 : k) by rfl]
              rw [mul_smul]
            calc
              a •
                  (((hd.2 : k) • ClassFun.character hd.1)
                    + (tl.map fun P =>
                        (P.2 : k) • ClassFun.character P.1).sum)
                  =
                a • ((hd.2 : k) • ClassFun.character hd.1)
                  + a •
                    (tl.map fun P =>
                      (P.2 : k) • ClassFun.character P.1).sum := by
                    rw [smul_add]
              _ =
                (((a * hd.2 : ClassFun.Lambda k G) : k) • ClassFun.character hd.1)
                  +
                (((tl.map fun P => (P.1, a * P.2)).map fun P =>
                    (P.2 : k) • ClassFun.character P.1).sum) := by
                    rw [hhead, ih_tl]
      simpa using scale_list l
  rcases h_Q with ⟨l, hl⟩
  let qOf : List (FDRep k E × ClassFun.Lambda k G) → ClassFun k E :=
    fun l => (l.map fun P => (P.2 : k) • ClassFun.character P.1).sum
  have H :
      ∀ l,
        ClassFun.HasLambdaCoords B (ClassFun.ind E (qOf l)) ∧
          nuStar B (ClassFun.ind E (qOf l))
            ∈ BrauerSpanChar (k := k) (G := G) := by
    intro l
    induction l with
    | nil =>
        simp only [qOf, List.map_nil, List.sum_nil]
        rw [ClassFun.ind_zero]
        constructor
        · exact ClassFun.HasLambdaCoords.zero B
        · rw [nuStar_zero]
          exact Submodule.zero_mem _
    | cons hd tl ih =>
        simp only [qOf, List.map_cons, List.sum_cons]
        have h_ind_char :
            ClassFun.ind E (ClassFun.character hd.1)
              =
            ClassFun.character (FDRep.ind E hd.1) := by
          exact (ClassFun.char_ind E hd.1).symm
        have h_first_coords :
            ClassFun.HasLambdaCoords B
              (ClassFun.ind E ((hd.2 : k) • ClassFun.character hd.1)) := by
          rw [ClassFun.ind_smul, h_ind_char]
          exact
            ClassFun.HasLambdaCoords.smul B
              hd.2.property
              (ClassFun.HasLambdaCoords.character B (FDRep.ind E hd.1))
        have h_first_mem :
            nuStar B
              (ClassFun.ind E ((hd.2 : k) • ClassFun.character hd.1))
                ∈ BrauerSpanChar (k := k) (G := G) := by
          rw [ClassFun.ind_smul, h_ind_char]
          rw [nuStar_smul_char B hd.2.property (FDRep.ind E hd.1)]
          let z : ℤ :=
            nu k G ⟨(hd.2 : k), hd.2.property⟩
          have hz :
              nu_ext (k := k) (G := G) (hd.2 : k) = (z : k) := by
            unfold nu_ext
            rw [dif_pos hd.2.property]
          rw [hz, Int.cast_smul_eq_zsmul]
          have h_gen :
              ClassFun.ind E (ClassFun.character hd.1)
                ∈ BrauerSpanChar (k := k) (G := G) := by
            apply Submodule.subset_span
            have hBrauer : IsBrauerElementary E := by
              exact IsBrauerElementary.ofIsPElementary p hE
            exact ⟨E, hBrauer, hd.1, rfl⟩
          rw [h_ind_char] at h_gen
          exact Submodule.smul_mem _ z h_gen
        rw [ClassFun.ind_add]
        constructor
        · exact ClassFun.HasLambdaCoords.add B h_first_coords ih.1
        · rw [nuStar_add B h_first_coords ih.1]
          exact Submodule.add_mem _ h_first_mem ih.2
  have hq_eq : q = qOf l := by
    simpa [qOf] using hl
  rw [hq_eq]
  exact H l

lemma nuStarLinear_maps_JIdeal [IsAlgClosed k]
    (B : ClassFun.IrrepCharBasis k G)
    (p : ℕ) [Fact p.Prime]
    {f : ClassFun.IntegralCyclotomicCharacterRing (k := k) (G := G)}
    (hf : f ∈ JIdeal (k := k) (G := G) p) :
    nuStarLinear B f ∈ BrauerIdeal := by
  change
    nuStar B (f : ClassFun k G) ∈
      BrauerSpanChar (k := k) (G := G)

  let P : ClassFun k G → Prop :=
    fun x =>
      ClassFun.HasLambdaCoords B x ∧
        nuStar B x ∈ BrauerSpanChar (k := k) (G := G)

  have hzero : P 0 := by
    constructor
    · exact ClassFun.HasLambdaCoords.zero B
    · rw [nuStar_zero B]
      exact Submodule.zero_mem _

  have hadd :
      ∀ x y, P x → P y → P (x + y) := by
    intro x y hx hy
    constructor
    · exact ClassFun.HasLambdaCoords.add B hx.1 hy.1
    · rw [nuStar_add B hx.1 hy.1]
      exact Submodule.add_mem _ hx.2 hy.2

  have H : P (f : ClassFun k G) := by
    change (f : ClassFun k G) ∈ J (k := k) (G := G) p at hf
    refine @Submodule.span_induction ℤ (ClassFun k G) _ _ _ _
      (fun y _ => P y) ?_ hzero ?_ ?_
      (f : ClassFun k G) hf
    · rintro _ ⟨E, hE, q, hq, rfl⟩
      exact nuStar_projects_E B p E hE q hq
    · intro x y _ _ hx hy
      exact hadd x y hx hy
    · intro z x _ hx
      constructor
      · exact ClassFun.HasLambdaCoords.zsmul B z hx.1
      · rw [nuStar_zsmul B z hx.1]
        exact Submodule.smul_mem _ z hx.2

  exact H.2

lemma nuStarLinear_maps_JGlobalIdeal [IsAlgClosed k]
    (B : ClassFun.IrrepCharBasis k G)
    {f : ClassFun.IntegralCyclotomicCharacterRing (k := k) (G := G)}
    (hf : f ∈ JGlobalIdeal) :
    nuStarLinear B f ∈ BrauerIdeal := by
  let Q := ClassFun.IntegralCyclotomicCharacterRing (k := k) (G := G)

  let P : Q → Prop :=
    fun x => nuStarLinear B x ∈ BrauerIdeal

  have hzero : P 0 := by
    change
      nuStarLinear B 0 ∈ BrauerIdeal
    simpa only [map_zero] using
      (BrauerIdeal (k := k) (G := G)).zero_mem

  have hadd :
      ∀ x y, P x → P y → P (x + y) := by
    intro x y hx hy
    change
      nuStarLinear B (x + y) ∈ BrauerIdeal
    rw [map_add]
    exact
      (BrauerIdeal (k := k) (G := G)).add_mem hx hy

  change P f
  unfold JGlobalIdeal at hf
  refine @Submodule.iSup_induction Q Q _ _ _ ℕ
    (fun p =>
      ⨆ (_ : Fact p.Prime),
        JIdeal (k := k) (G := G) p)
    P f hf ?_ hzero hadd
  intro p x hx
  refine @Submodule.iSup_induction Q Q _ _ _
    (Fact p.Prime)
    (fun _ =>
      JIdeal (k := k) (G := G) p)
    P x hx ?_ hzero hadd
  intro hp y hy
  letI : Fact p.Prime := hp
  exact
    nuStarLinear_maps_JIdeal B p hy

/--
The unit of the character ring belongs to the Brauer ideal.

This is Bernstein's final coefficient-projection step expressed in the
ring-and-ideal API.
-/
theorem one_mem_BrauerIdeal [IsAlgClosed k] :
    (1 : ClassFun.CharacterRing k G) ∈ BrauerIdeal := by
  let B := ClassFun.irrepCharBasis (k := k) (G := G)
  simpa only [nuStarLinear_one] using
    (nuStarLinear_maps_JGlobalIdeal B one_mem_JGlobalIdeal)

/--
Bernstein's argument shows that the Brauer ideal is the whole character ring.
-/
theorem BrauerIdeal.eq_top [IsAlgClosed k] :
    BrauerIdeal (k := k) (G := G) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  exact one_mem_BrauerIdeal (k := k) (G := G)

end CharacterCoefficientProjection

end CFSG.BrauerInduction.Bernstein
