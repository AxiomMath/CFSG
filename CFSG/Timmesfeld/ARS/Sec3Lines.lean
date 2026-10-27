module

public import CFSG.Timmesfeld.ARS.Sec3Natural
public import CFSG.Timmesfeld.ARS.BasicLines

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Matrix
open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec3

section Lines

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) {A B C : Subgroup G}
  (hA : A ∈ R) (hB : B ∈ R) (hAB : Opposite A B) (hAC : C ∈ lambdaSet R A)
  (hBC : C ∈ psiSet R B)
include hR hiso hA hB hAB hAC hBC

theorem card_setOf_mem_le_sup :
    Nat.card {E : Subgroup G // E ∈ R ∧ E ≤ A ⊔ C} = Nat.card A + 1 := by
  have hS := setOf_mem_le_sup_eq hR hiso hA hB hAB hAC hBC
  have hCR : C ∈ R := hAC.1.1
  have hN := commuting_sup_commutator hR hAC hBC
  set g : ↥(⁅B, C⁆ : Subgroup G) → Subgroup G := fun d => conjSub A d with hg
  have hrange : (Set.range fun n : ↥(C ⊔ ⁅B, C⁆) => conjSub A n) = Set.range g := by
    ext E
    constructor
    · rintro ⟨⟨n, hn⟩, rfl⟩
      obtain ⟨c, hc, d, hd, rfl⟩ := (mem_sup_commutator_iff hBC).1 hn
      refine ⟨⟨d, hd⟩, ?_⟩
      have hcd : c * d = d * c :=
        (hN c (Subgroup.mem_sup_left hc) d (Subgroup.mem_sup_right hd)).eq
      change conjSub A d = conjSub A (c * d)
      rw [hcd, conjSub_mul, conjSub_of_forall_commute fun a ha => (hAC.1.2.2 a ha c hc).symm]
    · rintro ⟨⟨d, hd⟩, rfl⟩
      exact ⟨⟨d, Subgroup.mem_sup_right hd⟩, rfl⟩
  have hinj : Function.Injective g := by
    rintro ⟨d, hd⟩ ⟨d', hd'⟩ h
    change conjSub A d = conjSub A d' at h
    have hm : conjSub A (d'⁻¹ * d) = A := by
      rw [conjSub_mul, h, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    have hmN : d'⁻¹ * d ∈ C ⊔ ⁅B, C⁆ :=
      Subgroup.mem_sup_right (Subgroup.mul_mem _ (Subgroup.inv_mem _ hd') hd)
    have hcomm : ∀ a ∈ A, Commute a (d'⁻¹ * d) := by
      intro a ha
      have h1 : ⁅a, d'⁻¹ * d⁆ ∈ C := commutatorElement_mem_of_mem_sup hR hiso hA hB hAB hAC hBC
        ha hmN
      have h2 : ⁅a, d'⁻¹ * d⁆ ∈ A := by
        have e : ⁅a, d'⁻¹ * d⁆ = a * ((d'⁻¹ * d) * a⁻¹ * (d'⁻¹ * d)⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [e]
        refine A.mul_mem ha ?_
        have := conj_mem_conjSub (d'⁻¹ * d) (A.inv_mem ha)
        rwa [hm] at this
      have h3 : ⁅a, d'⁻¹ * d⁆ ∈ A ⊓ C := ⟨h2, h1⟩
      rw [inf_eq_bot hR hiso hA hCR hAC.1.2.1.symm, Subgroup.mem_bot,
        commutatorElement_eq_one_iff_mul_comm] at h3
      exact h3
    have hmC := mem_of_forall_commute_of_mem_sup hR hiso hA hB hAB hAC hBC hmN hcomm
    have hne : C ≠ ⁅B, C⁆ := by
      have := hBC.2.symm.ne_commutator hR
      rwa [Subgroup.commutator_comm] at this
    have hmem : d'⁻¹ * d ∈ C ⊓ ⁅B, C⁆ :=
      ⟨hmC, Subgroup.mul_mem _ (Subgroup.inv_mem _ hd') hd⟩
    rw [inf_eq_bot hR hiso hCR hBC.2.1 hne, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact Subtype.ext hmem.symm
  have hCnot : C ∉ Set.range g := by
    rintro ⟨⟨d, hd⟩, h⟩
    change conjSub A d = C at h
    apply hAC.1.2.1
    have hdC : conjSub C d⁻¹ = C := conjSub_of_forall_commute fun c hc =>
      (hN _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ hd)) c (Subgroup.mem_sup_left hc))
    rw [← hdC, ← h, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have e1 : Nat.card {E : Subgroup G // E ∈ R ∧ E ≤ A ⊔ C} =
      Nat.card ↥{E : Subgroup G | E ∈ R ∧ E ≤ A ⊔ C} := rfl
  rw [e1, hS, hrange, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem hCnot,
    ← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj, hR.card_eq hBC.2.1 hA]

omit [Finite G] hA hB hAB hAC hBC in
theorem eq_of_mem_of_mem {P Q : Subgroup G} (hP : P ∈ R) (hQ : Q ∈ R) {x : G} (hxP : x ∈ P)
    (hxQ : x ∈ Q) (hx1 : x ≠ 1) : P = Q := by
  by_contra hne
  have hx : x ∈ P ⊓ Q := ⟨hxP, hxQ⟩
  rw [inf_eq_bot hR hiso hP hQ hne, Subgroup.mem_bot] at hx
  exact hx1 hx

theorem conjSub_props {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    Special R A (conjSub C b) ∧ ⁅A, conjSub C b⁆ = C ∧ C ∈ lambdaSet R (conjSub C b) ∧
      (∀ e ∈ conjSub C b, conjSub (A ⊔ C) e ≤ A ⊔ C) ∧
      (∀ x ∈ A ⊔ C, (∀ e ∈ conjSub C b, Commute e x) → x ∈ C) := by
  have hCR : C ∈ R := hAC.1.1
  have hN := commuting_sup_commutator hR hAC hBC
  have hsp := special_conjSub_of_mem_lambdaSet hR hA hAB hAC hBC hb hb1
  have hEN : conjSub C b ≤ C ⊔ ⁅B, C⁆ := by
    rw [← conjSub_sup_commutator_eq hR hiso hA hB hAB hAC hBC (Subgroup.mem_sup_right hb)]
    exact Subgroup.map_mono le_sup_left
  have hER : conjSub C b ∈ R := hR.conjSub_mem hCR b
  have hAE : ⁅A, conjSub C b⁆ = C := by
    have hle : ⁅A, conjSub C b⁆ ≤ C := by
      rw [Subgroup.commutator_le]
      intro a ha e he
      exact commutatorElement_mem_of_mem_sup hR hiso hA hB hAB hAC hBC ha (hEN he)
    by_contra hne
    have := inf_eq_bot hR hiso hsp.1 hCR hne
    rw [inf_of_le_left hle] at this
    exact hR.ne_bot _ hsp.1 this
  have hEC : conjSub C b ≠ C := by
    intro h
    obtain ⟨c, hc, hc1⟩ := hR.exists_ne_one hCR
    apply hc1
    refine eq_one_of_commute_of_special hR hiso hB hCR hBC.2 hb hb1 hc ?_
    have h1 : ⁅b, c⁆ ∈ C ⊓ ⁅B, C⁆ := by
      refine ⟨?_, Subgroup.commutator_mem_commutator hb hc⟩
      rw [commutatorElement_def]
      refine C.mul_mem ?_ (C.inv_mem hc)
      rw [← h]
      exact conj_mem_conjSub b hc
    have hne : C ≠ ⁅B, C⁆ := by
      have := hBC.2.symm.ne_commutator hR
      rwa [Subgroup.commutator_comm] at this
    rw [inf_eq_bot hR hiso hCR hBC.2.1 hne, Subgroup.mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hEcomm : Commuting (conjSub C b) C := hN.mono hEN le_sup_left
  have hCl : C ∈ lambdaSet R (conjSub C b) := by
    refine ⟨⟨hCR, hEC.symm, hEcomm⟩, ?_⟩
    have hsup : conjSub C b ⊔ C = C ⊔ ⁅B, C⁆ := sup_eq_of_le_of_commuting hR hiso hCR hBC.2.1
      hER hCR hBC.2.2.2.symm hEN le_sup_left hEC
    rw [hsup]
    exact coveredBy_sup_commutator hR hiso hA hB hAB hAC hBC
  refine ⟨hsp, hAE, hCl, fun e he => ?_, fun x hx hxE => ?_⟩
  · rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub,
      conjSub_of_forall_commute fun c hc => hEcomm e he c hc]
    refine sup_le ((conjSub_le_commutator_sup he).trans ?_) le_sup_right
    rw [hAE, sup_comm]
  · have hleAC : C ≤ Subgroup.normalizer (A : Set G) :=
      (commuting_iff_le_centralizer.1 hAC.1.2.2).trans (Subgroup.centralizer_le_normalizer _)
    have hx' : x ∈ ((A ⊔ C : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left A C hleAC] at hx'
    obtain ⟨a, ha, c, hc, rfl⟩ := hx'
    dsimp only at hxE ⊢
    obtain ⟨e, he, he1⟩ := hR.exists_ne_one hER
    have hea : Commute e a := by
      have h1 := hxE e he
      have h2 : Commute e c := hEcomm e he c hc
      have := h1.mul_right h2.inv_right
      rwa [mul_inv_cancel_right] at this
    rw [eq_one_of_commute_of_special hR hiso hER hA hsp.symm he he1 ha hea, one_mul]
    exact hc

end Lines

theorem exists_mem_lambdaSet_psiSet_of_le [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B C : Subgroup G} (hB : B ∈ R) (hA : A ∈ lambdaSet R B) (hC : C ∈ R)
    (hAC : Opposite A C) :
    ∃ B₀ ∈ R, B₀ ≤ A ⊔ B ∧ B₀ ∈ lambdaSet R A ∧ B₀ ∈ psiSet R C ∧ A ⊔ B₀ = A ⊔ B := by
  have hAR : A ∈ R := hA.1.1
  have hBl : B ∈ lambdaSet R A := mem_lambdaSet_comm hB hA
  obtain ⟨B₀, ⟨hB₀R, hB₀le, hB₀p⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hAR hC hAC hBl
  have hB₀A : B₀ ≠ A := fun e => Special.not_opposite hR hC hB₀p.2 (by rw [e]; exact hAC.symm)
  have hsup : A ⊔ B₀ = A ⊔ B := sup_eq_of_le_of_commuting hR hiso hAR hB hAR hB₀R hBl.1.2.2
    le_sup_left hB₀le hB₀A.symm
  have hcomm : Commuting (A ⊔ B) (A ⊔ B) :=
    Commuting.sup_left (Commuting.sup_right (hR.commuting_self hAR) hBl.1.2.2)
      (Commuting.sup_right hBl.1.2.2.symm (hR.commuting_self hB))
  exact ⟨B₀, hB₀R, hB₀le, ⟨⟨hB₀R, hB₀A, hcomm.mono le_sup_left hB₀le⟩, hsup ▸ hBl.2⟩, hB₀p,
    hsup⟩

theorem commuting_of_forall_conjSub_eq (hR : IsRootClass R) {L P : Subgroup G} (hL : L ∈ R)
    (hP : P ∈ R) (h : ∀ l ∈ L, conjSub P l = P) (hiso : NoIsolated R) : Commuting L P := by
  by_cases hLP : L = P
  · rw [hLP]
    exact hR.commuting_self hP
  rcases hR.rel L hL P hP hLP with hc | hop | hsp
  · exact hc
  · obtain ⟨l, hl, hl1⟩ := hR.exists_ne_one hL
    exact absurd (hop.eq_one_of_conjSub_eq hl (h l hl)) hl1
  · have hle : ⁅L, P⁆ ≤ P := by
      rw [Subgroup.commutator_le]
      intro l hl p hp
      rw [commutatorElement_def]
      refine P.mul_mem ?_ (P.inv_mem hp)
      rw [← h l hl]
      exact conj_mem_conjSub l hp
    have heq : ⁅L, P⁆ = P := by
      by_contra hne
      have := inf_eq_bot hR hiso hsp.1 hP hne
      rw [inf_of_le_left hle] at this
      exact hR.ne_bot _ hsp.1 this
    have := hsp.2.1
    rw [heq] at this
    exact this.symm

end Sec3

open Sec3

theorem line_card_and_transitive [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B : Subgroup G} (hB : B ∈ R) (hA : A ∈ lambdaSet R B) :
    Nat.card {C : Subgroup G // C ∈ R ∧ C ≤ A ⊔ B} = Nat.card A + 1 ∧
      ∃ E ∈ R, ∃ F ∈ R, Opposite E F ∧
        (∀ x ∈ E ⊔ F, conjSub (A ⊔ B) x = A ⊔ B) ∧
        (∀ C ∈ R, C ≤ A ⊔ B → ∀ D ∈ R, D ≤ A ⊔ B → ∃ x ∈ E ⊔ F, conjSub C x = D) ∧
        ∃ B₀ ∈ R, B₀ ≤ A ⊔ B ∧ B₀ ∈ lambdaSet R E ∧ B₀ ∈ psiSet R F ∧
          B₀ ⊔ ⁅F, B₀⁆ = A ⊔ B := by
  have hAR : A ∈ R := hA.1.1
  obtain ⟨C, hC, hAC⟩ := hiso A hAR
  obtain ⟨B₀, hB₀R, hB₀le, hB₀l, hB₀p, hsupB₀⟩ :=
    exists_mem_lambdaSet_psiSet_of_le hR hiso hB hA hC hAC
  obtain ⟨c, hc, hc1⟩ := hR.exists_ne_one hC
  obtain ⟨hEsp, hAE, hB₀El, hEnorm, hEcent⟩ :=
    conjSub_props hR hiso hAR hC hAC hB₀l hB₀p hc hc1
  set E := conjSub B₀ c with hEdef
  have hER : E ∈ R := hR.conjSub_mem hB₀R c
  obtain ⟨D, hD, hB₀D⟩ := hiso B₀ hB₀R
  obtain ⟨A₀, hA₀R, hA₀le, hA₀l, hA₀p, hsupA₀⟩ :=
    exists_mem_lambdaSet_psiSet_of_le hR hiso hAR hB₀l hD hB₀D
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hD
  obtain ⟨hFsp, hB₀F, hA₀Fl, hFnorm, hFcent⟩ :=
    conjSub_props hR hiso hB₀R hD hB₀D hA₀l hA₀p hd hd1
  set F := conjSub A₀ d with hFdef
  have hFR : F ∈ R := hR.conjSub_mem hA₀R d
  have hline : B₀ ⊔ A₀ = A ⊔ B := by rw [hsupA₀, sup_comm, hsupB₀]
  have hline' : A ⊔ B₀ = A ⊔ B := hsupB₀
  have hEB₀ : Commuting E B₀ := hB₀El.1.2.2
  have hFA₀ : Commuting F A₀ := hA₀Fl.1.2.2
  have hEFn : E ⊔ F ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    refine sup_le (le_normalizer_of_conjSub_le fun e he => ?_)
      (le_normalizer_of_conjSub_le fun f hf => ?_)
    · rw [← hline']
      exact hEnorm e he
    · rw [← hline]
      exact hFnorm f hf
  have hA₀le' : A₀ ≤ A ⊔ B₀ := by rw [hline', ← hline]; exact le_sup_right
  have hA₀E_le : ⁅A₀, E⁆ ≤ B₀ := by
    rw [Subgroup.commutator_le]
    intro x hx e he
    have hleAB₀ : B₀ ≤ Subgroup.normalizer (A : Set G) :=
      (commuting_iff_le_centralizer.1 hB₀l.1.2.2).trans (Subgroup.centralizer_le_normalizer _)
    have hx' : x ∈ ((A ⊔ B₀ : Subgroup G) : Set G) := hA₀le' hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left A B₀ hleAB₀] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    dsimp only
    have hbe : Commute b e := (hEB₀ e he b hb).symm
    have e1 : ⁅a * b, e⁆ = ⁅a, e⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc a * b * e * (a * b)⁻¹ * e⁻¹ = a * (b * e) * b⁻¹ * a⁻¹ * e⁻¹ := by group
        _ = a * (e * b) * b⁻¹ * a⁻¹ * e⁻¹ := by rw [hbe.eq]
        _ = a * e * a⁻¹ * e⁻¹ := by group
    rw [e1, ← hAE]
    exact Subgroup.commutator_mem_commutator ha he
  have hA₀E_ne : ⁅A₀, E⁆ ≠ ⊥ := by
    intro hbot
    have h1 : Commuting A₀ E := commuting_iff_commutator_eq_bot.2 hbot
    have h3 : Commuting (B₀ ⊔ A₀) E := Commuting.sup_left hEB₀.symm h1
    have h4 : Commuting A E := h3.mono (by rw [hline]; exact le_sup_left) le_rfl
    exact hEsp.not_commuting hR h4
  have hkey : ⁅⁅A₀, E⁆, F⁆ ≠ ⊥ := by
    intro hbot
    obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA₀E_ne
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    obtain ⟨f, hf, hf1⟩ := hR.exists_ne_one hFR
    have hyf : Commute f y := ((commuting_iff_commutator_eq_bot.2 hbot) y hy f hf).symm
    exact hy1' (eq_one_of_commute_of_special hR hiso hFR hB₀R hFsp.symm hf hf1 (hA₀E_le hy) hyf)
  have hEF_nc : ¬ Commuting E F := by
    intro h
    apply hkey
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [commuting_iff_commutator_eq_bot.1 h, Subgroup.commutator_bot_left]
    · rw [commuting_iff_commutator_eq_bot.1 hFA₀, Subgroup.commutator_bot_left]
  have hEF_ns : ¬ Special R E F := by
    intro hs
    have hLR : ⁅E, F⁆ ∈ R := hs.1
    have hLle : ⁅E, F⁆ ≤ E ⊔ F := by
      rw [Subgroup.commutator_le]
      intro e he f hf
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left he)
        (Subgroup.mem_sup_right hf)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left he)))
        (Subgroup.inv_mem _ (Subgroup.mem_sup_right hf))
    have hLA₀ : Commuting ⁅E, F⁆ A₀ := by
      refine commuting_of_forall_conjSub_eq hR hLR hA₀R (fun l hl => ?_) hiso
      have hA₀n : ⁅E, F⁆ ≤ Subgroup.normalizer (A₀ : Set G) := by
        refine le_normalizer_of_conjSub_le fun l' hl' => ?_
        rintro _ ⟨x, hx, rfl⟩
        change l' * x * l'⁻¹ ∈ A₀
        have hxAB : x ∈ A ⊔ B := (hline ▸ le_sup_right : A₀ ≤ A ⊔ B) hx
        have h1 : l' * x * l'⁻¹ ∈ B₀ ⊔ A₀ := by
          rw [hline, ← conjSub_eq_self_iff.2 (hEFn (hLle hl'))]
          exact conj_mem_conjSub l' hxAB
        refine hFcent _ h1 fun f hf => ?_
        have hlf : Commute f l' := (hs.2.2 l' hl' f hf).symm
        have hxf : Commute f x := hFA₀ f hf x hx
        exact (hlf.mul_right hxf).mul_right hlf.inv_right
      exact conjSub_eq_self_iff.2 (hA₀n hl)
    apply hkey
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · exact commuting_iff_commutator_eq_bot.1 hLA₀
    · rw [commuting_iff_commutator_eq_bot.1 hFA₀, Subgroup.commutator_bot_left]
  have hEF_ne : E ≠ F := fun h => hEF_nc (h ▸ hR.commuting_self hER)
  have hEF : Opposite E F := by
    rcases hR.rel E hER F hFR hEF_ne with h | h | h
    · exact absurd h hEF_nc
    · exact h
    · exact absurd h hEF_ns
  have hB₀Fp : B₀ ∈ psiSet R F := ⟨hB₀R, hFsp.symm⟩
  have hN3 : B₀ ⊔ ⁅F, B₀⁆ = A ⊔ B := by rw [Subgroup.commutator_comm, hB₀F, hline]
  refine ⟨?_, E, hER, F, hFR, hEF, fun x hx => ?_, fun P hP hPle Q hQ hQle => ?_,
    B₀, hB₀R, hB₀le, hB₀El, hB₀Fp, hN3⟩
  · rw [← hline']
    exact card_setOf_mem_le_sup hR hiso hAR hC hAC hB₀l hB₀p
  · rw [← hN3]
    exact conjSub_sup_commutator_eq hR hiso hER hFR hEF hB₀El hB₀Fp hx
  · obtain ⟨p, hp, hp1⟩ := hR.exists_ne_one hP
    obtain ⟨q, hq, hq1⟩ := hR.exists_ne_one hQ
    have hpN : p ∈ B₀ ⊔ ⁅F, B₀⁆ := hN3 ▸ hPle hp
    have hqN : q ∈ B₀ ⊔ ⁅F, B₀⁆ := hN3 ▸ hQle hq
    obtain ⟨x, hx, hxpq⟩ :=
      exists_conj_eq_of_mem_sup hR hiso hER hFR hEF hB₀El hB₀Fp hpN hp1 hqN hq1
    exact ⟨x, hx, eq_of_mem_of_mem hR hiso (hR.conjSub_mem hP x) hQ
      (hxpq ▸ conj_mem_conjSub x hp) hq hq1⟩

end CFSG.Timmesfeld.ARS
