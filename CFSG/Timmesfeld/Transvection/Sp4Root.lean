module

public import CFSG.Timmesfeld.Transvection.Sp4Radical
public import CFSG.Timmesfeld.Transvection.Sp4Frame
public import CFSG.Timmesfeld.Transvection.TriangleCoordsG
public import CFSG.Timmesfeld.Transvection.CommMap

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.NaturalModule
open scoped Matrix

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

@[expose] def commSub (C : Subgroup G) (h : G) : Subgroup G :=
  Subgroup.closure {x | ∃ m ∈ C, x = m * h * m⁻¹ * h⁻¹}

section CommSub

variable {C : Subgroup G} {h : G} (hC : ∀ x ∈ C, ∀ y ∈ C, Commute x y)
  (hh : ∀ x ∈ C, h * x * h⁻¹ ∈ C)
include hC hh

theorem commSub_eq_map : commSub C h = (commMap hC hh).range.map C.subtype := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨commMap hC hh ⟨m, hm⟩, ⟨⟨m, hm⟩, rfl⟩, rfl⟩
  · rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    exact Subgroup.subset_closure ⟨m, m.2, rfl⟩

theorem mem_commSub_iff {x : G} : x ∈ commSub C h ↔ ∃ m ∈ C, x = m * h * m⁻¹ * h⁻¹ := by
  rw [commSub_eq_map hC hh]
  constructor
  · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
    exact ⟨m, m.2, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨_, ⟨⟨m, hm⟩, rfl⟩, rfl⟩

theorem commSub_le : commSub C h ≤ C := by
  intro x hx
  obtain ⟨m, hm, rfl⟩ := (mem_commSub_iff hC hh).1 hx
  rw [show m * h * m⁻¹ * h⁻¹ = m * (h * m⁻¹ * h⁻¹) by group]
  exact C.mul_mem hm (hh _ (C.inv_mem hm))

theorem card_commSub : Nat.card (commSub C h) = Nat.card (commMap hC hh).range := by
  rw [commSub_eq_map hC hh]
  exact Subgroup.card_map_of_injective C.subtype_injective

end CommSub

namespace TriangleSetting

variable {A E B : Subgroup G} {t : G}

theorem graph_le_sup_right (S : TriangleSetting Δ A E B t) : graph A t ≤ A ⊔ B := by
  intro f hf
  obtain ⟨a, ha, rfl⟩ := (mem_graph_iff S.commuting_conjSub).1 hf
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
    (Subgroup.mem_sup_right (S.conjA ▸ conj_mem_conjSub t ha))

namespace Coords

variable {S : TriangleSetting Δ A E B t} (c : S.Coords)

theorem exists_unit_ne_one [Finite G] (hq : 4 ≤ Nat.card A) :
    ∃ μ : (GaloisField 2 c.k)ˣ, μ ≠ 1 := by
  classical
  by_contra hno
  push Not at hno
  have hk0 : c.k ≠ 0 := by
    intro h0
    have := c.card_eq
    rw [h0, pow_zero] at this
    omega
  let _ : Fintype (GaloisField 2 c.k) := Fintype.ofFinite _
  have h2 : Fintype.card (GaloisField 2 c.k)ˣ = 1 := Fintype.card_eq_one_iff.2 ⟨1, hno⟩
  rw [Fintype.card_units] at h2
  have h3 : Fintype.card (GaloisField 2 c.k) = Nat.card A := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 c.k hk0, c.card_eq]
  omega

theorem conjSub_eq_of_mat_eq_diagElt [Finite G] {h : G} (hX : h ∈ A ⊔ E)
    {μ : (GaloisField 2 c.k)ˣ} (hh : c.mat h = diagElt μ) :
    conjSub A h = A ∧ conjSub E h = E := by
  have key : ∀ {P : Subgroup G}, P ≤ A ⊔ E →
      ∀ {U : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 c.k))},
      (∀ {x : G}, x ∈ A ⊔ E → (x ∈ P ↔ c.mat x ∈ U)) →
      diagElt μ ∈ Subgroup.normalizer (U : Set _) → conjSub P h = P := by
    intro P hP U hU hnorm
    have hle : conjSub P h ≤ P := by
      rintro _ ⟨a, ha, rfl⟩
      show h * a * h⁻¹ ∈ P
      have haX : a ∈ A ⊔ E := hP ha
      have hX' : h * a ∈ A ⊔ E := Subgroup.mul_mem _ hX haX
      rw [hU (Subgroup.mul_mem _ hX' (Subgroup.inv_mem _ hX)), c.mat_mul hX'
        (Subgroup.inv_mem _ hX), c.mat_mul hX haX, c.mat_inv hX, hh]
      exact (Subgroup.mem_normalizer_iff.1 hnorm _).1 ((hU haX).1 ha)
    exact Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj h).injective).ge
  exact ⟨key le_sup_left (fun hx => c.mem_A_iff hx) (diagElt_mem_normalizer_lowerUnipotent μ),
    key le_sup_right (fun hx => c.mem_E_iff hx) (diagElt_mem_normalizer_upperUnipotent μ)⟩

theorem vec_conj_diagElt {h : G} (hX : h ∈ A ⊔ E) {μ : (GaloisField 2 c.k)ˣ}
    (hh : c.mat h = diagElt μ) {n : G} (hn : n ∈ corrN A E t) :
    c.vec (h * n * h⁻¹) = ![(μ : GaloisField 2 c.k) * c.vec n 0,
      ((μ⁻¹ : (GaloisField 2 c.k)ˣ) : GaloisField 2 c.k) * c.vec n 1] := by
  rw [c.vec_conj hX hn, hh, diagElt_mulVec]

end Coords

end TriangleSetting

namespace Sp4Frame

variable {A E D E' B : Subgroup G} {t t' : G}

theorem corrL_eq_corrL (F : Sp4Frame Δ A E D E' B) [Finite G] (hpts : PointsDetermined Δ)
    (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B) (S' : TriangleSetting Δ D E' B t')
    (htY' : t' ∈ D ⊔ E' ⊔ B) (hq : 4 ≤ Nat.card A) : corrL A E t = corrL D E' t' := by
  have hqD : 4 ≤ Nat.card D := by rwa [S.cls.root.card_eq F.memD F.memA]
  rw [F.corrL_eq_sup S.cls hpts S htY hq, F.swap.corrL_eq_sup S.cls hpts S' htY' hqD,
    sup_comm D A]

theorem conjSub_corrN_swap (F : Sp4Frame Δ A E D E' B) [Finite G] (hpts : PointsDetermined Δ)
    (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B) (S' : TriangleSetting Δ D E' B t')
    (htY' : t' ∈ D ⊔ E' ⊔ B) (hq : 4 ≤ Nat.card A) {h : G} (hh : h ∈ A ⊔ E)
    (hhA : conjSub A h = A) : conjSub (corrN D E' t') h = corrN D E' t' := by
  have hqD : 4 ≤ Nat.card D := by rwa [S.cls.root.card_eq F.memD F.memA]
  have hcomm : ∀ x ∈ D ⊔ E', Commute h x := fun x hx => F.comm h hh x hx
  have hD : conjSub D h = D :=
    Aux.conjSub_eq_of_commute fun d hd => hcomm d (Subgroup.mem_sup_left hd)
  have hE' : conjSub E' h = E' :=
    Aux.conjSub_eq_of_commute fun e he => hcomm e (Subgroup.mem_sup_right he)
  have S'' := S'.conj h
  rw [hD, hE'] at S''
  have htY'' := TriangleSetting.conj_mem_sup htY' h
  rw [hD, hE'] at htY''
  have hLh : conjSub (corrL A E t) h = corrL A E t :=
    S.conjSub_corrL_of_conjSub_eq (S.fourTerm htY hq) hq hh hhA
  have hLY : corrL A E t ≤ D ⊔ E' ⊔ B := by
    rw [F.corrL_eq_corrL hpts S htY S' htY' hq]
    exact S'.corrL_le_sup
  have hBh : conjSub B h ≤ D ⊔ E' ⊔ B :=
    ((Subgroup.map_mono S.le_corrL_right).trans hLh.le).trans hLY
  have hYle : conjSub (D ⊔ E' ⊔ B) h ≤ D ⊔ E' ⊔ B := by
    rw [conjSub_sup_eq_sup, conjSub_sup_eq_sup, hD, hE']
    exact sup_le le_sup_left hBh
  have hYeq := Subgroup.eq_of_le_of_card_ge hYle
    (Subgroup.card_map_of_injective (MulAut.conj h).injective).ge
  have hY : D ⊔ E' ⊔ B = D ⊔ E' ⊔ conjSub B h := by
    conv_lhs => rw [← hYeq]
    rw [conjSub_sup_eq_sup, conjSub_sup_eq_sup, hD, hE']
  rw [← corrN_conjSub, hD, hE']
  exact (TriangleSetting.corrN_eq_of_sup_eq S' htY' S'' htY'' hqD rfl hY).symm

theorem torus_spec (F : Sp4Frame Δ A E D E' B) [Finite G] (hpts : PointsDetermined Δ)
    (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B) (S' : TriangleSetting Δ D E' B t')
    (htY' : t' ∈ D ⊔ E' ⊔ B) (hq : 4 ≤ Nat.card A) (c : S.Coords) {h : G} (hh : h ∈ A ⊔ E)
    {μ : (GaloisField 2 c.k)ˣ} (hμ : c.mat h = diagElt μ) :
    (∀ x ∈ D ⊔ E', Commute h x) ∧ conjSub A h = A ∧ conjSub E h = E ∧
      conjSub (corrL A E t) h = corrL A E t ∧ conjSub (corrN A E t) h = corrN A E t ∧
      conjSub (corrN D E' t') h = corrN D E' t' := by
  obtain ⟨hA, hE⟩ := c.conjSub_eq_of_mat_eq_diagElt hh hμ
  exact ⟨fun x hx => F.comm h hh x hx, hA, hE,
    S.conjSub_corrL_of_conjSub_eq (S.fourTerm htY hq) hq hh hA, conjSub_corrN hh,
    F.conjSub_corrN_swap hpts S htY S' htY' hq hh hA⟩

theorem torus_spec_swap (F : Sp4Frame Δ A E D E' B) [Finite G] (hpts : PointsDetermined Δ)
    (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B) (S' : TriangleSetting Δ D E' B t')
    (htY' : t' ∈ D ⊔ E' ⊔ B) (hq : 4 ≤ Nat.card A) (c' : S'.Coords) {h : G}
    (hh : h ∈ D ⊔ E') {ν : (GaloisField 2 c'.k)ˣ} (hν : c'.mat h = diagElt ν) :
    (∀ x ∈ A ⊔ E, Commute h x) ∧ conjSub D h = D ∧ conjSub E' h = E' ∧
      conjSub (corrL A E t) h = corrL A E t ∧ conjSub (corrN A E t) h = corrN A E t ∧
      conjSub (corrN D E' t') h = corrN D E' t' := by
  have hqD : 4 ≤ Nat.card D := by rwa [S.cls.root.card_eq F.memD F.memA]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := F.swap.torus_spec hpts S' htY' S htY hqD c' hh hν
  rw [← F.corrL_eq_corrL hpts S htY S' htY' hq] at h4
  exact ⟨h1, h2, h3, h4, h6, h5⟩

theorem commSub_spec (F : Sp4Frame Δ A E D E' B) [Finite G] (hpts : PointsDetermined Δ)
    (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B) (S' : TriangleSetting Δ D E' B t')
    (htY' : t' ∈ D ⊔ E' ⊔ B) (hq : 4 ≤ Nat.card A) (c : S.Coords) {h : G} (hh : h ∈ A ⊔ E)
    {μ : (GaloisField 2 c.k)ˣ} (hμ : c.mat h = diagElt μ) (hμ1 : μ ≠ 1) :
    commSub (corrN A E t ⊓ Subgroup.centralizer (A : Set G)) h =
        corrN A E t ⊓ corrN D E' t' ∧
      Nat.card (commSub (corrN A E t ⊓ Subgroup.centralizer (A : Set G)) h) = Nat.card A := by
  classical
  have hΔ := S.cls
  have hqD : 4 ≤ Nat.card D := by rwa [hΔ.root.card_eq F.memD F.memA]
  obtain ⟨hhA, -⟩ := c.conjSub_eq_of_mat_eq_diagElt hh hμ
  have hDZ : D = corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G) :=
    S.eq_corrN_inf_centralizer htY hq hpts (F.mem_lineOf hΔ hpts) F.commuting_ED.symm
  have hAZ : A = corrN D E' t' ⊓ Subgroup.centralizer ((D ⊔ E' : Subgroup G) : Set G) :=
    S'.eq_corrN_inf_centralizer htY' hqD hpts (F.swap.mem_lineOf hΔ hpts) F.commuting_AE'
  set N := corrN A E t with hN
  set N' := corrN D E' t' with hN'
  set C := N ⊓ Subgroup.centralizer (A : Set G) with hC
  set Z := N ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G) with hZ
  have hCab : ∀ x ∈ C, ∀ y ∈ C, Commute x y := fun x hx y hy =>
    S.commute_of_mem_corrN' htY hq hx.1 hy.1
  have hhinvA : conjSub A h⁻¹ = A := conjSub_inv_eq hhA
  have hCh : ∀ x ∈ C, h * x * h⁻¹ ∈ C := by
    intro x hx
    refine ⟨conj_mem_corrN hh hx.1, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    have ha' : h⁻¹ * a * h ∈ A := by
      have := conj_mem_conjSub h⁻¹ ha
      rwa [hhinvA, inv_inv] at this
    have hc := Subgroup.mem_centralizer_iff.1 hx.2 _ ha'
    calc a * (h * x * h⁻¹) = h * ((h⁻¹ * a * h) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * a * h)) * h⁻¹ := by rw [hc]
      _ = h * x * h⁻¹ * a := by group
  have hvecC : ∀ {m : G}, m ∈ C → c.vec m 0 = 0 := fun hm =>
    (c.commute_A_iff hm.1).1 fun a ha => (Subgroup.mem_centralizer_iff.1 hm.2 a ha).symm
  have hvecm : ∀ {m : G}, m ∈ C → c.vec (m * h * m⁻¹ * h⁻¹) 1 =
      (1 - ((μ⁻¹ : (GaloisField 2 c.k)ˣ) : GaloisField 2 c.k)) * c.vec m 1 := by
    intro m hm
    have hm' : h * m⁻¹ * h⁻¹ ∈ N := conj_mem_corrN hh (Subgroup.inv_mem _ hm.1)
    rw [show m * h * m⁻¹ * h⁻¹ = m * (h * m⁻¹ * h⁻¹) by group, c.vec_mul hm.1 hm',
      c.vec_conj_diagElt hh hμ (Subgroup.inv_mem _ hm.1), c.vec_inv hm.1]
    simp only [Pi.add_apply, Pi.neg_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  have hμ1' : ((μ⁻¹ : (GaloisField 2 c.k)ˣ) : GaloisField 2 c.k) ≠ 1 := by
    intro h1
    apply hμ1
    have := Units.val_eq_one.1 h1
    rwa [inv_eq_one] at this
  have hsub : (1 : GaloisField 2 c.k) - ((μ⁻¹ : (GaloisField 2 c.k)ˣ) : GaloisField 2 c.k) ≠ 0 :=
    sub_ne_zero.2 (Ne.symm hμ1')
  have hkey : ∀ {m : G}, m ∈ C → c.vec (m * h * m⁻¹ * h⁻¹) = 0 → m ∈ Z := by
    intro m hm h0
    have h1 : c.vec m 1 = 0 := by
      have := congrFun h0 1
      simp only [Pi.zero_apply] at this
      rw [hvecm hm] at this
      exact (mul_eq_zero.1 this).resolve_left hsub
    have h2 : c.vec m = 0 := by
      funext i
      fin_cases i
      · exact hvecC hm
      · exact h1
    exact ⟨hm.1, (c.vec_eq_zero_iff hm.1).1 h2⟩
  have hZY : ∀ {z : G}, z ∈ Z → ∀ {y : G}, y ∈ A ⊔ E ⊔ B → Commute z y := fun hz _ hy =>
    S.commute_of_mem_corrN_inf_centralizer htY hq hz hy
  have hZh : ∀ {z : G}, z ∈ Z → Commute z h := fun hz => hZY hz (Subgroup.mem_sup_left hh)
  have hZC : Z ≤ C := fun z hz => ⟨hz.1, Subgroup.mem_centralizer_iff.2 fun a ha =>
    Subgroup.mem_centralizer_iff.1 hz.2 a (Subgroup.mem_sup_left ha)⟩
  have hFC : graph A t ≤ C := fun f hf => ⟨corrM_le_corrN (graph_le_corrM hf),
    Subgroup.mem_centralizer_iff.2 fun a ha => (S.commute_graph_left hf ha).symm.eq⟩
  have hCFZ : C = graph A t ⊔ Z := le_antisymm (fun m hm => S.mem_graph_sup_of_commute htY hq
    hm.1 fun a ha => (Subgroup.mem_centralizer_iff.1 hm.2 a ha).symm) (sup_le hFC hZC)
  have hcardZ : Nat.card Z = Nat.card A := S.card_corrN_inf_centralizer_eq htY hq hpts
  have hcardC : Nat.card C = Nat.card A * Nat.card A := by
    have hFZ : graph A t ⊓ Z = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
      have hx' : x ∈ Z ⊓ (A ⊔ B) := ⟨hx.2, S.graph_le_sup_right hx.1⟩
      rwa [S.corrN_inf_centralizer_inf_sup_eq_bot, Subgroup.mem_bot] at hx'
    have hFZc : Commuting (graph A t) Z := fun f hf z hz => (hZY hz (S.graph_le_sup hf)).symm
    rw [hCFZ, le_antisymm (card_sup_le_of_commuting hFZc) (card_mul_card_le_card_sup hFZ),
      S.card_graph, hcardZ]
  have hker : (commMap hCab hCh).ker = Z.subgroupOf C := by
    ext m
    rw [mem_ker_commMap_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hmh
      refine hkey m.2 ?_
      rw [show (m : G) * h * (m : G)⁻¹ * h⁻¹ = 1 by rw [hmh.eq]; group, c.vec_one]
    · exact fun hmZ => hZh hmZ
  have hcardX : Nat.card (commSub C h) = Nat.card A := by
    have h1 := card_range_commMap_mul hCab hCh
    rw [hker, card_subgroupOf_of_le hZC, hcardZ, hcardC] at h1
    rw [card_commSub hCab hCh]
    exact Nat.eq_of_mul_eq_mul_right (by omega) h1
  have hXC := commSub_le hCab hCh
  have hZX : Z ⊓ commSub C h = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    obtain ⟨m, hm, rfl⟩ := (mem_commSub_iff hCab hCh).1 hx.2
    have hmZ := hkey hm ((c.vec_eq_zero_iff hx.1.1).2 hx.1.2)
    rw [(hZh hmZ).eq]
    group
  have hqL : C ≤ corrL A E t := by
    rw [hCFZ]
    exact sup_le (S.graph_le_sup_right.trans (sup_le Transvection.le_corrL S.le_corrL_right))
      (S.corrN_inf_centralizer_le_corrL htY hq)
  have hLeq := F.corrL_eq_corrL hpts S htY S' htY' hq
  have hN'h := F.conjSub_corrN_swap hpts S htY S' htY' hq hh hhA
  have hDN' : D ≤ Subgroup.normalizer ((N' : Subgroup G) : Set G) := fun d hd =>
    conjSub_eq_self_iff.1 (conjSub_corrN (Subgroup.mem_sup_left hd))
  have hXN' : commSub C h ≤ N' := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := (mem_commSub_iff hCab hCh).1 hx
    have hmL : m ∈ ((D ⊔ N' : Subgroup G) : Set G) :=
      S'.corrL_le_sup_corrN htY' hqD (hLeq ▸ hqL hm)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hDN'] at hmL
    obtain ⟨d, hd, n', hn', hdn⟩ := hmL
    replace hdn : d * n' = m := hdn
    subst hdn
    have hdh : Commute d h := (F.comm h hh d (Subgroup.mem_sup_left hd)).symm
    have h1 : n' * (h * n'⁻¹ * h⁻¹) ∈ N' := by
      have := conj_mem_conjSub h (Subgroup.inv_mem _ hn')
      rw [hN'h] at this
      exact Subgroup.mul_mem _ hn' this
    have e : d * n' * h * (d * n')⁻¹ * h⁻¹ = d * (n' * (h * n'⁻¹ * h⁻¹)) * d⁻¹ := by
      calc d * n' * h * (d * n')⁻¹ * h⁻¹ = d * n' * h * n'⁻¹ * (d⁻¹ * h⁻¹) := by group
        _ = d * n' * h * n'⁻¹ * (h⁻¹ * d⁻¹) := by rw [hdh.inv_inv.eq]
        _ = d * (n' * (h * n'⁻¹ * h⁻¹)) * d⁻¹ := by group
    rw [e]
    exact conj_mem_corrN (Subgroup.mem_sup_left hd) h1
  have hZXc : Commuting Z (commSub C h) := fun z hz x hx => hCab z (hZC hz) x (hXC hx)
  have hCZX : C = Z ⊔ commSub C h := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le hZC hXC) ?_).symm
    rw [le_antisymm (card_sup_le_of_commuting hZXc) (card_mul_card_le_card_sup hZX), hcardZ,
      hcardX, hcardC]
  have hAN' : A ≤ N' := by
    rw [hAZ]
    exact inf_le_left
  refine ⟨le_antisymm (le_inf (hXC.trans inf_le_left) hXN') ?_, hcardX⟩
  intro n hn
  have hnC : n ∈ C := ⟨hn.1, Subgroup.mem_centralizer_iff.2 fun a ha =>
    (S'.commute_of_mem_corrN' htY' hqD hn.2 (hAN' ha)).symm.eq⟩
  rw [hCZX] at hnC
  obtain ⟨z, hz, x, hx, rfl⟩ := mem_sup_of_commuting hZXc hnC
  have hzN' : z ∈ N' := by
    rw [show z = z * x * x⁻¹ by group]
    exact Subgroup.mul_mem _ hn.2 (Subgroup.inv_mem _ (hXN' hx))
  have hz1 : z = 1 := S'.eq_one_of_mem_of_mem_corrN htY' hqD (hDZ ▸ hz) hzN'
  rw [hz1, one_mul]
  exact hx

theorem commSub_eq_inf (F : Sp4Frame Δ A E D E' B) [Finite G] (hpts : PointsDetermined Δ)
    (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B) (S' : TriangleSetting Δ D E' B t')
    (htY' : t' ∈ D ⊔ E' ⊔ B) (hq : 4 ≤ Nat.card A) (c : S.Coords) {h : G} (hh : h ∈ A ⊔ E)
    {μ : (GaloisField 2 c.k)ˣ} (hμ : c.mat h = diagElt μ) (hμ1 : μ ≠ 1) :
    commSub (corrN A E t ⊓ Subgroup.centralizer (A : Set G)) h =
      corrN A E t ⊓ corrN D E' t' :=
  (F.commSub_spec hpts S htY S' htY' hq c hh hμ hμ1).1

theorem commSub_eq_inf_swap (F : Sp4Frame Δ A E D E' B) [Finite G] (hpts : PointsDetermined Δ)
    (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B) (S' : TriangleSetting Δ D E' B t')
    (htY' : t' ∈ D ⊔ E' ⊔ B) (hq : 4 ≤ Nat.card A) (c' : S'.Coords) {h : G}
    (hh : h ∈ D ⊔ E') {ν : (GaloisField 2 c'.k)ˣ} (hν : c'.mat h = diagElt ν) (hν1 : ν ≠ 1) :
    commSub (corrN D E' t' ⊓ Subgroup.centralizer (D : Set G)) h =
      corrN A E t ⊓ corrN D E' t' := by
  have hqD : 4 ≤ Nat.card D := by rwa [S.cls.root.card_eq F.memD F.memA]
  rw [inf_comm (corrN A E t)]
  exact F.swap.commSub_eq_inf hpts S' htY' S htY hqD c' hh hν hν1

theorem card_inf_corrN (F : Sp4Frame Δ A E D E' B) [Finite G] (hpts : PointsDetermined Δ)
    (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B) (S' : TriangleSetting Δ D E' B t')
    (htY' : t' ∈ D ⊔ E' ⊔ B) (hq : 4 ≤ Nat.card A) :
    Nat.card ↥(corrN A E t ⊓ corrN D E' t') = Nat.card A := by
  let c := S.coords htY hq
  obtain ⟨μ, hμ1⟩ := c.exists_unit_ne_one hq
  obtain ⟨h, hh, hμ, -⟩ := c.exists_torus μ
  obtain ⟨heq, hcard⟩ := F.commSub_spec hpts S htY S' htY' hq c hh hμ hμ1
  rw [← heq]
  exact hcard

theorem inf_corrN_le_centralizer (F : Sp4Frame Δ A E D E' B) [Finite G]
    (hpts : PointsDetermined Δ) (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)
    (S' : TriangleSetting Δ D E' B t') (htY' : t' ∈ D ⊔ E' ⊔ B) (hq : 4 ≤ Nat.card A) :
    corrN A E t ⊓ corrN D E' t' ≤
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (D : Set G) := by
  have hqD : 4 ≤ Nat.card D := by rwa [S.cls.root.card_eq F.memD F.memA]
  have hAN' : A ≤ corrN D E' t' := by
    rw [S'.eq_corrN_inf_centralizer htY' hqD hpts (F.swap.mem_lineOf S.cls hpts)
      F.commuting_AE']
    exact inf_le_left
  have hDN : D ≤ corrN A E t := by
    rw [S.eq_corrN_inf_centralizer htY hq hpts (F.mem_lineOf S.cls hpts) F.commuting_ED.symm]
    exact inf_le_left
  intro x hx
  exact ⟨Subgroup.mem_centralizer_iff.2 fun a ha =>
      (S'.commute_of_mem_corrN' htY' hqD hx.2 (hAN' ha)).symm.eq,
    Subgroup.mem_centralizer_iff.2 fun d hd =>
      (S.commute_of_mem_corrN' htY hq hx.1 (hDN hd)).symm.eq⟩

theorem inf_corrN_inf_sup_eq_bot (F : Sp4Frame Δ A E D E' B) [Finite G]
    (hpts : PointsDetermined Δ) (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)
    (S' : TriangleSetting Δ D E' B t') (htY' : t' ∈ D ⊔ E' ⊔ B) (hq : 4 ≤ Nat.card A) :
    (corrN A E t ⊓ corrN D E' t') ⊓ (A ⊔ D) = ⊥ := by
  have hqD : 4 ≤ Nat.card D := by rwa [S.cls.root.card_eq F.memD F.memA]
  have hDN : D ≤ corrN A E t := by
    rw [S.eq_corrN_inf_centralizer htY hq hpts (F.mem_lineOf S.cls hpts) F.commuting_ED.symm]
    exact inf_le_left
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  obtain ⟨a, ha, d, hd, rfl⟩ := mem_sup_of_commuting F.commuting_AD hx.2
  have haN : a ∈ corrN A E t := by
    rw [show a = a * d * d⁻¹ by group]
    exact Subgroup.mul_mem _ hx.1.1 (Subgroup.inv_mem _ (hDN hd))
  have ha1 := S.eq_one_of_mem_of_mem_corrN htY hq ha haN
  subst ha1
  rw [one_mul] at hx ⊢
  exact S'.eq_one_of_mem_of_mem_corrN htY' hqD hd hx.1.2

theorem sup_inf_corrN_eq_corrL (F : Sp4Frame Δ A E D E' B) [Finite G]
    (hpts : PointsDetermined Δ) (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)
    (S' : TriangleSetting Δ D E' B t') (htY' : t' ∈ D ⊔ E' ⊔ B) (hq : 4 ≤ Nat.card A) :
    A ⊔ D ⊔ (corrN A E t ⊓ corrN D E' t') = corrL A E t := by
  have hXL : corrN A E t ⊓ corrN D E' t' ≤ corrL A E t := by
    intro x hx
    have hxC := F.inf_corrN_le_centralizer hpts S htY S' htY' hq hx
    rw [← S.sup_corrN_inf_centralizer_eq htY hq hpts]
    have hm := S.mem_graph_sup_of_commute htY hq hx.1 fun a ha =>
      (Subgroup.mem_centralizer_iff.1 hxC.1 a ha).symm
    exact (sup_le ((S.graph_le_sup_right).trans (sup_le (le_sup_left.trans le_sup_left)
      (le_sup_right.trans le_sup_left))) le_sup_right) hm
  have hDL := F.le_corrL S.cls hpts S htY hq
  refine Subgroup.eq_of_le_of_card_ge (sup_le (sup_le Transvection.le_corrL hDL) hXL) ?_
  have hc : Commuting (A ⊔ D) (corrN A E t ⊓ corrN D E' t') :=
    fun x hx y hy => S.commute_of_mem_corrL' htY hq (sup_le Transvection.le_corrL hDL hx) (hXL hy)
  have h1 := card_mul_card_le_card_sup (H := A ⊔ D) (K := corrN A E t ⊓ corrN D E' t')
    (by rw [inf_comm]; exact F.inf_corrN_inf_sup_eq_bot hpts S htY S' htY' hq)
  have h2 : Nat.card A * Nat.card A ≤ Nat.card ↥(A ⊔ D) := by
    have := card_mul_card_le_card_sup (S.cls.inf_eq_bot S.iso F.memA F.memD F.ne_AD)
    rwa [S.cls.root.card_eq F.memD F.memA] at this
  rw [S.card_corrL htY hq hpts]
  calc Nat.card A ^ 3 = Nat.card A * Nat.card A * Nat.card ↥(corrN A E t ⊓ corrN D E' t') := by
        rw [F.card_inf_corrN hpts S htY S' htY' hq]
        ring
    _ ≤ Nat.card ↥(A ⊔ D) * Nat.card ↥(corrN A E t ⊓ corrN D E' t') :=
        Nat.mul_le_mul_right _ h2
    _ ≤ _ := h1

end Sp4Frame

end CFSG.Timmesfeld.Transvection
