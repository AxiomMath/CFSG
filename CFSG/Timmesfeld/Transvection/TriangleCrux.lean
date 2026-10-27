module

public import CFSG.Timmesfeld.Transvection.TriangleLine
public import CFSG.Timmesfeld.Transvection.LineGroup

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

theorem card_fixedPoints_modEq_two {α : Type*} [Finite α] (σ : α → α)
    (hσ : ∀ x, σ (σ x) = x) : Nat.card α ≡ Nat.card (Function.fixedPoints σ) [MOD 2] := by
  classical
  let _ : Fintype α := Fintype.ofFinite α
  let f : Function.End α := σ
  have hf : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    exact funext hσ
  have h := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

namespace TriangleSetting

variable {A E B : Subgroup G} {t : G} (S : TriangleSetting Δ A E B t)
include S

theorem conjSub_partnerElt_ne [Finite G] {e₀ : G} (he₀ : e₀ ∈ E) (he₀1 : e₀ ≠ 1)
    {C : Subgroup G} (hC : C ∈ Δ) (hCA : Commuting C A) (hCB : Commuting C B)
    (hEC : Opposite E C) : conjSub C (partnerElt A E B e₀) ≠ C := by
  intro hCs
  set s := partnerElt A E B e₀ with hs_def
  have hsE : ∀ y ∈ E, Commute s y := fun y hy => S.commute_partnerElt he₀ he₀1 hy
  have hE := S.tri.memE
  have hee : e₀ * e₀ = 1 := S.cls.mul_self hE he₀
  have heinv : e₀⁻¹ = e₀ := inv_eq_of_mul_eq_one_right hee
  set c := partner E C e₀ with hc_def
  have hc : c ∈ C := partner_mem hEC he₀ he₀1
  have hc1 : c ≠ 1 := partner_ne_one hEC he₀ he₀1
  have hcs : Commute c s := by
    have h := partner_conj_of_conjSub_eq hEC he₀ he₀1 (Aux.conjSub_eq_of_commute hsE) hCs
    rw [(hsE e₀ he₀).eq, mul_inv_cancel_right] at h
    have h' : s * c = c * s := by
      calc s * c = s * c * s⁻¹ * s := by group
        _ = c * s := by rw [← h]
    exact h'.symm
  set a := partner E A e₀ with ha_def
  set b := partner E B e₀ with hb_def
  have ha : a ∈ A := partner_mem S.tri.oppA he₀ he₀1
  have hb : b ∈ B := partner_mem S.tri.oppB he₀ he₀1
  have ha1 : a ≠ 1 := partner_ne_one S.tri.oppA he₀ he₀1
  have hb1 : b ≠ 1 := partner_ne_one S.tri.oppB he₀ he₀1
  have hcf : Commute c (a * b) := (hCA c hc a ha).mul_right (hCB c hc b hb)
  have hs_eq : s = e₀ * (a * b) * e₀ * (a * b) := rfl
  have hcefe : Commute c (e₀ * (a * b) * e₀) := by
    have : e₀ * (a * b) * e₀ = s * (a * b)⁻¹ := by rw [hs_eq]; group
    rw [this]
    exact hcs.mul_right hcf.inv_right
  have hsplit : e₀ * (a * b) * e₀ = (e₀ * a * e₀) * (e₀ * b * e₀) := by
    calc e₀ * (a * b) * e₀ = e₀ * a * (e₀ * e₀) * b * e₀ := by rw [hee]; group
      _ = (e₀ * a * e₀) * (e₀ * b * e₀) := by group
  have hA' : conjSub A e₀ ∈ Δ := S.cls.root.conjSub_mem S.tri.memA e₀
  have hB' : conjSub B e₀ ∈ Δ := S.cls.root.conjSub_mem S.tri.memB e₀
  have hxA : e₀ * a * e₀ ∈ conjSub A e₀ := by
    have := conj_mem_conjSub e₀ ha
    rwa [heinv] at this
  have hyB : e₀ * b * e₀ ∈ conjSub B e₀ := by
    have := conj_mem_conjSub e₀ hb
    rwa [heinv] at this
  have hx1 : e₀ * a * e₀ ≠ 1 := fun h => ha1 (by
    have := conj_eq_one_iff.1 (show e₀ * a * e₀⁻¹ = 1 by rw [heinv]; exact h)
    exact this)
  have hy1 : e₀ * b * e₀ ≠ 1 := fun h => hb1 (by
    have := conj_eq_one_iff.1 (show e₀ * b * e₀⁻¹ = 1 by rw [heinv]; exact h)
    exact this)
  have hAB' : conjSub A e₀ ≠ conjSub B e₀ := fun h => S.tri.ne (conjSub_injective e₀ h)
  have hcAB' : Commuting (conjSub A e₀) (conjSub B e₀) := S.tri.comm.conjSub e₀
  have hcx : Commute c (e₀ * a * e₀) :=
    ((commute_mul_iff S.cls S.iso hC hA' hB' hAB' hcAB' hc hc1 hxA hx1 hyB hy1).1
      (hsplit ▸ hcefe)).1
  have hbraid := partner_braid S.cls hE S.tri.oppA he₀ he₀1
  have haa : a * a = 1 := S.cls.mul_self S.tri.memA ha
  have he₀eq : e₀ = a * (e₀ * a * e₀) * a := by
    rw [hbraid]
    calc e₀ = (a * a) * e₀ * (a * a) := by rw [haa, one_mul, mul_one]
      _ = a * (a * e₀ * a) * a := by group
  have hce : Commute c e₀ := by
    rw [he₀eq]
    exact ((hCA c hc a ha).mul_right hcx).mul_right (hCA c hc a ha)
  have hbraid' := partner_braid S.cls hE hEC he₀ he₀1
  have hcc : c * c = 1 := S.cls.mul_self hC hc
  have hceq : c = e₀ := by
    have h1 : e₀ * c * e₀ = c := by rw [hce.symm.eq, mul_assoc, hee, mul_one]
    have h2 : c * e₀ * c = e₀ := by rw [hce.eq, mul_assoc, hcc, mul_one]
    rw [← h1, hbraid', h2]
  exact hEC.ne (S.cls.eq_of_mem_of_mem S.iso hE hC he₀ (hceq ▸ hc) he₀1)

end TriangleSetting

theorem conjSub_sup_eq_sup (P Q : Subgroup G) (g : G) :
    conjSub (P ⊔ Q) g = conjSub P g ⊔ conjSub Q g :=
  Subgroup.map_sup P Q _

theorem commute_of_mem_sup_of_commute {x : G} {P Q : Subgroup G} (hP : ∀ y ∈ P, Commute x y)
    (hQ : ∀ y ∈ Q, Commute x y) {y : G} (hy : y ∈ P ⊔ Q) : Commute x y := by
  have hle : P ⊔ Q ≤ Subgroup.centralizer {x} := sup_le
    (fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hP y hy).eq.symm)
    (fun y hy => Subgroup.mem_centralizer_singleton_iff.2 (hQ y hy).eq.symm)
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

namespace TriangleSetting

variable {A E B : Subgroup G} {t : G} (S : TriangleSetting Δ A E B t) (htY : t ∈ A ⊔ E ⊔ B)
include S htY

theorem mem_lineOf_of_le_corrL [Finite G] (hq : 4 ≤ Nat.card A) (hpts : PointsDetermined Δ)
    {C : Subgroup G} (hC : C ∈ Δ) (hCL : C ≤ corrL A E t) : C ∈ lineOf Δ A B := by
  refine ⟨hC, fun W hW hWA hWB => ?_⟩
  have hWL : corrL A E t ≤ Subgroup.centralizer (W : Set G) := by
    rw [S.corrL_eq_iSup htY hq]
    exact iSup₂_le fun n hn => commuting_iff_le_centralizer.1
      ((S.conjSub_corrN_mem_lineOf htY hq hpts hn).2 W hW hWA hWB)
  exact commuting_iff_le_centralizer.2 (hCL.trans hWL)

omit htY in
theorem eq_of_mem_lineOf_of_commuting [Finite G] (hpts : PointsDetermined Δ)
    {C D : Subgroup G} (hC : C ∈ lineOf Δ A B) (hD : D ∈ lineOf Δ A B) (hCE : Commuting C E)
    (hDE : Commuting D E) : C = D := by
  by_contra hCD
  exact S.tri.oppA.not_commuting (S.cls.root.ne_bot E S.tri.memE)
    (commuting_of_commuting_of_mem_lineOf S.cls hpts S.tri.memA S.tri.memB S.tri.ne S.tri.comm
      hC hD hCD (left_mem_lineOf S.tri.memA) S.tri.memE hCE.symm hDE.symm)

theorem card_members_corrL_modEq [Finite G] (hq : 4 ≤ Nat.card A) (hpts : PointsDetermined Δ) :
    Nat.card {C : Subgroup G // C ∈ Δ ∧ C ≤ corrL A E t} ≡ 1 [MOD 2] := by
  classical
  have hΔ := S.cls
  have hiso := S.iso
  obtain ⟨e₀, he₀, he₀1⟩ := hΔ.root.exists_ne_one S.tri.memE
  have hsB : conjSub A (partnerElt A E B e₀) = B := S.conjSub_partnerElt he₀ he₀1
  have hss : partnerElt A E B e₀ * partnerElt A E B e₀ = 1 := S.partnerElt_mul_self he₀ he₀1
  have hsBA : conjSub B (partnerElt A E B e₀) = A :=
    Aux.conjSub_eq_of_conjSub_eq_of_mul_self hss hsB
  obtain ⟨E', hE', hE'A, hE'B⟩ : ∃ E' ∈ Δ, Commuting E' A ∧ Opposite E' B := by
    by_contra hno
    push Not at hno
    apply S.tri.ne
    refine hpts A S.tri.memA B S.tri.memB fun C hC => ⟨fun hAC => ?_, fun hBC => ?_⟩
    · by_contra hBC
      have hCB : C ≠ B := fun h => hBC (by rw [h]; exact hΔ.root.commuting_self S.tri.memB)
      rcases hΔ.commuting_or_opposite hC S.tri.memB hCB with h | h
      · exact hBC h.symm
      · exact hno C hC hAC.symm h
    · by_contra hAC
      have hC' := hΔ.root.conjSub_mem hC (partnerElt A E B e₀)
      have h1 : Commuting A (conjSub C (partnerElt A E B e₀)) := by
        have h1' := hBC.conjSub (partnerElt A E B e₀)
        rwa [hsBA] at h1'
      have h2 : ¬ Commuting B (conjSub C (partnerElt A E B e₀)) := by
        intro h
        apply hAC
        have h' := h.conjSub (partnerElt A E B e₀)
        rwa [hsBA, ← conjSub_mul, hss, conjSub_one] at h'
      have hCB : conjSub C (partnerElt A E B e₀) ≠ B := fun h =>
        h2 (by rw [h]; exact hΔ.root.commuting_self S.tri.memB)
      rcases hΔ.commuting_or_opposite hC' S.tri.memB hCB with h | h
      · exact h2 h.symm
      · exact hno _ hC' h1.symm h
  obtain ⟨n₀, hn₀, hn₀A, hn₀B⟩ := S.exists_conjSub_ne htY hq
  have hB'Δ : conjSub A n₀ ∈ Δ := hΔ.root.conjSub_mem S.tri.memA n₀
  have hB'L : conjSub A n₀ ≤ corrL A E t := S.conjSub_le_corrL htY hq hn₀
  have hB'l := S.conjSub_corrN_mem_lineOf htY hq hpts hn₀
  have hcBB' : Commuting B (conjSub A n₀) :=
    S.commuting_of_le_corrL htY hq S.le_corrL_right hB'L
  have huniq' : ∀ C ∈ lineOf Δ A B, Commuting E' C → C = A := by
    intro C hC hE'C
    by_contra hCA
    exact hE'B.not_commuting (hΔ.root.ne_bot E' hE')
      (commuting_of_commuting_of_mem_lineOf hΔ hpts S.tri.memA S.tri.memB S.tri.ne S.tri.comm
        hC (left_mem_lineOf S.tri.memA) hCA (right_mem_lineOf S.tri.memB) hE' hE'C hE'A)
  have hE'B' : Opposite E' (conjSub A n₀) := by
    have hne : E' ≠ conjSub A n₀ := fun h => hE'B.not_commuting (hΔ.root.ne_bot E' hE')
      (h ▸ hcBB'.symm)
    rcases hΔ.commuting_or_opposite hE' hB'Δ hne with h | h
    · exact absurd (huniq' _ hB'l h) hn₀A
    · exact h
  have hT' : IsTriangle Δ B E' (conjSub A n₀) :=
    ⟨S.tri.memB, hE', hB'Δ, Ne.symm hn₀B, hcBB', hE'B, hE'B'⟩
  obtain ⟨t', -, S'⟩ := exists_triangleSetting hΔ hiso hT'
  obtain ⟨e', he', he'1⟩ := hΔ.root.exists_ne_one hE'
  have hs'B : conjSub B (partnerElt B E' (conjSub A n₀) e') = conjSub A n₀ :=
    S'.conjSub_partnerElt he' he'1
  have hs's' : partnerElt B E' (conjSub A n₀) e' * partnerElt B E' (conjSub A n₀) e' = 1 :=
    S'.partnerElt_mul_self he' he'1
  have hs'B' : conjSub (conjSub A n₀) (partnerElt B E' (conjSub A n₀) e') = B :=
    Aux.conjSub_eq_of_conjSub_eq_of_mul_self hs's' hs'B
  have hs'E' : conjSub E' (partnerElt B E' (conjSub A n₀) e') = E' :=
    Aux.conjSub_eq_of_commute fun _ hy => S'.commute_partnerElt he' he'1 hy
  have hAs' : conjSub A (partnerElt B E' (conjSub A n₀) e') = A := by
    have hlBB' := lineOf_eq_of_mem hΔ hpts S.tri.memA S.tri.memB S.tri.ne S.tri.comm
      (right_mem_lineOf S.tri.memB) hB'l (Ne.symm hn₀B)
    have hAl' : A ∈ lineOf Δ B (conjSub A n₀) := by
      rw [hlBB']
      exact left_mem_lineOf S.tri.memA
    have h1 := conjSub_mem_lineOf_conjSub hΔ.root hAl' (partnerElt B E' (conjSub A n₀) e')
    rw [hs'B, hs'B', lineOf_comm, hlBB'] at h1
    refine huniq' _ h1 ?_
    have h2 := hE'A.conjSub (partnerElt B E' (conjSub A n₀) e')
    rwa [hs'E'] at h2
  have hLeq := S.sup_conjSub_eq htY hq hpts hn₀ hn₀A hn₀B
  have hs'L : conjSub (corrL A E t) (partnerElt B E' (conjSub A n₀) e') = corrL A E t := by
    rw [← hLeq, conjSub_sup_eq_sup, conjSub_sup_eq_sup, hAs', hs'B, hs'B', sup_right_comm]
  let σ' : {C : Subgroup G // C ∈ Δ ∧ C ≤ corrL A E t} →
      {C : Subgroup G // C ∈ Δ ∧ C ≤ corrL A E t} := fun C =>
    ⟨conjSub C.1 (partnerElt B E' (conjSub A n₀) e'), hΔ.root.conjSub_mem C.2.1 _,
      (Subgroup.map_mono C.2.2).trans hs'L.le⟩
  have hσ' : ∀ C, σ' (σ' C) = C := fun C => Subtype.ext (by
    show conjSub (conjSub C.1 (partnerElt B E' (conjSub A n₀) e'))
      (partnerElt B E' (conjSub A n₀) e') = C.1
    rw [← conjSub_mul, hs's', conjSub_one])
  have hfixσ' : ∀ C, σ' C = C → C.1 = A := by
    intro C hC
    have hCs : conjSub C.1 (partnerElt B E' (conjSub A n₀) e') = C.1 := congrArg Subtype.val hC
    have hCB : Commuting C.1 B := S.commuting_of_le_corrL htY hq C.2.2 S.le_corrL_right
    have hCB' : Commuting C.1 (conjSub A n₀) := S.commuting_of_le_corrL htY hq C.2.2 hB'L
    have hCE' : Commuting C.1 E' := by
      have hne : C.1 ≠ E' := fun h => hE'B.not_commuting (hΔ.root.ne_bot E' hE') (h ▸ hCB)
      rcases hΔ.commuting_or_opposite C.2.1 hE' hne with h | h
      · exact h
      · exact absurd hCs (S'.conjSub_partnerElt_ne he' he'1 C.2.1 hCB hCB' h.symm)
    exact huniq' _ (S.mem_lineOf_of_le_corrL htY hq hpts C.2.1 C.2.2) hCE'.symm
  have hpar' := card_fixedPoints_modEq_two σ' hσ'
  have hfix' : Nat.card (Function.fixedPoints σ') = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨⟨A, S.tri.memA, le_corrL⟩, Subtype.ext hAs'⟩, fun C => ?_⟩
    exact Subtype.ext (Subtype.ext ((hfixσ' C.1 C.2)))
  rwa [hfix'] at hpar'

theorem le_corrL_of_mem_lineOf [Finite G] (hq : 4 ≤ Nat.card A) (hpts : PointsDetermined Δ)
    {D : Subgroup G} (hD : D ∈ lineOf Δ A B) (hDE : Commuting D E) : D ≤ corrL A E t := by
  classical
  have hΔ := S.cls
  have hEne : E ≠ ⊥ := hΔ.root.ne_bot E S.tri.memE
  obtain ⟨e₀, he₀, he₀1⟩ := hΔ.root.exists_ne_one S.tri.memE
  have hsN : partnerElt A E B e₀ ∈ corrN A E t :=
    corrM_le_corrN (S.partnerElt_mem_corrM he₀ he₀1)
  have hss : partnerElt A E B e₀ * partnerElt A E B e₀ = 1 := S.partnerElt_mul_self he₀ he₀1
  have hsL : conjSub (corrL A E t) (partnerElt A E B e₀) = corrL A E t :=
    S.conjSub_corrL_of_mem_corrN (S.fourTerm htY hq) hq hsN
  let σ : {C : Subgroup G // C ∈ Δ ∧ C ≤ corrL A E t} →
      {C : Subgroup G // C ∈ Δ ∧ C ≤ corrL A E t} := fun C =>
    ⟨conjSub C.1 (partnerElt A E B e₀), hΔ.root.conjSub_mem C.2.1 _,
      (Subgroup.map_mono C.2.2).trans hsL.le⟩
  have hσ : ∀ C, σ (σ C) = C := fun C => Subtype.ext (by
    show conjSub (conjSub C.1 (partnerElt A E B e₀)) (partnerElt A E B e₀) = C.1
    rw [← conjSub_mul, hss, conjSub_one])
  have hfixσ : ∀ C, σ C = C → C.1 = D := by
    intro C hC
    have hCs : conjSub C.1 (partnerElt A E B e₀) = C.1 := congrArg Subtype.val hC
    have hCA : Commuting C.1 A := S.commuting_of_le_corrL htY hq C.2.2 le_corrL
    have hCB : Commuting C.1 B := S.commuting_of_le_corrL htY hq C.2.2 S.le_corrL_right
    have hCE : Commuting C.1 E := by
      have hne : C.1 ≠ E := fun h => S.tri.oppA.not_commuting hEne (h ▸ hCA)
      rcases hΔ.commuting_or_opposite C.2.1 S.tri.memE hne with h | h
      · exact h
      · exact absurd hCs (S.conjSub_partnerElt_ne he₀ he₀1 C.2.1 hCA hCB h.symm)
    exact S.eq_of_mem_lineOf_of_commuting hpts
      (S.mem_lineOf_of_le_corrL htY hq hpts C.2.1 C.2.2) hD hCE hDE
  have hpar := card_fixedPoints_modEq_two σ hσ
  by_contra hDL
  have hfix0 : Nat.card (Function.fixedPoints σ) = 0 := by
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨C, hC⟩
    exact hDL (hfixσ C hC ▸ C.2.2)
  rw [hfix0] at hpar
  exact absurd ((S.card_members_corrL_modEq htY hq hpts).symm.trans hpar) (by decide)

theorem le_sup_of_mem_lineOf [Finite G] (hq : 4 ≤ Nat.card A) (hpts : PointsDetermined Δ)
    {D : Subgroup G} (hD : D ∈ lineOf Δ A B) (hDE : Commuting D E) : D ≤ A ⊔ E ⊔ B :=
  (S.le_corrL_of_mem_lineOf htY hq hpts hD hDE).trans S.corrL_le_sup

theorem commute_of_mem_corrN_inf_centralizer [Finite G] (hq : 4 ≤ Nat.card A) {z : G}
    (hz : z ∈ corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G)) {y : G}
    (hy : y ∈ A ⊔ E ⊔ B) : Commute z y := by
  obtain ⟨e₀, he₀, he₀1⟩ := S.cls.root.exists_ne_one S.tri.memE
  have hsN : partnerElt A E B e₀ ∈ corrN A E t :=
    corrM_le_corrN (S.partnerElt_mem_corrM he₀ he₀1)
  have hzX : ∀ y ∈ A ⊔ E, Commute z y := fun y hy =>
    (Subgroup.mem_centralizer_iff.1 hz.2 y hy).symm
  refine commute_of_mem_sup_of_commute hzX (fun b hb => ?_) hy
  have hb' : b ∈ conjSub A (partnerElt A E B e₀) := by
    rw [S.conjSub_partnerElt he₀ he₀1]
    exact hb
  obtain ⟨a, ha, rfl⟩ := mem_conjSub_iff.1 hb'
  have hzs : Commute z (partnerElt A E B e₀) := S.commute_of_mem_corrN' htY hq hz.1 hsN
  exact (hzs.mul_right (hzX a (Subgroup.mem_sup_left ha))).mul_right hzs.inv_right

theorem corrN_inf_centralizer_le_corrL [Finite G] (hq : 4 ≤ Nat.card A) :
    corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G) ≤ corrL A E t := by
  have h4 := S.fourTerm htY hq
  obtain ⟨w, hw, hwE⟩ := S.exists_conjSub_eq_E
  intro z hz
  have hzN := hz.1
  have hzX : ∀ y ∈ A ⊔ E, Commute z y := fun y hy =>
    (Subgroup.mem_centralizer_iff.1 hz.2 y hy).symm
  rw [S.corrN_eq_sup h4 hq hw hwE] at hzN
  have hc : Commuting (corrN A E t ⊓ corrL A E t) (corrN A E t ⊓ conjSub (corrL A E t) w) :=
    fun x hx y hy => S.commute_of_mem_corrN' htY hq hx.1 hy.1
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_sup_of_commuting hc hzN
  have hEL : E ≤ conjSub (corrL A E t) w := by
    intro e he
    rw [← hwE] at he
    exact Subgroup.map_mono le_corrL he
  have huA : ∀ a ∈ A, Commute u a := fun a ha => S.commute_of_mem_corrL h4 hu.2 (le_corrL ha)
  have hvE : ∀ e ∈ E, Commute v e := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := mem_conjSub_iff.1 hv.2
    obtain ⟨y, hy, hey⟩ := mem_conjSub_iff.1 (hEL he)
    rw [hey]
    exact (S.commute_of_mem_corrL h4 hx hy).map (MulAut.conj w).toMonoidHom
  have huE : ∀ e ∈ E, Commute u e := fun e he => by
    have h1 := hzX e (Subgroup.mem_sup_right he)
    rw [show u = u * v * v⁻¹ by group]
    exact h1.mul_left (hvE e he).inv_left
  have huw : Commute u w := commute_of_mem_sup_of_commute huA huE hw
  have hvw : Commute v w := by
    rw [show v = u⁻¹ * (u * v) by group]
    exact huw.inv_left.mul_left (hzX w hw)
  obtain ⟨x, hx, hxv⟩ := mem_conjSub_iff.1 hv.2
  have hxv' : x = v := by
    rw [show x = w⁻¹ * v * w by rw [hxv]; group, mul_assoc, hvw.eq, ← mul_assoc,
      inv_mul_cancel, one_mul]
  exact Subgroup.mul_mem _ hu.2 (hxv' ▸ hx)

omit htY in
theorem corrN_inf_centralizer_inf_sup_eq_bot [Finite G] :
    (corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G)) ⊓ (A ⊔ B) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commuting S.tri.comm hx.2
  have hxE : ∀ e ∈ E, Commute e (a * b) := fun e he =>
    Subgroup.mem_centralizer_iff.1 hx.1.2 e (Subgroup.mem_sup_right he)
  obtain ⟨e, he, he1⟩ := S.cls.root.exists_ne_one S.tri.memE
  have hEne : E ≠ ⊥ := S.cls.root.ne_bot E S.tri.memE
  by_cases ha1 : a = 1
  · subst ha1
    rw [one_mul] at hxE ⊢
    by_contra hb1
    exact S.tri.oppB.not_commuting hEne
      (S.cls.commuting_of_commute S.iso S.tri.memE S.tri.memB he he1 hb hb1 (hxE e he))
  by_cases hb1 : b = 1
  · subst hb1
    rw [mul_one] at hxE
    exact absurd (S.cls.commuting_of_commute S.iso S.tri.memE S.tri.memA he he1 ha ha1
      (hxE e he)) (S.tri.oppA.not_commuting hEne)
  exact absurd (S.cls.commuting_of_commute S.iso S.tri.memE S.tri.memA he he1 ha ha1
    ((commute_mul_iff S.cls S.iso S.tri.memE S.tri.memA S.tri.memB S.tri.ne S.tri.comm he he1
      ha ha1 hb hb1).1 (hxE e he)).1) (S.tri.oppA.not_commuting hEne)

theorem card_corrN_inf_centralizer_le [Finite G] (hq : 4 ≤ Nat.card A)
    (hpts : PointsDetermined Δ) :
    Nat.card ↥(corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G)) ≤
      Nat.card A := by
  have h1 := card_mul_card_le_card_sup S.corrN_inf_centralizer_inf_sup_eq_bot
  have h2 : Nat.card ↥((corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G)) ⊔
      (A ⊔ B)) ≤ Nat.card A ^ 3 := by
    rw [← S.card_corrL htY hq hpts]
    exact Subgroup.card_le_of_le (sup_le (S.corrN_inf_centralizer_le_corrL htY hq)
      (sup_le le_corrL S.le_corrL_right))
  have h3 : Nat.card A * Nat.card A ≤ Nat.card ↥(A ⊔ B) := by
    have := card_mul_card_le_card_sup (S.cls.inf_eq_bot S.iso S.tri.memA S.tri.memB S.tri.ne)
    rwa [S.cls.root.card_eq S.tri.memB S.tri.memA] at this
  have hpos : 0 < Nat.card A * Nat.card A := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc Nat.card ↥(corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G)) *
        (Nat.card A * Nat.card A) ≤ Nat.card ↥(corrN A E t ⊓
          Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G)) * Nat.card ↥(A ⊔ B) :=
        Nat.mul_le_mul_left _ h3
    _ ≤ Nat.card A ^ 3 := h1.trans h2
    _ = Nat.card A * (Nat.card A * Nat.card A) := by ring

theorem corrL_le_sup_corrN [Finite G] (hq : 4 ≤ Nat.card A) :
    corrL A E t ≤ A ⊔ corrN A E t := by
  rw [S.corrL_eq_iSup htY hq]
  refine iSup₂_le fun n hn => ?_
  rintro _ ⟨a, ha, rfl⟩
  show n * a * n⁻¹ ∈ A ⊔ corrN A E t
  have h1 : a⁻¹ * n * a ∈ corrN A E t := by
    have := conj_mem_corrN (t := t) (Subgroup.inv_mem _ (Subgroup.mem_sup_left ha)) hn
    rwa [inv_inv] at this
  rw [show n * a * n⁻¹ = a * (a⁻¹ * n * a * n⁻¹) by group]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
    (Subgroup.mem_sup_right (Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hn)))

theorem eq_corrN_inf_centralizer [Finite G] (hq : 4 ≤ Nat.card A) (hpts : PointsDetermined Δ)
    {D : Subgroup G} (hD : D ∈ lineOf Δ A B) (hDE : Commuting D E) :
    D = corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G) := by
  have hDL := S.le_corrL_of_mem_lineOf htY hq hpts hD hDE
  obtain ⟨hAD, hBD⟩ := commuting_of_mem_lineOf' S.cls S.tri.memA S.tri.memB S.tri.comm hD
  have hDX : ∀ d ∈ D, ∀ y ∈ A ⊔ E, Commute d y := fun d hd y hy =>
    commute_of_mem_sup_of_commute (fun a ha => (hAD a ha d hd).symm) (fun e he => hDE d hd e he)
      hy
  have hDY : ∀ d ∈ D, ∀ y ∈ A ⊔ E ⊔ B, Commute d y := fun d hd y hy =>
    commute_of_mem_sup_of_commute (hDX d hd) (fun b hb => (hBD b hb d hd).symm) hy
  obtain ⟨e₀, he₀, he₀1⟩ := S.cls.root.exists_ne_one S.tri.memE
  have hsN : partnerElt A E B e₀ ∈ corrN A E t :=
    corrM_le_corrN (S.partnerElt_mem_corrM he₀ he₀1)
  have hle : D ≤ corrN A E t ⊓ Subgroup.centralizer ((A ⊔ E : Subgroup G) : Set G) := by
    intro d hd
    have hAN : A ≤ Subgroup.normalizer ((corrN A E t : Subgroup G) : Set G) := fun a ha =>
      conjSub_eq_self_iff.1 (conjSub_corrN (Subgroup.mem_sup_left ha))
    have hdAN : d ∈ ((A ⊔ corrN A E t : Subgroup G) : Set G) :=
      S.corrL_le_sup_corrN htY hq (hDL hd)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A _ hAN] at hdAN
    obtain ⟨a, ha, n, hn, hdan⟩ := hdAN
    obtain rfl : a * n = d := hdan
    have hds : Commute (a * n) (partnerElt A E B e₀) :=
      hDY _ hd _ (S.corrN_le_sup hsN)
    have hns : Commute n (partnerElt A E B e₀) := S.commute_of_mem_corrN' htY hq hn hsN
    have has : Commute a (partnerElt A E B e₀) := by
      rw [show a = a * n * n⁻¹ by group]
      exact hds.mul_left hns.inv_left
    have ha1 : a = 1 := by
      have hb := conj_mem_conjSub (partnerElt A E B e₀) ha
      rw [S.conjSub_partnerElt he₀ he₀1, has.symm.eq, mul_inv_cancel_right] at hb
      have hab : a ∈ A ⊓ B := ⟨ha, hb⟩
      rwa [S.cls.inf_eq_bot S.iso S.tri.memA S.tri.memB S.tri.ne, Subgroup.mem_bot] at hab
    subst ha1
    rw [one_mul] at hd ⊢
    exact ⟨hn, Subgroup.mem_centralizer_iff.2 fun y hy => (hDX n hd y hy).eq.symm⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [S.cls.root.card_eq hD.1 S.tri.memA]
  exact S.card_corrN_inf_centralizer_le htY hq hpts

end TriangleSetting

end CFSG.Timmesfeld.Transvection
