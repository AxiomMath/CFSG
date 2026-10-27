module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityPairAB
public import CFSG.RankThree.PartTwo.Sec4.E27.D4Shape
public import CFSG.RankThree.PartTwo.Sec4.E27.FixG2
public import CFSG.RankThree.PartTwo.Sec4.E27.D4TwoLines

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.Seitz CFSG.Open TauCeti
open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec11

namespace CFSG.RankThree.PartTwo.Sec4.E27

section TypeI


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem range_trialityG2Incl_eq_Gsub (hK : ringChar X = 2) :
    (KFacts.trialityG2Incl σ hK).range = Gsub σ := by
  ext g
  rw [KFacts.mem_range_trialityG2Incl_iff σ hK]
  rfl

noncomputable def gsubEquiv (hK : ringChar X = 2) :
    adjointGroup Tag.G2 (fixSubfield σ) ≃* Gsub σ :=
  (MonoidHom.ofInjective (KFacts.trialityG2Incl_injective σ hK)).trans
    (MulEquiv.subgroupCongr (range_trialityG2Incl_eq_Gsub hK))

theorem gsub_plane_closure (P : D4Par n X σ) (hn : 2 ≤ n) {Q : Subgroup (C0 σ)}
    (hQG : Q ≤ Gsub σ) (hQ : IsElemAbelian 3 Q) (hQc : Nat.card Q = 3 ^ 2) :
    Gsub σ ≤ Subgroup.closure {x : C0 σ | x ∈ Gsub σ ∧ ∃ b ∈ Q, b ≠ 1 ∧ x * b = b * x} := by
  classical
  haveI := P.charP
  haveI := P.charP_fix
  haveI : Finite (fixSubfield σ) := Nat.finite_of_card_ne_zero (by rw [P.card_fix]; positivity)
  have hK : ringChar X = 2 := ringChar.eq X 2
  have hmk : Nat.card (fixSubfield σ) = 2 ^ n := P.card_fix
  let q0 : PrimePower := ⟨2, n, Nat.prime_two, by omega⟩
  have hq0 : q0.card = Nat.card (fixSubfield σ) := by
    rw [PrimePower.card_def, hmk]
  have hv : (LieTypeIndex.G2 q0).Valid := by
    refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
    · have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      simp only [LieTypeIndex.inStandardRange_iff]
      omega
    · simp [LieTypeIndex.isDuplicateRepresentative_iff]
  let ε := (gsubEquiv (σ := σ) hK).symm
  refine le_closure_centralizers_of_equiv hQG ε ?_
  refine g2_plane_closure q0 rfl hv hq0.symm _ ?_ ?_
  · exact CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hQ _) _
  · rw [Subgroup.card_map_of_injective ε.injective]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQG).toEquiv, hQc]

theorem stepA_G (P : D4Par n X σ) (hn : 2 ≤ n) {E : Subgroup (MulAut (C0 σ))}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 27) (hτ : tauAut σ ∈ E) :
    Gsub σ ≤ Subgroup.closure {l | l ∈ Gsub σ ∧
      ∃ x ∈ E, x ∉ Subgroup.zpowers (tauAut σ) ∧ x l = l} := by
  have hI9 := card_innerPart_eq σ n P.one_le P.card P.frob hE hcard
  have hIab := innerPart_isElemAbelian σ n P.one_le P.card P.frob hE
  have hinj := conj_injective_C0 σ n P.one_le P.card P.frob
  have hIG : innerPart σ E ≤ Gsub σ := by
    intro x hx
    have hcomm : MulAut.conj x * tauAut σ = tauAut σ * MulAut.conj x :=
      comm_of_isElemAbelian hE hx hτ
    show tauAut σ x = x
    have h1 := aut_conj_conj (tauAut σ) x
    have h2 : tauAut σ * MulAut.conj x * (tauAut σ)⁻¹ = MulAut.conj x := by
      rw [← hcomm]; group
    exact hinj (h1.symm.trans h2)
  refine (gsub_plane_closure P hn hIG hIab hI9).trans (Subgroup.closure_mono ?_)
  rintro l ⟨hl, b, hb, hb1, hlb⟩
  refine ⟨hl, MulAut.conj b, hb, conj_not_mem_zpowers hinj (tauAut_pow_three P)
    (tauAut_not_inner σ n P.one_le P.card P.frob) hb1, ?_⟩
  rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
  exact hlb.symm

theorem typeI_seitzHyperGamma (hgold : CFSG.Goldschmidt.TopStatement) (P : D4Par n X σ)
    (hn : 2 ≤ n) {E : Subgroup (MulAut (C0 σ))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 27) (hτ : tauAut σ ∈ E) {a : C0 σ} (ha : a ∈ A0sub σ)
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hcaE : MulAut.conj a ∈ E) :
    seitzHyperGamma 3 E = ⊤ := by
  obtain ⟨h, hhA, hlang⟩ := exists_lang_A0 P ha ha3
  have hnotfix := lang_ne_fix (tauAut σ) hlang ha1
  have hh0 : h ∉ A0sub σ := fun hh => hnotfix (show tauAut σ h = h from hh.2)
  set f₂ : MulAut (C0 σ) := MulAut.conj a * tauAut σ with hf₂def
  have hf₂E : f₂ ∈ E := E.mul_mem hcaE hτ
  have hτ1 : tauAut σ ≠ 1 := tauAut_ne_one P
  have hf₂1 : f₂ ≠ 1 := by
    intro h1
    have h3 : f₂ h = h := by rw [h1]; rfl
    exact lang_not_comm (tauAut σ) hlang ha1 ((conj_tau_fixed σ a h).mp h3)
  set φ : MulAut (C0 σ) := MulAut.conj h with hφ
  have hcφτ : (MulAut.congr φ) (tauAut σ) = f₂ := by
    refine MulEquiv.ext fun z => ?_
    rw [congr_apply_eq]
    simp only [hf₂def, hφ, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, map_mul,
      map_inv, hlang]
  set E₂ : Subgroup (MulAut (C0 σ)) := E.comap (MulAut.congr φ).toMonoidHom with hE₂
  have hE₂map : E₂.map (MulAut.congr φ).toMonoidHom = E :=
    Subgroup.map_comap_eq_self_of_surjective (MulAut.congr φ).surjective E
  have hE₂ab : IsElemAbelian 3 E₂ :=
    isElemAbelian_comap_of_injective (MulAut.congr φ).toMonoidHom (MulAut.congr φ).injective hE
  have hE₂card : Nat.card E₂ = 27 := by
    calc Nat.card E₂ = Nat.card (E₂.map (MulAut.congr φ).toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulAut.congr φ).injective).symm
      _ = Nat.card E := by rw [hE₂map]
      _ = 27 := hcard
  have hτE₂ : tauAut σ ∈ E₂ := by
    show (MulAut.congr φ) (tauAut σ) ∈ E
    rw [hcφτ]
    exact hf₂E
  have hstep₂ := stepOK_map φ (stepA_G P hn hE₂ab hE₂card hτE₂)
  rw [hE₂map, hcφτ] at hstep₂
  refine seitzHyperGamma_eq_top_of_two_fixed_lines hE hcard hτ hf₂E hτ1 hf₂1
    (L₁ := Gsub σ) (L₂ := (Gsub σ).map φ.toMonoidHom) (fun l hl => hl) ?_
    (stepA_G P hn hE hcard hτ) hstep₂ ?_
  · rintro _ ⟨g, hg, rfl⟩
    have hgτ : tauAut σ g = g := hg
    show f₂ (h * g * h⁻¹) = h * g * h⁻¹
    exact (conj_tau_fixed σ a (h * g * h⁻¹)).mpr (lang_fixed_identity (tauAut σ) hlang hgτ)
  · set S : Subgroup (C0 σ) := Gsub σ ⊔ (Gsub σ).map φ.toMonoidHom with hS
    have hA0S : A0sub σ ≤ S := fun x hx => Subgroup.mem_sup_left hx.2
    have hconj : ∀ y ∈ A0sub σ, h * y * h⁻¹ ∈ S := fun y hy =>
      Subgroup.mem_sup_right ⟨y, hy.2, rfl⟩
    have hAS : Asub σ ≤ S := A_le_of_pair P hn hA0S hhA hh0 hconj
    have hBS : Bsub σ ≤ S := fun b hb => Subgroup.mem_sup_left (Bsub_le_Gsub P hb)
    have hnot : ¬ S ≤ Asub σ ⊔ Bsub σ := fun hle =>
      Gsub_not_le_AB P (le_sup_left.trans hle)
    exact eq_top_of_maximal_pair (ab_maximal hgold P hn) hAS hBS hnot

end TypeI

end CFSG.RankThree.PartTwo.Sec4.E27
