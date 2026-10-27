module

public import CFSG.Timmesfeld.ARS.CaseOADegSUFrame
public import CFSG.Timmesfeld.ARS.CaseOADegMain

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open Matrix CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.Timmesfeld.RankTwo CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.LieEmbed
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.Pres CaseOANSL

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace CaseOADeg

noncomputable abbrev σq (f : ℕ) : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f) :=
  unitaryInvolution (GaloisField 2 (2 * f)) 2 f

namespace DegOA

variable {A A₀ : Subgroup G} {Δ₁ Δ₂ : Set (Subgroup G)} (hD : DegOA R A A₀ Δ₁ Δ₂)
include hD

theorem output_su {f : ℕ} (hf : 1 ≤ f) (hcard : ∀ X ∈ Δ₁, Nat.card X = 2 ^ f)
    (Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 4) →* G)
    (hker : Φ.ker = Subgroup.center _) (hrange : Φ.range = gen Δ₁)
    (hΔ : ∀ X : Subgroup G, X ∈ Δ₁ ↔ ∃ g, X = (conjSub ((Unitary.rootDatum
      (card_galoisField_two_mul hf) 4).rootGroup (unitaryLongRoot 4 (by norm_num))) g).map Φ) :
    Output G R := by
  set K := GaloisField 2 (2 * f)
  set F := GaloisField 2 f
  have hK : Nat.card K = (2 ^ f) ^ 2 := card_galoisField_two_mul hf
  have hσ : ∀ c, σq f (σq f c) = c := unitaryInvolution_involutive hK
  have := hD.hyp.finite
  have hR := hD.hyp.root
  have hiso := hD.hyp.noIsolated
  have hGF : Nat.card F = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨E, C, P, Q, hfr, h0, h1, h2⟩ := hD.exists_subframe
  have hlong : unitaryLongRoot 4 (by norm_num) = (Pi.single (1 : Fin 2) 1 : Fin (4 / 2) → ℤ) := by
    rw [unitaryLongRoot_eq (m := 4) (by decide) (by norm_num)]
    try rfl
  have hΔ₀ : ∀ X : Subgroup G, X ∈ Δ₁ ↔ ∃ g,
      X = (conjSub (Unitary.rootGroup (σq f) hσ 4
      (Pi.single (1 : Fin 2) 1)) g).map Φ := by
    intro X
    rw [hΔ X, hlong]
    try rfl
  obtain ⟨g, hg⟩ := exists_aligned_su₂ hK Φ hker.le (P := ![P 2, P 1]) (Q := ![Q 2, Q 1])
    (fun i => by fin_cases i; exacts [(hΔ₀ _).1 h2.1, (hΔ₀ _).1 h1.1])
    (fun i => by fin_cases i; exacts [(hΔ₀ _).1 h2.2, (hΔ₀ _).1 h1.2])
    (fun i => by
      fin_cases i
      exacts [(hfr.opposite 2).not_commuting (hR.ne_bot _ (hfr.memP 2).1.1.1),
        (hfr.opposite 1).not_commuting (hR.ne_bot _ (hfr.memP 1).1.1.1)])
    (fun i j hij => by
      fin_cases i <;> fin_cases j <;> simp at hij
      exacts [hfr.commuting 2 1 (by decide), hfr.commuting 1 2 (by decide)])
  set Φ' := Φ.comp (MulAut.conj g).toMonoidHom with hΦ'def
  have hker' : Φ'.ker ≤ Subgroup.center _ := CaseMSU.ker_comp_conj_le_center hker.le g
  have hrange' : Φ'.range = gen Δ₁ := by
    rw [hΦ'def, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj g).surjective,
      ← MonoidHom.range_eq_map, hrange]
  have hΔ' : ∀ X : Subgroup G, X ∈ Δ₁ ↔
      ∃ g',
      X = (conjSub (Unitary.rootGroup (σq f) hσ 4 (Pi.single (1 : Fin 2) 1)) g').map Φ' := by
    have e : ∀ (X₀ : Subgroup (SU (σq f) 4)) (g' : SU (σq f) 4),
        (conjSub X₀ g').map Φ' = (conjSub X₀ (g * g')).map Φ := fun X₀ g' => by
      rw [hΦ'def, ← Subgroup.map_map, conjSub_mul]
    intro X
    refine ⟨fun hX => ?_, fun ⟨g', hg'⟩ => (hΔ₀ X).2 ⟨g * g', by rw [hg', e]⟩⟩
    obtain ⟨g'', rfl⟩ := (hΔ₀ X).1 hX
    exact ⟨g⁻¹ * g'', by rw [e, mul_inv_cancel_left]⟩
  have hP' : ∀ i, (Unitary.rootGroup (σq f) hσ 4 (longC2 i)).map Φ' = ![P 2,
      P 1] i :=
    fun i => (hg i).1
  have hQ' : ∀ i, (Unitary.rootGroup (σq f) hσ 4 (-longC2 i)).map Φ' = ![Q 2,
      Q 1] i :=
    fun i => (hg i).2
  have hcardF₀ : Nat.card (sigmaFixedField (σq f)) = 2 ^ f := by
    rw [← card_fixedSubfield (p := 2) hK]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  have : Finite (sigmaFixedField (σq f)) := Nat.finite_of_card_ne_zero (by rw [hcardF₀]; positivity)
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype (sigmaFixedField (σq f)) := Fintype.ofFinite _
  let e : F ≃+* sigmaFixedField (σq f) := FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hGF, hcardF₀])
  set ι : F →+* K := (sigmaFixedField (σq f)).subtype.comp (e : F →+* sigmaFixedField (σq f))
    with hιdef
  have hι : ∀ x, (σq f) (ι x) = ι x := fun x => (e x).2
  have hιs : ∀ x : K, (σq f) x = x → ∃ y, ι y = x := fun x hx =>
    ⟨e.symm ⟨x, hx⟩, by simp [hιdef]⟩
  obtain ⟨ζ, hζ⟩ := exists_unitaryInvolution_ne (p := 2) hK
  obtain ⟨b, hb⟩ := hιs (ζ + (σq f) ζ) (by rw [map_add, hσ]; exact add_comm _ _)
  obtain ⟨c, hc⟩ := hιs (ζ * (σq f) ζ) (by rw [map_mul, hσ]; exact mul_comm _ _)
  have hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0 := by
    intro s hs
    have h := congrArg ι hs
    rw [map_add, map_add, map_mul, map_pow, hb, hc, map_zero] at h
    have h' : (ι s + ζ) * (ι s + (σq f) ζ) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h₁ | h₁
    · have e₁ : ζ = ι s := by linear_combination h₁ - (CharTwo.add_self_eq_zero (ι s))
      exact hζ (by rw [e₁, hι])
    · have e₁ : (σq f) ζ = ι s := by linear_combination h₁ - (CharTwo.add_self_eq_zero (ι s))
      exact hζ (e₁.trans ((hι s).symm.trans ((congrArg (σq f) e₁).symm.trans (hσ ζ))))
  set L : (Fin (5 - 1) → ℤ) → F → G := fun γ x => Φ' (suL (σq f) ι γ x) with hLdef
  set S : (Fin (5 - 1) → ℤ) → (Fin 2 → F) → G := fun γ p => Φ' (suS (σq f) hσ ι ζ γ p) with hSdef
  set w : Fin (5 - 1) → G := fun k => Φ' (weylSU hσ k) with hwdef
  obtain ⟨β₂, hβ₂inj, hβ₂U, hβ₂L⟩ := exists_sl2_long hσ
  set ρX := (Φ'.comp β₂).comp (SpecialLinearGroup.map (e : F →+* sigmaFixedField (σq f))) with hρX
  have hρXU : ∀ x, ρX (sl2Upper x) = L (sr nd2) x := fun x => by
    rw [hρX, MonoidHom.comp_apply, MonoidHom.comp_apply, map_sl2Upper, hβ₂U]
    simp only [hLdef, suL, longIdx_d2]
    rfl
  have hρXL : ∀ x, ρX (sl2Lower x) = L (-sr nd2) x := fun x => by
    rw [hρX, MonoidHom.comp_apply, MonoidHom.comp_apply, map_sl2Lower, hβ₂L]
    simp only [hLdef, suL, longIdx_nd2]
    rfl
  have hρXinj : Function.Injective ρX := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : β₂ (SpecialLinearGroup.map (e : F →+* sigmaFixedField (σq f)) x) ∈
        Subgroup.center _ := hker' hx
    exact Linear.eq_one_of_map_mem_center F
      (ι := β₂.comp (SpecialLinearGroup.map (e : F →+* sigmaFixedField (σq f))))
      (hβ₂inj.comp (map_injective_of_injective (f := (e : F →+* sigmaFixedField (σq f)))
        e.injective)) hx'
  have hLong : ∀ (a : Fin (4 / 2) ⊕ Fin (4 / 2)) {γ : Fin (4 / 2) → ℤ},
      Unitary.toStd 4 γ = rt a a → ∀ y, y ∈ Unitary.rootGroup (σq f) hσ 4 γ ↔
        ∃ x : F, suLong (σq f) a (ι x) = y := by
    intro a γ hγ y
    rw [mem_rootGroup_iff_suLong hσ (by decide) a hγ]
    constructor
    · rintro ⟨c', hc', rfl⟩
      obtain ⟨x, hx⟩ := hιs c' (add_map_eq_zero_iff.1 hc')
      exact ⟨x, by rw [hx]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨ι x, trace_ι hι x, rfl⟩
  have hρXU' : (upperUnipotent F).map ρX = P 1 := by
    have e1 : (Unitary.rootGroup (σq f) hσ 4 (longC2 1)).map Φ' = P 1 := hP' 1
    rw [← e1]
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨t, rfl⟩ := (RankOne.mem_upperUnipotent_iff F).1 hu
      refine ⟨suLong (σq f) (Sum.inl j1) (ι t), (hLong (Sum.inl j1) (by decide) _).2 ⟨t,
          rfl⟩, ?_⟩
      rw [show RankOne.upperElt F t = sl2Upper t from rfl, hρXU]
      simp only [hLdef, suL, longIdx_d2]
    · rintro ⟨y', hy', rfl⟩
      obtain ⟨t, rfl⟩ := (hLong (Sum.inl j1) (by decide) _).1 hy'
      refine ⟨RankOne.upperElt F t, (RankOne.mem_upperUnipotent_iff F).2 ⟨t, rfl⟩, ?_⟩
      rw [show RankOne.upperElt F t = sl2Upper t from rfl, hρXU]
      simp only [hLdef, suL, longIdx_d2]
  have hρXL' : (lowerUnipotent F).map ρX = Q 1 := by
    have e1 : (Unitary.rootGroup (σq f) hσ 4 (-longC2 1)).map Φ' = Q 1 := hQ' 1
    rw [← e1]
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨t, rfl⟩ := (RankOne.mem_lowerUnipotent_iff F).1 hu
      refine ⟨suLong (σq f) (Sum.inr j1) (ι t), (hLong (Sum.inr j1) (by decide) _).2 ⟨t,
          rfl⟩, ?_⟩
      rw [show RankOne.lowerElt F t = sl2Lower t from rfl, hρXL]
      simp only [hLdef, suL, longIdx_nd2]
    · rintro ⟨y', hy', rfl⟩
      obtain ⟨t, rfl⟩ := (hLong (Sum.inr j1) (by decide) _).1 hy'
      refine ⟨RankOne.lowerElt F t, (RankOne.mem_lowerUnipotent_iff F).2 ⟨t, rfl⟩, ?_⟩
      rw [show RankOne.lowerElt F t = sl2Lower t from rfl, hρXL]
      simp only [hLdef, suL, longIdx_nd2]
  obtain ⟨hF', hEF, hcfg⟩ := hfr.isConfig hD.sec12
  have e0 := hcfg.edge 0 1 (by decide)
  have e1 := hcfg.edge 1 2 (by decide)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at e0 e1
  have hl₁ := fun {X : Subgroup G} (hX : X ∈ Δ₁) => hD.mem_leviSet₁ hX
  have hl₂ := fun {X : Subgroup G} (hX : X ∈ Δ₂) => hD.mem_leviSet₂ hX
  obtain ⟨ρ, hρ2, hρ, hedge⟩ := Linear.exists_chain hR hiso (m := 3)
    (A := ![P 0, E, P 1]) (B := ![Q 0, ⁅A₀, C⁆, Q 1])
    (fun i => by fin_cases i; exacts [(hl₂ h0.1).1.1, hfr.memE.1.1.1, (hl₁ h1.1).1.1])
    (fun i => by fin_cases i; exacts [(hl₂ h0.2).1.1, hF'.1.1.1, (hl₁ h1.2).1.1])
    (fun i => by fin_cases i; exacts [hfr.opposite 0, hEF, hfr.opposite 1])
    (fun i j hij => by
      fin_cases i <;> fin_cases j <;> simp at hij
      exacts [e0, e1])
    (k₀ := 2) (hcard _ h1.1) hρXinj hρXU' hρXL'
  obtain ⟨φ₀, hφ₀⟩ := hedge 0 1 rfl
  obtain ⟨φ₁, hφ₁⟩ := hedge 1 2 rfl
  have hρ0 : (ρ 0).range = P 0 ⊔ Q 0 := range_eq_sup_of_map (hρ 0).2.1 (hρ 0).2.2
  have hρ1 : (ρ 1).range = E ⊔ ⁅A₀, C⁆ := range_eq_sup_of_map (hρ 1).2.1 (hρ 1).2.2
  have hP0Q0 : P 0 ≠ Q 0 := (hfr.opposite 0).1
  have hgen₂ : gen Δ₂ = P 0 ⊔ Q 0 :=
    ((hD.sl2.opposite_of_ne hR hD.subset_R₂ h0.1 h0.2 hP0Q0).2).symm
  have hg0 : ∀ g, ρ 0 g ∈ gen Δ₂ := fun g => by
    have : ρ 0 g ∈ (ρ 0).range := ⟨g, rfl⟩
    rw [hρ0] at this
    exact sup_le (le_gen h0.1) (le_gen h0.2) this
  have key : ∀ g, ∀ y : G, y ∈ Subgroup.centralizer (E : Set G) →
      y ∈ Subgroup.centralizer (C : Set G) → y ∈ Subgroup.centralizer (A₀ : Set G) →
        Commute (ρ 1 g) y := by
    intro g y hyE hyC hyA
    have hle : E ⊔ ⁅A₀, C⁆ ≤ Subgroup.centralizer ({y} : Set G) :=
      sup_le (fun b hb => Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hyE b hb))
        (fun z hz => Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 (mem_centralizer_commutator hyA hyC) z hz))
    have hg : ρ 1 g ∈ E ⊔ ⁅A₀, C⁆ := by
      rw [← hρ1]
      exact ⟨g, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
  have hV₁A₀ : ∀ y, y ∈ gen Δ₁ → y ∈ Subgroup.centralizer (A₀ : Set G) := fun y hy =>
    levi_le_centralizer_right A A₀ (hD.gen₁_le_levi hy)
  have hmem : ∀ y, Φ' y ∈ gen Δ₁ := fun y => hrange' ▸ ⟨y, rfl⟩
  have hEshort : ∀ g p, Commute (ρ 1 g) (S (sr nd3) p) ∧ Commute (ρ 1 g) (S (-sr nd3) p) := by
    intro g p
    have eS : S (sr nd3) p = Φ' (suElt (σq f) hσ (Sum.inl j0) (Sum.inr j1) (kap ι ζ p)) := by
      simp only [hSdef, suS, shortIdx_d3]
    have eS' : S (-sr nd3) p = Φ' (suElt (σq f) hσ (Sum.inr j0) (Sum.inl j1) (kap ι ζ p)) := by
      simp only [hSdef, suS, shortIdx_nd3]
    rw [eS, eS']
    obtain ⟨hE1, hC1⟩ := hD.commute_shortSU hfr h0 hK hker' hrange' hΔ' hP' hQ'
      (Or.inl ⟨rfl, rfl⟩) (kap ι ζ p)
    obtain ⟨hE2, hC2⟩ := hD.commute_shortSU hfr h0 hK hker' hrange' hΔ' hP' hQ'
      (Or.inr ⟨rfl, rfl⟩) (kap ι ζ p)
    refine ⟨key g _ (Subgroup.mem_centralizer_iff.2 fun e he => (hE1 e he).symm.eq)
      (Subgroup.mem_centralizer_iff.2 fun x hx => (hC1 x hx).symm.eq) (hV₁A₀ _ (hmem _)),
      key g _ (Subgroup.mem_centralizer_iff.2 fun e he => (hE2 e he).symm.eq)
      (Subgroup.mem_centralizer_iff.2 fun x hx => (hC2 x hx).symm.eq) (hV₁A₀ _ (hmem _))⟩
  have hgenV : gen Δ₁ ≤ Subgroup.closure (Set.range (L (sr nd2)) ∪ Set.range (L (-sr nd2)) ∪
      Set.range (S (sr nd3)) ∪ Set.range (S (-sr nd3))) := by
    rw [← hrange', MonoidHom.range_eq_map, ← iSup_rankOne_SU4 hK, Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    rw [Subgroup.map_le_iff_le_comap]
    rcases (show k = j0 ∨ k = j1 by fin_cases k <;> decide) with rfl | rfl
    · refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨t, rfl⟩ := (mem_rootGroup_iff_suElt hσ (by decide) idx_d3 (by decide) x).1 hx
        obtain ⟨p, rfl⟩ := kap_surjective hσ hζ hιs t
        exact Subgroup.mem_comap.2 (Subgroup.subset_closure
          (Or.inl (Or.inr ⟨p, by simp only [hSdef, suS, shortIdx_d3]⟩)))
      · obtain ⟨t, rfl⟩ := (mem_rootGroup_iff_suElt hσ (by decide) idx_1 (by decide) x).1 hx
        obtain ⟨p, hp⟩ := kap_surjective hσ hζ hιs ((σq f) t)
        refine Subgroup.mem_comap.2 (Subgroup.subset_closure (Or.inr ⟨p, ?_⟩))
        simp only [hSdef, suS, shortIdx_nd3, hp]
        rw [suElt_swap hσ idx_1, hσ, CharTwo.neg_eq]
    · refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · obtain ⟨t, rfl⟩ := (hLong (Sum.inl j1) (by decide) x).1 hx
        exact Subgroup.mem_comap.2 (Subgroup.subset_closure
          (Or.inl (Or.inl (Or.inl ⟨t, by simp only [hLdef, suL, longIdx_d2]⟩))))
      · obtain ⟨t, rfl⟩ := (hLong (Sum.inr j1) (by decide) x).1 hx
        exact Subgroup.mem_comap.2 (Subgroup.subset_closure
          (Or.inl (Or.inl (Or.inr ⟨t, by simp only [hLdef, suL, longIdx_nd2]⟩))))
  have H : GlueHyp hirr φ₀ φ₁ (ρ 0) (ρ 1) L S w (gen Δ₁) :=
    { φ₀01 := fun x => (hφ₀ x).1
      φ₀10 := fun x => (hφ₀ x).2.1
      φ₀12 := fun x => (hφ₀ x).2.2.1
      φ₀21 := fun x => (hφ₀ x).2.2.2
      φ₁01 := fun x => (hφ₁ x).1
      φ₁10 := fun x => (hφ₁ x).2.1
      φ₁12 := fun x => by rw [(hφ₁ x).2.2.1, hρ2, LevisExtras.tv01_eq_sl2Upper, hρXU]
      φ₁21 := fun x => by rw [(hφ₁ x).2.2.2, hρ2, LevisExtras.tv10_eq_sl2Lower, hρXL]
      addL := fun γ x y => by
        simp only [hLdef]
        rw [suL_add hι, map_mul]
      addS := fun γ p q => by
        simp only [hSdef]
        rw [suS_add, map_mul]
      commB2 := fun p s => by
        simp only [hSdef, hLdef]
        rw [← map_commutatorElement, suS_comm_suL hσ hι hb hc, map_mul]
      commB2' := fun p q => by
        simp only [hSdef, hLdef]
        rw [← map_commutatorElement, suS_comm_suS hσ hι hb hc]
      commuteB2_b_2ab := fun p s => (suS_commute_suL₁ hσ hι p s).map Φ'
      commuteB2_ab_2ab := fun p s => (suS_commute_suL₂ hσ hι p s).map Φ'
      commuteB2_ab_a := fun p s => (suS_commute_suL₃ hσ hι p s).map Φ'
      commuteB2_2ab_a := fun s t => (suL_commute_suL hσ hι s t).map Φ'
      weylV := fun k hk γ hγ => by
        obtain ⟨h1', h2'⟩ := weylSU_conj (hσ := hσ) hι hb hirr hk hγ
        refine ⟨fun hL a => ?_, fun hS p => ?_⟩
        · simp only [hwdef, hLdef]
          rw [← map_inv, ← map_mul, ← map_mul, h1' hL a]
        · simp only [hwdef, hSdef]
          rw [← map_inv, ← map_mul, ← map_mul, h2' hS p]
      w₂_eq := by
        simp only [hwdef, hLdef, suL, longIdx_d2, longIdx_nd2, map_one]
        rw [weylSU_two, weyl₂, map_mul, map_mul]
      w₃_eq := by
        simp only [hwdef, hSdef, suS, shortIdx_d3, shortIdx_nd3, kap_planeOne]
        rw [weylSU_three, weyl₃, map_mul, map_mul]
      memL := fun γ x => hmem _
      memS := fun γ p => hmem _
      V := fun g y hy => (hD.commuting_gen _ hy _ (hg0 g)).symm
      E := hEshort
      rank₂ := ⟨ρX, hρXU, hρXL⟩
      genV := hgenV }
  have := fact_shortField hirr
  obtain ⟨β₃, hβ₃U, hβ₃L⟩ := exists_sl2_short hσ
  have hrank₃ : ∃ Θ : SL2E b c →* G, (∀ t, Θ (sl2Upper t) = S (sr nd3) (fieldCoord t)) ∧
      ∀ t, Θ (sl2Lower t) = S (-sr nd3) (starCoord t) := by
    refine ⟨(Φ'.comp β₃).comp (SpecialLinearGroup.map (lam hb hc)), fun t => ?_, fun t => ?_⟩
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, map_sl2Upper, hβ₃U]
      simp only [hSdef, suS, shortIdx_d3, kap_fieldCoord hb hc]
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, map_sl2Lower, hβ₃L]
      simp only [hSdef, suS, shortIdx_nd3, kap_starCoord hb hc hι]
      rw [suElt_swap hσ idx_1, hσ, CharTwo.neg_eq ((lam hb hc) t)]
  have htop : levi R A A₀ ⊔ E ⊔ ⁅A₀, C⁆ = ⊤ :=
    CaseOA.levi_sup_sup_eq_top hD.hyp hD.mem hD.ne hD.max hD.opp hfr.memE hF'
  rw [CaseOA.levi_eq_sup hD.hyp hD.mem hD.ne hD.opp hD.card_comps hD.comp₁ hD.comp₂
    hD.comp_ne] at htop
  have hgen : (ρ 0).range ⊔ (ρ 1).range ⊔ gen Δ₁ = ⊤ := by
    rw [hρ0, hρ1, ← hgen₂, eq_top_iff, ← htop]
    exact sup_le (sup_le (sup_le le_sup_right (le_sup_left.trans le_sup_left))
      (le_sup_left.trans (le_sup_right.trans le_sup_left)))
      (le_sup_right.trans (le_sup_right.trans le_sup_left))
  have hnt : ρ 0 (tv 0 1 1) ≠ 1 := by
    intro h1'
    have h1'' := (hρ 0).1 (h1'.trans (map_one (ρ 0)).symm)
    rw [LevisExtras.tv01_eq_sl2Upper] at h1''
    have := congrArg (fun M : SpecialLinearGroup (Fin 2) F =>
      (M : Matrix (Fin 2) (Fin 2) F) 0 1) h1''
    simp [sl2Upper] at this
  have hframe := (H.isMinusFrame hrank₃ hgen hnt).isCTFrame
  have hadm : StatedLieAdmissible .POmegaMinus 5 2 f := ⟨Nat.prime_two, hf, by norm_num⟩
  have hCT := CurtisTits.curtisTitsConclusion_spinMinus (n := 5) hirr hadm hGF
  have hL := leviConePresented_spinMinus hirr (show 4 ≤ 5 by norm_num)
  refine Output.of_nonSimplyLaced
    (.inr (.inl ⟨5, f, by norm_num, hf, hframe.lieModel hCT hL hD.hyp.center⟩)) ?_
  refine .inr (hframe.nslFrame hCT hL (minusDatum_isCTGroupDatum 5 hirr (by norm_num))
    (minusDatum_steinbergExtras 5 hirr) rfl (NSLType.minusDatum (by norm_num) hirr)
    (fun _ hγ => isPGroup_minusRootGroup hirr hγ) (NSLFrameData.comm_minusDatum (by norm_num) hirr)
    (hl₂ h0.1).1.1 ?_ ?_ (hfr.opposite 0))
  · refine Eq.symm ((range_minusPhiOf_long hirr _ _
      (minusLong_single (n := 5) (k := nd0) (by decide))).trans ?_)
    have e' : glueL φ₀ φ₁ L (sr nd0) = fun x => ρ 0 (tv 0 1 x) := funext H.v_d0
    show Set.range (glueL φ₀ φ₁ L (sr nd0)) = _
    rw [e', Linear.range_tv_upper, (hρ 0).2.1]
    rfl
  · refine Eq.symm ((range_minusPhiOf_long hirr _ _
      (minusLong_neg_single (n := 5) (k := nd0) (by decide))).trans ?_)
    have e' : glueL φ₀ φ₁ L (-sr nd0) = fun x => ρ 0 (tv 1 0 x) := funext H.v_nd0
    show Set.range (glueL φ₀ φ₁ L (-sr nd0)) = _
    rw [e', Linear.range_tv_lower, (hρ 0).2.2]
    rfl

end DegOA

theorem oaDegSUInput : OADegSUInput :=
  fun _ _ _ _ _ _ _ hD _ hf hcard Φ hker hrange hΔ => hD.output_su hf hcard Φ hker hrange hΔ

end CaseOADeg

theorem oaDegenerateInput : OADegenerateInput :=
  CaseOADeg.oaDegenerateInput_of CaseOADeg.oaDegSUInput

end CFSG.Timmesfeld.ARS
