module

public import CFSG.RankThree.PartOne.SEITZ7.D4AB

public section

namespace CFSG.RankThree.PartOne.SEITZ7

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.SEITZ3 CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem
open scoped commutatorElement

theorem rootGroup_weylAction_le_sub {K' : Type*} [Group K'] {D : UniversalRootDatum K'}
    {nw : Fin D.rank → K'} {Hs : Fin D.rank → Subgroup K'}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup nw Hs)
    {N : Subgroup K'} (hn : ∀ i, nw i ∈ N) {v : Fin D.rank → ℤ} (hv : v ∈ D.roots)
    (hN : D.rootGroup v ≤ N) (w : (coxeterMatrix D.isFiniteType).Group) :
    D.rootGroup (weylAction D.isFiniteType w v) ≤ N := by
  induction w using (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple_induction_left with
  | one => simpa using hN
  | mul_simple_left w i ih =>
    intro x hx
    set cs := (coxeterMatrix D.isFiniteType).toCoxeterSystem
    have hγ := weylAction_mem_roots hv (cs.simple i * w)
    have hconj := hct.conj_mem i _ hγ x hx
    have heq : weylAction D.isFiniteType (cs.simple i)
        (weylAction D.isFiniteType (cs.simple i * w) v) = weylAction D.isFiniteType w v := by
      rw [← weylAction_mul_apply, ← mul_assoc, cs.simple_mul_simple_self, one_mul]
    rw [heq] at hconj
    have hmem := N.mul_mem (N.mul_mem (N.inv_mem (hn i)) (ih hconj)) (hn i)
    simpa [mul_assoc] using hmem

variable {K : Type} [Field K] {σ : K →+* K}

theorem eq_top_of_simple_tw (hσ : ∀ c, σ (σ (σ c)) = c) {H : Subgroup (twistedGroup σ)}
    (hn0 : nHat σ (ng 0) ∈ H) (hn1 : nHat σ (ng 1) ∈ H)
    (h0 : twistedRootGroup σ (Pi.single (ng 0) 1) ≤ H)
    (h1 : twistedRootGroup σ (Pi.single (ng 1) 1) ≤ H) : H = ⊤ := by
  have hct := twistedDatum_isCTGroupDatum σ hσ
  rw [eq_top_iff, ← hct.iSup_eq_top]
  refine iSup₂_le fun γ hγ => ?_
  have hsingle : ∀ i, Pi.single i (1 : ℤ) ∈ (twistedDatum σ).roots := fun i =>
    Or.inl ⟨1, i, by simp⟩
  have hn : ∀ i : Fin (twistedDatum σ).rank, nHat σ i ∈ H := by
    intro i
    fin_cases i
    · exact hn0
    · exact hn1
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
  · refine rootGroup_weylAction_le_sub hct hn (hsingle i) ?_ w
    fin_cases i
    · exact h0
    · exact h1
  · exact absurd hi (Set.notMem_empty i)

theorem reflect_N_check : reflect d4 (nd 3) (d4Root 19) = d4Root 12 ∧
    reflect d4 (nd 1) (d4Root 12) = d4Root 5 ∧ reflect d4 (nd 0) (d4Root 5) = d4Root 2 := by
  decide +kernel

theorem nHat1_xN [CharP K 2] (c : K) :
    nHatE K (ng 1) * xN c * (nHatE K (ng 1))⁻¹ = xB c := by
  obtain ⟨h1, h2, h3⟩ := reflect_N_check
  show nHatE K (ng 1) * xd 19 c * (nHatE K (ng 1))⁻¹ = xd 2 c
  rw [nHatE_one]
  have e : weylElement d4 K (nd 0) * weylElement d4 K (nd 1) * weylElement d4 K (nd 3) *
      xd 19 c * (weylElement d4 K (nd 0) * weylElement d4 K (nd 1) *
        weylElement d4 K (nd 3))⁻¹ = weylElement d4 K (nd 0) * (weylElement d4 K (nd 1) *
          (weylElement d4 K (nd 3) * xd 19 c * (weylElement d4 K (nd 3))⁻¹) *
            (weylElement d4 K (nd 1))⁻¹) * (weylElement d4 K (nd 0))⁻¹ := by group
  rw [e, weylElement_conj_xd (nd 3) (by norm_num) h1, weylElement_conj_xd (nd 1) (by norm_num) h2,
    weylElement_conj_xd (nd 0) (by norm_num) h3]

theorem swap_23_19 [CharP K 2] (x y : K) :
    xd 23 y * xd 19 x = xd 8 (x * y) * (xd 19 x * xd 23 y) :=
  swap_gen (Or.inr rfl) (by decide +kernel) x y

theorem nHat_one_mem_Asub [CharP K 2] (hσ : ∀ c, σ (σ (σ c)) = c) :
    nHat σ (ng 1) ∈ Asub σ hσ := by
  have e : nHat σ (ng 1) = slShort σ hσ (sl2Upper 1) * slShort σ hσ (sl2Lower (-1)) *
      slShort σ hσ (sl2Upper 1) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, nHat_val, nHatE_one_eq, slShort_upper, slShort_lower, map_one,
      map_neg]
  rw [e]
  exact mul_mem (mul_mem ⟨_, rfl⟩ ⟨_, rfl⟩) ⟨_, rfl⟩

theorem rt0_single : (rt 0 : Fin 2 → ℤ) = Pi.single (ng 0) 1 := by
  ext i; fin_cases i <;> decide

theorem rt1_single : (rt 1 : Fin 2 → ℤ) = Pi.single (ng 1) 1 := by
  ext i; fin_cases i <;> decide

theorem torusB_mem_hHatE (σ : K →+* K) (s : Kˣ) (hs : σ (s : K) = (s : K)) :
    torusElement d4 K (nd 2) s ∈ hHatE σ (ng 0) :=
  show torusElement d4 K (nd 2) s ∈ (hLongHom σ).range from ⟨⟨s, (mem_fixedUnits σ).2 hs⟩, rfl⟩

theorem d4Root_dict' : d4Root 2 = (1 : ℤ) • Pi.single (nd 2) 1 ∧
    d4Root 8 = (-1 : ℤ) • Pi.single (nd 2) 1 := by
  decide +kernel

theorem eq_top_of_xN [CharP K 2] [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c)
    {H : Subgroup (twistedGroup σ)} (hL : Lsub σ hσ ≤ H) {b : K} (hb : b ≠ 0) (hbσ : σ b = b)
    (hN : ∃ x ∈ H, (x : adjointGroup d4 K) = xN b) : H = ⊤ := by
  obtain ⟨x0, hx0H, hx0⟩ := hN
  have hr0 : IsRoot .G2 (rt 0) := isRoot_rt (by norm_num)
  have hr1 : IsRoot .G2 (rt 1) := isRoot_rt (by norm_num)
  have hNc : ∀ c : K, σ c = c → ∃ x ∈ H, (x : adjointGroup d4 K) = xN c := by
    intro c hc
    by_cases hc0 : c = 0
    · exact ⟨1, one_mem _, by simp [hc0, xN, xd_zero]⟩
    · set s : Kˣ := Units.mk0 (b / c) (div_ne_zero hb hc0) with hs
      have hsσ : σ (s : K) = (s : K) := by simp [hs, map_div₀, hbσ, hc]
      let t : twistedGroup σ := ⟨torusElement d4 K (nd 2) s,
        hHatE_le_twistedGroup hσ (ng 0) (torusB_mem_hHatE σ s hsσ)⟩
      have htH : t ∈ H := hL (hB_mem_Lsub σ hσ hsσ rfl)
      refine ⟨t * x0 * t⁻¹, H.mul_mem (H.mul_mem htH hx0H) (H.inv_mem htH), ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx0]
      rw [show ((t : twistedGroup σ) : adjointGroup d4 K) = torusElement d4 K (nd 2) s from rfl,
        hB_xN]
      congr 2
      simp only [hs, Units.val_inv_eq_inv_val, Units.val_mk0]
      field_simp
  have hn1 : nHat σ (ng 1) ∈ H := hL (Asub_le_Lsub σ hσ (nHat_one_mem_Asub hσ))
  have hBc : ∀ c : K, σ c = c → ∃ x ∈ H, (x : adjointGroup d4 K) = xB c := by
    intro c hc
    obtain ⟨x, hxH, hx⟩ := hNc c hc
    refine ⟨nHat σ (ng 1) * x * (nHat σ (ng 1))⁻¹, H.mul_mem (H.mul_mem hn1 hxH) (H.inv_mem hn1),
      ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx, nHat_val]
    exact nHat1_xN c
  have hneg : ∃ x ∈ H, (x : adjointGroup d4 K) = xd 8 1 := by
    obtain ⟨x, hxH, hx⟩ := hNc 1 (map_one σ)
    have h23 : psiB σ hσ (sl2Lower (1 : fixedField σ)) ∈ H :=
      hL (Bsub_le_Lsub σ hσ ⟨_, rfl⟩)
    refine ⟨psiB σ hσ (sl2Lower (1 : fixedField σ)) * x *
      (x * psiB σ hσ (sl2Lower (1 : fixedField σ)))⁻¹,
      H.mul_mem (H.mul_mem h23 hxH) (H.inv_mem (H.mul_mem hxH h23)), ?_⟩
    have h1 := psiB_lower σ hσ (1 : fixedField σ)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hx, h1]
    have h2 := swap_23_19 (K := K) 1 1
    rw [mul_one] at h2
    rw [show (((1 : fixedField σ) : K)) = 1 from rfl]
    show xd 23 1 * xd 19 1 * (xd 19 1 * xd 23 1)⁻¹ = xd 8 1
    rw [h2, mul_inv_cancel_right]
  have hn0 : nHat σ (ng 0) ∈ H := by
    obtain ⟨x1, hx1H, hx1⟩ := hBc 1 (map_one σ)
    obtain ⟨x2, hx2H, hx2⟩ := hneg
    have e : nHat σ (ng 0) = x1 * x2 * x1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, nHat_val, nHatE_zero_eq, hx1, hx2]
      rw [← d4Root_dict'.1, ← d4Root_dict'.2, CharTwo.neg_eq (1 : K)]
      rfl
    rw [e]
    exact H.mul_mem (H.mul_mem hx1H hx2H) hx1H
  have h0 : twistedRootGroup σ (Pi.single (ng 0) 1) ≤ H := by
    intro y hy
    have hy' : (y : adjointGroup d4 K) ∈ twistedRootSubgroupD4 σ (rt 0) := by
      rw [rt0_single]
      exact Subgroup.mem_subgroupOf.1 hy
    obtain ⟨c, hcσ, hyc⟩ := (mem_XB hσ _).1 hy'
    obtain ⟨x, hxH, hx⟩ := hBc c hcσ
    have : y = x := Subtype.ext (hyc.trans hx.symm)
    rw [this]
    exact hxH
  have h1 : twistedRootGroup σ (Pi.single (ng 1) 1) ≤ H := by
    intro y hy
    have hy' : (y : adjointGroup d4 K) ∈ twistedRootSubgroupD4 σ (rt 1) := by
      rw [rt1_single]
      exact Subgroup.mem_subgroupOf.1 hy
    obtain ⟨a, hya⟩ := (mem_XA hσ _).1 hy'
    have : y = slShort σ hσ (sl2Upper a) :=
      Subtype.ext (hya.trans (slShort_upper_xA σ hσ a).symm)
    rw [this]
    exact hL (Asub_le_Lsub σ hσ ⟨_, rfl⟩)
  exact eq_top_of_simple_tw hσ hn0 hn1 h0 h1

end CFSG.RankThree.PartOne.SEITZ7
