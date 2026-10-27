module

public import CFSG.RankThree.GF2n.Stroth80.Ext1D4Datum
public import CFSG.RankThree.GF2n.Stroth80.Sec715TriNF

public section

namespace CFSG.RankThree.GF2n.Stroth80.Ext1D4

open CFSG.LieType.D4Small CFSG.RankThree.GF2n.Stroth80.Tri

@[expose] def nfWt (N m j : ℕ) (χ : Fin 4 → ℤ) : Fin 4 → ZMod N :=
  castW N fun i => 2 ^ j * m * χ i

theorem nfWt_add (N m j : ℕ) (χ ψ : Fin 4 → ℤ) :
    nfWt N m j (χ + ψ) = nfWt N m j χ + nfWt N m j ψ := by
  funext i
  simp only [nfWt, castW, Pi.add_apply]
  push_cast
  ring

theorem nfWt_posRoot {N m : ℕ} (hm : (2 * m : ZMod N) = 1) (j : ℕ) :
    ∀ β ∈ posRoot, nfWt N m j β = (2 : ZMod N) ^ j • castW N (halfVec β) := by
  intro β hβ
  funext i
  simp only [nfWt, castW, Pi.smul_apply, smul_eq_mul]
  rw [two_mul_halfVec β hβ i]
  push_cast
  linear_combination (2 : ZMod N) ^ j * (halfVec β i : ZMod N) * hm

theorem nfWt_eq_smul (N m j : ℕ) (χ : Fin 4 → ℤ) :
    nfWt N m j χ = ((2 : ZMod N) ^ j * m) • castW N χ := by
  funext i
  simp only [nfWt, castW, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem minWt_diff_bound {W : Finset (Fin 4 → ℤ)} (hW : IsMinWt W) :
    ∀ χ ∈ W, ∀ ψ ∈ W, ∀ β ∈ insert 0 posRoot, ∀ i, |ψ i - χ i - β i| ≤ 6 := by
  rcases hW with rfl | rfl | rfl <;> decide +kernel

theorem minWt_diff_three {W : Finset (Fin 4 → ℤ)} (hW : IsMinWt W) :
    ∀ χ ∈ W, ∀ ψ ∈ W, ∀ β ∈ insert 0 posRoot, (∀ i, (ψ i - χ i - β i) % 3 = 0) →
      ψ = χ + β := by
  rcases hW with rfl | rfl | rfl <;> decide +kernel

theorem natWt_spec : ∀ χ ∈ natWt, ∃ i : Fin 4, χ = Pi.single i 2 ∨ χ = Pi.single i (-2) := by
  decide +kernel

theorem single_mem_natWt : ∀ i : Fin 4, Pi.single i 2 ∈ natWt ∧ Pi.single i (-2) ∈ natWt := by
  decide +kernel

theorem evenWt_spec : ∀ χ ∈ evenWt, (∀ i, χ i = 1 ∨ χ i = -1) ∧
    (Finset.univ.filter fun i => χ i = -1).card % 2 = 0 := by
  decide +kernel

theorem oddWt_spec : ∀ χ ∈ oddWt, (∀ i, χ i = 1 ∨ χ i = -1) ∧
    (Finset.univ.filter fun i => χ i = -1).card % 2 = 1 := by
  decide +kernel

theorem signVec_mem : ∀ s : Fin 4 → Bool,
    ((Finset.univ.filter fun i => s i = false).card % 2 = 0 →
      (fun i => if s i then (1 : ℤ) else -1) ∈ evenWt) ∧
    ((Finset.univ.filter fun i => s i = false).card % 2 = 1 →
      (fun i => if s i then (1 : ℤ) else -1) ∈ oddWt) := by
  decide +kernel

theorem eq_of_castW_eq {N : ℕ} (hN : N = 3 ∨ 7 ≤ N) {W : Finset (Fin 4 → ℤ)} (hW : IsMinWt W)
    {χ ψ β : Fin 4 → ℤ} (hχ : χ ∈ W) (hψ : ψ ∈ W) (hβ : β ∈ insert 0 posRoot)
    (h : castW N ψ = castW N (χ + β)) : ψ = χ + β := by
  have hdvd : ∀ i, (N : ℤ) ∣ ψ i - χ i - β i := fun i => by
    have h1 := congrFun h i
    simp only [castW, Pi.add_apply] at h1
    have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub (χ i + β i) (ψ i) N).1 h1.symm
    rw [show ψ i - χ i - β i = ψ i - (χ i + β i) by ring]
    exact h2
  rcases hN with rfl | hN
  · exact minWt_diff_three hW χ hχ ψ hψ β hβ fun i => Int.emod_eq_zero_of_dvd (hdvd i)
  · funext i
    have hb := minWt_diff_bound hW χ hχ ψ hψ β hβ i
    have hN' : (6 : ℤ) < N := by exact_mod_cast hN
    have h0 := Int.eq_zero_of_abs_lt_dvd (hdvd i) (by linarith)
    simp only [Pi.add_apply]
    linarith

theorem nfWt_single (N m j : ℕ) (i : Fin 4) (s : ℤ) :
    nfWt N m j (Pi.single i s) = Pi.single i ((2 : ZMod N) ^ j * m * s) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [nfWt, castW]
  · simp [nfWt, castW, Pi.single_apply, hk]

theorem exists_minWt_of_nfType {N m j : ℕ} [Fact (1 < N)] (hm : (2 * m : ZMod N) = 1)
    {C : Finset (Fin 4 → ZMod N)} (hC : NFType j C) :
    ∃ W, IsMinWt W ∧ (∀ χ ∈ W, nfWt N m j χ ∈ C) ∧ ∀ a ∈ C, ∃ χ ∈ W, nfWt N m j χ = a := by
  classical
  have h2u : IsUnit (2 : ZMod N) := ⟨⟨2, (m : ZMod N), hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  have h2j : (2 : ZMod N) ^ j ≠ 0 := (h2u.pow j).ne_zero
  have hp : (2 : ZMod N) ^ j * m * 2 = 2 ^ j := by linear_combination (2 : ZMod N) ^ j * hm
  rcases hC with hC | ⟨b₀, e, hb₀, he, hC⟩
  ·
    refine ⟨natWt, Or.inl rfl, fun χ hχ => ?_, fun a ha => ?_⟩
    · rw [hC]
      obtain ⟨i, rfl | rfl⟩ := natWt_spec χ hχ
      · refine ⟨i, Or.inl ?_⟩
        rw [nfWt_single]
        push_cast
        rw [hp]
      · refine ⟨i, Or.inr ?_⟩
        rw [nfWt_single]
        push_cast
        rw [mul_neg, hp]
    · obtain ⟨i, rfl | rfl⟩ := (hC a).1 ha
      · refine ⟨Pi.single i 2, (single_mem_natWt i).1, ?_⟩
        rw [nfWt_single]
        push_cast
        rw [hp]
      · refine ⟨Pi.single i (-2), (single_mem_natWt i).2, ?_⟩
        rw [nfWt_single]
        push_cast
        rw [mul_neg, hp]
  ·
    have hb : b₀ = 2 ^ j * m := by linear_combination (-b₀) * hm + (m : ZMod N) * hb₀
    have hbne : b₀ ≠ -b₀ := fun h => h2j (by rw [← hb₀]; linear_combination h)
    have hv : ∀ χ : Fin 4 → ℤ, ∀ i, nfWt N m j χ i = b₀ * χ i := by
      intro χ i
      simp only [nfWt, castW]
      push_cast
      rw [hb]
    have hval1 : ∀ χ : Fin 4 → ℤ, ∀ i, χ i = 1 → nfWt N m j χ i = b₀ := fun χ i hi => by
      rw [hv, hi]
      simp
    have hval2 : ∀ χ : Fin 4 → ℤ, ∀ i, χ i = -1 → nfWt N m j χ i = -b₀ := fun χ i hi => by
      rw [hv, hi]
      simp
    have hiff : ∀ χ : Fin 4 → ℤ, ∀ i, χ i = 1 ∨ χ i = -1 →
        (χ i = -1 ↔ nfWt N m j χ i = -b₀) := by
      intro χ i hi
      rcases hi with hi | hi
      · rw [hval1 χ i hi, hi]
        exact ⟨fun h => absurd h (by norm_num), fun h => absurd h hbne⟩
      · rw [hval2 χ i hi, hi]
        exact ⟨fun _ => rfl, fun _ => rfl⟩
    have hspec : ∀ χ : Fin 4 → ℤ, (∀ i, χ i = 1 ∨ χ i = -1) →
        (Finset.univ.filter fun i => χ i = -1).card % 2 = e % 2 → nfWt N m j χ ∈ C := by
      intro χ h1 h2
      rw [hC]
      refine ⟨fun i => ?_, ?_⟩
      · rcases h1 i with hi | hi
        · exact Or.inl (hval1 χ i hi)
        · exact Or.inr (hval2 χ i hi)
      · rw [← h2]
        congr 2
        exact (Finset.filter_congr fun i _ => hiff χ i (h1 i)).symm
    have hsurj : ∀ a ∈ C, ∃ χ : Fin 4 → ℤ,
        (Finset.univ.filter fun i => χ i = -1).card % 2 = e % 2 ∧ nfWt N m j χ = a ∧
        χ = fun i => if decide (a i = b₀) then (1 : ℤ) else -1 := by
      intro a ha
      obtain ⟨ha1, ha2⟩ := (hC a).1 ha
      refine ⟨fun i => if decide (a i = b₀) then (1 : ℤ) else -1, ?_, ?_, rfl⟩
      · rw [← ha2]
        congr 2
        refine Finset.filter_congr fun i _ => ?_
        by_cases h : a i = b₀
        · simp [h, hbne]
        · have h' : a i = -b₀ := (ha1 i).resolve_left h
          simp [h, h', Ne.symm hbne]
      · funext i
        by_cases h : a i = b₀
        · rw [hval1 _ i (by simp [h]), h]
        · rw [hval2 _ i (by simp [h]), (ha1 i).resolve_left h]
    have he' : e = 0 ∨ e = 1 := by omega
    rcases he' with rfl | rfl
    · refine ⟨evenWt, Or.inr (Or.inl rfl), fun χ hχ => ?_, fun a ha => ?_⟩
      · obtain ⟨h1, h2⟩ := evenWt_spec χ hχ
        exact hspec χ h1 (by rw [h2])
      · obtain ⟨χ, h2, h3, hχ⟩ := hsurj a ha
        refine ⟨χ, ?_, h3⟩
        rw [hχ]
        refine (signVec_mem fun i => decide (a i = b₀)).1 ?_
        rw [hχ] at h2
        have : (Finset.univ.filter fun i => decide (a i = b₀) = false) =
            Finset.univ.filter fun i =>
              (fun i => if decide (a i = b₀) then (1 : ℤ) else -1) i = -1 := by
          refine Finset.filter_congr fun i _ => ?_
          by_cases h : a i = b₀ <;> simp [h]
        rw [this]
        simpa using h2
    · refine ⟨oddWt, Or.inr (Or.inr rfl), fun χ hχ => ?_, fun a ha => ?_⟩
      · obtain ⟨h1, h2⟩ := oddWt_spec χ hχ
        exact hspec χ h1 (by rw [h2])
      · obtain ⟨χ, h2, h3, hχ⟩ := hsurj a ha
        refine ⟨χ, ?_, h3⟩
        rw [hχ]
        refine (signVec_mem fun i => decide (a i = b₀)).2 ?_
        rw [hχ] at h2
        have : (Finset.univ.filter fun i => decide (a i = b₀) = false) =
            Finset.univ.filter fun i =>
              (fun i => if decide (a i = b₀) then (1 : ℤ) else -1) i = -1 := by
          refine Finset.filter_congr fun i _ => ?_
          by_cases h : a i = b₀ <;> simp [h]
        rw [this]
        simpa using h2

section Basis

variable {G : Type*} [Group G] {K : Type*} [Field K] [Fintype K] [CharP K 2]
  (D : D4Datum G K) {X : Type*} [AddCommGroup X] [Module K X] (ρ : Representation K G X)

theorem natCard_units_eq (K : Type*) [Field K] [Fintype K] :
    Nat.card Kˣ = Fintype.card K - 1 := by
  rw [Nat.card_units, Nat.card_eq_fintype_card]

theorem two_mul_eq_one_zmod {m : ℕ} (hm : 2 * m = Fintype.card K) :
    ((2 * m : ℕ) : ZMod (Nat.card Kˣ)) = 1 := by
  rw [hm, natCard_units_eq]
  have h1 : 1 ≤ Fintype.card K := Fintype.card_pos
  rw [show Fintype.card K = Fintype.card K - 1 + 1 by omega, Nat.cast_add, ZMod.natCast_self,
    zero_add, Nat.cast_one]

theorem card_units_cases {f : ℕ} (hf : Fintype.card K = 2 ^ f) (hq : 4 ≤ Fintype.card K) :
    Nat.card Kˣ = 3 ∨ 7 ≤ Nat.card Kˣ := by
  rw [natCard_units_eq, hf]
  rw [hf] at hq
  rcases Nat.lt_or_ge f 3 with h | h
  · interval_cases f <;> simp_all
  · right
    have : 2 ^ 3 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h
    omega

theorem wtChar_nfWt (m j : ℕ) (χ : Fin 4 → ℤ) (z : Fin 4 → Kˣ) :
    D4Datum.wtChar (nfWt (Nat.card Kˣ) m j χ) z = wtChar m j χ z := by
  rw [nfWt, D4Datum.wtChar_castW_units, torusChar_apply, wtChar, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul]
  congr 1
  push_cast
  ring

theorem exists_basis_of_nf {f m : ℕ} (hf : Fintype.card K = 2 ^ f) (hm : 2 * m = Fintype.card K)
    (hq : 4 ≤ Fintype.card K) {j : ℕ} {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))}
    {b : (Fin 4 → ZMod (Nat.card Kˣ)) → X} (hj : 2 ^ j < Nat.card Kˣ) (hC : NFType j C)
    (hb : NF D ρ j C b) :
    j < f ∧ ∃ W, IsMinWt W ∧ ∃ v : Module.Basis W K X,
      (∀ β ∈ posRoot, ∀ t χ, ρ (posX D β t) (v χ) = ∑ ψ, rootElt W β (t ^ 2 ^ j) ψ χ • v ψ) ∧
      ∀ z χ, ρ (D.h z) (v χ) = (wtChar m j (χ : Fin 4 → ℤ) z : K) • v χ := by
  classical
  have hNcase := card_units_cases hf hq
  haveI : Fact (1 < (Nat.card Kˣ)) := ⟨by rcases hNcase with h | h <;> omega⟩
  have hm' : (2 * m : ZMod (Nat.card Kˣ)) = 1 := by exact_mod_cast two_mul_eq_one_zmod hm
  have hjf : j < f := by
    have h1 : 2 ^ j < 2 ^ f := by
      have : Nat.card Kˣ < 2 ^ f := by
        rw [natCard_units_eq, hf]; have := Nat.one_le_two_pow (n := f); omega
      omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h1
  refine ⟨hjf, ?_⟩
  obtain ⟨W, hW, hWC, hCW⟩ := exists_minWt_of_nfType hm' hC
  have hunit : IsUnit ((2 : ZMod (Nat.card Kˣ)) ^ j * m) := by
    refine IsUnit.mul (IsUnit.pow _
      ⟨⟨2, (m : ZMod (Nat.card Kˣ)), hm', by rw [mul_comm]; exact hm'⟩, rfl⟩) ?_
    exact ⟨⟨(m : ZMod (Nat.card Kˣ)), 2, by rw [mul_comm]; exact hm', hm'⟩, rfl⟩
  have hinj : ∀ χ ∈ W, ∀ ψ ∈ W, ∀ β ∈ insert 0 posRoot,
      nfWt (Nat.card Kˣ) m j ψ = nfWt (Nat.card Kˣ) m j (χ + β) → ψ = χ + β := by
    intro χ hχ ψ hψ β hβ h
    rw [nfWt_eq_smul, nfWt_eq_smul] at h
    have h' := congrArg (fun a => (hunit.unit⁻¹ : (ZMod (Nat.card Kˣ))ˣ) • a) h
    simp only [smul_smul, Units.smul_def] at h'
    rw [show ((hunit.unit⁻¹ : (ZMod (Nat.card Kˣ))ˣ) : ZMod (Nat.card Kˣ)) *
        ((2 : ZMod (Nat.card Kˣ)) ^ j * m) = 1 from hunit.val_inv_mul, one_smul, one_smul] at h'
    exact eq_of_castW_eq hNcase hW hχ hψ hβ h'
  obtain ⟨u, hu⟩ : ∃ u : W → X, ∀ χ, u χ = b (nfWt (Nat.card Kˣ) m j χ) := ⟨_, fun _ => rfl⟩
  have hu0 : ∀ χ : W, u χ ≠ 0 := fun χ => by rw [hu]; exact hb.ne_zero _ (hWC χ χ.2)
  have huwt : ∀ χ : W, u χ ∈ D.wtSpace ρ (nfWt (Nat.card Kˣ) m j χ) := fun χ => by
    rw [hu]; exact hb.mem_wtSpace _ (hWC χ χ.2)
  have hli : LinearIndependent K u := by
    have hind := (D4Datum.iSupIndep_wtSpace D ρ).comp
      (f := fun χ : W => nfWt (Nat.card Kˣ) m j χ) (fun χ ψ h => Subtype.ext (by
        have := hinj χ χ.2 ψ ψ.2 0 (Finset.mem_insert_self _ _) (by rw [add_zero]; exact h.symm)
        rw [add_zero] at this
        exact this.symm))
    exact hind.linearIndependent _ huwt hu0
  have hspan : ⊤ ≤ Submodule.span K (Set.range u) := by
    rw [← hb.span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨χ, hχ, rfl⟩ := hCW a ha
    exact ⟨⟨χ, hχ⟩, hu _⟩
  set v := Module.Basis.mk hli hspan with hv
  have hvu : ∀ χ, v χ = u χ := fun χ => Module.Basis.mk_apply hli hspan χ
  refine ⟨W, hW, v, fun β hβ t χ => ?_, fun z χ => ?_⟩
  ·
    have hsum : ∑ ψ, rootElt W β (t ^ 2 ^ j) ψ χ • v ψ =
        v χ + if h : (χ : Fin 4 → ℤ) + β ∈ W then t ^ 2 ^ j • v ⟨_, h⟩ else 0 := by
      have e1 : ∀ ψ : W, rootElt W β (t ^ 2 ^ j) ψ χ • v ψ =
          (if ψ = χ then v ψ else 0) +
            (if (ψ : Fin 4 → ℤ) = χ + β then t ^ 2 ^ j • v ψ else 0) := fun ψ => by
        simp only [rootElt, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, rootMat,
          Matrix.of_apply, smul_eq_mul, add_smul]
        congr 1
        · split_ifs <;> simp
        · split_ifs <;> simp
      rw [Finset.sum_congr rfl fun ψ _ => e1 ψ, Finset.sum_add_distrib, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _)]
      congr 1
      split_ifs with h
      · rw [Finset.sum_eq_single ⟨_, h⟩ (fun ψ _ hψ => by
          rw [if_neg (fun h' => hψ (Subtype.ext h'))]) (fun h' => absurd (Finset.mem_univ _) h'),
          if_pos rfl]
      · exact Finset.sum_eq_zero fun ψ _ => by
          rw [if_neg (fun h' : (ψ : Fin 4 → ℤ) = χ + β => h (h' ▸ ψ.2))]
    rw [hsum, hvu, hu, posX, hb.root _ (isD4Root_halfVec β hβ) t _ (hWC χ χ.2),
      ← nfWt_posRoot hm' j β hβ, ← nfWt_add]
    congr 1
    split_ifs with h1 h2 h2
    · rw [hvu, hu]
    · obtain ⟨ψ, hψ, hψe⟩ := hCW _ h1
      exact absurd (hinj χ χ.2 ψ hψ β (Finset.mem_insert_of_mem hβ) hψe ▸ hψ) h2
    · exact absurd (hWC _ h2) h1
    · rfl
  ·
    rw [hvu, (huwt χ) z, wtChar_nfWt]

end Basis

end CFSG.RankThree.GF2n.Stroth80.Ext1D4
