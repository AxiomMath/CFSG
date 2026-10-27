module

public import CFSG.OddTranspositions.PartThree.Twelve.NineAxis
public import CFSG.OddTranspositions.PartThree.Twelve.NineCenter
public import CFSG.OddTranspositions.PartThree.Twelve.SevenClasses

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.Fischer QuadraticMap
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK

section Forms

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem span_setOf_eq_one_eq_top [Finite K] [CharP K 2] (hK : 2 < Nat.card K)
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) :
    Submodule.span K {v | Q v = 1} = ⊤ := by
  classical
  have hmem1 : ∀ v : V, Q v ≠ 0 → v ∈ Submodule.span K {v | Q v = 1} := by
    intro v hv
    obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (Q v)
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hs
      exact hv hs
    have hQinv : Q (s⁻¹ • v) = 1 := by
      rw [QuadraticMap.map_smul Q s⁻¹ v, hs, smul_eq_mul]
      calc s⁻¹ * s⁻¹ * (s * s) = (s⁻¹ * s) * (s⁻¹ * s) := by ring
        _ = 1 * 1 := by rw [inv_mul_cancel₀ hs0]
        _ = 1 := one_mul 1
    have hsv : v = s • (s⁻¹ • v) := by
      rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]
    rw [hsv]
    exact Submodule.smul_mem _ s (Submodule.subset_span hQinv)
  refine Submodule.eq_top_iff'.mpr fun v => ?_
  by_cases hv : Q v = 0
  · by_cases hv0 : v = 0
    · rw [hv0]; exact Submodule.zero_mem _
    · obtain ⟨x₀, hx₀⟩ : ∃ x, polar Q x v ≠ 0 := by
        by_contra h
        push Not at h
        exact hv0 (hQ.2 v (fun x => by rw [polarBilin_apply_apply]; exact h x))
      set x : V := (polar Q x₀ v)⁻¹ • x₀ with hxdef
      have hpx : polar Q x v = 1 := by
        rw [hxdef, QuadraticMap.polar_smul_left, smul_eq_mul, inv_mul_cancel₀ hx₀]
      have hQexp : ∀ μ : K, Q (x + μ • v) = Q x + μ := by
        intro μ
        rw [QuadraticMap.map_add Q x (μ • v)]
        rw [QuadraticMap.map_smul Q μ v, hv, smul_zero, add_zero]
        rw [QuadraticMap.polar_smul_right Q μ x v, hpx, smul_eq_mul, mul_one]
      haveI : Fintype K := Fintype.ofFinite K
      have hcardK : 2 < Fintype.card K := by
        rw [← Nat.card_eq_fintype_card]; exact hK
      have hcard_lt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
        rw [Finset.card_univ]
        have : ({0, 1} : Finset K).card ≤ 2 := by simp
        omega
      obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
      have ht0 : t ≠ 0 := fun h => ht (by simp [h])
      have ht1 : t ≠ 1 := fun h => ht (by simp [h])
      set y : V := x + (Q x + t) • v with hydef
      have hQy : Q y = t := by
        rw [hydef, hQexp (Q x + t)]
        exact CharTwo.add_cancel_left (Q x) t
      have hvy_eq : v + y = x + (1 + (Q x + t)) • v := by
        rw [hydef]
        conv_rhs => rw [add_smul, one_smul]
        abel
      have hQvy : Q (v + y) = 1 + t := by
        rw [hvy_eq, hQexp (1 + (Q x + t))]
        calc Q x + (1 + (Q x + t)) = Q x + (Q x + (1 + t)) := by abel
          _ = 1 + t := CharTwo.add_cancel_left (Q x) (1 + t)
      have h1t : 1 + t ≠ 0 := by
        intro h
        refine ht1 ?_
        have h11 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
        rw [← h11] at h
        exact add_left_cancel h
      have hy_mem : y ∈ Submodule.span K {v | Q v = 1} :=
        hmem1 y (by rw [hQy]; exact ht0)
      have hvy_mem : v + y ∈ Submodule.span K {v | Q v = 1} :=
        hmem1 (v + y) (by rw [hQvy]; exact h1t)
      have hvsub : v = (v + y) - y := by abel
      rw [hvsub]
      exact Submodule.sub_mem _ hvy_mem hy_mem
  · exact hmem1 v hv

theorem eq_of_polar_eq_of_subset {Q Q' : QuadraticForm K V}
    (hpol : ∀ x y, polar Q x y = polar Q' x y) (hspan : Submodule.span K {v | Q v = 1} = ⊤)
    (hsub : ∀ v, Q v = 1 → Q' v = 1) : Q = Q' := by
  refine QuadraticMap.ext fun x => ?_
  have hx : x ∈ Submodule.span K {v | Q v = 1} := by rw [hspan]; trivial
  refine Submodule.span_induction (p := fun x _ => Q x = Q' x) ?_ ?_ ?_ ?_ hx
  · intro v hv
    have hv' : Q v = 1 := Set.mem_setOf_eq.mp hv
    rw [hv', hsub v hv']
  · simp
  · intro x y _ _ hx hy
    rw [QuadraticMap.map_add Q x y, QuadraticMap.map_add Q' x y, hpol x y, hx, hy]
  · intro a x _ hx
    rw [QuadraticMap.map_smul Q a x, QuadraticMap.map_smul Q' a x, hx]

end Forms

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem isHypLineSpace_sp (hIH : Theorem4Below (Nat.card G)) (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    (hdiam : ∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).Nonempty) :
    IsHypLineSpace D := by
  have hd_claim : ∀ b ∈ D, ¬ Commute b hC.d → ∀ c, c ∈ lineMem D hC.d b → c ≠ hC.d →
      ¬ Commute c hC.d ∧ lineMem D hC.d c = lineMem D hC.d b := by
    intro w hw hwd c hc hcne
    obtain ⟨k, F, _, _, _, hnk, hF, ⟨ch⟩⟩ := exists_spChart hC hMZ hα hs hSp
    obtain ⟨v, hv_d, hv_w⟩ := hdiam w hw hwd
    obtain ⟨Q, hQpol, hQw, -⟩ :=
      exists_quadraticForm_commSet_inter hIH hC hMZ hα hs hn hf hSp ch hnk hF hv_d hw hwd
        hv_w.2.1.symm
    have hQnd : (polarBilin Q).Nondegenerate := by
      have h_eq : polarBilin Q = CFSG.RankThree.Classical.spForm k F := LinearMap.ext₂ fun a b => by
        rw [polarBilin_apply_apply, hQpol a b]
      rw [h_eq]; exact CFSG.RankThree.Classical.spForm_nondegenerate
    have hKcard : 2 < Nat.card F := by
      rw [hF]
      have h2f : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      norm_num at h2f
      omega
    have hspanQ : Submodule.span F {x | Q x = 1} = ⊤ :=
      span_setOf_eq_one_eq_top hKcard hQnd
    have hnc : ¬ Commute c hC.d := by
      intro hcd
      have hc_d : c ∈ commSet D hC.d := ⟨hc.1, hcd, hcne⟩
      have hQone : ∀ x, Q x = 1 → CFSG.RankThree.Classical.spForm k F x (ch.vec c) = 0 := by
        intro x hx
        have hx0 : x ≠ 0 := by
          rintro rfl
          have : (0 : F) = 1 := by simpa using hx
          exact zero_ne_one this
        obtain ⟨z, hz_d, hzv⟩ := ch.exists_vec x hx0
        have hz_w : z ∈ commSet D w := (hQw z hz_d).mpr (by rw [hzv]; exact hx)
        have hzc := hc.2 ⟨⟨hz_d.1, hz_d.2.1⟩, ⟨hz_w.1, hz_w.2.1⟩⟩
        have := (ch.commute_iff z hz_d c hc_d).mp hzc.2
        rwa [hzv] at this
      have hzero : ∀ x, CFSG.RankThree.Classical.spForm k F x (ch.vec c) = 0 := by
        have hle : Submodule.span F {x | Q x = 1} ≤
            LinearMap.ker ((CFSG.RankThree.Classical.spForm k F).flip (ch.vec c)) := by
          rw [Submodule.span_le]
          intro x hx
          exact LinearMap.mem_ker.mpr (hQone x hx)
        rw [hspanQ] at hle
        intro x
        exact LinearMap.mem_ker.mp (hle trivial)
      exact ch.vec_ne_zero c hc_d (CFSG.RankThree.Classical.spForm_nondegenerate.2 (ch.vec c) hzero)
    refine ⟨hnc, ?_⟩
    have hsub_dw_dc : commSet D hC.d ∩ commSet D w ⊆ commSet D hC.d ∩ commSet D c := by
      intro z hz
      obtain ⟨hz_d, hz_w⟩ := hz
      refine ⟨hz_d, ?_⟩
      have hzc := hc.2 ⟨⟨hz_d.1, hz_d.2.1⟩, ⟨hz_w.1, hz_w.2.1⟩⟩
      exact ⟨hzc.1, hzc.2, fun h => hnc (h ▸ hz_d.2.1)⟩
    have hv_c : v ∈ commSet D c := (hsub_dw_dc ⟨hv_d, hv_w⟩).2
    obtain ⟨Q', hQ'pol, hQ'w, -⟩ :=
      exists_quadraticForm_commSet_inter hIH hC hMZ hα hs hn hf hSp ch hnk hF hv_d hc.1 hnc
        hv_c.2.1.symm
    have hQ_eq : Q = Q' := by
      refine eq_of_polar_eq_of_subset (fun x y => by rw [hQpol x y, hQ'pol x y]) hspanQ ?_
      intro x hx
      have hx0 : x ≠ 0 := by
        rintro rfl
        have : (0 : F) = 1 := by simpa using hx
        exact zero_ne_one this
      obtain ⟨z, hz_d, hzv⟩ := ch.exists_vec x hx0
      have hz_w : z ∈ commSet D w := (hQw z hz_d).mpr (by rw [hzv]; exact hx)
      have hz_c : z ∈ commSet D c := (hsub_dw_dc ⟨hz_d, hz_w⟩).2
      have := (hQ'w z hz_d).mp hz_c
      rwa [hzv] at this
    have hsets : commSet D hC.d ∩ commSet D w = commSet D hC.d ∩ commSet D c := by
      refine Set.Subset.antisymm hsub_dw_dc fun z hz => ?_
      obtain ⟨hz_d, hz_c⟩ := hz
      refine ⟨hz_d, ?_⟩
      exact (hQw z hz_d).mpr (by rw [hQ_eq]; exact (hQ'w z hz_d).mp hz_c)
    exact (lineMem_eq_of_commSet_inter_eq hwd hnc hsets).symm
  intro a ha b hb hba c hc hca
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hC.hd ha)
  let b' : G := g⁻¹ * b * g
  let c' : G := g⁻¹ * c * g
  have hb'D : b' ∈ D := by simpa [b'] using hC.setup.conj_mem g⁻¹ hb
  have hb'g : g * b' * g⁻¹ = b := by
    show g * (g⁻¹ * b * g) * g⁻¹ = b
    group
  have hc'g : g * c' * g⁻¹ = c := by
    show g * (g⁻¹ * c * g) * g⁻¹ = c
    group
  have hconjc' : (MulAut.conj g) c' = c := by rw [MulAut.conj_apply]; exact hc'g
  have hconjd : (MulAut.conj g) hC.d = a := by rw [MulAut.conj_apply]; exact hg
  have hb'd : ¬ Commute b' hC.d := by
    intro h
    exact hba (by
      have h' : Commute (g * b' * g⁻¹) (g * hC.d * g⁻¹) := (Commute.conj_iff g).mpr h
      rwa [hb'g, hg] at h')
  have hc'd : c' ≠ hC.d := by
    intro h
    have h1 : (MulAut.conj g) c' = (MulAut.conj g) hC.d := by rw [h]
    rw [hconjc', hconjd] at h1
    exact hca h1
  have hc'line : c' ∈ lineMem D hC.d b' := by
    have hline : lineMem D a b = (MulAut.conj g) '' lineMem D hC.d b' := by
      have h := lineMem_conj (E := D) (fun g' z hz => hC.setup.conj_mem g' hz) g hC.d b'
      rwa [hg, hb'g] at h
    have hmem : c ∈ (MulAut.conj g) '' lineMem D hC.d b' := by rw [← hline]; exact hc
    obtain ⟨y, hy, hyeq⟩ := hmem
    have hyy : y = c' := (MulAut.conj g).injective (by rw [hyeq, hconjc'])
    rw [hyy] at hy
    exact hy
  obtain ⟨hnc', hline'⟩ := hd_claim b' hb'D hb'd c' hc'line hc'd
  refine ⟨?_, ?_⟩
  · intro h
    have h' : Commute ((MulAut.conj g) c') ((MulAut.conj g) hC.d) := by
      rw [hconjc', hconjd]; exact h
    exact hnc' ((Commute.conj_iff g).mp (by simpa only [MulAut.conj_apply] using h'))
  · have hline_a_c : lineMem D a c = (MulAut.conj g) '' lineMem D hC.d c' := by
      have h := lineMem_conj (E := D) (fun g' z hz => hC.setup.conj_mem g' hz) g hC.d c'
      rwa [hg, hc'g] at h
    have hline_a_b : lineMem D a b = (MulAut.conj g) '' lineMem D hC.d b' := by
      have h := lineMem_conj (E := D) (fun g' z hz => hC.setup.conj_mem g' hz) g hC.d b'
      rwa [hg, hb'g] at h
    rw [hline_a_c, hline_a_b, hline']

theorem twelveNine_sp (hIH : Theorem4Below (Nat.card G)) (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hSp : IsSymplecticTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    (hdiam : ∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).Nonempty) (u : D)
    (σ : commGraph D ≃g commGraph D) (hσ : ∀ v : D, Commute (v : G) u → σ v = v) :
    (∀ v : D, σ v = v) ∨ ∀ v : D, (σ v : G) = (u : G) * v * u := by
  obtain ⟨⟨w₁, hw₁, hw₁d, hl₁⟩, ⟨w₂, hw₂, hw₂d, hl₂⟩⟩ :=
    twelveSeven_sp_exists hIH hC hMZ hα hs hn hf hSp
  have hgcd : Nat.gcd ((lineMem D hC.d w₁).ncard - 1) ((lineMem D hC.d w₂).ncard - 1) ∣ 2 := by
    rw [hl₁, hl₂]
    have h2f : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 2 ^ f + 1 - 1 = 2 ^ f := by omega
    have h2 : 2 ^ f - 1 - 1 = 2 ^ f - 2 := by omega
    rw [h1, h2, Nat.gcd_self_sub_right h2f]
    exact Nat.gcd_dvd_right _ _
  exact twelveNine_forall hC.setup (isHypLineSpace_sp hIH hC hMZ hα hs hn hf hSp hdiam)
    (fun a ha b hb h => eq_of_commSet_eq hC hα ha hb h) hC.hd hw₁ hw₂ hw₁d hw₂d hgcd u σ hσ

end CFSG.OddTranspositions.PartThree
