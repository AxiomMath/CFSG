module

public import CFSG.Sporadic.Co2Smith.GlRootTrans
public import CFSG.Sporadic.Co2Smith.GlSteinConc

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.Sporadic.Co2Cert
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

section Charts

variable
  {G : Type*} [Group G] {z : G} {φ : centralizer ({z} : Set G) ≃* Cz} {ρ : C0c →* G}
  {α3c : Cz}

theorem frameConjK_cases (k : ℕ) :
    frameConjK k = 1 ∨ frameConjK k = δ1hK ∨ frameConjK k = δ1hK * δ0hK ∨
      frameConjK k = w1K ∨ frameConjK k = w1K * δ1hK ∨ frameConjK k = w1K * δ1hK * δ0hK := by
  unfold frameConjK
  split_ifs <;> simp

theorem transp_frameConjK (hm : SmithC0Marking φ α3c ρ) (hL : W1Levi φ ρ) (hD : D1Core φ ρ)
    (k : ℕ) : Transp φ ρ (frameConjK k) := by
  have P1 := transp_w1 hL
  have P2 := transp_w2 hm
  have Pd1 := transp_d1 hD P1 P2
  have Pd0 := transp_d0 hm
  rcases frameConjK_cases k with h | h | h | h | h | h <;> rw [h]
  · exact Transp.one
  · exact Pd1
  · exact Transp.mul δ1hK_mem_C0c δ0hK_mem_C0c Pd1 Pd0
  · exact P1
  · exact Transp.mul w1K_mem_C0c δ1hK_mem_C0c P1 Pd1
  · exact Transp.mul (C0c.mul_mem w1K_mem_C0c δ1hK_mem_C0c) δ0hK_mem_C0c
      (Transp.mul w1K_mem_C0c δ1hK_mem_C0c P1 Pd1) Pd0

variable (φ ρ) in
@[expose] noncomputable def chartMap (k : ℕ) (y : K) : G :=
  (rhoK ρ (frameConjK k))⁻¹ * phiInv φ (frameConjK k * y * (frameConjK k)⁻¹) *
    rhoK ρ (frameConjK k)

theorem conj_mem_Cz_of_comm {k : ℕ} (hk : k < 6) {y : K} (hy : y * xLongK k = xLongK k * y) :
    frameConjK k * y * (frameConjK k)⁻¹ ∈ Cz := by
  apply mem_Cz_of_comm
  have e := frameConjK_conj hk
  have e' : z0 = frameConjK k * xLongK k * (frameConjK k)⁻¹ := by
    rw [e]
    group
  rw [e', show frameConjK k * y * (frameConjK k)⁻¹ * (frameConjK k * xLongK k *
    (frameConjK k)⁻¹) = frameConjK k * (y * xLongK k) * (frameConjK k)⁻¹ by group, hy]
  group

theorem chartMap_mul {k : ℕ} (hk : k < 6) {y y' : K} (hy : y * xLongK k = xLongK k * y)
    (hy' : y' * xLongK k = xLongK k * y') :
    chartMap φ ρ k (y * y') = chartMap φ ρ k y * chartMap φ ρ k y' := by
  unfold chartMap
  rw [show frameConjK k * (y * y') * (frameConjK k)⁻¹ =
    (frameConjK k * y * (frameConjK k)⁻¹) * (frameConjK k * y' * (frameConjK k)⁻¹) by group,
    phiInv_mul φ (conj_mem_Cz_of_comm hk hy) (conj_mem_Cz_of_comm hk hy')]
  group

theorem chartMap_one (k : ℕ) : chartMap φ ρ k 1 = 1 := by
  unfold chartMap
  rw [show frameConjK k * 1 * (frameConjK k)⁻¹ = 1 by group, phiInv_one]
  group

theorem psiE_eq_chartMap (hm : SmithC0Marking φ α3c ρ) (hL : W1Levi φ ρ) (hD : D1Core φ ρ)
    {k : ℕ} (hk : k < 6) {y : K} (hyR : y ∈ rootSet) (hy : y * xLongK k = xLongK k * y) :
    psiE φ ρ y = chartMap φ ρ k y := by
  have P := (transp_frameConjK hm hL hD k).2 y hyR
  rw [psiE_of_mem φ ρ (conj_mem_Cz_of_comm hk hy)] at P
  unfold chartMap
  rw [← P]
  group

end Charts

section Relations

variable
  {G : Type} [Group G] {z : G} {φ : centralizer ({z} : Set G) ≃* Cz} {ρ : C0c →* G}
  {α3c : Cz}

variable (φ ρ) in
@[expose] noncomputable def psiGS (γ : Fin su6D.rank → ℤ) (x : su6D.rootGroup γ) : G :=
  psiE φ ρ (psiRootK γ x)

theorem psiRootK_letter_eq {p : Σ γ : Fin su6D.rank → ℤ, su6D.rootGroup γ} {t : Fin 18}
    (h : p.1 = su6Root t) :
    psiRootK p.1 p.2 = xRootK (letIdx p).val (su6Entry (letIdx p) p.2).code.val := by
  have hs : su6Idx p.1 = some (letIdx p) := by rw [letIdx_eq h, h, su6Idx_su6Root]
  unfold psiRootK
  rw [hs]

theorem glCharts_spec :
    (∀ r < 18, ∀ s < 18, Native.stOpp r s = true ∨ Native.glBlockChart (Native.stBlock r s) < 6) ∧
      Native.glBlockChart [3, 9] < 6 ∧ Native.glBlockChart [5, 11] < 6 ∧
      Native.glBlockChart [14, 17] < 6 := by
  have h := glWeylChart_check
  simp only [Native.glWeylChartOK, Native.glChartsOK, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] at h
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem inChart_of_blockChart {B : List ℕ} (h : Native.glBlockChart B < 6) :
    ∀ t ∈ B, Native.glInChart t (Native.glBlockChart B) = true := by
  unfold Native.glBlockChart at h ⊢
  cases hf : (List.range 6).find? (fun k => B.all fun t => Native.glInChart t k) with
  | none =>
    rw [hf] at h
    simp at h
  | some k =>
    have hk := List.find?_some hf
    simp only [List.all_eq_true] at hk
    simpa using hk

theorem chartMap_prod {k : ℕ} (hk : k < 6) :
    ∀ ys : List K, (∀ y ∈ ys, y * xLongK k = xLongK k * y) →
      chartMap φ ρ k ys.prod = (ys.map (chartMap φ ρ k)).prod := by
  intro ys
  induction ys with
  | nil => exact fun _ => chartMap_one k
  | cons y ys ih =>
    intro h
    have hy := h y List.mem_cons_self
    have hys : ys.prod * xLongK k = xLongK k * ys.prod := by
      have : ∀ zs : List K, (∀ y ∈ zs, y * xLongK k = xLongK k * y) →
          zs.prod * xLongK k = xLongK k * zs.prod := by
        intro zs
        induction zs with
        | nil => simp
        | cons w zs ihz =>
          intro hz
          rw [List.prod_cons, mul_assoc, ihz (fun y hy => hz y (List.mem_cons_of_mem _ hy)),
            ← mul_assoc, hz w List.mem_cons_self, mul_assoc]
      exact this ys fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [List.prod_cons, chartMap_mul hk hy hys, List.map_cons, List.prod_cons,
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem relationsHold_block_G (hm : SmithC0Marking φ α3c ρ) (hL : W1Levi φ ρ)
    (hD : D1Core φ ρ) {B : List ℕ} (h : Native.stCheck (Native.stGens B) = true)
    (hc : Native.glBlockChart B < 6) :
    RelationsHold su6D.rootGroup {γ | ∃ t : Fin 18, t.val ∈ B ∧ γ = su6Root t} (psiGS φ ρ) := by
  intro l hl h1
  have hK := relationsHold_block h l hl h1
  have hmem : ∀ p ∈ l, psiRootK p.1 p.2 ∈ rootSet ∧
      psiRootK p.1 p.2 * xLongK (Native.glBlockChart B) =
        xLongK (Native.glBlockChart B) * psiRootK p.1 p.2 := by
    intro p hp
    obtain ⟨t, htB, ht⟩ := hl p hp
    rw [psiRootK_letter_eq ht]
    have hcode := (su6Entry (letIdx p) p.2).code.isLt
    refine ⟨⟨_, (letIdx p).isLt, _, hcode, rfl⟩, ?_⟩
    have hcode' := (su6Entry t p.2).code.isLt
    rw [letIdx_eq ht]
    exact xRootK_comm_of_inChart t.isLt hc (inChart_of_blockChart hc _ htB) hcode'
  have e : (l.map fun p => psiGS φ ρ p.1 p.2) =
      ((l.map fun p => psiRootK p.1 p.2).map (chartMap φ ρ (Native.glBlockChart B))) := by
    rw [List.map_map]
    refine List.map_congr_left fun p hp => ?_
    exact psiE_eq_chartMap hm hL hD hc (hmem p hp).1 (hmem p hp).2
  rw [e, ← chartMap_prod hc _ (fun y hy => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
    exact (hmem p hp).2), hK, chartMap_one]

theorem relationsHold_of_subset_G {S T : Set (Fin su6D.rank → ℤ)}
    (h : RelationsHold su6D.rootGroup T (psiGS φ ρ)) (hST : S ⊆ T) :
    RelationsHold su6D.rootGroup S (psiGS φ ρ) :=
  fun l hl h1 => h l (fun p hp => hST (hl p hp)) h1

theorem psiGS_relations (hm : SmithC0Marking φ α3c ρ) (hL : W1Levi φ ρ) (hD : D1Core φ ρ) :
    ∀ S ∈ su6D.relsR1 ∪ su6D.relsR2, RelationsHold su6D.rootGroup S (psiGS φ ρ) := by
  obtain ⟨hcone, h39, h511, h1417⟩ := glStein_parts
  obtain ⟨ccone, c39, c511, c1417⟩ := glCharts_spec
  rintro S (⟨α, hα, β, hβ, hneg, rfl⟩ | ⟨i, rfl⟩)
  · obtain ⟨r, rfl⟩ := (mem_su6D_roots_iff' α).1 hα
    obtain ⟨s, rfl⟩ := (mem_su6D_roots_iff' β).1 hβ
    have hnopp : Native.stOpp r.val s.val = false := by
      by_contra hopp
      apply hneg
      refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
      rw [one_smul, one_smul]
      exact (stOpp_iff r s).1 (by simpa using hopp)
    have hchk : Native.stCheck (Native.stGens (Native.stBlock r s)) = true := by
      rcases hcone r.val r.isLt s.val s.isLt with h | h
      · rw [hnopp] at h
        exact absurd h (by decide)
      · exact h
    have hch : Native.glBlockChart (Native.stBlock r s) < 6 := by
      rcases ccone r.val r.isLt s.val s.isLt with h | h
      · rw [hnopp] at h
        exact absurd h (by decide)
      · exact h
    exact relationsHold_of_subset_G (relationsHold_block_G hm hL hD hchk hch)
      (cone_subset_block r s)
  · fin_cases i
    · refine relationsHold_of_subset_G (relationsHold_block_G hm hL hD h39 c39) ?_
      rintro γ (rfl | rfl)
      · exact ⟨3, by decide, by decide⟩
      · exact ⟨9, by decide, by decide⟩
    · refine relationsHold_of_subset_G (relationsHold_block_G hm hL hD h511 c511) ?_
      rintro γ (rfl | rfl)
      · exact ⟨5, by decide, by decide⟩
      · exact ⟨11, by decide, by decide⟩
    · refine relationsHold_of_subset_G (relationsHold_block_G hm hL hD h1417 c1417) ?_
      rintro γ (rfl | rfl)
      · exact ⟨14, by decide, by decide⟩
      · exact ⟨17, by decide, by decide⟩

theorem exists_thetaG (hm : SmithC0Marking φ α3c ρ) (hL : W1Levi φ ρ) (hD : D1Core φ ρ) :
    ∃ θ : SU6 →* G, ∀ γ ∈ su6D.roots, ∀ x : su6D.rootGroup γ, θ x = psiGS φ ρ γ x :=
  su6D_steinbergPresentation.2 G (psiGS φ ρ) (psiGS_relations hm hL hD)

end Relations

end CFSG.Sporadic.Co2Smith
