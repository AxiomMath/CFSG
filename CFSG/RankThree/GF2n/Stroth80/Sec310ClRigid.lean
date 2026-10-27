module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClScalar
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClPairDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClQuad

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : LinearMap.BilinForm K V}

theorem rigidity_core (hnd : F.Nondegenerate) (halt : F.IsAlt)
    (hdim : 3 ≤ Module.finrank K V) {H : Subgroup (V ≃ₗ[K] V)}
    (hF1 : ∀ e f : V, e ∈ ElPts F H → f ∈ ElPts F H → F e f = 1 → ∃ Q, PairForm F H e f Q)
    {e r' s' : V} (hr' : r' ∈ ElPts F H) (hs' : s' ∈ ElPts F H)
    (her : F e r' = 1) (hes : F e s' = 1) (hrs : F r' s' ≠ 0)
    (hind : ∀ a b : K, e ≠ a • r' + b • s')
    {Q Q' : QuadraticForm K V} (hQ : Q.polarBilin = F) (hQ' : Q'.polarBilin = F) (κ : K)
    (hκ : ∀ v, Q' v = Q v + κ * (F v e) ^ 2)
    (hQr : H ⊓ pointRadSubgroup F r' ≤ orthSubgroup Q)
    (hQs : H ⊓ pointRadSubgroup F s' ≤ orthSubgroup Q') : κ = 0 := by
  obtain ⟨c, hcdef⟩ : ∃ c : K, c = (F r' s')⁻¹ := ⟨_, rfl⟩
  have hc : c ≠ 0 := by
    rw [hcdef]
    exact inv_ne_zero hrs
  obtain ⟨s'', hs''def⟩ : ∃ s'' : V, s'' = c • s' := ⟨_, rfl⟩
  have hr's'' : F r' s'' = 1 := by
    rw [hs''def, map_smul, smul_eq_mul, hcdef, inv_mul_cancel₀ hrs]
  have hs''ne : s'' ≠ 0 := by
    rw [hs''def]
    exact smul_ne_zero hc hs'.1
  have hpr : pointRadSubgroup F s'' = pointRadSubgroup F s' := by
    rw [hs''def]
    exact pointRad_smul hc
  have hpr_set : pointRad F s'' = pointRad F s' := by
    unfold pointRad
    rw [hpr]
  have hs''mem : s'' ∈ ElPts F H := by
    show s'' ≠ 0 ∧ ElationFull F ((H : Set (V ≃ₗ[K] V)) ∩ pointRad F s'') s''
    refine ⟨hs''ne, ?_⟩
    rw [hpr_set, hs''def]
    exact (elationFull_smul hc).mpr hs'.2
  obtain ⟨Q'', hQ''⟩ := hF1 r' s'' hr' hs''mem hr's''
  have hD1 : ∀ g ∈ (H : Set (V ≃ₗ[K] V)) ∩ pointRad F r', ∀ v, Q (g v) = Q v :=
    fun g hg v => hQr (Subgroup.mem_inf.mpr ⟨hg.1, hg.2⟩) v
  have hD1'' : ∀ g ∈ (H : Set (V ≃ₗ[K] V)) ∩ pointRad F r', ∀ v, Q'' (g v) = Q'' v :=
    fun g hg v => hQ''.2.2.2.1 (Subgroup.mem_inf.mpr ⟨hg.1, hg.2⟩) v
  obtain ⟨c₁, hc₁⟩ := quadForm_eq_of_elationFull hnd halt hdim hr's''
    (D := (H : Set (V ≃ₗ[K] V)) ∩ pointRad F r') Set.inter_subset_right hr'.2
    hQ hQ''.1 hD1 hD1''
  have hD2 : ∀ g ∈ (H : Set (V ≃ₗ[K] V)) ∩ pointRad F s'', ∀ v, Q' (g v) = Q' v := by
    intro g hg v
    have hg2 : g ∈ pointRadSubgroup F s' := by
      rw [← hpr]
      exact hg.2
    exact hQs (Subgroup.mem_inf.mpr ⟨hg.1, hg2⟩) v
  have hD2'' : ∀ g ∈ (H : Set (V ≃ₗ[K] V)) ∩ pointRad F s'', ∀ v, Q'' (g v) = Q'' v :=
    fun g hg v => hQ''.2.2.2.2 (Subgroup.mem_inf.mpr ⟨hg.1, hg.2⟩) v
  have hF's'' : F s'' r' = 1 := by
    rw [form_comm halt]
    exact hr's''
  obtain ⟨μ, hμ⟩ := quadForm_eq_of_elationFull hnd halt hdim hF's''
    (D := (H : Set (V ≃ₗ[K] V)) ∩ pointRad F s'') Set.inter_subset_right hs''mem.2
    hQ' hQ''.1 hD2 hD2''
  have hnot : e ∉ Submodule.span K ({r', s''} : Set V) := by
    intro hmem
    obtain ⟨a₀, b₀, hab⟩ := Submodule.mem_span_pair.mp hmem
    apply hind a₀ (b₀ * c)
    rw [← hab, hs''def, smul_smul]
  obtain ⟨f₀, hf₀e, hf₀le⟩ := Submodule.exists_le_ker_of_notMem hnot
  obtain ⟨φ, hφe, hφr, hφs⟩ : ∃ φ : V →ₗ[K] K, φ e = 1 ∧ φ r' = 0 ∧ φ s'' = 0 := by
    have hr0 : f₀ r' = 0 :=
      LinearMap.mem_ker.mp (hf₀le (Submodule.subset_span (Set.mem_insert r' _)))
    have hs0 : f₀ s'' = 0 :=
      LinearMap.mem_ker.mp
        (hf₀le (Submodule.subset_span (Set.mem_insert_of_mem r' (Set.mem_singleton s''))))
    refine ⟨(f₀ e)⁻¹ • f₀, ?_, ?_, ?_⟩
    · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₀e]
    · rw [LinearMap.smul_apply, hr0, smul_zero]
    · rw [LinearMap.smul_apply, hs0, smul_zero]
  obtain ⟨v₀, hv₀⟩ := exists_vec_of_linear hnd (fun x y => form_comm halt x y) φ
  have hA : F v₀ r' = 0 := by rw [form_comm halt, hv₀, hφr]
  have hB : F v₀ s'' = 0 := by rw [form_comm halt, hv₀, hφs]
  have hC : F v₀ e = 1 := by rw [form_comm halt, hv₀, hφe]
  have h1 := hc₁ v₀
  have h2 := hμ v₀
  have h3 := hκ v₀
  rw [hA] at h1
  rw [hB] at h2
  rw [hC] at h3
  linear_combination -h3 - h2 + h1

theorem same_form_of_common_opposite (hnd : F.Nondegenerate) (halt : F.IsAlt)
    (hdim : 4 ≤ Module.finrank K V) (hq : 4 ≤ Nat.card K) {H : Subgroup (V ≃ₗ[K] V)}
    (hH : H ≤ sympSubgroup F)
    (hF1 : ∀ e f : V, e ∈ ElPts F H → f ∈ ElPts F H → F e f = 1 → ∃ Q, PairForm F H e f Q)
    {e f s : V} (he : e ∈ ElPts F H) (hf : f ∈ ElPts F H) (hs : s ∈ ElPts F H)
    (hef : F e f = 1) (hes : F e s = 1) {a : V → K} (ha : AData F H e f a)
    {Q Q' : QuadraticForm K V} (hQ : PairForm F H e f Q) (hQ' : PairForm F H e s Q') :
    Q = Q' := by
  have hdim3 : 3 ≤ Module.finrank K V := by omega
  have hfe : F f e = 1 := by
    rw [form_comm halt]
    exact hef
  have hse : F s e = 1 := by
    rw [form_comm halt]
    exact hes
  obtain ⟨κ, hκ⟩ := quadForm_eq_of_elationFull hnd halt hdim3 hef
    (D := (H : Set (V ≃ₗ[K] V)) ∩ pointRad F e) Set.inter_subset_right he.2 hQ.1 hQ'.1
    (fun g hg v => hQ.2.2.2.1 (Subgroup.mem_inf.mpr ⟨hg.1, hg.2⟩) v)
    (fun g hg v => hQ'.2.2.2.1 (Subgroup.mem_inf.mpr ⟨hg.1, hg.2⟩) v)
  have hκs : κ = Q s := by
    have h0 := hκ s
    rw [hQ'.2.2.1, hse, one_pow, mul_one] at h0
    linear_combination -h0 - (Q s) * (two_eq_zero_K (K := K))
  have hWQ : ∀ w, F w e = 0 → F w f = 0 → Q w = a w := by
    intro w hwe hwf
    obtain ⟨g, hg, hgw⟩ := ha.1 w hwe hwf
    have hgorth : g ∈ orthSubgroup Q := hQ.2.2.2.1 hg
    have key :=
      (pointRad_mem_orth_iff halt hef hQ.1 hQ.2.1 (Subgroup.mem_inf.mp hg).2).mp hgorth
    rw [hgw] at key
    have hfw : F f w = 0 := by
      rw [form_comm halt]
      exact hwf
    have e1 : Q (w + a w • e) = Q w := by
      rw [qf_add hQ.1, qf_smul, hQ.2.1, map_smul, hwe]
      simp
    have e2 : F f (w + a w • e) = a w := by
      rw [map_add, map_smul, hfw, hfe, smul_eq_mul, mul_one, zero_add]
    rw [e1, e2] at key
    exact key
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : K, c₀ = F s f := ⟨_, rfl⟩
  obtain ⟨w₀, hw₀def⟩ : ∃ w₀ : V, w₀ = s + f + c₀ • e := ⟨_, rfl⟩
  have hw₀e : F w₀ e = 0 := by
    rw [hw₀def]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hse,
      hfe, form_self halt]
    linear_combination (two_eq_zero_K (K := K))
  have hw₀f : F w₀ f = 0 := by
    rw [hw₀def]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hef,
      form_self halt]
    linear_combination -hc₀ + c₀ * (two_eq_zero_K (K := K))
  have hfw0 : F f w₀ = 0 := by
    rw [form_comm halt]
    exact hw₀f
  have hsdecomp : s = f + (w₀ + c₀ • e) := by
    have h2 : f + (w₀ + c₀ • e) = s + (f + f) + (c₀ • e + c₀ • e) := by
      rw [hw₀def]
      abel
    rw [h2, vec_add_self K f, vec_add_self K (c₀ • e), add_zero, add_zero]
  have hQs_eq : Q s = a w₀ + c₀ := by
    have hQw0 : Q w₀ = a w₀ := hWQ w₀ hw₀e hw₀f
    have hQsz : Q (f + (w₀ + c₀ • e)) = a w₀ + c₀ := by
      simp only [qf_add hQ.1, qf_smul, hQ.2.1, hQ.2.2.1, hQw0, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hw₀e, hfw0, hfe]
      ring
    exact (congrArg Q hsdecomp).trans hQsz
  have hκw : κ = a w₀ + c₀ := hκs.trans hQs_eq
  have hak : a w₀ + κ = c₀ := by
    linear_combination hκw + (a w₀) * (two_eq_zero_K (K := K))
  obtain ⟨g₀, hg₀, hg₀f⟩ := ha.1 w₀ hw₀e hw₀f
  have hg₀P : g₀ ∈ pointRadSubgroup F e := (Subgroup.mem_inf.mp hg₀).2
  have hg₀H : g₀ ∈ H := (Subgroup.mem_inf.mp hg₀).1
  have hg₀e : g₀ e = e := (mem_pointRad_iff.mp hg₀P).2.1
  have hg₀sq : g₀ * g₀ = 1 := pointRad_mul_self halt hef hg₀P
  have hgf₀ : g₀ f = f + (w₀ + a w₀ • e) := by
    rw [← hg₀f]
    abel
  have hvec : a w₀ • e + κ • e = c₀ • e := by
    rw [← add_smul, hak]
  have hgs : g₀ (f + κ • e) = s := by
    rw [map_add, map_smul, hg₀e, hgf₀, hsdecomp, ← hvec]
    abel
  have hg₀s : g₀ s = f + κ • e := by
    have h2 : g₀ (g₀ (f + κ • e)) = f + κ • e := by
      rw [← LinearEquiv.mul_apply, hg₀sq]
      rfl
    rw [hgs] at h2
    exact h2
  have hκ0 : κ = 0 := by
    by_contra hκne
    have hcex : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hsurj : Function.Surjective (fun b : Bool => if b then (1 : K) else 0) := by
        intro x
        by_cases hx : x = 0
        · exact ⟨false, by simp [hx]⟩
        · exact ⟨true, by simp [hcon x hx]⟩
      have hle := Nat.card_le_card_of_surjective _ hsurj
      have hB : Nat.card Bool = 2 := by simp
      omega
    obtain ⟨u, hue, huf, hune, hau⟩ : ∃ u : V, F u e = 0 ∧ F u f = 0 ∧ u ≠ 0 ∧ a u ≠ κ := by
      obtain ⟨u₀, hu₀ne, hu₀e, hu₀f⟩ := exists_perp_ne_zero (F := F) hdim3 e f
      obtain ⟨c, hc0, hc1⟩ := hcex
      by_cases h0 : a u₀ = κ
      · refine ⟨c • u₀, ?_, ?_, smul_ne_zero hc0 hu₀ne, ?_⟩
        · rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hu₀e, mul_zero]
        · rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hu₀f, mul_zero]
        · rw [ha.2.1 c u₀ hu₀e hu₀f, h0]
          intro hc2
          apply hκne
          have hc1' : c + 1 ≠ 0 := by
            intro h
            apply hc1
            linear_combination h - (two_eq_zero_K (K := K))
          have hsq : (c + 1) ^ 2 * κ = 0 := by
            linear_combination hc2 + (κ + c * κ) * (two_eq_zero_K (K := K))
          exact (mul_eq_zero.mp hsq).resolve_left (pow_ne_zero 2 hc1')
      · exact ⟨u₀, hu₀e, hu₀f, hu₀ne, h0⟩
    obtain ⟨gu, hgu, hguf⟩ := ha.1 u hue huf
    have hguP : gu ∈ pointRadSubgroup F e := (Subgroup.mem_inf.mp hgu).2
    have hguH : gu ∈ H := (Subgroup.mem_inf.mp hgu).1
    have hgue : gu e = e := (mem_pointRad_iff.mp hguP).2.1
    have hguf' : gu f = f + (u + a u • e) := by
      rw [← hguf]
      abel
    obtain ⟨kk, hkk⟩ : ∃ kk : V ≃ₗ[K] V, kk = gu * g₀ := ⟨_, rfl⟩
    have hkkH : kk ∈ H := by
      rw [hkk]
      exact H.mul_mem hguH hg₀H
    have hkkP : kk ∈ pointRadSubgroup F e := by
      rw [hkk]
      exact (pointRadSubgroup F e).mul_mem hguP hg₀P
    obtain ⟨s', hs'def⟩ : ∃ s' : V, s' = kk s := ⟨_, rfl⟩
    have hs'eq : s' = f + u + (a u + κ) • e := by
      rw [hs'def, hkk, LinearEquiv.mul_apply, hg₀s, map_add, map_smul, hgue, hguf', add_smul]
      abel
    have hs'0 : s' ≠ 0 := by
      rw [hs'def]
      intro h0
      exact hs.1 (kk.map_eq_zero_iff.mp h0)
    have hs'mem : s' ∈ ElPts F H := by
      show s' ≠ 0 ∧ ElationFull F ((H : Set (V ≃ₗ[K] V)) ∩ pointRad F s') s'
      refine ⟨hs'0, ?_⟩
      rw [hs'def]
      exact elationFull_conj hH hs.2 hkkH
    have heu : F e u = 0 := by
      rw [form_comm halt]
      exact hue
    have hfu : F f u = 0 := by
      rw [form_comm halt]
      exact huf
    have hes' : F e s' = 1 := by
      rw [hs'eq]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hef, heu, form_self halt]
      ring
    have hfs' : F f s' = a u + κ := by
      rw [hs'eq]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hfe, hfu, form_self halt]
      ring
    have hrs' : F f s' ≠ 0 := by
      rw [hfs']
      intro h0
      apply hau
      linear_combination h0 - κ * (two_eq_zero_K (K := K))
    have hind' : ∀ α β : K, e ≠ α • f + β • s' := by
      intro α β heq
      have p1 : α + β = 0 := by
        have h := congrArg (F e) heq
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          hef, hes', form_self halt] at h
        linear_combination -h
      have hαβ : α = β := by
        linear_combination p1 - β * (two_eq_zero_K (K := K))
      have p2 : β * (a u + κ) = 1 := by
        have h := congrArg (fun x => F x f) heq
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          hef, form_self halt] at h
        rw [form_comm halt s' f, hfs'] at h
        linear_combination -h
      have hp2e : (β * (a u + κ)) • e = e := by
        rw [p2, one_smul]
      rw [hαβ, hs'eq] at heq
      have key : β • u = 0 := by
        linear_combination (norm := module) -heq - (vec_add_self K (β • f)) - hp2e
      have hβ : β = 0 := by
        by_contra hβ0
        exact hune ((smul_eq_zero.mp key).resolve_left hβ0)
      rw [hβ, zero_mul] at p2
      exact zero_ne_one p2
    have hQs' : H ⊓ pointRadSubgroup F s' ≤ orthSubgroup Q' := by
      intro g hg
      obtain ⟨hgH, hgP⟩ := Subgroup.mem_inf.mp hg
      have hksym : kk⁻¹ ∈ sympSubgroup F := hH (H.inv_mem hkkH)
      have hconj := conj_mem_pointRad hksym hgP
      have hinv_s' : kk⁻¹ s' = s := by
        rw [hs'def]
        simp
      rw [inv_inv, hinv_s'] at hconj
      have hk : kk⁻¹ * g * kk ∈ H ⊓ pointRadSubgroup F s :=
        Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem (H.inv_mem hkkH) hgH) hkkH, hconj⟩
      have hkQ' : kk⁻¹ * g * kk ∈ orthSubgroup Q' := hQ'.2.2.2.2 hk
      have hkkQ' : kk ∈ orthSubgroup Q' := hQ'.2.2.2.1 (Subgroup.mem_inf.mpr ⟨hkkH, hkkP⟩)
      have hgeq : g = kk * (kk⁻¹ * g * kk) * kk⁻¹ := by group
      rw [hgeq]
      exact (orthSubgroup Q').mul_mem ((orthSubgroup Q').mul_mem hkkQ' hkQ')
        ((orthSubgroup Q').inv_mem hkkQ')
    exact hκne (rigidity_core hnd halt hdim3 hF1 hf hs'mem hef hes' hrs' hind' hQ.1 hQ'.1 κ
      hκ hQ.2.2.2.2 hQs')
  refine QuadraticMap.ext fun v => ?_
  rw [hκ v, hκ0, zero_mul, add_zero]

end CFSG.RankThree.GF2n.Stroth80.Classify
