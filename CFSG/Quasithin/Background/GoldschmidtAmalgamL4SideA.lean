module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4Mat
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL4Rel
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2Label

public section

namespace CFSG.Quasithin.F6.GoldAmL4

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.F6.GoldAmL

variable {D : Type*} [Group D] [Finite D]

omit [Finite D] in
theorem mmul_mI_left (M : V4 × V4) : mmul mI M = M := by
  have h : ∀ v : V4, app mI v = v := fun v => by
    ext <;> simp [app, mI]
  unfold mmul
  rw [h, h]

theorem exists_A_tuple {G T : Subgroup D} (hv : Vertex G T)
    (ε : ↥(pCoreOf 2 G) ≃* Multiplicative V4) :
    ∃ a b s x : D, ARel a b s x ∧ Subgroup.closure ({a, b} : Set D) = pCoreOf 2 G ∧
      Subgroup.closure ({a, b, s} : Set D) = T ∧ Subgroup.closure ({a, b, s, x} : Set D) = G := by
  set Q : Subgroup D := pCoreOf 2 G with hQ
  have hTG : T ≤ G := hv.T_le
  have hQT : Q ≤ T := hv.pCoreOf_le
  have hQn : ∀ g ∈ G, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 G hg) q).mp hq
  have hC : ∀ g ∈ G, (∀ q ∈ Q, g * q = q * g) → g ∈ Q := by
    intro g hg hc
    apply hv.charTwo
    refine ⟨hg, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    exact (hc q hq).symm
  have hidx : (Q.subgroupOf T).index = 2 := hv.relIndex_pCoreOf_T
  have hmulQ : ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ * t₂ ∈ Q ↔ (t₁ ∈ Q ↔ t₂ ∈ Q) := by
    intro t₁ h₁ t₂ h₂
    have := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨t₁, h₁⟩) (b := ⟨t₂, h₂⟩)
    simpa [Subgroup.mem_subgroupOf] using this
  have hsqQ : ∀ t ∈ T, t * t ∈ Q := fun t ht => by
    rw [hmulQ t ht t ht]
  obtain ⟨s₀, hs₀T, hs₀Q⟩ : ∃ s₀ ∈ T, s₀ ∉ Q := by
    by_contra hcon
    push Not at hcon
    have : Q.subgroupOf T = ⊤ := by
      rw [eq_top_iff]
      intro t _
      exact Subgroup.mem_subgroupOf.mpr (hcon t t.2)
    rw [this, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)
  obtain ⟨x₀, hx₀G, hx₀o⟩ := hv.exists_order_three
  have hx₀3 : x₀ ^ 3 = 1 := hx₀o ▸ pow_orderOf_eq_one x₀
  have hx₀T : x₀ ∉ T := hv.not_mem_of_orderOf hx₀o
  have hx₀Q : x₀ ∉ Q := fun h => hx₀T (hQT h)
  have hQG : ∀ q ∈ Q, q ∈ G := fun q hq => hTG (hQT hq)
  have hs₀G : s₀ ∈ G := hTG hs₀T
  have hx₀x₀ : x₀ * x₀ ∈ G := G.mul_mem hx₀G hx₀G
  have hx₀inv : x₀⁻¹ ∈ G := G.inv_mem hx₀G
  have hx₀3' : x₀ * (x₀ * x₀) = 1 := by rw [← pow_three]; exact hx₀3
  have hxinv : x₀⁻¹ = x₀ * x₀ := by
    rw [inv_eq_iff_mul_eq_one]; exact hx₀3'
  obtain ⟨X, hX⟩ : ∃ X, X = mat ε x₀ := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = mat ε s₀ := ⟨_, rfl⟩
  have hXm : mmul X (mmul X X) = mI := by
    rw [hX, ← mat_mul ε hQn hx₀G hx₀G, ← mat_mul ε hQn hx₀G hx₀x₀, hx₀3', mat_one]
  have hXne : X ≠ mI := by
    intro h
    apply hx₀Q
    apply hC x₀ hx₀G
    intro q hq
    have h1 := cact_eq_app ε hQn hx₀G (Qvec ε q)
    rw [← hX, h] at h1
    have h2 : app mI (Qvec ε q) = Qvec ε q := by ext <;> simp [app, mI]
    rw [h2] at h1
    have h3 := Qelt_cact ε hQn hx₀G (Qvec ε q)
    rw [h1, Qelt_Qvec ε hq] at h3
    calc x₀ * q = (x₀ * q * x₀⁻¹) * x₀ := by group
      _ = q * x₀ := by rw [← h3]
  have hSS : mmul S S = mI := by
    rw [hS, ← mat_mul ε hQn hs₀G hs₀G]
    exact mat_of_mem ε (hsqQ s₀ hs₀T)
  obtain ⟨φ, -, hφ⟩ := hv.exists_hom
  have hcomm : ∃ q ∈ Q, s₀ * x₀ * s₀⁻¹ = q * x₀⁻¹ := by
    refine ⟨s₀ * x₀ * s₀⁻¹ * x₀, ?_, by group⟩
    have hmem : s₀ * x₀ * s₀⁻¹ * x₀ ∈ G :=
      G.mul_mem (G.mul_mem (G.mul_mem hs₀G hx₀G) (G.inv_mem hs₀G)) hx₀G
    have hσ2 : φ ⟨s₀, hs₀G⟩ * φ ⟨s₀, hs₀G⟩ = 1 := by
      rw [← map_mul]; exact (hφ _).mpr (hsqQ s₀ hs₀T)
    have hσ1 : φ ⟨s₀, hs₀G⟩ ≠ 1 := fun h => hs₀Q ((hφ _).mp h)
    have hτ3 : φ ⟨x₀, hx₀G⟩ * φ ⟨x₀, hx₀G⟩ * φ ⟨x₀, hx₀G⟩ = 1 := by
      rw [← map_mul, ← map_mul]
      apply (hφ _).mpr
      show x₀ * x₀ * x₀ ∈ Q
      rw [show x₀ * x₀ * x₀ = 1 by rw [mul_assoc]; exact hx₀3']
      exact Q.one_mem
    have hτ1 : φ ⟨x₀, hx₀G⟩ ≠ 1 := fun h => hx₀Q ((hφ _).mp h)
    have key : ∀ σ τ : Equiv.Perm (Fin 3), σ * σ = 1 → σ ≠ 1 → τ * τ * τ = 1 → τ ≠ 1 →
        σ * τ * σ⁻¹ * τ = 1 := by decide
    have h1 := key _ _ hσ2 hσ1 hτ3 hτ1
    apply (hφ ⟨s₀ * x₀ * s₀⁻¹ * x₀, hmem⟩).mp
    have e : (⟨s₀ * x₀ * s₀⁻¹ * x₀, hmem⟩ : ↥G) =
        ⟨s₀, hs₀G⟩ * ⟨x₀, hx₀G⟩ * ⟨s₀, hs₀G⟩⁻¹ * ⟨x₀, hx₀G⟩ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv]
    exact h1
  obtain ⟨q, hqQ, hq⟩ := hcomm
  have hmx : mat ε x₀⁻¹ = mmul X X := by rw [hxinv, hX, mat_mul ε hQn hx₀G hx₀G]
  have hSX : mmul S X = mmul (mmul X X) S := by
    have e1 : s₀ * x₀ = q * (x₀⁻¹ * s₀) := by
      calc s₀ * x₀ = (s₀ * x₀ * s₀⁻¹) * s₀ := by group
        _ = q * x₀⁻¹ * s₀ := by rw [hq]
        _ = q * (x₀⁻¹ * s₀) := by group
    calc mmul S X = mat ε (s₀ * x₀) := by rw [hS, hX, mat_mul ε hQn hs₀G hx₀G]
      _ = mat ε (q * (x₀⁻¹ * s₀)) := by rw [e1]
      _ = mmul mI (mmul (mmul X X) S) := by
          rw [mat_mul ε hQn (hQG q hqQ) (G.mul_mem hx₀inv hs₀G), mat_of_mem ε hqQ,
            mat_mul ε hQn hx₀inv hs₀G, hmx, hS]
      _ = mmul (mmul X X) S := mmul_mI_left _
  obtain ⟨w₁, hw1, hw2, hw3, hgen⟩ := fin_basis X S hXm hXne hSS hSX
  obtain ⟨w₂, hw₂⟩ : ∃ w₂, w₂ = app (mmul X X) w₁ := ⟨_, rfl⟩
  rw [← hw₂] at hw1 hw2 hgen
  have hcx : ∀ v, cact ε x₀⁻¹ v = app (mmul X X) v := fun v => by
    rw [cact_eq_app ε hQn hx₀inv, hmx]
  have hcs : ∀ v, cact ε s₀ v = app S v := fun v => by
    rw [cact_eq_app ε hQn hs₀G, hS]
  obtain ⟨ρ, hρ⟩ := fin_solve X hXm hXne (-(Qvec ε q))
  obtain ⟨r, hr⟩ : ∃ r, r = Qelt ε ρ := ⟨_, rfl⟩
  have hrQ : r ∈ Q := by rw [hr]; exact Qelt_mem ε ρ
  have hrG : r ∈ G := hQG r hrQ
  obtain ⟨s, hs⟩ : ∃ s, s = r * s₀ := ⟨_, rfl⟩
  have hsT : s ∈ T := by rw [hs]; exact T.mul_mem (hQT hrQ) hs₀T
  have hsG : s ∈ G := hTG hsT
  have hsQ : s ∉ Q := by
    intro h
    apply hs₀Q
    have : s₀ = r⁻¹ * s := by rw [hs]; group
    rw [this]
    exact Q.mul_mem (Q.inv_mem hrQ) h
  have hSs : mat ε s = S := by
    rw [hs, mat_mul ε hQn hrG hs₀G, mat_of_mem ε hrQ, mmul_mI_left, hS]
  have hu1 : r * q * (x₀⁻¹ * r⁻¹ * x₀) = 1 := by
    have hw : x₀⁻¹ * r⁻¹ * x₀ ∈ Q := by
      simpa using hQn x₀⁻¹ hx₀inv r⁻¹ (Q.inv_mem hrQ)
    have hv : Qvec ε (x₀⁻¹ * r⁻¹ * x₀) = - app (mmul X X) ρ := by
      have e : x₀⁻¹ * r⁻¹ * x₀ = x₀⁻¹ * Qelt ε (-ρ) * x₀⁻¹⁻¹ := by
        rw [Qelt_neg, inv_inv, hr]
      have := cact_eq_app ε hQn hx₀inv (-ρ)
      unfold cact at this
      rw [← e, hmx] at this
      rw [this]
      ext <;> simp [app] <;> ring
    have hu : Qvec ε (r * q * (x₀⁻¹ * r⁻¹ * x₀)) = 0 := by
      rw [Qvec_mul ε (Q.mul_mem hrQ hqQ) hw, Qvec_mul ε hrQ hqQ, hv, hr, Qvec_Qelt]
      have : ρ - app (mmul X X) ρ = -Qvec ε q := hρ
      calc ρ + Qvec ε q + -app (mmul X X) ρ = (ρ - app (mmul X X) ρ) + Qvec ε q := by abel
        _ = 0 := by rw [this]; abel
    have hmem : r * q * (x₀⁻¹ * r⁻¹ * x₀) ∈ Q := Q.mul_mem (Q.mul_mem hrQ hqQ) hw
    rw [← Qelt_Qvec ε hmem, hu, Qelt_zero]
  have hsxs : s * x₀ * s⁻¹ = x₀⁻¹ := by
    calc s * x₀ * s⁻¹ = r * (s₀ * x₀ * s₀⁻¹) * r⁻¹ := by rw [hs]; group
      _ = r * (q * x₀⁻¹) * r⁻¹ := by rw [hq]
      _ = (r * q * (x₀⁻¹ * r⁻¹ * x₀)) * x₀⁻¹ := by group
      _ = x₀⁻¹ := by rw [hu1, one_mul]
  have hsx : s * x₀ = x₀⁻¹ * s := by
    calc s * x₀ = (s * x₀ * s⁻¹) * s := by group
      _ = x₀⁻¹ * s := by rw [hsxs]
  have hsx' : s * x₀⁻¹ = x₀ * s := by
    have := congrArg (fun z => z⁻¹) hsxs
    simp only [mul_inv_rev, inv_inv] at this
    calc s * x₀⁻¹ = (s * x₀⁻¹ * s⁻¹) * s := by group
      _ = x₀ * s := by
          have h2 : s * x₀⁻¹ * s⁻¹ = x₀ := by
            have := congrArg (fun z => z⁻¹) hsxs
            simpa [mul_assoc] using this
          rw [h2]
  have hss : s * s = 1 := by
    have hcs2 : s * s * x₀ = x₀ * (s * s) := by
      calc s * s * x₀ = s * (s * x₀) := by group
        _ = s * (x₀⁻¹ * s) := by rw [hsx]
        _ = (s * x₀⁻¹) * s := by group
        _ = (x₀ * s) * s := by rw [hsx']
        _ = x₀ * (s * s) := by group
    have hsq : s * s ∈ Q := hsqQ s hsT
    have hfix : app X (Qvec ε (s * s)) = Qvec ε (s * s) := by
      rw [hX, ← cact_eq_app ε hQn hx₀G]
      have : x₀ * Qelt ε (Qvec ε (s * s)) * x₀⁻¹ = s * s := by
        rw [Qelt_Qvec ε hsq]
        calc x₀ * (s * s) * x₀⁻¹ = (s * s * x₀) * x₀⁻¹ := by rw [hcs2]
          _ = s * s := by group
      unfold cact
      rw [this]
    have h0 := fin_fixed X hXm hXne _ hfix
    rw [← Qelt_Qvec ε hsq, h0, Qelt_zero]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  obtain ⟨a, ha⟩ : ∃ a, a = Qelt ε w₁ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = Qelt ε w₂ := ⟨_, rfl⟩
  have haQ : a ∈ Q := by rw [ha]; exact Qelt_mem ε w₁
  have hbQ : b ∈ Q := by rw [hb]; exact Qelt_mem ε w₂
  have hxa : x₀⁻¹ * a * x₀ = b := by
    have h := Qelt_cact ε hQn hx₀inv w₁
    rw [hcx w₁, ← hw₂, inv_inv, ← ha, ← hb] at h
    exact h.symm
  have hxb : x₀⁻¹ * b * x₀ = a⁻¹ * b⁻¹ := by
    have h := Qelt_cact ε hQn hx₀inv w₂
    rw [hcx w₂, hw2, inv_inv, ← hb] at h
    rw [← h, sub_eq_add_neg, Qelt_add, Qelt_neg, Qelt_neg, ← ha, ← hb]
  have hsa : s * a * s = b := by
    have h := Qelt_cact ε hQn hsG w₁
    rw [cact_eq_app ε hQn hsG w₁, hSs, hw1, hsinv, ← ha, ← hb] at h
    exact h.symm
  have hsb : s * b * s = a := by
    have h := Qelt_cact ε hQn hsG w₂
    have h2 : app S w₂ = w₁ := by rw [← hw1]; exact hw3
    rw [cact_eq_app ε hQn hsG w₂, hSs, h2, hsinv, ← ha, ← hb] at h
    exact h.symm
  have hxs : x₀ * s * x₀ = s := by
    calc x₀ * s * x₀ = x₀ * (s * x₀) := by group
      _ = x₀ * (x₀⁻¹ * s) := by rw [hsx]
      _ = s := by group
  have hT : TRel a b s :=
    ⟨by rw [ha]; exact Qelt_pow_four ε w₁, by rw [hb]; exact Qelt_pow_four ε w₂,
      by rw [pow_two]; exact hss, by rw [ha, hb]; exact Qelt_comm ε w₁ w₂, hsa, hsb⟩
  have hA : ARel a b s x₀ := ⟨hT, hx₀3, hxa, hxb, hxs⟩
  have hcl_ab : Subgroup.closure ({a, b} : Set D) = Q := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact haQ
      · exact hbQ
    · intro g hg
      obtain ⟨m, n, hmn⟩ := hgen (Qvec ε g)
      have : g = a ^ m.val * b ^ n.val := by
        rw [← Qelt_Qvec ε hg, hmn, Qelt_add, Qelt_nsmul, Qelt_nsmul, ← ha, ← hb]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  have hQcl : Q ≤ Subgroup.closure ({a, b, s} : Set D) := by
    rw [← hcl_ab]
    exact Subgroup.closure_mono (by intro y hy; simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy ⊢; tauto)
  have hcl_abs : Subgroup.closure ({a, b, s} : Set D) = T := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact hQT haQ
      · exact hQT hbQ
      · exact hsT
    · intro t ht
      by_cases htQ : t ∈ Q
      · exact hQcl htQ
      · have hts : t * s⁻¹ ∈ Q := by
          rw [hmulQ t ht s⁻¹ (T.inv_mem hsT)]
          exact iff_of_false htQ (fun h => hsQ (by simpa using Q.inv_mem h))
        have h1 : t * s⁻¹ ∈ Subgroup.closure ({a, b, s} : Set D) := hQcl hts
        have h2 : s ∈ Subgroup.closure ({a, b, s} : Set D) := Subgroup.subset_closure (by simp)
        have := Subgroup.mul_mem _ h1 h2
        simpa using this
  have hTC : T ≤ Subgroup.closure ({a, b, s, x₀} : Set D) := by
    rw [← hcl_abs]
    exact Subgroup.closure_mono (by intro y hy; simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy ⊢; tauto)
  have hCG : Subgroup.closure ({a, b, s, x₀} : Set D) ≤ G := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact hQG _ haQ
    · exact hQG _ hbQ
    · exact hsG
    · exact hx₀G
  have hcl_x : Subgroup.closure ({a, b, s, x₀} : Set D) = G :=
    le_antisymm hCG (hv.le_of_not_mem hTC hCG (Subgroup.subset_closure (by simp)) hx₀T)
  exact ⟨a, b, s, x₀, hA, hcl_ab, hcl_abs, hcl_x⟩

end CFSG.Quasithin.F6.GoldAmL4
