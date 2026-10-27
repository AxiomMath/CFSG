module

public import CFSG.Quasithin.Recognition.F112Crit.APrime.Config
public import CFSG.Quasithin.Recognition.F112Crit.Lemma65

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112Crit
open CFSG.Quasithin.CosetGeom
open CFSG.Quasithin.F7
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T L E : Subgroup G}

theorem ConfigA.critDist_ne_one (hA : ConfigA G₀ G₁ G₂ T L E)
    (hL : LocalA G₀ G₁ G₂ E) : critDist G₀ G₁ G₂ E ≠ 1 := by
  intro hb
  classical
  obtain ⟨δ, hδdist, hδnot⟩ := exists_dist_eq_critDist_not_le hA.hypV hA.ne_bot
  rw [hb] at hδdist
  have hδnbrs : δ ∈ nbrs (γ₀ G₀ G₁ G₂) := dist_eq_one_iff_adj.mp hδdist
  have hδt : vtype δ = true :=
    vtype_eq_true_of_mem_nbrs (γ := γ₀ G₀ G₁ G₂) (by rw [vtype_γ₀]) hδnbrs
  have hγ₀nbrs : γ₀ G₀ G₁ G₂ ∈ nbrs δ := mem_nbrs_symm hδnbrs
  have hE_stabγ₀ : E ≤ stab (γ₀ G₀ G₁ G₂) := by
    rw [stab_γ₀ hA.hypV.le₁]
    exact hA.hypV.V_le
  have hE_stabδ : E ≤ stab δ := by
    have h := hL.le_stab (γ₀ G₀ G₁ G₂) (by rw [vtype_γ₀]) δ (by omega)
    rwa [Vv_γ₀ hA.hypV.normalizes] at h
  have hQδ_le_ballStab : pCoreOf 2 (stab δ) ≤ ballStab 1 δ :=
    pCoreOf_stab_le_ballStab_one hA.hypV.toAmalgamHyp δ
  have hQδ_le_G₁ : pCoreOf 2 (stab δ) ≤ G₁ := by
    have h1 : ballStab 1 δ ≤ stab (γ₀ G₀ G₁ G₂) :=
      ballStab_le_stab_of_dist_le (by rw [CosetGeom.dist_comm, hδdist])
    calc pCoreOf 2 (stab δ) ≤ ballStab 1 δ := hQδ_le_ballStab
      _ ≤ stab (γ₀ G₀ G₁ G₂) := h1
      _ = G₁ := stab_γ₀ hA.hypV.le₁
  have hE_not_Qδ : ¬ E ≤ pCoreOf 2 (stab δ) := fun h => hδnot (h.trans hQδ_le_ballStab)
  have hHidx : (E ⊓ pCoreOf 2 (stab δ)).relIndex E ≤ 2 :=
    (hL.point δ hδt).relIndex_le_two (γ₀ G₀ G₁ G₂) hγ₀nbrs E
      (le_inf hE_stabδ hE_stabγ₀) hA.hypV.isPGroup
  set H : Subgroup G := E ⊓ pCoreOf 2 (stab δ) with hH_def
  have hH_le_E : H ≤ E := by rw [hH_def]; exact inf_le_left
  have hH_le_Qδ : H ≤ pCoreOf 2 (stab δ) := by rw [hH_def]; exact inf_le_right
  have hHidx' : H.relIndex E ≤ 2 := by rwa [hH_def]
  have hstep1 : ∃ μ' ∈ nbrs δ, ¬ H ≤ pCoreOf 2 (stab μ') := by
    by_contra hno
    have hcon : ∀ μ' ∈ nbrs δ, H ≤ pCoreOf 2 (stab μ') := by
      intro μ' hμ'
      by_contra h
      exact hno ⟨μ', hμ', h⟩
    have hVδ_C_H : Vv E δ ≤ Subgroup.centralizer (H : Set G) := by
      refine Vv_le_of_forall_mem_nbrs hδt fun μ hμ => ?_
      have hμfalse : vtype μ = false := vtype_eq_false_of_mem_nbrs hδt hμ
      have hHle : H ≤ pCoreOf 2 (stab μ) := hcon μ hμ
      have h1 : Vv E μ ≤ Subgroup.centralizer (pCoreOf 2 (stab μ) : Set G) :=
        (Subgroup.le_centralizer_iff).mp (hL.pCoreOf_le_centralizer μ hμfalse)
      exact h1.trans (Subgroup.centralizer_le (fun x hx => hHle hx))
    have hVδ_le_S : Vv E δ ≤ stab δ := by
      refine Vv_le_of_forall_mem_nbrs hδt fun μ hμ => ?_
      have hμfalse : vtype μ = false := vtype_eq_false_of_mem_nbrs hδt hμ
      have hdist : dist μ δ ≤ critDist G₀ G₁ G₂ E := by
        have h1 : dist μ δ = 1 := by rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hμ
        rw [h1, hb]
      exact hL.le_stab μ hμfalse δ hdist
    have hVδ_norm : stab δ ≤ Subgroup.normalizer (Vv E δ : Set G) :=
      stab_le_normalizer_Vv hA.hypV.normalizes δ
    have hE_le_Vδ : E ≤ Vv E δ := by
      have h := Vv_le_Vv_of_mem_nbrs (Z := E) hδt hγ₀nbrs
      rwa [Vv_γ₀ hA.hypV.normalizes] at h
    obtain ⟨e, heE, heQδ⟩ := Set.not_subset.mp hE_not_Qδ
    have he_stabδ : e ∈ stab δ := hVδ_le_S (hE_le_Vδ heE)
    have heVδ : e ∈ Vv E δ := hE_le_Vδ heE
    have he2 : ∃ k : ℕ, e ^ 2 ^ k = 1 := by
      obtain ⟨k, hk⟩ := hA.hypV.isPGroup ⟨e, heE⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have htrans := (hL.point δ hδt).transitive_of_normal (Vv E δ) hVδ_le_S hVδ_norm
      ⟨e, heVδ, he2, heQδ⟩
    have hH_normal : stab δ ≤ Subgroup.normalizer (H : Set G) := by
      intro x hx
      let x' : ↥G₀ := ⟨x, stab_le δ hx⟩
      have hx'δ : x' • δ = δ := smul_eq_of_mem_stab hx
      have hx'γ₀ : x' • γ₀ G₀ G₁ G₂ ∈ nbrs δ := by
        have h := (smul_adj x').mpr hγ₀nbrs
        rwa [hx'δ] at h
      obtain ⟨v, hvV, hvsmul⟩ := htrans (γ₀ G₀ G₁ G₂) hγ₀nbrs (x' • γ₀ G₀ G₁ G₂) hx'γ₀
      let y' : ↥G₀ := v⁻¹ * x'
      have hvδ : v • δ = δ := smul_eq_of_mem_stab (hVδ_le_S hvV)
      have hy'δ : y' • δ = δ := by
        show (v⁻¹ * x') • δ = δ
        have h1 : (v⁻¹ * x') • δ = v⁻¹ • δ := by rw [mul_smul, hx'δ]
        rw [h1]
        calc v⁻¹ • δ = v⁻¹ • (v • δ) := by rw [hvδ]
          _ = δ := by rw [inv_smul_smul]
      have hy'γ₀ : y' • γ₀ G₀ G₁ G₂ = γ₀ G₀ G₁ G₂ := by
        show (v⁻¹ * x') • γ₀ G₀ G₁ G₂ = γ₀ G₀ G₁ G₂
        rw [mul_smul, ← hvsmul, inv_smul_smul]
      have hy_stabδ : (y' : G) ∈ stab δ := mem_stab_of_smul_eq hy'δ
      have hy_stabγ₀ : (y' : G) ∈ stab (γ₀ G₀ G₁ G₂) := mem_stab_of_smul_eq hy'γ₀
      have hy_G₁ : (y' : G) ∈ G₁ := by
        rw [stab_γ₀ hA.hypV.le₁] at hy_stabγ₀
        exact hy_stabγ₀
      have hy_normE : (y' : G) ∈ Subgroup.normalizer (E : Set G) := hA.hypV.normalizes hy_G₁
      have hy_normQ : (y' : G) ∈ Subgroup.normalizer (pCoreOf 2 (stab δ) : Set G) :=
        le_normalizer_pCoreOf 2 (stab δ) hy_stabδ
      have hy_normH : (y' : G) ∈ Subgroup.normalizer (H : Set G) := by
        rw [hH_def]
        exact F7.mem_normalizer_inf hy_normE hy_normQ
      have hv_centH : (v : G) ∈ Subgroup.centralizer (H : Set G) := hVδ_C_H hvV
      have hv_normH : (v : G) ∈ Subgroup.normalizer (H : Set G) :=
        Subgroup.centralizer_le_normalizer (H : Set G) hv_centH
      have hx_eq : x = (v : G) * (y' : G) := by
        show x = (v : G) * ((v : G)⁻¹ * x)
        group
      rw [hx_eq]
      exact Subgroup.mul_mem (Subgroup.normalizer (H : Set G)) hv_normH hy_normH
    have hHexp : ∀ h ∈ H, h ^ 2 = 1 := fun h hh =>
      isElemAbelian_pow_eq_one hA.hypV.elemAbelian (hH_le_E hh)
    let N : Subgroup G :=
      { carrier := {x | x ∈ stab δ ∧ x ∈ Subgroup.centralizer (H : Set G) ∧
          ∀ q ∈ pCoreOf 2 (stab δ), x * q * x⁻¹ * q⁻¹ ∈ H}
        one_mem' := by
          refine ⟨(stab δ).one_mem, (Subgroup.centralizer (H : Set G)).one_mem, ?_⟩
          intro q _
          simp
        mul_mem' := by
          rintro x y ⟨hxS, hxC, hxQ⟩ ⟨hyS, hyC, hyQ⟩
          refine ⟨(stab δ).mul_mem hxS hyS,
            (Subgroup.centralizer (H : Set G)).mul_mem hxC hyC, ?_⟩
          intro q hq
          have ha : y * q * y⁻¹ * q⁻¹ ∈ H := hyQ q hq
          have hxa : x * (y * q * y⁻¹ * q⁻¹) * x⁻¹ = y * q * y⁻¹ * q⁻¹ := by
            have hcomm : (y * q * y⁻¹ * q⁻¹) * x = x * (y * q * y⁻¹ * q⁻¹) :=
              Subgroup.mem_centralizer_iff.mp hxC _ ha
            rw [← hcomm]
            group
          have hxq : x * q * x⁻¹ * q⁻¹ ∈ H := hxQ q hq
          have heq : (x * y) * q * (x * y)⁻¹ * q⁻¹ =
              (y * q * y⁻¹ * q⁻¹) * (x * q * x⁻¹ * q⁻¹) := by
            rw [mul_inv_rev]
            calc (x * y) * q * (y⁻¹ * x⁻¹) * q⁻¹
                = x * (y * q * y⁻¹) * x⁻¹ * q⁻¹ := by group
              _ = x * ((y * q * y⁻¹ * q⁻¹) * q) * x⁻¹ * q⁻¹ := by group
              _ = (x * (y * q * y⁻¹ * q⁻¹) * x⁻¹) * (x * q * x⁻¹ * q⁻¹) := by group
              _ = (y * q * y⁻¹ * q⁻¹) * (x * q * x⁻¹ * q⁻¹) := by rw [hxa]
          rw [heq]
          exact H.mul_mem ha hxq
        inv_mem' := by
          rintro x ⟨hxS, hxC, hxQ⟩
          refine ⟨(stab δ).inv_mem hxS, (Subgroup.centralizer (H : Set G)).inv_mem hxC, ?_⟩
          intro q hq
          have ha : x * q * x⁻¹ * q⁻¹ ∈ H := hxQ q hq
          have hcomm : (x * q * x⁻¹ * q⁻¹) * x = x * (x * q * x⁻¹ * q⁻¹) :=
            Subgroup.mem_centralizer_iff.mp hxC _ ha
          have hxa : x * (x * q * x⁻¹ * q⁻¹) = (x * q * x⁻¹ * q⁻¹) * x := hcomm.symm
          have haeq : x * q * x⁻¹ * q⁻¹ = q * x⁻¹ * q⁻¹ * x := by
            calc x * q * x⁻¹ * q⁻¹
                = x⁻¹ * (x * (x * q * x⁻¹ * q⁻¹)) := by group
              _ = x⁻¹ * ((x * q * x⁻¹ * q⁻¹) * x) := by rw [hxa]
              _ = q * x⁻¹ * q⁻¹ * x := by group
          have heq : x⁻¹ * q * x⁻¹⁻¹ * q⁻¹ = (x * q * x⁻¹ * q⁻¹)⁻¹ := by
            rw [haeq]
            group
          rw [heq]
          exact H.inv_mem ha }
    have hN_le_S : N ≤ stab δ := fun _ hx => hx.1
    have hconj : ∀ g ∈ stab δ, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
      intro g hg n ⟨hnS, hnC, hnQ⟩
      refine ⟨(stab δ).mul_mem ((stab δ).mul_mem hg hnS) ((stab δ).inv_mem hg), ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have hgN : g ∈ Subgroup.normalizer (H : Set G) := hH_normal hg
        have hh' : g⁻¹ * h * g ∈ H := by
          simpa [inv_inv] using
            (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) h).mp hh
        have hcomm : (g⁻¹ * h * g) * n = n * (g⁻¹ * h * g) :=
          Subgroup.mem_centralizer_iff.mp hnC _ hh'
        have hcalc : (g * n * g⁻¹) * h = h * (g * n * g⁻¹) := by
          calc (g * n * g⁻¹) * h = g * (n * (g⁻¹ * h * g)) * g⁻¹ := by group
            _ = g * ((g⁻¹ * h * g) * n) * g⁻¹ := by rw [hcomm]
            _ = h * (g * n * g⁻¹) := by group
        exact hcalc.symm
      · intro q hq
        have hgQ : g ∈ Subgroup.normalizer (pCoreOf 2 (stab δ) : Set G) :=
          le_normalizer_pCoreOf 2 (stab δ) hg
        have hq' : g⁻¹ * q * g ∈ pCoreOf 2 (stab δ) := by
          simpa [inv_inv] using
            (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgQ) q).mp hq
        have hnq := hnQ (g⁻¹ * q * g) hq'
        have hgHN : g ∈ Subgroup.normalizer (H : Set G) := hH_normal hg
        have heq : (g * n * g⁻¹) * q * (g * n * g⁻¹)⁻¹ * q⁻¹ =
            g * (n * (g⁻¹ * q * g) * n⁻¹ * (g⁻¹ * q * g)⁻¹) * g⁻¹ := by group
        rw [heq]
        exact (Subgroup.mem_normalizer_iff.mp hgHN _).mp hnq
    have hN_normal : stab δ ≤ Subgroup.normalizer (N : Set G) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · intro hn
        exact hconj g hg n hn
      · intro hn
        have h := hconj g⁻¹ ((stab δ).inv_mem hg) (g * n * g⁻¹) hn
        simpa [mul_assoc] using h
    have hN_sq : ∀ n ∈ N, n ^ 2 ∈ pCoreOf 2 (stab δ) := by
      intro n hn
      have hnS : n ∈ stab δ := hn.1
      have hnC : n ∈ Subgroup.centralizer (H : Set G) := hn.2.1
      have hnQ := hn.2.2
      have hn2C : n ^ 2 ∈ Subgroup.centralizer (pCoreOf 2 (stab δ) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        have ha : n * q * n⁻¹ * q⁻¹ ∈ H := hnQ q hq
        have hcomm : (n * q * n⁻¹ * q⁻¹) * n = n * (n * q * n⁻¹ * q⁻¹) :=
          Subgroup.mem_centralizer_iff.mp hnC _ ha
        have hconj : n * (n * q * n⁻¹ * q⁻¹) * n⁻¹ = n * q * n⁻¹ * q⁻¹ := by
          rw [← hcomm]
          group
        have hpow' : (n * q * n⁻¹ * q⁻¹) * (n * q * n⁻¹ * q⁻¹) = 1 := by
          have := hHexp _ ha
          simpa [pow_two] using this
        have hmul : ⁅n ^ 2, q⁆ = 1 := by
          rw [pow_two, commutatorElement_mul_left_eq_conj_mul,
            show ⁅n, q⁆ = n * q * n⁻¹ * q⁻¹ from commutatorElement_def n q, hconj, hpow']
        exact (commutatorElement_eq_one_iff_mul_comm.mp hmul).symm
      exact (hL.point δ hδt).charTwo ⟨(stab δ).pow_mem hnS 2, hn2C⟩
    have hN_two : IsPGroup 2 N := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro n
      have hn2Q : ((n : G) ^ 2) ∈ pCoreOf 2 (stab δ) := hN_sq n n.2
      obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (stab δ)).exists_pow_pow_eq_one
        ⟨((n : G) ^ 2), hn2Q⟩
      refine ⟨k + 1, ?_⟩
      apply Subtype.ext
      have hk' : ((n : G) ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hexp : ((n : G) ^ 2 ^ (k + 1)) = ((n : G) ^ 2) ^ 2 ^ k := by
        rw [pow_succ, Nat.mul_comm, pow_mul]
      change ((n : G) ^ 2 ^ (k + 1)) = 1
      rw [hexp]
      exact hk'
    have hN_le_Q : N ≤ pCoreOf 2 (stab δ) :=
      le_pCoreOf_of_le_normalizer 2 hN_le_S hN_normal hN_two
    have heN : e ∈ N := by
      refine ⟨he_stabδ, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact isElemAbelian_comm hA.hypV.elemAbelian (hH_le_E hh) heE
      · intro q hq
        have hqG₁ : q ∈ G₁ := hQδ_le_G₁ hq
        have hnormqE : q ∈ Subgroup.normalizer (E : Set G) := hA.hypV.normalizes hqG₁
        have h1E : q * e * q⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hnormqE e).mp heE
        have h2E : q * e⁻¹ * q⁻¹ = (q * e * q⁻¹)⁻¹ := by group
        have hE : e * q * e⁻¹ * q⁻¹ ∈ E := by
          have heq : e * q * e⁻¹ * q⁻¹ = e * (q * e⁻¹ * q⁻¹) := by group
          rw [heq, h2E]
          exact E.mul_mem heE (E.inv_mem h1E)
        have hnorm_e_Q : e ∈ Subgroup.normalizer (pCoreOf 2 (stab δ) : Set G) :=
          le_normalizer_pCoreOf 2 (stab δ) he_stabδ
        have h1Q : e * q * e⁻¹ ∈ pCoreOf 2 (stab δ) :=
          (Subgroup.mem_normalizer_iff.mp hnorm_e_Q q).mp hq
        have hQ : e * q * e⁻¹ * q⁻¹ ∈ pCoreOf 2 (stab δ) :=
          (pCoreOf 2 (stab δ)).mul_mem h1Q ((pCoreOf 2 (stab δ)).inv_mem hq)
        rw [hH_def]
        exact ⟨hE, hQ⟩
    exact heQδ (hN_le_Q heN)
  obtain ⟨μ', hμ'nbrs, hH_not_Qμ'⟩ := hstep1
  have hμ'false : vtype μ' = false := vtype_eq_false_of_mem_nbrs hδt hμ'nbrs
  have hH_le_Qγ₀ : H ≤ pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) := by
    refine hH_le_E.trans ?_
    have h := hL.le_pCoreOf (γ₀ G₀ G₁ G₂) (by rw [vtype_γ₀])
    rwa [Vv_γ₀ hA.hypV.normalizes] at h
  have hμ'_ne : μ' ≠ γ₀ G₀ G₁ G₂ := by
    intro h
    apply hH_not_Qμ'
    rwa [h]
  obtain ⟨g, hg_stab, hgγ₀, hgμ'⟩ :=
    (hL.point δ hδt).exists_swap (γ₀ G₀ G₁ G₂) hγ₀nbrs μ' hμ'nbrs (Ne.symm hμ'_ne)
  set H' : Subgroup G := conjSub (g : G) H with hH'_def
  have hgE : conjSub (g : G) E = Vv E μ' := by
    rw [← hgγ₀, Vv_smul_γ₀ hA.hypV.normalizes g]
  have hgQ : conjSub (g : G) (pCoreOf 2 (stab δ)) = pCoreOf 2 (stab δ) :=
    F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 (stab δ) hg_stab)
  have hH'_eq : H' = Vv E μ' ⊓ pCoreOf 2 (stab δ) := by
    rw [hH'_def, hH_def, conjSub_inf, hgE, hgQ]
  have hH'_not_Qγ₀ : ¬ H' ≤ pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) := by
    intro hle
    apply hH_not_Qμ'
    have hconj_le : conjSub (g : G)⁻¹ H' ≤
        conjSub (g : G)⁻¹ (pCoreOf 2 (stab (γ₀ G₀ G₁ G₂))) := conjSub_mono _ hle
    have hleft : conjSub (g : G)⁻¹ H' = H := by
      rw [hH'_def, conjSub_conjSub_inv]
    have hginv : g⁻¹ • γ₀ G₀ G₁ G₂ = μ' := by
      calc g⁻¹ • γ₀ G₀ G₁ G₂ = g⁻¹ • (g • μ') := by rw [hgμ']
        _ = μ' := by rw [inv_smul_smul]
    have hright : conjSub (g : G)⁻¹ (pCoreOf 2 (stab (γ₀ G₀ G₁ G₂))) =
        pCoreOf 2 (stab μ') := by
      rw [← pCoreOf_conjSub]
      congr 1
      rw [show (g : G)⁻¹ = ↑(g⁻¹ : ↥G₀) by rw [Subgroup.coe_inv]]
      rw [← stab_smul (g⁻¹ : ↥G₀) (γ₀ G₀ G₁ G₂), hginv]
    rwa [hleft, hright] at hconj_le
  have hconjQμ'γ₀ : conjSub (g : G) (pCoreOf 2 (stab μ')) =
      pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) := by
    rw [← pCoreOf_conjSub]
    congr 1
    rw [← stab_smul g μ', hgμ']
  have hrel : (H' ⊓ pCoreOf 2 (stab (γ₀ G₀ G₁ G₂))).relIndex H' =
      (H ⊓ pCoreOf 2 (stab μ')).relIndex H := by
    rw [hH'_def]
    have h1 : conjSub (g : G) (H ⊓ pCoreOf 2 (stab μ')) =
        conjSub (g : G) H ⊓ pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) := by
      rw [hH_def, conjSub_inf, conjSub_inf, hgE, hgQ, hconjQμ'γ₀]
    rw [← h1]
    exact Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj (g : G)).toMonoidHom)
      (H ⊓ pCoreOf 2 (stab μ')) H (MulEquiv.injective (MulAut.conj (g : G)))
  have hH'_le_Eμ' : H' ≤ Vv E μ' := by
    rw [hH'_eq]
    exact inf_le_left
  have hH'_ea : IsElemAbelian 2 H' :=
    (hL.elemAbelian μ' hμ'false).mono hH'_le_Eμ'
  have hH'_le_Qδ : H' ≤ pCoreOf 2 (stab δ) := by
    rw [hH'_eq]
    exact inf_le_right
  have hH'_le_G₁ : H' ≤ G₁ := hH'_le_Qδ.trans hQδ_le_G₁
  have hstabγ₀_eq : pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) = pCoreOf 2 G₁ := by
    rw [stab_γ₀ hA.hypV.le₁]
  have hH'_not_pcore : ¬ H' ≤ pCoreOf 2 G₁ := by
    intro h
    apply hH'_not_Qγ₀
    rwa [hstabγ₀_eq]
  have hbound := hA.star.of_isElemAbelian hH'_le_G₁ hH'_ea hH'_not_pcore
  have hC_le : H ⊓ pCoreOf 2 (stab μ') ≤ E ⊓ Subgroup.centralizer (H' : Set G) := by
    refine le_inf (inf_le_left.trans hH_le_E) ?_
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hzQ : z ∈ pCoreOf 2 (stab μ') := hz.2
    have hwEμ' : w ∈ Vv E μ' := hH'_le_Eμ' hw
    have h1 : pCoreOf 2 (stab μ') ≤ Subgroup.centralizer (Vv E μ' : Set G) :=
      hL.pCoreOf_le_centralizer μ' hμ'false
    exact Subgroup.mem_centralizer_iff.mp (h1 hzQ) w hwEμ'
  have hmono : (E ⊓ Subgroup.centralizer (H' : Set G)).relIndex E ≤
      (H ⊓ pCoreOf 2 (stab μ')).relIndex E :=
    Subgroup.relIndex_le_of_le_left hC_le Subgroup.index_ne_zero_of_finite
  have hrel2 : (H ⊓ pCoreOf 2 (stab μ')).relIndex E =
      (H ⊓ pCoreOf 2 (stab μ')).relIndex H * H.relIndex E :=
    (Subgroup.relIndex_mul_relIndex (H ⊓ pCoreOf 2 (stab μ')) H E inf_le_left hH_le_E).symm
  have hmono2 : (E ⊓ Subgroup.centralizer (H' : Set G)).relIndex E ≤
      2 * (H ⊓ pCoreOf 2 (stab μ')).relIndex H := by
    calc (E ⊓ Subgroup.centralizer (H' : Set G)).relIndex E
        ≤ (H ⊓ pCoreOf 2 (stab μ')).relIndex E := hmono
      _ = (H ⊓ pCoreOf 2 (stab μ')).relIndex H * H.relIndex E := hrel2
      _ ≤ (H ⊓ pCoreOf 2 (stab μ')).relIndex H * 2 := Nat.mul_le_mul_left _ hHidx'
      _ = 2 * (H ⊓ pCoreOf 2 (stab μ')).relIndex H := Nat.mul_comm _ 2
  have hbound' : 2 * (H' ⊓ pCoreOf 2 (stab (γ₀ G₀ G₁ G₂))).relIndex H' <
      (E ⊓ Subgroup.centralizer (H' : Set G)).relIndex E := by
    rw [← hstabγ₀_eq] at hbound
    exact hbound
  have hlt : 2 * (H' ⊓ pCoreOf 2 (stab (γ₀ G₀ G₁ G₂))).relIndex H' <
      2 * (H ⊓ pCoreOf 2 (stab μ')).relIndex H :=
    lt_of_lt_of_le hbound' hmono2
  rw [hrel] at hlt
  exact (lt_irrefl _) hlt

end CFSG.Quasithin.F112Crit.APrime

end
