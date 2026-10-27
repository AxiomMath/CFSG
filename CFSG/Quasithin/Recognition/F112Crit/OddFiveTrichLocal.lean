module

public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTrichDefs
public import CFSG.Quasithin.Recognition.F112Crit.OddFiveQ

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type} [Group G] {G₀ G₁ G₂ : Subgroup G}

open CosetGeom (graph stab ballStab nbrs vtype)

theorem TrichConcl.smul {δ μ' : CosetGeom G₀ G₁ G₂} {Q K : Subgroup G}
    (h : TrichConcl δ μ' Q K) (g : ↥G₀) :
    TrichConcl (g • δ) (g • μ') (conjSub (g : G) Q) (conjSub (g : G) K) := by
  unfold TrichConcl at h ⊢
  rcases h with h | h | ⟨h1, h2, h3, a, ha, b, hb, hab⟩
  · left
    rw [CosetGeom.ballStab_smul]
    exact conjSub_mono (g : G) h
  · right; left
    intro ε hε ε' hε' hne hne'
    obtain ⟨e, rfl⟩ : ∃ e, ε = g • e := ⟨g⁻¹ • ε, by simp⟩
    obtain ⟨e', rfl⟩ : ∃ e', ε' = g • e' := ⟨g⁻¹ • ε', by simp⟩
    have he : e ∈ nbrs μ' := (CosetGeom.smul_adj g).mp hε
    have he' : e' ∈ nbrs μ' := (CosetGeom.smul_adj g).mp hε'
    have hne0 : e ≠ δ := fun h0 => hne (by rw [h0])
    have hne0' : e' ≠ δ := fun h0 => hne' (by rw [h0])
    obtain ⟨r, hr, hre⟩ := h e he e' he' hne0 hne0'
    refine ⟨g * r * g⁻¹, ?_, ?_⟩
    · exact mul_mem_conjSub hr
    · calc (g * r * g⁻¹ : ↥G₀) • (g • e) = g • (r • e) := by simp [mul_smul]
        _ = g • e' := by rw [hre]
  · right; right
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk x hx
      rw [CosetGeom.ballStab_smul, mem_conjSub]
      have hk' : (g : G)⁻¹ * k * g ∈ K := mem_conjSub.mp hk
      have hx' : (g : G)⁻¹ * x * g ∈ Q := mem_conjSub.mp hx
      have h := h1 _ hk' _ hx'
      have e : (g : G)⁻¹ * (k * x * k⁻¹ * x⁻¹) * g =
          ((g : G)⁻¹ * k * g) * ((g : G)⁻¹ * x * g) * ((g : G)⁻¹ * k * g)⁻¹ *
            ((g : G)⁻¹ * x * g)⁻¹ := by group
      rw [e]
      exact h
    · intro x hx y hy
      rw [CosetGeom.ballStab_smul]
      have hx' : (g : G)⁻¹ * x * g ∈ Q := mem_conjSub.mp hx
      have hy' : (g : G)⁻¹ * y * g ∈ Q := mem_conjSub.mp hy
      obtain ⟨k, hk, hkk⟩ := h2 _ hx' _ hy'
      refine ⟨(g : G) * k * (g : G)⁻¹, mul_mem_conjSub hk, ?_⟩
      rw [mem_conjSub]
      have e : (g : G)⁻¹ * (((g : G) * k * (g : G)⁻¹)⁻¹ * (x * y * x⁻¹ * y⁻¹)) * g =
          k⁻¹ * (((g : G)⁻¹ * x * g) * ((g : G)⁻¹ * y * g) * ((g : G)⁻¹ * x * g)⁻¹ *
            ((g : G)⁻¹ * y * g)⁻¹) := by group
      rw [e]
      exact hkk
    · intro k hk
      rw [CosetGeom.ballStab_smul, mem_conjSub]
      have hk' : (g : G)⁻¹ * k * g ∈ K := mem_conjSub.mp hk
      have h := h3 _ hk'
      have e : (g : G)⁻¹ * (k * k) * g = ((g : G)⁻¹ * k * g) * ((g : G)⁻¹ * k * g) := by
        group
      rw [e]
      exact h
    · refine ⟨(g : G) * a * (g : G)⁻¹, mul_mem_conjSub ha,
        (g : G) * b * (g : G)⁻¹, mul_mem_conjSub hb, ?_⟩
      intro hmem
      rw [CosetGeom.ballStab_smul, mem_conjSub] at hmem
      apply hab
      have e : (g : G)⁻¹ * (((g : G) * a * (g : G)⁻¹) * ((g : G) * b * (g : G)⁻¹) *
          ((g : G) * a * (g : G)⁻¹)⁻¹ * ((g : G) * b * (g : G)⁻¹)⁻¹) * g =
          a * b * a⁻¹ * b⁻¹ := by group
      rwa [e] at hmem

variable [Finite G]

private theorem commutator_inv_mul_mem_of_normal {E H : Subgroup G}
    (hEH : E ≤ H) (hNorm : H ≤ Subgroup.normalizer (E : Set G))
    {x x' y y' : G} (hx : x ∈ H) (hx' : x' ∈ H) (hy : y ∈ H) (hy' : y' ∈ H)
    (hxx' : x⁻¹ * x' ∈ E) (hyy' : y⁻¹ * y' ∈ E) :
    (x * y * x⁻¹ * y⁻¹)⁻¹ * (x' * y' * x'⁻¹ * y'⁻¹) ∈ E := by
  haveI : (E.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEH).mpr hNorm
  set z : G := (x * y * x⁻¹ * y⁻¹)⁻¹ * (x' * y' * x'⁻¹ * y'⁻¹) with hz
  have hzH : z ∈ H :=
    H.mul_mem (H.inv_mem (H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx))
      (H.inv_mem hy))) (H.mul_mem (H.mul_mem (H.mul_mem hx' hy') (H.inv_mem hx'))
      (H.inv_mem hy'))
  have hxq : (QuotientGroup.mk' (E.subgroupOf H)) ⟨x, hx⟩ =
      (QuotientGroup.mk' (E.subgroupOf H)) ⟨x', hx'⟩ := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa using hxx'
  have hyq : (QuotientGroup.mk' (E.subgroupOf H)) ⟨y, hy⟩ =
      (QuotientGroup.mk' (E.subgroupOf H)) ⟨y', hy'⟩ := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa using hyy'
  have hcomm : (QuotientGroup.mk' (E.subgroupOf H))
      (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹) =
      (QuotientGroup.mk' (E.subgroupOf H))
        (⟨x', hx'⟩ * ⟨y', hy'⟩ * ⟨x', hx'⟩⁻¹ * ⟨y', hy'⟩⁻¹) := by
    simp only [map_mul, map_inv, hxq, hyq]
  have h1 : (QuotientGroup.mk' (E.subgroupOf H)) ⟨z, hzH⟩ = 1 := by
    have hzeq : (⟨z, hzH⟩ : ↥H) =
        (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹)⁻¹ *
          (⟨x', hx'⟩ * ⟨y', hy'⟩ * ⟨x', hx'⟩⁻¹ * ⟨y', hy'⟩⁻¹) :=
      Subtype.ext hz.symm
    rw [hzeq, map_mul, map_inv, hcomm, inv_mul_cancel]
  have hmem : (⟨z, hzH⟩ : ↥H) ∈ E.subgroupOf H := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
    exact h1
  exact Subgroup.mem_subgroupOf.mp hmem

private theorem mem_stab_of_odd_mem_inf {ν δ μ : CosetGeom G₀ G₁ G₂}
    (hδ : δ ∈ nbrs ν) (hμ : μ ∈ nbrs δ) (hne : μ ≠ ν) (h3 : (nbrs δ).ncard = 3)
    {d : G} (hd : d ∈ stab ν ⊓ stab δ) (hodd : Odd (orderOf d)) : d ∈ stab μ := by
  have hdν : d ∈ stab ν := hd.1
  have hdδ : d ∈ stab δ := hd.2
  let d' : ↥G₀ := ⟨d, CosetGeom.stab_le δ hdδ⟩
  have hd'ν : d' • ν = ν := CosetGeom.smul_eq_of_mem_stab hdν
  have hd'δ : d' • δ = δ := CosetGeom.smul_eq_of_mem_stab hdδ
  by_cases hfix : d' • μ = μ
  · exact CosetGeom.mem_stab_of_smul_eq hfix
  · exfalso
    have hν : ν ∈ nbrs δ := CosetGeom.mem_nbrs_symm hδ
    set ρ := d' • μ with hρ
    have hρ_mem : ρ ∈ nbrs δ := by
      have h := (CosetGeom.smul_adj d').mpr hμ
      rwa [hd'δ] at h
    have hρν : ρ ≠ ν := fun h =>
      hne (smul_left_cancel d' ((hρ.symm.trans h).trans hd'ν.symm))
    have hρμ : ρ ≠ μ := fun h => hfix (hρ.symm.trans h)
    have hνμ : ν ≠ μ := fun h => hne h.symm
    have htriple : ({ν, μ, ρ} : Set (CosetGeom G₀ G₁ G₂)).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨ν, μ, ρ, hνμ, hρν.symm, hρμ.symm, rfl⟩
    have hsub : ({ν, μ, ρ} : Set (CosetGeom G₀ G₁ G₂)) ⊆ nbrs δ := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hν
      · exact hμ
      · exact hρ_mem
    have hset : ({ν, μ, ρ} : Set (CosetGeom G₀ G₁ G₂)) = nbrs δ :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [h3, htriple])
    have hρ' : d' • ρ ∈ nbrs δ := by
      have h := (CosetGeom.smul_adj d').mpr hρ_mem
      rwa [hd'δ] at h
    have hd'ρ : d' • ρ = μ := by
      have hmem : d' • ρ ∈ ({ν, μ, ρ} : Set (CosetGeom G₀ G₁ G₂)) := by
        rw [hset]
        exact hρ'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h
      · exact (hρν (smul_left_cancel d' (h.trans hd'ν.symm))).elim
      · exact h
      · exact (hρμ (smul_left_cancel d' (h.trans hρ))).elim
    have hsq : (d' ^ 2) • μ = μ := by
      rw [pow_two, mul_smul, ← hρ, hd'ρ]
    have h2all : ∀ n : ℕ, (d' ^ 2) ^ n • μ = μ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, mul_smul, hsq, ih]
    obtain ⟨k, hk⟩ := hodd
    have hk' : orderOf d' = 2 * k + 1 := by
      rw [← Subgroup.orderOf_coe d', hk]
    have hpow : d' ^ (2 * k + 1) = 1 := by
      rw [← hk']
      exact pow_orderOf_eq_one d'
    have hfinal : d' • μ = μ := by
      have h1 : d' • ((d' ^ 2) ^ k • μ) = (d' ^ (2 * k + 1)) • μ := by
        rw [← mul_smul]
        congr 1
        rw [← pow_mul, pow_succ']
      have h2 : d' • ((d' ^ 2) ^ k • μ) = μ := by
        simp [h1, hpow]
      simpa [h2all k] using h2
    exact hfix hfinal

theorem trichConcl_of_trichFor {T : Subgroup G} (hyp : AmalgamHyp G₀ G₁ G₂ T)
    {ν δ μ : CosetGeom G₀ G₁ G₂} {U : Subgroup G} (hδ : δ ∈ nbrs ν) (hμ : μ ∈ nbrs δ)
    (hne : μ ≠ ν) (h3 : (nbrs δ).ncard = 3) (hUν : U ≤ stab ν) (hUδ : U ≤ stab δ)
    (hUtr : ∀ ε ∈ nbrs ν, ∀ ε' ∈ nbrs ν, ε ≠ δ → ε' ≠ δ →
      ∃ g : ↥G₀, (g : G) ∈ U ∧ g • ε = ε')
    (h4 : ∃ ε₀ ∈ nbrs ν, ∃ ε₁ ∈ nbrs ν, ∃ ε₂ ∈ nbrs ν, ε₀ ≠ δ ∧ ε₁ ≠ δ ∧ ε₂ ≠ δ ∧
      ε₀ ≠ ε₁ ∧ ε₀ ≠ ε₂ ∧ ε₁ ≠ ε₂)
    (hQU : pCoreOf 2 (stab δ) ≤ U ⊔ ballStab 1 ν)
    (hidx : ∀ a ∈ U, ∀ b ∈ U, a ∉ pCoreOf 2 (stab δ) → b ∉ pCoreOf 2 (stab δ) →
      a⁻¹ * b ∈ pCoreOf 2 (stab δ))
    (hT : TrichFor ν δ U) :
    TrichConcl δ ν (pCoreOf 2 (stab δ)) (pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ)) := by
  unfold TrichConcl
  have hQν : pCoreOf 2 (stab δ) ≤ stab ν := pCoreOf_stab_le_stab hyp hδ
  have hQμ_stab : pCoreOf 2 (stab δ) ≤ stab μ :=
    pCoreOf_stab_le_stab hyp (CosetGeom.mem_nbrs_symm hμ)
  have hQG0 : pCoreOf 2 (stab δ) ≤ G₀ :=
    (pCoreOf_le 2 (stab δ)).trans (CosetGeom.stab_le δ)
  have hQnormE : pCoreOf 2 (stab δ) ≤
      Subgroup.normalizer (ballStab 1 ν : Set G) :=
    hQν.trans (CosetGeom.le_normalizer_ballStab 1 ν)
  have hUnormE : U ≤ Subgroup.normalizer (ballStab 1 ν : Set G) :=
    hUν.trans (CosetGeom.le_normalizer_ballStab 1 ν)
  have hKnormE : (pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ)) ≤
      Subgroup.normalizer (ballStab 1 ν : Set G) :=
    inf_le_left.trans hQnormE
  have hUQE : U ≤ pCoreOf 2 (stab δ) ⊔ ballStab 1 ν := by
    have hT1 := hT (pCoreOf 2 (stab δ) ⊔ ballStab 1 ν) le_sup_right
      (sup_le hQU le_sup_right)
      (F1.le_normalizer_sup
        (hUδ.trans (le_normalizer_pCoreOf 2 (stab δ))) hUnormE)
      (fun d hd _ => Subgroup.inf_normalizer_le_normalizer_sup (pCoreOf 2 (stab δ))
        (ballStab 1 ν) ⟨le_normalizer_pCoreOf 2 (stab δ) hd.2,
          CosetGeom.le_normalizer_ballStab 1 ν hd.1⟩)
    rcases hT1 with hN1E | hN1U | ⟨hc1, hu1, hs1, hex1⟩
    · exfalso
      have hQE : pCoreOf 2 (stab δ) ≤ ballStab 1 ν := le_sup_left.trans hN1E
      obtain ⟨ε₀, hε₀, ε₁, hε₁, ε₂, hε₂, hε₀δ, hε₁δ, hε₂δ, hε₀₁, hε₀₂, hε₁₂⟩ := h4
      obtain ⟨g₁, hg₁U, hg₁⟩ := hUtr ε₀ hε₀ ε₁ hε₁ hε₀δ hε₁δ
      obtain ⟨g₂, hg₂U, hg₂⟩ := hUtr ε₀ hε₀ ε₂ hε₂ hε₀δ hε₂δ
      have hg₁Q : (g₁ : G) ∉ pCoreOf 2 (stab δ) := by
        intro h
        exact hε₀₁ ((hg₁.symm.trans
          (BenderLocalOf.smul_eq_of_mem_ballStab_one hε₀ (hQE h))).symm)
      have hg₂Q : (g₂ : G) ∉ pCoreOf 2 (stab δ) := by
        intro h
        exact hε₀₂ ((hg₂.symm.trans
          (BenderLocalOf.smul_eq_of_mem_ballStab_one hε₀ (hQE h))).symm)
      have hidx12 : (g₁ : G)⁻¹ * (g₂ : G) ∈ pCoreOf 2 (stab δ) :=
        hidx (g₁ : G) hg₁U (g₂ : G) hg₂U hg₁Q hg₂Q
      have h12E : (g₁ : G)⁻¹ * (g₂ : G) ∈ ballStab 1 ν := hQE hidx12
      let e : ↥G₀ := ⟨(g₁ : G)⁻¹ * (g₂ : G), hQG0 hidx12⟩
      have he_fix : e • ε₀ = ε₀ :=
        BenderLocalOf.smul_eq_of_mem_ballStab_one hε₀ h12E
      have he_eq : e = (g₁ : ↥G₀)⁻¹ * g₂ := Subtype.ext rfl
      have hsmul : (g₁ : ↥G₀)⁻¹ • (g₂ • ε₀) = ε₀ := by
        rw [← mul_smul, ← he_eq]
        exact he_fix
      exact hε₁₂ (hg₁.symm.trans ((inv_smul_eq_iff.mp hsmul).symm.trans hg₂))
    · exact hN1U
    · exfalso
      obtain ⟨a, haU, b, hbU, hab⟩ := hex1
      have hcommE : a * b * a⁻¹ * b⁻¹ ∈ ballStab 1 ν := by
        by_cases haQ : a ∈ pCoreOf 2 (stab δ)
        · exact hc1 a (Subgroup.mem_sup_left haQ) b hbU
        · by_cases hbQ : b ∈ pCoreOf 2 (stab δ)
          · have h := hc1 b (Subgroup.mem_sup_left hbQ) a haU
            have e : a * b * a⁻¹ * b⁻¹ = (b * a * b⁻¹ * a⁻¹)⁻¹ := by group
            rw [e]
            exact (ballStab 1 ν).inv_mem h
          · have hq : a⁻¹ * b ∈ pCoreOf 2 (stab δ) := hidx a haU b hbU haQ hbQ
            have h := hc1 (a⁻¹ * b) (Subgroup.mem_sup_left hq) a haU
            have h' : a * ((a⁻¹ * b) * a * (a⁻¹ * b)⁻¹ * a⁻¹)⁻¹ * a⁻¹ ∈
                ballStab 1 ν :=
              (Subgroup.mem_normalizer_iff.mp (hUnormE haU) _).mp
                ((ballStab 1 ν).inv_mem h)
            have e : a * b * a⁻¹ * b⁻¹ =
                a * ((a⁻¹ * b) * a * (a⁻¹ * b)⁻¹ * a⁻¹)⁻¹ * a⁻¹ := by group
            rwa [e]
      exact hab hcommE
  have hUN : U ≤ Subgroup.normalizer
      (((pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ)) ⊔ ballStab 1 ν : Subgroup G) : Set G) := by
    refine hUQE.trans (sup_le ?_ ?_)
    · refine F1.le_normalizer_sup (X := pCoreOf 2 (stab δ)) ?_ ?_
      · intro x hx
        exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hx,
            (hQμ_stab.trans (le_normalizer_pCoreOf 2 (stab μ))) hx⟩
      · exact hQnormE
    · exact le_sup_right.trans Subgroup.le_normalizer
  have hoddN : ∀ d ∈ stab ν ⊓ stab δ, Odd (orderOf d) → d ∈ Subgroup.normalizer
      (((pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ)) ⊔ ballStab 1 ν : Subgroup G) : Set G) := by
    intro d hd hodd
    have hdμ : d ∈ stab μ := mem_stab_of_odd_mem_inf hδ hμ hne h3 hd hodd
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨Subgroup.inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_pCoreOf 2 (stab δ) hd.2, le_normalizer_pCoreOf 2 (stab μ) hdμ⟩,
        CosetGeom.le_normalizer_ballStab 1 ν hd.1⟩
  have hT2 := hT ((pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ)) ⊔ ballStab 1 ν) le_sup_right
    (sup_le (inf_le_left.trans hQU) le_sup_right) hUN hoddN
  rcases hT2 with hN2E | hN2U | ⟨hc2, hu2, hs2, hex2⟩
  · left
    exact le_sup_left.trans hN2E
  · right; left
    intro ε hε ε' hε' hneε hneε'
    obtain ⟨g, hgU, hg⟩ := hUtr ε hε ε' hε' hneε hneε'
    have hgN : (g : G) ∈ (pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ)) ⊔ ballStab 1 ν :=
      hN2U hgU
    obtain ⟨k, hk, e, he, hge⟩ :=
      (F1.mem_sup_iff_exists_mul_of_le_normalizer hKnormE).mp hgN
    have heG0 : e ∈ G₀ := CosetGeom.stab_le ν (CosetGeom.ballStab_le_stab 1 ν he)
    let e' : ↥G₀ := ⟨e, heG0⟩
    refine ⟨g * e'⁻¹, ?_, ?_⟩
    · have hcoe : ((g * e'⁻¹ : ↥G₀) : G) = k := by
        show (g : G) * e⁻¹ = k
        rw [hge]
        group
      rw [hcoe]
      exact hk
    · calc (g * e'⁻¹ : ↥G₀) • ε = g • (e'⁻¹ • ε) := by rw [mul_smul]
        _ = g • ε := by
              rw [BenderLocalOf.smul_eq_of_mem_ballStab_one hε ((ballStab 1 ν).inv_mem he)]
        _ = ε' := hg
  · right; right
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk x hx
      obtain ⟨u, hu, e, he, rfl⟩ :=
        (F1.mem_sup_iff_exists_mul_of_le_normalizer hUnormE).mp (hQU hx)
      have hku : k * u * k⁻¹ * u⁻¹ ∈ ballStab 1 ν := hc2 k (Subgroup.mem_sup_left hk) u hu
      have hke : k * e * k⁻¹ * e⁻¹ ∈ ballStab 1 ν := by
        have h1 : k * e * k⁻¹ ∈ ballStab 1 ν :=
          (Subgroup.mem_normalizer_iff.mp (hKnormE hk) e).mp he
        have e' : k * e * k⁻¹ * e⁻¹ = (k * e * k⁻¹) * e⁻¹ := by group
        rw [e']
        exact (ballStab 1 ν).mul_mem h1 ((ballStab 1 ν).inv_mem he)
      have hconj : u * (k * e * k⁻¹ * e⁻¹) * u⁻¹ ∈ ballStab 1 ν :=
        (Subgroup.mem_normalizer_iff.mp (hUnormE hu) _).mp hke
      have hident : k * (u * e) * k⁻¹ * (u * e)⁻¹ =
          (k * u * k⁻¹ * u⁻¹) * (u * (k * e * k⁻¹ * e⁻¹) * u⁻¹) := by group
      rw [hident]
      exact (ballStab 1 ν).mul_mem hku hconj
    · intro a ha b hb
      obtain ⟨u₁, hu₁, e₁, he₁, rfl⟩ :=
        (F1.mem_sup_iff_exists_mul_of_le_normalizer hUnormE).mp (hQU ha)
      obtain ⟨u₂, hu₂, e₂, he₂, rfl⟩ :=
        (F1.mem_sup_iff_exists_mul_of_le_normalizer hUnormE).mp (hQU hb)
      obtain ⟨k, hk, e₃, he₃, hke₃⟩ :=
        (F1.mem_sup_iff_exists_mul_of_le_normalizer hKnormE).mp (hu2 u₁ hu₁ u₂ hu₂)
      refine ⟨k, hk, ?_⟩
      have hmod : (u₁ * u₂ * u₁⁻¹ * u₂⁻¹)⁻¹ *
          ((u₁ * e₁) * (u₂ * e₂) * (u₁ * e₁)⁻¹ * (u₂ * e₂)⁻¹) ∈ ballStab 1 ν :=
        commutator_inv_mul_mem_of_normal (CosetGeom.ballStab_normal 1 ν).1
          (CosetGeom.le_normalizer_ballStab 1 ν)
          (hUν hu₁) ((stab ν).mul_mem (hUν hu₁) (CosetGeom.ballStab_le_stab 1 ν he₁))
          (hUν hu₂) ((stab ν).mul_mem (hUν hu₂) (CosetGeom.ballStab_le_stab 1 ν he₂))
          (by have h1 : u₁⁻¹ * (u₁ * e₁) = e₁ := by group
              rwa [h1])
          (by have h1 : u₂⁻¹ * (u₂ * e₂) = e₂ := by group
              rwa [h1])
      have hk_eq : k⁻¹ * (u₁ * u₂ * u₁⁻¹ * u₂⁻¹) = e₃ := by
        rw [hke₃]
        group
      have hident : k⁻¹ * ((u₁ * e₁) * (u₂ * e₂) * (u₁ * e₁)⁻¹ * (u₂ * e₂)⁻¹) =
          e₃ * ((u₁ * u₂ * u₁⁻¹ * u₂⁻¹)⁻¹ *
            ((u₁ * e₁) * (u₂ * e₂) * (u₁ * e₁)⁻¹ * (u₂ * e₂)⁻¹)) := by
        rw [← hk_eq]
        group
      rw [hident]
      exact (ballStab 1 ν).mul_mem he₃ hmod
    · intro k hk
      exact hs2 k (Subgroup.mem_sup_left hk)
    · obtain ⟨a', ha'U, b', hb'U, hab'⟩ := hex2
      obtain ⟨a, haQ, e₁, he₁, hae⟩ :=
        (F1.mem_sup_iff_exists_mul_of_le_normalizer hQnormE).mp (hUQE ha'U)
      obtain ⟨b, hbQ, e₂, he₂, hbe⟩ :=
        (F1.mem_sup_iff_exists_mul_of_le_normalizer hQnormE).mp (hUQE hb'U)
      refine ⟨a, haQ, b, hbQ, ?_⟩
      intro habE
      have hmod : (a * b * a⁻¹ * b⁻¹)⁻¹ * (a' * b' * a'⁻¹ * b'⁻¹) ∈ ballStab 1 ν :=
        commutator_inv_mul_mem_of_normal (CosetGeom.ballStab_normal 1 ν).1
          (CosetGeom.le_normalizer_ballStab 1 ν)
          (hQν haQ) (hUν ha'U) (hQν hbQ) (hUν hb'U)
          (by have h1 : a⁻¹ * a' = e₁ := by rw [hae]; group
              rwa [h1])
          (by have h1 : b⁻¹ * b' = e₂ := by rw [hbe]; group
              rwa [h1])
      have hthis : a' * b' * a'⁻¹ * b'⁻¹ ∈ ballStab 1 ν := by
        have e : a' * b' * a'⁻¹ * b'⁻¹ =
            (a * b * a⁻¹ * b⁻¹) * ((a * b * a⁻¹ * b⁻¹)⁻¹ * (a' * b' * a'⁻¹ * b'⁻¹)) :=
          by group
        rw [e]
        exact (ballStab 1 ν).mul_mem habE hmod
      exact hab' hthis

end CFSG.Quasithin.F112Crit

end
