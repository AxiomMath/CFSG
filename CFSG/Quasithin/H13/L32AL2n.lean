module

public import CFSG.Quasithin.H13.L32AL2m

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.L32A.C CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative

section Transvection

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

theorem isTransvection_of_centralizes (h : HypF91 T V L V₁ Vp H) {t : ↥H} {D : Subgroup G}
    (hD2 : D.relIndex (conjClosure Vp H) = 2) (htD : ∀ d ∈ D, (t : G) * d * (t : G)⁻¹ = d)
    (ht : ∃ u ∈ conjClosure Vp H, (t : G) * u * (t : G)⁻¹ * u⁻¹ ∉ V₁) :
    IsTransvection (C1Pack.rhoH h t) := by
  set U := conjClosure Vp H with hU
  set ρ := C1Pack.rhoH h t with hρ
  have hidx : (D.subgroupOf U).index = 2 := hD2
  obtain ⟨u₀, hu₀, hu₀D⟩ : ∃ u ∈ U, u ∉ D := by
    by_contra hall
    push Not at hall
    have : D.subgroupOf U = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact Subgroup.mem_subgroupOf.mpr (hall x x.2)
    rw [this, Subgroup.index_top] at hidx
    exact absurd hidx (by norm_num)
  set w₀ := ρ (clsU h hu₀) * (clsU h hu₀)⁻¹ with hw₀
  have hcases : ∀ v : UMod h, ρ v = v ∨ ρ v = v * w₀ := by
    intro v
    obtain ⟨u, hu, rfl⟩ := exists_clsU h v
    by_cases huD : u ∈ D
    · left
      rw [hρ, rhoH_clsU]
      exact clsU_congr h _ hu (htD u huD)
    · right
      have hd : u₀⁻¹ * u ∈ D := by
        have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨u₀, hu₀⟩ : ↥U)⁻¹)
          (b := ⟨u, hu⟩)).mpr
        have h1 : (⟨u₀, hu₀⟩ : ↥U)⁻¹ ∉ D.subgroupOf U := fun hm => hu₀D (by
          have := Subgroup.inv_mem _ hm
          rw [inv_inv, Subgroup.mem_subgroupOf] at this
          exact this)
        have h2 : (⟨u, hu⟩ : ↥U) ∉ D.subgroupOf U := fun hm => huD (Subgroup.mem_subgroupOf.mp hm)
        exact Subgroup.mem_subgroupOf.mp (key (iff_of_false h1 h2))
      have hdU : u₀⁻¹ * u ∈ U := mul_mem (inv_mem hu₀) hu
      have e1 : clsU h hu = clsU h hu₀ * clsU h hdU := by
        rw [clsU_mul]
        exact clsU_congr h _ _ (by group)
      have e2 : ρ (clsU h hdU) = clsU h hdU := by
        rw [hρ, rhoH_clsU]
        exact clsU_congr h _ hdU (htD _ hd)
      rw [e1, map_mul, e2, hw₀]
      calc ρ (clsU h hu₀) * clsU h hdU = clsU h hdU * ρ (clsU h hu₀) := mul_comm _ _
        _ = clsU h hdU * (clsU h hu₀ * (ρ (clsU h hu₀) * (clsU h hu₀)⁻¹)) := by
            rw [mul_comm (ρ (clsU h hu₀)) _, mul_inv_cancel_left]
        _ = clsU h hu₀ * clsU h hdU * (ρ (clsU h hu₀) * (clsU h hu₀)⁻¹) := by
            rw [← mul_assoc, mul_comm (clsU h hdU) (clsU h hu₀)]
  have hρ1 : ρ ≠ 1 := by
    obtain ⟨u, hu, hut⟩ := ht
    intro h1
    apply hut
    rw [← rhoH_clsU_eq_iff h t hu, ← hρ, h1, MulAut.one_apply]
  have hw1 : w₀ ≠ 1 := by
    intro h1
    apply hρ1
    refine MulEquiv.ext fun v => ?_
    rcases hcases v with e | e
    · exact e
    · rw [e, h1, mul_one]
      rfl
  exact ⟨hρ1, w₀, hw1, hcases⟩

theorem A₁_le_of_relIndex (hF : HypF98 T V L V₁ Vp H) {γ γ' : F8.Geom T L H}
    {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hγ2 : (F8.Dγ Vp V₁ H (g : G)).relIndex (F8.Uγ Vp H (g : G)) = 2)
    (hH2 : (F8.DH Vp V₁ H (g : G)).relIndex (conjClosure Vp H) = 2)
    (hnt : ∀ y : ↥H, ¬ IsTransvection (C1Pack.rhoH hF.toHypF91 y)) :
    F8.A₁ V₁ (g : G) ≤ conjClosure Vp H := by
  set U := conjClosure Vp H with hU
  set A₁ := F8.A₁ V₁ (g : G) with hA₁
  by_contra hA
  have hinf : A₁ ⊓ U = ⊥ := by
    have h1 : Nat.card ↥(A₁ ⊓ U) ∣ 2 := by
      rw [← hF.card_A₁ (g := g)]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(A₁ ⊓ U) ≠ 2 := by
      intro h2
      apply hA
      have : A₁ ⊓ U = A₁ :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h2, hF.card_A₁])
      rw [← this]
      exact inf_le_right
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exact absurd h h2
  obtain ⟨t, htU, htD⟩ : ∃ t ∈ F8.Uγ Vp H (g : G), t ∉ F8.Dγ Vp V₁ H (g : G) := by
    by_contra hall
    push Not at hall
    have : (F8.Dγ Vp V₁ H (g : G)).relIndex (F8.Uγ Vp H (g : G)) = 1 :=
      Subgroup.relIndex_eq_one.mpr hall
    omega
  have htH : t ∈ H := hF.Uγ_le_H s htU
  have hcomm : ∀ d ∈ F8.DH Vp V₁ H (g : G), t * d * t⁻¹ = d := by
    intro d hd
    have hdU : d ∈ U := centralizerMod_le_left _ _ _ hd
    have h1 : d * t * d⁻¹ * t⁻¹ ∈ A₁ := (mem_centralizerMod.mp hd).2.2 t htU
    have h2 : d * t * d⁻¹ * t⁻¹ ∈ U := by
      have := mul_mem hdU (conj_mem_UH htH (inv_mem hdU))
      rwa [show d * (t * d⁻¹ * t⁻¹) = d * t * d⁻¹ * t⁻¹ by group] at this
    have h3 : d * t * d⁻¹ * t⁻¹ = 1 := by
      have : d * t * d⁻¹ * t⁻¹ ∈ A₁ ⊓ U := Subgroup.mem_inf.mpr ⟨h1, h2⟩
      rwa [hinf, Subgroup.mem_bot] at this
    calc t * d * t⁻¹ = (d * t * d⁻¹ * t⁻¹)⁻¹ * d := by group
      _ = d := by rw [h3, inv_one, one_mul]
  have hmoves : ∃ u ∈ U, t * u * t⁻¹ * u⁻¹ ∉ V₁ := by
    by_contra hall
    push Not at hall
    exact htD ⟨htU, hF.toHypF91.H_normalizes_V₁ htH, hall⟩
  exact hnt ⟨t, htH⟩ (isTransvection_of_centralizes hF.toHypF91 hH2 hcomm hmoves)

end Transvection

variable {G : Type} [Group G] [Finite G] {T L V K : Subgroup G}

theorem caseOne_of_red (hD36 : D36) (hD37 : D37)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6) (h33 : Lemma14_7_33)
    (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h29 : Thm14_7_29) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (R : L2Red G T L V K)
    (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V)) : L2CaseOne G T L V := by
  have hall := dγ_lt_uγ_of_red hA37 hA38 h29 h1222 h1332 h1334 h76 h33 h36 hlist R hF
  refine ⟨hall, ?_⟩
  have : IsMulCommutative ↥(conjClosure V (A6.g1 T V)) := hF.F911_3.1
  obtain ⟨t₀, C⟩ := exists_ctxL2_of_red hA37 hA38 R
  obtain ⟨W, hW⟩ := exists_topW R.S hF
  have X : TopCtx T L V K W t₀ := ⟨R, C, hW⟩
  obtain ⟨γ₀, γ₀', g₀, s₀⟩ := hF.exists_F8Setup
  obtain ⟨γ, γ', g, s, hpos, hle, -⟩ := hF.lemma_14_5_18_four s₀ (hall _ _ _ s₀)
  have hUp : IsPGroup 2 ↥(conjClosure V (A6.g1 T V)) := F7.isPGroup_of_isElemAbelian hF.F911_3
  have hUγp : IsPGroup 2 ↥(F8.Uγ V (A6.g1 T V) (g : G)) :=
    F7.isPGroup_of_isElemAbelian hF.isElemAbelian_Uγ
  have h4 := X.card_img_lt_four hD36 hD37 hA37 hA38 h76 h33 h36 hlist h29 h1222 h1332 h1334 s
    hpos hle
  have hcard : Nat.card (X.img (F8.Uγ V (A6.g1 T V) (g : G))) =
      (F8.Dγ V (fsuV1 T V) (A6.g1 T V) (g : G)).relIndex (F8.Uγ V (A6.g1 T V) (g : G)) := by
    rw [X.card_img hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 (hF.Uγ_le_H s),
      hF.Dγ_eq_inf_pCoreOf s]
  have hm1 : mIdx (F8.Uγ V (A6.g1 T V) (g : G)) (F8.Dγ V (fsuV1 T V) (A6.g1 T V) (g : G)) = 1 := by
    have h1 : 2 ^ mIdx (F8.Uγ V (A6.g1 T V) (g : G)) (F8.Dγ V (fsuV1 T V) (A6.g1 T V) (g : G)) <
        2 ^ 2 := by
      rw [← HypF98.relIndex_eq_two_pow_mIdx hUγp, ← hcard]
      exact h4
    have h2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h1
    omega
  have hγ2 : (F8.Dγ V (fsuV1 T V) (A6.g1 T V) (g : G)).relIndex
      (F8.Uγ V (A6.g1 T V) (g : G)) = 2 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hUγp, hm1, pow_one]
  have hDHlt : F8.DH V (fsuV1 T V) (A6.g1 T V) (g : G) < conjClosure V (A6.g1 T V) := by
    refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun hDHU => ?_
    obtain ⟨δ, δ', k, y, sk, -, -, eU, -, -, eDγ⟩ :=
      hF.exists_symmetric_setup s (hF.not_Vγ_le_ballStab_of_lt s (hall γ γ' g s))
    have := hall δ δ' k sk
    rw [eDγ, hDHU, ← eU] at this
    exact lt_irrefl _ this
  have hH2 : (F8.DH V (fsuV1 T V) (A6.g1 T V) (g : G)).relIndex (conjClosure V (A6.g1 T V)) =
      2 := by
    have h1 : mIdx (conjClosure V (A6.g1 T V)) (F8.DH V (fsuV1 T V) (A6.g1 T V) (g : G)) ≤ 1 :=
      hle.trans hm1.le
    have h2 : (F8.DH V (fsuV1 T V) (A6.g1 T V) (g : G)).relIndex (conjClosure V (A6.g1 T V)) ≠
        1 := fun h =>
      hDHlt.ne ((Subgroup.relIndex_eq_one.mp h).antisymm (centralizerMod_le_left _ _ _)).symm
    rw [HypF98.relIndex_eq_two_pow_mIdx hUp] at h2 ⊢
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with h0 | h0
    · rw [h0, pow_zero] at h2
      exact absurd rfl h2
    · rw [h0, pow_one]
  have hnt : ∀ y : ↥(A6.g1 T V), ¬ IsTransvection (C1Pack.rhoH hF.toHypF91 y) := fun y =>
    not_isTransvection_red hA37 hA38 h29 h1222 h1332 h1334 h76 h33 h36 hlist R hF
      (QuotientGroup.mk y)
  have hA1 := A₁_le_of_relIndex hF s hγ2 hH2 hnt
  have hV1 : fsuV1 T V ≤ F8.Uγ V (A6.g1 T V) (g : G) := by
    obtain ⟨δ, δ', k, y, sk, -, hyδ, eU, eB, eDH, eDγ⟩ :=
      hF.exists_symmetric_setup s (hF.not_Vγ_le_ballStab_of_lt s (hall γ γ' g s))
    have hky : ((k : G))⁻¹ * (y : G) ∈ A6.g1 T V := by
      have h1 : (k⁻¹ * y) • F8.γ₁ T L (A6.g1 T V) = F8.γ₁ T L (A6.g1 T V) := by
        rw [mul_smul, hyδ, ← sk.edge₁, inv_smul_smul]
      have := mem_stab_of_smul_eq h1
      rw [stab_γ₁ hF.amalgamHypV.le₂] at this
      simpa using this
    have eA : F8.A₁ (fsuV1 T V) (k : G) = Quasithin.conjSub (y : G) (fsuV1 T V) := by
      have e : (y : G) = (k : G) * ((k : G)⁻¹ * (y : G)) := by group
      rw [F8.A₁, e, Quasithin.conjSub_mul, F7.conjSub_eq_of_mem_normalizer
        (hF.toHypF91.H_normalizes_V₁ hky)]
    have hγ2k : (F8.Dγ V (fsuV1 T V) (A6.g1 T V) (k : G)).relIndex
        (F8.Uγ V (A6.g1 T V) (k : G)) = 2 := by
      rw [eDγ, eU, F9.relIndex_conjSub]
      exact hH2
    have hH2k : (F8.DH V (fsuV1 T V) (A6.g1 T V) (k : G)).relIndex
        (conjClosure V (A6.g1 T V)) = 2 := by
      rw [eDH, ← eB, F9.relIndex_conjSub]
      exact hγ2
    have h := A₁_le_of_relIndex hF sk hγ2k hH2k hnt
    rw [eA, ← eB] at h
    have := conjSub_mono ((y : G))⁻¹ h
    rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this
  refine ⟨γ, γ', g, s, ?_, hH2, hV1, hA1⟩
  have hc : Nat.card ↥(modO2Image (A6.g1 T V) (F8.Uγ V (A6.g1 T V) (g : G))) =
      Nat.card (X.img (F8.Uγ V (A6.g1 T V) (g : G))) := by
    rw [TopCtx.img_eq_map, Subgroup.card_map_of_injective
      (X.actDot_injective hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334)]
  rw [hc, hcard, hγ2]

theorem lemma14_7_32_L2_mod_of
    (hD36 : D36) (hD37 : D37) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6)
    (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h29 : Thm14_7_29)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    Lemma14_7_32_L2_mod := by
  intro G _ _ T L V K R
  exact caseOne_of_red hD36 hD37 hA37 hA38 h76 h33 h36 hlist h29 h1222 h1332 h1334 R
    (Setting147.hypF98 R.S (stmt13_3_2_two_of h1332) (stmtL32NModule_of_inputs h1332 h1334) h1222)

end CFSG.Quasithin.H13.L32A.L2
