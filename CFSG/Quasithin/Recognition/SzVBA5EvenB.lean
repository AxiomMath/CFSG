module

public import CFSG.Quasithin.Recognition.SzVBA5Geo
public import CFSG.Quasithin.Recognition.SzVBA5Uc

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

omit [Finite G] in
private theorem le_normalizer_of_forall_conj_mem {H U : Subgroup G}
    (key : ∀ h ∈ H, ∀ w ∈ U, h * w * h⁻¹ ∈ U) : H ≤ Subgroup.normalizer (U : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨fun hw => key h hh w hw, fun hw => ?_⟩
  have := key h⁻¹ (H.inv_mem hh) _ hw
  simpa [mul_assoc] using this

private theorem mem_or_mul_inv_mem_of_relIndex_two {Q Y : Subgroup G}
    (h : Q.relIndex Y ≤ 2) {v y : G} (hv : v ∈ Y) (hvQ : v ∉ Q) (hy : y ∈ Y) :
    y ∈ Q ∨ y * v⁻¹ ∈ Q := by
  have hpos : 0 < Q.relIndex Y :=
    Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card (H := Q) (K := Y)) Nat.card_pos
  have hdvd : Q.relIndex Y ∣ 2 := by
    rcases (show Q.relIndex Y = 1 ∨ Q.relIndex Y = 2 by omega) with h1 | h2
    · rw [h1]
      exact one_dvd _
    · rw [h2]
  obtain ⟨a, -, ha⟩ := Subgroup.relIndex_dvd_two_iff.mp hdvd
  have hva : v * a ∈ Q := (ha v hv).resolve_right hvQ
  rcases ha y hy with hya | hyQ
  · right
    have e : y * a * (v * a)⁻¹ = y * v⁻¹ := by group
    simpa only [e] using Q.mul_mem hya (Q.inv_mem hva)
  · exact Or.inl hyQ

private theorem le_of_relIndex_le_two {Q Y N : Subgroup G} (h : Q.relIndex Y ≤ 2) (hQ : Q ≤ N)
    {a : G} (haY : a ∈ Y) (haQ : a ∉ Q) (haN : a ∈ N) : Y ≤ N := by
  intro y hy
  rcases mem_or_mul_inv_mem_of_relIndex_two h haY haQ hy with h1 | h2
  · exact hQ h1
  · have e : y = (y * a⁻¹) * a := by group
    rw [e]
    exact N.mul_mem (hQ h2) haN

private theorem conj_mem_of_relIndex_le_two {Q U V W : Subgroup G} {z : G}
    (hrel : Q.relIndex U ≤ 2) (hVU : V ≤ U) (hz : z ∈ V)
    (hQW : ∀ q ∈ Q, ∀ a ∈ W, a * q = q * a) (hcomm : ⁅V, W⁆ ≤ Subgroup.zpowers z)
    {v₀ : G} (hv₀ : v₀ ∈ V) (hv₀Q : v₀ ∉ Q) {a : G} (ha : a ∈ W) {y : G} (hy : y ∈ U) :
    a * y * a⁻¹ ∈ U := by
  rcases mem_or_mul_inv_mem_of_relIndex_two hrel (hVU hv₀) hv₀Q hy with hyQ | hq
  · have e : a * y * a⁻¹ = y := by
      rw [hQW y hyQ a ha]
      group
    rw [e]
    exact hy
  · have hqU : y * v₀⁻¹ ∈ U := U.mul_mem hy (U.inv_mem (hVU hv₀))
    have hc : a * v₀ * a⁻¹ * v₀⁻¹ ∈ Subgroup.zpowers z := by
      have h1 := Subgroup.commutator_mem_commutator ha hv₀
      rw [Subgroup.commutator_comm W V, commutatorElement_def] at h1
      exact hcomm h1
    have hcU : a * v₀ * a⁻¹ * v₀⁻¹ ∈ U := hVU ((Subgroup.zpowers_le.mpr hz) hc)
    have e : a * y * a⁻¹ = (y * v₀⁻¹) * (a * v₀ * a⁻¹ * v₀⁻¹) * v₀ := by
      calc a * y * a⁻¹ = (a * (y * v₀⁻¹)) * (v₀ * a⁻¹) := by group
        _ = ((y * v₀⁻¹) * a) * (v₀ * a⁻¹) := by rw [hQW _ hq a ha]
        _ = (y * v₀⁻¹) * (a * v₀ * a⁻¹ * v₀⁻¹) * v₀ := by group
    rw [e]
    exact U.mul_mem (U.mul_mem hqU hcU) (hVU hv₀)

omit [Finite G] in
private theorem le_or_ge_of_index3 {K : Subgroup G} (hT3 : T.relIndex G₁ = 3) (hTK : T ≤ K)
    (hKG : K ≤ G₁) : K ≤ T ∨ G₁ ≤ K := by
  have hmul := Subgroup.relIndex_mul_relIndex T K G₁ hTK hKG
  rw [hT3] at hmul
  have hdvd : K.relIndex G₁ ∣ 3 := Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Or.inr (Subgroup.relIndex_eq_one.mp h1)
  · left
    rw [h3] at hmul
    have h1 : T.relIndex K = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp h1

private theorem V_le_Uc (hC : GeoCtx G₀ G₁ G₂ T V z) {β : CosetGeom G₀ G₁ G₂}
    (hβ : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β) : V ≤ Uc V (γ₀ G₀ G₁ G₂) β := by
  intro w hw
  have hV : Vv V (γ₀ G₀ G₁ G₂) = V := Vv_γ₀ hC.hyp.normalizes
  have hw' : w ∈ Vv V (γ₀ G₀ G₁ G₂) := by
    rw [hV]
    exact hw
  refine mem_Uc.mpr ⟨⟨Subgroup.le_normalizer hw', fun q hq => ?_⟩, ?_⟩
  · rw [stab_γ₀ hC.hyp.le₁] at hq
    have hcomm : w * q = q * w :=
      Subgroup.mem_centralizer_iff.mp (CosetGeom.pCoreOf_le_centralizer hC.hyp hq) w hw
    have e : q * w * q⁻¹ * w⁻¹ = 1 := by
      rw [← hcomm]
      group
    rw [hV, e]
    exact V.one_mem
  · exact Vv_le_Vv_of_adj hβ vtype_γ₀ hw'

private theorem not_inf_stab_le_T (hC : GeoCtx G₀ G₁ G₂ T V z) {β : CosetGeom G₀ G₁ G₂}
    (hβ : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β) (hβ1 : β ≠ γ₁ G₀ G₁ G₂) :
    ¬ G₁ ⊓ stab β ≤ T := by
  intro hHT
  have h₁ : G₁ ≤ G₀ := hC.hyp.le₁
  have h₂ : G₂ ≤ G₀ := hC.hyp.le₂
  have hTG₁ : T ≤ G₁ := hC.hyp.sylow₁.1
  obtain ⟨l, hl0, hlβ⟩ := exists_stab_smul_eq (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂)) hβ
  subst hlβ
  have hlG₁ : (l : G) ∈ G₁ := by
    have := mem_stab_of_smul_eq hl0
    rwa [stab_γ₀ h₁] at this
  have hH : G₁ ⊓ stab (l • γ₁ G₀ G₁ G₂) = conjSub (l : G) T := by
    rw [stab_smul, stab_γ₁ h₂, ← hC.inf_eq, conjSub_inf, F7.conjSub_eq_of_mem hlG₁]
  have hTeq : G₁ ⊓ stab (l • γ₁ G₀ G₁ G₂) = T := by
    refine Subgroup.eq_of_le_of_card_ge hHT ?_
    exact (by rw [hH, card_conjSub] :
      Nat.card T = Nat.card (G₁ ⊓ stab (l • γ₁ G₀ G₁ G₂) : Subgroup G)).le
  have hlN : (l : G) ∈ Subgroup.normalizer (T : Set G) :=
    mem_normalizer_of_conjSub_eq (hH.symm.trans hTeq)
  have hlT : (l : G) ∉ T := fun hlT => by
    refine hβ1 (smul_eq_of_mem_stab ?_)
    rw [stab_γ₁ h₂]
    exact hC.hyp.sylow₂.1 hlT
  rcases le_or_ge_of_index3 hC.index3 (le_inf Subgroup.le_normalizer hTG₁) inf_le_right with h | h
  · exact hlT (h ⟨hlN, hlG₁⟩)
  · have hTb : T ≤ ballStab 1 (γ₀ G₀ G₁ G₂) :=
      (ballStab_one_γ₀ hC.hyp.gen).2.2 ⟨hC.inf_eq.ge, h.trans inf_le_left⟩
    rw [ballStab_one_eq_pCoreOf hC, stab_γ₀ h₁] at hTb
    have h2 := F112W.relIndex_pCoreOf_T hC.hyp hC.natS3
    have h1 : (pCoreOf 2 G₁).relIndex T = 1 := Subgroup.relIndex_eq_one.mpr hTb
    omega

private theorem le_normalizer_of_T_inf_stab (hC : GeoCtx G₀ G₁ G₂ T V z)
    {β : CosetGeom G₀ G₁ G₂} (hβ : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β)
    (hβ1 : β ≠ γ₁ G₀ G₁ G₂) {U : Subgroup G} (hT : T ≤ Subgroup.normalizer (U : Set G))
    (hH : G₁ ⊓ stab β ≤ Subgroup.normalizer (U : Set G)) :
    G₁ ≤ Subgroup.normalizer (U : Set G) := by
  rcases le_or_ge_of_index3 hC.index3 (le_inf hT hC.hyp.sylow₁.1) inf_le_right with h | h
  · exact absurd ((le_inf hH inf_le_left).trans h) (not_inf_stab_le_T hC hβ hβ1)
  · exact h.trans inf_le_left

theorem normalizer_Uc {u δ x ω p2 : CosetGeom G₀ G₁ G₂}
    (D : CritFacts G₀ G₁ G₂ T V z u δ x ω p2)
    (ha : ∀ β, (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β →
      Uc V (γ₀ G₀ G₁ G₂) β ≤ pCoreOf 2 (stab u))
    {β : CosetGeom G₀ G₁ G₂} (hβ : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β)
    (hβ1 : β ≠ γ₁ G₀ G₁ G₂) :
    G₁ ≤ Subgroup.normalizer (Uc V (γ₀ G₀ G₁ G₂) β : Set G) := by
  have hC := D.hC
  have hyp := hC.hyp
  have h₁ : G₁ ≤ G₀ := hyp.le₁
  have hN : G₁ ≤ Subgroup.normalizer (V : Set G) := hyp.normalizes
  have hH : G₁ ⊓ stab β ≤ Subgroup.normalizer (Uc V (γ₀ G₀ G₁ G₂) β : Set G) := by
    have := stab_inf_le_normalizer_Uc hN (γ₀ G₀ G₁ G₂) β
    rwa [stab_γ₀ h₁] at this
  have hQ₀ : pCoreOf 2 G₁ ≤ Subgroup.normalizer (Uc V (γ₀ G₀ G₁ G₂) β : Set G) := by
    refine (le_inf (pCoreOf_le 2 G₁) ?_).trans hH
    have hb : pCoreOf 2 G₁ = ballStab 1 (γ₀ G₀ G₁ G₂) := by
      rw [ballStab_one_eq_pCoreOf hC, stab_γ₀ h₁]
    rw [hb]
    exact ballStab_le_stab_of_dist_le (dist_eq_one_iff_adj.mpr hβ).le
  have hUQ : Uc V (γ₀ G₀ G₁ G₂) β ≤ pCoreOf 2 (stab u) := ha β hβ
  have hUω : Uc V (γ₀ G₀ G₁ G₂) β ≤ stab ω :=
    hUQ.trans ((ballStab_one_eq_pCoreOf hC u).symm.le.trans
      (ballStab_le_stab_of_dist_le (dist_eq_one_iff_adj.mpr D.adj_uω).le))
  have hUp : IsPGroup 2 (Uc V (γ₀ G₀ G₁ G₂) β) := (pCoreOf_isPGroup 2 _).to_le hUQ
  have hrel := relIndex_pCoreOf_le_two hC D.t_ω hUω hUp
  have hVU : V ≤ Uc V (γ₀ G₀ G₁ G₂) β := V_le_Uc hC hβ
  obtain ⟨v₀, hv₀V, hv₀Q⟩ := IsConcreteLE.not_le_iff_exists.mp D.hcrit
  have hQW : ∀ q ∈ pCoreOf 2 (stab ω), ∀ a ∈ Vv V ω, a * q = q * a := fun q hq a ha' =>
    Subgroup.mem_centralizer_iff.mp (pCoreOf_le_centralizer_Vv hC D.t_ω hq) a ha'
  have hWω : Vv V ω ≤ Subgroup.normalizer (Uc V (γ₀ G₀ G₁ G₂) β : Set G) :=
    le_normalizer_of_forall_conj_mem fun a haW y hy =>
      conj_mem_of_relIndex_le_two hrel hVU hC.klein.z_mem hQW D.comm_le hv₀V hv₀Q haW hy
  have hWQ : ¬ Vv V ω ≤ pCoreOf 2 G₁ := by
    intro hle
    apply D.comm_ne
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hle.trans (CosetGeom.pCoreOf_le_centralizer hyp))
  obtain ⟨a', ha'W, ha'Q⟩ := IsConcreteLE.not_le_iff_exists.mp hWQ
  have hT : T ≤ Subgroup.normalizer (Uc V (γ₀ G₀ G₁ G₂) β : Set G) :=
    le_of_relIndex_le_two (F112W.relIndex_pCoreOf_T hyp hC.natS3).le hQ₀ (D.Vω_le_T ha'W) ha'Q
      (hWω ha'W)
  exact le_normalizer_of_T_inf_stab hC hβ hβ1 hT hH

theorem Uc_eq {u δ x ω p2 : CosetGeom G₀ G₁ G₂}
    (D : CritFacts G₀ G₁ G₂ T V z u δ x ω p2)
    (ha : ∀ β, (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β →
      Uc V (γ₀ G₀ G₁ G₂) β ≤ pCoreOf 2 (stab u))
    {β β' : CosetGeom G₀ G₁ G₂} (hβ : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β)
    (hβ' : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β') :
    Uc V (γ₀ G₀ G₁ G₂) β = Uc V (γ₀ G₀ G₁ G₂) β' := by
  obtain ⟨β₂, hβ₂, hβ₂1, -⟩ := D.EV3
  have hnorm := normalizer_Uc D ha hβ₂ hβ₂1
  have key : ∀ b, (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) b →
      Uc V (γ₀ G₀ G₁ G₂) b = Uc V (γ₀ G₀ G₁ G₂) β₂ := by
    intro b hb
    obtain ⟨g, hg0, hgb⟩ := exists_stab_smul_eq hβ₂ hb
    have h1 := Uc_smul D.hC.hyp.normalizes g (γ₀ G₀ G₁ G₂) β₂
    rw [hg0, hgb] at h1
    rw [h1]
    have hgG₁ : (g : G) ∈ G₁ := by
      have := mem_stab_of_smul_eq hg0
      rwa [stab_γ₀ D.hC.hyp.le₁] at this
    exact F7.conjSub_eq_of_mem_normalizer (hnorm hgG₁)
  exact (key β hβ).trans (key β' hβ').symm

end CFSG.Quasithin.SzVB
