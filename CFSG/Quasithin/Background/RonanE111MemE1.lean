module

public import CFSG.Quasithin.Background.RonanE111E1Data
public import CFSG.Quasithin.Background.RonanE111WrP
public import CFSG.Quasithin.Background.RonanE111MemE2

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB
  CFSG.Quasithin.E2.E22N CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem twoResidual_le_of_le_sup_two {J S P : Subgroup G} (hSJ : S ≤ Subgroup.normalizer (J : Set G))
    (hS2 : IsPGroup 2 S) (hP : P ≤ J ⊔ S) : twoResidual P ≤ J := by
  have hJS : J ⊔ S ≤ Subgroup.normalizer (J : Set G) := sup_le Subgroup.le_normalizer hSJ
  have h1 : twoResidual P ≤ P ⊓ J := by
    refine twoResidual_le_of_isTwoQuotient inf_le_left ?_ ?_
    · exact fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx, hJS (hP hx)⟩
    · intro y hy
      obtain ⟨k, hk⟩ := pow_mem_of_mem_sup_two hSJ hS2 (hP hy)
      exact ⟨k, P.pow_mem hy _, hk⟩
  exact h1.trans inf_le_right

theorem P_le_cov_E1 {X T J : Subgroup G} (hR : E111Reduced G X T) (hJ : IsComp X J) {n : ℕ}
    (hn : 1 ≤ n) {G₁ : Subgroup G} (hTG : T ≤ G₁) {A : Subgroup G} (hAT : A ≤ T)
    (hAab : IsElemAbelian 2 A) (hmem : ∀ K : Subgroup G, E1.IsE n ⊤ T A K → K ≤ G₁)
    {P : Subgroup G}
    (hPH : P ≤ J ⊔ (T ⊓ Subgroup.normalizer (J : Set G)))
    (htau : E1.tauOf (J ⊔ (T ⊓ Subgroup.normalizer (J : Set G))) (T ⊓ Subgroup.normalizer (J : Set G))
      (A ⊓ Subgroup.normalizer (J : Set G)) ≤ (T ⊓ Subgroup.normalizer (J : Set G)) ⊓ P)
    (hSyl : IsSylowIn 2 ((T ⊓ Subgroup.normalizer (J : Set G)) ⊓ P) P)
    (hE1 : E1.EOne ↥P ((A ⊓ Subgroup.normalizer (J : Set G)).subgroupOf P)) :
    P ≤ Cov G₁ J := by
  classical
  set S : Subgroup G := T ⊓ Subgroup.normalizer (J : Set G) with hSdef
  set V : Subgroup G := A ⊓ Subgroup.normalizer (J : Set G) with hVdef
  set H : Subgroup G := J ⊔ S with hHdef
  have hSN : S ≤ Subgroup.normalizer (J : Set G) := inf_le_right
  have hST : S ≤ T := inf_le_left
  have hHS : S ≤ H := le_sup_right
  have hVS : V ≤ S := le_inf (inf_le_left.trans hAT) inf_le_right
  have hAcent : ∀ v ∈ V, v ∈ Subgroup.centralizer (V : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := congrArg Subtype.val (hAab.1.is_comm.comm ⟨w, hw.1⟩ ⟨v, hv.1⟩)
    exact this
  have hVP : V ≤ P := fun v hv =>
    (htau (centralizer_inf_le_tauOf hHS ⟨hVS hv, hAcent v hv⟩)).2
  obtain ⟨p, R, YR, hp, hp2, hRdef, hRP, hYR, hYRS, hRn, hYn, hPR, hpq, hgen⟩ :=
    e1_data hVP hSyl hE1
  have hT : IsSylowIn 2 T ⊤ := hR.2.2.2.2.2.1
  have hS2 : IsPGroup 2 ↥S := hT.2.1.to_le hST
  have hRJ : R ≤ J := by
    rw [hRdef]
    exact twoResidual_le_of_le_sup_two hSN hS2 hPH
  obtain ⟨Z, hZA, hZV, hZVA⟩ := exists_compl hAab (inf_le_left : V ≤ A)
  have hset : DiagSetting X T A J Z := ⟨hR, hAT, hAab, hJ, hZA, hZV⟩
  haveI : Fintype ↥Z := Fintype.ofFinite _
  have hEP : actE T A J ≤ P := by
    intro e he
    obtain ⟨heT, heN, heA⟩ := mem_actE_iff.mp he
    refine (htau (centralizer_inf_le_tauOf hHS ⟨⟨heT, heN⟩, ?_⟩)).2
    show e ∈ Subgroup.centralizer (V : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_iff.mp heA v hv.1
  have hconj : ∀ {U : Subgroup G}, (∀ x ∈ P, ∀ u ∈ U, x * u * x⁻¹ ∈ U) → ∀ e ∈ P,
      A1b.conjSub e U = U := by
    intro U hU e he
    apply le_antisymm
    · intro x hx
      rw [A1b.mem_conjSub_iff] at hx
      have := hU e he _ hx
      simpa [mul_assoc] using this
    · intro x hx
      rw [A1b.mem_conjSub_iff]
      simpa using hU e⁻¹ (P.inv_mem he) x hx
  have hYT : YR ≤ T := (hYRS.trans inf_le_left).trans hST
  have hYRn : ∀ r ∈ R, ∀ y ∈ YR, r * y * r⁻¹ ∈ YR := fun r hr y hy => hYn r (hRP hr) y hy
  have hcov := pgroup_diag_cover hn hset hp hp2 hRJ hYR hYRn hYT
    (fun e he => hconj hRn e (hEP he)) (fun e he => hconj hYn e (hEP he)) hpq hgen
  have hG₁ : T ⊔ ⨆ K ∈ {K : Subgroup G | E1.IsE n ⊤ T A K}, K ≤ G₁ :=
    sup_le hTG (iSup₂_le fun K hK => hmem K hK)
  have hRCov : R ≤ Cov G₁ J := le_Cov_of_dimg hset hRJ (hcov.trans hG₁)
  have hSCov : S ≤ Cov G₁ J := fun s hs => mem_Cov_of_mem (hTG hs.1) hs.2
  rw [hPR]
  exact sup_le hRCov (inf_le_left.trans hSCov)

end CFSG.Quasithin.RonanE111
